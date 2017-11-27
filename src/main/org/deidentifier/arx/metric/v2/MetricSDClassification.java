/*
 * ARX: Powerful Data Anonymization
 * Copyright 2012 - 2017 Fabian Prasser, Florian Kohlmayer and contributors
 * 
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.deidentifier.arx.metric.v2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.deidentifier.arx.ARXConfiguration;
import org.deidentifier.arx.DataDefinition;
import org.deidentifier.arx.certificate.elements.ElementData;
import org.deidentifier.arx.criteria.EDDifferentialPrivacy;
import org.deidentifier.arx.framework.check.distribution.Distribution;
import org.deidentifier.arx.framework.check.groupify.HashGroupify;
import org.deidentifier.arx.framework.check.groupify.HashGroupifyEntry;
import org.deidentifier.arx.framework.data.Data;
import org.deidentifier.arx.framework.data.DataManager;
import org.deidentifier.arx.framework.data.GeneralizationHierarchy;
import org.deidentifier.arx.framework.lattice.Transformation;
import org.deidentifier.arx.metric.MetricConfiguration;

/**
 * This class provides an implementation of the classification metric.
 * 
 * @author Fabian Prasser
 * @author Johanna Eicher
 */
public class MetricSDClassification extends AbstractMetricSingleDimensional {

    /** SVUID. */
    private static final long serialVersionUID             = -7940144844158472876L;
    
    /** Record wrapper */
    class RecordWrapper {

        /** Field*/
        private final int[] tuple;
        /** Field*/
        private final int hash;

        /**
         * Constructor
         * @param tuple
         */
        public RecordWrapper(int[] tuple) {
            this.tuple = tuple;
            this.hash = Arrays.hashCode(tuple);
        }

        @Override
        public boolean equals(Object other) {
            return Arrays.equals(this.tuple, ((RecordWrapper)other).tuple);
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    /** Indices of response variables in distributions */
    private int[]             responseVariables            = null;
    /** Indices of response variables in quasi-identifiers */
    private int[]             responseVariablesNotAnalyzed = null;

    /** Penalty */
    private double            penaltySuppressed            = 1d;
    /** Penalty */
    private double            penaltyInfrequentResponse    = 1d;
    /** Penalty */
    private double            penaltyNoMajorityResponse    = 1d;

    /** Minimal size of equivalence classes enforced by the differential privacy model */
    private double            k;

    /** The root values of all generalization hierarchies or -1 if no single root value exists */
    private int[]             rootValues;

    /**
     * Creates a new instance.
     */
    protected MetricSDClassification() {
        super(false, false, false);
    }

    /**
     * Creates a new instance.
     * 
     * @param gsFactor
     */
    protected MetricSDClassification(double gsFactor) {
        super(false, false, false, gsFactor);
    }

    @Override
    public ILSingleDimensional createMaxInformationLoss() {
        Double rows = getNumTuples();
        if (rows == null) {
            
            throw new IllegalStateException("Metric must be initialized first");
            
        } else {
            
            // TODO: This is probably crap. Non-analyzed RVs need to be treated differently.
            // Non-analyzed response variables are only penalized if they are suppressed
            double max = rows * responseVariablesNotAnalyzed.length * penaltySuppressed;
            
            // Use maximal penalty for other response variables
            double maxPenalty = Math.max(penaltySuppressed, Math.max(penaltyInfrequentResponse, penaltyNoMajorityResponse));
            max += rows * responseVariables.length * maxPenalty;
            
            // Done
            return new ILSingleDimensional(max);
        }
    }
    
    @Override
    public ILSingleDimensional createMinInformationLoss() {
        return new ILSingleDimensional(0d);
    }
    
    /**
     * Returns the configuration of this metric.
     *
     * @return
     */
    public MetricConfiguration getConfiguration() {
        return new MetricConfiguration(false, // monotonic
                                       super.getGeneralizationSuppressionFactor(), // gs-factor
                                       false, // precomputed
                                       0.0d,  // precomputation threshold
                                       AggregateFunction.SUM // aggregate function
        );
    }
    
    /**
     * Penalty for records with non-majority response
     * @return the penaltyDifferentFromMajority
     */
    public double getPenaltyInfrequentResponse() {
        return penaltyInfrequentResponse;
    }
    
    /**
     * Penalty for records without a majority response
     * @return the penaltyNoMajority
     */
    public double getPenaltyNoMajorityResponse() {
        return penaltyNoMajorityResponse;
    }

    /**
     * Penalty for suppressed features
     * @return the penaltySuppressed
     */
    public double getPenaltySuppressed() {
        return penaltySuppressed;
    }
    
    @Override
    public ILScore getScore(final Transformation node, final HashGroupify groupify) {
        
        // Prepare
        Map<RecordWrapper, Map<RecordWrapper, Integer>> featuresToClassToCount = new HashMap<>();

        // Setup data structures
        HashGroupifyEntry m = groupify.getFirstEquivalenceClass();
        while (m != null) {
            m.read();
            
            if (!m.isNotOutlier) continue;
            
            int[] features = new int[rootValues.length - responseVariablesNotAnalyzed.length];
            int featuresIndex = 0;
            int[] responseValues = new int[responseVariablesNotAnalyzed.length];
            int responseIndex = 0;
            int nextResponseIndex = 0;
            boolean featuresSuppressed = true;
            
            for (int i=0; i<rootValues.length; ++i) {
                int value = m.next();
                if (i == responseVariablesNotAnalyzed[nextResponseIndex]) {
                    responseValues[responseIndex] = value;
                    responseIndex++;
                    nextResponseIndex++;
                } else {
                    features[featuresIndex] = value;
                    featuresIndex++;
                    if(rootValues[i] == -1 || value != rootValues[i]) {
                        featuresSuppressed = false;
                    }
                }
            }
            
            if (featuresSuppressed) continue;

            RecordWrapper featuresWrapped = new RecordWrapper(features);
            RecordWrapper responseValuesWrapped = new RecordWrapper(responseValues);

            Map<RecordWrapper, Integer> classToCount = featuresToClassToCount.get(featuresWrapped);
            if (classToCount == null) {
                classToCount = new HashMap<>();
                classToCount.put(responseValuesWrapped, m.count);
            } else {
                int classCount = classToCount.containsKey(responseValuesWrapped) ? classToCount.get(responseValuesWrapped) + m.count : m.count;
                classToCount.put(responseValuesWrapped, classCount);
            }
            featuresToClassToCount.put(featuresWrapped, classToCount);
            
            m = m.nextOrdered;
        }

        // Calculate score
        double score = 0d;
        for (Map<RecordWrapper, Integer> classToCount : featuresToClassToCount.values()) {
            int maxCount = 0;
            for (int count : classToCount.values()) {
                maxCount = Math.max(maxCount, count);
            }
            score += maxCount;
        }

        // Return
        return new ILScore(score / (double)k);
    }

    @Override
    public boolean isGSFactorSupported() {
        return true;
    }
    
    @Override
    public boolean isScoreFunctionSupported() {
        return true;
    }

    @Override
    public ElementData render(ARXConfiguration config) {
        ElementData result = new ElementData("Classification accuracy");
        result.addProperty("Monotonic", this.isMonotonic(config.getSuppressionLimit()));
        result.addProperty("Penalty for suppressed features", this.getPenaltySuppressed());
        result.addProperty("Penalty for records with non-majority response", this.getPenaltyInfrequentResponse());
        result.addProperty("Penalty for records without a majority response", this.getPenaltyNoMajorityResponse());
        return result;
    }

    @Override
    public String toString() {
        return "Classification accuracy";
    }
    
    /**
     * Returns the penalty for the given entry
     * @param entry
     * @return
     */
    private double getPenalty(HashGroupifyEntry entry) {

        // Prepare
        double result = 0d;
        
        // Suppressed
        if (!entry.isNotOutlier) {
            
            // According penalty for all records and response variables in this class
            result += entry.count * (responseVariablesNotAnalyzed.length + responseVariables.length) * penaltySuppressed;
            
        // Not suppressed
        } else {
            
            // For each analyzed response variable
            for (int index : this.responseVariables) {
                
                // Find frequencies of most frequent and second most frequent attribute values
                int top1 = -1;
                int top2 = -1;
                
                // For each bucket
                Distribution distribution = entry.distributions[index];
                int[] buckets = distribution.getBuckets();
                for (int i = 0; i < buckets.length; i += 2) {
                    
                    // Get frequency
                    int frequency = buckets[i + 1];
                    boolean largerThanTop1 = frequency > top1;
                    boolean largerThanTop2 = frequency > top2;
                    
                    // Step 1: If frequency is > top1 
                    //         --> top1 is moved down to top2
                    top2 = largerThanTop1 ? top1 : top2;
    
                    // Step 2: If frequency is > top1 
                    //         --> top1 is set to new frequency
                    top1 = largerThanTop1 ? frequency : top1;
                    
                    // Step 3: If frequency is > top2 but not > top1 (which implies frequency != top1, because of step 2)
                    //         --> top2 is set to new frequency
                    top2 = largerThanTop2 && frequency != top1 ? frequency : top2;
                }
                
                // If a majority class label exists
                if (top1 != top2) {
                    
                    // Records with other than majority class label get penalized
                    result += (entry.count - top1) * penaltyInfrequentResponse;
                } else {
                    
                    // All records get penalized
                    result += entry.count * penaltyNoMajorityResponse;
                }
                
                // TODO: Non-analyzed RVs need to also be treated.
            }
        }
        
        // Return overall penalty
        return result;
    }
    
    @Override
    protected ILSingleDimensionalWithBound getInformationLossInternal(final Transformation node, final HashGroupify g) {
       
        // Prepare
        double penalty = 0d;
        HashGroupifyEntry m = g.getFirstEquivalenceClass();
        
        // For each group
        while (m != null) {
            if (m.count > 0) {
                penalty += getPenalty(m);
            }
            m = m.nextOrdered;
        }

        // Return
        // TODO: Can a lower bound be calculated for this model?
        return createInformationLoss(penalty);
    }

    @Override
    protected ILSingleDimensionalWithBound getInformationLossInternal(Transformation node, HashGroupifyEntry m) {

        if (m.count > 0) {
            // TODO: Can a lower bound be calculated for this model?
            return createInformationLoss(getPenalty(m));
        } else {
            return createInformationLoss(0d);
        }
    }

    @Override
    protected ILSingleDimensional getLowerBoundInternal(Transformation node) {
        // TODO: Can a lower bound be calculated for this model?
        return null;
    }

    @Override
    protected ILSingleDimensional getLowerBoundInternal(Transformation node, HashGroupify groupify) {
        // TODO: Can a lower bound be calculated for this model?
        return null;
    }

    @Override
    protected void initializeInternal(DataManager manager,
                                      DataDefinition definition,
                                      Data input,
                                      GeneralizationHierarchy[] hierarchies,
                                      ARXConfiguration config) {

        // Super
        super.initializeInternal(manager, definition, input, hierarchies, config);
        
        // Extract indices of response variables
        List<Integer> indices = new ArrayList<>();
        List<Integer> indicesNotAnalyzed = new ArrayList<>();
        for (String variable : definition.getResponseVariables()){
            int index = manager.getDataAnalyzed().getIndexOf(variable);
            if (index != -1) {
                indices.add(index);
            } else {
                indicesNotAnalyzed.add(index);
            }
        }
        
        // Store information about response variables
        Collections.sort(indices);
        this.responseVariables = new int[indices.size()];
        for (int i = 0; i < indices.size(); i++) {
            responseVariables[i] = indices.get(i);
        }
        Collections.sort(indicesNotAnalyzed);
        this.responseVariablesNotAnalyzed = new int[indicesNotAnalyzed.size()];
        for (int i = 0; i < indicesNotAnalyzed.size(); i++) {
            responseVariablesNotAnalyzed[i] = indicesNotAnalyzed.get(i);
        }
        
        // Set penalties using the gs-factor. This is sort of a hack but should be OK for now.
        penaltySuppressed            = super.getSuppressionFactor();
        penaltyInfrequentResponse    = super.getGeneralizationFactor();
        penaltyNoMajorityResponse    = super.getGeneralizationSuppressionFactor();
        
        if (config.isPrivacyModelSpecified(EDDifferentialPrivacy.class)) {
            // Store minimal size of equivalence classes
            EDDifferentialPrivacy dpCriterion = config.getPrivacyModel(EDDifferentialPrivacy.class);
            k = (double)dpCriterion.getMinimalClassSize();
            
            // Store root values of generalization hierarchies or -1 if no single root value exists
            rootValues = new int[hierarchies.length];
            for (int i = 0; i < hierarchies.length; i++) {
                int rootValue = -1;
                for (int[] row : hierarchies[i].getArray()) {
                    if (rootValue == -1) {
                        rootValue = row[row.length-1];
                    } else if (row[row.length-1] != rootValue) {
                        rootValue = -1;
                        break;
                    }
                }
                rootValues[i] = rootValue;
            }
        }
    }
}