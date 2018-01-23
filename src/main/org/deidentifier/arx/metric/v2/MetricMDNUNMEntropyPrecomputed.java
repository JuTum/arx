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

import java.util.Arrays;

import org.deidentifier.arx.ARXConfiguration;
import org.deidentifier.arx.DataDefinition;
import org.deidentifier.arx.certificate.elements.ElementData;
import org.deidentifier.arx.framework.check.groupify.HashGroupify;
import org.deidentifier.arx.framework.check.groupify.HashGroupifyEntry;
import org.deidentifier.arx.framework.data.Data;
import org.deidentifier.arx.framework.data.DataManager;
import org.deidentifier.arx.framework.data.DataMatrix;
import org.deidentifier.arx.framework.data.Dictionary;
import org.deidentifier.arx.framework.data.GeneralizationHierarchy;
import org.deidentifier.arx.framework.lattice.Transformation;
import org.deidentifier.arx.metric.MetricConfiguration;

import com.carrotsearch.hppc.IntIntOpenHashMap;

/**
 * This class provides an implementation of the non-uniform entropy
 * metric. See:<br>
 * A. De Waal and L. Willenborg: 
 * "Information loss through global recoding and local suppression" 
 * Netherlands Off Stat, vol. 14, pp. 17–20, 1999.
 * 
 * @author Fabian Prasser
 * @author Florian Kohlmayer
 */
public class MetricMDNUNMEntropyPrecomputed extends MetricMDNUEntropyPrecomputed {

    /** SVUID. */
    private static final long serialVersionUID = -7428794463838685004L;

    /**
     * Creates a new instance.
     */
    protected MetricMDNUNMEntropyPrecomputed() {
        super(true, false, false, 0.5d, AggregateFunction.SUM);
    }
    
    /**
     * Creates a new instance.
     *
     * @param gsFactor
     * @param function
     */
    protected MetricMDNUNMEntropyPrecomputed(double gsFactor, AggregateFunction function){
        super(true, false, false, gsFactor, function);
    }
    
    /**
     * Returns the configuration of this metric.
     *
     * @return
     */
    public MetricConfiguration getConfiguration() {
        return new MetricConfiguration(false, // monotonic
                                       super.getGeneralizationSuppressionFactor(), // gs-factor
                                       true, // precomputed
                                       1.0d, // precomputation threshold
                                       this.getAggregateFunction() // aggregate function
        );
    }

    @Override
    public boolean isGSFactorSupported() {
        return true;
    }

    @Override
    public boolean isPrecomputed() {
        return true;
    }

    @Override
    public ElementData render(ARXConfiguration config) {
        ElementData result = new ElementData("Non-uniform entropy");
        result.addProperty("Aggregate function", super.getAggregateFunction().toString());
        result.addProperty("Monotonic", this.isMonotonic(config.getSuppressionLimit()));
        result.addProperty("Generalization factor", this.getGeneralizationFactor());
        result.addProperty("Suppression factor", this.getSuppressionFactor());
        return result;
    }

    @Override
    public String toString() {
        return "Non-monotonic non-uniform entropy";
    }

    @Override
    protected ILMultiDimensionalWithBound getInformationLossInternal(final Transformation node, final HashGroupify g) {
        
        // Prepare
        double sFactor = super.getSuppressionFactor();
        
        // Compute non-uniform entropy
        double[] result = super.getInformationLossInternalRaw(node, g); // The information loss of all non-suppressed cells
        double[] bound = new double[result.length];
        System.arraycopy(result, 0, bound, 0, result.length);
        
        // Compute loss induced by suppression
        int[] numSuppressed = new int[node.getGeneralization().length];
        final IntIntOpenHashMap[] original = new IntIntOpenHashMap[node.getGeneralization().length];
        for (int i = 0; i < original.length; i++) {
            original[i] = new IntIntOpenHashMap();
        }
        
        // Compute counts for suppressed values in each column 
        HashGroupifyEntry m = g.getFirstEquivalenceClass();
        while (m != null) {
            m.read();
            for (int dimension=0; dimension<node.getGeneralization().length; dimension++) {
                int value = m.next();
                if (!m.isNotOutlier || (rootValues[dimension] != -1 && value == rootValues[dimension])) {
                    // The attribute value has been suppressed because of record suppression or because of generalization
                    numSuppressed[dimension] += m.count;
                    original[dimension].putOrAdd(value, m.count, m.count);
                }
                // Add values for records which have been suppressed by sampling
                int nummSuppressedBySampling = m.pcount - m.count;
                numSuppressed[dimension] += nummSuppressedBySampling;
                original[dimension].putOrAdd(value, nummSuppressedBySampling, nummSuppressedBySampling);
            }
            m = m.nextOrdered;
        }

        // Evaluate non-uniform entropy for suppressed values
        for (int i = 0; i < original.length; i++) {
        	IntIntOpenHashMap map = original[i];
        	for (int j = 0; j < map.allocated.length; j++) {
        		if (map.allocated[j]) {
        			double count = map.values[j];
        			result[i] += count * log2((double)count / (double)numSuppressed[i]) * sFactor;
        		}
        	}
        }
        
        // Switch sign bit and round
        for (int column = 0; column < result.length; column++) {
            result[column] = round(result[column] == 0.0d ? result[column] : -result[column]);
            bound[column] = round(bound[column] == 0.0d ? bound[column] : -bound[column]);
        }
        
        // Normalize
        double[] max = super.getMax();
        double maxSum = 0d;
        for (int i = 0; i < max.length; i++) {
        	maxSum += max[i];
        }
        for (int i = 0; i < max.length; i++) {
        	result[i] = (max[i] - result[i]) / maxSum;
        	bound[i] = (max[i] - bound[i]) / maxSum;
        }

        // Return
        return new ILMultiDimensionalWithBound(createInformationLoss(result),
                                               createInformationLoss(bound));
    }

    @Override
    protected AbstractILMultiDimensional getLowerBoundInternal(Transformation node) {
        return super.getInformationLossInternal(node, (HashGroupify)null).getLowerBound();
    }

    @Override
    protected AbstractILMultiDimensional getLowerBoundInternal(Transformation node,
                                                       HashGroupify groupify) {
        return super.getInformationLossInternal(node, (HashGroupify)null).getLowerBound();
    }

    @Override
    protected void initializeInternal(final DataManager manager,
                                      final DataDefinition definition, 
                                      final Data input, 
                                      final GeneralizationHierarchy[] hierarchies, 
                                      final ARXConfiguration config) {
        
        super.initializeInternal(manager, definition, input, hierarchies, config);

        // Prepare
        double sFactor = super.getSuppressionFactor();
        
        // Compute a reasonable minimum & maximum
        double[] min = new double[hierarchies.length];
        Arrays.fill(min, 0d);
        
        double[] max = getMaxInformationLoss(input, sFactor);
        
        super.setMax(max);
        super.setMin(min);
    }
    
    /**
     * Returns the maximal information loss
     * @param data
     * @param sFactor
     * @return
     */
    private double[] getMaxInformationLoss(final Data data, final double sFactor) {
    	DataMatrix array = data.getArray();
    	Dictionary dictionary = data.getDictionary();

    	// Initialize counts
    	int counts[][] = new int[array.getNumColumns()][];
    	for (int i = 0; i < counts.length; i++) {
    		counts[i] = new int[dictionary.getMapping()[i].length];
    	}

    	// Compute counts
    	for (int i = 0; i < array.getNumRows(); i++) { 
    		array.setRow(i);
    		for (int column = 0; column < array.getNumColumns(); column++) {
    			counts[column][array.getValueAtColumn(column)]++;
    		}
    	}
    	
    	// Compute maximal information loss
    	double[] max = new double[array.getNumColumns()];
    	for (int i = 0; i < counts.length; i++) {
    		for (int v = 0; v < counts[i].length; v++) {
    			int count = counts[i][v];
    			max[i] += count * log2((double)count / (double)array.getNumRows()) * sFactor;
    		}
    	}
    	
    	// Switch sign bit and round
        for (int column = 0; column < max.length; column++) {
        	max[column] = round(max[column] == 0.0d ? max[column] : -max[column]);
        }
    	
    	return max;
    }
}
