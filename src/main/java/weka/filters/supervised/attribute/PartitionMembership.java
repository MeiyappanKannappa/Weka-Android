/*
 *   This program is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 *    PartitionMembership.java
 *    Copyright (C) 2012 Eibe Frank
 *
 */

package weka.filters.supervised.attribute;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.Vector;

import weka.classifiers.trees.J48;
import weka.core.*;
import weka.filters.Filter;
import weka.filters.SupervisedFilter;

/**
 * <!-- globalinfo-start -->
 * * A filter that uses a PartitionGenerator to generate partition membership values; filtered instances are composed of these values plus the class attribute (if set in the input data) and rendered as sparse instances. See Section 3 of<br>
 * * Eibe Frank, Bernhard Pfahringer: Propositionalisation of Multi-instance Data Using Random Forests. In: AI 2013: Advances in Artificial Intelligence, 362-373, 2013.
 * * <br><br>
 * <!-- globalinfo-end -->
 * 
 * <!-- options-start -->
 * * Valid options are: <p>
 * * 
 * * <pre> -W &lt;name of partition generator&gt;
 * *  Full name of partition generator to use, e.g.:
 * *   weka.classifiers.trees.J48
 * *  Additional options after the '--'.
 * *  (default: weka.classifiers.trees.J48)</pre>
 * * 
 * <!-- options-end -->
 * 
 * Options after the -- are passed on to the clusterer.
 * 
 * @author Eibe Frank (eibe@cs.waikato.ac.nz)
 * @author Mark Hall (mhall@cs.waikato.ac.nz)
 * @version $Revision: 11932 $
 */
public class PartitionMembership extends Filter implements SupervisedFilter,
  OptionHandler, RevisionHandler, TechnicalInformationHandler {

  /** for serialization */
  static final long serialVersionUID = 333532554667754026L;

  /** The partition generator */
  protected PartitionGenerator m_partitionGenerator = new J48();

  /**
   * Returns the Capabilities of this filter.
   * 
   * @return the capabilities of this object
   * @see Capabilities
   */
  @Override
  public Capabilities getCapabilities() {

    Capabilities result = m_partitionGenerator.getCapabilities();

    result.setMinimumNumberInstances(0);

    return result;
  }

  /**
   * Tests the data whether the filter can actually handle it
   * 
   * @param instanceInfo the data to test
   * @throws Exception if the test fails
   */
  @Override
  protected void testInputFormat(Instances instanceInfo) throws Exception {

    getCapabilities().testWithFail(instanceInfo);
  }

  /**
   * Sets the format of the input instances.
   * 
   * @param instanceInfo an Instances object containing the input instance
   *          structure (any instances contained in the object are ignored -
   *          only the structure is required).
   * @return true if the outputFormat may be collected immediately
   * @throws Exception if the inputFormat can't be set successfully
   */
  @Override
  public boolean setInputFormat(Instances instanceInfo) throws Exception {

    super.setInputFormat(instanceInfo);

    return false;
  }

  /**
   * Signify that this batch of input to the filter is finished.
   * 
   * @return true if there are instances pending output
   * @throws IllegalStateException if no input structure has been defined
   */
  @Override
  public boolean batchFinished() throws Exception {

    if (getInputFormat() == null) {
      throw new IllegalStateException("No input instance format defined");
    }

    if (outputFormatPeek() == null) {
      Instances toFilter = getInputFormat();

      // Build the partition generator
      m_partitionGenerator.generatePartition(toFilter);

      // Create output dataset
      ArrayList<Attribute> attInfo = new ArrayList<Attribute>();
      for (int i = 0; i < m_partitionGenerator.numElements(); i++) {
        attInfo.add(new Attribute("partition_" + i));
      }
      if (toFilter.classIndex() >= 0) {
        attInfo.add((Attribute) toFilter.classAttribute().copy());
      }
      attInfo.trimToSize();
      Instances filtered = new Instances(toFilter.relationName()
        + "_partitionMembership", attInfo, 0);
      if (toFilter.classIndex() >= 0) {
        filtered.setClassIndex(filtered.numAttributes() - 1);
      }
      setOutputFormat(filtered);

      // build new dataset
      for (int i = 0; i < toFilter.numInstances(); i++) {
        convertInstance(toFilter.instance(i));
      }
    }
    flushInput();

    m_NewBatch = true;
    return (numPendingOutput() != 0);
  }

  /**
   * Input an instance for filtering. Ordinarily the instance is processed and
   * made available for output immediately. Some filters require all instances
   * be read before producing output.
   * 
   * @param instance the input instance
   * @return true if the filtered instance may now be collected with output().
   * @throws IllegalStateException if no input format has been defined.
   */
  @Override
  public boolean input(Instance instance) throws Exception {

    if (getInputFormat() == null) {
      throw new IllegalStateException("No input instance format defined");
    }
    if (m_NewBatch) {
      resetQueue();
      m_NewBatch = false;
    }

    if (outputFormatPeek() != null) {
      convertInstance(instance);
      return true;
    }

    bufferInput(instance);
    return false;
  }

  /**
   * Convert a single instance over. The converted instance is added to the end
   * of the output queue.
   * 
   * @param instance the instance to convert
   * @throws Exception if something goes wrong
   */
  protected void convertInstance(Instance instance) throws Exception {

    // Make copy and set weight to one
    Instance cp = (Instance) instance.copy();
    cp.setWeight(1.0);

    // Set up values
    double[] instanceVals = new double[outputFormatPeek().numAttributes()];
    double[] vals = m_partitionGenerator.getMembershipValues(cp);
    System.arraycopy(vals, 0, instanceVals, 0, vals.length);
    if (instance.classIndex() >= 0) {
      instanceVals[instanceVals.length - 1] = instance.classValue();
    }

    push(new SparseInstance(instance.weight(), instanceVals));
  }

  /**
   * Returns an enumeration describing the available options.
   * 
   * @return an enumeration of all the available options.
   */
  @Override
  public Enumeration<Option> listOptions() {

    Vector<Option> newVector = new Vector<Option>(1);

    newVector.addElement(new Option(
            "\tFull name of partition generator to use, e.g.:\n"
                    + "\t\tweka.classifiers.trees.J48\n"
                    + "\tAdditional options after the '--'.\n"
                    + "\t(default: weka.classifiers.trees.J48)", "W", 1,
            "-W <name of partition generator>"));

    return newVector.elements();
  }

  /**
   * Parses a given list of options.
   * <p/>
   * 
   * <!-- options-start -->
   * * Valid options are: <p>
   * * 
   * * <pre> -W &lt;name of partition generator&gt;
   * *  Full name of partition generator to use, e.g.:
   * *   weka.classifiers.trees.J48
   * *  Additional options after the '--'.
   * *  (default: weka.classifiers.trees.J48)</pre>
   * * 
   * <!-- options-end -->
   * 
   * Options after the -- are passed on to the clusterer.
   * 
   * @param options the list of options as an array of strings
   * @throws Exception if an option is not supported
   */
  @Override
  public void setOptions(String[] options) throws Exception {

    String generatorString = Utils.getOption('W', options);
    if (generatorString.length() == 0) {
      generatorString = J48.class.getName();
    }
    setPartitionGenerator((PartitionGenerator) Utils.forName(
      PartitionGenerator.class, generatorString,
      Utils.partitionOptions(options)));

    Utils.checkForRemainingOptions(options);
  }

  /**
   * Gets the current settings of the filter.
   * 
   * @return an array of strings suitable for passing to setOptions
   */
  @Override
  public String[] getOptions() {

    Vector<String> options = new Vector<String>();

    if (m_partitionGenerator != null) {
      options.add("-W");
      options.add(getPartitionGenerator().getClass().getName());
    }

    if ((m_partitionGenerator != null)
      && (m_partitionGenerator instanceof OptionHandler)) {
      String[] generatorOptions = ((OptionHandler) m_partitionGenerator)
        .getOptions();

      if (generatorOptions.length > 0) {
        options.add("--");
        Collections.addAll(options, generatorOptions);
      }
    }
    return options.toArray(new String[0]);
  }

  /**
   * Returns a string describing this filter
   * 
   * @return a description of the filter suitable for displaying in the
   *         explorer/experimenter gui
   */
  public String globalInfo() {

    return "A filter that uses a PartitionGenerator to generate partition "
      + "membership values; filtered instances are composed of these values "
      + "plus the class attribute (if set in the input data) and rendered "
      + "as sparse instances. See Section 3 of\n" + getTechnicalInformation().toString();
  }

  /**
   * Returns an instance of a TechnicalInformation object, containing detailed
   * information about the technical background of this class, e.g., paper
   * reference or book this class is based on.
   *
   * @return the technical information about this class
   */
  @Override
  public TechnicalInformation getTechnicalInformation() {
    TechnicalInformation result;

    result = new TechnicalInformation(TechnicalInformation.Type.INPROCEEDINGS);
    result.setValue(TechnicalInformation.Field.AUTHOR, "Eibe Frank and Bernhard Pfahringer");
    result.setValue(TechnicalInformation.Field.TITLE,
                    "Propositionalisation of Multi-instance Data Using Random Forests");
    result.setValue(TechnicalInformation.Field.BOOKTITLE, "AI 2013: Advances in Artificial Intelligence");
    result.setValue(TechnicalInformation.Field.YEAR, "2013");
    result.setValue(TechnicalInformation.Field.PUBLISHER, "Springer");
    result.setValue(TechnicalInformation.Field.PAGES, "362-373");

    return result;
  }

  /**
   * Returns a description of this option suitable for display as a tip text in
   * the gui.
   * 
   * @return description of this option
   */
  public String partitionGeneratorTipText() {
    return "The partition generator that will generate membership values for the instances.";
  }

  /**
   * Set the generator for use in filtering
   * 
   * @param newPartitionGenerator the generator to use
   */
  public void setPartitionGenerator(PartitionGenerator newPartitionGenerator) {
    m_partitionGenerator = newPartitionGenerator;
  }

  /**
   * Get the generator used by this filter
   * 
   * @return the generator used
   */
  public PartitionGenerator getPartitionGenerator() {
    return m_partitionGenerator;
  }

  /**
   * Main method for testing this class.
   * 
   * @param argv should contain arguments to the filter: use -h for help
   */
  public static void main(String[] argv) {
    runFilter(new PartitionMembership(), argv);
  }

  @Override
  public String getRevision() {
    return RevisionUtils.extract("$Revision: 11932 $");
  }
}

