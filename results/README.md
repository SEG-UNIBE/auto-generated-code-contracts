# AI-Generated Code Contracts

## Results

Our results can be found in the Zenodo replication package (https://doi.org/10.5281/zenodo.13351003) that contains the following artifacts:

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.13351003.svg)](https://doi.org/10.5281/zenodo.13351003)

### Sourcegraph Search Results

- ```sourcegraph-results.tar```: the results of the Sourcegraph search queries 

### Datasets

- ```dataset.tar```: the dataset including the [weka-project](https://github.com/svn2github/weka) which contributes two-thirds of the contracts
- ```dataset-withoutweka.tar```: the dataset without weka, which is significantly smaller and was used to examine the performance bias when training and testing without weka

### CodeT5 Models

- ```codet5-contracts.tar```: the best performing CodeT5 model which was fine-tuned to create OpenJML annotations for methods
- ```codet5p-contracts.tar```: the best performing CodeT5+ model which was fine-tuned to create OpenJML annotations for methods
- ```codet5p-contracts-withoutweka.tar```: the CodeT5+ model which was trained without weka on the same task

### Analysis Results

- ```analysis-results.tar/compilability-analysis```: the results of the compilability analysis
  - the subjects to which we applied the best performing CodeT5+
  - the compilation results and their analysis

- ```analysis-results.tar/logical-analysis``` the results of the logical analysis
  - the analysis of logic validity of SimpleStack and SimpleTicTacToe
