\section{Tests}
Testing is done using the Hspec testing framework and QuickCheck for property-based testing. The tests are organized into different modules, each focusing on a specific aspect of the code. The main test file is \verb|Spec.lhs|, which serves as an entry point for running all the tests. This file uses the Hspec framework to automatically discover and run all the tests in the project. The \verb|hspec-discover| tool automatically finds all the test files with the suffix \verb|Spec.lhs| in the \verb|test| directory and runs them. 

\vspace{10pt}
\begin{code}
{-# OPTIONS_GHC -F -pgmF hspec-discover #-}
\end{code}

This project follows the convention of one spec file per module. Each spec file includes both example and property based tests. The example tests are used to verify the correctness of the code, while the property-based tests are used to check that the code behaves correctly for a wide range of inputs. Test fixtures where used where appropriate to avoid code duplication. 
Custom generators are used to create random inputs for some of property-based tests. These generators can either be found in the \verb|Test/Generators.lhs| file or as an instance of the \verb|Arbitrary| typeclass alongside the relevant type.
Below will be a couple of our custom generators, followed by a few examples of the tests we have written.
\vspace{10pt}