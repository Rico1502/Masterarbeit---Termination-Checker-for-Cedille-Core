# Cedille Core Checker extended by termination checker using the type inference algorithm

### Index (src):
*  Check.hs                     Type checking
*  CedilleCore.hs               Main I/O
*  Norm.hs                      (Head-)Normalizing, erasing, and substituting functions
*  Parser.hs                    Parser
*  Trie.hs                      Trie datatype and related functions
*  Types.hs                     Definitions of fundamental types for terms/types/kinds
*  ElaborationChecker(N/MP).hs  Type Inference algorithm
*  Core.hs                      Old Cedille Core, Main.hs still uses syntax of this implementation
*  CoreToPrim.hs                Conversion functions Cedille <-> TrmP       
*  Elaboration.hs               Elaboration Datatype
*  StrictType.hs                StrictType and Intersection datatypes
*  StrictTypeTransform.hs       Unification
