import Mathlib
import Flows.Walk
import Flows.FlowDefs

/-#
# The Ford Fulkerson method
The ford-fulkerson "method" is simple. It says,
1. Find augmenting paths
2. Augment their flow
3. Repeat until there are no augmenting paths.

Per textbooks and wikipedia this is distinct from
the Edmonds Karp algorithm in the sense that Edmonds-Karp
fills in the unspecified details of the Ford-Fulkerson method,
specifically on how the find augmenting paths.
-/
