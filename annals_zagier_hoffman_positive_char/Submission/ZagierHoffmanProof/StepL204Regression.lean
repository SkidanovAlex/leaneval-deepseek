import Submission.ZagierHoffmanProof.StepL204

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Regression checks for StepL204 (`d(w) > 0`, non-emptiness/finiteness of the spanning sets)

Instantiated at `F = ZMod 2` and `F = ZMod 3`.
-/

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

example : 0 < d (ZMod 2) 0 := d_pos (ZMod 2) 0
example : 0 < d (ZMod 2) 7 := d_pos (ZMod 2) 7
example : 0 < d (ZMod 3) 5 := d_pos (ZMod 3) 5
example : 0 < d (ZMod 3) 100 := d_pos (ZMod 3) 100

example : (𝒯 (ZMod 2) 4).Nonempty := T_nonempty (ZMod 2) 4 (by norm_num)
example : (𝒯0 (ZMod 2) 4).Nonempty := T0_nonempty (ZMod 2) 4 (by norm_num)
example : (𝒯 (ZMod 3) 5).Nonempty := T_nonempty (ZMod 3) 5 (by norm_num)
example : (𝒯0 (ZMod 3) 5).Nonempty := T0_nonempty (ZMod 3) 5 (by norm_num)

example : 0 < Set.ncard (𝒯 (ZMod 2) 4) := ncard_T_pos (ZMod 2) 4 (by norm_num)
example : 0 < Set.ncard (𝒯0 (ZMod 3) 5) := ncard_T0_pos (ZMod 3) 5 (by norm_num)

example : 𝒵 (ZMod 3) 4 ≠ (⊥ : Submodule (RatFunc (ZMod 3)) (RatFunc.CompletionAtInfty (ZMod 3))) :=
  Z_ne_bot (ZMod 3) 4 (by norm_num)

example : 0 < Module.rank (RatFunc (ZMod 2)) (𝒵 (ZMod 2) 6) :=
  rank_Z_pos (ZMod 2) 6 (by norm_num)

end ZagierHoffmanPositiveChar
