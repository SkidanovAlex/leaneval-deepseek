import Submission.ZagierHoffmanProof.StepC
set_option autoImplicit false
set_option maxHeartbeats 100000000
/-!
# Step L70: weight of a depth-1 tuple is its single entry (SESSION 224)

The pure fact needed by the per-member `e` dispatch's depth-1 exclusion
(kAdm_one_iff_front's `hdepth : dep = 1 → pad0 m 0 ≠ q`): a tuple of depth 1 has
weight equal to its single (front) entry.
  ★ weight_one_eq_pad0 (m : Fin 1 → ℕ+) : weight 1 m = pad0 m 0
  ★ weight_dep_one_eq_pad0 {dep} (m : Fin dep → ℕ+) (hd : dep = 1) :
      weight dep m = pad0 m 0   [subst + the base case]
F-free; module import is only StepC (pad0/weight).  In q_type3_member_e's ¬2-adm
branch this transports `weight (Q.dep …) m = pad0 m 0` under `Q.dep … = 1`, so the
contradiction `weight = pad0 m 0 = q` vs `weight = w ≥ q+2` (case1_weight_ge_q_add_two)
closes the depth-1 exclusion.  Named gates unchanged.
-/

namespace ZagierHoffmanPositiveChar

/-- A depth-1 tuple has weight equal to its single (front) entry. -/
lemma weight_one_eq_pad0 (m : Fin 1 → ℕ+) : weight 1 m = pad0 m 0 := by
  classical
  have hp : pad0 m 0 = (m ⟨0, by omega⟩ : ℕ) := pad0_of_lt m (by omega : 0 < 1)
  rw [hp]
  rw [weight]
  simp

/-- Under `dep = 1`, a tuple's weight is its single (front) entry. -/
lemma weight_dep_one_eq_pad0 {dep : ℕ} (m : Fin dep → ℕ+) (hd : dep = 1) :
    weight dep m = pad0 m 0 := by
  subst dep
  exact weight_one_eq_pad0 m

end ZagierHoffmanPositiveChar
