import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2SzDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2

open LeanEval.GroupTheory.Defs

/-- Every element of the Suzuki `2`-group `U = szTwoGroupS n` is a root element `u(a,d)`.

This only uses that `szTwoGroupS n` is `szTwoGroup n` (the set `{u(a,b)}` of root
elements) viewed inside `SzModel n`. -/
lemma szUgS_exists_of_mem_center_aux (n : ℕ) (x : ↥(Submission.Sz.szTwoGroupS n)) :
    ∃ a d : Submission.Sz.SzField n, (x : SzModel n) = szUgS n a d := by
  have h : (x : SzModel n) ∈ (Submission.Sz.szTwoGroup n).subgroupOf (SzModel n) := x.2
  have hx : ((x : SzModel n) : GL (Fin 4) (Submission.Sz.SzField n)) ∈
      Submission.Sz.szTwoGroup n := Subgroup.mem_subgroupOf.mp h
  obtain ⟨a, d, had⟩ := hx
  exact ⟨a, d, Subtype.ext (by simpa using had)⟩

/-- The root elements `u(0,b)` are central for the multiplication law of the Suzuki
`2`-group: `u(0,b)` commutes with every root element `u(c,d)`.

Indeed both products collapse, via `szUgS_mul`, to `u(c, b + d)` and `u(c, d + b)`. -/
lemma szUgS_zero_comm (n : ℕ) (b c d : Submission.Sz.SzField n) :
    szUgS n 0 b * szUgS n c d = szUgS n c d * szUgS n 0 b := by
  rw [szUgS_mul, szUgS_mul]
  congr 1
  · rw [zero_add, add_zero]
  · rw [zero_mul, zero_pow (show 2 ^ (n + 1) ≠ 0 by positivity), mul_zero]
    ring

lemma szUgS_zero_mem_center (n : ℕ) (b : Submission.Sz.SzField n) :
    (⟨szUgS n 0 b, szUgS_mem_U n 0 b⟩ : ↥(Submission.Sz.szTwoGroupS n)) ∈
      Subgroup.center ↥(Submission.Sz.szTwoGroupS n) := by
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  obtain ⟨a, d, had⟩ := szUgS_exists_of_mem_center_aux n g
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [had]
  exact (szUgS_zero_comm n b a d).symm

end Work.BSLit.BenderFacts2
