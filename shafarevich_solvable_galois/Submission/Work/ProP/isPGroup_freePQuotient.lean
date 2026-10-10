import Mathlib.GroupTheory.PGroup
import Submission.Work.ProP.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- For every element `x` of a group and every `ν`, the `p ^ ν`-th power of `x` lies in the
`ν`-th term of the descending `p`-central series: `x ^ p ^ ν ∈ P_ν`.

Proof by induction on `ν`.  For `ν = 0` we have `x ^ p ^ 0 = x ∈ ⊤ = P_0`.  For the step,
`x ^ p ^ (ν+1) = (x ^ p ^ ν) ^ p` lies in `P_{ν+1}` by the induction hypothesis and
`Work.Shrinking.pow_mem_pCentralSeries_succ`. -/
theorem pow_pow_mem_pCentralSeries (p : ℕ) (P : Type*) [Group P] (ν : ℕ) (x : P) :
    x ^ p ^ ν ∈ Work.Shrinking.pCentralSeries p P ν := by
  induction ν with
  | zero => simp
  | succ ν ih =>
      have h : x ^ p ^ (ν + 1) = (x ^ p ^ ν) ^ p := by rw [pow_succ, pow_mul]
      rw [h]
      exact Work.Shrinking.pow_mem_pCentralSeries_succ p P ih

/-- The generic kernel quotients `F^(n)/F^(n)(ν)` are `p`-groups.

Proof: every element of `FreeGroup (Fin n) ⧸ F^(n)(ν)` satisfies `y ^ p ^ ν = 1`, because
`x ^ p ^ ν ∈ pCentralSeries p (FreeGroup (Fin n)) ν` for every `x` (induction on `ν`: the step is
`(x ^ p ^ ν) ^ p ∈ P_ν ^ p ≤ P_{ν+1}`), which is exactly the defining property of `IsPGroup p`
with the single witness `k = ν` (`isPGroup_iff_pow_pow_eq_one`).  Note that the exponent is
`p ^ ν`, not `p ^ (ν - 1)`: `F^(n)(1) = Φ_p(F^(n))` already has exponent `p` (its order is
`p ^ n`, `Work.ProP.card_freePQuotient_one`).  No finiteness of the quotient is needed. -/
theorem isPGroup_freePQuotient {p : ℕ} [Fact p.Prime] (n ν : ℕ) :
    IsPGroup p (FreePQuotient p n ν) := by
  refine fun y => ⟨ν, ?_⟩
  obtain ⟨x, rfl⟩ := freePQuotientMk_surjective p n ν y
  rw [← map_pow, freePQuotientMk_apply, QuotientGroup.eq_one_iff]
  exact pow_pow_mem_pCentralSeries p (FreeGroup (Fin n)) ν x

end Work.ProP
