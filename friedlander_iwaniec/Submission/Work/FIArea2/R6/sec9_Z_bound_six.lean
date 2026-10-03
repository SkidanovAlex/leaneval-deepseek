/-
# `FIArea2/R6/sec9_Z_bound_six.lean` — the §9 per-frequency bound at the sector-scale threshold

This is the sector-scale companion of `Submission/Work/FIArea2/sec9_Z_bound_eight.lean`: the
per-frequency weight sum of *FI* (9.5)

  `Z(h₁,h₂) = Σ_{axis-free (z₁,z₂) ∈ B²} τ(Δ)³|Δ|⁻¹(Λ,Δ)`,  `Λ = z₁h₁² − z₂h₂²`, `Δ = Im(z̄₁z₂)`,

is bounded by `C ϑ⁻¹ (log N + 2)⁸ · U(h₁,h₂)` where `U = sec9Usumming` is the weighted
`(u₁,u₂)`-sum `Σ (u₁,u₂)τ₄(u₁h₁² − u₂h₂²)`, and where *axis-free* is the **sector-scale** exclusion
`Work.FITop4.IsAxisFree`, i.e. `ϑ√N < |Re z|, |Im z|` — the threshold carried by the round-6
coefficient family `Defs6.IsBetaCoeff6` (see `Submission/Work/FIArea2/R6/SixDefs.lean`).

The proof is a three-line composition of two independent pieces:

* `sec9Zsum6_le_ZBsix` — the rewriting of (9.5) into the four-fold coordinate sum
  `Work.FIArea2.Count.ZB (radN Pa) h₁ h₂ (ϑ√N)` (dropping the coprimality indicator);
* `sector_ZB_bound_six` — the arithmetic core at the sector-scale threshold: `ZB` at
  `thr = ϑ√Nr` is at most `C ϑ⁻¹ (log(Nr+2))⁸ · UB`, obtained from the two `_eight` theorems
  (`ZAc_bound_eight`, `ZBc_bound_eight`, which are stated for the threshold `√(ϑNr)` and produce
  `ϑ^{-1/2}`) by the substitution `ϑ ↦ ϑ²`: `√(ϑ²Nr) = ϑ√Nr` and `(ϑ²)^{-1/2} = ϑ⁻¹`.

The remaining assembly below is the bookkeeping: the `(Λ,Δ)`-bound `DmN` on the box, the
identification `UB (radN Pa) h₁ h₂ = sec9Usumming Pa h₁ h₂`, the logarithmic comparison
`log(N+2) ≤ log N + 2`, and the monotonicity of multiplication by the non-negative factor
`C ϑ⁻¹ (log(N+2))⁸`.
-/
import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.R6.sec9Zsum6_le_ZBsix
import Submission.Work.FIArea2.R6.sector_ZB_bound_six
import Submission.Work.FIArea2.Count.ZAc_bound_eight
import Submission.Work.FIArea2.Count.ZBc_bound_eight
import Submission.Work.FIArea2.Count.sec9Zsum_le_ZB
import Submission.Work.FIArea2.Count.sec9_Z_params

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `sec9Usumming` is a sum of non-negative terms (the `(u₁,u₂)`-weight is a gcd, the inside is a
fourth power of a `dividors.card`, both cast from `ℕ`). -/
private lemma sec9Usumming_nonneg_six (Pa : Work.FITop.Params) (h1 h2 : ℤ) :
    0 ≤ Work.FIArea2.sec9Usumming Pa h1 h2 := by
  unfold Work.FIArea2.sec9Usumming
  refine Finset.sum_nonneg fun u1 _ => Finset.sum_nonneg fun u2 _ => ?_
  exact mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **The §9 per-frequency bound at the sector-scale axis threshold.**  There is an absolute
constant `C > 0` with

  `Σ_{(z₁,z₂) coprime, ϑ√N-axis-free} τ(Δ)³(Λ,Δ)|Δ|⁻¹ ≤ C ϑ⁻¹ (log N + 2)⁸ U(h₁,h₂)`

for every `Pa` and every `(h₁,h₂) ≠ (0,0)`.  The factor is `ϑ⁻¹` (not `ϑ^{-1/2}`) because the
sector-scale exclusion `ϑ√N < |Re z|, |Im z|` gives the counting factor `(2R+1)/|r₁| ≤ 8ϑ⁻¹`, and
it is exactly the `ϑ^{-1}` of the paper's (9.10). -/
theorem sec9_Z_bound_six :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (h1 h2 : ℤ), h1 ≠ 0 ∨ h2 ≠ 0 →
      Work.FIArea2.R6.sec9Zsum6 Pa h1 h2
      ≤ C * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ (8 : ℕ) * Work.FIArea2.sec9Usumming Pa h1 h2 := by
  obtain ⟨C, hCpos, hC⟩ := sector_ZB_bound_six
  refine ⟨C, hCpos, ?_⟩
  intro Pa h1 h2 hh
  -- the `(Λ,Δ)`-bound `cdg ≤ DmN` on the whole coordinate box
  have hcdg : ∀ r1 ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa),
      ∀ s1 ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa),
      ∀ r2 ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa),
      ∀ s2 ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa),
      Work.FIArea2.Count.cdg h1 h2 r1 s1 r2 s2 ≤ Work.FIArea2.Count.DmN (Work.FITop.radN Pa) h1 h2 :=
    fun r1 hr1 s1 hs1 r2 hr2 s2 hs2 =>
      Work.FIArea2.Count.cdg_le_DmN h1 h2 r1 s1 r2 s2 hr1 hs1 hr2 hs2
  -- the arithmetic core at the sector-scale threshold `thr = ϑ√N`
  have hZB := hC (Work.FITop.radN Pa) h1 h2 (Pa.ϑ * Real.sqrt Pa.N) Pa.N Pa.ϑ
    (Work.FIArea2.Count.DmN (Work.FITop.radN Pa) h1 h2)
    Pa.hϑ0 (le_of_lt (Work.FIArea2.Count.thetaU_lt_one Pa)) Pa.hN1
    (Work.FIArea2.Count.radN_nonneg Pa) rfl (Work.FIArea2.Count.radN_bound Pa)
    (Work.FIArea2.Count.one_le_DmN _ h1 h2) hh hcdg
  rw [Work.FIArea2.Count.UB_eq_sec9Usumming Pa h1 h2] at hZB
  -- `log(N+2) ≤ log N + 2`, and the comparison of the two eighth powers
  have hlogN2 : Real.log (Pa.N + 2) ≤ Real.log Pa.N + 2 :=
    Work.FIArea2.Count.log_add_two_le_add Pa.N Pa.hN1
  have hbase : (0 : ℝ) ≤ Real.log (Pa.N + 2) := Real.log_nonneg (by linarith [Pa.hN1])
  have hL : (Real.log (Pa.N + 2)) ^ (8 : ℕ) ≤ (Real.log Pa.N + 2) ^ (8 : ℕ) :=
    pow_le_pow_left₀ hbase hlogN2 8
  have hUBnn : 0 ≤ Work.FIArea2.sec9Usumming Pa h1 h2 := sec9Usumming_nonneg_six Pa h1 h2
  have hXnn : (0 : ℝ) ≤ C * Pa.ϑ⁻¹ := mul_nonneg hCpos.le (inv_nonneg.mpr Pa.hϑ0.le)
  have hstep : C * Pa.ϑ⁻¹ * (Real.log (Pa.N + 2)) ^ (8 : ℕ) * Work.FIArea2.sec9Usumming Pa h1 h2
      ≤ C * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ (8 : ℕ) * Work.FIArea2.sec9Usumming Pa h1 h2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hXnn) hUBnn
  exact le_trans (le_trans (sec9Zsum6_le_ZBsix Pa h1 h2) hZB) hstep

end

end Work.FIArea2.R6
