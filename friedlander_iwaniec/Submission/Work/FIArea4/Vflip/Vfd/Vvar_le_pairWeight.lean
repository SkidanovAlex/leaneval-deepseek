import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.VfdDefs
import Submission.Work.FIArea4.Vflip.Vfd.pairSum_large_sieve
import Submission.Work.FIArea4.Vflip.FlipSetup
import Submission.Work.FIArea4.A4varbounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Expansion of the smooth majorant as a `pairWeight` double sum (FI §12)

We prove that the global variance `Vvar R S D α` is bounded by the real part of the double sum
`Σ_{p,q ∈ [1,2R]×[1,2S]} α_p conj(α_q) · pairWeight D p q`, where `pairWeight` is the `d`-sum of
the smooth majorant over the congruence `r₁s₂ ≡ r₂s₁ (mod d)` — the "expansion of the smooth
majorant" used to set up the flipping-of-moduli argument of Friedlander–Iwaniec's §12.

The route is short: `Vvar` is a sum of nonnegative local variances over `D < d ≤ 2D`, where the
smooth bump `bump (d/D)` equals `1`; extending the range to `1 ≤ d ≤ 3D` (the full support of the
bump) can only increase the sum.  For each `d ≥ 1` the self-pair sum `pairSum R S d α α` is the
complex cast of `Evar R S d α` (the coefficients are supported on odd `r`, so the coprimality
condition of the class decomposition is automatic), and `Σ_d bump (d/D) · pairSum d` is exactly the
target double sum.
-/

/-- The product of the two Jacobi weights of a pair is the single integer cast appearing in
`pairSum`. -/
lemma jw_mul (d a b : ℕ) :
    Work.FIArea4.jw d a * Work.FIArea4.jw d b
      = ((jacobiSym (a : ℤ) (Work.FIPlan.oddPart d)
          * jacobiSym (b : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ) := by
  simp only [Work.FIArea4.jw]
  push_cast
  ring

/-- `pairSum` written as a double sum over the box `[1,2R] × [1,2S]` (with `u = v = α`). -/
lemma pairSum_box_self (R S d : ℕ) (α : ℕ → ℕ → ℂ) :
    Work.FIArea4.pairSum R S d α α
      = ∑ p ∈ (Finset.Icc 1 (2 * R)) ×ˢ (Finset.Icc 1 (2 * S)),
        ∑ q ∈ (Finset.Icc 1 (2 * R)) ×ˢ (Finset.Icc 1 (2 * S)),
          α p.1 p.2 * star (α q.1 q.2) *
            (if ((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d) then
              ((jacobiSym (p.1 : ℤ) (Work.FIPlan.oddPart d)
                * jacobiSym (q.1 : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
             else 0) := by
  simp only [Work.FIArea4.pairSum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun s1 _ =>
    Finset.sum_congr rfl (fun r2 _ => Finset.sum_congr rfl (fun s2 _ => ?_))))
  by_cases h : ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- For `α` supported on odd `r` and `1 ≤ d`, the self-pair sum is the complex cast of the local
variance `Evar R S d α`. -/
lemma pairSum_self_eq_Evar (R S d : ℕ) (hd : 1 ≤ d) (α : ℕ → ℕ → ℂ)
    (hodd : ∀ r s, α r s ≠ 0 → Odd r) :
    Work.FIArea4.pairSum R S d α α = ((Work.FIPlan.Evar R S d α : ℝ) : ℂ) := by
  rw [pairSum_eq_trunc R S d α α hodd hodd hd]
  rw [Work.FIArea4.pairSum_decomp R S d (by omega) _ _
      (truncCoeff_coprime d α) (truncCoeff_coprime d α)]
  rw [Work.FIArea4.Evar_eq_sum_normSq_clsSum]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [clsSum_truncCoeff]
  exact Complex.mul_conj _

/-- The target double sum equals the `d`-sum of `bump (d/D) · pairSum R S d α α`. -/
lemma target_eq_pairWeight_dsum (R S D : ℕ) (α : ℕ → ℕ → ℂ) :
    (∑ p ∈ (Finset.Icc 1 (2 * R)) ×ˢ (Finset.Icc 1 (2 * S)),
      ∑ q ∈ (Finset.Icc 1 (2 * R)) ×ˢ (Finset.Icc 1 (2 * S)),
        α p.1 p.2 * star (α q.1 q.2) * Work.FIArea4.Vflip.pairWeight D p q)
      = ∑ d ∈ Finset.Icc 1 (3 * D),
          (Work.FIArea4.Vflip.bump ((d : ℝ) / D) : ℂ) *
            Work.FIArea4.pairSum R S d α α := by
  have key : ∀ d : ℕ,
      (∑ p ∈ (Finset.Icc 1 (2 * R)) ×ˢ (Finset.Icc 1 (2 * S)),
        ∑ q ∈ (Finset.Icc 1 (2 * R)) ×ˢ (Finset.Icc 1 (2 * S)),
          α p.1 p.2 * star (α q.1 q.2) *
            (if ((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d) then
              ((jacobiSym (p.1 : ℤ) (Work.FIPlan.oddPart d)
                * jacobiSym (q.1 : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
             else 0)) = Work.FIArea4.pairSum R S d α α :=
    fun d => (pairSum_box_self R S d α).symm
  simp only [Work.FIArea4.Vflip.pairWeight, jw_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [← key d]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  ring

/-- The smooth majorant over the full support of the bump: the variance is at most the
`bump (d/D)`-weighted sum of local variances over *all* `1 ≤ d ≤ 3D`. -/
lemma Vvar_le_bump_majorant_threeD (R S D : ℕ) (hD : 1 ≤ D) (α : ℕ → ℕ → ℂ) :
    Work.FIPlan.Vvar R S D α ≤
      ∑ d ∈ Finset.Icc 1 (3 * D),
        Work.FIArea4.Vflip.bump ((d : ℝ) / D) * Work.FIPlan.Evar R S d α := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hle : (∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d α)
      ≤ ∑ d ∈ Finset.Ioc D (2 * D),
          Work.FIArea4.Vflip.bump ((d : ℝ) / D) * Work.FIPlan.Evar R S d α := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    rw [Finset.mem_Ioc] at hd
    have h1 : (1 : ℝ) ≤ (d : ℝ) / D := by
      rw [le_div_iff₀ hDpos]
      have : ((D : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : D ≤ d)
      linarith
    have h2 : (d : ℝ) / D ≤ 2 := by
      rw [div_le_iff₀ hDpos]
      have : (d : ℝ) ≤ ((2 * D : ℕ) : ℝ) := by exact_mod_cast (by omega : d ≤ 2 * D)
      push_cast at this
      linarith
    rw [Work.FIArea4.Vflip.bump_eq_one h1 h2, one_mul]
  rw [Work.FIPlan.Vvar]
  refine hle.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro d hd
    rw [Finset.mem_Ioc] at hd
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro d _ _
    exact mul_nonneg (Work.FIArea4.Vflip.bump_nonneg _) (Work.FIArea4.Vflip.Evar_nonneg R S d α)

/-- **Expansion of the smooth majorant as a `pairWeight` double sum** (FI §12). -/
theorem Vvar_le_pairWeight (R S D : ℕ) (hD : 1 ≤ D) (α : ℕ → ℕ → ℂ)
    (hodd : ∀ r s, α r s ≠ 0 → Odd r) :
    Work.FIPlan.Vvar R S D α ≤
      (∑ p ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S),
        ∑ q ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S),
          α p.1 p.2 * star (α q.1 q.2) * Work.FIArea4.Vflip.pairWeight D p q).re := by
  rw [target_eq_pairWeight_dsum R S D α, Complex.re_sum]
  have hterm : ∀ d ∈ Finset.Icc 1 (3 * D),
      ((Work.FIArea4.Vflip.bump ((d : ℝ) / D) : ℂ) * Work.FIArea4.pairSum R S d α α).re
        = Work.FIArea4.Vflip.bump ((d : ℝ) / D) * Work.FIPlan.Evar R S d α := by
    intro d hd
    rw [pairSum_self_eq_Evar R S d (Finset.mem_Icc.mp hd).1 α hodd, Complex.re_ofReal_mul,
      Complex.ofReal_re]
  rw [Finset.sum_congr rfl hterm]
  exact Vvar_le_bump_majorant_threeD R S D hD α

end

end Work.FIArea4.Vflip.Vfd
