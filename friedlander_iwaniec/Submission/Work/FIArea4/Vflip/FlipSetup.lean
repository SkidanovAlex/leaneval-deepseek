import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.Assembly
import Submission.Work.FIPlan.Interface

/-!
# Set-up for the "flipping of moduli" (Friedlander–Iwaniec §12): the smooth majorant

This module contains the two elementary ingredients that the large-moduli bound
`Vflip_large` (FI Proposition 12.1 in the range `R*S < D*D`) starts from:

* `bump`, a smooth bump `ℝ → ℝ` with `bump y = 1` for `1 ≤ y ≤ 2` and `bump y = 0` for `y ≤ 1/2`
  or `5/2 ≤ y` (built from `Real.smoothTransition`, hence `C^∞`);
* the **smooth majorant** (12.6): since `bump (d/D) = 1` on the dyadic range `D < d ≤ 2D` and all
  the summands `Evar R S d α` are nonnegative, the variance `V(D) = Σ_{D<d≤2D} E(d)` is at most
  `Σ_{1 ≤ d ≤ 2D} bump (d/D) * E(d)`, the sum now running over *all* `d ≤ 2D` — which is what makes
  the change of variables `d ↦ Δ/d` (`Δ = r₁ s₂ - r₂ s₁`) possible.
-/

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The smooth bump -/

/-- The smooth bump `bump y = st(2y-1)·st(5-2y)` of `Real.smoothTransition`: it equals `1` on the
interval `[1,2]` and vanishes outside `(1/2, 5/2)`. -/
def bump (y : ℝ) : ℝ := Real.smoothTransition (2 * y - 1) * Real.smoothTransition (5 - 2 * y)

lemma bump_nonneg (y : ℝ) : 0 ≤ bump y :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma bump_le_one (y : ℝ) : bump y ≤ 1 := by
  have h1 := Real.smoothTransition.le_one (2 * y - 1)
  have h2 := Real.smoothTransition.le_one (5 - 2 * y)
  have h1' := Real.smoothTransition.nonneg (2 * y - 1)
  have h2' := Real.smoothTransition.nonneg (5 - 2 * y)
  rw [bump]
  nlinarith

lemma bump_eq_one {y : ℝ} (h1 : 1 ≤ y) (h2 : y ≤ 2) : bump y = 1 := by
  rw [bump, Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 2 * y - 1 by linarith),
    Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 5 - 2 * y by linarith), mul_one]

lemma bump_eq_zero_of_le {y : ℝ} (h : y ≤ 1 / 2) : bump y = 0 := by
  rw [bump, Real.smoothTransition.zero_of_nonpos (show 2 * y - 1 ≤ 0 by linarith), zero_mul]

lemma bump_eq_zero_of_ge {y : ℝ} (h : 5 / 2 ≤ y) : bump y = 0 := by
  rw [bump, Real.smoothTransition.zero_of_nonpos (show 5 - 2 * y ≤ 0 by linarith), mul_zero]

lemma contDiff_bump : ContDiff ℝ (⊤ : ℕ∞) bump := by
  unfold bump
  exact ContDiff.mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => 2 * y - 1)))
    ((Real.smoothTransition.contDiff (n := ⊤)).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => 5 - 2 * y)))

/-! ## Nonnegativity of the local variance -/

/-- `Evar` is a sum of squared moduli, hence nonnegative. -/
lemma Evar_nonneg (R S d : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ Work.FIPlan.Evar R S d α := by
  rw [Work.FIPlan.Evar]
  exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)

/-- `p14L2` is nonnegative. -/
lemma p14L2_nonneg (R S : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ Work.FIArea4.p14L2 R S α := by
  rw [Work.FIArea4.p14L2]
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

/-- `p14Ener` is nonnegative. -/
lemma p14Ener_nonneg (R S : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ Work.FIArea4.p14Ener R S α := by
  rw [Work.FIArea4.p14Ener]
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)))

/-- `p14L2 ≤ p14Ener`, since `1 ≤ τ(r) = r.divisors.card` for `r ≥ 1`. -/
lemma p14L2_le_p14Ener (R S : ℕ) (α : ℕ → ℕ → ℂ) :
    Work.FIArea4.p14L2 R S α ≤ Work.FIArea4.p14Ener R S α := by
  rw [Work.FIArea4.p14L2, Work.FIArea4.p14Ener]
  refine Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun s _ => ?_))
  rw [Finset.mem_Icc] at hr
  have hcard : (1 : ℝ) ≤ ((r.divisors.card : ℕ) : ℝ) := by
    have hr1 : r ≠ 0 := by omega
    have h1 : 1 ∈ r.divisors := by rw [Nat.mem_divisors]; exact ⟨one_dvd r, hr1⟩
    have : 1 ≤ r.divisors.card := Finset.card_pos.mpr ⟨1, h1⟩
    exact_mod_cast this
  nlinarith [Complex.normSq_nonneg (α r s)]

/-! ## The smooth majorant (12.6) -/

/-- **The smooth majorant of Friedlander–Iwaniec (12.6).**  Since `bump (d/D) = 1` for
`D < d ≤ 2D` and every summand is nonnegative, the variance is bounded by the `bump`-weighted sum
over all moduli `d ≤ 2D`. -/
theorem Vvar_le_bump_majorant (R S D : ℕ) (hD : 1 ≤ D) (α : ℕ → ℕ → ℂ) :
    Work.FIPlan.Vvar R S D α ≤
      ∑ d ∈ Finset.Icc 1 (2 * D), bump ((d : ℝ) / D) * Work.FIPlan.Evar R S d α := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hle : (∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d α)
      ≤ ∑ d ∈ Finset.Ioc D (2 * D),
          bump ((d : ℝ) / D) * Work.FIPlan.Evar R S d α := by
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
    rw [bump_eq_one h1 h2, one_mul]
  rw [Work.FIPlan.Vvar]
  refine hle.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro d hd
    rw [Finset.mem_Ioc] at hd
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro d _ _
    exact mul_nonneg (bump_nonneg _) (Evar_nonneg R S d α)


/-! ## Reduction of the Jacobi weight by the common divisor of the pair -/

/-- If `(c,d) = 1` then replacing both moduli of a pair by `c`-multiples does not change the
product of the Jacobi weights `(r | d')`: `(c r₁|d')(c r₂|d') = (r₁|d')(r₂|d')`, because
`(c|d')² = 1`.  This is the reduction of the pair `(r₁,r₂) = c` to the coprime pair
`(r₁,r₂)` used before the reciprocity flip (`jacobiSym_oddPart_flip`). -/
lemma jacobiSym_prod_mul_left {c r1 r2 d : ℕ} (hcop : Nat.Coprime c d) :
    jacobiSym ((c * r1 : ℕ) : ℤ) (Work.FIPlan.oddPart d)
        * jacobiSym ((c * r2 : ℕ) : ℤ) (Work.FIPlan.oddPart d)
      = jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d)
        * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d) := by
  have h : (c : ℤ).gcd (Work.FIPlan.oddPart d) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact (hcop.coprime_dvd_right (Work.FIArea4.oddPart_dvd d)).gcd_eq_one
  have h2 : jacobiSym (c : ℤ) (Work.FIPlan.oddPart d) ^ 2 = 1 := jacobiSym.sq_one h
  rw [show ((c * r1 : ℕ) : ℤ) = (c : ℤ) * (r1 : ℤ) by push_cast; ring,
    show ((c * r2 : ℕ) : ℤ) = (c : ℤ) * (r2 : ℤ) by push_cast; ring,
    jacobiSym.mul_left, jacobiSym.mul_left]
  calc (jacobiSym (c : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d))
        * (jacobiSym (c : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d))
      = jacobiSym (c : ℤ) (Work.FIPlan.oddPart d) ^ 2
        * (jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d)) := by
        ring
    _ = jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d) := by
        rw [h2, one_mul]

end

end Work.FIArea4.Vflip
