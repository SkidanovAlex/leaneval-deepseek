import Mathlib
import Submission.Work.HP.WedgeDefs
import Submission.Work.HP.tau_basic

/-!
# Covolume of `(x, k•x + m•w)`

The covolume `wedgeNorm` (equivalently `wedgeR`) of a pair of vectors is the square root of the
2×2 Gram determinant.  Since the Gram determinant is multilinear in its arguments and vanishes
on a repeated vector, the pair `(x, k•x + m•w)` has Gram determinant `m²` times that of `(x, w)`:

`√(‖x‖²‖k x + m w‖² − ⟨x, k x + m w⟩²) = √(m² · (‖x‖²‖w‖² − ⟨x,w⟩²)) = |m| √(‖x‖²‖w‖² − ⟨x,w⟩²)`.

For `m ≥ 0` this is `m · wedgeR x w`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.D2M

variable {ι : Type*} [Fintype ι]

/-! ## Elementary bilinearity of `dotR` -/

lemma dotR_add_left' (v w u : ι → ℝ) : dotR (v + w) u = dotR v u + dotR w u := by
  simp only [dotR, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dotR_smul_left' (c : ℝ) (v w : ι → ℝ) : dotR (c • v) w = c * dotR v w := by
  simp only [dotR, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotR_self_eq_rNorm_sq (v : ι → ℝ) : dotR v v = rNorm v ^ 2 := by
  rw [rNorm_sq, dotR]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## The shear identity for the real covolume -/

lemma rNorm_add_smul_sq (v w : ι → ℝ) (k m : ℝ) :
    rNorm (k • v + m • w) ^ 2
      = k ^ 2 * rNorm v ^ 2 + (2 * k * m) * dotR v w + m ^ 2 * rNorm w ^ 2 := by
  rw [rNorm_sq, rNorm_sq, rNorm_sq, dotR]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma dotR_self_add_smul (v w : ι → ℝ) (k m : ℝ) :
    dotR v (k • v + m • w) = k * rNorm v ^ 2 + m * dotR v w := by
  rw [dotR_add_right, dotR_smul_right, dotR_smul_right, dotR_self_eq_rNorm_sq]

theorem wedgeR_smul_add (v w : ι → ℝ) (k m : ℝ) (hm : 0 ≤ m) :
    wedgeR v (k • v + m • w) = m * wedgeR v w := by
  have h1 := rNorm_add_smul_sq v w k m
  have h2 := dotR_self_add_smul v w k m
  have hid : rNorm v ^ 2
        * (k ^ 2 * rNorm v ^ 2 + (2 * k * m) * dotR v w + m ^ 2 * rNorm w ^ 2)
        - (k * rNorm v ^ 2 + m * dotR v w) ^ 2
      = m ^ 2 * (rNorm v ^ 2 * rNorm w ^ 2 - dotR v w ^ 2) := by ring
  simp only [wedgeR, h1, h2, hid, Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hm]

/-! ## The integral statement -/

theorem wedgeNorm_eq_of_smul_add {ι : Type*} [Fintype ι] (x w : ι → ℤ)
    (k m : ℤ) (hm : 0 ≤ m) :
    Work.HP.wedgeNorm x (k • x + m • w) = (m : ℝ) * Work.HP.wedgeNorm x w := by
  have ht : toR (k • x + m • w) = (k : ℝ) • toR x + (m : ℝ) • toR w := by
    ext i
    simp only [toR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [wedgeNorm_eq_wedgeR, ht, wedgeR_smul_add _ _ _ _ (by exact_mod_cast hm),
    ← wedgeNorm_eq_wedgeR]

end Work.HP.D2M
