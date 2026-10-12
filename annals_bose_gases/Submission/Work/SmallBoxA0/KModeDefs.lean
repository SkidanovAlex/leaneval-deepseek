import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import ChallengeDeps
import Submission.Work.SmallBoxModeParseval
import Submission.Work.SmallBoxSpectral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The normalised box-Neumann modes as smooth functions, and their basic algebra

`Work.SmallBoxA0.kModeWord_le_kinWord` needs the box-Neumann kinetic word
`kMode s c hs f = Σ_k [π‖k‖/s − c]₊²·‖⟨ê_k, f⟩‖²` dominated by the honest
Dirichlet energy of a smooth function on the centred cube `acube s`.

The modes `ê_k = boxModeOrtho s hs k` of `SmallBoxL2Modes` are `Lp ℝ 2 (boxVol s)`
elements; for the spectral inequality one needs a *genuine* smooth function
representing `ê_k`, namely

  `bModeF s k z = √(modeW s k) · boxNeumann3 s k z`

(`modeW s k = (∏_j coordSqNorm s (k j))⁻¹`, so `√(modeW s k)` is the inverse of
the `L²`-norm of the raw product mode `boxNeumann3`).  This module collects the
elementary facts: smoothness, the Fréchet derivative, the `L²` pairing with the
raw modes (`∫ bN3_k · bN3_l = δ_{kl} ∏_j (s or s/2)`), and the identification of
the Hilbert-space inner product `⟨ê_k, toLp g⟩` with `∫ bModeF s k · g`.
-/

namespace Work.SmallBoxA0

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Smoothness of the raw product mode as a function on `ℝ³`. -/
lemma contDiff_boxNeumann3 (s : ℝ) (k : Fin 3 → ℕ) :
    ContDiff ℝ ∞ (fun z : ℝ³ => boxNeumann3 s k z) := by
  unfold boxNeumann3 boxNeumann
  fun_prop

/-- The normalised box-Neumann mode `ê_k` as a genuine function on `ℝ³`:
`bModeF s k z = √(modeW s k) · boxNeumann3 s k z`. -/
noncomputable def bModeF (s : ℝ) (k : Fin 3 → ℕ) (z : ℝ³) : ℝ :=
  Real.sqrt (modeW s k) * boxNeumann3 s k z

lemma bModeF_apply (s : ℝ) (k : Fin 3 → ℕ) (z : ℝ³) :
    bModeF s k z = Real.sqrt (modeW s k) * boxNeumann3 s k z := rfl

lemma bModeF_contDiff (s : ℝ) (k : Fin 3 → ℕ) : ContDiff ℝ ∞ (bModeF s k) := by
  rw [show bModeF s k
      = fun z : ℝ³ => Real.sqrt (modeW s k) * boxNeumann3 s k z from rfl]
  exact contDiff_const.mul (contDiff_boxNeumann3 s k)

lemma fderiv_bModeF_apply (s : ℝ) (k : Fin 3 → ℕ) (z v : ℝ³) :
    fderiv ℝ (bModeF s k) z v
      = Real.sqrt (modeW s k) * fderiv ℝ (fun w : ℝ³ => boxNeumann3 s k w) z v := by
  have hd : DifferentiableAt ℝ (fun w : ℝ³ => boxNeumann3 s k w) z :=
    (contDiff_boxNeumann3 s k).differentiable (by norm_num) z
  rw [show bModeF s k
      = fun w : ℝ³ => Real.sqrt (modeW s k) * boxNeumann3 s k w from rfl]
  rw [fderiv_const_mul hd]
  rfl

/-- The squared norm of the raw product mode is `∏_j coordSqNorm s (k j)`, so
`modeW s k` times it is `1`. -/
lemma modeW_mul_coordSqNorm {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) :
    modeW s k * ∏ j : Fin 3, coordSqNorm s (k j) = 1 := by
  rw [modeW]
  have hpos : 0 < ∏ j : Fin 3, coordSqNorm s (k j) :=
    Finset.prod_pos (fun j _ => coordSqNorm_pos hs (k j))
  field_simp

lemma sqrt_modeW_sq {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) :
    Real.sqrt (modeW s k) ^ 2 = modeW s k :=
  Real.sq_sqrt (modeW_nonneg hs k)

lemma sqrt_modeW_ne_zero {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) :
    Real.sqrt (modeW s k) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (modeW_pos hs k))

/-- **The `L²` pairing of the raw product modes** over the centred cube:
`∫_{cube} bN3_k · bN3_l = δ_{kl} ∏_j coordSqNorm s (k j)`. -/
lemma boxNeumann3_pair_integral {s : ℝ} (hs : 0 < s) (k l : Fin 3 → ℕ) :
    (∫ z in acube s, boxNeumann3 s k z * boxNeumann3 s l z)
      = if k = l then ∏ j : Fin 3, coordSqNorm s (k j) else 0 := by
  have h := boxInner_eq_boxIntegral s k l
  rw [show (∫ z : ℝ³, boxNeumann3 s k z * boxNeumann3 s l z ∂(boxVol s))
      = ∫ z in acube s, boxNeumann3 s k z * boxNeumann3 s l z from rfl] at h
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, ← h, boxMode_inner_self_coord hs k]
  · rw [if_neg hkl, ← h, boxMode_inner_eq_zero_of_ne hs hkl]

/-- Pulling the normalisation constant out of the box integral. -/
lemma integral_bModeF_mul (s : ℝ) (k : Fin 3 → ℕ) (g : ℝ³ → ℝ) :
    (∫ z in acube s, bModeF s k z * g z)
      = Real.sqrt (modeW s k) * ∫ z in acube s, boxNeumann3 s k z * g z := by
  rw [show (fun z : ℝ³ => bModeF s k z * g z)
      = fun z : ℝ³ => Real.sqrt (modeW s k) * (boxNeumann3 s k z * g z) from by
        funext z; rw [bModeF_apply]; ring]
  exact MeasureTheory.integral_const_mul _ _

/-- **The Hilbert inner product with a normalised mode is the box integral against
`bModeF`**: `⟨ê_k, toLp g⟩ = ∫_{cube} bModeF s k · g`. -/
lemma boxModeOrtho_inner_eq_bModeF {s : ℝ} (hs : 0 < s) {k : Fin 3 → ℕ} {g : ℝ³ → ℝ}
    (hg : MemLp g 2 (boxVol s)) :
    inner ℝ (boxModeOrtho s hs k) (MemLp.toLp g hg)
      = ∫ z in acube s, bModeF s k z * g z := by
  rw [boxModeOrtho_inner_eq hs k hg, integral_bModeF_mul]

end Work.SmallBoxA0
