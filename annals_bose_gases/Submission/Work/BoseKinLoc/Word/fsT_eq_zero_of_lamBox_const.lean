import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.tsupport_bsWin_subset_bsBox
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Word.fsT_eq_zero_of_lamBox_const`

If a one-body state `ψ` is constant (`= c`) on the moving box `Λ(u) = lamBox ℓ u`, then every
one of the four kinetic words of FS `eq:DefT` vanishes, hence `fsT ℓ d s εT b u ψ = 0`:

* the box mean `bsMean ℓ u ψ` equals `c` (the mean of a constant over a box of volume `ℓ³`),
  so `Q_uψ = bsQ ℓ u ψ` vanishes pointwise on `Λ(u)`;
* `gapWord` is the `L²`-norm of `Q_uψ` on `Λ(u)`, hence `0`;
* `neuWord` is `sInf` of a set of nonnegative numbers containing `0`, hence `0`;
* `momWord` and `mainWord` are Fourier forms of the *zero* function (`Q_uψ = 0` on `Λ(u)`
  and the window/indicator vanishes off `Λ(u)`).

The auxiliary lemmas are stated in terms of the corpus vocabulary (`bsMean`, `bsQ`, `bsWin`,
`lamBox`, …) so they apply directly to `Qfree`, `gapBare`, `momForm`, `bsOneBody`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Word

open Submission.BoseGases
open Work.BSKinetic

/-! ## 0. Measurability of the moving box -/

lemma measurableSet_lamBox (ℓ : ℝ) (u : ℝ³) : MeasurableSet (lamBox ℓ u) := by
  show MeasurableSet (bsBox ℓ u)
  rw [bsBox]
  exact (Submission.BoseGases.acube_measurable ℓ).preimage (by fun_prop)

/-! ## 1. The box mean of a constant, and the vanishing of `Q_uψ` on the box -/

/-- If `ψ` is constant `= c` on `Λ(u)`, its box mean is `c`. -/
lemma bsMean_eq_of_lamBox_const {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (h : ∀ z ∈ lamBox ℓ u, ψ z = c) : bsMean ℓ u ψ = c := by
  unfold bsMean
  have hpt : ∀ z ∈ Submission.BoseGases.acube ℓ, ψ (ℓ • u + z) = c := by
    intro z hz
    apply h
    show (ℓ • u + z - ℓ • u) ∈ Submission.BoseGases.acube ℓ
    rwa [add_sub_cancel_left]
  have hcongr : ∫ z in Submission.BoseGases.acube ℓ, ψ (ℓ • u + z)
      = ∫ z in Submission.BoseGases.acube ℓ, c :=
    setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) (fun z hz => hpt z hz)
  rw [hcongr, setIntegral_const, Measure.real_def,
    Submission.BoseGases.acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]

/-- `Q_uψ` vanishes pointwise on `Λ(u)` when `ψ` is constant there. -/
lemma bsQ_eq_zero_of_lamBox_const {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (h : ∀ z ∈ lamBox ℓ u, ψ z = c) : ∀ z ∈ lamBox ℓ u, bsQ ℓ u ψ z = 0 := by
  intro z hz
  unfold bsQ
  rw [bsMean_eq_of_lamBox_const hℓ u h, h z hz, sub_self]

/-- The mean-free projection `Qfree ℓ u ψ = bsQ ℓ u ψ` vanishes pointwise on `Λ(u)`. -/
lemma Qfree_eq_zero_of_lamBox_const {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (h : ∀ z ∈ lamBox ℓ u, ψ z = c) : ∀ z ∈ lamBox ℓ u, Qfree ℓ u ψ z = 0 := by
  intro z hz
  simp only [Qfree]
  exact bsQ_eq_zero_of_lamBox_const hℓ u h z hz

/-! ## 2. The window vanishes off the box -/

/-- The window `χ_u` vanishes off the moving box. -/
lemma bsWin_eq_zero_of_not_mem_lamBox {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {z : ℝ³}
    (hz : z ∉ lamBox ℓ u) : bsWin ℓ u z = 0 := by
  by_contra hne
  have hmem : z ∈ tsupport (bsWin ℓ u) :=
    subset_closure (by rwa [Function.mem_support])
  exact hz (tsupport_bsWin_subset_bsBox hℓ u hmem)

/-! ## 3. Integrals over `Λ(u)` of functions vanishing there -/

lemma integral_lamBox_sq_eq_zero {ℓ : ℝ} (u : ℝ³) {φ : ℝ³ → ℝ}
    (hφ : ∀ z ∈ lamBox ℓ u, φ z = 0) : ∫ z in lamBox ℓ u, (φ z) ^ 2 = 0 := by
  have h : ∫ z in lamBox ℓ u, (φ z) ^ 2 = ∫ z in lamBox ℓ u, (0 : ℝ) :=
    setIntegral_congr_fun (measurableSet_lamBox ℓ u) (fun z hz => by rw [hφ z hz]; ring)
  rw [h]; simp

lemma integral_lamBox_mul_eq_zero {ℓ : ℝ} (u : ℝ³) {φ g : ℝ³ → ℝ}
    (hφ : ∀ z ∈ lamBox ℓ u, φ z = 0) : ∫ z in lamBox ℓ u, φ z * g z = 0 := by
  have h : ∫ z in lamBox ℓ u, φ z * g z = ∫ z in lamBox ℓ u, (0 : ℝ) :=
    setIntegral_congr_fun (measurableSet_lamBox ℓ u) (fun z hz => by rw [hφ z hz]; ring)
  rw [h]; simp

/-! ## 4. The four words vanish -/

/-- `neuFrac` of a function vanishing on `Λ(u)` is `0`: the defining set of trials is bounded
below by `0` and contains `0` (the trial `g = 0`). -/
lemma neuFrac_eq_zero_of_lamBox_eq_zero {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : ℝ³) {φ : ℝ³ → ℝ}
    (hφ : ∀ z ∈ lamBox ℓ u, φ z = 0) : neuFrac ℓ a2 u φ = 0 := by
  unfold neuFrac
  set S := { c : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      c = (∫ z in lamBox ℓ u, (φ z) ^ 2)
          - 2 * a2 * (∫ z in lamBox ℓ u, φ z * g z)
          + a2 * ((∑ k : Fin 3, ∫ z in lamBox ℓ u, (fderiv ℝ g z (kcStdBasis k)) ^ 2)
                  + a2 * (∫ z in lamBox ℓ u, (g z) ^ 2)) } with hS
  have hzero : (0 : ℝ) ∈ S := by
    refine ⟨fun _ : ℝ³ => (0 : ℝ), contDiff_const, HasCompactSupport.zero, ?_⟩
    rw [integral_lamBox_sq_eq_zero u hφ, integral_lamBox_mul_eq_zero u hφ]
    simp
  have hnonneg : ∀ c ∈ S, 0 ≤ c := by
    rintro c ⟨g, -, -, rfl⟩
    rw [integral_lamBox_sq_eq_zero u hφ, integral_lamBox_mul_eq_zero u hφ]
    simp only [mul_zero, sub_zero, zero_add]
    exact mul_nonneg ha2
      (add_nonneg (Finset.sum_nonneg fun k _ => integral_nonneg fun z => sq_nonneg _)
        (mul_nonneg ha2 (integral_nonneg fun z => sq_nonneg _)))
  exact le_antisymm (csInf_le ⟨0, fun c hc => hnonneg c hc⟩ hzero)
    (le_csInf ⟨0, hzero⟩ fun b hb => hnonneg b hb)

/-- The `L²`-mass `gapBare` vanishes when the mean-free part vanishes on the box. -/
lemma gapBare_eq_zero_of_lamBox_const {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (h : ∀ z ∈ lamBox ℓ u, ψ z = c) : gapBare ℓ u ψ = 0 := by
  unfold gapBare
  exact integral_lamBox_sq_eq_zero u (Qfree_eq_zero_of_lamBox_const hℓ u h)

/-- The windowed mean-free product `χ_u·Q_uψ` is identically zero when `ψ` is constant on
`Λ(u)`. -/
lemma bsWin_mul_bsQ_eq_zero {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (h : ∀ z ∈ lamBox ℓ u, ψ z = c) :
    (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) = 0 := by
  funext z
  by_cases hz : z ∈ lamBox ℓ u
  · rw [bsQ_eq_zero_of_lamBox_const hℓ u h z hz]; simp
  · rw [bsWin_eq_zero_of_not_mem_lamBox hℓ u hz]; simp

/-- The one-body kinetic form vanishes when the windowed mean-free product does. -/
lemma bsOneBody_eq_zero {ℓ c : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (h : ∀ z ∈ lamBox ℓ u, ψ z = c) : bsOneBody ℓ F u ψ = 0 := by
  unfold bsOneBody
  rw [bsWin_mul_bsQ_eq_zero hℓ u h]
  simp [kinFT]

/-- The momentum form vanishes: its integrand is the Fourier transform of the zero function. -/
lemma momForm_eq_zero_of_lamBox_const {ℓ d c : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (h : ∀ z ∈ lamBox ℓ u, ψ z = c) : momForm ℓ d u ψ = 0 := by
  unfold momForm
  have hfun : (fun z : ℝ³ => (((indU ℓ u z : ℝ)) : ℂ) * ((Qfree ℓ u ψ z : ℝ) : ℂ)) = 0 := by
    funext z
    by_cases hz : z ∈ lamBox ℓ u
    · have hz' : Qfree ℓ u ψ z = 0 := Qfree_eq_zero_of_lamBox_const hℓ u h z hz
      rw [hz']; simp
    · have hz' : indU ℓ u z = 0 := by
        simp only [indU]
        exact Set.indicator_of_notMem hz _
      rw [hz']; simp
  rw [hfun]
  simp [kinFT]

/-! ## 5. The target -/

theorem fsT_eq_zero_of_lamBox_const {ℓ d s εT b c : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∀ z ∈ Work.BoseKinLoc.lamBox ℓ u, ψ z = c) :
    Work.BoseKinLoc.fsT ℓ d s εT b u ψ = 0 := by
  have hQ : ∀ z ∈ lamBox ℓ u, Qfree ℓ u ψ z = 0 := Qfree_eq_zero_of_lamBox_const hℓ u h
  have hneu : neuWord ℓ d εT u ψ = 0 := by
    unfold neuWord
    rw [neuFrac_eq_zero_of_lamBox_eq_zero (by positivity : (0 : ℝ) ≤ (d * ℓ) ^ (-2 : ℤ)) u hQ,
      mul_zero]
  have hgap : gapWord ℓ b u ψ = 0 := by
    unfold gapWord
    rw [gapBare_eq_zero_of_lamBox_const hℓ u h, mul_zero]
  have hmom : momWord ℓ d εT b u ψ = 0 := by
    unfold momWord
    rw [momForm_eq_zero_of_lamBox_const hℓ u h, mul_zero]
  have hmain : mainWord ℓ d s εT u ψ = 0 := by
    unfold mainWord
    rw [bsOneBody_eq_zero hℓ _ u h, bsOneBody_eq_zero hℓ _ u h, mul_zero, mul_zero, add_zero]
  rw [fsT_eq_sum, hneu, hgap, hmom, hmain]
  simp

end Work.BoseKinLoc.Word
