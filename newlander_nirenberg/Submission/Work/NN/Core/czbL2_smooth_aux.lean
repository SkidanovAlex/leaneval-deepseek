/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Auxiliary lemmas for `Work.NN.Core.czbL2_bound_of_smooth`

Elementary facts used to pass from `C^∞_c` data to `C¹_c` data in the `L²` bound for
`∂ (bmPotential h)`:

* a compactly supported function vanishes outside a ball of some radius (`exists_norm_le_of_hasCompactSupport`);
* `fderiv` (and hence `dCoord`) of a function vanishing outside a ball vanishes strictly outside it;
* the Bochner–Martinelli potential of a compactly supported `C¹` family is `C¹`
  (`contDiff_one_bmPotential`, the compact-support companion of
  `Work.CR.Flat.Cauchy.bmPotential_contDiff_one`);
* the elementary estimate `‖dCoord k u z - dCoord k v z‖ ≤ ‖fderiv ℝ u z - fderiv ℝ v z‖`.
-/
import Mathlib
import Submission.Work.NN.Core.czB_L2_defs
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal ContDiff Convolution

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-- A compactly supported function on a normed space vanishes outside some closed ball. -/
lemma exists_norm_le_of_hasCompactSupport {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {f : E → F} (hf : HasCompactSupport f) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ x : E, ρ ≤ ‖x‖ → f x = 0 := by
  obtain ⟨r, hr⟩ := hf.isCompact.isBounded.subset_closedBall (0 : E)
  refine ⟨max r 0 + 1, by positivity, fun x hx => ?_⟩
  by_contra h
  have hx' : x ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr h)
  have hle : ‖x‖ ≤ r := by
    have h2 := hr hx'
    rwa [Metric.mem_closedBall, dist_zero_right] at h2
  have h1 : (max r 0 + 1 : ℝ) ≤ ‖x‖ := hx
  have h3 : r ≤ max r 0 := le_max_left _ _
  linarith

/-- If `u` vanishes outside the ball of radius `ρ`, then `fderiv ℝ u` vanishes strictly outside
it (on the open set where `ρ < ‖w‖` the function is locally zero). -/
lemma fderiv_eq_zero_of_forall_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ρ : ℝ} {u : E → F}
    (h : ∀ w, ρ ≤ ‖w‖ → u w = 0) : ∀ w, ρ < ‖w‖ → fderiv ℝ u w = 0 := by
  intro w hw
  have hopen : IsOpen {x : E | ρ < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hnb : {x : E | ρ < ‖x‖} ∈ nhds w := hopen.mem_nhds hw
  have hev : u =ᶠ[nhds w] 0 := by
    filter_upwards [hnb] with x hx
    exact h x hx.le
  rw [Filter.EventuallyEq.fderiv_eq hev]
  simp

/-- `dCoord` of a function vanishing outside the ball of radius `ρ` vanishes strictly outside it. -/
lemma dCoord_eq_zero_of_forall_norm_le {n : ℕ} (k : Fin n) {ρ : ℝ}
    {u : (Fin n → ℂ) → ℂ} (h : ∀ w, ρ ≤ ‖w‖ → u w = 0) :
    ∀ w, ρ < ‖w‖ → Work.CR.Flat.dCoord k u w = 0 := by
  intro w hw
  rw [Work.CR.Flat.dCoord, fderiv_eq_zero_of_forall_norm_le h w hw]
  simp

/-- The difference of the `dCoord`s of two functions vanishing outside a ball vanishes strictly
outside it. -/
lemma dCoord_sub_eq_zero_of_forall_norm_le {n : ℕ} (k : Fin n) {ρ : ℝ}
    {u v : (Fin n → ℂ) → ℂ} (hu : ∀ w, ρ ≤ ‖w‖ → u w = 0)
    (hv : ∀ w, ρ ≤ ‖w‖ → v w = 0) :
    ∀ w, ρ < ‖w‖ → Work.CR.Flat.dCoord k u w - Work.CR.Flat.dCoord k v w = 0 := by
  intro w hw
  rw [dCoord_eq_zero_of_forall_norm_le k hu w hw, dCoord_eq_zero_of_forall_norm_le k hv w hw,
    sub_self]

/-- The Wirtinger derivative is `1`-Lipschitz for the operator norm of the real derivative. -/
lemma norm_dCoord_sub_le {n : ℕ} (k : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    ‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k v z‖
      ≤ ‖fderiv ℝ u z - fderiv ℝ v z‖ := by
  set Δ : (Fin n → ℂ) →L[ℝ] ℂ := fderiv ℝ u z - fderiv ℝ v z with hΔ
  have hkey : Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k v z
      = (1 / 2 : ℂ) * (Δ (Pi.single k 1) - Complex.I * Δ (Pi.single k Complex.I)) := by
    rw [hΔ, Work.CR.Flat.dCoord, Work.CR.Flat.dCoord]
    simp only [ContinuousLinearMap.sub_apply]
    ring
  have h1 : ‖(Pi.single k (1 : ℂ) : Fin n → ℂ)‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    rw [Pi.single_apply]
    split <;> simp
  have h2 : ‖(Pi.single k Complex.I : Fin n → ℂ)‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    rw [Pi.single_apply]
    split <;> simp
  have h3 : ‖Δ (Pi.single k (1 : ℂ))‖ ≤ ‖Δ‖ := by
    calc ‖Δ (Pi.single k (1 : ℂ))‖ ≤ ‖Δ‖ * ‖(Pi.single k (1 : ℂ) : Fin n → ℂ)‖ :=
          ContinuousLinearMap.le_opNorm Δ _
      _ ≤ ‖Δ‖ * 1 := by gcongr
      _ = ‖Δ‖ := mul_one _
  have h4 : ‖Δ (Pi.single k Complex.I)‖ ≤ ‖Δ‖ := by
    calc ‖Δ (Pi.single k Complex.I)‖ ≤ ‖Δ‖ * ‖(Pi.single k Complex.I : Fin n → ℂ)‖ :=
          ContinuousLinearMap.le_opNorm Δ _
      _ ≤ ‖Δ‖ * 1 := by gcongr
      _ = ‖Δ‖ := mul_one _
  have h5 : ‖Δ (Pi.single k (1 : ℂ)) - Complex.I * Δ (Pi.single k Complex.I)‖ ≤ ‖Δ‖ + ‖Δ‖ := by
    calc ‖Δ (Pi.single k (1 : ℂ)) - Complex.I * Δ (Pi.single k Complex.I)‖
        ≤ ‖Δ (Pi.single k (1 : ℂ))‖ + ‖Complex.I * Δ (Pi.single k Complex.I)‖ :=
          norm_sub_le _ _
      _ = ‖Δ (Pi.single k (1 : ℂ))‖ + ‖Δ (Pi.single k Complex.I)‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖Δ‖ + ‖Δ‖ := add_le_add h3 h4
  have h12 : ‖((1 / 2 : ℂ))‖ = (1 / 2 : ℝ) := by norm_num
  rw [hkey, norm_mul, h12]
  calc (1 / 2 : ℝ) * ‖Δ (Pi.single k (1 : ℂ)) - Complex.I * Δ (Pi.single k Complex.I)‖
      ≤ (1 / 2) * (‖Δ‖ + ‖Δ‖) := by gcongr
    _ = ‖Δ‖ := by ring

/-- The Bochner–Martinelli potential of a compactly supported `C¹` family is `C¹`. -/
lemma contDiff_one_bmPotential {n : ℕ} (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ 1 (f j)) (hcs : ∀ j, HasCompactSupport (f j)) :
    ContDiff ℝ 1 (bmPotential f) := by
  have hconv : ∀ j, ContDiff ℝ 1 (bmKernel j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f j) :=
    fun j => HasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      (hcs j) (locallyIntegrable_bmKernel hn j) (hf j)
  rw [bmPotential_eq_neg_conv f]
  exact ContDiff.neg (ContDiff.sum fun j _ => hconv j)

/-- `z ↦ dCoord k u z` is continuous when `u` is `C¹`. -/
lemma czbL2smooth_continuous_dCoord {n : ℕ} {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ 1 u) (k : Fin n) :
    Continuous (fun z => Work.CR.Flat.dCoord k u z) := by
  have hdu : Continuous (fun z => fderiv ℝ u z) := hu.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun z => fderiv ℝ u z (Pi.single k (1 : ℂ))) :=
    hdu.clm_apply continuous_const
  have h2 : Continuous (fun z => fderiv ℝ u z (Pi.single k Complex.I)) :=
    hdu.clm_apply continuous_const
  have hfun : (fun z => Work.CR.Flat.dCoord k u z) = fun z =>
      (1 / 2 : ℂ) * (fderiv ℝ u z (Pi.single k 1)
        - Complex.I * fderiv ℝ u z (Pi.single k Complex.I)) := rfl
  rw [hfun]
  exact continuous_const.mul (h1.sub (continuous_const.mul h2))

end Work.NN.Core
