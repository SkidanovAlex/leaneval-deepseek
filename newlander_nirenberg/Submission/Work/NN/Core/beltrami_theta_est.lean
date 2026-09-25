/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Estimates for `∂(bmPotential ·)` used by `beltrami_theta_fixedpoint`
-/
import Mathlib
import Submission.Work.NN.Core.beltrami_theta_aux
import Submission.Work.NN.Core.bmPot_holder_C0a
import Submission.Work.NN.Core.exists_holderNorm_wirtinger_le
import Submission.Work.CR.Flat.Cauchy.bmPotential_dCoord_holderNorm_le
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing

noncomputable section

open scoped NNReal ENNReal
open Set MeasureTheory

namespace Work.NN.Core

namespace BTheta

variable {n : ℕ}

/-- At order one the norm of a difference of iterated derivatives is the norm of the difference
of the (within) Fréchet derivatives. -/
private lemma norm_iteratedFDerivWithin_one_sub' {P : Set (Fin n → ℂ)} (f : (Fin n → ℂ) → ℂ)
    {x y : Fin n → ℂ} (hx : UniqueDiffWithinAt ℝ P x) (hy : UniqueDiffWithinAt ℝ P y) :
    ‖iteratedFDerivWithin ℝ 1 f P x - iteratedFDerivWithin ℝ 1 f P y‖
      = ‖fderivWithin ℝ f P x - fderivWithin ℝ f P y‖ := by
  have key : ∀ z : Fin n → ℂ, UniqueDiffWithinAt ℝ P z →
      continuousMultilinearCurryFin1 ℝ (Fin n → ℂ) ℂ (iteratedFDerivWithin ℝ 1 f P z)
        = fderivWithin ℝ f P z := by
    intro z hz
    ext v
    rw [continuousMultilinearCurryFin1_apply, iteratedFDerivWithin_one_apply hz]
    simp
  calc ‖iteratedFDerivWithin ℝ 1 f P x - iteratedFDerivWithin ℝ 1 f P y‖
      = ‖continuousMultilinearCurryFin1 ℝ (Fin n → ℂ) ℂ
          (iteratedFDerivWithin ℝ 1 f P x - iteratedFDerivWithin ℝ 1 f P y)‖ :=
        (LinearIsometryEquiv.norm_map _ _).symm
    _ = ‖fderivWithin ℝ f P x - fderivWithin ℝ f P y‖ := by rw [map_sub, key x hx, key y hy]

/-- For an open set `Ω`, the `C^{0,α}`-norm of `∂_i f` is bounded by `2` times the
`C^{1,α}`-norm of `f`.  No regularity hypothesis is needed: at points where `f` is not
differentiable `fderiv ℝ f` is `0` by convention, and on an open set
`‖iteratedFDerivWithin ℝ 1 f Ω z‖ = ‖fderiv ℝ f z‖`. -/
theorem holderNorm_dCoord_le {α : ℝ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (f : (Fin n → ℂ) → ℂ) (i : Fin n) :
    Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i f z) Ω
      ≤ 2 * Work.CR.Flat.holderNorm 1 α f Ω := by
  -- the sup part
  have hI : Work.CR.Flat.iterDerivNorm 0 (fun z => Work.CR.Flat.dCoord i f z) Ω
      ≤ Work.CR.Flat.holderNorm 1 α f Ω := by
    refine iSup₂_le fun z hz => ?_
    rw [norm_iteratedFDerivWithin_zero]
    have hkey : ‖Work.CR.Flat.dCoord i f z‖ ≤ ‖iteratedFDerivWithin ℝ 1 f Ω z‖ := by
      rw [show Work.CR.Flat.dCoord i f z = dCoordLin i (fderiv ℝ f z) from
        congrFun (dCoord_eq_comp i f) z]
      calc ‖dCoordLin i (fderiv ℝ f z)‖
          ≤ ‖dCoordLin i‖ * ‖fderiv ℝ f z‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖fderiv ℝ f z‖ :=
            mul_le_mul_of_nonneg_right (norm_dCoordLin_le i) (norm_nonneg _)
        _ = ‖fderiv ℝ f z‖ := one_mul _
        _ = ‖fderivWithin ℝ f Ω z‖ := by rw [fderivWithin_of_isOpen hΩ hz]
        _ = ‖iteratedFDerivWithin ℝ 1 f Ω z‖ :=
            (norm_iteratedFDerivWithin_one f (hΩ.uniqueDiffWithinAt hz)).symm
    calc ENNReal.ofReal ‖Work.CR.Flat.dCoord i f z‖
        ≤ ENNReal.ofReal ‖iteratedFDerivWithin ℝ 1 f Ω z‖ := ENNReal.ofReal_le_ofReal hkey
      _ ≤ Work.CR.Flat.iterDerivNorm 1 f Ω := Work.CR.Flat.le_iterDerivNorm 1 f Ω hz
      _ ≤ Work.CR.Flat.holderNorm 1 α f Ω :=
          Work.CR.Flat.iterDerivNorm_le_holderNorm 1 α f Ω le_rfl
  -- the Hölder part
  have hS : Work.CR.Flat.holderSeminorm 0 α (fun z => Work.CR.Flat.dCoord i f z) Ω
      ≤ Work.CR.Flat.holderNorm 1 α f Ω := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [BTheta.norm_iteratedFDerivWithin_zero_sub]
    have hkey : ‖Work.CR.Flat.dCoord i f x - Work.CR.Flat.dCoord i f y‖
        ≤ ‖iteratedFDerivWithin ℝ 1 f Ω x - iteratedFDerivWithin ℝ 1 f Ω y‖ := by
      rw [show Work.CR.Flat.dCoord i f x = dCoordLin i (fderiv ℝ f x) from
            congrFun (dCoord_eq_comp i f) x,
          show Work.CR.Flat.dCoord i f y = dCoordLin i (fderiv ℝ f y) from
            congrFun (dCoord_eq_comp i f) y]
      calc ‖dCoordLin i (fderiv ℝ f x) - dCoordLin i (fderiv ℝ f y)‖
          = ‖dCoordLin i (fderiv ℝ f x - fderiv ℝ f y)‖ := by rw [map_sub]
        _ ≤ ‖dCoordLin i‖ * ‖fderiv ℝ f x - fderiv ℝ f y‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖fderiv ℝ f x - fderiv ℝ f y‖ :=
            mul_le_mul_of_nonneg_right (norm_dCoordLin_le i) (norm_nonneg _)
        _ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := one_mul _
        _ = ‖fderivWithin ℝ f Ω x - fderivWithin ℝ f Ω y‖ := by
            rw [fderivWithin_of_isOpen hΩ hx, fderivWithin_of_isOpen hΩ hy]
        _ = ‖iteratedFDerivWithin ℝ 1 f Ω x - iteratedFDerivWithin ℝ 1 f Ω y‖ :=
            (norm_iteratedFDerivWithin_one_sub' f (hΩ.uniqueDiffWithinAt hx)
              (hΩ.uniqueDiffWithinAt hy)).symm
    refine (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hkey
      (Real.rpow_nonneg (norm_nonneg _) α))).trans ?_
    exact (Work.CR.Flat.le_holderSeminorm 1 α f Ω hx hy hxy).trans
      (Work.CR.Flat.holderSeminorm_le_holderNorm 1 α f Ω le_rfl)
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_one]
  calc Work.CR.Flat.iterDerivNorm 0 (fun z => Work.CR.Flat.dCoord i f z) Ω
        + Work.CR.Flat.holderSeminorm 0 α (fun z => Work.CR.Flat.dCoord i f z) Ω
      ≤ Work.CR.Flat.holderNorm 1 α f Ω + Work.CR.Flat.holderNorm 1 α f Ω := add_le_add hI hS
    _ = 2 * Work.CR.Flat.holderNorm 1 α f Ω := (two_mul _).symm

/-! ## The Schauder estimate for `∂(bmPot ·)` of `C^{0,α}`-data on a polydisc -/

theorem dCoord_bmPot_holderNorm_le {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {σ τ : Fin n → ℝ} (hσ : ∀ j, 0 < σ j) (hτ : ∀ j, 0 < τ j) (hστ : ∀ j, σ j ≤ τ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, Work.CR.Flat.holderNorm 0 α (H j) Set.univ < ⊤) →
      (∀ j z, z ∉ Work.CR.Flat.polydisc 0 σ → H j z = 0) →
      ∀ i : Fin n,
        Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
            (Work.CR.Flat.Cauchy.bmPot H) z) (Work.CR.Flat.polydisc 0 τ)
          ≤ ENNReal.ofReal C * ∑ j, Work.CR.Flat.holderNorm 0 α (H j) Set.univ := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.NN.Core.bmPot_holder_C0a (n := n) hn (c := (0 : Fin n → ℂ))
    (r := fun j => 2 * τ j) (α := α) hα0 hα1 (fun j => by linarith [hτ j])
  refine ⟨2 * C₁, by positivity, ?_⟩
  intro H hHfin hHvan i
  have hsupp : ∀ j z, (∃ k, (2 * τ k) / 2 ≤ ‖z k - (0 : Fin n → ℂ) k‖) → H j z = 0 := by
    intro j z hz
    refine hHvan j z fun hmem => ?_
    obtain ⟨k, hk⟩ := hz
    rw [show (2 * τ k) / 2 = τ k from by ring] at hk
    simp only [Pi.zero_apply, sub_zero] at hk
    have hlt : ‖z k‖ < τ k :=
      lt_of_lt_of_le (by simpa only [Pi.zero_apply, sub_zero] using hmem k) (hστ k)
    exact absurd (lt_of_le_of_lt hk hlt) (lt_irrefl _)
  have h1 := hC₁ H hsupp (fun j => ne_of_lt (hHfin j))
  have hpoly : Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun j => (2 * τ j) / 2)
      = Work.CR.Flat.polydisc 0 τ := by
    congr 1
    funext j
    ring
  rw [hpoly] at h1
  have h2 := holderNorm_dCoord_le (α := α) (Work.CR.Flat.isOpen_polydisc (0 : Fin n → ℂ) τ)
    (Work.CR.Flat.Cauchy.bmPot H) i
  calc Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
          (Work.CR.Flat.Cauchy.bmPot H) z) (Work.CR.Flat.polydisc 0 τ)
      ≤ 2 * Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPot H)
          (Work.CR.Flat.polydisc 0 τ) := h2
    _ ≤ 2 * (ENNReal.ofReal C₁ * ∑ j, Work.CR.Flat.holderNorm 0 α (H j) Set.univ) :=
        mul_le_mul_right h1 2
    _ = ENNReal.ofReal (2 * C₁) * ∑ j, Work.CR.Flat.holderNorm 0 α (H j) Set.univ := by
        have h2C : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := (ENNReal.ofReal_natCast 2).symm
        rw [← mul_assoc, h2C, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]

/-! ## Finiteness for compactly supported `C¹` data -/

/-- A compactly supported function vanishes outside a ball. -/
lemma exists_radius_of_hasCompactSupport {f : (Fin n → ℂ) → ℂ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Fin n → ℂ, R ≤ ‖x‖ → f x = 0 := by
  obtain ⟨r, hr⟩ := hf.isCompact.isBounded.subset_closedBall (0 : Fin n → ℂ)
  refine ⟨max r 0 + 1, by positivity, fun x hx => ?_⟩
  by_contra hx0
  have hmem : x ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hx0)
  have h1 : ‖x‖ ≤ r := by
    have h := hr hmem
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have h2 : r ≤ max r 0 := le_max_left _ _
  linarith

theorem dCoord_bmPotential_finite {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {τ : Fin n → ℝ} (hτ : ∀ j, 0 < τ j) :
    ∀ (G : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ 1 (G j)) →
      (∀ j, HasCompactSupport (G j)) →
      (∀ j, Work.CR.Flat.holderNorm 0 α (G j) Set.univ < ⊤) →
      ∃ C : ℝ, 0 < C ∧ ∀ i : Fin n,
        Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
            (Work.CR.Flat.Cauchy.bmPotential G) z) (Work.CR.Flat.polydisc 0 τ)
          ≤ ENNReal.ofReal C := by
  intro G hG1 hGcs hGfin
  choose R hR0 hR using fun j => exists_radius_of_hasCompactSupport (hGcs j)
  have hRsum : (0 : ℝ) ≤ ∑ j, R j := Finset.sum_nonneg fun i _ => hR0 i
  have hτsum : (0 : ℝ) ≤ ∑ j, τ j := Finset.sum_nonneg fun i _ => (hτ i).le
  set S : ℝ := (∑ j, R j) + (∑ j, τ j) + 1 with hSdef
  have hSR : ∀ j, R j ≤ S := by
    intro j
    have h1 : R j ≤ ∑ i, R i := Finset.single_le_sum (fun i _ => hR0 i) (Finset.mem_univ j)
    rw [hSdef]; linarith
  have hSτ : ∀ j, τ j ≤ S := by
    intro j
    have h1 : τ j ≤ ∑ i, τ i := Finset.single_le_sum (fun i _ => (hτ i).le) (Finset.mem_univ j)
    rw [hSdef]; linarith
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.CR.Flat.Cauchy.bmPotential_dCoord_holderNorm_le (n := n) hn
    (c := (0 : Fin n → ℂ)) (r := fun j => 2 * S) hα0 hα1 (fun j => by positivity)
  have hsupp : ∀ j z, (∃ k, (2 * S) / 2 ≤ ‖z k - (0 : Fin n → ℂ) k‖) → G j z = 0 := by
    intro j z hz
    obtain ⟨k, hk⟩ := hz
    rw [show (2 * S) / 2 = S from by ring] at hk
    simp only [Pi.zero_apply, sub_zero] at hk
    refine hR j z ?_
    calc R j ≤ S := hSR j
      _ ≤ ‖z k‖ := hk
      _ ≤ ‖z‖ := norm_le_pi_norm z k
  have hmain := hC₁ G hG1 hsupp
  set K : ℝ := ∑ j, (Work.CR.Flat.holderNorm 0 α (G j) Set.univ).toReal with hKdef
  have hSumEq : (∑ j, Work.CR.Flat.holderNorm 0 α (G j) Set.univ) = ENNReal.ofReal K := by
    have h1 : (∑ j, Work.CR.Flat.holderNorm 0 α (G j) Set.univ)
        = ∑ j, ENNReal.ofReal ((Work.CR.Flat.holderNorm 0 α (G j) Set.univ).toReal) :=
      Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_toReal (ne_of_lt (hGfin j))).symm
    rw [h1, hKdef, ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
  refine ⟨C₁ * (K + 1), by positivity, fun i => ?_⟩
  have hpoly : Work.CR.Flat.polydisc (0 : Fin n → ℂ) τ
      ⊆ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun j => (2 * S) / 2) := by
    intro z hz
    rw [Work.CR.Flat.mem_polydisc] at hz ⊢
    intro j
    rw [show (2 * S) / 2 = S from by ring]
    exact lt_of_lt_of_le (hz j) (hSτ j)
  calc Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
          (Work.CR.Flat.Cauchy.bmPotential G) z) (Work.CR.Flat.polydisc 0 τ)
      ≤ Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
          (Work.CR.Flat.Cauchy.bmPotential G) z)
          (Work.CR.Flat.polydisc 0 (fun j => (2 * S) / 2)) :=
        Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 (fun j => (2 * S) / 2))
          (Work.CR.Flat.isOpen_polydisc 0 τ) hpoly 0 α _
    _ ≤ ENNReal.ofReal C₁ * ∑ j, Work.CR.Flat.holderNorm 0 α (G j) Set.univ := hmain i
    _ = ENNReal.ofReal C₁ * ENNReal.ofReal K := by rw [hSumEq]
    _ = ENNReal.ofReal (C₁ * K) := (ENNReal.ofReal_mul hC₁pos.le).symm
    _ ≤ ENNReal.ofReal (C₁ * (K + 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_left (by linarith) hC₁pos.le

section OneStep

variable {ρ τ : Fin n → ℝ}

/-- `bmPotential` and `bmPot` are the same function. -/
lemma bmPotential_eq_bmPot_fun (H : Fin n → (Fin n → ℂ) → ℂ) :
    Work.CR.Flat.Cauchy.bmPotential H = Work.CR.Flat.Cauchy.bmPot H :=
  funext fun z => Work.CR.Flat.Cauchy.bmPotential_eq_bmPot H z

/-- **The one-step (contraction) estimate for the Beltrami fixed-point operator.**  For a family
of coefficients `c` of `C^{0,α}`-norm at most `δ`, supported in `polydisc 0 ρ`, and data `H` of
finite `C^{0,α}`-norm, supported off `polydisc 0 ρ`, the `C^{0,α}`-norm of
`z ↦ (bmGamma n)⁻¹ Σ_l c_l z · ∂_l (bmPotential H) z` is at most `C δ` times `Σ_l ‖H_l‖`. -/
theorem one_step_bound {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ τ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hτ : ∀ j, 0 < τ j) (hρτ : ∀ j, ρ j < τ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Fin n → (Fin n → ℂ) → ℂ) (H : Fin n → (Fin n → ℂ) → ℂ) (δ : ℝ),
      (∀ l, Work.CR.Flat.holderNorm 0 α (c l) Set.univ ≤ ENNReal.ofReal δ) →
      (∀ l z, c l z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
      (∀ l, Work.CR.Flat.holderNorm 0 α (H l) Set.univ < ⊤) →
      (∀ l z, z ∉ Work.CR.Flat.polydisc 0 ρ → H l z = 0) →
      Work.CR.Flat.holderNorm 0 α (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
          ∑ l, c l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H) z) Set.univ
        ≤ ENNReal.ofReal (C * δ) * ∑ l, Work.CR.Flat.holderNorm 0 α (H l) Set.univ := by
  obtain ⟨Cv, hCvpos, hCv⟩ := dCoord_bmPot_holderNorm_le (n := n) hn (α := α) hα0 hα1
    (σ := ρ) (τ := τ) hρ hτ (fun j => (hρτ j).le)
  refine ⟨‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * (3 * (n : ℝ) * Cv) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ Cv := hCvpos.le
    have h3 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    positivity
  intro c H δ hcδ hcsupp hHfin hHvan
  set S : ℝ≥0∞ := ∑ l, Work.CR.Flat.holderNorm 0 α (H l) Set.univ with hSdef
  by_cases hδ : δ ≤ 0
  · have hcl0 : ∀ l z, c l z = 0 := by
      intro l z
      have h0 : ENNReal.ofReal δ = 0 := ENNReal.ofReal_eq_zero.mpr hδ
      have h1 : ENNReal.ofReal ‖c l z‖ ≤ ENNReal.ofReal (0 : ℝ) :=
        ((Work.CR.Flat.norm_apply_le_holderNorm 0 α (c l) Set.univ
          (Set.mem_univ z)).trans (hcδ l)).trans
          (le_of_eq (by rw [h0, ENNReal.ofReal_zero]))
      refine norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _))
      exact (ENNReal.ofReal_le_ofReal_iff le_rfl).mp h1
    have hzero : (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
        ∑ l, c l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H) z) = 0 := by
      funext z
      have hsumz : (∑ l, c l z * Work.CR.Flat.dCoord l
          (Work.CR.Flat.Cauchy.bmPotential H) z) = 0 := by
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [hcl0 l z, zero_mul]
      rw [hsumz, mul_zero]
      rfl
    rw [hzero, Work.CR.Flat.holderNorm_zero]
    exact bot_le
  · push_neg at hδ
    have hSfin : S ≠ ⊤ := by
      rw [hSdef]
      exact ENNReal.sum_ne_top.mpr fun l _ => ne_of_lt (hHfin l)
    have hS1 : 0 ≤ S.toReal := ENNReal.toReal_nonneg
    -- ### the `C^{0,α}`-bound of `∂_l (bmPotential H)` on `polydisc 0 τ`
    have hV : ∀ l, Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord l
          (Work.CR.Flat.Cauchy.bmPotential H) z) (Work.CR.Flat.polydisc 0 τ)
        ≤ ENNReal.ofReal (Cv * S.toReal) := by
      intro l
      have h1 := hCv H hHfin hHvan l
      rw [← bmPotential_eq_bmPot_fun H] at h1
      rw [← hSdef] at h1
      calc Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord l
              (Work.CR.Flat.Cauchy.bmPotential H) z) (Work.CR.Flat.polydisc 0 τ)
          ≤ ENNReal.ofReal Cv * (∑ l, Work.CR.Flat.holderNorm 0 α (H l) Set.univ) := h1
        _ = ENNReal.ofReal Cv * ENNReal.ofReal S.toReal := by rw [ENNReal.ofReal_toReal hSfin]
        _ = ENNReal.ofReal (Cv * S.toReal) := (ENNReal.ofReal_mul hCvpos.le).symm
    -- ### the product bound, term by term
    have hprod : ∀ l, Work.CR.Flat.holderNorm 0 α (fun z => c l z *
          Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H) z) Set.univ
        ≤ ENNReal.ofReal (3 * δ * (Cv * S.toReal)) := by
      intro l
      have hvan : ∀ z, (∃ i, ρ i ≤ ‖z i - (0 : Fin n → ℂ) i‖) →
          (fun z => c l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H) z) z = 0 := by
        intro z hz
        have hzP : z ∉ Work.CR.Flat.polydisc 0 ρ := by
          rw [Work.CR.Flat.mem_polydisc]
          push_neg
          exact hz
        have hcz : c l z = 0 := by
          by_contra hc
          exact hzP (hcsupp l z hc)
        simp [hcz]
      have htrans := Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
        (c := (0 : Fin n → ℂ)) (r := ρ) (r' := τ) hρτ (k := 0) (α := α) hα0.le hvan
      have hcQ : Work.CR.Flat.holderNorm 0 α (c l) (Work.CR.Flat.polydisc 0 τ)
          ≤ ENNReal.ofReal δ :=
        (Work.CR.Flat.holderNorm_mono_set (Ω := Set.univ)
          (Ω' := Work.CR.Flat.polydisc 0 τ) isOpen_univ
          (Work.CR.Flat.isOpen_polydisc 0 τ) (Set.subset_univ _) 0 α (c l)).trans (hcδ l)
      exact htrans.trans (holderNorm_zero_mul_le_ofReal hδ.le
        (mul_nonneg hCvpos.le hS1) hcQ (hV l))
    -- ### summing over `l` and multiplying by `(bmGamma n)⁻¹`
    have hsum : Work.CR.Flat.holderNorm 0 α (fun z => ∑ l, c l z *
          Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H) z) Set.univ
        ≤ ENNReal.ofReal ((n : ℝ) * (3 * δ * (Cv * S.toReal))) := by
      refine (holderNorm_zero_sum_le Finset.univ
        (fun l z => c l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H) z)
        Set.univ).trans ((Finset.sum_le_sum fun l _ => hprod l).trans ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ n)]
    have hγ : (0 : ℝ) ≤ ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ := norm_nonneg _
    calc Work.CR.Flat.holderNorm 0 α (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
            ∑ l, c l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H) z) Set.univ
        ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ *
            Work.CR.Flat.holderNorm 0 α (fun z => ∑ l, c l z *
              Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H) z) Set.univ :=
          holderNorm_zero_const_mul_le _ _ _
      _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ *
            ENNReal.ofReal ((n : ℝ) * (3 * δ * (Cv * S.toReal))) :=
          mul_le_mul_right hsum _
      _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ *
            ((n : ℝ) * (3 * δ * (Cv * S.toReal)))) := (ENNReal.ofReal_mul hγ).symm
      _ = ENNReal.ofReal ((‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * (3 * (n : ℝ) * Cv) * δ)
            * S.toReal) := by
          congr 1; ring
      _ ≤ ENNReal.ofReal ((‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * (3 * (n : ℝ) * Cv) + 1) * δ
            * S.toReal) := by
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [hγ, hCvpos, hδ.le, hS1, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      _ = ENNReal.ofReal ((‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * (3 * (n : ℝ) * Cv) + 1) * δ)
            * ENNReal.ofReal S.toReal :=
          ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal ((‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * (3 * (n : ℝ) * Cv) + 1) * δ)
            * ∑ l, Work.CR.Flat.holderNorm 0 α (H l) Set.univ := by
          rw [hSdef, ENNReal.ofReal_toReal hSfin]

/-- **Finiteness of the one-step operator on compactly supported `C¹` data.** -/
theorem one_step_finite {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ τ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hτ : ∀ j, 0 < τ j) (hρτ : ∀ j, ρ j < τ j) :
    ∀ (c : Fin n → (Fin n → ℂ) → ℂ) (G : Fin n → (Fin n → ℂ) → ℂ),
      (∀ l, Work.CR.Flat.holderNorm 0 α (c l) Set.univ < ⊤) →
      (∀ l z, c l z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
      (∀ l, ContDiff ℝ 1 (G l)) → (∀ l, HasCompactSupport (G l)) →
      (∀ l, Work.CR.Flat.holderNorm 0 α (G l) Set.univ < ⊤) →
      ∃ C : ℝ, 0 < C ∧ Work.CR.Flat.holderNorm 0 α (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
          ∑ l, c l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential G) z) Set.univ
        ≤ ENNReal.ofReal C := by
  intro c G hcfin hcsupp hG1 hGcs hGfin
  obtain ⟨Cg, hCgpos, hCg⟩ := dCoord_bmPotential_finite (n := n) hn (α := α) hα0 hα1 hτ
    G hG1 hGcs hGfin
  set Cc : ℝ := ∑ l, (Work.CR.Flat.holderNorm 0 α (c l) Set.univ).toReal with hCcdef
  have hCc0 : 0 ≤ Cc := Finset.sum_nonneg fun l _ => ENNReal.toReal_nonneg
  have hcl : ∀ l, (Work.CR.Flat.holderNorm 0 α (c l) Set.univ).toReal ≤ Cc := by
    intro l
    rw [hCcdef]
    exact Finset.single_le_sum
      (f := fun i => (Work.CR.Flat.holderNorm 0 α (c i) Set.univ).toReal)
      (fun i _ => ENNReal.toReal_nonneg) (Finset.mem_univ l)
  have hprod : ∀ l, Work.CR.Flat.holderNorm 0 α (fun z => c l z *
        Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential G) z) Set.univ
      ≤ ENNReal.ofReal (3 * Cc * Cg) := by
    intro l
    have hvan : ∀ z, (∃ i, ρ i ≤ ‖z i - (0 : Fin n → ℂ) i‖) →
        (fun z => c l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential G) z) z = 0 := by
      intro z hz
      have hzP : z ∉ Work.CR.Flat.polydisc 0 ρ := by
        rw [Work.CR.Flat.mem_polydisc]
        push_neg
        exact hz
      have hcz : c l z = 0 := by
        by_contra hc
        exact hzP (hcsupp l z hc)
      simp [hcz]
    have htrans := Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
      (c := (0 : Fin n → ℂ)) (r := ρ) (r' := τ) hρτ (k := 0) (α := α) hα0.le hvan
    have hcQ : Work.CR.Flat.holderNorm 0 α (c l) (Work.CR.Flat.polydisc 0 τ)
        ≤ ENNReal.ofReal Cc := by
      refine (Work.CR.Flat.holderNorm_mono_set (Ω := Set.univ)
        (Ω' := Work.CR.Flat.polydisc 0 τ) isOpen_univ
        (Work.CR.Flat.isOpen_polydisc 0 τ) (Set.subset_univ _) 0 α (c l)).trans ?_
      rw [← ENNReal.ofReal_toReal (ne_of_lt (hcfin l))]
      exact ENNReal.ofReal_le_ofReal (hcl l)
    exact htrans.trans (holderNorm_zero_mul_le_ofReal hCc0 hCgpos.le hcQ (hCg l))
  have hsum : Work.CR.Flat.holderNorm 0 α (fun z => ∑ l, c l z *
        Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential G) z) Set.univ
      ≤ ENNReal.ofReal ((n : ℝ) * (3 * Cc * Cg)) := by
    refine (holderNorm_zero_sum_le Finset.univ
      (fun l z => c l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential G) z)
      Set.univ).trans ((Finset.sum_le_sum fun l _ => hprod l).trans ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ n)]
  refine ⟨‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * ((n : ℝ) * (3 * Cc * Cg)) + 1, by positivity, ?_⟩
  have hγ : (0 : ℝ) ≤ ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ := norm_nonneg _
  calc Work.CR.Flat.holderNorm 0 α (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
          ∑ l, c l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential G) z) Set.univ
      ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ *
          Work.CR.Flat.holderNorm 0 α (fun z => ∑ l, c l z *
            Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential G) z) Set.univ :=
        holderNorm_zero_const_mul_le _ _ _
    _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ *
          ENNReal.ofReal ((n : ℝ) * (3 * Cc * Cg)) := mul_le_mul_right hsum _
    _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * ((n : ℝ) * (3 * Cc * Cg))) :=
        (ENNReal.ofReal_mul hγ).symm
    _ ≤ ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * ((n : ℝ) * (3 * Cc * Cg)) + 1) := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith

end OneStep

end BTheta

end Work.NN.Core
