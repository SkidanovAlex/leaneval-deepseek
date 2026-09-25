/-
# Elementary helpers for the `ℓ¹` kernel bound of the MST major-arc model

This module collects the structural facts that the per-level, trivial `ℓ¹` bound of the MST §4.2
model (`mstModelFn_kernel_l1`) uses, and that the companion modules
`circleLift_dilate_fourier`, `polyProfile_star_kernel_fubini` and `fourierDilateLattice_l1` reuse:

* the level dilation factor `mstC d χ s = 2^{s(d−χ)}` and its elementary bounds;
* the evaluation of the canonical lift `iwRep` on the fundamental domain;
* the exponential form `star (fourier p ζ) = e(−iwRep ζ · p)` of the conjugate character, and the
  multiplicativity `fourier p (ζ + β) = fourier p ζ · fourier p β` of the character in the base
  point;
* the two facts about the fundamental-domain lift `F₀ = circleLift (mstEta d χ η 0)` of the level-`0`
  bump: `F₀ x = η (−x)` on `Ioo (−1/2) (1/2)`, and `F₀ x = 0` off `Icc (−1/2) (1/2)`;
* consequently `η =ᵐ F₀ ∘ (−·)` (the only possible exceptions are the points `±1/2`), whence `η` is
  a.e. strongly measurable and a.e. bounded, and `η (c ·)` is `L^∞` on the fundamental domain — so
  that the level bumps `mstEta d χ η s` are `MemLp ⊤` on the circle via `memLp_comp_iwRep`.
-/
import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.memLp_scaled_bump
import Submission.Work.BourgainPlan.Maximal.memLp_comp_iwRep
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haar" => (AddCircle.haarAddCircle (T := 1))
local notation "circleLift" => Work.BourgainPlan.Thm52.circleLift

noncomputable section

/-! ## The level dilation factor -/

/-- The dilation factor `c_s = 2^{s(d−χ)}` of the MST level bump `η_s = mstEta d χ η s`. -/
noncomputable def mstC (d : ℕ) (χ : ℝ) (s : ℕ) : ℝ := (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))

@[simp] theorem mstEta_eq_mstC (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (ζ : Circ) :
    mstEta d χ η s ζ = η (mstC d χ s * iwRep ζ) := rfl

theorem mstC_nonneg (d : ℕ) (χ : ℝ) (hd : 1 ≤ d) (hχ0 : 0 ≤ χ) (hχd : χ ≤ (d : ℝ))
    (s : ℕ) : 0 ≤ mstC d χ s :=
  Real.rpow_nonneg (by norm_num) _

theorem one_le_mstC (d : ℕ) (χ : ℝ) (hd : 1 ≤ d) (hχ0 : 0 ≤ χ) (hχd : χ ≤ (d : ℝ))
    (s : ℕ) : 1 ≤ mstC d χ s := by
  refine Real.one_le_rpow (by norm_num) ?_
  have h1 : (0 : ℝ) ≤ (d : ℝ) - χ := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  exact mul_nonneg (by positivity) h1

theorem mstC_pos (d : ℕ) (χ : ℝ) (hd : 1 ≤ d) (hχ0 : 0 ≤ χ) (hχd : χ ≤ (d : ℝ))
    (s : ℕ) : 0 < mstC d χ s := lt_of_lt_of_le zero_lt_one (one_le_mstC d χ hd hχ0 hχd s)

@[simp] theorem mstC_zero (d : ℕ) (χ : ℝ) : mstC d χ 0 = 1 := by
  simp [mstC]

/-! ## The canonical lift `iwRep` -/

/-- On the fundamental domain `Ioc (−1/2) (1/2)` the canonical lift is the identity. -/
theorem iwRep_coe_of_mem {y : ℝ} (hy : y ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :
    iwRep (y : Circ) = y := by
  have h := AddCircle.liftIoc_coe_apply (p := (1 : ℝ)) (a := -(1 / 2 : ℝ))
    (f := fun x : ℝ => x) (x := y) (by
      rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]; exact hy)
  simpa only [iwRep] using h

/-! ## The characters of the circle -/

/-- **The conjugate character in exponential form**: `star (fourier p ζ) = e(−iwRep ζ · p)`. -/
theorem star_fourier_eq_exp (p : ℤ) (ζ : Circ) :
    star (fourier p ζ)
      = Complex.exp (-(2 * Real.pi * Complex.I * (iwRep ζ * (p : ℝ)))) := by
  have h : star (fourier p ζ) = fourier (-p) ζ := by
    have h1 := fourier_neg (n := p) (x := ζ)
    rw [starRingEnd_apply] at h1
    exact h1.symm
  rw [h]
  conv_lhs => rw [← coe_iwRep ζ]
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- **The character is multiplicative in the base point**:
`fourier p (ζ + β) = fourier p ζ * fourier p β`. -/
theorem fourier_add_right (p : ℤ) (ζ β : Circ) :
    fourier p (ζ + β) = fourier p ζ * fourier p β := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

theorem star_fourier_add_right (p : ℤ) (ζ β : Circ) :
    star (fourier p (ζ + β)) = star (fourier p ζ) * star (fourier p β) := by
  rw [fourier_add_right, star_mul, mul_comm]

/-! ## The fundamental-domain lift of the level-`0` bump -/

theorem mstEta_zero_eq (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (ζ : Circ) :
    mstEta d χ η 0 ζ = η (iwRep ζ) := by
  rw [mstEta_eq_mstC, mstC_zero, one_mul]

/-- On the open fundamental domain `Ioo (−1/2) (1/2)` the lift `circleLift (mstEta d χ η 0)` is
`x ↦ η (−x)`. -/
theorem circleLift_mstEta_zero_coe (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    circleLift (mstEta d χ η 0) x = η (-x) := by
  rw [Work.BourgainPlan.Thm52.circleLift_of_mem (Set.Ioo_subset_Ioc_self hx), mstEta_zero_eq]
  have hx' : (-x) ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [Set.mem_Ioo] at hx
    rw [Set.mem_Ioc]
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hcoe : (-(x : Circ)) = ((-x : ℝ) : Circ) := by
    rw [← AddCircle.coe_neg]
  rw [hcoe, iwRep_coe_of_mem hx']

/-- The lift `circleLift (mstEta d χ η 0)` is supported in `Icc (−1/2) (1/2)`. -/
theorem circleLift_mstEta_zero_supp (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    ∀ x : ℝ, x ∉ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) → circleLift (mstEta d χ η 0) x = 0 := by
  refine Work.BourgainPlan.Thm52.circleLift_eq_zero_of_support (a := (1 / 2 : ℝ)) ?_
  intro ξ hξ
  rw [mstEta_zero_eq]
  refine hη2 _ ?_
  rw [← norm_eq_abs_iwRep ξ]
  exact hξ

/-- **The pointwise form of the a.e. identity `η =ᵐ F₀ ∘ (−·)`**, away from the two exceptional
points `±1/2`. -/
theorem eta_eq_circleLift_of_abs_ne (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) {u : ℝ} (h : |u| ≠ 1 / 2) :
    η u = circleLift (mstEta d χ η 0) (-u) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hmem : (-u) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      rw [Set.mem_Ioo]
      rw [abs_lt] at hlt
      exact ⟨by linarith [hlt.2], by linarith [hlt.1]⟩
    rw [circleLift_mstEta_zero_coe d χ η hmem, neg_neg]
  · rw [hη2 u hgt, circleLift_mstEta_zero_supp d χ η hη2 (-u) (by
      intro hx
      rw [Set.mem_Icc] at hx
      have hle : |u| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
      exact absurd (lt_of_lt_of_le hgt hle) (lt_irrefl _))]

/-- **`η` agrees a.e. with the reflected level-`0` lift**: the only possible exceptions are `±1/2`. -/
theorem eta_ae_eq_circleLift_neg (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    (fun u : ℝ => η u) =ᵐ[volume] (fun u : ℝ => circleLift (mstEta d χ η 0) (-u)) := by
  change ∀ᵐ u ∂(volume : Measure ℝ), η u = circleLift (mstEta d χ η 0) (-u)
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (by
    have hfin : (({-(1 / 2 : ℝ), 1 / 2} : Set ℝ)).Finite := Set.toFinite _
    exact hfin.measure_zero volume)
  intro u hu
  by_contra hcon
  have hne : |u| = 1 / 2 := by
    by_contra h'
    exact hu (eta_eq_circleLift_of_abs_ne d χ η hη2 h')
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hne with h' | h'
  · exact hcon (by simp [h'])
  · exact hcon (by simp [h'])

/-- **The scaled identity**: `η (c ·) =ᵐ F₀ ∘ (−(c ·))` for `c ≠ 0`. -/
theorem eta_scaled_ae_eq_circleLift (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => η (c * x))
      =ᵐ[volume] (fun x : ℝ => circleLift (mstEta d χ η 0) (-(c * x))) := by
  change ∀ᵐ x ∂(volume : Measure ℝ), η (c * x) = circleLift (mstEta d χ η 0) (-(c * x))
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (by
    have hfin : (({1 / (2 * c), -(1 / (2 * c))} : Set ℝ)).Finite := Set.toFinite _
    exact hfin.measure_zero volume)
  intro x hx
  by_contra hcon
  have hne : |c * x| = 1 / 2 := by
    by_contra h'
    exact hx (eta_eq_circleLift_of_abs_ne d χ η hη2 h')
  have hxne : |x| = 1 / (2 * c) := by
    rw [abs_mul, abs_of_pos hc] at hne
    field_simp at hne ⊢
    linarith
  rcases (abs_eq (by positivity : (0 : ℝ) ≤ 1 / (2 * c))).mp hxne with h' | h'
  · exact hcon (by simp [h'])
  · exact hcon (by simp [h'])

/-! ## Measurability and boundedness consequences -/

/-- **`η` is a.e. strongly measurable**, from the continuity of the level-`0` lift. -/
theorem aestronglyMeasurable_eta (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (hcont : Continuous (circleLift (mstEta d χ η 0))) :
    AEStronglyMeasurable η (volume : Measure ℝ) :=
  ((hcont.comp continuous_neg).aestronglyMeasurable).congr
    (eta_ae_eq_circleLift_neg d χ η hη2).symm

/-- **`η` is a.e. bounded**, from the continuity of the level-`0` lift. -/
theorem eta_ae_bound (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (hcont : Continuous (circleLift (mstEta d χ η 0))) :
    ∃ M : ℝ, ∀ᵐ x ∂(volume : Measure ℝ), ‖η x‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-(1 / 2) : ℝ) (1 / 2)) hcont.continuousOn
  refine ⟨max M 0, ?_⟩
  filter_upwards [(eta_ae_eq_circleLift_neg d χ η hη2)] with u hu
  rw [hu]
  by_cases hx : (-u) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  · exact le_trans (hM (-u) hx) (le_max_left _ _)
  · rw [circleLift_mstEta_zero_supp d χ η hη2 (-u) hx, norm_zero]
    exact le_max_right _ _

/-- The level-`0` lift is bounded. -/
theorem circleLift_mstEta_zero_bound (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (hcont : Continuous (circleLift (mstEta d χ η 0))) :
    ∃ M : ℝ, ∀ x : ℝ, ‖circleLift (mstEta d χ η 0) x‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-(1 / 2) : ℝ) (1 / 2)) hcont.continuousOn
  refine ⟨max M 0, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  · exact le_trans (hM x hx) (le_max_left _ _)
  · rw [circleLift_mstEta_zero_supp d χ η hη2 x hx, norm_zero]
    exact le_max_right _ _

/-- **The scaled bump `x ↦ η (c x)` is `L^∞` on the fundamental domain** (for `c > 0`). -/
theorem memLp_scaled_eta (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (hcont : Continuous (circleLift (mstEta d χ η 0)))
    {c : ℝ} (hc : 0 < c) :
    MemLp (fun x : ℝ => η (c * x)) ⊤
      (volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (1 / 2))) := by
  set g : ℝ → ℂ := fun x => circleLift (mstEta d χ η 0) (-(c * x)) with hg
  have hcont' : Continuous g := by
    rw [hg]
    exact hcont.comp (((continuous_const (y := c)).mul continuous_id).neg)
  have hbase : MemLp g ⊤ (volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (1 / 2))) :=
    memLp_restrict_Ioc_of_continuous hcont'
  have hae : (fun x : ℝ => η (c * x))
      =ᵐ[volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (1 / 2))] g := by
    rw [hg]
    exact ae_restrict_of_ae (eta_scaled_ae_eq_circleLift d χ η hη2 hc)
  exact (memLp_congr_ae hae).mpr hbase

/-- **The bump `ζ ↦ η (c iwRep ζ)` is `L^∞` on the circle** for `1 ≤ c`. -/
theorem memLp_eta_comp_iwRep (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (hcont : Continuous (circleLift (mstEta d χ η 0)))
    {c : ℝ} (hc : 1 ≤ c) : MemLp (fun ζ : Circ => η (c * iwRep ζ)) ⊤ haar :=
  memLp_comp_iwRep (g := fun x : ℝ => η (c * x)) (memLp_scaled_eta d χ η hη2 hcont (lt_of_lt_of_le zero_lt_one hc))

/-- **The level bump `mstEta d χ η s` is `L^∞` on the circle.** -/
theorem memLp_mstEta (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (hcont : Continuous (circleLift (mstEta d χ η 0)))
    (hd : 1 ≤ d) (hχ0 : 0 ≤ χ) (hχd : χ ≤ (d : ℝ)) (s : ℕ) :
    MemLp (mstEta d χ η s) ⊤ haar := by
  have h := memLp_eta_comp_iwRep d χ η hη2 hcont (c := mstC d χ s)
    (one_le_mstC d χ hd hχ0 hχd s)
  rwa [show (fun ζ : Circ => η (mstC d χ s * iwRep ζ)) = mstEta d χ η s from rfl] at h

end

end Work.BourgainPlan.Maximal
