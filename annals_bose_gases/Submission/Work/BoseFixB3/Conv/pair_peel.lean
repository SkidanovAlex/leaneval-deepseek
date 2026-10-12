import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.CS.highSlot_bound_of_pos
import Submission.Work.BoseFixB3.CS.highSlot_sq_le_of_nonpos
import Submission.Work.BoseFixB3.CS.highSlot_stronglyMeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Conv.pair_peel`

The **pair peel** of FS's convolution step (`lem:Convolution`): inside the `n`-particle box
integral, the pair kernel `χ_ℓ(x_i) f(x_i − x_j) χ_ℓ(x_j)` may be replaced by
`ℓ⁻³ χ_ℓ(x_j) (f ⋆ χ_ℓ)(x_j)`.  The weight multiplying the kernel,
`highSlot fc κ ℓ j (P_iΦ) · P_j P_i Φ`, is independent of the slot-`i` coordinate, so the
`x_i`-integral collapses onto the one-variable identity

  `∫_{acube ℓ} χ_ℓ(y) f (y − z) dy = (f ⋆ χ_ℓ)(z)`

(`chiPeel`), obtained from the support of `χ_ℓ` inside the cube and the evenness of `f`.

## Contents

* `volume_acube_sdiff_interior`, `ae_mem_interior_acube_box`: the boundary of the cube is
  null, so a.e. box point has its coordinates in `interior (acube ℓ)` — this is what makes the
  `κ ≤ 0` branch of the `highSlot` bound work a.e.;
* `chiPeel`: the one-variable identity;
* `integrableOn_sub_coord'`: `x ↦ f (x i − x j)` is integrable on the box;
* `pair_peel`: the target.
-/

noncomputable section
open MeasureTheory
open scoped Topology Real ENNReal

namespace Work.BoseFixB3.Conv

open Submission.BoseGases
open Work.BoseBoxFix

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. Almost every point of the cube and of the box lies in the interior -/

/-- The open box `{y | ∀ m, y m ∈ Ioo (−ℓ/2) (ℓ/2)}` is open. -/
private lemma isOpen_openBox (ℓ : ℝ) :
    IsOpen {y : E3 | ∀ m : Fin 3, y m ∈ Set.Ioo (-ℓ / 2) (ℓ / 2)} := by
  have h : {y : E3 | ∀ m : Fin 3, y m ∈ Set.Ioo (-ℓ / 2) (ℓ / 2)} =
      ⋂ m : Fin 3, {y : E3 | y m ∈ Set.Ioo (-ℓ / 2) (ℓ / 2)} := by
    ext y
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun m =>
    isOpen_Ioo.preimage (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) m)

/-- The open box is contained in the interior of the closed cube. -/
private lemma openBox_subset_interior_acube (ℓ : ℝ) :
    {y : E3 | ∀ m : Fin 3, y m ∈ Set.Ioo (-ℓ / 2) (ℓ / 2)}
      ⊆ interior (Submission.BoseGases.acube ℓ) := by
  refine interior_maximal ?_ (isOpen_openBox ℓ)
  intro y hy
  rw [Submission.BoseGases.mem_acube_iff]
  intro m
  exact Set.mem_Icc.mpr ⟨le_of_lt (hy m).1, le_of_lt (hy m).2⟩

/-- Each coordinate hyperplane `{y : ℝ³ | y m = c}` has zero volume. -/
private lemma volume_coord_eq_zero (m : Fin 3) (c : ℝ) :
    (volume : Measure E3) {y : E3 | y m = c} = 0 := by
  have hH' : (volume : Measure (Fin 3 → ℝ)) {x : Fin 3 → ℝ | x m = c} = 0 :=
    MeasureTheory.Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) m c
  have hmeas : MeasurableSet {x : Fin 3 → ℝ | x m = c} :=
    (isClosed_singleton.preimage (continuous_apply m)).measurableSet
  have hset : {y : E3 | y m = c} = ⇑Submission.BoseGases.cgEuc3 '' {x : Fin 3 → ℝ | x m = c} := by
    ext y
    constructor
    · intro hy
      refine ⟨Submission.BoseGases.cgEuc3.symm y, ?_, by simp⟩
      simpa [Submission.BoseGases.cgEuc3] using hy
    · rintro ⟨x, hx, rfl⟩
      simpa [Submission.BoseGases.cgEuc3] using hx
  rw [hset]
  conv_lhs => rw [← Submission.BoseGases.cgEuc3_mp.map_eq]
  rw [MeasureTheory.Measure.map_apply Submission.BoseGases.cgEuc3_mp.measurable
    (Submission.BoseGases.cgEuc3.measurableSet_image.2 hmeas)]
  rw [Set.preimage_image_eq _ (MeasurableEquiv.injective Submission.BoseGases.cgEuc3)]
  exact hH'

/-- The boundary of the centred cube has zero volume. -/
private lemma volume_acube_sdiff_interior (ℓ : ℝ) :
    (volume : Measure E3) (Submission.BoseGases.acube ℓ \ interior (Submission.BoseGases.acube ℓ))
      = 0 := by
  have hsub : Submission.BoseGases.acube ℓ \ interior (Submission.BoseGases.acube ℓ)
      ⊆ ⋃ m : Fin 3, {y : E3 | y m = -ℓ / 2 ∨ y m = ℓ / 2} := by
    intro y hy
    rw [Set.mem_sdiff] at hy
    obtain ⟨hyacube, hyint⟩ := hy
    rw [Submission.BoseGases.mem_acube_iff] at hyacube
    have hnot : ¬ ∀ m : Fin 3, y m ∈ Set.Ioo (-ℓ / 2) (ℓ / 2) := fun h =>
      hyint (openBox_subset_interior_acube ℓ h)
    simp only [not_forall] at hnot
    obtain ⟨m, hm⟩ := hnot
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hm
    rw [Set.mem_iUnion]
    refine ⟨m, ?_⟩
    rcases hm with h | h
    · exact Or.inl (le_antisymm h (hyacube m).1)
    · exact Or.inr (le_antisymm (hyacube m).2 h)
  refine measure_mono_null hsub ?_
  rw [measure_iUnion_null_iff]
  intro m
  have hset : {y : E3 | y m = -ℓ / 2 ∨ y m = ℓ / 2}
      = {y : E3 | y m = -ℓ / 2} ∪ {y : E3 | y m = ℓ / 2} := by
    ext y
    simp
  rw [hset, measure_union_null_iff]
  exact ⟨volume_coord_eq_zero m (-ℓ / 2), volume_coord_eq_zero m (ℓ / 2)⟩

/-- Almost every point of the centred cube lies in its interior. -/
private lemma ae_mem_interior_acube {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ y ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)),
      y ∈ interior (Submission.BoseGases.acube ℓ) := by
  rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.acube_measurable ℓ),
    MeasureTheory.ae_iff]
  have hset : {y : E3 | ¬ (y ∈ Submission.BoseGases.acube ℓ →
      y ∈ interior (Submission.BoseGases.acube ℓ))}
      = Submission.BoseGases.acube ℓ \ interior (Submission.BoseGases.acube ℓ) := by
    ext y
    simp
  rw [hset]
  exact volume_acube_sdiff_interior ℓ

/-- Almost every point of the `n`-particle box has its slot-`j` coordinate in the
interior of the centred cube. -/
theorem ae_mem_interior_acube_box {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) :
    ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ)), x j ∈ interior (Submission.BoseGases.acube ℓ) := by
  have hν0 : ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      {y : E3 | ¬ y ∈ interior (Submission.BoseGases.acube ℓ)} = 0 :=
    MeasureTheory.ae_iff.mp (ae_mem_interior_acube hℓ)
  rw [Submission.BoseGases.restrict_abox_eq_pi n ℓ, MeasureTheory.ae_iff]
  have hpi := MeasureTheory.Measure.pi_eval_preimage_null
    (fun _ : Fin n => (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) (i := j) hν0
  simpa using hpi

/-! ## 2. The one-variable identity -/

/-- `∫_{acube ℓ} χ_ℓ(y) f (y − z) dy = (f ⋆ χ_ℓ)(z)` for even `f` and `0 < ℓ`. -/
lemma chiPeel {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℝ} (hf : MeasureTheory.Integrable f)
    (hfeven : ∀ x : E3, f (-x) = f x) (z : E3) :
    (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.chiScale ℓ y * f (y - z))
      = Submission.BoseGases.conv3 f (fun w => Submission.BoseGases.chi ((ℓ⁻¹) • w)) z := by
  have hsupp : ∀ y : E3, y ∉ Submission.BoseGases.acube ℓ →
      Submission.BoseGases.chiScale ℓ y * f (y - z) = 0 := by
    intro y hy
    have h0 : Submission.BoseGases.chiScale ℓ y = 0 := by
      by_contra hne
      refine hy ?_
      rw [Submission.BoseGases.mem_acube_iff]
      intro m
      have h1 : |y m| ≤ ℓ / 2 := by
        calc |y m| = ‖y m‖ := (Real.norm_eq_abs (y m)).symm
          _ ≤ ‖y‖ := PiLp.norm_apply_le y m
          _ ≤ ℓ / 2 := Submission.BoseGases.chiScale_support_le hℓ hne
      have h2 := abs_le.mp h1
      exact ⟨by linarith [h2.1], h2.2⟩
    rw [h0, zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  have hsub := Submission.BoseGases.integral_comp_sub_left
    (fun w : E3 => Submission.BoseGases.chiScale ℓ w * f (w - z)) z
  rw [← hsub]
  rw [Submission.BoseGases.conv3]
  apply integral_congr_ae
  filter_upwards with w
  have hw : (z - w) - z = -w := by abel
  rw [hw, hfeven w, mul_comm]
  rfl

/-! ## 3. Integrability of the relative coordinate on the box -/

/-- If `v =ᵐ w` on `ℝ³` then the relative profiles `x ↦ v (x i − x j)` and `x ↦ w (x i − x j)`
agree a.e. on the box (the difference set pulls back to a null set). -/
private lemma abox_ae_pair_of_ae {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v w : E3 → ℝ}
    (hvw : v =ᵐ[volume] w) (i j : Fin n) (hij : i ≠ j) :
    (fun x : Submission.BoseGases.X n => v (x i - x j))
      =ᵐ[volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun x : Submission.BoseGases.X n => w (x i - x j)) := by
  have hN : volume {y : E3 | v y ≠ w y} = 0 := by
    rw [← MeasureTheory.ae_iff]
    exact hvw
  obtain ⟨t, hNt, htm, ht0⟩ :=
    exists_measurable_superset_of_null (μ := (volume : Measure E3)) hN
  have hpre : (volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ) {x : Submission.BoseGases.X n | x i - x j ∈ t} = 0 :=
    Submission.BoseGases.abox_null_preimage_pair hℓ htm ht0 i j hij
  have hfail : (volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ)
      {x : Submission.BoseGases.X n | v (x i - x j) ≠ w (x i - x j)} = 0 :=
    measure_mono_null (fun x hx => hNt hx) hpre
  rw [show ((fun x : Submission.BoseGases.X n => v (x i - x j))
        =ᵐ[volume.restrict (Submission.BoseGases.abox n ℓ)]
        (fun x : Submission.BoseGases.X n => w (x i - x j)))
      ↔ {x : Submission.BoseGases.X n | v (x i - x j) = w (x i - x j)}
          ∈ ae (volume.restrict (Submission.BoseGases.abox n ℓ)) from Iff.rfl]
  rw [mem_ae_iff,
    show ({x : Submission.BoseGases.X n | v (x i - x j) = w (x i - x j)})ᶜ
      = {x : Submission.BoseGases.X n | v (x i - x j) ≠ w (x i - x j)} by
        ext x; simp]
  exact hfail

/-- `x ↦ f (x i − x j)` is integrable on the box for `0 < ℓ` and `f` integrable. -/
lemma integrableOn_sub_coord' {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {f : E3 → ℝ} (hf : MeasureTheory.Integrable f) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => f (x i - x j))
      (Submission.BoseGases.abox n ℓ) volume := by
  set w : E3 → ℝ := hf.aemeasurable.mk with hw
  have hwm : Measurable w := hf.aemeasurable.measurable_mk
  have hwae : f =ᵐ[volume] w := hf.aemeasurable.ae_eq_mk
  have hwInt : MeasureTheory.Integrable w := hf.congr hwae
  have hwa : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => |w (x i - x j)|)
      (Submission.BoseGases.abox n ℓ) volume :=
    Submission.BoseGases.integrableOn_abs_sub_abox hℓ hwInt i j hij
  have hwaesm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => w (x i - x j))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    (hwm.comp (by fun_prop : Measurable fun x : Submission.BoseGases.X n => x i - x j)).aestronglyMeasurable
  have hwsub : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => w (x i - x j))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    refine hwa.mono' hwaesm ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
  have hae := abox_ae_pair_of_ae hℓ hwae i j hij
  exact hwsub.congr hae.symm

lemma highSlot_update_eq {fc : LowCut} {κ ℓ : ℝ} {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Ψ : X n → ℝ} (hΨinv : ∀ (x : X n) (z : E3), Ψ (Function.update x i z) = Ψ x)
    (x : X n) (z : E3) :
    highSlot fc κ ℓ j Ψ (Function.update x i z) = highSlot fc κ ℓ j Ψ x := by
  have h2 : lowSlot fc κ ℓ j Ψ (Function.update x i z) = lowSlot fc κ ℓ j Ψ x := by
    simp only [lowSlot]
    have hfun : (fun w : E3 => Ψ (Function.update (Function.update x i z) j w))
        = (fun w : E3 => Ψ (Function.update x j w)) := by
      funext w
      rw [Function.update_comm hij z w x]
      exact hΨinv (Function.update x j w) z
    rw [hfun, Function.update_of_ne (Ne.symm hij) z x]
  simp only [highSlot]
  rw [h2, hΨinv x z]

theorem pair_peel {n : ℕ} {ℓ κ : ℝ} (fc : Work.BoseBoxFix.LowCut) (hℓ : 0 < ℓ)
    {i j : Fin n} (hij : i ≠ j) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : MeasureTheory.Integrable f)
    (hfeven : ∀ x : EuclideanSpace ℝ (Fin 3), f (-x) = f x) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * (Submission.BoseGases.chiScale ℓ (x i) * f (x i - x j) * Submission.BoseGases.chiScale ℓ (x j)))
      = (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
            * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
            * (Submission.BoseGases.chiScale ℓ (x j)
                * Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) (x j)) := by
  -- A box needs at least one particle
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fin.pos i))
  -- Notations
  set Ψ : X (m + 1) → ℝ := Submission.BoseGases.aP ℓ i Φ with hΨ
  have hΨc : Continuous Ψ := by rw [hΨ]; exact Submission.BoseGases.aP_continuous hℓ i hΦ
  set H : X (m + 1) → ℝ := fun x => Work.BoseFixB3.highSlot fc κ ℓ j Ψ x * Submission.BoseGases.aP ℓ j Ψ x
    with hH
  set G₁ : X (m + 1) → ℝ := fun x =>
    Submission.BoseGases.chiScale ℓ (x i) * f (x i - x j) * Submission.BoseGases.chiScale ℓ (x j)
    with hG₁
  set G₂ : X (m + 1) → ℝ := fun x => Submission.BoseGases.chiScale ℓ (x j)
    * Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) (x j) with hG₂
  change (∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x * G₁ x)
    = (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x * G₂ x
  -- Index bookkeeping: `j` is the image of some `k : Fin m` under `i.succAbove`
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
  have hcoord : ∀ (y : E3) (r : X m), (Submission.BoseGases.kcInsN m i (y, r)) j = r k := by
    intro y r
    rw [← hk]
    exact Submission.BoseGases.kc_insN_apply_succ m i y r k
  have hcoord0 : ∀ r : X m, (Submission.BoseGases.kcInsN m i (0, r)) j = r k := fun r => hcoord 0 r
  -- Invariance of `H` and of `G₂` in the slot `i`
  have hHinv : ∀ (x : X (m + 1)) (z : E3), H (Function.update x i z) = H x := by
    intro x z
    have h1 : Work.BoseFixB3.highSlot fc κ ℓ j Ψ (Function.update x i z)
        = Work.BoseFixB3.highSlot fc κ ℓ j Ψ x :=
      highSlot_update_eq (Ψ := Ψ) hij
        (fun x z => Submission.BoseGases.aP_const_in_coord hℓ i hΦ x z) x z
    have h2 : Submission.BoseGases.aP ℓ j Ψ (Function.update x i z)
        = Submission.BoseGases.aP ℓ j Ψ x :=
      Submission.BoseGases.aP_pair_const_in_j (ℓ := ℓ) hℓ (i := j) (j := i) (Ne.symm hij) hΦ x z
    rw [hH]
    simp only
    rw [h1, h2]
  have hHins : ∀ (y : E3) (r : X m),
      H (Submission.BoseGases.kcInsN m i (y, r)) = H (Submission.BoseGases.kcInsN m i (0, r)) := by
    intro y r
    rw [Submission.BoseGases.kcInsN_update_zero i y r]
    exact hHinv (Submission.BoseGases.kcInsN m i (0, r)) y
  have hG₂ins : ∀ (y : E3) (r : X m),
      G₂ (Submission.BoseGases.kcInsN m i (y, r)) = G₂ (Submission.BoseGases.kcInsN m i (0, r)) := by
    intro y r
    simp only [hG₂]
    rw [Submission.BoseGases.kc_insN_other_indep m i y 0 r j (Ne.symm hij),
      Submission.BoseGases.kc_insN_other_indep m i 0 0 r j (Ne.symm hij)]
  -- The peel at the slot `i`
  set μ' : Measure E3 := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) with hμ'
  set ν : Measure (X m) := (volume : Measure (X m)).restrict (Submission.BoseGases.abox m ℓ) with hν
  have hmp : MeasurePreserving (⇑(Submission.BoseGases.kcInsN m i)) (μ'.prod ν)
      ((volume : Measure (X (m + 1))).restrict (Submission.BoseGases.abox (m + 1) ℓ)) := by
    have h := MeasurePreserving.symm
      (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E3) i)
      (Submission.BoseGases.abox_peel_mp m ℓ i)
    simpa [Submission.BoseGases.kcInsN, hμ', hν] using h
  have hpeel : ∀ F : X (m + 1) → ℝ, (∫ x in Submission.BoseGases.abox (m + 1) ℓ, F x)
      = ∫ p : E3 × X m, F (Submission.BoseGases.kcInsN m i p) ∂(μ'.prod ν) := by
    intro F
    exact (hmp.integral_comp' F).symm
  -- A uniform bound for `Ψ` and for `P_jΨ` on the box
  obtain ⟨C₀, hC₀⟩ :=
    (Work.UBBInputs9.B.abox_isCompact (m + 1) ℓ).exists_bound_of_continuousOn hΨc.continuousOn
  set M : ℝ := max C₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hΨb : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |Ψ x| ≤ M := by
    intro x hx
    have h := hC₀ x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  have haPb : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |Submission.BoseGases.aP ℓ j Ψ x| ≤ M :=
    Submission.BoseGases.aP_abs_le hℓ j hΨc hM0 hΨb
  -- The a.e. bound on `highSlot` (the two signs of `κ`)
  have hhs : ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ x ∂((volume : Measure (X (m + 1))).restrict
      (Submission.BoseGases.abox (m + 1) ℓ)),
      |Work.BoseFixB3.highSlot fc κ ℓ j Ψ x| ≤ K := by
    by_cases hκ : 0 < κ
    · obtain ⟨C, hC0, hC⟩ := Work.BoseFixB3.CS.highSlot_bound_of_pos (fc := fc) hκ hℓ j hΨc
      exact ⟨C, hC0, (ae_restrict_iff' (Submission.BoseGases.abox_measurable (m + 1) ℓ)).mpr
        (ae_of_all _ (fun x hx => hC x hx))⟩
    · refine ⟨2 * M, by positivity, ?_⟩
      filter_upwards [ae_mem_interior_acube_box (ℓ := ℓ) hℓ j,
        self_mem_ae_restrict (Submission.BoseGases.abox_measurable (m + 1) ℓ)] with x hxint hxmem
      have hx := Work.BoseFixB3.CS.highSlot_sq_le_of_mem_interior (fc := fc) (κ := κ) (ℓ := ℓ)
        (le_of_not_gt hκ) hℓ j hΨc hxint
      have hΨM : (Ψ x) ^ 2 ≤ M ^ 2 := by
        have h1 : |Ψ x| ≤ M := hΨb x hxmem
        calc (Ψ x) ^ 2 = |Ψ x| ^ 2 := (sq_abs _).symm
          _ ≤ |M| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by simpa [abs_of_nonneg hM0] using h1) 2
          _ = M ^ 2 := by rw [abs_of_nonneg hM0]
      have hsq : |Work.BoseFixB3.highSlot fc κ ℓ j Ψ x| ^ 2 ≤ (2 * M) ^ 2 := by
        calc |Work.BoseFixB3.highSlot fc κ ℓ j Ψ x| ^ 2
            = (Work.BoseFixB3.highSlot fc κ ℓ j Ψ x) ^ 2 := by rw [sq_abs]
          _ ≤ 4 * (Ψ x) ^ 2 := hx
          _ ≤ 4 * M ^ 2 := by linarith
          _ = (2 * M) ^ 2 := by ring
      have h2M0 : (0 : ℝ) ≤ 2 * M := by positivity
      have hfin := sq_le_sq.mp hsq
      rw [abs_of_nonneg h2M0] at hfin
      simpa using hfin
  obtain ⟨K, hK0, hK⟩ := hhs
  -- A.e. bound on `H`
  have hHK : ∀ᵐ x ∂((volume : Measure (X (m + 1))).restrict
      (Submission.BoseGases.abox (m + 1) ℓ)), |H x| ≤ K * M := by
    filter_upwards [hK, self_mem_ae_restrict (Submission.BoseGases.abox_measurable (m + 1) ℓ)]
      with x hx hxmem
    have haP := haPb x hxmem
    have h1 : H x = Work.BoseFixB3.highSlot fc κ ℓ j Ψ x * Submission.BoseGases.aP ℓ j Ψ x := by
      rw [hH]
    rw [h1, abs_mul]
    exact mul_le_mul hx haP (abs_nonneg _) hK0
  -- Integrability of `G₁` and of `H * G₁` on the box
  have hfsub : IntegrableOn (fun x : X (m + 1) => f (x i - x j))
      (Submission.BoseGases.abox (m + 1) ℓ) volume :=
    integrableOn_sub_coord' hℓ hij hf
  have hchi_ae : AEStronglyMeasurable
      (fun x : X (m + 1) => Submission.BoseGases.chiScale ℓ (x i) * Submission.BoseGases.chiScale ℓ (x j))
      (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) :=
    (((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)).mul
      ((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply j))).aestronglyMeasurable
  have hchi_bdd : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)),
      ‖Submission.BoseGases.chiScale ℓ (x i) * Submission.BoseGases.chiScale ℓ (x j)‖
        ≤ ((Real.sqrt Submission.BoseGases.chiNormSq)⁻¹) ^ 2 := by
    refine ae_of_all _ (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hc : (0 : ℝ) ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    calc |Submission.BoseGases.chiScale ℓ (x i)| * |Submission.BoseGases.chiScale ℓ (x j)|
        ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
          * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
          mul_le_mul (Submission.BoseGases.abs_chiScale_le ℓ (x i))
            (Submission.BoseGases.abs_chiScale_le ℓ (x j)) (abs_nonneg _) hc
      _ = ((Real.sqrt Submission.BoseGases.chiNormSq)⁻¹) ^ 2 := by ring
  have hG₁int : Integrable (fun x : X (m + 1) => G₁ x)
      (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) := by
    rw [hG₁]
    have h := hfsub.mul_bdd hchi_ae hchi_bdd
    simpa only [Pi.mul_apply, mul_assoc, mul_comm, mul_left_comm] using h
  have hHae : AEStronglyMeasurable H (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) := by
    rw [hH]
    exact (StronglyMeasurable.mul
      (Work.BoseFixB3.CS.highSlot_stronglyMeasurable (fc := fc) (κ := κ) (ℓ := ℓ) j hΨc)
      (Submission.BoseGases.aP_continuous hℓ j hΨc).stronglyMeasurable).aestronglyMeasurable
  have hFG : Integrable (fun x : X (m + 1) => H x * G₁ x)
      (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) := by
    refine Integrable.mono' ((hG₁int.norm).const_mul (K * M)) (hHae.mul hG₁int.aestronglyMeasurable) ?_
    filter_upwards [hHK] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hFGint : Integrable (fun p : E3 × X m =>
      H (Submission.BoseGases.kcInsN m i p) * G₁ (Submission.BoseGases.kcInsN m i p)) (μ'.prod ν) :=
    (hmp.integrable_comp (g := fun x => H x * G₁ x) (hHae.mul hG₁int.aestronglyMeasurable)).mpr hFG
  -- The peeled form of the left-hand side
  have hkey : (∫ p : E3 × X m,
        H (Submission.BoseGases.kcInsN m i p) * G₁ (Submission.BoseGases.kcInsN m i p) ∂(μ'.prod ν))
      = ∫ r : X m, H (Submission.BoseGases.kcInsN m i (0, r)) * G₂ (Submission.BoseGases.kcInsN m i (0, r)) ∂ν := by
    rw [MeasureTheory.integral_prod_symm _ hFGint]
    apply integral_congr_ae
    filter_upwards with r
    have hinner : (∫ y : E3, H (Submission.BoseGases.kcInsN m i (y, r))
          * G₁ (Submission.BoseGases.kcInsN m i (y, r)) ∂μ')
        = H (Submission.BoseGases.kcInsN m i (0, r)) * G₂ (Submission.BoseGases.kcInsN m i (0, r)) := by
      have h1 : (∫ y : E3, H (Submission.BoseGases.kcInsN m i (y, r))
            * G₁ (Submission.BoseGases.kcInsN m i (y, r)) ∂μ')
          = ∫ y : E3, H (Submission.BoseGases.kcInsN m i (0, r))
            * G₁ (Submission.BoseGases.kcInsN m i (y, r)) ∂μ' := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hHins y r]
      rw [h1, MeasureTheory.integral_const_mul]
      congr 1
      -- the one-variable identity, on the fibre
      have hG₁eq : ∀ y : E3, G₁ (Submission.BoseGases.kcInsN m i (y, r))
          = Submission.BoseGases.chiScale ℓ y * f (y - r k) * Submission.BoseGases.chiScale ℓ (r k) := by
        intro y
        simp only [hG₁, Submission.BoseGases.kc_insN_apply_same m i y r, hcoord y r]
      have hstep : (∫ y : E3, Submission.BoseGases.chiScale ℓ y * f (y - r k)
            * Submission.BoseGases.chiScale ℓ (r k) ∂μ')
          = Submission.BoseGases.chiScale ℓ (r k)
            * Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) (r k) := by
        rw [MeasureTheory.integral_mul_const, chiPeel hℓ hf hfeven (r k), mul_comm]
      calc (∫ y : E3, G₁ (Submission.BoseGases.kcInsN m i (y, r)) ∂μ')
          = ∫ y : E3, Submission.BoseGases.chiScale ℓ y * f (y - r k)
              * Submission.BoseGases.chiScale ℓ (r k) ∂μ' := by
            apply integral_congr_ae
            filter_upwards with y
            exact hG₁eq y
        _ = Submission.BoseGases.chiScale ℓ (r k)
              * Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) (r k) := hstep
        _ = G₂ (Submission.BoseGases.kcInsN m i (0, r)) := by
            simp only [hG₂, hcoord0 r]
    rw [hinner]
  -- The peeled form of the right-hand side
  have hrhs : (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x * G₂ x
      = ∫ r : X m, H (Submission.BoseGases.kcInsN m i (0, r))
          * G₂ (Submission.BoseGases.kcInsN m i (0, r)) ∂ν := by
    rw [hpeel (fun x => H x * G₂ x)]
    have h1 : (∫ p : E3 × X m, H (Submission.BoseGases.kcInsN m i p)
          * G₂ (Submission.BoseGases.kcInsN m i p) ∂(μ'.prod ν))
        = ∫ p : E3 × X m, H (Submission.BoseGases.kcInsN m i (0, p.2))
          * G₂ (Submission.BoseGases.kcInsN m i (0, p.2)) ∂(μ'.prod ν) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hHins p.1 p.2, hG₂ins p.1 p.2]
    rw [h1]
    have h2 : (∫ p : E3 × X m, H (Submission.BoseGases.kcInsN m i (0, p.2))
          * G₂ (Submission.BoseGases.kcInsN m i (0, p.2)) ∂(μ'.prod ν))
        = ∫ p : E3 × X m, (1 : ℝ) * (H (Submission.BoseGases.kcInsN m i (0, p.2))
          * G₂ (Submission.BoseGases.kcInsN m i (0, p.2))) ∂(μ'.prod ν) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [one_mul]
    rw [h2]
    have hprod := MeasureTheory.integral_prod_mul (μ := μ') (ν := ν)
      (f := fun _ : E3 => (1 : ℝ))
      (g := fun r : X m => H (Submission.BoseGases.kcInsN m i (0, r))
        * G₂ (Submission.BoseGases.kcInsN m i (0, r)))
    rw [hprod]
    rw [show (∫ y : E3, (1 : ℝ) ∂μ') = ℓ ^ 3 from by
      rw [show (∫ y : E3, (1 : ℝ) ∂μ') = ∫ y in Submission.BoseGases.acube ℓ, (1 : ℝ) from rfl,
        Submission.BoseGases.integral_const_acube ℓ hℓ 1]
      ring]
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (ℓ : ℝ) ^ 3 ≠ 0), one_mul]
  rw [hpeel (fun x => H x * G₁ x), hrhs]
  exact hkey


end Work.BoseFixB3.Conv
