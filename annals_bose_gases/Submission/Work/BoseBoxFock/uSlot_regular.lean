import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.BoxFockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.uSlot_regular` — the integrability of the condensate slot row

The condensate row of the box ↔ model dictionary (`BF3b`, `BOSE_BOXFOCK_LEAD.md`) is proved in
`Submission/Work/BoseBoxFock/uSlot_int_eq_aPC.lean` as the identity

    `Re ∫_{abox d ℓ} conj Θ · Σ_j uSlot u j Θ = Σ_j ∫_{abox d ℓ} ‖aPC ℓ j Θ‖²`,

whose two sides *both* contain improper integrals (`uSlot` and `aPC` are themselves `z`-integrals
of `Θ`), so that module has to carry the `IntegrableOn` inputs as hypotheses.  This file supplies
them from the standing hypotheses of the bridge: `u` is the pinned condensate vector
`u =ᵐ c·θ_Λ` with `conj c · c = ℓ⁻³`, and `Θ` is an a.e.-bounded, a.e. strongly measurable state
supported in the box.

Content (all `sorry`-free):

* `qmp_update_Xn_aux` — the slice map `(x,z) ↦ Function.update x j z` is *quasi*-measure-
  preserving for Lebesgue measure (its fibres are lines; it is *not* a projection, so this is a
  real statement).  This is a self-contained copy of
  `Work.FibreWord.quasiMeasurePreserving_update` (reproduced so that this module needs nothing
  beyond `Mathlib` and `BoxFockDefs`).
* `ae_slice_bound_aux` — hence an a.e. bound on `Θ` propagates to an a.e. bound on every slice;
* `aPC_aesm_aux` — `aPC ℓ j Θ` is a.e. strongly measurable on the box when `Θ` is;
* `aPC_ae_bound_aux` — `‖aPC ℓ j Θ‖ ≤ C` a.e. on the box, with the same `C`;
* `uSlot_eq_mul_setIntegral_aux` / `uSlot_ae_eq_aPC_aux` — the pointwise collapse of the slot
  operator: on the box, `uSlot u j Θ =ᵐ aPC ℓ j Θ` (the `c·conj c = ℓ⁻³` normalisation);
* the target `uSlot_regular`, whose two conjuncts are then `IntegrableOn.of_bound` applied to
  the a.e. bounds `‖conj Θ‖ ≤ C` and `‖aPC ℓ j Θ‖ ≤ C`.
-/

noncomputable section

open MeasureTheory
open scoped Topology BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

local notation "Sp" => Work.BoseDict.Sp

/-- The box indicator `thetaFun ℓ` is real-valued, hence fixed by conjugation. -/
theorem conj_thetaFun_aux {ℓ : ℝ} (z : Sp) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ z)
      = Work.BoseK15.corpusBox.thetaFun ℓ z := by
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  split <;> simp

/-! ## 1. The slice map is quasi-measure-preserving -/

/-- The slice map `(x,z) ↦ Function.update x i z` (one coordinate replaced) is
quasi-measure-preserving for Lebesgue measure on the `(m+1)`-particle configuration space.
Factored through `MeasurableEquiv.piFinSuccAbove`, the map is `((a,b),z) ↦ (z,b)`, i.e. a
projection followed by a swap. -/
theorem qmp_update_Xn_succ_aux (m : ℕ) (i : Fin (m + 1)) :
    Measure.QuasiMeasurePreserving
      (fun p : Work.BoseDict.Xn (m + 1) × Sp => Function.update p.1 i p.2)
      (volume : Measure (Work.BoseDict.Xn (m + 1) × Sp))
      (volume : Measure (Work.BoseDict.Xn (m + 1))) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Sp) i
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => Sp) i
  have hS : Measure.QuasiMeasurePreserving
      (fun p : (Sp × (Fin m → Sp)) × Sp => (p.2, p.1.2)) volume volume :=
    (Measure.measurePreserving_swap (μ := volume) (ν := volume)).quasiMeasurePreserving.comp
      (QuasiMeasurePreserving.prodMap Measure.quasiMeasurePreserving_snd
        (Measure.QuasiMeasurePreserving.id volume))
  have hT : (fun p : Work.BoseDict.Xn (m + 1) × Sp => Function.update p.1 i p.2)
      = e.symm ∘ (fun p : (Sp × (Fin m → Sp)) × Sp => (p.2, p.1.2)) ∘ Prod.map e id := by
    funext p
    obtain ⟨x, z⟩ := p
    simp only [Function.comp_apply, Prod.map, id_eq]
    have h1 : e (Function.update x i z) = (z, i.removeNth x) := by
      rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
        ← Fin.insertNth_removeNth, Fin.insertNth_apply_same, Fin.removeNth_insertNth]
    have h2 : (e x).2 = i.removeNth x := by
      rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
    rw [← e.symm_apply_apply (Function.update x i z), h1, h2]
  rw [hT]
  exact (he.symm.quasiMeasurePreserving).comp
    (hS.comp ((MeasurePreserving.prod he (MeasurePreserving.id volume)).quasiMeasurePreserving))

/-- The slice map at every particle number. -/
theorem qmp_update_Xn_aux {d : ℕ} (j : Fin d) :
    Measure.QuasiMeasurePreserving
      (fun p : Work.BoseDict.Xn d × Sp => Function.update p.1 j p.2)
      (volume : Measure (Work.BoseDict.Xn d × Sp))
      (volume : Measure (Work.BoseDict.Xn d)) := by
  match d, j with
  | m + 1, i => exact qmp_update_Xn_succ_aux m i

/-! ## 2. A.e. bounds propagate to the slices -/

/-- **A.e. boundedness propagates to the slices.**  If `‖Θ‖ ≤ C` a.e. on the configuration
space, then for a.e. `x` in the box and a.e. `z` in the cube the slice value `Θ (x ←_j z)` is
bounded by `C`. -/
theorem ae_slice_bound_aux {d : ℕ} (j : Fin d) {ℓ C : ℝ} {Θ : Work.BoseDict.Xn d → ℂ}
    (hΘb : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)),
      ‖Θ x‖ ≤ C) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)),
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)),
        ‖Θ (Function.update x j z)‖ ≤ C := by
  have h1 : ∀ᵐ p ∂(MeasureTheory.volume :
        MeasureTheory.Measure (Work.BoseDict.Xn d × Sp)),
      ‖Θ (Function.update p.1 j p.2)‖ ≤ C := by
    rw [MeasureTheory.ae_iff] at hΘb ⊢
    simpa using (qmp_update_Xn_aux j).preimage_null hΘb
  have h2 := Measure.ae_ae_of_ae_prod h1
  have h3 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)),
      ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
        ‖Θ (Function.update x j z)‖ ≤ C :=
    MeasureTheory.ae_mono Measure.restrict_le_self h2
  filter_upwards [h3] with x hx
  exact MeasureTheory.ae_mono Measure.restrict_le_self hx

/-! ## 3. `aPC` is a.e. strongly measurable and a.e. bounded on the box -/

/-- **`aPC ℓ j Θ` is a.e. strongly measurable on the box** when `Θ` is a.e. strongly measurable:
it is a partial Bochner integral of the jointly a.e. strongly measurable function
`(x,z) ↦ Θ (x ←_j z)`. -/
theorem aPC_aesm_aux {d : ℕ} (j : Fin d) {ℓ : ℝ} {Θ : Work.BoseDict.Xn d → ℂ}
    (hΘm : MeasureTheory.AEStronglyMeasurable Θ
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d))) :
    MeasureTheory.AEStronglyMeasurable (Work.BoseBoxFock.aPC ℓ j Θ)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)) := by
  obtain ⟨Θ', hΘ'sm, hΘ'eq⟩ := hΘm
  have hmeas_upd : Measurable
      (fun p : Work.BoseDict.Xn d × Sp => Function.update p.1 j p.2) := by
    have hfun : (fun p : Work.BoseDict.Xn d × Sp => Function.update p.1 j p.2)
        = fun p i => if i = j then p.2 else p.1 i := by
      funext p i; rw [Function.update_apply]
    rw [hfun]
    refine measurable_pi_iff.mpr (fun i => ?_)
    by_cases hi : i = j
    · subst hi; simpa using measurable_snd
    · simp only [if_neg hi]; exact (measurable_pi_apply i).comp measurable_fst
  have hcomp : (fun p : Work.BoseDict.Xn d × Sp => Θ (Function.update p.1 j p.2))
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d × Sp))]
      (fun p => Θ' (Function.update p.1 j p.2)) :=
    (qmp_update_Xn_aux j).ae_eq hΘ'eq
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : Work.BoseDict.Xn d × Sp => Θ (Function.update p.1 j p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)).prod
        (MeasureTheory.volume : MeasureTheory.Measure Sp)) :=
    (hΘ'sm.comp_measurable hmeas_upd).aestronglyMeasurable.congr hcomp.symm
  have hmono : (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict (Submission.BoseGases.acube ℓ))
      ≤ (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)).prod
        (MeasureTheory.volume : MeasureTheory.Measure Sp) :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hjoint' : MeasureTheory.AEStronglyMeasurable
      (fun p : Work.BoseDict.Xn d × Sp => Θ (Function.update p.1 j p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
          (Submission.BoseGases.acube ℓ))) :=
    hjoint.mono_measure hmono
  have hpi : MeasureTheory.AEStronglyMeasurable
      (fun x : Work.BoseDict.Xn d => ∫ z : Sp,
        Θ (Function.update x j z)
        ∂((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
          (Submission.BoseGases.acube ℓ)))
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)) :=
    hjoint'.integral_prod_right'
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun x : Work.BoseDict.Xn d => ((1 / ℓ ^ 3 : ℝ) : ℂ) * ∫ z : Sp,
        Θ (Function.update x j z)
        ∂((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
          (Submission.BoseGases.acube ℓ)))
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)) :=
    hpi.const_mul _
  exact h2.restrict (s := Submission.BoseGases.abox d ℓ)

/-- **`aPC ℓ j Θ` is a.e. bounded by `C` on the box**, for the same `C` that bounds `Θ`. -/
theorem aPC_ae_bound_aux {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin d)
    {Θ : Work.BoseDict.Xn d → ℂ} {C : ℝ}
    (hΘb : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)),
      ‖Θ x‖ ≤ C) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)),
      ‖Work.BoseBoxFock.aPC ℓ j Θ x‖ ≤ C := by
  have hsl := ae_slice_bound_aux (ℓ := ℓ) j hΘb
  filter_upwards [hsl] with x hx
  haveI : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
        (Submission.BoseGases.acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
  have hreal : ((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
      (Submission.BoseGases.acube ℓ)).real Set.univ = ℓ ^ 3 := by
    rw [Measure.real, Measure.restrict_apply_univ,
      Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  have hIntBound : ‖∫ z in Submission.BoseGases.acube ℓ, Θ (Function.update x j z)‖
      ≤ C * (ℓ ^ 3) := by
    have h := norm_integral_le_of_norm_le_const
      (μ := (MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
        (Submission.BoseGases.acube ℓ))
      (f := fun z : Sp => Θ (Function.update x j z)) hx
    rwa [hreal] at h
  have hval : ‖Work.BoseBoxFock.aPC ℓ j Θ x‖
      = (1 / ℓ ^ 3) * ‖∫ z in Submission.BoseGases.acube ℓ, Θ (Function.update x j z)‖ := by
    unfold Work.BoseBoxFock.aPC
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hval]
  calc (1 / ℓ ^ 3) * ‖∫ z in Submission.BoseGases.acube ℓ, Θ (Function.update x j z)‖
      ≤ (1 / ℓ ^ 3) * (C * ℓ ^ 3) :=
        mul_le_mul_of_nonneg_left hIntBound (by positivity)
    _ = C := by field_simp

/-! ## 4. The slot operator collapses to `aPC` on the box -/

/-- **Replacing `u` by its a.e. value `c · θ_Λ` turns the `z`-integral in `uSlot` into
`conj c` times the centred-box integral of `Θ`** — for *every* `x` (no integrability of `Θ` is
needed: the Bochner integral is total and the two sides degenerate in the same way). -/
theorem uSlot_eq_mul_setIntegral_aux {ℓ : ℝ} (hℓ : 0 < ℓ) {u : Sp → ℂ} {c : ℂ}
    (huc : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
      u z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    {d : ℕ} (j : Fin d) (Θ : Work.BoseDict.Xn d → ℂ) (x : Work.BoseDict.Xn d) :
    Work.BoseBoxFock.uSlot u j Θ x = u (x j) * (starRingEnd ℂ) c
      * ∫ z in Submission.BoseGases.acube ℓ, Θ (Function.update x j z) := by
  have hconjae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
      (starRingEnd ℂ) (u z) = (starRingEnd ℂ) c * Work.BoseK15.corpusBox.thetaFun ℓ z := by
    filter_upwards [huc] with z hz
    rw [hz, map_mul, conj_thetaFun_aux z]
  have hθind : (fun z : Sp => Work.BoseK15.corpusBox.thetaFun ℓ z
        * Θ (Function.update x j z))
      = fun z : Sp => (Submission.BoseGases.acube ℓ).indicator
          (fun z => Θ (Function.update x j z)) z := by
    funext z
    rw [thetaFun_eq_indicator hℓ]
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  unfold Work.BoseBoxFock.uSlot
  rw [show (∫ z : Sp, (starRingEnd ℂ) (u z) * Θ (Function.update x j z))
      = ∫ z : Sp, (starRingEnd ℂ) c
          * (Work.BoseK15.corpusBox.thetaFun ℓ z * Θ (Function.update x j z)) from by
    refine integral_congr_ae ?_
    filter_upwards [hconjae] with z hz
    rw [hz, mul_assoc]]
  rw [MeasureTheory.integral_const_mul, hθind,
    MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ), mul_assoc]

/-- **The slot operator is the slot mean on the box.**  With `u =ᵐ c·θ_Λ` and `conj c · c = ℓ⁻³`,
`uSlot u j Θ` and `aPC ℓ j Θ` agree a.e. on the box. -/
theorem uSlot_ae_eq_aPC_aux {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin d)
    {u : Sp → ℂ} {c : ℂ} {Θ : Work.BoseDict.Xn d → ℂ}
    (huc : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
      u z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹) :
    (fun x => Work.BoseBoxFock.uSlot u j Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
      (fun x => Work.BoseBoxFock.aPC ℓ j Θ x) := by
  have h2 : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)),
      u (x j) = c * Work.BoseK15.corpusBox.thetaFun ℓ (x j) := by
    have hq := (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin d => (MeasureTheory.volume : MeasureTheory.Measure Sp)) j).ae_eq huc
    filter_upwards [hq] with x hx
    simpa only [Function.comp_apply] using hx
  have h3 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)),
      u (x j) = c * Work.BoseK15.corpusBox.thetaFun ℓ (x j) :=
    MeasureTheory.ae_mono Measure.restrict_le_self h2
  filter_upwards [h3, self_mem_ae_restrict (Submission.BoseGases.abox_measurable d ℓ)]
    with x hu hx
  have hmem : x j ∈ Submission.BoseGases.acube ℓ :=
    (Submission.BoseGases.mem_abox_iff d ℓ x).mp hx j
  have hu' : u (x j) = c := by
    rw [hu, Work.BoseB4.BoxData.thetaFun_apply,
      if_pos (by rw [Work.BoseBoxFock.corpusBox_boxL_eq_acube hℓ]; exact hmem), mul_one]
  rw [uSlot_eq_mul_setIntegral_aux hℓ huc j Θ x, hu']
  have hcc' : c * (starRingEnd ℂ) c = Complex.ofReal ((ℓ ^ 3 : ℝ)⁻¹) := by
    rw [mul_comm]; exact hcc
  have hval : (∫ z in Submission.BoseGases.acube ℓ, Θ (Function.update x j z))
      = (((ℓ ^ 3 : ℝ)) : ℂ) * Work.BoseBoxFock.aPC ℓ j Θ x := by
    unfold Work.BoseBoxFock.aPC
    rw [← mul_assoc, ← Complex.ofReal_mul,
      show (ℓ ^ 3 : ℝ) * (1 / ℓ ^ 3) = 1 by field_simp]
    simp
  rw [hval, hcc', ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), Complex.ofReal_one, one_mul]

/-! ## 5. The target -/

theorem uSlot_regular {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin d)
    {u : Work.BoseDict.Sp → ℂ} {c : ℂ} {Θ : Work.BoseDict.Xn d → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (huc : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp),
        u z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox d ℓ)
    (hΘm : MeasureTheory.AEStronglyMeasurable Θ MeasureTheory.volume)
    (hΘb : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)), ‖Θ x‖ ≤ C) :
    MeasureTheory.IntegrableOn
        (fun x => (starRingEnd ℂ) (Θ x) * Work.BoseBoxFock.uSlot u j Θ x)
        (Submission.BoseGases.abox d ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (fun x => ‖Work.BoseBoxFock.aPC ℓ j Θ x‖ ^ 2)
        (Submission.BoseGases.abox d ℓ) MeasureTheory.volume := by
  have hfin := Submission.BoseGases.abox_lt_top d ℓ hℓ.le
  have hbound := aPC_ae_bound_aux hℓ j hΘb
  have haesm := aPC_aesm_aux (ℓ := ℓ) j hΘm
  have hΘb' : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)),
      ‖Θ x‖ ≤ C := MeasureTheory.ae_mono Measure.restrict_le_self hΘb
  constructor
  · -- the slot row is integrable: a.e. it is `conj Θ · aPC`, which is bounded by `C²`
    have hsm : MeasureTheory.AEStronglyMeasurable
        (fun x => (starRingEnd ℂ) (Θ x) * Work.BoseBoxFock.aPC ℓ j Θ x)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)) :=
      (hΘm.restrict (s := Submission.BoseGases.abox d ℓ)).star.mul haesm
    have hb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)),
        ‖(starRingEnd ℂ) (Θ x) * Work.BoseBoxFock.aPC ℓ j Θ x‖ ≤ C * C := by
      filter_upwards [hΘb', hbound] with x h1 h2
      rw [norm_mul,
        show ‖(starRingEnd ℂ) (Θ x)‖ = ‖Θ x‖ by rw [starRingEnd_apply, norm_star]]
      exact mul_le_mul h1 h2 (norm_nonneg _) hC
    have hI : MeasureTheory.IntegrableOn
        (fun x => (starRingEnd ℂ) (Θ x) * Work.BoseBoxFock.aPC ℓ j Θ x)
        (Submission.BoseGases.abox d ℓ) MeasureTheory.volume :=
      MeasureTheory.IntegrableOn.of_bound hfin hsm (C * C) hb
    have hcongr : (fun x => (starRingEnd ℂ) (Θ x) * Work.BoseBoxFock.aPC ℓ j Θ x)
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
        (fun x => (starRingEnd ℂ) (Θ x) * Work.BoseBoxFock.uSlot u j Θ x) := by
      filter_upwards [uSlot_ae_eq_aPC_aux hℓ j huc hcc] with x hx
      rw [hx]
    exact hI.congr hcongr
  · -- the slot mean square is integrable: it is bounded by `C²`
    have hsm : MeasureTheory.AEStronglyMeasurable
        (fun x => ‖Work.BoseBoxFock.aPC ℓ j Θ x‖ ^ 2)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)) :=
      haesm.norm.pow 2
    have hb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)),
        ‖‖Work.BoseBoxFock.aPC ℓ j Θ x‖ ^ 2‖ ≤ C * C := by
      filter_upwards [hbound] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
      exact mul_self_le_mul_self (norm_nonneg _) hx
    exact MeasureTheory.IntegrableOn.of_bound hfin hsm (C * C) hb

end Work.BoseBoxFock
