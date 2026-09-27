import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLC8Core.phi_conj_u

/-!
# Conjugation of the `ℝ`-valued leafwise measure by the contracting flow

`nuR ν = (ν.restrict U_01).map par` is the `ℝ`-valued leafwise measure of EKL.  Conjugating a
measure supported on `U_01` by `φ_w = diag(e^{-w}, e^{w}, 1)` pushes the parameter distribution
forward by `t ↦ e^{-2w} t` (because `φ_w u_01(s) φ_w⁻¹ = u_01(e^{-2w} s)`), and the real-valued
measure of an interval scales accordingly: `Icc (-σ) σ` becomes `Icc (-(σ e^{2w})) (σ e^{2w})`.
-/

namespace Work.EKLCompLeaf

open MeasureTheory
open Work.EKLContract

/-- Preimage of a symmetric interval under `t ↦ a * t` for `a > 0`. -/
private lemma preimage_const_mul_Icc {a σ : ℝ} (ha : 0 < a) :
    (fun t : ℝ => a * t) ⁻¹' Set.Icc (-σ) σ = Set.Icc (-(σ / a)) (σ / a) := by
  ext t
  simp only [Set.mem_preimage, Set.mem_Icc]
  rw [← neg_div, div_le_iff₀ ha, le_div_iff₀ ha]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith [mul_comm t a], by linarith [mul_comm t a]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith [mul_comm t a], by linarith [mul_comm t a]⟩

/-- Conjugation by `φ_w` pushes `nuR` forward by `t ↦ e^{-2w} t`, for measures supported on
`U_01`. -/
private theorem nuR_map_conj_phi (m : Measure SL3)
    (hm : m (Uij Work.EKLComp.h01 : Set SL3)ᶜ = 0) (w : ℝ) :
    Work.EKLComp.nuR (m.map (fun g => Work.EKLComp.phi w * g * (Work.EKLComp.phi w)⁻¹))
      = (Work.EKLComp.nuR m).map (fun t => Real.exp (-2 * w) * t) := by
  have hf : Measurable (fun g : SL3 => Work.EKLComp.phi w * g * (Work.EKLComp.phi w)⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hcar : (m.map (fun g : SL3 => Work.EKLComp.phi w * g * (Work.EKLComp.phi w)⁻¹))
      (Uij Work.EKLComp.h01 : Set SL3)ᶜ = 0 := by
    rw [Measure.map_apply hf (Work.EKLComp.closed_Uij.measurableSet.compl)]
    refine measure_mono_null (fun g hg => ?_) hm
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hg ⊢
    intro hgU
    obtain ⟨t, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff Work.EKLComp.h01 g).mp hgU
    have htu : Work.EKLComp.phi w * uij Work.EKLComp.h01 t * (Work.EKLComp.phi w)⁻¹
        = Work.EKLComp.u (Real.exp (-2 * w) * t) := Work.EKLC8Core.phi_conj_u w t
    exact hg (htu ▸ Work.EKLComp.u_mem _)
  have h0 : m.restrict (Uij Work.EKLComp.h01 : Set SL3) = m :=
    Work.EKLComp.restrict_Uij_of_compl_eq_zero hm
  have h1 : (m.map (fun g : SL3 => Work.EKLComp.phi w * g * (Work.EKLComp.phi w)⁻¹)).restrict
      (Uij Work.EKLComp.h01 : Set SL3)
      = m.map (fun g : SL3 => Work.EKLComp.phi w * g * (Work.EKLComp.phi w)⁻¹) :=
    Work.EKLComp.restrict_Uij_of_compl_eq_zero hcar
  have hfun : (fun g : SL3 => Work.EKLComp.par (Work.EKLComp.phi w * g * (Work.EKLComp.phi w)⁻¹))
      =ᵐ[m] (fun g : SL3 => Real.exp (-2 * w) * Work.EKLComp.par g) := by
    filter_upwards [Work.EKLComp.ae_mem_Uij_of_compl_eq_zero hm] with g hg
    obtain ⟨t, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff Work.EKLComp.h01 g).mp hg
    rw [show Work.EKLComp.phi w * uij Work.EKLComp.h01 t * (Work.EKLComp.phi w)⁻¹
          = Work.EKLComp.phi w * Work.EKLComp.u t * (Work.EKLComp.phi w)⁻¹ from rfl,
        Work.EKLComp.par_phi_conj_u, Work.EKLComp.par_uij_h01]
  rw [Work.EKLComp.nuR, h1, Work.EKLComp.nuR, h0,
    Measure.map_map (g := Work.EKLComp.par)
      (f := fun g : SL3 => Work.EKLComp.phi w * g * (Work.EKLComp.phi w)⁻¹)
      Work.EKLComp.measurable_par hf,
    Measure.map_map (g := fun t : ℝ => Real.exp (-2 * w) * t) (f := Work.EKLComp.par)
      (measurable_const.mul measurable_id) Work.EKLComp.measurable_par]
  exact Measure.map_congr hfun

theorem nuR_conj_phi_Icc (m : MeasureTheory.Measure Work.EKLContract.SL3)
    (hm : m (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3)ᶜ = 0)
    (w σ : ℝ) :
    (Work.EKLComp.nuR (m.map (fun g => Work.EKLComp.phi w * g * (Work.EKLComp.phi w)⁻¹))).real
        (Set.Icc (-σ) σ)
      = (Work.EKLComp.nuR m).real
          (Set.Icc (-(σ * Real.exp (2 * w))) (σ * Real.exp (2 * w))) := by
  rw [nuR_map_conj_phi m hm w]
  have hmul : Measurable (fun t : ℝ => Real.exp (-2 * w) * t) :=
    measurable_const.mul measurable_id
  rw [MeasureTheory.map_measureReal_apply hmul measurableSet_Icc]
  rw [preimage_const_mul_Icc (Real.exp_pos (-2 * w))]
  have hdiv : σ / Real.exp (-2 * w) = σ * Real.exp (2 * w) := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  rw [hdiv]

end Work.EKLCompLeaf
