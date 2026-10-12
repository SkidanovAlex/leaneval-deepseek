import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.SliceBadAux
import Submission.Work.BoseBoxFock.sliceFCRealise
import Submission.Work.BoseBoxFock.uSlot_regular
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.XSpow_aeStronglyMeasurable_ae_bounded`

`XSpow ℓ S j` is the `j`-th iterate of the slot-count operator
`XS ℓ S Ψ = Σ_{i ∈ S} (Ψ − aPC ℓ i Ψ)` (`SliceBadAux.lean`).  This file proves that it
preserves a.e. strong measurability together with a.e. boundedness, with no hypothesis on
the state `Θ` beyond those two facts: the only ingredient is that the slot mean
`aPC ℓ i Θ = ℓ⁻³ ∫_{acube ℓ} Θ (x[i ↦ z]) dz` is a.e. strongly measurable (a partial
Bochner integral of an a.e. strongly measurable function, through the quasi-measure-preserving
slice map `(x,z) ↦ Function.update x i z`) and a.e. bounded by the same constant as `Θ`
(the `z`-average of an a.e. bounded function).

The variants `aPC_aesm_full` / `aPC_ae_bound_full` are the *global*-measure versions of
`uSlot_regular.aPC_aesm_aux` / `aPC_ae_bound_aux`, whose conclusions are a.e. statements on
the box only (which is what the `uSlot` chapter, being an integral over the box, needs).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The slot mean: a.e. strong measurability and a.e. boundedness *globally* -/

/-- **`aPC ℓ i Θ` is a.e. strongly measurable on the whole configuration space** when `Θ` is:
it is the partial Bochner integral of the jointly a.e. strongly measurable function
`(x,z) ↦ Θ (x[i ↦ z])` over the cube, and `AEStronglyMeasurable.integral_prod_right'` gives
a.e. strong measurability with respect to the *full* measure on the first factor. -/
theorem aPC_aesm_full {n : ℕ} (ℓ : ℝ) (i : Fin n) {Θ : (Fin n → Sp) → ℂ}
    (hΘ : MeasureTheory.AEStronglyMeasurable Θ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp))) :
    MeasureTheory.AEStronglyMeasurable (aPC ℓ i Θ)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)) := by
  obtain ⟨Θ', hΘ'sm, hΘ'eq⟩ := hΘ
  have hmeas_upd : Measurable (fun p : (Fin n → Sp) × Sp => Function.update p.1 i p.2) := by
    have hfun : (fun p : (Fin n → Sp) × Sp => Function.update p.1 i p.2)
        = fun p j => if j = i then p.2 else p.1 j := by
      funext p j; rw [Function.update_apply]
    rw [hfun]
    refine measurable_pi_iff.mpr (fun j => ?_)
    by_cases hj : j = i
    · subst hj; simpa using measurable_snd
    · simp only [if_neg hj]; exact (measurable_pi_apply j).comp measurable_fst
  have hcomp : (fun p : (Fin n → Sp) × Sp => Θ (Function.update p.1 i p.2))
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ((Fin n → Sp) × Sp))]
      (fun p => Θ' (Function.update p.1 i p.2)) :=
    (qmp_update_Xn_aux i).ae_eq hΘ'eq
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : (Fin n → Sp) × Sp => Θ (Function.update p.1 i p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)).prod
        (MeasureTheory.volume : MeasureTheory.Measure Sp)) :=
    (hΘ'sm.comp_measurable hmeas_upd).aestronglyMeasurable.congr hcomp.symm
  have hjoint' : MeasureTheory.AEStronglyMeasurable
      (fun p : (Fin n → Sp) × Sp => Θ (Function.update p.1 i p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
          (Submission.BoseGases.acube ℓ))) :=
    hjoint.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hpi : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin n → Sp => ∫ z : Sp, Θ (Function.update x i z)
        ∂((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
          (Submission.BoseGases.acube ℓ)))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)) :=
    hjoint'.integral_prod_right'
  have h2 := hpi.const_mul (((1 / ℓ ^ 3 : ℝ)) : ℂ)
  exact h2

/-- **`aPC ℓ i Θ` is a.e. bounded by the same constant as `Θ`**, on the whole configuration
space: the cube average of an a.e. bounded function is bounded by the same bound. -/
theorem aPC_ae_bound_full {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (i : Fin n) {C : ℝ} (_hC : 0 ≤ C)
    {Θ : (Fin n → Sp) → ℂ}
    (hΘ : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)), ‖Θ x‖ ≤ C) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)), ‖aPC ℓ i Θ x‖ ≤ C := by
  have : IsFiniteMeasure ((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
      (Submission.BoseGases.acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
  have h1 : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure ((Fin n → Sp) × Sp)),
      ‖Θ (Function.update p.1 i p.2)‖ ≤ C := by
    rw [MeasureTheory.ae_iff] at hΘ ⊢
    simpa using (qmp_update_Xn_aux i).preimage_null hΘ
  have h2 : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)),
      ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
        ‖Θ (Function.update x i z)‖ ≤ C := MeasureTheory.Measure.ae_ae_of_ae_prod h1
  filter_upwards [h2] with x hx
  have hx' : ∀ᵐ z ∂((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
      (Submission.BoseGases.acube ℓ)), ‖Θ (Function.update x i z)‖ ≤ C :=
    MeasureTheory.ae_mono Measure.restrict_le_self hx
  have hInt : ‖∫ z : Sp, Θ (Function.update x i z)
      ∂((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
        (Submission.BoseGases.acube ℓ))‖ ≤ C * ℓ ^ 3 := by
    have h := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
        (Submission.BoseGases.acube ℓ))
      (f := fun z : Sp => Θ (Function.update x i z)) hx'
    rwa [Submission.BoseGases.real_volume_acube ℓ hℓ.le] at h
  have hval : ‖aPC ℓ i Θ x‖
      = (1 / ℓ ^ 3) * ‖∫ z : Sp, Θ (Function.update x i z)
          ∂((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
            (Submission.BoseGases.acube ℓ))‖ := by
    unfold aPC
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hval]
  have hmul : (1 / ℓ ^ 3) * ‖∫ z : Sp, Θ (Function.update x i z)
      ∂((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
        (Submission.BoseGases.acube ℓ))‖ ≤ (1 / ℓ ^ 3) * (C * ℓ ^ 3) :=
    mul_le_mul_of_nonneg_left hInt (by positivity)
  have hsimp : (1 / ℓ ^ 3) * (C * ℓ ^ 3) = C := by
    rw [mul_comm C (ℓ ^ 3), ← mul_assoc, one_div,
      inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]
  linarith

/-! ## 2. The slot-count operator `XS` preserves both properties -/

/-- `XS ℓ S` preserves a.e. strong measurability. -/
theorem XS_aesm {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) {Ψ : (Fin n → Sp) → ℂ}
    (hΨ : MeasureTheory.AEStronglyMeasurable Ψ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp))) :
    MeasureTheory.AEStronglyMeasurable (XS ℓ S Ψ)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)) := by
  have h := Finset.aestronglyMeasurable_sum (s := S)
    (f := fun i (x : Fin n → Sp) => Ψ x - aPC ℓ i Ψ x)
    (fun i _ => hΨ.sub (aPC_aesm_full ℓ i hΨ))
  refine h.congr ?_
  filter_upwards with x
  simp only [XS, Finset.sum_apply]

/-- `XS ℓ S` maps the a.e. bound `B ≥ 0` to the a.e. bound `2·#S·B`. -/
theorem XS_ae_bound {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n)) {B : ℝ} (hB : 0 ≤ B)
    {Ψ : (Fin n → Sp) → ℂ}
    (hΨ : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)), ‖Ψ x‖ ≤ B) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)),
      ‖XS ℓ S Ψ x‖ ≤ 2 * (S.card : ℝ) * B := by
  have hall : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)),
      ∀ i : Fin n, ‖aPC ℓ i Ψ x‖ ≤ B :=
    Filter.eventually_all.mpr (fun i => aPC_ae_bound_full ℓ hℓ i hB hΨ)
  filter_upwards [hΨ, hall] with x hx hxall
  calc ‖XS ℓ S Ψ x‖ = ‖∑ i ∈ S, (Ψ x - aPC ℓ i Ψ x)‖ := rfl
    _ ≤ ∑ i ∈ S, ‖Ψ x - aPC ℓ i Ψ x‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, (B + B) :=
        Finset.sum_le_sum (fun i _ =>
          le_trans (norm_sub_le _ _) (add_le_add hx (hxall i)))
    _ = 2 * (S.card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-! ## 3. The iterates -/

theorem XSpow_aeStronglyMeasurable_ae_bounded {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n))
    {Θ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hmeas : MeasureTheory.AEStronglyMeasurable Θ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → EuclideanSpace ℝ (Fin 3))))
    (hbdd : ∃ C, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → EuclideanSpace ℝ (Fin 3))),
      ‖Θ x‖ ≤ C) (j : ℕ) :
    MeasureTheory.AEStronglyMeasurable (Work.BoseBoxFock.XSpow ℓ S j Θ)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → EuclideanSpace ℝ (Fin 3)))
    ∧ ∃ C, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → EuclideanSpace ℝ (Fin 3))),
        ‖Work.BoseBoxFock.XSpow ℓ S j Θ x‖ ≤ C := by
  classical
  obtain ⟨C, hC⟩ := hbdd
  set D : ℝ := max C 0 with hD
  have hDnn : 0 ≤ D := by rw [hD]; exact le_max_right C 0
  have hDC : C ≤ D := by rw [hD]; exact le_max_left C 0
  have hΘ : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)), ‖Θ x‖ ≤ D :=
    hC.mono (fun x hx => le_trans hx hDC)
  have hK : (0 : ℝ) ≤ 2 * (S.card : ℝ) := by positivity
  have key : ∀ j : ℕ,
      MeasureTheory.AEStronglyMeasurable (XSpow ℓ S j Θ)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp))
      ∧ ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → Sp)),
        ‖XSpow ℓ S j Θ x‖ ≤ (2 * (S.card : ℝ)) ^ j * D := by
    intro j
    induction j with
    | zero =>
        have h0 : XSpow ℓ S 0 Θ = Θ := rfl
        rw [h0]
        simpa using And.intro hmeas hΘ
    | succ j ih =>
        obtain ⟨hm, hb⟩ := ih
        refine ⟨?_, ?_⟩
        · have h := XS_aesm ℓ S hm
          simpa only [XSpow] using h
        · have hbnn : (0 : ℝ) ≤ (2 * (S.card : ℝ)) ^ j * D := by positivity
          have h := XS_ae_bound ℓ hℓ S hbnn hb
          filter_upwards [h] with x hx
          calc ‖XSpow ℓ S (j + 1) Θ x‖ = ‖XS ℓ S (XSpow ℓ S j Θ) x‖ := rfl
            _ ≤ 2 * (S.card : ℝ) * ((2 * (S.card : ℝ)) ^ j * D) := hx
            _ = (2 * (S.card : ℝ)) ^ (j + 1) * D := by rw [pow_succ]; ring
  obtain ⟨hm, hb⟩ := key j
  exact ⟨hm, ⟨_, hb⟩⟩

end Work.BoseBoxFock
