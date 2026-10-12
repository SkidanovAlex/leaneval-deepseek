import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.CS.highSlot_bound_of_pos
import Submission.Work.BoseFixB3.CS.highSlot_stronglyMeasurable
import Submission.Work.BoseFixB3.Conv.highMult_box_transfer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Conv.pair_transfer_pos`

The `κ > 0` **pair-slot transfer** of FS §7: the pair amplitude
`⟨(1−f_L)_j(P_iΦ), w₁(x_i−x_j)·Q_jQ_iΦ⟩` may be moved off the *state* and onto the
*weight*: at `κ > 0`, where `1 − f_L` is the genuine complementary Fourier multiplier
`highMult`,

`∫_{Λⁿ} (1−f_L)_j(P_iΦ)·P_jP_iΦ·W(x_j)
   = ∫_{Λⁿ} P_iΦ·P_jP_iΦ·(1−f_L)(W)(x_j)`.

The proof peels the slot-`j` coordinate out of the box integral
(`Submission.BoseGases.abox_integral_peel`, i.e. the measure-preserving insertion
`kcInsN m j` and Fubini), reducing the statement to the one-body identity
`Work.BoseFixB3.Conv.highMult_box_transfer` applied to the slot-`j` fibre
`z ↦ P_iΦ(kcInsN m j (z,r))`.  The factor `P_jP_iΦ` is constant in the slot-`j`
coordinate (`Q0Sector.aP_const_in_coord`), hence pulls out of the inner integral, and it
is the *same* factor on both sides, so it cancels.

The sibling `Conv/abox_highSlot_transfer` states the identity *without* `0 < κ` and is
**false** there (at `κ ≤ 0` the multiplier degenerates to the "junk zero" of a non-`L¹`
Fourier transform); the hypothesis `hκ` is what makes the transfer valid.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Conv

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseFixB3.HighMass

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The slot-`j` fibre identity on inserted configurations.**  On `kcInsN m j (y,r)`
the slot-`j` high-momentum operator acts as the one-variable complementary multiplier
`1 − f_L` on the fibre `z ↦ A (kcInsN m j (z,r))`, evaluated at `y`. -/
lemma highSlot_kcInsN {fc : LowCut} {κ ℓ : ℝ} {m : ℕ} (j : Fin (m + 1))
    {A : X (m + 1) → ℝ} (y : EuclideanSpace ℝ (Fin 3)) (r : X m) :
    highSlot fc κ ℓ j A (kcInsN m j (y, r))
      = highMult fc κ ℓ (fun z : EuclideanSpace ℝ (Fin 3) => A (kcInsN m j (z, r))) y := by
  have hupd : ∀ z : EuclideanSpace ℝ (Fin 3),
      Function.update (kcInsN m j (y, r)) j z = kcInsN m j (z, r) := by
    intro z
    ext k
    by_cases hk : k = j
    · subst hk
      simp [kc_insN_apply_same]
    · rw [Function.update_of_ne hk, kc_insN_other_indep m j y z r k hk]
  simp only [highSlot, highMult, lowSlot]
  rw [show (fun z : EuclideanSpace ℝ (Fin 3) => A (Function.update (kcInsN m j (y, r)) j z))
      = (fun z : EuclideanSpace ℝ (Fin 3) => A (kcInsN m j (z, r)))
      from funext (fun z => congrArg A (hupd z)),
    kc_insN_apply_same]

/-- The slot-`j` mean `P_j P_i Φ` is constant in the slot-`j` coordinate, in the
"inserted" form used by the peel. -/
lemma aP_ins_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {m : ℕ} (j : Fin (m + 1)) {A : X (m + 1) → ℝ}
    (hAc : Continuous A) (y : EuclideanSpace ℝ (Fin 3)) (r : X m) :
    aP ℓ j A (kcInsN m j (y, r)) = aP ℓ j A (kcInsN m j (0, r)) := by
  rw [kcInsN_update_zero j y r]
  exact aP_const_in_coord hℓ j hAc _ y

/-- An inserted configuration lies in the `(m+1)`-box when the inserted coordinate and
the rest both lie in the boxes. -/
lemma kcInsN_mem_abox {ℓ : ℝ} {m : ℕ} (j : Fin (m + 1))
    {y : EuclideanSpace ℝ (Fin 3)} {r : X m}
    (hy : y ∈ acube ℓ) (hr : r ∈ abox m ℓ) : kcInsN m j (y, r) ∈ abox (m + 1) ℓ := by
  rw [mem_abox_iff]
  intro k
  by_cases hk : k = j
  · subst hk
    rwa [kc_insN_apply_same]
  · obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq (x := k) (y := j) hk
    rw [← hk', kc_insN_apply_succ]
    exact hr k'

/-- The slot-`j` coordinate of an inserted (paired) configuration. -/
lemma kcInsN_apply_self {m : ℕ} (j : Fin (m + 1)) (p : EuclideanSpace ℝ (Fin 3) × X m) :
    (kcInsN m j p) j = p.1 := by
  rcases p with ⟨y, r⟩
  exact kc_insN_apply_same m j y r

theorem pair_transfer_pos {n : ℕ} {ℓ κ : ℝ} (fc : Work.BoseBoxFix.LowCut) (hℓ : 0 < ℓ) (hκ : 0 < κ)
    {i j : Fin n} (hij : i ≠ j) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hm : Measurable W) (hb : ∃ C : ℝ, ∀ y, |W y| ≤ C) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x * W (x j))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x
            * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
            * Work.BoseFixB3.highMult fc κ ℓ W (x j) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fin.pos j))
  -- ### abbreviations
  set A : X (m + 1) → ℝ := aP ℓ i Φ with hA
  have hAc : Continuous A := by rw [hA]; exact aP_continuous hℓ i hΦ
  set Ap : X (m + 1) → ℝ := aP ℓ j A with hAp
  have hApcont : Continuous Ap := by rw [hAp]; exact aP_continuous hℓ j hAc
  have hApins : ∀ (y : EuclideanSpace ℝ (Fin 3)) (r : X m),
      Ap (kcInsN m j (y, r)) = Ap (kcInsN m j (0, r)) := by
    intro y r
    rw [hAp]
    exact aP_ins_eq hℓ j hAc y r
  -- ### bounds on the box
  obtain ⟨C₀, hC₀⟩ :=
    (Work.UBBInputs9.B.abox_isCompact (m + 1) ℓ).exists_bound_of_continuousOn hΦ.continuousOn
  set M : ℝ := max C₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hΦb : ∀ x ∈ abox (m + 1) ℓ, |Φ x| ≤ M := by
    intro x hx
    have h := hC₀ x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  have hAb : ∀ x ∈ abox (m + 1) ℓ, |A x| ≤ M := by
    intro x hx
    simp only [hA]
    exact aP_abs_le hℓ i hΦ hM0 hΦb x hx
  have hApb : ∀ x ∈ abox (m + 1) ℓ, |Ap x| ≤ M := by
    intro x hx
    simp only [hAp]
    exact aP_abs_le hℓ j hAc hM0 hAb x hx
  obtain ⟨CW, hCW⟩ := hb
  have hCW0 : 0 ≤ CW := le_trans (abs_nonneg (W 0)) (hCW 0)
  -- ### the low-momentum multiplier bound for the weight `W`
  have hWl1 : IntegrableOn W (acube ℓ) volume :=
    MeasureTheory.IntegrableOn.of_bound (acube_lt_top ℓ hℓ.le) hm.aestronglyMeasurable.restrict CW
      (ae_restrict_of_forall_mem (acube_measurable ℓ) (fun z _ => by
        rw [Real.norm_eq_abs]; exact hCW z))
  have hθWint : Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      (((acube ℓ).indicator W z : ℝ) : ℂ)) volume :=
    (hWl1.integrable_indicator (acube_measurable ℓ)).ofReal
  set KWM : ℝ := ((2 * π) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
      |fc.f (‖p‖ / κ)| *
        ‖kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          (((acube ℓ).indicator W z : ℝ) : ℂ)) p‖ with hKWM
  have hWlow : ∀ y : EuclideanSpace ℝ (Fin 3), |lowMult fc κ ℓ W y| ≤ KWM := by
    intro y
    have h := abs_lowMult_le (fc := fc) (κ := κ) (ℓ := ℓ) hκ hθWint y
    rw [hKWM]
    exact h
  have hHWb : ∀ y : EuclideanSpace ℝ (Fin 3), |highMult fc κ ℓ W y| ≤ CW + KWM := by
    intro y
    simp only [highMult]
    calc |W y - lowMult fc κ ℓ W y| ≤ |W y| + |lowMult fc κ ℓ W y| := abs_sub _ _
      _ ≤ CW + KWM := add_le_add (hCW y) (hWlow y)
  -- ### the two integrands
  set F : X (m + 1) → ℝ := fun x => highSlot fc κ ℓ j A x * Ap x * W (x j) with hFdef
  set G : X (m + 1) → ℝ := fun x => A x * Ap x * highMult fc κ ℓ W (x j) with hGdef
  change (∫ x in abox (m + 1) ℓ, F x) = ∫ x in abox (m + 1) ℓ, G x
  obtain ⟨KH, hKH0, hKH⟩ := CS.highSlot_bound_of_pos (fc := fc) (κ := κ) (ℓ := ℓ) hκ hℓ j hAc
  -- ### the measure-preserving peel of the slot-`j` coordinate
  have hmp : MeasurePreserving (⇑(kcInsN m j))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
        ((volume : Measure (X m)).restrict (abox m ℓ)))
      ((volume : Measure (X (m + 1))).restrict (abox (m + 1) ℓ)) := by
    have h := MeasurePreserving.symm
      (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => EuclideanSpace ℝ (Fin 3)) j)
      (abox_peel_mp m ℓ j)
    simpa [kcInsN] using h
  have hpeel : ∀ H : X (m + 1) → ℝ, (∫ x in abox (m + 1) ℓ, H x)
      = ∫ p : EuclideanSpace ℝ (Fin 3) × X m, H (kcInsN m j p)
          ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
            ((volume : Measure (X m)).restrict (abox m ℓ))) := by
    intro H
    exact (hmp.integral_comp' H).symm
  have hmemp : ∀ᵐ p ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
      ((volume : Measure (X m)).restrict (abox m ℓ))), p.1 ∈ acube ℓ ∧ p.2 ∈ abox m ℓ := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem ((acube_measurable ℓ).prod (abox_measurable m ℓ))] with p hp
    exact hp
  have hμfin : (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
      ((volume : Measure (X m)).restrict (abox m ℓ))) Set.univ < ⊤ := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
      Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (acube_lt_top ℓ hℓ.le) (abox_lt_top m ℓ hℓ.le)
  -- ### integrability of the peeled integrands
  have hFasm : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × X m => F (kcInsN m j p))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
        ((volume : Measure (X m)).restrict (abox m ℓ))) := by
    have h1 : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × X m => highSlot fc κ ℓ j A (kcInsN m j p))
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
          ((volume : Measure (X m)).restrict (abox m ℓ))) :=
      ((CS.highSlot_stronglyMeasurable j hAc).comp_measurable
        (kcInsN m j).measurable).aestronglyMeasurable
    have h2 : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × X m => Ap (kcInsN m j p))
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
          ((volume : Measure (X m)).restrict (abox m ℓ))) :=
      (hApcont.measurable.comp (kcInsN m j).measurable).aestronglyMeasurable
    have h3 : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × X m => W ((kcInsN m j p) j))
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
          ((volume : Measure (X m)).restrict (abox m ℓ))) :=
      (hm.comp ((measurable_pi_apply j).comp (kcInsN m j).measurable)).aestronglyMeasurable
    have hcongr : (fun p : EuclideanSpace ℝ (Fin 3) × X m => F (kcInsN m j p))
        = fun p : EuclideanSpace ℝ (Fin 3) × X m =>
            highSlot fc κ ℓ j A (kcInsN m j p) * Ap (kcInsN m j p) * W ((kcInsN m j p) j) := by
      funext p; rw [hFdef]
    rw [hcongr]
    exact (h1.mul h2).mul h3
  haveI hμfinI : IsFiniteMeasure
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
        ((volume : Measure (X m)).restrict (abox m ℓ))) := ⟨hμfin⟩
  have hFins_int : Integrable (fun p : EuclideanSpace ℝ (Fin 3) × X m => F (kcInsN m j p))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
        ((volume : Measure (X m)).restrict (abox m ℓ))) := by
    refine Integrable.of_bound hFasm (KH * M * CW) ?_
    filter_upwards [hmemp] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hmem : kcInsN m j p ∈ abox (m + 1) ℓ := kcInsN_mem_abox j hp1 hp2
    rw [Real.norm_eq_abs,
      show F (kcInsN m j p)
        = highSlot fc κ ℓ j A (kcInsN m j p) * Ap (kcInsN m j p) * W ((kcInsN m j p) j)
        from by rw [hFdef],
      abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hKH _ hmem) (hApb _ hmem) (abs_nonneg _) hKH0)
      (hCW ((kcInsN m j p) j)) (abs_nonneg _) (mul_nonneg hKH0 hM0)
  have hLW' : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × X m => lowMult fc κ ℓ W p.1)
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
        ((volume : Measure (X m)).restrict (abox m ℓ))) := by
    have h1 : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin 3) => lowMult fc κ ℓ W y)
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)) :=
      (aestronglyMeasurable_lowMult hm).mono_ac
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    exact h1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hHWfst : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × X m => highMult fc κ ℓ W p.1)
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
        ((volume : Measure (X m)).restrict (abox m ℓ))) := by
    have h2 : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × X m => W p.1)
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
          ((volume : Measure (X m)).restrict (abox m ℓ))) :=
      (hm.comp measurable_fst).aestronglyMeasurable
    have hgoal : (fun p : EuclideanSpace ℝ (Fin 3) × X m => highMult fc κ ℓ W p.1)
        = (fun p : EuclideanSpace ℝ (Fin 3) × X m => W p.1)
          - (fun p : EuclideanSpace ℝ (Fin 3) × X m => lowMult fc κ ℓ W p.1) := by
      funext p; simp [highMult]
    rw [hgoal]
    exact h2.sub hLW'
  have hGasm : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × X m => G (kcInsN m j p))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
        ((volume : Measure (X m)).restrict (abox m ℓ))) := by
    have h1 : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × X m => A (kcInsN m j p))
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
          ((volume : Measure (X m)).restrict (abox m ℓ))) :=
      (hAc.measurable.comp (kcInsN m j).measurable).aestronglyMeasurable
    have h2 : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × X m => Ap (kcInsN m j p))
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
          ((volume : Measure (X m)).restrict (abox m ℓ))) :=
      (hApcont.measurable.comp (kcInsN m j).measurable).aestronglyMeasurable
    have h3 : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × X m => highMult fc κ ℓ W ((kcInsN m j p) j))
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
          ((volume : Measure (X m)).restrict (abox m ℓ))) := by
      simpa only [kcInsN_apply_self] using hHWfst
    have hcongr : (fun p : EuclideanSpace ℝ (Fin 3) × X m => G (kcInsN m j p))
        = fun p : EuclideanSpace ℝ (Fin 3) × X m =>
            A (kcInsN m j p) * Ap (kcInsN m j p) * highMult fc κ ℓ W ((kcInsN m j p) j) := by
      funext p; rw [hGdef]
    rw [hcongr]
    exact (h1.mul h2).mul h3
  have hGins_int : Integrable (fun p : EuclideanSpace ℝ (Fin 3) × X m => G (kcInsN m j p))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
        ((volume : Measure (X m)).restrict (abox m ℓ))) := by
    refine Integrable.of_bound hGasm (M * M * (CW + KWM)) ?_
    filter_upwards [hmemp] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hmem : kcInsN m j p ∈ abox (m + 1) ℓ := kcInsN_mem_abox j hp1 hp2
    rw [Real.norm_eq_abs,
      show G (kcInsN m j p)
        = A (kcInsN m j p) * Ap (kcInsN m j p) * highMult fc κ ℓ W ((kcInsN m j p) j)
        from by rw [hGdef],
      abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hAb _ hmem) (hApb _ hmem) (abs_nonneg _) hM0)
      (hHWb ((kcInsN m j p) j)) (abs_nonneg _) (mul_nonneg hM0 hM0)
  -- ### peel both sides and Fubini
  have hLHS : (∫ x in abox (m + 1) ℓ, F x)
      = ∫ r in abox m ℓ, ∫ y in acube ℓ, F (kcInsN m j (y, r)) := by
    rw [hpeel F]
    exact integral_prod_symm (f := fun p : EuclideanSpace ℝ (Fin 3) × X m => F (kcInsN m j p))
      hFins_int
  have hRHS : (∫ x in abox (m + 1) ℓ, G x)
      = ∫ r in abox m ℓ, ∫ y in acube ℓ, G (kcInsN m j (y, r)) := by
    rw [hpeel G]
    exact integral_prod_symm (f := fun p : EuclideanSpace ℝ (Fin 3) × X m => G (kcInsN m j p))
      hGins_int
  rw [hLHS, hRHS]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (abox_measurable m ℓ)] with r hr
  -- ### the one-body reduction at the slot-`j` fibre
  set u : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => A (kcInsN m j (z, r)) with hu
  have huM : ∀ z ∈ acube ℓ, |u z| ≤ M := by
    intro z hz
    simp only [hu]
    exact hAb _ (kcInsN_mem_abox j hz hr)
  have huc : Continuous u := by
    rw [hu]
    have h1 : (fun z : EuclideanSpace ℝ (Fin 3) => A (kcInsN m j (z, r)))
        = fun z : EuclideanSpace ℝ (Fin 3) =>
            A (Function.update (kcInsN m j (0, r)) j z) := by
      funext z; rw [kcInsN_update_zero j z r]
    rw [h1]
    have hupd_cont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
        Function.update (kcInsN m j (0, r)) j z) :=
      (contDiff_update (𝕜 := ℝ) (k := ⊤) (kcInsN m j (0, r)) j).continuous
    exact hAc.comp hupd_cont
  have hFeq : ∀ y : EuclideanSpace ℝ (Fin 3), F (kcInsN m j (y, r))
      = highMult fc κ ℓ u y * W y * Ap (kcInsN m j (0, r)) := by
    intro y
    simp only [hFdef, hu]
    rw [highSlot_kcInsN, hApins y r, kc_insN_apply_same]
    ring
  have hGeq : ∀ y : EuclideanSpace ℝ (Fin 3), G (kcInsN m j (y, r))
      = u y * highMult fc κ ℓ W y * Ap (kcInsN m j (0, r)) := by
    intro y
    simp only [hGdef, hu]
    rw [hApins y r, kc_insN_apply_same]
    ring
  calc (∫ y in acube ℓ, F (kcInsN m j (y, r)))
      = ∫ y in acube ℓ, (highMult fc κ ℓ u y * W y) * Ap (kcInsN m j (0, r)) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hFeq y]
    _ = (∫ y in acube ℓ, highMult fc κ ℓ u y * W y) * Ap (kcInsN m j (0, r)) :=
        integral_mul_const _ _
    _ = (∫ y in acube ℓ, u y * highMult fc κ ℓ W y) * Ap (kcInsN m j (0, r)) := by
        rw [highMult_box_transfer (fc := fc) (κ := κ) (ℓ := ℓ) hκ hℓ huc.measurable
          ⟨M, huM⟩ hm ⟨CW, hCW⟩]
    _ = ∫ y in acube ℓ, u y * highMult fc κ ℓ W y * Ap (kcInsN m j (0, r)) :=
        (integral_mul_const _ _).symm
    _ = ∫ y in acube ℓ, G (kcInsN m j (y, r)) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hGeq y]

end Work.BoseFixB3.Conv
