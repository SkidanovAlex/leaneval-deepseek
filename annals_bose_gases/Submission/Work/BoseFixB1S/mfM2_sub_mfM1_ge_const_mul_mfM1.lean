import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1B.boxM2_sub_boxM1_eq_omegaMass
import Submission.Work.BoseFixB1S.mfGatesV2B1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Monotonicity of the Bochner integral under a two-sided a.e. sandwich**, with the
junk-value convention handled: if `c·f ≤ h ≤ f` and `0 ≤ f` a.e. (`c > 0`, all functions a.e.
strongly measurable) then `h` is integrable exactly when `f` is, and

    c · ∫f ≤ ∫h .

If `f` is not integrable, `h` is not integrable either, both integrals are `0` by the
`integral_undef` convention, and the inequality is `0 ≤ 0`. -/
lemma mfM2M1_const_mul_integral_le {α : Type*} [MeasurableSpace α]
    {μ₀ : MeasureTheory.Measure α} {f g : α → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : MeasureTheory.AEStronglyMeasurable f μ₀)
    (hg : MeasureTheory.AEStronglyMeasurable g μ₀)
    (hfnn : 0 ≤ᵐ[μ₀] f) (hgf : g ≤ᵐ[μ₀] f) (hcg : ∀ᵐ x ∂μ₀, c * f x ≤ g x) :
    c * (∫ x, f x ∂μ₀) ≤ ∫ x, g x ∂μ₀ := by
  have hgnn : ∀ᵐ x ∂μ₀, 0 ≤ g x := by
    filter_upwards [hfnn, hcg] with x hx hcx
    exact le_trans (mul_nonneg hc.le hx) hcx
  by_cases hfi : MeasureTheory.Integrable f μ₀
  · have hgi : MeasureTheory.Integrable g μ₀ := by
      refine MeasureTheory.Integrable.mono' hfi hg ?_
      filter_upwards [hgnn, hgf] with x hgx hgfx
      rw [Real.norm_of_nonneg hgx]
      exact hgfx
    calc c * (∫ x, f x ∂μ₀) = ∫ x, c * f x ∂μ₀ := (MeasureTheory.integral_const_mul c f).symm
      _ ≤ ∫ x, g x ∂μ₀ := MeasureTheory.integral_mono_ae (hfi.const_mul c) hgi hcg
  · have hgi : ¬ MeasureTheory.Integrable g μ₀ := by
      intro hgint
      refine hfi ?_
      have hcfi : MeasureTheory.Integrable (fun x => c * f x) μ₀ := by
        refine MeasureTheory.Integrable.mono' hgint (hf.const_mul c) ?_
        filter_upwards [hfnn, hcg] with x hx hcx
        rw [Real.norm_of_nonneg (mul_nonneg hc.le hx)]
        exact hcx
      have h2 : MeasureTheory.Integrable (fun x => c⁻¹ * (c * f x)) μ₀ := hcfi.const_mul c⁻¹
      refine h2.congr (Filter.Eventually.of_forall (fun x => ?_))
      show c⁻¹ * (c * f x) = f x
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]
    rw [MeasureTheory.integral_undef hfi, MeasureTheory.integral_undef hgi, mul_zero]

/-- **The abstract mass comparison.**  For every regularity `M ≥ 1`, every box scale `ℓ > 0`,
every `d > 0` and every sliding position `u`:

    (a v)/(2R) · boxM1 ℓ B(u) w_{1,B(u)}
      ≤ boxM2 |B(u)| B(u) w_{2,B(u)} − boxM1 ℓ B(u) w_{1,B(u)} .

All hypotheses of the diluteness regime are *absent*: only `0 ≤ v` radial, `tsupport v ⊆ ball 0 R`
and the existence of a radial scattering solution (plus `MemLp v 1`, needed only for the
measurability of `g₂` inside the `ω`-mass identity) enter. -/
lemma mfM2M1_key {v : E3 → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v)
    {M' : ℕ} (hM' : 1 ≤ M') {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) :
    (_root_.BoseGases.a v / (2 * R)) *
        Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M' ℓ d u)
      ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M' ℓ d u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M' ℓ d u) := by
  classical
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set νA : MeasureTheory.Measure E3 :=
    (MeasureTheory.volume : MeasureTheory.Measure E3).restrict A with hνdef
  have hAmeas : MeasurableSet A := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hle : νA.prod νA ≤ (MeasureTheory.volume : MeasureTheory.Measure E3).prod
      (MeasureTheory.volume : MeasureTheory.Measure E3) := by
    rw [hνdef]
    exact MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self
      MeasureTheory.Measure.restrict_le_self
  -- ### 1. the `ω`-mass identity: the difference is the `ω₀`-weighted one-body mass
  have hId : Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) A
        (Submission.BoseGases.wSmallPair M' ℓ d u (Submission.BoseGases.g2 v h))
      - Work.BoseFixB1S.boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M' ℓ d u)
      = ∫ p in A ×ˢ A, Classical.choose h (p.1 - p.2)
          * Submission.BoseGases.wSmall1Pair h M' ℓ d u p.1 p.2 := by
    simpa only [hAdef] using
      (Work.BoseFixB1B.boxM2_sub_boxM1_eq_omegaMass (v := v) (R0 := R) hv_supp hR0 hv hvrad
        hv1 (h := h) (M := M') hM' (ℓ := ℓ) (d := d) hℓ hd u)
  -- ### 2. `boxM1` in iterated form
  have hvanF : ∀ x y : E3, (x ∉ A ∨ y ∉ A) →
      Submission.BoseGases.wSmallPair M' ℓ d u (Submission.BoseGases.g0 v h) x y = 0 :=
    fun x y hxy => Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM' hℓ hd u hxy
  have hvanF' : ∀ x y : E3, (x ∉ A ∨ y ∉ A) →
      Work.BoseFixB1B.omF h M' ℓ d u (x, y) = 0 :=
    fun x y hxy => hvanF x y hxy
  have hbox1 : Work.BoseFixB1S.boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M' ℓ d u)
      = ∫ x in A, ∫ y in A, Work.BoseFixB1B.omF h M' ℓ d u (x, y) := by
    have hnest1 : Work.BoseFixB1S.boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M' ℓ d u)
        = ∫ x : E3, ∫ y : E3, Submission.BoseGases.wSmall1Pair h M' ℓ d u x y := by
      simpa only [hAdef] using
        (Work.BoseFixB1S.boxM1_eq_nested (ℓ := ℓ) (d := d) u
          (w := Submission.BoseGases.wSmall1Pair h M' ℓ d u)
          (fun x y hxy => hvanF x y hxy))
    have hnest : Work.BoseFixB1S.boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M' ℓ d u)
        = ∫ x : E3, ∫ y : E3, Work.BoseFixB1B.omF h M' ℓ d u (x, y) := by
      rw [hnest1]
      rfl
    rw [hnest]
    have hout : (∫ x : E3, ∫ y : E3, Work.BoseFixB1B.omF h M' ℓ d u (x, y))
        = ∫ x in A, ∫ y : E3, Work.BoseFixB1B.omF h M' ℓ d u (x, y) :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := A) (f := fun x : E3 => ∫ y : E3, Work.BoseFixB1B.omF h M' ℓ d u (x, y))
        (fun x hx => by
          have hzero : (fun y : E3 => Work.BoseFixB1B.omF h M' ℓ d u (x, y)) =
              fun _ => (0 : ℝ) := by
            funext y
            exact hvanF' x y (Or.inl hx)
          rw [hzero, MeasureTheory.integral_zero])).symm
    rw [hout]
    refine MeasureTheory.setIntegral_congr_fun hAmeas (fun x _ => ?_)
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => hvanF' x y (Or.inr hy))).symm
  -- ### 3. the Fubini-type identification of the product and iterated integrals
  have hg0aem : AEMeasurable (Submission.BoseGases.g0 v h)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    (Submission.BoseGases.g0_integrable hR0 hv_supp h).aemeasurable
  have hw0aesm : MeasureTheory.AEStronglyMeasurable (Classical.choose h)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    (Classical.choose_spec h).2.lhs_integrable.aestronglyMeasurable
  have hFaesm0 : MeasureTheory.AEStronglyMeasurable
      (fun p => Work.BoseFixB1B.omF h M' ℓ d u p)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)) :=
    Work.BoseFixB1.aesm_wSmallPair_prod_full (M := M') (ℓ := ℓ) (d := d) u
      (f := Submission.BoseGases.g0 v h) hg0aem
  have hqmp : Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3))
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant _ _
  have hHaesm0 : MeasureTheory.AEStronglyMeasurable
      (fun p => Work.BoseFixB1B.omH h M' ℓ d u p)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)) :=
    (hw0aesm.comp_quasiMeasurePreserving hqmp).mul hFaesm0
  have hFaesm : MeasureTheory.AEStronglyMeasurable
      (fun p => Work.BoseFixB1B.omF h M' ℓ d u p) (νA.prod νA) :=
    hFaesm0.mono_measure hle
  have hHaesm : MeasureTheory.AEStronglyMeasurable
      (fun p => Work.BoseFixB1B.omH h M' ℓ d u p) (νA.prod νA) :=
    hHaesm0.mono_measure hle
  obtain ⟨hFnn0, hHnn0, hHF0, hcF0⟩ :=
    Work.BoseFixB1B.ae_om_bounds (v := v) (R0 := R) hv_supp hR0 hv hvrad h hM' ℓ d u
  have hFnn : 0 ≤ᵐ[νA.prod νA] (fun p => Work.BoseFixB1B.omF h M' ℓ d u p) :=
    (MeasureTheory.ae_mono hle) hFnn0
  have hHF : (fun p => Work.BoseFixB1B.omH h M' ℓ d u p) ≤ᵐ[νA.prod νA]
      (fun p => Work.BoseFixB1B.omF h M' ℓ d u p) :=
    (MeasureTheory.ae_mono hle) hHF0
  have hcF : ∀ᵐ p ∂(νA.prod νA), (_root_.BoseGases.a v / (2 * R)) *
      Work.BoseFixB1B.omF h M' ℓ d u p ≤ Work.BoseFixB1B.omH h M' ℓ d u p :=
    (MeasureTheory.ae_mono hle) hcF0
  have hFfibint : ∀ᵐ x ∂νA,
      MeasureTheory.Integrable (fun y => Work.BoseFixB1B.omF h M' ℓ d u (x, y)) νA :=
    Work.BoseFixB1B.ae_integrable_omF_fibre (v := v) (R0 := R) hv_supp hR0 hv hvrad h hM'
      hℓ hd u
  have hFub : (∫ p, Work.BoseFixB1B.omF h M' ℓ d u p ∂(νA.prod νA))
      = ∫ x in A, ∫ y in A, Work.BoseFixB1B.omF h M' ℓ d u (x, y) :=
    Work.BoseFixB1B.integral_prod_eq_iterated_of_ae_fibre_integrable hFaesm hFnn hFfibint
  -- ### 4. the monotonicity step and the identification of the right-hand side
  have hmono : (_root_.BoseGases.a v / (2 * R)) *
        (∫ p, Work.BoseFixB1B.omF h M' ℓ d u p ∂(νA.prod νA))
      ≤ ∫ p, Work.BoseFixB1B.omH h M' ℓ d u p ∂(νA.prod νA) :=
    mfM2M1_const_mul_integral_le (div_pos hav (by linarith)) hFaesm hHaesm hFnn hHF hcF
  have hId' : (∫ p, Work.BoseFixB1B.omH h M' ℓ d u p ∂(νA.prod νA))
      = Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) A
          (Submission.BoseGases.wSmallPair M' ℓ d u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1S.boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M' ℓ d u) := by
    rw [hId]
    have hν : νA.prod νA = ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)).restrict (A ×ˢ A) := by
      rw [hνdef]
      exact MeasureTheory.Measure.prod_restrict
        (μ := (MeasureTheory.volume : MeasureTheory.Measure E3))
        (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) A A
    rw [hν]
    rfl
  -- ### 5. assembly
  calc (_root_.BoseGases.a v / (2 * R)) *
        Work.BoseFixB1S.boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M' ℓ d u)
      = (_root_.BoseGases.a v / (2 * R)) *
          (∫ p, Work.BoseFixB1B.omF h M' ℓ d u p ∂(νA.prod νA)) := by
        rw [hbox1, hFub]
    _ ≤ ∫ p, Work.BoseFixB1B.omH h M' ℓ d u p ∂(νA.prod νA) := hmono
    _ = Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) A
          (Submission.BoseGases.wSmallPair M' ℓ d u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1S.boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M' ℓ d u) := hId'

/-- **The mass comparison `mfM2 ≥ (1 + c₀)·mfM1` at the sliding box** (the `mf*` form of the
comparison half of FS `lm:w2>w1`).  There is `c₀ = (a v)/(2R) > 0` such that for every admissible
`μ` and every sliding position `u` (no density/diluteness condition on the position is needed)

    c₀ · mfM1 h μ u ≤ mfM2 h μ u − mfM1 h μ u . -/
theorem mfM2_sub_mfM1_ge_const_mul_mfM1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v) {M : ℕ} (hM : 1 ≤ M) :
    ∃ ε₀ c₀ : ℝ, 0 < ε₀ ∧ 0 < c₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1S.mfInt v μ u →
        c₀ * Work.BoseFixB1S.mfM1 h μ u ≤ Work.BoseFixB1S.mfM2 h μ u - Work.BoseFixB1S.mfM1 h μ u := by
  refine ⟨1, _root_.BoseGases.a v / (2 * R), one_pos, div_pos hav (by linarith), ?_⟩
  intro μ hAdm u _hu
  have hMμ : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  exact mfM2M1_key (v := v) (R := R) hv_supp hR0 hv hvrad hv1 h hav hMμ
    (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm) u

end

end Work.BoseFixB1S
