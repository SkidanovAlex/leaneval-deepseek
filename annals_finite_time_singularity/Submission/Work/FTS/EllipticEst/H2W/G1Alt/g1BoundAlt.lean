import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.slice5_rel
import Submission.Work.FTS.EllipticEst.remov.slice5_eqn_deriv2
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.slice_v_identities
import Submission.Work.FTS.EllipticEst.remov.sliceUdivCosUniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- The statement of the crux `Work.FTS.EllipticEst.H2W.vTwoW4Weak`
(`Submission/Work/FTS/EllipticEst/H2W/vTwoW4Weak.lean`), as a hypothesis so that this
module can be used with whichever proof of it becomes available first
(`H2W.VTwoAlt.vTwoW4WeakAlt` is a sibling proof target). -/
def VTwoW4Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u : ℝ → ℝ),
    1 ≤ γ → γ ≤ 3 / 2 →
    ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))


set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Elementary arithmetic -/

private lemma sq_four_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b + c + d)]

/-! ## Facts on `Iθ` -/

private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

private lemma sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

private lemma measurable_sig2 (γ : ℝ) (hγ2 : γ ≤ 3 / 2) :
    Measurable (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
  (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).measurable.comp
    (Real.continuous_sin.measurable.comp (continuous_const.mul continuous_id).measurable)

/-- Almost every point of `Iθ` lies in the open interval. -/
private lemma ae_mem_Ioo :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))).symm
  rw [(show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl),
    MeasureTheory.Measure.restrict_congr_set h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The weight identity `sin²θ · sin(2θ)^{2-γ} = (sin(2θ)^{4-γ}/cos²θ)/4`. -/
private lemma sin_sq_mul_sig2 (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin θ ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      = Real.rpow (Real.sin (2 * θ)) (4 - γ) / (4 * Real.cos θ ^ 2) := by
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcos : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩).ne'
  have hsplit : Real.rpow (Real.sin (2 * θ)) (4 - γ)
      = Real.rpow (Real.sin (2 * θ)) (2 - γ) * Real.sin (2 * θ) ^ 2 := by
    have h := Real.rpow_add hpos (2 - γ) 2
    rw [show (2 - γ) + 2 = 4 - γ by ring, Real.rpow_two] at h
    exact h
  rw [hsplit, Real.sin_two_mul]
  field_simp
  ring

/-! ## The pointwise identity `g' = -u''' + sinθ·v'' + sinθ·v - 4u'` -/

private lemma gprime_ident_v (u g : ℝ → ℝ)
    (hu3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv g θ = - deriv (deriv (deriv u)) θ
        + Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ
        + Real.sin θ * (u θ / Real.cos θ) - 4 * deriv u θ := by
  intro θ hθ
  have hA := Work.FTS.EllipticEst.remov.slice_gprime_ident u g hu3 hode θ hθ
  have hB := Work.FTS.EllipticEst.remov.slice_v_identities u hu3 θ hθ
  rw [hA, hB.2.2.1, hB.2.2.2]
  ring

/-! ## The theorem -/

theorem g1BoundAlt (hcrux : VTwoW4Statement) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
    1 ≤ γ → γ ≤ 3 / 2 →
    ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  obtain ⟨Cw, hCwpos, hCw⟩ := hcrux
  obtain ⟨Cv, hCvpos, hCv⟩ := Work.FTS.EllipticEst.remov.sliceUdivCosUniform
  refine ⟨4 + Cw + 4 * Cv + 64, by linarith, ?_⟩
  intro γ u g hγ1 hγ2 hu4 hcont hu0 hupi hode hI4 hI3 hI2 hI1 hI0 hIg2
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hu3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) := hu4.of_le (by norm_num)
  -- abbreviations
  set sg2 : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ) with hsg2
  set w4 : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2 with hw4
  set A3 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ with hA3
  set A2 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
    Work.FTS.EllipticEst.sEta θ with hA2
  set A1 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hA1
  set A0 : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 with hA0
  set B2 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ) with hB2
  change (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * sg2 θ)
    ≤ (4 + Cw + 4 * Cv + 64) * (B2 + A3 + A2 + A1 + A0)
  -- nonnegativity of the data
  have hA3nn : 0 ≤ A3 := by
    rw [hA3]
    exact MeasureTheory.setIntegral_nonneg hIθmeas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have hA2nn : 0 ≤ A2 := by
    rw [hA2]
    exact MeasureTheory.setIntegral_nonneg hIθmeas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  have hA1nn : 0 ≤ A1 := by
    rw [hA1]; exact MeasureTheory.setIntegral_nonneg hIθmeas (fun θ _ => sq_nonneg _)
  have hA0nn : 0 ≤ A0 := by
    rw [hA0]; exact MeasureTheory.setIntegral_nonneg hIθmeas (fun θ _ => sq_nonneg _)
  have hB2nn : 0 ≤ B2 := by
    rw [hB2]
    exact MeasureTheory.setIntegral_nonneg hIθmeas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  -- restatements of the integrability hypotheses, in terms of `sg2`
  have hI3' : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ)
      Work.Spaces.Iθ := hI3
  have hI1' : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ := hI1
  -- the imported slot estimates
  have hVslots := hCv γ u hγ1 hγ2 hu3 hcont hu0 hupi hI1 hI0
  obtain ⟨hVint, hVle⟩ := hVslots
  have hVint' : MeasureTheory.IntegrableOn
      (fun θ => (u θ / Real.cos θ) ^ 2 * sg2 θ) Work.Spaces.Iθ := hVint
  have hVle' : (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 * sg2 θ)
      ≤ Cv * (A1 + A0) := hVle
  have hWle : (∫ θ in Work.Spaces.Iθ,
      (deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * w4 θ) ≤ Cw * (A3 + A2 + A1 + A0) :=
    hCw γ u hγ1 hγ2 hu4 hcont hu0 hupi hI3 hI2 hI1 hI0
  -- the pointwise identity and the pointwise bound
  have hid := gprime_ident_v u g hu3 hode
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv g θ) ^ 2 * sg2 θ ≤ 4 * ((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
        + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ
        + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ
        + 16 * (deriv u θ) ^ 2) := by
    intro θ hθ
    have h2 : (deriv g θ) ^ 2
        = (- deriv (deriv (deriv u)) θ
            + Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ
            + Real.sin θ * (u θ / Real.cos θ) + (-4 * deriv u θ)) ^ 2 := by
      rw [hid θ hθ]; ring
    have h4 := sq_four_le (- deriv (deriv (deriv u)) θ)
      (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ)
      (Real.sin θ * (u θ / Real.cos θ)) (-4 * deriv u θ)
    have hs : 0 ≤ sg2 θ := by
      rw [hsg2]
      exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
    have hs1 : sg2 θ ≤ 1 := by
      rw [hsg2]
      exact Real.rpow_le_one (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) (Real.sin_le_one _)
        (by linarith)
    have h4' := mul_le_mul_of_nonneg_right h4 hs
    have h64 : (-4 * deriv u θ) ^ 2 * sg2 θ ≤ (-4 * deriv u θ) ^ 2 := by
      have hnn : (0 : ℝ) ≤ (-4 * deriv u θ) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hs1 hnn]
    calc (deriv g θ) ^ 2 * sg2 θ
        = (- deriv (deriv (deriv u)) θ
            + Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ
            + Real.sin θ * (u θ / Real.cos θ) + (-4 * deriv u θ)) ^ 2 * sg2 θ := by rw [h2]
      _ ≤ (4 * ((- deriv (deriv (deriv u)) θ) ^ 2
              + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
              + (Real.sin θ * (u θ / Real.cos θ)) ^ 2
              + (-4 * deriv u θ) ^ 2)) * sg2 θ := h4'
      _ = 4 * ((((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
              + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ)
              + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
            + (-4 * deriv u θ) ^ 2 * sg2 θ) := by ring
      _ ≤ 4 * ((((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
              + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ)
              + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
            + (-4 * deriv u θ) ^ 2) := by linarith [h64]
      _ = 4 * ((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
            + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ
            + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ
            + 16 * (deriv u θ) ^ 2) := by ring
  -- the weight identity, almost everywhere on `Iθ`
  have hW4ae : (fun θ => (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
        * sg2 θ)
      =ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ]
      (fun θ => ((deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * w4 θ) / 4) := by
    filter_upwards [ae_mem_Ioo] with θ hθ
    rw [hsg2, hw4]
    have h := sin_sq_mul_sig2 γ hθ
    calc (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        = (deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
          * (Real.sin θ ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by ring
      _ = (deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
          * (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (4 * Real.cos θ ^ 2)) := by rw [h]
      _ = (deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
          * (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2) / 4 := by ring
  -- integrability of the `(sinθ · v)²σ₂` piece
  have hz3Int : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ) Work.Spaces.Iθ := by
    have hmeas : AEStronglyMeasurable
        (fun θ => (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
      refine AEStronglyMeasurable.mul (AEStronglyMeasurable.pow ?_ 2)
        (measurable_sig2 γ hγ2).aestronglyMeasurable
      refine AEStronglyMeasurable.mul Real.continuous_sin.measurable.aestronglyMeasurable ?_
      exact AEStronglyMeasurable.div₀ (hcont.aestronglyMeasurable hIθmeas)
        Real.continuous_cos.measurable.aestronglyMeasurable
    refine MeasureTheory.Integrable.mono' hVint' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIθmeas] with θ hθ
    have hs : 0 ≤ sg2 θ := by
      rw [hsg2]
      exact Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _
    have hv : 0 ≤ (u θ / Real.cos θ) ^ 2 := sq_nonneg _
    have h1 : 0 ≤ (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ :=
      mul_nonneg (sq_nonneg _) hs
    have h2 : 0 ≤ (u θ / Real.cos θ) ^ 2 * sg2 θ := mul_nonneg hv hs
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    have hs1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    nlinarith [mul_nonneg hv hs, sq_nonneg (Real.sin θ)]
  -- the case split
  by_cases hD : MeasureTheory.IntegrableOn
      (fun θ => (deriv g θ) ^ 2 * sg2 θ) Work.Spaces.Iθ
  · -- main case
    have hz2Int : MeasureTheory.IntegrableOn
        (fun θ => (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
          * sg2 θ) Work.Spaces.Iθ := by
      have hmaj : MeasureTheory.IntegrableOn (fun θ => 4 * ((deriv g θ) ^ 2 * sg2 θ
          + (deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ
          + 16 * (deriv u θ) ^ 2)) Work.Spaces.Iθ :=
        (((hD.add hI3').add hz3Int).add (hI1'.const_mul 16)).const_mul 4
      have hmeas : AEStronglyMeasurable
          (fun θ => (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
            * sg2 θ) ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
        (AEStronglyMeasurable.mul (AEStronglyMeasurable.pow
          (AEStronglyMeasurable.mul Real.continuous_sin.measurable.aestronglyMeasurable
            (measurable_deriv (deriv (fun s => u s / Real.cos s))).aestronglyMeasurable) 2)
          (measurable_sig2 γ hγ2).aestronglyMeasurable)
      refine MeasureTheory.Integrable.mono' hmaj hmeas ?_
      filter_upwards [ae_mem_Ioo] with θ hθ
      have h := hid θ hθ
      have hS : Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ
          = deriv g θ + deriv (deriv (deriv u)) θ
            - Real.sin θ * (u θ / Real.cos θ) + 4 * deriv u θ := by linarith
      have hs : 0 ≤ sg2 θ := by
        rw [hsg2]
        exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
      have hs1 : sg2 θ ≤ 1 := by
        rw [hsg2]
        exact Real.rpow_le_one (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) (Real.sin_le_one _)
          (by linarith)
      have h4 := sq_four_le (deriv g θ) (deriv (deriv (deriv u)) θ)
        (-(Real.sin θ * (u θ / Real.cos θ))) (4 * deriv u θ)
      have h4' := mul_le_mul_of_nonneg_right h4 hs
      have hnn : 0 ≤ (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
          * sg2 θ := mul_nonneg (sq_nonneg _) hs
      have h16 : (4 * deriv u θ) ^ 2 * sg2 θ ≤ (4 * deriv u θ) ^ 2 := by
        have hnn2 : (0 : ℝ) ≤ (4 * deriv u θ) ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hs1 hnn2]
      rw [Real.norm_eq_abs, abs_of_nonneg hnn, hS]
      calc (deriv g θ + deriv (deriv (deriv u)) θ - Real.sin θ * (u θ / Real.cos θ)
            + 4 * deriv u θ) ^ 2 * sg2 θ
          = (deriv g θ + deriv (deriv (deriv u)) θ
              + (-(Real.sin θ * (u θ / Real.cos θ))) + (4 * deriv u θ)) ^ 2 * sg2 θ := by ring
        _ ≤ (4 * ((deriv g θ) ^ 2 + (deriv (deriv (deriv u)) θ) ^ 2
              + (-(Real.sin θ * (u θ / Real.cos θ))) ^ 2 + (4 * deriv u θ) ^ 2)) * sg2 θ := h4'
        _ = 4 * ((((deriv g θ) ^ 2 * sg2 θ + (deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ)
              + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
            + (4 * deriv u θ) ^ 2 * sg2 θ) := by ring
        _ ≤ 4 * ((((deriv g θ) ^ 2 * sg2 θ + (deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ)
              + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
            + (4 * deriv u θ) ^ 2) := by linarith [h16]
        _ = 4 * ((deriv g θ) ^ 2 * sg2 θ + (deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
              + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ
              + 16 * (deriv u θ) ^ 2) := by ring
    have hmajInt : MeasureTheory.IntegrableOn
        (fun θ => 4 * ((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ
          + 16 * (deriv u θ) ^ 2)) Work.Spaces.Iθ :=
      (((hI3'.add hz2Int).add hz3Int).add (hI1'.const_mul 16)).const_mul 4
    have hle := MeasureTheory.integral_mono_ae hD hmajInt
      (ae_mem_Ioo.mono (fun θ hθ => hpt θ hθ))
    -- the value of the majorant integral
    have hMajVal : (∫ θ in Work.Spaces.Iθ, 4 * ((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ + 16 * (deriv u θ) ^ 2))
        = 4 * (A3 + (∫ θ in Work.Spaces.Iθ,
              (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ)
            + (∫ θ in Work.Spaces.Iθ, (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
            + 16 * A1) := by
      rw [MeasureTheory.integral_const_mul]
      have hpoint : ∀ x : ℝ, (deriv (deriv (deriv u)) x) ^ 2 * sg2 x
            + (Real.sin x * deriv (deriv (fun s => u s / Real.cos s)) x) ^ 2 * sg2 x
            + (Real.sin x * (u x / Real.cos x)) ^ 2 * sg2 x + 16 * (deriv u x) ^ 2
          = ((deriv (deriv (deriv u)) x) ^ 2 * sg2 x
              + (Real.sin x * deriv (deriv (fun s => u s / Real.cos s)) x) ^ 2 * sg2 x)
            + (((Real.sin x * (u x / Real.cos x)) ^ 2 * sg2 x) + 16 * (deriv u x) ^ 2) :=
        fun x => by ring
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
      have h12 : MeasureTheory.Integrable (fun x : ℝ =>
          (deriv (deriv (deriv u)) x) ^ 2 * sg2 x
            + (Real.sin x * deriv (deriv (fun s => u s / Real.cos s)) x) ^ 2 * sg2 x)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hI3'.add hz2Int
      have h34 : MeasureTheory.Integrable (fun x : ℝ =>
          (Real.sin x * (u x / Real.cos x)) ^ 2 * sg2 x + 16 * (deriv u x) ^ 2)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hz3Int.add (hI1'.const_mul 16)
      rw [MeasureTheory.integral_add h12 h34]
      have h1 : MeasureTheory.Integrable (fun x : ℝ => (deriv (deriv (deriv u)) x) ^ 2 * sg2 x)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hI3'
      have h2 : MeasureTheory.Integrable (fun x : ℝ =>
          (Real.sin x * deriv (deriv (fun s => u s / Real.cos s)) x) ^ 2 * sg2 x)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hz2Int
      have h3 : MeasureTheory.Integrable (fun x : ℝ =>
          (Real.sin x * (u x / Real.cos x)) ^ 2 * sg2 x)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hz3Int
      have h4 : MeasureTheory.Integrable (fun x : ℝ => 16 * (deriv u x) ^ 2)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hI1'.const_mul 16
      rw [MeasureTheory.integral_add h1 h2]
      have hpoint2 : ∀ x : ℝ, (Real.sin x * (u x / Real.cos x)) ^ 2 * sg2 x
            + 16 * (deriv u x) ^ 2
          = (Real.sin x * (u x / Real.cos x)) ^ 2 * sg2 x
            + (fun y : ℝ => 16 * (deriv u y) ^ 2) x := fun x => rfl
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint2)]
      rw [MeasureTheory.integral_add h3 h4, MeasureTheory.integral_const_mul, hA3.symm,
        hA1.symm]
      ring
    -- the two slot bounds
    have hz2le : (∫ θ in Work.Spaces.Iθ,
        (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ)
        ≤ (Cw / 4) * (A3 + A2 + A1 + A0) := by
      have heq : (∫ θ in Work.Spaces.Iθ,
          (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ)
          = (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * w4 θ) / 4 := by
        rw [MeasureTheory.integral_congr_ae hW4ae, MeasureTheory.integral_div]
      rw [heq]
      have h := mul_le_mul_of_nonneg_left hWle (by norm_num : (0 : ℝ) ≤ 1 / 4)
      linarith [h]
    have hz3le : (∫ θ in Work.Spaces.Iθ, (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
        ≤ Cv * (A1 + A0) := by
      refine le_trans ?_ hVle'
      refine MeasureTheory.integral_mono_ae hz3Int hVint' ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hIθmeas] with θ hθ
      have hs : 0 ≤ sg2 θ := by
        rw [hsg2]
        exact Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _
      have hv : 0 ≤ (u θ / Real.cos θ) ^ 2 := sq_nonneg _
      have hs1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
      nlinarith [mul_nonneg hv hs, sq_nonneg (Real.sin θ)]
    -- assembly
    have step1 : (∫ θ in Work.Spaces.Iθ, 4 * ((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ + 16 * (deriv u θ) ^ 2))
        ≤ 4 * (A3 + (Cw / 4) * (A3 + A2 + A1 + A0) + Cv * (A1 + A0) + 16 * A1) := by
      rw [hMajVal]
      linarith [hz2le, hz3le]
    have step2 : 4 * (A3 + (Cw / 4) * (A3 + A2 + A1 + A0) + Cv * (A1 + A0) + 16 * A1)
        ≤ (4 + Cw) * (A3 + A2 + A1 + A0) + (4 * Cv + 64) * (A1 + A0) := by
      nlinarith [hA2nn, hA1nn, hA0nn, hCwpos, hCvpos]
    have step3 : (4 + Cw) * (A3 + A2 + A1 + A0) + (4 * Cv + 64) * (A1 + A0)
        ≤ (4 + Cw + 4 * Cv + 64) * (B2 + A3 + A2 + A1 + A0) := by
      have h1 : A3 + A2 + A1 + A0 ≤ B2 + A3 + A2 + A1 + A0 := by linarith [hB2nn]
      have h2 : A1 + A0 ≤ B2 + A3 + A2 + A1 + A0 := by linarith [hB2nn, hA3nn, hA2nn]
      have h3 : 0 ≤ B2 + A3 + A2 + A1 + A0 := by
        linarith [hB2nn, hA3nn, hA2nn, hA1nn, hA0nn]
      have h4 : 0 ≤ A3 + A2 + A1 + A0 := by linarith [hA3nn, hA2nn, hA1nn, hA0nn]
      have h5 : 0 ≤ A1 + A0 := by linarith [hA1nn, hA0nn]
      nlinarith [h1, h2, h3, h4, h5, hCwpos, hCvpos]
    exact le_trans hle (le_trans step1 (le_trans step2 step3))
  · -- junk case
    have hzero : (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * sg2 θ) = 0 :=
      MeasureTheory.integral_undef hD
    have h3 : 0 ≤ B2 + A3 + A2 + A1 + A0 := by
      linarith [hB2nn, hA3nn, hA2nn, hA1nn, hA0nn]
    have hCpos : 0 < 4 + Cw + 4 * Cv + 64 := by linarith [hCwpos, hCvpos]
    rw [hzero]
    nlinarith [h3, hCpos]

end

end Work.FTS.EllipticEst.H2W
