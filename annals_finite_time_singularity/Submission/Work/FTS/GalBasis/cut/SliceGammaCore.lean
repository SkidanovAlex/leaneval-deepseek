/-
Copyright: work module for the Elgindi finite-time singularity project.

# The core estimate on a closed subinterval for `Work.FTS.GalBasis.cut.sliceGamma`

For `0 < α ≤ β < π/2`, `b > 0`, `γ - 1 - b > 0` and `G` of class `C¹` on `(0, π/2)`,

  `4·min(b, b(γ-1-b)) · ∫_α^β G² sin(2θ)^{-γ} ≤ ∫_α^β (G')² sin(2θ)^{2-γ} + [A·G²]_α^β`,

where `A = sgA γ b`.  This is the completion of squares of `sgPtwise_aux`: with `Φ = sgPhi b`,
`w = sgW γ`, `w₀ = sgW0 γ` and `A = Φ·w` one has

  `G'²w = (G' + GΦ)²w + G²(A' - ΦA) - (G²A)'`     and      `A' - ΦA ≥ 4·min(b, b(γ-1-b))·w₀`,

so the square term can be dropped and the flux term integrated by the fundamental theorem of
calculus.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.GalBasis.cut.SliceGammaDefs
import Submission.Work.FTS.GalBasis.cut.sliceGammaPtwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cut

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The pointwise calculus of the completion of squares (from the pointwise `rpow` identities
of `sliceGammaPtwise`). -/
private theorem sgPtwise_aux {γ b θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (sgA γ b) (sgAd γ b θ) θ ∧
    (sgAd γ b θ - sgPhi b θ * sgA γ b θ
      = (4 * b * (sgS θ) ^ 2 + 4 * b * (γ - 1 - b) * (sgC θ) ^ 2) * sgW0 γ θ) ∧
    (sgA γ b θ = sgPhi b θ * sgW γ θ) := by
  obtain ⟨h1, h2, h3⟩ := sliceGammaPtwise (γ := γ) (b := b) hθ
  refine ⟨?_, ?_, ?_⟩
  · change HasDerivAt (fun t : ℝ => -2 * b * Real.cos (2 * t) * (Real.sin (2 * t)) ^ (1 - γ))
      (4 * b * (Real.sin (2 * θ)) ^ (2 - γ) + 4 * b * (γ - 1) * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-γ)) θ
    exact h1
  · change (4 * b * (Real.sin (2 * θ)) ^ (2 - γ) + 4 * b * (γ - 1) * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-γ))
      - (-2 * b * Real.cos (2 * θ) / (Real.sin (2 * θ)))
          * (-2 * b * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (1 - γ))
      = (4 * b * (Real.sin (2 * θ)) ^ 2 + 4 * b * (γ - 1 - b) * (Real.cos (2 * θ)) ^ 2)
          * (Real.sin (2 * θ)) ^ (-γ)
    exact h2
  · change (-2 * b * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (1 - γ)
      = (-2 * b * Real.cos (2 * θ) / (Real.sin (2 * θ))) * (Real.sin (2 * θ)) ^ (2 - γ))
    exact h3

/-- **The core estimate on a closed subinterval.** -/
theorem sliceGamma_core {γ b : ℝ} (hb : 0 < b) (hbγ : 0 < γ - 1 - b)
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ 1 G (Set.Ioo 0 (Real.pi / 2)))
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β < Real.pi / 2) :
    (4 * min b (b * (γ - 1 - b))) * (∫ θ in α..β, sgF γ G θ)
      ≤ (∫ θ in α..β, sgD γ G θ) + sgCfun γ b G β - sgCfun γ b G α := by
  have hxO : ∀ x ∈ Set.Icc α β, x ∈ Set.Ioo 0 (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hα hx.1, lt_of_le_of_lt hx.2 hβ⟩
  have hs_pos : ∀ x ∈ Set.Icc α β, 0 < Real.sin (2 * x) := fun x hx => by
    have h := hxO x hx
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2, Real.pi_pos])
  -- the three pointwise facts
  have hA_deriv : ∀ x ∈ Set.Icc α β, HasDerivAt (sgA γ b) (sgAd γ b x) x := fun x hx =>
    (sgPtwise_aux (γ := γ) (b := b) (hxO x hx)).1
  have hAw : ∀ x ∈ Set.Icc α β, sgA γ b x = sgPhi b x * sgW γ x := fun x hx =>
    (sgPtwise_aux (γ := γ) (b := b) (hxO x hx)).2.2
  have hgap : ∀ x ∈ Set.Icc α β,
      (4 * min b (b * (γ - 1 - b))) * sgW0 γ x ≤ sgAd γ b x - sgPhi b x * sgA γ b x := by
    intro x hx
    rw [(sgPtwise_aux (γ := γ) (b := b) (hxO x hx)).2.1]
    have hnum : 4 * min b (b * (γ - 1 - b))
        ≤ 4 * b * (sgS x) ^ 2 + 4 * b * (γ - 1 - b) * (sgC x) ^ 2 := by
      have h1 := min_le_left b (b * (γ - 1 - b))
      have h2 := min_le_right b (b * (γ - 1 - b))
      have h3 : (sgS x) ^ 2 + (sgC x) ^ 2 = 1 := sgS_sq_add_sgC_sq x
      have h4 : 0 ≤ (sgS x) ^ 2 := sq_nonneg _
      have h5 : 0 ≤ (sgC x) ^ 2 := sq_nonneg _
      nlinarith [h1, h2, h3, h4, h5]
    exact mul_le_mul_of_nonneg_right hnum (le_of_lt (sgW0_pos (hxO x hx)))
  -- differentiability of `G` on the open subinterval
  have hGd : ∀ x ∈ Set.Ioo α β, HasDerivAt G (deriv G x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := ⟨lt_trans hα hx.1, lt_trans hx.2 hβ⟩
    exact (((hG.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hx'))).hasDerivAt
  -- the derivative of the flux `A·G²`
  have hcfun_deriv : ∀ x ∈ Set.Ioo α β,
      HasDerivAt (fun y : ℝ => sgCfun γ b G y)
        (sgAd γ b x * (G x) ^ 2 + sgA γ b x * (2 * G x * deriv G x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => (G y) ^ 2) (2 * G x * deriv G x) x :=
      ((hGd x hx).pow 2).congr_deriv (by ring)
    have h2 := (hA_deriv x (Ioo_subset_Icc_self hx)).mul h1
    unfold sgCfun
    exact h2
  -- continuity
  have hcontG : ContinuousOn G (Set.Icc α β) := hG.continuousOn.mono (fun x hx => hxO x hx)
  have hcontdG : ContinuousOn (deriv G) (Set.Icc α β) :=
    (hG.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono
      (fun x hx => hxO x hx)
  have hcont_sin : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.Icc α β) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcont_cos : ContinuousOn (fun x : ℝ => Real.cos (2 * x)) (Set.Icc α β) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hcont_w : ContinuousOn (sgW γ) (Set.Icc α β) := by
    unfold sgW
    exact hcont_sin.rpow_const (fun x hx => Or.inl (ne_of_gt (hs_pos x hx)))
  have hcont_w0 : ContinuousOn (sgW0 γ) (Set.Icc α β) := by
    unfold sgW0
    exact hcont_sin.rpow_const (fun x hx => Or.inl (ne_of_gt (hs_pos x hx)))
  have hcont_phi : ContinuousOn (sgPhi b) (Set.Icc α β) := by
    unfold sgPhi
    exact (hcont_cos.const_mul (-2 * b)).div hcont_sin (fun x hx => ne_of_gt (hs_pos x hx))
  have hcont_A : ContinuousOn (sgA γ b) (Set.Icc α β) := by
    unfold sgA
    exact (hcont_cos.const_mul (-2 * b)).mul
      (hcont_sin.rpow_const (fun x hx => Or.inl (ne_of_gt (hs_pos x hx))))
  have hcont_Ad : ContinuousOn (sgAd γ b) (Set.Icc α β) := by
    unfold sgAd
    refine ((hcont_sin.rpow_const (fun x hx => Or.inl (ne_of_gt (hs_pos x hx)))).const_mul
      (4 * b)).add ?_
    exact ((hcont_cos.pow 2).const_mul (4 * b * (γ - 1))).mul
      (hcont_sin.rpow_const (fun x hx => Or.inl (ne_of_gt (hs_pos x hx))))
  have hcfun_cont : ContinuousOn (sgCfun γ b G) (Set.Icc α β) := by
    unfold sgCfun
    exact hcont_A.mul (hcontG.pow 2)
  -- interval integrability of the pieces
  have huIcc : Set.uIcc α β = Set.Icc α β := Set.uIcc_of_le hαβ
  have hIntD : IntervalIntegrable
      (fun x => sgAd γ b x * (G x) ^ 2 + sgA γ b x * (2 * G x * deriv G x)) volume α β := by
    have h : ContinuousOn
        (fun x => sgAd γ b x * (G x) ^ 2 + sgA γ b x * (2 * G x * deriv G x))
        (Set.uIcc α β) := by
      rw [huIcc]
      exact (hcont_Ad.mul (hcontG.pow 2)).add (hcont_A.mul ((hcontG.const_mul 2).mul hcontdG))
    exact h.intervalIntegrable
  have hintZ : IntervalIntegrable
      (fun x => ((deriv G x) + G x * sgPhi b x) ^ 2 * sgW γ x) volume α β := by
    have h : ContinuousOn (fun x => ((deriv G x) + G x * sgPhi b x) ^ 2 * sgW γ x)
        (Set.uIcc α β) := by
      rw [huIcc]; exact ((hcontdG.add (hcontG.mul hcont_phi)).pow 2).mul hcont_w
    exact h.intervalIntegrable
  have hintU : IntervalIntegrable
      (fun x => (G x) ^ 2 * (sgAd γ b x - sgPhi b x * sgA γ b x)) volume α β := by
    have h : ContinuousOn (fun x => (G x) ^ 2 * (sgAd γ b x - sgPhi b x * sgA γ b x))
        (Set.uIcc α β) := by
      rw [huIcc]; exact (hcontG.pow 2).mul (hcont_Ad.sub (hcont_phi.mul hcont_A))
    exact h.intervalIntegrable
  have hintX : IntervalIntegrable (fun x => (G x) ^ 2 * sgW0 γ x) volume α β := by
    have h : ContinuousOn (fun x => (G x) ^ 2 * sgW0 γ x) (Set.uIcc α β) := by
      rw [huIcc]; exact (hcontG.pow 2).mul hcont_w0
    exact h.intervalIntegrable
  -- the fundamental theorem of calculus for the flux
  have hFtc : (∫ x in α..β, (sgAd γ b x * (G x) ^ 2 + sgA γ b x * (2 * G x * deriv G x)))
      = sgCfun γ b G β - sgCfun γ b G α :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hαβ hcfun_cont hcfun_deriv hIntD
  -- the pointwise identity
  have hpt : ∀ x ∈ Set.Icc α β,
      sgD γ G x
        = ((deriv G x) + G x * sgPhi b x) ^ 2 * sgW γ x
          + (G x) ^ 2 * (sgAd γ b x - sgPhi b x * sgA γ b x)
          - (sgAd γ b x * (G x) ^ 2 + sgA γ b x * (2 * G x * deriv G x)) := by
    intro x hx
    rw [hAw x hx]
    simp only [sgD]
    ring
  -- the integrated identity
  have hsplit : (∫ x in α..β, sgD γ G x)
      = (∫ x in α..β, ((deriv G x) + G x * sgPhi b x) ^ 2 * sgW γ x)
        + (∫ x in α..β, (G x) ^ 2 * (sgAd γ b x - sgPhi b x * sgA γ b x))
        - (∫ x in α..β, (sgAd γ b x * (G x) ^ 2 + sgA γ b x * (2 * G x * deriv G x))) := by
    have hcongr : (∫ x in α..β, sgD γ G x)
        = ∫ x in α..β, (((deriv G x) + G x * sgPhi b x) ^ 2 * sgW γ x
            + (G x) ^ 2 * (sgAd γ b x - sgPhi b x * sgA γ b x)
            - (sgAd γ b x * (G x) ^ 2 + sgA γ b x * (2 * G x * deriv G x))) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [huIcc] at hx
      exact hpt x hx
    rw [hcongr, intervalIntegral.integral_sub (hintZ.add hintU) hIntD,
      intervalIntegral.integral_add hintZ hintU]
  -- the two integral inequalities
  have hZnn : 0 ≤ ∫ x in α..β, ((deriv G x) + G x * sgPhi b x) ^ 2 * sgW γ x :=
    intervalIntegral.integral_nonneg hαβ (fun x hx =>
      mul_nonneg (sq_nonneg _) (le_of_lt (sgW_pos (hxO x hx))))
  have hUle : (4 * min b (b * (γ - 1 - b))) * (∫ x in α..β, sgF γ G x)
      ≤ ∫ x in α..β, (G x) ^ 2 * (sgAd γ b x - sgPhi b x * sgA γ b x) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hαβ (hintX.const_mul _) hintU (fun x hx => ?_)
    have h := mul_le_mul_of_nonneg_left (hgap x hx) (sq_nonneg (G x))
    calc (4 * min b (b * (γ - 1 - b))) * ((G x) ^ 2 * sgW0 γ x)
        = (G x) ^ 2 * ((4 * min b (b * (γ - 1 - b))) * sgW0 γ x) := by ring
      _ ≤ (G x) ^ 2 * (sgAd γ b x - sgPhi b x * sgA γ b x) := h
  linarith [hUle, hsplit, hZnn, hFtc]

end Work.FTS.GalBasis.cut
