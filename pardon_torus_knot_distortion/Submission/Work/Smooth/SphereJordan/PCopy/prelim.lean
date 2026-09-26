import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.SpanHyp
import Submission.Work.Smooth.SphereJordan.PCopy.SpanSetup
import Submission.Work.Smooth.SphereJordan.PCopy.tgtUpPC_isSimple
import Submission.Work.Smooth.SphereJordan.BoundedSide
import Submission.Work.Smooth.SphereJordan.windNumber_ne_zero_of_mem_V
import Submission.Work.Smooth.SphereJordan.thetaTwoHalvesSphereOfPlane

/-!
# The bounded side of `γ` avoids the four target curves

For the two-pccuts configuration `H : pcSpanHyp h hs hball S`, the bounded side `S.V` of `γ` is
disjoint from the trace of each of the four four-arc curves `H.pcupPC b`, `H.pcdnPC b`.  Consequently
each of the four winding-number functions `x ↦ windNumber (H.pcupPC b).γ _ x` is constant on `S.V`
(which is preconnected).
-/

open Set

namespace Work.SphereJordan

noncomputable section

open Work.Smooth.Jordan

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The bounded side of a simple closed curve in the open unit disc lies in the open unit disc. -/
theorem pcV_subset_ball (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) : S.V ⊆ Metric.ball (0 : ℂ) 1 := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  by_contra hcon
  push_neg at hcon
  have hle : ‖x‖ ≤ 1 :=
    Work.Smooth.SphereJordan.planeSeparation_V_subset_closedBall S.toPlaneSeparation hball x hx
  have heq : ‖x‖ = 1 := le_antisymm hle hcon
  obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp (S.isOpen_V.mem_nhds hx)
  have hclose : ((1 + ε / 2 : ℝ) : ℂ) * x ∈ S.V := by
    apply hε'
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : ((1 + ε / 2 : ℝ) : ℂ) * x - x = ((ε / 2 : ℝ) : ℂ) * x := by push_cast; ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), heq, mul_one]
    linarith
  have hbd :=
    Work.Smooth.SphereJordan.planeSeparation_V_subset_closedBall S.toPlaneSeparation hball _ hclose
  have hnorm : ‖((1 + ε / 2 : ℝ) : ℂ) * x‖ = 1 + ε / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), heq, mul_one]
  rw [hnorm] at hbd
  linarith

/-- The trace of `γ` avoids its bounded side. -/
theorem pctrace_notMem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t : ℝ} :
    γ.γ t ∉ S.V := by
  intro h
  have hmem : γ.γ t ∈ S.U ∪ S.V := Or.inr h
  rw [S.union_eq] at hmem
  exact hmem ⟨t, rfl⟩

/-- The upper outer semicircle avoids `S.V`. -/
theorem pcsrcOuterUp_notMem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (x : ℝ) :
    Work.Smooth.SphereJordan.pcsrcOuterUp S x ∉ S.V := by
  intro h
  have h1 := pcV_subset_ball S hball h
  rw [Metric.mem_ball, dist_zero_right] at h1
  rw [Work.SphereJordan.pcnorm_srcOuterUp] at h1
  linarith

/-- The lower outer semicircle avoids `S.V`. -/
theorem pcsrcOuterDn_notMem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (x : ℝ) :
    Work.Smooth.SphereJordan.pcsrcOuterDn S x ∉ S.V := by
  intro h
  have h1 := pcV_subset_ball S hball h
  rw [Metric.mem_ball, dist_zero_right] at h1
  have hnorm : ‖Work.Smooth.SphereJordan.pcsrcOuterDn S x‖ = 1 := by
    have hneg : Work.Smooth.SphereJordan.pcsrcOuterDn S x =
        -(Work.Smooth.SphereJordan.pcsrcOuterUp S x) := by
      rw [Work.Smooth.SphereJordan.pcsrcOuterDn, Work.Smooth.SphereJordan.pcsrcOuterUp]
      ring
    rw [hneg, norm_neg, Work.SphereJordan.pcnorm_srcOuterUp]
  rw [hnorm] at h1
  linarith

/-- The first crosscut avoids `S.V`. -/
theorem pctgtCut₁_notMem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ : ℝ} (ht₁s₁ : t₁ < s₁)
    (ha₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (t₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
        Metric.ball (0 : ℂ) 1 \ S.V)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁ y ∉ S.V := by
  set σ : ℝ := s₁ + y * (t₁ - s₁) with hσ
  have hσmem : t₁ ≤ σ ∧ σ ≤ s₁ := by
    constructor
    · rw [hσ]; nlinarith
    · rw [hσ]; nlinarith
  have hval : Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁ y =
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
    rw [Work.Smooth.SphereJordan.pctgtCut₁, hσ]
  rw [hval]
  rcases lt_or_eq_of_le hσmem.1 with hlt | heq
  · rcases lt_or_eq_of_le hσmem.2 with hlt2 | heq2
    · exact (hseg₁ σ hlt hlt2).2
    · rw [heq2, hout₁]
      intro hmem
      have h1 := pcV_subset_ball S hball hmem
      rw [Metric.mem_ball, dist_zero_right, Work.Smooth.SphereJordan.pcnorm_cutDir] at h1
      linarith
  · rw [← heq]
    obtain ⟨θ, hθ⟩ := ha₁
    rw [← hθ]
    exact pctrace_notMem_V S

/-- The second crosscut avoids `S.V`. -/
theorem pctgtCut₂_notMem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₂ s₂ : ℝ} (ht₂s₂ : t₂ < s₂)
    (ha₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (t₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
        Metric.ball (0 : ℂ) 1 \ S.V)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂ y ∉ S.V := by
  set σ : ℝ := s₂ + y * (t₂ - s₂) with hσ
  have hσmem : t₂ ≤ σ ∧ σ ≤ s₂ := by
    constructor
    · rw [hσ]; nlinarith
    · rw [hσ]; nlinarith
  have hval : Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂ y =
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
    rw [Work.Smooth.SphereJordan.pctgtCut₂, hσ]
  rw [hval]
  rcases lt_or_eq_of_le hσmem.1 with hlt | heq
  · rcases lt_or_eq_of_le hσmem.2 with hlt2 | heq2
    · exact (hseg₂ σ hlt hlt2).2
    · rw [heq2, hout₂]
      intro hmem
      have h1 := pcV_subset_ball S hball hmem
      rw [Metric.mem_ball, dist_zero_right, norm_neg, Work.Smooth.SphereJordan.pcnorm_cutDir] at h1
      linarith
  · rw [← heq]
    obtain ⟨θ, hθ⟩ := ha₂
    rw [← hθ]
    exact pctrace_notMem_V S

/-- **The trace of `H.pcupPC b` avoids `S.V`.** -/
theorem pcupPC_notMem_V (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : pcSpanHyp h hs hball S) (b : Bool) (τ : ℝ) : (H.pcupPC b).γ τ ∉ S.V := by
  rw [pcSpanHyp.pcupPC_apply, Work.SphereJordan.pctgtUpB_eq]
  set σ := Work.Smooth.SphereJordan.pcperPt τ with hσ
  have hσmem : σ ∈ Set.Ico 0 (2 * Real.pi) := Work.SphereJordan.pcperPt_mem τ
  have hpos : (0:ℝ) < Real.pi / 2 := by positivity
  simp only [Work.SphereJordan.pctgtUpBun]
  rcases le_or_gt σ (Real.pi / 2) with h1 | h1
  · rw [if_pos h1]
    exact pcsrcOuterUp_notMem_V S hball _
  · rw [if_neg (not_le.mpr h1)]
    rcases le_or_gt σ Real.pi with h2 | h2
    · rw [if_pos h2]
      refine pctgtCut₂_notMem_V S hball H.ht₂s₂ H.ha₂ H.hseg₂ H.hout₂ (by positivity) ?_
      rw [div_le_one hpos]
      linarith
    · rw [if_neg (not_le.mpr h2)]
      rcases le_or_gt σ (3 * Real.pi / 2) with h3 | h3
      · rw [if_pos h3]
        by_cases hb : b
        · rw [if_pos hb]; exact pctrace_notMem_V S
        · rw [if_neg hb]; exact pctrace_notMem_V S
      · rw [if_neg (not_le.mpr h3)]
        refine pctgtCut₁_notMem_V S hball H.ht₁s₁ H.ha₁ H.hseg₁ H.hout₁ ?_ ?_
        · have hx : (σ - 3 * Real.pi / 2) / (Real.pi / 2) ≤ 1 := by
            rw [div_le_one (by positivity : (0:ℝ) < Real.pi / 2)]
            linarith [hσmem.2]
          linarith
        · have hx : 0 ≤ (σ - 3 * Real.pi / 2) / (Real.pi / 2) :=
            div_nonneg (by linarith [h3]) (by positivity)
          linarith

/-- **The trace of `H.pcdnPC b` avoids `S.V`.** -/
theorem pcdnPC_notMem_V (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : pcSpanHyp h hs hball S) (b : Bool) (τ : ℝ) : (H.pcdnPC b).γ τ ∉ S.V := by
  rw [pcSpanHyp.pcdnPC_apply, Work.SphereJordan.pctgtDnB_eq]
  set σ := Work.Smooth.SphereJordan.pcperPt τ with hσ
  have hσmem : σ ∈ Set.Ico 0 (2 * Real.pi) := Work.SphereJordan.pcperPt_mem τ
  have hpos : (0:ℝ) < Real.pi / 2 := by positivity
  simp only [Work.SphereJordan.pctgtDnBun]
  rcases le_or_gt σ (Real.pi / 2) with h1 | h1
  · rw [if_pos h1]
    exact pcsrcOuterDn_notMem_V S hball _
  · rw [if_neg (not_le.mpr h1)]
    rcases le_or_gt σ Real.pi with h2 | h2
    · rw [if_pos h2]
      refine pctgtCut₁_notMem_V S hball H.ht₁s₁ H.ha₁ H.hseg₁ H.hout₁ (by positivity) ?_
      rw [div_le_one hpos]
      linarith
    · rw [if_neg (not_le.mpr h2)]
      rcases le_or_gt σ (3 * Real.pi / 2) with h3 | h3
      · rw [if_pos h3]
        by_cases hb : b
        · rw [if_pos hb]; exact pctrace_notMem_V S
        · rw [if_neg hb]; exact pctrace_notMem_V S
      · rw [if_neg (not_le.mpr h3)]
        refine pctgtCut₂_notMem_V S hball H.ht₂s₂ H.ha₂ H.hseg₂ H.hout₂ ?_ ?_
        · have hx : (σ - 3 * Real.pi / 2) / (Real.pi / 2) ≤ 1 := by
            rw [div_le_one (by positivity : (0:ℝ) < Real.pi / 2)]
            linarith [hσmem.2]
          linarith
        · have hx : 0 ≤ (σ - 3 * Real.pi / 2) / (Real.pi / 2) :=
            div_nonneg (by linarith [h3]) (by positivity)
          linarith

end

end Work.SphereJordan
