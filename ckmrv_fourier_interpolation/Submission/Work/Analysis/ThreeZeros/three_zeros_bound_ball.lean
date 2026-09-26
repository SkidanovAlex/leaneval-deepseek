import Mathlib

set_option linter.unusedVariables false

namespace Work.Analysis.ThreeZeros

open Metric Filter
open scoped Topology

/-- `dslope` preserves complex differentiability on the ball.  The point `a` at which the slope
is taken may be anywhere: if it lies inside the ball we use the removable-singularity form of the
statement, otherwise `dslope f a` agrees with the ordinary slope there. -/
lemma differentiableOn_dslope_ball {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ} {a : ℂ} :
    DifferentiableOn ℂ (dslope f a) (Metric.ball c ρ) ↔
      DifferentiableOn ℂ f (Metric.ball c ρ) := by
  by_cases ha : a ∈ Metric.ball c ρ
  · exact Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds ha)
  · exact differentiableOn_dslope_of_notMem ha

/-- `dslope` preserves continuity on the closure of the ball, provided the point `a` is either
strictly inside the ball (then it is a removable singularity) or outside the closure of the ball
(then `dslope f a` agrees with the slope, which is continuous wherever `f` is). -/
lemma continuousOn_dslope_closure_ball {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ} {a : ℂ}
    (hf : DiffContOnCl ℂ f (Metric.ball c ρ))
    (ha : a ∈ Metric.ball c ρ ∨ a ∉ closure (Metric.ball c ρ)) :
    ContinuousOn (dslope f a) (closure (Metric.ball c ρ)) ↔
      ContinuousOn f (closure (Metric.ball c ρ)) := by
  rcases ha with ha | ha
  · have hmem : closure (Metric.ball c ρ) ∈ 𝓝 a :=
      mem_of_superset (Metric.isOpen_ball.mem_nhds ha) subset_closure
    rw [continuousOn_dslope hmem]
    exact and_iff_left (hf.1.differentiableAt (Metric.isOpen_ball.mem_nhds ha))
  · refine ⟨ContinuousOn.of_dslope, fun hc x hx => ?_⟩
    exact (continuousWithinAt_dslope_of_ne (ne_of_mem_of_not_mem hx ha)).mpr (hc x hx)

/-- **Three-zeros (Schwarz-type) estimate, with an abstract boundary constant.**

If `f` is holomorphic on the ball `ball c ρ`, continuous on its closure and bounded by `M` there,
if `f` vanishes at three distinct points `z₁ z₂ z₃`, and if on the sphere `sphere c ρ` the product
of the distances to the three zeros is at least `δ > 0`, then throughout the ball

  `‖f z‖ ≤ (M / δ) ‖z-z₁‖ ‖z-z₂‖ ‖z-z₃‖`.

The three zeros need not lie in the ball.  The proof divides out the three zeros using the divided
slopes `dslope`, which remove the singularities (and are harmless when the zero is outside the
ball), and then applies the maximum modulus principle on `ball c ρ`. -/
theorem three_zeros_bound_ball {f : ℂ → ℂ} {c : ℂ} {ρ M δ : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hδ : 0 < δ) (hf : DiffContOnCl ℂ f (Metric.ball c ρ))
    (hbd : ∀ z ∈ Metric.ball c ρ, ‖f z‖ ≤ M) {z₁ z₂ z₃ : ℂ} (hne₁ : z₁ ≠ z₂)
    (hne₂ : z₁ ≠ z₃) (hne₃ : z₂ ≠ z₃) (hf₁ : f z₁ = 0) (hf₂ : f z₂ = 0) (hf₃ : f z₃ = 0)
    (hbound : ∀ z ∈ Metric.sphere c ρ, δ ≤ ‖z - z₁‖ * ‖z - z₂‖ * ‖z - z₃‖) :
    ∀ z ∈ Metric.ball c ρ, ‖f z‖ ≤ (M / δ) * ‖z - z₁‖ * ‖z - z₂‖ * ‖z - z₃‖ := by
  -- No zero lies on the sphere: there the product of distances would vanish, contradicting `δ > 0`.
  have hsp₁ : z₁ ∉ Metric.sphere c ρ := by
    intro h
    have hb : δ ≤ 0 := by simpa using hbound z₁ h
    linarith
  have hsp₂ : z₂ ∉ Metric.sphere c ρ := by
    intro h
    have hb : δ ≤ 0 := by simpa using hbound z₂ h
    linarith
  have hsp₃ : z₃ ∉ Metric.sphere c ρ := by
    intro h
    have hb : δ ≤ 0 := by simpa using hbound z₃ h
    linarith
  -- So each zero is either strictly inside the ball or outside its closure.
  have hclsub : closure (Metric.ball c ρ) ⊆ Metric.closedBall c ρ :=
    closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
  have hcase₁ : z₁ ∈ Metric.ball c ρ ∨ z₁ ∉ closure (Metric.ball c ρ) := by
    by_cases h : z₁ ∈ Metric.ball c ρ
    · exact Or.inl h
    · refine Or.inr fun hcl => hsp₁ (Metric.mem_sphere.mpr ?_)
      exact le_antisymm (Metric.mem_closedBall.mp (hclsub hcl))
        (not_lt.mp fun hlt => h (Metric.mem_ball.mpr hlt))
  have hcase₂ : z₂ ∈ Metric.ball c ρ ∨ z₂ ∉ closure (Metric.ball c ρ) := by
    by_cases h : z₂ ∈ Metric.ball c ρ
    · exact Or.inl h
    · refine Or.inr fun hcl => hsp₂ (Metric.mem_sphere.mpr ?_)
      exact le_antisymm (Metric.mem_closedBall.mp (hclsub hcl))
        (not_lt.mp fun hlt => h (Metric.mem_ball.mpr hlt))
  have hcase₃ : z₃ ∈ Metric.ball c ρ ∨ z₃ ∉ closure (Metric.ball c ρ) := by
    by_cases h : z₃ ∈ Metric.ball c ρ
    · exact Or.inl h
    · refine Or.inr fun hcl => hsp₃ (Metric.mem_sphere.mpr ?_)
      exact le_antisymm (Metric.mem_closedBall.mp (hclsub hcl))
        (not_lt.mp fun hlt => h (Metric.mem_ball.mpr hlt))
  -- the successive divided slopes, which peel off the three zeros
  set A₁ : ℂ → ℂ := dslope f z₁ with hA₁
  set A₂ : ℂ → ℂ := dslope A₁ z₂ with hA₂
  set A₃ : ℂ → ℂ := dslope A₂ z₃ with hA₃
  have hdiff₁ : DifferentiableOn ℂ A₁ (Metric.ball c ρ) := by
    rw [hA₁]; exact differentiableOn_dslope_ball.mpr hf.1
  have hcont₁ : ContinuousOn A₁ (closure (Metric.ball c ρ)) := by
    rw [hA₁]; exact (continuousOn_dslope_closure_ball hf hcase₁).mpr hf.2
  have hD₁ : DiffContOnCl ℂ A₁ (Metric.ball c ρ) := ⟨hdiff₁, hcont₁⟩
  have hdiff₂ : DifferentiableOn ℂ A₂ (Metric.ball c ρ) := by
    rw [hA₂]; exact differentiableOn_dslope_ball.mpr hdiff₁
  have hcont₂ : ContinuousOn A₂ (closure (Metric.ball c ρ)) := by
    rw [hA₂]; exact (continuousOn_dslope_closure_ball hD₁ hcase₂).mpr hcont₁
  have hD₂ : DiffContOnCl ℂ A₂ (Metric.ball c ρ) := ⟨hdiff₂, hcont₂⟩
  have hdiff₃ : DifferentiableOn ℂ A₃ (Metric.ball c ρ) := by
    rw [hA₃]; exact differentiableOn_dslope_ball.mpr hdiff₂
  have hcont₃ : ContinuousOn A₃ (closure (Metric.ball c ρ)) := by
    rw [hA₃]; exact (continuousOn_dslope_closure_ball hD₂ hcase₃).mpr hcont₂
  have hD₃ : DiffContOnCl ℂ A₃ (Metric.ball c ρ) := ⟨hdiff₃, hcont₃⟩
  -- peeling identities
  have hfac₁ : ∀ z : ℂ, (z - z₁) * A₁ z = f z := by
    intro z
    have h := sub_smul_dslope_of_zero hf₁ z
    rw [← hA₁] at h
    simpa [smul_eq_mul] using h
  have hA₁z₂ : A₁ z₂ = 0 := by
    have h := hfac₁ z₂
    rw [hf₂] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne₁.symm)
  have hfac₂ : ∀ z : ℂ, (z - z₂) * A₂ z = A₁ z := by
    intro z
    have h := sub_smul_dslope_of_zero hA₁z₂ z
    rw [← hA₂] at h
    simpa [smul_eq_mul] using h
  have hA₁z₃ : A₁ z₃ = 0 := by
    have h := hfac₁ z₃
    rw [hf₃] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne₂.symm)
  have hA₂z₃ : A₂ z₃ = 0 := by
    have h := hfac₂ z₃
    rw [hA₁z₃] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne₃.symm)
  have hfac₃ : ∀ z : ℂ, (z - z₃) * A₃ z = A₂ z := by
    intro z
    have h := sub_smul_dslope_of_zero hA₂z₃ z
    rw [← hA₃] at h
    simpa [smul_eq_mul] using h
  -- the product of the three peeled linear factors times `A₃` reproduces `f`
  have hmain : ∀ z : ℂ, (z - z₁) * (z - z₂) * (z - z₃) * A₃ z = f z := by
    intro z
    calc (z - z₁) * (z - z₂) * (z - z₃) * A₃ z
        = (z - z₁) * (z - z₂) * ((z - z₃) * A₃ z) := by ring
      _ = (z - z₁) * (z - z₂) * A₂ z := by rw [hfac₃ z]
      _ = (z - z₁) * ((z - z₂) * A₂ z) := by ring
      _ = (z - z₁) * A₁ z := by rw [hfac₂ z]
      _ = f z := hfac₁ z
  -- `f` is bounded by `M` on the closure of the ball
  have hclosed : IsClosed
      (closure (Metric.ball c ρ) ∩ (fun z : ℂ => ‖f z‖) ⁻¹' Set.Iic M) :=
    ContinuousOn.preimage_isClosed_of_isClosed hf.2.norm isClosed_closure isClosed_Iic
  have hsubset : Metric.ball c ρ ⊆
      closure (Metric.ball c ρ) ∩ (fun z : ℂ => ‖f z‖) ⁻¹' Set.Iic M :=
    fun z hz => ⟨subset_closure hz, hbd z hz⟩
  have hclsub₂ : closure (Metric.ball c ρ) ⊆
      closure (Metric.ball c ρ) ∩ (fun z : ℂ => ‖f z‖) ⁻¹' Set.Iic M :=
    closure_minimal hsubset hclosed
  have hfM : ∀ z ∈ closure (Metric.ball c ρ), ‖f z‖ ≤ M := fun z hz => (hclsub₂ hz).2
  -- bound on the frontier of the big ball
  have hbdy : ∀ z ∈ frontier (Metric.ball c ρ), ‖A₃ z‖ ≤ M / δ := by
    intro z hz
    have hzsphere : z ∈ Metric.sphere c ρ := Metric.frontier_ball_subset_sphere hz
    have hprodge : δ ≤ ‖(z - z₁) * (z - z₂) * (z - z₃)‖ := by
      rw [norm_mul, norm_mul]
      exact hbound z hzsphere
    have hprodne : (z - z₁) * (z - z₂) * (z - z₃) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hprodge
      linarith
    have hA₃eq : A₃ z = f z / ((z - z₁) * (z - z₂) * (z - z₃)) := by
      rw [eq_div_iff hprodne, mul_comm]
      exact hmain z
    rw [hA₃eq, norm_div]
    exact div_le_div₀ hM (hfM z (frontier_subset_closure hz)) hδ hprodge
  -- maximum modulus on the big ball
  intro z hz
  have hA₃le : ‖A₃ z‖ ≤ M / δ :=
    Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hD₃ hbdy
      (subset_closure hz)
  calc ‖f z‖ = ‖z - z₁‖ * ‖z - z₂‖ * ‖z - z₃‖ * ‖A₃ z‖ := by
        rw [← hmain z]; simp only [norm_mul]
    _ ≤ ‖z - z₁‖ * ‖z - z₂‖ * ‖z - z₃‖ * (M / δ) :=
        mul_le_mul_of_nonneg_left hA₃le (by positivity)
    _ = (M / δ) * ‖z - z₁‖ * ‖z - z₂‖ * ‖z - z₃‖ := by ring

end Work.Analysis.ThreeZeros
