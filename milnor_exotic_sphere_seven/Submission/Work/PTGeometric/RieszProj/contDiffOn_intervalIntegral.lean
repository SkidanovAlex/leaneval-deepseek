import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric.RieszProj

open scoped ContDiff
open Set
open MeasureTheory Filter
open scoped Topology
universe u

/-- Differentiation under the integral sign for a parametric *interval* integral, with the
integrand simply assumed `C^∞` on `s ×ˢ J` where `J` is an open set containing `[a,b]`.
This is the analogue of `hasFDerivAt_convolution_right_with_param`. -/
private theorem hasFDerivAt_intervalIntegral_aux {E H : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {G : H → ℝ → E} {s : Set H} {J : Set ℝ} {a b : ℝ}
    (hab : a ≤ b) (hs : IsOpen s) (hJ : IsOpen J) (hsub : Set.Icc a b ⊆ J)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (s ×ˢ J)) {x₀ : H} (hx₀ : x₀ ∈ s) :
    HasFDerivAt (fun x : H => ∫ t in a..b, G x t)
      (∫ t in a..b, (fderiv ℝ (Function.uncurry G) (x₀, t)).comp
        (ContinuousLinearMap.inl ℝ H ℝ)) x₀ := by
  have hGd : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry G)) (s ×ˢ J) :=
    hG.fderiv_of_isOpen (hs.prod hJ) le_rfl
  have hSmooth : ContDiffOn ℝ ∞
      (fun p : H × ℝ => (fderiv ℝ (Function.uncurry G) p).comp
        (ContinuousLinearMap.inl ℝ H ℝ)) (s ×ˢ J) :=
    hGd.clm_comp (contDiffOn_const (c := ContinuousLinearMap.inl ℝ H ℝ))
  have hslice : ∀ x ∈ s, ContinuousOn (fun t : ℝ => G x t) (uIcc a b) := by
    intro x hx
    refine hG.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) ?_
    intro t ht
    exact ⟨hx, hsub (by rwa [uIcc_of_le hab] at ht)⟩
  have hslice' : ContinuousOn
      (fun t : ℝ => (fderiv ℝ (Function.uncurry G) (x₀, t)).comp
        (ContinuousLinearMap.inl ℝ H ℝ)) (uIcc a b) := by
    refine hSmooth.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) ?_
    intro t ht
    exact ⟨hx₀, hsub (by rwa [uIcc_of_le hab] at ht)⟩
  -- a uniform bound for the derivative of the integrand, near `x₀` and over `[a,b]`
  have hK : IsCompact ({x₀} ×ˢ Set.Icc a b) := isCompact_singleton.prod isCompact_Icc
  have hKsub : ({x₀} ×ˢ Set.Icc a b) ⊆ s ×ˢ J := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    obtain rfl : p = x₀ := by simpa using hp
    exact ⟨hx₀, hsub ht⟩
  obtain ⟨topen, hKt, htopen, htbdd⟩ :=
    Metric.exists_isOpen_isBounded_image_of_isCompact_of_continuousOn hK (hs.prod hJ)
      hKsub hGd.continuousOn
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hK.exists_thickening_subset_open htopen hKt
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.isOpen_iff.1 hs x₀ hx₀
  obtain ⟨C, hCpos, hC⟩ := htbdd.subset_closedBall_lt 0 (0 : (H × ℝ) →L[ℝ] E)
  have h1 : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (G x)
      ((MeasureTheory.volume).restrict (uIoc a b)) := by
    filter_upwards [Metric.ball_mem_nhds x₀ (lt_min hδ₁pos hδ₂pos)] with x hx
    exact ((hslice x (hδ₂ (Metric.ball_subset_ball (min_le_right _ _) hx))).mono
      uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have h2 : IntervalIntegrable (fun t : ℝ => G x₀ t) MeasureTheory.volume a b :=
    (hslice x₀ hx₀).intervalIntegrable
  have h3 : AEStronglyMeasurable
      (fun t : ℝ => (fderiv ℝ (Function.uncurry G) (x₀, t)).comp
        (ContinuousLinearMap.inl ℝ H ℝ)) ((MeasureTheory.volume).restrict (uIoc a b)) :=
    (hslice'.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have h4 : ∀ᵐ t ∂MeasureTheory.volume, t ∈ uIoc a b →
      ∀ x ∈ Metric.ball x₀ (min δ₁ δ₂),
        ‖(fderiv ℝ (Function.uncurry G) (x, t)).comp
          (ContinuousLinearMap.inl ℝ H ℝ)‖ ≤ (fun _ => C) t := by
    filter_upwards with t ht x hx
    have ht' : t ∈ Set.Icc a b := by
      rw [← uIcc_of_le hab]
      exact uIoc_subset_uIcc ht
    have hxδ : dist x x₀ < δ₁ :=
      lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_left _ _)
    have hmem : (x, t) ∈ topen := by
      apply hδ₁
      rw [Metric.mem_thickening_iff]
      refine ⟨(x₀, t), ⟨rfl, ht'⟩, ?_⟩
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact hxδ
    have hnorm : ‖fderiv ℝ (Function.uncurry G) (x, t)‖ ≤ C := by
      have h := hC (mem_image_of_mem _ hmem)
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    calc ‖(fderiv ℝ (Function.uncurry G) (x, t)).comp
            (ContinuousLinearMap.inl ℝ H ℝ)‖
        ≤ ‖fderiv ℝ (Function.uncurry G) (x, t)‖ * ‖ContinuousLinearMap.inl ℝ H ℝ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := mul_le_mul hnorm (ContinuousLinearMap.norm_inl_le_one ℝ H ℝ)
          (norm_nonneg _) hCpos.le
      _ = C := mul_one C
  have h5 : IntervalIntegrable (fun _ : ℝ => C) MeasureTheory.volume a b :=
    intervalIntegrable_const
  have h6 : ∀ᵐ t ∂MeasureTheory.volume, t ∈ uIoc a b →
      ∀ x ∈ Metric.ball x₀ (min δ₁ δ₂),
        HasFDerivAt (fun y : H => G y t)
          ((fderiv ℝ (Function.uncurry G) (x, t)).comp
            (ContinuousLinearMap.inl ℝ H ℝ)) x := by
    filter_upwards with t ht x hx
    have ht' : t ∈ Set.Icc a b := by
      rw [← uIcc_of_le hab]
      exact uIoc_subset_uIcc ht
    have hxs : x ∈ s := hδ₂ (Metric.ball_subset_ball (min_le_right _ _) hx)
    have hmem : (x, t) ∈ s ×ˢ J := ⟨hxs, hsub ht'⟩
    have hdiff : DifferentiableAt ℝ (Function.uncurry G) (x, t) :=
      (hG.differentiableOn (by simp)).differentiableAt ((hs.prod hJ).mem_nhds hmem)
    have hproj : HasFDerivAt (fun y : H => (y, t)) (ContinuousLinearMap.inl ℝ H ℝ) x := by
      simpa using
        ((ContinuousLinearMap.inl ℝ H ℝ).hasFDerivAt (x := x)).add_const ((0 : H), t)
    exact hdiff.hasFDerivAt.comp x hproj
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (μ := MeasureTheory.volume) (F := G)
    (F' := fun x t => (fderiv ℝ (Function.uncurry G) (x, t)).comp
      (ContinuousLinearMap.inl ℝ H ℝ))
    (x₀ := x₀) (s := Metric.ball x₀ (min δ₁ δ₂)) (bound := fun _ => C)
    (Metric.ball_mem_nhds x₀ (lt_min hδ₁pos hδ₂pos)) h1 h2 h3 h4 h5 h6

/-- The `n`-th order version of the smoothness of a parametric interval integral. -/
private theorem contDiffOn_intervalIntegral_aux (n : ℕ∞) :
    ∀ {E H : Type u}
      [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
      {G : H → ℝ → E} {s : Set H} {J : Set ℝ} {a b : ℝ},
      a ≤ b → IsOpen s → IsOpen J → Set.Icc a b ⊆ J →
      ContDiffOn ℝ ∞ (Function.uncurry G) (s ×ˢ J) →
      ContDiffOn ℝ ((n : ℕ∞) : ℕ∞ω) (fun x : H => ∫ t in a..b, G x t) s := by
  induction n using ENat.nat_induction with
  | zero =>
    intro E H _ _ _ _ _ _ G s J a b hab hs hJ hsub hG
    rw [show ((0 : ℕ∞) : ℕ∞ω) = 0 from rfl, contDiffOn_zero]
    exact DifferentiableOn.continuousOn fun x hx =>
      (hasFDerivAt_intervalIntegral_aux hab hs hJ hsub hG hx).differentiableAt.differentiableWithinAt
  | succ n ih =>
    intro E H _ _ _ _ _ _ G s J a b hab hs hJ hsub hG
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, WithTop.coe_add,
      WithTop.coe_natCast, WithTop.coe_one] at ⊢
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun x hx =>
      (hasFDerivAt_intervalIntegral_aux hab hs hJ hsub hG hx).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    let G' : H → ℝ → (H →L[ℝ] E) := fun x t =>
      (fderiv ℝ (Function.uncurry G) (x, t)).comp (ContinuousLinearMap.inl ℝ H ℝ)
    have hG'smooth : ContDiffOn ℝ ∞ (Function.uncurry G') (s ×ˢ J) := by
      have hGd : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry G)) (s ×ˢ J) :=
        hG.fderiv_of_isOpen (hs.prod hJ) le_rfl
      have h := hGd.clm_comp (contDiffOn_const (c := ContinuousLinearMap.inl ℝ H ℝ))
      refine h.congr fun p _ => ?_
      simp only [Function.uncurry]
      rfl
    have ih' := ih (E := H →L[ℝ] E) (H := H) (G := G') hab hs hJ hsub hG'smooth
    refine ih'.congr fun x hx => ?_
    exact (hasFDerivAt_intervalIntegral_aux hab hs hJ hsub hG hx).fderiv
  | top ih =>
    intro E H _ _ _ _ _ _ G s J a b hab hs hJ hsub hG
    rw [contDiffOn_infty]
    intro n
    exact ih n (E := E) (H := H) (G := G) hab hs hJ hsub hG

/-- Smoothness of a parametric interval integral: if `G : H → ℝ → E` is jointly `C^∞` on the
product of an open set `s ⊆ H` and an open set `J ⊆ ℝ` containing `[a,b]`, then
`x ↦ ∫ t in a..b, G x t` is `C^∞` on `s`.

Proof route (mirrors the already formalised `contDiffOn_convolution_right_with_param_aux` in
`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`): prove the `n`-th order statement for
`n : ℕ∞` by `ENat.nat_induction` (this is why `E` and `H` are required to live in the same
universe: at each step the target space becomes `H →L[ℝ] E`, which must stay in that universe),
using `contDiffOn_succ_iff_fderiv_of_isOpen` on the open domain `s ×ˢ J` and
`intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip_interval` (or
`hasFDerivAt_integral_of_dominated_of_fderiv_le`) to differentiate under the integral sign.  The
uniform Lipschitz/dominating bound over `t ∈ Icc a b` comes from the continuity of
`fderiv ℝ (Function.uncurry G)` on the open set `s ×ˢ J` together with
`exists_isOpen_isBounded_image_of_isCompact_of_continuousOn` applied to the compact set
`{x} ×ˢ Icc a b`, as in the convolution reference. -/
theorem contDiffOn_intervalIntegral {E H : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {G : H → ℝ → E} {s : Set H} {J : Set ℝ} {a b : ℝ}
    (hab : a ≤ b) (hs : IsOpen s) (hJ : IsOpen J) (hsub : Set.Icc a b ⊆ J)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (s ×ˢ J)) :
    ContDiffOn ℝ ∞ (fun x : H => ∫ t in a..b, G x t) s := by
  have h := contDiffOn_intervalIntegral_aux (n := ⊤) (E := E) (H := H) (G := G)
    (s := s) (J := J) (a := a) (b := b) hab hs hJ hsub hG
  simpa using h

end Work.PTGeometric.RieszProj
