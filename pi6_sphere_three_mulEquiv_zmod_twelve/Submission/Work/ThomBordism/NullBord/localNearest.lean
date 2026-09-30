import Mathlib

set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

/-!
# Local uniqueness of the nearest point of a smoothly embedded manifold

`Work.ThomBordism.NullBord.localNearestUnique` is the analytic core of the proof that the image of
a compact `C^∞` manifold `X` (with corners, model `ℝ^9₊`) under a smooth immersion `e : X → ℝ^N`
which is a closed embedding is a Euclidean neighbourhood retract: a point of the image that is
*nearest* to a nearby point `y` of `ℝ^N` is locally the *unique* nearest point of `y`.
-/

open scoped Manifold ContDiff Topology
open Set Metric Filter

namespace Work.ThomBordism.NullBord

noncomputable section

/-! ## The algebraic core -/

/-- **Second-order data force the uniqueness of the nearest point.**

If `u` is a nearest point of `y` in the convex set `s`, the derivative `D` at `u` of the immersion
`f` is uniformly expanding (`hexp`), the second-order Taylor estimate `htar` holds, and the
first-order (Fermat) condition `hferm` holds at `u`, then no *other* point `u'` of `s` can be at
distance `≤` the distance of `u`, provided the total error `2C(‖y-fu‖ + ‖D(u'-u)‖)` is smaller than
`c²`. -/
theorem nearestUniqueOfEstimates {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {u u' : E} {D : E →L[ℝ] F} {y : F} {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hexp : ∀ v : E, c * ‖v‖ ≤ ‖D v‖)
    (htar : ‖f u' - f u - D (u' - u)‖ ≤ C * ‖u' - u‖ ^ 2)
    (hferm : 0 ≤ -2 * inner ℝ (y - f u) (D (u' - u)))
    (hu'min : ‖y - f u'‖ ≤ ‖y - f u‖)
    (hsmall : 2 * C * ‖y - f u‖ + 2 * C * ‖D (u' - u)‖ < c ^ 2) :
    u' = u := by
  by_contra hne
  set Δ : E := u' - u with hΔ
  set w : F := y - f u with hw
  set P : F := D Δ with hP
  set R : F := f u' - f u - D Δ with hR
  have hneΔ : Δ ≠ 0 := by rw [hΔ, sub_ne_zero]; exact hne
  have hΔpos : 0 < ‖Δ‖ := norm_pos_iff.mpr hneΔ
  have hPnorm : c * ‖Δ‖ ≤ ‖P‖ := by rw [hP]; exact hexp Δ
  have hRnorm : ‖R‖ ≤ C * ‖Δ‖ ^ 2 := by rw [hR, hΔ]; exact htar
  have hwnorm : ‖w‖ = ‖y - f u‖ := rfl
  have hone : 0 ≤ -2 * inner ℝ w P := by rw [hw, hP]; exact hferm
  -- the identity `y - f u' = w - (P + R)`
  have hfu' : y - f u' = w - (P + R) := by rw [hw, hP, hR]; abel
  -- auxiliary estimates
  have hinner : inner ℝ w (P + R) ≤ ‖w‖ * ‖R‖ := by
    rw [inner_add_right]
    have h1 : inner ℝ w P ≤ 0 := by linarith [hone]
    have h2 : inner ℝ w R ≤ ‖w‖ * ‖R‖ := real_inner_le_norm w R
    linarith
  have hsq : ‖P + R‖ ^ 2 ≥ ‖P‖ ^ 2 - 2 * ‖P‖ * ‖R‖ := by
    have h3 := norm_add_sq_real P R
    have h4 : -(‖P‖ * ‖R‖) ≤ inner ℝ P R := by
      have h5 := abs_real_inner_le_norm P R
      rw [abs_le] at h5
      linarith [h5.1]
    nlinarith [h3, h4, sq_nonneg ‖R‖]
  -- the difference of the squared distances
  have hdiff : ‖y - f u'‖ ^ 2 - ‖y - f u‖ ^ 2
      = -2 * inner ℝ w (P + R) + ‖P + R‖ ^ 2 := by
    rw [hfu', norm_sub_sq_real, hw]
    ring
  -- the lower bound
  have hkey : c ^ 2 * ‖Δ‖ ^ 2 - 2 * C * ‖P‖ * ‖Δ‖ ^ 2 - 2 * C * ‖w‖ * ‖Δ‖ ^ 2
      ≤ ‖y - f u'‖ ^ 2 - ‖y - f u‖ ^ 2 := by
    rw [hdiff]
    have h6 : (c * ‖Δ‖) ^ 2 ≤ ‖P‖ ^ 2 := by
      have h6a : 0 ≤ c * ‖Δ‖ := mul_nonneg (le_of_lt hc) (norm_nonneg _)
      nlinarith [hPnorm, h6a, norm_nonneg P]
    have h7 : 0 ≤ ‖P‖ := norm_nonneg _
    have h8 : 0 ≤ C := le_of_lt hC
    have h9 : 0 ≤ ‖Δ‖ ^ 2 := sq_nonneg _
    have h10 : 0 ≤ ‖w‖ := norm_nonneg _
    have h11 : ‖R‖ * (‖P‖ + ‖w‖) ≤ (C * ‖Δ‖ ^ 2) * (‖P‖ + ‖w‖) :=
      mul_le_mul_of_nonneg_right hRnorm (by linarith)
    nlinarith [hinner, hsq, h6, hRnorm, h11, h7, h8, h9, h10]
  -- strict positivity
  have hstrict : 0 < ‖y - f u'‖ ^ 2 - ‖y - f u‖ ^ 2 := by
    have h11 : 0 < ‖Δ‖ ^ 2 := sq_pos_of_pos hΔpos
    have h12 : 2 * C * ‖P‖ + 2 * C * ‖w‖ < c ^ 2 := by nlinarith [hsmall, mul_comm (2 * C) ‖w‖]
    nlinarith [hkey, h11, h12]
  -- contradicting the minimality of `u'`
  have hmono : ‖y - f u'‖ ^ 2 ≤ ‖y - f u‖ ^ 2 := by
    nlinarith [hu'min, norm_nonneg (y - f u'), norm_nonneg (y - f u)]
  linarith [hstrict, hmono]

/-! ## The Fermat (first-order) condition at a nearest point -/

/-- **The Fermat condition at a nearest point.**  If `u` minimises `w ↦ ‖y - f w‖` on the convex
set `s`, and `f` has derivative `D` at `u` within `s`, then the direction to any other point `u'`
of `s` makes a non-positive scalar product with `y - f u`. -/
theorem fermatCondition {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {s : Set E} (hs : Convex ℝ s) {u u' : E} (hu : u ∈ s) (hu' : u' ∈ s)
    {y : F} {D : E →L[ℝ] F} (hD : HasFDerivWithinAt f D s u)
    (hmin : ∀ w ∈ s, ‖y - f u‖ ≤ ‖y - f w‖) :
    0 ≤ -2 * inner ℝ (y - f u) (D (u' - u)) := by
  have hloc : IsLocalMinOn (fun w => ‖y - f w‖ ^ 2) s u := by
    rw [IsLocalMinOn, IsMinFilter]
    filter_upwards [self_mem_nhdsWithin] with w hw
    have h1 : (0:ℝ) ≤ ‖y - f u‖ := norm_nonneg _
    have h2 := hmin w hw
    nlinarith [h1, h2, norm_nonneg (y - f w)]
  have hderiv : HasFDerivWithinAt (fun w => ‖y - f w‖ ^ 2)
      (2 • ((innerSL ℝ (y - f u)) ∘SL (-D))) s u :=
    (hD.const_sub y).norm_sq
  have htan : u' - u ∈ posTangentConeAt s u := by
    have hseg : segment ℝ u u' ⊆ s := hs.segment_subset hu hu'
    exact sub_mem_posTangentConeAt_of_openSegment_subset
      ((openSegment_subset_segment ℝ u u').trans hseg)
  have h := hloc.hasFDerivWithinAt_nonneg hderiv htan
  have h' : (2 • ((innerSL ℝ (y - f u)) ∘SL (-D))) (u' - u)
      = -2 * inner ℝ (y - f u) (D (u' - u)) := by
    simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, neg_apply,
      inner_neg_right]
    ring
  rwa [h'] at h


/-! ## The analytic estimates on a compact convex set -/

/-- **A uniformly expanding linear map is bounded below.**  For a continuous linear map with trivial
kernel between finite-dimensional spaces there is `c > 0` with `c ‖v‖ ≤ ‖D v‖` for all `v`. -/
theorem exists_pos_le_norm_of_injective {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : E →L[ℝ] F} (hD : Function.Injective D) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : E, c * ‖v‖ ≤ ‖D v‖ := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  by_cases htriv : Subsingleton E
  · refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := Subsingleton.elim v 0
    rw [hv, norm_zero, mul_zero]
    exact norm_nonneg _
  · haveI : Nontrivial E := not_subsingleton_iff_nontrivial.mp htriv
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : E)
    have hv₀pos : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀
    have hne : (Metric.sphere (0 : E) 1).Nonempty :=
      ⟨(‖v₀‖⁻¹) • v₀, by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_pos hv₀pos, inv_mul_cancel₀ (ne_of_gt hv₀pos)]⟩
    obtain ⟨v₁, hv₁, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne
      (continuous_norm.comp_continuousOn D.continuous.continuousOn)
    have hv₁ne : v₁ ≠ 0 := by
      intro h
      rw [h] at hv₁
      simpa [Metric.mem_sphere, dist_eq_norm] using hv₁
    have hpos : 0 < ‖D v₁‖ := by
      rw [norm_pos_iff]; intro h
      exact hv₁ne (hD (by simpa using h))
    refine ⟨‖D v₁‖, hpos, fun v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hmem : (‖v‖⁻¹ • v) ∈ Metric.sphere (0 : E) 1 := by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_pos hvnorm, inv_mul_cancel₀ (ne_of_gt hvnorm)]
      have h1 : ‖D v₁‖ ≤ ‖D ((‖v‖⁻¹) • v)‖ := hmin hmem
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvnorm)] at h1
      rw [inv_mul_eq_div, le_div_iff₀ hvnorm] at h1
      linarith [h1]

/-- **Expansion and second-order Taylor estimates on a compact convex set.**

For a `C²` map `g` on a compact convex set `s` with nonempty interior whose derivative at `u₀` has
trivial kernel, the derivative is uniformly expanding on a ball around `u₀` and the second-order
Taylor estimate holds on all of `s`. -/
theorem exists_expansion_taylor_compact {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {s : Set E} (hs : Convex ℝ s) (hsc : IsCompact s) (hint : (interior s).Nonempty)
    {u₀ : E} (hu₀ : u₀ ∈ s) (hC2 : ContDiffOn ℝ 2 g s)
    (hinj : ∀ v : E, fderivWithin ℝ g s u₀ v = 0 → v = 0) :
    ∃ ρ c C : ℝ, 0 < ρ ∧ 0 < c ∧ 0 < C ∧
      (∀ u ∈ s, ‖u - u₀‖ < ρ → ∀ v : E, c * ‖v‖ ≤ ‖fderivWithin ℝ g s u v‖) ∧
      ∀ u ∈ s, ∀ u' ∈ s, ‖g u' - g u - fderivWithin ℝ g s u (u' - u)‖ ≤ C * ‖u' - u‖ ^ 2 := by
  have huniq : UniqueDiffOn ℝ s := uniqueDiffOn_convex hs hint
  have hcontD : ContinuousOn (fun u => fderivWithin ℝ g s u) s :=
    hC2.continuousOn_fderivWithin huniq (by norm_num)
  -- ## 1. the expansion at `u₀`
  have hD0inj : Function.Injective (fderivWithin ℝ g s u₀) := by
    intro v v' h
    have h' : v - v' = 0 := hinj (v - v') (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp h'
  obtain ⟨c₀, hc₀pos, hc₀⟩ :=
    exists_pos_le_norm_of_injective (D := fderivWithin ℝ g s u₀) hD0inj
  -- ## 2. the uniform expansion on a ball
  have hcont0 : ContinuousWithinAt (fun u => fderivWithin ℝ g s u) s u₀ := hcontD.continuousWithinAt hu₀
  rw [Metric.continuousWithinAt_iff] at hcont0
  obtain ⟨ρ, hρpos, hρ⟩ := hcont0 (c₀ / 2) (by linarith)
  have hexp : ∀ u ∈ s, ‖u - u₀‖ < ρ → ∀ v : E, (c₀ / 2) * ‖v‖ ≤ ‖fderivWithin ℝ g s u v‖ := by
    intro u hu huρ v
    have huρ' : dist u u₀ < ρ := by simpa [dist_eq_norm] using huρ
    have h1 : ‖fderivWithin ℝ g s u - fderivWithin ℝ g s u₀‖ < c₀ / 2 := by
      have := hρ hu huρ'
      simpa [dist_eq_norm] using this
    have h2 : fderivWithin ℝ g s u₀ v = fderivWithin ℝ g s u v + (fderivWithin ℝ g s u₀ - fderivWithin ℝ g s u) v := by
      rw [sub_apply]; abel
    have h3 : ‖fderivWithin ℝ g s u₀ v‖ ≤ ‖fderivWithin ℝ g s u v‖ + ‖fderivWithin ℝ g s u₀ - fderivWithin ℝ g s u‖ * ‖v‖ := by
      rw [h2]
      calc ‖fderivWithin ℝ g s u v + (fderivWithin ℝ g s u₀ - fderivWithin ℝ g s u) v‖
          ≤ ‖fderivWithin ℝ g s u v‖ + ‖(fderivWithin ℝ g s u₀ - fderivWithin ℝ g s u) v‖ := norm_add_le _ _
        _ ≤ ‖fderivWithin ℝ g s u v‖ + ‖fderivWithin ℝ g s u₀ - fderivWithin ℝ g s u‖ * ‖v‖ := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
    have h4 : ‖fderivWithin ℝ g s u₀ - fderivWithin ℝ g s u‖ = ‖fderivWithin ℝ g s u - fderivWithin ℝ g s u₀‖ := by
      rw [← norm_neg, neg_sub]
    nlinarith [hc₀ v, h3, h1, h4, norm_nonneg v, norm_nonneg (fderivWithin ℝ g s u v)]
  -- ## 3. a uniform bound on the second derivative on the compact `s`
  have hC1 : ContDiffOn ℝ 1 (fun u => fderivWithin ℝ g s u) s :=
    hC2.fderivWithin huniq (by norm_num)
  have hcontD2 : ContinuousOn (fun u => fderivWithin ℝ (fun u => fderivWithin ℝ g s u) s u) s :=
    hC1.continuousOn_fderivWithin huniq (by norm_num)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ u ∈ s,
      ‖fderivWithin ℝ (fun u => fderivWithin ℝ g s u) s u‖ ≤ C := by
    have hnormcont : ContinuousOn
        (fun u => ‖fderivWithin ℝ (fun u => fderivWithin ℝ g s u) s u‖) s := by
      have h := continuous_norm.comp_continuousOn
        (f := fun u => fderivWithin ℝ (fun u => fderivWithin ℝ g s u) s u) hcontD2
      simpa only [Function.comp_def] using h
    have := hsc.bddAbove_image hnormcont
    rw [bddAbove_def] at this
    obtain ⟨C, hC⟩ := this
    exact ⟨C, fun u hu => hC _ (mem_image_of_mem _ hu)⟩
  have hCpos : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨ρ, c₀ / 2, max C 1, hρpos, by linarith, hCpos, hexp, ?_⟩
  -- ## 4. the Lipschitz bound on `u ↦ fderivWithin ℝ g s u`
  have hLip : ∀ u ∈ s, ∀ v ∈ s,
      ‖fderivWithin ℝ g s u - fderivWithin ℝ g s v‖ ≤ max C 1 * ‖u - v‖ := by
    intro u hu v hv
    have hdiff : DifferentiableOn ℝ (fun u => fderivWithin ℝ g s u) s :=
      hC1.differentiableOn (by norm_num)
    have := Convex.norm_image_sub_le_of_norm_fderivWithin_le (𝕜 := ℝ)
      (f := fun u => fderivWithin ℝ g s u) (C := max C 1) (x := v) (y := u)
      hdiff (fun w hw => le_trans (hC w hw) (le_max_left _ _)) hs hv hu
    simpa using this
  -- ## 5. the second-order estimate along the segment
  intro u hu u' hu'
  set Δ : E := u' - u with hΔ
  set γ : ℝ → E := fun t => u + t • Δ with hγ
  have hγmem : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ s := by
    intro t ht
    have h1 : γ t = (1 - t) • u + t • u' := by
      simp only [hγ, hΔ]; module
    rw [h1]
    exact hs hu hu' (sub_nonneg.mpr ht.2) ht.1 (by linarith)
  have hchain : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt γ Δ (Set.Icc (0:ℝ) 1) t := by
    intro t ht
    simpa [hγ, hΔ] using
      ((hasDerivWithinAt_id t (Set.Icc (0:ℝ) 1)).smul_const Δ).const_add u
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt (fun t => g (γ t) - t • (fderivWithin ℝ g s u Δ))
        (fderivWithin ℝ g s (γ t) Δ - fderivWithin ℝ g s u Δ) (Set.Icc (0:ℝ) 1) t := by
    intro t ht
    have hG : HasFDerivWithinAt g (fderivWithin ℝ g s (γ t)) s (γ t) :=
      ((hC2 (γ t) (hγmem t ht)).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have h2 := hG.comp_hasDerivWithinAt t (hchain t ht) (fun y hy => hγmem y hy)
    have h3 : HasDerivWithinAt (fun t : ℝ => t • (fderivWithin ℝ g s u Δ))
        (fderivWithin ℝ g s u Δ) (Set.Icc (0:ℝ) 1) t := by
      simpa using (hasDerivWithinAt_id t (Set.Icc (0:ℝ) 1)).smul_const (fderivWithin ℝ g s u Δ)
    have h4 := h2.sub h3
    convert h4 using 1
    ext t
    simp only [Pi.sub_apply, Function.comp_apply]
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) 1,
      ‖fderivWithin ℝ g s (γ t) Δ - fderivWithin ℝ g s u Δ‖ ≤ max C 1 * ‖Δ‖ ^ 2 := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
    have hmem := hγmem t ht'
    have h1 : ‖fderivWithin ℝ g s (γ t) Δ - fderivWithin ℝ g s u Δ‖
        ≤ max C 1 * ‖γ t - u‖ * ‖Δ‖ := by
      rw [← sub_apply]
      calc ‖(fderivWithin ℝ g s (γ t) - fderivWithin ℝ g s u) Δ‖
          ≤ ‖fderivWithin ℝ g s (γ t) - fderivWithin ℝ g s u‖ * ‖Δ‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (max C 1 * ‖γ t - u‖) * ‖Δ‖ :=
            mul_le_mul_of_nonneg_right (hLip (γ t) hmem u hu) (norm_nonneg Δ)
    have h2 : ‖γ t - u‖ = t * ‖Δ‖ := by
      simp only [hγ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have h3 : max C 1 * ‖γ t - u‖ * ‖Δ‖ = max C 1 * t * ‖Δ‖ ^ 2 := by
      rw [h2]; ring
    have h4 : max C 1 * t * ‖Δ‖ ^ 2 ≤ max C 1 * ‖Δ‖ ^ 2 := by
      have h5 : 0 ≤ max C 1 * ‖Δ‖ ^ 2 := by positivity
      nlinarith [ht.2, h5]
    linarith [h1, h3, h4]
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0:ℝ)) (b := 1) hderiv hbound 1 (right_mem_Icc.mpr zero_le_one)
  have h0 : γ 0 = u := by simp [hγ]
  have h1' : γ 1 = u' := by simp [hγ, hΔ]
  have hL : (fun t => g (γ t) - t • (fderivWithin ℝ g s u Δ)) 1
      - (fun t => g (γ t) - t • (fderivWithin ℝ g s u Δ)) 0
      = g u' - g u - fderivWithin ℝ g s u (u' - u) := by
    simp only [h0, h1', one_smul, zero_smul, sub_zero, hΔ]
    abel
  rw [hL] at hmain
  have hD : fderivWithin ℝ g s u Δ
      = fderivWithin ℝ g s u u' - fderivWithin ℝ g s u u := by rw [hΔ, map_sub]
  rw [hD]
  simpa using hmain


/-! ## The chart representative of the immersion -/

section Chart

variable {X : Type} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 9) X]
  [IsManifold (modelWithCornersEuclideanHalfSpace 9) ∞ X]

/-- The chart representative of a `C^∞` map into a Euclidean space is `C²` within the half-space, at
every point of the (extended) chart target. -/
theorem chartRep_contDiffWithinAt {N : ℕ} {e : X → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (modelWithCornersEuclideanHalfSpace 9) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ∞ e) (x₀ : X)
    {u : EuclideanSpace ℝ (Fin 9)} (hu : u ∈ (extChartAt (modelWithCornersEuclideanHalfSpace 9) x₀).target) :
    ContDiffWithinAt ℝ 2 (fun v => e ((extChartAt (modelWithCornersEuclideanHalfSpace 9) x₀).symm v))
      (Set.range (modelWithCornersEuclideanHalfSpace 9)) u := by
  have h1 : ContMDiffWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 9)) (modelWithCornersEuclideanHalfSpace 9) ∞
      (↑(extChartAt (modelWithCornersEuclideanHalfSpace 9) x₀).symm) (Set.range (modelWithCornersEuclideanHalfSpace 9)) u :=
    contMDiffWithinAt_extChartAt_symm_range x₀ hu
  have h2 := (he ((extChartAt (modelWithCornersEuclideanHalfSpace 9) x₀).symm u)).comp_contMDiffWithinAt u h1
  exact h2.contDiffWithinAt.of_le ENat.LEInfty.out

/-- The within-derivative of the chart representative at the base point is the `mfderiv` of the
map, hence injective. -/
theorem chartRep_fderivWithin_injective {N : ℕ} {e : X → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (modelWithCornersEuclideanHalfSpace 9) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ∞ e)
    (hinj : ∀ x : X, Function.Injective
      (mfderiv (modelWithCornersEuclideanHalfSpace 9) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) e x)) (x₀ : X) :
    Function.Injective (fderivWithin ℝ (fun v => e ((extChartAt (modelWithCornersEuclideanHalfSpace 9) x₀).symm v))
      (Set.range (modelWithCornersEuclideanHalfSpace 9)) (extChartAt (modelWithCornersEuclideanHalfSpace 9) x₀ x₀)) := by
  have hmd : MDifferentiableAt (modelWithCornersEuclideanHalfSpace 9) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) e x₀ :=
    (he x₀).mdifferentiableAt (by simp)
  have h := hmd.mfderiv
  have hinj₀ := hinj x₀
  rw [h] at hinj₀
  have hfun : writtenInExtChartAt (modelWithCornersEuclideanHalfSpace 9)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) x₀ e
      = fun v => e ((extChartAt (modelWithCornersEuclideanHalfSpace 9) x₀).symm v) := by
    funext v
    rw [show writtenInExtChartAt (modelWithCornersEuclideanHalfSpace 9)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) x₀ e v
        = extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) (e x₀)
            (e ((extChartAt (modelWithCornersEuclideanHalfSpace 9) x₀).symm v)) from rfl]
    have hself : (↑(extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) (e x₀)) :
        EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) = id := by
      rw [extChartAt_self_eq]
      rfl
    rw [hself]
    rfl
  rwa [hfun] at hinj₀

end Chart


variable {X : Type} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 9) X]
  [IsManifold (modelWithCornersEuclideanHalfSpace 9) ∞ X]

/-- **Local uniqueness of the nearest point.**  For a `C^∞` immersion `e` of a compact manifold
with boundary that is a closed embedding, the nearest point of a nearby point `y` is locally
unique. -/
theorem localNearestUnique {N : ℕ} (e : X → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (modelWithCornersEuclideanHalfSpace 9)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ∞ e)
    (hinj : ∀ x : X, Function.Injective (mfderiv (modelWithCornersEuclideanHalfSpace 9)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) e x)) (x₀ : X) :
    ∃ (W : Set X) (_ : IsOpen W) (_ : x₀ ∈ W) (ν : ℝ) (_ : 0 < ν),
      ∀ x ∈ W, ∀ y : EuclideanSpace ℝ (Fin N),
        (∀ x'' : X, dist y (e x'') ≥ dist y (e x)) → dist y (e x) < ν →
          ∀ x' ∈ W, dist y (e x') ≤ dist y (e x) → x' = x := by
  classical
  set φ := extChartAt (modelWithCornersEuclideanHalfSpace 9) x₀ with hφ
  have hrange : Set.range (modelWithCornersEuclideanHalfSpace 9)
      = {v : EuclideanSpace ℝ (Fin 9) | 0 ≤ v 0} := range_modelWithCornersEuclideanHalfSpace 9
  have hx₀src : x₀ ∈ φ.source := by rw [hφ, extChartAt_source]; exact mem_chart_source _ _
  have hmem_range : ∀ z ∈ φ.source, φ z ∈ Set.range (modelWithCornersEuclideanHalfSpace 9) :=
    fun z hz => extChartAt_target_subset_range (I := modelWithCornersEuclideanHalfSpace 9)
      x₀ (φ.map_source hz)
  have hφopen : IsOpen φ.source := by
    rw [hφ, extChartAt_source]
    exact (chartAt (EuclideanHalfSpace 9) x₀).open_source
  have hφcont : ContinuousOn (↑φ) φ.source := hφ ▸ continuousOn_extChartAt x₀
  -- a ball around `u₀` inside the chart target
  obtain ⟨ρt, hρtpos, hρt⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Set.range (modelWithCornersEuclideanHalfSpace 9)
      ∩ Metric.ball (φ x₀) ρ ⊆ φ.target := by
    have H := OpenPartialHomeomorph.extend_target_mem_nhdsWithin
      (I := modelWithCornersEuclideanHalfSpace 9)
      (f := chartAt (EuclideanHalfSpace 9) x₀) (mem_chart_source (EuclideanHalfSpace 9) x₀)
    rw [Metric.mem_nhdsWithin_iff] at H
    obtain ⟨ρ, hρ, hρ'⟩ := H
    exact ⟨ρ, hρ, fun v hv => hρ' ⟨hv.2, hv.1⟩⟩
  set ρs : ℝ := ρt / 2 with hρsdef
  have hρspos : 0 < ρs := by rw [hρsdef]; linarith
  have hρslt : ρs < ρt := by rw [hρsdef]; linarith
  set s : Set (EuclideanSpace ℝ (Fin 9)) :=
    Set.range (modelWithCornersEuclideanHalfSpace 9) ∩ Metric.closedBall (φ x₀) ρs with hsdef
  have hu₀s : φ x₀ ∈ s := ⟨hmem_range x₀ hx₀src, by
    rw [Metric.mem_closedBall, dist_self]; exact le_of_lt hρspos⟩
  have hst : s ⊆ φ.target := fun v hv =>
    hρt ⟨hv.1, by
      rw [Metric.mem_ball]
      have := Metric.mem_closedBall.mp hv.2
      linarith⟩
  have hsconv : Convex ℝ s := by
    rw [hsdef, hrange]
    exact (EuclideanHalfSpace.convex (n := 9)).inter (convex_closedBall _ _)
  have hsc : IsCompact s := by
    rw [hsdef, hrange, Set.inter_comm]
    exact (isCompact_closedBall _ _).inter_right
      (isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 9 => ℝ) 0))
  have hsingle : (EuclideanSpace.single (0 : Fin 9) (1:ℝ) : EuclideanSpace ℝ (Fin 9)) 0 = 1 := by
    simp
  have hsingle_norm : ‖(EuclideanSpace.single (0 : Fin 9) (1:ℝ) : EuclideanSpace ℝ (Fin 9))‖ = 1 :=
    by simp
  have hsint : (interior s).Nonempty := by
    have h0 : (0:ℝ) ≤ (φ x₀) 0 := by
      have := hmem_range x₀ hx₀src; rwa [hrange] at this
    have hpt : φ x₀ + (ρs/4) • (EuclideanSpace.single (0 : Fin 9) (1:ℝ) :
        EuclideanSpace ℝ (Fin 9)) ∈
        {v : EuclideanSpace ℝ (Fin 9) | 0 < v 0} ∩ Metric.ball (φ x₀) ρs := by
      refine ⟨?_, ?_⟩
      · have hcoord : (φ x₀ + (ρs/4) • (EuclideanSpace.single (0 : Fin 9) (1:ℝ) :
            EuclideanSpace ℝ (Fin 9))) 0 = (φ x₀) 0 + ρs/4 := by
          simp [hsingle]
        show 0 < (φ x₀ + (ρs/4) • (EuclideanSpace.single (0 : Fin 9) (1:ℝ) :
          EuclideanSpace ℝ (Fin 9))) 0
        rw [hcoord]
        linarith
      · rw [Metric.mem_ball, dist_eq_norm]
        have hsub : φ x₀ + (ρs/4) • (EuclideanSpace.single (0 : Fin 9) (1:ℝ) :
            EuclideanSpace ℝ (Fin 9)) - φ x₀
            = (ρs/4) • (EuclideanSpace.single (0 : Fin 9) (1:ℝ) :
              EuclideanSpace ℝ (Fin 9)) := by abel
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hsingle_norm,
          mul_one]
        linarith
    refine ⟨φ x₀ + (ρs/4) • (EuclideanSpace.single (0 : Fin 9) (1:ℝ) :
      EuclideanSpace ℝ (Fin 9)), interior_maximal ?_ ?_ hpt⟩
    · intro v hv
      have hv1 : (0:ℝ) < v 0 := by simpa using hv.1
      exact ⟨by rw [hrange]; exact le_of_lt hv1, Metric.ball_subset_closedBall hv.2⟩
    · exact (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 9 => ℝ) 0)).inter
        Metric.isOpen_ball
  have hC2 : ContDiffOn ℝ 2 (fun v => e (φ.symm v)) s :=
    fun v hv => (chartRep_contDiffWithinAt he x₀ (hst hv)).mono Set.inter_subset_left
  have hinjs : ∀ v : EuclideanSpace ℝ (Fin 9),
      fderivWithin ℝ (fun v => e (φ.symm v)) s (φ x₀) v = 0 → v = 0 := by
    intro v hv
    have huniq : UniqueDiffWithinAt ℝ s (φ x₀) :=
      (uniqueDiffOn_convex hsconv hsint) (φ x₀) hu₀s
    have hdiff : DifferentiableWithinAt ℝ (fun v => e (φ.symm v))
        (Set.range (modelWithCornersEuclideanHalfSpace 9)) (φ x₀) :=
      (chartRep_contDiffWithinAt he x₀ (φ.map_source hx₀src)).differentiableWithinAt (by norm_num)
    have h1 : fderivWithin ℝ (fun v => e (φ.symm v)) s (φ x₀)
        = fderivWithin ℝ (fun v => e (φ.symm v))
          (Set.range (modelWithCornersEuclideanHalfSpace 9)) (φ x₀) :=
      fderivWithin_subset Set.inter_subset_left huniq hdiff
    rw [h1] at hv
    exact chartRep_fderivWithin_injective he hinj x₀ (by rw [hv, map_zero])
  obtain ⟨ρ, c, C, hρpos, hcpos, hCpos, hexp, htar⟩ :=
    exists_expansion_taylor_compact hsconv hsc hsint hu₀s hC2 hinjs
  set ρuse : ℝ := min ρ (min ρs (c / (4 * C))) with hρusedef
  have hρusepos : 0 < ρuse := by
    rw [hρusedef]; exact lt_min hρpos (lt_min hρspos (by positivity))
  have hρuseρ : ρuse ≤ ρ := by rw [hρusedef]; exact min_le_left _ _
  have hρusers : ρuse ≤ ρs := by
    rw [hρusedef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρusec : ρuse ≤ c / (4 * C) := by
    rw [hρusedef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hνpos : 0 < c ^ 2 / (24 * C) := by positivity
  refine ⟨φ.source ∩ φ ⁻¹' Metric.ball (φ x₀) ρuse, ?_, ?_, c ^ 2 / (24 * C), hνpos, ?_⟩
  · exact ContinuousOn.isOpen_inter_preimage hφcont hφopen Metric.isOpen_ball
  · exact ⟨hx₀src, by rw [Set.mem_preimage, Metric.mem_ball, dist_self]; exact hρusepos⟩
  · intro x hxW y hmin hyν x' hx'W hx'min
    obtain ⟨hxsrc, hxball⟩ := hxW
    obtain ⟨hx'src, hx'ball⟩ := hx'W
    rw [Set.mem_preimage, Metric.mem_ball] at hxball hx'ball
    have hu : φ x ∈ s := ⟨hmem_range x hxsrc, by
      rw [Metric.mem_closedBall]; linarith [Metric.mem_ball.mp hxball, hρusers]⟩
    have hu' : φ x' ∈ s := ⟨hmem_range x' hx'src, by
      rw [Metric.mem_closedBall]; linarith [Metric.mem_ball.mp hx'ball, hρusers]⟩
    have hFx : (fun v => e (φ.symm v)) (φ x) = e x := by
      show e (φ.symm (φ x)) = e x
      rw [φ.left_inv hxsrc]
    have hFx' : (fun v => e (φ.symm v)) (φ x') = e x' := by
      show e (φ.symm (φ x')) = e x'
      rw [φ.left_inv hx'src]
    have hmin' : ∀ w ∈ s, ‖y - (fun v => e (φ.symm v)) (φ x)‖
        ≤ ‖y - (fun v => e (φ.symm v)) w‖ := by
      intro w hw
      have h2 : (fun v => e (φ.symm v)) w = e (φ.symm w) := rfl
      rw [hFx, h2]
      have h3 := hmin (φ.symm w)
      rw [dist_eq_norm, dist_eq_norm] at h3
      exact h3
    have hD : HasFDerivWithinAt (fun v => e (φ.symm v))
        (fderivWithin ℝ (fun v => e (φ.symm v)) s (φ x)) s (φ x) :=
      ((hC2 (φ x) hu).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have hferm : 0 ≤ -2 * inner ℝ (y - (fun v => e (φ.symm v)) (φ x))
        (fderivWithin ℝ (fun v => e (φ.symm v)) s (φ x) (φ x' - φ x)) :=
      fermatCondition hsconv hu hu' hD hmin'
    have hΔnorm : ‖φ x' - φ x‖ ≤ 2 * ρuse := by
      have h1 := Metric.mem_ball.mp hxball
      have h2 := Metric.mem_ball.mp hx'ball
      rw [dist_eq_norm] at h1 h2
      calc ‖φ x' - φ x‖ ≤ ‖φ x' - φ x₀‖ + ‖φ x₀ - φ x‖ := by
            rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
            exact dist_triangle _ _ _
        _ ≤ ρuse + ρuse := by rw [norm_sub_rev (φ x₀) (φ x)]; linarith [h1, h2]
        _ = 2 * ρuse := by ring
    have hfar : ‖(fun v => e (φ.symm v)) (φ x') - (fun v => e (φ.symm v)) (φ x)‖
        ≤ dist y (e x') + dist y (e x) := by
      rw [hFx, hFx']
      calc ‖e x' - e x‖ = dist (e x') (e x) := by rw [dist_eq_norm]
        _ ≤ dist (e x') y + dist y (e x) := dist_triangle _ _ _
        _ = dist y (e x') + dist y (e x) := by rw [dist_comm (e x') y]
    have hsmall : 2 * C * ‖y - (fun v => e (φ.symm v)) (φ x)‖
        + 2 * C * ‖fderivWithin ℝ (fun v => e (φ.symm v)) s (φ x) (φ x' - φ x)‖ < c ^ 2 := by
      have h1 : ‖y - (fun v => e (φ.symm v)) (φ x)‖ = dist y (e x) := by rw [hFx, dist_eq_norm]
      have h2 : ‖fderivWithin ℝ (fun v => e (φ.symm v)) s (φ x) (φ x' - φ x)‖
          ≤ (dist y (e x') + dist y (e x)) + C * ‖φ x' - φ x‖ ^ 2 := by
        have ht := htar (φ x) hu (φ x') hu'
        have h3 : fderivWithin ℝ (fun v => e (φ.symm v)) s (φ x) (φ x' - φ x)
            = ((fun v => e (φ.symm v)) (φ x') - (fun v => e (φ.symm v)) (φ x))
              - ((fun v => e (φ.symm v)) (φ x') - (fun v => e (φ.symm v)) (φ x)
                - fderivWithin ℝ (fun v => e (φ.symm v)) s (φ x) (φ x' - φ x)) := by abel
        rw [h3]
        exact (norm_sub_le _ _).trans (by linarith [ht, hfar])
      have h4 : dist y (e x') ≤ dist y (e x) := hx'min
      have h5 : ‖φ x' - φ x‖ ^ 2 ≤ 4 * ρuse ^ 2 := by
        have := norm_nonneg (φ x' - φ x); nlinarith [hΔnorm]
      have hA : 4 * C * ρuse ≤ c := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * C)] at hρusec
        linarith [hρusec]
      have hB : 2 * C * ρuse ≤ c / 2 := by linarith [hA]
      have hν6 : 6 * C * (c ^ 2 / (24 * C)) = c ^ 2 / 4 := by
        field_simp
        ring
      have h9 : (4 * C * ρuse) * (2 * C * ρuse) ≤ c * (c / 2) :=
        mul_le_mul hA hB (by positivity) (by positivity)
      have h10 : 2 * C * ‖y - (fun v => e (φ.symm v)) (φ x)‖
          + 2 * C * ‖fderivWithin ℝ (fun v => e (φ.symm v)) s (φ x) (φ x' - φ x)‖
          ≤ 6 * C * dist y (e x) + 8 * C ^ 2 * ρuse ^ 2 := by
        rw [h1]
        have h11 : 2 * C * (dist y (e x') + dist y (e x)) ≤ 4 * C * dist y (e x) := by
          nlinarith [h4, hCpos]
        have h12 : 2 * C * (C * ‖φ x' - φ x‖ ^ 2) ≤ 8 * C ^ 2 * ρuse ^ 2 := by
          nlinarith [h5, hCpos]
        have h2' : 2 * C * ‖fderivWithin ℝ (fun v => e (φ.symm v)) s (φ x) (φ x' - φ x)‖
            ≤ 2 * C * ((dist y (e x') + dist y (e x)) + C * ‖φ x' - φ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        linarith [h2', h11, h12]
      have h13 : 8 * C ^ 2 * ρuse ^ 2 ≤ c ^ 2 / 2 := by nlinarith [h9]
      have h14 : 6 * C * dist y (e x) < c ^ 2 / 4 := by nlinarith [hyν, hν6, hCpos]
      have hc2 : 0 < c ^ 2 := by positivity
      linarith [h10, h13, h14, hc2]
    have hexp' : ∀ v : EuclideanSpace ℝ (Fin 9),
        c * ‖v‖ ≤ ‖(fderivWithin ℝ (fun v => e (φ.symm v)) s (φ x)) v‖ :=
      hexp (φ x) hu (by
        have hb := hxball
        rw [dist_eq_norm] at hb
        linarith [hb, hρuseρ])
    have hx'min' : ‖y - (fun v => e (φ.symm v)) (φ x')‖
        ≤ ‖y - (fun v => e (φ.symm v)) (φ x)‖ := by
      rw [hFx', hFx]
      rwa [dist_eq_norm, dist_eq_norm] at hx'min
    have huu : φ x' = φ x :=
      nearestUniqueOfEstimates (f := fun v => e (φ.symm v)) (u := φ x) (u' := φ x')
        (D := fderivWithin ℝ (fun v => e (φ.symm v)) s (φ x)) (y := y)
        hcpos hCpos hexp' (htar (φ x) hu (φ x') hu') hferm hx'min' hsmall
    exact φ.injOn hx'src hxsrc huu

end

end Work.ThomBordism.NullBord
