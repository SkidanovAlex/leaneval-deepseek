import Mathlib

/-!
# Uniform quadratic flatness at critical points

`flat_sigma0`: if `g : ℝⁿ → ℝᵐ` is of class `C²`, then for every `ε > 0` the critical points of
`g` inside a closed ball of radius `R` are uniformly `ε`-quadratically flat:

```
∀ ε > 0, ∃ δ > 0, ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
  fderiv ℝ g x = 0 → fderiv ℝ g y = 0 → ‖y - x‖ ≤ δ → ‖g y - g x‖ ≤ ε * ‖y - x‖ ^ 2
```

The *uniformity* in `x` is the content: pointwise quadratic flatness at each critical point would
only give a modulus depending on the point.

## Proof

Fix `ε > 0`, put `η = ε/2`, and let `B` be the closed ball of radius `R`.  The second derivative
`h = D²g` is continuous, hence uniformly continuous on the compact set `B` (Heine–Cantor,
`second_deriv_uniform` below): there is `δ₁ > 0` with

`‖h z - h x‖ ≤ η` whenever `x, z ∈ B` and `‖z - x‖ ≤ δ₁`.   (*)

1. **First-order Taylor for `Dg`.**  Apply the mean value inequality
   `Convex.norm_image_sub_le_of_norm_fderiv_le'` to `f = Dg`, the linear map `φ = h x` and the
   convex segment `[x, w]`: by (*) the derivative `h z` differs from `φ` by at most `η` on it, so
   for `x, w ∈ B` with `‖w - x‖ ≤ δ₁`,

   `‖Dg w - Dg x - h x (w - x)‖ ≤ η ‖w - x‖`.   (†)

2. **Smallness of the Hessian on the increment.**  Taking `w = y` in (†) and using that both `x`
   and `y` are critical (`Dg = 0`) gives `‖h x (y - x)‖ ≤ η ‖y - x‖`.   (‡)

3. **Bounding `Dg` along the segment.**  For `z` on the segment `[x, y]`, write
   `z - x = θ (y - x)`; then (†) at `z` gives `‖Dg z - Dg x - h x (z - x)‖ ≤ η ‖z - x‖ ≤ η ‖y - x‖`,
   while `‖h x (z - x)‖ ≤ ‖h x (y - x)‖ ≤ η ‖y - x‖` by (‡).  Hence `‖Dg z‖ ≤ 2 η ‖y - x‖`.

4. **Mean value inequality for `g`.**  Applying `Convex.norm_image_sub_le_of_norm_fderiv_le` to `g`
   on the convex segment `[x, y]` with the bound of step 3 yields
   `‖g y - g x‖ ≤ 2 η ‖y - x‖² = ε ‖y - x‖²`.
-/

namespace Work.WilE2.RegVals

open Metric Filter
open scoped Topology Uniformity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

/-- A continuous linear map which is bounded by `c` on the closed unit ball has operator norm
at most `c`. -/
private lemma opnorm_le_of_forall {n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (φ : (Fin n → ℝ) →L[ℝ] G) {c : ℝ} (hc : 0 < c)
    (hφ : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ‖φ x‖ ≤ c) : ‖φ‖ ≤ c := by
  refine (ContinuousLinearMap.opNorm_le_iff (le_of_lt hc)).mpr (fun x => ?_)
  by_cases hx : ‖x‖ = 0
  · simp [norm_eq_zero.mp hx]
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    have hu : (‖x‖)⁻¹ • x ∈ closedBall (0 : Fin n → ℝ) 1 := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hxpos), inv_mul_cancel₀ hx]
    have hfu := hφ _ hu
    have hfx : ‖φ x‖ = ‖x‖ * ‖φ ((‖x‖)⁻¹ • x)‖ := by
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos),
        ← mul_assoc, mul_inv_cancel₀ hx, one_mul]
    rw [hfx]
    calc ‖x‖ * ‖φ ((‖x‖)⁻¹ • x)‖ ≤ ‖x‖ * c := mul_le_mul_of_nonneg_left hfu (norm_nonneg x)
      _ = c * ‖x‖ := by ring


/-- The second derivative `D²g` of a `C²` map is uniformly continuous on a closed ball: for every
`η > 0` there is `δ > 0` such that `x, z` in the ball at distance `≤ δ` have `‖D²g z - D²g x‖ ≤ η`.

This is the Heine–Cantor theorem (`IsCompact.uniformContinuousOn_of_continuous`) for the compact
ball.  It is phrased in terms of the norm (rather than of an abstract notion of uniform
continuity) so that it can be applied directly to the continuous-linear-map-valued `D²g`: the
`ε`-`δ` form is read off the norm-basis of the (ambient) uniformity of the operator-normed space
of continuous linear maps. -/
private lemma second_deriv_uniform {n m : ℕ} (g : (Fin n → ℝ) → (Fin m → ℝ))
    (hg : ContDiff ℝ 2 g) (R : ℝ) :
    ∀ η > 0, ∃ δ > 0, ∀ x ∈ closedBall (0 : Fin n → ℝ) R, ∀ z ∈ closedBall (0 : Fin n → ℝ) R,
      ‖z - x‖ ≤ δ → ‖fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) x‖ ≤ η := by
  intro η hη
  have h1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hhcont : Continuous (fun z : Fin n → ℝ => fderiv ℝ (fderiv ℝ g) z) :=
    h1.continuous_fderiv (by norm_num)
  have hK : IsCompact (closedBall (0 : Fin n → ℝ) R) := isCompact_closedBall 0 R
  have hη2 : 0 < η / 2 := by linarith
  have hη4 : 0 < η / 4 := by linarith
  -- `{f | ‖f‖ < η/2}` is a neighbourhood of `0` (operator-norm topology)
  have hV : {f : (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) | ‖f‖ < η / 2} ∈
      𝓝 (0 : (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ))) := by
    refine ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.mpr
      ⟨(closedBall (0 : Fin n → ℝ) 1,
        {g : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) |
          ∀ y ∈ closedBall (0 : Fin n → ℝ) 1, g y ∈ ball (0 : Fin m → ℝ) (η / 4)}),
        ⟨?_, ?_⟩, ?_⟩
    · exact NormedSpace.isVonNBounded_closedBall ℝ (Fin n → ℝ) 1
    · refine ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.mpr
        ⟨(closedBall (0 : Fin n → ℝ) 1, ball (0 : Fin m → ℝ) (η / 4)),
          ⟨NormedSpace.isVonNBounded_closedBall ℝ (Fin n → ℝ) 1,
            Metric.ball_mem_nhds 0 hη4⟩, fun g hg => hg⟩
    · intro f hf
      simp only [Set.mem_setOf_eq] at hf ⊢
      have hfx : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ‖f x‖ ≤ η / 4 := by
        intro x hx
        refine opnorm_le_of_forall (f x) hη4 (fun y hy => ?_)
        have h := hf x hx y hy
        rw [mem_ball, dist_zero_right] at h
        exact le_of_lt h
      have hf' := opnorm_le_of_forall f hη4 hfx
      linarith
  -- each point of the space has a ball on which `D²g` oscillates by less than `η/2`
  have hU : ∀ x : Fin n → ℝ, ∃ ρ > 0, ∀ z, ‖z - x‖ < ρ →
      ‖fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) x‖ < η / 2 := by
    intro x
    have hnb : {w : (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) |
        ‖w - fderiv ℝ (fderiv ℝ g) x‖ < η / 2} ∈ 𝓝 (fderiv ℝ (fderiv ℝ g) x) := by
      rw [← map_add_left_nhds_zero (fderiv ℝ (fderiv ℝ g) x), Filter.mem_map]
      refine Filter.mem_of_superset hV (fun y hy => ?_)
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy ⊢
      rw [show fderiv ℝ (fderiv ℝ g) x + y - fderiv ℝ (fderiv ℝ g) x = y from by abel]
      exact hy
    have hpre := hhcont.continuousAt hnb
    obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp hpre
    exact ⟨ρ, hρpos, fun z hz => hρ hz⟩
  choose ρ hρpos hρ using hU
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x _ => ball x (ρ x / 2))
    (fun x _ => ball_mem_nhds x (by linarith [hρpos x]))
  rcases t.eq_empty_or_nonempty with rfl | htne
  · exact ⟨1, one_pos, fun x hx z hz hzx => absurd (ht hx) (by simp)⟩
  · let vals : Finset ℝ := t.image (fun x : ↥(closedBall (0 : Fin n → ℝ) R) => ρ x.1 / 4)
    have hne : vals.Nonempty := by
      obtain ⟨y, hy⟩ := htne
      exact ⟨ρ y.1 / 4, Finset.mem_image_of_mem _ hy⟩
    set m : ℝ := vals.min' hne with hm
    have hmpos : 0 < m := by
      obtain ⟨y, hy, hym⟩ := Finset.mem_image.mp (Finset.min'_mem vals hne)
      rw [hm, ← hym]
      linarith [hρpos y.1]
    refine ⟨m, hmpos, fun x hx z hz hzx => ?_⟩
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hxi' : ‖x - i.1‖ < ρ i.1 / 2 := by simpa [mem_ball, dist_eq_norm] using hxi
    have hmi : m ≤ ρ i.1 / 4 := by
      rw [hm]
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hi)
    have hzi : ‖z - i.1‖ < ρ i.1 := by
      have hstep : ‖z - i.1‖ ≤ ‖z - x‖ + ‖x - i.1‖ := by
        calc ‖z - i.1‖ = ‖(z - x) + (x - i.1)‖ := by congr 1; abel
          _ ≤ ‖z - x‖ + ‖x - i.1‖ := norm_add_le (z - x) (x - i.1)
      linarith [hρpos i.1]
    have hz1 : ‖fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) i.1‖ < η / 2 := hρ i.1 z hzi
    have hz2 : ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) i.1‖ < η / 2 :=
      hρ i.1 x (by linarith [hxi', hρpos i.1])
    have hstep2 : ‖fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) x‖
        ≤ ‖fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) i.1‖
          + ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) i.1‖ := by
      have hs := norm_sub_le
        (fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) i.1)
        (fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) i.1)
      rwa [show (fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) i.1)
            - (fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) i.1)
          = fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) x from by abel] at hs
    linarith

theorem flat_sigma0 {n m : ℕ} (g : (Fin n → ℝ) → (Fin m → ℝ)) (hg : ContDiff ℝ 2 g) (R : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y : Fin n → ℝ, ‖x‖ ≤ R → ‖y‖ ≤ R →
      fderiv ℝ g x = 0 → fderiv ℝ g y = 0 → ‖y - x‖ ≤ δ → ‖g y - g x‖ ≤ ε * ‖y - x‖ ^ 2 := by
  intro ε hε
  -- the auxiliary constant `η = ε/2`
  set η : ℝ := ε / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  have h1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hhdiff : Differentiable ℝ (fderiv ℝ g) := h1.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  -- uniform continuity of the second derivative on the closed ball
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := second_deriv_uniform g hg R η hηpos
  refine ⟨δ₁ / 2, by linarith, ?_⟩
  intro x y hxR hyR hfx hfy hxy
  have hxball : x ∈ closedBall (0 : Fin n → ℝ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm]; simpa using hxR
  have hyball : y ∈ closedBall (0 : Fin n → ℝ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm]; simpa using hyR
  have hylt : ‖y - x‖ < δ₁ := by linarith
  -- the segment `[x,y]` stays inside the ball
  have hsegB : segment ℝ x y ⊆ closedBall (0 : Fin n → ℝ) R :=
    (convex_closedBall (0 : Fin n → ℝ) R).segment_subset hxball hyball
  -- `‖z - x‖ ≤ ‖y - x‖` for `z` on the segment
  have hzxle : ∀ z ∈ segment ℝ x y, ‖z - x‖ ≤ ‖y - x‖ := by
    intro z hz
    rw [segment_eq_image] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    have h1' : (1 - θ) • x + θ • y - x = θ • (y - x) := by module
    rw [h1', norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hθ.2
  -- first-order Taylor bound for `Dg` on the ball
  have hTaylor : ∀ w : Fin n → ℝ, w ∈ closedBall (0 : Fin n → ℝ) R → ‖w - x‖ < δ₁ →
      ‖fderiv ℝ g w - fderiv ℝ g x - (fderiv ℝ (fderiv ℝ g) x) (w - x)‖ ≤ η * ‖w - x‖ := by
    intro w hwB hwd
    have hbound : ∀ z ∈ segment ℝ x w,
        ‖fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) x‖ ≤ η := by
      intro z hz
      have hzB : z ∈ closedBall (0 : Fin n → ℝ) R :=
        (convex_closedBall (0 : Fin n → ℝ) R).segment_subset hxball hwB hz
      have hzx : ‖z - x‖ ≤ ‖w - x‖ := by
        rw [segment_eq_image] at hz
        obtain ⟨θ, hθ, rfl⟩ := hz
        have h1' : (1 - θ) • x + θ • w - x = θ • (w - x) := by module
        rw [h1', norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hθ.2
      exact hδ₁ x hxball z hzB (le_of_lt (lt_of_le_of_lt hzx hwd))
    exact (convex_segment x w).norm_image_sub_le_of_norm_fderiv_le'
      (f := fderiv ℝ g) (C := η) (φ := fderiv ℝ (fderiv ℝ g) x)
      (fun z _ => hhdiff.differentiableAt) hbound
      (left_mem_segment ℝ x w) (right_mem_segment ℝ x w)
  -- smallness of `h x (y - x)`
  have hKey : ‖(fderiv ℝ (fderiv ℝ g) x) (y - x)‖ ≤ η * ‖y - x‖ := by
    have h := hTaylor y hyball hylt
    have h2 : fderiv ℝ g y - fderiv ℝ g x - (fderiv ℝ (fderiv ℝ g) x) (y - x)
        = -((fderiv ℝ (fderiv ℝ g) x) (y - x)) := by rw [hfy, hfx]; abel
    rw [h2, norm_neg] at h
    exact h
  -- bound for `h x` applied to a point of the segment
  have hzlin : ∀ z ∈ segment ℝ x y,
      ‖(fderiv ℝ (fderiv ℝ g) x) (z - x)‖ ≤ η * ‖y - x‖ := by
    intro z hz
    rw [segment_eq_image] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    have h1' : (1 - θ) • x + θ • y - x = θ • (y - x) := by module
    rw [h1', map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    calc θ * ‖(fderiv ℝ (fderiv ℝ g) x) (y - x)‖
        ≤ 1 * ‖(fderiv ℝ (fderiv ℝ g) x) (y - x)‖ := by
          gcongr; exact hθ.2
      _ = ‖(fderiv ℝ (fderiv ℝ g) x) (y - x)‖ := one_mul _
      _ ≤ η * ‖y - x‖ := hKey
  -- pointwise bound for `Dg` along the segment
  have hbound2 : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ g z‖ ≤ 2 * η * ‖y - x‖ := by
    intro z hz
    have hzB : z ∈ closedBall (0 : Fin n → ℝ) R := hsegB hz
    have hzd : ‖z - x‖ < δ₁ := lt_of_le_of_lt (hzxle z hz) hylt
    have htz := hTaylor z hzB hzd
    have hdecomp : fderiv ℝ g z
        = (fderiv ℝ g z - fderiv ℝ g x - (fderiv ℝ (fderiv ℝ g) x) (z - x))
          + (fderiv ℝ (fderiv ℝ g) x) (z - x) := by
      rw [hfx]; abel
    rw [hdecomp]
    calc ‖(fderiv ℝ g z - fderiv ℝ g x - (fderiv ℝ (fderiv ℝ g) x) (z - x))
            + (fderiv ℝ (fderiv ℝ g) x) (z - x)‖
        ≤ ‖fderiv ℝ g z - fderiv ℝ g x - (fderiv ℝ (fderiv ℝ g) x) (z - x)‖
          + ‖(fderiv ℝ (fderiv ℝ g) x) (z - x)‖ := norm_add_le _ _
      _ ≤ η * ‖z - x‖ + η * ‖y - x‖ := add_le_add htz (hzlin z hz)
      _ ≤ η * ‖y - x‖ + η * ‖y - x‖ := by
          have := hzxle z hz; gcongr
      _ = 2 * η * ‖y - x‖ := by ring
  -- mean value inequality for `g` on the segment
  have hmvt := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (f := g) (C := 2 * η * ‖y - x‖)
    (fun z _ => hgd.differentiableAt) hbound2
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  calc ‖g y - g x‖ ≤ (2 * η * ‖y - x‖) * ‖y - x‖ := hmvt
    _ = ε * ‖y - x‖ ^ 2 := by rw [hηdef]; ring

end Work.WilE2.RegVals
