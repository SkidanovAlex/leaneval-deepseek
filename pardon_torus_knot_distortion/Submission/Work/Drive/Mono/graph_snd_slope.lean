import Mathlib
import Submission.Work.Smooth.BoxGeneric.LocalArc.exists_root_pair
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_tangential

namespace Work.Drive.Mono

theorem graph_snd_slope {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hg0 : g 0 = 0)
    (hdg : fderiv ℝ g 0 = ContinuousLinearMap.snd ℝ ℝ ℝ) :
    ∃ R₁ R₂ ρ : ℝ, 0 < R₁ ∧ 0 < R₂ ∧ 0 < ρ ∧ ∃ ψ : ℝ → ℝ, ψ 0 = 0 ∧
      ContinuousOn ψ (Set.Ioo (-R₁) R₁) ∧
      (∀ x : ℝ, |x| ≤ R₁ → |ψ x| ≤ |x| / 2) ∧
      (∀ x y : ℝ, |x| ≤ R₁ → |y| ≤ R₂ →
        (g (x, y) ≤ 0 ↔ y ≤ ψ x) ∧ (g (x, y) = 0 ↔ y = ψ x)) ∧
      (∀ z : ℝ × ℝ, ‖z‖ ≤ ρ → |g z - z.2| ≤ ‖z‖ / 4) := by
  -- `h := g - snd` is `C¹` with vanishing derivative at the origin.
  have hCont : ContDiff ℝ 1 (fun z : ℝ × ℝ => g z - z.2) := by fun_prop
  have hfd_cont : Continuous (fderiv ℝ (fun z : ℝ × ℝ => g z - z.2)) :=
    hCont.continuous_fderiv (by norm_num)
  have hfd0 : fderiv ℝ (fun z : ℝ × ℝ => g z - z.2) (0:ℝ×ℝ) = 0 := by
    have h1 : HasFDerivAt (fun z : ℝ × ℝ => g z - z.2)
        ((fderiv ℝ g 0) - ContinuousLinearMap.snd ℝ ℝ ℝ) (0:ℝ×ℝ) := by
      have hg' : HasFDerivAt g (fderiv ℝ g 0) (0:ℝ×ℝ) :=
        (hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have hs' : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (0:ℝ×ℝ) :=
        (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
      exact hg'.sub hs'
    rw [h1.fderiv, hdg, sub_self]
  -- A radius on which `‖fderiv h‖ ≤ 1/4`.
  obtain ⟨r, hrpos, hr⟩ : ∃ r > 0, ∀ z : ℝ × ℝ, ‖z‖ ≤ r →
      ‖fderiv ℝ (fun z : ℝ × ℝ => g z - z.2) z‖ ≤ 1/4 := by
    have hct : ContinuousAt (fun z : ℝ × ℝ => ‖fderiv ℝ (fun z : ℝ × ℝ => g z - z.2) z‖) 0 :=
      (continuous_norm.comp hfd_cont).continuousAt
    rw [Metric.continuousAt_iff] at hct
    obtain ⟨δ, hδpos, hδ⟩ := hct (1/4) (by norm_num)
    refine ⟨δ/2, by linarith, fun z hz => ?_⟩
    have hz' : dist z (0:ℝ×ℝ) < δ := by rw [dist_eq_norm, sub_zero]; linarith
    have hthis := hδ hz'
    rw [Real.dist_eq] at hthis
    have h0' : ‖fderiv ℝ (fun z : ℝ × ℝ => g z - z.2) (0:ℝ×ℝ)‖ = 0 := by rw [hfd0, norm_zero]
    rw [h0', sub_zero, abs_of_nonneg (norm_nonneg _)] at hthis
    exact le_of_lt hthis
  -- The mean value bound `|h z| ≤ ‖z‖/4` on that radius (also the last clause of the goal).
  have hbound : ∀ z : ℝ × ℝ, ‖z‖ ≤ r → |g z - z.2| ≤ ‖z‖ / 4 := by
    intro z hz
    have hconv : Convex ℝ (Metric.closedBall (0:ℝ×ℝ) r) := convex_closedBall 0 r
    have hdiff : ∀ p ∈ Metric.closedBall (0:ℝ×ℝ) r,
        DifferentiableAt ℝ (fun z : ℝ × ℝ => g z - z.2) p :=
      fun p hp => (hCont.differentiable (by norm_num)).differentiableAt
    have hbnd : ∀ p ∈ Metric.closedBall (0:ℝ×ℝ) r,
        ‖fderiv ℝ (fun z : ℝ × ℝ => g z - z.2) p‖ ≤ 1/4 := by
      intro p hp
      exact hr p (by rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hp)
    have hz' : z ∈ Metric.closedBall (0:ℝ×ℝ) r := by
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have h0' : (0:ℝ×ℝ) ∈ Metric.closedBall (0:ℝ×ℝ) r := by
      rw [Metric.mem_closedBall, dist_self]; linarith
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbnd hconv hz' h0'
    rw [norm_sub_rev 0 z, sub_zero, Real.norm_eq_abs] at hmvt
    rw [abs_sub_comm] at hmvt
    simp only [hg0, Prod.snd_zero, sub_zero] at hmvt
    linarith
  -- Swap coordinates: the zero set of `g` becomes a graph over the first coordinate of `F`.
  set F : ℝ × ℝ → ℝ := fun z => g (z.2, z.1) with hFdef
  have hFcd : ContDiff ℝ 1 F := by rw [hFdef]; fun_prop
  have hF0 : F 0 = 0 := by
    rw [hFdef]; simp only [Prod.snd_zero, Prod.fst_zero]; exact hg0
  have hFpos : 0 < (fderiv ℝ F 0) (1,0) := by
    set S : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ) with hS
    have hSap : ∀ z : ℝ × ℝ, S z = (z.2, z.1) := by
      intro z; rw [hS, ContinuousLinearMap.prod_apply]; simp
    have hFderiv : fderiv ℝ F 0 = (fderiv ℝ g 0).comp S := by
      have hsw : (fun z : ℝ × ℝ => (z.2, z.1)) = ⇑S := by funext z; rw [hSap]
      have hSfd : HasFDerivAt (fun z : ℝ × ℝ => (z.2, z.1)) S 0 := by
        rw [hsw]; exact S.hasFDerivAt
      have hgfd : HasFDerivAt g (fderiv ℝ g 0) ((fun z : ℝ × ℝ => (z.2, z.1)) 0) :=
        ((hg.differentiable (by norm_num)).differentiableAt (x := 0)).hasFDerivAt
      have hcomp := (hgfd.comp (f := fun z : ℝ × ℝ => (z.2, z.1)) 0 hSfd).fderiv
      rw [hFdef]
      simpa only [Function.comp_def] using hcomp
    rw [hFderiv, ContinuousLinearMap.comp_apply, hSap, hdg]
    norm_num
  obtain ⟨Rx, Ry, hRx, hRy, ψ, _, hψ0, _, hψc, _, hroot, hle, heq⟩ :=
    Work.Smooth.BoxGeneric.LocalArc.exists_root_pair hFcd hFcd hF0 hF0 rfl hFpos
  -- The graph description in the coordinates of `g`.
  have hle' : ∀ a b : ℝ, |a| ≤ Rx → |b| ≤ Ry → (g (b, a) ≤ 0 ↔ a ≤ ψ b) := by
    intro a b ha hb
    have h := (hle a b ha hb).1
    simpa [hFdef] using h
  have heq' : ∀ a b : ℝ, |a| ≤ Rx → |b| ≤ Ry → (g (b, a) = 0 ↔ a = ψ b) := by
    intro a b ha hb
    have h := (heq a b ha hb).1
    simpa [hFdef] using h
  -- The box used for the final statement.
  set R₁ : ℝ := min (min Ry (r/4)) (3*Rx) with hR₁
  set R₂ : ℝ := min Rx (r/4) with hR₂
  have hR₁pos : 0 < R₁ := by rw [hR₁]; exact lt_min (lt_min hRy (by linarith)) (by linarith)
  have hR₂pos : 0 < R₂ := by rw [hR₂]; exact lt_min hRx (by linarith)
  have hR₁leRy : R₁ ≤ Ry := by rw [hR₁]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hR₁le_r4 : R₁ ≤ r/4 := by rw [hR₁]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hR₁le3Rx : R₁ ≤ 3*Rx := by rw [hR₁]; exact min_le_right _ _
  have hR₂leRx : R₂ ≤ Rx := by rw [hR₂]; exact min_le_left _ _
  have hR₂le_r4 : R₂ ≤ r/4 := by rw [hR₂]; exact min_le_right _ _
  -- Sharp bound on the graph function.
  have hsharp : ∀ x : ℝ, |x| ≤ R₁ → |ψ x| ≤ |x| / 2 := by
    intro x hx
    have hxRy : |x| ≤ Ry := le_trans hx hR₁leRy
    have hxle : |x| ≤ r/4 := le_trans hx hR₁le_r4
    have hnorm_gen : ∀ y : ℝ, ‖(x,y)‖ ≤ |x| + |y| := by
      intro y
      rw [Prod.norm_def]
      simp only [Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg y)) (le_add_of_nonneg_left (abs_nonneg x))
    have habs3 : |(|x|/3 : ℝ)| = |x|/3 := abs_of_nonneg (by positivity)
    have hu_leRx : |(|x|/3 : ℝ)| ≤ Rx := by
      rw [habs3]
      have h2 : R₁/3 ≤ Rx := by linarith [hR₁le3Rx]
      linarith [hxle, h2]
    have hu_leR₂ : |(|x|/3 : ℝ)| ≤ R₂ := by
      rw [hR₂]; exact le_min hu_leRx (by rw [habs3]; linarith [hxle])
    -- `g (x, |x|/3) ≥ 0` and `g (x, -|x|/3) ≤ 0`, so the root sits in between.
    have hgnu : g (x, |x|/3) ≥ 0 := by
      have h := hbound (x, |x|/3) (by
        have h1 := hnorm_gen (|x|/3)
        rw [habs3] at h1
        linarith [h1, hxle, abs_nonneg x])
      have h2 : ‖(x, |x|/3)‖ ≤ 4*|x|/3 := by
        have h1 := hnorm_gen (|x|/3)
        rw [habs3] at h1
        linarith [h1]
      have : ‖(x, |x|/3)‖ / 4 ≤ |x|/3 := by linarith [h2]
      have := neg_abs_le (g (x, |x|/3) - |x|/3)
      linarith
    have hψx_le : ψ x ≤ |x|/3 := by
      rcases lt_or_eq_of_le hgnu with hlt | heq0
      · have hnot : ¬ ((|x|/3) ≤ ψ x) :=
          fun hle => absurd ((hle' (|x|/3) x hu_leRx hxRy).mpr hle) (not_le.mpr hlt)
        exact le_of_lt (not_le.mp hnot)
      · exact le_of_eq ((heq' (|x|/3) x hu_leRx hxRy).mp heq0.symm).symm
    have hgnv : g (x, -(|x|/3)) ≤ 0 := by
      have h := hbound (x, -(|x|/3)) (by
        have h1 := hnorm_gen (-(|x|/3))
        rw [abs_neg, habs3] at h1
        linarith [h1, hxle, abs_nonneg x])
      have h2 : ‖(x, -(|x|/3))‖ ≤ 4*|x|/3 := by
        have h1 := hnorm_gen (-(|x|/3))
        rw [abs_neg, habs3] at h1
        linarith [h1]
      have h3 : ‖(x, -(|x|/3))‖ / 4 ≤ |x|/3 := by linarith [h2]
      have h4 := le_abs_self (g (x, -(|x|/3)) - (-(|x|/3)))
      linarith
    have hψx_ge : -(|x|/3) ≤ ψ x :=
      (hle' (-(|x|/3)) x (by rw [abs_neg]; exact hu_leRx) hxRy).mp hgnv
    have h3 : |ψ x| ≤ |x|/3 := abs_le.mpr ⟨hψx_ge, hψx_le⟩
    linarith [abs_nonneg x]
  refine ⟨R₁, R₂, r, hR₁pos, hR₂pos, hrpos, ψ, hψ0, ?_, hsharp, ?_, ?_⟩
  · refine hψc.mono ?_
    intro x hx
    rw [Set.mem_Ioo] at hx ⊢
    exact ⟨by linarith [hx.1, hR₁leRy], by linarith [hx.2, hR₁leRy]⟩
  · intro x y hx hy
    exact ⟨hle' y x (le_trans hy hR₂leRx) (le_trans hx hR₁leRy),
           heq' y x (le_trans hy hR₂leRx) (le_trans hx hR₁leRy)⟩
  · exact hbound

end Work.Drive.Mono
