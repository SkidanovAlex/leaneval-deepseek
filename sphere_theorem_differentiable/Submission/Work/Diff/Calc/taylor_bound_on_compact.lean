import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform second order Taylor bound on a compact set

Let `f : E → F` be `C²` on an open set `s`, and let `K ⊆ s` be compact.  Then the second order
Taylor remainder `f (x + h) - f x - fderiv ℝ f x h` is `O(‖h‖ ^ 2)`, uniformly for `x ∈ K` and for
small `h`.

The proof has two ingredients.

* **Local data.**  At each point `x ∈ s` the function `z ↦ fderiv ℝ f z` is Lipschitz on a
  neighbourhood of `x`.  Indeed `fderiv ℝ f` is `C¹` on the open set `s`, so it is differentiable
  there with continuous derivative `fderiv ℝ (fderiv ℝ f)`; the mean value theorem on a ball then
  produces a Lipschitz neighbourhood (this is the lemma
  `Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt`).
* **The estimate on a ball.**  If `fderiv ℝ f` is `C`-Lipschitz on a ball around `y`, then the mean
  value theorem for `f` itself, in the "derivative close to a fixed linear map" form
  `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`, gives
  `‖f (y + h) - f y - fderiv ℝ f y h‖ ≤ C ‖h‖ ^ 2`.

Finally, compactness of `K` turns the pointwise data into uniform data: `IsCompact.elim_finite_subcover`
produces a finite subcover, and one takes the minimum of the finitely many radii and the maximum of
the finitely many constants.

## Main result

* `Work.Diff.Calc.taylor_bound_on_compact`
-/

namespace Work.Diff.Calc

/-- Pointwise form of the second order Taylor estimate: for `x` in an open set `s` on which `f` is
`C²`, there are `r > 0` and `M ≥ 0` such that for all `y` with `‖y - x‖ ≤ r` and all `h` with
`‖h‖ ≤ r` the second order Taylor remainder of `f` at `y` in direction `h` is at most
`M * ‖h‖ ^ 2`. -/
lemma taylor_bound_local_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ 2 f s) (x : E) (hx : x ∈ s) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ y, ‖y - x‖ ≤ r → ∀ h, ‖h‖ ≤ r →
        ‖f (y + h) - f y - fderiv ℝ f y h‖ ≤ M * ‖h‖ ^ 2 := by
  have hdf : DifferentiableOn ℝ f s := hf.differentiableOn (by norm_num)
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ f) s := hf.fderiv_of_isOpen hs (by norm_num)
  have hdfd : DifferentiableOn ℝ (fderiv ℝ f) s := hfd.differentiableOn (by norm_num)
  have hc0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ f)) s := hfd.fderiv_of_isOpen hs (by norm_num)
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ f)) s := hc0.continuousOn
  obtain ⟨r0, hr0, hr0'⟩ := Metric.isOpen_iff.mp hs x hx
  set K : NNReal := ‖fderiv ℝ (fderiv ℝ f) x‖₊ + 1 with hK
  have hder : ∀ᶠ y in nhdsWithin x (Metric.ball x r0),
      HasFDerivWithinAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) (Metric.ball x r0) y := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((hdfd.differentiableAt (hs.mem_nhds (hr0' hy))).hasFDerivAt).hasFDerivWithinAt
  have hcontx : ContinuousWithinAt (fderiv ℝ (fderiv ℝ f)) (Metric.ball x r0) x :=
    (hcont.continuousAt (hs.mem_nhds hx)).continuousWithinAt
  obtain ⟨t, ht, hLip⟩ :=
    (convex_ball x r0).exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt (𝕜 := ℝ)
      hder hcontx K (by rw [hK]; exact lt_add_one _)
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhdsWithin_iff.mp ht
  refine ⟨min ε r0 / 4, by positivity, (K : ℝ), by positivity, ?_⟩
  intro y hy h hh
  have hρ : 0 < min ε r0 := lt_min hε hr0
  have hsub : Metric.ball x (min ε r0) ⊆ t := by
    intro z hz
    exact hεt ⟨Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left _ _)),
      Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _))⟩
  have hLip' : LipschitzOnWith K (fderiv ℝ f) (Metric.ball x (min ε r0)) := hLip.mono hsub
  have hyρ : y ∈ Metric.ball x (min ε r0) := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  have hseg : ∀ z ∈ segment ℝ y (y + h), z ∈ Metric.ball x (min ε r0) := by
    intro z hz
    have h1 : ‖z - y‖ ≤ ‖h‖ := by
      simpa using norm_sub_le_of_mem_segment (x := y) (z := y + h) hz
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖z - x‖ ≤ ‖z - y‖ + ‖y - x‖ := by
          rw [show z - x = (z - y) + (y - x) by abel]; exact norm_add_le _ _
      _ ≤ min ε r0 / 4 + min ε r0 / 4 := add_le_add (le_trans h1 hh) hy
      _ < min ε r0 := by linarith
  have hbdd : ∀ z ∈ segment ℝ y (y + h), ‖fderiv ℝ f z - fderiv ℝ f y‖ ≤ (K : ℝ) * ‖h‖ := by
    intro z hz
    have h1 := (lipschitzOnWith_iff_norm_sub_le.mp hLip') (hseg z hz) hyρ
    have h2 : ‖z - y‖ ≤ ‖h‖ := by
      simpa using norm_sub_le_of_mem_segment (x := y) (z := y + h) hz
    calc ‖fderiv ℝ f z - fderiv ℝ f y‖ ≤ (K : ℝ) * ‖z - y‖ := h1
      _ ≤ (K : ℝ) * ‖h‖ := by gcongr
  have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ)
    (f := f) (f' := fun z => fderiv ℝ f z) (φ := fderiv ℝ f y) (C := (K : ℝ) * ‖h‖)
    (fun z hz => ((hdf.differentiableAt (hs.mem_nhds (hr0' (Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp (hseg z hz)) (min_le_right _ _)))))).hasFDerivAt).hasFDerivWithinAt)
    (fun z hz => hbdd z hz)
    (convex_segment y (y + h)) (left_mem_segment ℝ y (y + h)) (right_mem_segment ℝ y (y + h))
  rw [add_sub_cancel_left] at hmvt
  calc ‖f (y + h) - f y - fderiv ℝ f y h‖ ≤ ((K : ℝ) * ‖h‖) * ‖h‖ := hmvt
    _ = (K : ℝ) * ‖h‖ ^ 2 := by ring

theorem taylor_bound_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (s : Set E) (K : Set E)
    (hs : IsOpen s) (hK : IsCompact K) (hKs : K ⊆ s) (hf : ContDiffOn ℝ 2 f s) :
    ∃ (δ M : ℝ), 0 < δ ∧ 0 ≤ M ∧ ∀ x ∈ K, ∀ h : E, ‖h‖ ≤ δ →
      ‖f (x + h) - f x - fderiv ℝ f x h‖ ≤ M * ‖h‖ ^ 2 := by
  have hlocal : ∀ x, x ∈ K → ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ y, ‖y - x‖ ≤ r → ∀ h, ‖h‖ ≤ r →
        ‖f (y + h) - f y - fderiv ℝ f y h‖ ≤ M * ‖h‖ ^ 2 :=
    fun x hx => taylor_bound_local_data f hs hf x (hKs hx)
  by_cases hKne : K.Nonempty
  · choose r hr M hM hloc using hlocal
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : ↥K => Metric.ball (x : E) (r x x.prop))
      (fun _ => Metric.isOpen_ball)
      (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hr y hy)⟩)
    have htne : t.Nonempty := by
      obtain ⟨y, hy⟩ := hKne
      have hmem := ht hy
      rw [Set.mem_iUnion] at hmem
      obtain ⟨x, hx⟩ := hmem
      rw [Set.mem_iUnion] at hx
      exact ⟨x, hx.1⟩
    refine ⟨t.inf' htne (fun x : ↥K => r x x.prop), t.sup' htne (fun x : ↥K => M x x.prop),
      ?_, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro i hi
      exact hr i i.prop
    · obtain ⟨x0, hx0⟩ := htne
      exact le_trans (hM x0 x0.prop) (Finset.le_sup' (f := fun x : ↥K => M x x.prop) hx0)
    · intro y hyK h hh
      obtain ⟨x, hxt, hyx⟩ : ∃ x : ↥K, x ∈ t ∧ y ∈ Metric.ball (x : E) (r x x.prop) := by
        have hmem := ht hyK
        rw [Set.mem_iUnion] at hmem
        obtain ⟨x, hx⟩ := hmem
        rw [Set.mem_iUnion] at hx
        exact ⟨x, hx.1, hx.2⟩
      have hyx' : ‖y - x‖ < r x x.prop := by
        rw [Metric.mem_ball, dist_eq_norm] at hyx; exact hyx
      have hδle : t.inf' htne (fun x : ↥K => r x x.prop) ≤ r x x.prop :=
        Finset.inf'_le (f := fun x : ↥K => r x x.prop) hxt
      have hMle : M x x.prop ≤ t.sup' htne (fun x : ↥K => M x x.prop) :=
        Finset.le_sup' (f := fun x : ↥K => M x x.prop) hxt
      have hhr : ‖h‖ ≤ r x x.prop := le_trans hh hδle
      exact (hloc x x.prop y (le_of_lt hyx') h hhr).trans
        (mul_le_mul_of_nonneg_right hMle (sq_nonneg _))
  · rw [Set.not_nonempty_iff_eq_empty] at hKne
    exact ⟨1, 0, one_pos, le_refl 0, fun x hx => absurd hx (by simp [hKne])⟩

end Work.Diff.Calc
