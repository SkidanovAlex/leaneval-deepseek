import Mathlib

namespace Work.L62

/-- **A uniform bound for a single chosen preimage.**  Let `X ⊆ ℂ` be open, `f : ℂ → ℂ`, `K ⊆ ℂ`
compact, and suppose (i) `f` is *open on `X`*: the image of every open subset of `X` is open in `ℂ`;
(ii) every `y ∈ K` is attained by `f` at some point of `X`.  Then a single `M` bounds a *chosen*
preimage of every `y ∈ K`.  (The bound is on a chosen preimage, not on all preimages: that is what
the compactness of `K` buys, via the openness of `f` at a preimage of an accumulation point of a
putative bad sequence `yₙ`.) -/
theorem uniform_preimage_bound {X K : Set ℂ} {f : ℂ → ℂ} (hX : IsOpen X)
    (hopen : ∀ s ⊆ X, IsOpen s → IsOpen (f '' s)) (hK : IsCompact K)
    (hsurj : ∀ y ∈ K, ∃ x ∈ X, f x = y) :
    ∃ M : ℝ, 0 < M ∧ ∀ y ∈ K, ∃ x ∈ X, f x = y ∧ ‖x‖ ≤ M := by
  classical
  -- For every `y ∈ K` choose a preimage `c y ∈ X`, and a radius `r y` with `ball (c y) (r y) ⊆ X`.
  have hpre : ∀ y : K, ∃ x : ℂ, x ∈ X ∧ f x = (y : ℂ) := fun y => hsurj y.1 y.2
  choose c hcX hcf using hpre
  have hr : ∀ y : K, ∃ r : ℝ, 0 < r ∧ Metric.ball (c y) r ⊆ X := fun y =>
    Metric.isOpen_iff.mp hX (c y) (hcX y)
  choose r hrpos hrsub using hr
  -- The images `f '' ball (c y) (r y)` are open and cover `K`.
  have hcover : K ⊆ ⋃ y : K, f '' Metric.ball (c y) (r y) := by
    intro y hy
    refine Set.mem_iUnion.mpr ⟨⟨y, hy⟩, c ⟨y, hy⟩, ?_, hcf ⟨y, hy⟩⟩
    rw [Metric.mem_ball, dist_self]
    exact hrpos ⟨y, hy⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : K => f '' Metric.ball (c y) (r y))
    (fun y => hopen _ (hrsub y) Metric.isOpen_ball) hcover
  refine ⟨max 1 (∑ y ∈ t, (‖c y‖ + r y)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro y hy
  -- `y` lies in one of the finitely many open images.
  have hy' : y ∈ ⋃ y' ∈ t, f '' Metric.ball (c y') (r y') := ht hy
  rw [Set.mem_iUnion] at hy'
  obtain ⟨y', hy'⟩ := hy'
  rw [Set.mem_iUnion] at hy'
  obtain ⟨hy't, hmem⟩ := hy'
  obtain ⟨x, hxball, hxf⟩ := hmem
  have hxX : x ∈ X := hrsub y' hxball
  have hxd : dist x (c y') < r y' := Metric.mem_ball.mp hxball
  have hbound : ‖x‖ < ‖c y'‖ + r y' := by
    have hsplit : c y' + (x - c y') = x := by ring
    have h1 : ‖x‖ ≤ ‖c y'‖ + dist x (c y') := by
      calc ‖x‖ = ‖c y' + (x - c y')‖ := by rw [hsplit]
        _ ≤ ‖c y'‖ + ‖x - c y'‖ := norm_add_le _ _
        _ = ‖c y'‖ + dist x (c y') := by rw [dist_eq_norm]
    linarith
  have hle : ‖c y'‖ + r y' ≤ ∑ y ∈ t, (‖c y‖ + r y) := by
    refine Finset.single_le_sum (f := fun y : K => ‖c y‖ + r y) (fun i _ => ?_) hy't
    have := hrpos i
    have := norm_nonneg (c i)
    linarith
  exact ⟨x, hxX, hxf, le_trans hbound.le (le_trans hle (le_max_right _ _))⟩

end Work.L62
