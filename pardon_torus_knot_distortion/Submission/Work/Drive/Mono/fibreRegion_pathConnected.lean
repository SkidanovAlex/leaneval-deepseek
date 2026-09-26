import Mathlib

namespace Work.Drive.Mono

/-- **The region between two continuous graphs over an interval is path-connected** (the lead's
"fibre lemma" for the gate analysis of the tilted sweep).  Let `f g : ℝ → ℝ` be continuous with
`f x < g x` on the open interval `Ioo a b`, and let `a < b` (which the first draft of this statement
missed: without it the region is empty and `IsPathConnected ∅` is false — the reviews found that).  Then

  `{(x, y) ∈ ℝ × ℝ | x ∈ Ioo a b ∧ f x < y ∧ y < g x}`

is path-connected.  A clean proof: the map `(x, t) ↦ (x, f x + t * (g x - f x))` is a homeomorphism
from `Ioo a b × Ioo 0 1` onto the region (the inverse `(x,y) ↦ (x, (y - f x) / (g x - f x))` is
continuous because `g x - f x` is positive and continuous on `Ioo a b`), and a product of
path-connected spaces is path-connected (using `isPathConnected_iff` / `IsPathConnected.prod` and the
path-connectedness of the two intervals).  The docstring sketch of the first draft ("move horizontally
at the middle height") is wrong and should not be followed. -/
theorem fibreRegion_pathConnected {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a < b) (hfg : ∀ x ∈ Set.Ioo a b, f x < g x) :
    IsPathConnected {p : ℝ × ℝ | p.1 ∈ Set.Ioo a b ∧ f p.1 < p.2 ∧ p.2 < g p.1} := by
  -- The rectangle `Ioo a b × Ioo 0 1` is path-connected (product of two nonempty intervals).
  have hbox : IsPathConnected (Set.Ioo a b ×ˢ Set.Ioo (0:ℝ) 1) :=
    IsPathConnected.prod (Convex.isPathConnected (convex_Ioo a b) (Set.nonempty_Ioo.mpr hab))
      (Convex.isPathConnected (convex_Ioo (0:ℝ) 1)
        (Set.nonempty_Ioo.mpr (by norm_num : (0:ℝ) < 1)))
  -- The "vertical interpolation" map, continuous.
  have hΦcont : Continuous (fun p : ℝ × ℝ => (p.1, f p.1 + p.2 * (g p.1 - f p.1))) :=
    Continuous.prodMk continuous_fst
      ((hf.comp continuous_fst).add
        (continuous_snd.mul ((hg.comp continuous_fst).sub (hf.comp continuous_fst))))
  -- It maps the rectangle exactly onto the region: surjective since `g x - f x > 0` on `Ioo a b`.
  have himage : (fun p : ℝ × ℝ => (p.1, f p.1 + p.2 * (g p.1 - f p.1))) ''
      (Set.Ioo a b ×ˢ Set.Ioo (0:ℝ) 1)
      = {p : ℝ × ℝ | p.1 ∈ Set.Ioo a b ∧ f p.1 < p.2 ∧ p.2 < g p.1} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hx, ht⟩ := hq
      have hden : (0:ℝ) < g q.1 - f q.1 := sub_pos.mpr (hfg q.1 hx)
      refine ⟨hx, ?_, ?_⟩
      · have : 0 < q.2 * (g q.1 - f q.1) := mul_pos ht.1 hden
        linarith
      · have h : q.2 * (g q.1 - f q.1) < 1 * (g q.1 - f q.1) :=
          mul_lt_mul_of_pos_right ht.2 hden
        linarith
    · intro hp
      obtain ⟨hx, h1, h2⟩ := hp
      have hden : (0:ℝ) < g p.1 - f p.1 := sub_pos.mpr (hfg p.1 hx)
      refine ⟨(p.1, (p.2 - f p.1) / (g p.1 - f p.1)), ⟨hx, ?_, ?_⟩, ?_⟩
      · exact div_pos (sub_pos.mpr h1) hden
      · rw [div_lt_one hden]; linarith
      · refine Prod.ext rfl ?_
        show f p.1 + (p.2 - f p.1) / (g p.1 - f p.1) * (g p.1 - f p.1) = p.2
        rw [div_mul_cancel₀ _ (ne_of_gt hden)]
        ring
  -- A continuous image of a path-connected set is path-connected.
  rw [← himage]
  exact hbox.image hΦcont

end Work.Drive.Mono
