import Mathlib
import Submission.Work.RPB.B1a.HalfBallRegion
import Submission.Work.RPB.B1a.shearRegion_snd_lt
import Submission.Work.RPB.B1a.shearRegion_horiz_mem

/-!
# `Work.RPB.B1a.shearRegion_preconnected_of_mono`

The sheared half-disk region

`shearRegion P Q r = {p | 0 < p.2 ∧ (p.2 - P p.1)^2 + (Q p.1)^2 < r^2 ∧ p ∈ ball 0 (2r)}`

is preconnected, under the two hypotheses used in the B1a straightening argument:

* `hmono`: for every `y ∈ (0,r)` the function `x ↦ (y - P x)^2 + (Q x)^2` is monotone on
  `[0,2r]` and antitone on `[-2r,0]`; i.e. the "spine" point `x = 0` is the innermost point of
  every horizontal slice;
* `hnocap`: the curve `x ↦ (P x, Q x)` does not poke out of the disk of radius `r` above height
  `r`, which is what bounds the vertical coordinate of the region by `r`.

Assembly.  Write `S = shearRegion P Q r`.

1. (the "cap", `shearRegion_snd_lt`) Every point of `S` has `0 < p.2 < r`: from
   `(p.2 - P p.1)^2 + (Q p.1)^2 < r^2` one gets `|Q p.1| < r` and, with `|p.1| ≤ ‖p‖ < 2r`,
   `hnocap` applies and gives `p.2 < P p.1 + sqrt (r^2 - (Q p.1)^2) ≤ r`.
2. (`shearRegion_spine_mem`) Hence `(0, y) ∈ S` for every `y ∈ (0, r)`: this is the **spine**.
3. (`shearRegion_horiz_mem`) For `(x, y) ∈ S` and `z ∈ uIcc 0 x`, also `(z, y) ∈ S`: the whole
   horizontal segment from `(x,y)` to the spine point `(0,y)` stays inside `S`, by the monotonicity
   hypothesis at height `y ∈ (0,r)`.
4. Consequently each point `p = (x,y) ∈ S` lies in the "wedge"
   `shearSpineWedge r x y = shearVertSeg r y ∪ shearHorizSeg x y`, where `shearVertSeg r y` is the
   vertical segment `{0} × uIcc y (r/2)` through the spine and `shearHorizSeg x y` is the horizontal
   segment `uIcc 0 x × {y}`.  Each wedge is a union of two connected sets meeting at `(0,y)`, hence
   connected, and *all* wedges contain the common point `(0, r/2)`.  As `S` is the union of the
   wedges over `p ∈ S`, it is preconnected.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1a

open Set Metric

/-- The vertical segment at `x = 0` between the height `y` and the fixed height `r/2`. -/
def shearVertSeg (r y : ℝ) : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.1 = 0 ∧ z.2 ∈ Set.uIcc y (r / 2)}

/-- The horizontal segment at height `y` from `x = 0` to `x = x`. -/
def shearHorizSeg (x y : ℝ) : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.2 = y ∧ z.1 ∈ Set.uIcc 0 x}

/-- The "wedge" through the point `(x, y)`: the horizontal segment from `(x,y)` to the spine point
`(0,y)`, followed by the vertical spine segment from `(0,y)` to `(0, r/2)`. -/
def shearSpineWedge (r x y : ℝ) : Set (ℝ × ℝ) := shearVertSeg r y ∪ shearHorizSeg x y

/-- The spine point `(0, y)` lies in the region for `0 < y < r`. -/
theorem shearRegion_spine_mem (P Q : ℝ → ℝ) {r y : ℝ}
    (hP0 : P 0 = 0) (hQ0 : Q 0 = 0) (hy : 0 < y) (hyr : y < r) :
    (((0 : ℝ), y) : ℝ × ℝ) ∈ shearRegion P Q r := by
  rw [mem_shearRegion]
  refine ⟨hy, ?_, ?_⟩
  · rw [hP0, hQ0]
    nlinarith
  · have hnorm : ‖(((0 : ℝ), y) : ℝ × ℝ)‖ = y := by
      simp [Prod.norm_def, Real.norm_eq_abs, abs_of_pos hy, max_eq_right (le_of_lt hy)]
    rw [Metric.mem_ball]
    simp only [dist_zero_right, hnorm]
    linarith

private lemma uIcc_subset_Ioo_of_mem {a b c d : ℝ} (ha : a ∈ Set.Ioo c d) (hb : b ∈ Set.Ioo c d) :
    Set.uIcc a b ⊆ Set.Ioo c d := by
  intro t ht
  rw [Set.mem_uIcc] at ht
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨lt_of_lt_of_le ha.1 h1, lt_of_le_of_lt h2 hb.2⟩
  · exact ⟨lt_of_lt_of_le hb.1 h1, lt_of_le_of_lt h2 ha.2⟩

lemma shearVertSeg_eq_image (r y : ℝ) :
    shearVertSeg r y = (fun t : ℝ => (((0 : ℝ), t) : ℝ × ℝ)) '' Set.uIcc y (r / 2) := by
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨z.2, h2, Prod.ext h1.symm rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨rfl, ht⟩

lemma shearHorizSeg_eq_image (x y : ℝ) :
    shearHorizSeg x y = (fun t : ℝ => ((t, y) : ℝ × ℝ)) '' Set.uIcc 0 x := by
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨z.1, h2, Prod.ext rfl h1.symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨rfl, ht⟩

lemma isPreconnected_shearVertSeg (r y : ℝ) : IsPreconnected (shearVertSeg r y) := by
  rw [shearVertSeg_eq_image]
  exact isPreconnected_uIcc.image _ (by fun_prop)

lemma isPreconnected_shearHorizSeg (x y : ℝ) : IsPreconnected (shearHorizSeg x y) := by
  rw [shearHorizSeg_eq_image]
  exact isPreconnected_uIcc.image _ (by fun_prop)

lemma isPreconnected_shearSpineWedge (r x y : ℝ) : IsPreconnected (shearSpineWedge r x y) :=
  IsPreconnected.union (((0 : ℝ), y) : ℝ × ℝ) ⟨rfl, Set.left_mem_uIcc⟩ ⟨rfl, Set.left_mem_uIcc⟩
    (isPreconnected_shearVertSeg r y) (isPreconnected_shearHorizSeg x y)

theorem shearRegion_preconnected_of_mono (P Q : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (hP0 : P 0 = 0) (hQ0 : Q 0 = 0)
    (hmono : ∀ y ∈ Set.Ioo 0 r,
      MonotoneOn (fun x => (y - P x) ^ 2 + (Q x) ^ 2) (Set.Icc 0 (2 * r)) ∧
      AntitoneOn (fun x => (y - P x) ^ 2 + (Q x) ^ 2) (Set.Icc (-2 * r) 0))
    (hnocap : ∀ x, |x| ≤ 2 * r → |Q x| < r → P x + Real.sqrt (r ^ 2 - (Q x) ^ 2) ≤ r) :
    IsPreconnected (Work.RPB.B1a.shearRegion P Q r) := by
  have hhalf : r / 2 ∈ Set.Ioo (0 : ℝ) r := ⟨by linarith, by linarith⟩
  have hspine : ∀ y, 0 < y → y < r → (((0 : ℝ), y) : ℝ × ℝ) ∈ shearRegion P Q r :=
    fun y hy hyr => shearRegion_spine_mem P Q hP0 hQ0 hy hyr
  -- every point of `S` has second coordinate in `(0, r)`, and the horizontal segment from the
  -- point to the spine point at the same height stays in `S`
  have hpiece : ∀ p : ↥(shearRegion P Q r),
      shearSpineWedge r p.1.1 p.1.2 ⊆ shearRegion P Q r := by
    rintro ⟨⟨x, y⟩, hp⟩ z hz
    have hy0 : 0 < y := (mem_shearRegion.mp hp).1
    have hyr : y < r := shearRegion_snd_lt P Q hr hnocap hp
    have hyIo : y ∈ Set.Ioo (0 : ℝ) r := ⟨hy0, hyr⟩
    rcases hz with ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩
    · obtain ⟨hz2a, hz2b⟩ := uIcc_subset_Ioo_of_mem hyIo hhalf hz2
      have h := hspine z.2 hz2a hz2b
      rwa [show z = (((0 : ℝ), z.2) : ℝ × ℝ) from Prod.ext hz1 rfl]
    · have h := shearRegion_horiz_mem P Q hr hmono hp hyr hz2
      rwa [show z = (z.1, y) from Prod.ext rfl hz1]
  -- all the wedges contain the common point `(0, r/2)`
  have hbase : ∀ p : ↥(shearRegion P Q r),
      (((0 : ℝ), r / 2) : ℝ × ℝ) ∈ shearSpineWedge r p.1.1 p.1.2 :=
    fun _ => Or.inl ⟨rfl, Set.right_mem_uIcc⟩
  -- `S` is the union of the wedges through its points
  have hUnion : (⋃ p : ↥(shearRegion P Q r), shearSpineWedge r p.1.1 p.1.2) =
      shearRegion P Q r :=
    Subset.antisymm (Set.iUnion_subset fun p => hpiece p)
      (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Or.inr ⟨rfl, Set.right_mem_uIcc⟩⟩)
  rw [← hUnion]
  exact isPreconnected_iUnion ⟨_, Set.mem_iInter.mpr fun p => hbase p⟩
    fun p => isPreconnected_shearSpineWedge r p.1.1 p.1.2

end Work.RPB.B1a
