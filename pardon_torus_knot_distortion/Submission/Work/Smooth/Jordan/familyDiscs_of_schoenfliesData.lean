import Mathlib
import Submission.Work.Smooth.Jordan.Family
import Submission.Work.Topology.Classical.Defs
import Submission.Work.Topology.Classical.nested_discs_of_schoenfliesData

/-!
# A `SchoenfliesData` is a `FamilyDiscs`

The structure `Work.Topology.Classical.SchoenfliesData A ι c` is the conclusion of
Jordan–Schoenflies *on a sphere* `A ⊆ ℝ³` for a finite family of pairwise disjoint simple closed
curves `c i`: two embedded discs `e i`, `e' i` per curve, covering `A` and meeting along the curve,
and a nesting rank.  The structure `Work.Smooth.Jordan.FamilyDiscs A ι c` is the *usable* form of
the same picture for the innermost arguments: one spanning disc `disc i` per curve, its boundary
being `c i`, together with the two nesting properties

* `nested`: a curve meeting the interior of the disc of another has smaller rank;
* `inside_subset`: a curve meeting the interior of the disc of another has its own whole disc
  contained in that disc.

Here we take the disc of `i` to be `e i`, the first of the two discs of the `SchoenfliesData`.

* `nested` is immediate from the corresponding field of `SchoenfliesData`;
* `inside_subset` is the standard-position statement: if the curve `c j` meets the interior of the
  disc `e i`, then the *open* discs are nested (`Work.Topology.Classical.nested_discs_of_schoenfliesData`),
  and since the *closed* disc `range (e i)` is compact and the boundary of `range (e j)` lies in the
  closure of the open disc of `j`, the closed disc `range (e j)` is contained in `range (e i)`
  (`range_e_subset_of_meets_interior`).

The auxiliary fact that the image of the closed disc is contained in the closure of the image of the
open disc, `range_subset_closure_image_openDisc`, is the elementary density of the open unit ball in
the closed unit ball.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.Jordan

noncomputable section

/-- **The image of the closed model disc is contained in the closure of the image of the open
disc.**  The open unit ball is dense in the closed unit ball, so for every continuous
`f : 𝔻 → ℝ³` the points `f z` with `‖z‖ < 1` approach each boundary point `f z` with `‖z‖ = 1`.

(Concretely: `closure {z : 𝔻 | ‖z‖ < 1} = univ`, and `image_closure_subset_closure_image`.) -/
theorem range_subset_closure_image_openDisc {A : Set R3} {ι : Type} [Fintype ι]
    {c : ι → ℝ → R3} (D : Work.Topology.Classical.SchoenfliesData A ι c) (k : ι) :
    Set.range (D.e k) ⊆ closure (D.e k '' {z : Disc | ‖(z : ℂ)‖ < 1}) := by
  have hclosure : closure ({z : Disc | ‖(z : ℂ)‖ < 1} : Set Disc) = Set.univ := by
    have hind : Topology.IsInducing (Subtype.val : Disc → ℂ) := Topology.IsInducing.subtypeVal
    have h := hind.closure_eq_preimage_closure_image {z : Disc | ‖(z : ℂ)‖ < 1}
    rw [h, Set.eq_univ_iff_forall]
    intro z
    have himg : (Subtype.val '' {z : Disc | ‖(z : ℂ)‖ < 1} : Set ℂ) = Metric.ball 0 1 := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      · intro hw
        refine ⟨⟨w, ?_⟩, by simpa [Metric.mem_ball, dist_eq_norm] using hw, rfl⟩
        simpa [Metric.mem_closedBall, dist_eq_norm] using
          le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
    rw [himg, closure_ball (0 : ℂ) one_ne_zero]
    exact z.2
  calc Set.range (D.e k) = D.e k '' (Set.univ : Set Disc) := Set.image_univ.symm
    _ = D.e k '' closure ({z : Disc | ‖(z : ℂ)‖ < 1} : Set Disc) := by rw [hclosure]
    _ ⊆ closure (D.e k '' {z : Disc | ‖(z : ℂ)‖ < 1}) :=
        image_closure_subset_closure_image (D.e k).continuous

/-- **The closed disc of an inner curve lies in the closed disc of the outer one.**  If the curve
`c j` meets the *interior* of the disc `e i` of a `SchoenfliesData`, then `c j` lies wholly inside
the disc of `i`, and so does the disc it spans: `range (e j) ⊆ range (e i)`.

The open discs are nested by `Work.Topology.Classical.nested_discs_of_schoenfliesData`; the closed
disc `range (e i)` is closed, and every point of `range (e j)` is a limit of points of the open disc
of `j` (`range_subset_closure_image_openDisc`), hence lies in `range (e i)`. -/
theorem range_e_subset_of_meets_interior {A : Set R3} {ι : Type} [Fintype ι]
    {c : ι → ℝ → R3} (D : Work.Topology.Classical.SchoenfliesData A ι c) {i j : ι}
    (hint : ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e i z ∈ Set.range (c j)) :
    Set.range (D.e j) ⊆ Set.range (D.e i) := by
  by_cases hij : i = j
  · subst hij
    exact subset_rfl
  have hopen := Work.Topology.Classical.nested_discs_of_schoenfliesData D hij hint
  refine (range_subset_closure_image_openDisc D j).trans (closure_minimal ?_ ?_)
  · rintro x ⟨z, hz, rfl⟩
    have hmem : (⟨D.e j z, D.mem j z⟩ : A) ∈
        {x : A | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e i z = (x : R3)} := hopen ⟨z, hz, rfl⟩
    obtain ⟨z', _, hz'⟩ := hmem
    exact ⟨z', hz'⟩
  · exact (isCompact_range (D.e i).continuous).isClosed

/-- **The conclusion of Jordan–Schoenflies, in the form of a family of discs with nested discs.**

Let `c i` (`i` in a finite type) be pairwise disjoint simple closed curves on a set `A ⊆ ℝ³` which
carry a `SchoenfliesData` — that is, `A` is a `2`-sphere (or the boundary of Pardon's box) and the
curves are in standard position, each bounding two complementary embedded discs.  Then the family
bounds spanning discs which are *nested*: a curve meeting the interior of the disc of another lies
inside it, and the ranks decrease.

This is the passage from the classical statement (`SchoenfliesData`, in the vocabulary of the
Jordan–Schoenflies chapter) to the datum which the innermost arguments consume (`FamilyDiscs`, in
the vocabulary of the smooth Jordan chapter). -/
theorem familyDiscs_of_schoenfliesData {A : Set LeanEval.KnotTheory.PardonDistortion.R3} {ι : Type} [Fintype ι] {c : ι → ℝ → LeanEval.KnotTheory.PardonDistortion.R3} (h : Work.Topology.Classical.SchoenfliesData A ι c) (hs : ∀ i : ι, IsSimpleClosedCurveOn A (c i)) (hd : Pairwise fun i j : ι => Disjoint (Set.range (c i)) (Set.range (c j))) : Nonempty (FamilyDiscs A ι c) := by
  refine ⟨?_⟩
  exact
    { simple := hs
      disjoint := hd
      disc := h.e
      disc_inj := h.inj
      disc_boundary := h.boundary
      disc_mem := h.mem
      rank := h.rank
      nested := fun i j _ hmem => h.nested i j hmem
      inside_subset := fun i j hmem => range_e_subset_of_meets_interior h hmem }

end

end Work.Smooth.Jordan
