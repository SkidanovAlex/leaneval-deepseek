/-
  Area C2 (WilC2): the real side of `C2_models_ominimal`.

  If every fibre `{t | φ(c, t)}` of a parametric family `φ` is a union of at most `N`
  preconnected subsets of `ℝ`, then `SliceGood (N+1) φ ℝ`: the fibre can be "cut" by
  `N+1` cut points so that it is convex as soon as one stays between two consecutive cut
  points (no cut point strictly in between).

  Construction: for every member `I` of the family put the candidate cut point

      cand I := (sSup I + sInf {x ∈ U | sSup I < x}) / 2

  i.e. the midpoint of the gap immediately to the right of the right end of `I`.  Some
  `I` whose supremum is the left end of the gap containing `w` produces a candidate
  strictly inside `(u,v)`, and there are at most `N` candidates, padded to `N+1` with a
  dummy point.
-/
import Mathlib
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.Convert
import Submission.Work.WilC2.exists_cut_mem
import Submission.Work.WilC2.exists_monotone_covers

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-- **The real side of C2.** Uniform finiteness of the fibres of `φ` over `ℝ` (each fibre is a
union of at most `N` preconnected sets) produces cut points exhibiting the fibre as a union of
at most `2(N+1)+1` convex pieces, i.e. `SliceGood (N+1) φ ℝ`. -/
theorem realSide_sliceGood {n : ℕ} (φ : ParamFormula n) {N : ℕ}
    (hfib : ∀ c : Fin n → ℝ, ∃ s : Finset (Set ℝ), s.card ≤ N ∧ (∀ I ∈ s, IsPreconnected I) ∧
      {t : ℝ | φ.Realize (Sum.elim c (fun _ => t))} = ⋃₀ (s : Set (Set ℝ))) :
    SliceGood (N + 1) φ ℝ := by
  intro c
  obtain ⟨s, hcard, hpre, hS⟩ := hfib c
  -- the finite set of candidate cut points (the extra `0` makes it nonempty)
  let Z : Finset ℝ :=
    s.image (fun I : Set ℝ => (sSup I + sInf {x ∈ ⋃₀ (s : Set (Set ℝ)) | sSup I < x}) / 2)
      ∪ {0}
  have hZcard : Z.card ≤ N + 1 := by
    have h1 : (s.image (fun I : Set ℝ =>
        (sSup I + sInf {x ∈ ⋃₀ (s : Set (Set ℝ)) | sSup I < x}) / 2)).card ≤ N :=
      le_trans Finset.card_image_le hcard
    have h2 : Z.card ≤ (s.image (fun I : Set ℝ =>
        (sSup I + sInf {x ∈ ⋃₀ (s : Set (Set ℝ)) | sSup I < x}) / 2)).card + 1 := by
      have := Finset.card_union_le (s.image (fun I : Set ℝ =>
        (sSup I + sInf {x ∈ ⋃₀ (s : Set (Set ℝ)) | sSup I < x}) / 2)) ({0} : Finset ℝ)
      simpa only [Z, Finset.card_singleton] using this
    omega
  obtain ⟨y, hmono, hycovers⟩ := exists_monotone_covers (K := N + 1) (Z := Z) hZcard
  refine ⟨y, fun i j hij => hmono hij, ?_⟩
  intro u w v hu hv hb hcut
  by_contra hw
  have huU : u ∈ ⋃₀ (s : Set (Set ℝ)) := by
    rw [← hS]; exact hu
  have hvU : v ∈ ⋃₀ (s : Set (Set ℝ)) := by
    rw [← hS]; exact hv
  have hwU : w ∉ ⋃₀ (s : Set (Set ℝ)) := by
    rw [← hS]; exact hw
  rcases hb with ⟨huw, hwv⟩ | ⟨hvw, hwu⟩
  · obtain ⟨I, hIs, hlt1, hlt2⟩ := exists_cut_mem hpre huU hvU huw hwv hwU
    have hmem : (sSup I + sInf {x ∈ ⋃₀ (s : Set (Set ℝ)) | sSup I < x}) / 2 ∈ Z :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨I, hIs, rfl⟩))
    obtain ⟨i, hi⟩ := hycovers _ hmem
    exact hcut i (by rw [hi]; exact Or.inl ⟨hlt1, hlt2⟩)
  · obtain ⟨I, hIs, hlt1, hlt2⟩ := exists_cut_mem hpre hvU huU hvw hwu hwU
    have hmem : (sSup I + sInf {x ∈ ⋃₀ (s : Set (Set ℝ)) | sSup I < x}) / 2 ∈ Z :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨I, hIs, rfl⟩))
    obtain ⟨i, hi⟩ := hycovers _ hmem
    exact hcut i (by rw [hi]; exact Or.inr ⟨hlt1, hlt2⟩)

end Work.WilC2
