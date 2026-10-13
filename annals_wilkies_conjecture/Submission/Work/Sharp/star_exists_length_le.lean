/-
  Sharp: the `*`-pieces of a `*`-set of format `≤ F` and degree `≤ D` can be chosen so that
  there are at most `D + 1` of them (without changing the set, the format bound or the degree
  bound).

  The mathematical content is that a piece of degree `0` is either empty or the whole closed
  cube `[-1,1]ⁿ` (`Work.WilE8.Star.starPiece_set_eq_empty_or_cube`: a basic set of degree `0`
  has no atoms at all, so it holds on the whole cube, and the connected component of a point of
  the (preconnected) cube is the cube).  Hence all the degree-`0` pieces of a list can be
  replaced by a single piece, the cube piece `Work.WilE8.cubePiece n`, and the remaining pieces
  all have degree `≥ 1`, so there are at most `D` of them.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Star.starPiece_set_eq_empty_or_cube

namespace Work.Sharp

open WilkiesDesign WilkiesDesign.E

/-- Combinatorial core of `star_exists_length_le` (kept local; the same statement is also
proved in `Submission.Work.Sharp.list_sets_le`).

Let `L` be a finite list of "pieces", `S a` the set attached to a piece `a` and `g a : ℕ` its
degree.  Suppose every degree-`0` piece has `S a = ∅` or `S a = z`, and suppose `a₀` is a piece of
degree `0` with `S a₀ = z`.  Then the union of the sets of `L` is also the union of the sets of a
list `M` consisting only of `a₀` and of elements of `L`, whose length is at most the total degree
of `L` plus one and whose total degree is at most that of `L`.

Indeed, writing `Lp` for the sublist of the pieces of positive degree, either some degree-`0`
piece of `L` is nonempty — then its set is `z`, and `M := a₀ :: Lp` works, the single extra
`a₀` absorbing *all* degree-`0` pieces — or every degree-`0` piece of `L` is empty and
`M := Lp` works.  In both cases the pieces kept have degree `≥ 1`, hence number at most
`(L.map g).sum`. -/
theorem list_sets_le_aux {α : Type*} {Z : Type*} (L : List α) (S : α → Set Z) (g : α → ℕ)
    (z : Set Z) (a₀ : α) (ha₀ : g a₀ = 0) (hS₀ : S a₀ = z)
    (h : ∀ a, g a = 0 → S a = ∅ ∨ S a = z) :
    ∃ M : List α, (⋃ a ∈ L, S a) = (⋃ a ∈ M, S a) ∧ (∀ a ∈ M, a = a₀ ∨ a ∈ L) ∧
      M.length ≤ (L.map g).sum + 1 ∧ (M.map g).sum ≤ (L.map g).sum := by
  classical
  -- the sublist of the pieces of positive degree
  set Lp : List α := L.filter (fun a => decide (g a ≠ 0)) with hLp
  have hLpsub : Lp.Sublist L := by rw [hLp]; exact List.filter_sublist
  have hLpL : ∀ a ∈ Lp, a ∈ L := fun a ha => hLpsub.subset ha
  have hLpmem : ∀ a ∈ Lp, g a ≠ 0 := by
    intro a ha
    have h2 : a ∈ L ∧ decide (g a ≠ 0) = true := by rwa [hLp, List.mem_filter] at ha
    exact of_decide_eq_true h2.2
  have hLpmem' : ∀ a ∈ L, g a ≠ 0 → a ∈ Lp := by
    intro a haL hga
    rw [hLp, List.mem_filter]
    exact ⟨haL, decide_eq_true_eq.mpr hga⟩
  have hLpsum : (Lp.map g).sum ≤ (L.map g).sum :=
    (hLpsub.map g).sum_le_sum (fun a _ => Nat.zero_le a)
  have hLplen : Lp.length ≤ (L.map g).sum := by
    have h2 := List.length_le_sum_of_one_le (Lp.map g) (fun i hi => by
      rw [List.mem_map] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      exact Nat.one_le_iff_ne_zero.mpr (hLpmem a ha))
    simpa using h2.trans hLpsum
  by_cases hz : ∃ a ∈ L, g a = 0 ∧ S a ≠ ∅
  · -- some degree-`0` piece is nonempty, hence equal to `z`: add the cube piece `a₀`
    obtain ⟨c, hcL, hgc, hSne⟩ := hz
    have hSc : S c = z := by
      rcases h c hgc with h0 | h0
      · exact absurd h0 hSne
      · exact h0
    refine ⟨a₀ :: Lp, ?_, ?_, ?_, ?_⟩
    · refine Set.Subset.antisymm ?_ ?_
      · intro x hx
        simp only [Set.mem_iUnion, exists_prop] at hx ⊢
        obtain ⟨a, haL, hxa⟩ := hx
        by_cases hga : g a = 0
        · rcases h a hga with h0 | h0
          · rw [h0] at hxa; exact absurd hxa (Set.notMem_empty x)
          · exact ⟨a₀, List.mem_cons_self, by rw [hS₀]; rw [← h0]; exact hxa⟩
        · exact ⟨a, List.mem_cons_of_mem a₀ (hLpmem' a haL hga), hxa⟩
      · intro x hx
        simp only [Set.mem_iUnion, exists_prop] at hx ⊢
        obtain ⟨a, ha, hxa⟩ := hx
        rcases List.mem_cons.mp ha with rfl | hap
        · exact ⟨c, hcL, by rw [hSc, ← hS₀]; exact hxa⟩
        · exact ⟨a, hLpL a hap, hxa⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | hap
      · exact Or.inl rfl
      · exact Or.inr (hLpL a hap)
    · have : (a₀ :: Lp).length = Lp.length + 1 := List.length_cons
      omega
    · have h2 : ((a₀ :: Lp).map g).sum = g a₀ + (Lp.map g).sum := List.sum_cons
      omega
  · -- every degree-`0` piece is empty: the positive-degree pieces already cover everything
    have hz' : ∀ a ∈ L, g a = 0 → S a = ∅ := by
      intro a haL hga
      by_contra hne
      exact hz ⟨a, haL, hga, hne⟩
    refine ⟨Lp, ?_, ?_, ?_, ?_⟩
    · refine Set.Subset.antisymm ?_ ?_
      · intro x hx
        simp only [Set.mem_iUnion, exists_prop] at hx ⊢
        obtain ⟨a, haL, hxa⟩ := hx
        by_cases hga : g a = 0
        · rw [hz' a haL hga] at hxa; exact absurd hxa (Set.notMem_empty x)
        · exact ⟨a, hLpmem' a haL hga, hxa⟩
      · intro x hx
        simp only [Set.mem_iUnion, exists_prop] at hx ⊢
        obtain ⟨a, ha, hxa⟩ := hx
        exact ⟨a, hLpL a ha, hxa⟩
    · intro a ha; exact Or.inr (hLpL a ha)
    · omega
    · exact hLpsum

theorem star_exists_length_le {F D n : ℕ} {Y : Set (Fin n → ℝ)}
    (h : WilkiesDesign.E.Star F D n Y) :
    ∃ L : List (WilkiesDesign.E.StarPiece n),
      Y = (⋃ P ∈ L, WilkiesDesign.E.StarPiece.set P) ∧ L.length ≤ D + 1 ∧
        (∀ P ∈ L, P.X.fmt ≤ F) ∧ (L.map fun P => P.X.deg).sum ≤ D := by
  classical
  obtain ⟨L, hY, hfmt, hdeg⟩ := h
  rcases eq_or_ne L [] with rfl | hLne
  · -- no pieces at all: nothing to do
    exact ⟨[], hY, by simp, by simp, by simp⟩
  · -- a piece of the list has format `≥ n`, so the format budget `F` admits the cube piece
    obtain ⟨P₀, hP₀⟩ := List.exists_mem_of_ne_nil L hLne
    have hnF : n ≤ F := by
      have h1 := hfmt P₀ hP₀
      have h2 : n ≤ P₀.X.fmt := by
        show n ≤ (n + P₀.m) + P₀.X.r
        omega
      omega
    -- replace all the pieces of degree `0` by the single cube piece
    obtain ⟨M, heq, hMsub, hlen, hsum⟩ :=
      list_sets_le_aux L (fun P : WilkiesDesign.E.StarPiece n => P.set) (fun P => P.X.deg)
        (WilkiesDesign.E.cubeC n) (Work.WilE8.cubePiece n)
        (by simp [Work.WilE8.cubePiece, Work.WilE8.cubeSemiPf, WilkiesDesign.E.SemiPf.deg,
          WilkiesDesign.E.Basic.deg])
        (Work.WilE8.cubePiece_set n)
        (fun P hP => Work.WilE8.Star.starPiece_set_eq_empty_or_cube P hP)
    refine ⟨M, ?_, ?_, ?_, ?_⟩
    · rw [hY, heq]
    · omega
    · intro P hP
      rcases hMsub P hP with hEq | hPL
      · rw [hEq]
        simpa [Work.WilE8.cubePiece, Work.WilE8.cubeSemiPf, WilkiesDesign.E.SemiPf.fmt] using hnF
      · exact hfmt P hPL
    · omega

end Work.Sharp
