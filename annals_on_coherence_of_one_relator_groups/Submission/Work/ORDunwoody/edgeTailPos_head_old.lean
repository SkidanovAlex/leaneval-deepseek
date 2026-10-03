import Mathlib
import Submission.Work.ORDunwoody.colour_collapsed

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley

/-! ## The first vertex of `edgeTailPos`

`edgeTailPos D a j` is the list of vertices visited after `(a, ∗)` when the positive generator
edge `j` is traversed from `a`.  Its structure is

* a single old vertex `(a * genE (j,true), ∗)` when the generator is collapsed (`L = 0`);
* otherwise the pattern point of the first cell followed by the old vertex at the far end of
  the first cell, and so on, so its head is always a *pattern point* (`Sum.inr`).

Consequently a hypothesis that the head of `edgeTailPos` is an *old* vertex (`Sum.inl`) can only
be satisfied in the collapsed case, which is the key case distinction below. -/

/-- `List.finRange n` is nonempty for `n ≠ 0`, so its head is some `k : Fin n`. -/
theorem exists_head?_finRange_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∃ k : Fin n, (List.finRange n).head? = some k := by
  cases n with
  | zero => exact absurd rfl hn
  | succ m => exact ⟨⟨0, Nat.succ_pos m⟩, by simp [List.finRange_succ]⟩

/-- If every block `F k` of a `flatMap` over `List.finRange n` starts with `H k`, then the
`flatMap` (for `n ≠ 0`) starts with `H k` for some `k`. -/
theorem exists_head?_flatMap_finRange {β : Type*} {n : ℕ} (hn : n ≠ 0)
    (F : Fin n → List β) (H : Fin n → β) (hF : ∀ k, (F k).head? = some (H k)) :
    ∃ p, ((List.finRange n).flatMap F).head? = some (H p) := by
  obtain ⟨k, hk⟩ := exists_head?_finRange_of_ne_zero hn
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp hk
  rw [hrest, List.flatMap_cons, List.head?_append, hF k]
  exact ⟨k, rfl⟩

/-- For a non-collapsed generator, the traversal of the positive generator edge starts at a
pattern point. -/
theorem edgeTailPos_head_inr {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a : G) (j : Fin P.n)
    (hL : D.L (j, true) ≠ 0) :
    ∃ p : Dunwoody.MidV D, (Dunwoody.edgeTailPos D a j).head? = some (Sum.inr p) := by
  rw [Dunwoody.edgeTailPos, if_neg hL]
  obtain ⟨p, hp⟩ := exists_head?_flatMap_finRange hL
    (fun k : Fin (D.L (j, true)) =>
      ([Sum.inr (⟨a, ⟨j, k⟩⟩ : Dunwoody.MidV D),
        Sum.inl (Dunwoody.pos D a j (k + 1))] : List (Dunwoody.Vertex D)))
    (fun k => (Sum.inr (⟨a, ⟨j, k⟩⟩ : Dunwoody.MidV D) : Dunwoody.Vertex D))
    (fun k => rfl)
  exact ⟨⟨a, ⟨j, p⟩⟩, hp⟩

theorem edgeTailPos_head_old {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a : G) (j : Fin P.n)
    (b : Work.ORDunwoody.Dunwoody.BaseV D)
    (h : (Work.ORDunwoody.Dunwoody.edgeTailPos D a j).head? =
      some (Sum.inl b : Work.ORDunwoody.Dunwoody.Vertex D)) :
    Work.ORDunwoody.Dunwoody.colour D (a, (Sum.inl () : Work.ORDunwoody.Dunwoody.BaseV₀ D)) = Work.ORDunwoody.Dunwoody.colour D b := by
  rcases eq_or_ne (D.L (j, true)) 0 with hL | hL
  · -- collapsed generator: the head is `(a * genE (j,true), ∗)`, which has the same colour
    -- as `(a, ∗)` because the collapsed generator fixes the base point `t₀`
    rw [Dunwoody.edgeTailPos, if_pos hL] at h
    simp only [List.head?_cons, Option.some.injEq, Sum.inl.injEq] at h
    rw [← h, Dunwoody.colour_base, Dunwoody.colour_base, mul_smul,
      genE_smul_eq_self_of_L_eq_zero (D := D) (j, true) hL]
  · -- non-collapsed generator: the head is a pattern point, so `h` is absurd
    obtain ⟨p, hp⟩ := edgeTailPos_head_inr (D := D) a j hL
    rw [hp] at h
    simp only [Option.some.injEq] at h
    exact (Sum.inr_ne_inl h).elim

end Work.ORDunwoody
