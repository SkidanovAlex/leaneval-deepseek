import Mathlib
import Submission.Work.WilG4c.AlBadParDefs
import Submission.Work.WilG1.Cell.thin_union

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-! ## Elementary auxiliary lemmas for `AlBadParThin` -/

/-- A set that lies in the graph of a function `g` contains no ball. -/
theorem no_ball_of_graph {k : ℕ} {g : (Fin k → ℝ) → ℝ} {s : Set (Fin (k + 1) → ℝ)}
    (hs : ∀ y ∈ s, y (Fin.last k) = g (Fin.init y)) :
    ¬ ∃ (y₀ : Fin (k + 1) → ℝ) (ε : ℝ), 0 < ε ∧
      ∀ y : Fin (k + 1) → ℝ, dist y y₀ < ε → y ∈ s := by
  rintro ⟨y₀, ε, hε, hball⟩
  have hy0s : y₀ ∈ s := hball y₀ (by rw [dist_self]; exact hε)
  have hy0 : y₀ (Fin.last k) = g (Fin.init y₀) := hs y₀ hy0s
  have hdist : dist (Fin.snoc (Fin.init y₀) (y₀ (Fin.last k) + ε / 2) : Fin (k + 1) → ℝ) y₀ < ε := by
    have h := Work.WilG1.Cell.dist_snoc_last (Fin.init y₀) (y₀ (Fin.last k) + ε / 2)
      (y₀ (Fin.last k))
    rw [Fin.snoc_init_self y₀] at h
    rw [h, show y₀ (Fin.last k) + ε / 2 - y₀ (Fin.last k) = ε / 2 from by ring,
      abs_of_pos (by linarith)]
    linarith
  have hys : (Fin.snoc (Fin.init y₀) (y₀ (Fin.last k) + ε / 2) : Fin (k + 1) → ℝ) ∈ s :=
    hball _ hdist
  have h2 : (Fin.snoc (Fin.init y₀) (y₀ (Fin.last k) + ε / 2) : Fin (k + 1) → ℝ) (Fin.last k)
      = g (Fin.init (Fin.snoc (Fin.init y₀) (y₀ (Fin.last k) + ε / 2) : Fin (k + 1) → ℝ)) :=
    hs _ hys
  rw [Fin.snoc_last, Fin.init_snoc, ← hy0] at h2
  linarith

/-- A graph cell has no bad parameters. -/
theorem BadFib_empty_of_graph {p k : ℕ} {κ : Set (Fin (p + (k + 1)) → ℝ)}
    {g : (Fin (p + k) → ℝ) → ℝ}
    (hκ : ∀ z, z ∈ κ → z (Fin.last (p + k)) = g (Fin.init z)) :
    BadFib p (k + 1) κ = ∅ := by
  ext l
  constructor
  · rintro ⟨y₀, ε, hε, hball⟩
    exact (no_ball_of_graph (g := fun y' => g (Fin.append l y'))
      (s := fibSet p (k + 1) κ l) (fun y hy => by
        have h2 := hκ (Fin.append l y) hy
        rw [append_last, init_append] at h2
        exact h2)
      ⟨y₀, ε, hε, fun y hy => hball y hy⟩).elim
  · intro h
    rw [Set.mem_empty_iff_false] at h
    exact h.elim

/-- The bad-fibre parameters of any set inject into those of its projection: a ball in the
`(q+1)`-dimensional fibre forces a ball in the `q`-dimensional fibre of `projLast`. -/
theorem BadFib_projLast_subset {p q : ℕ} {κ : Set (Fin (p + (q + 1)) → ℝ)} :
    BadFib p (q + 1) κ ⊆ BadFib p q (projLast κ) := by
  rintro l ⟨y₀, ε, hε, hball⟩
  refine ⟨Fin.init y₀, ε, hε, ?_⟩
  intro y' hy'
  let Y : Fin (q + 1) → ℝ := Fin.snoc y' (y₀ (Fin.last q))
  have hY : Y = Fin.snoc y' (y₀ (Fin.last q)) := rfl
  have hdist : dist Y y₀ < ε := by
    have h := Work.WilG1.Cell.dist_snoc_snoc y' (Fin.init y₀) (y₀ (Fin.last q))
    rw [Fin.snoc_init_self y₀] at h
    rw [hY, h]
    exact hy'
  have hmem : apPt p (q + 1) l Y ∈ κ := hball Y hdist
  refine ⟨(apPt p (q + 1) l Y) (Fin.last (p + q)), ?_⟩
  have hinit : Fin.init (apPt p (q + 1) l Y) = Fin.append l y' := by
    have hX : apPt p (q + 1) l Y = Fin.append l ((Fin.snoc y' (y₀ (Fin.last q)) : Fin (q + 1) → ℝ)) := by
      rw [apPt_apply]
    rw [hX]
    exact init_append_snoc l y' (y₀ (Fin.last q))
  have heq : Fin.snoc (Fin.append l y') ((apPt p (q + 1) l Y) (Fin.last (p + q)))
      = apPt p (q + 1) l Y := by
    rw [← hinit]
    exact Fin.snoc_init_self (apPt p (q + 1) l Y)
  rw [heq]
  exact hmem

/-- A finite cover of a nonempty open set by sets each of which is nowhere dense as soon as it
has empty interior must have a member with nonempty interior. -/
theorem exists_mem_interior_nonempty_of_cover {X : Type*} [TopologicalSpace X] {ι : Type*}
    {u : Finset ι} {s : ι → Set X} {B : Set X}
    (hB : IsOpen B) (hBne : B.Nonempty) (hcov : B ⊆ ⋃ i ∈ u, s i)
    (hgood : ∀ i ∈ u, interior (s i) = ∅ → IsNowhereDense (s i)) :
    ∃ i ∈ u, (interior (s i)).Nonempty := by
  by_contra h
  have hemp : ∀ i ∈ u, interior (s i) = ∅ := by
    intro i hi
    by_contra hne
    exact h ⟨i, hi, Set.nonempty_iff_ne_empty.mpr hne⟩
  have hnd : interior (closure (⋃ i ∈ u, s i)) = ∅ :=
    IsNowhereDense.biUnion (fun i hi => hgood i hi (hemp i hi))
  have hsub : B ⊆ interior (closure (⋃ i ∈ u, s i)) := by
    rw [← IsOpen.interior_eq hB]
    exact (interior_mono subset_closure).trans (interior_mono (closure_mono hcov))
  rw [hnd] at hsub
  exact hBne.ne_empty (Set.subset_empty_iff.mp hsub)

/-- The base of a band cell with empty interior itself has empty interior. -/
theorem band_base_interior_empty {m : ℕ} {C : Set (Fin m → ℝ)} {a b : (Fin m → ℝ) → EReal}
    (ha : ContinuousOn a C) (hb : ContinuousOn b C) (hab : ∀ x ∈ C, a x < b x)
    (hint : interior {z : Fin (m + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
      ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z)} = ∅) :
    interior C = ∅ := by
  by_contra h
  have hne : (interior C).Nonempty := Set.nonempty_iff_ne_empty.mpr h
  have hband := Work.WilG1.Cell.interior_band_nonempty ha hb hab hne
  rw [hint] at hband
  exact Set.not_nonempty_empty hband

/-- The zero-dimensional fibre statement: a ball in `ℝ^0` is automatic, so the bad-fibre
parameters of `V ⊆ ℝ^{p+0}` are exactly `V`. -/
theorem BadFib_zero {p : ℕ} (V : Set (Fin (p + 0) → ℝ)) : BadFib p 0 V = V := by
  ext l
  constructor
  · rintro ⟨y₀, ε, hε, h⟩
    have h1 : Fin.append l y₀ ∈ V := h y₀ (by rw [dist_self]; exact hε)
    have hy : y₀ = Fin.elim0 := funext (fun i => i.elim0)
    rw [hy, Fin.append_elim0] at h1
    simpa using h1
  · intro hl
    refine ⟨Fin.elim0, 1, one_pos, ?_⟩
    intro y _
    have hy : y = Fin.elim0 := funext (fun i => i.elim0)
    rw [hy, Fin.append_elim0]
    simpa using hl

end Work.WilG4c
