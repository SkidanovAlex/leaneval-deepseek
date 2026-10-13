import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.ChoiceDefs
import Submission.Work.WilG1.Choice.Eff.Defs
import Submission.Work.WilG1.Choice.selSet_fibre
import Submission.Work.WilG1.Choice.cylDecomp_cell_of_mem
import Submission.Work.WilG4a.isCell_fiber
import Submission.Work.WilG5.Basic

set_option maxHeartbeats 1000000

namespace Work.WilG1.Choice.G1Sel

open Work.WilG1.Choice.Eff

/-- If the fibre of `K` over `l` is empty, then the fibre of `selOf K` over `l` is empty too.
Indeed every disjunct of the selection rule produces a point of the fibre — the first one
because `isAll` is nonempty, the third and fourth by their first conjunct — except the
"centre of symmetry" disjunct, which requires the centre to be *unique*; but an empty fibre
is symmetric about every real, so it admits no unique centre. -/
lemma selOf_fibre_eq_empty {p : ℕ} {K : Set (Fin (p + 1) → ℝ)} {l : Fin p → ℝ}
    (h : ¬ ∃ y : ℝ, Fin.snoc l y ∈ K) :
    {s : ℝ | Fin.snoc l s ∈ selOf K} = ∅ := by
  have hset : {s : ℝ | Fin.snoc l s ∈ selOf K}
      = {s : ℝ | Fin.snoc l s ∈ Work.WilG1.selSet K (Work.WilG1.projPar K)} := rfl
  rw [hset]
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hs
  rw [Work.WilG1.Choice.mem_selSet_snoc_iff] at hs
  obtain ⟨-, hrule⟩ := hs
  have hempty : ∀ y : ℝ, ¬ Work.WilG1.inFib K l y := fun y hy => h ⟨y, hy⟩
  rcases hrule with ⟨hall, -⟩ | ⟨-, c, -, huniq⟩ | ⟨hin, -⟩ | ⟨hin, -⟩
  · exact h ⟨0, hall 0⟩
  · have hcent : ∀ c' : ℝ,
        (∀ u : ℝ, Work.WilG1.inFib K l (c' + u) ↔ Work.WilG1.inFib K l (c' - u)) :=
      fun c' u => ⟨fun hh => absurd hh (hempty _), fun hh => absurd hh (hempty _)⟩
    have hc1 : c + 1 = c := huniq (c + 1) (hcent (c + 1))
    linarith
  · exact h ⟨s, hin⟩
  · exact h ⟨s, hin⟩

/-- The fibre over `l` of the selection set `selOf K` of a *cell* `K` is finite: it is either
empty, or a single point.  If the fibre of `K` is empty this is `selOf_fibre_eq_empty`;
otherwise `isCell_fiber` exhibits the fibre as a point or an `EReal` interval and
`selSet_fibre` shows that the selection rule picks exactly one point of it. -/
lemma fibre_selOf_finite {p : ℕ} {K : Set (Fin (p + 1) → ℝ)}
    (hcell : WilkiesDesign.IsCell (p + 1) K) (l : Fin p → ℝ) :
    ({s : ℝ | Fin.snoc l s ∈ selOf K}).Finite := by
  by_cases hfib : ∃ y : ℝ, Fin.snoc l y ∈ K
  · obtain ⟨y₀, hy₀⟩ := hfib
    obtain ⟨t, -, hsing⟩ :=
      Work.WilG1.Choice.selSet_fibre (K := K) (R := Work.WilG1.projPar K)
        ⟨y₀, hy₀⟩ ⟨y₀, hy₀⟩ (Work.WilG4a.isCell_fiber p hcell l)
    have hset : {s : ℝ | Fin.snoc l s ∈ selOf K}
        = {s : ℝ | Fin.snoc l s ∈ Work.WilG1.selSet K (Work.WilG1.projPar K)} := rfl
    rw [hset, hsing]
    exact Set.finite_singleton t
  · rw [selOf_fibre_eq_empty hfib]
    exact Set.finite_empty

/-- `minGraph X (sigmaOf C X)` is the graph of a function on the parameters whose fibre in
`X` is nonempty.

`sigmaOf C X = ⋃ κ ∈ C.filter (· ⊆ X), selSet κ (projPar κ)` (see `Choice/Eff/Defs.lean`), and
`minGraph X Sg = {z | (z (Fin.last p) = 0 ∧ ¬∃ t, Fin.snoc (Fin.init z) t ∈ X) ∨
  (z ∈ Sg ∧ ∀ t, Fin.snoc (Fin.init z) t ∈ Sg → z (Fin.last p) ≤ t)}`.

Proof strategy: for `z = Fin.snoc l t`, the first disjunct of `minGraph` contradicts `hne`, so
`Fin.snoc l t ∈ minGraph X (sigmaOf C X) ↔ Fin.snoc l t ∈ sigmaOf C X ∧ t` is the least element
of the `sigmaOf`-fibre over `l`. Nonemptiness: pick `t₀` with `Fin.snoc l t₀ ∈ X`; by
`cylDecomp_cell_of_mem` there is `κ ∈ C` with `κ ⊆ X` and `Fin.snoc l t₀ ∈ κ`, so `l ∈ projPar κ`,
`κ` is a cell (`hdec`), `isCell_fiber` gives the point/`IooE`-interval dichotomy for its fibre and
`selSet_fibre` produces a selected point of `selOf κ = selSet κ (projPar κ) ∩ κ ⊆ X`, hence an
element of `sigmaOf C X`. Finiteness: `selSet_fibre` says each relevant cell contributes at most
one point, so the `sigmaOf`-fibre is a finite nonempty set of reals and has a least element. -/
theorem minGraphFibreG1 {p : ℕ} {C : Finset (Set (Fin (p + 1) → ℝ))}
    {X : Set (Fin (p + 1) → ℝ)}
    (hdec : WilkiesDesign.IsCylDecomp (p + 1) C)
    (hadapt : ∀ κ ∈ C, κ ⊆ X ∨ Disjoint κ X) {l : Fin p → ℝ}
    (hne : ∃ t : ℝ, Fin.snoc l t ∈ X) :
    ∃! t : ℝ,
      Fin.snoc l t ∈ Work.WilG1.Choice.Eff.minGraph X (Work.WilG1.Choice.Eff.sigmaOf C X) := by
  -- For `z = Fin.snoc l t` the first disjunct of `minGraph` is excluded by `hne`, so `z` lies in
  -- `minGraph X (sigmaOf C X)` exactly when it is a minimal point of the `sigmaOf`-fibre over `l`.
  have hmem : ∀ t : ℝ, Fin.snoc l t ∈ minGraph X (sigmaOf C X) ↔
      (Fin.snoc l t ∈ sigmaOf C X ∧ ∀ s : ℝ, Fin.snoc l s ∈ sigmaOf C X → t ≤ s) := by
    intro t
    rw [mem_minGraph, Fin.init_snoc, Fin.snoc_last]
    exact ⟨fun h => h.elim (fun h1 => absurd hne h1.2) id, fun h => Or.inr h⟩
  -- Nonemptiness of the `sigmaOf`-fibre: a cell contained in `X` meets it.
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨κ, hκC, hκX, hκmem⟩ := cylDecomp_cell_of_mem hdec hadapt ht₀
  obtain ⟨t, htκ, hsing⟩ :=
    Work.WilG1.Choice.selSet_fibre (K := κ) (R := Work.WilG1.projPar κ)
      ⟨t₀, hκmem⟩ ⟨t₀, hκmem⟩ (Work.WilG4a.isCell_fiber p (hdec.1 κ hκC).1 l)
  have hselκ : Fin.snoc l t ∈ selOf κ := by
    have : t ∈ ({s : ℝ | Fin.snoc l s ∈ selOf κ}) := by
      rw [show {s : ℝ | Fin.snoc l s ∈ selOf κ}
            = {s : ℝ | Fin.snoc l s ∈ Work.WilG1.selSet κ (Work.WilG1.projPar κ)} from rfl,
        hsing]
      exact Set.mem_singleton t
    exact this
  have htSg : Fin.snoc l t ∈ sigmaOf C X :=
    mem_sigmaOf.mpr ⟨κ, hκC, hκX, hselκ, hκX htκ⟩
  -- Finiteness of the `sigmaOf`-fibre: it is contained in the union of the `selOf`-fibres of the
  -- finitely many cells of `C`, each of which is finite by `fibre_selOf_finite`.
  have hsub : {s : ℝ | Fin.snoc l s ∈ sigmaOf C X} ⊆
      ⋃ κ ∈ (C : Set (Set (Fin (p + 1) → ℝ))), {s : ℝ | Fin.snoc l s ∈ selOf κ} := by
    intro s hs
    obtain ⟨κ', hκ'C, -, hsel', -⟩ := mem_sigmaOf.mp hs
    exact Set.mem_biUnion hκ'C hsel'
  have hfin : ({s : ℝ | Fin.snoc l s ∈ sigmaOf C X}).Finite :=
    Set.Finite.subset
      ((Finset.finite_toSet C).biUnion (fun κ hκ => fibre_selOf_finite (hdec.1 κ hκ).1 l)) hsub
  -- A finite nonempty set of reals has a least element.
  obtain ⟨tmin, htminSg, htminle⟩ := hfin.exists_minimal ⟨t, htSg⟩
  have hleast : ∀ b : ℝ, Fin.snoc l b ∈ sigmaOf C X → tmin ≤ b := by
    intro b hb
    by_contra hlt
    exact absurd (htminle hb (le_of_lt (not_le.mp hlt))) hlt
  refine ⟨tmin, (hmem tmin).mpr ⟨htminSg, hleast⟩, ?_⟩
  -- Uniqueness: two minimal elements of the same fibre are equal.
  intro y hy
  obtain ⟨hySg, hyle⟩ := (hmem y).mp hy
  exact le_antisymm (hyle tmin htminSg) (hleast y hySg)

end Work.WilG1.Choice.G1Sel
