import Mathlib
import Submission.Work.WilE7.Endgame.E2Aux
import Submission.Work.WilE7.DecompDefs
import Submission.Work.CoreStep.projTop_graph_union_cyl
import Submission.Work.WilE7.CoreStep.bandCell_subset_or_disjoint_of_interior

namespace Work.WilE7.Endgame

set_option autoImplicit false
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

/-! ## Elementary cell lemmas

The cell family `cfs b TT` of a level family `TT` over a base set `b` consists of the graph cells
`gr b (lvl TT · i)` of the `K+2` levels and of the band cells `bd b (lvl TT · i) (lvl TT · i.succ)`
between consecutive levels.  The two facts below are the whole combinatorial content of the cell
compatibility: a graph cell over a level agrees with (or misses) the graph of any one level
function, and a band cell misses every graph cell. -/

/-- Graph cells over the same base set coincide as soon as the two level functions agree on it. -/
theorem gr_congr {n : ℕ} {C : Set (Fin n → ℝ)} {f g : (Fin n → ℝ) → ℝ}
    (h : ∀ x ∈ C, f x = g x) : Work.WilE7.gr C f = Work.WilE7.gr C g := by
  ext z
  rw [Work.WilE7.gr, Set.mem_ofPred_eq, Work.WilE7.gr, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hz⟩; exact ⟨hx, hz.trans (h _ hx)⟩
  · rintro ⟨hx, hz⟩; exact ⟨hx, hz.trans (h _ hx).symm⟩

/-- **A cell of the level family is contained in the graph of a level function, or disjoint from
it.**  If `f` agrees on `b` with one of the levels `lvl TT · i` of the family, then `gr b f` is one
of the graph cells of `cfs b TT`; since the levels are strictly increasing and `TT` is bounded by
`1`, the cells of `cfs b TT` are pairwise disjoint, so every cell either is that graph cell or
misses it.

This is the combinatorial heart of `E2_cells_compat`: it produces the compatibility of the level
cells with the graph of an arbitrary sheet (or level) function, and thereby with a union of such
graphs. -/
theorem cell_subset_or_disjoint_gr {n K : ℕ} {b : Set (Fin n → ℝ)}
    (TT : Fin K → (Fin n → ℝ) → ℝ)
    (hmono : ∀ x ∈ b, StrictMono fun i : Fin K => TT i x)
    (hbnd : ∀ x ∈ b, ∀ i : Fin K, |TT i x| < 1)
    (f : (Fin n → ℝ) → ℝ)
    (hf : ∃ i : Fin (K + 2), ∀ x ∈ b, f x = Work.WilE7.lvl TT x i) :
    ∀ κ ∈ Work.WilE7.cfs b TT, κ ⊆ Work.WilE7.gr b f ∨ Disjoint κ (Work.WilE7.gr b f) := by
  obtain ⟨i0, hi0⟩ := hf
  intro κ hκ
  rw [Work.WilE7.mem_cfs] at hκ
  rcases hκ with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · -- graph cell of the level `i`
    by_cases h : i = i0
    · left
      have hfun : (fun x => Work.WilE7.lvl TT x i) = fun x => Work.WilE7.lvl TT x i0 := by
        funext x; rw [h]
      rw [hfun]
      exact le_of_eq (gr_congr (fun x hx => (hi0 x hx).symm))
    · right
      rw [Set.disjoint_left]
      intro z hz1 hz2
      rw [Work.WilE7.gr, Set.mem_ofPred_eq] at hz1 hz2
      obtain ⟨hx, he1⟩ := hz1
      obtain ⟨-, he2⟩ := hz2
      have heq : Work.WilE7.lvl TT (Fin.init z) i = Work.WilE7.lvl TT (Fin.init z) i0 :=
        he1.symm.trans (he2.trans (hi0 (Fin.init z) hx))
      exact h ((Work.WilE7.strictMono_lvl (hmono (Fin.init z) hx)
        (fun k => hbnd (Fin.init z) hx k)).injective heq)
  · -- band cell between the levels `i` and `i+1`
    right
    rw [Set.disjoint_left]
    intro z hzB hzgr
    rw [Work.WilE7.bd, Set.mem_ofPred_eq] at hzB
    obtain ⟨hx, h1, h2⟩ := hzB
    rw [Work.WilE7.gr, Set.mem_ofPred_eq] at hzgr
    obtain ⟨-, hlast⟩ := hzgr
    have ht : z (Fin.last n) = Work.WilE7.lvl TT (Fin.init z) i0 := by
      rw [hlast, hi0 (Fin.init z) hx]
    exact (Work.WilE7.CoreStep.lvl_ne_of_between TT hmono
      (fun i x hx => hbnd x hx i) hx h1 h2) i0 ht

theorem E2_cells_compat {n m r K : ℕ} {b : Set (Fin n → ℝ)}
    (S : Fin r → Stratum 0 (n + (m + 1)))
    (k : Fin r → ℕ) (s : (t : Fin r) → Fin (k t) → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ (t : Fin r) (j : Fin (k t)) (x : Fin n → ℝ), x ∈ b →
      Fin.append x (s t j x) ∈ absSet (S t))
    (hcov : ∀ (t : Fin r), ∀ z ∈ absSet (S t), projFirst n (m + 1) z ∈ b →
      ∃ j : Fin (k t), s t j (projFirst n (m + 1) z) = projSnd n (m + 1) z)
    (hbnd : ∀ (t : Fin r) (j : Fin (k t)) (x : Fin n → ℝ), x ∈ b → |(s t j x) (Fin.last m)| ≤ 1)
    (hcls : ∀ (t : Fin r) (j : Fin (k t)), (∀ x ∈ b, (s t j x) (Fin.last m) = 1) ∨
      (∀ x ∈ b, (s t j x) (Fin.last m) = -1) ∨ (∀ x ∈ b, |(s t j x) (Fin.last m)| < 1))
    (hdich : ∀ (t t' : Fin r) (j : Fin (k t)) (j' : Fin (k t')),
      (∃ x ∈ b, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m)) →
      ∀ x ∈ b, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m))
    (K : ℕ) (TT : Fin K → (Fin n → ℝ) → ℝ)
    (hTTmono : ∀ x ∈ b, StrictMono fun i : Fin K => TT i x)
    (hTTbnd : ∀ x ∈ b, ∀ i : Fin K, |TT i x| < 1)
    (hTTsheet : ∀ i : Fin K, ∃ (t : Fin r) (j : Fin (k t)),
      ∀ x ∈ b, TT i x = (s t j x) (Fin.last m))
    (hlevel : ∀ (t : Fin r) (j : Fin (k t)),
      (∃ i : Fin K, ∀ x ∈ b, TT i x = (s t j x) (Fin.last m)) ∨
      (∀ x ∈ b, (s t j x) (Fin.last m) = 1) ∨
      (∀ x ∈ b, (s t j x) (Fin.last m) = -1))
    (t₀ : Fin r) :
    (∀ κ ∈ Work.WilE7.cfs b TT, ∀ (t : Fin r) (j : Fin (k t)),
      κ ⊆ Work.WilE7.gr b (fun x => (s t j x) (Fin.last m)) ∨
        Disjoint κ (Work.WilE7.gr b (fun x => (s t j x) (Fin.last m)))) ∧
      (∀ κ ∈ Work.WilE7.cfs b TT, κ ⊆ projTopSet (S t₀) ∨ Disjoint κ (projTopSet (S t₀))) := by
  -- The vertical coordinate of a sheet is one of the levels of `TT` on `b` (case 1), or the
  -- constant level `1` (case 2) resp. `-1` (case 3), which are the extreme levels `lvl TT · _`.
  have hlevel_of : ∀ (t : Fin r) (j : Fin (k t)),
      ∃ i : Fin (K + 2), ∀ x ∈ b, (s t j x) (Fin.last m) = Work.WilE7.lvl TT x i := by
    intro t j
    rcases hlevel t j with ⟨i, hi⟩ | h1 | hm1
    · exact ⟨Fin.succ (Fin.castSucc i), fun x hx => by
        rw [Work.WilE7.lvl_succ]; exact (hi x hx).symm⟩
    · exact ⟨Fin.last (K + 1), fun x hx => by
        rw [Work.WilE7.lvl_last]; exact h1 x hx⟩
    · exact ⟨0, fun x hx => by
        rw [Work.WilE7.lvl_zero]; exact hm1 x hx⟩
  refine ⟨?_, ?_⟩
  · -- Part 1: compatibility with each sheet graph, from the combinatorial core.
    intro κ hκ t j
    exact cell_subset_or_disjoint_gr TT hTTmono hTTbnd _
      (hlevel_of t j) κ hκ
  · -- Part 2: the `π_{n+1}`-projection of `S t₀` over `b` is the union of the sheet graphs.
    have hunion : projTopSet (S t₀) ∩ Work.WilE7.cyl b =
        ⋃ j : Fin (k t₀), Work.WilE7.gr b (fun x => (s t₀ j x) (Fin.last m)) := by
      rw [Work.WilE7.CoreStep.projTopSet]
      simpa only [Work.WilE7.CoreStep.vertCoord] using
        Work.CoreStep.projTop_graph_union_cyl (S t₀) b (s t₀) (hsub t₀) (hcov t₀)
    intro κ hκ
    have hcyl : κ ⊆ Work.WilE7.cyl b := Work.WilE7.cfs_subset_cyl hTTmono hTTbnd κ hκ
    have hdich : ∀ j : Fin (k t₀),
        κ ⊆ Work.WilE7.gr b (fun x => (s t₀ j x) (Fin.last m)) ∨
          Disjoint κ (Work.WilE7.gr b (fun x => (s t₀ j x) (Fin.last m))) :=
      fun j => cell_subset_or_disjoint_gr TT hTTmono hTTbnd _ (hlevel_of t₀ j) κ hκ
    by_cases hex : ∃ j : Fin (k t₀),
        κ ⊆ Work.WilE7.gr b (fun x => (s t₀ j x) (Fin.last m))
    · -- `κ` is one of the graphs of the union, hence inside the projection of `S t₀`.
      left
      obtain ⟨j, hj⟩ := hex
      intro z hz
      have hzu : z ∈ ⋃ j : Fin (k t₀),
          Work.WilE7.gr b (fun x => (s t₀ j x) (Fin.last m)) :=
        Set.mem_iUnion.mpr ⟨j, hj hz⟩
      rw [← hunion] at hzu
      exact hzu.1
    · -- otherwise `κ` meets no graph of the union, hence misses the projection.
      right
      rw [Set.disjoint_left]
      intro z hzκ hzproj
      have hzu : z ∈ ⋃ j : Fin (k t₀),
          Work.WilE7.gr b (fun x => (s t₀ j x) (Fin.last m)) := by
        rw [← hunion]
        exact ⟨hzproj, hcyl hzκ⟩
      rw [Set.mem_iUnion] at hzu
      obtain ⟨j, hzj⟩ := hzu
      rcases hdich j with h | h
      · exact hex ⟨j, h⟩
      · exact (Set.disjoint_left.mp h) hzκ hzj

end Work.WilE7.Endgame
