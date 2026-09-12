import Mathlib
import Submission.Szemeredi.CornersRemovalD
import Submission.Szemeredi.Removal.Main2

/-!
# The partite corollary of the hypergraph removal lemma

We deduce `Szemeredi.SimplexRemovalProgrammeD d` (for `d ≥ 1`) from the σ-algebra form of the
hypergraph removal lemma (`Szemeredi.Removal.hypergraph_removal_complete`), by encoding a
partite `(d+1)`-partite `d`-uniform hypergraph `E : Fin (d+1) → Finset (Fin d → G)` as a
family of `coord e`-measurable subsets of `G^{Fin (d+1)}`.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Szemeredi

variable {d : ℕ} {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The parts of the hypergraph system: all equal to `G`. -/
abbrev VG (d : ℕ) (G : Type*) : Fin (d+1) → Type _ := fun _ => G

/-- The `Pt`-level encoding of a partite hypergraph: `x` is in the lift of `E` at the face `e`
when the `j`-face of `x` is an edge, where `e = univ.erase j`. -/
noncomputable def Fsimp (E : Fin (d+1) → Finset (Fin d → G)) :
    Finset (Fin (d+1)) → Finset (Pt (VG d G)) :=
  fun e => Finset.univ.filter (fun x => ∀ j : Fin (d+1), e = Finset.univ.erase j → faceD j x ∈ E j)

theorem mem_Fsimp {E : Fin (d+1) → Finset (Fin d → G)} {e : Finset (Fin (d+1))}
    {x : Pt (VG d G)} :
    x ∈ Fsimp E e ↔ ∀ j : Fin (d+1), e = Finset.univ.erase j → faceD j x ∈ E j := by
  simp [Fsimp]

theorem faceD_congr {j : Fin (d+1)} {x y : Pt (VG d G)}
    (h : ∀ i : Fin (d+1), i ≠ j → y i = x i) : faceD j y = faceD j x := by
  funext k
  exact h (Fin.succAbove j k) (Fin.succAbove_ne j k)

theorem Fsimp_isMeas (E : Fin (d+1) → Finset (Fin d → G)) (e : Finset (Fin (d+1))) :
    (coord (V := VG d G) e).IsMeas (Fsimp E e) := by
  rw [coord_isMeas_iff]
  intro x y hxy
  have key : ∀ j : Fin (d+1), e = Finset.univ.erase j → faceD j y = faceD j x := by
    intro j hj
    refine faceD_congr (fun i hij => ?_)
    exact hxy i (by rw [hj]; exact Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  rw [mem_Fsimp, mem_Fsimp]
  constructor
  · intro h j hj
    rw [← key j hj]
    exact h j hj
  · intro h j hj
    rw [key j hj]
    exact h j hj

theorem erase_inj {j j' : Fin (d+1)}
    (h : (Finset.univ.erase j : Finset (Fin (d+1))) = Finset.univ.erase j') : j = j' := by
  by_contra hne
  have h1 : j ∈ Finset.univ.erase j' := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩
  rw [← h] at h1
  exact (Finset.mem_erase.mp h1).1 rfl

theorem Fsimp_of_erase (E : Fin (d+1) → Finset (Fin d → G)) (j : Fin (d+1)) :
    Fsimp E (Finset.univ.erase j)
      = Finset.univ.filter (fun x : Pt (VG d G) => faceD j x ∈ E j) := by
  ext x
  rw [mem_Fsimp, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨Finset.mem_univ _, h j rfl⟩
  · intro h j' hj'
    have hjj : j' = j := by
      by_contra hne
      have h1 : j' ∈ Finset.univ.erase j :=
        Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j'⟩
      rw [hj'] at h1
      exact (Finset.mem_erase.mp h1).1 rfl
    rw [hjj]
    exact h.2

/-- For a `d`-element subset of `Fin (d+1)` there is a unique omitted index. -/
theorem exists_erase_of_card (e : Finset (Fin (d+1))) (he : e.card = d) :
    ∃! j : Fin (d+1), e = Finset.univ.erase j := by
  have hcompl : eᶜ.card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcompl
  have hje : e = Finset.univ.erase j := by
    ext i
    rw [Finset.mem_erase]
    constructor
    · intro hi
      refine ⟨?_, Finset.mem_univ i⟩
      intro hji
      rw [hji] at hi
      have hc : j ∈ eᶜ := by rw [hj]; exact Finset.mem_singleton_self j
      exact Finset.mem_compl.mp hc hi
    · intro h
      by_contra hie
      have hc : i ∈ eᶜ := Finset.mem_compl.mpr hie
      rw [hj, Finset.mem_singleton] at hc
      exact h.1 hc
  refine ⟨j, hje, ?_⟩
  intro j' hj'
  rw [hje] at hj'
  exact (erase_inj (j := j) (j' := j') hj').symm

/-- The product of the lifted indicators equals one exactly on the simplices. -/
theorem prod_Fsimp_pos (E : Fin (d+1) → Finset (Fin d → G)) (x : Pt (VG d G))
    (h : IsSimplexD E x) :
    ∏ e ∈ HdC d, SigAlg.indicator (Fsimp E e) x = 1 := by
  refine Finset.prod_eq_one (fun e _ => ?_)
  have hx : x ∈ Fsimp E e := by
    rw [mem_Fsimp]
    exact fun j _ => h j
  rw [SigAlg.indicator, if_pos hx]

/-- The product of the lifted indicators vanishes off the simplices. -/
theorem prod_Fsimp_zero (E : Fin (d+1) → Finset (Fin d → G)) (x : Pt (VG d G))
    (h : ¬ IsSimplexD E x) :
    ∏ e ∈ HdC d, SigAlg.indicator (Fsimp E e) x = 0 := by
  rw [IsSimplexD] at h
  push_neg at h
  obtain ⟨j, hj⟩ := h
  have hcard : (Finset.univ.erase j : Finset (Fin (d+1))).card = d := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
    simp
  refine Finset.prod_eq_zero (mem_HdC.mpr hcard) ?_
  rw [SigAlg.indicator, if_neg]
  intro hx
  exact hj ((mem_Fsimp.mp hx) j rfl)

end Szemeredi
