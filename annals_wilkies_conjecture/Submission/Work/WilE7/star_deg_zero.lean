import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE8.Basic

namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-!
## Degree-zero `*`-pieces

A `*`-piece of degree `0` is "trivial": it is either empty or the whole ambient cube.
This is used in `cells_select`-style selection arguments, where pieces that are known
to be trivial can be discarded from the covering list.

The reason is that the degree of a `SemiPf` set is the sum of the atom degrees of its
basics, and an atom degree is `totalDegree + 1 ≥ 1`.  Hence degree `0` forces every
basic set in the DNF to have no equations and no inequalities at all: such a basic set
holds everywhere, so the semi-Pfaffian set is either empty (empty DNF) or the whole
cube; and in the second case the connected component of any point of the cube is the
whole cube, whose projection is the cube again.
-/

/-- A basic `EA` set has degree `0` exactly when it imposes no condition at all
(no equations and no strict inequalities). -/
lemma basic_deg_zero_iff {k r : ℕ} (B : Basic k r) :
    B.deg = 0 ↔ B.eqs = [] ∧ B.pos = [] := by
  constructor
  · intro h
    have hnil : B.eqs ++ B.pos = [] := by
      by_contra hne
      obtain ⟨Q, hQ⟩ := List.exists_mem_of_ne_nil _ hne
      have h1 : atomDeg Q ≤ B.deg := by
        rw [Basic.deg]
        exact List.le_sum_of_mem (List.mem_map_of_mem (f := atomDeg) hQ)
      have h2 : 1 ≤ atomDeg Q := Nat.le_add_left 1 Q.totalDegree
      omega
    exact List.append_eq_nil_iff.mp hnil
  · intro ⟨he, hp⟩
    rw [Basic.deg, he, hp]
    simp

/-- A semi-Pfaffian set of degree `0` is empty or the whole cube. -/
lemma semiPf_set_of_deg_zero {k : ℕ} (X : SemiPf k) (h : X.deg = 0) :
    X.set = ∅ ∨ X.set = cubeC k := by
  have hb : ∀ B ∈ X.basics, B.eqs = [] ∧ B.pos = [] := by
    intro B hB
    have hBle : Basic.deg B ≤ X.deg := by
      rw [SemiPf.deg]
      exact List.le_sum_of_mem (List.mem_map_of_mem (f := Basic.deg) hB)
    have hB0 : Basic.deg B = 0 := by omega
    exact (basic_deg_zero_iff B).mp hB0
  by_cases hnil : X.basics = []
  · left
    ext x
    simp [SemiPf.set, hnil]
  · right
    refine Set.Subset.antisymm (Work.WilE8.SemiPf.set_subset_cube X) ?_
    intro x hx
    obtain ⟨B, hB⟩ := List.exists_mem_of_ne_nil _ hnil
    refine ⟨hx, B, hB, ?_⟩
    obtain ⟨he, hp⟩ := hb B hB
    simp [Basic.holds, he, hp]

theorem star_deg_zero :
    (∀ {n : ℕ} (P : WilkiesDesign.E.StarPiece n), P.X.deg = 0 →
        (P.set = ∅ ∨ P.set = WilkiesDesign.E.cubeC n)) ∧
    (∀ {n : ℕ} (L : List (WilkiesDesign.E.StarPiece n)),
        (∀ P ∈ L, 1 ≤ P.X.deg) → L.length ≤ (L.map fun P => P.X.deg).sum) := by
  refine ⟨?_, ?_⟩
  · intro n P hP
    have hset : P.set = projFirst n P.m '' connectedComponentIn P.X.set P.p := rfl
    obtain hX | hX := semiPf_set_of_deg_zero P.X hP
    · left
      rw [hset, hX,
        connectedComponentIn_eq_empty (F := (∅ : Set (Fin (n + P.m) → ℝ))) (x := P.p) (by simp)]
      exact Set.image_empty _
    · by_cases hp : P.p ∈ cubeC (n + P.m)
      · right
        rw [hset, hX,
          IsPreconnected.connectedComponentIn (Work.WilE8.cubeC_preconnected (n + P.m)) hp]
        exact Work.WilE8.projFirst_image_cubeC n P.m
      · left
        rw [hset, hX, connectedComponentIn_eq_empty hp]
        exact Set.image_empty _
  · intro n L hL
    have h := List.length_le_sum_of_one_le (L.map (fun P => P.X.deg)) (by
      intro i hi
      rw [List.mem_map] at hi
      obtain ⟨P, hP, rfl⟩ := hi
      exact hL P hP)
    simpa using h

end Work.WilE7
