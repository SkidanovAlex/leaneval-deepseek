/-
  WilE8 / Star — a `*`-piece of degree `0` is either empty or the whole closed cube.

  `P.set = projFirst n P.m '' connectedComponentIn P.X.set P.p` is the projection of ONE
  connected component of the semi-Pfaffian set `P.X.set`.  If `P.X.deg = 0` then each basic
  set of the DNF `P.X.basics` has empty `eqs` and empty `pos` list (the atoms `atomDeg Q =
  Q.totalDegree + 1 ≥ 1` cannot disappear any other way), hence holds vacuously everywhere in
  the cube.  Therefore `P.X.set` is either `∅` (empty DNF) or the whole cube, and the
  connected component through `P.p` is correspondingly `∅` or the whole cube.  So the
  projection is `∅` or `cubeC n`.
-/
import Mathlib
import Submission.Work.WilE8.Basic

namespace Work.WilE8.Star

open WilkiesDesign WilkiesDesign.E

/-! ## Degree-`0` semialgebraic `Basic` sets are vacuous -/

/-- The degree of a single atom never vanishes: it is `Q.totalDegree + 1`. -/
lemma starPiece_deg0_atomDeg_ne_zero {k r : ℕ} (Q : EAPoly k r) : atomDeg Q ≠ 0 :=
  Nat.succ_ne_zero _

/-- A basic EA set has degree `0` exactly when it has no equations and no inequalities, i.e.
when it holds everywhere. -/
lemma starPiece_deg0_basic_deg_eq_zero_iff {k r : ℕ} (B : Basic k r) :
    B.deg = 0 ↔ B.eqs = [] ∧ B.pos = [] := by
  constructor
  · intro h
    have hpos : ∀ x ∈ (B.eqs ++ B.pos).map atomDeg, 0 < x := by
      intro x hx
      obtain ⟨Q, -, rfl⟩ := List.mem_map.mp hx
      exact Nat.pos_of_ne_zero (starPiece_deg0_atomDeg_ne_zero Q)
    have hnil : (B.eqs ++ B.pos).map atomDeg = [] := by
      by_contra hne
      exact absurd h (ne_of_gt (List.sum_pos _ hpos hne))
    have h2 : B.eqs ++ B.pos = [] := List.map_eq_nil_iff.mp hnil
    exact ⟨(List.append_eq_nil_iff.mp h2).1, (List.append_eq_nil_iff.mp h2).2⟩
  · intro h
    simp [Basic.deg, h.1, h.2]

/-- A semi-Pfaffian set of degree `0` is either empty or the whole closed cube. -/
lemma starPiece_deg0_semipf_set_eq_empty_or_cube {k : ℕ} (X : SemiPf k)
    (h : X.deg = 0) : X.set = ∅ ∨ X.set = WilkiesDesign.E.cubeC k := by
  have hB : ∀ B ∈ X.basics, B.eqs = [] ∧ B.pos = [] := by
    intro B hB
    have h1 : Basic.deg B = 0 :=
      (List.sum_eq_zero_iff.mp h) (Basic.deg B) (List.mem_map.mpr ⟨B, hB, rfl⟩)
    exact (starPiece_deg0_basic_deg_eq_zero_iff B).mp h1
  by_cases hbasics : X.basics = []
  · -- empty DNF: nothing is satisfied
    left
    ext x
    simp [SemiPf.set, hbasics]
  · -- every basic set of the DNF holds everywhere in the cube
    right
    ext x
    constructor
    · intro hx; exact hx.1
    · intro hx
      obtain ⟨B, hBm⟩ := List.exists_mem_of_ne_nil X.basics hbasics
      refine ⟨hx, B, hBm, ?_⟩
      obtain ⟨he, hp⟩ := hB B hBm
      simp [Basic.holds, he, hp]

/-- The connected component of a point of the closed cube is the whole cube. -/
lemma starPiece_deg0_connectedComponentIn_cubeC {k : ℕ} {x : Fin k → ℝ}
    (hx : x ∈ WilkiesDesign.E.cubeC k) :
    connectedComponentIn (WilkiesDesign.E.cubeC k) x = WilkiesDesign.E.cubeC k := by
  refine Set.Subset.antisymm (connectedComponentIn_subset _ _) ?_
  exact IsPreconnected.subset_connectedComponentIn (Work.WilE8.cubeC_preconnected k) hx
    (subset_refl _)

/-! ## The target -/

theorem starPiece_set_eq_empty_or_cube {n : ℕ} (P : WilkiesDesign.E.StarPiece n)
    (h : P.X.deg = 0) : P.set = ∅ ∨ P.set = WilkiesDesign.E.cubeC n := by
  rcases starPiece_deg0_semipf_set_eq_empty_or_cube P.X h with hX | hX
  · -- `P.X.set = ∅`, so `P.p` lies in no component
    left
    have hp : P.p ∉ P.X.set := by rw [hX]; exact Set.notMem_empty P.p
    show projFirst n P.m '' connectedComponentIn P.X.set P.p = ∅
    rw [connectedComponentIn_eq_empty hp, Set.image_empty]
  · rcases Classical.em (P.p ∈ P.X.set) with hp | hp
    · -- `P.X.set = cubeC (n+m)` and the component through `P.p` is the whole cube
      right
      show projFirst n P.m '' connectedComponentIn P.X.set P.p = WilkiesDesign.E.cubeC n
      rw [hX, starPiece_deg0_connectedComponentIn_cubeC (hX ▸ hp)]
      exact Work.WilE8.projFirst_image_cubeC n P.m
    · left
      show projFirst n P.m '' connectedComponentIn P.X.set P.p = ∅
      rw [connectedComponentIn_eq_empty hp, Set.image_empty]

end Work.WilE8.Star
