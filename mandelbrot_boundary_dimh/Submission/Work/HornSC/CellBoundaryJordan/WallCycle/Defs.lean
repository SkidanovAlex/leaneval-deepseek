import Mathlib
import Submission.Work.HornSC.Cells
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.wall_local_even

/-!
# The wall graph of a finite family of lattice cells

`wallSet A` (from `CellBoundaryJordan.Defs`) is the union of the unit grid segments that separate
a cell of `A` from a cell outside `A`.  This file sets up the *graph* whose vertices are lattice
points and whose edges are those wall segments, in the vocabulary needed to decompose `wallSet A`
into simple closed polygonal curves.

* `nbhdPts v` : the four unit neighbours of `v` (the only lattice points that can be joined to `v`
  by a unit grid segment);
* `WallAdj A u v` : the unit grid segment with endpoints `u`, `v` is a wall of `A`;
* `wallVerts A` : the (finite) set of lattice points that can be an endpoint of a wall of `A`;
* `wallGraph A` : the graph on `wallVerts A` whose edges are the walls;
* `WallDeg A v` : the number of wall edges incident with `v`, proved even (`even_WallDeg`) using
  `wall_local_even`.
-/

open Work.HornSC

namespace Work.HornSC.CellBoundaryJordan.WallCycle

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

/-- The four unit neighbours of the lattice point `v`. -/
def nbhdPts (v : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {(v.1 + 1, v.2), (v.1 - 1, v.2), (v.1, v.2 + 1), (v.1, v.2 - 1)}

@[simp] lemma mem_nbhdPts {v w : ℤ × ℤ} :
    w ∈ nbhdPts v ↔ w = (v.1 + 1, v.2) ∨ w = (v.1 - 1, v.2) ∨ w = (v.1, v.2 + 1) ∨
      w = (v.1, v.2 - 1) := by
  simp only [nbhdPts, Finset.mem_insert, Finset.mem_singleton]

/-- `WallAdj A u v` says that the unit grid segment with endpoints `u` and `v` is a wall of `A`.
The condition is stated through the base point of the corresponding grid segment
(`hSeg`/`vSeg`). -/
def WallAdj (A : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) : Prop :=
  (v = (u.1 + 1, u.2) ∧ hWallAt A u) ∨
  (v = (u.1 - 1, u.2) ∧ hWallAt A (u.1 - 1, u.2)) ∨
  (v = (u.1, u.2 + 1) ∧ vWallAt A u) ∨
  (v = (u.1, u.2 - 1) ∧ vWallAt A (u.1, u.2 - 1))

instance instDecidableHWallAt (A : Finset (ℤ × ℤ)) (u : ℤ × ℤ) : Decidable (hWallAt A u) := by
  unfold hWallAt; infer_instance

instance instDecidableVWallAt (A : Finset (ℤ × ℤ)) (u : ℤ × ℤ) : Decidable (vWallAt A u) := by
  unfold vWallAt; infer_instance

instance instDecidableWallAdj (A : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) : Decidable (WallAdj A u v) := by
  unfold WallAdj; infer_instance

lemma WallAdj_east (A : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    WallAdj A v (v.1 + 1, v.2) ↔ hWallAt A v := by
  unfold WallAdj
  constructor
  · rintro (⟨-, h⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
    · exact h
    all_goals (simp only [Prod.mk.injEq] at h1; omega)
  · exact fun h => Or.inl ⟨rfl, h⟩

lemma WallAdj_west (A : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    WallAdj A v (v.1 - 1, v.2) ↔ hWallAt A (v.1 - 1, v.2) := by
  unfold WallAdj
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
    · simp only [Prod.mk.injEq] at h1; omega
    · exact h
    all_goals (simp only [Prod.mk.injEq] at h1; omega)
  · exact fun h => Or.inr (Or.inl ⟨rfl, h⟩)

lemma WallAdj_north (A : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    WallAdj A v (v.1, v.2 + 1) ↔ vWallAt A v := by
  unfold WallAdj
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h⟩ | ⟨h1, -⟩)
    · simp only [Prod.mk.injEq] at h1; omega
    · simp only [Prod.mk.injEq] at h1; omega
    · exact h
    · simp only [Prod.mk.injEq] at h1; omega
  · exact fun h => Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))

lemma WallAdj_south (A : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    WallAdj A v (v.1, v.2 - 1) ↔ vWallAt A (v.1, v.2 - 1) := by
  unfold WallAdj
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h⟩)
    · simp only [Prod.mk.injEq] at h1; omega
    · simp only [Prod.mk.injEq] at h1; omega
    · simp only [Prod.mk.injEq] at h1; omega
    · exact h
  · exact fun h => Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))

lemma WallAdj_symm {A : Finset (ℤ × ℤ)} {u v : ℤ × ℤ} (h : WallAdj A u v) :
    WallAdj A v u := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1
    exact Or.inr (Or.inl ⟨by ext <;> simp, by convert h2 using 2 <;> simp⟩)
  · subst h1
    exact Or.inl ⟨by ext <;> simp, by convert h2 using 2 <;> simp⟩
  · subst h1
    exact Or.inr (Or.inr (Or.inr ⟨by ext <;> simp, by convert h2 using 2 <;> simp⟩))
  · subst h1
    exact Or.inr (Or.inr (Or.inl ⟨by ext <;> simp, by convert h2 using 2 <;> simp⟩))

lemma WallAdj_irrefl {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} : ¬ WallAdj A u u := by
  rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
  · exact absurd (congrArg Prod.fst h1) (by omega)
  · exact absurd (congrArg Prod.fst h1) (by omega)
  · exact absurd (congrArg Prod.snd h1) (by omega)
  · exact absurd (congrArg Prod.snd h1) (by omega)

lemma WallAdj_unitAdj {A : Finset (ℤ × ℤ)} {u v : ℤ × ℤ} (h : WallAdj A u v) :
    IsUnitAdj u v :=
  h.elim (fun h => Or.inl h.1)
    (fun h => h.elim (fun h => Or.inr (Or.inl h.1))
      (fun h => h.elim (fun h => Or.inr (Or.inr (Or.inl h.1)))
        (fun h => Or.inr (Or.inr (Or.inr h.1)))))

lemma WallAdj_mem_nbhdPts {A : Finset (ℤ × ℤ)} {u v : ℤ × ℤ} (h : WallAdj A u v) :
    v ∈ nbhdPts u := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1]; exact mem_nbhdPts.mpr (Or.inl rfl)
  · rw [h1]; exact mem_nbhdPts.mpr (Or.inr (Or.inl rfl))
  · rw [h1]; exact mem_nbhdPts.mpr (Or.inr (Or.inr (Or.inl rfl)))
  · rw [h1]; exact mem_nbhdPts.mpr (Or.inr (Or.inr (Or.inr rfl)))

/-- The number of wall edges incident with `v`, counted over the four unit neighbours of `v`. -/
def WallDeg (A : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : ℕ :=
  ∑ w ∈ nbhdPts v, if WallAdj A v w then 1 else 0

lemma WallDeg_expand (A : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    WallDeg A v = (if hWallAt A v then 1 else 0) + (if hWallAt A (v.1 - 1, v.2) then 1 else 0) +
      (if vWallAt A v then 1 else 0) + (if vWallAt A (v.1, v.2 - 1) then 1 else 0) := by
  rw [WallDeg, nbhdPts]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Prod.mk.injEq]; omega),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Prod.mk.injEq]; omega),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Prod.mk.injEq]; omega),
      Finset.sum_singleton]
  simp only [WallAdj_east, WallAdj_west, WallAdj_north, WallAdj_south]
  omega

/-- The number of wall edges through a lattice point is even. -/
lemma even_WallDeg (A : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : Even (WallDeg A v) := by
  have hloc := wall_local_even A v
  rw [WallDeg_expand]
  by_cases h1 : hWallAt A v <;> by_cases h2 : hWallAt A (v.1 - 1, v.2) <;>
    by_cases h3 : vWallAt A v <;> by_cases h4 : vWallAt A (v.1, v.2 - 1) <;>
    simp only [h1, h2, h3, h4, ite_true, ite_false, reduceCtorEq, not_false_eq_true,
      not_true_eq_false, or_false, or_true, false_or, true_or, and_false, false_and, true_and,
      and_true, not_and, Classical.not_not] at hloc ⊢ <;>
    (first | exact absurd hloc (by tauto) | norm_num)

/-- The lattice points that can occur as endpoints of a wall of `A`: `A` together with its
translates by `(1,0)`, `(0,1)` and `(1,1)`. -/
def wallVerts (A : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  (A ∪ shift A (0, 1)) ∪ (shift A (1, 0) ∪ shift A (1, 1))

lemma mem_wallVerts {A : Finset (ℤ × ℤ)} {x : ℤ × ℤ} :
    x ∈ wallVerts A ↔ x ∈ A ∨ x ∈ shift A (0, 1) ∨ x ∈ shift A (1, 0) ∨ x ∈ shift A (1, 1) := by
  simp only [wallVerts, Finset.mem_union]
  tauto

lemma hWallAt_fst_mem_wallVerts {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} (h : hWallAt A u) :
    u ∈ wallVerts A := by
  rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact mem_wallVerts.mpr (Or.inl h1)
  · refine mem_wallVerts.mpr (Or.inr (Or.inl ?_))
    rw [Work.HornSC.mem_shift (A := A) (v := (0, 1)) (q := u)]
    exact ⟨(u.1, u.2 - 1), h2, by ext <;> simp only [Work.HornSC.shiftIdx] <;> omega⟩

lemma hWallAt_snd_mem_wallVerts {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} (h : hWallAt A u) :
    (u.1 + 1, u.2) ∈ wallVerts A := by
  rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
  · refine mem_wallVerts.mpr (Or.inr (Or.inr (Or.inl ?_)))
    rw [Work.HornSC.mem_shift (A := A) (v := (1, 0)) (q := (u.1 + 1, u.2))]
    exact ⟨(u.1, u.2), h1, by ext <;> simp only [Work.HornSC.shiftIdx] <;> omega⟩
  · refine mem_wallVerts.mpr (Or.inr (Or.inr (Or.inr ?_)))
    rw [Work.HornSC.mem_shift (A := A) (v := (1, 1)) (q := (u.1 + 1, u.2))]
    exact ⟨(u.1, u.2 - 1), h2, by ext <;> simp only [Work.HornSC.shiftIdx] <;> omega⟩

lemma vWallAt_fst_mem_wallVerts {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} (h : vWallAt A u) :
    u ∈ wallVerts A := by
  rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact mem_wallVerts.mpr (Or.inl h1)
  · refine mem_wallVerts.mpr (Or.inr (Or.inr (Or.inl ?_)))
    rw [Work.HornSC.mem_shift (A := A) (v := (1, 0)) (q := u)]
    exact ⟨(u.1 - 1, u.2), h2, by ext <;> simp only [Work.HornSC.shiftIdx] <;> omega⟩

lemma vWallAt_snd_mem_wallVerts {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} (h : vWallAt A u) :
    (u.1, u.2 + 1) ∈ wallVerts A := by
  rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
  · refine mem_wallVerts.mpr (Or.inr (Or.inl ?_))
    rw [Work.HornSC.mem_shift (A := A) (v := (0, 1)) (q := (u.1, u.2 + 1))]
    exact ⟨(u.1, u.2), h1, by ext <;> simp only [Work.HornSC.shiftIdx] <;> omega⟩
  · refine mem_wallVerts.mpr (Or.inr (Or.inr (Or.inr ?_)))
    rw [Work.HornSC.mem_shift (A := A) (v := (1, 1)) (q := (u.1, u.2 + 1))]
    exact ⟨(u.1 - 1, u.2), h2, by ext <;> simp only [Work.HornSC.shiftIdx] <;> omega⟩

lemma WallAdj_fst_mem_wallVerts {A : Finset (ℤ × ℤ)} {u v : ℤ × ℤ} (h : WallAdj A u v) :
    u ∈ wallVerts A := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hWallAt_fst_mem_wallVerts h2
  · convert hWallAt_snd_mem_wallVerts h2 using 2 <;> omega
  · exact vWallAt_fst_mem_wallVerts h2
  · convert vWallAt_snd_mem_wallVerts h2 using 2 <;> omega

lemma WallAdj_snd_mem_wallVerts {A : Finset (ℤ × ℤ)} {u v : ℤ × ℤ} (h : WallAdj A u v) :
    v ∈ wallVerts A := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]; exact hWallAt_snd_mem_wallVerts h2
  · rw [h1]; exact hWallAt_fst_mem_wallVerts h2
  · rw [h1]; exact vWallAt_snd_mem_wallVerts h2
  · rw [h1]; exact vWallAt_fst_mem_wallVerts h2

/-- The graph whose vertices are the lattice points that can carry a wall of `A` and whose edges
are the wall segments. -/
def wallGraph (A : Finset (ℤ × ℤ)) : SimpleGraph {v : ℤ × ℤ // v ∈ wallVerts A} where
  Adj x y := WallAdj A x.1 y.1
  symm := Std.Symm.mk fun _ _ h => WallAdj_symm h
  loopless := Std.Irrefl.mk fun _ h => WallAdj_irrefl h

instance instDecidableRelWallGraph (A : Finset (ℤ × ℤ)) :
    DecidableRel (wallGraph A).Adj := fun x y => instDecidableWallAdj A x.1 y.1

lemma degree_wallGraph (A : Finset (ℤ × ℤ)) (x : {v : ℤ × ℤ // v ∈ wallVerts A}) :
    (wallGraph A).degree x = WallDeg A x.1 := by
  have himg : ((wallGraph A).neighborFinset x).image Subtype.val
      = (nbhdPts x.1).filter (fun w => WallAdj A x.1 w) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨WallAdj_mem_nbhdPts hy, hy⟩
    · rintro ⟨-, hadj⟩
      exact ⟨⟨w, WallAdj_snd_mem_wallVerts hadj⟩, hadj, rfl⟩
  rw [SimpleGraph.degree, ← Finset.card_image_of_injective _ Subtype.val_injective, himg,
    WallDeg, Finset.card_filter]

/-- Every vertex of the wall graph has even degree. -/
lemma even_degree_wallGraph (A : Finset (ℤ × ℤ)) (x : {v : ℤ × ℤ // v ∈ wallVerts A}) :
    Even ((wallGraph A).degree x) := by
  rw [degree_wallGraph]
  exact even_WallDeg A x.1

end Work.HornSC.CellBoundaryJordan.WallCycle
