import Mathlib
import Submission.Work.HornSC.Cells

/-!
# Vocabulary for the boundary of a union of lattice cells

`cell p` (from `Work.HornSC.Cells`) is the closed unit square `[p.1,p.1+1] × [p.2,p.2+1]`.

The *wall set* of a finite family `A` of cells is the union of the closed unit grid segments that
separate a cell of `A` from a cell outside `A`; it is exactly the frontier of `cellUnion A`
(proved in `frontier_eq_walls.lean`).
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

/-! ## Lattice points -/

/-- The lattice point `v` as a complex number. -/
def lpt (v : ℤ × ℤ) : ℂ := ⟨(v.1 : ℝ), (v.2 : ℝ)⟩

@[simp] lemma lpt_re (v : ℤ × ℤ) : (lpt v).re = (v.1 : ℝ) := rfl
@[simp] lemma lpt_im (v : ℤ × ℤ) : (lpt v).im = (v.2 : ℝ) := rfl

lemma lpt_injective : Function.Injective lpt := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h1 : (a : ℝ) = (c : ℝ) := by simpa using congrArg Complex.re h
  have h2 : (b : ℝ) = (d : ℝ) := by simpa using congrArg Complex.im h
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

@[simp] lemma lpt_eq_iff {u v : ℤ × ℤ} : lpt u = lpt v ↔ u = v := lpt_injective.eq_iff

lemma lpt_ne_iff {u v : ℤ × ℤ} : lpt u ≠ lpt v ↔ u ≠ v := not_congr lpt_eq_iff

/-! ## Open cells and unit grid segments -/

/-- The open unit cell at `p`. -/
def iCell (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) < z.re ∧ z.re < (p.1 : ℝ) + 1 ∧ (p.2 : ℝ) < z.im ∧ z.im < (p.2 : ℝ) + 1}

/-- The closed unit grid segment from `u` east to `u + (1,0)`. -/
def hSeg (u : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | z.im = (u.2 : ℝ) ∧ (u.1 : ℝ) ≤ z.re ∧ z.re ≤ (u.1 : ℝ) + 1}

/-- The closed unit grid segment from `u` north to `u + (0,1)`. -/
def vSeg (u : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | z.re = (u.1 : ℝ) ∧ (u.2 : ℝ) ≤ z.im ∧ z.im ≤ (u.2 : ℝ) + 1}

@[simp] lemma mem_hSeg {u : ℤ × ℤ} {z : ℂ} :
    z ∈ hSeg u ↔ z.im = (u.2 : ℝ) ∧ (u.1 : ℝ) ≤ z.re ∧ z.re ≤ (u.1 : ℝ) + 1 := Iff.rfl

@[simp] lemma mem_vSeg {u : ℤ × ℤ} {z : ℂ} :
    z ∈ vSeg u ↔ z.re = (u.1 : ℝ) ∧ (u.2 : ℝ) ≤ z.im ∧ z.im ≤ (u.2 : ℝ) + 1 := Iff.rfl

lemma isClosed_hSeg (u : ℤ × ℤ) : IsClosed (hSeg u) := by
  have h1 : IsClosed {z : ℂ | z.im = (u.2 : ℝ)} :=
    isClosed_eq Complex.continuous_im continuous_const
  have h2 : IsClosed {z : ℂ | (u.1 : ℝ) ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  have h3 : IsClosed {z : ℂ | z.re ≤ (u.1 : ℝ) + 1} :=
    isClosed_le Complex.continuous_re continuous_const
  have h : IsClosed ({z : ℂ | z.im = (u.2 : ℝ)} ∩ {z : ℂ | (u.1 : ℝ) ≤ z.re} ∩
      {z : ℂ | z.re ≤ (u.1 : ℝ) + 1}) := (h1.inter h2).inter h3
  convert h using 1
  ext z; simp [hSeg, and_assoc]

lemma isClosed_vSeg (u : ℤ × ℤ) : IsClosed (vSeg u) := by
  have h1 : IsClosed {z : ℂ | z.re = (u.1 : ℝ)} :=
    isClosed_eq Complex.continuous_re continuous_const
  have h2 : IsClosed {z : ℂ | (u.2 : ℝ) ≤ z.im} :=
    isClosed_le continuous_const Complex.continuous_im
  have h3 : IsClosed {z : ℂ | z.im ≤ (u.2 : ℝ) + 1} :=
    isClosed_le Complex.continuous_im continuous_const
  have h : IsClosed ({z : ℂ | z.re = (u.1 : ℝ)} ∩ {z : ℂ | (u.2 : ℝ) ≤ z.im} ∩
      {z : ℂ | z.im ≤ (u.2 : ℝ) + 1}) := (h1.inter h2).inter h3
  convert h using 1
  ext z; simp [vSeg, and_assoc]

lemma convex_hSeg (u : ℤ × ℤ) : Convex ℝ (hSeg u) := by
  have h1 : Convex ℝ {z : ℂ | z.im = (u.2 : ℝ)} := by
    have : {z : ℂ | z.im = (u.2 : ℝ)} = Complex.imCLM ⁻¹' ({(u.2 : ℝ)} : Set ℝ) := by
      ext z; simp
    rw [this]
    exact (convex_singleton _).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  have h2 : Convex ℝ {z : ℂ | (u.1 : ℝ) ≤ z.re} :=
    (convex_Ici _).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have h3 : Convex ℝ {z : ℂ | z.re ≤ (u.1 : ℝ) + 1} :=
    (convex_Iic _).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have h : Convex ℝ ({z : ℂ | z.im = (u.2 : ℝ)} ∩ {z : ℂ | (u.1 : ℝ) ≤ z.re} ∩
      {z : ℂ | z.re ≤ (u.1 : ℝ) + 1}) := (h1.inter h2).inter h3
  convert h using 1
  ext z; simp [hSeg, and_assoc]

lemma convex_vSeg (u : ℤ × ℤ) : Convex ℝ (vSeg u) := by
  have h1 : Convex ℝ {z : ℂ | z.re = (u.1 : ℝ)} := by
    have : {z : ℂ | z.re = (u.1 : ℝ)} = Complex.reCLM ⁻¹' ({(u.1 : ℝ)} : Set ℝ) := by
      ext z; simp
    rw [this]
    exact (convex_singleton _).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have h2 : Convex ℝ {z : ℂ | (u.2 : ℝ) ≤ z.im} :=
    (convex_Ici _).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  have h3 : Convex ℝ {z : ℂ | z.im ≤ (u.2 : ℝ) + 1} :=
    (convex_Iic _).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  have h : Convex ℝ ({z : ℂ | z.re = (u.1 : ℝ)} ∩ {z : ℂ | (u.2 : ℝ) ≤ z.im} ∩
      {z : ℂ | z.im ≤ (u.2 : ℝ) + 1}) := (h1.inter h2).inter h3
  convert h using 1
  ext z; simp [vSeg, and_assoc]

@[simp] lemma isConnected_hSeg (u : ℤ × ℤ) : IsConnected (hSeg u) :=
  (convex_hSeg u).isConnected ⟨lpt u, by simp [hSeg, lpt]⟩

@[simp] lemma isConnected_vSeg (u : ℤ × ℤ) : IsConnected (vSeg u) :=
  (convex_vSeg u).isConnected ⟨lpt u, by simp [vSeg, lpt]⟩

@[simp] lemma lpt_mem_hSeg (u : ℤ × ℤ) : lpt u ∈ hSeg u := by simp [hSeg, lpt]
@[simp] lemma lpt_add_one_mem_hSeg (u : ℤ × ℤ) : lpt (u.1 + 1, u.2) ∈ hSeg u := by
  simp [hSeg, lpt]
@[simp] lemma lpt_mem_vSeg (u : ℤ × ℤ) : lpt u ∈ vSeg u := by simp [vSeg, lpt]
@[simp] lemma lpt_add_one_mem_vSeg (u : ℤ × ℤ) : lpt (u.1, u.2 + 1) ∈ vSeg u := by
  simp [vSeg, lpt]

lemma hSeg_subset_cell_left (u : ℤ × ℤ) : hSeg u ⊆ cell (u.1, u.2) := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [h1] <;> push_cast <;> linarith [h2, h3]


/-! ## Walls -/

/-- The horizontal unit segment at `u` (from `u` east) is a *wall* of `A`: exactly one of the two
cells adjacent to it (above: `(u.1,u.2)`, below: `(u.1,u.2-1)`) belongs to `A`. -/
def hWallAt (A : Finset (ℤ × ℤ)) (u : ℤ × ℤ) : Prop :=
  (((u.1, u.2) : ℤ × ℤ) ∈ A ∧ ((u.1, u.2 - 1) : ℤ × ℤ) ∉ A) ∨
    (((u.1, u.2) : ℤ × ℤ) ∉ A ∧ ((u.1, u.2 - 1) : ℤ × ℤ) ∈ A)

/-- The vertical unit segment at `u` (from `u` north) is a *wall* of `A`: exactly one of the two
cells adjacent to it (right: `(u.1,u.2)`, left: `(u.1-1,u.2)`) belongs to `A`. -/
def vWallAt (A : Finset (ℤ × ℤ)) (u : ℤ × ℤ) : Prop :=
  (((u.1, u.2) : ℤ × ℤ) ∈ A ∧ ((u.1 - 1, u.2) : ℤ × ℤ) ∉ A) ∨
    (((u.1, u.2) : ℤ × ℤ) ∉ A ∧ ((u.1 - 1, u.2) : ℤ × ℤ) ∈ A)

/-- The set of horizontal wall segments. -/
def hWallSet (A : Finset (ℤ × ℤ)) : Set ℂ := ⋃ u : {u : ℤ × ℤ // hWallAt A u}, hSeg u.1

/-- The set of vertical wall segments. -/
def vWallSet (A : Finset (ℤ × ℤ)) : Set ℂ := ⋃ u : {u : ℤ × ℤ // vWallAt A u}, vSeg u.1

/-- The wall set of `A`: the union of the horizontal and vertical wall segments. -/
def wallSet (A : Finset (ℤ × ℤ)) : Set ℂ := hWallSet A ∪ vWallSet A

lemma mem_hWallSet {A : Finset (ℤ × ℤ)} {z : ℂ} :
    z ∈ hWallSet A ↔ ∃ u : ℤ × ℤ, hWallAt A u ∧ z ∈ hSeg u := by
  constructor
  · intro hz
    rw [hWallSet, Set.mem_iUnion] at hz
    obtain ⟨u, hu⟩ := hz
    exact ⟨u.1, u.2, hu⟩
  · rintro ⟨u, hu, hz⟩
    rw [hWallSet, Set.mem_iUnion]
    exact ⟨⟨u, hu⟩, hz⟩

lemma mem_vWallSet {A : Finset (ℤ × ℤ)} {z : ℂ} :
    z ∈ vWallSet A ↔ ∃ u : ℤ × ℤ, vWallAt A u ∧ z ∈ vSeg u := by
  constructor
  · intro hz
    rw [vWallSet, Set.mem_iUnion] at hz
    obtain ⟨u, hu⟩ := hz
    exact ⟨u.1, u.2, hu⟩
  · rintro ⟨u, hu, hz⟩
    rw [vWallSet, Set.mem_iUnion]
    exact ⟨⟨u, hu⟩, hz⟩

lemma mem_wallSet {A : Finset (ℤ × ℤ)} {z : ℂ} :
    z ∈ wallSet A ↔ (∃ u : ℤ × ℤ, hWallAt A u ∧ z ∈ hSeg u) ∨
      (∃ u : ℤ × ℤ, vWallAt A u ∧ z ∈ vSeg u) := by
  rw [wallSet, Set.mem_union, mem_hWallSet, mem_vWallSet]

/-! ## Cell adjacency and the outer (unbounded) cell component -/

/-- Two cells are `4`-adjacent (share an edge). -/
def Adj4 (p q : ℤ × ℤ) : Prop :=
  q = (p.1 + 1, p.2) ∨ q = (p.1 - 1, p.2) ∨ q = (p.1, p.2 + 1) ∨ q = (p.1, p.2 - 1)

lemma adj4_symm {p q : ℤ × ℤ} (h : Adj4 p q) : Adj4 q p := by
  rcases h with h | h | h | h
  · subst h; right; left; apply Prod.ext <;> omega
  · subst h; left; apply Prod.ext <;> omega
  · subst h; right; right; right; apply Prod.ext <;> omega
  · subst h; right; right; left; apply Prod.ext <;> omega

lemma adj4_ne {p q : ℤ × ℤ} (h : Adj4 p q) : p ≠ q := by
  rintro rfl
  rcases h with h | h | h | h
  · exact absurd (congrArg Prod.fst h) (by omega)
  · exact absurd (congrArg Prod.fst h) (by omega)
  · exact absurd (congrArg Prod.snd h) (by omega)
  · exact absurd (congrArg Prod.snd h) (by omega)

/-- A cell far to the north-east of every cell of `A` (in particular outside `A`). -/
noncomputable def farCell (A : Finset (ℤ × ℤ)) : ℤ × ℤ :=
  ((insert (0, 0) A).sup' (Finset.insert_nonempty _ _) (fun p => p.1) + 2,
   (insert (0, 0) A).sup' (Finset.insert_nonempty _ _) (fun p => p.2) + 2)

lemma farCell_fst (A : Finset (ℤ × ℤ)) :
    (farCell A).1 = (insert (0, 0) A).sup' (Finset.insert_nonempty _ _) (fun p => p.1) + 2 := rfl

lemma farCell_snd (A : Finset (ℤ × ℤ)) :
    (farCell A).2 = (insert (0, 0) A).sup' (Finset.insert_nonempty _ _) (fun p => p.2) + 2 := rfl

lemma farCell_not_mem (A : Finset (ℤ × ℤ)) : farCell A ∉ A := by
  intro hmem
  have h1 : (insert (0, 0) A).sup' (Finset.insert_nonempty _ _) (fun p => p.1) + 2 ≤
      (insert (0, 0) A).sup' (Finset.insert_nonempty _ _) (fun p => p.1) :=
    calc (insert (0, 0) A).sup' (Finset.insert_nonempty _ _) (fun p => p.1) + 2
        = (farCell A).1 := (farCell_fst A).symm
      _ ≤ _ := Finset.le_sup' (fun p => p.1) (Finset.mem_insert_of_mem hmem)
  omega

/-- `OuterCell A q` says: `q` is a cell outside `A` that is `4`-connected to a cell far away from
`A`, i.e. `q` belongs to the unbounded connected component of `ℤ² ∖ A`. -/
def OuterCell (A : Finset (ℤ × ℤ)) (q : ℤ × ℤ) : Prop :=
  q ∉ A ∧ Relation.ReflTransGen (fun p r => Adj4 p r ∧ r ∉ A) q (farCell A)

lemma OuterCell.not_mem {A : Finset (ℤ × ℤ)} {q : ℤ × ℤ} (h : OuterCell A q) : q ∉ A := h.1

lemma OuterCell_farCell {A : Finset (ℤ × ℤ)} : OuterCell A (farCell A) :=
  ⟨farCell_not_mem A, Relation.ReflTransGen.refl⟩

lemma OuterCell.step {A : Finset (ℤ × ℤ)} {p r : ℤ × ℤ} (hp : OuterCell A p) (hr : r ∉ A)
    (hadj : Adj4 p r) : OuterCell A r :=
  ⟨hr, hp.2.head ⟨adj4_symm hadj, hp.not_mem⟩⟩

lemma OuterCell_of_adj {A : Finset (ℤ × ℤ)} {p r : ℤ × ℤ} (h : OuterCell A r) (hp : p ∉ A)
    (hadj : Adj4 p r) : OuterCell A p :=
  ⟨hp, h.2.head ⟨hadj, h.not_mem⟩⟩

/-- The wall between an outer cell and a non-outer cell, horizontal version. -/
def hOuterWallAt (A : Finset (ℤ × ℤ)) (u : ℤ × ℤ) : Prop :=
  hWallAt A u ∧
    (OuterCell A ((u.1, u.2) : ℤ × ℤ) ∨ OuterCell A ((u.1, u.2 - 1) : ℤ × ℤ))

/-- The wall between an outer cell and a non-outer cell, vertical version. -/
def vOuterWallAt (A : Finset (ℤ × ℤ)) (u : ℤ × ℤ) : Prop :=
  vWallAt A u ∧
    (OuterCell A ((u.1, u.2) : ℤ × ℤ) ∨ OuterCell A ((u.1 - 1, u.2) : ℤ × ℤ))

/-- The outer wall segments: the walls of `A` incident with the unbounded region. -/
def outerWallSet (A : Finset (ℤ × ℤ)) : Set ℂ :=
  (⋃ u : {u : ℤ × ℤ // hOuterWallAt A u}, hSeg u.1) ∪
  (⋃ u : {u : ℤ × ℤ // vOuterWallAt A u}, vSeg u.1)

lemma outerWallSet_subset_wallSet (A : Finset (ℤ × ℤ)) : outerWallSet A ⊆ wallSet A := by
  rintro z (hz | hz)
  · rw [Set.mem_iUnion] at hz
    obtain ⟨u, hu⟩ := hz
    exact Or.inl (mem_hWallSet.mpr ⟨u.1, u.2.1, hu⟩)
  · rw [Set.mem_iUnion] at hz
    obtain ⟨u, hu⟩ := hz
    exact Or.inr (mem_vWallSet.mpr ⟨u.1, u.2.1, hu⟩)

/-! ## Unit steps -/

/-- An oriented unit grid step: `e = (u,v)` with `v = u + (1,0)` or `v = u + (0,1)`. -/
def IsUnitStep (e : (ℤ × ℤ) × (ℤ × ℤ)) : Prop :=
  e.2 = (e.1.1 + 1, e.1.2) ∨ e.2 = (e.1.1, e.1.2 + 1)

/-- The closed unit grid segment spanned by a unit step. -/
def stepSeg (e : (ℤ × ℤ) × (ℤ × ℤ)) : Set ℂ :=
  if e.2 = (e.1.1 + 1, e.1.2) then hSeg e.1 else vSeg e.1

lemma stepSeg_of_eq_east {u v : ℤ × ℤ} (h : v = (u.1 + 1, u.2)) : stepSeg (u, v) = hSeg u := by
  rw [stepSeg, if_pos h]

lemma stepSeg_of_eq_north {u v : ℤ × ℤ} (h : v = (u.1, u.2 + 1)) : stepSeg (u, v) = vSeg u := by
  rw [stepSeg, if_neg (fun hc => by
    rw [h] at hc; simp at hc)]

/-- The set of wall steps of `A`: the unit steps whose segment is a wall of `A`. -/
def wallSteps (A : Finset (ℤ × ℤ)) : Set ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {e | IsUnitStep e ∧ stepSeg e ⊆ wallSet A}

lemma mem_wallSteps {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)} :
    e ∈ wallSteps A ↔ IsUnitStep e ∧ stepSeg e ⊆ wallSet A := Iff.rfl

lemma hWallAt_step {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} (h : hWallAt A u) :
    (u, (u.1 + 1, u.2)) ∈ wallSteps A := by
  refine ⟨Or.inl rfl, ?_⟩
  rw [stepSeg_of_eq_east rfl]
  intro z hz
  exact Or.inl (mem_hWallSet.mpr ⟨u, h, hz⟩)

lemma vWallAt_step {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} (h : vWallAt A u) :
    (u, (u.1, u.2 + 1)) ∈ wallSteps A := by
  refine ⟨Or.inr rfl, ?_⟩
  rw [stepSeg_of_eq_north rfl]
  intro z hz
  exact Or.inr (mem_vWallSet.mpr ⟨u, h, hz⟩)

/-- Two lattice points are *unit-adjacent*: they differ by a unit vector in one of the four
directions (the segment between them is a unit grid segment). -/
def IsUnitAdj (u v : ℤ × ℤ) : Prop :=
  v = (u.1 + 1, u.2) ∨ v = (u.1 - 1, u.2) ∨ v = (u.1, u.2 + 1) ∨ v = (u.1, u.2 - 1)

/-- The closed segment between two lattice points (a unit grid segment when they are unit-adjacent). -/
def adjSeg (u v : ℤ × ℤ) : Set ℂ := segment ℝ (lpt u) (lpt v)

end Work.HornSC.CellBoundaryJordan
