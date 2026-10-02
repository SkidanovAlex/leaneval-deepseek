import Mathlib
import Submission.Work.RatHurewicz.Triad.GridDefs
import Submission.Work.RatHurewicz.Triad.FlowTransfer
import Submission.Work.RatHurewicz.Triad.Helpers
import Submission.Work.RatHurewicz.Triad.Star

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The rule of the grid induction (the vocabulary)

This file fixes the *rule* of the preparation theorem for the triad `(X; B, C)`: which treatment is
applied to which cell of the grid, and what each treatment has to achieve.

Given the initial admissible map `Φ : I^{n+1} → X`, the cells of the grid fall into three classes:

* `CellB c` and `CellC c` (the cell is mapped into `B ∩ C`): **no treatment** is applied — such
  cells are never moved, and their values stay `Φ`-values, hence in `B ∩ C ∩ pathComponent x₀`;
* `CellB c` and `¬ CellC c`: for `cellDim c ≤ p+1` a *compression* into `B ∩ C`, for
  `cellDim c > p+1` the `K`-trick with `p+2` directions (`hBc` resp. `(6.9.1)`);
* `¬ CellB c` and `CellC c`: the `C`-dual.

The clauses that the treatments have to establish, cell by cell, are collected in `ConClauses`;
`Inv d g` says that all cells of dimension `≤ d` satisfy them.  Two further properties of the map
are maintained throughout: `ValsB`/`ValsC` (the values on `CellB`/`CellC` cells lie in `B`/`C`) and
`InitFace` (the initial face is constantly `x₀`, which by path connectedness of the cube forces all
values to lie in the path component of `x₀`).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

open Work.ThomBordism.TwoSet

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X} {j N : ℕ} {n p q : ℕ}

/-- `c` is a **subcell** of `c'`: the coordinatewise inclusion of the grid cells. -/
def Subcell (c c' : CellIdx j N) : Prop :=
  (∀ i, c'.lo i ≤ c.lo i) ∧ (∀ i, c.hi i ≤ c'.hi i)

theorem Subcell.refl (c : CellIdx j N) : Subcell c c := ⟨fun _ => le_rfl, fun _ => le_rfl⟩

theorem cellSet_subcell {c c' : CellIdx j N} (h : Subcell c c') : cellSet c ⊆ cellSet c' :=
  cellSet_mono h.1 h.2

/-- **The cell `c` is mapped by `Φ` into `B`.** -/
def CellB (B : Set X) (Φ : C(IC j, X)) (c : CellIdx j N) : Prop :=
  ∀ z, z ∈ cellSet c → Φ z ∈ B

/-- **The cell `c` is mapped by `Φ` into `C`.** -/
def CellC (C : Set X) (Φ : C(IC j, X)) (c : CellIdx j N) : Prop :=
  ∀ z, z ∈ cellSet c → Φ z ∈ C

theorem CellB_subcell {Φ : C(IC j, X)} {c c' : CellIdx j N} (h : Subcell c c')
    (hc : CellB B Φ c') : CellB B Φ c :=
  fun z hz => hc z (cellSet_subcell h hz)

theorem CellC_subcell {Φ : C(IC j, X)} {c c' : CellIdx j N} (h : Subcell c c')
    (hc : CellC C Φ c') : CellC C Φ c :=
  fun z hz => hc z (cellSet_subcell h hz)

/-- The owner of a point of a cell is a subcell of it. -/
theorem subcell_cOf_of_mem {c : CellIdx j N} {x : IC j} (hx : x ∈ cellSet c) :
    Subcell (cOf N x) c :=
  cOf_sub_of_mem_cellSet hx

/-- A cell all of whose points are mapped by `Φ` into `B ∩ C` is never treated. -/
theorem cellB_and_cellC_of_Phi {Φ : C(IC j, X)} {c : CellIdx j N}
    (h : ∀ z, z ∈ cellSet c → Φ z ∈ B ∩ C) : CellB B Φ c ∧ CellC C Φ c :=
  ⟨fun z hz => (h z hz).1, fun z hz => (h z hz).2⟩

section CellLocal

variable {x : IC j} {i : Fin j} {v : ℕ}

/-- In a coordinate in which the point `x` sits exactly at a node `v/N` of the grid, the owner of
`x` has a *node* there as well: `lo = hi = v`. -/
theorem cOf_lo_eq_cOf_hi_of_coord_eq {N : ℕ} (hN : 1 ≤ N) (hv : v ≤ N)
    (h : (x i : ℝ) = (v : ℝ) / N) :
    (cOf N x).lo i = v ∧ (cOf N x).hi i = v := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (N : ℝ) * (x i : ℝ) = (v : ℝ) := by
    rw [h]; field_simp
  constructor
  · rw [cOf_lo, hx, Nat.floor_natCast]
  · rw [cOf_hi, hx, Nat.ceil_natCast]

/-- Every point of the owner of a point `x` with `x i = v/N` has `i`-coordinate `v/N`. -/
theorem coord_eq_of_mem_cellSet_cOf {N : ℕ} (hN : 1 ≤ N) (hv : v ≤ N)
    (h : (x i : ℝ) = (v : ℝ) / N) {z : IC j} (hz : z ∈ cellSet (cOf N x)) :
    (z i : ℝ) = (v : ℝ) / N := by
  obtain ⟨hlo, hhi⟩ := cOf_lo_eq_cOf_hi_of_coord_eq hN hv h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := (mem_cellSet.mp hz i).1
  have h2 := (mem_cellSet.mp hz i).2
  rw [hlo] at h1
  rw [hhi] at h2
  have h1' : (v : ℝ) / N ≤ (z i : ℝ) := h1
  have h2' : (z i : ℝ) ≤ (v : ℝ) / N := h2
  linarith

/-- A point of the owner of a point with last coordinate `0` also has last coordinate `0`. -/
theorem last_eq_zero_of_mem_cellSet_cOf {N : ℕ} (hN : 1 ≤ N) {x z : IC (n + 1)}
    (hx : x (Fin.last n) = 0) (hz : z ∈ cellSet (cOf N x)) : z (Fin.last n) = 0 := by
  have hv : (0 : ℕ) ≤ N := Nat.zero_le N
  have h : ((x (Fin.last n) : unitInterval) : ℝ) = ((0 : ℕ) : ℝ) / N := by
    rw [hx]; norm_num
  have := coord_eq_of_mem_cellSet_cOf (j := n + 1) hN hv h hz
  exact Subtype.ext (by simp [this])

end CellLocal

/-- **The clauses that the treatments have to establish**, cell by cell. -/
def ConClauses (p q : ℕ) (B C : Set X) (Φ g : C(IC j, X)) (c : CellIdx j N) : Prop :=
  (CellB B Φ c → ¬ CellC C Φ c → cellDim c ≤ p + 1 →
      ∀ z, z ∈ cellSet c → g z ∈ B ∩ C) ∧
  (CellB B Φ c → ¬ CellC C Φ c → p + 1 < cellDim c →
      ∀ z, z ∈ cellSet c → g z ∉ C → KW N (p + 2) c z) ∧
  (¬ CellB B Φ c → CellC C Φ c → cellDim c ≤ q + 1 →
      ∀ z, z ∈ cellSet c → g z ∈ B ∩ C) ∧
  (¬ CellB B Φ c → CellC C Φ c → q + 1 < cellDim c →
      ∀ z, z ∈ cellSet c → g z ∉ B → GW N (q + 2) c z)

/-- **The staged invariant**: every cell of dimension `≤ d` satisfies its clauses. -/
def Inv (p q : ℕ) (B C : Set X) (Φ g : C(IC (n + 1), X)) (d : ℕ) : Prop :=
  ∀ c : CellIdx (n + 1) N, cellDim c ≤ d → ConClauses p q B C Φ g c

/-- **The value-set property for `B`**: the values on a `CellB` cell lie in `B`. -/
def ValsB (B : Set X) (Φ g : C(IC (n + 1), X)) : Prop :=
  ∀ c : CellIdx (n + 1) N, CellB B Φ c → ∀ z, z ∈ cellSet c → g z ∈ B

/-- **The value-set property for `C`**: the values on a `CellC` cell lie in `C`. -/
def ValsC (C : Set X) (Φ g : C(IC (n + 1), X)) : Prop :=
  ∀ c : CellIdx (n + 1) N, CellC C Φ c → ∀ z, z ∈ cellSet c → g z ∈ C

/-- **The initial face is fixed**: `g` is constantly `x₀` on `{z | z (Fin.last n) = 0}`. -/
def InitFace (x₀ : X) (g : C(IC (n + 1), X)) : Prop :=
  ∀ z : IC (n + 1), z (Fin.last n) = 0 → g z = x₀

/-- A map fixing the initial face takes all its values in the path component of the base point:
the cube is path connected and contains a point of the initial face. -/
theorem mem_pathComponent_of_initFace {x₀ : X} {g : C(IC (n + 1), X)} (h : InitFace x₀ g) :
    ∀ z : IC (n + 1), g z ∈ pathComponent x₀ := by
  have hpc : IsPathConnected (Set.range g) := isPathConnected_range g.continuous
  have hx : x₀ ∈ Set.range g :=
    ⟨Fin.snoc (fun _ : Fin n => (0 : unitInterval)) 0, h _ (Fin.snoc_last ..)⟩
  intro z
  exact hpc.subset_pathComponent hx ⟨z, rfl⟩

end

end Work.RatHurewicz.Triad
