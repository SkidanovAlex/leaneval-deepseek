import Mathlib
import Submission.Work.ThomBordism.TwoSet.spreadCell
import Submission.Work.ThomBordism.TwoSet.keyLemma
import Submission.Work.ThomBordism.TwoSet.CollarSubdivision
import Submission.Work.ThomBordism.TwoSet.compresses_homeo
import Submission.Work.ThomBordism.TwoSet.exists_cellHomeo
import Submission.Work.ThomBordism.TwoSet.Process

/-!
# The vocabulary of the cell-by-cell compression

For the compression of a map `f : I^j → X` along a collared subdivision with a box labelling
`lab : (Fin j → Fin N) → Bool` we need:

* `Away c` — the cell `c` does not meet the boundary `∂I^j` (equivalently `1 ≤ c.lo i` and
  `c.hi i ≤ N - 1` for all `i`);
* `Vcell lab c` / `Ucell lab c` — the cell `c` is contained in a `V`- (resp. `U`-) labelled box;
* `Proc lab c` — the cells which the process handles: away from the boundary and *unambiguously*
  typed (exactly one of `Vcell`, `Ucell`).

The main combinatorial lemmas are `cellSet_cOf_subset` (`cOf N x` is contained in every cell
containing `x`), `cellDim_cOf_le_of_mem` (its dimension is the least), `Vcell_away` (a `V`-typed
cell is away from the boundary, by the collar hypothesis) and
`nuOf_eq_zero_of_away_of_mem_boundary` (the spreading of an away cell fixes `∂I^j`).
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

variable {j N : ℕ}

/-- **Away from the boundary.**  The cell `c` does not meet `∂I^j`. -/
def Away (c : CellIdx j N) : Prop := ∀ i, 1 ≤ c.lo i ∧ c.hi i ≤ N - 1

/-- The cell is contained in a `V`-labelled box. -/
def Vcell (lab : (Fin j → Fin N) → Bool) (c : CellIdx j N) : Prop :=
  ∃ m : Fin j → Fin N, lab m = true ∧ cellSet c ⊆ boxSet m

/-- The cell is contained in a `U`-labelled box. -/
def Ucell (lab : (Fin j → Fin N) → Bool) (c : CellIdx j N) : Prop :=
  ∃ m : Fin j → Fin N, lab m = false ∧ cellSet c ⊆ boxSet m

/-- The cells handled by the process: away from the boundary and unambiguously typed. -/
def Proc (lab : (Fin j → Fin N) → Bool) (c : CellIdx j N) : Prop :=
  Away c ∧ ((Vcell lab c ∧ ¬ Ucell lab c) ∨ (Ucell lab c ∧ ¬ Vcell lab c))

/-! ### `cOf N x` is the minimal cell containing `x` -/

/-- The index inequalities: every cell containing `x` contains `cOf N x`. -/
theorem cellSet_cOf_subset (hN : 1 ≤ N) (c : CellIdx j N) {x : IC j} (hx : x ∈ cellSet c) :
    ∀ i, c.lo i ≤ (cOf N x).lo i ∧ (cOf N x).hi i ≤ c.hi i := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  intro i
  have hxi := hx i
  have h1 : (c.lo i : ℝ) ≤ (N : ℝ) * (x i : ℝ) := by
    rw [div_le_iff₀ hNpos] at hxi; linarith [hxi.1]
  have h2 : (N : ℝ) * (x i : ℝ) ≤ (c.hi i : ℝ) := by
    rw [le_div_iff₀ hNpos] at hxi; linarith [hxi.2]
  constructor
  · rw [cOf_lo]
    exact Nat.le_floor h1
  · rw [cOf_hi]
    exact (Nat.ceil_le).mpr h2

/-- Monotonicity of the dimension under the index order. -/
theorem cellDim_le_of_le {c c' : CellIdx j N}
    (h : ∀ i, c.lo i ≤ c'.lo i ∧ c'.hi i ≤ c.hi i) : cellDim c' ≤ cellDim c := by
  unfold cellDim
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hi
  have := h i
  omega

/-- The dimension of the minimal cell of a point of `c` is at most the dimension of `c`. -/
theorem cellDim_cOf_le_of_mem (hN : 1 ≤ N) (c : CellIdx j N) {x : IC j}
    (hx : x ∈ cellSet c) : cellDim (cOf N x) ≤ cellDim c :=
  cellDim_le_of_le (cellSet_cOf_subset hN c hx)

/-! ### The typing and `Away` are inherited by subcells -/

theorem Vcell_mono (hN : 1 ≤ N) {lab : (Fin j → Fin N) → Bool} {c c' : CellIdx j N}
    (h : ∀ i, c.lo i ≤ c'.lo i ∧ c'.hi i ≤ c.hi i) (hc : Vcell lab c) : Vcell lab c' := by
  obtain ⟨m, hm, hmc⟩ := hc
  refine ⟨m, hm, fun x hx => hmc fun i => ?_⟩
  have hxi := hx i
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hNpos] at hxi ⊢
    have h1 : (c.lo i : ℝ) ≤ (c'.lo i : ℝ) := by exact_mod_cast (h i).1
    linarith [hxi.1]
  · rw [le_div_iff₀ hNpos] at hxi ⊢
    have h1 : (c'.hi i : ℝ) ≤ (c.hi i : ℝ) := by exact_mod_cast (h i).2
    linarith [hxi.2]

theorem Ucell_mono (hN : 1 ≤ N) {lab : (Fin j → Fin N) → Bool} {c c' : CellIdx j N}
    (h : ∀ i, c.lo i ≤ c'.lo i ∧ c'.hi i ≤ c.hi i) (hc : Ucell lab c) : Ucell lab c' := by
  obtain ⟨m, hm, hmc⟩ := hc
  refine ⟨m, hm, fun x hx => hmc fun i => ?_⟩
  have hxi := hx i
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hNpos] at hxi ⊢
    have h1 : (c.lo i : ℝ) ≤ (c'.lo i : ℝ) := by exact_mod_cast (h i).1
    linarith [hxi.1]
  · rw [le_div_iff₀ hNpos] at hxi ⊢
    have h1 : (c'.hi i : ℝ) ≤ (c.hi i : ℝ) := by exact_mod_cast (h i).2
    linarith [hxi.2]

theorem Away_mono {c c' : CellIdx j N}
    (h : ∀ i, c.lo i ≤ c'.lo i ∧ c'.hi i ≤ c.hi i) (hc : Away c) : Away c' := by
  intro i
  exact ⟨le_trans (hc i).1 (h i).1, le_trans (h i).2 (hc i).2⟩

/-! ### Every cell is contained in a box; typing is total -/

/-- Every cell is contained in a box of the grid. -/
theorem exists_box_of_cellSet (hN : 1 ≤ N) (c : CellIdx j N) :
    ∃ m : Fin j → Fin N, cellSet c ⊆ boxSet m := by
  classical
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  let m : Fin j → Fin N := fun i => ⟨min (N-1) (c.lo i), lt_of_le_of_lt (min_le_left _ _) (by omega)⟩
  refine ⟨m, fun y hy i => ?_⟩
  have hle : (c.lo i : ℝ) ≤ (N:ℝ) := by
    exact_mod_cast (le_trans (c.hle i) (c.hhi i))
  have hyc := hy i
  have hmval : ((m i : ℕ) : ℝ) = ((min (N-1) (c.lo i) : ℕ) : ℝ) := rfl
  rw [hmval]
  have h1 : ((min (N-1) (c.lo i) : ℕ) : ℝ) ≤ (c.lo i : ℝ) := by
    exact_mod_cast min_le_right (N-1) (c.lo i)
  constructor
  · have h3 := (div_le_iff₀ hNpos).mp hyc.1
    nlinarith [h1, h3]
  · rcases le_or_gt (c.lo i) (N-1) with h | h
    · have hmin : min (N-1) (c.lo i) = c.lo i := min_eq_right h
      rw [hmin]
      have h4 := (le_div_iff₀ hNpos).mp hyc.2
      have hhi : (c.hi i : ℝ) ≤ (c.lo i : ℝ) + 1 := by
        have hs := c.hstep i
        have : (c.hi i : ℝ) ≤ ((c.lo i + 1 : ℕ) : ℝ) := by exact_mod_cast hs
        push_cast at this; linarith
      linarith
    · have hmin : min (N-1) (c.lo i) = N-1 := min_eq_left (le_of_lt h)
      rw [hmin]
      have hy1 : (y i : ℝ) ≤ 1 := (y i).2.2
      have hcast : (((N - 1 : ℕ)) : ℝ) = (N:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ N)]; norm_num
      rw [hcast]
      nlinarith

/-- Every cell is `V`-typed or `U`-typed. -/
theorem cell_typed (hN : 1 ≤ N) {lab : (Fin j → Fin N) → Bool} (c : CellIdx j N) :
    Vcell lab c ∨ Ucell lab c := by
  obtain ⟨m, hm⟩ := exists_box_of_cellSet hN c
  cases h : lab m with
  | false => exact Or.inr ⟨m, h, hm⟩
  | true => exact Or.inl ⟨m, h, hm⟩

/-! ### `V`-typed cells are away from the boundary -/

/-- **A `V`-typed cell is away from the boundary**, by the collar hypothesis. -/
theorem Vcell_away (hN : 1 ≤ N) {lab : (Fin j → Fin N) → Bool}
    (hfar : ∀ m, lab m = true → ∀ x ∈ boxSet m, ∀ i, 2/(N:ℝ) ≤ (x i : ℝ) ∧
      (x i : ℝ) ≤ 1 - 2/(N:ℝ))
    {c : CellIdx j N} (hc : Vcell lab c) : Away c := by
  obtain ⟨m, hm, hmc⟩ := hc
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  intro i
  have hNn : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  -- the point with all coordinates `c.hi k / N`
  have hhi_mem : (fun k : Fin j => (⟨((c.hi k : ℕ) : ℝ)/N, by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hNpos]; exact_mod_cast c.hhi k⟩ : unitInterval)) ∈ cellSet c := by
    intro k
    refine ⟨?_, le_rfl⟩
    rw [div_le_div_iff_of_pos_right hNpos]; exact_mod_cast c.hle k
  have h1 := hfar m hm _ (hmc hhi_mem) i
  -- the point with all coordinates `c.lo k / N`
  have hlo_mem : (fun k : Fin j => (⟨((c.lo k : ℕ) : ℝ)/N, by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hNpos]; exact_mod_cast (le_trans (c.hle k) (c.hhi k))⟩ : unitInterval))
      ∈ cellSet c := by
    intro k
    refine ⟨le_rfl, ?_⟩
    rw [div_le_div_iff_of_pos_right hNpos]; exact_mod_cast c.hle k
  have h2 := hfar m hm _ (hmc hlo_mem) i
  constructor
  · have h3 : (2:ℝ) ≤ (c.lo i : ℝ) := by
      have hh := h2.1
      rw [div_le_div_iff_of_pos_right hNpos] at hh
      exact hh
    have h4 : (2:ℕ) ≤ c.lo i := by exact_mod_cast h3
    omega
  · have h3 : ((c.hi i : ℝ)) / N ≤ 1 - 2/(N:ℝ) := h1.2
    have h4 : ((c.hi i : ℝ)) + 2 ≤ (N:ℝ) := by
      rw [div_le_iff₀ hNpos] at h3
      have h5 : (1 - 2/(N:ℝ)) * (N:ℝ) = (N:ℝ) - 2 := by field_simp
      rw [h5] at h3
      linarith
    have h5 : c.hi i + 2 ≤ N := by exact_mod_cast h4
    omega

/-- The membership in the boundary of the cube. -/
theorem mem_boundary_iff {x : IC j} :
    x ∈ Cube.boundary (Fin j) ↔ ∃ i, x i = 0 ∨ x i = 1 := by
  simp [Cube.boundary]

/-- The spreading of a cell away from the boundary does not move `∂I^j`. -/
theorem nuOf_eq_zero_of_away_of_mem_boundary (hN : 1 ≤ N) {c : CellIdx j N} (hc : Away c)
    {x : IC j} (hx : x ∈ Cube.boundary (Fin j)) : nuOf c x = 0 := by
  obtain ⟨i, hi | hi⟩ := mem_boundary_iff.mp hx
  · have h1 : (1:ℝ) ≤ cellDistCoord c i x := by
      have h2 := cellDistCoord_le c i x
      have h3 : (c.lo i : ℝ) - (N:ℝ) * (x i : ℝ) = (c.lo i : ℝ) := by rw [hi]; simp
      have h4 : (1:ℝ) ≤ (c.lo i : ℝ) := by exact_mod_cast (hc i).1
      linarith
    have h5 : (1:ℝ) ≤ cellDist c x := le_trans h1 (cellDistCoord_le_cellDist c i x)
    rw [nuOf, rOf, min_eq_left (by linarith : (1:ℝ) ≤ cellDist c x),
      max_eq_left (by linarith : (1:ℝ) - 4 * 1 ≤ 0)]
  · have h1 : (1:ℝ) ≤ cellDistCoord c i x := by
      have h2 := cellDistCoord_le' c i x
      have h3 : (N:ℝ) * (x i : ℝ) - (c.hi i : ℝ) = (N:ℝ) - (c.hi i : ℝ) := by rw [hi]; simp
      have h4 : (c.hi i : ℝ) ≤ (N:ℝ) - 1 := by
        have := hc i
        have : (c.hi i : ℝ) ≤ ((N-1:ℕ):ℝ) := by exact_mod_cast this.2
        rw [Nat.cast_sub (by omega : 1 ≤ N)] at this; norm_num at this ⊢; linarith
      linarith
    have h5 : (1:ℝ) ≤ cellDist c x := le_trans h1 (cellDistCoord_le_cellDist c i x)
    rw [nuOf, rOf, min_eq_left (by linarith : (1:ℝ) ≤ cellDist c x),
      max_eq_left (by linarith : (1:ℝ) - 4 * 1 ≤ 0)]

/-! ### The finite type of cells -/

/-- The dimension of a cell is at most `j`. -/
theorem cellDim_le (c : CellIdx j N) : cellDim c ≤ j := by
  rw [cellDim]
  simpa using Finset.card_le_univ (Finset.univ.filter fun i : Fin j => c.lo i < c.hi i)

/-- The index order on cells implies the inclusion of the cells. -/
theorem cellSet_antitone {c c' : CellIdx j N} (h1 : ∀ i, c.lo i ≤ c'.lo i)
    (h2 : ∀ i, c'.hi i ≤ c.hi i) : cellSet c' ⊆ cellSet c := by
  intro x hx i
  have hxi := hx i
  exact ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h1 i) (Nat.cast_nonneg N)) hxi.1,
    le_trans hxi.2 (div_le_div_of_nonneg_right (by exact_mod_cast h2 i) (Nat.cast_nonneg N))⟩

/-- A subcell of the same dimension is equal to the cell. -/
theorem cellIdx_eq_of_le_of_cellDim_eq {c c' : CellIdx j N}
    (h1 : ∀ i, c.lo i ≤ c'.lo i) (h2 : ∀ i, c'.hi i ≤ c.hi i) (hd : cellDim c' = cellDim c) :
    c' = c := by
  have hcardle : (Finset.univ.filter fun k : Fin j => c'.lo k < c'.hi k).card ≤
      (Finset.univ.filter fun k : Fin j => c.lo k < c.hi k).card := by
    apply Finset.card_le_card
    intro k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hk
    have h1k := h1 k
    have h2k := h2 k
    omega
  have e1 : cellDim c' = (Finset.univ.filter fun k : Fin j => c'.lo k < c'.hi k).card := rfl
  have e2 : cellDim c = (Finset.univ.filter fun k : Fin j => c.lo k < c.hi k).card := rfl
  have hcardeq : (Finset.univ.filter fun k : Fin j => c'.lo k < c'.hi k).card =
      (Finset.univ.filter fun k : Fin j => c.lo k < c.hi k).card := by
    rw [← e1, ← e2]
    exact hd
  have hset : (Finset.univ.filter fun k : Fin j => c'.lo k < c'.hi k) =
      (Finset.univ.filter fun k : Fin j => c.lo k < c.hi k) :=
    Finset.eq_of_subset_of_card_le (fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      have h1k := h1 k
      have h2k := h2 k
      omega) (le_of_eq hcardeq.symm)
  have hsub : ∀ i, c'.lo i = c.lo i ∧ c'.hi i = c.hi i := by
    intro i
    have h1i := h1 i
    have h2i := h2 i
    by_cases hlt : c.lo i < c.hi i
    · have hlt' : c'.lo i < c'.hi i := by
        have : i ∈ (Finset.univ.filter fun k : Fin j => c.lo k < c.hi k) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hlt
        rw [← hset] at this
        simpa using this
      have st := c.hstep i
      exact ⟨le_antisymm (by omega) h1i, le_antisymm h2i (by omega)⟩
    · have hge : c.hi i ≤ c.lo i := le_of_not_gt hlt
      refine ⟨le_antisymm ?_ h1i, le_antisymm h2i ?_⟩
      · exact le_trans (le_trans (c'.hle i) h2i) hge
      · exact le_trans (le_trans hge h1i) (c'.hle i)
  have hl : c'.lo = c.lo := funext fun i => (hsub i).1
  have hh : c'.hi = c.hi := funext fun i => (hsub i).2
  obtain ⟨l, hh', _, _, _⟩ := c'
  obtain ⟨l', hh'', _, _, _⟩ := c
  simp only at hl hh
  subst hl
  subst hh
  rfl

/-- The coding of a cell index by a pair of functions into `Fin (N+1)`; the cells of the
`N`-grid inject into `(Fin j → Fin (N+1)) × (Fin j → Fin (N+1))`, so they form a finite type. -/
def cellCode (c : CellIdx j N) :
    (Fin j → Fin (N+1)) × (Fin j → Fin (N+1)) :=
  (fun i => (⟨c.lo i, Nat.lt_succ_of_le (le_trans (c.hle i) (c.hhi i))⟩ : Fin (N+1)),
   fun i => (⟨c.hi i, Nat.lt_succ_of_le (c.hhi i)⟩ : Fin (N+1)))

theorem cellCode_injective : Function.Injective (cellCode (j := j) (N := N)) := by
  intro c c' h
  have h1 : c.lo = c'.lo := by
    funext i
    have := congrFun (congrArg Prod.fst h) i
    exact congrArg Fin.val this
  have h2 : c.hi = c'.hi := by
    funext i
    have := congrFun (congrArg Prod.snd h) i
    exact congrArg Fin.val this
  obtain ⟨l, hh, hle, hstep, hhi⟩ := c
  obtain ⟨l', hh', hle', hstep', hhi'⟩ := c'
  simp only at h1 h2
  subst h1
  subst h2
  rfl

instance instDecidableEqCellIdx : DecidableEq (CellIdx j N) :=
  cellCode_injective.decidableEq

noncomputable instance instFintypeCellIdx : Fintype (CellIdx j N) :=
  Fintype.ofInjective (cellCode (j := j) (N := N)) cellCode_injective

end Work.ThomBordism.TwoSet
