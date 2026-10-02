import Mathlib
import Submission.Work.ThomBordism.TwoSet.Basic
import Submission.Work.ThomBordism.TwoSet.Subdivision

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The closed cells of the `N`-grid, their dimension, and the clamp onto a cell

Vocabulary for the cell-by-cell compression argument of
`Work.ThomBordism.TwoSet.compressRel_twoSet`.

A *cell* of the `N`-grid of `I^j` is a product `∏ᵢ [aᵢ/N, bᵢ/N]` with `aᵢ ≤ bᵢ ≤ aᵢ + 1 ≤ N + 1`.
Its *dimension* is the number of coordinates with `bᵢ > aᵢ` (the "interval" coordinates); its
*relative boundary* is the set of its points in which some interval coordinate is at an endpoint.

* `cellSet`, `cellRelbd`, `cellDim` — the cell, its relative boundary, its dimension;
* `clampCell` — the coordinatewise clamp of `I^j` onto a cell (a continuous retraction);
* `cOf` — the minimal cell containing a point;
* `cOf_contains_of_clamp_not_relbd` — the KEY LEMMA.
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

variable {j N : ℕ}

/-- A cell index of the `N`-grid: maps `lo ≤ hi ≤ lo + 1 ≤ N + 1`. -/
structure CellIdx (j N : ℕ) where
  lo : Fin j → ℕ
  hi : Fin j → ℕ
  hle : ∀ i, lo i ≤ hi i
  hstep : ∀ i, hi i ≤ lo i + 1
  hhi : ∀ i, hi i ≤ N

/-- The closed cell of the index `c`. -/
noncomputable def cellSet (c : CellIdx j N) : Set (IC j) :=
  {x | ∀ i, (c.lo i : ℝ) / N ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (c.hi i : ℝ) / N}

@[simp] theorem mem_cellSet {c : CellIdx j N} {x : IC j} :
    x ∈ cellSet c ↔ ∀ i, (c.lo i : ℝ) / N ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (c.hi i : ℝ) / N :=
  Iff.rfl

/-- The coordinate interval of a cell in coordinate `i`. -/
noncomputable def coordInterval (c : CellIdx j N) (i : Fin j) : Set unitInterval :=
  {t : unitInterval | (c.lo i : ℝ) / N ≤ (t : ℝ) ∧ (t : ℝ) ≤ (c.hi i : ℝ) / N}

@[simp] theorem mem_coordInterval {c : CellIdx j N} {i : Fin j} {t : unitInterval} :
    t ∈ coordInterval c i ↔ (c.lo i : ℝ) / N ≤ (t : ℝ) ∧ (t : ℝ) ≤ (c.hi i : ℝ) / N :=
  Iff.rfl

/-- The relative boundary of the cell `c`. -/
noncomputable def cellRelbd (c : CellIdx j N) : Set (IC j) :=
  {x | ∃ i, c.lo i < c.hi i ∧
    ((x i : ℝ) = (c.lo i : ℝ) / N ∨ (x i : ℝ) = (c.hi i : ℝ) / N)}

@[simp] theorem mem_cellRelbd {c : CellIdx j N} {x : IC j} :
    x ∈ cellRelbd c ↔ ∃ i, c.lo i < c.hi i ∧
      ((x i : ℝ) = (c.lo i : ℝ) / N ∨ (x i : ℝ) = (c.hi i : ℝ) / N) := Iff.rfl

/-- The dimension of the cell `c`: its number of interval coordinates. -/
def cellDim (c : CellIdx j N) : ℕ :=
  (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)).card

/-- The real-valued coordinate clamp onto `[l/N, u/N] ∩ [0,1]`, for `l ≤ u ≤ N`, `N ≥ 1`. -/
noncomputable def clampR (N : ℕ) (l u : ℕ) (t : ℝ) : ℝ :=
  max ((l : ℝ) / N) (min ((u : ℝ) / N) t)

theorem clampR_mem (N : ℕ) (hN : 1 ≤ N) {l u : ℕ} (hle : l ≤ u) (hu : u ≤ N)
    (t : unitInterval) : 0 ≤ clampR N l u (t : ℝ) ∧ clampR N l u (t : ℝ) ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hl1 : ((l : ℝ)) / N ≤ 1 := by
    rw [div_le_one hNpos]; exact_mod_cast (le_trans hle hu)
  have hu1 : ((u : ℝ)) / N ≤ 1 := by
    rw [div_le_one hNpos]; exact_mod_cast hu
  refine ⟨?_, ?_⟩
  · rw [clampR]; exact le_trans (by positivity) (le_max_left _ _)
  · rw [clampR]; exact max_le hl1 (le_trans (min_le_left _ _) hu1)

/-- The coordinate clamp as an element of `[0,1]`. -/
noncomputable def clampU (N : ℕ) (hN : 1 ≤ N) {l u : ℕ} (hle : l ≤ u) (hu : u ≤ N)
    (t : unitInterval) : unitInterval :=
  ⟨clampR N l u t, clampR_mem N hN hle hu t⟩

@[simp] theorem clampU_val (N : ℕ) (hN : 1 ≤ N) {l u : ℕ} (hle : l ≤ u) (hu : u ≤ N)
    (t : unitInterval) : ((clampU N hN hle hu t : unitInterval) : ℝ) = clampR N l u t := rfl

theorem continuous_clampU (N : ℕ) (hN : 1 ≤ N) {l u : ℕ} (hle : l ≤ u) (hu : u ≤ N) :
    Continuous (clampU N hN hle hu) :=
  Continuous.subtype_mk
    ((continuous_const.max (continuous_const.min continuous_id)).comp
      continuous_subtype_val) _

/-- The coordinatewise clamp of `I^j` onto the cell `c`. -/
noncomputable def clampCell (c : CellIdx j N) (hN : 1 ≤ N) : C(IC j, IC j) :=
  ⟨fun x i => clampU N hN (c.hle i) (c.hhi i) (x i),
   continuous_pi (fun i => (continuous_clampU N hN (c.hle i) (c.hhi i)).comp
     (continuous_apply i))⟩

@[simp] theorem clampCell_apply (c : CellIdx j N) (hN : 1 ≤ N) (x : IC j) (i : Fin j) :
    clampCell c hN x i = clampU N hN (c.hle i) (c.hhi i) (x i) := rfl

theorem clampCell_val (c : CellIdx j N) (hN : 1 ≤ N) (x : IC j) (i : Fin j) :
    (((clampCell c hN x i : unitInterval)) : ℝ) = clampR N (c.lo i) (c.hi i) (x i : ℝ) := by
  rw [clampCell_apply, clampU_val]

theorem clampCell_mem (c : CellIdx j N) (hN : 1 ≤ N) (x : IC j) :
    clampCell c hN x ∈ cellSet c := by
  intro i
  have hle' : ((c.lo i : ℝ)) / N ≤ ((c.hi i : ℝ)) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast c.hle i) (Nat.cast_nonneg N)
  simp only [clampCell_val, clampR, mem_cellSet]
  exact ⟨le_max_left _ _, max_le hle' (min_le_left _ _)⟩

theorem clampCell_eq_self (c : CellIdx j N) (hN : 1 ≤ N) {x : IC j} (hx : x ∈ cellSet c) :
    clampCell c hN x = x := by
  funext i
  have hi := (mem_cellSet.mp hx) i
  have hle' : ((c.lo i : ℝ)) / N ≤ ((c.hi i : ℝ)) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast c.hle i) (Nat.cast_nonneg N)
  apply Subtype.ext
  show clampR N (c.lo i) (c.hi i) (x i : ℝ) = (x i : ℝ)
  rw [clampR, max_eq_right (le_min hle' hi.1), min_eq_right hi.2]

/-- The minimal cell of the `N`-grid containing a point. -/
noncomputable def cOf (N : ℕ) (x : IC j) : CellIdx j N where
  lo i := ⌊(N : ℝ) * (x i : ℝ)⌋₊
  hi i := ⌈(N : ℝ) * (x i : ℝ)⌉₊
  hle i := Nat.floor_le_ceil _
  hstep i := Nat.ceil_le_floor_add_one _
  hhi i := by
    rw [Nat.ceil_le]
    have hx1 : (x i : ℝ) ≤ 1 := (x i).2.2
    exact mul_le_of_le_one_right (Nat.cast_nonneg N) hx1

@[simp] theorem cOf_lo (N : ℕ) (x : IC j) (i : Fin j) :
    (cOf N x).lo i = ⌊(N : ℝ) * (x i : ℝ)⌋₊ := rfl

@[simp] theorem cOf_hi (N : ℕ) (x : IC j) (i : Fin j) :
    (cOf N x).hi i = ⌈(N : ℝ) * (x i : ℝ)⌉₊ := rfl

theorem mem_cOf (N : ℕ) (hN : 1 ≤ N) (x : IC j) : x ∈ cellSet (cOf N x) := by
  intro i
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hfloor : (((⌊(N : ℝ) * (x i : ℝ)⌋₊ : ℕ) : ℝ)) ≤ (N : ℝ) * (x i : ℝ) :=
    Nat.floor_le (mul_nonneg (le_of_lt hNpos) (x i).2.1)
  have hceil : (N : ℝ) * (x i : ℝ) ≤ (((⌈(N : ℝ) * (x i : ℝ)⌉₊ : ℕ) : ℝ)) :=
    Nat.le_ceil _
  refine ⟨?_, ?_⟩
  · calc (((⌊(N : ℝ) * (x i : ℝ)⌋₊ : ℕ) : ℝ)) / N
        ≤ ((N : ℝ) * (x i : ℝ)) / N := div_le_div_of_nonneg_right hfloor (le_of_lt hNpos)
      _ = (x i : ℝ) := by field_simp
  · calc (x i : ℝ) = ((N : ℝ) * (x i : ℝ)) / N := by field_simp
      _ ≤ (((⌈(N : ℝ) * (x i : ℝ)⌉₊ : ℕ) : ℝ)) / N :=
          div_le_div_of_nonneg_right hceil (le_of_lt hNpos)

/-- The real clamp of a point of an interval coordinate with `l < u ≤ N` has strict interior
values exactly when the point does. -/
theorem clampR_inl_interior {N : ℕ} (hN : 1 ≤ N) {l u : ℕ} (h : l < u) (hu : u ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hne : clampR N l u t ≠ (l : ℝ) / N)
    (hne2 : clampR N l u t ≠ (u : ℝ) / N) :
    (l : ℝ) / N < t ∧ t < (u : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlu : ((l : ℝ)) / N < ((u : ℝ)) / N := by
    rw [div_lt_div_iff_of_pos_right hNpos]; exact_mod_cast h
  rw [clampR] at hne hne2
  constructor
  · by_contra hcon
    push_neg at hcon
    have h1 : min ((u : ℝ) / N) t = t := min_eq_right (le_trans hcon (le_of_lt hlu))
    rw [h1, max_eq_left hcon] at hne
    exact hne rfl
  · by_contra hcon
    push_neg at hcon
    have h1 : min ((u : ℝ) / N) t = (u : ℝ) / N := min_eq_left hcon
    rw [h1, max_eq_right (le_of_lt hlu)] at hne2
    exact hne2 rfl

/-- **The KEY LEMMA.**  Let `c` be a grid cell of the `N`-grid with `N ≥ 1`, and let `x : I^j` have
all coordinates within `1/(4N)` of the corresponding coordinate interval of `c`, and assume that
the clamp of `x` onto `c` is not on the relative boundary of `c`.  Then `cOf N x` (the minimal cell
containing `x`) contains the cell `c`; and if `x ∉ cellSet c`, then `cellDim (cOf N x) > cellDim c`. -/
theorem cOf_contains_of_clamp_not_relbd (N : ℕ) (hN : 1 ≤ N) (c : CellIdx j N) {x : IC j}
    (hclose : ∀ i, (N : ℝ) * (x i : ℝ) < (c.lo i : ℝ) + 1 / 4 ∧
      (c.hi i : ℝ) - 1 / 4 < (N : ℝ) * (x i : ℝ))
    (hclamp : clampCell c hN x ∉ cellRelbd c) :
    (∀ i, (cOf N x).lo i ≤ c.lo i) ∧ (∀ i, c.hi i ≤ (cOf N x).hi i) ∧
      (x ∉ cellSet c → cellDim c < cellDim (cOf N x)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hzx : ∀ i, (0 : ℝ) ≤ (N : ℝ) * (x i : ℝ) :=
    fun i => mul_nonneg (le_of_lt hNpos) (x i).2.1
  -- (1): the floor of `N xᵢ` is at most `loᵢ`
  have key1 : ∀ i, (cOf N x).lo i ≤ c.lo i := by
    intro i
    rw [cOf_lo]
    have h : (N : ℝ) * (x i : ℝ) < (c.lo i : ℝ) + 1 := by linarith [(hclose i).1]
    have h2 : ⌊(N : ℝ) * (x i : ℝ)⌋₊ < c.lo i + 1 :=
      (Nat.floor_lt (hzx i)).mpr (by push_cast; linarith)
    omega
  -- (2): the ceiling of `N xᵢ` is at least `hiᵢ`
  have key2 : ∀ i, c.hi i ≤ (cOf N x).hi i := by
    intro i
    rw [cOf_hi]
    have h : (c.hi i : ℝ) - 1 < (N : ℝ) * (x i : ℝ) := by linarith [(hclose i).2]
    by_cases h0 : c.hi i = 0
    · omega
    · have hone : (1 : ℕ) ≤ c.hi i := Nat.one_le_iff_ne_zero.mpr h0
      have h1 : (((c.hi i - 1 : ℕ)) : ℝ) = (c.hi i : ℝ) - 1 := by
        push_cast [Nat.cast_sub hone]; ring
      have h2 : (((c.hi i - 1 : ℕ)) : ℝ) < (N : ℝ) * (x i : ℝ) := by rw [h1]; exact h
      have h3 : (c.hi i - 1 : ℕ) < ⌈(N : ℝ) * (x i : ℝ)⌉₊ := Nat.lt_ceil.mpr h2
      omega
  -- the clamped coordinate is never an endpoint of an interval coordinate
  have hnotR : ∀ i, c.lo i < c.hi i →
      clampR N (c.lo i) (c.hi i) (x i : ℝ) ≠ (c.lo i : ℝ) / N ∧
      clampR N (c.lo i) (c.hi i) (x i : ℝ) ≠ (c.hi i : ℝ) / N := by
    intro i hlt
    constructor
    · intro hcon
      apply hclamp
      rw [mem_cellRelbd]
      exact ⟨i, hlt, Or.inl (by rw [clampCell_val]; exact hcon)⟩
    · intro hcon
      apply hclamp
      rw [mem_cellRelbd]
      exact ⟨i, hlt, Or.inr (by rw [clampCell_val]; exact hcon)⟩
  refine ⟨key1, key2, fun hx => ?_⟩
  -- a coordinate of `x` missing the cell
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ∉ coordInterval c i := by
    by_contra hcon
    push_neg at hcon
    exact hx (mem_cellSet.mpr hcon)
  -- that coordinate must be a point coordinate of `c`
  have hpt : c.lo i₀ = c.hi i₀ := by
    by_contra hne
    have hlt : c.lo i₀ < c.hi i₀ := lt_of_le_of_ne (c.hle i₀) hne
    have hcl := hnotR i₀ hlt
    have hint := clampR_inl_interior hN hlt (c.hhi i₀) (x i₀).2 hcl.1 hcl.2
    exact absurd ⟨le_of_lt hint.1, le_of_lt hint.2⟩ hi₀
  -- `N x i₀ ≠ lo i₀`
  have hne : (N : ℝ) * (x i₀ : ℝ) ≠ (c.lo i₀ : ℝ) := by
    intro hcon
    apply hi₀
    have hx_eq : (x i₀ : ℝ) = (c.lo i₀ : ℝ) / N := by rw [← hcon]; field_simp
    refine (mem_coordInterval).mpr ⟨?_, ?_⟩ <;> (rw [hx_eq, hpt]) <;> rfl
  -- hence `⌊N x i₀⌋ ≠ ⌈N x i₀⌉`
  have hnonInt : ⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ ≠ ⌈(N : ℝ) * (x i₀ : ℝ)⌉₊ := by
    intro hcon
    have hfl : ((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) * (x i₀ : ℝ) :=
      Nat.floor_le (hzx i₀)
    have hce : (N : ℝ) * (x i₀ : ℝ) ≤ ((⌈(N : ℝ) * (x i₀ : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    rw [hcon] at hfl
    have heq : (N : ℝ) * (x i₀ : ℝ) = ((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ) := by
      rw [hcon]; exact le_antisymm hce hfl
    have hlt : ((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ) < (c.lo i₀ : ℝ) + 1 / 4 := by
      rw [← heq]; exact (hclose i₀).1
    have hgt : (c.lo i₀ : ℝ) - 1 / 4 < ((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ) := by
      rw [← heq]
      have h := (hclose i₀).2
      rw [← hpt] at h
      exact h
    have hh1 : ⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ ≤ c.lo i₀ := by
      by_contra hc
      push_neg at hc
      have h2 : (((c.lo i₀ : ℕ) : ℝ)) + 1 ≤ ((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ) := by
        have hcast : (((c.lo i₀ : ℕ) : ℝ)) + 1 = (((c.lo i₀ + 1 : ℕ)) : ℝ) := by push_cast; ring
        rw [hcast]
        exact_mod_cast hc
      linarith
    have hh2 : c.lo i₀ ≤ ⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ := by
      by_contra hc
      push_neg at hc
      have h2 : (((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ)) + 1 ≤ (c.lo i₀ : ℝ) := by
        have hcast : (((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ)) + 1 =
            (((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ + 1 : ℕ)) : ℝ) := by push_cast; ring
        rw [hcast]
        exact_mod_cast hc
      linarith
    exact hne (by rw [heq, le_antisymm hh1 hh2])
  -- interval coordinates of `c` are interval coordinates of `cOf N x`
  have hsub : (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) ⊆
      (Finset.univ.filter (fun i : Fin j =>
        ⌊(N : ℝ) * (x i : ℝ)⌋₊ < ⌈(N : ℝ) * (x i : ℝ)⌉₊)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hcl := hnotR i hi
    have hint := clampR_inl_interior hN hi (c.hhi i) (x i).2 hcl.1 hcl.2
    have hz1 : (c.lo i : ℝ) < (N : ℝ) * (x i : ℝ) := by
      have h := hint.1
      rw [div_lt_iff₀ hNpos] at h
      linarith
    have hz2 : (N : ℝ) * (x i : ℝ) < (c.hi i : ℝ) := by
      have h := hint.2
      rw [lt_div_iff₀ hNpos] at h
      linarith
    have hstep : c.hi i = c.lo i + 1 := by have := c.hstep i; omega
    have e1 : ⌊(N : ℝ) * (x i : ℝ)⌋₊ = c.lo i := by
      have h1 : c.lo i ≤ ⌊(N : ℝ) * (x i : ℝ)⌋₊ := Nat.le_floor (le_of_lt hz1)
      have h2 : ⌊(N : ℝ) * (x i : ℝ)⌋₊ < c.lo i + 1 := by
        refine (Nat.floor_lt (hzx i)).mpr ?_
        rw [hstep] at hz2
        exact hz2
      omega
    have e2 : ⌈(N : ℝ) * (x i : ℝ)⌉₊ = c.lo i + 1 := by
      have h1 : c.lo i < ⌈(N : ℝ) * (x i : ℝ)⌉₊ := Nat.lt_ceil.mpr hz1
      have h2 : ⌈(N : ℝ) * (x i : ℝ)⌉₊ ≤ c.lo i + 1 := by
        rw [Nat.ceil_le]
        rw [hstep] at hz2
        exact le_of_lt hz2
      omega
    rw [e1, e2] <;> omega
  have hmemB : i₀ ∈ (Finset.univ.filter (fun i : Fin j =>
      ⌊(N : ℝ) * (x i : ℝ)⌋₊ < ⌈(N : ℝ) * (x i : ℝ)⌉₊)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_le_of_ne (Nat.floor_le_ceil _) hnonInt
  have hnotmemA : i₀ ∉ (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hssub : (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) ⊂
      (Finset.univ.filter (fun i : Fin j =>
        ⌊(N : ℝ) * (x i : ℝ)⌋₊ < ⌈(N : ℝ) * (x i : ℝ)⌉₊)) :=
    (Finset.ssubset_iff_of_subset hsub).mpr ⟨i₀, hmemB, hnotmemA⟩
  have hcard := Finset.card_lt_card hssub
  have hgoal : cellDim c < cellDim (cOf N x) := by
    rw [cellDim, cellDim]
    exact hcard
  exact hgoal


/-- The point  of . -/
noncomputable def segMap (x y : IC j) (t : I) : IC j :=
  fun i => ⟨(1 - (t : ℝ)) * (x i : ℝ) + (t : ℝ) * (y i : ℝ), by
    have hx0 := (x i).2.1; have hx1 := (x i).2.2
    have hy0 := (y i).2.1; have hy1 := (y i).2.2
    have ht0 := (t : I).2.1; have ht1 := (t : I).2.2
    constructor <;> nlinarith⟩

@[simp] theorem segMap_zero (x y : IC j) : segMap x y 0 = x := by
  funext i
  apply Subtype.ext
  simp only [segMap]
  norm_num

@[simp] theorem segMap_one (x y : IC j) : segMap x y 1 = y := by
  funext i
  apply Subtype.ext
  simp only [segMap]
  norm_num

theorem continuous_segMap (j : ℕ) :
    Continuous fun p : IC j × IC j × I => segMap p.1 p.2.1 p.2.2 := by
  refine continuous_pi (fun i => Continuous.subtype_mk ?_ _)
  have hx : Continuous fun p : IC j × IC j × I => (p.1 i : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)
  have hy : Continuous fun p : IC j × IC j × I => (p.2.1 i : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply i).comp (continuous_fst.comp continuous_snd))
  have ht : Continuous fun p : IC j × IC j × I => (p.2.2 : ℝ) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  exact ((continuous_const.sub ht).mul hx).add (ht.mul hy)

/-- The relative boundary of a cell consists of points of strictly smaller minimal-cell
dimension. -/
theorem cellDim_cOf_lt_of_mem_cellRelbd (N : ℕ) (hN : 1 ≤ N) {c : CellIdx j N} {z : IC j}
    (hz : z ∈ cellRelbd c) (hzc : z ∈ cellSet c) : cellDim (cOf N z) < cellDim c := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- each coordinate interval of cOf N z is contained in the corresponding one of c
  have hlo : ∀ i, c.lo i ≤ (cOf N z).lo i := by
    intro i
    have h := (mem_cellSet.mp hzc i).1
    rw [cOf_lo]
    refine Nat.le_floor ?_
    rw [div_le_iff₀ hNpos] at h
    linarith
  have hhi : ∀ i, (cOf N z).hi i ≤ c.hi i := by
    intro i
    have h := (mem_cellSet.mp hzc i).2
    rw [cOf_hi, Nat.ceil_le]
    rw [le_div_iff₀ hNpos] at h
    linarith
  have hsub : (Finset.univ.filter (fun i : Fin j => (cOf N z).lo i < (cOf N z).hi i)) ⊆
      (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_le_of_lt (hlo i) (lt_of_lt_of_le hi (hhi i))
  obtain ⟨i₀, hi₀lt, hi₀end⟩ := hz
  have hnot : i₀ ∉ (Finset.univ.filter (fun i : Fin j => (cOf N z).lo i < (cOf N z).hi i)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have : (cOf N z).lo i₀ = (cOf N z).hi i₀ := by
      rcases hi₀end with h | h
      · have hz_eq : (N : ℝ) * (z i₀ : ℝ) = (c.lo i₀ : ℝ) := by rw [h]; field_simp
        rw [cOf_lo, cOf_hi, hz_eq, Nat.floor_natCast, Nat.ceil_natCast]
      · have hz_eq : (N : ℝ) * (z i₀ : ℝ) = (c.hi i₀ : ℝ) := by rw [h]; field_simp
        rw [cOf_lo, cOf_hi, hz_eq, Nat.floor_natCast, Nat.ceil_natCast]
    omega
  have hmem : i₀ ∈ (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi₀lt
  have hssub : (Finset.univ.filter (fun i : Fin j => (cOf N z).lo i < (cOf N z).hi i)) ⊂
      (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) :=
    (Finset.ssubset_iff_of_subset hsub).mpr ⟨i₀, hmem, hnot⟩
  have hcard := Finset.card_lt_card hssub
  rw [cellDim, cellDim]
  exact hcard

end Work.ThomBordism.TwoSet
