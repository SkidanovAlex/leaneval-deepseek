import Mathlib
import Submission.Work.EKLC6Core.cellW_depth_aux
import Submission.Work.EKLC6Core.InjRadius
import Submission.Work.EKLC6Core.exists_dense_seq_X3
import Submission.Work.EKLC6Core.shell_radius_nullfrontier
import Submission.Work.EKLC6Core.vball_packing_uniform
import Submission.Work.EKLC6Core.tsum_measure_le_of_card_bound
import Submission.Work.EKLComp.inv_mem_V
import Submission.Work.Misiurewicz.closure_Vball_subset_vMove_le
import Submission.Work.EKLC6Core.injCap_le_mul_of_mem_Vball

/-!
# `Work.EKLC6Core.cell_relthin_cover2`

Relative thinness of a cell cover (`Q`, `δ`, `g`, `C`, `α` covering a conull set by injective
balls whose "relative margin" blow-up is a power of `ε`).

## Scheme

* Fix a dense sequence `y : ℕ → X₃` and the *separation radius* `sepRad x = injCap x / 2^20`.
* Select, by a greedy recursion over the sequence, a subfamily `sel ⊆ ℕ` which is *symmetric
  separated*: for `j < m` both `y m ∉ Vball (sepRad (y j)) (y j)` and
  `y j ∉ Vball (sepRad (y m)) (y m)`.  The greedy is *maximal* in the strong sense that an
  index `m ∉ sel` has an immediate witness `j ∈ sel`, `j < m`, so that every point of `X₃` is
  covered by a `cellLo`-ball of a *selected* index in one step.
* For `n ∈ sel` the radius `cellRad μ y n ∈ [injCap (y n)/4096, injCap (y n)/2048]` is chosen by
  `Work.EKLC6Core.shell_radius_nullfrontier`: the frontier is `μ`-null and the relative shell
  measures are linearly bounded by `32 δ · μ (Vball (2 cellHi) (y n))`.
* The cells `Qcell` are the disjointification `cellBall k ∩ ⋂_{l<k} (closure (cellBall l))ᶜ`.
* `δ k = 2 * cellRad`, `g k` a lift of `y k`.
* The set of points of small relative margin inside their cell sits in the union of the
  two-sided shells of the ball boundaries; the shells have mass `≤ 32 ρ · μ (countBall k)` and the
  counting balls have bounded multiplicity (uniformly in the scale, by
  `Work.EKLC6Core.vball_packing_uniform`), because the selected indices are separated at the
  `sepRad` scale and the corresponding points have comparable `injCap`.

The final estimate is `μ (bad ε) ≤ C ε` with `α = 1`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

open Classical

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## 1. The scales -/

/-- The separation radius attached to a point: `injCap x / 2^20`. -/
def sepRad (x : X3) : ℝ := injCap x / 1048576

/-- The lower end of the admissible good-radius interval: `injCap x / 4096 = 256 * sepRad x`. -/
def cellLo (x : X3) : ℝ := injCap x / 4096

/-- The upper end of the admissible good-radius interval: `injCap x / 2048 = 512 * sepRad x`. -/
def cellHi (x : X3) : ℝ := injCap x / 2048

theorem sepRad_pos (x : X3) : 0 < sepRad x :=
  div_pos (injCap_pos x) (by norm_num)

theorem cellLo_pos (x : X3) : 0 < cellLo x :=
  div_pos (injCap_pos x) (by norm_num)

theorem cellHi_pos (x : X3) : 0 < cellHi x :=
  div_pos (injCap_pos x) (by norm_num)

theorem cellLo_lt_cellHi (x : X3) : cellLo x < cellHi x := by
  have h := injCap_pos x
  rw [cellLo, cellHi]
  linarith

theorem sepRad_le_cellLo (x : X3) : sepRad x ≤ cellLo x := by
  have h := injCap_pos x
  rw [sepRad, cellLo]
  linarith

theorem cellLo_eq (x : X3) : cellLo x = 256 * sepRad x := by
  rw [cellLo, sepRad]; ring

theorem cellHi_eq (x : X3) : cellHi x = 512 * sepRad x := by
  rw [cellHi, sepRad]; ring

theorem cellHi_le (x : X3) : cellHi x ≤ 1 / 4096 := by
  have h := injCap_le_half x
  rw [cellHi]
  linarith

theorem sepRad_le_one (x : X3) : sepRad x ≤ 1 := by
  have h := injCap_le_half x
  rw [sepRad]
  linarith

/-! ## 2. The greedy selection -/

/-- `selCond y S m` says that `y m` is separated, in *both* directions, from every point
`y j`, `j ∈ S`, at the two `sepRad` scales. -/
def selCond (y : ℕ → X3) (S : Finset ℕ) (m : ℕ) : Prop :=
  ∀ j ∈ S, y m ∉ Work.EKLComp.Vball (sepRad (y j)) (y j) ∧
    y j ∉ Work.EKLComp.Vball (sepRad (y m)) (y m)

/-- The indices selected before `m`. -/
def selN (y : ℕ → X3) : ℕ → Finset ℕ
  | 0 => ∅
  | (m + 1) => if selCond y (selN y m) m then insert m (selN y m) else selN y m

/-- The greedy maximal separated subfamily of the dense sequence. -/
def sel (y : ℕ → X3) : Set ℕ := {n | n ∈ selN y (n + 1)}

theorem selN_succ_subset (y : ℕ → X3) (m : ℕ) : selN y m ⊆ selN y (m + 1) := by
  rw [selN]
  split_ifs
  · intro x hx; exact Finset.mem_insert_of_mem hx
  · exact subset_rfl

theorem mem_selN_lt (y : ℕ → X3) : ∀ {m j : ℕ}, j ∈ selN y m → j < m := by
  intro m
  induction m with
  | zero =>
      intro j hj
      rw [selN] at hj
      exact absurd hj (by simp)
  | succ m ih =>
      intro j hj
      rw [selN] at hj
      split_ifs at hj with h
      · rcases Finset.mem_insert.mp hj with h' | h'
        · omega
        · exact Nat.lt_succ_of_lt (ih h')
      · exact Nat.lt_succ_of_lt (ih hj)

theorem selN_mono (y : ℕ → X3) : ∀ {m m' : ℕ}, m ≤ m' → selN y m ⊆ selN y m' := by
  intro m m' h
  have key : ∀ d : ℕ, selN y m ⊆ selN y (m + d) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        have h1 : m + (d + 1) = m + d + 1 := by omega
        rw [h1]
        exact ih.trans (selN_succ_subset y (m + d))
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact key d

theorem mem_selN_imp (y : ℕ → X3) : ∀ m j, j ∈ selN y m → j ∈ sel y := by
  intro m
  induction m with
  | zero =>
      intro j hj
      rw [selN] at hj
      exact absurd hj (by simp)
  | succ k ih =>
      intro j hj
      rw [selN] at hj
      split_ifs at hj with h
      · rcases Finset.mem_insert.mp hj with h' | h'
        · rw [h']
          show k ∈ selN y (k + 1)
          rw [selN, if_pos h]
          exact Finset.mem_insert_self k (selN y k)
        · exact ih j h'
      · exact ih j hj

theorem mem_selN_iff (y : ℕ → X3) {m j : ℕ} (hj : j < m) : (j ∈ selN y m ↔ j ∈ sel y) :=
  ⟨mem_selN_imp y m j, fun h => selN_mono y (Nat.succ_le_of_lt hj) h⟩

theorem sel_iff (y : ℕ → X3) (n : ℕ) : n ∈ sel y ↔ selCond y (selN y n) n := by
  show n ∈ selN y (n + 1) ↔ _
  rw [selN]
  by_cases hc : selCond y (selN y n) n
  · rw [if_pos hc]
    exact ⟨fun _ => hc, fun _ => Finset.mem_insert_self n (selN y n)⟩
  · rw [if_neg hc]
    exact ⟨fun h => absurd h (by have := mem_selN_lt y h; omega), fun h => absurd h hc⟩

theorem mem_sel_iff (y : ℕ → X3) (n : ℕ) :
    n ∈ sel y ↔ ∀ j, j < n → j ∈ sel y →
      (y n ∉ Work.EKLComp.Vball (sepRad (y j)) (y j) ∧
        y j ∉ Work.EKLComp.Vball (sepRad (y n)) (y n)) := by
  rw [sel_iff]
  constructor
  · intro h j hj hjs
    have hjn : j ∈ selN y n := (mem_selN_iff y hj).mpr hjs
    exact h j hjn
  · intro h j hj
    have hjn : j < n := mem_selN_lt y hj
    exact h j hjn ((mem_selN_iff y hjn).mp hj)

theorem exists_sel_witness (y : ℕ → X3) {n : ℕ} (hn : n ∉ sel y) :
    ∃ j, j < n ∧ j ∈ sel y ∧ (y n ∈ Work.EKLComp.Vball (sepRad (y j)) (y j) ∨
      y j ∈ Work.EKLComp.Vball (sepRad (y n)) (y n)) := by
  rw [mem_sel_iff] at hn
  push_neg at hn
  obtain ⟨j, hj, hjs, hcase⟩ := hn
  refine ⟨j, hj, hjs, ?_⟩
  by_cases hA : y n ∈ Work.EKLComp.Vball (sepRad (y j)) (y j)
  · exact Or.inl hA
  · exact Or.inr (hcase hA)

theorem sel_sep (y : ℕ → X3) {n m : ℕ} (hn : n ∈ sel y) (hm : m ∈ sel y) (hne : n ≠ m) :
    y m ∉ Work.EKLComp.Vball (sepRad (y n)) (y n) ∧
      y n ∉ Work.EKLComp.Vball (sepRad (y m)) (y m) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hc := (mem_sel_iff y m).mp hm n h hn
    exact ⟨hc.1, hc.2⟩
  · have hc := (mem_sel_iff y n).mp hn m h hm
    exact ⟨hc.2, hc.1⟩

theorem sel_inj (y : ℕ → X3) {n m : ℕ} (hn : n ∈ sel y) (hm : m ∈ sel y)
    (h : y n = y m) : n = m := by
  by_contra hne
  have hball : y m ∈ Work.EKLComp.Vball (sepRad (y n)) (y n) := by
    refine ⟨1, (Work.EKLContract.Lemmas.V_open_one _ (sepRad_pos (y n))).2, ?_⟩
    show (1 : SL3) • y n = y m
    rw [one_smul, h]
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (sel_sep y hn hm hne).1 hball
  · exact (sel_sep y hm hn (Ne.symm hne)).2 hball

/-! ## 3. The good radius -/

/-- The existence statement underlying `cellRad`. -/
theorem exists_cellRad (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (n : ℕ) :
    ∃ s : ℝ, cellLo (y n) ≤ s ∧ s ≤ cellHi (y n) ∧
      μ (frontier (Work.EKLComp.Vball s (y n))) = 0 ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        (μ (Work.EKLComp.Vball (s * (1 + δ)) (y n))).toReal -
          (μ (Work.EKLComp.Vball (s * (1 - δ)) (y n))).toReal
        ≤ 32 * δ * (μ (Work.EKLComp.Vball (2 * cellHi (y n)) (y n))).toReal) := by
  obtain ⟨s, h1, h2, h3, h4⟩ :=
    shell_radius_nullfrontier μ (y n) (cellLo_pos (y n)) (cellLo_lt_cellHi (y n))
  refine ⟨s, h1, h2, h3, fun δ hδ hδ1 => ?_⟩
  have hb := h4 δ hδ hδ1
  have hden : cellHi (y n) - cellLo (y n) ≠ 0 := by
    have h := cellLo_lt_cellHi (y n); linarith
  have hc : 16 * cellHi (y n) / (cellHi (y n) - cellLo (y n)) = 32 := by
    rw [div_eq_iff hden, cellHi, cellLo]
    ring
  rwa [hc] at hb

/-- The good radius attached to `n`: for `n ∈ sel y` it is chosen inside
`[cellLo (y n), cellHi (y n)]` by `Work.EKLC6Core.shell_radius_nullfrontier`; otherwise a
dummy. -/
def cellRad (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (n : ℕ) : ℝ :=
  if n ∈ sel y then Classical.choose (exists_cellRad μ y n) else cellLo (y n)

theorem cellRad_spec {μ : MeasureTheory.Measure X3} [MeasureTheory.IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} (hn : n ∈ sel y) :
    cellLo (y n) ≤ cellRad μ y n ∧ cellRad μ y n ≤ cellHi (y n) ∧
      μ (frontier (Work.EKLComp.Vball (cellRad μ y n) (y n))) = 0 ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        (μ (Work.EKLComp.Vball (cellRad μ y n * (1 + δ)) (y n))).toReal -
          (μ (Work.EKLComp.Vball (cellRad μ y n * (1 - δ)) (y n))).toReal
        ≤ 32 * δ * (μ (Work.EKLComp.Vball (2 * cellHi (y n)) (y n))).toReal) := by
  rw [cellRad, if_pos hn]
  exact Classical.choose_spec (exists_cellRad μ y n)

theorem cellRad_pos {μ : MeasureTheory.Measure X3} [MeasureTheory.IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} (hn : n ∈ sel y) : 0 < cellRad μ y n :=
  lt_of_lt_of_le (cellLo_pos (y n)) (cellRad_spec hn).1

theorem cellRad_le_cellHi {μ : MeasureTheory.Measure X3} [MeasureTheory.IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} (hn : n ∈ sel y) : cellRad μ y n ≤ cellHi (y n) :=
  (cellRad_spec hn).2.1

/-! ## 4. The cells and the counting balls -/

/-- The ball of the `k`-th cell; `∅` for `k ∉ sel y`. -/
def cellBall (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (n : ℕ) : Set X3 :=
  if n ∈ sel y then Work.EKLComp.Vball (cellRad μ y n) (y n) else ∅

/-- The *counting* ball of the `k`-th cell; `∅` for `k ∉ sel y`. -/
def countBall (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (n : ℕ) : Set X3 :=
  if n ∈ sel y then Work.EKLComp.Vball (2 * cellHi (y n)) (y n) else ∅

theorem cellBall_eq {μ : MeasureTheory.Measure X3} [MeasureTheory.IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} (hn : n ∈ sel y) :
    cellBall μ y n = Work.EKLComp.Vball (cellRad μ y n) (y n) := by
  rw [cellBall, if_pos hn]

theorem cellBall_eq_empty {μ : MeasureTheory.Measure X3} [MeasureTheory.IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} (hn : n ∉ sel y) : cellBall μ y n = ∅ := by
  rw [cellBall, if_neg hn]

theorem countBall_eq {μ : MeasureTheory.Measure X3} [MeasureTheory.IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} (hn : n ∈ sel y) :
    countBall μ y n = Work.EKLComp.Vball (2 * cellHi (y n)) (y n) := by
  rw [countBall, if_pos hn]

theorem countBall_eq_empty {μ : MeasureTheory.Measure X3} [MeasureTheory.IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} (hn : n ∉ sel y) : countBall μ y n = ∅ := by
  rw [countBall, if_neg hn]

theorem cellBall_open (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (n : ℕ) : IsOpen (cellBall μ y n) := by
  rw [cellBall]
  split_ifs with hn
  · exact Work.Misiurewicz.isOpen_Vball (y n) (cellRad_pos hn)
  · exact isOpen_empty

theorem countBall_open (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (n : ℕ) : IsOpen (countBall μ y n) := by
  rw [countBall]
  split_ifs with hn
  · exact Work.Misiurewicz.isOpen_Vball (y n) (by have := cellHi_pos (y n); linarith)
  · exact isOpen_empty

theorem cellBall_measurable (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (n : ℕ) : MeasurableSet (cellBall μ y n) :=
  (cellBall_open μ y n).measurableSet

theorem countBall_measurable (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (n : ℕ) : MeasurableSet (countBall μ y n) :=
  (countBall_open μ y n).measurableSet

theorem cellBall_frontier_null (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (n : ℕ) : μ (frontier (cellBall μ y n)) = 0 := by
  rw [cellBall]
  split_ifs with hn
  · exact (cellRad_spec hn).2.2.1
  · rw [frontier_empty, measure_empty]

/-- The cell ball is contained in the counting ball. -/
theorem cellBall_subset_countBall (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (n : ℕ) : cellBall μ y n ⊆ countBall μ y n := by
  rw [cellBall, countBall]
  split_ifs with hn
  · exact Work.Misiurewicz.Vball_mono (y n) (by
      have := cellRad_le_cellHi (μ := μ) hn
      have := cellHi_pos (y n)
      linarith)
  · exact subset_rfl

/-! ## 5. The disjointified cells -/

/-- The disjointification of the cell balls: `cellBall k` minus the closures of the earlier
cell balls. -/
def Qcell (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (k : ℕ) : Set X3 :=
  cellBall μ y k ∩ ⋂ l ∈ Set.Iio k, (closure (cellBall μ y l))ᶜ

theorem Qcell_subset (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (k : ℕ) : Qcell μ y k ⊆ cellBall μ y k := Set.inter_subset_left

theorem Qcell_subset_countBall (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (k : ℕ) : Qcell μ y k ⊆ countBall μ y k :=
  (Qcell_subset μ y k).trans (cellBall_subset_countBall μ y k)

theorem Qcell_open (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (k : ℕ) : IsOpen (Qcell μ y k) := by
  refine (cellBall_open μ y k).inter ?_
  refine Set.Finite.isOpen_biInter (Set.finite_Iio k) (fun l _ => ?_)
  exact isClosed_closure.isOpen_compl

theorem Qcell_disjoint (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) : ∀ k l, k ≠ l → Disjoint (Qcell μ y k) (Qcell μ y l) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro x hkx hlx
  rcases lt_or_gt_of_ne hkl with hlt | hlt
  · have hxk : x ∈ cellBall μ y k := hkx.1
    have h2 : x ∉ closure (cellBall μ y k) := by
      have hh : x ∈ ⋂ l' ∈ Set.Iio l, (closure (cellBall μ y l'))ᶜ := hlx.2
      simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_compl_iff] at hh
      exact hh k hlt
    exact h2 (subset_closure hxk)
  · have hxl : x ∈ cellBall μ y l := hlx.1
    have h2 : x ∉ closure (cellBall μ y l) := by
      have hh : x ∈ ⋂ l' ∈ Set.Iio k, (closure (cellBall μ y l'))ᶜ := hkx.2
      simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_compl_iff] at hh
      exact hh l hlt
    exact h2 (subset_closure hxl)

private theorem notMem_closure_of_notMem_frontier_of_isOpen {B : Set X3} (hB : IsOpen B)
    {x : X3} (hxB : x ∉ B) (hf : x ∉ frontier B) : x ∉ closure B := by
  intro hxc
  exact hf (by rw [frontier]; exact ⟨hxc, by rwa [hB.interior_eq]⟩)

/-- The disjointified cells cover a conull set, provided the cell balls cover everything. -/
theorem Qcell_conull (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (hcover : (⋃ n, cellBall μ y n) = Set.univ) :
    μ ((⋃ k, Qcell μ y k))ᶜ = 0 := by
  have hsub : (⋃ k, Qcell μ y k)ᶜ ⊆ (⋃ k, frontier (cellBall μ y k)) := by
    intro x hx
    by_contra hxN
    have hxN' : ∀ k, x ∉ frontier (cellBall μ y k) := fun k hk =>
      hxN (Set.mem_iUnion.mpr ⟨k, hk⟩)
    have hxU : x ∈ ⋃ k, cellBall μ y k := by rw [hcover]; exact Set.mem_univ x
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxU
    have hex : ∃ k, x ∈ cellBall μ y k := ⟨k, hk⟩
    have hmin : ∀ l, l < Nat.find hex → x ∉ cellBall μ y l := by
      intro l hl hxl
      have hle : Nat.find hex ≤ l := Nat.find_min' hex hxl
      omega
    have hmem : x ∈ Qcell μ y (Nat.find hex) := by
      refine ⟨Nat.find_spec hex, ?_⟩
      simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_compl_iff]
      intro l hl
      exact notMem_closure_of_notMem_frontier_of_isOpen (cellBall_open μ y l) (hmin l hl)
        (hxN' l)
    exact hx (Set.mem_iUnion.mpr ⟨Nat.find hex, hmem⟩)
  exact MeasureTheory.measure_mono_null hsub
    (MeasureTheory.measure_iUnion_null fun k => cellBall_frontier_null μ y k)

/-! ## 6. The shell bound -/

/-- Every `V`-ball is measurable (it is open, or empty when the radius is nonpositive). -/
theorem measurableSet_Vball_cr2 (r : ℝ) (x : X3) : MeasurableSet (Work.EKLComp.Vball r x) := by
  by_cases h : r ≤ 0
  · have hzero : Work.EKLComp.Vball r x = ∅ := by
      ext z
      constructor
      · rintro ⟨u, hu, -⟩
        have h1 := hu 0 0
        have h2 : 0 ≤ |(u : Matrix (Fin 3) (Fin 3) ℝ) 0 0
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0| := abs_nonneg _
        exact absurd h1 (by linarith)
      · intro hz
        exact absurd hz (by simp)
    rw [hzero]
    exact MeasurableSet.empty
  · exact (Work.Misiurewicz.isOpen_Vball x (lt_of_not_ge h)).measurableSet

/-- The relative width constant of the collar estimate: `deltac` is chosen large enough that
the collar of any cell is contained in the shell of relative width `deltac * ε`. -/
def deltac : ℝ := 2 ^ 60

/-- The threshold below which the collar estimate is applied. -/
def epsZero : ℝ := 1 / deltac

theorem deltac_pos : 0 < deltac := by norm_num [deltac]
theorem epsZero_pos : 0 < epsZero := by rw [epsZero]; exact div_pos one_pos deltac_pos
theorem deltac_mul_epsZero : deltac * epsZero = 1 := by
  rw [epsZero, mul_one_div, div_self (ne_of_gt deltac_pos)]
theorem deltac_eps_le_one {ε : ℝ} (hε : ε ≤ epsZero) : deltac * ε ≤ 1 := by
  have := mul_le_mul_of_nonneg_left hε (le_of_lt deltac_pos)
  rwa [deltac_mul_epsZero] at this

/-- The two-sided shell of the `j`-th cell ball at relative width `ρ`. -/
def shell (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (ρ : ℝ) (j : ℕ) : Set X3 :=
  Work.EKLComp.Vball (cellRad μ y j * (1 + ρ)) (y j) \
    Work.EKLComp.Vball (cellRad μ y j * (1 - ρ)) (y j)

theorem shell_measure_le (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) {j : ℕ} (hj : j ∈ sel y) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    μ (shell μ y ρ j) ≤ ENNReal.ofReal (32 * ρ) * μ (countBall μ y j) := by
  show μ (Work.EKLComp.Vball (cellRad μ y j * (1 + ρ)) (y j) \
      Work.EKLComp.Vball (cellRad μ y j * (1 - ρ)) (y j)) ≤
    ENNReal.ofReal (32 * ρ) * μ (countBall μ y j)
  have hcr : 0 < cellRad μ y j := cellRad_pos hj
  have hsub : Work.EKLComp.Vball (cellRad μ y j * (1 - ρ)) (y j) ⊆
      Work.EKLComp.Vball (cellRad μ y j * (1 + ρ)) (y j) :=
    Work.Misiurewicz.Vball_mono (y j) (by nlinarith)
  have hBmeas : MeasurableSet (Work.EKLComp.Vball (cellRad μ y j * (1 - ρ)) (y j)) :=
    measurableSet_Vball_cr2 _ _
  have hfin : μ (Work.EKLComp.Vball (cellRad μ y j * (1 - ρ)) (y j)) ≠ ⊤ :=
    measure_ne_top μ _
  have hdiff : μ (Work.EKLComp.Vball (cellRad μ y j * (1 + ρ)) (y j) \
        Work.EKLComp.Vball (cellRad μ y j * (1 - ρ)) (y j))
      = μ (Work.EKLComp.Vball (cellRad μ y j * (1 + ρ)) (y j))
        - μ (Work.EKLComp.Vball (cellRad μ y j * (1 - ρ)) (y j)) :=
    MeasureTheory.measure_diff hsub hBmeas.nullMeasurableSet hfin
  have hspec := (cellRad_spec (μ := μ) hj).2.2.2 ρ hρ0 hρ1
  have htoReal : (μ (Work.EKLComp.Vball (cellRad μ y j * (1 + ρ)) (y j))
        - μ (Work.EKLComp.Vball (cellRad μ y j * (1 - ρ)) (y j))).toReal
      ≤ 32 * ρ * (μ (countBall μ y j)).toReal := by
    rw [ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top μ _)]
    rw [countBall_eq hj]
    exact hspec
  have hfinAB : μ (Work.EKLComp.Vball (cellRad μ y j * (1 + ρ)) (y j) \
      Work.EKLComp.Vball (cellRad μ y j * (1 - ρ)) (y j)) ≠ ⊤ := measure_ne_top μ _
  calc μ (Work.EKLComp.Vball (cellRad μ y j * (1 + ρ)) (y j) \
        Work.EKLComp.Vball (cellRad μ y j * (1 - ρ)) (y j))
      = ENNReal.ofReal ((μ (Work.EKLComp.Vball (cellRad μ y j * (1 + ρ)) (y j) \
          Work.EKLComp.Vball (cellRad μ y j * (1 - ρ)) (y j))).toReal) :=
        (ENNReal.ofReal_toReal hfinAB).symm
    _ ≤ ENNReal.ofReal (32 * ρ * (μ (countBall μ y j)).toReal) :=
        ENNReal.ofReal_le_ofReal (by rw [hdiff]; exact htoReal)
    _ = ENNReal.ofReal (32 * ρ) * ENNReal.ofReal ((μ (countBall μ y j)).toReal) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (32 * ρ) * μ (countBall μ y j) :=
        mul_le_mul' le_rfl ENNReal.ofReal_toReal_le

/-! ## 7. Remaining pieces (delegated) — the exact plans

### 7a. The cover: `exists_mem_cellBall`

Goal: `∃ n, n ∈ sel y ∧ z ∈ cellBall μ y n` for every `z`.

Take `a := injCap z / 2^30`.  `Vball a z` is a nonempty open set, so by density there are `n` and
`u ∈ V a` with `u • z = y n`; then `z = u⁻¹ • y n`.  From `injCap_mem_V_le` (`a ≤ injCap z / 8`)
we get `injCap z / 16 ≤ injCap (y n)`.

* If `n ∈ sel y`: `u⁻¹ ∈ V (10a)` (`Work.EKLComp.inv_mem_V`), and
  `10 a ≤ injCap z / 2^26 ≤ cellLo (y n) = injCap (y n) / 4096 ≤ cellRad μ y n`.
* If `n ∉ sel y`: let `j < n` be the witness of `exists_sel_witness`.
  - If `y n = w • y j`, `w ∈ V (sepRad (y j))`: `z = (u⁻¹ w) • y j` with
    `u⁻¹ w ∈ V (10a + sepRad (y j) + …) ⊆ V (2 sepRad (y j)) ⊆ V (cellLo (y j))`.
  - If `y j = w • y n`, `w ∈ V (sepRad (y n))`: `injCap_mem_V_le` at `x = y n` with
    `a' = 10 * sepRad (y n)` (legal since `10 / 2^20 ≤ 1/8`) gives
    `injCap (y n) / 16 ≤ injCap (y j)`, i.e. `sepRad (y n) ≤ 16 * sepRad (y j)`; hence
    `z = (u⁻¹ w⁻¹) • y j` with `u⁻¹ w⁻¹ ∈ V (10a + 10 sepRad (y n) + …) ⊆ V (163 sepRad (y j))
    ⊆ V (256 sepRad (y j)) = V (cellLo (y j))`.
  In both cases `z ∈ Vball (cellLo (y j)) (y j) ⊆ cellBall μ y j` and `j ∈ sel y`.

### 7b. The counting: `sel_counting_sum`

Goal: `∃ M > 0, ∑' n, μ (countBall μ y n) ≤ ofReal M`.

Fix `x : X₃`.  For `n` with `x ∈ countBall μ y n` one has `n ∈ sel y` and `x = u • y n` with
`u ∈ V (2 * cellHi (y n)) = V (injCap (y n) / 1024)`; hence
* `injCap (y n) / 16 ≤ injCap x`   (`injCap_mem_V_le` at `x = y n`, `a = injCap (y n) / 1024`),
* `y n = u⁻¹ • x` with `u⁻¹ ∈ V (10 * injCap (y n) / 1024) ⊆ V (injCap x / 6.4)` (using the first
  point and `injCap (y n) ≤ 16 injCap x`, which follows from the same lemma applied at `x` after
  the case distinction `injCap (y n) ≤ injCap x`).

So `A_x := {n : x ∈ countBall μ y n}` satisfies `sepRad (y n) ≥ injCap x / 2^24 =: sep` and
`y n ∈ Vball (injCap x / 6.4) x`.  The family `{y n : n ∈ A_x ∩ F}` is `sep`-separated because
`sel_sep` gives separation at `max (sepRad (y n)) (sepRad (y m)) ≥ sep`; together with
`Work.EKLC6Core.vball_packing_uniform` at the constant `c = 2621440` (so that
`c * sep = injCap x / 6.4`, and `c * sep ≤ injCap x / 2` is satisfied) and `sel_inj` (so that
`n ↦ y n` is injective on `sel y`) this bounds
`#(F.filter (fun n => x ∈ countBall μ y n))` by the corresponding `M(c)`, uniformly in `x`.
Then `Work.EKLC6Core.tsum_measure_le_of_card_bound` (with `μ univ = 1`) finishes.

### 7c. The collar: `bad_subset_shells`

The statement is
```
theorem bad_subset_shells (μ : Measure X3) [IsFiniteMeasure μ] (y : ℕ → X3)
    (hcover : ∀ z : X3, ∃ n, n ∈ sel y ∧ z ∈ cellBall μ y n)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ epsZero) {z : X3} {k : ℕ}
    (hz : z ∈ Qcell μ y k) (hm : cellMargin (Qcell μ y) k z < ε * injCap z) :
    ∃ j : ℕ, j ∈ sel y ∧ z ∈ shell μ y (deltac * ε) j
```
with `deltac = 2^60` and `epsZero = 1/deltac` (so `deltac * ε ≤ 1`).  A *proved* model of the
argument — with different scales, but the same structure and the same case analysis — is
`Work.EKLC6Core.outCol_subset` and `Work.EKLC6Core.inCol_subset` in
`Submission/Work/EKLC6Core/relthin_cover_exists.lean`; it is worth reading and adapting.

Write `m := cellMargin (Qcell μ y) k z` and pick `r` with `m < r < ε * injCap z` (then `0 < r`,
`r ≤ 2`).  There is `v ∈ V r` with `v • z ∉ Qcell μ y k` (contrapositive of the defining property
of `cellMargin`).  By `hcover`, `v • z ∈ cellBall μ y n` for some `n ∈ sel y`.  Two cases:

* `n < k`: then `z ∉ closure (cellBall μ y n)` (the `⋂` part of `Qcell μ y k`), so
  `z ∉ cellBall μ y n`.  Write `v • z = b • y n` with `b ∈ V (cellRad μ y n)`; then
  `z = (v⁻¹ b) • y n` with `v⁻¹ ∈ V (10 r)` (`Work.EKLComp.inv_mem_V`), i.e. `z ∈ V R • y n` for
  `R := 10*r + cellRad μ y n + 30*r*cellRad μ y n`.  Show `R ≤ cellRad μ y n * (1 + deltac * ε)`:
  case on `R ≤ injCap (y n)/8`.
  - If yes: `Work.EKLC6Core.injCap_le_mul_of_mem_Vball` gives `injCap z ≤ 2^19 * injCap (y n)`,
    and `injCap (y n) ≤ 2048 * cellRad μ y n`, so `r < ε * injCap z` gives the claim once
    `deltac ≥ 2^19 * 2048 * 11`.
  - If no: `r` (hence `ε * injCap z`) is not small compared with `injCap (y n)`.  Use `hcover` at
    `z` to get `z ∈ cellBall μ y m'`.  Copying the second half of the proof of `outCol_subset`
    gives first `injCap (y n) ≤ 1200 * ε * 2^19 * injCap (y m')`, then (via a second application
    of `injCap_mem_V_le`, whose legality uses `ε ≤ epsZero` and `epsZero ≤ 1/(68736 * 2^19)`)
    `injCap (y m')/16 ≤ injCap (y n)`, hence `injCap z ≤ 16 * 2^19 * injCap (y n)` and again the
    claim (`deltac ≥ 16 * 2^19 * 2048 * 3`).
  Using `z ∉ Vball (cellRad μ y n * (1 - deltac*ε)) (y n)`, which follows from `z ∉ cellBall μ y n`
  and `Vball (cellRad*(1-ρ)) ⊆ Vball (cellRad)`, gives `z ∈ shell μ y (deltac*ε) n` with
  `n ∈ sel y`.
* `n = k`: then `v • z ∈ cellBall μ y k` and `v • z ∉ Qcell μ y k`, so `v • z ∈ closure (cellBall μ
  y l)` for some `l < k`.  Take `l` and `δ > 0` small with `closure (cellBall μ y l) ⊆
  Vball (cellRad μ y l * (1 + δ)) (y l)` (`Work.Misiurewicz.closure_Vball_subset_Vball_of_lt`),
  and repeat the outside analysis with `cellRad μ y l * (1+δ)` in place of `cellRad μ y l` (the
  constant `deltac` absorbs the extra factor `1 + δ`).  Note `z ∉ closure (cellBall μ y l)`, so
  `z ∉ Vball (cellRad μ y l * (1 - deltac*ε)) (y l)`.
* `n > k`: `z ∈ cellBall μ y k` and `v • z ∈ cellBall μ y n` — this cannot happen for the *same*
  `r`: … (in fact, for `n > k` one uses the *cover* of `z` again; see `outCol_subset`'s treatment,
  which handles an arbitrary pair of balls and only needs `z ∈ outCol` of the ball `n` and
  `z ∈` *some* ball `m`).
-/

/-! ## 8. Helpers for the final assembly -/

theorem cellRad_pos_all (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (n : ℕ) : 0 < cellRad μ y n := by
  by_cases h : n ∈ sel y
  · exact cellRad_pos h
  · rw [cellRad, if_neg h]; exact cellLo_pos (y n)

theorem cellRad_le_cellHi_all (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (n : ℕ) : cellRad μ y n ≤ cellHi (y n) := by
  by_cases h : n ∈ sel y
  · exact cellRad_le_cellHi h
  · rw [cellRad, if_neg h]; exact le_of_lt (cellLo_lt_cellHi (y n))

/-- The shell of the `n`-th cell, emptied at the indices that are not selected. -/
def selShell (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (ρ : ℝ) (j : ℕ) : Set X3 :=
  if j ∈ sel y then shell μ y ρ j else ∅

theorem selShell_measurable (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) (ρ : ℝ) (j : ℕ) : MeasurableSet (selShell μ y ρ j) := by
  rw [selShell]
  split_ifs with hj
  · show MeasurableSet (Work.EKLComp.Vball (cellRad μ y j * (1 + ρ)) (y j) \
      Work.EKLComp.Vball (cellRad μ y j * (1 - ρ)) (y j))
    exact (measurableSet_Vball_cr2 _ _).diff (measurableSet_Vball_cr2 _ _)
  · exact MeasurableSet.empty

theorem selShell_measure_le (μ : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure μ]
    (y : ℕ → X3) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ) :
    μ (selShell μ y ρ j) ≤ ENNReal.ofReal (32 * ρ) * μ (countBall μ y j) := by
  rw [selShell]
  split_ifs with hj
  · exact shell_measure_le μ y hj hρ0 hρ1
  · rw [measure_empty]; exact bot_le


-- TEMPORARY STUBS (to be replaced by the imported child lemmas)
/-! ## 9. The total mass of the counting balls

(Inlined from the module `Submission.Work.EKLC6Core.sel_counting_sum`, which cannot be imported
here because it imports this module.) -/

/-- The counting ball of a selected index, written at the level of the injectivity radius. -/
theorem cnt_countBall_eq_vball_injCap {μ : Measure X3} [IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} (hn : n ∈ sel y) :
    countBall μ y n = Work.EKLComp.Vball (injCap (y n) / 1024) (y n) := by
  rw [countBall_eq hn]
  congr 1
  rw [cellHi]
  ring

/-- A non-trivial counting ball forces its index to be selected. -/
theorem cnt_mem_sel_of_mem_countBall {μ : Measure X3} [IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} {x : X3} (hx : x ∈ countBall μ y n) : n ∈ sel y := by
  by_contra hn
  rw [countBall_eq_empty hn] at hx
  exact Set.notMem_empty x hx

/-- **The two-sided scale of a counting ball.** -/
theorem cnt_injCap_bounds_of_mem_countBall {μ : Measure X3} [IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} {x : X3} (hx : x ∈ countBall μ y n) :
    injCap (y n) / 16 ≤ injCap x ∧ injCap x ≤ 4 * injCap (y n) := by
  have hn := cnt_mem_sel_of_mem_countBall hx
  rw [cnt_countBall_eq_vball_injCap hn] at hx
  obtain ⟨u, hu, hueq⟩ := Work.EKLComp.mem_Vball.mp hx
  set a : ℝ := injCap (y n) / 1024 with ha
  have hapos : 0 < a := by rw [ha]; exact div_pos (injCap_pos _) (by norm_num)
  have hahalf : a ≤ 1 / 2 := by
    rw [ha]
    have := injCap_le_half (y n)
    linarith
  have ha8 : a ≤ injCap (y n) / 8 := by rw [ha]; linarith
  refine ⟨?_, ?_⟩
  · have h := injCap_mem_V_le (x := y n) (a := a) hapos hahalf ha8 hu
    rwa [hueq] at h
  · have h := injCap_smul_le (x := y n) (a := a) hapos hahalf ha8 hu
    rwa [hueq] at h

/-- The centre of a counting ball containing `x` lies in the fat ball of `x` at the uniform
scale `5 * 2^19 * (injCap x / 2^24)`. -/
theorem cnt_mem_fatVball_of_mem_countBall {μ : Measure X3} [IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} {x : X3} (hx : x ∈ countBall μ y n) :
    y n ∈ Work.EKLComp.Vball (5 * 2 ^ 19 * (injCap x / 2 ^ 24)) x := by
  have hb := cnt_injCap_bounds_of_mem_countBall hx
  have hle16 : injCap (y n) ≤ 16 * injCap x := by linarith [hb.1]
  have hn := cnt_mem_sel_of_mem_countBall hx
  rw [cnt_countBall_eq_vball_injCap hn] at hx
  obtain ⟨u, hu, hueq⟩ := Work.EKLComp.mem_Vball.mp hx
  have ha1 : injCap (y n) / 1024 ≤ 1 := by
    have := injCap_le_half (y n)
    linarith
  have hinv : u⁻¹ ∈ V (10 * (injCap (y n) / 1024)) :=
    Work.EKLComp.inv_mem_V (div_pos (injCap_pos _) (by norm_num)) ha1 hu
  refine Work.EKLComp.mem_Vball.mpr ⟨u⁻¹, Work.Misiurewicz.V_mono ?_ hinv, ?_⟩
  · rw [show 5 * 2 ^ 19 * (injCap x / 2 ^ 24) = 5 / 32 * injCap x by ring]
    rw [show 10 * (injCap (y n) / 1024) = 5 / 512 * injCap (y n) by ring]
    linarith
  · show u⁻¹ • x = y n
    rw [← hueq, ← mul_smul, inv_mul_cancel, one_smul]

/-- **Separation of the centres of two counting balls through `x`.** -/
theorem cnt_countBall_sep {μ : Measure X3} [IsFiniteMeasure μ]
    {y : ℕ → X3} {x : X3} {n m : ℕ}
    (hn : x ∈ countBall μ y n) (hm : x ∈ countBall μ y m) (hne : n ≠ m) {w : SL3}
    (hw : w ∈ V (injCap x / 2 ^ 24)) : w • y n ≠ y m := by
  have hns := cnt_mem_sel_of_mem_countBall hn
  have hms := cnt_mem_sel_of_mem_countBall hm
  have hb := cnt_injCap_bounds_of_mem_countBall hn
  have hsep : injCap x / 2 ^ 24 ≤ sepRad (y n) := by
    rw [sepRad]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2 ^ 24)]
    nlinarith [hb.2, injCap_pos (y n)]
  intro heq
  exact (sel_sep y hns hms hne).1
    (Work.EKLComp.mem_Vball.mpr ⟨w, Work.Misiurewicz.V_mono hsep hw, heq⟩)

/-- **The counting balls of the greedy family have finite total mass.**  For a probability measure
`μ` on `X₃` and a dense sequence `y`, there is `M > 0` with
`∑' n, μ (countBall μ y n) ≤ ofReal M`: the multiplicities of the counting balls are bounded
uniformly in the point, by the packing bound of `Work.EKLC6Core.vball_packing_uniform` and the
separation of the selected centres. -/
theorem sel_count_sum (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ] (y : ℕ → Work.EKLContract.X3)
    (hy : Dense (Set.range y)) :
    ∃ M : ℝ, 0 < M ∧ ∑' n : ℕ, μ (Work.EKLC6Core.countBall μ y n) ≤ ENNReal.ofReal M := by
  classical
  obtain ⟨M, hMpos, hM⟩ := vball_packing_uniform (c := 5 * 2 ^ 19) (by norm_num)
  refine ⟨M, hMpos, ?_⟩
  have hcard : ∀ (F : Finset ℕ) (x : X3),
      ((F.filter (fun n => x ∈ countBall μ y n)).card : ℝ) ≤ M := by
    intro F x
    have hSel : ∀ n ∈ F.filter (fun n => x ∈ countBall μ y n), n ∈ sel y :=
      fun n hn => cnt_mem_sel_of_mem_countBall (Finset.mem_filter.mp hn).2
    have hcard_eq : ((F.filter (fun n => x ∈ countBall μ y n)).image y).card
        = (F.filter (fun n => x ∈ countBall μ y n)).card :=
      Finset.card_image_of_injOn fun a ha b hb h => sel_inj y (hSel a ha) (hSel b hb) h
    rw [← hcard_eq]
    refine hM (injCap x / 2 ^ 24) (div_pos (injCap_pos x) (by norm_num)) x
      ((F.filter (fun n => x ∈ countBall μ y n)).image y) ?_ ?_ ?_
    · rw [show 5 * 2 ^ 19 * (injCap x / 2 ^ 24) = 5 / 32 * injCap x by ring]
      linarith [injCap_pos x]
    · intro s hs
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hs
      exact cnt_mem_fatVball_of_mem_countBall (Finset.mem_filter.mp hn).2
    · intro s hs s' hs' hne w hw
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨m, hm, hmeq⟩ := Finset.mem_image.mp hs'
      have hnm : n ≠ m := fun h => hne (by rw [h, hmeq])
      rw [← hmeq]
      exact cnt_countBall_sep (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2 hnm hw
  have hmain := tsum_measure_le_of_card_bound μ (fun n => countBall μ y n)
    (fun n => countBall_measurable μ y n) (le_of_lt hMpos) hcard
  rwa [measure_univ, mul_one] at hmain


/-! ## 10. The cover by the selected cell balls

(Inlined from `Submission.Work.EKLC6Core.exists_mem_cellBall` and its arithmetic helper modules,
which cannot be imported here because they import this module.) -/

/-- Arithmetic cover estimate `A`: with `p = P / 2^80`, `r = R / 2^20`, the sum
`10p + r + 3 (10p) r` is dominated by `R / 4096`, using `P ≤ 16 Q ≤ 2^19 · 16 R`. -/
theorem c2_cover_arith_outA {P Q R : ℝ} (hPhalf : P ≤ 1 / 2) (hR0 : 0 ≤ R) (hRh : R ≤ 1 / 2)
    (hPQ : P ≤ 16 * Q) (hQR : Q ≤ 2 ^ 19 * R) :
    10 * (P / 2 ^ 80) + R / 2 ^ 20 + 3 * (10 * (P / 2 ^ 80)) * (R / 2 ^ 20) ≤ R / 4096 := by
  nlinarith [hPQ, hQR, hPhalf, hR0, hRh]

/-- Arithmetic cover estimate `B`: writing `p = P / 2^80`, `q = Q / 2^20`, the sum
`10p + 10q + 3·(10p)(10q)` is dominated by `R / 4096`, using only that `P ≤ 16Q`,
`Q ≤ 16R` and `P, Q ≤ 1/2`. -/
theorem c2_cover_arith_outB {P Q R : ℝ} (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) (hPhalf : P ≤ 1 / 2)
    (hQhalf : Q ≤ 1 / 2) (hR0 : 0 ≤ R) (hPQ : P ≤ 16 * Q) (hQR : Q ≤ 16 * R) :
    10 * (P / 2 ^ 80) + 10 * (Q / 2 ^ 20) + 3 * (10 * (P / 2 ^ 80)) * (10 * (Q / 2 ^ 20))
      ≤ R / 4096 := by
  have hA : 10 * (P / 2 ^ 80) ≤ (1 / 8) * (Q / 2 ^ 16) := by
    nlinarith [hPQ, hQ0]
  have hB : 10 * (Q / 2 ^ 20) = (5 / 8) * (Q / 2 ^ 16) := by ring
  have hC : 3 * (10 * (P / 2 ^ 80)) * (10 * (Q / 2 ^ 20)) ≤ (1 / 8) * (Q / 2 ^ 16) := by
    nlinarith [hPhalf, hQ0]
  have hR' : Q / 2 ^ 16 ≤ R / 4096 := by
    nlinarith [hQR]
  linarith [hA, hB, hC, hR']

/-- `10 * (P / 2^80) ≤ Q / 4096` when `P ≤ 16 Q` (and `Q ≥ 0`). -/
private theorem c2_cover_arith_sel_local {P Q : ℝ} (hQ : 0 ≤ Q) (hPQ : P ≤ 16 * Q) :
    10 * (P / 2 ^ 80) ≤ Q / 4096 := by
  have h1 : P / 2 ^ 80 ≤ 16 * Q / 2 ^ 80 :=
    div_le_div_of_nonneg_right hPQ (by positivity)
  have h4 : (10 : ℝ) * (16 * Q / 2 ^ 80) = 160 * Q / 2 ^ 80 := by ring
  have h2 : (160 : ℝ) * Q / 2 ^ 80 ≤ Q / 4096 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4096)]
    rw [div_mul_eq_mul_div]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 80)]
    nlinarith [hQ, (show ((160 : ℝ) * 4096) ≤ 2 ^ 80 by norm_num)]
  linarith [h1, h2, h4]

theorem sel_cover (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure μ] (y : ℕ → Work.EKLContract.X3)
    (hy : Dense (Set.range y)) (z : Work.EKLContract.X3) :
    ∃ n : ℕ, n ∈ Work.EKLC6Core.sel y ∧ z ∈ Work.EKLC6Core.cellBall μ y n := by
  classical
  set a : ℝ := injCap z / 2 ^ 80 with ha
  have hapos : 0 < a := by rw [ha]; exact div_pos (injCap_pos z) (by positivity)
  have hahalf : a ≤ 1 / 2 := by
    rw [ha]
    have h1 : injCap z / 2 ^ 80 ≤ (1 / 2) / 2 ^ 80 :=
      div_le_div_of_nonneg_right (injCap_le_half z) (by positivity)
    have h2 : ((1 : ℝ) / 2) / 2 ^ 80 ≤ 1 / 2 := by norm_num
    linarith
  have ha1 : a ≤ 1 := by linarith
  have ha8 : a ≤ injCap z / 8 := by
    rw [ha]
    exact div_le_div_of_nonneg_left (a := injCap z) (b := (2 : ℝ) ^ 80) (c := 8)
      (le_of_lt (injCap_pos z)) (by positivity) (show (8 : ℝ) ≤ 2 ^ 80 by norm_num)
  -- density gives a point of the dense sequence inside the tiny ball `Vball a z`
  have hUopen : IsOpen (Work.EKLComp.Vball a z) := Work.Misiurewicz.isOpen_Vball z hapos
  have hUne : (Work.EKLComp.Vball a z).Nonempty :=
    ⟨z, ⟨1, (Work.EKLContract.Lemmas.V_open_one a hapos).2, by simp⟩⟩
  obtain ⟨zz, hzz, hU⟩ := hy.exists_mem_open hUopen hUne
  obtain ⟨n, rfl⟩ := hzz
  obtain ⟨u, hu, huz⟩ := Work.EKLComp.mem_Vball.mp hU
  -- lower semicontinuity of the injectivity radius at `z`
  have hlsc : injCap z / 16 ≤ injCap (y n) := by
    have h := injCap_mem_V_le (x := z) hapos hahalf ha8 hu
    rwa [huz] at h
  have hP16 : injCap z ≤ 16 * injCap (y n) := by linarith
  have hu10 : u⁻¹ ∈ V (10 * a) := Work.EKLComp.inv_mem_V hapos ha1 hu
  by_cases hn : n ∈ sel y
  · -- the dense point is itself selected
    refine ⟨n, hn, ?_⟩
    rw [cellBall_eq hn]
    have h10a : (10 : ℝ) * a ≤ cellRad μ y n := by
      have hstep : (10 : ℝ) * a ≤ cellLo (y n) := by
        rw [ha, cellLo]
        exact c2_cover_arith_sel_local (le_of_lt (injCap_pos (y n))) hP16
      exact le_trans hstep (cellRad_spec hn).1
    refine ⟨u⁻¹, Work.Misiurewicz.V_mono h10a hu10, ?_⟩
    show u⁻¹ • y n = z
    rw [← huz, ← mul_smul, inv_mul_cancel, one_smul]
  · -- otherwise the greedy maximality provides an earlier selected witness
    obtain ⟨j, hjn, hjs, hcase⟩ := exists_sel_witness y hn
    refine ⟨j, hjs, ?_⟩
    rw [cellBall_eq hjs]
    rcases hcase with hA | hB
    · -- `y n` lies in the separation ball of `y j`
      obtain ⟨w, hw, hwy⟩ := Work.EKLComp.mem_Vball.mp hA
      have hmem : u⁻¹ * w ∈ V (10 * a + sepRad (y j) + 3 * (10 * a) * sepRad (y j)) :=
        V_mul_subset_V (by linarith [hapos]) (le_of_lt (sepRad_pos (y j))) hu10 hw
      have hbound : (10 : ℝ) * a + sepRad (y j) + 3 * (10 * a) * sepRad (y j)
          ≤ cellRad μ y j := by
        have hsr8 : sepRad (y j) ≤ injCap (y j) / 8 := by
          rw [sepRad]
          exact div_le_div_of_nonneg_left (a := injCap (y j)) (b := 1048576) (c := 8)
            (le_of_lt (injCap_pos (y j))) (by norm_num) (by norm_num : (8 : ℝ) ≤ 1048576)
        have hQR : injCap (y n) ≤ 2 ^ 19 * injCap (y j) :=
          injCap_le_mul_of_mem_Vball (le_of_lt (sepRad_pos (y j))) hsr8 hA
        have harith := c2_cover_arith_outA (P := injCap z) (Q := injCap (y n))
          (R := injCap (y j)) (injCap_le_half z) (le_of_lt (injCap_pos (y j)))
          (injCap_le_half (y j)) hP16 hQR
        have hsep : sepRad (y j) = injCap (y j) / 2 ^ 20 := by rw [sepRad]; norm_num
        have hgoal : (10 : ℝ) * a + sepRad (y j) + 3 * (10 * a) * sepRad (y j)
            ≤ cellLo (y j) := by
          rw [ha, hsep, cellLo]
          exact harith
        exact le_trans hgoal (cellRad_spec hjs).1
      refine ⟨u⁻¹ * w, Work.Misiurewicz.V_mono hbound hmem, ?_⟩
      show (u⁻¹ * w) • y j = z
      rw [mul_smul, hwy, ← huz, ← mul_smul, inv_mul_cancel, one_smul]
    · -- `y j` lies in the separation ball of `y n`
      obtain ⟨w, hw, hwy⟩ := Work.EKLComp.mem_Vball.mp hB
      have hwinv : w⁻¹ ∈ V (10 * sepRad (y n)) :=
        Work.EKLComp.inv_mem_V (sepRad_pos (y n)) (sepRad_le_one (y n)) hw
      have hmem : u⁻¹ * w⁻¹ ∈
          V (10 * a + 10 * sepRad (y n) + 3 * (10 * a) * (10 * sepRad (y n))) :=
        V_mul_subset_V (by linarith [hapos]) (by linarith [sepRad_pos (y n)]) hu10 hwinv
      have hbound : (10 : ℝ) * a + 10 * sepRad (y n) + 3 * (10 * a) * (10 * sepRad (y n))
          ≤ cellRad μ y j := by
        have hsr_half_n : sepRad (y n) ≤ 1 / 2 := by
          rw [sepRad]
          have h1 : injCap (y n) / 1048576 ≤ (1 / 2) / 1048576 :=
            div_le_div_of_nonneg_right (injCap_le_half (y n)) (by norm_num)
          have h2 : ((1 : ℝ) / 2) / 1048576 ≤ 1 / 2 := by norm_num
          linarith
        have hsr8_n : sepRad (y n) ≤ injCap (y n) / 8 := by
          rw [sepRad]
          exact div_le_div_of_nonneg_left (a := injCap (y n)) (b := 1048576) (c := 8)
            (le_of_lt (injCap_pos (y n))) (by norm_num) (by norm_num : (8 : ℝ) ≤ 1048576)
        have hQR : injCap (y n) ≤ 16 * injCap (y j) := by
          have h := injCap_mem_V_le (x := y n) (a := sepRad (y n)) (sepRad_pos (y n))
            hsr_half_n hsr8_n hw
          rw [hwy] at h
          linarith
        have harith := c2_cover_arith_outB (P := injCap z) (Q := injCap (y n))
          (R := injCap (y j)) (le_of_lt (injCap_pos z)) (le_of_lt (injCap_pos (y n)))
          (injCap_le_half z) (injCap_le_half (y n)) (le_of_lt (injCap_pos (y j))) hP16 hQR
        have hsep : sepRad (y n) = injCap (y n) / 2 ^ 20 := by rw [sepRad]; norm_num
        have hgoal : (10 : ℝ) * a + 10 * sepRad (y n) + 3 * (10 * a) * (10 * sepRad (y n))
            ≤ cellLo (y j) := by
          rw [ha, hsep, cellLo]
          exact harith
        exact le_trans hgoal (cellRad_spec hjs).1
      refine ⟨u⁻¹ * w⁻¹, Work.Misiurewicz.V_mono hbound hmem, ?_⟩
      show (u⁻¹ * w⁻¹) • y j = z
      have hw1 : w⁻¹ • y j = y n := by rw [← hwy, ← mul_smul, inv_mul_cancel, one_smul]
      rw [mul_smul, hw1, ← huz, ← mul_smul, inv_mul_cancel, one_smul]



/-! ## 11. The collar estimate

(Inlined from the modules `Submission.Work.EKLC6Core.{bad_subset_shells,bad_inCol_shell,
bad_outCol_upper,boc_arith_*}`, which cannot be imported here because they import this module.) -/


-- inlined from `boc_arith_case_small`

theorem c2_boc_arith_case_small {ε J Ij Rj ρ R : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ Work.EKLC6Core.epsZero)
    (hJ0 : 0 < J) (hJh : J ≤ 1 / 2) (hIj0 : 0 < Ij) (hRj0 : 0 ≤ Rj)
    (hcase : Ij / 8 < R) (hR : R = 30 * (ε * J) + ρ + 3 * (30 * (ε * J)) * ρ)
    (hRj : Rj ≤ Ij / 2048)
    (hρ : ρ ≤ Rj * (1 + Work.EKLC6Core.deltac * ε / 2)) (hde1 : Work.EKLC6Core.deltac * ε ≤ 1) :
    Ij < 1440 * (ε * J) := by
  -- Unfold the constants: `epsZero = 1/2^60`.
  have heps : ε ≤ 1 / (2:ℝ)^60 := by
    have h := hε1
    rw [Work.EKLC6Core.epsZero, Work.EKLC6Core.deltac] at h
    exact h
  have hEJ0 : (0:ℝ) ≤ ε * J := le_of_lt (mul_pos hε0 hJ0)
  -- `ε * J ≤ 2⁻⁶¹`.
  have hEJ : ε * J ≤ 1 / (2:ℝ)^61 := by
    have h : ε * J ≤ (1/(2:ℝ)^60) * (1/2) :=
      mul_le_mul heps hJh (le_of_lt hJ0) (by norm_num)
    have h2 : (1/(2:ℝ)^60) * (1/2) = 1/(2:ℝ)^61 := by norm_num
    linarith
  -- `1 + deltac * ε / 2 ≤ 3/2`.
  have hA_le : 1 + Work.EKLC6Core.deltac * ε / 2 ≤ 3/2 := by
    rw [Work.EKLC6Core.deltac]
    linarith
  -- `1 + 90 * (ε * J) ≤ 2`, and it is nonnegative.
  have hB_le : 1 + 90 * (ε * J) ≤ 2 := by
    have h90 : 90 * (ε * J) ≤ 1 := by nlinarith [hEJ]
    linarith
  have hB_nn : (0:ℝ) ≤ 1 + 90 * (ε * J) := by linarith
  have h3 : Rj * (1 + Work.EKLC6Core.deltac * ε / 2) ≤ Rj * (3/2) :=
    mul_le_mul_of_nonneg_left hA_le hRj0
  -- The key bound on the `ρ`-term.
  have hkey : ρ * (1 + 90 * (ε * J)) ≤ 3 * Rj :=
    calc ρ * (1 + 90 * (ε * J))
        ≤ Rj * (1 + Work.EKLC6Core.deltac * ε / 2) * (1 + 90 * (ε * J)) :=
          mul_le_mul_of_nonneg_right hρ hB_nn
      _ ≤ Rj * (3/2) * (1 + 90 * (ε * J)) := mul_le_mul_of_nonneg_right h3 hB_nn
      _ ≤ Rj * (3/2) * 2 := mul_le_mul_of_nonneg_left hB_le (by linarith)
      _ = 3 * Rj := by ring
  have hR' : R = 30 * (ε * J) + ρ * (1 + 90 * (ε * J)) := by
    rw [hR]; ring
  rw [hR'] at hcase
  have hkey2 : ρ * (1 + 90 * (ε * J)) ≤ 3 * (Ij / 2048) := by linarith
  have hstep : Ij * (253/2048) < 30 * (ε * J) := by linarith
  have hstep2 : Ij < 30 * (ε * J) * (2048/253) := by linarith
  have hbound : 30 * (ε * J) * (2048/253) ≤ 1440 * (ε * J) := by linarith
  linarith



-- inlined from `boc_arith_R_small`

theorem c2_boc_arith_R_small {ε J Im Ij Rj ρ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ Work.EKLC6Core.epsZero) (hJ0 : 0 < J) (hJh : J ≤ 1 / 2)
    (hIm0 : 0 < Im) (hImh : Im ≤ 1 / 2) (hRj0 : 0 ≤ Rj)
    (hIj : Ij < 1440 * (ε * J)) (hJIm : J ≤ 2 ^ 19 * Im)
    (hRj : Rj ≤ Ij / 2048) (hρ : ρ ≤ Rj * (1 + Work.EKLC6Core.deltac * ε / 2))
    (hde1 : Work.EKLC6Core.deltac * ε ≤ 1) :
    30 * (ε * J) + ρ + 3 * (30 * (ε * J)) * ρ ≤ 2 ^ 25 * (ε * Im) := by
  have _ : Im ≤ 1 / 2 := hImh
  have hde : 0 < Work.EKLC6Core.deltac * ε := mul_pos Work.EKLC6Core.deltac_pos hε0
  have hA0 : 0 < ε * J := mul_pos hε0 hJ0
  have heps2 : ε ≤ 1 / 2 := by
    have h : Work.EKLC6Core.epsZero ≤ 1 / 2 := by rw [epsZero, deltac]; norm_num
    linarith
  have hAq : ε * J ≤ 1 / 4 := by nlinarith [hε0, hJ0, heps2, hJh]
  have hAub : ε * J ≤ 2 ^ 19 * (ε * Im) := by nlinarith [hJIm, hε0]
  have hRjb : Rj ≤ 45 / 64 * (ε * J) := by nlinarith [hRj, hIj]
  have hfac : 1 + Work.EKLC6Core.deltac * ε / 2 ≤ 3 / 2 := by nlinarith [hde1]
  have hρb : ρ ≤ 135 / 128 * (ε * J) := by nlinarith [hRj0, hRjb, hfac, hρ]
  nlinarith [hA0, hAq, hAub, hρb, hρ]



-- inlined from `boc_arith_Rprime`

theorem c2_epsZero_le_inv_two_pow_40 : epsZero ≤ 1 / (2 : ℝ) ^ 40 := by
  rw [epsZero, deltac]
  norm_num

/-- Bilinear domination: for `R ≤ R0`, `Rm ≤ Rm0` with `Rm0 ≥ 0` (so in particular
`1 + 3 Rm ≥ 0`) and `R0 ≥ 0`, the expression `30 R + Rm + 3 (30 R) Rm` is bounded
by its value at the corner `(R0, Rm0)`. -/
theorem c2_bilinear_thirty_bound {R Rm R0 Rm0 : ℝ}
    (hR : R ≤ R0) (hRm : Rm ≤ Rm0) (hRm0 : 0 ≤ Rm) (hR0 : 0 ≤ R0) :
    30 * R + Rm + 3 * (30 * R) * Rm ≤ 30 * R0 + Rm0 + 3 * (30 * R0) * Rm0 := by
  have hrew : 30 * R + Rm + 3 * (30 * R) * Rm = 30 * R * (1 + 3 * Rm) + Rm := by ring
  rw [hrew]
  have hA : 30 * R * (1 + 3 * Rm) ≤ 30 * R0 * (1 + 3 * Rm) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 1 + 3 * Rm)
    exact mul_le_mul_of_nonneg_left hR (by norm_num)
  have hB : 30 * R0 * (1 + 3 * Rm) ≤ 30 * R0 * (1 + 3 * Rm0) := by
    have h1 : (1 + 3 * Rm) ≤ (1 + 3 * Rm0) := by linarith
    exact mul_le_mul_of_nonneg_left h1 (by nlinarith)
  have hgoal : 30 * R0 * (1 + 3 * Rm0) + Rm0 = 30 * R0 + Rm0 + 3 * (30 * R0) * Rm0 := by
    ring
  linarith [hA, hB, hRm]

theorem c2_boc_arith_Rprime {ε R Im Rm : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ Work.EKLC6Core.epsZero) (hIm0 : 0 < Im) (hImh : Im ≤ 1 / 2)
    (hRm0 : 0 ≤ Rm) (hR : R ≤ 2 ^ 25 * (ε * Im)) (hRm : Rm ≤ Im / 2048) :
    30 * R + Rm + 3 * (30 * R) * Rm ≤ Im / 8 := by
  have hεle : ε ≤ 1 / (2 : ℝ) ^ 40 := le_trans hε1 c2_epsZero_le_inv_two_pow_40
  have hR0 : (0 : ℝ) ≤ 2 ^ 25 * (ε * Im) := by positivity
  have hRm00 : (0 : ℝ) ≤ Im / 2048 := by positivity
  -- Step 1: dominate the left-hand side by its value at the corner `(R0, Rm0)`.
  have hcorn : 30 * R + Rm + 3 * (30 * R) * Rm ≤
      30 * (2 ^ 25 * (ε * Im)) + Im / 2048 + 3 * (30 * (2 ^ 25 * (ε * Im))) * (Im / 2048) :=
    c2_bilinear_thirty_bound hR hRm hRm0 hR0
  -- Step 2: the corner value is at most `Im/8`.
  have hcorner : 30 * (2 ^ 25 * (ε * Im)) + Im / 2048 +
      3 * (30 * (2 ^ 25 * (ε * Im))) * (Im / 2048) ≤ Im / 8 := by
    have key : 30 * 2 ^ 25 * ε * (1 + 3 * (Im / 2048)) + 1 / 2048 ≤ 1 / 8 := by
      have hIM : (1 + 3 * (Im / 2048)) ≤ 2 := by linarith [hImh]
      have hb1 : 30 * 2 ^ 25 * ε * (1 + 3 * (Im / 2048)) ≤ 30 * 2 ^ 25 * ε * 2 :=
        mul_le_mul_of_nonneg_left hIM (by positivity)
      have hb2 : 30 * 2 ^ 25 * ε * 2 ≤ 30 * 2 ^ 25 * (1 / (2 : ℝ) ^ 40) * 2 := by
        have hh : (30 * (2 : ℝ) ^ 25 * 2) * ε ≤ (30 * (2 : ℝ) ^ 25 * 2) * (1 / (2 : ℝ) ^ 40) :=
          mul_le_mul_of_nonneg_left hεle (by norm_num)
        nlinarith [hh]
      have hnum : 30 * 2 ^ 25 * (1 / (2 : ℝ) ^ 40) * 2 + 1 / 2048 ≤ 1 / 8 := by norm_num
      linarith [hb1, hb2, hnum]
    have hmul := mul_le_mul_of_nonneg_left key (le_of_lt hIm0)
    nlinarith [hmul]
  linarith [hcorn, hcorner]



-- inlined from `boc_arith_final`

theorem c2_boc_arith_final {ε J Ij Rj ρ : ℝ}
    (hε0 : 0 < ε) (hde1 : Work.EKLC6Core.deltac * ε ≤ 1)
    (hJ0 : 0 < J) (hJh : J ≤ 1 / 2) (hIj0 : 0 < Ij) (hIj : Ij ≤ 1 / 2) (hRj0 : 0 ≤ Rj)
    (hRj_lo : Ij / 4096 ≤ Rj) (hRj_hi : Rj ≤ Ij / 2048)
    (hρ : ρ ≤ Rj * (1 + Work.EKLC6Core.deltac * ε / 2))
    (hJb : J ≤ 16 * 2 ^ 19 * Ij) :
    30 * (ε * J) + ρ + 3 * (30 * (ε * J)) * ρ ≤ Rj * (1 + Work.EKLC6Core.deltac * ε) := by
  have hdt : deltac = 2 ^ 60 := rfl
  rw [hdt] at hde1 hρ ⊢
  -- `Rj` is strictly positive and bounded by `1/4096`.
  have hRjpos : 0 < Rj := by
    have : (0 : ℝ) < Ij / 4096 := by positivity
    linarith [hRj_lo]
  have hRjle : Rj ≤ 1 / 4096 := by linarith [hRj_hi, hIj]
  -- The main smallness estimate: `30 ε J ≤ Rj * (deltac * ε) / 4`.
  have hA : 30 * (ε * J) ≤ Rj * (2 ^ 60 * ε) / 4 := by
    nlinarith [hε0, hRjpos, hJb, hRj_lo]
  -- `3 * Rj * (1 + deltac * ε / 2) ≤ 1`.
  have hB : 3 * Rj * (1 + 2 ^ 60 * ε / 2) ≤ 1 := by
    nlinarith [hRjle, hde1, hε0]
  have hEJ0 : 0 ≤ 1 + 90 * (ε * J) := by nlinarith [hε0, hJ0]
  have hRjD : 0 ≤ Rj * (1 + 2 ^ 60 * ε / 2) := by nlinarith [hRjpos, hε0]
  have hC1 : 90 * (ε * J) ≤ 3 * Rj * (2 ^ 60 * ε) / 4 := by linarith [hA]
  have hC2 : ρ * (1 + 90 * (ε * J))
      ≤ Rj * (1 + 2 ^ 60 * ε / 2) * (1 + 90 * (ε * J)) :=
    mul_le_mul_of_nonneg_right hρ hEJ0
  have hC3 : Rj * (1 + 2 ^ 60 * ε / 2) * (1 + 90 * (ε * J))
      ≤ Rj * (1 + 2 ^ 60 * ε / 2) * (1 + 3 * Rj * (2 ^ 60 * ε) / 4) := by
    apply mul_le_mul_of_nonneg_left _ hRjD
    linarith [hC1]
  have hC4 : Rj * (2 ^ 60 * ε) / 4
        + Rj * (1 + 2 ^ 60 * ε / 2) * (1 + 3 * Rj * (2 ^ 60 * ε) / 4)
      ≤ Rj * (1 + 2 ^ 60 * ε) := by
    nlinarith [hB, hRjpos, hε0]
  have hrw : 30 * (ε * J) + ρ + 3 * (30 * (ε * J)) * ρ
      = 30 * (ε * J) + ρ * (1 + 90 * (ε * J)) := by ring
  rw [hrw]
  linarith [hA, hC2, hC3, hC4]



-- inlined from `bad_inCol_shell`

theorem c2_badInCol_arith_k {r ink0 inkz ε de : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 2)
    (hε : 0 < ε) (hde : 0 ≤ de) (hde1 : de ≤ 1)
    (hβ : ink0 ≤ 4096 * r) (hK : inkz ≤ 2 ^ 19 * ink0)
    (hde_eq : de = deltac * ε) :
    ε * inkz * (1 + 3 * (r * (1 - de))) ≤ r * de := by
  have h1 : (1 + 3 * (r * (1 - de))) ≤ 3 := by nlinarith [hr, hr1, hde, hde1]
  have h2 : ε * inkz ≤ ε * (2 ^ 19 * ink0) := mul_le_mul_of_nonneg_left hK (le_of_lt hε)
  have h3 : ε * (2 ^ 19 * ink0) ≤ ε * (2 ^ 19 * (4096 * r)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hβ (by norm_num)) (le_of_lt hε)
  have h4 : ε * inkz ≤ ε * (2 ^ 19 * (4096 * r)) := le_trans h2 h3
  have h5 : ε * inkz * (1 + 3 * (r * (1 - de))) ≤ ε * (2 ^ 19 * (4096 * r)) * 3 := by
    have h6 : 0 ≤ 1 + 3 * (r * (1 - de)) := by nlinarith [hde, hde1, hr]
    have h7 : 0 ≤ ε * (2 ^ 19 * (4096 * r)) := by positivity
    exact mul_le_mul h4 h1 h6 h7
  have h8 : ε * (2 ^ 19 * (4096 * r)) * 3 = 3 * 2^19 * 4096 * (ε * r) := by ring
  have h9 : 3 * 2^19 * 4096 * (ε * r) ≤ deltac * (ε * r) := by
    have hm : 3 * 2^19 * 4096 ≤ deltac := by norm_num [deltac]
    exact mul_le_mul_of_nonneg_right hm (by positivity)
  have h10 : deltac * (ε * r) = r * de := by rw [hde_eq]; ring
  linarith [h5, h8, h9, h10]

/-- Rewriting step of the inside collar: the exponent of the product displacement
`V_mul_subset_V` is bounded by `r`. -/
theorem c2_badInCol_arith_sum {r inkz ε de : ℝ}
    (hk : ε * inkz * (1 + 3 * (r * (1 - de))) ≤ r * de) :
    ε * inkz + r * (1 - de) + 3 * (ε * inkz) * (r * (1 - de)) ≤ r := by
  nlinarith [hk]

theorem c2_bad_inCol_shell {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsFiniteMeasure μ] {y : ℕ → Work.EKLContract.X3} {j : ℕ}
    (hj : j ∈ Work.EKLC6Core.sel y) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ Work.EKLC6Core.epsZero) {z : Work.EKLContract.X3} {v : Work.EKLContract.SL3}
    (hzB : z ∈ Work.EKLComp.Vball (Work.EKLC6Core.cellRad μ y j) (y j))
    (hv : v ∈ Work.EKLContract.V (ε * Work.EKLC6Core.injCap z))
    (hvz : v • z ∉ Work.EKLComp.Vball (Work.EKLC6Core.cellRad μ y j) (y j)) :
    z ∈ Work.EKLC6Core.shell μ y (Work.EKLC6Core.deltac * ε) j := by
  have hspec := Work.EKLC6Core.cellRad_spec (μ := μ) hj
  have hrpos : 0 < Work.EKLC6Core.cellRad μ y j := Work.EKLC6Core.cellRad_pos (μ := μ) hj
  have hrhi : Work.EKLC6Core.cellRad μ y j ≤ Work.EKLC6Core.cellHi (y j) := hspec.2.1
  have hr1 : Work.EKLC6Core.cellRad μ y j ≤ 1 / 2 :=
    le_trans (le_trans hrhi (Work.EKLC6Core.cellHi_le _)) (by norm_num)
  have hlo : Work.EKLC6Core.cellLo (y j) ≤ Work.EKLC6Core.cellRad μ y j := hspec.1
  -- `cellLo (y j) = injCap (y j)/4096 ≤ cellRad μ y j`, i.e. `injCap (y j) ≤ 4096 * cellRad`.
  have hβ : Work.EKLC6Core.injCap (y j) ≤ 4096 * Work.EKLC6Core.cellRad μ y j := by
    have h := hlo
    rw [Work.EKLC6Core.cellLo, div_le_iff₀ (by norm_num : (0:ℝ) < 4096)] at h
    linarith
  have hde : 0 ≤ Work.EKLC6Core.deltac * ε :=
    mul_nonneg (le_of_lt Work.EKLC6Core.deltac_pos) (le_of_lt hε0)
  have hde1 : Work.EKLC6Core.deltac * ε ≤ 1 := Work.EKLC6Core.deltac_eps_le_one hε1
  -- the shallow ball is well inside the injectivity threshold of `y j`.
  have hr8 : Work.EKLC6Core.cellRad μ y j * (1 - Work.EKLC6Core.deltac * ε)
      ≤ Work.EKLC6Core.injCap (y j) / 8 := by
    have h1 : Work.EKLC6Core.cellRad μ y j * (1 - Work.EKLC6Core.deltac * ε)
        ≤ Work.EKLC6Core.cellRad μ y j := by nlinarith [hde, hrpos]
    have h2 : Work.EKLC6Core.cellRad μ y j ≤ Work.EKLC6Core.injCap (y j) / 8 :=
      le_trans hrhi (by
        rw [Work.EKLC6Core.cellHi]
        exact div_le_div_of_nonneg_left (le_of_lt (Work.EKLC6Core.injCap_pos _))
          (by norm_num) (by norm_num))
    linarith
  have hmon : Work.EKLC6Core.cellRad μ y j
      ≤ Work.EKLC6Core.cellRad μ y j * (1 + Work.EKLC6Core.deltac * ε) := by
    nlinarith [hde, hrpos]
  rw [Work.EKLC6Core.shell]
  refine ⟨Work.Misiurewicz.Vball_mono (y j) hmon hzB, ?_⟩
  -- suppose `z = u • y j` lies deep inside the ball.
  intro hzdeep
  obtain ⟨u, hu, rfl⟩ := Work.EKLComp.mem_Vball.mp hzdeep
  have hcap : Work.EKLC6Core.injCap (u • y j) ≤ 2 ^ 19 * Work.EKLC6Core.injCap (y j) :=
    Work.EKLC6Core.injCap_le_mul_of_mem_Vball (z := u • y j) (y := y j)
      (r := Work.EKLC6Core.cellRad μ y j * (1 - Work.EKLC6Core.deltac * ε))
      (by nlinarith [hde, hde1, hrpos]) hr8 ⟨u, hu, rfl⟩
  have hkey := c2_badInCol_arith_k (r := Work.EKLC6Core.cellRad μ y j)
    (ink0 := Work.EKLC6Core.injCap (y j)) (inkz := Work.EKLC6Core.injCap (u • y j))
    (ε := ε) (de := Work.EKLC6Core.deltac * ε)
    hrpos hr1 hε0 hde hde1 hβ hcap rfl
  have hsum := c2_badInCol_arith_sum (r := Work.EKLC6Core.cellRad μ y j)
    (inkz := Work.EKLC6Core.injCap (u • y j)) (ε := ε)
    (de := Work.EKLC6Core.deltac * ε) hkey
  have hmem : v • (u • y j) ∈ Work.EKLComp.Vball (Work.EKLC6Core.cellRad μ y j) (y j) := by
    refine ⟨v * u, ?_, ?_⟩
    · refine Work.Misiurewicz.V_mono ?_ (Work.EKLC6Core.V_mul_subset_V
        (s := ε * Work.EKLC6Core.injCap (u • y j))
        (t := Work.EKLC6Core.cellRad μ y j * (1 - Work.EKLC6Core.deltac * ε))
        (mul_nonneg (le_of_lt hε0) (le_of_lt (Work.EKLC6Core.injCap_pos _)))
        (by nlinarith [hde, hde1, hrpos]) hv hu)
      linarith [hsum]
    · exact mul_smul v u (y j)
  exact hvz hmem



-- inlined from `bad_outCol_upper`

theorem c2_bad_outCol_upper {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsFiniteMeasure μ] {y : ℕ → Work.EKLContract.X3} {j m : ℕ}
    (hj : j ∈ Work.EKLC6Core.sel y) (hm : m ∈ Work.EKLC6Core.sel y) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ Work.EKLC6Core.epsZero) {z : Work.EKLContract.X3}
    {v : Work.EKLContract.SL3} {ρ : ℝ}
    (hz_in : z ∈ Work.EKLComp.Vball (Work.EKLC6Core.cellRad μ y m) (y m))
    (hv : v ∈ Work.EKLContract.V (ε * Work.EKLC6Core.injCap z))
    (hρ_lo : Work.EKLC6Core.cellRad μ y j ≤ ρ)
    (hρ_hi : ρ ≤ Work.EKLC6Core.cellRad μ y j * (1 + Work.EKLC6Core.deltac * ε / 2))
    (hvz : v • z ∈ Work.EKLComp.Vball ρ (y j)) :
    z ∈ Work.EKLComp.Vball (Work.EKLC6Core.cellRad μ y j * (1 + Work.EKLC6Core.deltac * ε)) (y j) := by
  have hde1 : Work.EKLC6Core.deltac * ε ≤ 1 := Work.EKLC6Core.deltac_eps_le_one hε1
  have hJpos : 0 < Work.EKLC6Core.injCap z := Work.EKLC6Core.injCap_pos z
  have hJhalf : Work.EKLC6Core.injCap z ≤ 1 / 2 := Work.EKLC6Core.injCap_le_half z
  have hIjpos : 0 < Work.EKLC6Core.injCap (y j) := Work.EKLC6Core.injCap_pos _
  have hIjhalf : Work.EKLC6Core.injCap (y j) ≤ 1 / 2 := Work.EKLC6Core.injCap_le_half _
  have hImpos : 0 < Work.EKLC6Core.injCap (y m) := Work.EKLC6Core.injCap_pos _
  have hImhalf : Work.EKLC6Core.injCap (y m) ≤ 1 / 2 := Work.EKLC6Core.injCap_le_half _
  have hRjpos : 0 < Work.EKLC6Core.cellRad μ y j := Work.EKLC6Core.cellRad_pos hj
  have hRmpos : 0 < Work.EKLC6Core.cellRad μ y m := Work.EKLC6Core.cellRad_pos hm
  have hRj_lo : Work.EKLC6Core.injCap (y j) / 4096 ≤ Work.EKLC6Core.cellRad μ y j := by
    have h := (Work.EKLC6Core.cellRad_spec (μ := μ) hj).1
    rwa [Work.EKLC6Core.cellLo] at h
  have hRj_hi : Work.EKLC6Core.cellRad μ y j ≤ Work.EKLC6Core.injCap (y j) / 2048 := by
    have h := (Work.EKLC6Core.cellRad_spec (μ := μ) hj).2.1
    rwa [Work.EKLC6Core.cellHi] at h
  have hRm_hi : Work.EKLC6Core.cellRad μ y m ≤ Work.EKLC6Core.injCap (y m) / 2048 := by
    have h := (Work.EKLC6Core.cellRad_spec (μ := μ) hm).2.1
    rwa [Work.EKLC6Core.cellHi] at h
  have hRm_le8 : Work.EKLC6Core.cellRad μ y m ≤ Work.EKLC6Core.injCap (y m) / 8 := by
    have h1 : Work.EKLC6Core.injCap (y m) / 2048 ≤ Work.EKLC6Core.injCap (y m) / 8 :=
      div_le_div_of_nonneg_left (le_of_lt hImpos) (by norm_num) (by norm_num)
    linarith
  have hJ_le_Im : Work.EKLC6Core.injCap z ≤ 2 ^ 19 * Work.EKLC6Core.injCap (y m) :=
    Work.EKLC6Core.injCap_le_mul_of_mem_Vball (le_of_lt hRmpos) hRm_le8 hz_in
  obtain ⟨b, hb, hbEq⟩ := Work.EKLComp.mem_Vball.mp hvz
  have hapos : 0 < ε * Work.EKLC6Core.injCap z := mul_pos hε0 hJpos
  have hahalf : ε * Work.EKLC6Core.injCap z ≤ 1 / 2 := by
    have h1 : ε ≤ 1 / 2 :=
      le_trans hε1 (by rw [Work.EKLC6Core.epsZero, Work.EKLC6Core.deltac]; norm_num)
    nlinarith [hε0, hJhalf]
  have hvinv : v⁻¹ ∈ Work.EKLContract.V (30 * (ε * Work.EKLC6Core.injCap z)) :=
    Work.Misiurewicz.V_mono (by linarith) (Work.EKLComp.inv_mem_V hapos (by linarith) hv)
  have hρ_nonneg : 0 ≤ ρ := le_trans (le_of_lt hRjpos) hρ_lo
  set E : ℝ := 30 * (ε * Work.EKLC6Core.injCap z) + ρ
      + 3 * (30 * (ε * Work.EKLC6Core.injCap z)) * ρ with hEdef
  have hW : v⁻¹ * b ∈ Work.EKLContract.V E := by
    rw [hEdef]
    exact Work.EKLC6Core.V_mul_subset_V (mul_nonneg (by norm_num) (le_of_lt hapos)) hρ_nonneg hvinv hb
  have hzW_eq : (v⁻¹ * b) • (y j) = z := by
    rw [mul_smul, hbEq, ← mul_smul, inv_mul_cancel, one_smul]
  have hzW : z ∈ Work.EKLComp.Vball E (y j) := ⟨v⁻¹ * b, hW, hzW_eq⟩
  have hEpos : 0 < E := by rw [hEdef]; nlinarith [hapos, hρ_nonneg]
  by_cases hcase : E ≤ Work.EKLC6Core.injCap (y j) / 8
  · -- ## small case
    have hJb : Work.EKLC6Core.injCap z ≤ 16 * 2 ^ 19 * Work.EKLC6Core.injCap (y j) := by
      have h1 : Work.EKLC6Core.injCap z ≤ 2 ^ 19 * Work.EKLC6Core.injCap (y j) :=
        Work.EKLC6Core.injCap_le_mul_of_mem_Vball (z := z) (y := y j) (r := E)
          (le_of_lt hEpos) hcase hzW
      nlinarith [h1, hIjpos]
    have hfin : E ≤ Work.EKLC6Core.cellRad μ y j * (1 + Work.EKLC6Core.deltac * ε) := by
      rw [hEdef]
      exact c2_boc_arith_final hε0 hde1 hJpos hJhalf hIjpos hIjhalf (le_of_lt hRjpos)
        hRj_lo hRj_hi hρ_hi hJb
    exact Work.Misiurewicz.Vball_mono (y j) hfin hzW
  · -- ## large case
    push_neg at hcase
    have hsmall : Work.EKLC6Core.injCap (y j) < 1440 * (ε * Work.EKLC6Core.injCap z) :=
      c2_boc_arith_case_small hε0 hε1 hJpos hJhalf hIjpos (le_of_lt hRjpos) hcase hEdef
        hRj_hi hρ_hi hde1
    have hRsmall : E ≤ 2 ^ 25 * (ε * Work.EKLC6Core.injCap (y m)) := by
      rw [hEdef]
      exact c2_boc_arith_R_small hε0 hε1 hJpos hJhalf hImpos hImhalf (le_of_lt hRjpos)
        hsmall hJ_le_Im hRj_hi hρ_hi hde1
    have hRp : 30 * E + Work.EKLC6Core.cellRad μ y m
          + 3 * (30 * E) * Work.EKLC6Core.cellRad μ y m
        ≤ Work.EKLC6Core.injCap (y m) / 8 :=
      c2_boc_arith_Rprime hε0 hε1 hImpos hImhalf (le_of_lt hRmpos) hRsmall hRm_hi
    have hE1 : E ≤ 1 := by
      have h2 : ε * Work.EKLC6Core.injCap (y m) ≤ 1 / 2 ^ 36 := by
        have hε2 : ε ≤ 1 / 2 ^ 60 :=
          le_trans hε1 (by rw [Work.EKLC6Core.epsZero, Work.EKLC6Core.deltac])
        nlinarith [hε2, hImhalf]
      nlinarith [hRsmall, h2]
    have hWinv : (v⁻¹ * b)⁻¹ ∈ Work.EKLContract.V (30 * E) :=
      Work.Misiurewicz.V_mono (by linarith) (Work.EKLComp.inv_mem_V hEpos hE1 hW)
    obtain ⟨dd, hdd, hddEq⟩ := Work.EKLComp.mem_Vball.mp hz_in
    have hyj_eq : ((v⁻¹ * b)⁻¹ * dd) • (y m) = y j := by
      rw [mul_smul, hddEq, ← hzW_eq, ← mul_smul, inv_mul_cancel, one_smul]
    have hyj_mem : y j ∈ Work.EKLComp.Vball (30 * E + Work.EKLC6Core.cellRad μ y m
        + 3 * (30 * E) * Work.EKLC6Core.cellRad μ y m) (y m) :=
      ⟨(v⁻¹ * b)⁻¹ * dd,
        Work.EKLC6Core.V_mul_subset_V (mul_nonneg (by norm_num) (le_of_lt hEpos))
          (le_of_lt hRmpos) hWinv hdd, hyj_eq⟩
    obtain ⟨ww, hww, hwwEq⟩ := Work.EKLComp.mem_Vball.mp hyj_mem
    have hIm16 : Work.EKLC6Core.injCap (y m) / 16 ≤ Work.EKLC6Core.injCap (y j) := by
      have hpos : 0 < 30 * E + Work.EKLC6Core.cellRad μ y m
          + 3 * (30 * E) * Work.EKLC6Core.cellRad μ y m := by
        nlinarith [hEpos, hRmpos]
      have hhalf : 30 * E + Work.EKLC6Core.cellRad μ y m
          + 3 * (30 * E) * Work.EKLC6Core.cellRad μ y m ≤ 1 / 2 := by
        nlinarith [hRp, hImhalf, hImpos]
      have h := Work.EKLC6Core.injCap_mem_V_le (x := y m)
        (a := 30 * E + Work.EKLC6Core.cellRad μ y m
          + 3 * (30 * E) * Work.EKLC6Core.cellRad μ y m) hpos hhalf hRp hww
      rwa [hwwEq] at h
    have hJb : Work.EKLC6Core.injCap z ≤ 16 * 2 ^ 19 * Work.EKLC6Core.injCap (y j) := by
      nlinarith [hJ_le_Im, hIm16, hImpos]
    have hfin : E ≤ Work.EKLC6Core.cellRad μ y j * (1 + Work.EKLC6Core.deltac * ε) := by
      rw [hEdef]
      exact c2_boc_arith_final hε0 hde1 hJpos hJhalf hIjpos hIjhalf (le_of_lt hRjpos)
        hRj_lo hRj_hi hρ_hi hJb
    exact Work.Misiurewicz.Vball_mono (y j) hfin hzW



-- inlined from `bad_subset_shells`

theorem c2_bad_subset_shells (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure μ] (y : ℕ → Work.EKLContract.X3)
    (hcover : ∀ z : Work.EKLContract.X3, ∃ n : ℕ, n ∈ Work.EKLC6Core.sel y ∧
      z ∈ Work.EKLC6Core.cellBall μ y n)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ Work.EKLC6Core.epsZero) {z : Work.EKLContract.X3}
    {k : ℕ} (hz : z ∈ Work.EKLC6Core.Qcell μ y k)
    (hm : Work.EKLC6Core.cellMargin (Work.EKLC6Core.Qcell μ y) k z <
      ε * Work.EKLC6Core.injCap z) :
    ∃ j : ℕ, j ∈ Work.EKLC6Core.sel y ∧
      z ∈ Work.EKLC6Core.shell μ y (Work.EKLC6Core.deltac * ε) j := by
  -- ## Step 1: there is a displacement `v ∈ V (ε * injCap z)` moving `z` out of its cell
  have hηpos : 0 < ε * injCap z := mul_pos hε0 (injCap_pos z)
  have heps1 : epsZero ≤ 1 := by rw [epsZero, deltac]; norm_num
  have hη2 : ε * injCap z ≤ 2 := by
    have h1 := injCap_le_half z
    nlinarith [le_of_lt hε0, hε1, heps1, h1]
  have hcross : ∃ v : SL3, v ∈ V (ε * injCap z) ∧ v • z ∉ Qcell μ y k := by
    by_contra hcon
    push_neg at hcon
    have hmem : ε * injCap z ∈ {r : ℝ | 0 < r ∧ r ≤ 2 ∧
        ∀ v : SL3, v ∈ V r → v • z ∈ Qcell μ y k} := ⟨hηpos, hη2, hcon⟩
    have hle : ε * injCap z ≤ cellMargin (Qcell μ y) k z := by
      rw [cellMargin]
      exact le_csSup ⟨2, fun r hr => hr.2.1⟩ hmem
    linarith
  obtain ⟨v, hv, hvznot⟩ := hcross
  -- ## Step 2: `k` is selected and `z` lies in the `k`-th cell ball
  have hk_sel : k ∈ sel y := by
    by_contra hk
    have hzB : z ∈ cellBall μ y k := Qcell_subset μ y k hz
    rw [cellBall_eq_empty hk] at hzB
    exact absurd hzB (Set.notMem_empty z)
  have hzBk : z ∈ Work.EKLComp.Vball (cellRad μ y k) (y k) := by
    have h := Qcell_subset μ y k hz
    rwa [cellBall_eq hk_sel] at h
  -- ## Step 3: split according to whether `v • z` is still in the `k`-th cell ball
  by_cases hcase : v • z ∈ cellBall μ y k
  · -- ### Case 2: `v • z` is still in the `k`-th ball; it must have crossed an earlier ball
    have hl_exists : ∃ l : ℕ, l < k ∧ v • z ∈ closure (cellBall μ y l) := by
      by_contra hcon
      push_neg at hcon
      have hmem : v • z ∈ Qcell μ y k := by
        refine ⟨hcase, ?_⟩
        simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_compl_iff]
        intro l hl
        exact hcon l hl
      exact hvznot hmem
    obtain ⟨l, hlk, hvl⟩ := hl_exists
    have hl_sel : l ∈ sel y := by
      by_contra hl
      rw [cellBall_eq_empty hl, closure_empty] at hvl
      exact absurd hvl (Set.notMem_empty (v • z))
    have hcellpos : 0 < cellRad μ y l := cellRad_pos hl_sel
    have hδpos : 0 < deltac * ε := mul_pos deltac_pos hε0
    have hδ1 : deltac * ε ≤ 1 := deltac_eps_le_one hε1
    set ρ : ℝ := cellRad μ y l * (1 + deltac * ε / 2) with hρdef
    have hρ_lo : cellRad μ y l ≤ ρ := by rw [hρdef]; nlinarith [hδpos, hcellpos]
    have hρ_hi : ρ ≤ cellRad μ y l * (1 + deltac * ε / 2) := le_of_eq hρdef
    have hρ_gt : cellRad μ y l < ρ := by rw [hρdef]; nlinarith [hδpos, hcellpos]
    have hvl2 : v • z ∈ closure (Work.EKLComp.Vball (cellRad μ y l) (y l)) := by
      rwa [cellBall_eq hl_sel] at hvl
    have hvl' : v • z ∈ Work.EKLComp.Vball ρ (y l) :=
      Work.Misiurewicz.closure_Vball_subset_Vball_of_lt (y l) hρ_gt hvl2
    have hup : z ∈ Work.EKLComp.Vball (cellRad μ y l * (1 + deltac * ε)) (y l) :=
      c2_bad_outCol_upper hl_sel hk_sel hε0 hε1 hzBk hv hρ_lo hρ_hi hvl'
    have hnotcl : z ∉ closure (cellBall μ y l) := by
      have hh : z ∈ ⋂ l' ∈ Set.Iio k, (closure (cellBall μ y l'))ᶜ := hz.2
      simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_compl_iff] at hh
      exact hh l hlk
    have hlow : z ∉ Work.EKLComp.Vball (cellRad μ y l * (1 - deltac * ε)) (y l) := by
      intro hzlow
      apply hnotcl
      rw [cellBall_eq hl_sel]
      exact subset_closure (Work.Misiurewicz.Vball_mono (y l)
        (by nlinarith [hcellpos, hδpos, hδ1]) hzlow)
    refine ⟨l, hl_sel, ?_⟩
    rw [shell]
    exact ⟨hup, hlow⟩
  · -- ### Case 1: `v • z` left the `k`-th ball: the "inside collar"
    have hvz_out : v • z ∉ Work.EKLComp.Vball (cellRad μ y k) (y k) := by
      rw [cellBall_eq hk_sel] at hcase
      exact hcase
    exact ⟨k, hk_sel, c2_bad_inCol_shell hk_sel hε0 hε1 hzBk hv hvz_out⟩



theorem cell_relthin_cover2 {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] :
    ∃ (Q : ℕ → Set Work.EKLContract.X3) (δ : ℕ → ℝ) (g : ℕ → Work.EKLContract.SL3)
      (C α : ℝ),
      (∀ k, IsOpen (Q k)) ∧ (∀ k l, k ≠ l → Disjoint (Q k) (Q l)) ∧
      μ (Set.iUnion (fun k : ℕ => Q k))ᶜ = 0 ∧
      (∀ k, 0 < δ k ∧ δ k ≤ 1 / 16) ∧
      (∀ k, Q k ⊆ (fun v : Work.EKLContract.SL3 => v • Work.EKLContract.mkX (g k)) ''
        (Work.EKLContract.V (δ k / 2))) ∧
      (∀ k (v₁ v₂ : Work.EKLContract.SL3), v₁ ∈ Work.EKLContract.V (4 * δ k) →
        v₂ ∈ Work.EKLContract.V (4 * δ k) →
        v₁ • Work.EKLContract.mkX (g k) = v₂ • Work.EKLContract.mkX (g k) → v₁ = v₂) ∧
      0 < C ∧ 0 < α ∧
      ∀ ε : ℝ, 0 < ε → μ {y : Work.EKLContract.X3 |
          ∀ k, y ∈ Q k → Work.EKLC6Core.cellMargin Q k y < ε * Work.EKLC6Core.injCap y}
        ≤ ENNReal.ofReal (C * ε ^ α) := by
  classical
  haveI hfin : MeasureTheory.IsFiniteMeasure μ := inferInstance
  obtain ⟨y, hy⟩ := exists_dense_seq_X3
  have hcover : ∀ z : X3, ∃ n : ℕ, n ∈ sel y ∧ z ∈ cellBall μ y n :=
    fun z => sel_cover μ y hy z
  have hcovU : (⋃ n, cellBall μ y n) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨n, -, hn⟩ := hcover z
    exact ⟨n, hn⟩
  obtain ⟨Msum, hMpos, hsum⟩ := sel_count_sum μ y hy
  set Cc : ℝ := max (32 * deltac * Msum) (1 / epsZero) with hCc
  set g : ℕ → SL3 := fun k => Classical.choose (QuotientGroup.mk_surjective (y k)) with hgdef
  have hgmk : ∀ k, mkX (g k) = y k := fun k =>
    Classical.choose_spec (QuotientGroup.mk_surjective (y k))
  refine ⟨Qcell μ y, fun k => 2 * cellRad μ y k, g, Cc, 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; exact Qcell_open μ y k
  · intro k l hkl; exact Qcell_disjoint μ y k l hkl
  · exact Qcell_conull μ y hcovU
  · intro k
    refine ⟨by have := cellRad_pos_all μ y k; linarith, ?_⟩
    have h1 : cellRad μ y k ≤ cellHi (y k) := cellRad_le_cellHi_all μ y k
    have h2 : cellHi (y k) ≤ 1 / 4096 := cellHi_le (y k)
    linarith
  · intro k z hz
    have hsub : z ∈ cellBall μ y k := Qcell_subset μ y k hz
    by_cases hk : k ∈ sel y
    · rw [cellBall_eq hk] at hsub
      obtain ⟨u, hu, huz⟩ := hsub
      refine ⟨u, ?_, ?_⟩
      · show u ∈ Work.EKLContract.V ((2 * cellRad μ y k) / 2)
        rwa [show (2 * cellRad μ y k) / 2 = cellRad μ y k by ring]
      · show u • mkX (g k) = z
        rw [hgmk k]
        exact huz
    · rw [cellBall_eq_empty hk] at hsub
      exact hsub.elim
  · intro k v₁ v₂ h₁ h₂ heq
    have h1 : v₁ ∈ Work.EKLContract.V (8 * cellRad μ y k) := by
      rw [show 4 * (2 * cellRad μ y k) = 8 * cellRad μ y k by ring] at h₁
      exact h₁
    have h2 : v₂ ∈ Work.EKLContract.V (8 * cellRad μ y k) := by
      rw [show 4 * (2 * cellRad μ y k) = 8 * cellRad μ y k by ring] at h₂
      exact h₂
    have hinj : InjAt (y k) (8 * cellRad μ y k) := by
      refine injAt_of_lt_injCap (by have := cellRad_pos_all μ y k; linarith) ?_
      have h3 : 8 * cellRad μ y k ≤ 8 * cellHi (y k) := by
        have := cellRad_le_cellHi_all μ y k; linarith
      have h4 : 8 * cellHi (y k) < injCap (y k) := by
        rw [cellHi]; have := injCap_pos (y k); linarith
      linarith
    have heq' : v₁ • y k = v₂ • y k := by
      rw [← hgmk k]
      exact heq
    exact hinj v₁ v₂ h1 h2 heq'
  · refine lt_of_lt_of_le ?_ (le_max_left _ _)
    have : (0 : ℝ) < deltac := deltac_pos
    positivity
  · exact one_pos
  · intro ε hε
    by_cases hεs : ε ≤ epsZero
    · have hρ0 : 0 < deltac * ε := mul_pos deltac_pos hε
      have hρ1 : deltac * ε ≤ 1 := deltac_eps_le_one hεs
      have hsub : {w : X3 | ∀ k, w ∈ Qcell μ y k → cellMargin (Qcell μ y) k w < ε * injCap w}
          ⊆ (⋃ k, Qcell μ y k)ᶜ ∪ ⋃ j ∈ sel y, shell μ y (deltac * ε) j := by
        intro w hw
        by_cases hwU : w ∈ ⋃ k, Qcell μ y k
        · right
          obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hwU
          obtain ⟨j, hj, hjs⟩ := c2_bad_subset_shells μ y hcover hε hεs hk (hw k hk)
          exact Set.mem_iUnion₂.mpr ⟨j, hj, hjs⟩
        · left; exact hwU
      have hmono : μ (⋃ j ∈ sel y, shell μ y (deltac * ε) j)
          ≤ μ (⋃ j, selShell μ y (deltac * ε) j) := by
        refine measure_mono ?_
        intro w hw
        obtain ⟨j, hj, hwj⟩ := Set.mem_iUnion₂.mp hw
        exact Set.mem_iUnion.mpr ⟨j, by rw [selShell, if_pos hj]; exact hwj⟩
      have hunion : μ (⋃ j, selShell μ y (deltac * ε) j)
          ≤ ∑' j, μ (selShell μ y (deltac * ε) j) :=
        measure_iUnion_le (fun j => selShell μ y (deltac * ε) j)
      calc μ {w : X3 | ∀ k, w ∈ Qcell μ y k → cellMargin (Qcell μ y) k w < ε * injCap w}
          ≤ μ ((⋃ k, Qcell μ y k)ᶜ ∪ ⋃ j ∈ sel y, shell μ y (deltac * ε) j) :=
              measure_mono hsub
        _ ≤ μ ((⋃ k, Qcell μ y k)ᶜ) + μ (⋃ j ∈ sel y, shell μ y (deltac * ε) j) :=
              measure_union_le _ _
        _ = μ (⋃ j ∈ sel y, shell μ y (deltac * ε) j) := by
              rw [Qcell_conull μ y hcovU, zero_add]
        _ ≤ μ (⋃ j, selShell μ y (deltac * ε) j) := hmono
        _ ≤ ∑' j, μ (selShell μ y (deltac * ε) j) := hunion
        _ ≤ ∑' j, ENNReal.ofReal (32 * (deltac * ε)) * μ (countBall μ y j) :=
              ENNReal.tsum_le_tsum fun j => selShell_measure_le μ y hρ0 hρ1 j
        _ = ENNReal.ofReal (32 * (deltac * ε)) * ∑' j, μ (countBall μ y j) :=
              ENNReal.tsum_mul_left
        _ ≤ ENNReal.ofReal (32 * (deltac * ε)) * ENNReal.ofReal Msum :=
              mul_le_mul' le_rfl hsum
        _ = ENNReal.ofReal (32 * (deltac * ε) * Msum) :=
              (ENNReal.ofReal_mul
                (mul_nonneg (by norm_num : (0:ℝ) ≤ 32) (le_of_lt hρ0))).symm
        _ = ENNReal.ofReal ((32 * deltac * Msum) * ε) := by
              congr 1; ring
        _ ≤ ENNReal.ofReal (Cc * ε ^ (1:ℝ)) := by
              rw [Real.rpow_one, hCc]
              exact ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hε))
    · have hεp : epsZero < ε := lt_of_not_ge hεs
      have hge : 1 < Cc * ε := by
        have hpos : 0 < 1 / epsZero := div_pos one_pos epsZero_pos
        have h1 : (1 / epsZero) * epsZero = 1 := by
          rw [div_mul_cancel₀ _ (ne_of_gt epsZero_pos)]
        have h2 : (1 / epsZero) * epsZero < (1 / epsZero) * ε :=
          mul_lt_mul_of_pos_left hεp hpos
        calc (1 : ℝ) = (1 / epsZero) * epsZero := h1.symm
          _ < (1 / epsZero) * ε := h2
          _ ≤ Cc * ε := by
              rw [hCc]
              exact mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hε)
      calc μ {w : X3 | ∀ k, w ∈ Qcell μ y k → cellMargin (Qcell μ y) k w < ε * injCap w}
          ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ ≤ ENNReal.ofReal (Cc * ε ^ (1:ℝ)) := by
            rw [← ENNReal.ofReal_one, Real.rpow_one]
            exact ENNReal.ofReal_le_ofReal (le_of_lt hge)

end Work.EKLC6Core
