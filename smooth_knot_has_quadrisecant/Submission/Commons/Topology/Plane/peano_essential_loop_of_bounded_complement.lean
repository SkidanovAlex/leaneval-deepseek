import Mathlib
import Submission.Commons.Topology.Plane.paeno_continuum_pathConnected
import Submission.Commons.Topology.Plane.essential_loop_of_bounded_component
import Submission.Commons.Topology.Plane.exists_injective_circle_of_essential_loop

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Set Metric Filter
open scoped Topology
open Commons.Topology.Peano

namespace Commons.Topology.Plane

namespace LocalPeano

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [LocallyConnectedSpace X]

/-- The `ε`-sequence used for the local chain construction inside a bounded set `V`. -/
noncomputable def peps (V : Set X) (n : ℕ) : ℝ := (Metric.diam V + 1) * (1 / 2) ^ n

lemma peps_pos (V : Set X) (n : ℕ) : 0 < peps V n := by
  have h : (0 : ℝ) < Metric.diam V + 1 := by
    have := Metric.diam_nonneg (s := V); linarith
  exact mul_pos h (pow_pos (by norm_num) n)

lemma peps_zero (V : Set X) : peps V 0 = Metric.diam V + 1 := by simp [peps]

lemma peps_succ (V : Set X) (n : ℕ) : peps V (n + 1) = peps V n * (1 / 2) := by
  simp only [peps, pow_succ]; ring

lemma peps_tendsto_zero (V : Set X) : Tendsto (fun n : ℕ => peps V n) atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 : ℝ) / 2 < 1 by norm_num)
  simpa only [peps, mul_zero] using h.const_mul (Metric.diam V + 1)

/-- The initial stage of the local construction: the single cell `V`. -/
noncomputable def pstage0 {V : Set X} (hVo : IsOpen V) (hVc : IsConnected V) (x y : X)
    (hx : x ∈ V) (hy : y ∈ V) : Stage X (peps V 0) where
  x := x
  y := y
  k := 1
  hk := one_pos
  U := fun _ => V
  isOpen_U := fun i hi => hVo
  isConn_U := fun i hi => hVc
  chain_U := fun i hi => absurd hi (by omega)
  x_mem := hx
  y_mem := hy
  diam_U := fun i hi => by
    rw [peps_zero]; linarith [Metric.diam_nonneg (s := V)]

/-- The nested family of stages of the local construction. -/
noncomputable def pstages {V : Set X} (hVo : IsOpen V) (hVc : IsConnected V) (x y : X)
    (hx : x ∈ V) (hy : y ∈ V) : (n : ℕ) → Stage X (peps V n)
  | 0 => pstage0 hVo hVc x y hx hy
  | n + 1 => (pstages hVo hVc x y hx hy n).refine (peps V (n + 1)) (peps_pos V (n + 1))

lemma pstages_succ {V : Set X} (hVo : IsOpen V) (hVc : IsConnected V) (x y : X)
    (hx : x ∈ V) (hy : y ∈ V) (n : ℕ) :
    pstages hVo hVc x y hx hy (n + 1) =
      (pstages hVo hVc x y hx hy n).refine (peps V (n + 1)) (peps_pos V (n + 1)) := by
  rw [pstages]

lemma pstages_k_succ {V : Set X} (hVo : IsOpen V) (hVc : IsConnected V) (x y : X)
    (hx : x ∈ V) (hy : y ∈ V) (n : ℕ) :
    (pstages hVo hVc x y hx hy (n + 1)).k =
      (pstages hVo hVc x y hx hy n).k *
        (pstages hVo hVc x y hx hy n).blockLen (peps V (n + 1)) (peps_pos V (n + 1)) := by
  rw [pstages_succ]; rfl

/-- Nested nonempty closed sets of diameter tending to `0` in a complete metric space have a
unique common point. -/
lemma complete_unique_mem_iInter_nested (C : ℕ → Set X) (hclosed : ∀ n, IsClosed (C n))
    (hbdd : ∀ n, Bornology.IsBounded (C n))
    (hanti : ∀ i j, i ≤ j → C j ⊆ C i) (hne : ∀ n, (C n).Nonempty)
    (hdiam : ∀ ε : ℝ, 0 < ε → ∃ n, Metric.diam (C n) < ε) :
    ∃! x : X, x ∈ ⋂ n, C n := by
  have hnonempty : (⋂ n, C n).Nonempty := by
    refine Metric.nonempty_iInter_of_nonempty_biInter hclosed hbdd (fun N => ?_) ?_
    · obtain ⟨z, hz⟩ := hne N
      exact ⟨z, by
        rw [mem_iInter]
        intro i
        rw [mem_iInter]
        intro hi
        exact hanti i N hi hz⟩
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := hdiam ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hle : Metric.diam (C n) ≤ Metric.diam (C N) :=
        Metric.diam_mono (hanti N n hn) (hbdd N)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg]
      linarith
  have hdiam0 : Metric.diam (⋂ n, C n) = 0 := by
    refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) Metric.diam_nonneg
    obtain ⟨N, hN⟩ := hdiam ε hε
    have h1 : Metric.diam (⋂ n, C n) ≤ Metric.diam (C N) :=
      Metric.diam_mono (Set.iInter_subset C N) (hbdd N)
    linarith
  obtain ⟨x, hx⟩ := hnonempty
  refine ⟨x, hx, fun y hy => ?_⟩
  have h1 : dist y x ≤ Metric.diam (⋂ n, C n) :=
    Metric.dist_le_diam_of_mem (hbdd 0 |>.subset (iInter_subset C 0)) hy hx
  rw [hdiam0] at h1
  exact dist_eq_zero.mp (le_antisymm h1 dist_nonneg)

/-! ### The Limit section -/

section Limit

lemma gridIdx_zero (K : ℕ) : gridIdx K 0 = 0 := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp [gridIdx]
  · rw [gridIdx_eq K hK (by norm_num : (0:ℝ) ≤ 1)]
    exact Nat.eq_zero_of_le_zero (Nat.find_min' _
      (show (0:ℝ) ≤ (((0:ℕ):ℝ) + 1) / (K:ℝ) by positivity))

lemma gridIdx_one (K : ℕ) (hK : 0 < K) : gridIdx K 1 = K - 1 := by
  have h := gridIdx_le K hK (le_refl (1:ℝ))
  refine le_antisymm h ?_
  rw [gridIdx_eq K hK (le_refl (1:ℝ)), Nat.le_find_iff]
  intro m hm
  rw [not_le, div_lt_one (by exact_mod_cast hK)]
  have : m + 1 < K := by omega
  exact_mod_cast this

variable {V : Set X}

lemma pstages_x (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V) (hy : y ∈ V)
    (n : ℕ) : (pstages hVo hVc x y hx hy n).x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pstages_succ]; exact ih

lemma pstages_y (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V) (hy : y ∈ V)
    (n : ℕ) : (pstages hVo hVc x y hx hy n).y = y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pstages_succ]; exact ih

noncomputable def cell (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V)
    (hy : y ∈ V) (n : ℕ) (t : ℝ) : ℕ := gridIdx (pstages hVo hVc x y hx hy n).k t

lemma cell_lt (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V) (hy : y ∈ V)
    (n : ℕ) {t : ℝ} (ht : t ≤ 1) : cell hVo hVc x y hx hy n t < (pstages hVo hVc x y hx hy n).k :=
  lt_of_le_of_lt (gridIdx_le (pstages hVo hVc x y hx hy n).k (pstages hVo hVc x y hx hy n).hk ht)
    (Nat.sub_one_lt_of_lt (pstages hVo hVc x y hx hy n).hk)

lemma cell_zero (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V) (hy : y ∈ V)
    (n : ℕ) : cell hVo hVc x y hx hy n 0 = 0 := gridIdx_zero _

lemma cell_one (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V) (hy : y ∈ V)
    (n : ℕ) : cell hVo hVc x y hx hy n 1 = (pstages hVo hVc x y hx hy n).k - 1 :=
  gridIdx_one _ (pstages hVo hVc x y hx hy n).hk

noncomputable def cellSet (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V)
    (hy : y ∈ V) (n : ℕ) (t : ℝ) : Set X :=
  (pstages hVo hVc x y hx hy n).U (cell hVo hVc x y hx hy n t)

noncomputable def cellCl (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V)
    (hy : y ∈ V) (n : ℕ) (t : ℝ) : Set X := closure (cellSet hVo hVc x y hx hy n t)

lemma cellSet_subset_V (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V)
    (hy : y ∈ V) (n : ℕ) {t : ℝ} (ht : t ≤ 1) : cellSet hVo hVc x y hx hy n t ⊆ V := by
  induction n with
  | zero =>
    intro z hz
    exact hz
  | succ n ih =>
    intro z hz
    rw [cellSet] at hz
    have hcell : cell hVo hVc x y hx hy (n+1) t < (pstages hVo hVc x y hx hy (n+1)).k :=
      cell_lt hVo hVc x y hx hy (n+1) ht (t := t)
    rw [pstages_k_succ] at hcell
    have h2 := (pstages hVo hVc x y hx hy n).sub_refineU (peps V (n+1)) (peps_pos V (n+1))
      hcell hz
    have hdiv : cell hVo hVc x y hx hy (n+1) t /
        (pstages hVo hVc x y hx hy n).blockLen (peps V (n+1)) (peps_pos V (n+1)) =
        cell hVo hVc x y hx hy n t := by
      show gridIdx (pstages hVo hVc x y hx hy (n+1)).k t /
          (pstages hVo hVc x y hx hy n).blockLen (peps V (n+1)) (peps_pos V (n+1)) =
        gridIdx (pstages hVo hVc x y hx hy n).k t
      rw [pstages_k_succ]
      exact gridIdx_div _ _ (pstages hVo hVc x y hx hy n).hk
        ((pstages hVo hVc x y hx hy n).blockLen_pos (peps V (n+1)) (peps_pos V (n+1)))
        ht (t := t)
    rw [hdiv] at h2
    exact ih h2

lemma cellSet_nonempty (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V)
    (hy : y ∈ V) (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    (cellSet hVo hVc x y hx hy n t).Nonempty :=
  ((pstages hVo hVc x y hx hy n).isConn_U _ (cell_lt hVo hVc x y hx hy n ht)).1

lemma cellCl_nonempty (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V)
    (hy : y ∈ V) (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    (cellCl hVo hVc x y hx hy n t).Nonempty :=
  (cellSet_nonempty hVo hVc x y hx hy n ht).mono subset_closure

lemma cellSet_bounded (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    Bornology.IsBounded (cellSet hVo hVc x y hx hy n t) :=
  hVb.subset (cellSet_subset_V hVo hVc x y hx hy n ht)

lemma cellCl_bounded (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    Bornology.IsBounded (cellCl hVo hVc x y hx hy n t) :=
  (cellSet_bounded hVo hVc hVb x y hx hy n ht).closure

lemma cellSet_succ_subset (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V)
    (hy : y ∈ V) (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    cellSet hVo hVc x y hx hy (n+1) t ⊆ cellSet hVo hVc x y hx hy n t := by
  have hcell : cell hVo hVc x y hx hy (n+1) t < (pstages hVo hVc x y hx hy (n+1)).k :=
    cell_lt hVo hVc x y hx hy (n+1) ht
  rw [pstages_k_succ] at hcell
  have hdiv : cell hVo hVc x y hx hy (n+1) t /
        (pstages hVo hVc x y hx hy n).blockLen (peps V (n+1)) (peps_pos V (n+1)) =
      cell hVo hVc x y hx hy n t := by
    show gridIdx (pstages hVo hVc x y hx hy (n+1)).k t /
        (pstages hVo hVc x y hx hy n).blockLen (peps V (n+1)) (peps_pos V (n+1)) =
      gridIdx (pstages hVo hVc x y hx hy n).k t
    rw [pstages_k_succ]
    exact gridIdx_div _ _ (pstages hVo hVc x y hx hy n).hk
      ((pstages hVo hVc x y hx hy n).blockLen_pos (peps V (n+1)) (peps_pos V (n+1))) ht
  intro z hz
  rw [cellSet] at hz ⊢
  rw [pstages_succ] at hz
  have h2 := (pstages hVo hVc x y hx hy n).sub_refineU (peps V (n+1)) (peps_pos V (n+1)) hcell hz
  rwa [hdiv] at h2

lemma cellSet_anti (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V)
    (hy : y ∈ V) {i j : ℕ} (hij : i ≤ j) {t : ℝ} (ht : t ≤ 1) :
    cellSet hVo hVc x y hx hy j t ⊆ cellSet hVo hVc x y hx hy i t := by
  induction hij with
  | refl => exact Subset.rfl
  | step h ih => exact (cellSet_succ_subset hVo hVc x y hx hy _ ht).trans ih

lemma cellCl_anti (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V)
    (hy : y ∈ V) {i j : ℕ} (hij : i ≤ j) {t : ℝ} (ht : t ≤ 1) :
    cellCl hVo hVc x y hx hy j t ⊆ cellCl hVo hVc x y hx hy i t :=
  closure_mono (cellSet_anti hVo hVc x y hx hy hij ht)

lemma diam_cellCl (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V)
    (hy : y ∈ V) (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    Metric.diam (cellCl hVo hVc x y hx hy n t) < peps V n := by
  rw [cellCl, Metric.diam_closure]
  exact (pstages hVo hVc x y hx hy n).diam_U _ (cell_lt hVo hVc x y hx hy n ht)

lemma cellCl_unique (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) (t : ℝ) (ht : t ≤ 1) :
    ∃! z : X, z ∈ ⋂ n, cellCl hVo hVc x y hx hy n t := by
  refine complete_unique_mem_iInter_nested _
    (fun n => isClosed_closure)
    (fun n => cellCl_bounded hVo hVc hVb x y hx hy n ht)
    (fun i j hij => cellCl_anti hVo hVc x y hx hy hij ht)
    (fun n => cellCl_nonempty hVo hVc x y hx hy n ht) ?_
  intro ε hε
  have hev : ∀ᶠ n in Filter.atTop, peps V n < ε :=
    (peps_tendsto_zero V).eventually (isOpen_Iio.mem_nhds hε)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n, lt_trans (diam_cellCl hVo hVc x y hx hy n ht) hn⟩

noncomputable def fAt (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) (t : ℝ) (ht : t ≤ 1) : X :=
  (cellCl_unique hVo hVc hVb x y hx hy t ht).choose

lemma fAt_mem (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) (t : ℝ) (ht : t ≤ 1) (n : ℕ) :
    fAt hVo hVc hVb x y hx hy t ht ∈ cellCl hVo hVc x y hx hy n t :=
  Set.mem_iInter.mp (cellCl_unique hVo hVc hVb x y hx hy t ht).choose_spec.1 n

lemma cellSet_inter (hVo : IsOpen V) (hVc : IsConnected V) (x y : X) (hx : x ∈ V)
    (hy : y ∈ V) (n : ℕ) {s t : ℝ} (hs : s ≤ 1) (ht : t ≤ 1)
    (h : cell hVo hVc x y hx hy n s ≤ cell hVo hVc x y hx hy n t + 1)
    (h' : cell hVo hVc x y hx hy n t ≤ cell hVo hVc x y hx hy n s + 1) :
    (cellSet hVo hVc x y hx hy n s ∩ cellSet hVo hVc x y hx hy n t).Nonempty := by
  rcases Nat.lt_or_ge (cell hVo hVc x y hx hy n s) (cell hVo hVc x y hx hy n t) with hlt | hge
  · have hlt' : cell hVo hVc x y hx hy n s + 1 = cell hVo hVc x y hx hy n t := by omega
    have hk : cell hVo hVc x y hx hy n s + 1 < (pstages hVo hVc x y hx hy n).k := by
      rw [hlt']; exact cell_lt hVo hVc x y hx hy n ht
    obtain ⟨z, hz1, hz2⟩ := (pstages hVo hVc x y hx hy n).chain_U (cell hVo hVc x y hx hy n s) hk
    exact ⟨z, by rw [cellSet]; exact hz1, by rw [cellSet, ← hlt']; exact hz2⟩
  · rcases Nat.lt_or_ge (cell hVo hVc x y hx hy n t) (cell hVo hVc x y hx hy n s) with hlt | hge'
    · have hlt' : cell hVo hVc x y hx hy n t + 1 = cell hVo hVc x y hx hy n s := by omega
      have hk : cell hVo hVc x y hx hy n t + 1 < (pstages hVo hVc x y hx hy n).k := by
        rw [hlt']; exact cell_lt hVo hVc x y hx hy n hs
      obtain ⟨z, hz1, hz2⟩ := (pstages hVo hVc x y hx hy n).chain_U (cell hVo hVc x y hx hy n t) hk
      exact ⟨z, by rw [cellSet, ← hlt']; exact hz2, by rw [cellSet]; exact hz1⟩
    · have heq : cell hVo hVc x y hx hy n s = cell hVo hVc x y hx hy n t := le_antisymm hge' hge
      obtain ⟨z, hz⟩ := cellSet_nonempty hVo hVc x y hx hy n hs
      refine ⟨z, hz, ?_⟩
      rw [cellSet, ← heq, ← cellSet]
      exact hz

lemma dist_fAt_le (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) (n : ℕ) {s t : ℝ} (hs : s ≤ 1) (ht : t ≤ 1)
    (hst : |s - t| ≤ 1 / ((pstages hVo hVc x y hx hy n).k : ℝ)) :
    dist (fAt hVo hVc hVb x y hx hy s hs) (fAt hVo hVc hVb x y hx hy t ht) ≤ 2 * peps V n := by
  obtain ⟨h1, h2⟩ := abs_le.mp hst
  have ha : cell hVo hVc x y hx hy n s ≤ cell hVo hVc x y hx hy n t + 1 :=
    gridIdx_adj (pstages hVo hVc x y hx hy n).hk hs ht (by linarith)
  have hb : cell hVo hVc x y hx hy n t ≤ cell hVo hVc x y hx hy n s + 1 :=
    gridIdx_adj (pstages hVo hVc x y hx hy n).hk ht hs (by linarith)
  obtain ⟨z, hz1, hz2⟩ := cellSet_inter hVo hVc x y hx hy n hs ht ha hb
  have hmem1 : fAt hVo hVc hVb x y hx hy s hs ∈ cellCl hVo hVc x y hx hy n s :=
    fAt_mem hVo hVc hVb x y hx hy s hs n
  have hmem2 : fAt hVo hVc hVb x y hx hy t ht ∈ cellCl hVo hVc x y hx hy n t :=
    fAt_mem hVo hVc hVb x y hx hy t ht n
  have hbdd : Bornology.IsBounded (cellCl hVo hVc x y hx hy n s ∪ cellCl hVo hVc x y hx hy n t) :=
    (cellCl_bounded hVo hVc hVb x y hx hy n hs).union
      (cellCl_bounded hVo hVc hVb x y hx hy n ht)
  have hdist : dist (fAt hVo hVc hVb x y hx hy s hs) (fAt hVo hVc hVb x y hx hy t ht) ≤
      Metric.diam (cellCl hVo hVc x y hx hy n s ∪ cellCl hVo hVc x y hx hy n t) :=
    Metric.dist_le_diam_of_mem hbdd (Or.inl hmem1) (Or.inr hmem2)
  have hdiam : Metric.diam (cellCl hVo hVc x y hx hy n s ∪ cellCl hVo hVc x y hx hy n t)
      ≤ 2 * peps V n := by
    have hu := Metric.diam_union (subset_closure hz1) (subset_closure hz2)
    simp only [dist_self, add_zero] at hu
    rw [← cellCl, ← cellCl] at hu
    linarith [hu, diam_cellCl hVo hVc x y hx hy n hs, diam_cellCl hVo hVc x y hx hy n ht]
  linarith

end Limit

/-! ### The Final section -/

section Final

variable {V : Set X}

noncomputable def fI (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) (t : unitInterval) : X :=
  fAt hVo hVc hVb x y hx hy t.val t.property.2

lemma fAt_proof_irrel (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) (t : ℝ) (h1 h2 : t ≤ 1) :
    fAt hVo hVc hVb x y hx hy t h1 = fAt hVo hVc hVb x y hx hy t h2 := by
  have h : cellCl_unique hVo hVc hVb x y hx hy t h1 = cellCl_unique hVo hVc hVb x y hx hy t h2 :=
    Subsingleton.elim _ _
  unfold fAt
  rw [h]

lemma fAt_zero (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) :
    fAt hVo hVc hVb x y hx hy 0 (by norm_num : (0:ℝ) ≤ 1) = x := by
  apply dist_eq_zero.mp
  refine le_antisymm (le_of_forall_pos_lt_add fun δ hδ => ?_) dist_nonneg
  have hev : ∀ᶠ n in Filter.atTop, peps V n < δ :=
    (peps_tendsto_zero V).eventually (isOpen_Iio.mem_nhds hδ)
  obtain ⟨n, hn⟩ := hev.exists
  have h1 : fAt hVo hVc hVb x y hx hy 0 (by norm_num : (0:ℝ) ≤ 1) ∈
      cellCl hVo hVc x y hx hy n 0 := fAt_mem hVo hVc hVb x y hx hy 0 (by norm_num) n
  have h2 : x ∈ cellCl hVo hVc x y hx hy n 0 := by
    rw [cellCl, cellSet, cell_zero]
    refine subset_closure ?_
    have hm : (pstages hVo hVc x y hx hy n).x ∈ (pstages hVo hVc x y hx hy n).U 0 :=
      (pstages hVo hVc x y hx hy n).x_mem
    rwa [pstages_x hVo hVc x y hx hy n] at hm
  have hd := Metric.dist_le_diam_of_mem
    (cellCl_bounded hVo hVc hVb x y hx hy n (by norm_num : (0:ℝ) ≤ 1)) h1 h2
  have hd2 := diam_cellCl hVo hVc x y hx hy n (by norm_num : (0:ℝ) ≤ 1)
  linarith

lemma fAt_one (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) :
    fAt hVo hVc hVb x y hx hy 1 (by norm_num : (1:ℝ) ≤ 1) = y := by
  apply dist_eq_zero.mp
  refine le_antisymm (le_of_forall_pos_lt_add fun δ hδ => ?_) dist_nonneg
  have hev : ∀ᶠ n in Filter.atTop, peps V n < δ :=
    (peps_tendsto_zero V).eventually (isOpen_Iio.mem_nhds hδ)
  obtain ⟨n, hn⟩ := hev.exists
  have h1 : fAt hVo hVc hVb x y hx hy 1 (by norm_num : (1:ℝ) ≤ 1) ∈
      cellCl hVo hVc x y hx hy n 1 := fAt_mem hVo hVc hVb x y hx hy 1 (by norm_num) n
  have h2 : y ∈ cellCl hVo hVc x y hx hy n 1 := by
    rw [cellCl, cellSet, cell_one]
    refine subset_closure ?_
    have hm : (pstages hVo hVc x y hx hy n).y ∈
        (pstages hVo hVc x y hx hy n).U ((pstages hVo hVc x y hx hy n).k - 1) :=
      (pstages hVo hVc x y hx hy n).y_mem
    rwa [pstages_y hVo hVc x y hx hy n] at hm
  have hd := Metric.dist_le_diam_of_mem
    (cellCl_bounded hVo hVc hVb x y hx hy n (by norm_num : (1:ℝ) ≤ 1)) h1 h2
  have hd2 := diam_cellCl hVo hVc x y hx hy n (by norm_num : (1:ℝ) ≤ 1)
  linarith

lemma continuous_fI (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) : Continuous (fI hVo hVc hVb x y hx hy) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  have hev : ∀ᶠ n in Filter.atTop, 2 * peps V n < ε := by
    have h2 : Filter.Tendsto (fun n : ℕ => 2 * peps V n) Filter.atTop (nhds (2 * 0)) :=
      Filter.Tendsto.const_mul 2 (peps_tendsto_zero V)
    simpa using h2.eventually (isOpen_Iio.mem_nhds (by linarith : (2:ℝ) * 0 < ε))
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨1 / ((pstages hVo hVc x y hx hy n).k : ℝ),
    div_pos one_pos (by exact_mod_cast (pstages hVo hVc x y hx hy n).hk), fun a ha => ?_⟩
  have ha' : |a.val - b.val| ≤ 1 / ((pstages hVo hVc x y hx hy n).k : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq] at ha
    exact le_of_lt ha
  have h := dist_fAt_le hVo hVc hVb x y hx hy n a.property.2 b.property.2 ha'
  show dist (fAt hVo hVc hVb x y hx hy a.val a.property.2)
    (fAt hVo hVc hVb x y hx hy b.val b.property.2) < ε
  linarith

lemma fI_zero (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) : fI hVo hVc hVb x y hx hy 0 = x := by
  rw [fI]
  exact fAt_zero hVo hVc hVb x y hx hy

lemma fI_one (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (x y : X) (hx : x ∈ V) (hy : y ∈ V) : fI hVo hVc hVb x y hx hy 1 = y := by
  rw [fI]
  exact fAt_one hVo hVc hVb x y hx hy

end Final

/-- **A complete, locally connected metric space: paths inside the closure of a bounded connected
open set.**  If `V` is a bounded, open, connected subset of a complete locally connected metric
space and `x, y ∈ V`, then there is a path from `x` to `y` whose image is contained in the
closure of `V`. -/
theorem exists_path_mem_closure {V : Set X} (hVo : IsOpen V) (hVc : IsConnected V)
    (hVb : Bornology.IsBounded V) {x y : X} (hx : x ∈ V) (hy : y ∈ V) :
    ∃ γ : Path x y, ∀ t, γ t ∈ closure V := by
  refine ⟨⟨⟨fI hVo hVc hVb x y hx hy, continuous_fI hVo hVc hVb x y hx hy⟩,
      fI_zero hVo hVc hVb x y hx hy, fI_one hVo hVc hVb x y hx hy⟩, fun t => ?_⟩
  show fAt hVo hVc hVb x y hx hy t.val t.property.2 ∈ closure V
  exact closure_mono (cellSet_subset_V hVo hVc x y hx hy 0 t.property.2)
    (fAt_mem hVo hVc hVb x y hx hy t.val t.property.2 0)

/-- In a complete, locally connected metric space, the path component of a point in an open set
is open. -/
lemma isOpen_pathComponentIn {U : Set X} (hUo : IsOpen U) (x : X) :
    IsOpen (pathComponentIn U x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hUo y (pathComponentIn_subset hy)
  obtain ⟨V, hVo, hVc, hyV, hVsub, _⟩ :=
    exists_isConnected_isOpen_subset (W := Metric.ball y (ρ/2)) (Metric.isOpen_ball)
      (Metric.mem_ball_self (by linarith)) (by linarith)
  have hVb : Bornology.IsBounded V := Metric.isBounded_ball.subset hVsub
  have hclV : closure V ⊆ U := by
    refine (closure_mono hVsub).trans ?_
    refine Metric.closure_ball_subset_closedBall.trans ?_
    intro z hz
    exact hρU (by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
  have hVS : V ⊆ pathComponentIn U x := by
    intro z hzV
    obtain ⟨γ, hγ⟩ := exists_path_mem_closure hVo hVc hVb hyV hzV
    exact hy.trans ⟨γ, fun t => hclV (hγ t)⟩
  exact Filter.mem_of_superset (hVo.mem_nhds hyV) hVS

/-- **Mazurkiewicz–Moore–Menger theorem.** A complete, locally connected metric space is locally
path-connected. -/
theorem locallyPathConnectedSpace_of_complete_locallyConnected (X : Type*) [MetricSpace X]
    [CompleteSpace X] [LocallyConnectedSpace X] : LocallyPathConnectedSpace X := by
  refine ⟨fun x => ?_⟩
  rw [Filter.hasBasis_iff]
  intro t
  constructor
  · intro ht
    rw [_root_.mem_nhds_iff] at ht
    obtain ⟨U, hUt, hUo, hxU⟩ := ht
    have hxS : x ∈ pathComponentIn U x := mem_pathComponentIn_self hxU
    have hSU : pathComponentIn U x ⊆ U := pathComponentIn_subset
    have hSopen : IsOpen (pathComponentIn U x) := isOpen_pathComponentIn hUo x
    refine ⟨pathComponentIn U x, ⟨hSopen.mem_nhds hxS, ?_⟩, hSU.trans hUt⟩
    refine isPathConnected_iff.mpr ⟨⟨x, hxS⟩, fun y hy z hz => ?_⟩
    obtain ⟨γ, hγ⟩ := hy
    obtain ⟨δ, hδ⟩ := hz
    have hrange : Set.range (γ.symm.trans δ) ⊆ pathComponentIn U x := by
      intro w hw
      rw [Path.trans_range, Set.mem_union, Path.range_symm] at hw
      rcases hw with hw | hw
      · obtain ⟨s, rfl⟩ := hw
        exact ⟨(γ.subpath 0 s).cast (Path.source γ).symm rfl, fun u => hγ _⟩
      · obtain ⟨s, rfl⟩ := hw
        exact ⟨(δ.subpath 0 s).cast (Path.source δ).symm rfl, fun u => hδ _⟩
    exact ⟨γ.symm.trans δ, fun w => hrange (Set.mem_range_self w)⟩
  · rintro ⟨s, ⟨hs, _⟩, hst⟩
    exact Filter.mem_of_superset hs hst


/-! ### Extending a logarithm from a compact set to a neighbourhood -/

/-- **A continuous logarithm on a compact set extends to a logarithm on a neighbourhood.**

If `C ⊆ ℂ` is compact, `0 ∉ C`, and the identity of `C` has a continuous logarithm `F`
(`exp (F x) = x` for all `x ∈ C`), then the identity has a continuous logarithm on an open
neighbourhood of `C` avoiding `0`.

Proof: extend `F` to a continuous `G : ℂ → ℂ` (Tietze), and correct it: the map
`φ w := w / exp (G w)` is continuous and equals `1` on `C`, so on the open neighbourhood
`W₀ := {w | ‖φ w - 1‖ < 1}` of `C` the principal logarithm `log (φ w)` is continuous, and
`g w := G w + log (φ w)` satisfies `exp (g w) = w`. -/
theorem exists_log_on_neighborhood_of_log {C : Set ℂ} (hC : IsCompact C) (h0 : (0 : ℂ) ∉ C)
    (F : C(↥C, ℂ)) (hF : ∀ x : ↥C, Complex.exp (F x) = (x : ℂ)) :
    ∃ W : Set ℂ, IsOpen W ∧ C ⊆ W ∧ (0 : ℂ) ∉ W ∧
      ∃ g : ℂ → ℂ, ContinuousOn g W ∧ ∀ w ∈ W, Complex.exp (g w) = w := by
  obtain ⟨G, hG⟩ := F.exists_restrict_eq hC.isClosed
  have hGC : ∀ x : ↥C, G (x : ℂ) = F x := by
    intro x
    have h := congrArg (fun m : C(↥C, ℂ) => m x) hG
    simpa [ContinuousMap.restrict_apply] using h
  set φ : ℂ → ℂ := fun w => w / Complex.exp (G w) with hφdef
  have hφc : Continuous φ := by
    rw [hφdef]
    exact continuous_id.div (Complex.continuous_exp.comp G.continuous)
      (fun w => Complex.exp_ne_zero (G w))
  have hφC : ∀ x : ↥C, φ x = 1 := by
    intro x
    have hxne : (x : ℂ) ≠ 0 := fun h => h0 (h ▸ x.2)
    rw [hφdef]
    simp only [hGC x, hF x]
    exact div_self hxne
  set W₀ : Set ℂ := {w | ‖φ w - 1‖ < 1} with hW₀def
  have hW₀open : IsOpen W₀ :=
    isOpen_lt (continuous_norm.comp (hφc.sub continuous_const)) continuous_const
  have hCW₀ : C ⊆ W₀ := by
    intro x hx
    rw [hW₀def]
    simp only [Set.mem_setOf_eq]
    have : φ x = 1 := hφC ⟨x, hx⟩
    rw [this]; norm_num
  have hre : ∀ w ∈ W₀, 0 < (φ w).re := by
    intro w hw
    rw [hW₀def] at hw
    simp only [Set.mem_setOf_eq] at hw
    have h1 : |(φ w - 1).re| ≤ ‖φ w - 1‖ := Complex.abs_re_le_norm _
    have h2 : (φ w - 1).re = (φ w).re - 1 := by simp
    rw [h2] at h1
    have h3 : |(φ w).re - 1| < 1 := lt_of_le_of_lt h1 hw
    rw [abs_lt] at h3
    linarith [h3.1]
  have hslit : ∀ w ∈ W₀, φ w ∈ Complex.slitPlane := fun w hw => by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (hre w hw)
  have hφne : ∀ w ∈ W₀, φ w ≠ 0 := fun w hw h => by
    have h1 := hre w hw
    rw [h] at h1
    simp at h1
  have hlogcont : ContinuousOn (fun w => Complex.log (φ w)) W₀ := fun w hw =>
    hφc.continuousAt.continuousWithinAt.clog (hslit w hw)
  refine ⟨W₀ ∩ {0}ᶜ, hW₀open.inter isClosed_singleton.isOpen_compl,
    fun x hx => ⟨hCW₀ hx, fun h => h0 (h ▸ hx)⟩, fun h => h.2 rfl, ?_⟩
  refine ⟨fun w => G w + Complex.log (φ w), ?_, ?_⟩
  · exact G.continuous.continuousOn.add (hlogcont.mono Set.inter_subset_left)
  · intro w hw
    have hw₀ : w ∈ W₀ := hw.1
    have h1 : Complex.exp (Complex.log (φ w)) = φ w := Complex.exp_log (hφne w hw₀)
    rw [Complex.exp_add, h1, hφdef]
    exact mul_div_cancel₀ w (Complex.exp_ne_zero (G w))

/-! ### The standard parametrization of the circle and the values of `loopCircleMap` -/

/-- Every point of the circle is of the form `Circle.exp (2 * π * s)` with `s : unitInterval`. -/
lemma exists_unitInterval_exp_eq (z : Circle) :
    ∃ s : unitInterval, Circle.exp (2 * Real.pi * (s : ℝ)) = z := by
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective z
  set f : ℝ := Int.fract (θ / (2 * Real.pi)) with hf
  have hf0 : 0 ≤ f := Int.fract_nonneg _
  have hf1 : f < 1 := Int.fract_lt_one _
  set k : ℤ := ⌊θ / (2 * Real.pi)⌋ with hk
  refine ⟨⟨f, hf0, le_of_lt hf1⟩, ?_⟩
  rw [← hθ, Circle.exp_eq_exp]
  refine ⟨-k, ?_⟩
  have h1 : f + (k : ℝ) = θ / (2 * Real.pi) := Int.fract_add_floor _
  have h2 : θ = 2 * Real.pi * f + 2 * Real.pi * (k : ℝ) := by
    have h3 := congrArg (fun x : ℝ => x * (2 * Real.pi)) h1
    rw [div_mul_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)] at h3
    linarith [h3]
  show 2 * Real.pi * f = θ + ((-k : ℤ) : ℝ) * (2 * Real.pi)
  rw [h2]
  push_cast
  ring

/-- The values of `loopCircleMap p` are values of `p`. -/
lemma exists_eq_loopCircleMap {Y : Type*} [TopologicalSpace Y] {y : Y} (p : Path y y)
    (z : Circle) : ∃ s : unitInterval, loopCircleMap p z = p s := by
  obtain ⟨s, hs⟩ := exists_unitInterval_exp_eq z
  exact ⟨s, by rw [← hs, circleMap_apply]⟩

/-! ### A logarithm on a neighbourhood forbids a bounded complementary component -/

/-- **If the identity has a continuous logarithm on an open neighbourhood `W` of a compact set `E`
avoiding `0`, then `0` can be joined to infinity inside `Eᶜ`** (the component of `0` in `Eᶜ` is
unbounded).

This is the contrapositive form of the classical statement that a compact set whose complement
has a bounded component around `0` admits an essential loop in that complement
(`Commons.Topology.Plane.essential_loop_of_bounded_component`): a logarithm on a neighbourhood
turns such an essential loop into a null-homotopy avoiding `0`. -/
lemma component_unbounded_of_log_on_neighborhood {E W : Set ℂ} (hE : IsCompact E) (hW : IsOpen W)
    (hEW : E ⊆ W) (h0 : (0 : ℂ) ∉ W) {g : ℂ → ℂ} (hg : ContinuousOn g W)
    (hlog : ∀ z ∈ W, Complex.exp (g z) = z) :
    ∀ R : ℝ, ∃ z : ℂ, R < ‖z‖ ∧ z ∈ connectedComponentIn (Eᶜ) (0 : ℂ) := by
  by_contra hcon
  rw [not_forall] at hcon
  obtain ⟨R, hR⟩ := hcon
  have hbddE : Bornology.IsBounded (connectedComponentIn (Eᶜ) (0 : ℂ)) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨R, fun z hz => le_of_not_gt (fun hlt => hR ⟨z, hlt, hz⟩)⟩
  set K : Set ℂ := Wᶜ with hKdef
  have hKclosed : IsClosed K := hW.isClosed_compl
  have h0K : (0 : ℂ) ∈ K := by simp [hKdef, h0]
  have hKsubE : K ⊆ Eᶜ := by
    intro z hz
    simp only [hKdef, mem_compl_iff] at hz ⊢
    intro hzE
    exact hz (hEW hzE)
  have hbddK : Bornology.IsBounded (connectedComponentIn K (0 : ℂ)) :=
    hbddE.subset (connectedComponentIn_mono 0 hKsubE)
  obtain ⟨γ, hγK, hγess⟩ :=
    Commons.Topology.Plane.essential_loop_of_bounded_component hKclosed h0K hbddK
  have hγW : ∀ t, (γ t : ℂ) ∈ W := by
    intro t
    have := hγK t
    simpa [hKdef] using this
  apply hγess
  have hcontγ : Continuous (fun t : Circle => g (γ t)) :=
    hg.comp_continuous (continuous_subtype_val.comp γ.continuous) hγW
  let F : unitInterval × Circle → {z : ℂ // z ≠ 0} := fun p =>
    ⟨Complex.exp (((1 : ℂ) - ((p.1 : ℝ) : ℂ)) * g (γ p.2) + ((p.1 : ℝ) : ℂ) * g (γ 1)),
      Complex.exp_ne_zero _⟩
  have hFcont : Continuous F := by
    refine Continuous.subtype_mk ?_ _
    apply Complex.continuous_exp.comp
    have hs : Continuous (fun p : unitInterval × Circle => ((p.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
    have hgγ : Continuous (fun p : unitInterval × Circle => g (γ p.2)) :=
      hcontγ.comp continuous_snd
    exact ((Continuous.sub continuous_const hs).mul hgγ).add (hs.mul continuous_const)
  refine ⟨γ 1, ⟨⟨F, hFcont⟩, ?_, ?_⟩⟩
  · intro t
    change F ((0 : unitInterval), t) = γ t
    apply Subtype.ext
    show Complex.exp (((1 : ℂ) - (((0 : unitInterval) : ℝ) : ℂ)) * g (γ t)
      + (((0 : unitInterval) : ℝ) : ℂ) * g (γ 1)) = (γ t : ℂ)
    norm_num
    exact hlog (γ t) (hγW t)
  · intro t
    change F ((1 : unitInterval), t) = γ 1
    apply Subtype.ext
    show Complex.exp (((1 : ℂ) - (((1 : unitInterval) : ℝ) : ℂ)) * g (γ t)
      + (((1 : unitInterval) : ℝ) : ℂ) * g (γ 1)) = (γ 1 : ℂ)
    norm_num
    exact hlog (γ 1) (hγW 1)

/-! ### From free null-homotopies of circle maps to based null-homotopies of loops -/

/-- The inclusion of `C` into the punctured plane `ℂ \ {0}` (valid because `0 ∉ C`). -/
def punctIncl {C : Set ℂ} (h0 : (0 : ℂ) ∉ C) : C(↥C, {z : ℂ // z ≠ 0}) :=
  ⟨fun x => ⟨(x : ℂ), fun hh => h0 (hh ▸ x.2)⟩, Continuous.subtype_mk continuous_subtype_val _⟩

/-- **A loop in `C` is null-homotopic in `ℂ \ {0}` as soon as every circle map with values in `C`
is free-null-homotopic avoiding `0`.** -/
lemma loop_map_homotopic_refl {C : Set ℂ} (h0 : (0 : ℂ) ∉ C)
    (h : ∀ γ : C(Circle, ℂ), (∀ t, γ t ∈ C) → ∀ t₀ : Circle,
      ∃ H : C(Circle × Set.Icc (0 : ℝ) 1, ℂ),
        (∀ t, H (t, (0 : Set.Icc (0 : ℝ) 1)) = γ t) ∧
        (∀ t, H (t, (1 : Set.Icc (0 : ℝ) 1)) = γ t₀) ∧
        ∀ p : Circle × Set.Icc (0 : ℝ) 1, H p ≠ (0 : ℂ))
    {x : ↥C} (L : Path x x) :
    (L.map (punctIncl h0).continuous).Homotopic (Path.refl _) := by
  let Lf : Path ((punctIncl h0) x) ((punctIncl h0) x) := L.map (punctIncl h0).continuous
  have hLf_coe : ∀ t : unitInterval, ((Lf t : {z : ℂ // z ≠ 0}) : ℂ) = (L t : ℂ) := by
    intro t
    have h1 : ((L.map (punctIncl h0).continuous : unitInterval → {z : ℂ // z ≠ 0}) t)
        = (punctIncl h0) (L t) := congr_fun (Path.map_coe L (punctIncl h0).continuous) t
    change (((L.map (punctIncl h0).continuous : unitInterval → {z : ℂ // z ≠ 0}) t :
      {z : ℂ // z ≠ 0}) : ℂ) = (L t : ℂ)
    rw [h1]
    rfl
  have hnull : (loopCircleMap Lf).Nullhomotopic := by
    let γc : C(Circle, ℂ) :=
      ⟨fun z => (((loopCircleMap Lf) z : {z : ℂ // z ≠ 0}) : ℂ),
        continuous_subtype_val.comp (loopCircleMap Lf).continuous⟩
    have hval : ∀ z, γc z ∈ C := by
      intro z
      obtain ⟨s, hs⟩ := exists_eq_loopCircleMap Lf z
      have hcoe : γc z = (((Lf s : {z : ℂ // z ≠ 0}) : ℂ)) := by
        show (((loopCircleMap Lf) z : {z : ℂ // z ≠ 0}) : ℂ) = _
        rw [hs]
      rw [hcoe, hLf_coe s]
      exact (L s).2
    obtain ⟨H, hH0, hH1, hHne⟩ := h γc hval 1
    refine ⟨loopCircleMap Lf 1, ?_⟩
    refine ⟨⟨fun p : unitInterval × Circle => ⟨H (p.2, p.1), hHne _⟩, ?_⟩, ?_, ?_⟩
    · exact Continuous.subtype_mk (H.continuous.comp (continuous_snd.prodMk continuous_fst)) _
    · intro z
      apply Subtype.ext
      change H (z, (0 : Set.Icc (0 : ℝ) 1)) = (((loopCircleMap Lf) z : {z : ℂ // z ≠ 0}) : ℂ)
      rw [hH0 z]
      rfl
    · intro z
      apply Subtype.ext
      change H (z, (1 : Set.Icc (0 : ℝ) 1)) = (((loopCircleMap Lf) 1 : {z : ℂ // z ≠ 0}) : ℂ)
      rw [hH1 z]
      rfl
  exact homotopic_refl_of_nullhomotopic_circleMap Lf hnull

/-! ### Existence of a continuous logarithm from the vanishing of the monodromy -/

/-- **Lifting criterion for the exponential covering.**  If every loop in `C` (as a circle map with
values in `C`) is null-homotopic avoiding `0`, and `↥C` is path-connected and locally
path-connected, then the identity of `C` has a continuous logarithm. -/
theorem exists_log_of_loops_nullhomotopic {C : Set ℂ} (hC : IsCompact C) (h0 : (0 : ℂ) ∉ C)
    [PathConnectedSpace ↥C] [LocallyPathConnectedSpace ↥C]
    (h : ∀ γ : C(Circle, ℂ), (∀ t, γ t ∈ C) → ∀ t₀ : Circle,
      ∃ H : C(Circle × Set.Icc (0 : ℝ) 1, ℂ),
        (∀ t, H (t, (0 : Set.Icc (0 : ℝ) 1)) = γ t) ∧
        (∀ t, H (t, (1 : Set.Icc (0 : ℝ) 1)) = γ t₀) ∧
        ∀ p : Circle × Set.Icc (0 : ℝ) 1, H p ≠ (0 : ℂ)) :
    ∃ F : C(↥C, ℂ), ∀ x : ↥C, Complex.exp (F x) = (x : ℂ) := by
  classical
  have _ := hC
  let a₀ : ↥C := Classical.choice (inferInstance : Nonempty ↥C)
  let f : C(↥C, {z : ℂ // z ≠ 0}) := punctIncl h0
  let p : ℂ → {z : ℂ // z ≠ 0} := fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩
  have hp : IsCoveringMap p := Complex.isCoveringMap_exp
  have hloc : IsLocalHomeomorph p := hp.isLocalHomeomorph
  let e₀ : ℂ := Complex.log (a₀ : ℂ)
  have he : p e₀ = f a₀ := by
    apply Subtype.ext
    show Complex.exp (Complex.log ((a₀ : ℂ))) = (a₀ : ℂ)
    exact Complex.exp_log (fun hh => h0 (hh ▸ a₀.2))
  have hex : ∀ γ : C(unitInterval, ↥C), γ 0 = a₀ →
      ∃ Γ : C(unitInterval, ℂ), Γ 0 = e₀ ∧ p ∘ Γ = f.comp γ := by
    intro γ hγ0
    have hpt : (f.comp γ) 0 = p e₀ := by
      rw [ContinuousMap.comp_apply, hγ0]
      exact he.symm
    obtain ⟨Γ, hΓl, hΓ0⟩ := hp.exists_path_lifts (f.comp γ) e₀ hpt
    exact ⟨Γ, hΓ0, hΓl⟩
  have huniq : ∀ γ γ' : C(unitInterval, ↥C), ∀ Γ Γ' : C(unitInterval, ℂ),
      γ 0 = a₀ → γ' 0 = a₀ → Γ 0 = e₀ → Γ' 0 = e₀ →
      p ∘ Γ = f.comp γ → p ∘ Γ' = f.comp γ' → γ 1 = γ' 1 → Γ 1 = Γ' 1 := by
    intro γ γ' Γ Γ' hγ0 hγ'0 hΓ0 hΓ'0 hl hl' hγ1
    have hc : Continuous (fun x : ↥C => (punctIncl h0) x) := (punctIncl h0).continuous
    -- the two paths from `a₀` to the common endpoint
    let γp : Path a₀ (γ 1) := ⟨γ, hγ0, rfl⟩
    let γp' : Path a₀ (γ 1) := ⟨γ', hγ'0, hγ1.symm⟩
    have hp0 : (punctIncl h0) a₀ = p e₀ := he.symm
    have hloop := loop_map_homotopic_refl h0 h (γp.trans γp'.symm)
    have key : ((γp.map hc).trans ((γp'.map hc).symm)).Homotopic (Path.refl _) := by
      simpa only [Path.map_trans, Path.map_symm] using hloop
    have hAB : (γp.map hc).Homotopic (γp'.map hc) := by
      let A : Path ((punctIncl h0) a₀) ((punctIncl h0) (γ 1)) := γp.map hc
      let B : Path ((punctIncl h0) a₀) ((punctIncl h0) (γ 1)) := γp'.map hc
      have h1 : A.Homotopic (A.trans (Path.refl _)) := (Path.Homotopic.trans_refl A).symm
      have h2 : (A.trans (Path.refl _)).Homotopic (A.trans (B.symm.trans B)) :=
        Path.Homotopic.hcomp (Path.Homotopic.refl A) (Path.Homotopic.symm_trans B).symm
      have h3 : (A.trans (B.symm.trans B)).Homotopic ((A.trans B.symm).trans B) :=
        (Path.Homotopic.trans_assoc A B.symm B).symm
      have h4 : ((A.trans B.symm).trans B).Homotopic ((Path.refl _).trans B) :=
        Path.Homotopic.hcomp key (Path.Homotopic.refl B)
      have h5 : ((Path.refl _).trans B).Homotopic B := Path.Homotopic.refl_trans B
      exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
    -- convert to the `ContinuousMap` formulation
    have hγeq : (γp.map hc : C(unitInterval, {z : ℂ // z ≠ 0})) = f.comp γ := by
      ext t
      rfl
    have hγ'eq : (γp'.map hc : C(unitInterval, {z : ℂ // z ≠ 0})) = f.comp γ' := by
      ext t
      rfl
    have hABrel : (f.comp γ).HomotopicRel (f.comp γ') {0,1} := by
      rw [← hγeq, ← hγ'eq]
      exact hAB
    -- identify the two lifts with the `liftPath`s
    have hA₀ : (f.comp γ) 0 = p e₀ := by
      rw [ContinuousMap.comp_apply, hγ0]; exact he.symm
    have hA'₀ : (f.comp γ') 0 = p e₀ := by
      rw [ContinuousMap.comp_apply, hγ'0]; exact he.symm
    have hΓ : Γ = hp.liftPath (f.comp γ) e₀ hA₀ :=
      (hp.eq_liftPath_iff' (Γ := Γ) (γ := f.comp γ) (e := e₀) (γ_0 := hA₀)).mpr ⟨hl, hΓ0⟩
    have hΓ' : Γ' = hp.liftPath (f.comp γ') e₀ hA'₀ :=
      (hp.eq_liftPath_iff' (Γ := Γ') (γ := f.comp γ') (e := e₀) (γ_0 := hA'₀)).mpr ⟨hl', hΓ'0⟩
    have hsame := hp.liftPath_apply_one_eq_of_homotopicRel hABrel e₀ hA₀ hA'₀
    rw [hΓ, hΓ']
    exact hsame
  obtain ⟨F, ⟨-, hFp⟩, -⟩ := hloc.existsUnique_continuousMap_lifts f a₀ e₀ he hex huniq
  refine ⟨F, fun x => ?_⟩
  have hx := congrArg Subtype.val (congrFun hFp x)
  simpa [f, p, punctIncl] using hx

/-! ### The zero-basepoint version -/

/-- A closed subset of `ℂ` is complete (for the Peano/MMM theorem). -/
lemma locallyPathConnectedSpace_of_compact_locallyConnected {C : Set ℂ} (hC : IsCompact C)
    (hlc : LocallyConnectedSpace ↥C) : LocallyPathConnectedSpace ↥C := by
  haveI : CompleteSpace ↥C := (completeSpace_coe_iff_isComplete (s := C)).mpr hC.isClosed.isComplete
  exact locallyPathConnectedSpace_of_complete_locallyConnected ↥C

/-- **A Peano continuum separating `0` from infinity carries an essential loop (basepoint `0`).** -/
theorem peano_essential_loop_of_bounded_complement_zero {C : Set ℂ} (hC : IsCompact C)
    (hconn : IsPreconnected C) (hlc : LocallyConnectedSpace ↥C) (h0 : (0 : ℂ) ∉ C)
    (hbdd : Bornology.IsBounded (connectedComponentIn Cᶜ 0)) :
    ∃ γ : C(Circle, ℂ), (∀ t, γ t ∈ C) ∧ ∃ t₀ : Circle,
      ¬ ∃ H : C(Circle × Set.Icc (0 : ℝ) 1, ℂ),
        (∀ t, H (t, (0 : Set.Icc (0 : ℝ) 1)) = γ t) ∧
        (∀ t, H (t, (1 : Set.Icc (0 : ℝ) 1)) = γ t₀) ∧
        ∀ p : Circle × Set.Icc (0 : ℝ) 1, H p ≠ (0 : ℂ) := by
  by_contra hcon
  push_neg at hcon
  have hne : C.Nonempty := by
    rcases C.eq_empty_or_nonempty with rfl | hne
    · exfalso
      rw [compl_empty, connectedComponentIn_univ,
        PreconnectedSpace.connectedComponent_eq_univ] at hbdd
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hbdd
      have h1 := hM (((max M 0 + 1 : ℝ)) : ℂ) (mem_univ _)
      simp only [Complex.norm_real, Real.norm_eq_abs] at h1
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ max M 0 + 1)] at h1
      linarith [le_max_left M 0]
    · exact hne
  haveI : PathConnectedSpace ↥C := paeno_continuum_pathConnected hC ⟨hne, hconn⟩ hlc
  haveI : LocallyPathConnectedSpace ↥C := locallyPathConnectedSpace_of_compact_locallyConnected hC hlc
  obtain ⟨F, hF⟩ := exists_log_of_loops_nullhomotopic hC h0 hcon
  obtain ⟨W, hWopen, hCW, h0W, g, hg, hlog⟩ := exists_log_on_neighborhood_of_log hC h0 F hF
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hbdd
  obtain ⟨w, hw, hwmem⟩ := component_unbounded_of_log_on_neighborhood hC hWopen hCW h0W hg hlog M
  exact absurd (hM w hwmem) (not_le.mpr hw)

end LocalPeano

open LocalPeano

/-- **Classical: a Peano continuum separating a point from infinity carries an essential loop.**

Let `C ⊆ ℂ` be a Peano continuum and `z ∉ C` a point whose connected component in `Cᶜ` is
bounded.  Then there is a loop `γ : Circle → C` which is not null-homotopic while avoiding `z`:
there is `t₀` such that no homotopy from `γ` to the constant loop at `γ t₀` stays away from `z`. -/
theorem peano_essential_loop_of_bounded_complement {C : Set ℂ} (hC : IsCompact C)
    (hconn : IsPreconnected C) (hlc : LocallyConnectedSpace ↥C) {z : ℂ} (hz : z ∈ Cᶜ)
    (hbdd : Bornology.IsBounded (connectedComponentIn Cᶜ z)) :
    ∃ γ : C(Circle, ℂ), (∀ t, γ t ∈ C) ∧ ∃ t₀ : Circle,
      ¬ ∃ H : C(Circle × Set.Icc (0 : ℝ) 1, ℂ),
        (∀ t, H (t, (0 : Set.Icc (0 : ℝ) 1)) = γ t) ∧
        (∀ t, H (t, (1 : Set.Icc (0 : ℝ) 1)) = γ t₀) ∧
        ∀ p : Circle × Set.Icc (0 : ℝ) 1, H p ≠ z := by
  set e : ℂ ≃ₜ ℂ := Homeomorph.subRight z with he
  set C' : Set ℂ := e '' C with hC'def
  have hez : e z = 0 := by simp [e]
  have h0' : (0 : ℂ) ∉ C' := by
    rintro ⟨c, hc, hcc⟩
    have hcz : c = z := by
      have h2 : e c = c - z := by
        rw [he]
        exact congrFun (Homeomorph.coe_subRight z) c
      rw [h2] at hcc
      exact sub_eq_zero.mp hcc
    exact hz (hcz ▸ hc)
  have hC'cpt : IsCompact C' := hC.image e.continuous
  have hC'pre : IsPreconnected C' := hconn.image e e.continuous.continuousOn
  have hC'lc : LocallyConnectedSpace ↥C' :=
    Homeomorph.locallyConnectedSpace ((Homeomorph.image e C).symm)
  have hcc : e '' connectedComponentIn Cᶜ z = connectedComponentIn (C')ᶜ 0 := by
    have h1 := Homeomorph.image_connectedComponentIn (h := e) (s := Cᶜ) (x := z) hz
    have h2 : e '' Cᶜ = (C')ᶜ := by
      rw [hC'def, Set.image_compl_eq e.bijective]
    rw [h2, hez] at h1
    exact h1
  have hbdd' : Bornology.IsBounded (connectedComponentIn (C')ᶜ 0) := by
    rw [← hcc]
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hbdd
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M + ‖z‖, ?_⟩
    rintro w ⟨u, hu, rfl⟩
    have h1 : ‖u‖ ≤ M := hM u hu
    have h2 : e u = u - z := rfl
    rw [h2]
    calc ‖u - z‖ ≤ ‖u‖ + ‖z‖ := norm_sub_le u z
      _ ≤ M + ‖z‖ := by linarith
  obtain ⟨γ, hγmem, t₀, ht₀⟩ :=
    peano_essential_loop_of_bounded_complement_zero hC'cpt hC'pre hC'lc h0' hbdd'
  refine ⟨⟨fun t => γ t + z, γ.continuous.add continuous_const⟩, fun t => ?_, t₀, ?_⟩
  · obtain ⟨c, hc, hcc'⟩ := hγmem t
    have hcz : c = γ t + z := by
      have h2 : e c = c - z := by
        rw [he]
        exact congrFun (Homeomorph.coe_subRight z) c
      rw [h2] at hcc'
      rw [← hcc']
      ring
    show γ t + z ∈ C
    rw [← hcz]
    exact hc
  · rintro ⟨H, hH0, hH1, hHne⟩
    refine ht₀ ⟨⟨fun p => H p - z, H.continuous.sub continuous_const⟩, ?_, ?_, ?_⟩
    · intro t
      change H (t, (0 : Set.Icc (0:ℝ) 1)) - z = γ t
      rw [hH0 t]
      simp only [ContinuousMap.coe_mk]
      ring
    · intro t
      change H (t, (1 : Set.Icc (0:ℝ) 1)) - z = γ t₀
      rw [hH1 t]
      simp only [ContinuousMap.coe_mk]
      ring
    · intro p
      exact sub_ne_zero.mpr (hHne p)

end Commons.Topology.Plane
