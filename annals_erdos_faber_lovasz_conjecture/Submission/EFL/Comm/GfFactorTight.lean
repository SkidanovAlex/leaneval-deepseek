import Submission.EFL.Comm.BarrierCountGF
import Submission.EFL.Comm.AltWalkFlipDegree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Zify

/-!
# Lovász's tight `(h, h+1)`-factor theorem (the `g < f` case in the `g = h`, `f = h+1` form)

**Theorem** (`gf_factor_tight`).  Let `G` be a finite simple graph and `h : V → ℕ` with
`h v + 1 ≤ d_G(v)` for all `v`.  If the Lovász condition

  `e_G(S,T) ≤ ∑_{s∈S} (h s + 1) + ∑_{t∈T} (d_G(t) − h t)`

holds for all disjoint `S, T ⊆ V`, then `G` has a spanning subgraph `R` with
`h v ≤ d_R(v) ≤ h v + 1` for every `v`.

This is the special case `g = h`, `f = h + 1` of Lovász's `(g,f)`-factor theorem
(*Subgraphs with prescribed valencies*, Theorem 7.3), a key input in the proof of the
Erdős–Faber–Lovász conjecture.

## Proof strategy

Minimise the *defect* `dfct R = ∑_v max 0 (h v − d_R v)` over all subgraphs `R ≤ G` with
`d_R ≤ h+1`.  If the defect is `0` we are done.  Otherwise let `D = {v : d_R v < h v} ≠ ∅` and
let `Xw` / `Yw` be the vertices reachable from `D` by even- and odd-length *edge-simple alternating
walks* (`IsEW`: the `i`-th edge lies in `R` iff `i` is odd).  Flipping the edges of such a walk
(`alt_walk_flip_degree`: the flipped degrees change by `+1` at the start and by `−(−1)^n` at the
end) shows

* every `y ∈ Yw` is *saturated*: `d_R(y) = h y + 1`;
* no `x ∈ Xw` is saturated: `d_R(x) ≤ h x`;
* hence `Xw ∩ Yw = ∅`;
* and the reachable sets are closed: `R`-neighbours of `Yw` lie in `Xw`, other `G`-neighbours of
  `Xw` lie in `Yw`.

With `X = Xw`, `Y = Yw`, `barrier_count_gf` gives the exact identity
`e_G(Y,X) = ∑_Y (h+1) + ∑_X (d_G − h) + ∑_X (h − d_R)`,
while Lovász's condition bounds `e_G(Y,X) ≤ ∑_Y (h+1) + ∑_X (d_G − h)`.  The last sum is `≤ 0`,
but since `D ⊆ Xw` it equals the defect `dfct R > 0` — a contradiction.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped BigOperators

namespace Commons.Combinatorics.Factor

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def sdeg (G : SimpleGraph V) (R : G.Subgraph) (v : V) : ℕ :=
  Nat.card {w : V // R.Adj v w}

def Dset (G : SimpleGraph V) (h : V → ℕ) (R : G.Subgraph) : Set V :=
  {v | sdeg G R v < h v}

def lastV {n : ℕ} (v : Fin (n+1) → V) : V := v ⟨n, Nat.lt_succ_self n⟩

def IsEW (G : SimpleGraph V) (h : V → ℕ) (R : G.Subgraph) (n : ℕ) (v : Fin (n+1) → V) : Prop :=
  v 0 ∈ Dset G h R ∧
    (∀ i : Fin n, G.Adj (v i.castSucc) (v i.succ)) ∧
    (∀ i : Fin n, R.Adj (v i.castSucc) (v i.succ) ↔ Odd i.val) ∧
    Function.Injective (fun i : Fin n => s(v i.castSucc, v i.succ))

def Xw (G : SimpleGraph V) (h : V → ℕ) (R : G.Subgraph) : Set V :=
  {v | ∃ n, Even n ∧ ∃ w : Fin (n+1) → V, IsEW G h R n w ∧ lastV w = v}

def Yw (G : SimpleGraph V) (h : V → ℕ) (R : G.Subgraph) : Set V :=
  {v | ∃ n, Odd n ∧ ∃ w : Fin (n+1) → V, IsEW G h R n w ∧ lastV w = v}

def Adm (G : SimpleGraph V) (h : V → ℕ) (R : G.Subgraph) : Prop := ∀ v, sdeg G R v ≤ h v + 1

noncomputable def dfct (G : SimpleGraph V) (h : V → ℕ) (R : G.Subgraph) : ℕ :=
  ∑ v, max 0 (h v - sdeg G R v)

/-! ## Prefix of an alternating walk -/

lemma IsEW.prefix {G : SimpleGraph V} {h : V → ℕ} {R : G.Subgraph} {n : ℕ} {v : Fin (n+1) → V}
    (hv : IsEW G h R n v) {k : ℕ} (hk : k ≤ n) :
    IsEW G h R k (fun i : Fin (k+1) => v (Fin.castLE (by omega : k+1 ≤ n+1) i)) := by
  obtain ⟨hd, hadj, hal, hinj⟩ := hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hd
  · intro i
    simp only [Fin.castLE_castSucc, Fin.castLE_succ]
    exact hadj (Fin.castLE (by omega : k ≤ n) i)
  · intro i
    simp only [Fin.castLE_castSucc, Fin.castLE_succ]
    exact hal (Fin.castLE (by omega : k ≤ n) i)
  · intro a b hab
    simp only [Fin.castLE_castSucc, Fin.castLE_succ] at hab
    have h : Fin.castLE (by omega : k ≤ n) a = Fin.castLE (by omega : k ≤ n) b :=
      @hinj _ _ hab
    exact Fin.castLE_injective (by omega) h

lemma IsEW.prefix_last {G : SimpleGraph V} {h : V → ℕ} {R : G.Subgraph} {n : ℕ}
    {v : Fin (n+1) → V} {k : ℕ} (hk : k ≤ n) :
    lastV (fun i : Fin (k+1) => v (Fin.castLE (by omega : k+1 ≤ n+1) i)) = v ⟨k, by omega⟩ := rfl

/-! ## Extending an alternating walk by one edge -/

lemma IsEW.extend {G : SimpleGraph V} {h : V → ℕ} {R : G.Subgraph} {n : ℕ} {v : Fin (n+1) → V}
    (hv : IsEW G h R n v) {z : V} (hgz : G.Adj (lastV v) z) (hRz : R.Adj (lastV v) z ↔ Odd n)
    (hnew : ∀ i : Fin n, s(v i.castSucc, v i.succ) ≠ s(lastV v, z)) :
    IsEW G h R (n+1) (Fin.snoc v z) := by
  obtain ⟨hd, hadj, hal, hinj⟩ := hv
  have h0 : ((Fin.snoc v z : Fin (n+2) → V)) (0 : Fin (n+2)) = v 0 := by
    rw [← Fin.castSucc_zero (n := n+1), Fin.snoc_castSucc]
  have hlast : ((Fin.snoc v z : Fin (n+2) → V)) (Fin.last (n+1)) = z := Fin.snoc_last ..
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h0]; exact hd
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
      exact hadj j
    · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
      exact hgz
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc, Fin.val_castSucc]
      exact hal j
    · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last]
      exact hRz
  · intro a b hab
    rcases Fin.eq_castSucc_or_eq_last a with ⟨j, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨l, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_last, Fin.succ_last] at hab
        rw [@hinj j l hab]
      · simp only [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_last, Fin.succ_last] at hab
        exact absurd hab (hnew j)
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨l, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_last, Fin.succ_last] at hab
        exact absurd hab.symm (hnew l)
      · rfl

/-! ## Memberships -/

lemma mem_Xw_of_isEW {G : SimpleGraph V} {h : V → ℕ} {R : G.Subgraph} {n : ℕ}
    {v : Fin (n+1) → V} (hn : Even n) (hv : IsEW G h R n v) : lastV v ∈ Xw G h R :=
  ⟨n, hn, v, hv, rfl⟩

lemma mem_Yw_of_isEW {G : SimpleGraph V} {h : V → ℕ} {R : G.Subgraph} {n : ℕ}
    {v : Fin (n+1) → V} (hn : Odd n) (hv : IsEW G h R n v) : lastV v ∈ Yw G h R :=
  ⟨n, hn, v, hv, rfl⟩

lemma Dset_subset_Xw {G : SimpleGraph V} {h : V → ℕ} {R : G.Subgraph} {d : V}
    (hd : d ∈ Dset G h R) : d ∈ Xw G h R := by
  refine ⟨0, ⟨0, rfl⟩, (fun _ : Fin 1 => d), ?_, rfl⟩
  refine ⟨hd, ?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i

/-! ## The minimiser: saturated endpoints of odd walks, non-saturated endpoints of even walks -/

section Flip

variable {G : SimpleGraph V} [DecidableRel G.Adj] {h : V → ℕ} {R : G.Subgraph}

/-- Auxiliary: the flipped degrees, written as a sum of the original degree and two indicator
terms, when the walk has odd length. -/
private lemma delta_odd {n : ℕ} {v : Fin (n+1) → V}
    (hnodd : Odd n) {y : V} (R' : G.Subgraph)
    (hdeg : ∀ a : V, (sdeg G R' a : ℤ)
        = (sdeg G R a : ℤ)
          + (if a = v 0 then 1 else 0)
          - (if a = v (Fin.last n) then ((-1 : ℤ) ^ n) else 0))
    (hy : v (Fin.last n) = y) :
    ∀ a : V, (sdeg G R' a : ℤ) = (sdeg G R a : ℤ)
        + (if a = v 0 then (1:ℤ) else 0) + (if a = y then (1:ℤ) else 0) := by
  intro a
  have h := hdeg a
  rw [hy, hnodd.neg_one_pow] at h
  rw [h]
  split_ifs <;> ring

end Flip

variable {G : SimpleGraph V} [DecidableRel G.Adj] {h : V → ℕ} {R : G.Subgraph}

lemma Yw_subset_Sat (hAdm : Adm G h R)
    (hmin : ∀ R' : G.Subgraph, Adm G h R' → dfct G h R ≤ dfct G h R')
    {y : V} (hy : y ∈ Yw G h R) : sdeg G R y = h y + 1 := by
  obtain ⟨n, hnodd, v, hv, hlast⟩ := hy
  obtain ⟨hd, hadj, hal, hinj⟩ := hv
  by_contra hne
  have hle : sdeg G R y ≤ h y := by have := hAdm y; omega
  obtain ⟨R', _hspan, hdeg⟩ := Commons.Combinatorics.SimpleGraph.alt_walk_flip_degree G R v hadj hinj hal
  have hvy : v (Fin.last n) = y := hlast
  have hdelta := delta_odd (R := R) hnodd R' hdeg hvy
  have hbdelta : ∀ a : V, a ≠ v 0 → (sdeg G R' a : ℤ)
      = (sdeg G R a : ℤ) + (if a = y then (1:ℤ) else 0) := by
    intro a ha
    rw [hdelta a, if_neg ha]
    ring
  have hmono : ∀ a : V, a ≠ v 0 → (sdeg G R a : ℤ) ≤ (sdeg G R' a : ℤ) := by
    intro a ha
    rw [hbdelta a ha]
    have : (0:ℤ) ≤ (if a = y then (1:ℤ) else 0) := by split_ifs <;> norm_num
    linarith
  have hstrict : (sdeg G R (v 0) : ℤ) + 1 ≤ (sdeg G R' (v 0) : ℤ) := by
    rw [hdelta (v 0), if_pos rfl]
    have : (0:ℤ) ≤ (if v 0 = y then (1:ℤ) else 0) := by split_ifs <;> norm_num
    linarith
  have hmonoN : ∀ a : V, a ≠ v 0 → sdeg G R a ≤ sdeg G R' a :=
    fun a ha => by exact_mod_cast hmono a ha
  have hstrictN : sdeg G R (v 0) + 1 ≤ sdeg G R' (v 0) := by exact_mod_cast hstrict
  have hb2 : (sdeg G R' (v 0) : ℤ) ≤ (sdeg G R (v 0) : ℤ) + 2 := by
    rw [hdelta (v 0), if_pos rfl]
    have : (if v 0 = y then (1:ℤ) else 0) ≤ 1 := by split_ifs <;> norm_num
    linarith
  have hAdm' : Adm G h R' := by
    intro a
    have h1 : (sdeg G R' a : ℤ) ≤ (h a : ℤ) + 1 := by
      by_cases ha : a = v 0
      · subst ha
        have hd0 : sdeg G R (v 0) < h (v 0) := hd
        have hb := hb2
        omega
      · rw [hbdelta a ha]
        by_cases hay : a = y
        · rw [if_pos hay]
          subst hay
          have := hle
          omega
        · rw [if_neg hay]
          have := hAdm a
          omega
    exact_mod_cast h1
  have hterm_lt : max 0 (h (v 0) - sdeg G R' (v 0))
      < max 0 (h (v 0) - sdeg G R (v 0)) := by
    have hd0 : sdeg G R (v 0) < h (v 0) := hd
    have hs : sdeg G R (v 0) + 1 ≤ sdeg G R' (v 0) := hstrictN
    have e2 : h (v 0) - sdeg G R' (v 0) ≤ h (v 0) - sdeg G R (v 0) - 1 := by omega
    have e5 : max 0 (h (v 0) - sdeg G R (v 0)) = h (v 0) - sdeg G R (v 0) :=
      max_eq_right (by omega)
    rw [e5]
    calc max 0 (h (v 0) - sdeg G R' (v 0))
        ≤ max 0 (h (v 0) - sdeg G R (v 0) - 1) := max_le_max le_rfl e2
      _ ≤ h (v 0) - sdeg G R (v 0) - 1 := max_le (by omega) le_rfl
      _ < h (v 0) - sdeg G R (v 0) := by omega
  have hterm : ∀ a : V, max 0 (h a - sdeg G R' a) ≤ max 0 (h a - sdeg G R a) := by
    intro a
    by_cases ha : a = v 0
    · subst ha; exact le_of_lt hterm_lt
    · exact max_le_max le_rfl (Nat.sub_le_sub_left (hmonoN a ha) _)
  have hsum : dfct G h R' < dfct G h R := by
    rw [dfct, dfct]
    exact Finset.sum_lt_sum (fun a _ => hterm a) ⟨v 0, Finset.mem_univ _, hterm_lt⟩
  have := hmin R' hAdm'
  exact absurd this (not_le.mpr hsum)

lemma Xw_disjoint_Sat (hAdm : Adm G h R)
    (hmin : ∀ R' : G.Subgraph, Adm G h R' → dfct G h R ≤ dfct G h R')
    {x : V} (hx : x ∈ Xw G h R) : sdeg G R x ≤ h x := by
  obtain ⟨n, hneven, v, hv, hlast⟩ := hx
  obtain ⟨hd, hadj, hal, hinj⟩ := hv
  by_contra hcon
  push_neg at hcon
  have hsat : sdeg G R x = h x + 1 := by have := hAdm x; omega
  obtain ⟨R', _hspan, hdeg⟩ := Commons.Combinatorics.SimpleGraph.alt_walk_flip_degree G R v hadj hinj hal
  have hvx : v (Fin.last n) = x := hlast
  have hdelta : ∀ a : V, (sdeg G R' a : ℤ) = (sdeg G R a : ℤ)
      + (if a = v 0 then (1:ℤ) else 0) - (if a = x then (1:ℤ) else 0) := by
    intro a
    have hh : (sdeg G R' a : ℤ) = (sdeg G R a : ℤ)
        + (if a = v 0 then (1:ℤ) else 0)
        - (if a = v (Fin.last n) then ((-1:ℤ) ^ n) else 0) := hdeg a
    rw [hvx, hneven.neg_one_pow] at hh
    rw [hh]
  have hv0ne : v 0 ≠ x := by
    intro hvv
    have hd0 : sdeg G R (v 0) < h (v 0) := hd
    rw [hvv, hsat] at hd0
    omega
  have hbdelta : ∀ a : V, a ≠ v 0 → (sdeg G R' a : ℤ)
      = (sdeg G R a : ℤ) - (if a = x then (1:ℤ) else 0) := by
    intro a ha
    rw [hdelta a, if_neg ha]
    ring
  have hmono : ∀ a : V, a ≠ v 0 → (sdeg G R' a : ℤ) ≤ (sdeg G R a : ℤ) := by
    intro a ha
    rw [hbdelta a ha]
    have : (0:ℤ) ≤ (if a = x then (1:ℤ) else 0) := by split_ifs <;> norm_num
    linarith
  have hstrict : (sdeg G R (v 0) : ℤ) + 1 ≤ (sdeg G R' (v 0) : ℤ) := by
    rw [hdelta (v 0), if_pos rfl]
    have hz : (if v 0 = x then (1:ℤ) else 0) = 0 := by rw [if_neg hv0ne]
    linarith
  have hmonoN : ∀ a : V, a ≠ v 0 → sdeg G R' a ≤ sdeg G R a :=
    fun a ha => by exact_mod_cast hmono a ha
  have hstrictN : sdeg G R (v 0) + 1 ≤ sdeg G R' (v 0) := by exact_mod_cast hstrict
  have hb2 : (sdeg G R' (v 0) : ℤ) = (sdeg G R (v 0) : ℤ) + 1 := by
    rw [hdelta (v 0), if_pos rfl, if_neg hv0ne]
    ring
  have hAdm' : Adm G h R' := by
    intro a
    have h1 : (sdeg G R' a : ℤ) ≤ (h a : ℤ) + 1 := by
      by_cases ha : a = v 0
      · subst ha
        have hd0 : sdeg G R (v 0) < h (v 0) := hd
        have hs := hb2
        omega
      · rw [hbdelta a ha]
        have hb := hAdm a
        omega
    exact_mod_cast h1
  have hterm_lt : max 0 (h (v 0) - sdeg G R' (v 0))
      < max 0 (h (v 0) - sdeg G R (v 0)) := by
    have hd0 : sdeg G R (v 0) < h (v 0) := hd
    have hs : sdeg G R (v 0) + 1 ≤ sdeg G R' (v 0) := hstrictN
    have e2 : h (v 0) - sdeg G R' (v 0) ≤ h (v 0) - sdeg G R (v 0) - 1 := by omega
    have e5 : max 0 (h (v 0) - sdeg G R (v 0)) = h (v 0) - sdeg G R (v 0) :=
      max_eq_right (by omega)
    rw [e5]
    calc max 0 (h (v 0) - sdeg G R' (v 0))
        ≤ max 0 (h (v 0) - sdeg G R (v 0) - 1) := max_le_max le_rfl e2
      _ ≤ h (v 0) - sdeg G R (v 0) - 1 := max_le (by omega) le_rfl
      _ < h (v 0) - sdeg G R (v 0) := by omega
  have hRx' : sdeg G R' x = h x := by
    have hh := hdelta x
    rw [if_neg (fun hc => hv0ne hc.symm), if_pos rfl, hsat] at hh
    push_cast at hh
    have : (sdeg G R' x : ℤ) = (h x : ℤ) := by linarith
    exact_mod_cast this
  have hterm : ∀ a : V, max 0 (h a - sdeg G R' a) ≤ max 0 (h a - sdeg G R a) := by
    intro a
    by_cases ha : a = v 0
    · subst ha; exact le_of_lt hterm_lt
    · by_cases hax : a = x
      · have h1 : h a - sdeg G R' a = 0 := by rw [hax, hRx']; omega
        have h2 : h a - sdeg G R a = 0 := by rw [hax, hsat]; omega
        rw [h1, h2]
      · have hdeg' : (sdeg G R' a : ℤ) = (sdeg G R a : ℤ) := by
          rw [hbdelta a ha, if_neg hax]
          ring
        have hEq : sdeg G R' a = sdeg G R a := by exact_mod_cast hdeg'
        rw [hEq]
  have hsum : dfct G h R' < dfct G h R := by
    rw [dfct, dfct]
    exact Finset.sum_lt_sum (fun a _ => hterm a) ⟨v 0, Finset.mem_univ _, hterm_lt⟩
  have := hmin R' hAdm'
  exact absurd this (not_le.mpr hsum)

lemma Xw_inter_Yw_empty (hAdm : Adm G h R)
    (hmin : ∀ R' : G.Subgraph, Adm G h R' → dfct G h R ≤ dfct G h R') :
    Disjoint (Xw G h R) (Yw G h R) := by
  rw [Set.disjoint_left]
  intro v hx hy
  have h1 := Yw_subset_Sat hAdm hmin hy
  have h2 := Xw_disjoint_Sat hAdm hmin hx
  omega

/-! ## Closure properties of the reachable sets -/

lemma mem_Xw_of_prefix {G : SimpleGraph V} {h : V → ℕ} {R : G.Subgraph} {n : ℕ}
    {v : Fin (n+1) → V} (hv : IsEW G h R n v) {k : ℕ} (hk : k ≤ n) (hpar : Even k) :
    v ⟨k, by omega⟩ ∈ Xw G h R :=
  ⟨k, hpar, (fun j : Fin (k+1) => v (Fin.castLE (by omega : k+1 ≤ n+1) j)),
    hv.prefix hk, IsEW.prefix_last (G := G) (h := h) (R := R) hk⟩

lemma mem_Yw_of_prefix {G : SimpleGraph V} {h : V → ℕ} {R : G.Subgraph} {n : ℕ}
    {v : Fin (n+1) → V} (hv : IsEW G h R n v) {k : ℕ} (hk : k ≤ n) (hpar : Odd k) :
    v ⟨k, by omega⟩ ∈ Yw G h R :=
  ⟨k, hpar, (fun j : Fin (k+1) => v (Fin.castLE (by omega : k+1 ≤ n+1) j)),
    hv.prefix hk, IsEW.prefix_last (G := G) (h := h) (R := R) hk⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj] {h : V → ℕ} {R : G.Subgraph}

lemma not_mem_Yw_of_mem_Xw (hAdm : Adm G h R)
    (hmin : ∀ R' : G.Subgraph, Adm G h R' → dfct G h R ≤ dfct G h R')
    {x : V} (hx : x ∈ Xw G h R) : x ∉ Yw G h R :=
  fun hy => (Set.disjoint_left.mp (Xw_inter_Yw_empty hAdm hmin) hx) hy

lemma not_mem_Xw_of_mem_Yw (hAdm : Adm G h R)
    (hmin : ∀ R' : G.Subgraph, Adm G h R' → dfct G h R ≤ dfct G h R')
    {y : V} (hy : y ∈ Yw G h R) : y ∉ Xw G h R :=
  fun hx => (Set.disjoint_left.mp (Xw_inter_Yw_empty hAdm hmin) hx) hy

lemma Yw_Rnbr_subset_Xw (hAdm : Adm G h R)
    (hmin : ∀ R' : G.Subgraph, Adm G h R' → dfct G h R ≤ dfct G h R')
    {y : V} (hy : y ∈ Yw G h R) {z : V} (hz : R.Adj y z) : z ∈ Xw G h R := by
  have hyw : y ∈ Yw G h R := hy
  obtain ⟨n, hnodd, v, hw, hlast⟩ := hy
  have hd : v 0 ∈ Dset G h R := hw.1
  have hadj : ∀ i : Fin n, G.Adj (v i.castSucc) (v i.succ) := hw.2.1
  by_cases hcase : ∃ i : Fin n, s(v i.castSucc, v i.succ) = s(y, z)
  · obtain ⟨i, hi⟩ := hcase
    have hcs : v i.castSucc = v ⟨i.val, by omega⟩ := by congr 1
    have hsc : v i.succ = v ⟨i.val + 1, by omega⟩ := by congr 1
    rcases Sym2.eq_iff.mp hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hpar : Even (i.val + 1)
      · have hmem := mem_Xw_of_prefix hw (k := i.val + 1) (by omega) hpar
        rwa [show v ⟨i.val + 1, by omega⟩ = z from by rw [← hsc, h2]] at hmem
      · exfalso
        have hev : Even i.val := by
          rcases Nat.even_or_odd i.val with hh | hh
          · exact hh
          · exact absurd hh.add_one hpar
        have hmem := mem_Xw_of_prefix hw (k := i.val) (by omega) hev
        have hyx : y ∈ Xw G h R := by
          rwa [show v ⟨i.val, by omega⟩ = y from by rw [← hcs, h1]] at hmem
        exact not_mem_Xw_of_mem_Yw hAdm hmin hyw hyx
    · by_cases hpar : Even i.val
      · have hmem := mem_Xw_of_prefix hw (k := i.val) (by omega) hpar
        rwa [show v ⟨i.val, by omega⟩ = z from by rw [← hcs, h1]] at hmem
      · exfalso
        have hodd : Odd i.val := by
          rcases Nat.even_or_odd i.val with hh | hh
          · exact absurd hh hpar
          · exact hh
        have hmem := mem_Xw_of_prefix hw (k := i.val + 1) (by omega) hodd.add_one
        have hyx : y ∈ Xw G h R := by
          rwa [show v ⟨i.val + 1, by omega⟩ = y from by rw [← hsc, h2]] at hmem
        exact not_mem_Xw_of_mem_Yw hAdm hmin hyw hyx
  · push_neg at hcase
    have hext : IsEW G h R (n+1) (Fin.snoc v z) := by
      refine hw.extend ?_ ?_ ?_
      · rw [hlast]; exact R.adj_sub hz
      · rw [hlast]; exact ⟨fun _ => hnodd, fun _ => hz⟩
      · intro i; rw [hlast]; exact hcase i
    exact ⟨n+1, hnodd.add_one, Fin.snoc v z, hext, Fin.snoc_last ..⟩

lemma Xw_nonRnbr_subset_Yw (hAdm : Adm G h R)
    (hmin : ∀ R' : G.Subgraph, Adm G h R' → dfct G h R ≤ dfct G h R')
    {x : V} (hx : x ∈ Xw G h R) {z : V} (hgz : G.Adj x z) (hnz : ¬ R.Adj x z) :
    z ∈ Yw G h R := by
  have hxw : x ∈ Xw G h R := hx
  obtain ⟨n, hneven, v, hw, hlast⟩ := hx
  have hd : v 0 ∈ Dset G h R := hw.1
  have hadj : ∀ i : Fin n, G.Adj (v i.castSucc) (v i.succ) := hw.2.1
  by_cases hcase : ∃ i : Fin n, s(v i.castSucc, v i.succ) = s(x, z)
  · obtain ⟨i, hi⟩ := hcase
    have hcs : v i.castSucc = v ⟨i.val, by omega⟩ := by congr 1
    have hsc : v i.succ = v ⟨i.val + 1, by omega⟩ := by congr 1
    rcases Sym2.eq_iff.mp hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hpar : Odd (i.val + 1)
      · have hmem := mem_Yw_of_prefix hw (k := i.val + 1) (by omega) hpar
        rwa [show v ⟨i.val + 1, by omega⟩ = z from by rw [← hsc, h2]] at hmem
      · exfalso
        have hodd : Odd i.val := by
          rcases Nat.even_or_odd i.val with hh | hh
          · exact absurd hh.add_one hpar
          · exact hh
        have hmem := mem_Yw_of_prefix hw (k := i.val) (by omega) hodd
        have hxy : x ∈ Yw G h R := by
          rwa [show v ⟨i.val, by omega⟩ = x from by rw [← hcs, h1]] at hmem
        exact not_mem_Yw_of_mem_Xw hAdm hmin hxw hxy
    · by_cases hpar : Odd i.val
      · have hmem := mem_Yw_of_prefix hw (k := i.val) (by omega) hpar
        rwa [show v ⟨i.val, by omega⟩ = z from by rw [← hcs, h1]] at hmem
      · exfalso
        have hev : Even i.val := by
          rcases Nat.even_or_odd i.val with hh | hh
          · exact hh
          · exact absurd hh hpar
        have hmem := mem_Yw_of_prefix hw (k := i.val + 1) (by omega) hev.add_one
        have hxy : x ∈ Yw G h R := by
          rwa [show v ⟨i.val + 1, by omega⟩ = x from by rw [← hsc, h2]] at hmem
        exact not_mem_Yw_of_mem_Xw hAdm hmin hxw hxy
  · push_neg at hcase
    have hext : IsEW G h R (n+1) (Fin.snoc v z) := by
      refine hw.extend ?_ ?_ ?_
      · rw [hlast]; exact hgz
      · rw [hlast]
        exact ⟨fun hh => absurd hh hnz,
          fun hh => absurd hh (Nat.not_odd_iff_even.mpr hneven)⟩
      · intro i; rw [hlast]; exact hcase i
    exact ⟨n+1, hneven.add_one, Fin.snoc v z, hext, Fin.snoc_last ..⟩

/-! ## The minimiser exists -/

lemma exists_min_dfct (G : SimpleGraph V) (h : V → ℕ) :
    ∃ R : G.Subgraph, Adm G h R ∧ ∀ R' : G.Subgraph, Adm G h R' → dfct G h R ≤ dfct G h R' := by
  classical
  letI : Fintype G.Subgraph := Fintype.ofFinite _
  have hne : (Finset.univ.filter (Adm G h)).Nonempty := by
    refine ⟨⊥, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro v
    simp [sdeg]
  obtain ⟨R, hRmem, hRmin⟩ := Finset.exists_min_image (Finset.univ.filter (Adm G h)) (dfct G h) hne
  exact ⟨R, (Finset.mem_filter.mp hRmem).2,
    fun R' hR' => hRmin R' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR'⟩)⟩

/-! ## Assembly -/

theorem gf_factor_tight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V → ℕ)
    (hg : ∀ v, h v + 1 ≤ Nat.card {w : V // G.Adj v w})
    (hlov : ∀ S T : Finset V, Disjoint S T →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℤ)
        ≤ (S.sum (fun s => ((h s : ℤ) + 1)))
          + T.sum (fun t => ((Nat.card {y : V // G.Adj t y} : ℤ) - (h t : ℤ)))) :
    ∃ R : G.Subgraph, ∀ v, (h v : ℤ) ≤ (Nat.card {w : V // R.Adj v w} : ℤ) ∧
      (Nat.card {w : V // R.Adj v w} : ℤ) ≤ (h v : ℤ) + 1 := by
  classical
  obtain ⟨R, hAdm, hmin⟩ := exists_min_dfct G h
  by_cases hzero : dfct G h R = 0
  · refine ⟨R, fun v => ⟨?_, ?_⟩⟩
    · have hh : max 0 (h v - sdeg G R v) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => Nat.zero_le _)).mp
          (by simpa [dfct] using hzero) v (Finset.mem_univ v)
      have h1 : h v - sdeg G R v = 0 := le_antisymm (hh ▸ le_max_right 0 _) (Nat.zero_le _)
      have h2 : h v ≤ sdeg G R v := by omega
      exact_mod_cast h2
    · have hh := hAdm v
      exact_mod_cast hh
  · -- barrier
    set X : Finset V := (Xw G h R).toFinset with hXdef
    set Y : Finset V := (Yw G h R).toFinset with hYdef
    have hdisj : Disjoint Y X := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact (Set.disjoint_left.mp (Xw_inter_Yw_empty hAdm hmin) ((Set.mem_toFinset).mp hb))
        ((Set.mem_toFinset).mp ha)
    have hYsat : ∀ y ∈ Y, Nat.card {z : V // R.Adj y z} = h y + 1 := by
      intro y hy
      exact Yw_subset_Sat hAdm hmin ((Set.mem_toFinset).mp hy)
    have hcl1 : ∀ y ∈ Y, ∀ z : V, R.Adj y z → z ∈ X := by
      intro y hy z hyz
      exact (Set.mem_toFinset).mpr (Yw_Rnbr_subset_Xw hAdm hmin ((Set.mem_toFinset).mp hy) hyz)
    have hcl2 : ∀ x ∈ X, ∀ z : V, G.Adj x z → ¬ R.Adj x z → z ∈ Y := by
      intro x hx z hgx hnx
      exact (Set.mem_toFinset).mpr
        (Xw_nonRnbr_subset_Yw hAdm hmin ((Set.mem_toFinset).mp hx) hgx hnx)
    have hbar := Commons.Combinatorics.SimpleGraph.barrier_count_gf G R X Y h hYsat hcl1 hcl2
    have hlov' := hlov Y X hdisj
    -- lower bound on the X-sum: it equals the defect
    have hXle : ∀ x ∈ X, sdeg G R x ≤ h x := by
      intro x hx
      exact Xw_disjoint_Sat hAdm hmin ((Set.mem_toFinset).mp hx)
    have hterm_eq : ∀ x ∈ X, ((h x : ℤ) - (sdeg G R x : ℤ)) = ((max 0 (h x - sdeg G R x) : ℕ) : ℤ) := by
      intro x hx
      have hle := hXle x hx
      have h1 : max 0 (h x - sdeg G R x) = h x - sdeg G R x := max_eq_right (Nat.zero_le _)
      rw [h1, Nat.cast_sub hle]
    have hzero_out : ∀ v : V, v ∉ X → max 0 (h v - sdeg G R v) = 0 := by
      intro v hv
      have hv' : v ∉ Xw G h R := by simpa [hXdef] using hv
      have h1 : h v ≤ sdeg G R v := by
        by_contra hc
        push_neg at hc
        exact hv' (Dset_subset_Xw hc)
      omega
    have hsumX : X.sum (fun x => max 0 (h x - sdeg G R x)) = dfct G h R := by
      rw [dfct]
      exact Finset.sum_subset (Finset.subset_univ X) (fun x _ hx => hzero_out x hx)
    have hC : (X.sum (fun x => ((h x : ℤ) - (sdeg G R x : ℤ)))) = ((dfct G h R : ℕ) : ℤ) := by
      calc X.sum (fun x => ((h x : ℤ) - (sdeg G R x : ℤ)))
          = X.sum (fun x => ((max 0 (h x - sdeg G R x) : ℕ) : ℤ)) :=
            Finset.sum_congr rfl (fun x hx => hterm_eq x hx)
        _ = ((X.sum (fun x => max 0 (h x - sdeg G R x)) : ℕ) : ℤ) := (Nat.cast_sum _ _).symm
        _ = ((dfct G h R : ℕ) : ℤ) := by rw [hsumX]
    have hsum1 : 0 < (X.sum (fun x => ((h x : ℤ) - (sdeg G R x : ℤ)))) := by
      rw [hC]
      have : 0 < dfct G h R := by omega
      exact_mod_cast this
    have hbar' : (((Y.product X).filter (fun p => G.Adj p.1 p.2)).card : ℤ)
        = Y.sum (fun y => ((h y : ℤ) + 1))
          + X.sum (fun x => ((Nat.card {w : V // G.Adj x w} : ℤ) - (h x : ℤ)))
          + X.sum (fun x => ((h x : ℤ) - (sdeg G R x : ℤ))) := by
      simpa [sdeg] using hbar
    have hsum0 : (X.sum (fun x => ((h x : ℤ) - (sdeg G R x : ℤ)))) ≤ 0 := by
      linarith [hbar', hlov']
    exact absurd (lt_of_lt_of_le hsum1 hsum0) (lt_irrefl 0)

end Commons.Combinatorics.Factor
