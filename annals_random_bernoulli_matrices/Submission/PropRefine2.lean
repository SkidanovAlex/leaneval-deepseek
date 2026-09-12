import Mathlib
import Submission.Sec3Tower
import Submission.ProdCount
import Submission.PropRefine

open Submission.Sec3Tower
open Submission.ProdCount

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Prop refinement: the sequential (per-prefix) counting lemma

Tikhomirov 2020, Section 3 (`prop: refinement`, proof lines ~1358–1368).

For `m` mixing steps with coordinate sets `J : Fin m → Finset ℤ`, suppose at
each position `k < m` the number of "bad" values of the next coordinate
(relative to any valid prefix) is at most `c·|J_k|`.  Then the number of full
tuples `x ∈ prodFinset m J` with at least `r` bad positions is at most
`C(m,r)·c^r·∏|J_j|`.

This is the per-`S` union-bound ingredient of phase 1: with
`BadStep_k(u, a) := ¬flat(g_k(u)) ∧ ¬drop(g_k(u), a)` the per-prefix bound is
`Refine3.step_bad_count` (flatness makes the set empty), giving
`c := 1024μ`; combined with `count_ge_events_le` and
`Commons.Analysis.Real.prop_refine_tail` it yields the phase-1 export.

`badCnt` counts the bad positions of a length-`L` prefix `v`:
position `i` is bad iff `rawBad i.val (pre v (i.val+1))`.
-/

namespace Submission.PropRefine2

attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- number of bad positions of a prefix `v` of length `L`. -/
def badCnt {L : ℕ} (rawBad : (k : ℕ) → (Fin (k + 1) → ℤ) → Prop)
    (v : Fin L → ℤ) : ℕ :=
  ((Finset.univ : Finset (Fin L)).filter (fun i : Fin L =>
    rawBad i.val (pre v (i.val + 1) (Nat.succ_le_of_lt i.isLt)))).card


/-- `pre` does not depend on the proof that `m ≤ ℓ`. -/
lemma pre_bound_irrel {ℓ : ℕ} (x : Fin ℓ → ℤ) {m : ℕ} {p₁ p₂ : m ≤ ℓ} :
    pre x m p₁ = pre x m p₂ := by
  funext j
  dsimp [pre]

/-- restricting a vector to its first `k` coordinates and then to the first
`j+1 ≤ k` is the same as restricting directly to the first `j+1`. -/
lemma pre_restrict_eq {k : ℕ} (v : Fin (k + 1) → ℤ) {j : ℕ} (hj : j + 1 ≤ k) :
    pre v (j + 1) (Nat.le_trans hj (Nat.le_succ k)) = pre (restrict v) (j + 1) hj := by
  funext q
  dsimp [pre, restrict]

/-- extending a prefix by one coordinate does not change the earlier prefixes. -/
lemma pre_extend_eq {k : ℕ} (u : Fin k → ℤ) (a : ℤ) {j : ℕ} (hj : j + 1 ≤ k) :
    pre (extendFin u a) (j + 1) (Nat.le_trans hj (Nat.le_succ k)) = pre u (j + 1) hj := by
  calc
    pre (extendFin u a) (j + 1) (Nat.le_trans hj (Nat.le_succ k))
        = pre (restrict (extendFin u a)) (j + 1) hj := pre_restrict_eq (extendFin u a) hj
    _ = pre u (j + 1) hj := by rw [restrict_extend u a]

/-- `pre` of a full vector is the vector itself (up to the bound proof). -/
lemma pre_full_eq {ℓ : ℕ} (v : Fin (ℓ + 1) → ℤ) :
    pre v (ℓ + 1) (Nat.le_refl (ℓ + 1)) = v := by
  funext j
  dsimp [pre]

/-- the bad count of an extension is the bad count of the prefix plus the
indicator of the new (last) coordinate being bad. -/
lemma badCnt_extend {k : ℕ} (rawBad : (j : ℕ) → (Fin (j + 1) → ℤ) → Prop)
    (u : Fin k → ℤ) (a : ℤ) :
    badCnt rawBad (extendFin u a) =
      badCnt rawBad u + (if rawBad k (extendFin u a) then 1 else 0) := by
  classical
  -- cardinality as an indicator sum over positions
  have hcardL : badCnt rawBad (extendFin u a) =
      ∑ i : Fin (k + 1), (if rawBad i.val
        (pre (extendFin u a) (i.val + 1) (Nat.succ_le_of_lt i.isLt)) then 1 else 0) := by
    dsimp [badCnt]
    rw [Finset.card_filter]
  have hcardR : badCnt rawBad u + (if rawBad k (extendFin u a) then 1 else 0) =
      (∑ i : Fin k, (if rawBad i.val
        (pre u (i.val + 1) (Nat.succ_le_of_lt i.isLt)) then 1 else 0)) +
        (if rawBad k (extendFin u a) then 1 else 0) := by
    dsimp [badCnt]
    rw [Finset.card_filter]
  -- map each prefix-position i to the position i.castSucc of the extension
  have hsum : (∑ i : Fin (k + 1), (if rawBad i.val
        (pre (extendFin u a) (i.val + 1) (Nat.succ_le_of_lt i.isLt)) then 1 else 0)) =
      (∑ i : Fin k, (if rawBad i.val
        (pre u (i.val + 1) (Nat.succ_le_of_lt i.isLt)) then 1 else 0)) +
        (if rawBad k (extendFin u a) then 1 else 0) := by
    rw [Fin.sum_univ_castSucc (fun i : Fin (k + 1) => if rawBad i.val
      (pre (extendFin u a) (i.val + 1) (Nat.succ_le_of_lt i.isLt)) then 1 else 0)]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hji : i.val + 1 ≤ k := Nat.succ_le_of_lt i.isLt
      have hpreArg : pre (extendFin u a) (i.val + 1)
            (Nat.succ_le_of_lt (Fin.castSucc i).isLt) =
          pre u (i.val + 1) (Nat.succ_le_of_lt i.isLt) := by
        calc
          pre (extendFin u a) (i.val + 1) (Nat.succ_le_of_lt (Fin.castSucc i).isLt)
              = pre (extendFin u a) (i.val + 1) (Nat.le_trans hji (Nat.le_succ k)) :=
                pre_bound_irrel (extendFin u a)
          _ = pre u (i.val + 1) hji := pre_extend_eq u a hji
      have hc : (rawBad (Fin.castSucc i).val
            (pre (extendFin u a) ((Fin.castSucc i).val + 1) (Nat.succ_le_of_lt (Fin.castSucc i).isLt))) =
          (rawBad i.val (pre u (i.val + 1) (Nat.succ_le_of_lt i.isLt))) := by
        change rawBad i.val (pre (extendFin u a) (i.val + 1)
            (Nat.succ_le_of_lt (Fin.castSucc i).isLt)) =
          rawBad i.val (pre u (i.val + 1) (Nat.succ_le_of_lt i.isLt))
        exact congrArg (rawBad i.val) hpreArg
      rw [hc]
  calc
    badCnt rawBad (extendFin u a)
        = ∑ i : Fin (k + 1), (if rawBad i.val
            (pre (extendFin u a) (i.val + 1) (Nat.succ_le_of_lt i.isLt)) then 1 else 0) := hcardL
    _ = (∑ i : Fin k, (if rawBad i.val
            (pre u (i.val + 1) (Nat.succ_le_of_lt i.isLt)) then 1 else 0)) +
          (if rawBad k (extendFin u a) then 1 else 0) := hsum
    _ = badCnt rawBad u + (if rawBad k (extendFin u a) then 1 else 0) := hcardR.symm


/-- `extendFin u a` is injective in `a` (for fixed `u`). -/
lemma extendFin_injective_a {ℓ : ℕ} (y : Fin ℓ → ℤ) :
    Function.Injective (fun a : ℤ => extendFin y a) := by
  intro a₁ a₂ h
  have hlast := congrFun h (Fin.last ℓ)
  simpa [extendFin] using hlast

/-- the fiber decomposition of the filtered product: a filtered
`(k+1)`-product is the disjoint union over prefixes of the fibers. -/
lemma fiber_filter {k : ℕ} (A : Fin (k + 1) → Finset ℤ) (P : (Fin (k + 1) → ℤ) → Prop) :
    ((prodFinset (k + 1) A).filter P).card =
      ∑ y ∈ prodFinset k (fun j : Fin k => A (Fin.castSucc j)),
        ((A (Fin.last k)).filter (fun a : ℤ => P (extendFin y a))).card := by
  classical
  have hdecomp : prodFinset (k + 1) A =
      (prodFinset k (fun j : Fin k => A (Fin.castSucc j))).biUnion
        (fun y : Fin k → ℤ => (A (Fin.last k)).image (fun a : ℤ => extendFin y a)) := by
    rfl
  rw [hdecomp]
  rw [Finset.filter_biUnion]
  let s : Finset (Fin k → ℤ) := prodFinset k (fun j : Fin k => A (Fin.castSucc j))
  have hdisj : (↑s : Set (Fin k → ℤ)).PairwiseDisjoint
      (fun y : Fin k → ℤ => ((A (Fin.last k)).image (fun a : ℤ => extendFin y a)).filter P) := by
    intro y₁ hy₁ y₂ hy₂ hne
    have hst := disjoint_extend_image (Y := A (Fin.last k)) (y₁ := y₁) (y₂ := y₂) hne
    change Disjoint (((A (Fin.last k)).image (fun a : ℤ => extendFin y₁ a)).filter P)
        (((A (Fin.last k)).image (fun a : ℤ => extendFin y₂ a)).filter P)
    rw [Finset.disjoint_left] at hst ⊢
    intro x hx₁ hx₂
    exact (hst (Finset.mem_filter.mp hx₁).1) (Finset.mem_filter.mp hx₂).1
  have hb := Finset.card_biUnion hdisj
  calc
    (((prodFinset k (fun j : Fin k => A (Fin.castSucc j))).biUnion
        (fun y : Fin k → ℤ => ((A (Fin.last k)).image (fun a : ℤ => extendFin y a)).filter P)).card)
        = (∑ y ∈ prodFinset k (fun j : Fin k => A (Fin.castSucc j)),
              (((A (Fin.last k)).image (fun a : ℤ => extendFin y a)).filter P).card) := by
          simpa [s] using hb
    _ = (∑ y ∈ prodFinset k (fun j : Fin k => A (Fin.castSucc j)),
          ((A (Fin.last k)).filter (fun a : ℤ => P (extendFin y a))).card) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.filter_image]
          exact (Finset.card_image_of_injective
            (s := (A (Fin.last k)).filter (fun a : ℤ => P (extendFin y a)))
            (f := fun a : ℤ => extendFin y a) (extendFin_injective_a y))
/-- count of length-`m` tuples (values in `J`) with at least `s` bad steps. -/
noncomputable def cnt (m : ℕ) (J : Fin m → Finset ℤ)
    (rawBad : (j : ℕ) → (Fin (j + 1) → ℤ) → Prop) (s : ℕ) : ℕ :=
  ((prodFinset m J).filter (fun x : Fin m → ℤ => s ≤ badCnt rawBad x)).card


/-- equal coordinate families give equal product sets. -/
lemma prodFinset_congr {ℓ : ℕ} {B B' : Fin ℓ → Finset ℤ}
    (h : ∀ j : Fin ℓ, B j = B' j) : prodFinset ℓ B = prodFinset ℓ B' := by
  ext x
  rw [mem_prodFinset, mem_prodFinset]
  constructor
  · intro hx j
    rw [← h j]
    exact hx j
  · intro hx j
    rw [h j]
    exact hx j

/-- pointwise: `1[r+1 ≤ n + b] ≤ 1[r+1 ≤ n] + 1[r ≤ n]·b` for `b ∈ {0,1}`. -/
lemma ind_r_succ {r n : ℕ} {b : ℕ} (hb : b = 0 ∨ b = 1) :
    (if r + 1 ≤ n + b then 1 else 0) ≤
      (if r + 1 ≤ n then 1 else 0) + (if r ≤ n then 1 else 0) * b := by
  rcases hb with rfl | rfl
  · simp
  · by_cases h1 : r + 1 ≤ n + 1
    · by_cases h2 : r + 1 ≤ n
      · have hr : r ≤ n := by omega
        simp [h1, h2, hr]
      · have hr : r ≤ n := by omega
        simp [h1, h2, hr]
    · have hngt : ¬ r + 1 ≤ n := by omega
      have hnr : ¬ r ≤ n := by omega
      simp [h1, hngt, hnr]

/-- the sequential counting bound: with at most a `c`-fraction of bad values at
each position (given any valid prefix), the number of length-`m` tuples with at
least `r` bad positions is at most `C(m,r)·c^r·∏|J_j|`. -/
lemma fiber_boundN (m r : ℕ) (u : Fin m → ℤ) (L : Finset ℤ)
    (rawBad : (j : ℕ) → (Fin (j + 1) → ℤ) → Prop) :
    (L.filter (fun a : ℤ => r + 1 ≤ badCnt rawBad (extendFin u a))).card ≤
      L.card * (if r + 1 ≤ badCnt rawBad u then 1 else 0) +
        (if r ≤ badCnt rawBad u then 1 else 0) *
          (L.filter (fun a : ℤ => rawBad m (extendFin u a))).card := by
  classical
  have hcard : (L.filter (fun a : ℤ => r + 1 ≤ badCnt rawBad (extendFin u a))).card =
      ∑ a ∈ L, (if r + 1 ≤ badCnt rawBad (extendFin u a) then 1 else 0) := by
    simpa using (Finset.sum_boole (p := fun a : ℤ => r + 1 ≤ badCnt rawBad (extendFin u a)) (s := L))
  have hterm_ind : ∀ a ∈ L,
      (if r + 1 ≤ badCnt rawBad (extendFin u a) then 1 else 0) ≤
        (if r + 1 ≤ badCnt rawBad u then 1 else 0) +
          (if r ≤ badCnt rawBad u then 1 else 0) *
            (if rawBad m (extendFin u a) then 1 else 0) := by
    intro a ha
    have hb : (if rawBad m (extendFin u a) then 1 else 0) = 0 ∨
        (if rawBad m (extendFin u a) then 1 else 0) = 1 := by
      by_cases h : rawBad m (extendFin u a) <;> simp [h]
    have hsplit := badCnt_extend (k := m) (rawBad := rawBad) u a
    have hin := ind_r_succ (r := r) (n := badCnt rawBad u)
      (b := (if rawBad m (extendFin u a) then 1 else 0)) hb
    rwa [← hsplit] at hin
  have hsumind := Finset.sum_le_sum (s := L) (fun a ha => hterm_ind a ha)
  have hsum1 : (∑ a ∈ L, (if r + 1 ≤ badCnt rawBad u then 1 else 0)) =
      L.card * (if r + 1 ≤ badCnt rawBad u then 1 else 0) := by
    rw [Finset.sum_const]
    exact nsmul_eq_mul (L.card) (if r + 1 ≤ badCnt rawBad u then 1 else 0)
  have hsum2 : (∑ a ∈ L, (if r ≤ badCnt rawBad u then 1 else 0) *
        (if rawBad m (extendFin u a) then 1 else 0)) =
      (if r ≤ badCnt rawBad u then 1 else 0) *
        (L.filter (fun a : ℤ => rawBad m (extendFin u a))).card := by
    have hfac : (∑ a ∈ L, (if r ≤ badCnt rawBad u then 1 else 0) *
          (if rawBad m (extendFin u a) then 1 else 0)) =
        (if r ≤ badCnt rawBad u then 1 else 0) *
          (∑ a ∈ L, (if rawBad m (extendFin u a) then 1 else 0)) := by
      rw [Finset.mul_sum]
    have hsum_b : (∑ a ∈ L, (if rawBad m (extendFin u a) then 1 else 0)) =
        (L.filter (fun a : ℤ => rawBad m (extendFin u a))).card := by
      simpa using (Finset.sum_boole (p := fun a : ℤ => rawBad m (extendFin u a)) (s := L))
    rw [hfac, hsum_b]
  calc
    (L.filter (fun a : ℤ => r + 1 ≤ badCnt rawBad (extendFin u a))).card
        = ∑ a ∈ L, (if r + 1 ≤ badCnt rawBad (extendFin u a) then 1 else 0) := hcard
    _ ≤ ∑ a ∈ L, ((if r + 1 ≤ badCnt rawBad u then 1 else 0) +
          (if r ≤ badCnt rawBad u then 1 else 0) *
            (if rawBad m (extendFin u a) then 1 else 0)) := hsumind
    _ = L.card * (if r + 1 ≤ badCnt rawBad u then 1 else 0) +
          (if r ≤ badCnt rawBad u then 1 else 0) *
            (L.filter (fun a : ℤ => rawBad m (extendFin u a))).card := by
          rw [Finset.sum_add_distrib, hsum1, hsum2]

/-- ℕ-level recursion core: counting length-`m+1` tuples with ≥ r+1 bad steps
is at most `|L|·cnt(r+1) + Σ_{u ∈ B} A(u).card`, `B := {prefixes with
r ≤ badCnt}`, `A(u)` the rawBad-fiber over the last coordinate. -/
lemma cnt_m1_leN (m r : ℕ) (J : Fin (m + 1) → Finset ℤ)
    (rawBad : (j : ℕ) → (Fin (j + 1) → ℤ) → Prop) :
    cnt (m + 1) J rawBad (r + 1) ≤
      (J (Fin.last m)).card * cnt m (fun j : Fin m => J (Fin.castSucc j)) rawBad (r + 1) +
        ∑ u ∈ (prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
            (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
          ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card := by
  classical
  let RF : Fin m → Finset ℤ := fun j : Fin m => J (Fin.castSucc j)
  let s : Finset (Fin m → ℤ) := prodFinset m RF
  have hfib0 := fiber_filter (k := m) (A := J)
      (P := fun x : Fin (m + 1) → ℤ => r + 1 ≤ badCnt rawBad x)
  -- cnt (m+1) = Σ_u S(u).card  (ℕ)
  have hcntN : cnt (m + 1) J rawBad (r + 1) =
      ∑ u ∈ s, ((J (Fin.last m)).filter (fun a : ℤ => r + 1 ≤ badCnt rawBad (extendFin u a))).card := by
    calc
      cnt (m + 1) J rawBad (r + 1)
          = ((prodFinset (m + 1) J).filter (fun x : Fin (m + 1) → ℤ => r + 1 ≤ badCnt rawBad x)).card := rfl
      _ = ∑ u ∈ prodFinset m (fun j : Fin m => J (Fin.castSucc j)),
            ((J (Fin.last m)).filter (fun a : ℤ => r + 1 ≤ badCnt rawBad (extendFin u a))).card := by
            simpa using hfib0
      _ = ∑ u ∈ s, ((J (Fin.last m)).filter (fun a : ℤ => r + 1 ≤ badCnt rawBad (extendFin u a))).card := by
            simp [s, RF]
  -- per-u bound (ℕ): S(u).card ≤ |L|·1a(u) + A(u)·1b(u)
  have hterm : ∀ u : Fin m → ℤ, u ∈ s →
      ((J (Fin.last m)).filter (fun a : ℤ => r + 1 ≤ badCnt rawBad (extendFin u a))).card ≤
        (J (Fin.last m)).card * (if r + 1 ≤ badCnt rawBad u then 1 else 0) +
          (if r ≤ badCnt rawBad u then 1 else 0) *
            ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card := by
    intro u hu
    exact fiber_boundN (m := m) (r := r) (u := u) (L := J (Fin.last m)) (rawBad := rawBad)
  have hsumind : (∑ u ∈ s, ((J (Fin.last m)).filter (fun a : ℤ => r + 1 ≤ badCnt rawBad (extendFin u a))).card) ≤
      ∑ u ∈ s, ((J (Fin.last m)).card * (if r + 1 ≤ badCnt rawBad u then 1 else 0) +
          (if r ≤ badCnt rawBad u then 1 else 0) *
            ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card) := by
    exact Finset.sum_le_sum (s := s) (fun u hu => hterm u hu)
  have hsum1a : (∑ u ∈ s, (if r + 1 ≤ badCnt rawBad u then 1 else 0)) =
      cnt m RF rawBad (r + 1) := by
    calc
      (∑ u ∈ s, (if r + 1 ≤ badCnt rawBad u then 1 else 0))
          = ((s.filter (fun u : Fin m → ℤ => r + 1 ≤ badCnt rawBad u)).card) := by
            simpa using (Finset.sum_boole (p := fun u : Fin m → ℤ => r + 1 ≤ badCnt rawBad u) (s := s))
      _ = cnt m RF rawBad (r + 1) := rfl
  -- sum over the 1b-filtered part equals the B-sum
  have hsumB : (∑ u ∈ s, (if r ≤ badCnt rawBad u then 1 else 0) *
        ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card) =
      ∑ u ∈ s.filter (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
        ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card := by
    have hfw : (∑ u ∈ s.filter (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
          ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card) =
        ∑ u ∈ s, (if r ≤ badCnt rawBad u then
          ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card else 0) := by
      exact Finset.sum_filter (p := fun u : Fin m → ℤ => r ≤ badCnt rawBad u)
        (f := fun u : Fin m → ℤ => ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card)
    rw [hfw]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases h : r ≤ badCnt rawBad u <;> simp [h]
  calc
    cnt (m + 1) J rawBad (r + 1)
        = ∑ u ∈ s, ((J (Fin.last m)).filter (fun a : ℤ => r + 1 ≤ badCnt rawBad (extendFin u a))).card := hcntN
    _ ≤ ∑ u ∈ s, ((J (Fin.last m)).card * (if r + 1 ≤ badCnt rawBad u then 1 else 0) +
          (if r ≤ badCnt rawBad u then 1 else 0) *
            ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card) := hsumind
    _ = (J (Fin.last m)).card * (∑ u ∈ s, (if r + 1 ≤ badCnt rawBad u then 1 else 0)) +
          ∑ u ∈ s, (if r ≤ badCnt rawBad u then 1 else 0) *
            ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card := by
          rw [Finset.sum_add_distrib]
          congr 1
          rw [← Finset.mul_sum]
    _ = (J (Fin.last m)).card * cnt m RF rawBad (r + 1) +
          ∑ u ∈ s.filter (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
            ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card := by
          rw [hsum1a, hsumB]
    _ = (J (Fin.last m)).card * cnt m (fun j : Fin m => J (Fin.castSucc j)) rawBad (r + 1) +
          ∑ u ∈ (prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
              (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
            ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card := by
          simp [RF, s]



/-- cast of a natural-valued finset sum to reals. -/
lemma cast_sum_real {ι : Type} (s : Finset ι) (f : ι → ℕ) :
    (((∑ i ∈ s, f i) : ℕ) : ℝ) = ∑ i ∈ s, (f i : ℝ) := by
  exact map_sum (Nat.castAddMonoidHom ℝ) f s

/-- real version of the recursion: from the per-prefix `c`-bound on the rawBad
fiber one obtains the two-threshold recursion bound. -/
lemma cnt_m1_le (m r : ℕ) {J : Fin (m + 1) → Finset ℤ}
    (rawBad : (j : ℕ) → (Fin (j + 1) → ℤ) → Prop) {c : ℝ} (hc : 0 ≤ c)
    (hfiber : ∀ u : Fin m → ℤ,
      u ∈ prodFinset m (fun j : Fin m => J (Fin.castSucc j)) →
      (((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card : ℝ) ≤
        c * ((J (Fin.last m)).card : ℝ)) :
    ((cnt (m + 1) J rawBad (r + 1) : ℕ) : ℝ) ≤
      ((J (Fin.last m)).card : ℝ) *
          ((cnt m (fun j : Fin m => J (Fin.castSucc j)) rawBad (r + 1) : ℕ) : ℝ) +
        c * ((J (Fin.last m)).card : ℝ) *
          ((cnt m (fun j : Fin m => J (Fin.castSucc j)) rawBad r : ℕ) : ℝ) := by
  classical
  let RF : Fin m → Finset ℤ := fun j : Fin m => J (Fin.castSucc j)
  let B : Finset (Fin m → ℤ) := (prodFinset m RF).filter (fun u : Fin m → ℤ => r ≤ badCnt rawBad u)
  let g : (Fin m → ℤ) → ℕ := fun u => ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card
  have hN := cnt_m1_leN (m := m) (r := r) (J := J) (rawBad := rawBad)
  -- hN (nat): cnt (m+1) J rawBad (r+1) ≤ |L|·cnt₁ + Σ_{u∈B'} g u,  B' := (prodFinset m (fun j => J (Fin.castSucc j))).filter ...
  have hR1 : ((cnt (m + 1) J rawBad (r + 1) : ℕ) : ℝ) ≤
      ((((J (Fin.last m)).card * cnt m (fun j : Fin m => J (Fin.castSucc j)) rawBad (r + 1) +
        (∑ u ∈ (prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
            (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
              ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card)) : ℕ) : ℝ) := by
    exact_mod_cast hN
  have hBcast : ((((∑ u ∈ (prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
          (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
            ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card)) : ℕ) : ℝ) =
      ∑ u ∈ (prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
          (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
        (((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card : ℝ) := by
    simpa [B, g] using cast_sum_real B g
  have hBpart : (∑ u ∈ (prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
          (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
        (((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card : ℝ)) ≤
      c * ((J (Fin.last m)).card : ℝ) * ((cnt m RF rawBad r : ℕ) : ℝ) := by
    calc
      (∑ u ∈ (prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
            (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
          (((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card : ℝ))
          ≤ ∑ u ∈ (prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
              (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
              c * ((J (Fin.last m)).card : ℝ) := by
            apply Finset.sum_le_sum
            intro u hu
            have hu' : u ∈ prodFinset m (fun j : Fin m => J (Fin.castSucc j)) :=
              (Finset.mem_filter.mp hu).1
            exact hfiber u hu'
      _ = ((((prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
              (fun u : Fin m → ℤ => r ≤ badCnt rawBad u)).card : ℕ) : ℝ) *
            (c * ((J (Fin.last m)).card : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = c * ((J (Fin.last m)).card : ℝ) * ((cnt m RF rawBad r : ℕ) : ℝ) := by
            have hc1 : (((prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
                  (fun u : Fin m → ℤ => r ≤ badCnt rawBad u)).card : ℕ) =
                (cnt m RF rawBad r : ℕ) := by
              dsimp [RF]
              rfl
            rw [hc1]
            ring
  calc
    ((cnt (m + 1) J rawBad (r + 1) : ℕ) : ℝ)
        ≤ ((((J (Fin.last m)).card * cnt m (fun j : Fin m => J (Fin.castSucc j)) rawBad (r + 1) +
          (∑ u ∈ (prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
              (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
                ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card)) : ℕ) : ℝ) := hR1
    _ = ((J (Fin.last m)).card : ℝ) *
            ((cnt m (fun j : Fin m => J (Fin.castSucc j)) rawBad (r + 1) : ℕ) : ℝ) +
          ((((∑ u ∈ (prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
              (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
                ((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card)) : ℕ) : ℝ) := by
          norm_num
    _ = ((J (Fin.last m)).card : ℝ) *
            ((cnt m (fun j : Fin m => J (Fin.castSucc j)) rawBad (r + 1) : ℕ) : ℝ) +
          ∑ u ∈ (prodFinset m (fun j : Fin m => J (Fin.castSucc j))).filter
              (fun u : Fin m → ℤ => r ≤ badCnt rawBad u),
            (((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card : ℝ) := by
          rw [hBcast]
    _ ≤ ((J (Fin.last m)).card : ℝ) *
            ((cnt m (fun j : Fin m => J (Fin.castSucc j)) rawBad (r + 1) : ℕ) : ℝ) +
          c * ((J (Fin.last m)).card : ℝ) * ((cnt m RF rawBad r : ℕ) : ℝ) := by
          exact add_le_add_right hBpart (((J (Fin.last m)).card : ℝ) *
            ((cnt m (fun j : Fin m => J (Fin.castSucc j)) rawBad (r + 1) : ℕ) : ℝ))
    _ = ((J (Fin.last m)).card : ℝ) *
            ((cnt m (fun j : Fin m => J (Fin.castSucc j)) rawBad (r + 1) : ℕ) : ℝ) +
          c * ((J (Fin.last m)).card : ℝ) *
            ((cnt m (fun j : Fin m => J (Fin.castSucc j)) rawBad r : ℕ) : ℝ) := by
          simp [RF]


/-- the double-induction engine for `seq_bad_ge`. -/
lemma seq_bad_ge_aux (r : ℕ) : ∀ (m : ℕ) {J : Fin m → Finset ℤ} {c : ℝ}
    (hc : 0 ≤ c) (rawBad : (j : ℕ) → (Fin (j + 1) → ℤ) → Prop)
    (hstep : ∀ (k : ℕ) (hk : k < m) (u : Fin k → ℤ),
      u ∈ prodFinset k (fun j : Fin k => J (Fin.castLE (Nat.le_of_lt hk) j)) →
      (((J ⟨k, hk⟩).filter (fun a : ℤ => rawBad k (extendFin u a))).card : ℝ) ≤
        c * ((J ⟨k, hk⟩).card : ℝ)),
    ((cnt m J rawBad r : ℕ) : ℝ) ≤ (m.choose r : ℝ) * c ^ r * (∏ j : Fin m, ((J j).card : ℝ)) := by
  classical
  induction r with
  | zero =>
      intro m J c hc rawBad hstep
      have hcnt0 : cnt m J rawBad 0 = (prodFinset m J).card := by
        dsimp [cnt]
        rw [show (prodFinset m J).filter (fun x : Fin m → ℤ => 0 ≤ badCnt rawBad x) = prodFinset m J by
          ext x
          rw [Finset.mem_filter]
          constructor
          · intro hx; exact hx.1
          · intro hx; exact ⟨hx, Nat.zero_le _⟩]
      calc
        ((cnt m J rawBad 0 : ℕ) : ℝ) = ((prodFinset m J).card : ℝ) := by rw [hcnt0]
        _ = ∏ j : Fin m, ((J j).card : ℝ) := by
              exact_mod_cast (prodFinset_card J)
        _ ≤ (m.choose 0 : ℝ) * c ^ 0 * (∏ j : Fin m, ((J j).card : ℝ)) := by
              simp
  | succ r ih =>
      intro m J c hc rawBad hstep
      induction m with
      | zero =>
          -- m = 0: cnt 0 = 0
          have hzero : (cnt 0 J rawBad (r + 1) : ℕ) = 0 := by
            dsimp [cnt]
            rw [show (prodFinset 0 J).filter (fun x : Fin 0 → ℤ => r + 1 ≤ badCnt rawBad x) = ∅ by
              ext x
              rw [Finset.mem_filter]
              simp
              intro hx
              have hb : badCnt rawBad x = 0 := by
                dsimp [badCnt]
                simp
              omega]
            simp
          calc
            ((cnt 0 J rawBad (r + 1) : ℕ) : ℝ) = 0 := by rw [hzero]; norm_num
            _ ≤ ((0 : ℕ).choose (r + 1) : ℝ) * c ^ (r + 1) * (∏ j : Fin 0, ((J j).card : ℝ)) := by
                  have hc0 : (0 : ℕ).choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
                  rw [hc0]
                  simp
      | succ m ih_m =>
          let RF : Fin m → Finset ℤ := fun j : Fin m => J (Fin.castSucc j)
          let L : Finset ℤ := J (Fin.last m)
          have hfib : ∀ u : Fin m → ℤ,
              u ∈ prodFinset m (fun j : Fin m => J (Fin.castSucc j)) →
              (((J (Fin.last m)).filter (fun a : ℤ => rawBad m (extendFin u a))).card : ℝ) ≤
                c * ((J (Fin.last m)).card : ℝ) := by
            intro u hu
            have hfam : (fun j : Fin m => J (Fin.castSucc j)) =
                (fun j : Fin m => J (Fin.castLE (Nat.le_of_lt (Nat.lt_succ_self m)) j)) := by
              funext j
              congr 1
            have hu' : u ∈ prodFinset m (fun j : Fin m => J (Fin.castLE (Nat.le_of_lt (Nat.lt_succ_self m)) j)) := by
              rwa [hfam] at hu
            have hamb := hstep m (Nat.lt_succ_self m) u hu'
            have hlast : (J ⟨m, Nat.lt_succ_self m⟩) = J (Fin.last m) := by
              congr 1
            rwa [hlast] at hamb
          have hrec := cnt_m1_le (m := m) (r := r) (J := J) rawBad hc hfib
          have hstepRF : ∀ (k : ℕ) (hk : k < m) (u : Fin k → ℤ),
              u ∈ prodFinset k (fun j : Fin k => RF (Fin.castLE (Nat.le_of_lt hk) j)) →
              (((RF ⟨k, hk⟩).filter (fun a : ℤ => rawBad k (extendFin u a))).card : ℝ) ≤
                c * ((RF ⟨k, hk⟩).card : ℝ) := by
            intro k hk u hu
            have hk' : k < m + 1 := Nat.lt_trans hk (Nat.lt_succ_self m)
            have hfam : (fun j : Fin k => RF (Fin.castLE (Nat.le_of_lt hk) j)) =
                (fun j : Fin k => J (Fin.castLE (Nat.le_of_lt hk') j)) := by
              funext j
              dsimp [RF]
            have hu' : u ∈ prodFinset k (fun j : Fin k => J (Fin.castLE (Nat.le_of_lt hk') j)) := by
              rwa [hfam] at hu
            have hamb := hstep k hk' u hu'
            have hidx : RF ⟨k, hk⟩ = J ⟨k, hk'⟩ := by
              dsimp [RF]
            rwa [← hidx] at hamb
          have hA := ih_m (J := RF) hstepRF
          have hB := ih (m := m) (J := RF) hc rawBad hstepRF
          have hL0 : (0 : ℝ) ≤ ((J (Fin.last m)).card : ℝ) := by
            exact_mod_cast (Nat.zero_le _)
          have hL_A : (L.card : ℝ) * ((cnt m RF rawBad (r + 1) : ℕ) : ℝ) ≤
              (L.card : ℝ) * ((m.choose (r + 1) : ℝ) * c ^ (r + 1) * (∏ j : Fin m, ((RF j).card : ℝ))) := by
            simpa [L] using (mul_le_mul_of_nonneg_left hA hL0)
          have hL_B : (c * (L.card : ℝ)) * ((cnt m RF rawBad r : ℕ) : ℝ) ≤
              (c * (L.card : ℝ)) * ((m.choose r : ℝ) * c ^ r * (∏ j : Fin m, ((RF j).card : ℝ))) := by
            simpa [L] using (mul_le_mul_of_nonneg_left hB (mul_nonneg hc hL0))
          have hsum := add_le_add hL_A hL_B
          have hrecRF : ((cnt (m + 1) J rawBad (r + 1) : ℕ) : ℝ) ≤
              (L.card : ℝ) * ((cnt m RF rawBad (r + 1) : ℕ) : ℝ) +
                c * (L.card : ℝ) * ((cnt m RF rawBad r : ℕ) : ℝ) := by
            simpa [L, RF] using hrec
          have hcho : ((m + 1).choose (r + 1) : ℝ) = (m.choose r : ℝ) + (m.choose (r + 1) : ℝ) := by
            have hc2 := Nat.choose_succ_succ m r
            rw [hc2]
            exact_mod_cast rfl
          have hprod : (∏ j : Fin (m + 1), ((J j).card : ℝ)) =
              (L.card : ℝ) * (∏ j : Fin m, ((RF j).card : ℝ)) := by
            dsimp [RF, L]
            rw [Fin.prod_univ_castSucc (fun j : Fin (m + 1) => ((J j).card : ℝ))]
            ring
          have hident : (L.card : ℝ) * ((m.choose (r + 1) : ℝ) * c ^ (r + 1) *
                (∏ j : Fin m, ((RF j).card : ℝ))) +
              (c * (L.card : ℝ)) * ((m.choose r : ℝ) * c ^ r *
                (∏ j : Fin m, ((RF j).card : ℝ))) =
              ((m + 1).choose (r + 1) : ℝ) * c ^ (r + 1) *
                (∏ j : Fin (m + 1), ((J j).card : ℝ)) := by
            rw [hprod]
            rw [hcho]
            rw [pow_succ]
            ring
          have hcombo : (L.card : ℝ) * ((cnt m RF rawBad (r + 1) : ℕ) : ℝ) +
                c * (L.card : ℝ) * ((cnt m RF rawBad r : ℕ) : ℝ) ≤
              ((m + 1).choose (r + 1) : ℝ) * c ^ (r + 1) * (∏ j : Fin (m + 1), ((J j).card : ℝ)) := by
            calc
              (L.card : ℝ) * ((cnt m RF rawBad (r + 1) : ℕ) : ℝ) +
                    c * (L.card : ℝ) * ((cnt m RF rawBad r : ℕ) : ℝ)
                  ≤ (L.card : ℝ) * ((m.choose (r + 1) : ℝ) * c ^ (r + 1) *
                        (∏ j : Fin m, ((RF j).card : ℝ))) +
                      (c * (L.card : ℝ)) * ((m.choose r : ℝ) * c ^ r *
                        (∏ j : Fin m, ((RF j).card : ℝ))) := hsum
              _ = ((m + 1).choose (r + 1) : ℝ) * c ^ (r + 1) *
                    (∏ j : Fin (m + 1), ((J j).card : ℝ)) := hident
          exact le_trans hrecRF hcombo


theorem seq_bad_ge (r m : ℕ) {J : Fin m → Finset ℤ} {c : ℝ} (hc : 0 ≤ c)
    (rawBad : (j : ℕ) → (Fin (j + 1) → ℤ) → Prop)
    (hstep : ∀ (k : ℕ) (hk : k < m) (u : Fin k → ℤ),
      u ∈ prodFinset k (fun j : Fin k => J (Fin.castLE (Nat.le_of_lt hk) j)) →
      (((J ⟨k, hk⟩).filter (fun a : ℤ => rawBad k (extendFin u a))).card : ℝ) ≤
        c * ((J ⟨k, hk⟩).card : ℝ)) :
    ((cnt m J rawBad r : ℝ)) ≤ (m.choose r : ℝ) * c ^ r * (∏ j : Fin m, ((J j).card : ℝ)) := by
  classical
  exact seq_bad_ge_aux r m (J := J) hc rawBad hstep

end Submission.PropRefine2
