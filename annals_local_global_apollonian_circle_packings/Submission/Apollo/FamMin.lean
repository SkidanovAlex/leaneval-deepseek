/-
The min-value theorem for the family packings (root/descent theory).

For every Descartes quadruple w in the Apollonian orbit of famQuad t, all
coordinates satisfy famA t ≤ w j.

Strategy (fully elementary):
  * "big" coordinate: 2·w i > S(w). A Descartes quadruple (positive sum) has
    AT MOST ONE big coordinate.
  * "sink": no big coordinate (all 2·w i ≤ S(w)).  Moving a big coordinate
    (the deterministic reduction step ρ) strictly decreases the (positive
    integer) sum, so iterating ρ from any state reaches a sink.
  * every move is ρ-compatible, hence the sink reached from any orbit state
    is the same; the family root r_t = gen 3 • famQuad t is a sink, hence THE
    sink of the orbit.
  * the minimum coordinate is non-increasing under ρ, hence
    min(w) ≥ min(r_t) = famA t.
-/
import Submission.Apollo.FamOrbit
import Submission.Apollo.PackDistinct
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-! ## sums, big coordinates, sinks, minima -/

/-- coordinate sum of a quadruple. -/
def famSum (w : Fin 4 → ℤ) : ℤ := ∑ i : Fin 4, w i

/-- the sum after an S-move. -/
lemma famSum_gen (i : Fin 4) (w : Fin 4 → ℤ) :
    famSum (gen i • w) = 3 * famSum w - 4 * w i := by
  unfold famSum
  rw [Fin.sum_univ_four]
  rw [Fin.sum_univ_four]
  fin_cases i <;> simp [gen, Matrix.mulVec_eq_sum, Fin.sum_univ_four] <;> ring

/-- the sum of the coordinates except i. -/
lemma famSum_except (i : Fin 4) (w : Fin 4 → ℤ) :
    (∑ k : Fin 4, if k = i then 0 else w k) = famSum w - w i := by
  have hterm : ∀ k : Fin 4, (if k = i then 0 else w k) = w k - (if k = i then w k else 0) := by
    intro k
    by_cases hki : k = i <;> simp [hki]
  calc
    (∑ k : Fin 4, if k = i then 0 else w k)
        = ∑ k : Fin 4, (w k - (if k = i then w k else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact hterm k
    _ = (∑ k : Fin 4, w k) - ∑ k : Fin 4, (if k = i then w k else 0) := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ k : Fin 4, w k) - w i := by
            have h := Finset.sum_ite_eq' (s := (Finset.univ : Finset (Fin 4)))
              (a := i) (b := fun x : Fin 4 => w x)
            simpa using h

/-- Descartes equation (sum form). -/
def famDesc (w : Fin 4 → ℤ) : Prop := (famSum w) ^ 2 = 2 * ∑ i : Fin 4, (w i) ^ 2

/-- "big" coordinate: more than half of the sum. -/
def famBig (w : Fin 4 → ℤ) (i : Fin 4) : Prop := 2 * w i > famSum w

/-- "sink": no big coordinate. -/
def famSink (w : Fin 4 → ℤ) : Prop := ∀ i : Fin 4, 2 * w i ≤ famSum w

/-- minimum coordinate. -/
noncomputable def famMin (w : Fin 4 → ℤ) : ℤ :=
  (Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- the minimum is attained. -/
lemma famMin_attained (w : Fin 4 → ℤ) : ∃ j : Fin 4, w j = famMin w := by
  unfold famMin
  have hm : (Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)
      ∈ Finset.univ.image w := by
    exact Finset.min'_mem _ _
  rcases (Finset.mem_image.mp hm) with ⟨j, hj, h⟩
  refine ⟨j, ?_⟩
  exact h

/-- the minimum is ≤ every coordinate. -/
lemma famMin_le (w : Fin 4 → ℤ) (i : Fin 4) : famMin w ≤ w i := by
  unfold famMin
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- 4·min ≤ sum. -/
lemma famMin_avg (w : Fin 4 → ℤ) : 4 * famMin w ≤ famSum w := by
  have h0 : famMin w ≤ w 0 := famMin_le w 0
  have h1 : famMin w ≤ w 1 := famMin_le w 1
  have h2 : famMin w ≤ w 2 := famMin_le w 2
  have h3 : famMin w ≤ w 3 := famMin_le w 3
  unfold famSum
  rw [Fin.sum_univ_four]
  omega

/-- a big coordinate strictly exceeds the minimum. -/
lemma famBig_gt_min {w : Fin 4 → ℤ} {i : Fin 4} (hpos : 0 < famSum w) (hb : famBig w i) :
    famMin w < w i := by
  have havg : 4 * famMin w ≤ famSum w := famMin_avg w
  have hb' : famSum w < 2 * w i := hb
  omega

/-! ## at most one big coordinate -/

/-- the sum of two (distinct) squares is at most the full square sum. -/
lemma sqsum_pair_le (w : Fin 4 → ℤ) {i j : Fin 4} (hij : i ≠ j) :
    (w i) ^ 2 + (w j) ^ 2 ≤ ∑ x : Fin 4, (w x) ^ 2 := by
  fin_cases i <;> fin_cases j
  all_goals try (exfalso; exact hij rfl)
  all_goals
    rw [Fin.sum_univ_four]
    simp
    nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2), sq_nonneg (w 3)]

/-- a Descartes quadruple (positive sum) has at most one big coordinate. -/
theorem fam_atMostOne_big (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w) :
    ¬ ∃ i j : Fin 4, i ≠ j ∧ famBig w i ∧ famBig w j := by
  rintro ⟨i, j, hij, hi, hj⟩
  have hSi : (2 * w i) ^ 2 > (famSum w) ^ 2 := by
    have h2 := Int.mul_self_lt_mul_self (a := famSum w) (b := 2 * w i) (le_of_lt hpos) hi
    simpa [pow_two] using h2
  have hSj : (2 * w j) ^ 2 > (famSum w) ^ 2 := by
    have h2 := Int.mul_self_lt_mul_self (a := famSum w) (b := 2 * w j) (le_of_lt hpos) hj
    simpa [pow_two] using h2
  have hSq := sqsum_pair_le w hij
  unfold famDesc at hD
  nlinarith [hD, hSi, hSj, hSq]

/-- sinks are exactly the states without a big coordinate. -/
lemma famSink_iff (w : Fin 4 → ℤ) : famSink w ↔ ¬ ∃ i : Fin 4, famBig w i := by
  constructor
  · intro hs h
    rcases h with ⟨i, hb⟩
    exact (not_lt_of_ge (hs i)) hb
  · intro h i
    by_contra hb
    exact h ⟨i, not_le.mp hb⟩

/-- if one coordinate equals half the sum, the state is a sink. -/
lemma famSink_of_half (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w)
    (i : Fin 4) (hh : 2 * w i = famSum w) : famSink w := by
  intro j
  by_contra hb
  have hbj : famBig w j := not_le.mp hb
  by_cases hji : j = i
  · subst j
    omega
  · have hSi : (2 * w i) ^ 2 = (famSum w) ^ 2 := by rw [hh]
    have hSj : (2 * w j) ^ 2 > (famSum w) ^ 2 := by
      have h2 := Int.mul_self_lt_mul_self (a := famSum w) (b := 2 * w j) (le_of_lt hpos) hbj
      simpa [pow_two] using h2
    have hSq := sqsum_pair_le w hji
    unfold famDesc at hD
    nlinarith [hD, hSi, hSj, hSq]

/-! ## the reduction step -/

/-- the (deterministic) reduction step: move the unique big coordinate. -/
noncomputable def famRho (w : Fin 4 → ℤ) : Fin 4 → ℤ := by
  classical
  exact if h : ∃ i : Fin 4, famBig w i then gen (Classical.choose h) • w else w

/-- reduction fixes sinks. -/
lemma famRho_fix (w : Fin 4 → ℤ) (hs : famSink w) : famRho w = w := by
  unfold famRho
  rw [dif_neg]
  exact fun h => (famSink_iff w).1 hs h

/-- reduction of a state with a big coordinate at i moves exactly i. -/
lemma famRho_eq (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w)
    (i : Fin 4) (hb : famBig w i) : famRho w = gen i • w := by
  unfold famRho
  rw [dif_pos ⟨i, hb⟩]
  have hc : Classical.choose (show ∃ i : Fin 4, famBig w i from ⟨i, hb⟩) = i := by
    by_contra hne
    have hbch : famBig w (Classical.choose (show ∃ i : Fin 4, famBig w i from ⟨i, hb⟩)) :=
      Classical.choose_spec (show ∃ i : Fin 4, famBig w i from ⟨i, hb⟩)
    exact fam_atMostOne_big w hD hpos
      ⟨Classical.choose (show ∃ i : Fin 4, famBig w i from ⟨i, hb⟩), i, hne, hbch, hb⟩
  exact congrArg (fun x : Fin 4 => gen x • w) hc

/-- reduction strictly decreases the sum (when a big coordinate exists). -/
lemma famRho_sum_lt (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w)
    (h : ¬ famSink w) : famSum (famRho w) < famSum w := by
  have hex : ∃ i : Fin 4, famBig w i := by
    by_contra hnb
    exact h ((famSink_iff w).2 hnb)
  rcases hex with ⟨i, hb⟩
  rw [famRho_eq w hD hpos i hb]
  rw [famSum_gen]
  have hb' : famSum w < 2 * w i := hb
  omega

/-- reduction preserves Descartes and positive sum. -/
lemma famRho_desc_pos (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w) :
    famDesc (famRho w) ∧ 0 < famSum (famRho w) := by
  by_cases hs : famSink w
  · rw [famRho_fix w hs]
    exact ⟨hD, hpos⟩
  · have hex : ∃ i : Fin 4, famBig w i := by
      by_contra hnb
      exact hs ((famSink_iff w).2 hnb)
    rcases hex with ⟨i, hb⟩
    rw [famRho_eq w hD hpos i hb]
    constructor
    · change (∑ j : Fin 4, (gen i • w) j) ^ 2 = 2 * ∑ j : Fin 4, ((gen i • w) j) ^ 2
      exact gen_smul_descarates i w (by simpa [famDesc, famSum] using hD)
    · change 0 < ∑ j : Fin 4, (gen i • w) j
      exact sum_gt_zero_of_descarates_and_possum w (by simpa [famDesc, famSum] using hD)
        (by simpa [famSum] using hpos) i

/-- the minimum does not increase under reduction. -/
lemma famMin_rho_le (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w) :
    famMin (famRho w) ≤ famMin w := by
  by_cases hs : famSink w
  · rw [famRho_fix w hs]
  · have hex : ∃ i : Fin 4, famBig w i := by
      by_contra hnb
      exact hs ((famSink_iff w).2 hnb)
    rcases hex with ⟨i, hb⟩
    rw [famRho_eq w hD hpos i hb]
    rcases famMin_attained w with ⟨j, hj⟩
    have hji : j ≠ i := by
      intro hji
      subst j
      exact (ne_of_lt (famBig_gt_min hpos hb)) hj.symm
    have hkeep : (gen i • w) j = w j := other_coord_eq w i j hji
    calc
      famMin (gen i • w) ≤ (gen i • w) j := famMin_le (gen i • w) j
      _ = w j := hkeep
      _ = famMin w := hj

/-- moving a strictly-non-big coordinate makes it big. -/
lemma famBig_of_nonbig (w : Fin 4 → ℤ) (i : Fin 4) (hnb : 2 * w i < famSum w) :
    famBig (gen i • w) i := by
  unfold famBig
  change 2 * (gen i • w) i > famSum (gen i • w)
  rw [famSum_gen]
  rw [gen_smul_apply]
  simp
  rw [famSum_except]
  omega

/-- moving a coordinate equal to half the sum is the identity. -/
lemma gen_eq_self_of_half (w : Fin 4 → ℤ) (i : Fin 4) (hh : 2 * w i = famSum w) :
    gen i • w = w := by
  ext j
  rw [gen_smul_apply]
  by_cases hji : j = i
  · subst j
    simp
    rw [famSum_except]
    omega
  · simp [hji]

/-- moving a strictly-non-big coordinate: reduction moves straight back. -/
lemma famRho_of_nonbig (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w)
    (i : Fin 4) (hnb : 2 * w i < famSum w) : famRho (gen i • w) = w := by
  let w' : Fin 4 → ℤ := gen i • w
  have hb' : famBig w' i := by
    dsimp [w']
    exact famBig_of_nonbig w i hnb
  have hD' : famDesc w' := by
    dsimp [w']
    exact gen_smul_descarates i w (by simpa [famDesc, famSum] using hD)
  have hpos' : 0 < famSum w' := by
    dsimp [w']
    exact sum_gt_zero_of_descarates_and_possum w (by simpa [famDesc, famSum] using hD)
      (by simpa [famSum] using hpos) i
  calc
    famRho w' = gen i • w' := famRho_eq w' hD' hpos' i hb'
    _ = w := by
      rw [gen_smul_gen_smul]

/-- moving the big coordinate is exactly the reduction step. -/
lemma famRho_of_big (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w)
    (i : Fin 4) (hb : famBig w i) : gen i • w = famRho w := by
  rw [famRho_eq w hD hpos i hb]

/-- iterate of ρ on a sink stays at the sink. -/
lemma famRho_iterate_fix (w : Fin 4 → ℤ) (hs : famSink w) (k : ℕ) : famRho^[k] w = w := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hs' : famSink (famRho^[k] w) := by simpa [ih] using hs
      rw [famRho_fix _ hs']
      exact ih

/-- iterates: ρ^[k] (ρ w) = ρ^[k+1] w. -/
lemma famRho_iterate_step (w : Fin 4 → ℤ) (k : ℕ) : famRho^[k] (famRho w) = famRho^[k+1] w := by
  rw [Function.iterate_succ_apply]

/-- the sink reached from a move is the same as from the original state. -/
lemma sinkReach_step (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w)
    (i : Fin 4) (u : Fin 4 → ℤ) (hu : famSink u) :
    (∃ k : ℕ, u = famRho^[k] (gen i • w)) → (∃ k : ℕ, u = famRho^[k] w) := by
  rintro ⟨k, hk⟩
  by_cases hgt : 2 * w i > famSum w
  · refine ⟨k + 1, ?_⟩
    calc
      u = famRho^[k] (gen i • w) := hk
      _ = famRho^[k] (famRho w) := by rw [famRho_of_big w hD hpos i hgt]
      _ = famRho^[k+1] w := famRho_iterate_step w k
  · have hle : 2 * w i ≤ famSum w := le_of_not_gt hgt
    rcases lt_or_eq_of_le hle with hlt | heq
    · by_cases k0 : k = 0
      · subst k
        exfalso
        have hb' : famBig (gen i • w) i := famBig_of_nonbig w i hlt
        have hu' : famSink (gen i • w) := by simpa [hk] using hu
        exact (famSink_iff (gen i • w)).1 hu' ⟨i, hb'⟩
      · rcases Nat.exists_eq_succ_of_ne_zero k0 with ⟨m, hm⟩
        subst k
        refine ⟨m, ?_⟩
        calc
          u = famRho^[m+1] (gen i • w) := hk
          _ = famRho^[m] (famRho (gen i • w)) := famRho_iterate_step (gen i • w) m
          _ = famRho^[m] w := by rw [famRho_of_nonbig w hD hpos i hlt]
    · have hgen : gen i • w = w := gen_eq_self_of_half w i heq
      exact ⟨k, by simpa [hgen] using hk⟩

/-- every state reaches a sink in finitely many reduction steps. -/
lemma sink_reachable (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w) :
    ∃ u : Fin 4 → ℤ, famSink u ∧ ∃ k : ℕ, u = famRho^[k] w := by
  have hrec : ∀ N : ℕ, ∀ w : Fin 4 → ℤ, famDesc w → 0 < famSum w →
      Int.toNat (famSum w) = N → ∃ u : Fin 4 → ℤ, famSink u ∧ ∃ k : ℕ, u = famRho^[k] w := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro w hD hpos hN
      by_cases hs : famSink w
      · exact ⟨w, hs, 0, rfl⟩
      · have hex : ∃ i : Fin 4, famBig w i := by
          by_contra hnb
          exact hs ((famSink_iff w).2 hnb)
        rcases hex with ⟨i, hb⟩
        let w' : Fin 4 → ℤ := famRho w
        have hD' : famDesc w' := (famRho_desc_pos w hD hpos).1
        have hpos' : 0 < famSum w' := (famRho_desc_pos w hD hpos).2
        have hlt : famSum w' < famSum w := famRho_sum_lt w hD hpos hs
        have hN' : Int.toNat (famSum w') < N := by
          omega
        rcases ih (Int.toNat (famSum w')) hN' w' hD' hpos' rfl with ⟨u, hus, k, hk⟩
        refine ⟨u, hus, k + 1, ?_⟩
        calc
          u = famRho^[k] w' := hk
          _ = famRho^[k] (famRho w) := rfl
          _ = famRho^[k+1] w := famRho_iterate_step w k
  exact hrec (Int.toNat (famSum w)) w hD hpos rfl

/-- if two sinks are both reachable from the same state, they are equal. -/
lemma sink_unique_reachable (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w)
    (u v : Fin 4 → ℤ) (hu : famSink u) (hv : famSink v)
    (huR : ∃ k : ℕ, u = famRho^[k] w) (hvR : ∃ k : ℕ, v = famRho^[k] w) : u = v := by
  rcases huR with ⟨ku, hku⟩
  rcases hvR with ⟨kv, hkv⟩
  by_cases hkle : ku ≤ kv
  · have hsub : kv = (kv - ku) + ku := by omega
    have hExp : famRho^[kv] w = famRho^[(kv - ku) + ku] w := by
      exact congrArg (fun e : ℕ => famRho^[e] w) hsub
    have hv' : v = famRho^[kv - ku] u := by
      calc
        v = famRho^[kv] w := hkv
        _ = famRho^[(kv - ku) + ku] w := hExp
        _ = famRho^[kv - ku] (famRho^[ku] w) := by rw [Function.iterate_add_apply]
        _ = famRho^[kv - ku] u := by rw [hku]
    rw [hv']
    exact (famRho_iterate_fix u hu (kv - ku)).symm
  · have hgt : kv ≤ ku := le_of_not_ge hkle
    have hsub : ku = (ku - kv) + kv := by omega
    have hExp : famRho^[ku] w = famRho^[(ku - kv) + kv] w := by
      exact congrArg (fun e : ℕ => famRho^[e] w) hsub
    have hu' : u = famRho^[ku - kv] v := by
      calc
        u = famRho^[ku] w := hku
        _ = famRho^[(ku - kv) + kv] w := hExp
        _ = famRho^[ku - kv] (famRho^[kv] w) := by rw [Function.iterate_add_apply]
        _ = famRho^[ku - kv] v := by rw [hkv]
    rw [hu']
    exact famRho_iterate_fix v hv (ku - kv)



/-! ## the family root and the min-value theorem -/

/-- the root quadruple r_t = gen 3 • famQuad t = (famA t, famB t, famC t, famC t). -/
def famRoot (t : ℕ) : Fin 4 → ℤ := gen 3 • famQuad t

/-- the root quadruple is in the family orbit. -/
lemma famRoot_mem (t : ℕ) : famRoot t ∈ orbitOf (famQuad t) := by
  unfold famRoot
  exact famOrbit_gen t (famQuad t) (famQuad_mem_own_orbit t) 3

/-- the root is Descartes with positive sum (from membership). -/
lemma famRoot_desc (t : ℕ) : famDesc (famRoot t) := by
  unfold famDesc
  exact famOrbit_desc t (famRoot t) (famRoot_mem t)

/-- the root has positive sum. -/
lemma famRoot_pos (t : ℕ) : 0 < famSum (famRoot t) := by
  unfold famSum
  exact (famOrbit_desc_posSum t (famRoot t) (famRoot_mem t)).2

/-- the root coordinates: (famA t, famB t, famC t, famC t). -/
lemma famRoot_coords (t : ℕ) :
    famRoot t 0 = famA t ∧ famRoot t 1 = famB t ∧ famRoot t 2 = famC t ∧
      famRoot t 3 = famC t := by
  constructor
  · unfold famRoot
    rw [gen_smul_apply]
    simp [famQuad]
  · constructor
    · unfold famRoot
      rw [gen_smul_apply]
      simp [famQuad]
    · constructor
      · unfold famRoot
        rw [gen_smul_apply]
        simp [famQuad]
      · unfold famRoot
        rw [gen_smul_apply]
        simp
        rw [famSum_except]
        unfold famSum
        rw [Fin.sum_univ_four]
        simp [famQuad, famA, famB, famC, famD]
        omega

/-- the sum of the root. -/
lemma famRoot_sum (t : ℕ) : famSum (famRoot t) = 2 * famC t + 2 := by
  unfold famSum
  rcases famRoot_coords t with ⟨h0, h1, h2, h3⟩
  rw [Fin.sum_univ_four]
  simp [h0, h1, h2, h3]
  unfold famA famB
  omega

/-- every root coordinate is at least famA t. -/
lemma famRoot_ge_a (t : ℕ) (j : Fin 4) : famA t ≤ famRoot t j := by
  rcases famRoot_coords t with ⟨h0, h1, h2, h3⟩
  fin_cases j
  · change famA t ≤ famRoot t (0 : Fin 4)
    rw [h0]
  · change famA t ≤ famRoot t (1 : Fin 4)
    rw [h1]
    unfold famA famB
    omega
  · change famA t ≤ famRoot t (2 : Fin 4)
    rw [h2]
    have hneg : famA t < 0 := famA_lt_zero t
    have hpos : 0 ≤ famC t := le_of_lt (famC_pos t)
    omega
  · change famA t ≤ famRoot t (3 : Fin 4)
    rw [h3]
    have hneg : famA t < 0 := famA_lt_zero t
    have hpos : 0 ≤ famC t := le_of_lt (famC_pos t)
    omega

/-- the root is a sink. -/
lemma famRoot_sink (t : ℕ) : famSink (famRoot t) := by
  intro i
  rcases famRoot_coords t with ⟨h0, h1, h2, h3⟩
  have hsum : famSum (famRoot t) = 2 * famC t + 2 := famRoot_sum t
  have hz : 0 ≤ (t : ℤ) := by exact_mod_cast Nat.zero_le t
  fin_cases i <;> simp [h0, h1, h2, h3, hsum, famA, famB, famC] <;>
    nlinarith [sq_nonneg (6 * (t : ℤ) + 5), hz]

/-- the minimum of the root is famA t. -/
lemma famRoot_min (t : ℕ) : famMin (famRoot t) = famA t := by
  apply le_antisymm
  · have hle0 : famMin (famRoot t) ≤ famRoot t 0 := famMin_le (famRoot t) 0
    rcases famRoot_coords t with ⟨h0, _⟩
    rwa [h0] at hle0
  · rcases famMin_attained (famRoot t) with ⟨j, hj⟩
    rw [← hj]
    exact famRoot_ge_a t j

/-- the family base reduces in one step to the root. -/
lemma famRho_base_root (t : ℕ) : famRho (famQuad t) = famRoot t := by
  unfold famRoot
  have hD : famDesc (famQuad t) := by
    unfold famDesc
    exact famOrbit_desc t (famQuad t) (famQuad_mem_own_orbit t)
  have hpos : 0 < famSum (famQuad t) := by
    unfold famSum
    exact (famOrbit_desc_posSum t (famQuad t) (famQuad_mem_own_orbit t)).2
  have hb : famBig (famQuad t) 3 := by
    unfold famBig famSum
    rw [Fin.sum_univ_four]
    simp [famQuad, famA, famB, famC, famD]
    omega
  exact famRho_eq (famQuad t) hD hpos 3 hb

/-- famDesc and positive sum along ρ-iterates. -/
lemma famRho_iterate_desc_pos (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w)
    (k : ℕ) : famDesc (famRho^[k] w) ∧ 0 < famSum (famRho^[k] w) := by
  induction k with
  | zero => exact ⟨hD, hpos⟩
  | succ k ih =>
      simpa [Function.iterate_succ_apply'] using
        (famRho_desc_pos (famRho^[k] w) ih.1 ih.2)

/-- the minimum is non-increasing along ρ-iterates. -/
lemma famMin_iterate_le (w : Fin 4 → ℤ) (hD : famDesc w) (hpos : 0 < famSum w)
    (k : ℕ) : famMin (famRho^[k] w) ≤ famMin w := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hd : famDesc (famRho^[k] w) := (famRho_iterate_desc_pos w hD hpos k).1
      have hp : 0 < famSum (famRho^[k] w) := (famRho_iterate_desc_pos w hD hpos k).2
      exact le_trans
        (by simpa [Function.iterate_succ_apply'] using (famMin_rho_le (famRho^[k] w) hd hp)) ih

/-- a generator composed with itself is the identity. -/
lemma gen_mul_self (i : Fin 4) : (gen i) * gen i = (1 : GL (Fin 4) ℤ) := by
  fin_cases i <;> decide

/-- moving twice brings orbit membership back. -/
lemma famOrbit_involutive_mem (t : ℕ) (v : Fin 4 → ℤ) (i : Fin 4)
    (h : gen i • v ∈ orbitOf (famQuad t)) : v ∈ orbitOf (famQuad t) := by
  have h2 : gen i • (gen i • v) ∈ orbitOf (famQuad t) := famOrbit_gen t (gen i • v) h i
  rw [← mul_smul] at h2
  simpa [gen_mul_self i] using h2

/-- every orbit state descends (by ρ) to the root sink. -/
theorem fam_descent_root (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (u : Fin 4 → ℤ) (hu : famSink u) (huR : ∃ k : ℕ, u = famRho^[k] w) :
    u = famRoot t := by
  -- move-closure induction: the sink reached from any orbit state equals the root
  let P : (Fin 4 → ℤ) → Prop := fun v => (v ∈ orbitOf (famQuad t)) →
    ∀ u : Fin 4 → ℤ, famSink u → (∃ k : ℕ, u = famRho^[k] v) → u = famRoot t
  have hP : P (famQuad t) := by
    intro hvq u hu huR
    -- famQuad descends to the root; both u and the root are sinks reachable from famQuad
    have hD : famDesc (famQuad t) := by
      unfold famDesc
      exact famOrbit_desc t (famQuad t) hvq
    have hpos : 0 < famSum (famQuad t) := by
      unfold famSum
      exact (famOrbit_desc_posSum t (famQuad t) hvq).2
    have hrootR : ∃ k : ℕ, famRoot t = famRho^[k] (famQuad t) := by
      refine ⟨1, ?_⟩
      simp [famRho_base_root t]
    exact sink_unique_reachable (famQuad t) hD hpos u (famRoot t) hu (famRoot_sink t) huR hrootR
  have hS : ∀ i : Fin 4, ∀ v : Fin 4 → ℤ, P v → P (gen i • v) := by
    intro i v ih hv' u hu huR
    -- membership of v (move is an involution)
    have hvm : v ∈ orbitOf (famQuad t) := famOrbit_involutive_mem t v i hv'
    have hDv : famDesc v := by
      unfold famDesc
      exact famOrbit_desc t v hvm
    have hposv : 0 < famSum v := by
      unfold famSum
      exact (famOrbit_desc_posSum t v hvm).2
    rcases sinkReach_step v hDv hposv i u hu huR with ⟨k', hk'⟩
    exact ih hvm u hu ⟨k', hk'⟩
  have hall := of_orbitOf_apply (w0 := famQuad t) (P := P) hP hS w hw
  exact hall hw u hu huR

/-- the min-value theorem: every coordinate of every orbit quadruple is ≥ famA t. -/
theorem fam_orbit_min_ge (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t)) (j : Fin 4) :
    famA t ≤ w j := by
  have hD : famDesc w := by
    unfold famDesc
    exact famOrbit_desc t w hw
  have hpos : 0 < famSum w := by
    unfold famSum
    exact (famOrbit_desc_posSum t w hw).2
  rcases sink_reachable w hD hpos with ⟨u, hus, k, hku⟩
  have hu_root : u = famRoot t := fam_descent_root t w hw u hus ⟨k, hku⟩
  have hmin : famMin (famRho^[k] w) ≤ famMin w := famMin_iterate_le w hD hpos k
  have hwj : famMin w ≤ w j := famMin_le w j
  calc
    famA t = famMin (famRoot t) := (famRoot_min t).symm
    _ = famMin u := by rw [hu_root]
    _ = famMin (famRho^[k] w) := by rw [hku]
    _ ≤ famMin w := hmin
    _ ≤ w j := hwj

/-- the min-value theorem in terms of the famQuad coordinates. -/
theorem famPacking_values_ge (t : ℕ) (v : Fin 4 → ℤ) (hv : v ∈ orbitOf (famQuad t))
    (j : Fin 4) : famA t ≤ v j :=
  fam_orbit_min_ge t v hv j

end Apollo
