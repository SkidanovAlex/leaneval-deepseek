import Mathlib
import Submission.Work.WilkiesH.Strat.SI.cellMeetThin
import Submission.Work.WilkiesH.Strat.SI.polybook
import Submission.Work.WilkiesH.Strat.dimLE_iUnion_fin
import Submission.Work.WilkiesH.Strat.omega_closure_v2
import Submission.Work.WilkiesH.Strat.rft.Assemble

/-!
# The relative frontier of a cell inside a semialgebraic set is thin

For a sharply o-minimal structure `S` (BNZ §2.1) and a cell `κ ∈ S.Ω F D n` contained in a
semialgebraic `V ∈ S.Ω F Dv n` with `DimLE V μ`, the relative frontier `κ ∩ closure (V \ κ)`
is covered by an `Ω`-set `W ⊆ κ` with `DimLE W (μ - 1)` and format/degree bounded in terms of
`(D + Dv, n + 1)`.

## The proof

`SharpCD` applied to the pair `(κ, V)` (both padded to format `F + 2` and degree
`Dmax = max D Dv`) produces a cylindrical decomposition `CD` of `ℝⁿ` compatible with `κ` and
with `V`.  With `g : Fin CD.card → Set (Fin n → ℝ)` an enumeration of `CD` put

* `P i := if g i ⊆ κ then g i else ∅`;
* `Q j := closure (if g j ⊆ V ∧ Disjoint (g j) κ then g j else ∅)`;
* `W := (⋃ i, P i) ∩ (⋃ j, Q j)`.

Then:

* `κ = ⋃ i, P i` and `closure (V \ κ) = ⋃ j, Q j`: the cells of `CD` are pairwise disjoint and
  cover `ℝⁿ` and compatibility with `κ` and `V` identifies the cells contained in `V \ κ`
  (a cell meeting `V \ κ` lies in `V` and is disjoint from `κ`), so `κ ∩ closure (V \ κ) ⊆ W`
  and `W ⊆ κ`;
* `W ∈ S.Ω a (pm.eval ![D + Dv, n + 1]) n` is bookkeeping: the cells are `Ω`-sets of format
  `a₀` and degree `≤ c₀.eval Dmax` (`SharpCD`), their closures are `Ω`-sets of format `a_cl`
  and degree `≤ q_cl.eval _` (`omega_closure_v2`), the two finite unions are charged by the
  `union` axiom (degree multiplied by `CD.card ≤ b₀.eval ![Dmax, 2]`), the intersection by
  `Omega_inter2`; the bookkeeping polynomial `pm` dominates the resulting expression;
* `DimLE W (μ - 1)`: `W = ⋃ i, ⋃ j, (P i ∩ Q j)`, and `dimLE_iUnion_fin` (applied twice,
  which is where `SharpCD` enters again) reduces this to the pieces `P i ∩ Q j`; if one of the
  two filters fails the piece is `∅`, and otherwise it is `g i ∩ closure (g j)` with `g i ≠ g j`
  and `g i ∪ g j ⊆ V`, which is `(μ - 1)`-thin by `cellMeetThin`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace Work.WilkiesH.Strat.SI

open WilkiesDesign WilkiesConjecture

/-! ## 1. Polynomial bookkeeping -/

/-- A univariate polynomial evaluated at `t` is bounded by its value at `1` times
`(t + 1) ^ natDegree`. -/
private theorem poly_eval_le_eval_one' (c : Polynomial ℕ) (t : ℕ) :
    c.eval t ≤ c.eval 1 * (t + 1) ^ c.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  conv_rhs => rw [Polynomial.eval_eq_sum_range]
  simp only [one_pow, one_mul, mul_one]
  refine le_trans (Finset.sum_le_sum fun i hi => ?_) (le_of_eq (Finset.sum_mul ..).symm)
  refine Nat.mul_le_mul_left _ ?_
  have hi' : i ≤ c.natDegree := by
    have := Finset.mem_range.mp hi
    omega
  exact le_trans (Nat.pow_le_pow_left (Nat.le_succ t) i)
    (Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) hi')

/-- A two-variable polynomial evaluated at `![t, 2]` is bounded by its value at `![1, 2]`
times `(t + 1) ^ (sum of the first exponents over the support)`. -/
private theorem mv_eval_le' (b : MvPolynomial (Fin 2) ℕ) (t : ℕ) :
    MvPolynomial.eval ![t, 2] b
      ≤ MvPolynomial.eval ![1, 2] b * (t + 1) ^ (∑ m ∈ b.support, m 0) := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq']
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, one_mul, mul_one]
  have hterm : ∀ m ∈ b.support, b.coeff m * (t ^ m 0 * 2 ^ m 1)
      ≤ b.coeff m * 2 ^ m 1 * (t + 1) ^ (∑ m' ∈ b.support, m' 0) := by
    intro m hm
    have h1 : m 0 ≤ ∑ m' ∈ b.support, m' 0 :=
      Finset.single_le_sum (f := fun m' : Fin 2 →₀ ℕ => m' 0)
        (fun i _ => Nat.zero_le _) hm
    have h2 : t ^ m 0 ≤ (t + 1) ^ (∑ m' ∈ b.support, m' 0) :=
      le_trans (Nat.pow_le_pow_left (Nat.le_succ t) _)
        (Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) h1)
    calc b.coeff m * (t ^ m 0 * 2 ^ m 1) = b.coeff m * 2 ^ m 1 * t ^ m 0 := by ring
      _ ≤ b.coeff m * 2 ^ m 1 * (t + 1) ^ (∑ m' ∈ b.support, m' 0) :=
          Nat.mul_le_mul_left _ h2
  exact le_trans (Finset.sum_le_sum hterm) (le_of_eq (Finset.sum_mul ..).symm)

/-- **The bookkeeping lemma.**  There is a fixed two-variable polynomial `pm` which dominates,
at `![D + Dv, K]`, both `D` and the degree index

`2 * b(D + Dv, 2) * (c(D + Dv) + q(c(D + Dv)) + 5) + 8`

of the union of the pieces in the proof of `cellRelFrontierThin`: the factor `b(D + Dv, 2)`
bounds the number of cells of the sharp cell decomposition, and the second factor bounds the
format/degree index of one intersection of a cell with the closure of a cell. -/
private theorem exists_pm_dominate' (b : MvPolynomial (Fin 2) ℕ) (c q : Polynomial ℕ) :
    ∃ pm : MvPolynomial (Fin 2) ℕ, ∀ D Dv K : ℕ,
      max D (2 * (MvPolynomial.eval ![(D + Dv : ℕ), 2] b) *
        (c.eval (D + Dv) + q.eval (c.eval (D + Dv)) + 5) + 8)
        ≤ MvPolynomial.eval ![(D + Dv : ℕ), K] pm := by
  set B := MvPolynomial.eval ![1, 2] b with hB
  set Bd := ∑ m ∈ b.support, m 0 with hBd
  set C := c.eval 1 with hC
  set Cd := c.natDegree with hCd
  set Q := q.eval 1 with hQ
  set Qd := q.natDegree with hQd
  set E := Bd + Cd + Cd * Qd + 1 with hE
  set N := 2 * B * (C + Q * (C + 1) ^ Qd + 5) + 8 with hN
  refine ⟨MvPolynomial.X 0 + MvPolynomial.C N * (MvPolynomial.X 0 + 1) ^ (2 * E),
    fun D Dv K => ?_⟩
  set t := D + Dv with ht
  have hX : MvPolynomial.eval ![t, K] (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) = t := by simp
  have hpow : MvPolynomial.eval ![t, K]
      ((MvPolynomial.X 0 + 1 : MvPolynomial (Fin 2) ℕ) ^ (2 * E)) = (t + 1) ^ (2 * E) := by
    rw [MvPolynomial.eval_pow, MvPolynomial.eval_add, hX]
    simp
  have hCst : MvPolynomial.eval ![t, K] (MvPolynomial.C N : MvPolynomial (Fin 2) ℕ) = N :=
    MvPolynomial.eval_C N
  have heval : MvPolynomial.eval ![t, K]
      (MvPolynomial.X 0 + MvPolynomial.C N * (MvPolynomial.X 0 + 1) ^ (2 * E))
      = t + N * (t + 1) ^ (2 * E) := by
    rw [MvPolynomial.eval_add, hX, MvPolynomial.eval_mul, hCst, hpow]
  rw [heval]
  have hmain : 2 * MvPolynomial.eval ![t, 2] b * (c.eval t + q.eval (c.eval t) + 5) + 8
      ≤ N * (t + 1) ^ (2 * E) := by
    have hb : MvPolynomial.eval ![t, 2] b ≤ B * (t + 1) ^ Bd := mv_eval_le' b t
    have hc : c.eval t ≤ C * (t + 1) ^ Cd := poly_eval_le_eval_one' c t
    have h1 : c.eval t + 1 ≤ (C + 1) * (t + 1) ^ Cd := by
      have hpos : 1 ≤ (t + 1) ^ Cd := Nat.one_le_pow _ _ (by omega)
      nlinarith [hc, hpos, Nat.zero_le C]
    have hq : q.eval (c.eval t) ≤ Q * (C + 1) ^ Qd * (t + 1) ^ (Cd * Qd) := by
      refine le_trans (poly_eval_le_eval_one' q (c.eval t)) ?_
      have hstep := Nat.pow_le_pow_left h1 Qd
      have heq : ((C + 1) * (t + 1) ^ Cd) ^ Qd = (C + 1) ^ Qd * (t + 1) ^ (Cd * Qd) := by
        rw [mul_pow, ← pow_mul]
      rw [heq] at hstep
      calc Q * (c.eval t + 1) ^ Qd ≤ Q * ((C + 1) ^ Qd * (t + 1) ^ (Cd * Qd)) :=
            Nat.mul_le_mul_left _ hstep
        _ = Q * (C + 1) ^ Qd * (t + 1) ^ (Cd * Qd) := by ring
    have hsum : c.eval t + q.eval (c.eval t) + 5
        ≤ (C + Q * (C + 1) ^ Qd + 5) * (t + 1) ^ E := by
      have hcdE : (t + 1) ^ Cd ≤ (t + 1) ^ E :=
        Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) (by omega)
      have hcqE : (t + 1) ^ (Cd * Qd) ≤ (t + 1) ^ E :=
        Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) (by omega)
      have hb1 : c.eval t ≤ C * (t + 1) ^ E := Nat.mul_le_mul_left _ hcdE |> le_trans hc
      have hb2 : q.eval (c.eval t) ≤ Q * (C + 1) ^ Qd * (t + 1) ^ E :=
        le_trans hq (Nat.mul_le_mul_left _ hcqE)
      have hb3 : 5 ≤ 5 * (t + 1) ^ E := by
        calc (5 : ℕ) = 5 * 1 := (mul_one 5).symm
          _ ≤ 5 * (t + 1) ^ E :=
              Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
      calc c.eval t + q.eval (c.eval t) + 5
          ≤ C * (t + 1) ^ E + Q * (C + 1) ^ Qd * (t + 1) ^ E + 5 * (t + 1) ^ E :=
            add_le_add (add_le_add hb1 hb2) hb3
        _ = (C + Q * (C + 1) ^ Qd + 5) * (t + 1) ^ E := by ring
    have hb' : MvPolynomial.eval ![t, 2] b ≤ B * (t + 1) ^ E :=
      le_trans hb (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) (by omega)))
    have hstep : 2 * MvPolynomial.eval ![t, 2] b * (c.eval t + q.eval (c.eval t) + 5)
        ≤ 2 * (B * (t + 1) ^ E) * ((C + Q * (C + 1) ^ Qd + 5) * (t + 1) ^ E) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hb') hsum
    have hsq : ((t + 1) ^ E) * ((t + 1) ^ E) = (t + 1) ^ (2 * E) := by
      rw [← pow_add]; ring_nf
    have h8 : 8 ≤ 8 * (t + 1) ^ (2 * E) := by
      calc (8 : ℕ) = 8 * 1 := (mul_one 8).symm
        _ ≤ 8 * (t + 1) ^ (2 * E) :=
            Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
    have hmid : 2 * (B * (t + 1) ^ E) * ((C + Q * (C + 1) ^ Qd + 5) * (t + 1) ^ E)
        = 2 * B * (C + Q * (C + 1) ^ Qd + 5) * (((t + 1) ^ E) * ((t + 1) ^ E)) := by ring
    rw [hmid, hsq] at hstep
    have hfin : 2 * B * (C + Q * (C + 1) ^ Qd + 5) * (t + 1) ^ (2 * E) + 8 * (t + 1) ^ (2 * E)
        = N * (t + 1) ^ (2 * E) := by
      rw [hN]; ring
    calc 2 * MvPolynomial.eval ![t, 2] b * (c.eval t + q.eval (c.eval t) + 5) + 8
        ≤ 2 * B * (C + Q * (C + 1) ^ Qd + 5) * ((t + 1) ^ (2 * E)) + 8 * (t + 1) ^ (2 * E) :=
          add_le_add hstep h8
      _ = N * (t + 1) ^ (2 * E) := hfin
  refine max_le ?_ ?_
  · have h1 : 1 ≤ (t + 1) ^ (2 * E) := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ N * (t + 1) ^ (2 * E) :=
      Nat.succ_le_of_lt (Nat.mul_pos (by omega) (pow_pos (by omega : 0 < t + 1) _))
    omega
  · exact le_trans hmain (Nat.le_add_left _ _)

/-! ## 2. The assembly -/

theorem cellRelFrontierThin {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) :
    ∀ F n : ℕ, ∃ (a : ℕ) (pm : MvPolynomial (Fin 2) ℕ),
      ∀ (μ D Dv : ℕ) (V κ : Set (Fin n → ℝ)),
        V ∈ S.Ω F Dv n → WilkiesConjecture.IsSemialgebraic V → WilkiesDesign.DimLE V μ →
        κ ∈ S.Ω F D n → WilkiesDesign.IsCell n κ → κ.Nonempty → κ ⊆ V →
        ∃ W : Set (Fin n → ℝ),
          W ∈ S.Ω a (MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] pm) n ∧ W ⊆ κ ∧
          WilkiesDesign.DimLE W (μ - 1) ∧ κ ∩ closure (V \ κ) ⊆ W := by
  intro F n
  obtain ⟨a₀, b₀, c₀, H⟩ := hcd (F + 2) n
  obtain ⟨acl, qcl, hcl⟩ := omega_closure_v2 (S := S) hcd a₀ n
  obtain ⟨pm, hpm⟩ := exists_pm_dominate' b₀ c₀ qcl
  refine ⟨max (max a₀ acl + 1) (n + 6) + 1, pm,
    fun μ D Dv V κ hV hVsem hVdim hκ hκcell hκne hκV => ?_⟩
  -- pad the two `Ω`-sets to a common format and degree
  set Dmax : ℕ := max D Dv with hDmax
  have hDle : Dmax ≤ D + Dv := by omega
  have hκ2 : κ ∈ S.Ω (F + 2) Dmax n :=
    Work.WilG5.mem_mono hκ (F + 2) Dmax (by omega) (le_max_left _ _)
  have hV2 : V ∈ S.Ω (F + 2) Dmax n :=
    Work.WilG5.mem_mono hV (F + 2) Dmax (by omega) (le_max_right _ _)
  -- the sharp cell decomposition of the pair `(κ, V)`
  obtain ⟨CD, hCD, hcomp, hcard, hmem⟩ :=
    H Dmax 2 (fun i : Fin 2 => ![κ, V] i) (by
      intro i
      fin_cases i
      · simpa using hκ2
      · simpa using hV2)
  -- an enumeration of the cells
  let E : Fin CD.card ≃ ↥CD :=
    (finCongr (Fintype.card_coe CD).symm).trans (Fintype.equivFin ↥CD).symm
  let g : Fin CD.card → Set (Fin n → ℝ) := fun i => (E i).1
  have hg_mem : ∀ i, g i ∈ CD := fun i => (E i).2
  have hg_surj : ∀ c ∈ CD, ∃ i, g i = c := fun c hc => ⟨E.symm ⟨c, hc⟩, by simp [g]⟩
  have hg_ne : ∀ i, (g i).Nonempty :=
    fun i => Work.WilG5.Interior.nonempty_of_isCylDecomp hCD (hg_mem i)
  have hcomp_κ : ∀ c ∈ CD, c ⊆ κ ∨ Disjoint c κ := by
    intro c hc
    have h := hcomp 0 c hc
    simpa using h
  have hcomp_V : ∀ c ∈ CD, c ⊆ V ∨ Disjoint c V := by
    intro c hc
    have h := hcomp 1 c hc
    simpa using h
  -- closure witnesses for the cells
  choose cl hcl_mem hcl_char using fun j : Fin CD.card =>
    hcl (c₀.eval Dmax) (g j) (hmem (g j) (hg_mem j))
  have hcl_eq : ∀ j, cl j = closure (g j) := by
    intro j
    have h1 : cl j = Work.WilkiesH.Strat.closureSet (g j) := by
      ext x
      rw [hcl_char j x]
      rfl
    rw [h1, Book.closureSet_eq_closure]
  -- the three filters defining the pieces
  let P : Fin CD.card → Set (Fin n → ℝ) := fun i => if g i ⊆ κ then g i else ∅
  let Q : Fin CD.card → Set (Fin n → ℝ) :=
    fun j => closure (if g j ⊆ V ∧ Disjoint (g j) κ then g j else ∅)
  let W : Set (Fin n → ℝ) := (⋃ i, P i) ∩ (⋃ j, Q j)
  have hP_sub : ∀ i, P i ⊆ κ := by
    intro i
    by_cases h : g i ⊆ κ
    · rw [show P i = g i from if_pos h]
      exact h
    · rw [show P i = (∅ : Set (Fin n → ℝ)) from if_neg h]
      exact Set.empty_subset _
  have hκ_eq : κ = ⋃ i, P i := by
    refine Set.Subset.antisymm ?_ (Set.iUnion_subset hP_sub)
    intro x hx
    obtain ⟨c, hc, hxc⟩ := Work.WilG5.Interior.cylinder_decomp_cover hCD x
    have hcκ : c ⊆ κ := (hcomp_κ c hc).resolve_right (fun hd => Set.disjoint_left.mp hd hxc hx)
    obtain ⟨i, hi⟩ := hg_surj c hc
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    have hgi : g i ⊆ κ := by rw [hi]; exact hcκ
    rw [show P i = g i from if_pos hgi]
    rwa [hi]
  have hVκ_eq : V \ κ = ⋃ j, (if g j ⊆ V ∧ Disjoint (g j) κ then g j else ∅) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxV, hxκ⟩ := hx
      obtain ⟨c, hc, hxc⟩ := Work.WilG5.Interior.cylinder_decomp_cover hCD x
      have hcV : c ⊆ V :=
        (hcomp_V c hc).resolve_right (fun hd => Set.disjoint_left.mp hd hxc hxV)
      have hcdisj : Disjoint c κ := by
        by_contra hnd
        rw [Set.not_disjoint_iff] at hnd
        obtain ⟨y, hyc, hyκ⟩ := hnd
        rcases hcomp_κ c hc with hs | hd
        · exact hxκ (hs hxc)
        · exact Set.disjoint_left.mp hd hyc hyκ
      obtain ⟨j, hj⟩ := hg_surj c hc
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      have hcond : g j ⊆ V ∧ Disjoint (g j) κ := by
        rw [hj]; exact ⟨hcV, hcdisj⟩
      rw [if_pos hcond, hj]
      exact hxc
    · intro x hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      by_cases hcond : g j ⊆ V ∧ Disjoint (g j) κ
      · rw [if_pos hcond] at hxj
        exact ⟨hcond.1 hxj, fun hxκ => Set.disjoint_left.mp hcond.2 hxj hxκ⟩
      · rw [if_neg hcond] at hxj
        exact absurd hxj (Set.notMem_empty x)
  have hclVκ : closure (V \ κ) = ⋃ j, Q j := by
    rw [hVκ_eq]
    rw [closure_iUnion_of_finite
      (f := fun j : Fin CD.card => if g j ⊆ V ∧ Disjoint (g j) κ then g j else ∅)]
  -- the structural properties of `W`
  have hWsub : W ⊆ κ := by
    intro x hx
    obtain ⟨hx1, _⟩ := hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx1
    exact hP_sub i hi
  have hWcover : κ ∩ closure (V \ κ) ⊆ W := by
    intro x hx
    obtain ⟨hxκ, hxcl⟩ := hx
    rw [hκ_eq] at hxκ
    rw [hclVκ] at hxcl
    exact ⟨hxκ, hxcl⟩
  -- format/degree bookkeeping
  set FP : ℕ := max a₀ (n + 6) with hFP
  set DP : ℕ := max (c₀.eval Dmax) 4 with hDP
  set FQ : ℕ := max acl (n + 6) with hFQ
  set DQ : ℕ := max (qcl.eval (c₀.eval Dmax)) 4 with hDQ
  have hPmem : ∀ i, P i ∈ S.Ω FP DP n := by
    intro i
    by_cases h : g i ⊆ κ
    · rw [show P i = g i from if_pos h]
      refine Work.WilG5.mem_mono (hmem (g i) (hg_mem i)) FP DP ?_ ?_
      · rw [hFP]; exact le_max_left _ _
      · rw [hDP]; exact le_max_left _ _
    · rw [show P i = (∅ : Set (Fin n → ℝ)) from if_neg h]
      refine Work.WilG5.mem_mono (Work.WilG5.empty_mem (S := S) (n := n)) FP DP ?_ ?_
      · rw [hFP]; exact le_max_right _ _
      · rw [hDP]; exact le_max_right _ _
  have hQmem : ∀ j, Q j ∈ S.Ω FQ DQ n := by
    intro j
    by_cases hcond : g j ⊆ V ∧ Disjoint (g j) κ
    · have hQj : Q j = closure (g j) := by simp only [Q, if_pos hcond]
      rw [hQj, ← hcl_eq j]
      refine Work.WilG5.mem_mono (hcl_mem j) FQ DQ ?_ ?_
      · rw [hFQ]; exact le_max_left _ _
      · rw [hDQ]; exact le_max_left _ _
    · have hQj : Q j = (∅ : Set (Fin n → ℝ)) := by
        simp only [Q, if_neg hcond, closure_empty]
      rw [hQj]
      refine Work.WilG5.mem_mono (Work.WilG5.empty_mem (S := S) (n := n)) FQ DQ ?_ ?_
      · rw [hFQ]; exact le_max_right _ _
      · rw [hDQ]; exact le_max_right _ _
  have hPun_mem : (⋃ i, P i) ∈ S.Ω FP (CD.card * DP) n := by
    have h := S.union (fun _ : Fin CD.card => DP) P hPmem
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
  have hQun_mem : (⋃ j, Q j) ∈ S.Ω FQ (CD.card * DQ) n := by
    have h := S.union (fun _ : Fin CD.card => DQ) Q hQmem
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
  have hFF : FP ≤ max FP FQ := le_max_left _ _
  have hGG : FQ ≤ max FP FQ := le_max_right _ _
  have hWmem0 : W ∈ S.Ω (max FP FQ + 1) (CD.card * DP + CD.card * DQ) n :=
    Work.WilG0.Omega_inter2
      (Work.WilG5.mem_mono hPun_mem (max FP FQ) (CD.card * DP) hFF le_rfl)
      (Work.WilG5.mem_mono hQun_mem (max FP FQ) (CD.card * DQ) hGG le_rfl)
  have hcardB : CD.card ≤ MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ := by
    have h1 : CD.card ≤ MvPolynomial.eval ![Dmax, 2] b₀ := hcard
    refine le_trans h1 (Book.mv_nat_eval_mono (b := b₀) ?_)
    intro i
    fin_cases i <;> simp [hDle]
  have hcE : c₀.eval Dmax ≤ c₀.eval (D + Dv) := Book.poly_nat_eval_mono (p := c₀) hDle
  have hqE : qcl.eval (c₀.eval Dmax) ≤ qcl.eval (c₀.eval (D + Dv)) :=
    Book.poly_nat_eval_mono (p := qcl) hcE
  have hWmem : W ∈ S.Ω (max (max a₀ acl + 1) (n + 6) + 1)
      (MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] pm) n := by
    refine Work.WilG5.mem_mono hWmem0 _ _ ?_ ?_
    · -- format
      have ha₀ : a₀ ≤ max (max a₀ acl + 1) (n + 6) :=
        le_trans (le_trans (le_max_left a₀ acl) (Nat.le_succ _)) (le_max_left _ _)
      have hacl : acl ≤ max (max a₀ acl + 1) (n + 6) :=
        le_trans (le_trans (le_max_right a₀ acl) (Nat.le_succ _)) (le_max_left _ _)
      have hn : n + 6 ≤ max (max a₀ acl + 1) (n + 6) := le_max_right _ _
      have hmax : max FP FQ ≤ max (max a₀ acl + 1) (n + 6) := by
        rw [hFP, hFQ]
        exact max_le (max_le ha₀ hn) (max_le hacl hn)
      exact Nat.succ_le_succ hmax
    · -- degree
      have hDDP : DP ≤ c₀.eval (D + Dv) + 4 := by
        rw [hDP]; exact max_le (by omega) (by omega)
      have hDDQ : DQ ≤ qcl.eval (c₀.eval (D + Dv)) + 4 := by
        rw [hDQ]; exact max_le (by omega) (by omega)
      have hdeg1 : CD.card * DP ≤
          MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ * (c₀.eval (D + Dv) + 4) :=
        Nat.mul_le_mul hcardB hDDP
      have hdeg2 : CD.card * DQ ≤
          MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ * (qcl.eval (c₀.eval (D + Dv)) + 4) :=
        Nat.mul_le_mul hcardB hDDQ
      have hfin : CD.card * DP + CD.card * DQ ≤
          2 * MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ *
            (c₀.eval (D + Dv) + qcl.eval (c₀.eval (D + Dv)) + 5) + 8 := by
        have h1 : CD.card * DP + CD.card * DQ ≤
            MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ *
              (c₀.eval (D + Dv) + qcl.eval (c₀.eval (D + Dv)) + 8) := by
          calc CD.card * DP + CD.card * DQ
              ≤ MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ * (c₀.eval (D + Dv) + 4) +
                MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ * (qcl.eval (c₀.eval (D + Dv)) + 4) :=
                add_le_add hdeg1 hdeg2
            _ = MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ *
                  (c₀.eval (D + Dv) + qcl.eval (c₀.eval (D + Dv)) + 8) := by ring
        refine le_trans h1 ?_
        calc MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ *
              (c₀.eval (D + Dv) + qcl.eval (c₀.eval (D + Dv)) + 8)
            = MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ *
                (c₀.eval (D + Dv) + qcl.eval (c₀.eval (D + Dv)) + 5) +
              MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ * 3 := by ring
          _ ≤ MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ *
                (c₀.eval (D + Dv) + qcl.eval (c₀.eval (D + Dv)) + 5) +
              MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ *
                (c₀.eval (D + Dv) + qcl.eval (c₀.eval (D + Dv)) + 5) :=
              Nat.add_le_add_left
                (Nat.mul_le_mul_left _ (by omega :
                  3 ≤ c₀.eval (D + Dv) + qcl.eval (c₀.eval (D + Dv)) + 5)) _
          _ = 2 * MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ *
                (c₀.eval (D + Dv) + qcl.eval (c₀.eval (D + Dv)) + 5) := by ring
          _ ≤ 2 * MvPolynomial.eval ![(D + Dv : ℕ), 2] b₀ *
                (c₀.eval (D + Dv) + qcl.eval (c₀.eval (D + Dv)) + 5) + 8 :=
              Nat.le_add_right _ _
      exact le_trans hfin (le_trans (le_max_right _ _) (hpm D Dv (n + 1)))
  refine ⟨W, hWmem, hWsub, ?_, hWcover⟩
  -- the dimension bound
  have hpair_mem : ∀ i j, (P i ∩ Q j) ∈ S.Ω (max FP FQ + 1) (DP + DQ) n := by
    intro i j
    exact Work.WilG0.Omega_inter2
      (Work.WilG5.mem_mono (hPmem i) (max FP FQ) DP hFF le_rfl)
      (Work.WilG5.mem_mono (hQmem j) (max FP FQ) DQ hGG le_rfl)
  have hpair_dim : ∀ i j, WilkiesDesign.DimLE (P i ∩ Q j) (μ - 1) := by
    intro i j
    by_cases hi : g i ⊆ κ
    · have hPi : P i = g i := by simp only [P, if_pos hi]
      by_cases hj : g j ⊆ V ∧ Disjoint (g j) κ
      · have hQj : Q j = closure (g j) := by simp only [Q, if_pos hj]
        rw [hPi, hQj]
        refine cellMeetThin (S := S) (FD := a₀) (FE := a₀)
          (DD := c₀.eval Dmax) (DE := c₀.eval Dmax)
          hcd hVsem hVdim hCD (hg_mem i) (hg_mem j) ?_ ?_ ?_
          (hmem (g i) (hg_mem i)) (hmem (g j) (hg_mem j))
        · intro hEq
          obtain ⟨y, hy⟩ := hg_ne i
          exact Set.disjoint_left.mp hj.2 (hEq ▸ hy) (hi hy)
        · exact fun y hy => hκV (hi hy)
        · exact hj.1
      · have hQj : Q j = (∅ : Set (Fin n → ℝ)) := by
          simp only [Q, if_neg hj, closure_empty]
        rw [hPi, hQj, Set.inter_empty]
        intro e
        rw [Set.image_empty, interior_empty]
    · have hPi : P i = (∅ : Set (Fin n → ℝ)) := by simp only [P, if_neg hi]
      rw [hPi, Set.empty_inter]
      intro e
      rw [Set.image_empty, interior_empty]
  have hdim_inner : ∀ i,
      WilkiesDesign.DimLE (Set.iUnion (fun j : Fin CD.card => (P i ∩ Q j))) (μ - 1) := fun i =>
    dimLE_iUnion_fin (S := S) hcd (A := fun j : Fin CD.card => P i ∩ Q j)
      (fun j => hpair_mem i j) (fun j => hpair_dim i j)
  have hinner_mem : ∀ i,
      Set.iUnion (fun j : Fin CD.card => (P i ∩ Q j)) ∈
        S.Ω (max FP FQ + 1) (CD.card * (DP + DQ)) n := by
    intro i
    have h := S.union (fun _ : Fin CD.card => DP + DQ) (fun j => P i ∩ Q j) (hpair_mem i)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
  have hWeq : W = Set.iUnion (fun i : Fin CD.card =>
      Set.iUnion (fun j : Fin CD.card => (P i ∩ Q j))) := by
    have hset : W = Set.iUnion (fun i : Fin CD.card => P i) ∩
        Set.iUnion (fun j : Fin CD.card => Q j) := rfl
    rw [hset]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
      exact ⟨i, j, hi, hj⟩
    · intro h
      obtain ⟨i, j, hi, hj⟩ := h
      exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  rw [hWeq]
  exact dimLE_iUnion_fin (S := S) hcd
    (A := fun i : Fin CD.card => Set.iUnion (fun j : Fin CD.card => (P i ∩ Q j)))
    hinner_mem hdim_inner

end Work.WilkiesH.Strat.SI
