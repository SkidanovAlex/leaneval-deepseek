import Submission.AdjustedCheb
import Submission.Bclps
import Submission.ChebSerre
import Submission.DivLinear
import Submission.CompQNums

/-!
# The complementary polynomial (single-interval form of Smith's `defn:comp_Q`)

adjust.tex, Definition `defn:comp_Q` + the "even coefficients / pigeonhole /
norm" content of its paragraph.  Input: a real monic polynomial `P` of degree
`n ≥ 1` and an integer `r ≥ 2`.  Output: the data

    T   (the `lem:Bclps` polynomial for `P`: monic degree `r`, close to
         `T̃ = AdjustedCheb.prunedPoly r` pointwise within `κ^r/64` on the
         Serre interval, `T^D·P` even-integer at degrees `[n+(D−1)r, n+Dr−1]`),
    Q0  = ∏_{j'<D} (T − C(factorCenter r j'))        (monic degree Dr),
    eps : ℕ → ℝ   (each `eps t ∈ [0,2)`, slope-1 forcing downward),
    Q1  = Q0 + Σ_{1≤t≤d} C(eps t)·auxPoly t,
    N ≥ 0  (pigeonhole),  Q = Q1 + C N,

with the properties used downstream:
* `Q` monic of degree `Dr`; `P·Q` has even-integer coefficients at all degrees
  `[n+1, n+Dr−1]`;
* the pigeonhole lower bound `|Q(α)| ≥ n⁻¹·C2⁻¹·κ^{Dr}` at every root `α` of `P`
  (`eq:pigeonhole_space`);
* the sup-norm bound `‖Q‖ ≤ (r+n+2)^C·κ^{Dr}`.

The root-location (`lem:comp_Q_roots`) and norm/derivative/local-growth bounds
(`lem:comp_Q_roots2`) are separate modules that take this data as hypotheses.
-/

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.CompQ

open Submission.SerreExample
open Submission.ChebSerre
open Submission.AdjustedCheb
open Submission.Bclps
open Submission.DivLinear
open Submission.CompQNums

/-- the polynomial degree `d = (D−1)·r` of `Q0 − T^D` (range of the eps auxiliaries). -/
def d (r : ℕ) : ℕ := (Bclps.Dconst - 1) * r

/-- `Q0 = ∏_{j'<D} (T − C(c_{r,j'}))` (monic degree `Dr`). -/
noncomputable def q0poly (r : ℕ) (T : Polynomial ℝ) : Polynomial ℝ :=
  ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j'))

/-- the ε-forcing recursion states: `compState u` has fixed the coefficients at
degrees `n + d − i` for `i < u`. -/
noncomputable def compState (P T : Polynomial ℝ) (r n : ℕ) : ℕ → Polynomial ℝ
  | 0 => q0poly r T
  | u + 1 =>
      if _hu : u < d r then
        compState P T r n u +
          Polynomial.C (evenLam 1 ((P * compState P T r n u).coeff (n + d r - u))) *
            Bclps.auxPoly (d r - u)
      else compState P T r n u

/-- the chosen ε coefficients (in `[0,2)`, so that `P·Q1` has even integer
coefficients at the degrees `n+t`, `1 ≤ t ≤ d`). -/
noncomputable def epsChoice (P T : Polynomial ℝ) (r n : ℕ) (t : ℕ) : ℝ :=
  if _ht : t ∈ Finset.Icc 1 (d r) then
    evenLam 1 ((P * compState P T r n (d r - t)).coeff (n + t))
  else 0

/-- `Q1 = Q0 + Σ_{t=1}^{d} ε_t·auxPoly t`. -/
noncomputable def q1poly (P T : Polynomial ℝ) (r n : ℕ) : Polynomial ℝ :=
  compState P T r n (d r)

/-- `compState` at zero. -/
lemma compState_zero (P T : Polynomial ℝ) (r n : ℕ) :
    compState P T r n 0 = q0poly r T := rfl

/-- `compState` successor step. -/
lemma compState_succ (P T : Polynomial ℝ) (r n u : ℕ) :
    compState P T r n (u + 1) =
      if u < d r then
        compState P T r n u +
          C (evenLam 1 ((P * compState P T r n u).coeff (n + d r - u))) *
            auxPoly (d r - u)
      else compState P T r n u := rfl

/-- subtracting a constant from a monic polynomial of positive degree keeps it monic. -/
lemma monic_sub_C {f : Polynomial ℝ} {a : ℝ} (hf : f.Monic) (hdeg : 1 ≤ f.natDegree) :
    (f - C a).Monic := by
  rw [Polynomial.Monic.def] at hf ⊢
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_sub_C]
  rw [Polynomial.coeff_sub, Polynomial.coeff_C]
  have hfdeg : f.natDegree ≠ 0 := by omega
  simp [hf, hfdeg]

/-- every factor of `Q0` is monic of degree `r`. -/
lemma q0_factor_monic_deg {r : ℕ} (hr : 1 ≤ r) {T : Polynomial ℝ} (hT : T.Monic)
    (hTd : T.natDegree = r) (j' : ℕ) (hj' : j' ∈ Finset.range Bclps.Dconst) :
    (T - C (factorCenter r j')).Monic ∧ (T - C (factorCenter r j')).natDegree = r := by
  constructor
  · exact monic_sub_C hT (by rw [hTd]; exact hr)
  · rw [Polynomial.natDegree_sub_C, hTd]

/-- `Q0` is monic of degree `D·r`. -/
lemma q0poly_monic_deg (r : ℕ) (hr : 1 ≤ r) {T : Polynomial ℝ} (hT : T.Monic)
    (hTd : T.natDegree = r) :
    (q0poly r T).Monic ∧ (q0poly r T).natDegree = Bclps.Dconst * r := by
  have hfac : ∀ j' ∈ Finset.range Bclps.Dconst, (T - C (factorCenter r j')).Monic := by
    intro j' hj'
    exact (q0_factor_monic_deg hr hT hTd j' hj').1
  constructor
  · unfold q0poly
    exact Polynomial.monic_prod_of_monic (Finset.range Bclps.Dconst)
      (fun j' => T - C (factorCenter r j')) hfac
  · unfold q0poly
    calc
      (∏ j' ∈ Finset.range Bclps.Dconst, (T - C (factorCenter r j'))).natDegree
          = ∑ j' ∈ Finset.range Bclps.Dconst, (T - C (factorCenter r j')).natDegree :=
              Polynomial.natDegree_prod_of_monic _ _ hfac
      _ = ∑ _j' ∈ Finset.range Bclps.Dconst, r := by
            apply Finset.sum_congr rfl
            intro j' hj'
            rw [Polynomial.natDegree_sub_C, hTd]
      _ = Bclps.Dconst * r := by
            rw [Finset.sum_const, Finset.card_range]
            ring

/-- every state of the recursion is monic of degree `Dr`. -/
lemma compState_monic_deg (P T : Polynomial ℝ) (r n : ℕ) (hr : 1 ≤ r) (hT : T.Monic)
    (hTd : T.natDegree = r) :
    ∀ u : ℕ, (compState P T r n u).Monic ∧ (compState P T r n u).natDegree = Bclps.Dconst * r := by
  intro u
  induction' u with u ih
  · exact q0poly_monic_deg r hr hT hTd
  · rw [compState_succ]
    by_cases hu : u < d r
    · rw [if_pos hu]
      have hD1 : 1 ≤ Bclps.Dconst := Bclps.Dconst_pos
      have hdlt : d r < Bclps.Dconst * r := by
        unfold d
        have hDm : Bclps.Dconst * r = (Bclps.Dconst - 1) * r + r := by
          rw [show Bclps.Dconst = (Bclps.Dconst - 1) + 1 by omega]
          rw [add_mul]
          simp
        rw [hDm]
        omega
      have hlow : (auxPoly (d r - u)).natDegree < (compState P T r n u).natDegree := by
        rw [auxPoly_natDegree, ih.2]
        exact lt_of_le_of_lt (Nat.sub_le (d r) u) hdlt
      have hc : (C (evenLam 1 ((P * compState P T r n u).coeff (n + d r - u))) *
          auxPoly (d r - u)).natDegree < (compState P T r n u).natDegree := by
        calc
          (C (evenLam 1 ((P * compState P T r n u).coeff (n + d r - u))) *
              auxPoly (d r - u)).natDegree
              ≤ (C (evenLam 1 ((P * compState P T r n u).coeff (n + d r - u)))).natDegree +
                  (auxPoly (d r - u)).natDegree := Polynomial.natDegree_mul_le
          _ = (auxPoly (d r - u)).natDegree := by rw [Polynomial.natDegree_C, zero_add]
          _ < (compState P T r n u).natDegree := hlow
      have hm := Bclps.monic_add_lower ih.1 hc
      exact ⟨hm.1, by rw [hm.2, ih.2]⟩
    · rw [if_neg hu]
      exact ih


/-! ## ε forcing: coefficients of `P·(compState j)` at the band degrees -/

/-- top coefficient of a product of monic polynomials is `1`. -/
lemma coeff_monic_mul_top {A S : Polynomial ℝ} {a n : ℕ} (hAm : A.Monic)
    (hAd : A.natDegree = a) (hSm : S.Monic) (hSd : S.natDegree = n) :
    (A * S).coeff (n + a) = 1 := by
  have hprod : (A * S).Monic := hAm.mul hSm
  have hdeg : (A * S).natDegree = n + a := by
    rw [Polynomial.Monic.natDegree_mul hAm hSm, hAd, hSd]
    omega
  rw [← hdeg, Polynomial.coeff_natDegree]
  exact hprod.leadingCoeff

/-- coefficient of `P·A` above `deg P + deg A` vanishes. -/
lemma coeff_mul_lower_eq_zero {P A : Polynomial ℝ} {n m k : ℕ}
    (hPdeg : P.natDegree ≤ n) (hAdeg : A.natDegree ≤ m) (hk : n + m < k) :
    (P * A).coeff k = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  calc
    (P * A).natDegree ≤ P.natDegree + A.natDegree := Polynomial.natDegree_mul_le
    _ ≤ n + m := Nat.add_le_add hPdeg hAdeg
    _ < k := hk

/-- `evenLam 1 c` turns `c + λ` into an even integer. -/
lemma evenLam_add_even (c : ℝ) : ∃ z : ℤ, c + evenLam 1 c = (z : ℝ) ∧ Even z := by
  refine ⟨2 * Int.ceil (c / 2), ?_, ?_⟩
  · have h := (evenLam_props (D := 1) (by norm_num) c).2.2
    simpa [Int.cast_mul] using h
  · exact ⟨Int.ceil (c / 2), by ring⟩

/-- `ε_t ∈ [0,2)` at the used indices. -/
lemma epsChoice_mem (P T : Polynomial ℝ) (r n t : ℕ) (ht : t ∈ Finset.Icc 1 (d r)) :
    0 ≤ epsChoice P T r n t ∧ epsChoice P T r n t < 2 := by
  unfold epsChoice
  rw [dif_pos ht]
  rcases evenLam_props (D := 1) (by norm_num)
    ((P * compState P T r n (d r - t)).coeff (n + t)) with ⟨h0, h2, h3⟩
  exact ⟨h0, by simpa using h2⟩

/-- value of `ε` at the step index `u < d`: it is the λ used at that step. -/
lemma epsChoice_step (P T : Polynomial ℝ) (r n u : ℕ) (hu : u < d r) :
    epsChoice P T r n (d r - u) =
      evenLam 1 ((P * compState P T r n u).coeff (n + d r - u)) := by
  unfold epsChoice
  rw [dif_pos]
  · congr 1
    rw [Nat.sub_sub_self (le_of_lt hu)]
    have hsub : n + d r - u = n + (d r - u) := by omega
    rw [hsub]
  · rw [Finset.mem_Icc]
    constructor <;> omega

/-- the recursion step at `u < d` adds exactly the ε-term. -/
lemma compState_succ_eps (P T : Polynomial ℝ) (r n u : ℕ) (hu : u < d r) :
    compState P T r n (u + 1) = compState P T r n u +
      C (epsChoice P T r n (d r - u)) * auxPoly (d r - u) := by
  rw [compState_succ, if_pos hu]
  rw [epsChoice_step P T r n u hu]

/-- the step at `u` makes the coefficient at degree `n + d − u` an even integer. -/
lemma compState_step_fixes {P T : Polynomial ℝ} {r n u : ℕ}
    (hPm : P.Monic) (hPd : P.natDegree = n) (hu : u < d r) :
    ∃ z : ℤ, (P * compState P T r n (u + 1)).coeff (n + d r - u) = (z : ℝ) ∧ Even z := by
  let m := d r - u
  rw [compState_succ_eps P T r n u hu]
  have hstep : (P * (compState P T r n u + C (epsChoice P T r n m) * auxPoly m)).coeff
      (n + d r - u) =
      (P * compState P T r n u).coeff (n + d r - u) + epsChoice P T r n m := by
    rw [mul_add, coeff_add]
    congr 1
    rw [show P * (C (epsChoice P T r n m) * auxPoly m) =
        C (epsChoice P T r n m) * (P * auxPoly m) by ring]
    rw [coeff_C_mul]
    have hm' : n + d r - u = n + m := by
      dsimp [m]
      omega
    rw [hm']
    rw [show P * auxPoly m = auxPoly m * P by ring]
    rw [coeff_monic_mul_top (A := auxPoly m) (S := P) (auxPoly_monic m) (auxPoly_natDegree m)
      hPm hPd]
    ring
  rw [hstep]
  have heps : epsChoice P T r n m = evenLam 1 ((P * compState P T r n u).coeff (n + d r - u)) := by
    dsimp [m]
    exact epsChoice_step P T r n u hu
  rw [heps]
  exact evenLam_add_even ((P * compState P T r n u).coeff (n + d r - u))

/-- the step at `u` does not touch coefficients below `n + d − u`. -/
lemma compState_step_preserves {P T : Polynomial ℝ} {r n u i : ℕ}
    (hPm : P.Monic) (hPd : P.natDegree = n) (hu : u < d r) (hi : i < u) :
    (P * compState P T r n (u + 1)).coeff (n + d r - i) =
      (P * compState P T r n u).coeff (n + d r - i) := by
  let m := d r - u
  rw [compState_succ_eps P T r n u hu]
  rw [mul_add, coeff_add]
  have hzero : (P * (C (epsChoice P T r n m) * auxPoly m)).coeff (n + d r - i) = 0 := by
    rw [show P * (C (epsChoice P T r n m) * auxPoly m) =
        C (epsChoice P T r n m) * (P * auxPoly m) by ring]
    rw [coeff_C_mul]
    have hzero' : (P * auxPoly m).coeff (n + d r - i) = 0 := by
      apply coeff_mul_lower_eq_zero (P := P) (A := auxPoly m) (n := n) (m := m)
      · exact le_of_eq hPd
      · exact le_of_eq (auxPoly_natDegree m)
      · dsimp [m]
        omega
    rw [hzero', mul_zero]
  rw [hzero, add_zero]

/-- after `j` steps the coefficients at degrees `n+d−i`, `i < j`, are even integers. -/
lemma compState_even {P T : Polynomial ℝ} {r n : ℕ}
    (hPm : P.Monic) (hPd : P.natDegree = n) :
    ∀ j : ℕ, j ≤ d r → ∀ i : ℕ, i < j →
      ∃ z : ℤ, (P * compState P T r n j).coeff (n + d r - i) = (z : ℝ) ∧ Even z := by
  intro j
  induction' j with j ih
  · intro hj i hi
    omega
  · intro hj1 i hi
    have hjd : j < d r := by omega
    have hj_le : j ≤ d r := le_of_lt hjd
    by_cases hij : i = j
    · subst i
      exact compState_step_fixes (hPm := hPm) (hPd := hPd) (u := j) hjd
    · have hi' : i < j := by omega
      rcases ih hj_le i hi' with ⟨z, hz⟩
      refine ⟨z, ?_, hz.2⟩
      rw [compState_step_preserves (hPm := hPm) (hPd := hPd) (u := j) (i := i) hjd hi']
      exact hz.1


/-- the states are `Q0` plus the partial ε-sums. -/
lemma compState_step_eq (P T : Polynomial ℝ) (r n : ℕ) :
    ∀ u : ℕ, u ≤ d r → compState P T r n u = q0poly r T +
      (∑ i ∈ Finset.range u, C (epsChoice P T r n (d r - i)) * auxPoly (d r - i)) := by
  intro u
  induction' u with u ih
  · intro hu
    rw [compState_zero]
    simp
  · intro hus
    have hu_le : u ≤ d r := by omega
    have hu : u < d r := by omega
    rw [compState_succ_eps P T r n u hu]
    rw [ih hu_le]
    rw [Finset.sum_range_succ]
    ring

/-- reindex a sum over `range d` through `t = d − i` into `Icc 1 d`. -/
lemma sum_range_to_Icc (d : ℕ) (f : ℕ → Polynomial ℝ) :
    (∑ i ∈ Finset.range d, f (d - i)) = ∑ t ∈ Finset.Icc 1 d, f t := by
  by_cases hd : d = 0
  · subst d
    simp
  · have hd1 : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd)
    refine Finset.sum_bij (fun i hi => d - i) ?hi ?inj ?surj ?h
    · intro i hi
      rw [Finset.mem_Icc]
      have hi' : i < d := Finset.mem_range.mp hi
      constructor <;> omega
    · intro a₁ ha₁ a₂ ha₂ h
      have ha₁' : a₁ < d := Finset.mem_range.mp ha₁
      have ha₂' : a₂ < d := Finset.mem_range.mp ha₂
      omega
    · intro t ht
      rw [Finset.mem_Icc] at ht
      refine ⟨d - t, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · omega
    · intro i hi
      rfl

/-- `Q1 = Q0 + Σ_{t=1}^{d} ε_t·auxPoly t`. -/
lemma q1poly_eq_sum (P T : Polynomial ℝ) (r n : ℕ) :
    q1poly P T r n = q0poly r T +
      (∑ t ∈ Finset.Icc 1 (d r), C (epsChoice P T r n t) * auxPoly t) := by
  unfold q1poly
  rw [compState_step_eq P T r n (d r) (le_rfl)]
  congr 1
  rw [sum_range_to_Icc (d r) (fun t => C (epsChoice P T r n t) * auxPoly t)]

/-- `∏_{j<m}(T − C c_j) − T^m` has degree at most `(m−1)·r`. -/
lemma prod_sub_pow_natDegree {r m : ℕ} {T : Polynomial ℝ} (hT : T.Monic)
    (hTd : T.natDegree = r) (hr : 1 ≤ r) (c : ℕ → ℝ) :
    ((∏ j ∈ Finset.range m, (T - C (c j))) - T ^ m).natDegree ≤ (m - 1) * r := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        have h : (∏ j ∈ Finset.range 1, (T - C (c j))) - T ^ 1 = -C (c 0) := by
          rw [Finset.prod_range_succ]
          ring_nf
        rw [h]
        simp
      · have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
        let S : Polynomial ℝ := ∏ j ∈ Finset.range m, (T - C (c j))
        have hR : (S - T ^ m).natDegree ≤ (m - 1) * r := by
          simpa [S] using ih
        have heq : (∏ j ∈ Finset.range (m + 1), (T - C (c j))) - T ^ (m + 1) =
            (S - T ^ m) * (T - C (c m)) - C (c m) * T ^ m := by
          rw [Finset.prod_range_succ]
          rw [show S = T ^ m + (S - T ^ m) by ring]
          rw [pow_succ]
          ring
        calc
          ((∏ j ∈ Finset.range (m + 1), (T - C (c j))) - T ^ (m + 1)).natDegree
              = ((S - T ^ m) * (T - C (c m)) - C (c m) * T ^ m).natDegree := by rw [heq]
          _ ≤ max ((S - T ^ m) * (T - C (c m))).natDegree (C (c m) * T ^ m).natDegree :=
              Polynomial.natDegree_sub_le _ _
          _ ≤ m * r := by
              apply max_le
              · calc
                  ((S - T ^ m) * (T - C (c m))).natDegree
                      ≤ (S - T ^ m).natDegree + (T - C (c m)).natDegree :=
                          Polynomial.natDegree_mul_le
                  _ ≤ (m - 1) * r + r := by
                      apply Nat.add_le_add hR
                      rw [Polynomial.natDegree_sub_C, hTd]
                  _ ≤ m * r := by
                      have heq' : (m - 1) * r + r = m * r := by
                        have hsub : (m - 1) + 1 = m := by omega
                        calc
                          (m - 1) * r + r = (m - 1) * r + 1 * r := by ring
                          _ = ((m - 1) + 1) * r := by rw [← add_mul]
                          _ = m * r := by rw [hsub]
                      exact le_of_eq heq'
              · calc
                  (C (c m) * T ^ m).natDegree
                      ≤ (C (c m)).natDegree + (T ^ m).natDegree := Polynomial.natDegree_mul_le
                  _ = m * r := by
                      rw [Polynomial.natDegree_C, Polynomial.natDegree_pow, hTd]
                      simp
                  _ ≤ m * r := le_rfl
          _ = ((m + 1) - 1) * r := by
              rw [show (m + 1) - 1 = m by omega]


/-- `d r + 1 ≤ D·r` for `r ≥ 1`. -/
lemma d_add_one_le (r : ℕ) (hr : 1 ≤ r) : d r + 1 ≤ Bclps.Dconst * r := by
  have hD1 : 1 ≤ Bclps.Dconst := Bclps.Dconst_pos
  dsimp [d]
  have hsum : Bclps.Dconst * r = (Bclps.Dconst - 1) * r + r := by
    rw [show Bclps.Dconst = (Bclps.Dconst - 1) + 1 by omega]
    rw [add_mul]
    simp
  rw [hsum]
  omega

/-- `κ − 1 ≥ 1/16`. -/
lemma kappa_sub_one_ge : (1 / 16 : ℝ) ≤ kappaC - 1 := by
  unfold kappaC
  norm_num [aSerre, bSerre]

/-- `C2val ≥ 8`. -/
lemma C2val_ge_eight : (8 : ℝ) ≤ C2val := by
  dsimp [C2val, D]
  have hD1 : (1 : ℝ) ≤ (Bclps.Dconst : ℝ) := by exact_mod_cast Bclps.Dconst_pos
  have hbase : (1 : ℝ) ≤ 128 * (Bclps.Dconst : ℝ) := by nlinarith
  have hpow : (1 : ℝ) ≤ (128 * (Bclps.Dconst : ℝ)) ^ Bclps.Dconst := one_le_pow₀ hbase
  nlinarith

/-! ## the pigeonhole choice of `N` -/

/-- for one root, at most one candidate `k` is "bad". -/
lemma bad_k_unique {q1 B : ℝ} (hB : 0 < B) {k1 k2 : ℕ} (hk : k1 ≠ k2) :
    ¬(|q1 + (2 * (k1 : ℝ)) * B| < B ∧ |q1 + (2 * (k2 : ℝ)) * B| < B) := by
  intro h
  have hmain : ∀ {a b : ℕ}, a < b →
      ¬(|q1 + (2 * (a : ℝ)) * B| < B ∧ |q1 + (2 * (b : ℝ)) * B| < B) := by
    intro a b hab hbad
    have htri0 : |(q1 + (2 * (a : ℝ)) * B) + (-(q1 + (2 * (b : ℝ)) * B))| ≤
        |q1 + (2 * (a : ℝ)) * B| + |q1 + (2 * (b : ℝ)) * B| := by
      calc
        |(q1 + (2 * (a : ℝ)) * B) + (-(q1 + (2 * (b : ℝ)) * B))|
            ≤ |q1 + (2 * (a : ℝ)) * B| + |-(q1 + (2 * (b : ℝ)) * B)| := abs_add_le _ _
        _ = |q1 + (2 * (a : ℝ)) * B| + |q1 + (2 * (b : ℝ)) * B| := by rw [abs_neg]
    have htri : |(q1 + (2 * (a : ℝ)) * B) - (q1 + (2 * (b : ℝ)) * B)| ≤
        |q1 + (2 * (a : ℝ)) * B| + |q1 + (2 * (b : ℝ)) * B| := by
      rw [sub_eq_add_neg]
      exact htri0
    have hsumlt : |q1 + (2 * (a : ℝ)) * B| + |q1 + (2 * (b : ℝ)) * B| < 2 * B := by
      nlinarith [hbad.1, hbad.2]
    have hlt : |(q1 + (2 * (a : ℝ)) * B) - (q1 + (2 * (b : ℝ)) * B)| < 2 * B :=
      lt_of_le_of_lt htri hsumlt
    have hge : 2 * B ≤ |(q1 + (2 * (a : ℝ)) * B) - (q1 + (2 * (b : ℝ)) * B)| := by
      have hdiff : (q1 + (2 * (a : ℝ)) * B) - (q1 + (2 * (b : ℝ)) * B) =
          -((2 * ((b : ℝ) - (a : ℝ))) * B) := by ring
      rw [hdiff, abs_neg]
      have hnonneg : 0 ≤ (2 * ((b : ℝ) - (a : ℝ))) * B := by
        have hsub0 : 0 ≤ (b : ℝ) - (a : ℝ) := by
          have hleR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast (le_of_lt hab)
          linarith
        positivity
      rw [abs_of_nonneg hnonneg]
      have hk1 : 1 ≤ (b : ℝ) - (a : ℝ) := by
        have hb : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hab)
        linarith
      nlinarith
    nlinarith
  by_cases hlt : k1 < k2
  · exact hmain hlt h
  · have hgt : k2 < k1 := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) hk.symm
    exact hmain hgt ⟨h.2, h.1⟩

/-- existence of a good candidate: some `k ≤ n` keeps every root at distance ≥ `B`. -/
lemma good_candidate_exists {n : ℕ} {B : ℝ} (hB : 0 < B)
    (S : Finset ℝ) (hScard : S.card ≤ n) (q1 : ℝ → ℝ) :
    ∃ k : ℕ, k ≤ n ∧ ∀ α : ℝ, α ∈ S → B ≤ |q1 α + (2 * (k : ℝ)) * B| := by
  by_contra hnot
  have hbad : ∀ k : ℕ, k ≤ n → ∃ α : ℝ, α ∈ S ∧ |q1 α + (2 * (k : ℝ)) * B| < B := by
    intro k hk
    by_contra hb
    apply hnot
    refine ⟨k, hk, ?_⟩
    intro α hα
    by_contra hle
    exact hb ⟨α, hα, lt_of_not_ge hle⟩
  let g : ℕ → ℝ := fun k => if hk : k ≤ n then Classical.choose (hbad k hk) else 0
  have hg : ∀ k : ℕ, k ≤ n → g k ∈ S ∧ |q1 (g k) + (2 * (k : ℝ)) * B| < B := by
    intro k hk
    dsimp [g]
    rw [dif_pos hk]
    exact Classical.choose_spec (hbad k hk)
  have hinjOn : Set.InjOn g (↑(Finset.range (n + 1)) : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a < n + 1 := by simpa using ha
    have hb' : b < n + 1 := by simpa using hb
    by_contra hne
    have hval : a ≠ b := by
      intro hv
      exact hne hv
    have hga : g a ∈ S ∧ |q1 (g a) + (2 * (a : ℝ)) * B| < B := hg a (by omega)
    have hgb : g b ∈ S ∧ |q1 (g b) + (2 * (b : ℝ)) * B| < B := hg b (by omega)
    have hq : |q1 (g a) + (2 * (b : ℝ)) * B| < B := by
      simpa [hab] using hgb.2
    exact bad_k_unique (q1 := q1 (g a)) hB hval ⟨hga.2, hq⟩
  have hTcard : (Finset.image g (Finset.range (n + 1))).card = n + 1 := by
    rw [Finset.card_image_of_injOn hinjOn]
    simp
  have hsub : Finset.image g (Finset.range (n + 1)) ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    have hk' : k < n + 1 := Finset.mem_range.mp hk
    exact (hg k (by omega)).1
  have hle : n + 1 ≤ S.card := by
    calc
      n + 1 = (Finset.image g (Finset.range (n + 1))).card := hTcard.symm
      _ ≤ S.card := Finset.card_le_card hsub
  omega


/-! ## pointwise sup-norm bounds for `Q` -/

/-- `|Q0(x)|` on the interval: each factor is ≤ `2M·κ^r` pointwise. -/
lemma q0poly_ptwise_le {r : ℕ} {T : Polynomial ℝ} {M : ℝ} (hM1 : (1 : ℝ) ≤ M)
    (hT : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |T.eval x| ≤ M * kappaC ^ r) :
    ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      |(q0poly r T).eval x| ≤ (2 * M) ^ Bclps.Dconst * kappaC ^ (Bclps.Dconst * r) := by
  intro x hx
  unfold q0poly
  rw [Polynomial.eval_prod]
  calc
    |∏ j' ∈ Finset.range Bclps.Dconst, (T - C (factorCenter r j')).eval x|
        = ∏ j' ∈ Finset.range Bclps.Dconst,
            |(T - C (factorCenter r j')).eval x| := Finset.abs_prod _ _
    _ ≤ ∏ j' ∈ Finset.range Bclps.Dconst, (2 * M * kappaC ^ r) := by
        apply Finset.prod_le_prod
        · intro j' hj'
          exact abs_nonneg _
        · intro j' hj'
          have hj'lt : j' < Bclps.Dconst := Finset.mem_range.mp hj'
          have hc_lt : factorCenter r j' < kappaC ^ r / 64 := factor_center_lt hj'lt
          have hc_le : factorCenter r j' ≤ kappaC ^ r / 64 := le_of_lt hc_lt
          have hcpos : 0 ≤ factorCenter r j' := le_of_lt (factorCenter_pos r j')
          have hmain : |(T - C (factorCenter r j')).eval x| ≤
              |T.eval x| + factorCenter r j' := by
            have heval : (T - C (factorCenter r j')).eval x =
                T.eval x - factorCenter r j' := by simp
            rw [heval, sub_eq_add_neg]
            calc
              |T.eval x + -factorCenter r j'| ≤ |T.eval x| + |-factorCenter r j'| :=
                  abs_add_le _ _
              _ = |T.eval x| + |factorCenter r j'| := by rw [abs_neg]
              _ = |T.eval x| + factorCenter r j' := by rw [abs_of_nonneg hcpos]
          calc
            |(T - C (factorCenter r j')).eval x| ≤ |T.eval x| + factorCenter r j' := hmain
            _ ≤ M * kappaC ^ r + kappaC ^ r / 64 := by
                have h1 := hT x hx
                linarith
            _ = (M + 1 / 64) * kappaC ^ r := by ring
            _ ≤ (2 * M) * kappaC ^ r := by
                have hM16 : (1 / 64 : ℝ) ≤ M := by
                  calc (1 / 64 : ℝ) ≤ 1 := by norm_num
                    _ ≤ M := hM1
                nlinarith
    _ = (2 * M * kappaC ^ r) ^ Bclps.Dconst := by
        rw [Finset.prod_const, Finset.card_range]
    _ = (2 * M) ^ Bclps.Dconst * (kappaC ^ r) ^ Bclps.Dconst := by
        rw [mul_pow]
    _ = (2 * M) ^ Bclps.Dconst * kappaC ^ (Bclps.Dconst * r) := by
        have hp : (kappaC ^ r) ^ Bclps.Dconst = kappaC ^ (Bclps.Dconst * r) := by
          rw [← pow_mul]
          rw [Nat.mul_comm r Bclps.Dconst]
        rw [hp]

/-- `|(Σ ε_t·auxPoly t)(x)| ≤ 4κ^{Dr}/(κ−1)` pointwise. -/
lemma eps_part_ptwise_le {r n : ℕ} (hr : 1 ≤ r) {P T : Polynomial ℝ} :
    ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      |(∑ t ∈ Finset.Icc 1 (d r), C (epsChoice P T r n t) * auxPoly t).eval x| ≤
        4 * kappaC ^ (Bclps.Dconst * r) / (kappaC - 1) := by
  intro x hx
  rw [Polynomial.eval_finsetSum]
  calc
    |∑ t ∈ Finset.Icc 1 (d r), (C (epsChoice P T r n t) * auxPoly t).eval x|
        ≤ ∑ t ∈ Finset.Icc 1 (d r), |(C (epsChoice P T r n t) * auxPoly t).eval x| :=
            Finset.abs_sum_le_sum_abs (fun t => (C (epsChoice P T r n t) * auxPoly t).eval x)
              (Finset.Icc 1 (d r))
    _ ≤ ∑ t ∈ Finset.Icc 1 (d r), 4 * kappaC ^ t := by
        apply Finset.sum_le_sum
        intro t ht
        have heps : 0 ≤ epsChoice P T r n t ∧ epsChoice P T r n t < 2 :=
          epsChoice_mem P T r n t ht
        have haux : |(auxPoly t).eval x| ≤ 2 * kappaC ^ t := by
          exact le_trans (DivLinear.abs_eval_le_supNorm (P := auxPoly t) x hx)
            (auxPoly_supNorm_le t)
        calc
          |(C (epsChoice P T r n t) * auxPoly t).eval x|
              = |epsChoice P T r n t| * |(auxPoly t).eval x| := by
                  rw [Polynomial.eval_C_mul]
                  exact abs_mul _ _
          _ ≤ 2 * (2 * kappaC ^ t) := by
              have hepsa : |epsChoice P T r n t| ≤ 2 := by
                rw [abs_of_nonneg heps.1]
                exact le_of_lt heps.2
              exact mul_le_mul hepsa haux (abs_nonneg _) (by positivity)
          _ = 4 * kappaC ^ t := by ring
    _ ≤ 4 * kappaC ^ (d r + 1) / (kappaC - 1) := by
        have hsub : Finset.Icc 1 (d r) ⊆ Finset.range (d r + 1) := by
          intro t ht
          rw [Finset.mem_range]
          rw [Finset.mem_Icc] at ht
          omega
        calc
          (∑ t ∈ Finset.Icc 1 (d r), 4 * kappaC ^ t)
              ≤ ∑ t ∈ Finset.range (d r + 1), 4 * kappaC ^ t := by
                  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
                    intro t ht hnt
                    exact mul_nonneg (by norm_num) (pow_nonneg (le_of_lt kappaC_pos') t))
          _ ≤ 4 * kappaC ^ (d r + 1) / (kappaC - 1) := geom4 (d r + 1)
    _ ≤ 4 * kappaC ^ (Bclps.Dconst * r) / (kappaC - 1) := by
        have hdl : d r + 1 ≤ Bclps.Dconst * r := d_add_one_le r hr
        have hk : kappaC ^ (d r + 1) ≤ kappaC ^ (Bclps.Dconst * r) :=
          pow_le_pow_right₀ kappaC_ge_one hdl
        have hpos : 0 ≤ 4 / (kappaC - 1) := by
          exact div_nonneg (by norm_num) (le_of_lt kappaC_sub_one_pos)
        calc
          4 * kappaC ^ (d r + 1) / (kappaC - 1) = (4 / (kappaC - 1)) * kappaC ^ (d r + 1) := by ring
          _ ≤ (4 / (kappaC - 1)) * kappaC ^ (Bclps.Dconst * r) := by
              exact mul_le_mul_of_nonneg_left hk hpos
          _ = 4 * kappaC ^ (Bclps.Dconst * r) / (kappaC - 1) := by ring


/-- `Q0 − T^D` has degree at most `d`. -/
lemma q0poly_sub_pow_natDegree {r : ℕ} (hr : 1 ≤ r) {T : Polynomial ℝ} (hT : T.Monic)
    (hTd : T.natDegree = r) :
    (q0poly r T - T ^ Bclps.Dconst).natDegree ≤ d r := by
  unfold q0poly d
  exact prod_sub_pow_natDegree hT hTd hr (fun j => factorCenter r j)

/-- the ε-correction sum has degree at most `d`. -/
lemma epsSum_natDegree_le (P T : Polynomial ℝ) (r n : ℕ) :
    (∑ t ∈ Finset.Icc 1 (d r), C (epsChoice P T r n t) * auxPoly t).natDegree ≤ d r := by
  calc
    (∑ t ∈ Finset.Icc 1 (d r), C (epsChoice P T r n t) * auxPoly t).natDegree
        ≤ Finset.fold max 0 (fun t => (C (epsChoice P T r n t) * auxPoly t).natDegree)
            (Finset.Icc 1 (d r)) := Polynomial.natDegree_sum_le _ _
    _ ≤ d r := by
        rw [Finset.fold_max_le]
        constructor
        · exact Nat.zero_le (d r)
        · intro t ht
          calc
            (C (epsChoice P T r n t) * auxPoly t).natDegree
                ≤ (C (epsChoice P T r n t)).natDegree + (auxPoly t).natDegree :=
                    Polynomial.natDegree_mul_le
            _ = t := by rw [Polynomial.natDegree_C, zero_add, auxPoly_natDegree]
            _ ≤ d r := by
                rw [Finset.mem_Icc] at ht
                exact ht.2


/-- `T` from `lem:Bclps`, with an explicit polynomial factor `(r+n+2)^16`. -/
lemma compq_T (r n : ℕ) (hr : 2 ≤ r) {S : Polynomial ℝ}
    (hSmon : S.Monic) (hSdeg : S.natDegree = n) :
    ∃ T : Polynomial ℝ,
      T.Monic ∧ T.natDegree = r ∧
      (∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |T.eval x| ≤ ((r + n + 2 : ℕ) : ℝ) ^ 16 * kappaC ^ r) ∧
      (∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |T.eval x - (prunedPoly r).eval x| ≤ kappaC ^ r / 64) ∧
      (∀ i : Fin (r + 1),
        (bracketPoint r i ∈ Set.Icc aSerre bSerre) ∧
        (prunedPoly r).eval (bracketPoint r i) ≠ 0 ∧
        0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i) ∧
        |T.eval (bracketPoint r i)| ≥ |(prunedPoly r).eval (bracketPoint r i)| / 2) ∧
      (∀ k : ℕ, n + (Bclps.Dconst - 1) * r ≤ k → k ≤ n + Bclps.Dconst * r - 1 →
        ∃ z : ℤ, ((T ^ Bclps.Dconst) * S).coeff k = (z : ℝ) ∧ Even z) := by
  let T := qseq r n Bclps.Dconst S (prunedPoly r) r
  have hD : 1 ≤ Bclps.Dconst := Bclps.Dconst_pos
  have hr1 : 1 ≤ r := by omega
  have hTmon : T.Monic := (qseq_monic_deg r n Bclps.Dconst hD hr1 hSmon hSdeg
    (prunedPoly_monic r) (prunedPoly_natDegree r) r (le_rfl)).1
  have hTdeg : T.natDegree = r := (qseq_monic_deg r n Bclps.Dconst hD hr1 hSmon hSdeg
    (prunedPoly_monic r) (prunedPoly_natDegree r) r (le_rfl)).2
  refine ⟨T, hTmon, hTdeg, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hclose : |T.eval x - (prunedPoly r).eval x| ≤ kappaC ^ r / 64 := by
      simpa [T] using (qseq_final_close hr hSmon hSdeg x hx)
    have hpr := prunedPoly_bound r hr hx
    have htri : |T.eval x| ≤ |(prunedPoly r).eval x| + |T.eval x - (prunedPoly r).eval x| := by
      calc |T.eval x| = |(prunedPoly r).eval x + (T.eval x - (prunedPoly r).eval x)| := by
            congr 1
            ring
        _ ≤ |(prunedPoly r).eval x| + |T.eval x - (prunedPoly r).eval x| := abs_add_le _ _
    have htri2 : |T.eval x| ≤ |(prunedPoly r).eval x| + kappaC ^ r / 64 := by
      have hadd := add_le_add_left hclose (|(prunedPoly r).eval x|)
      have hadd' : |(prunedPoly r).eval x| + |T.eval x - (prunedPoly r).eval x| ≤
          |(prunedPoly r).eval x| + kappaC ^ r / 64 := by
        simpa [add_comm, add_assoc, add_left_comm] using hadd
      exact le_trans htri hadd'
    have htri3 : |T.eval x| ≤ ((r : ℝ) + 3) ^ 6 * kappaC ^ r + kappaC ^ r / 64 := by
      have hadd := add_le_add_left hpr (kappaC ^ r / 64)
      exact le_trans htri2 hadd
    have hkp1 : (1 : ℝ) ≤ kappaC ^ r := kappaC_pow_ge_one r
    have hmain1 : ((r : ℝ) + 3) ^ 6 * kappaC ^ r + kappaC ^ r / 64 ≤
        (((r : ℝ) + 3) ^ 6 + 1) * kappaC ^ r := by
      nlinarith [hkp1]
    have hmain2 : |T.eval x| ≤ (((r : ℝ) + 3) ^ 6 + 1) * kappaC ^ r := by
      exact le_trans htri3 hmain1
    have hpb := poly_base_bound r n hr
    exact le_trans hmain2 (mul_le_mul_of_nonneg_right hpb (le_of_lt (kappaC_pow_pos r)))
  · intro x hx
    simpa [T] using (qseq_final_close hr hSmon hSdeg x hx)
  · intro i
    have hyIcc : bracketPoint r i ∈ Set.Icc aSerre bSerre := bracketPoint_mem_Icc r i
    have hclose : |T.eval (bracketPoint r i) - (prunedPoly r).eval (bracketPoint r i)| ≤
        kappaC ^ r / 64 := by
      simpa [T] using (qseq_final_close hr hSmon hSdeg (bracketPoint r i) hyIcc)
    have hlow : (kappaC ^ r) / 32 ≤ |(prunedPoly r).eval (bracketPoint r i)| :=
      pruned_bracket_lower r hr i
    have hpos : 0 < kappaC ^ r := kappaC_pow_pos r
    have hbabs : 0 < |(prunedPoly r).eval (bracketPoint r i)| := by
      have h32 : (0 : ℝ) < kappaC ^ r / 32 := by nlinarith
      exact lt_of_lt_of_le h32 hlow
    have hbne0 : (prunedPoly r).eval (bracketPoint r i) ≠ 0 := abs_pos.mp hbabs
    have hB2 : 2 * (kappaC ^ r / 64) ≤ |(prunedPoly r).eval (bracketPoint r i)| := by
      have : 2 * (kappaC ^ r / 64) = kappaC ^ r / 32 := by ring
      rwa [this]
    have hcs := close_sign_half (a := T.eval (bracketPoint r i))
      (b := (prunedPoly r).eval (bracketPoint r i)) (B := kappaC ^ r / 64) hbne0 hclose hB2
    exact ⟨hyIcc, hbne0, hcs.1, hcs.2⟩
  · intro k hklo hkhi
    have hDr : Bclps.Dconst * r = (Bclps.Dconst - 1) * r + r := by
      have hD1 : Bclps.Dconst = (Bclps.Dconst - 1) + 1 := by omega
      calc Bclps.Dconst * r = ((Bclps.Dconst - 1) + 1) * r := by
            conv_lhs => rw [hD1]
        _ = (Bclps.Dconst - 1) * r + r := by rw [add_mul, one_mul]
    have hkhi2 : k ≤ n + (Bclps.Dconst - 1) * r + r - 1 := by
      have hrew : n + Bclps.Dconst * r - 1 = n + (Bclps.Dconst - 1) * r + r - 1 := by
        rw [hDr]
        omega
      rwa [hrew] at hkhi
    let s : ℕ := k - (n + (Bclps.Dconst - 1) * r)
    have hs_lt : s < r := by
      dsimp [s]
      omega
    have hks' : k = bandIndex r n Bclps.Dconst s := by
      dsimp [s, bandIndex]
      omega
    have hband := qseq_fixed_band r n Bclps.Dconst hD hr1 hSmon hSdeg
      (prunedPoly_monic r) (prunedPoly_natDegree r) r (le_rfl) s (by dsimp [s]; omega) hs_lt
    rcases hband with ⟨z, hz⟩
    refine ⟨2 * z, ?_, ?_⟩
    · have hz' : ((qseq r n Bclps.Dconst S (prunedPoly r) r ^ Bclps.Dconst) * S).coeff k =
        2 * (z : ℝ) := by
        rw [hks']
        exact hz
      rw [hz']
      have hcast : (((2 * z : ℤ) : ℝ)) = 2 * (z : ℝ) := by
        rw [Int.cast_mul]
        norm_num
      rw [← hcast]
    · exact ⟨z, by ring⟩

/-- sup-norm bound of the constructed `Q = Q1 + C N`. -/
lemma q_supnorm_bound {r n : ℕ} (hr : 2 ≤ r) {P T : Polynomial ℝ}
    (hPm : P.Monic) (hPd : P.natDegree = n) {base : ℝ} (hbase4 : (4 : ℝ) ≤ base)
    (hT : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |T.eval x| ≤ base ^ 16 * kappaC ^ r)
    {N : ℝ} (hN0 : 0 ≤ N)
    (hNle : N ≤ 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r)) :
    DivLinear.supNorm (q1poly P T r n + C N) ≤
      base ^ (17 * Bclps.Dconst + 2) * kappaC ^ (Bclps.Dconst * r) := by
  have hbase1 : (1 : ℝ) ≤ base := le_trans (by norm_num) hbase4
  have hbase2 : (2 : ℝ) ≤ base := le_trans (by norm_num : (2 : ℝ) ≤ 4) hbase4
  have hbase0 : 0 ≤ base := le_trans (by norm_num : (0 : ℝ) ≤ 1) hbase1
  have hM1 : (1 : ℝ) ≤ base ^ 16 := one_le_pow₀ hbase1
  have hr1 : 1 ≤ r := by omega
  have hD1n : 1 ≤ Bclps.Dconst := Bclps.Dconst_pos
  -- coefficient absorptions
  have h2M : 2 * base ^ 16 ≤ base ^ 17 := by
    have hb17 : base * base ^ 16 = base ^ 17 := by
      rw [show base ^ 17 = base ^ 16 * base by
        rw [show (17 : ℕ) = 16 + 1 by norm_num, pow_succ]]
      rw [mul_comm]
    rw [← hb17]
    exact mul_le_mul_of_nonneg_right hbase2 (pow_nonneg hbase0 16)
  have hprodpow : (2 * base ^ 16) ^ Bclps.Dconst ≤ base ^ (17 * Bclps.Dconst) := by
    have hp : (base ^ 17) ^ Bclps.Dconst = base ^ (17 * Bclps.Dconst) := by
      rw [← pow_mul]
    calc
      (2 * base ^ 16) ^ Bclps.Dconst ≤ (base ^ 17) ^ Bclps.Dconst :=
          pow_le_pow_left₀ (by positivity) h2M Bclps.Dconst
      _ = base ^ (17 * Bclps.Dconst) := hp
  have hbig : (256 : ℝ) ≤ base ^ (17 * Bclps.Dconst) := by
    have h17 : 4 ≤ 17 * Bclps.Dconst := by omega
    have h1 : base ^ 4 ≤ base ^ (17 * Bclps.Dconst) := pow_le_pow_right₀ hbase1 h17
    have h2 : (4 : ℝ) ^ 4 ≤ base ^ 4 := pow_le_pow_left₀ (by norm_num) hbase4 4
    calc
      (256 : ℝ) = (4 : ℝ) ^ 4 := by norm_num
      _ ≤ base ^ 4 := h2
      _ ≤ base ^ (17 * Bclps.Dconst) := h1
  have hc2 : 4 / (kappaC - 1) ≤ base ^ (17 * Bclps.Dconst) := by
    have hk16 : (1 / 16 : ℝ) ≤ kappaC - 1 := kappa_sub_one_ge
    have hkpos : 0 < kappaC - 1 := kappaC_sub_one_pos
    have h16pos : 0 < (1 / 16 : ℝ) := by norm_num
    have hinv : (kappaC - 1)⁻¹ ≤ 16 := by
      have hi := (inv_le_inv₀ hkpos h16pos).2 hk16
      simpa using hi
    have hc : 4 / (kappaC - 1) ≤ 64 := by
      calc
        4 / (kappaC - 1) = 4 * (kappaC - 1)⁻¹ := by ring
        _ ≤ 4 * 16 := by
            exact mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = 64 := by norm_num
    exact le_trans hc (by nlinarith [hbig])
  have hc3 : 2 * C2val⁻¹ ≤ base ^ (17 * Bclps.Dconst) := by
    have h8 : (8 : ℝ) ≤ C2val := C2val_ge_eight
    have hC2pos : 0 < C2val := C2val_pos
    have h8pos : 0 < (8 : ℝ) := by norm_num
    have hinv : C2val⁻¹ ≤ (8 : ℝ)⁻¹ := by
      exact (inv_le_inv₀ hC2pos h8pos).2 h8
    have hc : 2 * C2val⁻¹ ≤ 1 / 4 := by
      calc
        2 * C2val⁻¹ ≤ 2 * (8 : ℝ)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = 1 / 4 := by norm_num
    exact le_trans hc (by nlinarith [hbig])
  rw [DivLinear.supNorm_le_iff]
  intro x hx
  let epsSum : Polynomial ℝ := ∑ t ∈ Finset.Icc 1 (d r), C (epsChoice P T r n t) * auxPoly t
  have hq1e : q1poly P T r n = q0poly r T + epsSum := by
    dsimp [epsSum]
    exact q1poly_eq_sum P T r n
  have hQ0 : |(q0poly r T).eval x| ≤ (2 * base ^ 16) ^ Bclps.Dconst * kappaC ^ (Bclps.Dconst * r) :=
    q0poly_ptwise_le (M := base ^ 16) hM1 hT x hx
  have heps : |epsSum.eval x| ≤ 4 * kappaC ^ (Bclps.Dconst * r) / (kappaC - 1) := by
    dsimp [epsSum]
    exact eps_part_ptwise_le (r := r) (n := n) hr1 x hx
  have habs1 : |(q1poly P T r n).eval x| ≤ |(q0poly r T).eval x| + |epsSum.eval x| := by
    rw [hq1e]
    rw [Polynomial.eval_add]
    exact abs_add_le _ _
  have hNabs : |N| = N := abs_of_nonneg hN0
  have hmain : |(q1poly P T r n + C N).eval x| ≤ |(q0poly r T).eval x| + |epsSum.eval x| + N := by
    have h1 : |(q1poly P T r n + C N).eval x| ≤ |(q1poly P T r n).eval x| + |N| := by
      rw [Polynomial.eval_add]
      simp
      exact abs_add_le _ _
    have h2 : |(q1poly P T r n).eval x| + |N| ≤ |(q0poly r T).eval x| + |epsSum.eval x| + N := by
      rw [hNabs]
      nlinarith [habs1]
    exact le_trans h1 h2
  -- combine
  have hb1 : (2 * base ^ 16) ^ Bclps.Dconst * kappaC ^ (Bclps.Dconst * r) ≤
      base ^ (17 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) := by
    exact mul_le_mul_of_nonneg_right hprodpow
      (pow_nonneg (le_of_lt kappaC_pos') (Bclps.Dconst * r))
  have hb2 : 4 * kappaC ^ (Bclps.Dconst * r) / (kappaC - 1) ≤
      base ^ (17 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) := by
    have hk0 : 0 ≤ kappaC ^ (Bclps.Dconst * r) := pow_nonneg (le_of_lt kappaC_pos') _
    calc
      4 * kappaC ^ (Bclps.Dconst * r) / (kappaC - 1)
          = (4 / (kappaC - 1)) * kappaC ^ (Bclps.Dconst * r) := by ring
      _ ≤ base ^ (17 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) := by
          exact mul_le_mul_of_nonneg_right hc2 hk0
  have hb3 : N ≤ base ^ (17 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) := by
    have hk0 : 0 ≤ kappaC ^ (Bclps.Dconst * r) := pow_nonneg (le_of_lt kappaC_pos') _
    calc
      N ≤ 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := hNle
      _ = (2 * C2val⁻¹) * kappaC ^ (Bclps.Dconst * r) := by ring
      _ ≤ base ^ (17 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) := by
          exact mul_le_mul_of_nonneg_right hc3 hk0
  have hb2pow : base ^ 2 ≤ base ^ (17 * Bclps.Dconst + 2) := by
    rw [pow_add]
    calc
      base ^ 2 = 1 * base ^ 2 := by ring
      _ ≤ base ^ (17 * Bclps.Dconst) * base ^ 2 := by
          exact mul_le_mul_of_nonneg_right (one_le_pow₀ hbase1) (pow_nonneg hbase0 2)
  have h3le : 3 * base ^ (17 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) ≤
      base ^ (17 * Bclps.Dconst + 2) * kappaC ^ (Bclps.Dconst * r) := by
    have hx0 : 0 ≤ base ^ (17 * Bclps.Dconst) := pow_nonneg hbase0 _
    have hk0 : 0 ≤ kappaC ^ (Bclps.Dconst * r) := pow_nonneg (le_of_lt kappaC_pos') _
    have h3b2 : (3 : ℝ) ≤ base ^ 2 := by
      have h42 : (4 : ℝ) ^ 2 ≤ base ^ 2 := pow_le_pow_left₀ (by norm_num) hbase4 2
      exact le_trans (by norm_num : (3 : ℝ) ≤ (4 : ℝ) ^ 2) h42
    rw [pow_add]
    calc
      3 * base ^ (17 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r)
          = (3 * base ^ (17 * Bclps.Dconst)) * kappaC ^ (Bclps.Dconst * r) := by ring
      _ ≤ (base ^ 2 * base ^ (17 * Bclps.Dconst)) * kappaC ^ (Bclps.Dconst * r) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3b2 hx0) hk0
      _ = base ^ (17 * Bclps.Dconst) * base ^ 2 * kappaC ^ (Bclps.Dconst * r) := by ring
  -- assemble
  have hQ0b : |(q0poly r T).eval x| ≤ base ^ (17 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) :=
    le_trans hQ0 hb1
  have hepsb : |epsSum.eval x| ≤ base ^ (17 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) :=
    le_trans heps hb2
  let Bm : ℝ := base ^ (17 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r)
  have htmp1 : |(q0poly r T).eval x| + |epsSum.eval x| ≤ Bm + Bm := by
    dsimp [Bm]
    exact add_le_add hQ0b hepsb
  have htmp2 : |(q0poly r T).eval x| + |epsSum.eval x| + N ≤ (Bm + Bm) + Bm := by
    dsimp [Bm]
    exact add_le_add htmp1 hb3
  have hthree : |(q1poly P T r n + C N).eval x| ≤
      base ^ (17 * Bclps.Dconst + 2) * kappaC ^ (Bclps.Dconst * r) := by
    calc
      |(q1poly P T r n + C N).eval x| ≤ |(q0poly r T).eval x| + |epsSum.eval x| + N := hmain
      _ ≤ (Bm + Bm) + Bm := htmp2
      _ = 3 * Bm := by ring
      _ = 3 * base ^ (17 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) := by
          dsimp [Bm]
          ring
      _ ≤ base ^ (17 * Bclps.Dconst + 2) * kappaC ^ (Bclps.Dconst * r) := h3le
  exact hthree


/-- **Complementary polynomial**: existence of the full construction data with
the defining properties and the output properties.  (This is the content of
`defn:comp_Q`; each clause mirrors a line of the paper.) -/
theorem comp_q (r n : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) {P : Polynomial ℝ}
    (hPm : P.Monic) (hPd : P.natDegree = n) :
    ∃ C : ℝ, 0 < C ∧
    ∃ T Q0 Q1 Q : Polynomial ℝ, ∃ eps : ℕ → ℝ, ∃ N : ℝ,
      T.Monic ∧ T.natDegree = r ∧
      (∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
        |T.eval x - (prunedPoly r).eval x| ≤ kappaC ^ r / 64) ∧
      (∀ i : Fin (r + 1),
        0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i) ∧
        |T.eval (bracketPoint r i)| ≥ kappaC ^ r / 64) ∧
      (∀ k : ℕ, n + (Bclps.Dconst - 1) * r ≤ k → k ≤ n + Bclps.Dconst * r - 1 →
        ∃ z : ℤ, ((T ^ Bclps.Dconst) * P).coeff k = (z : ℝ) ∧ Even z) ∧
      Q0 = ∏ j' ∈ Finset.range Bclps.Dconst,
            (T - Polynomial.C (factorCenter r j')) ∧
      Q1 = Q0 + (∑ t ∈ Finset.Icc 1 (d r),
            Polynomial.C (eps t) * Bclps.auxPoly t) ∧
      Q = Q1 + Polynomial.C N ∧
      (∀ t : ℕ, t ∈ Finset.Icc 1 (d r) → 0 ≤ eps t ∧ eps t < 2) ∧
      0 ≤ N ∧ N ≤ 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ∧
      Q.Monic ∧ Q.natDegree = Bclps.Dconst * r ∧
      (∀ k : ℕ, n + 1 ≤ k → k ≤ n + Bclps.Dconst * r - 1 →
        ∃ z : ℤ, (P * Q).coeff k = (z : ℝ) ∧ Even z) ∧
      (∀ α : ℝ, P.eval α = 0 →
        |Q.eval α| ≥ (n : ℝ)⁻¹ * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r)) ∧
      DivLinear.supNorm Q ≤ (r + n + 2) ^ C * kappaC ^ (Bclps.Dconst * r) := by
  let Nexp : ℕ := 17 * Bclps.Dconst + 2
  let base : ℝ := (r : ℝ) + (n : ℝ) + 2
  have hNexp_pos : 0 < Nexp := by
    dsimp [Nexp]
    have hD1 : 1 ≤ Bclps.Dconst := Bclps.Dconst_pos
    omega
  rcases (compq_T r n hr hPm hPd) with
    ⟨T, hTmon, hTdeg, hTnorm16, hTclose, hTbracket, hTforce⟩
  have hTbracket_forall : ∀ i : Fin (r + 1),
      0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i) ∧
      |T.eval (bracketPoint r i)| ≥ kappaC ^ r / 64 := by
    intro i
    rcases (hTbracket i) with ⟨hyIcc, hprne, hsign, hmag⟩
    constructor
    · exact hsign
    · calc
        kappaC ^ r / 64 = (kappaC ^ r / 32) / 2 := by ring
        _ ≤ |(prunedPoly r).eval (bracketPoint r i)| / 2 := by
            exact div_le_div_of_nonneg_right (pruned_bracket_lower r hr i) (by norm_num)
        _ ≤ |T.eval (bracketPoint r i)| := hmag
  have hr1 : 1 ≤ r := by omega
  let Q0 : Polynomial ℝ := q0poly r T
  let eps : ℕ → ℝ := epsChoice P T r n
  let Q1 : Polynomial ℝ := q1poly P T r n
  let S : Finset ℝ := (P.roots).toFinset
  have hPne : P ≠ 0 := hPm.ne_zero
  have hScard : S.card ≤ n := by
    dsimp [S]
    calc
      (P.roots).toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le P.roots
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = n := hPd
  let B : ℝ := (n : ℝ)⁻¹ * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r)
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hBpos : 0 < B := by
    dsimp [B]
    exact mul_pos (mul_pos (inv_pos.mpr hnR) (inv_pos.mpr C2val_pos))
      (pow_pos kappaC_pos' (Bclps.Dconst * r))
  rcases (good_candidate_exists (B := B) hBpos S hScard (fun α => Q1.eval α)) with
    ⟨k, hk, hgood⟩
  let N : ℝ := (2 * (k : ℝ)) * B
  let Q : Polynomial ℝ := Q1 + Polynomial.C N
  have hNnonneg : 0 ≤ N := by
    dsimp [N]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    have hB0 : 0 ≤ B := le_of_lt hBpos
    nlinarith
  have hNle : N ≤ 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
    dsimp [N, B]
    have hk' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    have hnn : (n : ℝ) * (n : ℝ)⁻¹ = 1 := by
      exact mul_inv_cancel₀ (ne_of_gt hnR)
    have hnn0 : 0 ≤ (n : ℝ)⁻¹ * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by positivity
    have hstep : (2 * (k : ℝ)) * ((n : ℝ)⁻¹ * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r)) ≤
        (2 * (n : ℝ)) * ((n : ℝ)⁻¹ * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk' (by norm_num : (0:ℝ) ≤ 2))
        hnn0
    calc
      (2 * (k : ℝ)) * ((n : ℝ)⁻¹ * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r))
          ≤ (2 * (n : ℝ)) * ((n : ℝ)⁻¹ * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r)) := hstep
      _ = 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
          calc
            (2 * (n : ℝ)) * ((n : ℝ)⁻¹ * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r))
                = 2 * ((n : ℝ) * (n : ℝ)⁻¹) * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by ring
            _ = 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
                rw [hnn]
                ring
  have hQ1mon_deg : Q1.Monic ∧ Q1.natDegree = Bclps.Dconst * r := by
    dsimp [Q1, q1poly]
    exact compState_monic_deg P T r n hr1 hTmon hTdeg (d r)
  have hDrpos : 1 ≤ Bclps.Dconst * r := by
    have hD1 : 1 ≤ Bclps.Dconst := Bclps.Dconst_pos
    exact le_trans (by simpa using hr1) (Nat.mul_le_mul_right r hD1)
  have hCNdeg : (C N).natDegree < Bclps.Dconst * r := by
    rw [Polynomial.natDegree_C]
    exact hDrpos
  have hQmon : Q.Monic := by
    dsimp [Q]
    exact (Bclps.monic_add_lower hQ1mon_deg.1 (by
      rw [Polynomial.natDegree_C, hQ1mon_deg.2]
      exact hDrpos)).1
  have hQdeg : Q.natDegree = Bclps.Dconst * r := by
    dsimp [Q]
    rw [(Bclps.monic_add_lower hQ1mon_deg.1 (by
      rw [Polynomial.natDegree_C, hQ1mon_deg.2]
      exact hDrpos)).2, hQ1mon_deg.2]
  have hQ0eq : Q0 = ∏ j' ∈ Finset.range Bclps.Dconst, (T - C (factorCenter r j')) := by
    dsimp [Q0]
    rfl
  have hQ1eq : Q1 = Q0 + (∑ t ∈ Finset.Icc 1 (d r), C (eps t) * auxPoly t) := by
    dsimp [Q0, Q1, eps]
    rw [q1poly_eq_sum P T r n]
  have hQeq : Q = Q1 + C N := rfl
  have hepsrange : ∀ t : ℕ, t ∈ Finset.Icc 1 (d r) → 0 ≤ eps t ∧ eps t < 2 := by
    intro t ht
    dsimp [eps]
    exact epsChoice_mem P T r n t ht
  have hq1even : ∀ k : ℕ, n + 1 ≤ k → k ≤ n + d r →
      ∃ z : ℤ, (P * Q1).coeff k = (z : ℝ) ∧ Even z := by
    intro k hklo hkhi
    let i : ℕ := n + d r - k
    have hi : i < d r := by
      dsimp [i]
      omega
    have hk' : k = n + d r - i := by
      dsimp [i]
      omega
    rcases (compState_even (P := P) (T := T) (r := r) (n := n) hPm hPd (d r) (le_rfl) i hi)
      with ⟨z, hz1, hzE⟩
    refine ⟨z, ?_, hzE⟩
    rw [← hk'] at hz1
    simpa [Q1, q1poly] using hz1
  have hevenQ : ∀ k : ℕ, n + 1 ≤ k → k ≤ n + Bclps.Dconst * r - 1 →
      ∃ z : ℤ, (P * Q).coeff k = (z : ℝ) ∧ Even z := by
    intro k hklo hkhi
    by_cases hkle : k ≤ n + d r
    · rcases (hq1even k hklo hkle) with ⟨z, hz1, hzE⟩
      refine ⟨z, ?_, hzE⟩
      have hze : (P * Q).coeff k = (P * Q1).coeff k := by
        dsimp [Q]
        rw [show P * (Q1 + C N) = P * Q1 + P * C N by ring]
        rw [coeff_add]
        have hz0 : (P * C N).coeff k = 0 := by
          apply coeff_mul_lower_eq_zero (P := P) (A := C N) (n := n) (m := 0) (k := k)
          · exact le_of_eq hPd
          · rw [Polynomial.natDegree_C]
          · omega
        rw [hz0, add_zero]
      rw [hze]
      exact hz1
    · rcases (hTforce k (by dsimp [d] at hkle; omega) hkhi) with ⟨z, hz1, hzE⟩
      refine ⟨z, ?_, hzE⟩
      have hkeq : (P * Q).coeff k = ((T ^ Bclps.Dconst) * P).coeff k := by
        let E : Polynomial ℝ := ∑ t ∈ Finset.Icc 1 (d r), C (eps t) * auxPoly t
        have hQ1E : q1poly P T r n = Q0 + E := by
          dsimp [Q0, E, eps]
          exact q1poly_eq_sum P T r n
        have hid : Q - T ^ Bclps.Dconst = (Q0 - T ^ Bclps.Dconst) + E + C N := by
          dsimp [Q, Q1]
          rw [hQ1E]
          ring
        have hA : (Q0 - T ^ Bclps.Dconst).natDegree ≤ d r := by
          dsimp [Q0]
          exact q0poly_sub_pow_natDegree hr1 hTmon hTdeg
        have hB : E.natDegree ≤ d r := by
          dsimp [E, eps]
          exact epsSum_natDegree_le P T r n
        have hC : (C N).natDegree ≤ d r := by
          rw [Polynomial.natDegree_C]
          exact Nat.zero_le (d r)
        have hAB : ((Q0 - T ^ Bclps.Dconst) + E).natDegree ≤ d r := by
          exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hA hB)
        have hdegL : (Q - T ^ Bclps.Dconst).natDegree ≤ d r := by
          rw [hid]
          exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hAB hC)
        have hcoeff0 : (P * (Q - T ^ Bclps.Dconst)).coeff k = 0 := by
          apply coeff_mul_lower_eq_zero (P := P) (A := Q - T ^ Bclps.Dconst) (n := n) (m := d r) (k := k)
          · exact le_of_eq hPd
          · exact hdegL
          · omega
        have hdecomp : P * Q = P * (T ^ Bclps.Dconst) + P * (Q - T ^ Bclps.Dconst) := by
          rw [show Q = T ^ Bclps.Dconst + (Q - T ^ Bclps.Dconst) by ring]
          ring
        calc
          (P * Q).coeff k = (P * (T ^ Bclps.Dconst) + P * (Q - T ^ Bclps.Dconst)).coeff k := by
              rw [hdecomp]
          _ = (P * (T ^ Bclps.Dconst)).coeff k + (P * (Q - T ^ Bclps.Dconst)).coeff k := by
              rw [coeff_add]
          _ = (P * (T ^ Bclps.Dconst)).coeff k := by
              rw [hcoeff0, add_zero]
          _ = ((T ^ Bclps.Dconst) * P).coeff k := by
              rw [mul_comm]
      rw [hkeq]
      exact hz1
  have hrootbound : ∀ α : ℝ, P.eval α = 0 →
      |Q.eval α| ≥ (n : ℝ)⁻¹ * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
    intro α hα
    have hαS : α ∈ S := by
      dsimp [S]
      rw [Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hPne).2 (by simpa [Polynomial.IsRoot] using hα)
    have hg := hgood α hαS
    have hQe : Q.eval α = Q1.eval α + N := by
      dsimp [Q, N]
      simp
    rw [hQe]
    exact hg
  have hbase4 : (4 : ℝ) ≤ base := by
    dsimp [base]
    have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    nlinarith
  have hTb : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |T.eval x| ≤ base ^ 16 * kappaC ^ r := by
    intro x hx
    have hb := hTnorm16 x hx
    have hc : ((r + n + 2 : ℕ) : ℝ) = base := by
      dsimp [base]
      rw [Nat.cast_add, Nat.cast_add]
      ring
    rw [hc] at hb
    exact hb
  have hsupN : DivLinear.supNorm Q ≤ base ^ Nexp * kappaC ^ (Bclps.Dconst * r) := by
    dsimp [Q, Nexp]
    exact q_supnorm_bound hr hPm hPd hbase4 hTb hNnonneg hNle
  have hsup : DivLinear.supNorm Q ≤ (r + n + 2) ^ (Nexp : ℝ) * kappaC ^ (Bclps.Dconst * r) := by
    have hcast : (r + n + 2) ^ (Nexp : ℝ) = base ^ Nexp := by
      dsimp [base]
      rw [Real.rpow_natCast]
    calc
      DivLinear.supNorm Q ≤ base ^ Nexp * kappaC ^ (Bclps.Dconst * r) := hsupN
      _ = (r + n + 2) ^ (Nexp : ℝ) * kappaC ^ (Bclps.Dconst * r) := by
          rw [← hcast]

  -- assemble witnesses
  refine ⟨(Nexp : ℝ), ⟨?_, ?_⟩⟩
  · exact_mod_cast hNexp_pos
  · refine ⟨T, Q0, Q1, Q, eps, N, ?_⟩
    constructor
    · exact hTmon
    · constructor
      · exact hTdeg
      · constructor
        · exact hTclose
        · constructor
          · exact hTbracket_forall
          · constructor
            · exact hTforce
            · constructor
              · exact hQ0eq
              · constructor
                · exact hQ1eq
                · constructor
                  · exact hQeq
                  · constructor
                    · exact hepsrange
                    · constructor
                      · exact hNnonneg
                      · constructor
                        · exact hNle
                        · constructor
                          · exact hQmon
                          · constructor
                            · exact hQdeg
                            · constructor
                              · exact hevenQ
                              · constructor
                                · exact hrootbound
                                · exact hsup
