import Mathlib
import Submission.Work.C7.xdefs
import Submission.CDT.Residue

/-!
# Area C7 — `1, L, L²` are `ℚ[x]`-linearly independent for `L = log(1-x)`

`Work.C7.Lps = log(1-x) = -Σ_{n≥1} xⁿ/n ∈ ℚ⟦x⟧`.  We prove that the powers
`1, L, L², …` are linearly independent over `ℚ[x]`, by the elementary
"no new integration" argument in the form of a minimal-degree induction:

* if `Σ_{i ≤ n} Pᵢ(x)·Lⁱ = 0` with `Pₙ ≠ 0` minimal, then differentiating and
  multiplying by `(1-x)` (using `(1-x)·L' = -1`) produces the relation
  `Σ ((1-x)Pᵢ' - (i+1)P_{i+1})·Lⁱ = 0`, which combined with the original relation
  kills the top coefficient and yields, by minimality, the polynomial identity
  `(1-x)·(P_{n+1}Pₙ' - P_{n+1}'Pₙ) = (n+1)·P_{n+1}²`
  (indices relabelled: it is the relation of degree `n+1` that is reduced);
* mapping this identity to `ℚ(x)` gives `(Pₙ/P_{n+1})' = -(n+1)/(1-x)`, whose
  order of vanishing at `1` is `-1`, whereas a derivative in `ℚ(x)` never has a
  simple pole (`Submission.CDT.ordAt_dRat_ne_neg_one`).
-/

open PowerSeries
open scoped BigOperators

namespace Work.C7

noncomputable section

set_option maxHeartbeats 1000000

/-- The formal derivative `d/dx` on `ℚ⟦x⟧`. -/
abbrev Dp : Derivation ℚ (PowerSeries ℚ) (PowerSeries ℚ) := PowerSeries.derivative (R := ℚ)

/-- `(1 - x)·(log(1-x))' = -1`. -/
lemma one_sub_X_mul_Dp : (1 - X) * Dp Lps = -1 := deriv_Lps

/-- The coercion `ℚ[X] → ℚ⟦X⟧` commutes with `ℕ`-casts. -/
lemma natCast_coe (n : ℕ) : ((n : Polynomial ℚ) : PowerSeries ℚ) = (n : PowerSeries ℚ) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply]
  exact map_natCast _ n

/-- Derivative of a polynomial combination `Σ Pᵢ(x)·L(x)^i`. -/
lemma deriv_sum (N : ℕ) (P : ℕ → Polynomial ℚ) :
    Dp (∑ i ∈ Finset.range N, ((P i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i)
      = (∑ i ∈ Finset.range N, (((P i).derivative : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i)
        + ∑ i ∈ Finset.range N,
            ((P i : Polynomial ℚ) : PowerSeries ℚ)
              * ((i : PowerSeries ℚ) * Lps ^ (i - 1) * Dp Lps) := by
  rw [map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Derivation.leibniz, PowerSeries.derivative_coe, PowerSeries.derivative_pow]
  simp only [smul_eq_mul]
  ring

/-- Reindexing the derivative term: `Σᵢ Pᵢ·i·L^{i-1} = Σₖ (k+1)·P_{k+1}·L^k`. -/
lemma reindex_sum (N : ℕ) (P : ℕ → Polynomial ℚ) (hPN : P N = 0) :
    (∑ i ∈ Finset.range N,
        ((P i : Polynomial ℚ) : PowerSeries ℚ) * ((i : PowerSeries ℚ) * Lps ^ (i - 1)))
      = ∑ k ∈ Finset.range N,
          (((k + 1 : ℕ) : PowerSeries ℚ) * ((P (k + 1) : Polynomial ℚ) : PowerSeries ℚ)
            * Lps ^ k) := by
  cases N with
  | zero => simp
  | succ M =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    have h0 : ((P 0 : Polynomial ℚ) : PowerSeries ℚ)
        * (((0 : ℕ) : PowerSeries ℚ) * Lps ^ (0 - 1)) = 0 := by simp
    have hN : (((M + 1 : ℕ) : PowerSeries ℚ) * ((P (M + 1) : Polynomial ℚ) : PowerSeries ℚ)
        * Lps ^ M) = 0 := by
      rw [show P (M + 1) = 0 from hPN]; simp
    rw [h0, hN, add_zero, add_zero]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Nat.add_sub_cancel]
    ring

/-- The "shifted" relation: from `Σᵢ Pᵢ·L^i = 0` (`i < N`, `P N = 0`) follows
`Σᵢ ((1-x)Pᵢ' - (i+1)P_{i+1})·L^i = 0`. -/
lemma shift_relation (N : ℕ) (P : ℕ → Polynomial ℚ) (hPN : P N = 0)
    (hrel : ∑ i ∈ Finset.range N, ((P i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i = 0) :
    ∑ i ∈ Finset.range N,
        ((((1 - Polynomial.X) * (P i).derivative - ((i + 1 : ℕ) : Polynomial ℚ) * P (i + 1)
            : Polynomial ℚ) : PowerSeries ℚ)) * Lps ^ i = 0 := by
  have hder := deriv_sum N P
  rw [hrel, map_zero] at hder
  set S1 : PowerSeries ℚ := ∑ i ∈ Finset.range N,
    (((P i).derivative : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i with hS1def
  set S2 : PowerSeries ℚ := ∑ i ∈ Finset.range N,
    ((P i : Polynomial ℚ) : PowerSeries ℚ) * ((i : PowerSeries ℚ) * Lps ^ (i - 1) * Dp Lps)
    with hS2def
  have key : (1 - PowerSeries.X) * S1 + (1 - PowerSeries.X) * S2 = 0 := by
    rw [← mul_add, ← hder, mul_zero]
  have hS1rw : (1 - PowerSeries.X) * S1 = ∑ i ∈ Finset.range N,
      ((((1 - Polynomial.X) * (P i).derivative : Polynomial ℚ)) : PowerSeries ℚ) * Lps ^ i := by
    rw [hS1def, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast
    ring
  have hS2rw : -((1 - PowerSeries.X) * S2) = ∑ k ∈ Finset.range N,
      (((((k + 1 : ℕ) : Polynomial ℚ) * P (k + 1) : Polynomial ℚ)) : PowerSeries ℚ) * Lps ^ k := by
    rw [hS2def, Finset.mul_sum]
    have hterm : ∀ i ∈ Finset.range N,
        (1 - PowerSeries.X) * (((P i : Polynomial ℚ) : PowerSeries ℚ)
          * ((i : PowerSeries ℚ) * Lps ^ (i - 1) * Dp Lps))
        = -(((P i : Polynomial ℚ) : PowerSeries ℚ) * ((i : PowerSeries ℚ) * Lps ^ (i - 1))) := by
      intro i _
      calc (1 - PowerSeries.X) * (((P i : Polynomial ℚ) : PowerSeries ℚ)
            * ((i : PowerSeries ℚ) * Lps ^ (i - 1) * Dp Lps))
          = (((P i : Polynomial ℚ) : PowerSeries ℚ) * ((i : PowerSeries ℚ) * Lps ^ (i - 1)))
              * ((1 - PowerSeries.X) * Dp Lps) := by ring
        _ = (((P i : Polynomial ℚ) : PowerSeries ℚ) * ((i : PowerSeries ℚ) * Lps ^ (i - 1)))
              * (-1) := by rw [one_sub_X_mul_Dp]
        _ = -(((P i : Polynomial ℚ) : PowerSeries ℚ) * ((i : PowerSeries ℚ) * Lps ^ (i - 1))) := by
              ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, neg_neg]
    rw [reindex_sum N P hPN]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    push_cast
    try rw [natCast_coe k]
    try ring
  have hAB : (∑ i ∈ Finset.range N,
        ((((1 - Polynomial.X) * (P i).derivative : Polynomial ℚ)) : PowerSeries ℚ) * Lps ^ i)
      = ∑ k ∈ Finset.range N,
          (((((k + 1 : ℕ) : Polynomial ℚ) * P (k + 1) : Polynomial ℚ)) : PowerSeries ℚ) * Lps ^ k := by
    have h2 : (1 - PowerSeries.X) * S2
        = -(∑ k ∈ Finset.range N,
            (((((k + 1 : ℕ) : Polynomial ℚ) * P (k + 1) : Polynomial ℚ)) : PowerSeries ℚ) * Lps ^ k) := by
      rw [← hS2rw, neg_neg]
    rw [hS1rw, h2] at key
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using key)
  have hgoal : (∑ i ∈ Finset.range N,
        ((((1 - Polynomial.X) * (P i).derivative - ((i + 1 : ℕ) : Polynomial ℚ) * P (i + 1)
            : Polynomial ℚ) : PowerSeries ℚ)) * Lps ^ i)
      = (∑ i ∈ Finset.range N,
          ((((1 - Polynomial.X) * (P i).derivative : Polynomial ℚ)) : PowerSeries ℚ) * Lps ^ i)
        - (∑ k ∈ Finset.range N,
          (((((k + 1 : ℕ) : Polynomial ℚ) * P (k + 1) : Polynomial ℚ)) : PowerSeries ℚ) * Lps ^ k) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast
    try rw [natCast_coe i]
    try ring
  rw [hgoal, hAB, sub_self]

/-- Combining two relations `Σ PᵢL^i = Σ QᵢL^i = 0` of degree `≤ M` gives a relation
`Σ (P_M·Qᵢ - Q_M·Pᵢ)L^i = 0` of degree `< M`. -/
lemma combine_relation (M : ℕ) (P Q : ℕ → Polynomial ℚ)
    (hrelP : ∑ i ∈ Finset.range (M + 1), ((P i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i = 0)
    (hrelQ : ∑ i ∈ Finset.range (M + 1), ((Q i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i = 0) :
    ∑ i ∈ Finset.range M,
        ((((P M) * Q i - (Q M) * P i : Polynomial ℚ)) : PowerSeries ℚ) * Lps ^ i = 0 := by
  have hterm : ∀ i, ((((P M) * Q i - (Q M) * P i : Polynomial ℚ)) : PowerSeries ℚ) * Lps ^ i
      = ((P M : Polynomial ℚ) : PowerSeries ℚ) * (((Q i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i)
        - ((Q M : Polynomial ℚ) : PowerSeries ℚ) * (((P i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i) := by
    intro i
    push_cast
    ring
  have hsum : (∑ i ∈ Finset.range (M + 1),
      ((((P M) * Q i - (Q M) * P i : Polynomial ℚ)) : PowerSeries ℚ) * Lps ^ i) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hrelP, hrelQ, mul_zero, mul_zero, sub_self]
  rw [Finset.sum_range_succ] at hsum
  have hM : ((((P M) * Q M - (Q M) * P M : Polynomial ℚ)) : PowerSeries ℚ) * Lps ^ M = 0 := by
    rw [show P M * Q M - Q M * P M = 0 from by ring]
    simp
  rw [hM, add_zero] at hsum
  exact hsum

/-- `1 - x ≠ 0` in `ℚ(x)`. -/
lemma one_sub_Xr_ne_zero :
    (1 : RatFunc ℚ) - algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X ≠ 0 := by
  have h : (1 : RatFunc ℚ) - algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X
      = -(Submission.CDT.lin (1 : ℚ)) := by
    rw [Submission.CDT.lin]
    simp only [map_sub, map_one]
    ring
  rw [h]
  exact neg_ne_zero.mpr (Submission.CDT.lin_ne_zero 1)

/-- The order of vanishing of `1 - x` at `1`. -/
lemma ordAt_one_one_sub_X :
    Submission.CDT.ordAt (1 : ℚ)
      (1 - algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X) = 1 := by
  have h : (1 : RatFunc ℚ) - algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X
      = -(Submission.CDT.lin (1 : ℚ)) := by
    rw [Submission.CDT.lin]
    simp only [map_sub, map_one]
    ring
  rw [h, Submission.CDT.ordAt_neg, Submission.CDT.ordAt_lin]

/-- A nonzero constant polynomial has no zero at `1`, so `ordAt 1` vanishes. -/
lemma ordAt_one_poly_natCast (m : ℕ) :
    Submission.CDT.ordAt (1 : ℚ)
      (algebraMap (Polynomial ℚ) (RatFunc ℚ) ((m : ℕ) : Polynomial ℚ)) = 0 := by
  rw [show ((m : ℕ) : Polynomial ℚ) = Polynomial.C ((m : ℚ)) from
    (map_natCast Polynomial.C m).symm]
  rw [Submission.CDT.ordAt_algebraMap, Polynomial.rootMultiplicity_C]
  simp

/-- **The main induction**: no nonzero polynomial relation `Σ Pᵢ(x)·L(x)^i = 0`. -/
theorem no_relation : ∀ n : ℕ, ∀ P : ℕ → Polynomial ℚ,
    (∀ i, n < i → P i = 0) →
    (∑ i ∈ Finset.range (n + 1), ((P i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i = 0) →
    ∀ i, P i = 0 := by
  intro n
  induction n with
  | zero =>
      intro P hsupp hrel i
      have h0 : ((P 0 : Polynomial ℚ) : PowerSeries ℚ) = 0 := by
        simpa using hrel
      have hp0 : P 0 = 0 := Polynomial.coe_eq_zero_iff.mp h0
      rcases Nat.eq_zero_or_pos i with h | hi
      · rw [h]; exact hp0
      · exact hsupp i (by omega)
  | succ n ih =>
      intro P hsupp hrel
      by_cases htop : P (n + 1) = 0
      · have hsupp' : ∀ i, n < i → P i = 0 := by
          intro i hi
          by_cases h : i = n + 1
          · rw [h]; exact htop
          · exact hsupp i (by omega)
        have hrel' : ∑ i ∈ Finset.range (n + 1),
            ((P i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i = 0 := by
          have h := hrel
          rw [Finset.sum_range_succ] at h
          rw [show ((P (n + 1) : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ (n + 1) = 0 by
            rw [htop]; simp, add_zero] at h
          exact h
        exact ih P hsupp' hrel'
      · have hPtop : P (n + 1) ≠ 0 := htop
        set Q : ℕ → Polynomial ℚ := fun i =>
          (1 - Polynomial.X) * (P i).derivative - (((i + 1 : ℕ)) : Polynomial ℚ) * P (i + 1)
          with hQdef
        have hQsupp : ∀ i, n + 1 < i → Q i = 0 := by
          intro i hi
          have h1 : P i = 0 := hsupp i (by omega)
          have h2 : P (i + 1) = 0 := hsupp (i + 1) (by omega)
          simp [hQdef, h1, h2]
        have hrelQ : ∑ i ∈ Finset.range (n+1+1),
            ((Q i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i = 0 :=
          shift_relation (n+1+1) P (hsupp (n+1+1) (by omega)) hrel
        set U : ℕ → Polynomial ℚ := fun i => P (n + 1) * Q i - Q (n + 1) * P i with hUdef
        have hrelU : ∑ i ∈ Finset.range (n + 1),
            ((U i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i = 0 :=
          combine_relation (n + 1) P Q hrel hrelQ
        have hUsupp : ∀ i, n < i → U i = 0 := by
          intro i hi
          by_cases h : i = n + 1
          · rw [h, hUdef]; ring
          · have h1 : P i = 0 := hsupp i (by omega)
            have h2 : Q i = 0 := hQsupp i (by omega)
            rw [hUdef]
            simp [h1, h2]
        have hun : U n = 0 := ih U hUsupp hrelU n
        have hun' : P (n + 1) * Q n - Q (n + 1) * P n = 0 := hun
        have hQn : Q n = (1 - Polynomial.X) * (P n).derivative
            - (((n + 1 : ℕ)) : Polynomial ℚ) * P (n + 1) := by
          simp [hQdef]
        have hQn1 : Q (n + 1) = (1 - Polynomial.X) * (P (n + 1)).derivative := by
          have h : P (n + 2) = 0 := hsupp (n + 2) (by omega)
          simp [hQdef, h]
        have hid : (1 - Polynomial.X) *
            ((P (n + 1)) * (P n).derivative - (P (n + 1)).derivative * (P n))
            = (((n + 1 : ℕ)) : Polynomial ℚ) * (P (n + 1)) * (P (n + 1)) := by
          have h := hun'
          rw [hQn, hQn1] at h
          linear_combination h
        set A : RatFunc ℚ := algebraMap (Polynomial ℚ) (RatFunc ℚ) (P n) with hAdef
        set B : RatFunc ℚ := algebraMap (Polynomial ℚ) (RatFunc ℚ) (P (n + 1)) with hBdef
        set Cc : RatFunc ℚ := algebraMap (Polynomial ℚ) (RatFunc ℚ)
          (((n + 1 : ℕ)) : Polynomial ℚ) with hCdef
        set Xr : RatFunc ℚ := algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X with hXdef
        have hBne : B ≠ 0 := by
          rw [hBdef]
          exact RatFunc.algebraMap_ne_zero hPtop
        have hXne : (1 : RatFunc ℚ) - Xr ≠ 0 := by
          rw [hXdef]
          exact one_sub_Xr_ne_zero
        have hidR : (1 - Xr) * (B * Submission.CDT.dRat A - Submission.CDT.dRat B * A)
            = Cc * B ^ 2 := by
          have h := congrArg (algebraMap (Polynomial ℚ) (RatFunc ℚ)) hid
          simp only [map_mul, map_sub, map_one] at h
          rw [← Submission.CDT.dRat_algebraMap (P n),
            ← Submission.CDT.dRat_algebraMap (P (n + 1))] at h
          rw [← hXdef, ← hAdef, ← hBdef, ← hCdef] at h
          ring_nf at h ⊢
          exact h
        have hquot : Submission.CDT.dRat (A / B) = Cc / (1 - Xr) := by
          rw [hAdef, hBdef, Submission.CDT.dRat_div]
          set N : Polynomial ℚ := (P n).derivative * P (n + 1) - P n * (P (n + 1)).derivative
            with hNdef
          have hNval : algebraMap (Polynomial ℚ) (RatFunc ℚ) N
              = B * Submission.CDT.dRat A - Submission.CDT.dRat B * A := by
            rw [hNdef, hAdef, hBdef, map_sub, map_mul, map_mul,
              Submission.CDT.dRat_algebraMap, Submission.CDT.dRat_algebraMap]
            ring
          have hNprod : algebraMap (Polynomial ℚ) (RatFunc ℚ) N * (1 - Xr) = Cc * B ^ 2 := by
            rw [hNval, mul_comm]
            exact hidR
          rw [← hBdef]
          rw [div_eq_div_iff (pow_ne_zero 2 hBne) hXne]
          exact hNprod
        have hCcne : Cc ≠ 0 := by
          rw [hCdef]
          exact RatFunc.algebraMap_ne_zero (Nat.cast_ne_zero.mpr (by omega : n + 1 ≠ 0))
        have heq : Submission.CDT.ordAt (1 : ℚ) (Cc / (1 - Xr)) = -1 := by
          have hord : Submission.CDT.ordAt (1 : ℚ) Cc = 0 := by
            rw [hCdef]
            exact ordAt_one_poly_natCast (n + 1)
          calc Submission.CDT.ordAt (1 : ℚ) (Cc / (1 - Xr))
              = Submission.CDT.ordAt (1 : ℚ) Cc
                - Submission.CDT.ordAt (1 : ℚ) (1 - Xr) :=
                  Submission.CDT.ordAt_div (1 : ℚ) hCcne hXne
            _ = 0 - 1 := by rw [hord, hXdef, ordAt_one_one_sub_X]
            _ = -1 := by norm_num
        have hne := Submission.CDT.ordAt_dRat_ne_neg_one (1 : ℚ) (A / B)
        rw [hquot, heq] at hne
        exact (hne rfl).elim

/-- **`1, L, L², …` are `ℚ[x]`-linearly independent** for `L = log(1-x)`. -/
theorem lps_powers_independent (m : ℕ) :
    Submission.CDTPlan.PolyIndependent (fun i : Fin m => Lps ^ (i : ℕ)) := by
  intro P hrel
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    intro i
    exact i.elim0
  · intro j
    set P' : ℕ → Polynomial ℚ := fun i => if h : i < m then P ⟨i, h⟩ else 0 with hP'def
    have hsupp : ∀ i, (m - 1) < i → P' i = 0 := by
      intro i hi
      rw [hP'def]
      simp only
      rw [dif_neg (by omega)]
    have hsum_eq : (∑ i : Fin m, ((P i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ (i : ℕ))
        = ∑ i ∈ Finset.range m, ((P' i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun i : ℕ => ((P' i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i) m]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show P' ↑i = P i from by
        rw [hP'def]; simp only; rw [dif_pos i.isLt]]
    have hrel' : ∑ i ∈ Finset.range ((m - 1) + 1),
        ((P' i : Polynomial ℚ) : PowerSeries ℚ) * Lps ^ i = 0 := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m), ← hsum_eq]
      exact hrel
    have hall := no_relation (m - 1) P' hsupp hrel' j
    rw [hP'def] at hall
    simp only at hall
    rwa [dif_pos j.isLt] at hall

theorem indep_small :
    Submission.CDTPlan.PolyIndependent (fun i : Fin 2 => ![1, Work.C7.Lps] i) ∧
    Submission.CDTPlan.PolyIndependent (fun i : Fin 3 => ![1, Work.C7.Lps, Work.C7.Lps ^ 2] i) := by
  constructor
  · rw [show (fun i : Fin 2 => ![1, Work.C7.Lps] i) = (fun i : Fin 2 => Work.C7.Lps ^ (i : ℕ)) by
      funext i; fin_cases i <;> simp]
    exact lps_powers_independent 2
  · rw [show (fun i : Fin 3 => ![1, Work.C7.Lps, Work.C7.Lps ^ 2] i)
        = (fun i : Fin 3 => Work.C7.Lps ^ (i : ℕ)) by
      funext i; fin_cases i <;> simp]
    exact lps_powers_independent 3

end

end Work.C7
