import Submission.AdjustedCheb
import Submission.ChebSerre
import Submission.DivLinear
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The bounded-coefficient-forcing step (interval form of Smith's `lem:Bclps`)

Fix `r ≥ 2`, take `T̃ := AdjustedCheb.prunedPoly r` (monic degree `r`, all
roots in the open interval, `|T̃(y_i)| ≥ (1/32)·κ^r` at the bracket points
`y_i = bracketPoint r i`, one root per gap) and a real monic polynomial `S`
of degree `n`.  For `D = Dconst ≥ 256/(κ−1)`, there is a real monic degree-`r`
polynomial `T` with

* (forcing) the degree-`k` monomial coefficients of `T^D·S` are EVEN
  INTEGERS for all `k ∈ [n + (D−1)·r, n + D·r − 1]`;
* (sign) `T(y_i)` has the same sign as `T̃(y_i)` and
  `|T(y_i)| ≥ |T̃(y_i)|/2` for every `i`;
* (norm) `‖T‖ ≤ (r+n+2)^C · κ^r` for some constant `C` depending only on the
  interval.

Construction (paper, adjust.tex, proof of `lem:Bclps`): take auxiliaries
`A_j` = monic real polynomials of degree `j` with `‖A_j‖ ≤ 2κ^j`
(`A_j := chebT j` for `j ≥ 1`, `A_0 := 1`) and define, in decreasing degree
order, `λ_{r-1}, …, λ_0 ∈ [0, 2/D)` so that each step makes the next highest
coefficient of `(T̃ + Σ λ_{r-i} A_{r-i})^D · S` an even integer: adding
`λ A_{r-t}` changes the degree-`(Dr+n−t)` coefficient by exactly `D·λ`
(expansion of the D-th power; all other terms have lower top degree).  Such a
`λ ∈ [0, 2/D)` exists because for every real `c` there is `z : ℤ` with
`2z − c ∈ [0,2)` (take `z = ⌈c/2⌉`).  Finally `T := T̃ + Σ_i λ_i A_i`.
-/

noncomputable section

open scoped Real
open Polynomial

namespace Submission.Bclps

open Submission.SerreExample
open Submission.ChebSerre
open Submission.AdjustedCheb
open Submission.DivLinear

/-- The fixed integer `D` of the construction (any integer `≥ 256/(κ−1)`). -/
noncomputable def Dconst : ℕ := Nat.ceil (256 / (kappaC - 1))

/-- `Dconst ≥ 256/(κ−1)`. -/
lemma Dconst_ge : (256 : ℝ) / (kappaC - 1) ≤ (Dconst : ℝ) := by
  unfold Dconst
  exact Nat.le_ceil (256 / (kappaC - 1))

/-- κ − 1 > 0 (and numerically `> 1/16`, so `Dconst ≤ 4096` is not needed). -/
lemma kappaC_sub_one_pos : 0 < kappaC - 1 := by
  have h := kappaC_gt_one
  linarith

/-- `1 ≤ Dconst`. -/
lemma Dconst_pos : 1 ≤ Dconst := by
  have h : (256 : ℝ) / (kappaC - 1) ≤ (Dconst : ℝ) := Dconst_ge
  have hbig : 1 ≤ (256 : ℝ) / (kappaC - 1) := by
    -- κ − 1 ≤ 256 is trivial (κ ≈ 1.08), and c > 0 so 1 ≤ 256/c iff c ≤ 256
    have hk : kappaC - 1 ≤ (256 : ℝ) := by
      unfold kappaC
      norm_num [aSerre, bSerre]
    have hpos : 0 < kappaC - 1 := kappaC_sub_one_pos
    exact (le_div_iff₀ hpos).mpr (by simpa using hk)
  exact_mod_cast (le_trans hbig h)

/-- κ ≥ 1 (so powers of κ are ≥ 1). -/
lemma kappaC_ge_one : (1 : ℝ) ≤ kappaC := le_of_lt kappaC_gt_one

/-- `Dconst·(κ−1) ≥ 256`. -/
lemma Dconst_mul_ge : (256 : ℝ) ≤ (Dconst : ℝ) * (kappaC - 1) := by
  have h := Dconst_ge
  have hpos : 0 < kappaC - 1 := kappaC_sub_one_pos
  rw [div_le_iff₀ hpos] at h
  exact h

/-- κ^r ≥ 1 for every `r`. -/
lemma kappaC_pow_ge_one (r : ℕ) : (1 : ℝ) ≤ kappaC ^ r := by
  exact one_le_pow₀ kappaC_ge_one

/-- κ is positive. -/
lemma kappaC_pos' : (0 : ℝ) < kappaC := by
  have h := kappaC_gt_one
  linarith

/-- `r + n + 2 ≥ 4` when `2 ≤ r`. -/
lemma base_ge_four (r n : ℕ) (hr : 2 ≤ r) : (4 : ℝ) ≤ (r : ℝ) + (n : ℝ) + 2 := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hnR : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  nlinarith


/-! ## Auxiliary polynomials and the recursive forcing step -/

/-- Auxiliary real monic degree-`j` polynomials: `chebT j` for `j ≥ 1`, constant `1` for `j = 0`. -/
noncomputable def auxPoly (j : ℕ) : Polynomial ℝ :=
  if j = 0 then 1 else chebT j

lemma auxPoly_monic (j : ℕ) : (auxPoly j).Monic := by
  unfold auxPoly
  by_cases hj : j = 0
  · simp [hj]
  · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj)
    simp [hj, chebT_monic j hj1]

lemma auxPoly_natDegree (j : ℕ) : (auxPoly j).natDegree = j := by
  unfold auxPoly
  by_cases hj : j = 0
  · simp [hj]
  · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj)
    rw [if_neg hj]
    exact chebT_natDegree j hj1

/-- sup-norm of `auxPoly j` over the Serre interval is `≤ 2κ^j`. -/
lemma auxPoly_supNorm_le (j : ℕ) : DivLinear.supNorm (auxPoly j) ≤ 2 * kappaC ^ j := by
  rw [DivLinear.supNorm_le_iff]
  intro x hx
  unfold auxPoly
  by_cases hj : j = 0
  · simp [hj]
  · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj)
    rw [if_neg hj]
    exact chebT_bound j hj1 hx

/-- the band index `k_s = n + (D-1)r + s` of the coefficient forced by `A_s`. -/
def bandIndex (r n D s : ℕ) : ℕ := n + (D - 1) * r + s

/-- λ making `c + D·λ` an even integer, in `[0, 2/D)`. -/
noncomputable def evenLam (D : ℕ) (c : ℝ) : ℝ :=
  (2 * (Int.ceil (c / 2) : ℝ) - c) / (D : ℝ)

/-- Properties of the chosen λ: it is in `[0, 2/D)` and makes `c + D·λ = 2·⌈c/2⌉`. -/
lemma evenLam_props {D : ℕ} (hD : 1 ≤ D) (c : ℝ) :
    0 ≤ evenLam D c ∧ evenLam D c < 2 / (D : ℝ) ∧
    c + (D : ℝ) * evenLam D c = 2 * (Int.ceil (c / 2) : ℝ) := by
  have hDposR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hz1 : c / 2 ≤ (Int.ceil (c / 2) : ℝ) := Int.le_ceil (c / 2)
  have hz2 : (Int.ceil (c / 2) : ℝ) < c / 2 + 1 := Int.ceil_lt_add_one (c / 2)
  dsimp [evenLam]
  constructor
  · have hn : 0 ≤ 2 * (Int.ceil (c / 2) : ℝ) - c := by nlinarith
    exact div_nonneg hn (le_of_lt hDposR)
  · constructor
    · have hlt : 2 * (Int.ceil (c / 2) : ℝ) - c < 2 := by nlinarith
      rw [div_lt_div_iff_of_pos_right hDposR]
      exact hlt
    · field_simp [ne_of_gt hDposR]
      ring

/-- `κ^j`-based geometric sum bound: `Σ_{j<r} κ^j ≤ κ^r/(κ−1)`. -/
lemma geom_sum_le (r : ℕ) : (∑ j ∈ Finset.range r, kappaC ^ j) ≤ kappaC ^ r / (kappaC - 1) := by
  have hne : kappaC ≠ 1 := by
    intro h
    have : (1 : ℝ) < kappaC := kappaC_gt_one
    linarith
  have hsum := geom_sum_eq (x := kappaC) hne r
  have hpos : 0 < kappaC - 1 := kappaC_sub_one_pos
  calc
    (∑ j ∈ Finset.range r, kappaC ^ j) = (kappaC ^ r - 1) / (kappaC - 1) := hsum
    _ ≤ kappaC ^ r / (kappaC - 1) := by
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hpos)

/-- `κ^r` dominates the sum of the lower powers with the `D`-factor of the construction. -/
lemma lam_sum_bound (r : ℕ) :
    (2 / (Dconst : ℝ)) * (∑ j ∈ Finset.range r, 2 * kappaC ^ j) ≤ kappaC ^ r / 64 := by
  have hpos : 0 < kappaC - 1 := kappaC_sub_one_pos
  have hDmul : (256 : ℝ) ≤ (Dconst : ℝ) * (kappaC - 1) := Dconst_mul_ge
  have hDposR : (0 : ℝ) < (Dconst : ℝ) := by
    have : 1 ≤ (Dconst : ℝ) := by exact_mod_cast Dconst_pos
    linarith
  have hfactor : (∑ j ∈ Finset.range r, 2 * kappaC ^ j) =
      2 * (∑ j ∈ Finset.range r, kappaC ^ j) := by
    rw [Finset.mul_sum]
  have hfactor' : (2 / (Dconst : ℝ)) * (∑ j ∈ Finset.range r, 2 * kappaC ^ j) =
      (4 / (Dconst : ℝ)) * (∑ j ∈ Finset.range r, kappaC ^ j) := by
    rw [hfactor]
    ring
  calc
    (2 / (Dconst : ℝ)) * (∑ j ∈ Finset.range r, 2 * kappaC ^ j)
        = (4 / (Dconst : ℝ)) * (∑ j ∈ Finset.range r, kappaC ^ j) := hfactor'
    _ ≤ (4 / (Dconst : ℝ)) * (kappaC ^ r / (kappaC - 1)) := by
        exact mul_le_mul_of_nonneg_left (geom_sum_le r)
          (div_nonneg (by norm_num) (le_of_lt hDposR))
    _ = (4 / ((Dconst : ℝ) * (kappaC - 1))) * kappaC ^ r := by
        have hDne : (Dconst : ℝ) ≠ 0 := ne_of_gt hDposR
        have hkne : kappaC - 1 ≠ 0 := ne_of_gt hpos
        field_simp [hDne, hkne]
    _ ≤ (1 / 64) * kappaC ^ r := by
        have hfour : (4 : ℝ) / ((Dconst : ℝ) * (kappaC - 1)) ≤ 1 / 64 := by
          have hprodpos : 0 < (Dconst : ℝ) * (kappaC - 1) := mul_pos hDposR hpos
          rw [div_le_iff₀ hprodpos]
          norm_num
          nlinarith
        exact mul_le_mul_of_nonneg_right hfour (pow_nonneg (le_of_lt kappaC_pos') r)
    _ = kappaC ^ r / 64 := by ring

/-! ## Coefficient perturbation engine

Adding a small monic-degree-`s` multiple to a monic degree-`r` `Q` changes the
coefficient of `(Q^D·S)` at degree `n+(D−1)r+s` by exactly `D·λ`, and does not
touch any higher coefficient. -/

/-- `(m−1)(r−s) ≥ 1` when `m ≥ 2` and `s ≤ r−1`. -/
lemma deg_of_powterm {D r s m : ℕ} (hr : 1 ≤ r) (hs : s ≤ r - 1) (hm2 : 2 ≤ m) (hmD : m ≤ D) :
    m * s + (D - m) * r < (D - 1) * r + s := by
  have hslt : s < r := by omega
  have hD1 : 1 ≤ D := by omega
  have hge1a : (1 : ℝ) ≤ (m : ℝ) - 1 := by
    have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    linarith
  have hge1b : (1 : ℝ) ≤ (r : ℝ) - (s : ℝ) := by
    have hsR : (s : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hslt)
    linarith
  have hmD' : (m : ℝ) ≤ (D : ℝ) := by exact_mod_cast hmD
  have hprod : (1 : ℝ) ≤ ((m : ℝ) - 1) * ((r : ℝ) - (s : ℝ)) := by
    exact one_le_mul_of_one_le_of_one_le hge1a hge1b
  have hreal : (m : ℝ) * (s : ℝ) + ((D : ℝ) - (m : ℝ)) * (r : ℝ) <
      ((D : ℝ) - 1) * (r : ℝ) + (s : ℝ) := by
    nlinarith [hprod, hmD']
  exact_mod_cast hreal

/-- coefficient at the band index of a product of monic polynomials is `1`. -/
lemma coeff_top_monic_prod {A Q S : Polynomial ℝ} {s D r n : ℕ} (hA : A.Monic)
    (hAdeg : A.natDegree = s) (hQ : Q.Monic) (hQdeg : Q.natDegree = r)
    (hS : S.Monic) (hSdeg : S.natDegree = n) :
    (A * Q ^ (D - 1) * S).coeff (bandIndex r n D s) = 1 := by
  have hmon : (A * Q ^ (D - 1) * S).Monic := (hA.mul (hQ.pow (D - 1))).mul hS
  have hdeg : (A * Q ^ (D - 1) * S).natDegree = bandIndex r n D s := by
    unfold bandIndex
    rw [Polynomial.Monic.natDegree_mul (hA.mul (hQ.pow (D-1))) hS,
      Polynomial.Monic.natDegree_mul hA (hQ.pow (D-1))]
    rw [Polynomial.Monic.natDegree_pow hQ, hAdeg, hQdeg, hSdeg]
    ring_nf
  rw [← hdeg, Polynomial.coeff_natDegree]
  exact hmon.leadingCoeff

/-- degree bound for a term of the binomial expansion. -/
lemma natDegree_tail_le {x Q S : Polynomial ℝ} {m D r n s : ℕ}
    (hx : x.natDegree ≤ s) (hQd : Q.natDegree = r) (hSd : S.natDegree = n) :
    (x ^ m * Q ^ (D - m) * S).natDegree ≤ m * s + (D - m) * r + n := by
  calc
    (x ^ m * Q ^ (D - m) * S).natDegree
        ≤ (x ^ m * Q ^ (D - m)).natDegree + S.natDegree := Polynomial.natDegree_mul_le
    _ ≤ (x ^ m).natDegree + (Q ^ (D - m)).natDegree + S.natDegree := by
        have h2 := Polynomial.natDegree_mul_le (p := x ^ m) (q := Q ^ (D - m))
        omega
    _ = m * x.natDegree + (D - m) * r + n := by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow, hQd, hSd]
    _ ≤ m * s + (D - m) * r + n := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right (Nat.mul_le_mul_left m hx) ((D - m) * r)) n

/-- a scalar constant factor does not raise the degree. -/
lemma natDegree_mul_C_le (p : ℝ[X]) (a : ℝ) : (p * C a).natDegree ≤ p.natDegree := by
  calc (p * C a).natDegree ≤ p.natDegree + (C a).natDegree := Polynomial.natDegree_mul_le
    _ = p.natDegree := by rw [Polynomial.natDegree_C, add_zero]

/-- split a range-sum into the `m = 0`, `m = 1` and the rest. -/
lemma sum_peel (D : ℕ) (hD : 1 ≤ D) (g : ℕ → ℝ) :
    (∑ m ∈ Finset.range (D + 1), g m) = (∑ m ∈ Finset.range (D - 1), g (m + 2)) + g 1 + g 0 := by
  rw [Finset.sum_range_succ']
  apply congrArg₂ (· + ·) ?_ rfl
  have h1 := Finset.sum_range_succ' (fun m => g (m + 1)) (D - 1)
  rw [← h1]
  congr 1
  ext m
  simp
  omega

/-- **perturbation engine**: adding `λ·A` (`A` monic of degree `s`) to monic
degree-`r` `Q` changes the coefficient at degree `n+(D−1)r+s` of `Q^D·S` by
`D·λ`, and leaves every coefficient above it untouched. -/
lemma perturb_coeff {D r n s : ℕ} {Q S A : Polynomial ℝ} {lam : ℝ}
    (hr : 1 ≤ r) (hD : 1 ≤ D) (hs : s ≤ r - 1)
    (hQm : Q.Monic) (hQd : Q.natDegree = r)
    (hSm : S.Monic) (hSd : S.natDegree = n)
    (hAm : A.Monic) (hAd : A.natDegree = s) :
    (((Q + C lam * A) ^ D) * S).coeff (bandIndex r n D s) =
      (Q ^ D * S).coeff (bandIndex r n D s) + (D : ℝ) * lam ∧
    ∀ l : ℕ, bandIndex r n D s < l →
      (((Q + C lam * A) ^ D) * S).coeff l = (Q ^ D * S).coeff l := by
  let k := bandIndex r n D s
  let x : Polynomial ℝ := C lam * A
  have hbin : (Q + x) ^ D =
      ∑ m ∈ Finset.range (D + 1), x ^ m * Q ^ (D - m) * (Nat.choose D m : ℝ[X]) := by
    dsimp [x]
    have hb := add_pow (R := ℝ[X]) (x := C lam * A) (y := Q) (n := D)
    simpa [add_comm] using hb
  have hxdeg : x.natDegree ≤ s := by
    dsimp [x]
    calc (C lam * A).natDegree ≤ (C lam).natDegree + A.natDegree := Polynomial.natDegree_mul_le
      _ ≤ s := by rw [hAd]; simp
  let g : ℕ → ℕ → ℝ := fun l m => ((x ^ m * Q ^ (D - m) * (Nat.choose D m : ℝ[X])) * S).coeff l
  have hcoeff (l : ℕ) : (((Q + x) ^ D) * S).coeff l = ∑ m ∈ Finset.range (D + 1), g l m := by
    rw [hbin]
    rw [Finset.sum_mul]
    simp [g]
  have hg0 : ∀ l : ℕ, g l 0 = (Q ^ D * S).coeff l := by
    intro l
    dsimp [g, x]
    simp [Nat.choose_zero_right]
  have hg1 : ∀ l : ℕ, g l 1 = (D : ℝ) * ((C lam * A) * Q ^ (D - 1) * S).coeff l := by
    intro l
    dsimp [g]
    rw [pow_one, Nat.choose_one_right]
    rw [show (x * Q ^ (D - 1) * ((D : ℕ) : ℝ[X])) * S =
        (x * Q ^ (D - 1) * S) * ((D : ℕ) : ℝ[X]) by ring]
    rw [← Polynomial.C_eq_natCast (D)]
    rw [Polynomial.coeff_mul_C]
    dsimp [x]
    ring
  have hmany : ∀ (l : ℕ), k ≤ l → ∀ m : ℕ, 2 ≤ m → m ≤ D → g l m = 0 := by
    intro l hl m hm2 hmD
    dsimp [g]
    have hdeg : (x ^ m * Q ^ (D - m) * S).natDegree < k := by
      have hb : (x ^ m * Q ^ (D - m) * S).natDegree ≤ m * s + (D - m) * r + n :=
        natDegree_tail_le (x := x) (Q := Q) (S := S) (m := m) (D := D) hxdeg hQd hSd
      have hineq : m * s + (D - m) * r + n < bandIndex r n D s := by
        unfold bandIndex
        have hcore := deg_of_powterm hr hs hm2 hmD
        have h1 := Nat.add_lt_add_right hcore n
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
      exact lt_of_le_of_lt hb hineq
    have hrr : (x ^ m * Q ^ (D - m) * (Nat.choose D m : ℝ[X])) * S =
        (x ^ m * Q ^ (D - m) * S) * (Nat.choose D m : ℝ[X]) := by ring
    rw [hrr]
    rw [← Polynomial.C_eq_natCast (Nat.choose D m)]
    have hc := natDegree_mul_C_le (x ^ m * Q ^ (D - m) * S) ((Nat.choose D m : ℕ) : ℝ)
    have hdegL : (x ^ m * Q ^ (D - m) * S).natDegree < l := lt_of_lt_of_le hdeg hl
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hc hdegL)
  have h1band : ((C lam * A) * Q ^ (D - 1) * S).coeff k = lam := by
    calc ((C lam * A) * Q ^ (D - 1) * S).coeff k
        = lam * (A * Q ^ (D - 1) * S).coeff k := by
            rw [show (C lam * A) * Q ^ (D - 1) * S = C lam * (A * Q ^ (D - 1) * S) by ring]
            rw [Polynomial.coeff_C_mul]
    _ = lam := by
            rw [coeff_top_monic_prod hAm hAd hQm hQd hSm hSd]
            ring
  have h1high : ∀ l : ℕ, k < l → ((C lam * A) * Q ^ (D - 1) * S).coeff l = 0 := by
    intro l hl
    have hb : ((C lam * A) * Q ^ (D - 1) * S).natDegree ≤ 1 * s + (D - 1) * r + n := by
      simpa [pow_one] using (natDegree_tail_le (x := C lam * A) (Q := Q) (S := S) (m := 1) (D := D) hxdeg hQd hSd)
    have hk : 1 * s + (D - 1) * r + n = k := by
      dsimp [k, bandIndex]
      ring
    have hlt : 1 * s + (D - 1) * r + n < l := by omega
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hb hlt)
  constructor
  · rw [hcoeff k]
    rw [sum_peel D hD (g k)]
    rw [hg0 k, hg1 k, h1band]
    have htail : (∑ m ∈ Finset.range (D - 1), g k (m + 2)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      apply hmany k (le_rfl) (m + 2) (by omega)
      have hm' : m < D - 1 := Finset.mem_range.mp hm
      omega
    rw [htail]
    ring
  · intro l hl
    rw [hcoeff l]
    rw [sum_peel D hD (g l)]
    rw [hg0 l, hg1 l, h1high l hl]
    have htail : (∑ m ∈ Finset.range (D - 1), g l (m + 2)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      apply hmany l (le_of_lt hl) (m + 2) (by omega)
      have hm' : m < D - 1 := Finset.mem_range.mp hm
      omega
    rw [htail]
    ring

/-- Sup-norm (imported). -/
noncomputable def supNorm (P : Polynomial ℝ) : ℝ :=
  DivLinear.supNorm P

/-! ## The recursive forcing construction -/

/-- One recursive step: add `evenLam D c · A_s` (`s = r-1-u`), where `c` is the
current coefficient at the band position that step fixes. -/
noncomputable def stepQ (r n D : ℕ) (S Q : Polynomial ℝ) (u : ℕ) : Polynomial ℝ :=
  if hu : u < r then
    let s := r - 1 - u
    let k := bandIndex r n D s
    Q + C (evenLam D ((Q ^ D * S).coeff k)) * auxPoly s
  else Q

/-- state after `u` steps: `Tt` plus `u` corrections of degrees `r-1, …, r-u`. -/
noncomputable def qseq (r n D : ℕ) (S Tt : Polynomial ℝ) (u : ℕ) : Polynomial ℝ :=
  Nat.rec Tt (fun t prev => stepQ r n D S prev t) u

/-- `qseq` step recursion: unfolding at `u+1`. -/
lemma qseq_succ (r n D : ℕ) (S Tt : Polynomial ℝ) (u : ℕ) :
    qseq r n D S Tt (u + 1) = stepQ r n D S (qseq r n D S Tt u) u := rfl

/-- `qseq` at 0. -/
lemma qseq_zero (r n D : ℕ) (S Tt : Polynomial ℝ) : qseq r n D S Tt 0 = Tt := rfl

/-- adding a lower-degree polynomial to a monic one keeps it monic of the same degree. -/
lemma monic_add_lower {Q q : Polynomial ℝ} (hQ : Q.Monic) (hdeg : q.natDegree < Q.natDegree) :
    (Q + q).Monic ∧ (Q + q).natDegree = Q.natDegree := by
  have hd : Polynomial.degree q < Polynomial.degree Q := Polynomial.degree_lt_degree hdeg
  exact ⟨hQ.add_of_left hd, Polynomial.natDegree_add_eq_left_of_degree_lt hd⟩

/-- the degrees of the states: every `qseq u`, `u ≤ r`, is monic of degree `r`. -/
lemma qseq_monic_deg (r n D : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r) {S Tt : Polynomial ℝ}
    (hSm : S.Monic) (hSd : S.natDegree = n) (hTm : Tt.Monic) (hTd : Tt.natDegree = r) :
    ∀ u : ℕ, u ≤ r → (qseq r n D S Tt u).Monic ∧ (qseq r n D S Tt u).natDegree = r := by
  intro u
  induction' u with u ih
  · intro hu
    simpa [qseq] using ⟨hTm, hTd⟩
  · intro hus
    have hu : u < r := by omega
    have ih' := ih (le_of_lt hu)
    rw [qseq_succ]
    simp [stepQ, dif_pos hu]
    have hdegA : (C (evenLam D ((qseq r n D S Tt u ^ D * S).coeff
        (bandIndex r n D (r - 1 - u)))) * auxPoly (r - 1 - u)).natDegree < r := by
      have hdegC : (C (evenLam D ((qseq r n D S Tt u ^ D * S).coeff
          (bandIndex r n D (r - 1 - u))))).natDegree ≤ 0 := by
        rw [Polynomial.natDegree_C]
      calc
        (C (evenLam D ((qseq r n D S Tt u ^ D * S).coeff (bandIndex r n D (r - 1 - u)))) * auxPoly (r - 1 - u)).natDegree
            ≤ (C (evenLam D ((qseq r n D S Tt u ^ D * S).coeff (bandIndex r n D (r - 1 - u))))).natDegree
              + (auxPoly (r - 1 - u)).natDegree := Polynomial.natDegree_mul_le
        _ ≤ r - 1 - u := by rw [auxPoly_natDegree]; omega
        _ < r := by omega
    have hmain := monic_add_lower ih'.1 (by simpa [ih'.2] using hdegA)
    exact ⟨hmain.1, by simpa [ih'.2] using hmain.2⟩

/-- the recursive step fixes the band coefficient at `s = r-1-u` to an even integer
and leaves previously fixed (higher) coefficients unchanged. -/
lemma qseq_step_band {r n D u : ℕ} (hD : 1 ≤ D) (hr : 1 ≤ r) {S Tt : Polynomial ℝ}
    (hSm : S.Monic) (hSd : S.natDegree = n) (hTm : Tt.Monic) (hTd : Tt.natDegree = r)
    (hu : u < r) :
    let Q := qseq r n D S Tt u
    let Q' := qseq r n D S Tt (u + 1)
    let k := bandIndex r n D (r - 1 - u)
    let lam := evenLam D ((Q ^ D * S).coeff k)
    (∃ z : ℤ, (Q' ^ D * S).coeff k = 2 * (z : ℝ)) ∧
    ∀ l : ℕ, k < l → (Q' ^ D * S).coeff l = (Q ^ D * S).coeff l := by
  intro Q Q' k lam
  have hs : r - 1 - u ≤ r - 1 := by omega
  have hQ' : Q' = Q + C lam * auxPoly (r - 1 - u) := by
    dsimp [Q, Q', lam, k]
    rw [qseq_succ]
    simp [stepQ, dif_pos hu]
  have hu_le : u ≤ r := le_of_lt hu
  have hQ := qseq_monic_deg r n D hD hr hSm hSd hTm hTd u hu_le
  have hAs : (auxPoly (r - 1 - u)).Monic := auxPoly_monic (r - 1 - u)
  have hAd : (auxPoly (r - 1 - u)).natDegree = r - 1 - u := auxPoly_natDegree (r - 1 - u)
  have hpert := perturb_coeff (D := D) (r := r) (n := n) (s := r - 1 - u) (Q := Q) (S := S)
    (A := auxPoly (r - 1 - u)) (lam := lam) hr hD hs hQ.1 hQ.2 hSm hSd hAs hAd
  constructor
  · rcases hpert with ⟨hex, hhigh⟩
    have hlam : (Q ^ D * S).coeff k + (D : ℝ) * evenLam D ((Q ^ D * S).coeff k) =
        2 * (Int.ceil ((Q ^ D * S).coeff k / 2) : ℝ) := (evenLam_props hD ((Q ^ D * S).coeff k)).2.2
    refine ⟨Int.ceil ((Q ^ D * S).coeff k / 2), ?_⟩
    rw [hQ']
    rw [hex]
    simpa [lam] using hlam
  · intro l hl
    rcases hpert with ⟨hex, hhigh⟩
    rw [hQ']
    exact hhigh l hl

/-- after `u` steps all band coefficients with `s ≥ r−u` are even integers. -/
lemma qseq_fixed_band (r n D : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r) {S Tt : Polynomial ℝ}
    (hSm : S.Monic) (hSd : S.natDegree = n) (hTm : Tt.Monic) (hTd : Tt.natDegree = r) :
    ∀ u : ℕ, u ≤ r →
      (∀ s : ℕ, r - u ≤ s → s < r →
        ∃ z : ℤ, ((qseq r n D S Tt u) ^ D * S).coeff (bandIndex r n D s) = 2 * (z : ℝ)) := by
  intro u
  induction' u with u ih
  · intro hu s hs1 hs2
    omega
  · intro hus s hs1 hs2
    have hu : u < r := by omega
    have hu_le : u ≤ r := le_of_lt hu
    let s0 := r - 1 - u
    have hstep := qseq_step_band (r := r) (n := n) (D := D) hD hr hSm hSd hTm hTd hu
    by_cases hs : s = s0
    · subst s
      dsimp [s0] at hstep ⊢
      exact hstep.1
    · have hsgt : s0 < s := by
        dsimp [s0]
        omega
      have hprev := ih hu_le s (by dsimp [s0] at hsgt ⊢; omega) hs2
      have hpres : (qseq r n D S Tt (u + 1) ^ D * S).coeff (bandIndex r n D s) =
          (qseq r n D S Tt u ^ D * S).coeff (bandIndex r n D s) := by
        have hklt : bandIndex r n D s0 < bandIndex r n D s := by
          unfold bandIndex
          omega
        dsimp [s0] at hstep
        exact hstep.2 (bandIndex r n D s) hklt
      rcases hprev with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      rw [hpres]
      exact hz

/-! ## The sup-norm and value estimates for the constructed polynomial -/

/-- pointwise closeness of the states to `Tt` on the Serre interval. -/
lemma qseq_ptwise (r n D : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r) {S Tt : Polynomial ℝ}
    (hSm : S.Monic) (hSd : S.natDegree = n) (hTm : Tt.Monic) (hTd : Tt.natDegree = r) :
    ∀ u : ℕ, u ≤ r → ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      |(qseq r n D S Tt u).eval x - Tt.eval x| ≤
        (2 / (D : ℝ)) * (∑ t ∈ Finset.range u, DivLinear.supNorm (auxPoly (r - 1 - t))) := by
  intro u
  induction' u with u ih
  · intro hu x hx
    simp [qseq]
  · intro hus x hx
    have hu : u < r := by omega
    have hu_le : u ≤ r := le_of_lt hu
    let lam := evenLam D ((qseq r n D S Tt u ^ D * S).coeff (bandIndex r n D (r - 1 - u)))
    let A := auxPoly (r - 1 - u)
    have hQ' : qseq r n D S Tt (u + 1) = qseq r n D S Tt u + C lam * A := by
      dsimp [lam, A]
      rw [qseq_succ]
      simp [stepQ, dif_pos hu]
    have hlam0 : 0 ≤ lam := (evenLam_props hD ((qseq r n D S Tt u ^ D * S).coeff (bandIndex r n D (r - 1 - u)))).1
    have hlam2 : lam ≤ 2 / (D : ℝ) := le_of_lt (evenLam_props hD ((qseq r n D S Tt u ^ D * S).coeff (bandIndex r n D (r - 1 - u)))).2.1
    have hIH := ih hu_le x hx
    have hlamA : |lam * A.eval x| ≤ lam * DivLinear.supNorm A := by
      calc |lam * A.eval x| = |lam| * |A.eval x| := by rw [abs_mul]
        _ = lam * |A.eval x| := by rw [abs_of_nonneg hlam0]
        _ ≤ lam * DivLinear.supNorm A := by
            exact mul_le_mul_of_nonneg_left (DivLinear.abs_eval_le_supNorm (P := A) x hx) hlam0
    have hA2 : lam * DivLinear.supNorm A ≤ (2 / (D : ℝ)) * DivLinear.supNorm A := by
      exact mul_le_mul_of_nonneg_right hlam2 (DivLinear.supNorm_nonneg A)
    have hsum : (2 / (D : ℝ)) * (∑ t ∈ Finset.range (u + 1), DivLinear.supNorm (auxPoly (r - 1 - t))) =
        (2 / (D : ℝ)) * (∑ t ∈ Finset.range u, DivLinear.supNorm (auxPoly (r - 1 - t))) +
          (2 / (D : ℝ)) * DivLinear.supNorm (auxPoly (r - 1 - u)) := by
      rw [Finset.sum_range_succ]
      ring
    rw [hQ']
    calc
      |(qseq r n D S Tt u + C lam * A).eval x - Tt.eval x|
          ≤ |(qseq r n D S Tt u).eval x - Tt.eval x| + |lam * A.eval x| := by
              rw [show (qseq r n D S Tt u + C lam * A).eval x =
                  (qseq r n D S Tt u).eval x + lam * A.eval x by
                    simp [eval_add, eval_mul, eval_C]]
              rw [show ((qseq r n D S Tt u).eval x + lam * A.eval x) - Tt.eval x =
                  ((qseq r n D S Tt u).eval x - Tt.eval x) + lam * A.eval x by ring]
              exact abs_add_le _ _
      _ ≤ (2 / (D : ℝ)) * (∑ t ∈ Finset.range u, DivLinear.supNorm (auxPoly (r - 1 - t))) +
            |lam * A.eval x| := by
              nlinarith [hIH]
      _ ≤ (2 / (D : ℝ)) * (∑ t ∈ Finset.range u, DivLinear.supNorm (auxPoly (r - 1 - t))) +
            lam * DivLinear.supNorm A := by
              nlinarith [hlamA]
      _ ≤ (2 / (D : ℝ)) * (∑ t ∈ Finset.range u, DivLinear.supNorm (auxPoly (r - 1 - t))) +
            (2 / (D : ℝ)) * DivLinear.supNorm A := by
              nlinarith [hA2]
      _ = (2 / (D : ℝ)) * (∑ t ∈ Finset.range (u + 1), DivLinear.supNorm (auxPoly (r - 1 - t))) := by
              dsimp [A]
              rw [hsum]

/-- the total perturbation of the final state is at most `κ^r/64` pointwise. -/
lemma qseq_final_close {r n : ℕ} (hr : 2 ≤ r) {S : Polynomial ℝ}
    (hSm : S.Monic) (hSd : S.natDegree = n) :
    ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      |(qseq r n Dconst S (prunedPoly r) r).eval x - (prunedPoly r).eval x| ≤ kappaC ^ r / 64 := by
  intro x hx
  have hr1 : 1 ≤ r := by omega
  have hpt := qseq_ptwise r n Dconst Dconst_pos hr1 hSm hSd
    (prunedPoly_monic r) (prunedPoly_natDegree r) r (le_rfl) x hx
  have hA : (2 / (Dconst : ℝ)) * (∑ t ∈ Finset.range r, DivLinear.supNorm (auxPoly (r - 1 - t))) ≤
      (2 / (Dconst : ℝ)) * (∑ t ∈ Finset.range r, 2 * kappaC ^ (r - 1 - t)) := by
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun t ht => auxPoly_supNorm_le (r - 1 - t)))
      (div_nonneg (by norm_num) (le_trans (by norm_num : (0 : ℝ) ≤ (1 : ℝ)) (by exact_mod_cast Dconst_pos)))
  have hrefl : (∑ t ∈ Finset.range r, 2 * kappaC ^ (r - 1 - t)) =
      (∑ j ∈ Finset.range r, 2 * kappaC ^ j) := by
    exact Finset.sum_range_reflect (fun j => 2 * kappaC ^ j) r
  calc
    |(qseq r n Dconst S (prunedPoly r) r).eval x - (prunedPoly r).eval x|
        ≤ (2 / (Dconst : ℝ)) * (∑ t ∈ Finset.range r, DivLinear.supNorm (auxPoly (r - 1 - t))) := hpt
    _ ≤ (2 / (Dconst : ℝ)) * (∑ t ∈ Finset.range r, 2 * kappaC ^ (r - 1 - t)) := hA
    _ = (2 / (Dconst : ℝ)) * (∑ j ∈ Finset.range r, 2 * kappaC ^ j) := by rw [hrefl]
    _ ≤ kappaC ^ r / 64 := lam_sum_bound r

/-! ## Elementary real inequalities and the final bound -/

/-- If `a` is closer to nonzero `b` than `|b|`, they have the same sign. -/
lemma mul_pos_of_close {a b : ℝ} (hb : b ≠ 0) (h : |a - b| < |b|) : 0 < a * b := by
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have habs : |a - b| < -b := by simpa [abs_of_neg hbneg] using h
    have hlt := abs_lt.mp habs
    have ha0 : a < 0 := by nlinarith [hlt.2]
    have hpa : 0 < -a := by linarith
    have hpb : 0 < -b := by linarith
    have hmul : 0 < (-a) * (-b) := mul_pos hpa hpb
    have hre : (-a) * (-b) = a * b := by ring
    rwa [← hre]
  · have habs : |a - b| < b := by simpa [abs_of_pos hbpos] using h
    have hlt := abs_lt.mp habs
    have ha0 : 0 < a := by nlinarith [hlt.1]
    exact mul_pos ha0 hbpos

/-- lower bound on `|a|` when `a` is within `B` of `b` and `2B ≤ |b|`. -/
lemma abs_ge_half {a b B : ℝ} (h : |a - b| ≤ B) (hb2 : 2 * B ≤ |b|) : |b| / 2 ≤ |a| := by
  have htri : |b| ≤ |a - b| + |a| := by
    calc |b| = |(b - a) + a| := by congr 1; ring
      _ ≤ |b - a| + |a| := abs_add_le _ _
      _ = |a - b| + |a| := by rw [abs_sub_comm]
  nlinarith

/-- combined sign and magnitude closeness. -/
lemma close_sign_half {a b B : ℝ} (hb : b ≠ 0) (h : |a - b| ≤ B) (hb2 : 2 * B ≤ |b|) :
    0 < a * b ∧ |b| / 2 ≤ |a| := by
  have hstrict : |a - b| < |b| := by
    have hB2 : B < |b| := by
      have hbpos : 0 < |b| := abs_pos.mpr hb
      nlinarith
    exact lt_of_le_of_lt h hB2
  exact ⟨mul_pos_of_close hb hstrict, abs_ge_half h hb2⟩

/-- `κ^r` is positive. -/
lemma kappaC_pow_pos (r : ℕ) : (0 : ℝ) < kappaC ^ r :=
  lt_of_lt_of_le (by norm_num) (kappaC_pow_ge_one r)

/-- casts of `r+3` and `r+n+2` to the reals. -/
lemma cast_r3 (r : ℕ) : ((r + 3 : ℕ) : ℝ) = (r : ℝ) + 3 := by
  rw [Nat.cast_add]
  norm_num

lemma cast_sum3 (r n : ℕ) : ((r + n + 2 : ℕ) : ℝ) = (r : ℝ) + (n : ℝ) + 2 := by
  rw [Nat.cast_add]
  rw [Nat.cast_add]
  norm_num

/-- polynomial factor in the sup-norm bound: `(r+3)^6 + 1 ≤ (r+n+2)^16`. -/
lemma poly_base_bound (r n : ℕ) (hr : 2 ≤ r) :
    ((r : ℝ) + 3) ^ 6 + 1 ≤ ((r + n + 2 : ℕ) : ℝ) ^ 16 := by
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hnonneg_r2 : 0 ≤ (r : ℝ) + 2 := by positivity
  have hbase : (4 : ℝ) ≤ (r : ℝ) + 2 := by linarith
  have hr3_le : (r : ℝ) + 3 ≤ 2 * ((r : ℝ) + 2) := by nlinarith
  have hpow1 : ((r : ℝ) + 3) ^ 6 ≤ (2 * ((r : ℝ) + 2)) ^ 6 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ (r : ℝ) + 3) hr3_le 6
  have hr3ge : 1 ≤ (r : ℝ) + 3 := by linarith
  have hone : 1 ≤ ((r : ℝ) + 3) ^ 6 := one_le_pow₀ hr3ge
  have hA : (2 * ((r : ℝ) + 2)) ^ 6 ≤ 2 ^ 7 * ((r : ℝ) + 2) ^ 6 := by
    rw [mul_pow]
    have h26 : (2 ^ 6 : ℝ) ≤ 2 ^ 7 := by norm_num
    exact mul_le_mul_of_nonneg_right h26 (pow_nonneg hnonneg_r2 6)
  have hle1 : ((r : ℝ) + 3) ^ 6 + 1 ≤ 2 ^ 7 * ((r : ℝ) + 2) ^ 6 := by
    nlinarith [hpow1, hone, hA]
  have hb10 : (4 : ℝ) ^ 10 ≤ ((r : ℝ) + 2) ^ 10 := pow_le_pow_left₀ (by norm_num) hbase 10
  have hpow16 : (4 : ℝ) ^ 10 * ((r : ℝ) + 2) ^ 6 ≤ ((r : ℝ) + 2) ^ 16 := by
    calc (4 : ℝ) ^ 10 * ((r : ℝ) + 2) ^ 6
        ≤ ((r : ℝ) + 2) ^ 10 * ((r : ℝ) + 2) ^ 6 := mul_le_mul_of_nonneg_right hb10 (pow_nonneg hnonneg_r2 6)
    _ = ((r : ℝ) + 2) ^ (10 + 6) := by rw [pow_add]
    _ = ((r : ℝ) + 2) ^ 16 := by norm_num
  have h27 : (2 ^ 7 : ℝ) ≤ (4 : ℝ) ^ 10 := by norm_num
  have h2 : 2 ^ 7 * ((r : ℝ) + 2) ^ 6 ≤ (4 : ℝ) ^ 10 * ((r : ℝ) + 2) ^ 6 := by
    exact mul_le_mul_of_nonneg_right h27 (pow_nonneg hnonneg_r2 6)
  have hle3 : ((r : ℝ) + 3) ^ 6 + 1 ≤ ((r : ℝ) + 2) ^ 16 := by
    exact le_trans hle1 (le_trans h2 hpow16)
  have hrel : (r : ℝ) + 2 ≤ ((r + n + 2 : ℕ) : ℝ) := by
    rw [cast_sum3]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    nlinarith
  have hpowR : ((r : ℝ) + 2) ^ 16 ≤ (((r + n + 2 : ℕ) : ℝ)) ^ 16 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (r : ℝ) + 2) hrel 16
  exact le_trans hle3 hpowR

/-- Main theorem.  For every monic real `S` of degree `n` and every `r ≥ 2`
there is a monic real degree-`r` `T` with the forcing, sign and norm
properties. -/
theorem bclps_forcing (r n : ℕ) (hr : 2 ≤ r) {S : Polynomial ℝ}
    (hSmon : S.Monic) (hSdeg : S.natDegree = n) :
    ∃ C : ℝ, 0 < C ∧
    ∃ T : Polynomial ℝ,
      T.Monic ∧ T.natDegree = r ∧
      (∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |T.eval x| ≤ (r + n + 2) ^ C * kappaC ^ r) ∧
      (∀ i : Fin (r + 1),
        (bracketPoint r i ∈ Set.Icc aSerre bSerre) ∧
        (prunedPoly r).eval (bracketPoint r i) ≠ 0 ∧
        0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i) ∧
        |T.eval (bracketPoint r i)| ≥ |(prunedPoly r).eval (bracketPoint r i)| / 2) ∧
      (∀ k : ℕ, n + (Dconst - 1) * r ≤ k → k ≤ n + Dconst * r - 1 →
        ∃ z : ℤ, ((T ^ Dconst) * S).coeff k = (z : ℝ) ∧ Even z) := by
  refine ⟨(16 : ℝ), by norm_num, ?_⟩
  let T := qseq r n Dconst S (prunedPoly r) r
  have hD : 1 ≤ Dconst := Dconst_pos
  have hr1 : 1 ≤ r := by omega
  have hTmon : T.Monic := (qseq_monic_deg r n Dconst hD hr1 hSmon hSdeg
    (prunedPoly_monic r) (prunedPoly_natDegree r) r (le_rfl)).1
  have hTdeg : T.natDegree = r := (qseq_monic_deg r n Dconst hD hr1 hSmon hSdeg
    (prunedPoly_monic r) (prunedPoly_natDegree r) r (le_rfl)).2
  refine ⟨T, hTmon, hTdeg, ?_, ?_, ?_⟩
  · -- sup-norm bound on the interval
    intro x hx
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
    have hfinal : |T.eval x| ≤ ((r + n + 2 : ℕ) : ℝ) ^ 16 * kappaC ^ r := by
      calc
        |T.eval x| ≤ (((r : ℝ) + 3) ^ 6 + 1) * kappaC ^ r := hmain2
        _ ≤ ((r + n + 2 : ℕ) : ℝ) ^ 16 * kappaC ^ r := by
            exact mul_le_mul_of_nonneg_right hpb (le_of_lt (kappaC_pow_pos r))
    have hbases : ((r : ℝ) + (n : ℝ) + 2) ^ (16 : ℝ) = ((r + n + 2 : ℕ) : ℝ) ^ 16 := by
      rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num]
      rw [Real.rpow_natCast]
      rw [cast_sum3]
    calc
      |T.eval x| ≤ ((r + n + 2 : ℕ) : ℝ) ^ 16 * kappaC ^ r := hfinal
      _ = ((r : ℝ) + (n : ℝ) + 2) ^ (16 : ℝ) * kappaC ^ r := by rw [hbases]
  · -- bracket points
    intro i
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
    refine ⟨hyIcc, hbne0, hcs.1, hcs.2⟩
  · -- the top-band coefficients are even integers
    intro k hklo hkhi
    have hDr : Dconst * r = (Dconst - 1) * r + r := by
      have hD1 : Dconst = (Dconst - 1) + 1 := by omega
      calc Dconst * r = ((Dconst - 1) + 1) * r := by
            conv_lhs => rw [hD1]
        _ = (Dconst - 1) * r + r := by rw [add_mul, one_mul]
    have hkhi2 : k ≤ n + (Dconst - 1) * r + r - 1 := by
      have hrew : n + Dconst * r - 1 = n + (Dconst - 1) * r + r - 1 := by
        rw [hDr]
        omega
      rwa [hrew] at hkhi
    let s : ℕ := k - (n + (Dconst - 1) * r)
    have hs_le : s ≤ r - 1 := by
      dsimp [s]
      omega
    have hs_lt : s < r := by
      dsimp [s]
      omega
    have hks' : k = bandIndex r n Dconst s := by
      dsimp [s, bandIndex]
      omega
    have hband := qseq_fixed_band r n Dconst hD hr1 hSmon hSdeg
      (prunedPoly_monic r) (prunedPoly_natDegree r) r (le_rfl) s (by dsimp [s]; omega) hs_lt
    rcases hband with ⟨z, hz⟩
    refine ⟨2 * z, ?_, ?_⟩
    · have hz' : ((qseq r n Dconst S (prunedPoly r) r ^ Dconst) * S).coeff k = 2 * (z : ℝ) := by
        rw [hks']
        exact hz
      rw [hz']
      have hcast : (((2 * z : ℤ) : ℝ)) = 2 * (z : ℝ) := by
        rw [Int.cast_mul]
        norm_num
      rw [← hcast]
    · exact ⟨z, by ring⟩

end Submission.Bclps
