import Mathlib
import Submission.MonicDual
import Submission.PartAFound
import Submission.ValIntegral
import Submission.CoeffIntegral
/-!
# The GENERAL (non-monic) complex dual condition — `thm:adjust` core

Smith, GON.tex `thm:adjust` needs, for a SQUAREFREE INTEGER polynomial `Q` of
degree `n` (leading coefficient `c := Q.leadingCoeff`, NOT assumed ±1) with
distinct complex roots `α : Fin n → ℂ`, writing `Q_i = Q/(X − α_i)` and
`b_ij := coeff j (Q_i)`:

    ∀ nonzero d ∈ ℤⁿ:  ∃ i:  |Σ_j d_j·b_ij| ≥ 1.            (∗)

`Submission.MonicDual` proved the MONIC case (`c = 1`).  This file states the
general case.  Reuse `Submission.MonicDual` (`qic`, `cval`, `Dpoly`, `Qc`, and
the lemmas `res_int`, `res_complex`, `qic_coeff_eq_rq`, `cval_eq_eval_D`,
`exists_cval_ne_zero`, `kronecker_contra` …).

## Setup: what changes vs the monic case

With `c := Q.leadingCoeff : ℤ`, the complexification factors as
`Qc Q = C (c : ℂ) · ∏_i (X − C (α i))`, and the quotient by `(X − C (α i))` is
`C (c : ℂ) · qic α i`.  Hence `b_ij = (c : ℂ) · (qic α i).coeff j`, and the
dual values are `C_i := Σ_j (d j : ℂ) · (c : ℂ) · (qic α i).coeff j` = the
`cval` of `MonicDual` multiplied by `(c : ℂ)`.

## The key fact to prove (equivalent to (∗))

For `D := Dpoly Q d ∈ ℤ[X]` (the divided-difference polynomial built from `Q`'s
own coefficients — so `D.eval (α i) = C_i` — note `Dpoly` already uses
`Q.coeff t` which includes the leading coefficient, so NO extra `c` factor is
needed: `cval α d i` as defined in MonicDual equals `D.eval (α i)` where `D`
uses the full coefficients of `Q`; but the QUOTIENT coefficients are
`(c : ℂ) · (qic α i).coeff j = r_j(α i)`, and `cval` (built from `qic` without
`c`) satisfies `(c:ℂ)·cval α d i = D.eval (α i)`).

  Key target:  the polynomial  `F(T) := ∏_i (T − C(C_i))`  has INTEGER
  coefficients  (i.e. `∃ Fz : Polynomial ℤ, Fz.map (algebraMap ℤ ℂ) = F`).

Then `(∗)` follows exactly as in the monic case (`kronecker_contra` with
`c := fun i => C_i` and nonzero-ness from the invertibility of the coefficient
matrix, adapted by the factor `c ≠ 0`).

## Route to the key target (paper, GON.tex thm:adjust proof)

(A) (Rationality of the product — FREE.)  Over the ring `ℤ[T]`, the resultant
    `F̃(T) := Res_X(Q(X), T − D(X))` has integer coefficients, and over `ℂ(T)`
    (via `resultant_eq_prod_eval`/the `res_complex`/`res_int` machinery with the
    extra leading-coefficient factor) its image satisfies
    `F̃.mapℂ = (c : ℂ)^s · ∏_i (T − C(C_i))`  where `s := deg_X (T − D(X)) ≤ n−1`
    (so `c^s·F ∈ ℤ[T]` — hence `F ∈ ℚ[T]`; also `F` is MONIC of degree `n`).

(B) (Algebraic integrality of the values.)  Prove that every `C_i` is an
    algebraic integer: `IsIntegral ℤ C_i`.  Since `C_i = Σ_j d_j·b_ij`, it is
    enough to prove each `b_ij` is an algebraic integer.  THE paper proves this
    by Gauss's lemma over discrete valuation rings ("these coefficients are all
    algebraic integers; otherwise some `b_ij` would have negative valuation at
    some prime of `E = ℚ(α_1,…,α_n)`").  A clean valuation-free LOCAL argument:
    fix a discrete valuation `ν` of `E` with `ν(ℤ) ≥ 0` and write
    `b_j := b_ij`, `α := α_i`, `a := ν(α)`, `q_t := Q.coeff t`.
      * If `a ≥ 0`: `b_j = Σ_{t≥j+1} q_t·α^(t−1−j)` has all terms `ν ≥ 0`.
      * If `a < 0`: from `Q(α) = 0` one has `b_j = −Σ_{t≤j} q_t·β^(j+1−t)`
        with `β := α⁻¹`; equivalently the recursion
        `b₀ = −q₀/α`,  `b_{j+1} = (b_j − q_{j+1})/α`  (coefficients of
        `Q = (X−α)·Σ_j b_j X^j`) shows by induction that `ν(b_j) ≥ −a > 0`
        (base `ν(b₀) = ν(q₀) + (−a) ≥ −a`, step: `ν(b_j − q_{j+1}) ≥ 0` since
        both have `ν ≥ 0`, so `ν(b_{j+1}) = ν(b_j − q_{j+1}) − a ≥ −a`).
      So `b_ij ∈ O_E` at every discrete valuation, hence an algebraic integer.
    NOTE: formalizing "integral at every discrete valuation ⇒ algebraic integer"
    may require new Mathlib content (Valuation / IsDedekindDomain / field
    valuations).  ALTERNATIVE: find a direct monic-integer-polynomial witness:
    e.g. for each fixed `j` show the column product
    `G_j(T) := ∏_i (T − C(b_ij)) ∈ ℤ[T]` (equivalently each `b_ij` is a root of
    a monic integer polynomial), possibly by the same resultant trick applied to
    the REVERSED polynomial (β-roots).  Any route is acceptable; the CONCLUSION
    needed is simply `IsIntegral ℤ C_i` for every `i` (or the full key target).

(C) (Integer coefficients of F.)  From (A) `F ∈ ℚ[T]` and (B) each coefficient
    of `F` is a symmetric integer polynomial in the `C_i`, hence an algebraic
    integer; by `Submission.PartAFound.int_of_isIntegral_rat` (rational algebraic
    integers are integers) every coefficient is an integer.  Hence
    `F ∈ ℤ[T]` — the key target.  (Alternative: skip (B)+(C) if you can prove
    the exact divisibility `c^s | F̃` in `ℤ[T]` directly using the special form
    of `D`.)

Then finish `(∗)` with the `kronecker_contra`-style argument (adapting
`exists_cval_ne_zero` for the extra factor `(c : ℂ) ≠ 0`).

Deliver `general_dual` below.  You may add any helper lemmas in this file.
Axioms ⊆ {propext, Quot.sound, Classical.choice}.  This is a LONG, hard lemma —
build it in clearly separated components with many complete intermediate
lemmas.  Self-contained via the two imports above.
-/

noncomputable section
open scoped BigOperators
open Polynomial

set_option maxHeartbeats 1000000

namespace Submission.GeneralDual

open Submission.MonicDual
open Submission.PartAFound
open Submission.ValIntegral
open Submission.CoeffIntegral


/-- The value in the statement of `general_dual`: `Σ_j d_j·c·(qic α i).coeff j`
where `c := Q.leadingCoeff`. -/
noncomputable def cvalc {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ) (d : Fin n → ℤ) (i : Fin n) : ℂ :=
  ∑ j : Fin n, ((d j : ℂ) * ((Q.leadingCoeff : ℂ) * (qic α i).coeff (j.val)))

lemma cvalc_eq_cval_mul {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ) (d : Fin n → ℤ) (i : Fin n) :
    cvalc Q α d i = (Q.leadingCoeff : ℂ) * cval α d i := by
  unfold cvalc cval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The scaled quotient `(Q.leadingCoeff)·qic α i` equals the monic division of
`Qc Q` by `(X - C (α i))`. -/
lemma qic_lead_eq_divByMonic {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)))
    (i : Fin n) :
    Polynomial.C ((Q.leadingCoeff : ℂ)) * qic α i =
      (Q.map (algebraMap ℤ ℂ)) /ₘ (Polynomial.X - Polynomial.C (α i)) := by
  -- Qc = (X - C α_i) · (C(c)·qic α i)
  have hQ : Q.map (algebraMap ℤ ℂ) =
      (Polynomial.X - Polynomial.C (α i)) *
        (Polynomial.C ((Q.leadingCoeff : ℂ)) * qic α i) := by
    calc
      Q.map (algebraMap ℤ ℂ) = Polynomial.C ((Q.leadingCoeff : ℂ)) *
          ∏ k : Fin n, (Polynomial.X - Polynomial.C (α k)) := hfac
      _ = Polynomial.C ((Q.leadingCoeff : ℂ)) *
          ((Polynomial.X - Polynomial.C (α i)) * qic α i) := by
            rw [prod_univ_eq_mul_erase (f := fun k : Fin n => (Polynomial.X - Polynomial.C (α k))) (i := i)]
            rfl
      _ = (Polynomial.X - Polynomial.C (α i)) *
          (Polynomial.C ((Q.leadingCoeff : ℂ)) * qic α i) := by ring
  have hdiv : (Q.map (algebraMap ℤ ℂ)) /ₘ (Polynomial.X - Polynomial.C (α i)) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * qic α i := by
    rw [hQ]
    exact Polynomial.mul_divByMonic_cancel_left
      (p := Polynomial.C ((Q.leadingCoeff : ℂ)) * qic α i)
      (q := (Polynomial.X - Polynomial.C (α i))) (Polynomial.monic_X_sub_C (α i))
  exact hdiv.symm

/-- Coefficient of the scaled quotient equals the synthetic-division expression. -/
lemma qic_lead_coeff {n : ℕ} (Q : Polynomial ℤ) (hQn : Q.natDegree = n)
    (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)))
    (i : Fin n) (j : ℕ) :
    (Polynomial.C ((Q.leadingCoeff : ℂ)) * qic α i).coeff j =
      ∑ t ∈ Finset.Icc (j + 1) Q.natDegree,
        (α i) ^ (t - (j + 1)) * (Q.map (algebraMap ℤ ℂ)).coeff t := by
  rw [qic_lead_eq_divByMonic Q α hfac i]
  rw [Polynomial.coeff_divByMonic_X_sub_C (p := Q.map (algebraMap ℤ ℂ)) (a := α i) (n := j)]
  congr 1
  congr 1
  rw [Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℤ ℂ) Int.cast_injective Q]

/-- Value-relation: the dual value equals the evaluation of `Dpoly Q d` at `α i`. -/
lemma cvalc_eq_eval_D {n : ℕ} (Q : Polynomial ℤ) (hQn : Q.natDegree = n)
    (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)))
    (d : Fin n → ℤ) (i : Fin n) :
    cvalc Q α d i = eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ)) := by
  unfold cvalc
  trans eval (α i) (∑ j : Fin n,
      Polynomial.C ((d j : ℂ)) *
        ((rq Q (j.val)).map (algebraMap ℤ ℂ)))
  · rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j hj
    have hcoeff : ((Q.leadingCoeff : ℂ) * (qic α i).coeff (j.val)) =
        eval (α i) ((rq Q (j.val)).map (algebraMap ℤ ℂ)) := by
      calc
        (Q.leadingCoeff : ℂ) * (qic α i).coeff (j.val)
            = (Polynomial.C ((Q.leadingCoeff : ℂ)) * qic α i).coeff (j.val) := by simp
        _ = ∑ t ∈ Finset.Icc (j.val + 1) Q.natDegree,
              (α i) ^ (t - (j.val + 1)) * (Q.map (algebraMap ℤ ℂ)).coeff t := by
              rw [qic_lead_coeff Q hQn α hfac i (j.val)]
        _ = eval (α i) ((rq Q (j.val)).map (algebraMap ℤ ℂ)) := by
              symm
              exact rq_eval Q α i (j.val)
    calc
      (d j : ℂ) * ((Q.leadingCoeff : ℂ) * (qic α i).coeff (j.val))
          = (d j : ℂ) * eval (α i) ((rq Q (j.val)).map (algebraMap ℤ ℂ)) := by rw [hcoeff]
      _ = eval (α i) (Polynomial.C ((d j : ℂ)) * ((rq Q (j.val)).map (algebraMap ℤ ℂ))) := by
            rw [Polynomial.eval_mul, Polynomial.eval_C]
  · apply congrArg (eval (α i))
    rw [Dpoly]
    rw [polynomial_map_finset_sum (algebraMap ℤ ℂ)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Polynomial.map_mul, Polynomial.map_C]
    simp

/-- General injectivity of `Dpoly Q d` when the leading coefficient is nonzero. -/
lemma coeff_Dpoly_eq_d_lead {n : ℕ} (Q : Polynomial ℤ) (hQn : Q.natDegree = n)
    (d : Fin n → ℤ) (e : Fin n) (hind : ∀ j : Fin n, j.val < e.val → d j = 0) :
    (Dpoly Q d).coeff (n - 1 - e.val) = d e * Q.leadingCoeff := by
  have hside : ∀ j ∈ (Finset.univ : Finset (Fin n)), j ≠ e →
      (Polynomial.C (d j) * rq Q (j.val)).coeff (n - 1 - e.val) = 0 := by
    intro j hj hje
    by_cases hlt : j.val < e.val
    · have dj : d j = 0 := hind j hlt
      rw [Polynomial.coeff_C_mul, dj]
      simp
    · have hgt : e.val < j.val := by
        have hval : j.val ≠ e.val := by
          intro hv
          exact hje (Fin.ext hv)
        omega
      rw [Polynomial.coeff_C_mul]
      rw [rq_coeff_eq_zero Q (j := j.val) (m := n - 1 - e.val) (by
        rw [hQn]
        omega)]
      simp
  have he_not : e ∉ (Finset.univ : Finset (Fin n)) →
      (Polynomial.C (d e) * rq Q (e.val)).coeff (n - 1 - e.val) = 0 := by
    intro henot
    exact (henot (Finset.mem_univ e)).elim
  calc
    (Dpoly Q d).coeff (n - 1 - e.val)
        = (Polynomial.C (d e) * rq Q (e.val)).coeff (n - 1 - e.val) := by
            rw [Dpoly, coeff_fintype_sum]
            exact Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n)))
              (f := fun j : Fin n => (Polynomial.C (d j) * rq Q (j.val)).coeff (n - 1 - e.val))
              (a := e) hside he_not
    _ = d e * Q.leadingCoeff := by
          rw [Polynomial.coeff_C_mul]
          rw [show (rq Q (e.val)).coeff (n - 1 - e.val) = Q.coeff Q.natDegree by
            simpa [hQn] using (rq_coeff_self Q (j := e.val) (by simpa [hQn] using e.isLt))]
          rfl

lemma d_eq_zero_of_Dpoly_lead {n : ℕ} (Q : Polynomial ℤ) (hQn : Q.natDegree = n)
    (hc0 : Q.leadingCoeff ≠ 0) (d : Fin n → ℤ) (hD : Dpoly Q d = 0) : d = 0 := by
  classical
  have hstep : ∀ k : ℕ, (∀ m < k, ∀ j : Fin n, j.val = m → d j = 0) →
      ∀ j : Fin n, j.val = k → d j = 0 := by
    intro k ih j hk
    have hind : ∀ a : Fin n, a.val < j.val → d a = 0 := by
      intro a ha
      exact ih a.val (by rw [← hk]; exact ha) a rfl
    have hcoef := coeff_Dpoly_eq_d_lead Q hQn d j hind
    have hfromD := congrArg (fun P : Polynomial ℤ => P.coeff (n - 1 - j.val)) hD
    rw [hcoef] at hfromD
    have hdjc : d j * Q.leadingCoeff = 0 := by simpa using hfromD
    exact (mul_eq_zero.mp hdjc).resolve_right hc0
  funext e
  exact (Nat.strong_induction_on e.val (p := fun k => ∀ j : Fin n, j.val = k → d j = 0) hstep) e rfl

/-- `Res(r·f, g) = r^{deg g}·Res(f,g)` with default degree parameters. -/
lemma resultant_C_mul_left_default {R : Type*} [CommRing R] [IsDomain R] (r : R) (f g : R[X])
    (hr : r ≠ 0) (hf : f ≠ 0) :
    (C r * f).resultant g = r ^ g.natDegree * f.resultant g := by
  have hdeg : (C r * f).natDegree = f.natDegree := by
    rw [Polynomial.natDegree_C_mul hr]
  calc
    (C r * f).resultant g
        = (C r * f).resultant g (C r * f).natDegree g.natDegree := rfl
    _ = r ^ g.natDegree * f.resultant g (C r * f).natDegree g.natDegree := by
          rw [Polynomial.resultant_C_mul_left (f := f) (g := g)
            (m := (C r * f).natDegree) (n := g.natDegree) (r := r)]
    _ = r ^ g.natDegree * f.resultant g := by
          congr 1
          simpa [hdeg]

/-- `d ≠ 0` implies some dual value is nonzero. -/
lemma exists_cvalc_ne_zero {n : ℕ} (Q : Polynomial ℤ) (hQ0 : Q ≠ 0) (hQn : Q.natDegree = n)
    (hn : 1 ≤ n) (α : Fin n → ℂ) (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)))
    (d : Fin n → ℤ) (hd : d ≠ 0) : ∃ i : Fin n, cvalc Q α d i ≠ 0 := by
  by_contra h
  push Not at h
  have heval : ∀ i : Fin n, eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ)) = 0 := by
    intro i
    rw [← cvalc_eq_eval_D Q hQn α hfac d i]
    exact h i
  have hDc0 : (Dpoly Q d).map (algebraMap ℤ ℂ) = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (p := (Dpoly Q d).map (algebraMap ℤ ℂ)) (f := α)
    · exact hαinj
    · exact heval
    · simpa using Dc_natDegree_lt Q hQn hn d
  have hD0 : Dpoly Q d = 0 := by
    exact (Polynomial.map_eq_zero_iff (f := algebraMap ℤ ℂ) (Int.cast_injective)).mp hDc0
  have hc0 : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ0
  have hd0 : d = 0 := d_eq_zero_of_Dpoly_lead Q hQn hc0 d hD0
  exact hd hd0



-- ------------------------------------------------ Component R: resultant identities (general, with c)

lemma prod_map_X_sub_C {n : ℕ} (α : Fin n → ℂ) :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))).map
        (Polynomial.C : ℂ →+* Polynomial ℂ)
      = ∏ i : Fin n, (Polynomial.X - Polynomial.C (Polynomial.C (α i))) := by
  rw [polynomial_map_finset_prod (Polynomial.C : ℂ →+* Polynomial ℂ)
    (s := (Finset.univ : Finset (Fin n))) (f := fun i : Fin n => (Polynomial.X - Polynomial.C (α i)))]
  apply Finset.prod_congr rfl
  intro i hi
  simp [Polynomial.map_sub]

lemma prod_X_sub_C_ne_zero {n : ℕ} (α : Fin n → ℂ) :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))) ≠ 0 := by
  classical
  exact (Finset.prod_ne_zero_iff (s := (Finset.univ : Finset (Fin n)))
      (f := fun i : Fin n => (Polynomial.X - Polynomial.C (α i)))).mpr (by
    intro i hi
    exact Polynomial.Monic.ne_zero (Polynomial.monic_X_sub_C (α i)))

/-- The resultant of `Qc Q` with `T − D(X)` over `ℂ[T]`: with
`Qc Q = C c · ∏ (X − C α_i)` it factors as `C(c)^s · ∏_i (T − D(α_i))`. -/
lemma res_complex_gen {n : ℕ} (Q : Polynomial ℤ) (hQ0 : Q ≠ 0) (hQn : Q.natDegree = n)
    (α : Fin n → ℂ) (d : Fin n → ℤ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))) :
    let Dc : Polynomial ℂ := (Dpoly Q d).map (algebraMap ℤ ℂ)
    let g : Polynomial (Polynomial ℂ) := Polynomial.C (Polynomial.X : Polynomial ℂ) -
        Dc.map (Polynomial.C : ℂ →+* Polynomial ℂ)
    ((Q.map (algebraMap ℤ ℂ)).map (Polynomial.C : ℂ →+* Polynomial ℂ)).resultant g
      = (Polynomial.C ((Q.leadingCoeff : ℂ))) ^ g.natDegree
        * ∏ i : Fin n, (Polynomial.X - Polynomial.C (eval (α i) Dc)) := by
  intro Dc g
  have hc0 : (Q.leadingCoeff : ℂ) ≠ 0 := by
    exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr hQ0
  have hfacmap : (Q.map (algebraMap ℤ ℂ)).map (Polynomial.C : ℂ →+* Polynomial ℂ)
      = Polynomial.C (Polynomial.C ((Q.leadingCoeff : ℂ))) *
          (∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))).map (Polynomial.C : ℂ →+* Polynomial ℂ) := by
    rw [hfac]
    rw [Polynomial.map_mul, Polynomial.map_C]
  have hmain : ((Q.map (algebraMap ℤ ℂ)).map (Polynomial.C : ℂ →+* Polynomial ℂ)).resultant g
      = Polynomial.C ((Q.leadingCoeff : ℂ)) ^ g.natDegree *
          ((∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))).map
            (Polynomial.C : ℂ →+* Polynomial ℂ)).resultant g := by
    rw [hfacmap]
    have hlem := resultant_C_mul_left_default (R := Polynomial ℂ)
      (r := Polynomial.C ((Q.leadingCoeff : ℂ)))
      (f := (∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))).map (Polynomial.C : ℂ →+* Polynomial ℂ))
      (g := g) (Polynomial.C_ne_zero.mpr hc0) (by
        apply Polynomial.map_ne_zero
        exact prod_X_sub_C_ne_zero α)
    exact hlem
  have hm2 : Polynomial.C ((Q.leadingCoeff : ℂ)) ^ g.natDegree *
          ((∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))).map
            (Polynomial.C : ℂ →+* Polynomial ℂ)).resultant g
      = Polynomial.C ((Q.leadingCoeff : ℂ)) ^ g.natDegree *
          ∏ i : Fin n, eval (Polynomial.C (α i)) g := by
    rw [prod_map_X_sub_C α]
    rw [resultant_prod_X_sub_C (R := Polynomial ℂ)
      (a := fun i : Fin n => Polynomial.C (α i)) (g := g)]
  have hm3 : Polynomial.C ((Q.leadingCoeff : ℂ)) ^ g.natDegree *
          ∏ i : Fin n, eval (Polynomial.C (α i)) g
      = Polynomial.C ((Q.leadingCoeff : ℂ)) ^ g.natDegree *
          ∏ i : Fin n, (Polynomial.X - Polynomial.C (eval (α i) Dc)) := by
    apply congrArg (fun u => Polynomial.C ((Q.leadingCoeff : ℂ)) ^ g.natDegree * u)
    apply Finset.prod_congr rfl
    intro i hi
    have hev : eval (Polynomial.C (α i)) g =
        Polynomial.X - Polynomial.C (eval (α i) Dc) := by
      change eval (Polynomial.C (α i)) (Polynomial.C (Polynomial.X : Polynomial ℂ) -
          Dc.map (Polynomial.C : ℂ →+* Polynomial ℂ))
          = Polynomial.X - Polynomial.C (eval (α i) Dc)
      rw [Polynomial.eval_sub, Polynomial.eval_C]
      rw [map_eval_C Dc (α i)]
    exact hev
  exact hmain.trans (hm2.trans hm3)

/-- The resultant over `ℤ[T]`, mapped to `ℂ[T]`, factors as `C(c)^s·∏_i (T − D(α_i))`. -/
lemma res_int_gen {n : ℕ} (Q : Polynomial ℤ) (hQ0 : Q ≠ 0) (hQn : Q.natDegree = n)
    (α : Fin n → ℂ) (d : Fin n → ℤ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))) :
    let Dc : Polynomial ℂ := (Dpoly Q d).map (algebraMap ℤ ℂ)
    let gZ : Polynomial (Polynomial ℤ) := Polynomial.C (Polynomial.X : Polynomial ℤ) -
        (Dpoly Q d).map (Polynomial.C : ℤ →+* Polynomial ℤ)
    ((Q.map (Polynomial.C : ℤ →+* Polynomial ℤ)).resultant gZ).map (algebraMap ℤ ℂ)
      = (Polynomial.C ((Q.leadingCoeff : ℂ))) ^ gZ.natDegree
        * ∏ i : Fin n, (Polynomial.X - Polynomial.C (eval (α i) Dc)) := by
  intro Dc gZ
  let φ0 : ℤ →+* ℂ := algebraMap ℤ ℂ
  let Φ : Polynomial ℤ →+* Polynomial ℂ := Polynomial.mapRingHom φ0
  let fZ : Polynomial (Polynomial ℤ) := Q.map (Polynomial.C : ℤ →+* Polynomial ℤ)
  have hh : (Polynomial.mapRingHom φ0).comp (Polynomial.C : ℤ →+* Polynomial ℤ)
      = (Polynomial.C : ℂ →+* Polynomial ℂ).comp φ0 := by
    ext k
    simp
  have hf : fZ.map Φ = (Q.map φ0).map (Polynomial.C : ℂ →+* Polynomial ℂ) := by
    unfold fZ
    change (Q.map (Polynomial.C : ℤ →+* Polynomial ℤ)).map Φ
      = (Q.map φ0).map (Polynomial.C : ℂ →+* Polynomial ℂ)
    rw [Polynomial.map_map, Polynomial.map_map]
    exact congrArg (fun h : ℤ →+* Polynomial ℂ => Q.map h) hh
  have hg : gZ.map Φ = Polynomial.C (Polynomial.X : Polynomial ℂ) -
      ((Dpoly Q d).map φ0).map (Polynomial.C : ℂ →+* Polynomial ℂ) := by
    unfold gZ
    rw [Polynomial.map_sub]
    rw [show (Polynomial.C (Polynomial.X : Polynomial ℤ)).map Φ =
        Polynomial.C (Polynomial.X : Polynomial ℂ) by
      rw [Polynomial.map_C]
      simp [Φ]]
    rw [Polynomial.map_map, Polynomial.map_map]
    apply congrArg (fun p : Polynomial (Polynomial ℂ) =>
      Polynomial.C (Polynomial.X : Polynomial ℂ) - p)
    exact congrArg (fun h : ℤ →+* Polynomial ℂ => (Dpoly Q d).map h) hh
  have hres := resultant_map_comm (φ := Φ) (f := fZ) (g := gZ) (by
    exact Polynomial.map_injective φ0 Int.cast_injective)
  change (Polynomial.mapRingHom φ0) (fZ.resultant gZ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) ^ gZ.natDegree * ∏ i : Fin n, (Polynomial.X - Polynomial.C (eval (α i) Dc))
  rw [← hres]
  rw [hf, hg]
  have hcg := res_complex_gen Q hQ0 hQn α d hfac
  simp only at hcg
  rw [hcg]
  congr 1
  rw [← hg]
  rw [Polynomial.natDegree_map_eq_of_injective (f := Φ) (Polynomial.map_injective φ0 Int.cast_injective) gZ]





-- ------------------------------------------------ Component A: rationality of the product

/-- The monic polynomial `∏_i (X − C(eval(α_i) Dc))` is the complexification of a
rational polynomial (a resultant over `ℤ` divided by `c^s`). -/
lemma rat_poly_exists {n : ℕ} (Q : Polynomial ℤ) (hQ0 : Q ≠ 0) (hQn : Q.natDegree = n)
    (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)))
    (d : Fin n → ℤ) :
    ∃ FQ : Polynomial ℚ,
      FQ.map (algebraMap ℚ ℂ) =
        ∏ i : Fin n, (X - C (eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ)))) := by
  classical
  let resZ : Polynomial ℤ :=
    (Q.map (Polynomial.C : ℤ →+* Polynomial ℤ)).resultant
      (Polynomial.C (Polynomial.X : Polynomial ℤ) -
        (Dpoly Q d).map (Polynomial.C : ℤ →+* Polynomial ℤ))
  have hres := res_int_gen Q hQ0 hQn α d hfac
  dsimp at hres
  let F : Polynomial ℂ := ∏ i : Fin n, (X - C (eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ))))
  let s : ℕ := (Polynomial.C (Polynomial.X : Polynomial ℤ) -
        (Dpoly Q d).map (Polynomial.C : ℤ →+* Polynomial ℤ)).natDegree
  have hresF : resZ.map (algebraMap ℤ ℂ) = (Polynomial.C ((Q.leadingCoeff : ℂ))) ^ s * F := by
    unfold resZ s F
    simpa using hres
  have hc0 : (Q.leadingCoeff : ℂ) ≠ 0 := by exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr hQ0
  have hc0q : (Q.leadingCoeff : ℚ) ≠ 0 := by exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr hQ0
  let FQ : Polynomial ℚ := (resZ.map (algebraMap ℤ ℚ)) *
      Polynomial.C ((1 : ℚ) / ((Q.leadingCoeff : ℚ) ^ s))
  refine ⟨FQ, ?_⟩
  have hmapmap : FQ.map (algebraMap ℚ ℂ) = F := by
    unfold FQ
    rw [Polynomial.map_mul]
    have hmm : (resZ.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ) = resZ.map (algebraMap ℤ ℂ) := by
      apply Polynomial.ext
      intro m
      simp
    rw [hmm]
    rw [Polynomial.map_C]
    rw [hresF]
    let q : ℚ := (1 : ℚ) / ((Q.leadingCoeff : ℚ) ^ s)
    have hcq0 : (Q.leadingCoeff : ℚ) ^ s ≠ 0 := pow_ne_zero s hc0q
    have h1 : (algebraMap ℚ ℂ) q * (Q.leadingCoeff : ℂ) ^ s = 1 := by
      unfold q
      calc
        (algebraMap ℚ ℂ) (1 / ((Q.leadingCoeff : ℚ) ^ s)) * (Q.leadingCoeff : ℂ) ^ s
            = (algebraMap ℚ ℂ) (1 / ((Q.leadingCoeff : ℚ) ^ s)) *
                (algebraMap ℚ ℂ) ((Q.leadingCoeff : ℚ) ^ s) := by simp
        _ = (algebraMap ℚ ℂ) ((1 / ((Q.leadingCoeff : ℚ) ^ s)) * ((Q.leadingCoeff : ℚ) ^ s)) := by
              rw [← map_mul]
        _ = (algebraMap ℚ ℂ) 1 := by
              congr 1
              exact one_div_mul_cancel hcq0
        _ = 1 := by simp
    calc
      (Polynomial.C ((Q.leadingCoeff : ℂ)) ^ s * F) * Polynomial.C ((algebraMap ℚ ℂ) q)
          = (Polynomial.C ((Q.leadingCoeff : ℂ)) ^ s * Polynomial.C ((algebraMap ℚ ℂ) q)) * F := by ring
      _ = F := by
            have hC : (Polynomial.C ((Q.leadingCoeff : ℂ)) ^ s) *
                Polynomial.C ((algebraMap ℚ ℂ) q) = 1 := by
              rw [← Polynomial.C_pow]
              rw [← Polynomial.C_mul]
              have hs : (Q.leadingCoeff : ℂ) ^ s * (algebraMap ℚ ℂ) q = 1 := by
                calc
                  (Q.leadingCoeff : ℂ) ^ s * (algebraMap ℚ ℂ) q
                      = (algebraMap ℚ ℂ) q * (Q.leadingCoeff : ℂ) ^ s := by ring
                  _ = 1 := h1
              rw [hs]
              simp
            rw [hC, one_mul]
  exact hmapmap

-- ------------------------------------------------ Component C/D: an integer polynomial realising the product

lemma natDegree_prod_X_sub_C_le {n : ℕ} (a : Fin n → ℂ) :
    (∏ i : Fin n, (X - C (a i))).natDegree ≤ n := by
  classical
  let f : Fin n → ℂ[X] := fun i => (X - C (a i))
  have hmain : ∀ s : Finset (Fin n), (∏ i ∈ s, f i).natDegree ≤ s.card := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s his ih
      rw [Finset.prod_insert his]
      calc
        ((f i) * (∏ j ∈ s, f j)).natDegree ≤ (f i).natDegree + (∏ j ∈ s, f j).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ 1 + s.card := by
              have hdeg : (f i).natDegree ≤ 1 := by
                simp [f]
              omega
        _ = (insert i s).card := by
              rw [Finset.card_insert_of_notMem his]
              omega
  have hU : (∏ i : Fin n, (X - C (a i))) = (∏ i ∈ (Finset.univ : Finset (Fin n)), f i) := by
    simp [f]
  rw [hU]
  have := hmain (Finset.univ : Finset (Fin n))
  simpa using this

/-- The monic product over the values has an integer realisation (via coefficient-wise
integrality and rationality). -/
lemma int_poly_exists {n : ℕ} (Q : Polynomial ℤ) (hQ0 : Q ≠ 0) (hQn : Q.natDegree = n)
    (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)))
    (d : Fin n → ℤ) :
    ∃ FZ : Polynomial ℤ,
      FZ.map (algebraMap ℤ ℂ) =
        ∏ i : Fin n, (X - C (eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ)))) := by
  classical
  let F : Polynomial ℂ := ∏ i : Fin n, (X - C (eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ))))
  obtain ⟨FQ, hFQ⟩ := rat_poly_exists Q hQ0 hQn α hfac d
  -- hFQ : FQ.map (algebraMap ℚ ℂ) = F (definitionally the product)
  have hint : ∀ m : ℕ, IsIntegral ℤ (F.coeff m) := by
    intro m
    unfold F
    exact coeff_prod_X_sub_C_isIntegral (ι := Fin n)
      (c := fun i : Fin n => eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ)))
      (fun i => val_integral Q hQ0 hQn α hfac d i) m
  have hrational : ∀ m : ℕ, ∃ q : ℚ, (q : ℂ) = F.coeff m := by
    intro m
    refine ⟨FQ.coeff m, ?_⟩
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff m) hFQ
    calc
      (FQ.coeff m : ℂ) = (FQ.map (algebraMap ℚ ℂ)).coeff m := by simp
      _ = F.coeff m := hc
  let z : ℕ → ℤ := fun m => Classical.choose (int_of_isIntegral_rat (x := F.coeff m) (hint m) (hrational m))
  have hz : ∀ m : ℕ, (z m : ℂ) = F.coeff m := by
    intro m
    exact Classical.choose_spec (int_of_isIntegral_rat (x := F.coeff m) (hint m) (hrational m))
  
  have hFdeg : F.natDegree ≤ n := by
    unfold F
    exact natDegree_prod_X_sub_C_le (fun i : Fin n => eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ)))
  let FZ : Polynomial ℤ := ∑ m ∈ Finset.range (n + 1), Polynomial.C (z m) * Polynomial.X ^ m
  refine ⟨FZ, ?_⟩
  -- FZ.map φ = ∑ over range of C(z m : ℂ) X^m
  have hFZmap : FZ.map (algebraMap ℤ ℂ) =
      ∑ m ∈ Finset.range (n + 1), Polynomial.C ((z m : ℂ)) * Polynomial.X ^ m := by
    unfold FZ
    rw [polynomial_map_finset_sum (algebraMap ℤ ℂ)]
    apply Finset.sum_congr rfl
    intro m hm
    simp
  -- coefficient-wise equality with F
  rw [hFZmap]
  apply Polynomial.ext
  intro m
  by_cases hm : m ≤ n
  · -- m ∈ range (n+1)
    have hrange : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    have hz' : (z m : ℂ) = F.coeff m := hz m
    rw [coeff_finset_sum]
    calc
      (∑ r ∈ Finset.range (n + 1),
          (Polynomial.C ((z r : ℂ)) * Polynomial.X ^ r).coeff m)
          = (Polynomial.C ((z m : ℂ)) * Polynomial.X ^ m).coeff m := by
            refine Finset.sum_eq_single (s := Finset.range (n + 1))
              (f := fun r : ℕ => (Polynomial.C ((z r : ℂ)) * Polynomial.X ^ r).coeff m)
              (a := m) ?_ ?_
            · intro b hb hbm
              have hb0 : b ≠ m := hbm
              have hb1 : b < n + 1 := Finset.mem_range.mp hb
              rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
              simp [hb0.symm]
            · intro hnot
              exact (hnot hrange).elim
      _ = (z m : ℂ) := by
            rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
            simp
      _ = F.coeff m := hz'
  · have hmlt : n < m := Nat.lt_of_not_ge hm
    have hFm : F.coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hFdeg hmlt)
    rw [coeff_finset_sum]
    calc
      (∑ r ∈ Finset.range (n + 1),
          (Polynomial.C ((z r : ℂ)) * Polynomial.X ^ r).coeff m) = 0 := by
            apply Finset.sum_eq_zero
            intro r hr
            have hr1 : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
            have hrm : r ≠ m := by
              exact (ne_of_lt (lt_of_le_of_lt hr1 hmlt))
            rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
            simp [hrm.symm]
      _ = F.coeff m := by rw [hFm]

-- ------------------------------------------------ The theorem

/-- The general (non-monic) complex dual condition: for every nonzero integer
vector `d`, some `|Σ_j d_j · b_ij| ≥ 1`, `b_ij` = coefficient `j` of the
quotient `Q/(X − α_i)`. -/
theorem general_dual {n : ℕ} (hn : 1 ≤ n) (Q : Polynomial ℤ) (hQ0 : Q ≠ 0)
    (hQn : Q.natDegree = n) (α : Fin n → ℂ) (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) *
        ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)))
    (d : Fin n → ℤ) (hd : d ≠ 0) :
    ∃ i : Fin n, (1 : ℝ) ≤ ‖∑ j : Fin n,
      ((d j : ℂ) * ((Q.leadingCoeff : ℂ) * (qic α i).coeff (j.val)))‖ := by
  classical
  by_contra h
  have hsmall : ∀ i : Fin n, ‖cvalc Q α d i‖ < 1 := by
    intro i
    refine lt_of_not_ge ?_
    intro hle
    apply h
    refine ⟨i, ?_⟩
    simpa [cvalc] using hle
  obtain ⟨FZ, hFZ⟩ := int_poly_exists Q hQ0 hQn α hfac d
  have hprod_eq : (∏ i : Fin n, (X - C (eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ)))))
      = ∏ i : Fin n, (X - C (cvalc Q α d i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [cvalc_eq_eval_D Q hQn α hfac d i]
  have hmap : FZ.map (algebraMap ℤ ℂ) = ∏ i : Fin n, (X - C (cvalc Q α d i)) := by
    rw [hFZ, hprod_eq]
  have hne : ∃ i : Fin n, cvalc Q α d i ≠ 0 :=
    exists_cvalc_ne_zero Q hQ0 hQn hn α hαinj hfac d hd
  exact kronecker_contra FZ (fun i => cvalc Q α d i) hmap hne hsmall

end Submission.GeneralDual
