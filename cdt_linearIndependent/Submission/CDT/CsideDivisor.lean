import Mathlib
import Submission.CDT.CsideLocal
import Submission.Commons.Algebra.Polynomial.dvd_of_forall_rootMultiplicity_le
import Submission.Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_indicial_le
import Submission.Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_regular
import Submission.Commons.Algebra.Polynomial.dnum_def
import Submission.Commons.Algebra.Polynomial.iterate_deriv_div_dnum
import Submission.Commons.FieldTheory.RatFunc.zero_le_ordAtT_div_of_eval_ne_zero
import Submission.Commons.Algebra.Polynomial.rootMultiplicity_le_one_of_isCoprime_derivative
import Submission.Commons.Algebra.Polynomial.ne_zero_of_eval_eq_zero_of_isCoprime
import Submission.Commons.FieldTheory.RatFunc.exists_leading_term
import Submission.Commons.FieldTheory.RatFunc.ordInfT_mul
import Submission.Commons.FieldTheory.RatFunc.ordInfT_algebraMap

/-!
# The divisor bound for the C-side unknown `b₃`

The paper's Lemma `17functions` (CDT, arXiv:2408.15403, §"Functional Linear
Independence") reduces the functional linear independence of the `17`
functions to the analysis of the fourth-order equation

`Σᵢ (−1)ⁱ Dⁱ(γᵢ b₃) = −R`,   `γᵢ = cᵢ/c₄`,  `γ₄ = 1`,

with `c₃ = (y−4)y²Λnum`, `c₄ = (y−4)²y³R₄R₁₀`.  The five local bounds
`N₀ ≥ 0`, `N₄ ≥ 2`, `N_β ≥ 1` (β a root of `R₄`), `N_γ ≥ −1` (γ a root of
`R₁₀`), `N_∞ ≤ 5` (`Submission.CDT.CsideLocal`, `Submission.CDT.CsideInfty`)

give the factorisation `b₃ = ((y−4)²R₄/R₁₀)·Q` with `deg Q ≤ 9` (the paper's
equation `(b3eqlog)`), which is the direct analogue of the A-side
`Submission.CDT.DivisorBound.divisor_bound`.

This module supplies the two ingredients:

* `regular_bound` — the bound at a *non-singular* point (where all the `γᵢ`
  are regular): `0 ≤ ord_α b₃`.  This is what makes `R₁₀·b₃` a polynomial.
  It is proved from the commons indicial-exactness lemma
  `Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_indicial_le` with the
  constant data `e i = 0`, `m = −4`, `λ₄ = 1` (indicial value `(N)₄`);

* `cside_divisor_bound` — the assembly: `R₁₀·b₃` is a polynomial divisible by
  `(y−4)²R₄`, and the quotient `Q` has degree `≤ 9` (from `N_∞ ≤ 5`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace Submission.CDT.CsideDivisor

open Commons.FieldTheory.RatFunc

variable {K : Type*} [Field K]

/-! ## The bound at a non-singular point -/

/-- **The generic (non-singular point) bound.**  If the coefficients `γᵢ` of the eliminated
expression `Σᵢ (−1)ⁱ Dⁱ(γᵢ b)` are regular at `α` and `γ₄ = 1`, and `Σᵢ (−1)ⁱ Dⁱ(γᵢ b) = −R` with
`R` regular at `α`, then `b` has no pole at `α`: `0 ≤ ord_α b`. -/
theorem regular_bound {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {α : K} {b R : RatFunc K} (hb : b ≠ 0)
    (hR : (0 : WithTop ℤ) ≤ ordAtT α R)
    {γ : Fin 5 → RatFunc K} (hγ4 : γ 4 = 1)
    (hγ : ∀ i : Fin 5, (0 : WithTop ℤ) ≤ ordAtT α (γ i))
    (hsys : (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i]) (γ i * b))
      = -R) :
    (0 : ℤ) ≤ ordAt α b := by
  classical
  by_contra hcon
  have hNneg : ordAt α b < 0 := not_le.mp hcon
  obtain ⟨r, hr, hb'⟩ := exists_leading_term α hb
  have h := ordAtT_adjoint_eq_of_regular D hd α b hb r hr hb' γ hγ4 hγ hNneg
  rw [hsys] at h
  have h2 : (0 : WithTop ℤ) ≤ (((ordAt α b) - 4 : ℤ) : WithTop ℤ) := by
    rw [← h, ordAtT_neg]
    exact hR
  have h3 : (0 : ℤ) ≤ ordAt α b - 4 := WithTop.coe_le_coe.mp h2
  omega

/-- A quotient `p/q` in which `q` does not vanish at `α` is regular at `α` (the commons version
`Commons.FieldTheory.RatFunc.zero_le_ordAtT_div_of_eval_ne_zero`, imported here). -/
theorem zero_le_ordAtT_div_of_eval_ne_zero {K : Type*} [Field K] {p q : Polynomial K} {α : K}
    (hq : q.eval α ≠ 0) :
    (0 : WithTop ℤ) ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K) p
      / algebraMap (Polynomial K) (RatFunc K) q) :=
  Commons.FieldTheory.RatFunc.zero_le_ordAtT_div_of_eval_ne_zero hq


/-! ## The divisor bound -/

/-- **The C-side divisor bound** (the paper's `(b3eqlog)`).  Let `b` be a nonzero solution of the
eliminated fourth-order equation `Σᵢ (−1)ⁱ Dⁱ(γᵢ b) = −R` whose coefficient data is that of the
operator `LL`: `R₄` (degree `4`, squarefree, with `R₄(4) ≠ 0`, and no common root with `R₁₀`),
`R₁₀` (degree `10`, `R₁₀(4) ≠ 0`).  Assume the five local bounds

* `0 ≤ ord₀ b`, `2 ≤ ord₄ b`,
* `1 ≤ ord_β b` at every root `β` of `R₄`,
* `−1 ≤ ord_γ b` at every root `γ` of `R₁₀`,
* the generic bound `0 ≤ ord_α b` at every point where `R₄` and `R₁₀` are both nonzero
  (`Submission.CDT.CsideDivisor.regular_bound`),
* `N_∞ ≤ 5`, i.e. `ordInfT b ≤ 5`.

Then `R₁₀ · b` is a polynomial divisible by `(y−4)²R₄`, i.e.
`b = ((y−4)²R₄/R₁₀)·Q` with `Q` a polynomial of degree `≤ 9`. -/
theorem cside_divisor_bound {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {b : RatFunc K} (hb : b ≠ 0) {R4 R10 : Polynomial K} (hR4 : R4 ≠ 0) (hR10 : R10 ≠ 0)
    (hR4deg : R4.natDegree = 4) (hR10deg : R10.natDegree = 10)
    (hR4sq : ∀ β : K, R4.eval β = 0 → Polynomial.rootMultiplicity β R4 ≤ 1)
    (hcop : ∀ β : K, R4.eval β = 0 → R10.eval β ≠ 0)
    (h4R4 : R4.eval (4 : K) ≠ 0) (h4R10 : R10.eval (4 : K) ≠ 0)
    (h0b : (0 : ℤ) ≤ ordAt (0 : K) b) (h4b : (2 : ℤ) ≤ ordAt (4 : K) b)
    (hR4b : ∀ β : K, R4.eval β = 0 → (1 : ℤ) ≤ ordAt β b)
    (hR10b : ∀ γ : K, R10.eval γ = 0 → (-1 : ℤ) ≤ ordAt γ b)
    (hgen : ∀ α : K, R4.eval α ≠ 0 → R10.eval α ≠ 0 → α ≠ 0 → α ≠ 4 → (0 : ℤ) ≤ ordAt α b)
    (hinf : ordInfT b ≤ (5 : WithTop ℤ)) :
    ∃ Q : Polynomial K, Q.natDegree ≤ 9 ∧
      algebraMap (Polynomial K) (RatFunc K) R10 * b
        = algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C (4 : K)) ^ 2 * R4)
          * algebraMap (Polynomial K) (RatFunc K) Q := by
  classical
  have hamR10 : algebraMap (Polynomial K) (RatFunc K) R10 ≠ 0 := RatFunc.algebraMap_ne_zero hR10
  -- Step 1: `am R₁₀ * b` has nonnegative order everywhere.
  have hF : ∀ α : K, (0 : ℤ) ≤ ordAt α (algebraMap (Polynomial K) (RatFunc K) R10 * b) := by
    intro α
    rw [ordAt_mul α hamR10 hb]
    by_cases hgam : R10.eval α = 0
    · have h1 : (1 : ℤ) ≤ ordAt α (algebraMap (Polynomial K) (RatFunc K) R10) := by
        rw [ordAt_algebraMap]
        have hpos : 0 < Polynomial.rootMultiplicity α R10 :=
          (Polynomial.rootMultiplicity_pos hR10).mpr hgam
        omega
      have h2 := hR10b α hgam
      omega
    · have hz : ordAt α (algebraMap (Polynomial K) (RatFunc K) R10) = 0 := by
        rw [ordAt_algebraMap, Polynomial.rootMultiplicity_eq_zero (fun h => hgam h)]
        norm_num
      rw [hz]
      by_cases hbet : R4.eval α = 0
      · have h := hR4b α hbet
        omega
      · by_cases ha0 : α = 0
        · rw [ha0]
          have h := h0b
          omega
        · by_cases ha4 : α = 4
          · rw [ha4]
            have h := h4b
            omega
          · have h := hgen α hbet hgam ha0 ha4
            omega
  -- Step 2: `am R₁₀ * b` is an algebra-map of a polynomial `P`.
  have hdvd : (algebraMap (Polynomial K) (RatFunc K) R10 * b).denom
      ∣ (algebraMap (Polynomial K) (RatFunc K) R10 * b).num := by
    refine Commons.Algebra.Polynomial.dvd_of_forall_rootMultiplicity_le
      (RatFunc.denom_ne_zero _) (fun α => ?_)
    have h := hF α
    simp only [ordAt] at h
    omega
  obtain ⟨P, hP⟩ := hdvd
  have hP' : algebraMap (Polynomial K) (RatFunc K) R10 * b
      = algebraMap (Polynomial K) (RatFunc K) P := by
    conv_lhs => rw [← RatFunc.num_div_denom (algebraMap (Polynomial K) (RatFunc K) R10 * b)]
    rw [hP, map_mul,
      mul_div_cancel_left₀ _ (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _))]
  have hPne : P ≠ 0 := by
    intro h0
    exact (mul_ne_zero hamR10 hb) (by rw [hP', h0, map_zero])
  have hordP : ∀ α : K, ordAt α (algebraMap (Polynomial K) (RatFunc K) P)
      = ordAt α (algebraMap (Polynomial K) (RatFunc K) R10 * b) := fun α => by rw [hP']
  -- Step 3: `P` vanishes at `4` to order at least `2`.
  have h4ord : (2 : ℤ) ≤ ordAt (4 : K) (algebraMap (Polynomial K) (RatFunc K) P) := by
    rw [hordP 4, ordAt_mul _ hamR10 hb, ordAt_algebraMap,
      Polynomial.rootMultiplicity_eq_zero (fun h => h4R10 h)]
    have h := h4b
    omega
  have hnd4 : 2 ≤ Polynomial.rootMultiplicity (4 : K) P := by
    have h := h4ord
    rw [ordAt_algebraMap] at h
    exact_mod_cast h
  -- Step 4: `R₄ ∣ P`.
  have hmultR4 : ∀ α : K, Polynomial.rootMultiplicity α R4 ≤ Polynomial.rootMultiplicity α P := by
    intro α
    by_cases hbet : R4.eval α = 0
    · have h1 : (1 : ℤ) ≤ ordAt α (algebraMap (Polynomial K) (RatFunc K) P) := by
        rw [hordP α, ordAt_mul _ hamR10 hb, ordAt_algebraMap,
          Polynomial.rootMultiplicity_eq_zero (fun hh => hcop α hbet hh)]
        have h := hR4b α hbet
        omega
      rw [ordAt_algebraMap] at h1
      have h1' : 1 ≤ Polynomial.rootMultiplicity α P := by omega
      exact le_trans (hR4sq α hbet) h1'
    · rw [Polynomial.rootMultiplicity_eq_zero (fun hh => hbet hh)]
      exact Nat.zero_le _
  -- Step 5: `(y−4)²·R₄ ∣ P`.
  have hDne : (Polynomial.X - Polynomial.C (4 : K)) ^ 2 * R4 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero 4)) hR4
  have hz4R4 : Polynomial.rootMultiplicity (4 : K) R4 = 0 :=
    Polynomial.rootMultiplicity_eq_zero (fun h => h4R4 h)
  have hzX : ∀ α : K, α ≠ 4 →
      Polynomial.rootMultiplicity α ((Polynomial.X - Polynomial.C (4 : K)) ^ 2) = 0 := by
    intro α ha
    refine Polynomial.rootMultiplicity_eq_zero (fun h => ?_)
    rw [Polynomial.IsRoot.def, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at h
    exact pow_ne_zero 2 (sub_ne_zero.mpr ha) h
  have hprod : ((Polynomial.X - Polynomial.C (4 : K)) ^ 2 * R4) ∣ P := by
    refine Commons.Algebra.Polynomial.dvd_of_forall_rootMultiplicity_le hDne (fun α => ?_)
    rw [Polynomial.rootMultiplicity_mul hDne]
    by_cases ha4 : α = 4
    · subst ha4
      rw [Polynomial.rootMultiplicity_X_sub_C_pow, hz4R4, add_zero]
      exact hnd4
    · rw [hzX α ha4, zero_add]
      exact hmultR4 α
  obtain ⟨Q, hQ⟩ := hprod
  refine ⟨Q, ?_, ?_⟩
  · -- the degree bound, from `N_∞ ≤ 5`
    have hQne : Q ≠ 0 := fun h0 => hPne (by rw [hQ, h0, mul_zero])
    have hDdeg : ((Polynomial.X - Polynomial.C (4 : K)) ^ 2 * R4).natDegree = 6 := by
      rw [Polynomial.natDegree_mul (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero 4)) hR4,
        Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, hR4deg]
    have hinfZ : RatFunc.intDegree b ≤ 5 := by
      have h : ordInfT b = (RatFunc.intDegree b : WithTop ℤ) := ordInfT_eq_coe_intDegree hb
      rw [h] at hinf
      exact WithTop.coe_le_coe.mp hinf
    have hA : RatFunc.intDegree (algebraMap (Polynomial K) (RatFunc K) P)
        = RatFunc.intDegree (algebraMap (Polynomial K) (RatFunc K)
            ((Polynomial.X - Polynomial.C (4 : K)) ^ 2 * R4))
          + RatFunc.intDegree (algebraMap (Polynomial K) (RatFunc K) Q) := by
      rw [hQ, map_mul,
        RatFunc.intDegree_mul (RatFunc.algebraMap_ne_zero hDne) (RatFunc.algebraMap_ne_zero hQne)]
    have hkey : RatFunc.intDegree (algebraMap (Polynomial K) (RatFunc K) Q) + 6
        = 10 + RatFunc.intDegree b := by
      calc RatFunc.intDegree (algebraMap (Polynomial K) (RatFunc K) Q) + 6
          = RatFunc.intDegree (algebraMap (Polynomial K) (RatFunc K)
              ((Polynomial.X - Polynomial.C (4 : K)) ^ 2 * R4))
            + RatFunc.intDegree (algebraMap (Polynomial K) (RatFunc K) Q) := by
            simp only [RatFunc.intDegree_polynomial]
            rw [hDdeg]
            ring
        _ = RatFunc.intDegree (algebraMap (Polynomial K) (RatFunc K) P) := hA.symm
        _ = RatFunc.intDegree (algebraMap (Polynomial K) (RatFunc K) R10 * b) := by rw [← hP']
        _ = RatFunc.intDegree (algebraMap (Polynomial K) (RatFunc K) R10) + RatFunc.intDegree b :=
            RatFunc.intDegree_mul hamR10 hb
        _ = 10 + RatFunc.intDegree b := by
            rw [RatFunc.intDegree_polynomial, hR10deg]
            ring
    have h15 : (Polynomial.natDegree Q : ℤ) ≤ 9 := by
      have h := hkey
      rw [RatFunc.intDegree_polynomial] at h
      omega
    omega
  · rw [hP', hQ, map_mul]


/-! ## Clearing denominators in the eliminated equation -/

/-- **Clearing denominators in the adjoint (eliminated) equation.**

Let `b = p/q` be a rational function and `c` the polynomial coefficient vector of an operator with
leading coefficient `c₄ ≠ 0`.  If `Σᵢ (−1)ⁱ Dⁱ((cᵢ/c₄)·b) = S`, then after clearing the denominators
`(c₄q)^{i+1}` of the individual terms one gets the *polynomial* identity

`Σᵢ (−1)ⁱ · dnum (cᵢp) (c₄q) i · (c₄q)^{4−i} = (c₄q)^5 · S`

(equality in `K(X)`; both sides are in fact the algebra-map of a polynomial when `S` is a rational
function with the appropriate denominator).  This is the bridge from the rational/analytic system of
CDT arXiv:2408.15403 Lemma `17functions` (`(onceagain)`) to the polynomial linear algebra of the
`10 × 10` determinant; it is the C-side analogue of `Submission.CDT.InfinityBound.POLYq_mul_X2`.

Proof: `γᵢ·b = (cᵢp)/(c₄q)` and `Dⁱ(f/g) = dnum f g i / g^{i+1}`
(`Commons.Algebra.Polynomial.iterate_deriv_div_dnum`); multiply the whole identity by `(c₄q)^5` and
use `(c₄q)^5/(c₄q)^{i+1} = (c₄q)^{4−i}`. -/
theorem adjoint_cleared {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {c : Fin 5 → Polynomial K} (hc4 : c 4 ≠ 0)
    {p q : Polynomial K} (hq : q ≠ 0)
    {b S : RatFunc K}
    (hb : b = algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q)
    (hsys : (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i])
        (algebraMap (Polynomial K) (RatFunc K) (c i) / algebraMap (Polynomial K) (RatFunc K) (c 4)
          * b)) = S) :
    (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) •
        (algebraMap (Polynomial K) (RatFunc K) (Commons.Algebra.Polynomial.dnum (c i * p) (c 4 * q) (i : ℕ))
          * (algebraMap (Polynomial K) (RatFunc K) (c 4 * q)) ^ (4 - (i : ℕ))))
      = (algebraMap (Polynomial K) (RatFunc K) (c 4 * q)) ^ 5 * S := by
  classical
  set E : RatFunc K := algebraMap (Polynomial K) (RatFunc K) (c 4 * q) with hE
  have hcq : c 4 * q ≠ 0 := mul_ne_zero hc4 hq
  have hE0 : E ≠ 0 := by rw [hE]; exact RatFunc.algebraMap_ne_zero hcq
  have hterm : ∀ i : Fin 5, ((fun x : RatFunc K => D x)^[i])
      (algebraMap (Polynomial K) (RatFunc K) (c i) / algebraMap (Polynomial K) (RatFunc K) (c 4)
        * b)
      = algebraMap (Polynomial K) (RatFunc K) (Commons.Algebra.Polynomial.dnum (c i * p) (c 4 * q) (i : ℕ))
        / E ^ ((i : ℕ) + 1) := by
    intro i
    have hγ : algebraMap (Polynomial K) (RatFunc K) (c i) / algebraMap (Polynomial K) (RatFunc K) (c 4)
          * b
        = algebraMap (Polynomial K) (RatFunc K) (c i * p) / E := by
      rw [hb, hE]
      simp only [map_mul]
      field_simp
    rw [hγ]
    exact Commons.Algebra.Polynomial.iterate_deriv_div_dnum D hd (c i * p) (c 4 * q) hcq (i : ℕ)
  have hstep : ∀ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i])
        (algebraMap (Polynomial K) (RatFunc K) (c i) / algebraMap (Polynomial K) (RatFunc K) (c 4)
          * b) * E ^ 5
      = (-1 : ℤ) ^ (i : ℕ) •
          (algebraMap (Polynomial K) (RatFunc K) (Commons.Algebra.Polynomial.dnum (c i * p) (c 4 * q) (i : ℕ))
            * E ^ (4 - (i : ℕ))) := by
    intro i
    rw [hterm i]
    have hle : (i : ℕ) + 1 ≤ 5 := by have := i.isLt; omega
    have hinner : algebraMap (Polynomial K) (RatFunc K)
          (Commons.Algebra.Polynomial.dnum (c i * p) (c 4 * q) (i : ℕ)) / E ^ ((i : ℕ) + 1) * E ^ 5
        = algebraMap (Polynomial K) (RatFunc K)
          (Commons.Algebra.Polynomial.dnum (c i * p) (c 4 * q) (i : ℕ)) * E ^ (4 - (i : ℕ)) := by
      rw [div_mul_eq_mul_div, mul_div_assoc,
        show E ^ 5 / E ^ ((i : ℕ) + 1) = E ^ (4 - (i : ℕ)) from by
          rw [div_eq_iff (pow_ne_zero _ hE0), ← pow_add]
          congr 1
          omega]
    rw [smul_mul_assoc, hinner]
  have key : (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i])
        (algebraMap (Polynomial K) (RatFunc K) (c i) / algebraMap (Polynomial K) (RatFunc K) (c 4)
          * b)) * E ^ 5
      = ∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) •
          (algebraMap (Polynomial K) (RatFunc K) (Commons.Algebra.Polynomial.dnum (c i * p) (c 4 * q) (i : ℕ))
            * E ^ (4 - (i : ℕ))) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => hstep i)
  rw [hsys] at key
  rw [← key]
  ring


/-- **The divisor bound in the paper's own form**: `b = ((y−4)²R₄/R₁₀)·Q` with `deg Q ≤ 9`
(CDT arXiv:2408.15403, equation `(b3eqlog)`, with the notation `Q = q₀ + q₁y + … + q₉y⁹`). -/
theorem cside_divisor_bound_div {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {b : RatFunc K} (hb : b ≠ 0) {R4 R10 : Polynomial K} (hR4 : R4 ≠ 0) (hR10 : R10 ≠ 0)
    (hR4deg : R4.natDegree = 4) (hR10deg : R10.natDegree = 10)
    (hR4sq : ∀ β : K, R4.eval β = 0 → Polynomial.rootMultiplicity β R4 ≤ 1)
    (hcop : ∀ β : K, R4.eval β = 0 → R10.eval β ≠ 0)
    (h4R4 : R4.eval (4 : K) ≠ 0) (h4R10 : R10.eval (4 : K) ≠ 0)
    (h0b : (0 : ℤ) ≤ ordAt (0 : K) b) (h4b : (2 : ℤ) ≤ ordAt (4 : K) b)
    (hR4b : ∀ β : K, R4.eval β = 0 → (1 : ℤ) ≤ ordAt β b)
    (hR10b : ∀ γ : K, R10.eval γ = 0 → (-1 : ℤ) ≤ ordAt γ b)
    (hgen : ∀ α : K, R4.eval α ≠ 0 → R10.eval α ≠ 0 → α ≠ 0 → α ≠ 4 → (0 : ℤ) ≤ ordAt α b)
    (hinf : ordInfT b ≤ (5 : WithTop ℤ)) :
    ∃ Q : Polynomial K, Q.natDegree ≤ 9 ∧
      b = algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C (4 : K)) ^ 2 * R4)
        * algebraMap (Polynomial K) (RatFunc K) Q
        / algebraMap (Polynomial K) (RatFunc K) R10 := by
  obtain ⟨Q, hdeg, hQ⟩ := cside_divisor_bound hb hR4 hR10 hR4deg hR10deg hR4sq hcop h4R4 h4R10
    h0b h4b hR4b hR10b hgen hinf
  refine ⟨Q, hdeg, ?_⟩
  rw [eq_div_iff (RatFunc.algebraMap_ne_zero hR10), mul_comm b]
  exact hQ

/-- **The generic (non-singular point) bound for the paper's coefficient data.**  The `spec`-form of
`regular_bound`, i.e. the C-side companion of
`Submission.CDT.CsideLocal.local_bound_at_root_of_R4_spec`: if `α ∉ {0,4}` is a root of neither
`R₄` nor `R₁₀` — so that the common denominator `cden = (y−4)yR₄R₁₀` of the paper's `γᵢ = cᵢ/c₄` does
not vanish — then a solution `bb` of the eliminated equation has no pole at `α`. -/
theorem regular_bound_spec {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (a b α : K)
    (hα0 : α ≠ 0) (hα4 : α ≠ 4)
    (hR4 : (CsideLocal.spec a b LL.R4).eval α ≠ 0)
    (hR10 : (CsideLocal.spec a b LL.R10).eval α ≠ 0)
    (bb R : RatFunc K) (hb : bb ≠ 0) (hR : (0 : WithTop ℤ) ≤ ordAtT α R)
    (g : Fin 5 → RatFunc K)
    (hg4 : g 4 = 1)
    (hg3 : g 3 = algebraMap (Polynomial K) (RatFunc K) (CsideLocal.spec a b LL.LambdaNum)
      / algebraMap (Polynomial K) (RatFunc K)
          (CsideLocal.cden (CsideLocal.spec a b LL.R4) (CsideLocal.spec a b LL.R10)))
    (hg012 : ∀ i : Fin 5, (i : ℕ) ≤ 2 → ∃ c : Polynomial K,
      g i = algebraMap (Polynomial K) (RatFunc K) c
        / algebraMap (Polynomial K) (RatFunc K)
            (CsideLocal.cden (CsideLocal.spec a b LL.R4) (CsideLocal.spec a b LL.R10)))
    (hsys : (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i]) (g i * bb)) = -R) :
    (0 : ℤ) ≤ ordAt α bb := by
  have hcden : (CsideLocal.cden (CsideLocal.spec a b LL.R4) (CsideLocal.spec a b LL.R10)).eval α
      ≠ 0 := by
    rw [CsideLocal.cden]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hα4) hα0) hR4) hR10
  refine regular_bound D hd hb hR ?_ ?_ hsys
  · exact hg4
  · intro i
    have h5 : (i : ℕ) < 5 := i.isLt
    rcases Nat.lt_or_ge (i : ℕ) 3 with h3 | h3
    · obtain ⟨c, hc⟩ := hg012 i (by omega)
      rw [hc]
      exact zero_le_ordAtT_div_of_eval_ne_zero hcden
    · rcases eq_or_lt_of_le h3 with h3' | h3'
      · rw [show i = 3 from Fin.ext h3'.symm, hg3]
        exact zero_le_ordAtT_div_of_eval_ne_zero hcden
      · have hi4 : i = 4 := by
          apply Fin.ext
          omega
        rw [hi4, hg4]
        simp [ordAtT, Commons.FieldTheory.RatFunc.ordAt_one]


/-- **The C-side divisor bound with Bézout-style hypotheses.**  The hypothesis `hR4sq`
(squarefreeness of `R₄`) is replaced by coprimality of `R₄` with its derivative and the hypothesis
`hcop` (no common root of `R₄, R₁₀`) by coprimality of `R₄` and `R₁₀` — the standard certificates
supplied by an explicit Bézout identity `a·R₄ + b·R₄' = C c` and `a·R₄ + b·R₁₀ = C c` with `c ≠ 0`
(see `Commons.Algebra.Polynomial.isCoprime_of_mul_add_eq_C_ne_zero`); the paper obtains them from
Lemma `(res)` (`R₄` irreducible, `R₄` coprime to `R₁₀`). -/
theorem cside_divisor_bound_of_isCoprime {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {b : RatFunc K} (hb : b ≠ 0) {R4 R10 : Polynomial K} (hR4 : R4 ≠ 0) (hR10 : R10 ≠ 0)
    (hR4der : IsCoprime R4 R4.derivative) (hR4R10 : IsCoprime R4 R10)
    (hR4deg : R4.natDegree = 4) (hR10deg : R10.natDegree = 10)
    (h4R4 : R4.eval (4 : K) ≠ 0) (h4R10 : R10.eval (4 : K) ≠ 0)
    (h0b : (0 : ℤ) ≤ ordAt (0 : K) b) (h4b : (2 : ℤ) ≤ ordAt (4 : K) b)
    (hR4b : ∀ β : K, R4.eval β = 0 → (1 : ℤ) ≤ ordAt β b)
    (hR10b : ∀ γ : K, R10.eval γ = 0 → (-1 : ℤ) ≤ ordAt γ b)
    (hgen : ∀ α : K, R4.eval α ≠ 0 → R10.eval α ≠ 0 → α ≠ 0 → α ≠ 4 → (0 : ℤ) ≤ ordAt α b)
    (hinf : ordInfT b ≤ (5 : WithTop ℤ)) :
    ∃ Q : Polynomial K, Q.natDegree ≤ 9 ∧
      b = algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C (4 : K)) ^ 2 * R4)
        * algebraMap (Polynomial K) (RatFunc K) Q
        / algebraMap (Polynomial K) (RatFunc K) R10 := by
  exact cside_divisor_bound_div hb hR4 hR10 hR4deg hR10deg
    (fun β hβ => Commons.Algebra.Polynomial.rootMultiplicity_le_one_of_isCoprime_derivative hR4der β)
    (fun β hβ => Commons.Algebra.Polynomial.ne_zero_of_eval_eq_zero_of_isCoprime hR4R10 hβ)
    h4R4 h4R10 h0b h4b hR4b hR10b hgen hinf


end Submission.CDT.CsideDivisor
