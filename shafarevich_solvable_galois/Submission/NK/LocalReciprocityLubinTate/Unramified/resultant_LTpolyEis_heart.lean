import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Submission.NK.LocalReciprocityLubinTate.Unramified.Heart.normOp_sub_mem_span_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped ValuativeRel

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.LocalReciprocityLubinTate.Unramified

universe u

noncomputable section

/-- Evaluation at `0` preserves divisibility by a constant: if `C (p ^ m)` divides `w` then
`p ^ m` divides `w.eval 0`.  Used to pass from the divisibility of the `i`-fold norm-operator
iterate of `g` (a polynomial) to the corresponding divisibility of its value at `0`, which is the
resultant `Res(f^{(i)}, g)`. -/
theorem eval_zero_mem_span_of_mem_span_C {A : Type u} [CommRing A] (p : A) (m : ℕ)
    (w : Polynomial A) (hw : w ∈ Ideal.span {Polynomial.C (p ^ m)}) :
    w.eval 0 ∈ Ideal.span {p ^ m} := by
  rw [Ideal.mem_span_singleton] at hw ⊢
  obtain ⟨s, rfl⟩ := hw
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  exact dvd_mul_right _ _

end

/-- **The resultant form of the hard half of Honda's norm computation** (Honda's reciprocity law,
the `⊆` half).  Let `F` be a characteristic-`0` nonarchimedean local field, `P ∈ 𝒪[F]` an
irreducible element, `q = residueCard F ≥ 2`, `n ≥ 1` and `g ∈ 𝒪[F][X]` a polynomial whose constant
coefficient is a *unit*.  Then the resultant of the Eisenstein factor
`E = LTpolyEis P q (n-1)` (monic of degree `(q-1)q^{n-1}`) with `g` is `≡ 1` modulo `P^n`:
`Polynomial.resultant (LTpolyEis P q (n-1)) g - 1 ∈ Ideal.span {P^n}`.

PROOF ROUTE (elementary: resultants + residue-field Frobenius + Newton identities; no formal group
law, no power-series Coleman operator).  Let `f := LTpoly P q = P·X + X^q`, `f^{(i)}` its iterate,
`Φ_i(g) := Res(f^{(i)}, g) = ∏_{α: f^{(i)}(α)=0} g(α)`, and define the operator
`R(h)(Y) := Res_X(f(X) - Y, h(X)) ∈ 𝒪[F][Y]` (use `Polynomial.resultant` on the ring `𝒪[F][Y]`,
mapping `f(X)-Y` and `h(X)` into `(𝒪[F][Y])[X]` along `Polynomial.C`).
1. `R` is multiplicative in `h`; and in a splitting field `R(h)(Y) = ∏_{f(α)=Y} h(α)`
   (`Polynomial.resultant_eq_prod_eval`).
2. `R(h) ≡ h` mod `P` coefficientwise.  Indeed mod `P`, `f(X) ≡ X^q`, so
   `R(h)(Y) ≡ ∏_{α^q=Y} h(α) = h(Y^{1/q})^q = Σ_j (h.coeff j)^q Y^j`, and `(h.coeff j)^q ≡ h.coeff j`
   mod `P` because the residue field `𝓀[F]` has `q` elements (Frobenius is the identity on `𝓀[F]`).
3. GAIN: if `h ≡ 1` mod `P^k`, `k ≥ 1`, then `R(h) ≡ 1` mod `P^{k+1}`.  Write `h = 1 + P^k t`; then
   `R(h) = ∏_{f(α)=Y}(1 + P^k t(α)) = 1 + P^k E_1(Y) + Σ_{k'≥2} P^{k k'} E_{k'}(Y)`, where `E_{k'}`
   is the `k'`-th elementary symmetric function of the values `t(α)`.  The terms with `k' ≥ 2` are
   divisible by `P^{k+1}`; and `E_1 = Σ_j t_j p_j(Y)` with `p_j(Y) = Σ_{f(α)=Y} α^j`, where
   `p_j ∈ P·𝒪[F][Y]` for all `j ≥ 1`: for `X^q + PX - Y` the elementary symmetric functions satisfy
   `e_i ≡ 0` mod `P` for `1 ≤ i ≤ q-1` and `e_q = ±Y`, so Newton's identities give
   `p_j ≡ ±Y p_{j-q} ≡ 0` mod `P` by induction.  Hence `E_1 ∈ P·𝒪[F][Y]`.
4. `Φ_i(h) = R^i(h)(0) = ∏_{α ∈ Λ_i} h(α)` for polynomials `h`, where `Λ_i = rootSet f^{(i)}`
   (induction on `i`, using 1. and `Λ_{i+1} = f^{-1}(Λ_i)`).
5. Put `h := R(g)·g^{-1} ∈ 𝒪[F][[Y]]` (a unit in the power-series ring, since `g.coeff 0` is a
   unit), so `h ≡ 1` mod `P` by 2.  By multiplicativity, `R^i(g) = g·∏_{j<i} R^j(h)`; hence
   `Φ_n(g)/Φ_{n-1}(g) = R^n(g)(0)/R^{n-1}(g)(0) = R^{n-1}(h)(0) = ∏_{α∈Λ_{n-1}} h(α)`.
   Iterating the gain lemma `n-1` times gives `R^{n-1}(h) ≡ 1` mod `P^n`, hence this ratio is `≡ 1`
   mod `P^n`.  (To stay polynomial, replace `h` by its truncation of degree `< D` with
   `D ≥ n·([K_{n-1}:F])²`, which agrees with `h` at all `α ∈ Λ_{n-1}` modulo `P^n`.)
6. Finally `Φ_n(g)/Φ_{n-1}(g) = Res(f^{(n)},g)/Res(f^{(n-1)},g) = Res(f^{[n-1]}, g)
   = Res(LTpolyEis P q (n-1), g)` using `LTpolyIter_succ_eq_mul` and multiplicativity of
   `resultant` in its first argument.  The general case reduces to `g.coeff 0 = 1` by scaling:
   `Res(E, c·h) = c^(deg E)·Res(E, h)` and `c^((q-1)q^{n-1}) ≡ 1` mod `P^n`.

IMPLEMENTATION NOTE (the route actually formalised here).  With `f = LTpoly P q`, `q = residueCard F`
and `𝒩 h = normOp f h` (`𝒩(h)(Y) = Res_X(f(X) - Y, h(X))`):

* `normOp_sub_self_mem_span` (`Unramified/LTGain.lean`, the "Frobenius step"): `𝒩 h ≡ h` mod `P`;
* `Heart.normOp_sub_mem_span_pow` (the **gain step**, proved in this workspace): `u - v ∈ (P^k)`
  with `k ≥ 1` implies `𝒩 u - 𝒩 v ∈ (P^{k+1})`;
* iterating the gain over the pair `(𝒩 g, g)` gives `𝒩 ^ n g - 𝒩 ^ {n-1} g ∈ (P ^ n)`;
* `resultant_LTpolyIter_eq_eval_normOp` identifies the value at `0` of `𝒩 ^ i u` with
  `Res(f^{(i)}, u) = (LTpolyIter P q i).resultant u`;
* `LTpolyIter_succ_eq_mul` and multiplicativity of the resultant in the first argument give
  `Res(f^{(n)}, g) = Res(E, g) · Res(f^{(n-1)}, g)`, and `isUnit_resultant_LTpolyIter` says the
  second factor is a unit, so the congruence `Res(f^{(n)}, g) ≡ Res(f^{(n-1)}, g)` mod `P ^ n`
  can be divided by it and yields `Res(E, g) ≡ 1` mod `P ^ n`.

The gain step itself is proved by the two-parameter (`s`-parametrised) resultant and the twisted
Frobenius formula, as described in the docstring of `Heart.normOp_sub_mem_span_pow`. -/
theorem resultant_LTpolyEis_heart {F : Type u} [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (P : ↥(ValuativeRel.valuation F).integer) (hP : Irreducible P) (n : ℕ) (hn : 1 ≤ n)
    (g : Polynomial ↥(ValuativeRel.valuation F).integer) (hg : IsUnit (g.coeff 0)) :
    Polynomial.resultant
        (NK.LocalReciprocityLubinTate.LTpolyEis P
          (NK.LocalReciprocityLubinTate.residueCard F) (n - 1)) g - 1
      ∈ Ideal.span {P ^ n} := by
  classical
  have hq : 2 ≤ residueCard F := two_le_residueCard F
  have hq1 : 1 ≤ residueCard F := by omega
  -- the quotient `𝒪[F] ⧸ (P)` is the residue field
  have hmax : (Ideal.span ({P} : Set ↥(ValuativeRel.valuation F).integer)).IsMaximal := by
    rw [← hP.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal.isMaximal _
  haveI : Field (↥(ValuativeRel.valuation F).integer ⧸ Ideal.span ({P} : Set _)) :=
    Ideal.Quotient.field _
  have hpow : IsFrobeniusPower P (residueCard F) := LubinTate.isFrobeniusPower_integers F P hP
  have hres : IsFrobeniusResidue P (residueCard F) :=
    (NK.LocalReciprocityLubinTate.LubinTate.isLubinTateCoeff_integers F P hP).2.1
  -- **Step 1 (`𝒩 g ≡ g` mod `P`)**: the Frobenius step of the norm operator.
  have hstep : normOp (LTpoly P (residueCard F)) g - g ∈ Ideal.span {Polynomial.C P} :=
    normOp_sub_self_mem_span (A := ↥(ValuativeRel.valuation F).integer) P (residueCard F) hq hpow
      hres g
  -- **Step 2 (the gain, iterated)**: `𝒩 ^ i` gains one power of `P` at each iteration.
  have hiter : ∀ (i : ℕ) (u v : Polynomial ↥(ValuativeRel.valuation F).integer),
      u - v ∈ Ideal.span {Polynomial.C P} →
      ((fun h => normOp (LTpoly P (residueCard F)) h)^[i]) u
        - ((fun h => normOp (LTpoly P (residueCard F)) h)^[i]) v
      ∈ Ideal.span {Polynomial.C (P ^ (1 + i))} := by
    intro i
    induction i with
    | zero => intro u v huv; simpa using huv
    | succ i ih =>
      intro u v huv
      have h1 := NK.LocalReciprocityLubinTate.Unramified.Heart.normOp_sub_mem_span_pow
        P hP (1 + i) (by omega)
        (((fun h => normOp (LTpoly P (residueCard F)) h)^[i]) u)
        (((fun h => normOp (LTpoly P (residueCard F)) h)^[i]) v) (ih u v huv)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [show 1 + i + 1 = 1 + (i + 1) from by omega] at h1
      exact h1
  -- apply it to the pair `(𝒩 g, g)`
  have hmain : ((fun h => normOp (LTpoly P (residueCard F)) h)^[n - 1])
        (normOp (LTpoly P (residueCard F)) g)
      - ((fun h => normOp (LTpoly P (residueCard F)) h)^[n - 1]) g
      ∈ Ideal.span {Polynomial.C (P ^ n)} := by
    have h := hiter (n - 1) (normOp (LTpoly P (residueCard F)) g) g hstep
    have h2 : 1 + (n - 1) = n := by omega
    rwa [h2] at h
  have heval : ((fun h => normOp (LTpoly P (residueCard F)) h)^[n]) g
      = ((fun h => normOp (LTpoly P (residueCard F)) h)^[n - 1])
        (normOp (LTpoly P (residueCard F)) g) := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    rw [Function.iterate_succ_apply]
  have hdiffEval : (((fun h => normOp (LTpoly P (residueCard F)) h)^[n]) g).eval 0
      - (((fun h => normOp (LTpoly P (residueCard F)) h)^[n - 1]) g).eval 0
      ∈ Ideal.span {P ^ n} := by
    have h := eval_zero_mem_span_of_mem_span_C P n _ hmain
    rw [Polynomial.eval_sub] at h
    rwa [← heval] at h
  -- **Step 3**: identify the values at `0` with the resultants `Res(f^{(i)}, g)`.
  have hres_n := resultant_LTpolyIter_eq_eval_normOp (F := F) P hP (residueCard F) n hq g
  have hres_nm :=
    resultant_LTpolyIter_eq_eval_normOp (F := F) P hP (residueCard F) (n - 1) hq g
  have hdiffRes : (LTpolyIter P (residueCard F) n).resultant g
      - (LTpolyIter P (residueCard F) (n - 1)).resultant g ∈ Ideal.span {P ^ n} := by
    rw [hres_n, hres_nm]
    exact hdiffEval
  -- **Step 4**: `Res(f^{(n)}, g) = Res(f^{[n-1]}, g) · Res(f^{(n-1)}, g)`.
  have hfac : LTpolyIter P (residueCard F) n
      = LTpolyEis P (residueCard F) (n - 1) * LTpolyIter P (residueCard F) (n - 1) := by
    have h := LTpolyIter_succ_eq_mul P (residueCard F) (n - 1) hq1
    rwa [show n - 1 + 1 = n from by omega] at h
  have hene : LTpolyEis P (residueCard F) (n - 1) ≠ 0 :=
    LTpolyEis_ne_zero P (residueCard F) (n - 1) hq
  have hhne : LTpolyIter P (residueCard F) (n - 1) ≠ 0 :=
    LTpolyIter_ne_zero P (residueCard F) (n - 1) hq
  have hunit : IsUnit ((LTpolyIter P (residueCard F) (n - 1)).resultant g) :=
    isUnit_resultant_LTpolyIter (F := F) P hP (residueCard F) (n - 1) hq g hg
  have hmult : (LTpolyIter P (residueCard F) n).resultant g
      = (LTpolyEis P (residueCard F) (n - 1)).resultant g
        * (LTpolyIter P (residueCard F) (n - 1)).resultant g := by
    rw [hfac]
    rw [show (LTpolyEis P (residueCard F) (n - 1)
          * LTpolyIter P (residueCard F) (n - 1)).resultant g
        = (LTpolyEis P (residueCard F) (n - 1)
          * LTpolyIter P (residueCard F) (n - 1)).resultant g
            ((LTpolyEis P (residueCard F) (n - 1)).natDegree
              + (LTpolyIter P (residueCard F) (n - 1)).natDegree) g.natDegree
        from by rw [Polynomial.natDegree_mul hene hhne]]
    rw [Polynomial.resultant_mul_left _ _ _ _ le_rfl]
  -- **Step 5**: divide by the unit `Res(f^{(n-1)}, g)`.
  have hfinal : ((LTpolyEis P (residueCard F) (n - 1)).resultant g - 1)
      * (LTpolyIter P (residueCard F) (n - 1)).resultant g ∈ Ideal.span {P ^ n} := by
    have h := hdiffRes
    rw [hmult] at h
    convert h using 1
    ring
  obtain ⟨u, hu⟩ := hunit
  have h2 := Ideal.mul_mem_left (Ideal.span {P ^ n})
    (↑u⁻¹ : ↥(ValuativeRel.valuation F).integer) hfinal
  rw [← hu] at h2
  convert h2 using 1
  rw [← mul_assoc, mul_comm (↑u⁻¹ : ↥(ValuativeRel.valuation F).integer)
    ((LTpolyEis P (residueCard F) (n - 1)).resultant g - 1), mul_assoc,
    u.inv_mul, mul_one]

end NK.LocalReciprocityLubinTate.Unramified
