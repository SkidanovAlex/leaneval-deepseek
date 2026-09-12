import Mathlib
import Submission.Commons.Analysis.MvPolynomial.isStable_closed
import Submission.Commons.Analysis.MvPolynomial.lowerHalfRoots_path
import Submission.Commons.Analysis.MvPolynomial.realRooted_limit_closed

noncomputable section
open MvPolynomial Polynomial
open scoped BigOperators Topology
open Complex

set_option autoImplicit false

namespace Commons.Analysis.MvPolynomial

/-! # Gårding bivariate nonvanishing

Supporting lemmas for `gch_bivariate` (and its negative-cone engine `gch_negcone_engine`).
The strategy follows the classical argument of Gårding (as in Pemantle's survey,
Proposition 2.6): hyperbolic with respect to `e` and `u` in the hyperbolicity cone
implies that on every affine plane `x + ℂe + ℂu` the polynomial has no zeros with
the coefficients of both `e` and `u` having positive imaginary part.
-/

/-! ## 1. basic evaluation identities -/

/-- Mapping the real line restriction to ℂ gives the ℂ-line restriction. -/
lemma mapRealAeval_eq_complexAeval {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (a e : Fin m → ℝ) :
    Polynomial.map (algebraMap ℝ ℂ) (MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H) =
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C ((a i : ℝ) : ℂ) + Polynomial.C ((e i : ℝ) : ℂ) * Polynomial.X) H := by
  classical
  let f : Fin m → Polynomial ℝ := fun i => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X
  let φ : Polynomial ℝ →ₐ[ℝ] Polynomial ℂ := Polynomial.mapAlgHom (Algebra.ofId ℝ ℂ)
  have h := MvPolynomial.comp_aeval_apply (R := ℝ) (S₁ := Polynomial ℝ) (f := f) (φ := φ) (p := H)
  change φ ((MvPolynomial.aeval (R := ℝ) f) H) =
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C ((a i : ℝ) : ℂ) + Polynomial.C ((e i : ℝ) : ℂ) * Polynomial.X) H
  rw [h]
  have hfun : (fun i : Fin m => φ (f i)) = (fun i : Fin m =>
      Polynomial.C ((a i : ℝ) : ℂ) + Polynomial.C ((e i : ℝ) : ℂ) * Polynomial.X) := by
    funext i
    change (Polynomial.map (algebraMap ℝ ℂ))
      (Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) =
      Polynomial.C ((a i : ℝ) : ℂ) + Polynomial.C ((e i : ℝ) : ℂ) * Polynomial.X
    simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  rw [hfun]

/-- Evaluation of a complex line restriction at `b` equals evaluation of `H` at `z + b v`. -/
lemma cLine_eval_eq {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (z v : Fin m → ℂ) (b : ℂ) :
    Polynomial.eval b (MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) H) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => z i + b * v i) H := by
  classical
  let f : Fin m → Polynomial ℂ := fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  let φ : Polynomial ℂ →ₐ[ℝ] ℂ := (Polynomial.aeval (R := ℂ) b).restrictScalars ℝ
  have h := MvPolynomial.comp_aeval_apply (R := ℝ) (S₁ := Polynomial ℂ) (f := f) (φ := φ) (p := H)
  change φ ((MvPolynomial.aeval (R := ℝ) f) H) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => z i + b * v i) H
  rw [h]
  have hfun : (fun i : Fin m => φ (f i)) = (fun i : Fin m => z i + b * v i) := by
    funext i
    change Polynomial.aeval (R := ℂ) b
      (Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) = z i + b * v i
    rw [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp [mul_comm]
  rw [hfun]

/-- Evaluation of the complexified real line polynomial equals evaluating `H` at the complex point. -/
lemma realLine_eval_eq {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (a e : Fin m → ℝ) (b : ℂ) :
    Polynomial.eval b (Polynomial.map (algebraMap ℝ ℂ) (MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H)) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => (a i : ℂ) + b * (e i : ℂ)) H := by
  classical
  let f : Fin m → Polynomial ℝ := fun i => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X
  let φ : Polynomial ℝ →ₐ[ℝ] ℂ := Polynomial.aeval (R := ℝ) b
  have hφev : ∀ p : Polynomial ℝ, Polynomial.eval b (Polynomial.map (algebraMap ℝ ℂ) p) = φ p := by
    intro p
    dsimp [φ]
    rw [Polynomial.eval_map]
    rw [← Polynomial.aeval_def]
  have h := MvPolynomial.comp_aeval_apply (R := ℝ) (S₁ := Polynomial ℝ) (f := f) (φ := φ) (p := H)
  change Polynomial.eval b (Polynomial.map (algebraMap ℝ ℂ)
      ((MvPolynomial.aeval (R := ℝ) f) H)) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => (a i : ℂ) + b * (e i : ℂ)) H
  rw [hφev]
  rw [h]
  have hfun : (fun i : Fin m => φ (f i)) = (fun i : Fin m => (a i : ℂ) + b * (e i : ℂ)) := by
    funext i
    change Polynomial.aeval (R := ℝ) b
      (Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) = (a i : ℂ) + b * (e i : ℂ)
    rw [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp [mul_comm]
  rw [hfun]

/-! ## 2. scalar homogeneity -/

lemma finsupp_prod_pow_smul {σ : Type*} [Fintype σ] (m : σ →₀ ℕ) (a : ℂ) (v : σ → ℂ) :
    m.prod (fun i k => (a * v i) ^ k) = a ^ (∑ i : σ, m i) * m.prod (fun i k => v i ^ k) := by
  rw [Finsupp.prod_pow, Finsupp.prod_pow]
  calc
    (∏ i : σ, (a * v i) ^ m i) = ∏ i : σ, (a ^ m i * v i ^ m i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact mul_pow a (v i) (m i)
    _ = (∏ i : σ, a ^ m i) * (∏ i : σ, v i ^ m i) := Finset.prod_mul_distrib
    _ = a ^ (∑ i : σ, m i) * (∏ i : σ, v i ^ m i) := by
      congr 1
      simpa using (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset σ) (fun i => m i) a)

lemma finsupp_sum_univ_eq_degree {σ : Type*} [Fintype σ] (m : σ →₀ ℕ) :
    (∑ i : σ, m i) = Finsupp.degree m := by
  classical
  have hsupport_le : (m.support : Finset σ) ⊆ Finset.univ := by intro i hi; simp
  have hsum : (∑ i : σ, m i) = ∑ i ∈ (m.support : Finset σ), m i := by
    symm
    exact Finset.sum_subset hsupport_le (by
      intro i hi hin
      by_contra h
      exact hin (by simpa [Finsupp.mem_support_iff] using h))
  exact hsum.trans (Finsupp.degree_apply m)

/-- For a homogeneous polynomial, evaluation commutes with complex scalar multiplication. -/
lemma aeval_smul_homogeneous {m d : ℕ} (H : MvPolynomial (Fin m) ℝ) (hhom : H.IsHomogeneous d)
    (a : ℂ) (v : Fin m → ℂ) :
    MvPolynomial.aeval (R := ℝ) (fun i : Fin m => a * v i) H =
      a ^ d * MvPolynomial.aeval (R := ℝ) v H := by
  classical
  conv_lhs =>
    rw [← H.support_sum_monomial_coeff]
    rw [map_sum]
  conv_rhs =>
    rw [← H.support_sum_monomial_coeff]
    rw [map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M hM
  have hc : MvPolynomial.coeff (R := ℝ) M H ≠ 0 := MvPolynomial.mem_support_iff.mp hM
  have hdsum : (∑ i : Fin m, M i) = d := by
    have hdeg : Finsupp.degree M = d := by
      by_contra hne
      have hc0 : MvPolynomial.coeff (R := ℝ) M H = 0 :=
        IsHomogeneous.coeff_eq_zero hhom (d := M) hne
      exact hc hc0
    exact (finsupp_sum_univ_eq_degree (σ := Fin m) M).trans hdeg
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  rw [finsupp_prod_pow_smul (σ := Fin m) M a v]
  rw [hdsum]
  ring

/-! ## 3. conjugation -/

/-- complex conjugation commutes with evaluation of real polynomials at complex points -/
lemma aeval_conj {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (z : Fin m → ℂ) :
    star (MvPolynomial.aeval (R := ℝ) z H) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => star (z i)) H := by
  classical
  induction H using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      calc
        star ((MvPolynomial.aeval (R := ℝ) z) (p + q)) =
            star ((MvPolynomial.aeval (R := ℝ) z) p + (MvPolynomial.aeval (R := ℝ) z) q) := by rw [map_add]
        _ = star ((MvPolynomial.aeval (R := ℝ) z) p) + star ((MvPolynomial.aeval (R := ℝ) z) q) := by simp
        _ = (MvPolynomial.aeval (R := ℝ) (fun i => star (z i))) p +
            (MvPolynomial.aeval (R := ℝ) (fun i => star (z i))) q := by rw [hp, hq]
        _ = (MvPolynomial.aeval (R := ℝ) (fun i => star (z i))) (p + q) := by rw [map_add]
  | mul_X p i hp =>
      calc
        star ((MvPolynomial.aeval (R := ℝ) z) (p * MvPolynomial.X i)) =
            star ((MvPolynomial.aeval (R := ℝ) z) p * z i) := by rw [map_mul, MvPolynomial.aeval_X]
        _ = star ((MvPolynomial.aeval (R := ℝ) z) p) * star (z i) := by simp
        _ = (MvPolynomial.aeval (R := ℝ) (fun j => star (z j))) p * star (z i) := by rw [hp]
        _ = (MvPolynomial.aeval (R := ℝ) (fun j => star (z j))) (p * MvPolynomial.X i) := by
              rw [map_mul, MvPolynomial.aeval_X]

/-- `star` flips the imaginary part. -/
lemma star_im (z : ℂ) : (star z).im = - z.im := by simp

/-- If `-I / β` is a strictly negative real number then `β` has positive imaginary part. -/
lemma im_pos_of_neg_I_div {β : ℂ} (hβ : β ≠ 0) (hre : ((-I / β) : ℂ).re < 0)
    (him : ((-I / β) : ℂ).im = 0) : 0 < β.im := by
  let r : ℂ := -I / β
  have hrre : r.re < 0 := by simpa [r] using hre
  have hr_real : r = (r.re : ℂ) := by
    apply Complex.ext
    · simp [r]
    · simpa [r] using him
  have hβeq : β = -I / (r.re : ℂ) := by
    have hβ0c : (r.re : ℂ) ≠ 0 := by exact_mod_cast (ne_of_lt hrre)
    calc
      β = (r.re : ℂ)⁻¹ * ((r.re : ℂ) * β) := by field_simp [hβ0c]
      _ = (r.re : ℂ)⁻¹ * (-I) := by
        congr 1
        have hrβ : r * β = -I := by
          dsimp [r]
          field_simp [hβ]
        have : (r.re : ℂ) * β = r * β := by
          rw [← hr_real]
        rw [this, hrβ]
      _ = -I / (r.re : ℂ) := by field_simp [hβ0c]
  rw [hβeq]
  have hcalc : (-I / (r.re : ℂ)).im = -(r.re)⁻¹ := by
    rw [div_eq_mul_inv]
    rw [show (r.re : ℂ)⁻¹ = (((r.re)⁻¹ : ℝ) : ℂ) by simpa using Complex.ofReal_inv (r.re)]
    simp
  rw [hcalc]
  exact neg_pos.mpr (inv_lt_zero.mpr hrre)

/-! ## 3b. coefficient continuity of affine sections -/

/-- Coefficients of a linear factor depend continuously on the parameter. -/
lemma lincoef_cont {m : ℕ} (a b w : Fin m → ℂ) (i : Fin m) (u : ℕ) :
    Continuous (fun z : ℂ =>
      (Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X).coeff u) := by
  classical
  by_cases hu0 : u = 0
  · subst hu0
    have heq : (fun z : ℂ =>
          (Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X).coeff 0) =
        fun z : ℂ => a i + z * b i := by
      funext z
      simp
    rw [heq]
    exact continuous_const.add (continuous_id.mul continuous_const)
  · by_cases hu1 : u = 1
    · subst hu1
      have heq : (fun z : ℂ =>
            (Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X).coeff 1) =
          fun _ : ℂ => w i := by
        funext z
        simp
      rw [heq]
      exact continuous_const
    · have hge2 : 2 ≤ u := by omega
      have heq : (fun z : ℂ =>
            (Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X).coeff u) =
          fun _ : ℂ => 0 := by
        funext z
        have hnd : (Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X).natDegree ≤ 1 := by
          rw [add_comm]
          exact Polynomial.natDegree_linear_le
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hnd (by omega))
      rw [heq]
      exact continuous_const

/-- Coefficients of the affine `z`-dependent line polynomials depend continuously on `z`. -/
lemma aeval_affine_coeff_cont {m : ℕ} (H : MvPolynomial (Fin m) ℝ)
    (a b w : Fin m → ℂ) :
    ∀ j : ℕ,
    Continuous (fun z : ℂ =>
      (MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X) H).coeff j) := by
  classical
  induction H using MvPolynomial.induction_on with
  | C c =>
      intro j
      have hcst : (fun z : ℂ =>
          (MvPolynomial.aeval (R := ℝ)
            (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X)
            (MvPolynomial.C c)).coeff j) = fun _ : ℂ => (Polynomial.C (c : ℂ)).coeff j := by
        funext z
        rw [MvPolynomial.aeval_C]
        simp
      rw [hcst]
      exact continuous_const
  | add p q hfp hfq =>
      intro j
      have heq : (fun z : ℂ =>
          (MvPolynomial.aeval (R := ℝ)
            (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X)
            (p + q)).coeff j) =
          (fun z : ℂ =>
            (MvPolynomial.aeval (R := ℝ)
              (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X) p).coeff j
            + (MvPolynomial.aeval (R := ℝ)
              (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X) q).coeff j) := by
        funext z
        rw [map_add (MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X)) p q]
        rw [Polynomial.coeff_add]
      rw [heq]
      exact (hfp j).add (hfq j)
  | mul_X p i hfp =>
      intro j
      have heq : (fun z : ℂ =>
          (MvPolynomial.aeval (R := ℝ)
            (fun i0 : Fin m => Polynomial.C (a i0 + z * b i0) + Polynomial.C (w i0) * Polynomial.X)
            (p * MvPolynomial.X i)).coeff j) =
          (fun z : ℂ => ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal j : Finset (ℕ × ℕ)),
            (MvPolynomial.aeval (R := ℝ)
              (fun i0 : Fin m => Polynomial.C (a i0 + z * b i0) + Polynomial.C (w i0) * Polynomial.X) p).coeff x.1
              * (Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X).coeff x.2) := by
        funext z
        rw [map_mul (MvPolynomial.aeval (R := ℝ)
          (fun i0 : Fin m => Polynomial.C (a i0 + z * b i0) + Polynomial.C (w i0) * Polynomial.X))
          p (MvPolynomial.X i)]
        rw [MvPolynomial.aeval_X]
        rw [Polynomial.coeff_mul]
      rw [heq]
      apply continuous_finsetSum (s := (Finset.HasAntidiagonal.antidiagonal j : Finset (ℕ × ℕ)))
      intro x hx
      exact (hfp x.1).mul (lincoef_cont a b w i x.2)

/-! ## 4. the Gårding negative-cone engine -/

/-- For a homogeneous degree-`d ≥ 1` polynomial `H` hyperbolic w.r.t. `e` whose `u`-line
`r ↦ H(u + r e)` has all roots real and negative, no zero of `H` lies on `x + ℂe + ℂu`
with the `e`-coefficient in the open lower half-plane and `u`-coefficient in the closed
lower half-plane. -/
lemma gch_negcone_engine {m d : ℕ} (H : MvPolynomial (Fin m) ℝ) (e u : Fin m → ℝ)
    (hhom : H.IsHomogeneous d) (hdpos : 0 < d)
    (he_ne : MvPolynomial.eval e H ≠ 0)
    (hu0 : MvPolynomial.eval u H ≠ 0)
    (hcone : ∀ r : ℂ,
      Polynomial.eval r (MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C ((u i : ℂ)) + Polynomial.C ((e i : ℂ)) * Polynomial.X) H) = 0 →
        r.im = 0 ∧ r.re < 0)
    (hhyp : ∀ a : Fin m → ℝ,
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H = 0 ∨
        ∀ r : Complex, Polynomial.eval r (Polynomial.map (algebraMap ℝ Complex)
          (MvPolynomial.aeval (R := ℝ)
            (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H)) = 0 →
          ∃ s : ℝ, r = (s : Complex)) :
    ∀ x : Fin m → ℝ, ∀ s β : ℂ, s.im < 0 → β.im ≤ 0 →
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => (x i : ℂ) + s * (e i : ℂ) + β * (u i : ℂ)) H ≠ 0 := by
  classical
  let f : homogeneousSubmodule (Fin m) ℝ d := ⟨H, hhom⟩
  have hval_e : MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((e i : ℝ) : ℂ)) H ≠ 0 := by
    have hae : MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((e i : ℝ) : ℂ)) H =
        (algebraMap ℝ ℂ) (MvPolynomial.eval e H) := by
      change MvPolynomial.aeval (R := ℝ) (Complex.ofReal ∘ e) H = (algebraMap ℝ ℂ) (MvPolynomial.eval e H)
      simpa using MvPolynomial.aeval_algebraMap_apply (B := ℂ) (x := e) (p := H)
    rw [hae]
    exact Complex.ofReal_ne_zero.mpr he_ne
  have hval_u : MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((u i : ℝ) : ℂ)) H ≠ 0 := by
    have hae : MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((u i : ℝ) : ℂ)) H =
        (algebraMap ℝ ℂ) (MvPolynomial.eval u H) := by
      change MvPolynomial.aeval (R := ℝ) (Complex.ofReal ∘ u) H = (algebraMap ℝ ℂ) (MvPolynomial.eval u H)
      simpa using MvPolynomial.aeval_algebraMap_apply (B := ℂ) (x := u) (p := H)
    rw [hae]
    exact Complex.ofReal_ne_zero.mpr hu0
  -- hcone re-expressed at the aeval level
  have hconeAeval : ∀ r : ℂ,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((u i : ℝ) : ℂ) + r * ((e i : ℝ) : ℂ)) H = 0 →
      r.im = 0 ∧ r.re < 0 := by
    intro r hr
    apply hcone r
    rw [cLine_eval_eq H (fun i : Fin m => ((u i : ℝ) : ℂ)) (fun i : Fin m => ((e i : ℝ) : ℂ)) r]
    simpa [mul_comm] using hr
  -- the e-lines through real points have only real roots
  have hlineRoots : ∀ (a : Fin m → ℝ) (r : ℂ),
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((a i : ℝ) : ℂ) + r * ((e i : ℝ) : ℂ)) H = 0 → r.im = 0 := by
    intro a r hr
    have hline_ne : (MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C ((a i : ℂ)) + Polynomial.C ((e i : ℂ)) * Polynomial.X) H) ≠ 0 := by
      intro hz
      have hnd : (slicePoly m d (fun i : Fin m => ((a i : ℝ) : ℂ)) (fun i : Fin m => ((e i : ℝ) : ℂ)) f).natDegree = d := by
        exact slicePoly_natDegree_eq_of_aeval_ne_zero m d (fun i : Fin m => ((a i : ℝ) : ℂ))
          (fun i : Fin m => ((e i : ℝ) : ℂ)) f hval_e
      have hnd0 : (slicePoly m d (fun i : Fin m => ((a i : ℝ) : ℂ)) (fun i : Fin m => ((e i : ℝ) : ℂ)) f).natDegree = 0 := by
        change (MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => Polynomial.C ((a i : ℂ)) + Polynomial.C ((e i : ℂ)) * Polynomial.X) H).natDegree = 0
        simp [hz]
      omega
    rcases hhyp a with hzero | hrr
    · exfalso
      apply hline_ne
      rw [← mapRealAeval_eq_complexAeval H a e, hzero]
      simp
    · have hrr' : ∃ s : ℝ, r = (s : ℂ) := hrr r (by
        rw [realLine_eval_eq H a e r]
        exact hr)
      exact (rrl_exists_ofReal_eq_iff r).mp hrr'
  -- evaluating at a real point plus a non-real multiple of `e` is never zero
  have hoff : ∀ (a : Fin m → ℝ) (ζ : ℂ), ζ.im ≠ 0 →
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((a i : ℝ) : ℂ) + ζ * ((e i : ℝ) : ℂ)) H ≠ 0 := by
    intro a ζ hζ hz
    have hzIm : ζ.im = 0 := hlineRoots a ζ hz
    exact hζ hzIm
  -- The `u`-line through `-I e` has all roots in the open upper half-plane.
  have hUpper : ∀ β : ℂ,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => β * ((u i : ℝ) : ℂ) - I * ((e i : ℝ) : ℂ)) H = 0 → 0 < β.im := by
    intro β hβ
    by_cases hβ0 : β = 0
    · subst β
      have hne : MvPolynomial.aeval (R := ℝ) (fun i : Fin m => - I * ((e i : ℝ) : ℂ)) H ≠ 0 := by
        rw [aeval_smul_homogeneous H hhom (-I) (fun i : Fin m => ((e i : ℝ) : ℂ))]
        exact mul_ne_zero (pow_ne_zero d (by norm_num)) hval_e
      exact False.elim (hne (by simpa using hβ))
    · have hm := aeval_smul_homogeneous H hhom β
          (fun i : Fin m => ((u i : ℝ) : ℂ) - (I / β) * ((e i : ℝ) : ℂ))
      have hrew : (fun i : Fin m => β * (((u i : ℝ) : ℂ) - (I / β) * ((e i : ℝ) : ℂ))) =
          (fun i : Fin m => β * ((u i : ℝ) : ℂ) - I * ((e i : ℝ) : ℂ)) := by
        funext i
        field_simp [hβ0]
      have hpart : MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => ((u i : ℝ) : ℂ) - (I / β) * ((e i : ℝ) : ℂ)) H = 0 := by
        have hmul : β ^ d * MvPolynomial.aeval (R := ℝ)
            (fun i : Fin m => ((u i : ℝ) : ℂ) - (I / β) * ((e i : ℝ) : ℂ)) H = 0 := by
          have hm' : MvPolynomial.aeval (R := ℝ)
              (fun i : Fin m => β * ((u i : ℝ) : ℂ) - I * ((e i : ℝ) : ℂ)) H =
              β ^ d * MvPolynomial.aeval (R := ℝ)
                (fun i : Fin m => ((u i : ℝ) : ℂ) - (I / β) * ((e i : ℝ) : ℂ)) H := by
            simpa [hrew] using hm
          simpa [hm'] using hβ
        exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero d hβ0)
      have hrprem : MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => ((u i : ℝ) : ℂ) + (-I / β) * ((e i : ℝ) : ℂ)) H = 0 := by
        have hfun : (fun i : Fin m => ((u i : ℝ) : ℂ) + (-I / β) * ((e i : ℝ) : ℂ)) =
            (fun i : Fin m => ((u i : ℝ) : ℂ) - (I / β) * ((e i : ℝ) : ℂ)) := by
          funext i
          field_simp [hβ0]
          ring
        rw [hfun]
        exact hpart
      have hr := hconeAeval (-I / β) hrprem
      exact im_pos_of_neg_I_div hβ0 hr.2 hr.1
  -- ===== path argument =====
  intro x s β hsim hβim hz
  let a : Fin m → ℂ := fun i => -I * ((e i : ℝ) : ℂ)
  let b : Fin m → ℂ := fun i => ((x i : ℝ) : ℂ) + (s + I) * ((e i : ℝ) : ℂ)
  let ζ : ℝ → ℂ := fun w => (w : ℂ) * s + ((w : ℂ) - 1) * I
  let P : ℝ → Polynomial ℂ := fun w : ℝ =>
    slicePoly m d (fun i : Fin m => a i + (w : ℂ) * b i) (fun i : Fin m => ((u i : ℝ) : ℂ)) f
  -- the imaginary part of the `e`-coefficient along the path is always negative
  have hζim : ∀ w : ℝ, w ∈ Set.Icc 0 1 → (ζ w).im < 0 := by
    intro w hw
    by_cases hw1 : w = 1
    · subst w
      simp [ζ]
      exact hsim
    · have hwlt : w < 1 := lt_of_le_of_ne hw.2 hw1
      have hz0 : w * s.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw.1 (le_of_lt hsim)
      have hw1neg : w - 1 < 0 := by linarith
      have hmain : w * s.im + (w - 1) < 0 := by linarith
      have hcalc : (ζ w).im = w * s.im + (w - 1) := by
        simp [ζ]
      rw [hcalc]
      exact hmain
  have hdeg : ∀ w : ℝ, (P w).natDegree = d := by
    intro w
    dsimp [P]
    exact slicePoly_natDegree_eq_of_aeval_ne_zero m d (fun i : Fin m => a i + (w : ℂ) * b i)
      (fun i : Fin m => ((u i : ℝ) : ℂ)) f hval_u
  have hcont : ∀ j : ℕ, Continuous (fun w : ℝ => (P w).coeff j) := by
    intro j
    have hc := aeval_affine_coeff_cont H a b (fun i : Fin m => ((u i : ℝ) : ℂ)) j
    have hcomp : (fun w : ℝ => (P w).coeff j) =
        (fun z : ℂ => (MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C ((u i : ℝ) : ℂ) * Polynomial.X) H).coeff j)
        ∘ (fun w : ℝ => (w : ℂ)) := by
      funext w
      dsimp [P]
      rfl
    rw [hcomp]
    exact hc.comp Complex.continuous_ofReal
  -- vector identities along the path
  have hvecT (w t : ℝ) :
      (fun i : Fin m => (a i + (w : ℂ) * b i) + (t : ℂ) * ((u i : ℝ) : ℂ)) =
      (fun i : Fin m => (((w * x i + t * u i : ℝ) : ℂ) + ζ w * ((e i : ℝ) : ℂ))) := by
    funext i
    dsimp [a, b, ζ]
    rw [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul]
    ring_nf
  have hvec1 :
      (fun i : Fin m => (a i + (1 : ℂ) * b i) + β * ((u i : ℝ) : ℂ)) =
      (fun i : Fin m => ((x i : ℝ) : ℂ) + s * ((e i : ℝ) : ℂ) + β * ((u i : ℝ) : ℂ)) := by
    funext i
    dsimp [a, b]
    ring_nf
  have hnoReal : ∀ w : ℝ, w ∈ Set.Icc 0 1 → ∀ t : ℝ,
      Polynomial.eval (t : ℂ) (P w) ≠ 0 := by
    intro w hw t hroot
    have hev : Polynomial.eval (t : ℂ) (P w) =
        MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => (a i + (w : ℂ) * b i) + (t : ℂ) * ((u i : ℝ) : ℂ)) H := by
      dsimp [P]
      exact slicePoly_eval m d (fun i : Fin m => a i + (w : ℂ) * b i)
        (fun i : Fin m => ((u i : ℝ) : ℂ)) f (t : ℂ)
    have hzero : MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => (a i + (w : ℂ) * b i) + (t : ℂ) * ((u i : ℝ) : ℂ)) H = 0 :=
      hev.symm.trans hroot
    have hnonzero : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => (((w * x i + t * u i : ℝ) : ℂ) + ζ w * ((e i : ℝ) : ℂ))) H ≠ 0 := by
      exact hoff (fun i : Fin m => w * x i + t * u i) (ζ w) (ne_of_lt (hζim w hw))
    exact hnonzero (by rwa [hvecT w t] at hzero)
  have hroot0 : ∀ z : ℂ, Polynomial.eval z (P 0) = 0 → 0 < z.im := by
    intro z hz
    apply hUpper z
    have hev : Polynomial.eval z (P 0) =
        MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => (a i + (0 : ℂ) * b i) + z * ((u i : ℝ) : ℂ)) H := by
      dsimp [P]
      exact slicePoly_eval m d (fun i : Fin m => a i + (0 : ℂ) * b i)
        (fun i : Fin m => ((u i : ℝ) : ℂ)) f z
    have hzero : MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => (a i + (0 : ℂ) * b i) + z * ((u i : ℝ) : ℂ)) H = 0 :=
      hev.symm.trans hz
    have hvec0 : (fun i : Fin m => (a i + (0 : ℂ) * b i) + z * ((u i : ℝ) : ℂ)) =
        (fun i : Fin m => z * ((u i : ℝ) : ℂ) - I * ((e i : ℝ) : ℂ)) := by
      funext i
      dsimp [a, b]
      ring_nf
    rwa [← hvec0]
  have hpath := lowerHalfRoots_path hdpos P hdeg hcont hnoReal hroot0
  -- all roots of `P 1` lie in the open upper half-plane
  have hroot1 : Polynomial.eval β (P 1) = 0 := by
    dsimp [P]
    rw [slicePoly_eval m d (fun i : Fin m => a i + (1 : ℂ) * b i)
        (fun i : Fin m => ((u i : ℝ) : ℂ)) f β]
    rw [hvec1]
    exact hz
  have hpos : 0 < β.im := hpath β hroot1
  linarith


/-- Gårding bivariate nonvanishing: if a homogeneous polynomial is hyperbolic with respect
to `e` and `u` lies in the interior of the hyperbolicity cone (all roots of the `u`-line
`r ↦ H(u + r e)` are real and negative), then `H` has no zeros on the affine planes
`x + ℂe + ℂu` whose `e`- and `u`-coordinates both have strictly positive imaginary part. -/
theorem gch_bivariate {m d : ℕ} (H : MvPolynomial (Fin m) ℝ) (e u : Fin m → ℝ)
    (hhom : H.IsHomogeneous d) (hdpos : 0 < d)
    (he_ne : MvPolynomial.eval e H ≠ 0)
    (hu0 : MvPolynomial.eval u H ≠ 0)
    (hcone : ∀ r : ℂ,
      Polynomial.eval r (MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C ((u i : ℂ)) + Polynomial.C ((e i : ℂ)) * Polynomial.X) H) = 0 →
        r.im = 0 ∧ r.re < 0)
    (hhyp : ∀ a : Fin m → ℝ,
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H = 0 ∨
        ∀ r : Complex, Polynomial.eval r (Polynomial.map (algebraMap ℝ Complex)
          (MvPolynomial.aeval (R := ℝ)
            (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H)) = 0 →
          ∃ s : ℝ, r = (s : Complex)) :
    ∀ x : Fin m → ℝ, ∀ s : ℂ, 0 < s.im → ∀ t : ℂ, 0 < t.im →
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => (x i : ℂ) + s * (e i : ℂ) + t * (u i : ℂ)) H ≠ 0 := by
  classical
  intro x s hs t ht hroot
  have hsneg : (star s).im < 0 := by
    rw [star_im]
    linarith
  have htneg : (star t).im ≤ 0 := by
    rw [star_im]
    linarith
  have hconj : MvPolynomial.aeval (R := ℝ)
      (fun i : Fin m => (x i : ℂ) + star s * (e i : ℂ) + star t * (u i : ℂ)) H = 0 := by
    have hstar := congrArg star hroot
    have hstep : star (MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => (x i : ℂ) + s * (e i : ℂ) + t * (u i : ℂ)) H) = 0 := by
      simpa using hstar
    rw [aeval_conj] at hstep
    have hfun : (fun i : Fin m => (x i : ℂ) + star s * (e i : ℂ) + star t * (u i : ℂ)) =
        (fun i : Fin m => star ((x i : ℂ) + s * (e i : ℂ) + t * (u i : ℂ))) := by
      funext i
      simp
    have heq : MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => (x i : ℂ) + star s * (e i : ℂ) + star t * (u i : ℂ)) H =
        MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => star ((x i : ℂ) + s * (e i : ℂ) + t * (u i : ℂ))) H := by
      exact congrArg (fun g : Fin m → ℂ => MvPolynomial.aeval (R := ℝ) g H) hfun
    exact heq.trans hstep
  exact gch_negcone_engine H e u hhom hdpos he_ne hu0 hcone hhyp x (star s) (star t) hsneg htneg hconj

end Commons.Analysis.MvPolynomial
