import Mathlib
import Submission.Commons.Analysis.MvPolynomial.garding_stable_of_hyperbolic_and_cone

/-!
# Homogenization preserves stability for polynomials with nonnegative coefficients

Classical theorem (Borcea--Br\"and\'en--Liggett, JAMS 2009, Theorem 4.5, (2) => (1)):
if `p : MvPolynomial (Fin n) ℝ` has nonnegative coefficients, degree at most `d`, and is
stable on the open upper half plane (or zero), then its homogenization

    Σ_m a_m · X_0^(d - deg m) · X^m

is stable on `UpperHalfPlane^(n+1)` (or zero).
-/

noncomputable section

open Finsupp MvPolynomial UpperHalfPlane
open scoped BigOperators

set_option autoImplicit false

namespace Commons.Analysis.MvPolynomial

/-- The homogenization of `p` in the new variable at index `0` of `Fin (n+1)`. -/
def homogenization {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin (n + 1)) ℝ :=
  ∑ m ∈ p.support, MvPolynomial.monomial (Finsupp.cons (d - m.degree) m) (p.coeff m)

/-- Stable in the sense of non-vanishing on the open upper half plane, allowing zero. -/
def Stable {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  p = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
    MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0

/-- `(cons a m).degree = a + m.degree`. -/
lemma degree_cons (n a : ℕ) (m : Fin n →₀ ℕ) :
    (Finsupp.cons a m).degree = a + m.degree := by
  rw [Finsupp.degree_eq_sum]
  rw [Finsupp.degree_eq_sum]
  rw [Fin.sum_univ_succ]
  simp [Finsupp.cons_zero, Finsupp.cons_succ]

/-- Product over all indices of a `Finsupp`; terms with zero exponent equal one. -/
lemma finsupp_prod_eq_prod_univ {M : Type*} [CommMonoid M] {n : ℕ} (m : Fin n →₀ ℕ)
    (g : Fin n → ℕ → M) (hg : ∀ i, g i 0 = 1) :
    m.prod g = ∏ i : Fin n, g i (m i) := by
  classical
  unfold Finsupp.prod
  refine Finset.prod_subset ?hsub ?hf
  · intro i hi
    simp
  · intro i hi hnot
    have hmi : m i = 0 := by
      by_contra h
      exact hnot (mem_support_iff.mpr h)
    simp [hmi, hg i]

/-- The product of powers of a `cons` exponent vector splits off the first coordinate. -/
lemma prod_cons_univ {M : Type*} [CommMonoid M] (n a : ℕ) (m : Fin n →₀ ℕ)
    (w : Fin (n + 1) → M) :
    ∏ j : Fin (n + 1), (w j) ^ ((Finsupp.cons a m) j) =
      (w 0) ^ a * ∏ i : Fin n, (w i.succ) ^ (m i) := by
  rw [Fin.prod_univ_succ]
  simp [Finsupp.cons_zero, Finsupp.cons_succ]

/-- Evaluating the homogenization at `w = (y, x)` gives `∑ a_m · y^(d-|m|) · x^m`. -/
theorem hom_eval {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) (w : Fin (n + 1) → ℂ) :
    MvPolynomial.aeval (R := ℝ) w (homogenization d p) =
      ∑ m ∈ p.support,
        ((p.coeff m : ℝ) : ℂ) *
          ((w 0) ^ (d - m.degree) * ∏ i : Fin n, (w i.succ) ^ (m i)) := by
  classical
  unfold homogenization
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.aeval_monomial]
  have hconv := finsupp_prod_eq_prod_univ (m := Finsupp.cons (d - m.degree) m)
    (g := fun j e => w j ^ e) (by intro j; simp)
  rw [hconv]
  rw [prod_cons_univ]
  rw [show (algebraMap ℝ ℂ) (coeff m p) = ((coeff m p : ℝ) : ℂ) by simp]

/-- Evaluating the homogenization with the first coordinate equal to `1` recovers `p`. -/
theorem hom_eval_one {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (x : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ)
      (fun j : Fin (n + 1) => Fin.cases (1 : ℂ) (fun i : Fin n => x i) j)
      (homogenization d p) = MvPolynomial.aeval (R := ℝ) x p := by
  classical
  rw [hom_eval]
  conv_rhs => rw [← p.support_sum_monomial_coeff]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.aeval_monomial]
  have hprod : m.prod (fun i k => x i ^ k) = ∏ i : Fin n, (x i) ^ (m i) := by
    exact finsupp_prod_eq_prod_univ m (fun i k => x i ^ k) (by intro i; simp)
  rw [hprod]
  rw [show (algebraMap ℝ ℂ) (coeff m p) = ((coeff m p : ℝ) : ℂ) by simp]
  simp [Fin.cases_zero, Fin.cases_succ]

/-- The homogenization is homogeneous of degree `d`. -/
theorem hom_isHomogeneous {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d) :
    (homogenization d p).IsHomogeneous d := by
  classical
  unfold homogenization
  refine MvPolynomial.IsHomogeneous.sum (s := p.support)
    (φ := fun m => MvPolynomial.monomial (Finsupp.cons (d - m.degree) m) (p.coeff m))
    d ?_
  intro m hm
  refine MvPolynomial.isHomogeneous_monomial (p.coeff m) ?_
  rw [degree_cons]
  have hdegm : m.degree ≤ d := hdeg m hm
  omega

/-- Coefficients of the homogenization are nonnegative when those of `p` are. -/
theorem hom_coeff_nonneg {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) :
    ∀ m : Fin (n + 1) →₀ ℕ, 0 ≤ (homogenization d p).coeff m := by
  classical
  intro m
  unfold homogenization
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_nonneg (by
    intro e he
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · exact hnn e
    · exact le_rfl)

/-- Evaluating a real polynomial at real values expands over the support. -/
theorem aeval_sum_real {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial.aeval (R := ℝ) x p =
      ∑ m ∈ p.support, (p.coeff m) * (∏ i : Fin n, (x i) ^ (m i)) := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff]
  conv_lhs => rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.aeval_monomial]
  have hprod : m.prod (fun i k => x i ^ k) = ∏ i : Fin n, (x i) ^ (m i) := by
    exact finsupp_prod_eq_prod_univ m (fun i k => x i ^ k) (by intro i; simp)
  rw [hprod]
  simp

/-- The coefficient of the homogenization at the exponent `cons (d - deg m) m` equals
the coefficient of `p` at `m`. -/
theorem hom_coeff_cons {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ)
    (hm : m ∈ p.support) :
    (homogenization d p).coeff (Finsupp.cons (d - m.degree) m) = p.coeff m := by
  classical
  let m' : Fin (n + 1) →₀ ℕ := Finsupp.cons (d - m.degree) m
  unfold homogenization
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single m
    (f := fun e => MvPolynomial.coeff m' (MvPolynomial.monomial (Finsupp.cons (d - e.degree) e) (p.coeff e)))]
  · rw [MvPolynomial.coeff_monomial]
    simp [m']
  · intro e he hne
    rw [MvPolynomial.coeff_monomial]
    have hne' : Finsupp.cons (d - e.degree) e ≠ m' := by
      intro hc
      have ht := congrArg (fun q : Fin (n + 1) →₀ ℕ => q.tail) hc
      have ht' : e = m := by
        simpa [m', Finsupp.tail_cons] using ht
      exact hne ht'
    simp [hne', m']
  · intro hmnot
    exact False.elim (hmnot hm)

/-- If `p` has nonnegative coefficients and is nonzero, its homogenization is positive on
the strictly positive orthant of `Fin (n+1)`. -/
theorem hom_pos_orthant {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) (hp : p ≠ 0)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (x : Fin (n + 1) → ℝ) (hx : ∀ i : Fin (n + 1), 0 < x i) :
    0 < MvPolynomial.eval x (homogenization d p) := by
  classical
  change 0 < MvPolynomial.aeval (R := ℝ) x (homogenization d p)
  rw [aeval_sum_real]
  refine Finset.sum_pos' ?hge ?hpos
  · intro M hM
    have hprod : 0 ≤ ∏ i : Fin (n + 1), (x i) ^ (M i) := by
      refine Finset.prod_nonneg ?_
      intro i hi
      exact le_of_lt (pow_pos (hx i) (M i))
    exact mul_nonneg (hom_coeff_nonneg p hnn M) hprod
  · obtain ⟨m, hm⟩ := MvPolynomial.exists_coeff_ne_zero hp
    have hpos_c : 0 < p.coeff m := lt_of_le_of_ne (hnn m) (Ne.symm hm)
    let M0 : Fin (n + 1) →₀ ℕ := Finsupp.cons (d - m.degree) m
    have hM0_supp : M0 ∈ (homogenization d p).support := by
      rw [MvPolynomial.mem_support_iff]
      rw [hom_coeff_cons p m (MvPolynomial.mem_support_iff.mpr hm)]
      exact hm
    refine ⟨M0, hM0_supp, ?_⟩
    have hcM0 : 0 < (homogenization d p).coeff M0 := by
      rw [hom_coeff_cons p m (MvPolynomial.mem_support_iff.mpr hm)]
      exact hpos_c
    have hprod : 0 < ∏ i : Fin (n + 1), (x i) ^ (M0 i) := by
      exact Finset.prod_pos (by intro i hi; exact pow_pos (hx i) (M0 i))
    exact mul_pos hcM0 hprod

/-- Complex conjugation commutes with evaluation of real polynomials. -/
lemma aeval_conj_mv {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (z : Fin n → ℂ) :
    (starRingEnd ℂ) (MvPolynomial.aeval (R := ℝ) z p) =
      MvPolynomial.aeval (R := ℝ) (fun i => starRingEnd ℂ (z i)) p := by
  rw [MvPolynomial.map_aeval]
  have hcomp : (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = (algebraMap ℝ ℂ) := by
    ext r
    simp [algebraMap, Complex.conj_ofReal]
  rw [hcomp]
  rw [← MvPolynomial.aeval_eq_eval₂Hom]

/-- Stable polynomials with real coefficients and nonvanishing on the open upper half
plane also do not vanish when all coordinates have negative imaginary part. -/
theorem stable_no_root_negIm {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p ≠ 0)
    (hstab : ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    ∀ z : Fin n → ℂ, (∀ i : Fin n, (z i).im < 0) →
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z i) p ≠ 0 := by
  intro z hneg hz
  let zc : Fin n → ℂ := fun i => starRingEnd ℂ (z i)
  have hc_pos : ∀ i : Fin n, 0 < (zc i).im := by
    intro i
    have him : (starRingEnd ℂ (z i)).im = - (z i).im := by
      simpa using (Complex.conj_im (z i))
    dsimp [zc]
    linarith [hneg i, him]
  let z' : Fin n → UpperHalfPlane := fun i => ⟨zc i, hc_pos i⟩
  have hz' : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ)) p ≠ 0 :=
    hstab z'
  have hfun : (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ)) = zc := by
    funext i
    simp [z', zc]
  have hz'c : MvPolynomial.aeval (R := ℝ) zc p ≠ 0 := by
    simpa [hfun] using hz'
  have hstar : (starRingEnd ℂ) (MvPolynomial.aeval (R := ℝ) z p) =
      MvPolynomial.aeval (R := ℝ) zc p := by
    simpa [zc] using (aeval_conj_mv p z)
  apply hz'c
  rw [← hstar]
  simp [hz]

/-- `P = 0` or every complex root of `P` is real. -/
def RealRootedOrZero (P : Polynomial ℝ) : Prop :=
  P = 0 ∨ ∀ r : ℂ, Polynomial.eval r (Polynomial.map (algebraMap ℝ ℂ) P) = 0 →
    ∃ s : ℝ, r = (s : ℂ)

/-- Conjugation commutes with evaluating a real polynomial at complex numbers. -/
lemma eval_conj_real (P : Polynomial ℝ) (z : ℂ) :
    (Polynomial.map (algebraMap ℝ ℂ) P).eval (starRingEnd ℂ z) =
      starRingEnd ℂ ((Polynomial.map (algebraMap ℝ ℂ) P).eval z) := by
  rw [Polynomial.eval_map, Polynomial.eval_map]
  rw [Polynomial.hom_eval₂ (f := algebraMap ℝ ℂ) (g := starRingEnd ℂ) (x := z) (p := P)]
  have hcomp : (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = (algebraMap ℝ ℂ) := by
    ext r
    simp [Complex.conj_ofReal]
  rw [hcomp]

/-- A real polynomial with no roots in the open upper half plane is zero or has only
real roots. -/
theorem realRooted_of_noUHP {P : Polynomial ℝ}
    (h : ∀ r : ℂ, 0 < r.im → (Polynomial.map (algebraMap ℝ ℂ) P).eval r ≠ 0) :
    RealRootedOrZero P := by
  classical
  by_cases hP0 : P = 0
  · exact Or.inl hP0
  · right
    intro r hr
    have him_le : r.im ≤ 0 := by
      by_contra hnot
      have himpos : 0 < r.im := lt_of_not_ge hnot
      exact (h r himpos) (by simpa using hr)
    by_cases him0 : r.im = 0
    · refine ⟨r.re, ?_⟩
      apply Complex.ext <;> simp [him0]
    · have hne0 : r.im ≠ 0 := by exact fun hz => him0 hz
      have himneg : r.im < 0 := lt_of_le_of_ne him_le hne0
      have hconjroot : (Polynomial.map (algebraMap ℝ ℂ) P).eval (starRingEnd ℂ r) = 0 := by
        rw [eval_conj_real P r, hr]
        simp
      have himconjpos : 0 < (starRingEnd ℂ r).im := by
        rw [Complex.conj_im]
        linarith
      exact False.elim ((h (starRingEnd ℂ r) himconjpos) hconjroot)

/-- Evaluating the line restriction at a complex number equals the evaluation of `H` at
the corresponding complex point. -/
lemma lineEval {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (a b : Fin m → ℝ) (t : ℂ) :
    Polynomial.eval t (Polynomial.map (algebraMap ℝ ℂ) (LinePoly H a b)) =
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => ((a i : ℝ) : ℂ) + t * (b i : ℝ)) H := by
  let φ : Polynomial ℝ →ₐ[ℝ] ℂ := Polynomial.aeval (R := ℝ) t
  have hφ : ∀ P : Polynomial ℝ, φ P =
      Polynomial.eval t (Polynomial.map (algebraMap ℝ ℂ) P) := by
    intro P
    simp [φ, Polynomial.aeval_def, Polynomial.eval_map]
  calc
    Polynomial.eval t (Polynomial.map (algebraMap ℝ ℂ) (LinePoly H a b))
        = φ (LinePoly H a b) := by rw [hφ]
    _ = MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => φ (Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X)) H := by
          change φ (MvPolynomial.aeval (R := ℝ)
            (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) H) = _
          rw [MvPolynomial.comp_aeval_apply]
    _ = MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => ((a i : ℝ) : ℂ) + t * (b i : ℝ)) H := by
          have hfun : (fun i : Fin m => φ (Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X)) =
              (fun i : Fin m => ((a i : ℝ) : ℂ) + t * (b i : ℝ)) := by
            funext i
            simp [φ]
            ring
          rw [hfun]

/-- A line restriction with no zeros at upper-half-plane parameters is zero or real
rooted. -/
theorem line_realRooted_of_noUHP_eval {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (a b : Fin m → ℝ)
    (h : ∀ t : ℂ, 0 < t.im →
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => ((a i : ℝ) : ℂ) + t * (b i : ℝ)) H ≠ 0) :
    RealRootedOrZero (LinePoly H a b) := by
  apply realRooted_of_noUHP
  intro t ht
  intro hz
  have hz' := h t ht
  rw [lineEval] at hz
  exact hz' hz

/-- Real evaluation expansion over the support. -/
theorem aeval_sum_real_ℂ {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) x p =
      ∑ m ∈ p.support, ((p.coeff m : ℝ) : ℂ) * (∏ i : Fin n, (x i) ^ (m i)) := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff]
  conv_lhs => rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.aeval_monomial]
  have hprod : m.prod (fun i k => x i ^ k) = ∏ i : Fin n, (x i) ^ (m i) := by
    exact finsupp_prod_eq_prod_univ m (fun i k => x i ^ k) (by intro i; simp)
  rw [hprod]
  rw [show (algebraMap ℝ ℂ) (coeff m p) = ((coeff m p : ℝ) : ℂ) by simp]

/-- `∑ᵢ w0^{m i} = w0^{m.degree}`. -/
lemma pow_prod_degree {n : ℕ} (m : Fin n →₀ ℕ) (w0 : ℂ) :
    (∏ i : Fin n, w0 ^ (m i)) = w0 ^ m.degree := by
  classical
  rw [Finsupp.degree_eq_sum]
  rw [Finset.prod_pow_eq_pow_sum]

/-- Evaluating the homogenization at `w = (z₀, x)` with `z₀ ≠ 0` factors `z₀^d` and
substitutes `xᵢ / z₀` into `p`. -/
theorem hom_eval_dehom {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (w : Fin (n + 1) → ℂ) (hw0 : w 0 ≠ 0) :
    MvPolynomial.aeval (R := ℝ) w (homogenization d p) =
      (w 0) ^ d * MvPolynomial.aeval (R := ℝ) (fun i : Fin n => w i.succ / w 0) p := by
  classical
  rw [hom_eval]
  rw [aeval_sum_real_ℂ p (fun i : Fin n => w i.succ / w 0)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hdegm : m.degree ≤ d := hdeg m hm
  have hprod : (∏ i : Fin n, (w i.succ) ^ (m i)) =
      (w 0) ^ m.degree * ∏ i : Fin n, (w i.succ / w 0) ^ (m i) := by
    calc
      (∏ i : Fin n, (w i.succ) ^ (m i))
          = ∏ i : Fin n, ((w 0) * (w i.succ / w 0)) ^ (m i) := by
              apply Finset.prod_congr rfl
              intro i hi
              have hmul : (w 0) * (w i.succ / w 0) = w i.succ := by field_simp [hw0]
              rw [hmul]
      _ = ∏ i : Fin n, ((w 0) ^ (m i) * (w i.succ / w 0) ^ (m i)) := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [mul_pow]
      _ = (∏ i : Fin n, (w 0) ^ (m i)) * ∏ i : Fin n, (w i.succ / w 0) ^ (m i) := by
              rw [Finset.prod_mul_distrib]
      _ = (w 0) ^ m.degree * ∏ i : Fin n, (w i.succ / w 0) ^ (m i) := by
              rw [pow_prod_degree]
  have hp : (w 0) ^ (d - m.degree) * (w 0) ^ m.degree = (w 0) ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hdegm]
  calc
    ((p.coeff m : ℝ) : ℂ) * ((w 0) ^ (d - m.degree) * ∏ i : Fin n, (w i.succ) ^ (m i))
        = ((p.coeff m : ℝ) : ℂ) * ((w 0) ^ (d - m.degree) *
            ((w 0) ^ m.degree * ∏ i : Fin n, (w i.succ / w 0) ^ (m i))) := by
            rw [hprod]
    _ = (w 0) ^ d * (((p.coeff m : ℝ) : ℂ) * ∏ i : Fin n, (w i.succ / w 0) ^ (m i)) := by
            rw [← mul_assoc (w 0 ^ (d - m.degree)) (w 0 ^ m.degree)]
            rw [hp]
            ac_rfl


/-- The wall direction `(0,1,...,1)` used as the hyperbolic direction for the
homogenization. -/
def eWall (n : ℕ) : Fin (n + 1) → ℝ :=
  fun j => Fin.cases 0 (fun _ : Fin n => 1) j

lemma eWall_zero (n : ℕ) : eWall n 0 = 0 := by simp [eWall]
lemma eWall_succ (n : ℕ) (i : Fin n) : eWall n i.succ = 1 := by simp [eWall]

/-- Imaginary part of a division by a real number. -/
lemma im_div_real (z : ℂ) (r : ℝ) : (z / (r : ℂ)).im = z.im / r := by
  calc
    (z / (r : ℂ)).im = (z * (r : ℂ)⁻¹).im := by rw [div_eq_mul_inv]
    _ = (z * ((r⁻¹ : ℝ) : ℂ)).im := by rw [Complex.ofReal_inv r]
    _ = z.im * (r⁻¹ : ℝ) := by exact Complex.im_mul_ofReal z (r⁻¹)
    _ = z.im / r := by rw [div_eq_mul_inv]

/-- Nonvanishing of the homogenization at a point of the upper half plane whose first
coordinate is real and nonzero follows from the stability of `p`. -/
lemma hom_no_root_a0_ne_zero {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (hp0 : p ≠ 0)
    (hstab : ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0)
    (a : Fin (n + 1) → ℝ) (ha0 : a 0 ≠ 0)
    (t : ℂ) (ht : 0 < t.im) :
    MvPolynomial.aeval (R := ℝ)
      (fun j : Fin (n + 1) => ((a j : ℝ) : ℂ) + t * (eWall n j)) (homogenization d p) ≠ 0 := by
  classical
  let w : Fin (n + 1) → ℂ := fun j => ((a j : ℝ) : ℂ) + t * (eWall n j)
  have hw0 : w 0 ≠ 0 := by
    dsimp [w]
    simp [eWall]
    exact_mod_cast ha0
  have hw0eq : w 0 = ((a 0 : ℝ) : ℂ) := by
    dsimp [w]
    simp [eWall]
  have hwsucc : ∀ i : Fin n, w i.succ = ((a i.succ : ℝ) : ℂ) + t := by
    intro i
    simp [w, eWall]
  have hnum_add : ∀ i : Fin n, ((a i.succ : ℝ) : ℂ) + t = t + ((a i.succ : ℝ) : ℂ) := by
    intro i
    ring
  have himt : ∀ i : Fin n, (t + ((a i.succ : ℝ) : ℂ)).im = t.im := by
    intro i
    have hadd : (t + ((a i.succ : ℝ) : ℂ)).im = t.im + (((a i.succ : ℝ) : ℂ)).im := by simp
    simpa using hadd
  have him_ratio : ∀ i : Fin n, (w i.succ / w 0).im = t.im / (a 0 : ℝ) := by
    intro i
    rw [hwsucc i, hw0eq, im_div_real, hnum_add i, himt i]
  have hev := hom_eval_dehom p hdeg w hw0
  rw [hev]
  apply mul_ne_zero
  · exact pow_ne_zero d hw0
  · by_cases hpos : 0 < (a 0 : ℝ)
    · -- ratios in ℍⁿ
      let z' : Fin n → UpperHalfPlane := fun i =>
        ⟨w i.succ / w 0, by rw [him_ratio i]; exact div_pos ht hpos⟩
      have hz' : MvPolynomial.aeval (R := ℝ)
          (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ)) p ≠ 0 := hstab z'
      simpa [w] using hz'
    · -- a0 < 0 : ratios in (−ℍ)ⁿ
      have hneg0 : (a 0 : ℝ) < 0 := lt_of_le_of_ne (le_of_not_gt hpos) ha0
      have himneg : ∀ i : Fin n, (w i.succ / w 0).im < 0 := by
        intro i
        rw [him_ratio i]
        exact div_neg_of_pos_of_neg ht hneg0
      exact stable_no_root_negIm p hp0 hstab (fun i : Fin n => w i.succ / w 0) himneg

/-- The restriction of the homogenization to a line in the wall direction with nondegenerate
base (first coordinate nonzero) is zero or real-rooted. -/
theorem wallHyp_nonzero {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (hp0 : p ≠ 0)
    (hstab : ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0)
    (a : Fin (n + 1) → ℝ) (ha0 : a 0 ≠ 0) :
    RealRootedOrZero (LinePoly (homogenization d p) a (eWall n)) := by
  apply line_realRooted_of_noUHP_eval
  intro t ht
  exact hom_no_root_a0_ne_zero p hdeg hp0 hstab a ha0 t ht


/-- The degree-`d` homogeneous part of `p`. -/
def degreePart {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ m ∈ p.support.filter (fun m => m.degree = d), MvPolynomial.monomial m (p.coeff m)

/-- Coefficient of `degreePart d p` at `m`. -/
lemma degreePart_coeff {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ) :
    (degreePart d p).coeff m = if m.degree = d then p.coeff m else 0 := by
  classical
  unfold degreePart
  rw [MvPolynomial.coeff_sum]
  have hfun : (fun e => (MvPolynomial.monomial e (p.coeff e)).coeff m) =
      (fun e => if e = m then p.coeff e else 0) := by
    funext e
    rw [MvPolynomial.coeff_monomial]
  rw [hfun]
  rw [Finset.sum_ite_eq']
  by_cases hf : m ∈ p.support.filter (fun e => e.degree = d)
  · have hdegm : m.degree = d := (Finset.mem_filter.mp hf).2
    rw [if_pos hf, if_pos hdegm]
  · rw [if_neg hf]
    by_cases hd : m.degree = d
    · rw [if_pos hd]
      have hms : m ∉ p.support := by
        intro hm
        apply hf
        exact Finset.mem_filter.mpr ⟨hm, hd⟩
      have hc0 : p.coeff m = 0 := by
        by_contra hc
        exact hms (MvPolynomial.mem_support_iff.mpr hc)
      exact hc0.symm
    · rw [if_neg hd]

/-- Support of `degreePart d p` is contained in the support of `p`. -/
lemma degreePart_support_subset {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (degreePart d p).support ⊆ p.support := by
  classical
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  by_cases hd : m.degree = d
  · rw [degreePart_coeff, if_pos hd] at hm
    exact MvPolynomial.mem_support_iff.mpr hm
  · rw [degreePart_coeff, if_neg hd] at hm
    exact False.elim (hm rfl)

/-- Evaluating `degreePart d p` at real values expands over the degree-`d` monomials. -/
lemma aeval_degreePart {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) x (degreePart d p) =
      ∑ m ∈ p.support.filter (fun m => m.degree = d),
        ((p.coeff m : ℝ) : ℂ) * (∏ i : Fin n, (x i) ^ (m i)) := by
  classical
  unfold degreePart
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.aeval_monomial]
  have hprod : m.prod (fun i k => x i ^ k) = ∏ i : Fin n, (x i) ^ (m i) := by
    exact finsupp_prod_eq_prod_univ m (fun i k => x i ^ k) (by intro i; simp)
  rw [hprod]
  rw [show (algebraMap ℝ ℂ) (coeff m p) = ((coeff m p : ℝ) : ℂ) by simp]

/-- Evaluating the homogenization at a point whose first coordinate is zero leaves the
degree-`d` part of `p` evaluated at the remaining coordinates. -/
theorem hom_eval_first_zero {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (w : Fin (n + 1) → ℂ) (hw0 : w 0 = 0) :
    MvPolynomial.aeval (R := ℝ) w (homogenization d p) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => w i.succ) (degreePart d p) := by
  classical
  have hterm : ∀ m ∈ p.support,
      ((p.coeff m : ℝ) : ℂ) * ((w 0) ^ (d - m.degree) *
          (∏ i : Fin n, (w i.succ) ^ (m i))) =
        (if m.degree = d then
          ((p.coeff m : ℝ) : ℂ) * (∏ i : Fin n, (w i.succ) ^ (m i)) else 0) := by
    intro m hm
    have hdegm : m.degree ≤ d := hdeg m hm
    by_cases hd : m.degree = d
    · have hsub : d - m.degree = 0 := by omega
      have hzero_pow : (w 0) ^ (d - m.degree) = (1 : ℂ) := by
        rw [hsub, pow_zero]
      have hcond : (if m.degree = d then
          ((p.coeff m : ℝ) : ℂ) * (∏ i : Fin n, (w i.succ) ^ (m i)) else 0) =
          ((p.coeff m : ℝ) : ℂ) * (∏ i : Fin n, (w i.succ) ^ (m i)) := by
        simp [hd]
      rw [hcond, hzero_pow]
      simp
    · have hlt : m.degree < d := lt_of_le_of_ne hdegm hd
      have hsub_pos : 0 < d - m.degree := Nat.sub_pos_of_lt hlt
      have hzero_pow : (w 0) ^ (d - m.degree) = (0 : ℂ) := by
        rw [hw0, zero_pow (ne_of_gt hsub_pos)]
      have hcond : (if m.degree = d then
          ((p.coeff m : ℝ) : ℂ) * (∏ i : Fin n, (w i.succ) ^ (m i)) else 0) = 0 := by
        simp [hd]
      rw [hcond, hzero_pow]
      simp
  calc
    MvPolynomial.aeval (R := ℝ) w (homogenization d p)
        = ∑ m ∈ p.support, ((p.coeff m : ℝ) : ℂ) * ((w 0) ^ (d - m.degree) *
            (∏ i : Fin n, (w i.succ) ^ (m i))) := hom_eval p w
    _ = ∑ m ∈ p.support, (if m.degree = d then
          ((p.coeff m : ℝ) : ℂ) * (∏ i : Fin n, (w i.succ) ^ (m i)) else 0) := by
          apply Finset.sum_congr rfl
          intro m hm
          exact hterm m hm
    _ = ∑ m ∈ p.support.filter (fun m => m.degree = d),
          ((p.coeff m : ℝ) : ℂ) * (∏ i : Fin n, (w i.succ) ^ (m i)) := by
          rw [Finset.sum_filter]
    _ = MvPolynomial.aeval (R := ℝ) (fun i : Fin n => w i.succ) (degreePart d p) := by
          rw [aeval_degreePart]


/-! =====================================================================
Port of `isStable_tendsto_of_degree_le` (commons module of the same name),
with the three colliding names (`slicePoly`, `slicePoly_eval`,
`slicePoly_natDegree_le`) renamed to `tsl_*` so it can coexist with the
`garding`-chain imports above.
===================================================================== -/

open Filter Topology Polynomial
open scoped Topology


/-! The slice of a multivariate polynomial along an affine complex line. -/

/-- The univariate polynomial `t ↦ p(z + t v)`, viewed as a complex polynomial in `t`. -/
def tsl_slicePoly (n : ℕ) (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) : Polynomial ℂ :=
  MvPolynomial.aeval (R := ℝ)
    (fun i : Fin n => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) p

lemma tsl_slicePoly_eval (n : ℕ) (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) (b : ℂ) :
    Polynomial.eval b (tsl_slicePoly n z v p) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z i + b * v i) p := by
  unfold tsl_slicePoly
  let a : Fin n → Polynomial ℂ :=
    fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  let φ : Polynomial ℂ →ₐ[ℝ] ℂ := (Polynomial.aeval (R := ℂ) b).restrictScalars ℝ
  have h := MvPolynomial.comp_aeval_apply (f := a) (φ := φ) (p := p)
  change φ (MvPolynomial.aeval (R := ℝ) a p) =
    MvPolynomial.aeval (R := ℝ) (fun i => z i + b * v i) p
  have hfun : (fun i => φ (a i)) = (fun i => z i + b * v i) := by
    funext i
    dsimp [φ, a]
    change Polynomial.eval b (Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) = z i + b * v i
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [h, hfun]

/-- The slice monomial factor `∏_i (C (z i) + C (v i) X) ^ (m i)`. -/
def sliceMon (n : ℕ) (z v : Fin n → ℂ) (m : Fin n →₀ ℕ) : Polynomial ℂ :=
  m.prod fun i k => (Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) ^ k

lemma sliceMon_natDegree_le {n : ℕ} (z v : Fin n → ℂ) (m : Fin n →₀ ℕ) :
    (sliceMon n z v m).natDegree ≤ Finsupp.degree m := by
  classical
  let a : Fin n → Polynomial ℂ := fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  have hlin : ∀ i, (a i).natDegree ≤ 1 := by
    intro i
    dsimp [a]
    rw [add_comm]
    exact Polynomial.natDegree_linear_le
  calc
    (sliceMon n z v m).natDegree = (m.prod fun i k => a i ^ k).natDegree := by rfl
    _ ≤ ∑ i ∈ m.support, (a i ^ m i).natDegree := by
      simpa [Finsupp.prod] using
        (Polynomial.natDegree_prod_le m.support (fun i => a i ^ m i))
    _ ≤ ∑ i ∈ m.support, m i * 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Polynomial.natDegree_pow_le (p := a i) (n := m i)).trans
        (Nat.mul_le_mul_left (m i) (hlin i))
    _ = Finsupp.degree m := by
      rw [Finsupp.degree_apply]
      simp

lemma sliceMon_coeff_eq_zero_of_weight_lt {n : ℕ} (z v : Fin n → ℂ) (m : Fin n →₀ ℕ)
    {j : ℕ} (hj : Finsupp.degree m < j) : (sliceMon n z v m).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (sliceMon_natDegree_le z v m) hj)

lemma tsl_slicePoly_coeff_eq_sum_support (n : ℕ) (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) (j : ℕ) :
    (tsl_slicePoly n z v p).coeff j =
      ∑ m ∈ p.support, ((p.coeff m : ℝ) : ℂ) * (sliceMon n z v m).coeff j := by
  classical
  let a : Fin n → Polynomial ℂ :=
    fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  have hae : MvPolynomial.aeval (R := ℝ) a p =
      ∑ m ∈ p.support, Polynomial.C ((p.coeff m : ℝ) : ℂ) * sliceMon n z v m := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [MvPolynomial.aeval_monomial]
    rfl
  unfold tsl_slicePoly
  rw [hae]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.coeff_C_mul]

lemma tsl_slicePoly_natDegree_le (n : ℕ) (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) :
    (tsl_slicePoly n z v p).natDegree ≤ p.totalDegree := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [tsl_slicePoly_coeff_eq_sum_support]
  apply Finset.sum_eq_zero
  intro m hm
  have hdeg_le : Finsupp.degree m ≤ p.totalDegree := by
    have h := MvPolynomial.le_totalDegree (p := p) hm
    simpa [Finsupp.degree_apply, Finsupp.sum] using h
  have hlt : Finsupp.degree m < N := lt_of_le_of_lt hdeg_le hN
  rw [sliceMon_coeff_eq_zero_of_weight_lt (m := m) (j := N) (z := z) (v := v) hlt]
  simp

lemma tsl_slicePoly_eq_partialSum {n D : ℕ} (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ)
    (hdeg : p.totalDegree ≤ D) :
    tsl_slicePoly n z v p =
      ∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) ((tsl_slicePoly n z v p).coeff (i : ℕ)) := by
  classical
  have hnd : (tsl_slicePoly n z v p).natDegree ≤ D :=
    le_trans (tsl_slicePoly_natDegree_le n z v p) hdeg
  have hndlt : (tsl_slicePoly n z v p).natDegree < D + 1 := Nat.lt_succ_of_le hnd
  have h := Polynomial.as_sum_range' (tsl_slicePoly n z v p) (D + 1) hndlt
  calc
    tsl_slicePoly n z v p =
        ∑ i ∈ Finset.range (D + 1), Polynomial.monomial i ((tsl_slicePoly n z v p).coeff i) := h
    _ = ∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) ((tsl_slicePoly n z v p).coeff (i : ℕ)) := by
      exact (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => Polynomial.monomial i ((tsl_slicePoly n z v p).coeff i)) (D + 1)).symm

/-! The (finite) set of monomials of total degree at most `D`. -/

/-- All monomials in `n` variables of total degree at most `D`, as a finset. -/
def monomialsLE (n D : ℕ) : Finset (Fin n →₀ ℕ) := by
  classical
  exact (Finset.range (D + 1)).biUnion
    (fun d : ℕ => (Finset.univ : Finset (Fin n)).finsuppAntidiag d)

lemma mem_monomialsLE {n D : ℕ} (m : Fin n →₀ ℕ) :
    m ∈ monomialsLE n D ↔ Finsupp.degree m ≤ D := by
  classical
  rw [monomialsLE, Finset.mem_biUnion]
  constructor
  · rintro ⟨d, hd, hm⟩
    have hmem := (Finset.mem_finsuppAntidiag).mp hm
    have hd_le : d ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
    have hdeg : Finsupp.degree m = d := by
      rw [Finsupp.degree_eq_sum]
      exact hmem.1
    exact le_trans (le_of_eq hdeg) hd_le
  · intro hdeg
    refine ⟨Finsupp.degree m, Finset.mem_range.mpr (Nat.lt_succ_of_le hdeg), ?_⟩
    rw [Finset.mem_finsuppAntidiag]
    simp [Finsupp.degree_eq_sum]

lemma support_subset_monomialsLE {n D : ℕ} (p : MvPolynomial (Fin n) ℝ) (hdeg : p.totalDegree ≤ D) :
    p.support ⊆ monomialsLE n D := by
  classical
  intro m hm
  rw [mem_monomialsLE]
  have h := MvPolynomial.le_totalDegree (p := p) hm
  exact le_trans h hdeg

lemma tsl_slicePoly_coeff_eq_sum_monomialsLE {n D : ℕ} (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ)
    (hdeg : p.totalDegree ≤ D) (j : ℕ) :
    (tsl_slicePoly n z v p).coeff j =
      ∑ m ∈ monomialsLE n D, ((p.coeff m : ℝ) : ℂ) * (sliceMon n z v m).coeff j := by
  classical
  rw [tsl_slicePoly_coeff_eq_sum_support]
  exact Finset.sum_subset (support_subset_monomialsLE p hdeg) (by
    intro m hmS hmnot
    have hc : p.coeff m = 0 := by
      by_contra h
      exact hmnot (MvPolynomial.mem_support_iff.mpr h)
    simp [hc])

lemma tsl_slicePoly_coeff_tendsto {n D : ℕ} (z v : Fin n → ℂ) (u : ℕ → MvPolynomial (Fin n) ℝ)
    (g : MvPolynomial (Fin n) ℝ)
    (huD : ∀ k : ℕ, (u k).totalDegree ≤ D) (hgD : g.totalDegree ≤ D)
    (hconv : ∀ m : Fin n →₀ ℕ, Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)))
    (j : ℕ) :
    Tendsto (fun k : ℕ => (tsl_slicePoly n z v (u k)).coeff j) atTop
      (𝓝 ((tsl_slicePoly n z v g).coeff j)) := by
  classical
  rw [show (fun k : ℕ => (tsl_slicePoly n z v (u k)).coeff j) =
      fun k : ℕ => ∑ m ∈ monomialsLE n D,
        (((u k).coeff m : ℝ) : ℂ) * (sliceMon n z v m).coeff j by
        funext k
        exact (tsl_slicePoly_coeff_eq_sum_monomialsLE z v (u k) (huD k) j)]
  rw [show (𝓝 ((tsl_slicePoly n z v g).coeff j)) =
      𝓝 (∑ m ∈ monomialsLE n D,
        ((g.coeff m : ℝ) : ℂ) * (sliceMon n z v m).coeff j) by
        congr 1
        exact (tsl_slicePoly_coeff_eq_sum_monomialsLE z v g hgD j)]
  refine tendsto_finsetSum (monomialsLE n D) ?_
  intro m hm
  have hmc : Tendsto (fun k : ℕ => (((u k).coeff m : ℝ) : ℂ)) atTop (𝓝 (((g.coeff m : ℝ) : ℂ))) := by
    exact (continuous_algebraMap ℝ ℂ).continuousAt.tendsto.comp (hconv m)
  have hcst : Tendsto (fun k : ℕ => (sliceMon n z v m).coeff j) atTop
      (𝓝 ((sliceMon n z v m).coeff j)) := tendsto_const_nhds
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmc.mul hcst

/-! Convergence of coefficients, a good slice direction, root isolation. -/

lemma exists_monomial_ne_zero_of_ne_zero {n : ℕ} (g : MvPolynomial (Fin n) ℝ) (hg : g ≠ 0) :
    ∃ m : Fin n →₀ ℕ, g.coeff m ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hg
  ext m
  exact h m

lemma coeff_tendsto_of_deg_le {n D : ℕ} (u : ℕ → MvPolynomial (Fin n) ℝ)
    (g : MvPolynomial (Fin n) ℝ)
    (hconv : ∀ m : Fin n →₀ ℕ, Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)))
    (hg : g ≠ 0) :
    ∀ᶠ k in atTop, u k ≠ 0 := by
  classical
  rcases exists_monomial_ne_zero_of_ne_zero g hg with ⟨m, hm⟩
  have ht : Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)) := hconv m
  have hev : ∀ᶠ k in atTop, (u k).coeff m ≠ 0 := by
    exact ht.eventually_ne hm
  filter_upwards [hev] with k hk
  intro hk0
  apply hk
  rw [hk0]
  simp

lemma exists_tsl_slicePoly_ne_zero {n : ℕ} (z : Fin n → ℂ) (g : MvPolynomial (Fin n) ℝ)
    (hg : g ≠ 0) :
    ∃ v : Fin n → ℂ, tsl_slicePoly n z v g ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hg
  apply MvPolynomial.funext (p := g) (q := 0)
  intro x
  have hx : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => (x i : ℂ)) g = 0 := by
    have hv := h (fun i : Fin n => (x i : ℂ) - z i)
    have hslice := tsl_slicePoly_eval n z (fun i : Fin n => (x i : ℂ) - z i) g 1
    rw [hv] at hslice
    have hfun : (fun i : Fin n => z i + 1 * ((x i : ℂ) - z i)) = fun i : Fin n => (x i : ℂ) := by
      funext i
      ring
    simpa [hfun] using hslice.symm
  have h3 := MvPolynomial.aeval_algebraMap_apply (R := ℝ) (A := ℝ) (B := ℂ) (x := x) (p := g)
  have hx0 : (algebraMap ℝ ℂ (MvPolynomial.aeval x g)) = 0 := by
    rw [← h3]
    simpa [Function.comp_def] using hx
  have hx0' : MvPolynomial.aeval x g = 0 := Complex.ofReal_eq_zero.mp hx0
  simpa using hx0'

lemma exists_lt_norm_of_finite_nonzero {s : Finset ℂ} (hs : ∀ z ∈ s, z ≠ 0)
    (hsne : s.Nonempty) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ s, ρ < ‖z‖ := by
  classical
  let N : Finset ℝ := s.image (fun z : ℂ => ‖z‖)
  have hNne : N.Nonempty := by
    rcases hsne with ⟨z, hz⟩
    exact ⟨‖z‖, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  let m : ℝ := N.min' hNne
  have hm_mem : m ∈ N := Finset.min'_mem N hNne
  have hm_pos : 0 < m := by
    rcases Finset.mem_image.mp hm_mem with ⟨z, hz, hzN⟩
    rw [← hzN]
    exact norm_pos_iff.mpr (hs z hz)
  refine ⟨m / 2, by positivity, ?_⟩
  intro z hz
  have hzn : ‖z‖ ∈ N := Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hmle : m ≤ ‖z‖ := Finset.min'_le N ‖z‖ hzn
  linarith

lemma exists_root_isolated {p : Polynomial ℂ} (hp : p ≠ 0) (hp0 : p.eval 0 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, z ∈ Metric.closedBall 0 ρ → z ≠ 0 → p.eval z ≠ 0 := by
  classical
  let S : Set ℂ := {z | z ≠ 0 ∧ p.eval z = 0}
  have hSfin : S.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot hp).subset ?_
    intro z hz
    exact hz.2
  by_cases hS : S = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz hz0 hroot
    have hzS : z ∈ S := ⟨hz0, hroot⟩
    rw [hS] at hzS
    exact hzS
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS
    let T : Finset ℂ := hSfin.toFinset
    have hT : T.Nonempty := by
      rcases hSne with ⟨z, hz⟩
      exact ⟨z, (hSfin.mem_toFinset).mpr hz⟩
    have hTz : ∀ z ∈ T, z ≠ 0 := by
      intro z hz
      exact ((hSfin.mem_toFinset).mp hz).1
    rcases exists_lt_norm_of_finite_nonzero hTz hT with ⟨ρ, hρ0, hρ⟩
    refine ⟨ρ, hρ0, ?_⟩
    intro z hz hz0 hroot
    have hzS : z ∈ S := ⟨hz0, hroot⟩
    have hzT : z ∈ T := (hSfin.mem_toFinset).mpr hzS
    have hzρ : ‖z‖ ≤ ρ := by
      have hzball := Metric.mem_closedBall.mp hz
      simpa using hzball
    have hlt := hρ z hzT  -- ρ < ‖z‖
    linarith

/-- For every `i`, `z i + t (v i)` stays in the upper half plane for `‖t‖`
sufficiently small, uniformly in `i`. -/
lemma exists_stay_upper (n : ℕ) (z v : Fin n → ℂ)
    (hz : ∀ i : Fin n, 0 < (z i).im) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℂ, ‖t‖ < ρ → ∀ i : Fin n, 0 < (z i + t * v i).im := by
  classical
  by_cases hn : Nonempty (Fin n)
  · let ratio : Fin n → ℝ := fun i => (z i).im / (‖v i‖ + 1)
    have hratio_pos : ∀ i, 0 < ratio i := by
      intro i
      dsimp [ratio]
      exact div_pos (hz i) (by positivity)
    let ρ : ℝ := (Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio) / 2
    have hinf_pos : 0 < Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio := by
      rw [Finset.lt_inf'_iff]
      intro i hi
      exact hratio_pos i
    have hρpos : 0 < ρ := by
      dsimp [ρ]
      exact div_pos hinf_pos zero_lt_two
    have hρ_lt : ∀ i, ρ < ratio i := by
      intro i
      have hhalf : (Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio) / 2 <
          Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio := by
        rw [div_lt_iff₀ zero_lt_two]
        linarith
      have hle := Finset.inf'_le ratio (Finset.mem_univ i)
      exact lt_of_lt_of_le hhalf hle
    refine ⟨ρ, hρpos, ?_⟩
    intro t ht i
    have h_lt_ratio : ‖t‖ < ratio i := lt_trans ht (hρ_lt i)
    have hden : 0 < ‖v i‖ + 1 := by positivity
    have hmul_lt : ‖t‖ * ‖v i‖ < (z i).im := by
      have hmul : ‖t‖ * ‖v i‖ ≤ ‖t‖ * (‖v i‖ + 1) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg t)
      have hlt' : ‖t‖ * (‖v i‖ + 1) < (z i).im := by
        exact (lt_div_iff₀ hden).mp h_lt_ratio
      exact lt_of_le_of_lt hmul hlt'
    have him : ‖t * v i‖ < (z i).im := by
      simpa [norm_mul] using hmul_lt
    have h_abs_im : |(t * v i).im| < (z i).im :=
      (Complex.abs_im_le_norm (t * v i)).trans_lt him
    have hlow : -((z i).im) < (t * v i).im := (abs_lt.mp h_abs_im).1
    have him_sum : (z i + t * v i).im = (z i).im + (t * v i).im := by
      simp [Complex.add_im]
    rw [him_sum]
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro t ht i
    exact False.elim (hn ⟨i⟩)


theorem isStable_tendsto_of_degree_le (n D : ℕ) (u : ℕ → MvPolynomial (Fin n) ℝ)
    (g : MvPolynomial (Fin n) ℝ)
    (huD : ∀ k : ℕ, (u k).totalDegree ≤ D) (hgD : g.totalDegree ≤ D)
    (hconv : ∀ m : Fin n →₀ ℕ, Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)))
    (hstab : ∀ k : ℕ, (u k) = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) (u k) ≠ 0) :
    g = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) g ≠ 0 := by
  classical
  by_cases hg : g = 0
  · exact Or.inl hg
  · right
    intro z
    by_contra hz0
    let zc : Fin n → ℂ := fun i => ((z i : UpperHalfPlane) : ℂ)
    have hz0' : MvPolynomial.aeval (R := ℝ) zc g = 0 := by
      simpa [zc] using hz0
    have hz_im : ∀ i : Fin n, 0 < (zc i).im := by
      intro i
      dsimp [zc]
      exact UpperHalfPlane.im_pos (z i)
    obtain ⟨v, hv⟩ := exists_tsl_slicePoly_ne_zero zc g hg
    let Q : Polynomial ℂ := tsl_slicePoly n zc v g
    have hQ0 : Q.eval 0 = 0 := by
      change Polynomial.eval 0 (tsl_slicePoly n zc v g) = 0
      simpa [hz0'] using tsl_slicePoly_eval n zc v g 0
    obtain ⟨ρ₁, hρ₁0, hiso⟩ := exists_root_isolated (p := Q) hv hQ0
    obtain ⟨ρ₂, hρ₂0, hup⟩ := exists_stay_upper n zc v hz_im
    let ρ : ℝ := min ρ₁ ρ₂
    have hρ0 : 0 < ρ := lt_min hρ₁0 hρ₂0
    have hρ_le₁ : ρ ≤ ρ₁ := min_le_left ρ₁ ρ₂
    have hρ_le₂ : ρ ≤ ρ₂ := min_le_right ρ₁ ρ₂
    have hlim : ∀ i : Fin (D + 1),
        Tendsto (fun k : ℕ => (tsl_slicePoly n zc v (u k)).coeff (i : ℕ)) atTop
          (𝓝 ((tsl_slicePoly n zc v g).coeff (i : ℕ))) := by
      intro i
      exact tsl_slicePoly_coeff_tendsto zc v u g huD hgD hconv (i : ℕ)
    let c : ℕ → Fin (D + 1) → ℂ := fun k i => (tsl_slicePoly n zc v (u k)).coeff (i : ℕ)
    let cf : Fin (D + 1) → ℂ := fun i => (tsl_slicePoly n zc v g).coeff (i : ℕ)
    have hsum_eq_g : (∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) (cf i)) = Q := by
      dsimp [cf, Q]
      exact (tsl_slicePoly_eq_partialSum zc v g hgD).symm
    have hroot0 : Polynomial.eval 0 (∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) (cf i)) = 0 := by
      rw [hsum_eq_g]
      exact hQ0
    have hpunct : ∀ w : ℂ, w ∈ Metric.closedBall 0 ρ → w ≠ 0 →
        Polynomial.eval w (∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) (cf i)) ≠ 0 := by
      intro w hw hw0
      rw [hsum_eq_g]
      have hw₁ : w ∈ Metric.closedBall 0 ρ₁ := by
        exact (Metric.closedBall_subset_closedBall hρ_le₁) hw
      exact hiso w hw₁ hw0
    obtain ⟨N, hN⟩ := gch_complexHurwitz D c cf hlim (0 : ℂ) (ρ := ρ) hρ0 hroot0 hpunct
    have hnev : ∀ᶠ k in atTop, u k ≠ 0 := coeff_tendsto_of_deg_le (n := n) (D := D) u g hconv hg
    have hevge : ∀ᶠ k in atTop, N ≤ k := Filter.eventually_ge_atTop N
    have hevall : ∀ᶠ k in atTop, u k ≠ 0 ∧ N ≤ k := hnev.and hevge
    rw [Filter.eventually_atTop] at hevall
    rcases hevall with ⟨N₀, hN₀⟩
    let k : ℕ := max N₀ N
    have hkprop := hN₀ k (le_max_left N₀ N)
    have huk0 : u k ≠ 0 := hkprop.1
    have hkN : N ≤ k := le_max_right N₀ N
    rcases hN k hkN with ⟨w, hwd, hwroot⟩
    have hwρ : ‖w‖ < ρ := by
      simpa [dist_eq_norm] using hwd
    have hwρ₂ : ‖w‖ < ρ₂ := lt_of_lt_of_le hwρ hρ_le₂
    let z' : Fin n → UpperHalfPlane := fun i => ⟨zc i + w * v i, hup w hwρ₂ i⟩
    have hstabk := hstab k
    cases hstabk with
    | inl hk0 =>
        exact huk0 hk0
    | inr hstable =>
        -- hstable : ∀ z' : Fin n → UpperHalfPlane, aeval (fun i => (z' i : ℂ)) (u k) ≠ 0
        have hcontra : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ)) (u k) = 0 := by
          have hz'eval : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => zc i + w * v i) (u k) = 0 := by
            have heq : (tsl_slicePoly n zc v (u k)) = ∑ j : Fin (D + 1),
                Polynomial.monomial (j : ℕ) ((tsl_slicePoly n zc v (u k)).coeff (j : ℕ)) := by
              exact tsl_slicePoly_eq_partialSum zc v (u k) (huD k)
            have hwroot' : Polynomial.eval w (tsl_slicePoly n zc v (u k)) = 0 := by
              -- hwroot is about the c-sum; the c-sum equals the slice
              have hsum_eq_uk : (∑ j : Fin (D + 1), Polynomial.monomial (j : ℕ) (c k j)) =
                  tsl_slicePoly n zc v (u k) := by
                rw [heq]
              rw [← hsum_eq_uk]
              exact hwroot
            have hslice := tsl_slicePoly_eval n zc v (u k) w
            simpa using (hslice.symm.trans hwroot')
          simpa [z'] using hz'eval
        exact hstable z' hcontra


/-! =====================================================================
Port of the rescale / degree-part machinery and the `a₀ = 0` wall case
from commons `homogenization_wallHyperbolic` (definitions that already
exist in this file are not re-imported).
===================================================================== -/

noncomputable def rescale {n : ℕ} (d : ℕ) (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m * c ^ (d - m.degree))

lemma rescale_coeff {n : ℕ} (d : ℕ) (c : ℝ) (p : MvPolynomial (Fin n) ℝ)
    (m : Fin n →₀ ℕ) :
    (rescale d c p).coeff m = p.coeff m * c ^ (d - m.degree) := by
  classical
  unfold rescale
  rw [MvPolynomial.coeff_sum]
  by_cases hm : m ∈ p.support
  · rw [Finset.sum_eq_single m]
    · rw [MvPolynomial.coeff_monomial]
      simp
    · intro b hb hbne
      rw [MvPolynomial.coeff_monomial]
      have hbm : b ≠ m := by
        intro hbm'
        exact hbne hbm'
      simp [hbm]
    · intro hnot
      exact False.elim (hnot hm)
  · have hsum0 : (∑ x ∈ p.support,
        MvPolynomial.coeff m (MvPolynomial.monomial x (p.coeff x * c ^ (d - x.degree)))) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [MvPolynomial.coeff_monomial]
      have hxm : x ≠ m := by
        intro hxm'
        apply hm
        rw [← hxm']
        exact hx
      simp [hxm]
    rw [hsum0]
    have hp0 : p.coeff m = 0 := by
      by_contra h
      exact hm (MvPolynomial.mem_support_iff.mpr h)
    simp [hp0]

lemma rescale_support_subset {n : ℕ} (d : ℕ) (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    (rescale d c p).support ⊆ p.support := by
  classical
  intro m hm
  have hc : (rescale d c p).coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  rw [rescale_coeff] at hc
  exact MvPolynomial.mem_support_iff.mpr (by
    intro hp0
    apply hc
    simp [hp0])

/-- Evaluating the degree-`d` part at `x` expands over the degree-`d` support monomials. -/

lemma rescale_eval {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (c : ℝ) (hc : c ≠ 0) (w : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) w (rescale d c p) =
      ((c : ℝ) : ℂ) ^ d *
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => w i / (c : ℂ)) p := by
  classical
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  unfold rescale
  rw [map_sum]
  rw [aeval_sum_real_ℂ p (fun i : Fin n => w i / (c : ℂ))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hdegm : m.degree ≤ d := hdeg m hm
  rw [MvPolynomial.aeval_monomial]
  have hprod : (∏ i : Fin n, (w i) ^ (m i)) =
      ((c : ℝ) : ℂ) ^ m.degree * ∏ i : Fin n, (w i / (c : ℂ)) ^ (m i) := by
    calc
      (∏ i : Fin n, (w i) ^ (m i))
          = ∏ i : Fin n, (((c : ℂ) : ℂ) * (w i / (c : ℂ))) ^ (m i) := by
              apply Finset.prod_congr rfl
              intro i hi
              have hmul : ((c : ℝ) : ℂ) * (w i / (c : ℂ)) = w i := by field_simp [hcC]
              rw [hmul]
      _ = ∏ i : Fin n, (((c : ℝ) : ℂ) ^ (m i) * (w i / (c : ℂ)) ^ (m i)) := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [mul_pow]
      _ = (∏ i : Fin n, ((c : ℝ) : ℂ) ^ (m i)) * ∏ i : Fin n, (w i / (c : ℂ)) ^ (m i) := by
              rw [Finset.prod_mul_distrib]
      _ = ((c : ℝ) : ℂ) ^ m.degree * ∏ i : Fin n, (w i / (c : ℂ)) ^ (m i) := by
              rw [pow_prod_degree]
  have hp : ((c : ℝ) : ℂ) ^ (d - m.degree) * ((c : ℝ) : ℂ) ^ m.degree =
      ((c : ℝ) : ℂ) ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hdegm]
  have hconv : (algebraMap ℝ ℂ) (p.coeff m * c ^ (d - m.degree)) =
      ((p.coeff m : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ (d - m.degree) := by
    rw [map_mul, map_pow]
    simp
  calc
    (algebraMap ℝ ℂ) (p.coeff m * c ^ (d - m.degree)) *
        (m.prod (fun i k => w i ^ k))
        = ((p.coeff m : ℝ) : ℂ) * (((c : ℝ) : ℂ) ^ (d - m.degree) *
            ∏ i : Fin n, (w i) ^ (m i)) := by
            rw [hconv]
            have hprod_univ : m.prod (fun i k => w i ^ k) = ∏ i : Fin n, (w i) ^ (m i) := by
              exact finsupp_prod_eq_prod_univ m (fun i k => w i ^ k) (by intro i; simp)
            rw [hprod_univ]
            ring
    _ = ((p.coeff m : ℝ) : ℂ) * (((c : ℝ) : ℂ) ^ (d - m.degree) *
            (((c : ℝ) : ℂ) ^ m.degree * ∏ i : Fin n, (w i / (c : ℂ)) ^ (m i))) := by
            rw [hprod]
    _ = ((c : ℝ) : ℂ) ^ d * (((p.coeff m : ℝ) : ℂ) *
          ∏ i : Fin n, (w i / (c : ℂ)) ^ (m i)) := by
            rw [← mul_assoc (((c : ℝ) : ℂ) ^ (d - m.degree)) (((c : ℝ) : ℂ) ^ m.degree)]
            rw [hp]
            ring

/-- A positive rescaling of a stable polynomial is stable. -/
lemma rescale_stable {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (c : ℝ) (hc0 : 0 < c)
    (hstab : ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    ∀ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ))
        (rescale d c p) ≠ 0 := by
  classical
  intro z
  let zc : Fin n → ℂ := fun i => ((z i : UpperHalfPlane) : ℂ) / (c : ℂ)
  have hcne : c ≠ 0 := ne_of_gt hc0
  have him : ∀ i : Fin n, 0 < (zc i).im := by
    intro i
    dsimp [zc]
    rw [im_div_real]
    exact div_pos (UpperHalfPlane.im_pos (z i)) hc0
  let z' : Fin n → UpperHalfPlane := fun i => ⟨zc i, him i⟩
  have hz' : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ)) p ≠ 0 :=
    hstab z'
  have hz'c : (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ)) = zc := by
    funext i
    simp [z']
  have hne : MvPolynomial.aeval (R := ℝ) zc p ≠ 0 := by
    simpa [hz'c] using hz'
  have hev := rescale_eval p hdeg c hcne (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ))
  rw [hev]
  apply mul_ne_zero
  · exact pow_ne_zero d (by exact_mod_cast hcne)
  · simpa [zc] using hne

open Filter Topology

/-- `cSeq k = 1 / (k+1)`, a positive sequence tending to `0`. -/
def cSeq (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ)⁻¹

lemma cSeq_pos (k : ℕ) : 0 < cSeq k := by
  dsimp [cSeq]
  positivity

lemma cSeq_ne_zero (k : ℕ) : cSeq k ≠ 0 := ne_of_gt (cSeq_pos k)

lemma tendsto_cSeq_zero : Tendsto cSeq atTop (nhds (0 : ℝ)) := by
  have hden : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (f := fun k : ℕ => (k : ℝ)) (g := fun k : ℕ => ((k + 1 : ℕ) : ℝ))
    · intro k
      exact_mod_cast (Nat.le_succ k)
    · exact tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp hden

lemma tendsto_pow_cSeq_zero (e : ℕ) :
    Tendsto (fun k : ℕ => (cSeq k) ^ e) atTop (nhds ((0 : ℝ) ^ e)) := by
  induction e with
  | zero => simp
  | succ e ih =>
      have h : Tendsto (fun k : ℕ => (cSeq k) ^ e * cSeq k) atTop (𝓝 ((0 : ℝ) ^ e * 0)) :=
        ih.mul tendsto_cSeq_zero
      simpa [pow_succ] using h

/-- Coefficients of `rescale d (cSeq k) p` converge to the coefficients of `degreePart d p`. -/
lemma tendsto_rescale_coeff {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d) (m : Fin n →₀ ℕ) :
    Tendsto (fun k : ℕ => (rescale d (cSeq k) p).coeff m) atTop
      (𝓝 ((degreePart d p).coeff m)) := by
  classical
  by_cases hm : m ∈ p.support
  · have hfun : (fun k : ℕ => (rescale d (cSeq k) p).coeff m) =
        fun k : ℕ => p.coeff m * (cSeq k) ^ (d - m.degree) := by
      funext k
      rw [rescale_coeff]
    rw [hfun]
    rw [degreePart_coeff]
    by_cases hd : m.degree = d
    · rw [if_pos hd]
      have hsub : d - m.degree = 0 := by rw [hd]; simp
      have ht : Tendsto (fun k : ℕ => p.coeff m * (cSeq k) ^ (d - m.degree)) atTop
          (𝓝 (p.coeff m * (0 : ℝ) ^ (d - m.degree))) :=
        tendsto_const_nhds.mul (tendsto_pow_cSeq_zero (d - m.degree))
      have hval : p.coeff m * (0 : ℝ) ^ (d - m.degree) = p.coeff m := by
        rw [hsub]
        simp
      simpa [hval] using ht
    · rw [if_neg hd]
      have hlt : m.degree < d := lt_of_le_of_ne (hdeg m hm) hd
      have hpos : 0 < d - m.degree := Nat.sub_pos_of_lt hlt
      have ht : Tendsto (fun k : ℕ => p.coeff m * (cSeq k) ^ (d - m.degree)) atTop
          (𝓝 (p.coeff m * (0 : ℝ) ^ (d - m.degree))) :=
        tendsto_const_nhds.mul (tendsto_pow_cSeq_zero (d - m.degree))
      have hval : p.coeff m * (0 : ℝ) ^ (d - m.degree) = 0 := by
        rw [zero_pow (ne_of_gt hpos)]
        ring
      simpa [hval] using ht
  · have hp0 : p.coeff m = 0 := by
      by_contra h
      exact hm (MvPolynomial.mem_support_iff.mpr h)
    have hfun : (fun k : ℕ => (rescale d (cSeq k) p).coeff m) = fun _ : ℕ => 0 := by
      funext k
      rw [rescale_coeff]
      simp [hp0]
    rw [hfun]
    rw [degreePart_coeff]
    simp [hp0]

/-- The degree-`d` homogeneous part of a stable polynomial is stable (or zero). -/
theorem degreePart_stable_of_stable {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (hstab : ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    degreePart d p = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) (degreePart d p) ≠ 0 := by
  classical
  let u : ℕ → MvPolynomial (Fin n) ℝ := fun k => rescale d (cSeq k) p
  let D : ℕ := p.totalDegree
  have huD : ∀ k : ℕ, (u k).totalDegree ≤ D := by
    intro k
    dsimp [u, D]
    exact MvPolynomial.totalDegree_le_of_support_subset (rescale_support_subset d (cSeq k) p)
  have hgD : (degreePart d p).totalDegree ≤ D := by
    dsimp [D]
    exact MvPolynomial.totalDegree_le_of_support_subset (degreePart_support_subset d p)
  have hconv : ∀ m : Fin n →₀ ℕ,
      Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 ((degreePart d p).coeff m)) := by
    intro m
    dsimp [u]
    exact tendsto_rescale_coeff p hdeg m
  have hstab' : ∀ k : ℕ, u k = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) (u k) ≠ 0 := by
    intro k
    right
    dsimp [u]
    exact rescale_stable p hdeg (cSeq k) (cSeq_pos k) hstab
  exact isStable_tendsto_of_degree_le n D u (degreePart d p) huD hgD hconv hstab'

/-- The homogenized line restriction is zero or real-rooted when the base point lies on the
wall `a 0 = 0`. -/
theorem wallHyp_a0zero {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (hstab : ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0)
    (a : Fin (n + 1) → ℝ) (ha0 : a 0 = 0) :
    RealRootedOrZero (LinePoly (homogenization d p) a (eWall n)) := by
  classical
  have hsplit := degreePart_stable_of_stable p hdeg hstab
  rcases hsplit with hpd0 | hpdnv
  · left
    -- the line polynomial is zero because the degree-d part of `p` vanishes
    have hQc : Polynomial.map (algebraMap ℝ ℂ) (LinePoly (homogenization d p) a (eWall n)) = 0 := by
      apply Polynomial.funext (p := Polynomial.map (algebraMap ℝ ℂ)
        (LinePoly (homogenization d p) a (eWall n))) (q := 0)
      intro r
      have hle := lineEval (H := homogenization d p) (a := a) (b := eWall n) (t := r)
      -- hle : eval r (map C (LinePoly H a eWall n)) =
      --        aeval (fun j => ((a j : ℝ) : ℂ) + r * (eWall n j : ℝ)) H
      rw [hle]
      let w : Fin (n + 1) → ℂ := fun j => ((a j : ℝ) : ℂ) + r * (eWall n j : ℝ)
      have hw0 : w 0 = 0 := by
        dsimp [w]
        simp [ha0, eWall_zero]
      have hfe := hom_eval_first_zero p hdeg w hw0
      rw [hfe]
      simp [hpd0]
    exact (Polynomial.map_injective (algebraMap ℝ ℂ)
      (by intro x y h; exact Complex.ofReal_injective h)) (by simpa using hQc)
  · apply realRooted_of_noUHP (P := LinePoly (homogenization d p) a (eWall n))
    intro r hr
    have hle := lineEval (H := homogenization d p) (a := a) (b := eWall n) (t := r)
    rw [hle]
    let w : Fin (n + 1) → ℂ := fun j => ((a j : ℝ) : ℂ) + r * (eWall n j : ℝ)
    have hw0 : w 0 = 0 := by
      dsimp [w]
      simp [ha0, eWall_zero]
    have hfe := hom_eval_first_zero p hdeg w hw0
    rw [hfe]
    let zc : Fin n → ℂ := fun i => w i.succ
    have him : ∀ i : Fin n, 0 < (zc i).im := by
      intro i
      dsimp [zc, w]
      simp [eWall_succ, Complex.add_im]
      exact hr
    let z' : Fin n → UpperHalfPlane := fun i => ⟨zc i, him i⟩
    have hz' : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ))
        (degreePart d p) ≠ 0 := hpdnv z'
    have hz'c : (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ)) = zc := by
      funext i
      simp [z']
    have hne : MvPolynomial.aeval (R := ℝ) zc (degreePart d p) ≠ 0 := by
      simpa [hz'c] using hz'
    simpa [zc] using hne



/-! =====================================================================
Final glue: hyperbolicity for all bases, wall evaluation positivity,
X₀-factorization, and the constant case.
===================================================================== -/

/-- A monomial of degree zero is the zero monomial. -/
lemma degree_zero_eq_zero {n : ℕ} (m : Fin n →₀ ℕ) (h : m.degree = 0) : m = 0 :=
  (Finsupp.degree_eq_zero_iff m).mp h

/-- If `p ≠ 0` and every monomial of `p` has degree `0`, then the support of `p`
is exactly `{0}`. -/
lemma support_eq_zero_of_degree_zero {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp0 : p ≠ 0)
    (hdeg0 : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree = 0) : p.support = {0} := by
  classical
  apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
  constructor
  · rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hp0
    exact (MvPolynomial.support_eq_empty.mp h)
  · intro m hm
    exact degree_zero_eq_zero m (hdeg0 m hm)

/-- Hyperbolicity of the homogenization in the wall direction `eWall`, for every real
base point: the line restriction is zero or real-rooted. -/
theorem wallHyp_all {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (hp : p ≠ 0)
    (hstab : ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0)
    (a : Fin (n + 1) → ℝ) :
    RealRootedOrZero (LinePoly (homogenization d p) a (eWall n)) := by
  classical
  by_cases ha0 : a 0 = 0
  · exact wallHyp_a0zero p hdeg hstab a ha0
  · exact wallHyp_nonzero p hdeg hp hstab a ha0

/-- Real evaluation of the homogenization, expanded over the support of `p`. -/
lemma hom_eval_real {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Fin (n + 1) → ℝ) :
    MvPolynomial.aeval (R := ℝ) x (homogenization d p) =
      ∑ m ∈ p.support, (p.coeff m) *
        ((x 0) ^ (d - m.degree) * ∏ i : Fin n, (x i.succ) ^ (m i)) := by
  classical
  unfold homogenization
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.aeval_monomial]
  have hconv := finsupp_prod_eq_prod_univ (m := Finsupp.cons (d - m.degree) m)
    (g := fun j e => x j ^ e) (by intro j; simp)
  rw [hconv]
  rw [prod_cons_univ]
  simp

/-- Evaluating the homogenization at the wall direction `eWall` equals the sum of the
coefficients of the degree-`D` monomials; it is positive when those are nonnegative and
a degree-`D` monomial occurs. -/
lemma eval_wall_pos {n D : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ D)
    (hD : ∃ m ∈ p.support, m.degree = D) :
    0 < MvPolynomial.eval (eWall n) (homogenization D p) := by
  classical
  change 0 < MvPolynomial.aeval (R := ℝ) (fun j : Fin (n + 1) => (eWall n j)) (homogenization D p)
  rw [hom_eval_real]
  simp [eWall_zero, eWall_succ]
  have hterm : ∀ m ∈ p.support,
      p.coeff m * (0 : ℝ) ^ (D - m.degree) = if m.degree = D then p.coeff m else 0 := by
    intro m hm
    have hdegm : m.degree ≤ D := hdeg m hm
    by_cases hd : m.degree = D
    · have hsub : D - m.degree = 0 := by omega
      have hzero : (0 : ℝ) ^ (D - m.degree) = 1 := by rw [hsub]; simp
      simp [hd, hzero]
    · have hlt : m.degree < D := lt_of_le_of_ne hdegm hd
      have hpos : 0 < D - m.degree := Nat.sub_pos_of_lt hlt
      have hzero : (0 : ℝ) ^ (D - m.degree) = 0 := by rw [zero_pow (ne_of_gt hpos)]
      simp [hd, hzero]
  have heqsum : (∑ m ∈ p.support, p.coeff m * (0 : ℝ) ^ (D - m.degree)) =
        ∑ m ∈ p.support.filter (fun m => m.degree = D), p.coeff m := by
    calc
      (∑ m ∈ p.support, p.coeff m * (0 : ℝ) ^ (D - m.degree))
          = ∑ m ∈ p.support, (if m.degree = D then p.coeff m else 0) := by
              apply Finset.sum_congr rfl
              intro m hm
              exact hterm m hm
      _ = ∑ m ∈ p.support.filter (fun m => m.degree = D), p.coeff m := by
              rw [← Finset.sum_filter]
  rw [heqsum]
  rcases hD with ⟨m0, hm0s, hm0d⟩
  refine Finset.sum_pos' ?hge ?hpos
  · intro m hm
    exact hnn m
  · refine ⟨m0, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hm0s, hm0d⟩
    · have hne : p.coeff m0 ≠ 0 := (MvPolynomial.mem_support_iff.mp hm0s)
      exact lt_of_le_of_ne (hnn m0) (Ne.symm hne)

lemma hom_eval_X0 {n D E : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ E)
    (hDE : E ≤ D) (w : Fin (n + 1) → ℂ) :
    MvPolynomial.aeval (R := ℝ) w (homogenization D p) =
      (w 0) ^ (D - E) * MvPolynomial.aeval (R := ℝ) w (homogenization E p) := by
  classical
  rw [hom_eval]
  rw [hom_eval]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hdegm : m.degree ≤ E := hdeg m hm
  have hpw : (w 0) ^ (D - m.degree) = (w 0) ^ (D - E) * (w 0) ^ (E - m.degree) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpw]
  ring

/-- If all monomials of `p` have degree zero and `p ≠ 0`, then the homogenization of
`p` at degree zero is the constant `p.coeff 0`. -/
lemma homogenization_zero_eval {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp0 : p ≠ 0)
    (hdeg0 : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree = 0)
    (w : Fin (n + 1) → ℂ) :
    MvPolynomial.aeval (R := ℝ) w (homogenization 0 p) = ((p.coeff 0 : ℝ) : ℂ) := by
  classical
  have hsupp : p.support = {0} := support_eq_zero_of_degree_zero p hp0 hdeg0
  unfold homogenization
  rw [hsupp]
  rw [Finset.sum_singleton]
  rw [MvPolynomial.aeval_monomial]
  have hdegm : (0 : Fin n →₀ ℕ).degree = 0 := by simp
  have hcons : Finsupp.cons (0 - (0 : Fin n →₀ ℕ).degree) (0 : Fin n →₀ ℕ) = 0 := by
    ext j
    cases j using Fin.cases with
    | zero => simp [hdegm]
    | succ i => simp [hdegm]
  have hprod : ((0 : Fin (n + 1) →₀ ℕ).prod fun j e => w j ^ e) = 1 := by simp
  simp [hcons, hprod]



/-- The homogenization of a stable polynomial with nonnegative coefficients is stable on
the open upper half plane. -/
theorem homogenization_core_stable {n d d' : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m)
    (hdeg' : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d')
    (htop : ∃ m : Fin n →₀ ℕ, m ∈ p.support ∧ m.degree = d')
    (hd'le : d' ≤ d)
    (hp0 : p ≠ 0)
    (hpstab : ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    ∀ w : Fin (n + 1) → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
        (homogenization d p) ≠ 0 := by
  classical
  by_cases hd'0 : d' = 0
  · -- constant case: every monomial has degree `0`, so `p` is a nonzero constant and
    -- the homogenization is a pure power of `X₀`.
    intro w
    have hdeg0 : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree = 0 := by
      intro m hm
      have hle : m.degree ≤ 0 := by simpa [hd'0] using hdeg' m hm
      exact le_antisymm hle (Nat.zero_le _)
    have hc0ne : p.coeff 0 ≠ 0 := by
      have hsupp : p.support = {0} := support_eq_zero_of_degree_zero p hp0 hdeg0
      exact (MvPolynomial.mem_support_iff.mp (by rw [hsupp]; simp))
    have hw0 : (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ)) 0 ≠ 0 := by
      have him : 0 < (((w 0 : UpperHalfPlane) : ℂ).im) := UpperHalfPlane.im_pos (w 0)
      intro hz
      have hz' : ((w 0 : UpperHalfPlane) : ℂ) = 0 := by simpa using hz
      rw [hz'] at him
      simpa using him
    have hfac := hom_eval_X0 (D := d) (E := d') p hdeg' hd'le
      (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
    rw [hfac]
    have hsub : d - d' = d := by omega
    rw [hsub]
    rw [hd'0]
    rw [homogenization_zero_eval p hp0 hdeg0]
    apply mul_ne_zero
    · simpa using (pow_ne_zero d hw0)
    · exact_mod_cast hc0ne
  · -- nonconstant case: apply the Gårding cone theorem to the homogenization at the
    -- top degree `d' > 0` in the wall direction.
    have hdpos : 0 < d' := Nat.pos_of_ne_zero hd'0
    have hstab_core : ∀ w : Fin (n + 1) → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
          (homogenization d' p) ≠ 0 := by
      exact garding_stable_of_hyperbolic_and_cone (m := n + 1) (d := d')
        (homogenization d' p) (eWall n) hdpos
        (hom_isHomogeneous (d := d') p hdeg')
        (by
          rcases htop with ⟨m0, hm0s, hm0d⟩
          intro hz
          have hsub : d' - m0.degree = 0 := by omega
          have hc : (homogenization d' p).coeff (Finsupp.cons 0 m0) = p.coeff m0 := by
            simpa [hsub] using (hom_coeff_cons (d := d') p m0 hm0s)
          have hc0 : p.coeff m0 ≠ 0 := (MvPolynomial.mem_support_iff.mp hm0s)
          apply hc0
          rw [← hc]
          rw [hz]
          simp)
        (hom_coeff_nonneg (d := d') p hnn)
        (ne_of_gt (eval_wall_pos (D := d') p hnn hdeg' (by
          rcases htop with ⟨m0, hm0s, hm0d⟩
          exact ⟨m0, hm0s, hm0d⟩)))
        (by
          intro a
          change RealRootedOrZero (LinePoly (homogenization d' p) a (eWall n))
          exact wallHyp_all p hdeg' hp0 hpstab a)
        (by
          intro u hu t ht
          apply ne_of_gt
          exact hom_pos_orthant (d := d') p hnn hp0 hdeg'
            (fun i : Fin (n + 1) => u i + t * (eWall n i)) (by
              intro i
              cases i using Fin.cases with
              | zero =>
                  have he : eWall n 0 = 0 := eWall_zero n
                  simp [he]
                  exact hu 0
              | succ i =>
                  have he : eWall n i.succ = 1 := eWall_succ n i
                  simp [he]
                  exact lt_of_lt_of_le (hu i.succ) (le_add_of_nonneg_right ht)))
    intro w
    have hw0 : (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ)) 0 ≠ 0 := by
      have him : 0 < (((w 0 : UpperHalfPlane) : ℂ).im) := UpperHalfPlane.im_pos (w 0)
      intro hz
      have hz' : ((w 0 : UpperHalfPlane) : ℂ) = 0 := by simpa using hz
      rw [hz'] at him
      simpa using him
    have hfac := hom_eval_X0 (D := d) (E := d') p hdeg' hd'le
      (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
    rw [hfac]
    apply mul_ne_zero
    · exact pow_ne_zero (d - d') hw0
    · exact hstab_core w

theorem homogenization_stable_of_stable_nonneg (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m)
    (hd : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (hstab : p = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    (∑ m ∈ p.support, MvPolynomial.monomial (Finsupp.cons (d - m.degree) m) (p.coeff m)) = 0 ∨
      ∀ w : Fin (n + 1) → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
          (∑ m ∈ p.support, MvPolynomial.monomial (Finsupp.cons (d - m.degree) m) (p.coeff m)) ≠ 0 := by
  classical
  change Stable (homogenization d p)
  by_cases hp0 : p = 0
  · left
    unfold homogenization
    have hsupp : p.support = ∅ := MvPolynomial.support_eq_empty.mpr hp0
    simp [hsupp]
  · right
    have hpstab : ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0 := by
      exact hstab.elim (fun hp0' => False.elim (hp0 hp0')) (fun h => h)
    let S : Finset ℕ := p.support.image (fun m : Fin n →₀ ℕ => m.degree)
    have hSne : S.Nonempty := by
      have hsupne : p.support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        apply hp0
        exact (MvPolynomial.support_eq_empty.mp h)
      exact hsupne.image (fun m : Fin n →₀ ℕ => m.degree)
    let d' : ℕ := S.max' hSne
    have hdeg' : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d' := by
      intro m hm
      have hmem : m.degree ∈ S := by
        dsimp [S]
        exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
      dsimp [d']
      exact Finset.le_max' S (m.degree) hmem
    have htop : ∃ m : Fin n →₀ ℕ, m ∈ p.support ∧ m.degree = d' := by
      have hd'mem : d' ∈ S := by
        dsimp [d']
        exact Finset.max'_mem S hSne
      rcases (Finset.mem_image.mp hd'mem) with ⟨m, hm, hf⟩
      refine ⟨m, hm, ?_⟩
      exact hf
    have hd'le : d' ≤ d := by
      dsimp [d']
      refine Finset.max'_le S hSne d ?_
      intro y hy
      rcases (Finset.mem_image.mp hy) with ⟨m, hm, hf⟩
      rw [← hf]
      exact hd m hm
    exact homogenization_core_stable (d' := d') p hnn hdeg' htop hd'le hp0 hpstab


end Commons.Analysis.MvPolynomial
