import Mathlib.Algebra.MvPolynomial.PDeriv
import Submission.Commons.Analysis.Complex.Polynomial.deriv_stable_of_stable
import Submission.Commons.Analysis.MvPolynomial.top_in_j_stable_of_stable

set_option linter.unusedVariables false

open MvPolynomial UpperHalfPlane
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace Commons.Analysis.MvPolynomial

/-- The univariate polynomial obtained from `p` by making variable `j` the polynomial
variable and fixing all other variables at the complex numbers `z i`. -/
def sliceP {n : ℕ} (z : Fin n → ℂ) (j : Fin n) (p : MvPolynomial (Fin n) ℝ) : Polynomial ℂ :=
  MvPolynomial.aeval (R := ℝ) (fun i : Fin n => if i = j then Polynomial.X else Polynomial.C (z i)) p

/-- Evaluation of the slice at `t` substitutes `t` for variable `j`. -/
lemma sliceP_eval {n : ℕ} (z : Fin n → ℂ) (j : Fin n) (p : MvPolynomial (Fin n) ℝ) (t : ℂ) :
    (sliceP z j p).eval t =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => if i = j then t else z i) p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [sliceP]
  | add p q hp hq =>
      unfold sliceP at hp hq ⊢
      rw [map_add, Polynomial.eval_add, map_add, hp, hq]
  | mul_X p i hp =>
      unfold sliceP at hp ⊢
      rw [map_mul, Polynomial.eval_mul]
      simp only [MvPolynomial.aeval_X]
      rw [map_mul, MvPolynomial.aeval_X]
      rw [hp]
      split_ifs <;> simp

/-- The value of the derivative of the slice equals the value of the partial derivative. -/
lemma sliceP_deriv_eval {n : ℕ} (z : Fin n → ℂ) (j : Fin n) (p : MvPolynomial (Fin n) ℝ) (t : ℂ) :
    (sliceP z j p).derivative.eval t =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => if i = j then t else z i)
        (MvPolynomial.pderiv (R := ℝ) j p) := by
  classical
  let A : MvPolynomial (Fin n) ℝ →ₐ[ℝ] Polynomial ℂ :=
    MvPolynomial.aeval (R := ℝ) (fun i : Fin n => if i = j then Polynomial.X else Polynomial.C (z i))
  let g : Fin n → ℂ := fun i => if i = j then t else z i
  have hA_eval : ∀ pp : MvPolynomial (Fin n) ℝ, (A pp).eval t = aeval (R := ℝ) g pp := by
    intro pp
    change (sliceP z j pp).eval t = aeval (R := ℝ) g pp
    rw [sliceP_eval]
  have hderivA_eval_X : ∀ i : Fin n, (A (X i)).derivative.eval t = aeval (R := ℝ) g (pderiv (R := ℝ) j (X i)) := by
    intro i
    by_cases hij : i = j
    · subst i
      simp [A, g]
    · have hpd : pderiv (R := ℝ) j (X i) = 0 := by simp [hij]
      simp [A, g, hij, hpd]
  have hderivA_eval : ∀ pp : MvPolynomial (Fin n) ℝ,
      (A pp).derivative.eval t = aeval (R := ℝ) g (pderiv (R := ℝ) j pp) := by
    intro pp
    induction pp using MvPolynomial.induction_on with
    | C a => simp [A]
    | add p q hp hq =>
        calc
          (A (p + q)).derivative.eval t
              = ((A p).derivative.eval t + (A q).derivative.eval t) := by
                  simp [A, Polynomial.derivative_add, Polynomial.eval_add]
          _ = aeval (R := ℝ) g (pderiv (R := ℝ) j p) + aeval (R := ℝ) g (pderiv (R := ℝ) j q) := by rw [hp, hq]
          _ = aeval (R := ℝ) g (pderiv (R := ℝ) j p + pderiv (R := ℝ) j q) := by rw [← map_add]
          _ = aeval (R := ℝ) g (pderiv (R := ℝ) j (p + q)) := by rw [(pderiv (R := ℝ) j).map_add]
    | mul_X pp i hpp =>
        calc
          (A (pp * X i)).derivative.eval t
              = (A pp * A (X i)).derivative.eval t := by rw [map_mul]
          _ = ((A pp).derivative * A (X i) + A pp * (A (X i)).derivative).eval t := by
                rw [Polynomial.derivative_mul]
          _ = (A pp).derivative.eval t * (A (X i)).eval t + (A pp).eval t * (A (X i)).derivative.eval t := by
                rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul]
          _ = aeval (R := ℝ) g (pderiv (R := ℝ) j pp) * aeval (R := ℝ) g (X i) +
                aeval (R := ℝ) g pp * aeval (R := ℝ) g (pderiv (R := ℝ) j (X i)) := by
                rw [hpp, hA_eval, hA_eval, hderivA_eval_X]
          _ = aeval (R := ℝ) g (pderiv (R := ℝ) j pp * X i + pp * pderiv (R := ℝ) j (X i)) := by
                rw [← map_mul, ← map_mul, ← map_add]
          _ = aeval (R := ℝ) g (pderiv (R := ℝ) j (pp * X i)) := by rw [pderiv_mul]
  change (A p).derivative.eval t = aeval (R := ℝ) g (pderiv (R := ℝ) j p)
  exact hderivA_eval p

/-- Maximal exponent of variable `j` among the monomials of `p`. -/
def degIn {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n) : ℕ :=
  p.support.sup (fun m : Fin n →₀ ℕ => m j)

/-- The top part of `p` with respect to the variable `j`. -/
def topInJ {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ m ∈ p.support.filter (fun m : Fin n →₀ ℕ => m j = degIn p j), monomial m (p.coeff m)

lemma sliceP_monomial {n : ℕ} (z : Fin n → ℂ) (j : Fin n) (c : ℝ) (m : Fin n →₀ ℕ) :
    sliceP z j (monomial m c) =
      Polynomial.C (c : ℂ) * ∏ i : Fin n, (if i = j then Polynomial.X else Polynomial.C (z i)) ^ (m i) := by
  classical
  unfold sliceP
  rw [MvPolynomial.aeval_monomial]
  congr 1
  exact Finsupp.prod_pow m (fun i => if i = j then Polynomial.X else Polynomial.C (z i))

/-- Coefficient of a monomial in the slice: only the degree-`m j` coefficient is hit. -/
lemma sliceP_monomial_coeff {n : ℕ} (z : Fin n → ℂ) (j : Fin n) (c : ℝ) (m : Fin n →₀ ℕ) (k : ℕ) :
    (sliceP z j (monomial m c)).coeff k =
      if m j = k then (c : ℂ) * ∏ i ∈ (Finset.univ.erase j : Finset (Fin n)), z i ^ (m i) else 0 := by
  classical
  rw [sliceP_monomial]
  let E : ℂ := ∏ i ∈ (Finset.univ.erase j : Finset (Fin n)), z i ^ (m i)
  have hmem : j ∈ (Finset.univ : Finset (Fin n)) := by simp
  have hsplit : (∏ i : Fin n, (if i = j then Polynomial.X else Polynomial.C (z i)) ^ (m i)) =
      Polynomial.X ^ (m j) * Polynomial.C E := by
    have hg : ((if j = j then Polynomial.X else Polynomial.C (z j)) ^ (m j)) = Polynomial.X ^ (m j) := by simp
    have hE : (∏ i ∈ (Finset.univ.erase j : Finset (Fin n)),
          (if i = j then Polynomial.X else Polynomial.C (z i)) ^ (m i)) = Polynomial.C E := by
      dsimp [E]
      calc
        (∏ i ∈ (Finset.univ.erase j : Finset (Fin n)),
            (if i = j then Polynomial.X else Polynomial.C (z i)) ^ (m i))
            = (∏ i ∈ (Finset.univ.erase j : Finset (Fin n)), (Polynomial.C (z i)) ^ (m i)) := by
              apply Finset.prod_congr rfl
              intro i hi
              have hne : i ≠ j := (Finset.mem_erase.mp hi).1
              simp [hne]
        _ = (∏ i ∈ (Finset.univ.erase j : Finset (Fin n)), Polynomial.C ((z i) ^ (m i))) := by
              apply Finset.prod_congr rfl
              intro i hi
              exact (map_pow (Polynomial.C : ℂ →+* Polynomial ℂ) (z i) (m i)).symm
        _ = Polynomial.C (∏ i ∈ (Finset.univ.erase j : Finset (Fin n)), (z i) ^ (m i)) := by
              rw [← map_prod (Polynomial.C : ℂ →+* Polynomial ℂ)]
    calc
      (∏ i : Fin n, (if i = j then Polynomial.X else Polynomial.C (z i)) ^ (m i))
          = ((if j = j then Polynomial.X else Polynomial.C (z j)) ^ (m j)) *
              ∏ i ∈ (Finset.univ.erase j : Finset (Fin n)),
                (if i = j then Polynomial.X else Polynomial.C (z i)) ^ (m i) := by
            rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
              (f := fun i => (if i = j then Polynomial.X else Polynomial.C (z i)) ^ (m i)) hmem]
      _ = Polynomial.X ^ (m j) * Polynomial.C E := by rw [hg, hE]
  have hmul : ∀ a : ℂ, Polynomial.C a * (Polynomial.X ^ (m j) * Polynomial.C E) =
      Polynomial.C (a * E) * Polynomial.X ^ (m j) := by
    intro a
    calc
      Polynomial.C a * (Polynomial.X ^ (m j) * Polynomial.C E)
          = Polynomial.C a * Polynomial.C E * Polynomial.X ^ (m j) := by ring
      _ = Polynomial.C (a * E) * Polynomial.X ^ (m j) := by
            rw [← map_mul (Polynomial.C : ℂ →+* Polynomial ℂ)]
  by_cases hjk : m j = k
  · rw [if_pos hjk]
    rw [← hjk]
    calc
      (Polynomial.C (c : ℂ) * ∏ i : Fin n, (if i = j then Polynomial.X else Polynomial.C (z i)) ^ (m i)).coeff (m j)
          = (Polynomial.C (c : ℂ) * (Polynomial.X ^ (m j) * Polynomial.C E)).coeff (m j) := by rw [hsplit]
      _ = ((Polynomial.C ((c : ℂ) * E) * Polynomial.X ^ (m j))).coeff (m j) := by rw [hmul]
      _ = (c : ℂ) * E := by
            rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
            simp
      _ = (c : ℂ) * ∏ i ∈ (Finset.univ.erase j : Finset (Fin n)), z i ^ (m i) := by rfl
  · rw [if_neg hjk]
    calc
      (Polynomial.C (c : ℂ) * ∏ i : Fin n, (if i = j then Polynomial.X else Polynomial.C (z i)) ^ (m i)).coeff k
          = (Polynomial.C (c : ℂ) * (Polynomial.X ^ (m j) * Polynomial.C E)).coeff k := by rw [hsplit]
      _ = ((Polynomial.C ((c : ℂ) * E) * Polynomial.X ^ (m j))).coeff k := by rw [hmul]
      _ = 0 := by
            rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
            have hkm : k ≠ m j := by exact fun h => hjk h.symm
            rw [if_neg hkm]
            simp

lemma aeval_topInJ_eq_sum {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (z : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) z (topInJ p j) =
      ∑ m ∈ p.support.filter (fun m : Fin n →₀ ℕ => m j = degIn p j),
        ((p.coeff m : ℝ) : ℂ) * ∏ i : Fin n, (z i) ^ (m i) := by
  classical
  unfold topInJ
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.aeval_monomial]
  congr 1
  exact Finsupp.prod_pow m (fun i => z i)

lemma prod_univ_eq_pow_erase {n : ℕ} (j : Fin n) (z : Fin n → ℂ) (m : Fin n →₀ ℕ) :
    (∏ i : Fin n, (z i) ^ (m i)) = (z j) ^ (m j) * ∏ i ∈ (Finset.univ.erase j : Finset (Fin n)), (z i) ^ (m i) := by
  classical
  have hmem : j ∈ (Finset.univ : Finset (Fin n)) := by simp
  rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => (z i) ^ (m i)) hmem]

lemma coeff_sliceP_eq_sum {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (z : Fin n → ℂ) :
    (sliceP z j p).coeff (degIn p j) =
      ∑ m ∈ p.support.filter (fun m : Fin n →₀ ℕ => m j = degIn p j),
        ((p.coeff m : ℝ) : ℂ) * ∏ i ∈ (Finset.univ.erase j : Finset (Fin n)), (z i) ^ (m i) := by
  classical
  calc
    (sliceP z j p).coeff (degIn p j)
        = (sliceP z j (∑ m ∈ p.support, monomial m (p.coeff m))).coeff (degIn p j) := by
            rw [p.support_sum_monomial_coeff]
    _ = (∑ m ∈ p.support, sliceP z j (monomial m (p.coeff m))).coeff (degIn p j) := by
            congr 1
            unfold sliceP
            rw [map_sum]
    _ = ∑ m ∈ p.support, (sliceP z j (monomial m (p.coeff m))).coeff (degIn p j) := by
            rw [Polynomial.finsetSum_coeff]
    _ = ∑ m ∈ p.support, (if m j = degIn p j then ((p.coeff m : ℝ) : ℂ) *
          ∏ i ∈ (Finset.univ.erase j : Finset (Fin n)), (z i) ^ (m i) else 0) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [sliceP_monomial_coeff]
    _ = ∑ m ∈ p.support.filter (fun m : Fin n →₀ ℕ => m j = degIn p j),
          ((p.coeff m : ℝ) : ℂ) * ∏ i ∈ (Finset.univ.erase j : Finset (Fin n)), (z i) ^ (m i) := by
            rw [Finset.sum_filter]

/-- Evaluating the top part at `z` gives `z_j^d` times the top slice coefficient. -/
lemma aeval_topInJ_eq_pow_mul_slice_coeff {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
    (z : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) z (topInJ p j) =
      (z j) ^ degIn p j * (sliceP z j p).coeff (degIn p j) := by
  classical
  rw [aeval_topInJ_eq_sum]
  calc
    (∑ m ∈ p.support.filter (fun m : Fin n →₀ ℕ => m j = degIn p j),
        ((p.coeff m : ℝ) : ℂ) * ∏ i : Fin n, (z i) ^ (m i))
        = (z j) ^ degIn p j *
            (∑ m ∈ p.support.filter (fun m : Fin n →₀ ℕ => m j = degIn p j),
              ((p.coeff m : ℝ) : ℂ) * ∏ i ∈ (Finset.univ.erase j : Finset (Fin n)), (z i) ^ (m i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          have hmj : m j = degIn p j := (Finset.mem_filter.mp hm).2
          rw [prod_univ_eq_pow_erase j z m, hmj]
          ring
    _ = (z j) ^ degIn p j * (sliceP z j p).coeff (degIn p j) := by
          rw [← coeff_sliceP_eq_sum]

lemma degIn_pos_of_pderiv_ne_zero {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
    (h : MvPolynomial.pderiv (R := ℝ) j p ≠ 0) : 1 ≤ degIn p j := by
  classical
  obtain ⟨m0, hm0⟩ := MvPolynomial.exists_coeff_ne_zero h
  let e : Fin n →₀ ℕ := Finsupp.single j (1 : ℕ)
  have hcp' : coeff m0 (pderiv (R := ℝ) j p) = coeff (m0 + e) p * ((m0 j : ℝ) + 1) := by
    simpa [e] using (MvPolynomial.coeff_pderiv p m0)
  have hprod : coeff (m0 + e) p * ((m0 j : ℝ) + 1) ≠ 0 := by
    rwa [hcp'] at hm0
  have hc : coeff (m0 + e) p ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hmem : m0 + e ∈ p.support := (MvPolynomial.mem_support_iff).mpr hc
  have hle := Finset.le_sup (s := p.support) (f := fun m : Fin n →₀ ℕ => m j) hmem
  have hle' : m0 j + 1 ≤ p.support.sup (fun m : Fin n →₀ ℕ => m j) := by
    simpa [e, Finsupp.add_apply] using hle
  unfold degIn
  omega

lemma topInJ_ne_zero_of_ne_zero {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
    (hp : p ≠ 0) : topInJ p j ≠ 0 := by
  classical
  have hsupp : p.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hp
    exact (MvPolynomial.support_eq_empty).mp hempty
  obtain ⟨m0, hm0, hdeq⟩ := Finset.exists_mem_eq_sup p.support hsupp
    (fun m : Fin n →₀ ℕ => m j)
  have hdeq' : m0 j = degIn p j := hdeq.symm
  have hmfilter : m0 ∈ p.support.filter (fun m : Fin n →₀ ℕ => m j = degIn p j) :=
    Finset.mem_filter.mpr ⟨hm0, hdeq'⟩
  have hc0 : p.coeff m0 ≠ 0 := (MvPolynomial.mem_support_iff).mp hm0
  have hcT : coeff m0 (topInJ p j) = p.coeff m0 := by
    unfold topInJ
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single m0]
    · rw [MvPolynomial.coeff_monomial]
      simp
    · intro b hb hbne
      rw [MvPolynomial.coeff_monomial]
      simp [hbne]
    · intro hnot
      exact False.elim (hnot hmfilter)
  intro hT
  have hc0' : coeff m0 (topInJ p j) = 0 := by rw [hT]; simp
  exact hc0 (by simpa [hcT] using hc0')

/-- The top part in variable `j` of a stable polynomial is stable (zero or nonvanishing). -/
lemma topInJ_stable_of_stable {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
    (hstab : p = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    topInJ p j = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) (topInJ p j) ≠ 0 := by
  classical
  have h := top_in_j_stable_of_stable p j hstab
  dsimp [topInJ, degIn] at h ⊢
  exact h

lemma coeff_eq_zero_of_derivative_eq_zero {R : Type*} [Semiring R] [IsAddTorsionFree R]
    {P : Polynomial R} {k : ℕ} (hk : 0 < k) (h : P.derivative = 0) : P.coeff k = 0 := by
  have hn : P.natDegree = 0 := (Polynomial.derivative_eq_zero (R := R)).mp h
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hn]; exact hk)

lemma UHP_complex_ne_zero (z : UpperHalfPlane) : (z : ℂ) ≠ 0 := by
  intro hz
  have him : ((z : ℂ).im) = 0 := by simpa using congrArg Complex.im hz
  have hpos : 0 < ((z : ℂ).im) := z.im_pos
  linarith

lemma eval_ne_zero_of_coeff {R : Type*} [Semiring R] [Nontrivial R] (P : Polynomial R)
    (a : R) (h : P.eval a ≠ 0) : P ≠ 0 := by
  intro h0
  rw [h0, Polynomial.eval_zero] at h
  exact h rfl

/-- Partial derivatives preserve stability for polynomials with nonnegative coefficients:
if `p` is stable on the open upper half plane (or zero), then so is `∂_j p` (or it is zero). -/
theorem pderiv_stable_of_stable_nonneg (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m)
    (hstab : p = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    MvPolynomial.pderiv (R := ℝ) j p = 0 ∨
      ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ))
          (MvPolynomial.pderiv (R := ℝ) j p) ≠ 0 := by
  classical
  rcases hstab with hp0 | hpstab
  · left
    rw [hp0]
    simp [MvPolynomial.pderiv]
  · by_cases hpd : MvPolynomial.pderiv (R := ℝ) j p = 0
    · left
      exact hpd
    · right
      intro z
      let zc : Fin n → ℂ := fun i => ((z i : UpperHalfPlane) : ℂ)
      have hp0' : p ≠ 0 := by
        intro hp0
        apply hpd
        rw [hp0]
        simp [MvPolynomial.pderiv]
      let S : Polynomial ℂ := sliceP zc j p
      have hSstab : ∀ u : UpperHalfPlane, S.eval (u : ℂ) ≠ 0 := by
        intro u
        dsimp [S]
        rw [sliceP_eval]
        let z' : Fin n → UpperHalfPlane := fun i => if i = j then u else z i
        have hval : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => (z' i : ℂ)) p ≠ 0 :=
          hpstab z'
        have hfun : (fun i : Fin n => (if i = j then u else z i : UpperHalfPlane) : Fin n → ℂ) =
            (fun i : Fin n => if i = j then (u : ℂ) else zc i) := by
          funext i
          by_cases hij : i = j
          · simp [hij, zc]
          · simp [hij, zc]
        rw [← hfun]
        exact hval
      have hS0 : S ≠ 0 := by
        dsimp [S]
        refine eval_ne_zero_of_coeff (sliceP zc j p) (zc j) ?_
        have hS0' : (sliceP zc j p).eval (zc j) ≠ 0 := by
          rw [sliceP_eval]
          have hfun : (fun i : Fin n => if i = j then zc j else zc i) = zc := by
            funext i
            by_cases hij : i = j
            · simp [zc, hij]
            · simp [zc, hij]
          rw [hfun]
          exact hpstab z
        exact hS0'
      have hd : 1 ≤ degIn p j := degIn_pos_of_pderiv_ne_zero p j hpd
      have hTst := topInJ_stable_of_stable p j (Or.inr hpstab)
      have hT0 : topInJ p j ≠ 0 := topInJ_ne_zero_of_ne_zero p j hp0'
      have hTz : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => (z i : ℂ)) (topInJ p j) ≠ 0 :=
        (hTst.resolve_left hT0) z
      have hrel := aeval_topInJ_eq_pow_mul_slice_coeff p j zc
      have hzc_ne : zc j ≠ 0 := UHP_complex_ne_zero (z j)
      have hcoeff_ne : S.coeff (degIn p j) ≠ 0 := by
        dsimp [S]
        by_contra hc
        have hrel' : MvPolynomial.aeval (R := ℝ) zc (topInJ p j) =
            (zc j) ^ degIn p j * (sliceP zc j p).coeff (degIn p j) := hrel
        rw [hc, mul_zero] at hrel'
        have hTz' : MvPolynomial.aeval (R := ℝ) zc (topInJ p j) ≠ 0 := by
          change MvPolynomial.aeval (R := ℝ) (fun i : Fin n => (z i : ℂ)) (topInJ p j) ≠ 0
          exact hTz
        exact hTz' hrel'
      have hderiv : S.derivative = 0 ∨ ∀ u : UpperHalfPlane, S.derivative.eval (u : ℂ) ≠ 0 :=
        Commons.Analysis.Complex.Polynomial.deriv_stable_of_stable S hS0 hSstab
      have hderiv_ne : S.derivative ≠ 0 := by
        intro hder0
        have hc0 : S.coeff (degIn p j) = 0 :=
          coeff_eq_zero_of_derivative_eq_zero (R := ℂ) (P := S) hd hder0
        exact hcoeff_ne hc0
      have hderiv_ev : S.derivative.eval (zc j) ≠ 0 :=
        (hderiv.resolve_left hderiv_ne) (z j)
      by_contra h0
      have hfun : (fun i : Fin n => if i = j then zc j else zc i) =
          (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) := by
        funext i
        by_cases hij : i = j
        · simp [zc, hij]
        · simp [zc, hij]
      have hmain' : S.derivative.eval (zc j) =
          MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ))
            (MvPolynomial.pderiv (R := ℝ) j p) := by
        dsimp [S]
        rw [sliceP_deriv_eval, hfun]
      exact hderiv_ev (by simpa [hmain'] using h0)

end Commons.Analysis.MvPolynomial