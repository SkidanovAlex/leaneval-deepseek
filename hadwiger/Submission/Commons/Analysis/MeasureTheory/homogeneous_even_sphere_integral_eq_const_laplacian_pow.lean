import Mathlib
import Submission.Commons.Algebra.MvPolynomial.lapIter_evenMonomial_eval_zero
import Submission.Commons.Algebra.MvPolynomial.lapIter_monomial_eval_zero_of_odd
import Submission.Commons.Analysis.MeasureTheory.sphere_evenMonomial_integral_mul_dblFact
import Submission.Commons.Analysis.MeasureTheory.sphere_monomial_integral_zero_of_odd

noncomputable section
open scoped BigOperators Classical
open Set Function MeasureTheory Metric
open MvPolynomial

namespace Commons.Analysis.MeasureTheory

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev S (n : ℕ) := Metric.sphere (0 : E n) 1

-- Laplacian as a bundled ℝ-linear map
private noncomputable def lapLinear (n : ℕ) : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
  Finset.univ.sum (fun i : Fin n => (pderiv (R := ℝ) i : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ).comp
                (pderiv (R := ℝ) i : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ))

private lemma lapLinear_apply (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    lapLinear n Q = Finset.univ.sum (fun i : Fin n => pderiv i (pderiv i Q)) := by
  simp [lapLinear]

private lemma lapOp_eq_lapLinear (n : ℕ) :
    (fun Q : MvPolynomial (Fin n) ℝ => Finset.univ.sum (fun i : Fin n => pderiv i (pderiv i Q))) = (lapLinear n).toFun := by
  funext Q
  change Finset.univ.sum (fun i : Fin n => pderiv i (pderiv i Q)) = (lapLinear n) Q
  rw [lapLinear_apply]

private lemma lapIter_eq_lapLinearIter (n : ℕ) (m : ℕ) :
    ((fun Q : MvPolynomial (Fin n) ℝ => Finset.univ.sum (fun i : Fin n => pderiv i (pderiv i Q)))^[m])
      = (lapLinear n).toFun^[m] := by
  rw [lapOp_eq_lapLinear]

private lemma lapIter_sum_smul (n : ℕ) (m : ℕ) {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (g : ι → MvPolynomial (Fin n) ℝ) :
    ((lapLinear n : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ) ^[m])
        (∑ i ∈ s, a i • g i) =
      ∑ i ∈ s, a i • (((lapLinear n : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ) ^[m]) (g i)) := by
  classical
  let f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ := lapLinear n
  change (f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)^[m] (∑ i ∈ s, a i • g i) =
    ∑ i ∈ s, a i • ((f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)^[m]) (g i)
  have hsmul : ∀ (m : ℕ) (a : ℝ) (Q : MvPolynomial (Fin n) ℝ),
      (f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)^[m] (a • Q) =
        a • (f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)^[m] Q := by
    intro m a Q
    induction m with
    | zero => simp
    | succ m ih =>
        simp only [Function.iterate_succ_apply']
        rw [ih]
        rw [map_smul]
  have hsum : ∀ (m : ℕ) (h : ι → MvPolynomial (Fin n) ℝ),
      (f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)^[m] (∑ i ∈ s, h i) =
        ∑ i ∈ s, (f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)^[m] (h i) := by
    intro m h
    induction m with
    | zero => simp
    | succ m ih =>
        simp only [Function.iterate_succ_apply'] at *
        rw [ih]
        rw [map_sum]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  exact hsmul m (a i) (g i)

-- eval of a monomial at θ = product of powers
private lemma eval_monomial_prod (n : ℕ) (d : Fin n →₀ ℕ) (θ : E n) :
    MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial d (1 : ℝ))
      = Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (d i)) := by
  rw [MvPolynomial.eval_monomial]
  have hp : d.prod (fun i e => ((θ : E n) i) ^ e) =
      Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ d i) :=
    Finsupp.prod_fintype d (fun i e => ((θ : E n) i) ^ e) (by intro i; simp)
  rw [hp]
  simp

-- eval of a scalar monomial at θ
private lemma eval_monomial_scalar_prod (n : ℕ) (d : Fin n →₀ ℕ) (a : ℝ) (θ : E n) :
    MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial d a)
      = a * Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (d i)) := by
  rw [MvPolynomial.eval_monomial]
  have hp : d.prod (fun i e => ((θ : E n) i) ^ e) =
      Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ d i) :=
    Finsupp.prod_fintype d (fun i e => ((θ : E n) i) ^ e) (by intro i; simp)
  rw [hp]

-- eval at 0 = coeff 0
private lemma eval_zero_coeff (n : ℕ) (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) P = P.coeff 0 := by
  simp [MvPolynomial.constantCoeff_eq]

-- homogeneity gives weight of each monomial
private lemma mem_homogeneous_weight {n : ℕ} {m : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m)) :
    ∀ d ∈ P.support, (Finset.univ.sum (fun i : Fin n => d i)) = 2 * m := by
  intro d hd
  have hc : P.coeff d ≠ 0 := by simpa using hd
  have hhom : MvPolynomial.IsHomogeneous P (2 * m) :=
    (MvPolynomial.mem_homogeneousSubmodule (n := 2 * m) (p := P)).mp hP
  have hdeg : d.degree = 2 * m := by
    by_contra hd'
    have hz : P.coeff d = 0 := MvPolynomial.IsHomogeneous.coeff_eq_zero hhom hd'
    exact hc hz
  simpa [Finsupp.degree_eq_sum] using hdeg

-- even exponent vector and its half
private def halfExp {n : ℕ} (e : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  e.mapRange (fun k => k / 2) (by norm_num)

private lemma halfExp_apply {n : ℕ} (e : Fin n →₀ ℕ) (i : Fin n) : (halfExp e) i = e i / 2 := by
  simp [halfExp, Finsupp.mapRange_apply]

private lemma even_two_mul_half {n : ℕ} (e : Fin n →₀ ℕ)
    (he : ∀ i : Fin n, Even (e i)) (i : Fin n) :
    e i = 2 * (halfExp e i) := by
  rw [halfExp_apply]
  have hdvd : 2 ∣ e i := (even_iff_two_dvd.mp (he i))
  have hdiv : e i / 2 * 2 = e i := Nat.div_mul_cancel hdvd
  calc
    e i = e i / 2 * 2 := hdiv.symm
    _ = 2 * (e i / 2) := by rw [mul_comm]

private lemma weight_half {n : ℕ} {m : ℕ} (e : Fin n →₀ ℕ)
    (he : ∀ i : Fin n, Even (e i))
    (hw : (Finset.univ.sum (fun i : Fin n => e i)) = 2 * m) :
    (Finset.univ.sum (fun i : Fin n => halfExp e i)) = m := by
  have hsum : (Finset.univ.sum (fun i : Fin n => e i)) =
      2 * (Finset.univ.sum (fun i : Fin n => halfExp e i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact even_two_mul_half e he i
  omega

-- Odd hypothesis from not-all-even
private lemma odd_exists_of_not_all_even {n : ℕ} (e : Fin n →₀ ℕ)
    (h : ¬ ∀ i : Fin n, Even (e i)) : ∃ i : Fin n, Odd (e i) := by
  by_contra hc
  apply h
  intro i
  have hno : ¬ Odd (e i) := by intro ho; exact hc ⟨i, ho⟩
  exact Nat.not_odd_iff_even.mp hno

-- continuity of coordinate & monomial product on sphere
private lemma continuous_coord (n : ℕ) (i : Fin n) : Continuous (fun θ : S n => ((θ : E n) i)) := by
  dsimp [S, E]
  fun_prop

private lemma continuous_monomialProd (n : ℕ) (d : Fin n →₀ ℕ) :
    Continuous (fun θ : S n => Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (d i))) := by
  classical
  fun_prop

-- integrability of a continuous function on the sphere w.r.t. toSphere (finite measure, compact)
private lemma integrable_of_continuous_sphere (n : ℕ) (f : S n → ℝ) (hf : Continuous f) :
    MeasureTheory.Integrable f (MeasureTheory.volume.toSphere : Measure (S n)) := by
  classical
  let μ : Measure (S n) := MeasureTheory.volume.toSphere
  change MeasureTheory.Integrable f μ
  have hfin : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  letI : IsFiniteMeasure μ := hfin
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ θ : S n, ‖f θ‖ ≤ B := by
    have hb : Bornology.IsBounded ((fun θ : S n => ‖f θ‖) '' (univ : Set (S n))) :=
      (isCompact_univ.image hf.norm).isBounded
    obtain ⟨C, hC⟩ := hb.exists_norm_le
    refine ⟨C, ?_⟩
    intro θ
    simpa using hC ‖f θ‖ ⟨θ, trivial, rfl⟩
  exact Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all μ hB)

-- integral over sphere of a finite ℝ-linear combination of functions
private lemma sphere_integral_finset_sum_smul (n : ℕ) {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (f : ι → S n → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    (∫ θ : S n, (∑ i ∈ s, a i * f i θ) ∂MeasureTheory.volume.toSphere) =
      ∑ i ∈ s, a i * (∫ θ : S n, f i θ ∂MeasureTheory.volume.toSphere) := by
  classical
  let g : ι → S n → ℝ := fun i θ => a i * f i θ
  have hg : ∀ i ∈ s, Integrable (g i) (MeasureTheory.volume.toSphere : Measure (S n)) := by
    intro i hi
    exact (integrable_of_continuous_sphere n (f i) (hf i hi)).const_mul (a i)
  rw [integral_finsetSum (s := s) (f := g) hg]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul]

-- monomial polynomial = univ product of X powers
private lemma monomial_eq_prod_X (n : ℕ) (e : Fin n →₀ ℕ) :
    monomial e (1 : ℝ) = Finset.univ.prod (fun i : Fin n => (X i : MvPolynomial (Fin n) ℝ) ^ e i) := by
  classical
  rw [MvPolynomial.monomial_eq]
  simp only [map_one, one_mul]
  have hp : e.prod (fun i e => (X i : MvPolynomial (Fin n) ℝ) ^ e) =
      Finset.univ.prod (fun i : Fin n => (X i : MvPolynomial (Fin n) ℝ) ^ e i) :=
    Finsupp.prod_fintype e (fun i e => (X i : MvPolynomial (Fin n) ℝ) ^ e) (by intro i; simp)
  exact hp

-- double factorial product form
private def dfProd (n : ℕ) (β : Fin n →₀ ℕ) : ℝ :=
  Finset.univ.prod (fun i : Fin n => ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ))

-- per-monomial Pizzetti: sphere integral of each monomial ∝ Laplacian power at 0
private lemma monomial_pizzetti {n : ℕ} {m : ℕ} (hn : 0 < n) (C c : ℝ)
    (hC : ∀ (β : Fin n →₀ ℕ), (Finset.univ.sum (fun i : Fin n => β i)) = m →
      (∫ θ : S n, Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (2 * β i))
          ∂MeasureTheory.volume.toSphere) = C * dfProd n β)
    (hc : c = C / ((Nat.factorial m : ℝ) * (2 : ℝ) ^ m)) :
    ∀ (e : Fin n →₀ ℕ),
      (Finset.univ.sum (fun i : Fin n => e i)) = 2 * m →
        (∫ θ : S n, MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial e (1 : ℝ))
            ∂MeasureTheory.volume.toSphere) =
          c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
              (monomial e (1 : ℝ))) := by
  classical
  intro e hwe
  by_cases hodd : ∃ i : Fin n, Odd (e i)
  · have hL : (∫ θ : S n, MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial e (1 : ℝ))
          ∂MeasureTheory.volume.toSphere) = 0 := by
      have hfun : (fun θ : S n => MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial e (1 : ℝ)))
          = fun θ : S n => Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ e i) := by
        funext θ
        exact eval_monomial_prod n e θ
      rw [hfun]
      exact sphere_monomial_integral_zero_of_odd (n := n) hn e hodd
    have hR : MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
              (monomial e (1 : ℝ))) = 0 :=
      Commons.Algebra.MvPolynomial.lapIter_monomial_eval_zero_of_odd (n := n) (m := m) e hwe hodd
    rw [hL, hR]
    ring
  · have heven : ∀ i : Fin n, Even (e i) := by
      intro i
      exact Nat.not_odd_iff_even.mp (by intro ho; exact hodd ⟨i, ho⟩)
    let β : Fin n →₀ ℕ := halfExp e
    have hwβ : (Finset.univ.sum (fun i : Fin n => β i)) = m := by
      dsimp [β]
      exact weight_half e heven hwe
    have hdbl : ∀ i : Fin n, e i = 2 * β i := by
      intro i
      dsimp [β]
      exact even_two_mul_half e heven i
    -- LHS: eval monomial = product; e_i = 2 β_i
    have hL : (∫ θ : S n, MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial e (1 : ℝ))
          ∂MeasureTheory.volume.toSphere) = C * dfProd n β := by
      have hfun : (fun θ : S n => MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial e (1 : ℝ)))
          = fun θ : S n => Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ e i) := by
        funext θ
        exact eval_monomial_prod n e θ
      rw [hfun]
      have hprod : (fun θ : S n => Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ e i))
          = fun θ : S n => Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (2 * β i)) := by
        funext θ
        apply Finset.prod_congr rfl
        intro i hi
        rw [hdbl i]
      rw [hprod]
      exact hC β hwβ
    -- RHS: monomial = product of X powers
    have hR : MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
              (monomial e (1 : ℝ))) = (Nat.factorial m : ℝ) * (2 : ℝ) ^ m * dfProd n β := by
      have hmon : monomial e (1 : ℝ) = Finset.univ.prod (fun i : Fin n => (X i : MvPolynomial (Fin n) ℝ) ^ e i) :=
        monomial_eq_prod_X n e
      rw [hmon]
      have hprod : (Finset.univ.prod (fun i : Fin n => (X i : MvPolynomial (Fin n) ℝ) ^ e i))
          = Finset.univ.prod (fun i : Fin n => (X i : MvPolynomial (Fin n) ℝ) ^ (2 * β i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hdbl i]
      rw [hprod]
      change MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
              (Finset.univ.prod (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ (2 * β i))))
            = (Nat.factorial m : ℝ) * (2 : ℝ) ^ m * dfProd n β
      exact Commons.Algebra.MvPolynomial.lapIter_evenMonomial_eval_zero (n := n) (m := m) β hwβ
    rw [hL, hR, hc]
    have hne : (Nat.factorial m : ℝ) * (2 : ℝ) ^ m ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast (Nat.factorial_ne_zero m)) (pow_ne_zero m (by norm_num))
    field_simp [hne]
-- push (lap^[m]) over a sum of scalar multiples, then evaluate at 0
private lemma eval0_iter_sum_smul (n : ℕ) (m : ℕ) {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (Q : ι → MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
      ((fun Q : MvPolynomial (Fin n) ℝ =>
          Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
        (∑ i ∈ s, a i • Q i))
    = ∑ i ∈ s, a i * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
        ((fun Q : MvPolynomial (Fin n) ℝ =>
            Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
          (Q i)) := by
  classical
  rw [lapIter_eq_lapLinearIter n m]
  let f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ := lapLinear n
  change MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
      ((f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)^[m] (∑ i ∈ s, a i • Q i))
    = ∑ i ∈ s, a i * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
        ((f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)^[m] (Q i))
  have hsmul : ∀ (m : ℕ) (a : ℝ) (Q : MvPolynomial (Fin n) ℝ),
      (f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)^[m] (a • Q) =
        a • (f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)^[m] Q := by
    intro m a Q
    induction m with
    | zero => simp
    | succ m ih =>
        simp only [Function.iterate_succ_apply']
        rw [ih]
        rw [map_smul]
  have hsum : ∀ (m : ℕ) (h : ι → MvPolynomial (Fin n) ℝ),
      (f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)^[m] (∑ i ∈ s, h i) =
        ∑ i ∈ s, (f : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)^[m] (h i) := by
    intro m h
    induction m with
    | zero => simp
    | succ m ih =>
        simp only [Function.iterate_succ_apply'] at *
        rw [ih]
        rw [map_sum]
  rw [hsum]
  simp [hsmul]

theorem homogeneous_even_sphere_integral_eq_const_laplacian_pow
    {n : ℕ} {m : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, ∀ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m) →
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P
          ∂MeasureTheory.volume.toSphere) =
          c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q))^[m] P) := by
  classical
  obtain ⟨C, hC⟩ := sphere_evenMonomial_integral_mul_dblFact (n := n) (m := m) hn
  let c : ℝ := C / ((Nat.factorial m : ℝ) * (2 : ℝ) ^ m)
  refine ⟨c, ?_⟩
  intro P hP
  have hasP := MvPolynomial.as_sum P
  have hmono : ∀ (e : Fin n →₀ ℕ),
      (Finset.univ.sum (fun i : Fin n => e i)) = 2 * m →
        (∫ θ : S n, MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial e (1 : ℝ))
            ∂MeasureTheory.volume.toSphere)
          = c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
              (monomial e (1 : ℝ))) := by
    intro e hwe
    exact monomial_pizzetti (n := n) (m := m) hn C c (fun β hwβ => hC β hwβ) (by simp [c]) e hwe
  have hterm : ∀ d ∈ P.support,
      (P.coeff d) * (∫ θ : S n, Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (d i))
          ∂MeasureTheory.volume.toSphere)
        = (P.coeff d) * (c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
              (monomial d (1 : ℝ)))) := by
    intro d hd
    have hwd : (Finset.univ.sum (fun i : Fin n => d i)) = 2 * m := mem_homogeneous_weight P hP d hd
    have hconv : (∫ θ : S n, MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial d (1 : ℝ))
          ∂MeasureTheory.volume.toSphere)
        = (∫ θ : S n, Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (d i))
          ∂MeasureTheory.volume.toSphere) := by
      rw [show (fun θ : S n => MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial d (1 : ℝ)))
            = fun θ : S n => Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (d i)) from by
              funext θ
              exact eval_monomial_prod n d θ]
    rw [hconv.symm, hmono d hwd]
  have hLHS : (∫ θ : S n, MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P
          ∂MeasureTheory.volume.toSphere)
      = ∑ d ∈ P.support, (P.coeff d) * (∫ θ : S n, Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (d i))
          ∂MeasureTheory.volume.toSphere) := by
    have h1 : (fun θ : S n => MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P) =
        fun θ : S n => MvPolynomial.eval (fun i : Fin n => (θ : E n) i)
            (∑ d ∈ P.support, monomial d (P.coeff d)) := by
      funext θ
      exact congrArg (fun X : MvPolynomial (Fin n) ℝ =>
        MvPolynomial.eval (fun i : Fin n => (θ : E n) i) X) hasP
    have h2 : (fun θ : S n => MvPolynomial.eval (fun i : Fin n => (θ : E n) i)
            (∑ d ∈ P.support, monomial d (P.coeff d))) =
        fun θ : S n => (∑ d ∈ P.support,
            MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial d (P.coeff d))) := by
      funext θ
      rw [MvPolynomial.eval_sum]
    have h3 : (fun θ : S n => (∑ d ∈ P.support,
            MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial d (P.coeff d)))) =
        fun θ : S n => (∑ d ∈ P.support, (P.coeff d) *
            Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (d i))) := by
      funext θ
      apply Finset.sum_congr rfl
      intro d hd
      rw [eval_monomial_scalar_prod n d (P.coeff d) θ]
    calc
      (∫ θ : S n, MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P
          ∂MeasureTheory.volume.toSphere)
          = ∫ θ : S n, MvPolynomial.eval (fun i : Fin n => (θ : E n) i)
              (∑ d ∈ P.support, monomial d (P.coeff d)) ∂MeasureTheory.volume.toSphere := by
              rw [h1]
      _ = ∫ θ : S n, (∑ d ∈ P.support,
            MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (monomial d (P.coeff d)))
          ∂MeasureTheory.volume.toSphere := by
              rw [h2]
      _ = ∫ θ : S n, (∑ d ∈ P.support, (P.coeff d) *
            Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (d i)))
          ∂MeasureTheory.volume.toSphere := by
              rw [h3]
      _ = ∑ d ∈ P.support, (P.coeff d) * (∫ θ : S n,
            Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (d i))
          ∂MeasureTheory.volume.toSphere) := by
              exact sphere_integral_finset_sum_smul n P.support (fun d => P.coeff d)
                (fun d θ => Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (d i)))
                (by intro d hd; exact continuous_monomialProd n d)
  have hRHS : c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m] P)
      = ∑ d ∈ P.support, (P.coeff d) * (c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
              (monomial d (1 : ℝ)))) := by
    have hmon_smul : ∀ d : Fin n →₀ ℕ, monomial d (P.coeff d) = (P.coeff d) • monomial d (1 : ℝ) := by
      intro d
      rw [← MvPolynomial.C_mul']
      rw [MvPolynomial.C_mul_monomial]
      simp
    have hRHScore : MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
              (∑ d ∈ P.support, monomial d (P.coeff d)))
        = ∑ d ∈ P.support, (P.coeff d) * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
              (monomial d (1 : ℝ))) := by
      have heqsum : (∑ d ∈ P.support, monomial d (P.coeff d)) =
          (∑ d ∈ P.support, (P.coeff d) • monomial d (1 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hmon_smul d
      rw [heqsum]
      exact eval0_iter_sum_smul n m P.support (fun d => P.coeff d) (fun d => monomial d (1 : ℝ))
    calc
      c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m] P)
          = c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
              (∑ d ∈ P.support, monomial d (P.coeff d))) := by
              exact congrArg (fun X : MvPolynomial (Fin n) ℝ =>
                c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
                  ((fun Q : MvPolynomial (Fin n) ℝ =>
                      Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m] X)) hasP
      _ = c * (∑ d ∈ P.support, (P.coeff d) * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
              (monomial d (1 : ℝ)))) := by
              rw [hRHScore]
      _ = ∑ d ∈ P.support, (P.coeff d) * (c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
            ((fun Q : MvPolynomial (Fin n) ℝ =>
                Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
              (monomial d (1 : ℝ)))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro d hd
              ring
  calc
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P
      ∂MeasureTheory.volume.toSphere)
        = (∫ θ : S n, MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P
          ∂MeasureTheory.volume.toSphere) := rfl
    _ = ∑ d ∈ P.support, (P.coeff d) * (∫ θ : S n,
          Finset.univ.prod (fun i : Fin n => ((θ : E n) i) ^ (d i))
          ∂MeasureTheory.volume.toSphere) := hLHS
    _ = ∑ d ∈ P.support, (P.coeff d) * (c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
          ((fun Q : MvPolynomial (Fin n) ℝ =>
              Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
            (monomial d (1 : ℝ)))) := by
            apply Finset.sum_congr rfl
            intro d hd
            exact hterm d hd
    _ = c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
          ((fun Q : MvPolynomial (Fin n) ℝ =>
              Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m] P) := hRHS.symm
    _ = c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
          ((fun Q : MvPolynomial (Fin n) ℝ =>
              ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q))^[m] P) := rfl

end Commons.Analysis.MeasureTheory
