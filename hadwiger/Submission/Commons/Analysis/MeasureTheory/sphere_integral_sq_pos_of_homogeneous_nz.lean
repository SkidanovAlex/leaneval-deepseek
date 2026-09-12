import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Submission.Commons.Algebra.MvPolynomial.eval_eq_sum_expanded
import Submission.Commons.Analysis.MeasureTheory.sphere_polynomial_uniform_dense

noncomputable section
open scoped BigOperators
open Set Function MeasureTheory Metric
open MvPolynomial

namespace Commons.Analysis.MeasureTheory

private abbrev Eu (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev Sph (n : ℕ) := Metric.sphere (0 : Eu n) 1

/-- Scaling a homogeneous polynomial's variables multiplies its value by `a ^ k`. -/
private lemma homogeneous_eval_smul {n k : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.IsHomogeneous k) (a : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval (fun i : Fin n => a * x i) P = a ^ k * MvPolynomial.eval x P := by
  classical
  rw [MvPolynomial.eval_eq' (fun i : Fin n => a * x i) P, MvPolynomial.eval_eq' x P]
  calc
    (∑ m ∈ P.support, P.coeff m * (∏ i : Fin n, (a * x i) ^ (m i)))
        = ∑ m ∈ P.support, P.coeff m * (a ^ k * (∏ i : Fin n, (x i) ^ (m i))) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hw : (Finset.univ.sum (fun i : Fin n => m i)) = k := by
            have hdeg : m.degree = k := by
              by_contra hd'
              have hz : P.coeff m = 0 := MvPolynomial.IsHomogeneous.coeff_eq_zero hP hd'
              exact (by simpa using hm : P.coeff m ≠ 0) hz
            simpa [Finsupp.degree_eq_sum] using hdeg
          congr 1
          calc
            (∏ i : Fin n, (a * x i) ^ (m i)) = (∏ i : Fin n, (a ^ (m i)) * (x i) ^ (m i)) := by
                  apply Finset.prod_congr rfl
                  intro i hi
                  rw [mul_pow]
            _ = (∏ i : Fin n, a ^ (m i)) * (∏ i : Fin n, (x i) ^ (m i)) := by
                  rw [Finset.prod_mul_distrib]
            _ = a ^ (Finset.univ.sum (fun i : Fin n => m i)) * (∏ i : Fin n, (x i) ^ (m i)) := by
                  rw [Finset.prod_pow_eq_pow_sum]
            _ = a ^ k * (∏ i : Fin n, (x i) ^ (m i)) := by rw [hw]
    _ = a ^ k * (∑ m ∈ P.support, P.coeff m * (∏ i : Fin n, (x i) ^ (m i))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          ring

/-- An exponent vector of total degree zero is zero. -/
private lemma degree_zero_eq_zero {n : ℕ} (d : Fin n →₀ ℕ) (hdeg : d.degree = 0) : d = 0 := by
  apply Finsupp.ext
  intro i
  have hsum : (Finset.univ.sum (fun i : Fin n => d i)) = 0 := by
    simpa [Finsupp.degree_eq_sum] using hdeg
  have hle : d i ≤ Finset.univ.sum (fun i : Fin n => d i) := by
    exact Finset.single_le_sum (fun x hx => Nat.zero_le (d x)) (Finset.mem_univ i)
  have hle' : d i ≤ 0 := by simpa [hsum] using hle
  exact Nat.eq_zero_of_le_zero hle'

/-- A polynomial homogeneous of degree zero is constant. -/
private lemma homogeneous_zero_eq_C {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (hP : P.IsHomogeneous 0) :
    P = MvPolynomial.C (P.coeff 0) := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd0 : d = 0
  · subst d
    simp
  · have hdeg : d.degree ≠ 0 := by
      intro hd
      exact hd0 (degree_zero_eq_zero d hd)
    have hz : P.coeff d = 0 := MvPolynomial.IsHomogeneous.coeff_eq_zero hP hdeg
    have hC : (MvPolynomial.C (P.coeff 0)).coeff d = 0 :=
      MvPolynomial.coeff_C_of_ne_zero hd0 (P.coeff 0)
    rw [hz, hC]

/-- Evaluating a degree-`k ≥ 1` homogeneous polynomial at zero vanishes. -/
private lemma coeff0_zero_of_degree_pos {n k : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.IsHomogeneous k) (hk : k ≠ 0) :
    P.coeff 0 = 0 := by
  apply MvPolynomial.IsHomogeneous.coeff_eq_zero hP
  intro hdeg0
  apply hk
  simpa using hdeg0.symm

/-- Evaluating at the zero vector picks out the constant coefficient. -/
private lemma eval_zero_coeff {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) P = P.coeff 0 := by
  simp [MvPolynomial.constantCoeff_eq]

/-- The unit sphere in `ℝⁿ` is nonempty whenever `n` is. -/
private lemma sphere_nonempty (n : ℕ) [Nonempty (Fin n)] : Nonempty (Sph n) := by
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›
  refine ⟨⟨EuclideanSpace.single i (1 : ℝ), ?_⟩⟩
  rw [mem_sphere_zero_iff_norm]
  simp

/-- A nonzero homogeneous polynomial is not identically zero on the unit sphere. -/
private lemma exists_sphere_eval_ne_zero_of_homogeneous {n k : ℕ} [Nonempty (Fin n)]
    (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) (hP0 : P ≠ 0) :
    ∃ θ : Sph n, MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P ≠ 0 := by
  classical
  have hhom : P.IsHomogeneous k := (MvPolynomial.mem_homogeneousSubmodule (n := k) (p := P)).mp hP
  by_cases hk : k = 0
  · -- a degree-zero homogeneous polynomial is a nonzero constant, so it is
    -- nonzero at every point of the (nonempty) sphere
    have hhom0 : P.IsHomogeneous 0 := by
      simpa [hk] using hhom
    have hC : P = MvPolynomial.C (P.coeff 0) := homogeneous_zero_eq_C P hhom0
    have hc : P.coeff 0 ≠ 0 := by
      intro hz
      apply hP0
      rw [hC]
      simp [hz]
    obtain ⟨θ₀⟩ := sphere_nonempty (n := n)
    refine ⟨θ₀, ?_⟩
    rw [hC]
    simpa using hc
  · -- degree `k ≥ 1` : if the polynomial vanished on the whole sphere, then by
    -- homogeneity it would vanish on every ray and hence everywhere.
    by_contra hno
    have hvanish : ∀ θ : Sph n, MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P = 0 := by
      intro θ
      by_contra hz
      exact hno ⟨θ, hz⟩
    apply hP0
    apply MvPolynomial.funext
    intro f
    let x : Eu n := (EuclideanSpace.equiv (Fin n) ℝ).symm f
    have hxf : ∀ i : Fin n, x i = f i := by
      intro i
      simp [x]
    by_cases hx : x = 0
    · have hzero : f = fun _ : Fin n => (0 : ℝ) := by
        funext i
        have hxi : x i = 0 := by rw [hx]; rfl
        simpa [hxf i] using hxi
      rw [hzero]
      rw [eval_zero_coeff]
      exact coeff0_zero_of_degree_pos P hhom hk
    · let u : Eu n := (‖x‖⁻¹) • x
      have hnorm : ‖u‖ = 1 := by
        dsimp [u]
        calc
          ‖(‖x‖⁻¹) • x‖ = ‖‖x‖⁻¹‖ * ‖x‖ := by rw [norm_smul]
          _ = ‖x‖⁻¹ * ‖x‖ := by rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
          _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
      have hv_u : MvPolynomial.eval (fun i : Fin n => (u : Eu n) i) P = 0 :=
        hvanish ⟨u, by rw [mem_sphere_zero_iff_norm]; exact hnorm⟩
      have hxeq : (fun i : Fin n => x i) = fun i : Fin n => ‖x‖ * (u : Eu n) i := by
        funext i
        dsimp [u]
        field_simp [norm_ne_zero_iff.mpr hx]
      have hsc := homogeneous_eval_smul P hhom ‖x‖ (fun i : Fin n => (u : Eu n) i)
      calc
        MvPolynomial.eval f P = MvPolynomial.eval (fun i : Fin n => x i) P := by
          apply congrArg (fun g : Fin n → ℝ => MvPolynomial.eval g P)
          funext i
          exact (hxf i).symm
        _ = MvPolynomial.eval (fun i : Fin n => ‖x‖ * (u : Eu n) i) P := by
          rw [hxeq]
        _ = ‖x‖ ^ k * MvPolynomial.eval (fun i : Fin n => (u : Eu n) i) P := hsc
        _ = 0 := by rw [hv_u]; ring

/-- Restriction of a polynomial to the unit sphere is continuous. -/
private lemma continuous_eval_sphere {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    Continuous (fun θ : Sph n => MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P) := by
  have hcont : Continuous (fun θ : Sph n => (spherePolyToCont n P : Sph n → ℝ) θ) :=
    (spherePolyToCont n P).continuous
  convert hcont using 1
  funext θ
  exact (spherePoly_apply_eval P θ).symm

/-- A continuous function on the sphere is integrable w.r.t. the sphere measure. -/
private lemma integrable_of_continuous_sphere (n : ℕ) (f : Sph n → ℝ) (hf : Continuous f) :
    MeasureTheory.Integrable f (MeasureTheory.volume.toSphere : Measure (Sph n)) := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ θ : Sph n, ‖f θ‖ ≤ B := by
    have hb : Bornology.IsBounded ((fun θ : Sph n => ‖f θ‖) '' (univ : Set (Sph n))) :=
      (isCompact_univ.image hf.norm).isBounded
    obtain ⟨C, hC⟩ := hb.exists_norm_le
    refine ⟨C, ?_⟩
    intro θ
    simpa using hC ‖f θ‖ ⟨θ, trivial, rfl⟩
  exact Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all (MeasureTheory.volume.toSphere : Measure (Sph n)) hB)

/-- The square of a nonzero homogeneous polynomial integrates strictly positively
over the unit sphere. -/
theorem sphere_integral_sq_pos_of_homogeneous_nz
    {n : ℕ} {k : ℕ} [Nonempty (Fin n)]
    (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) (hP0 : P ≠ 0) :
    0 < (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P)^2
        ∂MeasureTheory.volume.toSphere) := by
  obtain ⟨θ₀, hθ₀⟩ := exists_sphere_eval_ne_zero_of_homogeneous (n := n) (k := k) P hP hP0
  let f : Sph n → ℝ := fun θ : Sph n =>
    (MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P)^2
  have hfcont : Continuous f := by
    dsimp [f]
    exact ((continuous_eval_sphere P).pow 2)
  have hfint : MeasureTheory.Integrable f (MeasureTheory.volume.toSphere : Measure (Sph n)) :=
    integrable_of_continuous_sphere n f hfcont
  have hfnonneg : 0 ≤ f := by
    intro θ
    dsimp [f]
    exact sq_nonneg _
  have hfθ₀ : f θ₀ ≠ 0 := by
    dsimp [f]
    exact pow_ne_zero 2 hθ₀
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
    (μ := (MeasureTheory.volume.toSphere : Measure (Sph n)))
    (f := f) hfcont hfint hfnonneg hfθ₀

end Commons.Analysis.MeasureTheory