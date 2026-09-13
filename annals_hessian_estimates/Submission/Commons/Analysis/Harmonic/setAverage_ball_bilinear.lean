import Mathlib
import Submission.Commons.Analysis.MeasureTheory.polar_integral
import Submission.Commons.Analysis.MeasureTheory.homogeneous_even_sphere_integral_eq_const_laplacian_pow
import Submission.Commons.Analysis.MeasureTheory.integral_ball_bilinear
import Submission.Commons.Analysis.MeasureTheory.sphere_evenMonomial_integral_mul_dblFact
import Submission.Commons.Analysis.MeasureTheory.sphere_monomial_integral_zero_of_odd
import Submission.Commons.Analysis.MeasureTheory.continuous_integrable_sphere

/-!
# The average of a bilinear form over a Euclidean ball

For a continuous bilinear form `M` on `EuclideanSpace ℝ (Fin n)` (`n > 0`) the average of the
quadratic form `z ↦ M z z` over the ball `ball 0 r` equals `r ^ 2 / (n + 2)` times the trace of
`M` in the standard coordinate basis:

`⨍ z in ball 0 r, M z z = r ^ 2 / (n + 2) * ∑ i, M (e i) (e i)`, `e i = single i 1`.

The proof combines three ingredients:

* `Commons.Analysis.MeasureTheory.integral_ball_bilinear` (polar coordinates): the integral of
  `M z z` over the ball is `r ^ (n + 2) / (n + 2)` times its integral over the unit sphere;
* `Commons.Analysis.Harmonic.sphere_integral_bilinear`: the integral of `M θ θ` over the unit
  sphere is `(surface area / n)` times the trace, which is deduced from the second moments
  `∫ θ_i θ_j dθ = (surface area / n) * δ_ij`
  (`Commons.Analysis.Harmonic.sphere_coord_mul_integral`), themselves consequences of the
  Pizzetti-type formula `Commons.Analysis.MeasureTheory.sphere_evenMonomial_integral_mul_dblFact`
  for even monomials and the vanishing of odd monomials
  (`Commons.Analysis.MeasureTheory.sphere_monomial_integral_zero_of_odd`);
* `volume_real_ball'`: `volume (ball 0 r) = (r ^ n / n) * (surface area)`, obtained from
  `Measure.addHaar_ball` and `Measure.toSphere_apply_univ`.
-/

open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.Analysis.Harmonic

private abbrev Eu (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev Sp (n : ℕ) := Metric.sphere (0 : Eu n) 1

private lemma sphere_sum_sq {n : ℕ} (θ : Sp n) :
    (∑ k : Fin n, (θ : Eu n) k * (θ : Eu n) k) = 1 := by
  have h : (∑ k : Fin n, ((θ : Eu n) k)^2) = 1 := by
    have hmem : (θ : Eu n) ∈ Metric.sphere (0 : Eu n) 1 := θ.2
    rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at hmem
    simpa using hmem
  simpa [sq] using h

private lemma prod_single_sq {n : ℕ} (k : Fin n) (θ : Eu n) :
    (Finset.univ.prod (fun i : Fin n => (θ i) ^ (2 * (Finsupp.single k (1:ℕ)) i)))
      = (θ k) * (θ k) := by
  rw [Finset.prod_eq_single k]
  · rw [Finsupp.single_eq_same]; ring
  · intro b _ hbk
    rw [Finsupp.single_eq_of_ne hbk, mul_zero, pow_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private lemma prod_dblfact_single {n : ℕ} (k : Fin n) :
    (Finset.univ.prod (fun i : Fin n =>
      ((Nat.doubleFactorial (2 * (Finsupp.single k (1:ℕ)) i - 1) : ℕ) : ℝ))) = 1 := by
  rw [Finset.prod_eq_single k]
  · norm_num
  · intro b _ hbk
    rw [Finsupp.single_eq_of_ne hbk, mul_zero, Nat.zero_sub]
    norm_num
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private lemma prod_two {n : ℕ} {i j : Fin n} (hij : i ≠ j) (θ : Eu n) :
    (Finset.univ.prod (fun k : Fin n =>
        (θ k) ^ ((Finsupp.single i (1:ℕ) + Finsupp.single j (1:ℕ)) k))) = (θ i) * (θ j) := by
  have hp : (Finsupp.single i (1:ℕ) + Finsupp.single j (1:ℕ)).prod (fun k m => (θ k) ^ m)
      = (Finset.univ.prod (fun k : Fin n =>
          (θ k) ^ ((Finsupp.single i (1:ℕ) + Finsupp.single j (1:ℕ)) k))) :=
    Finsupp.prod_fintype _ _ (by intro k; simp)
  rw [← hp]
  rw [Finsupp.prod_add_index (h := fun k m => (θ k)^m) (by intro a _; simp)
      (by intro a _ b1 b2; rw [pow_add])]
  rw [Finsupp.prod_single_index (h := fun k m => (θ k)^m) (by simp),
      Finsupp.prod_single_index (h := fun k m => (θ k)^m) (by simp)]
  ring

private lemma basis_sum {n : ℕ} (x : Eu n) :
    x = ∑ i : Fin n, x i • EuclideanSpace.single i (1:ℝ) := by
  nth_rw 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]

private lemma bilin_expansion {n : ℕ} (M : Eu n →L[ℝ] Eu n →L[ℝ] ℝ) (x y : Eu n) :
    M x y = ∑ i : Fin n, ∑ j : Fin n,
      M (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single j (1:ℝ)) * (x i) * (y j) := by
  conv_lhs => rw [basis_sum x, basis_sum y]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The second moment of the surface measure on the unit sphere: for `i ≠ j` the coordinates are
orthogonal in `L²`, and for `i = j` the common value is the total mass divided by `n`. -/
theorem sphere_coord_mul_integral {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (θ : EuclideanSpace ℝ (Fin n)) i * (θ : EuclideanSpace ℝ (Fin n)) j
      ∂MeasureTheory.volume.toSphere)
      = ((∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, (1:ℝ)
          ∂MeasureTheory.volume.toSphere) / (n : ℝ)) * (if i = j then 1 else 0) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set μ : Measure (Sp n) := MeasureTheory.volume.toSphere with hμ
  obtain ⟨C, hC⟩ := Commons.Analysis.MeasureTheory.sphere_evenMonomial_integral_mul_dblFact
      (n := n) (m := 1) hn
  have hsq : ∀ k : Fin n, (∫ θ : Sp n, (θ : Eu n) k * (θ : Eu n) k ∂μ) = C := by
    intro k
    have h := hC (Finsupp.single k (1:ℕ)) (by simp)
    have hp : (∫ θ : Sp n,
          (Finset.univ.prod (fun i : Fin n => ((θ : Eu n) i) ^ (2 * (Finsupp.single k (1:ℕ)) i)))
          ∂μ) = ∫ θ : Sp n, (θ : Eu n) k * (θ : Eu n) k ∂μ := by
      apply integral_congr_ae
      filter_upwards with θ
      exact prod_single_sq k (θ : Eu n)
    rw [hp, prod_dblfact_single k, mul_one] at h
    exact h
  have hsum : (∫ θ : Sp n, (1:ℝ) ∂μ) = (n : ℝ) * C := by
    have hpt : (fun θ : Sp n => (1:ℝ))
        = fun θ : Sp n => ∑ k : Fin n, (θ : Eu n) k * (θ : Eu n) k := by
      funext θ
      rw [sphere_sum_sq θ]
    rw [hpt]
    rw [integral_finsetSum (s := Finset.univ)
      (f := fun k (θ : Sp n) => (θ : Eu n) k * (θ : Eu n) k)
      (hf := by
        intro k _
        exact Commons.Analysis.MeasureTheory.continuous_integrable_sphere (n := n)
          (fun θ : Sp n => (θ : Eu n) k * (θ : Eu n) k) (by fun_prop))]
    simp [hsq, Finset.sum_const, nsmul_eq_mul]
  have hCeq : C = (∫ θ : Sp n, (1:ℝ) ∂μ) / (n : ℝ) := by
    rw [hsum]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, mul_one, hsq i, hCeq]
  · rw [if_neg hij, mul_zero]
    have hodd : ∃ k : Fin n, Odd ((Finsupp.single i (1:ℕ) + Finsupp.single j (1:ℕ)) k) := by
      refine ⟨i, ?_⟩
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij, add_zero]
      norm_num
    have hz := Commons.Analysis.MeasureTheory.sphere_monomial_integral_zero_of_odd (n := n) hn
      (Finsupp.single i (1:ℕ) + Finsupp.single j (1:ℕ)) hodd
    have hp : (∫ θ : Sp n, (θ : Eu n) i * (θ : Eu n) j ∂μ)
        = ∫ θ : Sp n, (Finset.univ.prod (fun k : Fin n =>
            ((θ : Eu n) k) ^ ((Finsupp.single i (1:ℕ) + Finsupp.single j (1:ℕ)) k))) ∂μ := by
      apply integral_congr_ae
      filter_upwards with θ
      exact (prod_two hij (θ : Eu n)).symm
    rw [hp, hμ]
    exact hz

/-- The integral of a quadratic form over the unit sphere is `(surface area / n) *` trace. -/
theorem sphere_integral_bilinear {n : ℕ} (hn : 0 < n)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, M θ θ
        ∂MeasureTheory.volume.toSphere)
      = ((∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, (1:ℝ)
          ∂MeasureTheory.volume.toSphere) / (n : ℝ)) *
        ∑ i : Fin n, M (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set c : ℝ := (∫ θ : Sp n, (1:ℝ) ∂MeasureTheory.volume.toSphere) / (n : ℝ) with hc
  have hcm : ∀ i j : Fin n, Integrable (fun θ : Sp n => (θ : Eu n) i * (θ : Eu n) j)
      (MeasureTheory.volume.toSphere : Measure (Sp n)) := fun i j =>
    Commons.Analysis.MeasureTheory.continuous_integrable_sphere (n := n)
      (fun θ : Sp n => (θ : Eu n) i * (θ : Eu n) j) (by fun_prop)
  have hmom : ∀ i j : Fin n,
      (∫ θ : Sp n, (θ : Eu n) i * (θ : Eu n) j ∂MeasureTheory.volume.toSphere)
        = c * (if i = j then 1 else 0) := by
    intro i j
    rw [hc]
    exact sphere_coord_mul_integral hn i j
  have hpt : ∀ θ : Sp n, M θ θ = ∑ i : Fin n, ∑ j : Fin n,
      M (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
        * ((θ : Eu n) i * (θ : Eu n) j) := by
    intro θ
    rw [bilin_expansion]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hstep1 : ∀ i : Fin n,
      (∫ θ : Sp n, (∑ j : Fin n, M (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
        * ((θ : Eu n) i * (θ : Eu n) j)) ∂MeasureTheory.volume.toSphere)
      = ∑ j : Fin n, M (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
          (c * (if i = j then 1 else 0)) := by
    intro i
    rw [integral_finsetSum (s := Finset.univ)
      (f := fun j (θ : Sp n) => M (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
        * ((θ : Eu n) i * (θ : Eu n) j))
      (hf := by
        intro j _
        exact (hcm i j).const_mul _)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, hmom i j]
  have hdiag : ∀ i : Fin n,
      (∑ j : Fin n, M (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
          (c * (if i = j then 1 else 0))) = M (EuclideanSpace.single i 1)
            (EuclideanSpace.single i 1) * c := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_one]
    · intro j _ hji
      rw [if_neg (fun h => hji h.symm), mul_zero, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have houter : ∀ i : Fin n, Integrable (fun θ : Sp n => ∑ j : Fin n,
      M (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
        * ((θ : Eu n) i * (θ : Eu n) j)) (MeasureTheory.volume.toSphere : Measure (Sp n)) :=
    fun i => by
      rw [show (fun θ : Sp n => ∑ j : Fin n, M (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1) * ((θ : Eu n) i * (θ : Eu n) j))
          = ∑ j : Fin n, (fun θ : Sp n => M (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1) * ((θ : Eu n) i * (θ : Eu n) j)) from by
        funext θ
        rw [Finset.sum_apply]]
      exact integrable_finsetSum' _ (fun j _ => (hcm i j).const_mul _)
  rw [show (∫ θ : Sp n, M θ θ ∂MeasureTheory.volume.toSphere)
      = ∫ θ : Sp n, (∑ i : Fin n, ∑ j : Fin n,
          M (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
            * ((θ : Eu n) i * (θ : Eu n) j)) ∂MeasureTheory.volume.toSphere from by
      apply integral_congr_ae
      filter_upwards with θ
      exact hpt θ]
  rw [integral_finsetSum (s := Finset.univ)
    (f := fun i (θ : Sp n) => ∑ j : Fin n,
      M (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
        * ((θ : Eu n) i * (θ : Eu n) j))
    (hf := by intro i _; exact houter i)]
  rw [Finset.sum_congr rfl (fun i _ => hstep1 i)]
  rw [Finset.sum_congr rfl (fun i _ => hdiag i)]
  rw [← Finset.sum_mul, hc]
  ring

/-- The surface area of the unit sphere is nonzero (it equals `n` times the volume of the unit
ball). -/
private lemma sphere_integral_one_ne_zero {n : ℕ} (hn : 0 < n) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, (1:ℝ)
      ∂MeasureTheory.volume.toSphere) ≠ 0 := by
  have hfinrank : Module.finrank ℝ (Eu n) = n := finrank_euclideanSpace_fin
  have hpos : 0 < (MeasureTheory.volume : Measure (Eu n))
      (Metric.ball (0 : Eu n) 1) := measure_ball_pos _ 0 one_pos
  have hfin : (MeasureTheory.volume : Measure (Eu n)) (Metric.ball (0 : Eu n) 1) ≠ ∞ := by
    rw [← lt_top_iff_ne_top]
    exact measure_ball_lt_top
  have hrealpos : 0 < ((MeasureTheory.volume : Measure (Eu n))
      (Metric.ball (0 : Eu n) 1)).toReal := ENNReal.toReal_pos hpos.ne' hfin
  have hIntOne : (∫ θ : Sp n, (1:ℝ) ∂MeasureTheory.volume.toSphere)
      = ((MeasureTheory.volume : Measure (Eu n)).toSphere).real Set.univ := by
    rw [MeasureTheory.integral_const]
    simp
  rw [hIntOne, Measure.toSphere_real_apply_univ, hfinrank, Measure.real_def]
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast hn.ne'
  · exact hrealpos.ne'

/-- The volume of a ball in terms of the surface area of the unit sphere. -/
private lemma volume_real_ball' {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    ((MeasureTheory.volume : Measure (Eu n)) (Metric.ball (0 : Eu n) r)).toReal
      = r ^ n / (n : ℝ) *
        (∫ θ : Sp n, (1:ℝ) ∂MeasureTheory.volume.toSphere) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hfinrank : Module.finrank ℝ (Eu n) = n := finrank_euclideanSpace_fin
  have hhaar := Measure.addHaar_ball (MeasureTheory.volume : Measure (Eu n)) (0 : Eu n) hr.le
  have hfin1 : (MeasureTheory.volume : Measure (Eu n)) (Metric.ball (0 : Eu n) 1) ≠ ∞ := by
    rw [← lt_top_iff_ne_top]
    exact measure_ball_lt_top
  have h1 : (∫ θ : Sp n, (1:ℝ) ∂MeasureTheory.volume.toSphere)
      = (n : ℝ) * ((MeasureTheory.volume : Measure (Eu n))
          (Metric.ball (0 : Eu n) 1)).toReal := by
    have hIntOne : (∫ θ : Sp n, (1:ℝ) ∂MeasureTheory.volume.toSphere)
        = ((MeasureTheory.volume : Measure (Eu n)).toSphere).real Set.univ := by
      rw [MeasureTheory.integral_const]
      simp
    rw [hIntOne, Measure.toSphere_real_apply_univ, hfinrank, Measure.real_def]
  rw [hhaar, hfinrank, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  rw [h1]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp



/-- The average of a bilinear form `M` over the Euclidean ball `ball 0 r ⊂ ℝ^n` equals
`r ^ 2 / (n + 2)` times the trace `∑ i, M (e i) (e i)` computed in the coordinate basis
`e i = EuclideanSpace.single i 1`. -/
theorem setAverage_ball_bilinear {n : ℕ} (hn : 0 < n)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r) :
    (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, M z z)
      = r ^ 2 / ((n : ℝ) + 2) *
        ∑ i : Fin n, M (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  classical
  have hsphere := sphere_integral_bilinear (n := n) hn M
  have hball := Commons.Analysis.MeasureTheory.integral_ball_bilinear (n := n) hn M hr
  have hvol := volume_real_ball' hn hr
  have hI : (∫ θ : Sp n, (1:ℝ) ∂MeasureTheory.volume.toSphere) ≠ 0 :=
    sphere_integral_one_ne_zero hn
  rw [setAverage_eq, Measure.real_def, hball, hvol, hsphere]
  have hrne : r ≠ 0 := hr.ne'
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpown : r ^ n ≠ 0 := pow_ne_zero n hrne
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  rw [smul_eq_mul, show r ^ (n + 2) = r ^ n * r ^ 2 by rw [pow_add]]
  rw [inv_mul_eq_div]
  field_simp

end Commons.Analysis.Harmonic
