import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.Gaussian.gaussian_moment_prod_pi
import Submission.Commons.Analysis.MeasureTheory.polar_integral_prod
import Submission.Commons.Analysis.MeasureTheory.polar_integral

noncomputable section
open Set Function MeasureTheory Metric
open scoped Real Topology Nat Pointwise

namespace Commons.Analysis.MeasureTheory

private lemma sm_even_full_eq_two_Ioi (k : ℕ) :
    (∫ t : ℝ, t ^ (2 * k) * Real.exp (-(t ^ 2))) =
      2 * (∫ t : ℝ in Ioi (0 : ℝ), t ^ (2 * k) * Real.exp (-(t ^ 2))) := by
  let f : ℝ → ℝ := fun x => x ^ (2 * k) * Real.exp (-(x ^ 2))
  have hcomp : (fun t : ℝ => t ^ (2 * k) * Real.exp (-(t ^ 2))) = f ∘ abs := by
    funext t
    dsimp [f]
    congr 1
    · rw [pow_mul, pow_mul, sq_abs]
    · rw [sq_abs]
  calc
    (∫ t : ℝ, t ^ (2 * k) * Real.exp (-(t ^ 2))) = ∫ t : ℝ, f (|t|) := by
      rw [hcomp]
      rfl
    _ = 2 * ∫ x : ℝ in Ioi 0, f x := by
      simpa using (integral_comp_abs (f := f))
    _ = 2 * (∫ t : ℝ in Ioi (0 : ℝ), t ^ (2 * k) * Real.exp (-(t ^ 2))) := by
      simp [f]

private lemma sm_rpow_pointwise (k : ℕ) (r : ℝ) (hr : 0 < r) :
    (2 * r) * (Real.exp (-(r ^ (2 : ℝ))) * (r ^ (2 : ℝ)) ^ (((k : ℝ) + 1 / 2) - 1)) =
      2 * (r ^ (2 * (k : ℝ))) * Real.exp (-(r ^ (2 : ℝ))) := by
  have hx : 0 ≤ r := le_of_lt hr
  let z : ℝ := ((k : ℝ) + 1 / 2) - 1
  have hz : 1 + 2 * z = 2 * (k : ℝ) := by
    dsimp [z]
    ring
  have h1 : (r ^ (2 : ℝ)) ^ z = r ^ (2 * z) :=
    (Real.rpow_mul hx (2 : ℝ) z).symm
  have h2 : r * r ^ (2 * z) = r ^ (1 + 2 * z) := by
    rw [mul_comm]
    rw [← Real.rpow_add_one (ne_of_gt hr) (2 * z)]
    congr 1
    ring
  calc
    (2 * r) * (Real.exp (-(r ^ (2 : ℝ))) * (r ^ (2 : ℝ)) ^ z)
        = (2 * r * (r ^ (2 : ℝ)) ^ z) * Real.exp (-(r ^ (2 : ℝ))) := by ring
    _ = (2 * r * r ^ (2 * z)) * Real.exp (-(r ^ (2 : ℝ))) := by
        rw [h1]
    _ = (2 * (r * r ^ (2 * z))) * Real.exp (-(r ^ (2 : ℝ))) := by ring
    _ = (2 * r ^ (1 + 2 * z)) * Real.exp (-(r ^ (2 : ℝ))) := by
        rw [h2]
    _ = (2 * r ^ (2 * (k : ℝ))) * Real.exp (-(r ^ (2 : ℝ))) := by
        rw [hz]
    _ = 2 * (r ^ (2 * (k : ℝ))) * Real.exp (-(r ^ (2 : ℝ))) := by ring

private lemma sm_pow2k_nat (k : ℕ) (r : ℝ) : r ^ (2 * (k : ℝ)) = r ^ (2 * k) := by
  rw [show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by norm_num]
  exact Real.rpow_natCast r (2 * k)

private lemma sm_exp_pow_two_eq (r : ℝ) : Real.exp (-(r ^ 2)) = Real.exp (-(r ^ (2 : ℝ))) := by
  rw [← Real.rpow_natCast r 2]
  congr 1

private lemma sm_pointwise_g (k : ℕ) (r : ℝ) (hr : 0 < r) :
    2 * ((r ^ (2 * (k : ℝ))) * Real.exp (-(r ^ 2))) =
      (2 * r) * (Real.exp (-(r ^ (2 : ℝ))) * (r ^ (2 : ℝ)) ^ (((k : ℝ) + 1 / 2) - 1)) := by
  rw [sm_exp_pow_two_eq, sm_rpow_pointwise k r hr]
  ring

private lemma sm_even_moment_eq_Gamma (k : ℕ) :
    (∫ t : ℝ, t ^ (2 * k) * Real.exp (-(t ^ 2))) = Real.Gamma ((k : ℝ) + 1 / 2) := by
  have hs : 0 < (k : ℝ) + 1 / 2 := by positivity
  have hGamma : ∫ u : ℝ in Ioi 0,
      Real.exp (-u) * u ^ (((k : ℝ) + 1 / 2) - 1) = Real.Gamma ((k : ℝ) + 1 / 2) := by
    rw [← Real.Gamma_eq_integral hs]
  have hsub : (∫ r : ℝ in Ioi 0,
      (2 * r) * (Real.exp (-(r ^ (2 : ℝ))) * (r ^ (2 : ℝ)) ^ (((k : ℝ) + 1 / 2) - 1))) =
      (∫ u : ℝ in Ioi 0, Real.exp (-u) * u ^ (((k : ℝ) + 1 / 2) - 1)) := by
    let g : ℝ → ℝ := fun u => Real.exp (-u) * u ^ (((k : ℝ) + 1 / 2) - 1)
    have h := integral_comp_rpow_Ioi_of_pos (p := (2 : ℝ)) (g := g) (by norm_num)
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp [g, smul_eq_mul]
    norm_num
  calc
    (∫ t : ℝ, t ^ (2 * k) * Real.exp (-(t ^ 2)))
        = 2 * (∫ r : ℝ in Ioi (0 : ℝ), r ^ (2 * k) * Real.exp (-(r ^ 2))) := sm_even_full_eq_two_Ioi k
    _ = 2 * (∫ r : ℝ in Ioi (0 : ℝ), (r ^ (2 * (k : ℝ))) * Real.exp (-(r ^ 2))) := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        change r ^ (2 * k) * Real.exp (-(r ^ 2)) = (r ^ (2 * (k : ℝ))) * Real.exp (-(r ^ 2))
        rw [sm_pow2k_nat k r]
    _ = (∫ r : ℝ in Ioi (0 : ℝ), 2 * ((r ^ (2 * (k : ℝ))) * Real.exp (-(r ^ 2)))) := by
        rw [← MeasureTheory.integral_const_mul (2 : ℝ)
          (fun r : ℝ => (r ^ (2 * (k : ℝ))) * Real.exp (-(r ^ 2)))]
    _ = (∫ r : ℝ in Ioi (0 : ℝ),
          (2 * r) * (Real.exp (-(r ^ (2 : ℝ))) * (r ^ (2 : ℝ)) ^ (((k : ℝ) + 1 / 2) - 1))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        change 2 * ((r ^ (2 * (k : ℝ))) * Real.exp (-(r ^ 2))) =
          (2 * r) * (Real.exp (-(r ^ (2 : ℝ))) * (r ^ (2 : ℝ)) ^ (((k : ℝ) + 1 / 2) - 1))
        exact sm_pointwise_g k r hr
    _ = ∫ u : ℝ in Ioi 0, Real.exp (-u) * u ^ (((k : ℝ) + 1 / 2) - 1) := hsub
    _ = Real.Gamma ((k : ℝ) + 1 / 2) := hGamma

private lemma sm_monomial_smul (n : ℕ) (β : Fin n →₀ ℕ) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (∏ i : Fin n, (((r • x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i))) =
      (r ^ (2 * Finset.univ.sum (fun i : Fin n => β i))) *
        (∏ i : Fin n, ((x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)) := by
  calc
    (∏ i : Fin n, (((r • x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)))
        = ∏ i : Fin n, ((r * ((x : EuclideanSpace ℝ (Fin n)) i)) ^ (2 * β i)) := by
          apply Finset.prod_congr rfl
          intro i hi
          congr 1
    _ = ∏ i : Fin n, (r ^ (2 * β i)) * ((x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [mul_pow]
    _ = (∏ i : Fin n, r ^ (2 * β i)) * (∏ i : Fin n, ((x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)) := by
          rw [Finset.prod_mul_distrib]
    _ = (r ^ (Finset.univ.sum (fun i : Fin n => 2 * β i))) *
        (∏ i : Fin n, ((x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)) := by
          rw [← Finset.prod_pow_eq_pow_sum]
    _ = (r ^ (2 * Finset.univ.sum (fun i : Fin n => β i))) *
        (∏ i : Fin n, ((x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)) := by
          congr 1
          congr 1
          rw [← Finset.mul_sum]

private lemma sm_polar_moment {n : ℕ} [NeZero n] (β : Fin n →₀ ℕ) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∏ i : Fin n, ((θ : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)
      ∂volume.toSphere) *
      (∫ r : Set.Ioi (0 : ℝ),
        (r : ℝ) ^ (2 * Finset.univ.sum (fun i : Fin n => β i)) *
          Real.exp (-((r : ℝ) ^ 2))
        ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) =
    (∫ x : EuclideanSpace ℝ (Fin n),
        (∏ i : Fin n, ((x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)) *
          Real.exp (-(‖x‖ ^ 2))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let S := Metric.sphere (0 : E) 1
  let σ : Measure S := volume.toSphere
  let ν : Measure (Set.Ioi (0 : ℝ)) := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  let M : E → ℝ := fun x => ∏ i : Fin n, ((x : E) i) ^ (2 * β i)
  let M' : S → ℝ := fun θ => M (θ : E)
  let h : Set.Ioi (0 : ℝ) → ℝ := fun r =>
    (r : ℝ) ^ (2 * Finset.univ.sum (fun i : Fin n => β i)) * Real.exp (-((r : ℝ) ^ 2))
  let F : E → ℝ := fun x => M x * Real.exp (-(‖x‖ ^ 2))
  have hpoint : ∀ p : S × Set.Ioi (0 : ℝ),
      F (p.2.1 • (p.1 : E)) = M' p.1 * h p.2 := by
    intro p
    dsimp [F, M', h, M]
    have hr : 0 ≤ p.2.1 := le_of_lt p.2.2
    have hnorm : ‖(p.2.1 • (p.1 : E))‖ ^ 2 = p.2.1 ^ 2 := by
      have hnorm' : ‖(p.2.1 • (p.1 : E))‖ = p.2.1 := by
        calc
          ‖(p.2.1 • (p.1 : E))‖ = |p.2.1| * ‖(p.1 : E)‖ := by
            simpa using (norm_smul p.2.1 (p.1 : E))
          _ = p.2.1 := by
            rw [abs_of_nonneg hr, mem_sphere_zero_iff_norm.mp p.1.2]
            simp
      rw [hnorm']
    rw [hnorm]
    have hm := sm_monomial_smul n β p.2.1 (p.1 : E)
    rw [hm]
    ring
  calc
    (∫ θ : S, ∏ i : Fin n, ((θ : E) i) ^ (2 * β i) ∂σ) *
        (∫ r : Set.Ioi (0 : ℝ), h r ∂ν)
        = ∫ p : S × Set.Ioi (0 : ℝ), M' p.1 * h p.2 ∂(σ.prod ν) := by
          simpa [S, σ, ν, M'] using ((integral_prod_mul (μ := σ) (ν := ν) (f := M') (g := h)).symm)
    _ = ∫ p : S × Set.Ioi (0 : ℝ), F (p.2.1 • (p.1 : E)) ∂(σ.prod ν) := by
          apply integral_congr_ae
          filter_upwards with p
          exact (hpoint p).symm
    _ = ∫ x : E, F x := by
          simpa [F, S, σ, ν] using (polar_integral_prod (V := E) F).symm

private lemma sm_moment_prod_euclidean {n : ℕ} (β : Fin n →₀ ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin n),
        ∏ i : Fin n, (((x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)) *
          Real.exp (-((((x : EuclideanSpace ℝ (Fin n)) i) ^ 2)))) =
      ∏ i : Fin n, (∫ t : ℝ, t ^ (2 * β i) * Real.exp (-(t ^ 2))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let F : E → ℝ := fun x => ∏ i : Fin n, (((x : E) i) ^ (2 * β i)) * Real.exp (-(((x : E) i) ^ 2))
  have hvol : ∫ x : (Fin n → ℝ), F (WithLp.toLp 2 x) = ∫ y : E, F y := by
    have hmp : MeasurePreserving (@WithLp.toLp 2 (Fin n → ℝ)) volume volume :=
      PiLp.volume_preserving_toLp (Fin n)
    simpa using (hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding (g := F))
  calc
    (∫ x : E, F x) = ∫ x : Fin n → ℝ, F (WithLp.toLp 2 x) := hvol.symm
    _ = ∫ x : Fin n → ℝ, ∏ i : Fin n, ((x i) ^ (2 * β i)) * Real.exp (-((x i) ^ 2)) := by
        apply integral_congr_ae
        filter_upwards with x
        simp [F]
    _ = ∏ i : Fin n, (∫ t : ℝ, t ^ (2 * β i) * Real.exp (-(t ^ 2))) := by
        exact Commons.Analysis.Gaussian.gaussian_moment_prod_pi β

private lemma sm_eucl_norm_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ i : Fin n, (x i) ^ 2 := by
  exact EuclideanSpace.real_norm_sq_eq x

private lemma sm_exp_neg_norm_sq_eq_prod (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-(‖x‖ ^ 2)) = ∏ i : Fin n, Real.exp (-((x i) ^ 2)) := by
  calc
    Real.exp (-(‖x‖ ^ 2)) = Real.exp (-(∑ i : Fin n, (x i) ^ 2)) := by
      congr 1
      rw [sm_eucl_norm_sq n x]
    _ = Real.exp (∑ i : Fin n, -((x i) ^ 2)) := by
      congr 1
      rw [Finset.sum_neg_distrib]
    _ = ∏ i : Fin n, Real.exp (-((x i) ^ 2)) := by
      simpa using (Real.exp_sum (Finset.univ : Finset (Fin n)) (fun i : Fin n => -((x i) ^ 2)))


private lemma sm_monomial_mul_exp_prod (n : ℕ) (β : Fin n →₀ ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (∏ i : Fin n, ((x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)) *
        Real.exp (-(‖x‖ ^ 2)) =
      ∏ i : Fin n, (((x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)) *
        Real.exp (-(((x : EuclideanSpace ℝ (Fin n)) i) ^ 2)) := by
  rw [sm_exp_neg_norm_sq_eq_prod]
  rw [Finset.prod_mul_distrib]


private lemma sm_gauss_over_eucl (n : ℕ) (β : Fin n →₀ ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin n),
        (∏ i : Fin n, ((x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)) *
          Real.exp (-(‖x‖ ^ 2))) =
      ∏ i : Fin n, (∫ t : ℝ, t ^ (2 * β i) * Real.exp (-(t ^ 2))) := by
  have hpm : (∫ x : EuclideanSpace ℝ (Fin n),
        (∏ i : Fin n, ((x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)) *
          Real.exp (-(‖x‖ ^ 2))) =
      (∫ x : EuclideanSpace ℝ (Fin n),
        ∏ i : Fin n, (((x : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i)) *
          Real.exp (-((((x : EuclideanSpace ℝ (Fin n)) i) ^ 2)))) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [sm_monomial_mul_exp_prod n β x]
  rw [hpm]
  exact sm_moment_prod_euclidean β


private lemma sm_moment_gamma (k : ℕ) :
    (∫ t : ℝ, t ^ (2 * k) * Real.exp (-(t ^ 2))) =
      (Real.sqrt Real.pi) * ((Nat.doubleFactorial (2 * k - 1) : ℕ) : ℝ) / 2 ^ k := by
  rw [sm_even_moment_eq_Gamma]
  rw [Real.Gamma_nat_add_half k]
  ring

private lemma sm_product_moments {n : ℕ} (β : Fin n →₀ ℕ) :
    (∏ i : Fin n, (∫ t : ℝ, t ^ (2 * β i) * Real.exp (-(t ^ 2)))) =
      (Real.sqrt Real.pi) ^ n *
        (∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ)) /
        (2 : ℝ) ^ (Finset.univ.sum (fun i : Fin n => β i)) := by
  calc
    (∏ i : Fin n, (∫ t : ℝ, t ^ (2 * β i) * Real.exp (-(t ^ 2))))
        = ∏ i : Fin n,
            ((Real.sqrt Real.pi) * ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ) / 2 ^ (β i)) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact sm_moment_gamma (β i)
    _ = (∏ i : Fin n, (Real.sqrt Real.pi) * ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ)) /
        (∏ i : Fin n, (2 : ℝ) ^ (β i)) := by
          rw [Finset.prod_div_distrib]
    _ = ((∏ i : Fin n, Real.sqrt Real.pi) *
          (∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ))) /
        (∏ i : Fin n, (2 : ℝ) ^ (β i)) := by
          rw [Finset.prod_mul_distrib]
    _ = ((Real.sqrt Real.pi) ^ n *
          (∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ))) /
        (∏ i : Fin n, (2 : ℝ) ^ (β i)) := by
          congr 2
          rw [Finset.prod_const]
          simp
    _ = ((Real.sqrt Real.pi) ^ n *
          (∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ))) /
        (2 : ℝ) ^ (Finset.univ.sum (fun i : Fin n => β i)) := by
          congr 1
          rw [← Finset.prod_pow_eq_pow_sum]

set_option linter.style.haveILetI false in
theorem sphere_evenMonomial_integral_mul_dblFact
    {n : ℕ} {m : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, ∀ (β : Fin n →₀ ℕ),
      (Finset.univ.sum (fun i : Fin n => β i)) = m →
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            Finset.univ.prod (fun i : Fin n => ((θ : EuclideanSpace ℝ (Fin n)) i) ^ (2 * β i))
          ∂MeasureTheory.volume.toSphere) =
          C * (Finset.univ.prod (fun i : Fin n => ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ))) := by
  haveI : NeZero n := ⟨ne_of_gt hn⟩
  let E := EuclideanSpace ℝ (Fin n)
  let S := Metric.sphere (0 : E) 1
  let ν : Measure (Set.Ioi (0 : ℝ)) := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  let R : ℝ := ∫ r : Set.Ioi (0 : ℝ),
    (r : ℝ) ^ (2 * m) * Real.exp (-((r : ℝ) ^ 2)) ∂ν
  let P : ℝ := (Real.sqrt Real.pi) ^ n / (2 : ℝ) ^ m
  let D : (Fin n →₀ ℕ) → ℝ := fun β =>
    ∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ)
  let X : (Fin n →₀ ℕ) → ℝ := fun β =>
    ∫ θ : S, ∏ i : Fin n, ((θ : E) i) ^ (2 * β i) ∂volume.toSphere
  have hmain : ∀ (β : Fin n →₀ ℕ),
      (Finset.univ.sum (fun i : Fin n => β i)) = m → X β * R = P * D β := by
    intro β hw
    have hp := sm_polar_moment (n := n) (β := β)
    have hg := sm_gauss_over_eucl n β
    have hprod := sm_product_moments (n := n) (β := β)
    have h2m : 2 * Finset.univ.sum (fun i : Fin n => β i) = 2 * m := by
      rw [hw]
    have hrad : (∫ r : Set.Ioi (0 : ℝ),
          (r : ℝ) ^ (2 * Finset.univ.sum (fun i : Fin n => β i)) * Real.exp (-((r : ℝ) ^ 2)) ∂ν) = R := by
      dsimp [R]
      apply integral_congr_ae
      filter_upwards with r
      rw [h2m]
    have hEq : X β * R = ∫ x : E,
        (∏ i : Fin n, ((x : E) i) ^ (2 * β i)) * Real.exp (-(‖x‖ ^ 2)) := by
      calc
        X β * R = X β * (∫ r : Set.Ioi (0 : ℝ),
            (r : ℝ) ^ (2 * Finset.univ.sum (fun i : Fin n => β i)) * Real.exp (-((r : ℝ) ^ 2)) ∂ν) := by
              rw [hrad]
        _ = ∫ x : E, (∏ i : Fin n, ((x : E) i) ^ (2 * β i)) * Real.exp (-(‖x‖ ^ 2)) := by
              dsimp [X]
              exact hp
    have hEq2 : (∫ x : E, (∏ i : Fin n, ((x : E) i) ^ (2 * β i)) * Real.exp (-(‖x‖ ^ 2))) =
        ∏ i : Fin n, (∫ t : ℝ, t ^ (2 * β i) * Real.exp (-(t ^ 2))) := by
      dsimp [E]
      exact hg
    have hEq3 : (∏ i : Fin n, (∫ t : ℝ, t ^ (2 * β i) * Real.exp (-(t ^ 2)))) = P * D β := by
      dsimp [P, D]
      rw [hprod]
      have h2m' : (2 : ℝ) ^ Finset.univ.sum (fun i : Fin n => β i) = (2 : ℝ) ^ m := by
        rw [hw]
      rw [h2m']
      ring
    calc
      X β * R = (∫ x : E, (∏ i : Fin n, ((x : E) i) ^ (2 * β i)) * Real.exp (-(‖x‖ ^ 2))) := hEq
      _ = ∏ i : Fin n, (∫ t : ℝ, t ^ (2 * β i) * Real.exp (-(t ^ 2))) := hEq2
      _ = P * D β := hEq3
  have hRne : R ≠ 0 := by
    rcases (Fintype.card_pos_iff.mp (by simpa using hn) : Nonempty (Fin n)) with ⟨i0⟩
    let β0 : Fin n →₀ ℕ := Finsupp.single i0 m
    have hw0 : (Finset.univ.sum (fun i : Fin n => β0 i)) = m := by
      dsimp [β0]
      rw [Finset.sum_eq_single i0]
      · simp
      · intro b hb hne
        simp [Finsupp.single_eq_of_ne hne]
      · intro hi
        simp at hi
    have hmain0 := hmain β0 hw0
    have hD0 : D β0 ≠ 0 := by
      dsimp [D]
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      have hpos : (0 : ℝ) < ((Nat.doubleFactorial (2 * β0 i - 1) : ℕ) : ℝ) := by
        exact_mod_cast (Nat.doubleFactorial_pos (2 * β0 i - 1))
      exact ne_of_gt hpos
    have hP0 : P ≠ 0 := by
      dsimp [P]
      apply div_ne_zero
      · apply pow_ne_zero
        exact (Real.sqrt_ne_zero').mpr Real.pi_pos
      · apply pow_ne_zero
        norm_num
    have hPD : P * D β0 ≠ 0 := mul_ne_zero hP0 hD0
    have hX0 : X β0 * R ≠ 0 := by
      rw [hmain0]
      exact hPD
    intro hR0
    have : X β0 * R = 0 := by rw [hR0, mul_zero]
    exact hX0 this
  refine ⟨P / R, ?_⟩
  intro β hw
  change X β = (P / R) * D β
  have hEq := hmain β hw
  have h1 : (X β * R) * R⁻¹ = X β := by
    calc
      (X β * R) * R⁻¹ = X β * (R * R⁻¹) := by rw [mul_assoc]
      _ = X β * 1 := by rw [mul_inv_cancel₀ hRne]
      _ = X β := by rw [mul_one]
  calc
    X β = (X β * R) * R⁻¹ := h1.symm
    _ = (P * D β) * R⁻¹ := by rw [hEq]
    _ = (P / R) * D β := by
      field_simp [hRne]

end Commons.Analysis.MeasureTheory