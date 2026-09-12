import Mathlib
import Submission.Commons.Analysis.MeasureTheory.harmonic_sphere_integral_zero

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Commons.Analysis.MeasureTheory

private abbrev E1 := EuclideanSpace ℝ (Fin 1)
private abbrev S1 := Metric.sphere (0 : E1) 1

private def eOne : E1 := EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

private lemma E1_coord (x : E1) : x = (x 0) • eOne := by
  apply PiLp.ext
  intro i
  fin_cases i
  simp [eOne, EuclideanSpace.single]

private lemma E1_inner (x y : E1) : inner ℝ x y = x 0 * y 0 := by
  simp [PiLp.inner_apply]
  ring

private lemma eOne_norm : ‖eOne‖ = 1 := by
  simp [eOne, EuclideanSpace.single]

private lemma sphere_fin_one_abs_inner (u θ : S1) : |inner ℝ (u : E1) (θ : E1)| = 1 := by
  have hxabs : ∀ x : S1, |(x : E1) 0| = 1 := by
    intro x
    have h := congrArg (fun y : E1 => ‖y‖) (E1_coord (x : E1))
    rw [norm_smul] at h
    rw [(mem_sphere_zero_iff_norm.mp x.2)] at h
    rw [eOne_norm] at h
    simpa [Real.norm_eq_abs] using h.symm
  rw [E1_inner (u : E1) (θ : E1)]
  rw [abs_mul]
  rw [hxabs u, hxabs θ]
  norm_num

theorem cosine_harmonic_scalar_fin_one {k : ℕ}
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 → ℝ)
    (hg : ∃ P : MvPolynomial (Fin 1) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin 1) ℝ k ∧
      (∑ i : Fin 1, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 ∧
      ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
        g θ = MvPolynomial.eval (fun i : Fin 1 => (θ : EuclideanSpace ℝ (Fin 1)) i) P) :
    ∃ c : ℝ, ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
          |inner ℝ (u : EuclideanSpace ℝ (Fin 1)) (θ : EuclideanSpace ℝ (Fin 1))| * g θ
        ∂MeasureTheory.volume.toSphere) = c * g u := by
  classical
  rcases hg with ⟨P, hP, hlap, hgP⟩
  by_cases hk : k = 0
  · subst k
    have hP0 : P ∈ MvPolynomial.homogeneousSubmodule (Fin 1) ℝ 0 := hP
    rw [MvPolynomial.homogeneousSubmodule_zero] at hP0
    rcases Submodule.mem_one.mp hP0 with ⟨r, hr⟩
    have hCr : P = MvPolynomial.C r := by
      simpa [MvPolynomial.algebraMap_eq] using hr.symm
    refine ⟨(MeasureTheory.volume.toSphere : Measure S1).real Set.univ, ?_⟩
    intro u
    have hgconst : ∀ θ : S1, g θ = r := by
      intro θ
      calc
        g θ = MvPolynomial.eval (fun i : Fin 1 => (θ : EuclideanSpace ℝ (Fin 1)) i) P := hgP θ
        _ = MvPolynomial.eval (fun i : Fin 1 => (θ : EuclideanSpace ℝ (Fin 1)) i) (MvPolynomial.C r) := by rw [hCr]
        _ = r := by simp
    calc
      (∫ θ : S1,
          |inner ℝ (u : EuclideanSpace ℝ (Fin 1)) (θ : EuclideanSpace ℝ (Fin 1))| * g θ
        ∂MeasureTheory.volume.toSphere)
          = ∫ θ : S1, r ∂MeasureTheory.volume.toSphere := by
              apply integral_congr_ae
              filter_upwards with θ
              rw [sphere_fin_one_abs_inner u θ, hgconst θ]
              simp
      _ = (MeasureTheory.volume.toSphere : Measure S1).real Set.univ * r := by
              rw [MeasureTheory.integral_const]
              simp [smul_eq_mul]
      _ = (MeasureTheory.volume.toSphere : Measure S1).real Set.univ * g u := by
              rw [hgconst u]
  · refine ⟨0, ?_⟩
    intro u
    have hφ : (∫ θ : S1,
          MvPolynomial.eval (fun i : Fin 1 => (θ : EuclideanSpace ℝ (Fin 1)) i) P
        ∂MeasureTheory.volume.toSphere) = 0 := by
      exact @harmonic_sphere_integral_zero 1 k (⟨0⟩ : Nonempty (Fin 1)) hk P hP hlap
    calc
      (∫ θ : S1,
          |inner ℝ (u : EuclideanSpace ℝ (Fin 1)) (θ : EuclideanSpace ℝ (Fin 1))| * g θ
        ∂MeasureTheory.volume.toSphere)
          = ∫ θ : S1,
              MvPolynomial.eval (fun i : Fin 1 => (θ : EuclideanSpace ℝ (Fin 1)) i) P
            ∂MeasureTheory.volume.toSphere := by
              apply integral_congr_ae
              filter_upwards with θ
              rw [sphere_fin_one_abs_inner u θ, hgP θ]
              simp
      _ = 0 := hφ
      _ = 0 * g u := by ring

end Commons.Analysis.MeasureTheory
