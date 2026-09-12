import Mathlib
import Submission.Commons.Analysis.MeasureTheory.cosine_even_degree_scalar_ne_zero
import Submission.Commons.Analysis.MeasureTheory.cosine_scalar_const_on_Hk
import Submission.Commons.Analysis.MeasureTheory.cosine_harmonic_scalar
import Submission.Commons.Algebra.MvPolynomial.zonal_eigenvalue_poly_decay
import Submission.Commons.Algebra.MvPolynomial.exists_zonalHarmonic
import Submission.Commons.Algebra.MvPolynomial.zonal_even_eigenvalue_ne_zero
import Submission.Commons.Algebra.MvPolynomial.zonal_pole_value_ne_zero

namespace Commons.Analysis.MeasureTheory

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped BigOperators

/-- **Eigenvalue decay for the cosine transform on even spherical harmonics.**

For every dimension `n ≥ 2` the cosine transform `g ↦ ∫ |⟨u,θ⟩| g θ dθ` on the
unit sphere of `EuclideanSpace ℝ (Fin n)` acts as a scalar `lam m` on the space of
restrictions of harmonic homogeneous polynomials of even degree `2m`.  This
scalar is non-zero in degree `0` and obeys the polynomial lower bound
`c0 · m ^ (-K) ≤ |lam m|` for all `m ≥ 1`: the eigenvalues decay at most
polynomially, which is exactly what makes the transform invertible on smooth even
functions. -/
theorem cosine_even_eigenvalue_decay
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ K : ℕ, ∃ lam : ℕ → ℝ,
      lam 0 ≠ 0 ∧
      (∀ m : ℕ, 1 ≤ m → c0 * (m : ℝ) ^ (-(K : ℤ)) ≤ |lam m|) ∧
      (∀ m : ℕ, ∀ P : MvPolynomial (Fin n) ℝ,
        P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m) →
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 →
        ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
                MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) P
            ∂MeasureTheory.volume.toSphere) =
            lam m * MvPolynomial.eval (fun l : Fin n => (u : EuclideanSpace ℝ (Fin n)) l) P) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  -- The Funk--Hecke scalar constant attached to each even degree, packaged as `lam` of `m`.
  have h_exists : ∀ m : ℕ, ∃ c : ℝ, ∀ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m) →
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 →
      ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
              MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) P
          ∂MeasureTheory.volume.toSphere) =
        c * MvPolynomial.eval (fun l : Fin n => (u : EuclideanSpace ℝ (Fin n)) l) P :=
    fun m => cosine_harmonic_scalar_uniform (n := n) (k := 2 * m) hn
  let lam : ℕ → ℝ := fun m => Classical.choose (h_exists m)
  have hlam : ∀ (m : ℕ) (P : MvPolynomial (Fin n) ℝ),
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m) →
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 →
      ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
              MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) P
          ∂MeasureTheory.volume.toSphere) =
        lam m * MvPolynomial.eval (fun l : Fin n => (u : EuclideanSpace ℝ (Fin n)) l) P :=
    fun m P hPh hlap u => Classical.choose_spec (h_exists m) P hPh hlap u
  let i0 : Fin n := ⟨0, by omega⟩
  -- Uniform decay constants over the zonal (axis) harmonics.
  obtain ⟨c0, hc0pos, K, hK⟩ :=
    Commons.Algebra.MvPolynomial.zonal_eigenvalue_poly_decay (n := n) (i := i0) hn
  refine ⟨c0, hc0pos, K, lam, ?_, ?_, ?_⟩
  · -- Non-vanishing in degree `0`, witnessed by the degree-`0` zonal harmonic.
    obtain ⟨Z, R, hZmem, hlapZ, hRmem, hdec⟩ :=
      Commons.Algebra.MvPolynomial.exists_zonalHarmonic (n := n) (k := 0)
        (a := (EuclideanSpace.single i0 (1 : ℝ) : EuclideanSpace ℝ (Fin n)))
    exact Commons.Algebra.MvPolynomial.zonal_even_eigenvalue_ne_zero (n := n) (m := 0) i0 hn
      Z R hZmem hlapZ hRmem hdec (lam 0) (hlam 0 Z hZmem hlapZ)
  · -- Polynomial lower bound on the eigenvalue for every `m ≥ 1`.
    intro m hm
    obtain ⟨Z, R, hZmem, hlapZ, hRmem, hdec⟩ :=
      Commons.Algebra.MvPolynomial.exists_zonalHarmonic (n := n) (k := 2 * m)
        (a := (EuclideanSpace.single i0 (1 : ℝ) : EuclideanSpace ℝ (Fin n)))
    exact hK m hm Z R hZmem hlapZ hRmem hdec (lam m) (hlam m Z hZmem hlapZ)
  · -- The defining scalar property of `lam`.
    intro m P hPh hlap u
    exact hlam m P hPh hlap u

end Commons.Analysis.MeasureTheory
