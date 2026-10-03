import Mathlib
import Submission.Work.KMTAreas.A7.LacDevBasics

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

/-- The deviation kernel sampled against a character is summable at every scale: it is the
deviation kernel (summable, `devKern_summable`) times a unimodular factor. -/
theorem summable_devKern_mul_chr (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
    (n : ℕ) (θ : ℝ) :
    Summable (fun j : ℤ => devKern K σ n j * Work.KMTAreas.ADev.chr j θ) := by
  refine Summable.of_norm_bounded (f := fun j : ℤ => devKern K σ n j * Work.KMTAreas.ADev.chr j θ)
    (g := fun j : ℤ => ‖devKern K σ n j‖) (devKern_summable K σ hσ1 n).norm ?_
  intro j
  rw [norm_mul, Work.KMTAreas.ADev.norm_chr, mul_one]

/-- The Fourier coefficient of the linearized deviation kernel is the signed sum of the Fourier
coefficients of the individual deviation kernels. -/
theorem lacDevLin_tsum_eq (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
    (U : Finset ℕ) (ω : ℕ → Bool) (θ : ℝ) :
    (∑' j : ℤ, Work.KMTAreas.A7.lacDevLin K σ U ω j * Work.KMTAreas.ADev.chr j θ)
      = ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n *
          (∑' j : ℤ, Work.KMTAreas.A7.devKern K σ n j * Work.KMTAreas.ADev.chr j θ) := by
  have hsum : ∀ n : ℕ, Summable (fun j : ℤ =>
      Work.KMTAreas.A7.devKern K σ n j * Work.KMTAreas.ADev.chr j θ) :=
    fun n => summable_devKern_mul_chr K σ hσ1 n θ
  calc (∑' j : ℤ, Work.KMTAreas.A7.lacDevLin K σ U ω j * Work.KMTAreas.ADev.chr j θ)
      = ∑' j : ℤ, ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n *
          (Work.KMTAreas.A7.devKern K σ n j * Work.KMTAreas.ADev.chr j θ) := by
        refine tsum_congr fun j => ?_
        simp only [lacDevLin]
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun n _ => by ring
    _ = ∑ n ∈ U, ∑' j : ℤ, Work.KMTAreas.ADev.bSign ω n *
          (Work.KMTAreas.A7.devKern K σ n j * Work.KMTAreas.ADev.chr j θ) :=
        Summable.tsum_finsetSum (fun n _ => (hsum n).mul_left _)
    _ = ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n *
          (∑' j : ℤ, Work.KMTAreas.A7.devKern K σ n j * Work.KMTAreas.ADev.chr j θ) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [tsum_mul_left]

end

end Work.KMTAreas.A7
