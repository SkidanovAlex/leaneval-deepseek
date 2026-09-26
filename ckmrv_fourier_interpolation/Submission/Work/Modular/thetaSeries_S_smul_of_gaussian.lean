import Mathlib
import Submission.Work.Modular.Lattice
import Submission.Work.Modular.ThetaImagAxis
import Submission.Work.Modular.thetaSeries_mdifferentiable
import Submission.Work.Modular.thetaSeries_imagPoint
import Submission.Work.Modular.gaussSum_inv_of_functionalEquation
import Submission.Work.Modular.imagPoint_S_smul
import Submission.Work.Modular.I_pow_div_two
import Submission.Work.Modular.mdifferentiable_S_smul
import Submission.Work.Modular.eq_of_eqOn_imagPoint

namespace Work.Modular

open Work.Modular
open scoped Manifold Real MatrixGroups
open UpperHalfPlane

/-- **From the Gaussian functional equation to the `S`-transformation law.**  If the Gaussian theta
sum of a discrete lattice `L ⊆ ℝⁿ` satisfies the functional equation
`F t = t^{-n/2} F (1/t)` for all `t > 0`, where `F t = ∑_{x ∈ L} exp (-π t ‖x‖²)`, then the theta
series satisfies `Θ_L (-1/τ) = τ^{n/2} Θ_L τ` for every `τ` in the upper half plane.

Both sides are holomorphic on `ℍ` (the left one because `g τ = ∑_{x ∈ L} exp (-π i ‖x‖² / τ)` is a
locally uniformly convergent sum of holomorphic functions), and they agree on the imaginary axis
`τ = i t`, `t > 0`, which has accumulation points; the identity theorem (e.g.
`AnalyticOn.eqOn_of_preconnected_of_eventuallyEq` for the functions composed with
`UpperHalfPlane.ofComplex`, or `MDifferentiable` composition with `UpperHalfPlane.contMDiff_smul`)
then gives the identity on all of `ℍ`.  The hypothesis `8 ∣ n` is used to know `i ^ (n/2) = 1`. -/
theorem thetaSeries_S_smul_of_gaussian {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] (hn : 8 ∣ n)
    (hfun : ∀ t : ℝ, 0 < t →
      (∑' x : L, Complex.exp (-(↑(Real.pi * t * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) : ℂ)))
        = ((t ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
          (∑' x : L, Complex.exp (-(↑(Real.pi / t * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) : ℂ)))) :
    ∀ τ : ℍ, thetaSeries L (ModularGroup.S • τ) = (τ : ℂ) ^ (n / 2) * thetaSeries L τ := by
  have h2 : 2 ∣ n := dvd_trans (by norm_num : (2 : ℕ) ∣ 8) hn
  have hfun' : ∀ t : ℝ, 0 < t →
      gaussSum L t = ((t ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
        (∑' x : L,
          Complex.exp (-(↑(Real.pi / t * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) : ℂ))) := by
    intro t ht
    rw [gaussSum]
    exact hfun t ht
  have hinv := gaussSum_inv_of_functionalEquation L h2 hfun'
  have hfeq : (fun τ : ℍ => thetaSeries L (ModularGroup.S • τ))
      = fun τ : ℍ => (τ : ℂ) ^ (n / 2) * thetaSeries L τ := by
    apply eq_of_eqOn_imagPoint
    · exact (thetaSeries_mdifferentiable L).comp mdifferentiable_S_smul
    · exact ((UpperHalfPlane.mdifferentiable_coe).pow (n / 2)).mul (thetaSeries_mdifferentiable L)
    · intro t ht
      rw [imagPoint_S_smul ht, thetaSeries_imagPoint L (1 / t) (by positivity),
        thetaSeries_imagPoint L t ht, coe_imagPoint ht, mul_pow, ← Complex.ofReal_pow,
        I_pow_div_two hn, mul_one]
      exact hinv t ht
  intro τ
  simpa only using congrFun hfeq τ

end Work.Modular
