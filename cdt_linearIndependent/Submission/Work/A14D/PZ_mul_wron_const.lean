import Mathlib
import Submission.Work.A14D.setup

/-!
# The Wronskian identity `PZ · wron u v = const` for solutions of `LZ`

For the self-adjoint Zagier operator `LZ f = PZ · f'' + PZ' · f' + RZ · f` (with
`PZ = z(1−z)(1−9z)`, `PZ' = 1 − 20z + 27z²`), two solutions `u, v` of `LZ = 0` on an open
preconnected set `U` have Wronskian `wron u v = u v' − u' v` satisfying

`PZ · wron u v = const` on `U`.

This is Abel's identity in normal form: writing the equation as `y'' + (PZ'/PZ) y' + (RZ/PZ) y = 0`,
the Wronskian obeys `W' = −(PZ'/PZ) W`, i.e. `(PZ · W)' = 0`.  The proof is therefore the
elementary computation `(PZ · wron u v)' = 0` on `U`, followed by
`IsOpen.exists_is_const_of_deriv_eq_zero`.

The only ingredient that is not a one-liner is `deriv PZ = PZ'` (`deriv_PZ` below), proved by
identifying `PZ` with the evaluation of a polynomial.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-- The derivative of the polynomial `PZ z = z(1−z)(1−9z)` is `PZ' z = 1 − 20z + 27z²`. -/
lemma deriv_PZ (z : ℂ) : deriv PZ z = PZ' z := by
  have hfun : PZ = fun w : ℂ =>
      (Polynomial.X - 10 * Polynomial.X ^ 2 + 9 * Polynomial.X ^ 3 : Polynomial ℂ).eval w := by
    funext w
    simp only [PZ, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
    ring
  rw [hfun, Polynomial.deriv]
  simp only [PZ', Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_ofNat, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_C, Polynomial.eval_zero, Polynomial.eval_one]
  ring

/-- **Wronskian identity.**  Two solutions of `LZ = 0` on an open preconnected set `U` have
`PZ · wron u v` constant on `U`.  (Abel's identity in normal form.) -/
theorem PZ_mul_wron_const {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    {u v : ℂ → ℂ} (hu : DifferentiableOn ℂ u U) (hv : DifferentiableOn ℂ v U)
    (huode : ∀ z ∈ U, LZ u z = 0) (hvode : ∀ z ∈ U, LZ v z = 0) :
    ∃ C : ℂ, ∀ z ∈ U, PZ z * wron u v z = C := by
  -- `deriv u`, `deriv v` and the Wronskian are holomorphic on the open set `U`
  have hu' : DifferentiableOn ℂ (deriv u) U := hu.deriv hUo
  have hv' : DifferentiableOn ℂ (deriv v) U := hv.deriv hUo
  have hw : DifferentiableOn ℂ (wron u v) U := by
    unfold wron
    exact (hu.mul hv').sub (hu'.mul hv)
  have hPZ : DifferentiableOn ℂ PZ U := by unfold PZ; fun_prop
  -- so is the function whose constancy we want
  have hF : DifferentiableOn ℂ (fun z => PZ z * wron u v z) U := hPZ.mul hw
  -- its derivative vanishes on `U`
  have hF' : Set.EqOn (deriv (fun z => PZ z * wron u v z)) 0 U := by
    intro z hz
    have hz' : U ∈ nhds z := hUo.mem_nhds hz
    have hPZz : DifferentiableAt ℂ PZ z := by unfold PZ; fun_prop
    have hwz : DifferentiableAt ℂ (wron u v) z := hw.differentiableAt hz'
    have hud : DifferentiableAt ℂ u z := hu.differentiableAt hz'
    have hvd : DifferentiableAt ℂ v z := hv.differentiableAt hz'
    have hudd : DifferentiableAt ℂ (deriv u) z := hu'.differentiableAt hz'
    have hvdd : DifferentiableAt ℂ (deriv v) z := hv'.differentiableAt hz'
    -- the derivative of the Wronskian
    have hderivW : deriv (wron u v) z
        = u z * deriv (deriv v) z - deriv (deriv u) z * v z := by
      change deriv ((u * deriv v) - (deriv u * v)) z
        = u z * deriv (deriv v) z - deriv (deriv u) z * v z
      rw [deriv_sub (hud.mul hvdd) (hudd.mul hvd),
        deriv_mul hud hvdd, deriv_mul hudd hvd]
      ring
    -- the product rule for `PZ · wron u v`
    have hprod : deriv (fun z => PZ z * wron u v z) z
        = PZ' z * wron u v z + PZ z * deriv (wron u v) z := by
      change deriv (PZ * wron u v) z = _
      rw [deriv_mul hPZz hwz, deriv_PZ z]
    rw [hprod, hderivW]
    -- rewrite the second derivatives using `LZ u = LZ v = 0`
    have hLu := huode z hz
    have hLv := hvode z hz
    rw [LZ_def] at hLu hLv
    have e1 : PZ z * deriv (deriv u) z = -(PZ' z * deriv u z + RZ z * u z) := by
      linear_combination hLu
    have e2 : PZ z * deriv (deriv v) z = -(PZ' z * deriv v z + RZ z * v z) := by
      linear_combination hLv
    rw [wron, show PZ z * (u z * deriv (deriv v) z - deriv (deriv u) z * v z)
        = u z * (PZ z * deriv (deriv v) z) - v z * (PZ z * deriv (deriv u) z) by ring,
      e2, e1]
    simp only [Pi.zero_apply]
    ring
  exact IsOpen.exists_is_const_of_deriv_eq_zero hUo hUc hF hF'

end

end Work.A14D
