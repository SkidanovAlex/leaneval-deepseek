import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Elliptic.L12Iterate
import Submission.Work.Coercivity.K_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `D_z`-iterates of `L₁₂^K(g)` and their `θ`-coercivity

This module proves `Work.Coercivity.DzRIter_L12f`.  With `D_z = z ∂_z` acting on functions of
`z` alone (`Work.Coercivity.CT.DzRIter`), the *index-raising* identity
`D_z^k L₁₂^K(g) = - ∫_θ K(θ) (D_z^{k-1} g)(·,θ) dθ` holds for every `k ≥ 1`; squaring it and
applying Cauchy–Schwarz in `θ` against the weight `K` gives
`(D_z^k L₁₂^K(g))² ≤ 3 ∫_θ (D_z^{k-1} g)²`.

The identity is the general-`k` form of `Work.Elliptic.L12Iterate` (which states it for
`k ≤ 4`, the range needed by the elliptic estimate `L12H`): the angular moments
`Q_j(z) = ∫_θ K(θ)(D_z^j g)(z,θ)dθ` satisfy `Q_{j+1} = z ∂_z Q_j`
(`Work.Elliptic.Qang_deriv_mul`, proved by differentiating under the `θ`-integral), so the
recursion is formalised here once and for all and then transported to the `Work.Coercivity`
vocabulary through the relabelling bridges `L12f g = Elliptic.L12 g` and
`CT.DzRIter = Elliptic.DzdIter` (both `rfl`).
-/

namespace Work.Coercivity

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Bridges to the `Work.Elliptic` vocabulary -/

/-- `Work.Coercivity.L12f g` is `Work.Elliptic.L12 g` (the same iterated integral of the same
density). -/
theorem DzRIter_L12f_bridge_L12 (g : ℝ → ℝ → ℝ) :
    L12f g = Work.Elliptic.L12 g := by
  funext z; rfl

/-- `CT.DzRIter` (iterates of `D_z` on a radial function) is `Elliptic.DzdIter`. -/
theorem DzRIter_L12f_bridge_DzR (j : ℕ) (R : ℝ → ℝ) :
    CT.DzRIter j R = Work.Elliptic.DzdIter j R := by
  induction j with
  | zero => rfl
  | succ n ih => rw [CT.DzRIter_succ, Work.Elliptic.DzdIter_succ, ih]; rfl

/-- The angular moment `Elliptic.Qang g j z` is the `θ`-integral against `Spaces.K`. -/
theorem DzRIter_L12f_bridge_Qang (g : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Work.Elliptic.Qang g j z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter j g z θ := by
  rw [Work.Elliptic.Qang]
  exact setIntegral_congr_fun measurableSet_Icc
    (fun θ _ => by rw [Work.Elliptic.Ktheta_eq_K])

/-! ## The general index-raising recursion -/

/-- **`D_z^{k+1} L₁₂(g) = -Q_k` for every `k`**: the `(k+1)`-st `D_z`-derivative of
`L₁₂(g)` is the negative of the `k`-th angular moment of `g`.  This is the unrestricted-`k`
form of `Work.Elliptic.L12Iterate`. -/
theorem DzRIter_L12f_DzdIter_L12 (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.L12 g z) (-(Work.Elliptic.L12dens g z)) z) :
    ∀ k : ℕ, ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (Work.Elliptic.L12 g) z = - Work.Elliptic.Qang g k z := by
  intro k
  induction k with
  | zero =>
      intro z hz
      have hd : deriv (Work.Elliptic.L12 g) z = -(Work.Elliptic.L12dens g z) :=
        (hderiv z hz).deriv
      change z * deriv (Work.Elliptic.L12 g) z = - Work.Elliptic.Qang g 0 z
      rw [hd, Work.Elliptic.L12dens_eq_Qang_div]
      have hz0 : z ≠ 0 := ne_of_gt hz
      have hmain : z * (Work.Elliptic.Qang g 0 z / z) = Work.Elliptic.Qang g 0 z := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ (Work.Elliptic.Qang g 0 z) hz0]
      rw [mul_neg]
      exact congrArg Neg.neg hmain
  | succ n ih =>
      intro z hz
      have hev : Work.Elliptic.DzdIter (n + 1) (Work.Elliptic.L12 g)
          =ᶠ[𝓝 z] (fun z' => - Work.Elliptic.Qang g n z') := by
        filter_upwards [Ioi_mem_nhds hz] with z' hz'
        exact ih z' hz'
      have hdv : deriv (Work.Elliptic.DzdIter (n + 1) (Work.Elliptic.L12 g)) z
          = - deriv (fun z' => Work.Elliptic.Qang g n z') z := by
        rw [hev.deriv_eq]
        exact deriv.neg
      change z * deriv (Work.Elliptic.DzdIter (n + 1) (Work.Elliptic.L12 g)) z
          = - Work.Elliptic.Qang g (n + 1) z
      rw [hdv, mul_neg, Work.Elliptic.Qang_deriv_mul g hsm n hz]

/-- The `θ`-integral of `K²` over `Iθ` is at most `3`. -/
theorem DzRIter_L12f_integral_K_sq_le_three :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ ^ 2) ≤ 3 := by
  have h := K_facts
  exact h.2.2.2

/-! ## The theorem -/

theorem DzRIter_L12f (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (hint : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi 0))
    (hcont : ∀ z : ℝ, 0 < z → ContinuousAt (Work.FM.L12dens Work.Spaces.K g) z)
    (j : ℕ) (hj : 1 ≤ j) :
    (∀ z : ℝ, 0 < z → Work.Coercivity.CT.DzRIter j (fun t => Work.Coercivity.L12f g t) z
        = -(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter (j - 1) g z θ))
    ∧ (∀ z : ℝ, 0 < z → (Work.Coercivity.CT.DzRIter j (fun t => Work.Coercivity.L12f g t) z) ^ 2
        ≤ 3 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter (j - 1) g z θ) ^ 2) := by
  -- the `z`-derivative of `L₁₂(g)` from the two analytic hypotheses
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun t => Work.Elliptic.L12 g t) (-(Work.Elliptic.L12dens g z)) z :=
    fun z hz => Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := g) (a := 0) (ρ := z)
      hint (hcont z hz) hz
  -- the general index-raising recursion, transported to the `Coercivity` vocabulary
  have hstep : ∀ z : ℝ, 0 < z →
      CT.DzRIter j (fun t => Work.Coercivity.L12f g t) z = - Work.Elliptic.Qang g (j - 1) z := by
    intro z hz
    conv_lhs => rw [← Nat.sub_add_cancel hj]
    rw [DzRIter_L12f_bridge_DzR]
    rw [show (fun t : ℝ => Work.Coercivity.L12f g t) = Work.Elliptic.L12 g from by
      funext t; rfl]
    exact DzRIter_L12f_DzdIter_L12 g hsm hderiv (j - 1) z hz
  constructor
  · intro z hz
    rw [hstep z hz, DzRIter_L12f_bridge_Qang]
  · intro z hz
    have hcs := Work.Elliptic.Qang_sq_le g hsm (j - 1) (z := z) (by linarith : (-1 : ℝ) < z)
    have hK : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) ≤ 3 := by
      rw [Work.Elliptic.Ktheta_eq_K]
      exact DzRIter_L12f_integral_K_sq_le_three
    rw [hstep z hz, neg_sq]
    calc (Work.Elliptic.Qang g (j - 1) z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter (j - 1) g z θ) ^ 2) := hcs
      _ ≤ 3 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter (j - 1) g z θ) ^ 2) :=
          mul_le_mul_of_nonneg_right hK
            (integral_nonneg (fun θ => sq_nonneg (Work.Spaces.DzIter (j - 1) g z θ)))

end Work.Coercivity
