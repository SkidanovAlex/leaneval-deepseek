/-
Copyright: work module for the Elgindi finite-time singularity project.

# The index-raising recursion `D_z^k L₁₂(g) = -Q_{k-1}` (tex 1276--1290)

For `g` smooth on a neighbourhood of the closed quadrant, the angular moments
`Q_j(z) = ∫_θ K(θ) · (D_z^j g)(z,θ) dθ` of `Work.Elliptic.Qang` satisfy
`Q_{j+1}(z) = z · ∂_z Q_j(z)`, because `D_z = z ∂_z` and differentiation may be brought
under the `θ`-integral (`hasDerivAt_integral_Iθ`).  Combining this with the defining
property `∂_z L₁₂(g) = -L₁₂dens g = -Q_0/z` of `L₁₂` gives, by induction on `k`,

  `D_z^k L₁₂(g)(z) = -Q_{k-1}(z)`

for every `k ≥ 1` (the statement below only asks for `k ≤ 4`, which is all the elliptic
estimate `L12H` uses).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Elliptic.PsiStar_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- `SmoothNbhd` is inherited by the iterated `D_z`-derivatives. -/
lemma smoothNbhd_DzIter {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g) (j : ℕ) :
    Work.Spaces.SmoothNbhd (Work.Spaces.DzIter j g) := by
  simpa [Work.Spaces.SmoothNbhd, Work.Spaces.nbhU] using contDiffOn_uncurry_DzIter_nbhU hsm j

/-- **Differentiation under the integral sign for the angular moment.**  The angular
moments `Q_j` are raised by the operator `D_z = z∂_z`: `Q_{j+1}(z) = z · ∂_z Q_j(z)`.

The `z`-derivative is brought inside the `θ`-integral with `hasDerivAt_integral_Iθ`, whose
domination hypothesis is supplied by the smoothness of `D_z^j g` on a neighbourhood of the
closed quadrant (the `θ`-interval is compact). -/
theorem Qang_deriv_mul (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) (j : ℕ) {z : ℝ}
    (hz : 0 < z) :
    z * deriv (fun z' => Qang g j z') z = Qang g (j + 1) z := by
  have hsm' : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter j g) := smoothNbhd_DzIter hsm j
  have hcontK : ContinuousOn Ktheta (Set.Icc 0 (π / 2)) := by
    unfold Ktheta
    exact ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn
  have h := hasDerivAt_integral_Iθ (Work.Spaces.DzIter j g) Ktheta hsm' hcontK
    (by linarith : (-1 : ℝ) < z)
  -- identify the differentiated function with `Qang g j`
  have hfun : ∀ z' : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter j g z' θ * Ktheta θ) = Qang g j z' := by
    intro z'
    unfold Qang
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)
  have hderiv : deriv (fun z' => Qang g j z') z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j g) z θ * Ktheta θ := by
    have h2 : (fun z' => Qang g j z')
        = (fun z' => ∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter j g z' θ * Ktheta θ) :=
      funext fun z' => (hfun z').symm
    rw [h2, h.deriv]
  rw [hderiv, ← MeasureTheory.integral_const_mul]
  unfold Qang
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [show Work.Spaces.DzIter (j + 1) g = Work.Spaces.Dz (Work.Spaces.DzIter j g) from
    Work.Spaces.DzIter_succ j g]
  simp only [Work.Spaces.Dz]
  ring

/-- **`D_z^k L₁₂(g) = -Q_{k-1}` for `1 ≤ k ≤ 4`** (tex 1276--1290): the `k`-th `D_z`-derivative
of `L₁₂(g)` is the negative of the `(k-1)`-st angular moment of `g`. -/
theorem L12Iterate (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.L12 g z) (-(Work.Elliptic.L12dens g z)) z)
    {k : ℕ} (hk : 1 ≤ k) (hk4 : k ≤ 4) {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    Work.Spaces.DzIter k (fun z θ => Work.Elliptic.L12 g z) z θ = - Work.Elliptic.Qang g (k - 1) z := by
  -- the general recursion, valid for every `k ≥ 1`
  have hgen : ∀ k : ℕ, ∀ z : ℝ, 0 < z →
      DzdIter (k + 1) (L12 g) z = - Qang g k z := by
    intro k
    induction k with
    | zero =>
        intro z hz
        have hd : deriv (L12 g) z = -(L12dens g z) := (hderiv z hz).deriv
        change z * deriv (L12 g) z = - Qang g 0 z
        rw [hd, L12dens_eq_Qang_div]
        have hz0 : z ≠ 0 := ne_of_gt hz
        have hmain : z * (Qang g 0 z / z) = Qang g 0 z := by
          rw [← mul_div_assoc, mul_div_cancel_left₀ (Qang g 0 z) hz0]
        rw [mul_neg]
        exact congrArg Neg.neg hmain
    | succ n ih =>
        intro z hz
        have hev : DzdIter (n + 1) (L12 g) =ᶠ[𝓝 z] (fun z' => - Qang g n z') := by
          filter_upwards [Ioi_mem_nhds hz] with z' hz'
          exact ih z' hz'
        have hdv : deriv (DzdIter (n + 1) (L12 g)) z
            = - deriv (fun z' => Qang g n z') z := by
          rw [hev.deriv_eq]
          exact deriv.neg
        change z * deriv (DzdIter (n + 1) (L12 g)) z = - Qang g (n + 1) z
        rw [hdv, mul_neg, Qang_deriv_mul g hsm n hz]
  have hrad : Work.Spaces.DzIter k (fun z θ => L12 g z) z θ = DzdIter k (L12 g) z :=
    DzIter_rad (L12 g) k z θ
  rw [hrad]
  have h1 : DzdIter (k - 1 + 1) (L12 g) z = - Qang g (k - 1) z := hgen (k - 1) z hz
  rwa [Nat.sub_add_cancel hk] at h1

end Work.Elliptic
