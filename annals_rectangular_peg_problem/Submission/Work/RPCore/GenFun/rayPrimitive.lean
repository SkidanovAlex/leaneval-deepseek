import Mathlib
import Submission.Work.RPCore.GenFun.Basic
import Submission.Work.RPCore.GenFun.dotB_exists
import Submission.Work.RPCore.GenFun.hasFDerivAt_integrand
import Submission.Work.RPCore.GenFun.integral_smul_fderiv_add
import Submission.Work.RPCore.GenFun.exists_bound_integrand

/-!
# The radial primitive of a curl-free vector field

`rayPrimitive` is the "potential from a closed 1-form" step of the generating-function route:
if `b : PS → PS` is `C³` and its derivative is symmetric with respect to the coordinate scalar
product `dot` (equivalently, the 1-form `v ↦ dot (b y) v` is closed), then

`W y = ∫ t in 0..1, dot (b (t • y)) y`

is a `C³` primitive of that 1-form, i.e. `fderiv ℝ W y = dotL (b y)` for every `y`.

The proof is the classical computation of the radial primitive.  Writing `B` for the continuous
bilinear form `dot` (`Work.RPCore.GenFun.dotB_exists`), differentiation under the integral sign
gives, at `y` and in direction `h`,

`D W(y) h = ∫ t in 0..1, (B (fderiv ℝ b (t•y) (t•h)) y + B (b (t•y)) h) dt`.

Symmetry of `fderiv ℝ b` with respect to `B` (`hclosed`) turns the first term into
`t * B (fderiv ℝ b (t•y) y) h`, so the integrand is
`B (t • fderiv ℝ b (t•y) y + b (t•y)) h = B (d/dt (t • b (t•y))) h`, and the fundamental theorem of
calculus over `[0,1]` gives `B (b y) h`.  Finally `fderiv ℝ W = fun y => B (b y)` is `C²`, so by
`contDiff_succ_iff_fderiv` the function `W` itself is `C³`.
-/

set_option autoImplicit false

noncomputable section

open Work.RPV

namespace Work.RPCore.GenFun

theorem rayPrimitive (b : Work.RPV.PS → Work.RPV.PS) (hb : ContDiff ℝ 3 b)
    (hclosed : ∀ y u v, Work.RPCore.GenFun.dot (fderiv ℝ b y u) v =
      Work.RPCore.GenFun.dot (fderiv ℝ b y v) u) :
    ContDiff ℝ 3 (fun y : Work.RPV.PS =>
        ∫ t in (0 : ℝ)..1, Work.RPCore.GenFun.dot (b (t • y)) y) ∧
    ∀ y : Work.RPV.PS,
      fderiv ℝ (fun y : Work.RPV.PS =>
        ∫ t in (0 : ℝ)..1, Work.RPCore.GenFun.dot (b (t • y)) y) y =
      Work.RPCore.GenFun.dotL (b y) := by
  -- `B` is the coordinate scalar product `dot` viewed as a continuous bilinear form.
  obtain ⟨B, hB, -⟩ := dotB_exists
  have hBclosed : ∀ y u v, B (fderiv ℝ b y u) v = B (fderiv ℝ b y v) u := by
    intro y u v
    rw [hB, hB]
    exact hclosed y u v
  have hdotL : ∀ u : Work.RPV.PS, B u = Work.RPCore.GenFun.dotL u := fun u =>
    ContinuousLinearMap.ext (fun v => by rw [hB, Work.RPCore.GenFun.dotL_apply])
  have hBcont : Continuous fun p : Work.RPV.PS × Work.RPV.PS => B p.1 p.2 :=
    (ContinuousLinearMap.isBoundedBilinearMap B).continuous
  have hfdcont : Continuous (fderiv ℝ b) := hb.continuous_fderiv (by norm_num)
  -- continuity in `t` of the integrand, and of the integrand's claimed derivative
  have hcont_integrand : ∀ x : Work.RPV.PS,
      Continuous fun t : ℝ => B (b (t • x)) x := by
    intro x
    exact hBcont.comp (((hb.continuous.comp (continuous_id.smul continuous_const)).prodMk
      continuous_const))
  have hcont_deriv : ∀ x : Work.RPV.PS,
      Continuous fun t : ℝ => t • fderiv ℝ b (t • x) x + b (t • x) := by
    intro x
    have h1 : Continuous fun t : ℝ => t • fderiv ℝ b (t • x) x :=
      continuous_id.smul ((hfdcont.comp (continuous_id.smul continuous_const)).clm_apply
        continuous_const)
    exact h1.add (hb.continuous.comp (continuous_id.smul continuous_const))
  -- the value of the derivative of the radial integral, computed by the FTC
  have hint_eq : ∀ y₀ : Work.RPV.PS,
      (∫ t in (0 : ℝ)..1, B (t • fderiv ℝ b (t • y₀) y₀ + b (t • y₀))) = B (b y₀) := by
    intro y₀
    rw [ContinuousLinearMap.intervalIntegral_comp_comm B
      ((hcont_deriv y₀).intervalIntegrable 0 1)]
    congr 1
    exact integral_smul_fderiv_add b (hb.of_le (by norm_num)) y₀
  -- differentiation under the integral sign
  have hG : ∀ y₀ : Work.RPV.PS,
      HasFDerivAt (fun y : Work.RPV.PS => ∫ t in (0 : ℝ)..1, B (b (t • y)) y)
        (B (b y₀)) y₀ := by
    intro y₀
    obtain ⟨bound, hbound_int, hbound⟩ := exists_bound_integrand B b hb y₀
    exact (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := MeasureTheory.volume) (a := 0) (b := 1) (s := Metric.closedBall y₀ 1) (x₀ := y₀)
      (F := fun y t => B (b (t • y)) y)
      (F' := fun y t => B (t • fderiv ℝ b (t • y) y + b (t • y)))
      (bound := bound)
      (Metric.closedBall_mem_nhds y₀ one_pos)
      (Filter.Eventually.of_forall (fun x => (hcont_integrand x).aestronglyMeasurable))
      ((hcont_integrand y₀).intervalIntegrable 0 1)
      ((B.continuous.comp (hcont_deriv y₀)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun t ht x hx => hbound t ht x hx))
      hbound_int
      (Filter.Eventually.of_forall
        (fun t _ x _ => hasFDerivAt_integrand B b hb hBclosed t x))).congr_fderiv
      (hint_eq y₀)
  -- smoothness: the derivative is `C²`, hence the function is `C³`
  have hGsm : ContDiff ℝ 3 (fun y : Work.RPV.PS => ∫ t in (0 : ℝ)..1, B (b (t • y)) y) := by
    refine (contDiff_succ_iff_fderiv (𝕜 := ℝ)
      (f := fun y : Work.RPV.PS => ∫ t in (0 : ℝ)..1, B (b (t • y)) y) (n := 2)).mpr
      ⟨?_, ?_, ?_⟩
    · exact fun y => (hG y).differentiableAt
    · intro h; exact absurd h (by norm_num)
    · rw [funext (fun y => (hG y).fderiv)]
      exact (B.contDiff.comp hb).of_le (by norm_num)
  -- transfer from `B` back to `dot` and `dotL`
  have hfun : (fun y : Work.RPV.PS => ∫ t in (0 : ℝ)..1, B (b (t • y)) y)
      = (fun y : Work.RPV.PS =>
          ∫ t in (0 : ℝ)..1, Work.RPCore.GenFun.dot (b (t • y)) y) := by
    funext y
    simp only [hB]
  exact ⟨hfun ▸ hGsm, fun y => by
    rw [show (fun y : Work.RPV.PS =>
          ∫ t in (0 : ℝ)..1, Work.RPCore.GenFun.dot (b (t • y)) y)
        = (fun y : Work.RPV.PS => ∫ t in (0 : ℝ)..1, B (b (t • y)) y) from hfun.symm]
    rw [(hG y).fderiv]
    exact hdotL (b y)⟩

end Work.RPCore.GenFun
