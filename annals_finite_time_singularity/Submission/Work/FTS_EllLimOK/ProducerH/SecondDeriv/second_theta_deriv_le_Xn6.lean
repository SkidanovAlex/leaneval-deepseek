import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SliceBound.slice_second_deriv_le
import Submission.Work.FTS_EllLimOK.PkgJets.L12jets_classC
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllExist.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_second_deriv_le_six
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_package_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- The statement uses the scoped notation `π` for `Real.pi`; without this line the identifier
-- `π` is unknown to the parser (the workspace sets `autoImplicit = false`), so the file would
-- not elaborate at all.  This changes nothing in the *statement* below.
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.SecondDeriv

/-!
# The second angular derivative of `E g` is bounded by `Xn₆`

The point of this file: `Work.FTS_EllLimOK.ProducerH.SliceBound.slice_second_deriv_le` says that an
angular slice `S : ℝ → ℝ` of class `C²` on `(0,π/2)` which solves

  `S'' = tan θ · S' + (cos θ)⁻² · S − 6 S − G`     on `(0,π/2)`

with `|S|`, `|sin(2θ)/2 · S' + S|` and `|G|` all bounded by `M`, obeys `|S''| ≤ 6 M`.  We apply
this to the slice `θ ↦ (E g) z θ` of the stream function at a fixed radius `z ∈ [a,b]`, with

  `G = Elliptic.Lzero (E g) z`,  `Lzero Ψ z θ = −∂_θ²Ψ + ∂_θ(tan θ · Ψ) − 6Ψ`,

which by the elliptic law `bslOp α (E g) = g` equals `g z θ + α²z²∂_z²(E g) z θ + α(5+α)z ∂_z(E g) z θ`
— a quantity involving only *radial* derivatives of `E g`, hence bounded pointwise by a multiple of
`Xn₆ α g` on the box `[a,b] × (0,π/2)` (`ProducerH.slice_package_bounds`, from the mixed-jet bound
`ProducerH.MixedJets.mixed_jets_le_Xn6`).

The constant `6` of the slice lemma is used in the *explicit* form
(`ProducerH.slice_second_deriv_le_six`) because it has to be uniform in `z`: the `∃K`-form of the
slice lemma would return a `z`-dependent constant.
-/

theorem second_theta_deriv_le_Xn6 {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ K : ℝ, 0 < K ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
        |deriv (deriv (fun θ' => (E g) z θ')) θ|
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g := by
  obtain ⟨M, hMpos, hM⟩ := slice_package_bounds hα hα4 hE ha hab
  refine ⟨6 * M, by positivity, ?_⟩
  intro g hg z hz θ hθ
  obtain ⟨hz1, hz2⟩ := hz
  have hzpos : 0 < z := lt_of_lt_of_le ha hz1
  have hMnn : 0 ≤ M * Work.FTS.StrongGlobal.Xn6 α g :=
    mul_nonneg hMpos.le (Work.Spaces.HkNorm_nonneg α 6 g)
  -- the open-quadrant smoothness of `E g` gives `C∞` (hence `C²`) of the angular slice
  have hSsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).2.2.smooth
  have h2 : ContDiffOn ℝ 2 (fun θ' => (E g) z θ') (Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.SmoothOpen.curry_θ hSsm hzpos).of_le (by norm_num)
  -- the slice form of `Lzero`
  have hLfun : Work.Elliptic.Lzero (E g) z
      = fun θ => -deriv (deriv (fun θ' => (E g) z θ')) θ
          + deriv (fun θ' => Real.tan θ' * (E g) z θ') θ - 6 * (E g) z θ := by
    funext θ'
    simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Work.Spaces.pth]
  -- the slice ODE, with `G = Lzero (E g) z`
  have heq : ∀ θ' ∈ Set.Ioo 0 (π / 2),
      deriv (deriv (fun θ'' => (E g) z θ'')) θ'
        = Real.tan θ' * deriv (fun θ'' => (E g) z θ'') θ'
          + ((Real.cos θ') ^ 2)⁻¹ * (E g) z θ' - 6 * (E g) z θ'
          - Work.Elliptic.Lzero (E g) z θ' := by
    intro θ' hθ'
    have hcos : 0 < Real.cos θ' :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩
    have hSd : HasDerivAt (fun θ'' => (E g) z θ'')
        (deriv (fun θ'' => (E g) z θ'') θ') θ' :=
      ((h2.contDiffAt (isOpen_Ioo.mem_nhds hθ')).differentiableAt (by norm_num)).hasDerivAt
    have htan : HasDerivAt Real.tan (((Real.cos θ') ^ 2)⁻¹) θ' := by
      simpa only [one_div] using Real.hasDerivAt_tan (ne_of_gt hcos)
    have hprod : deriv (fun θ'' => Real.tan θ'' * (E g) z θ'') θ'
        = ((Real.cos θ') ^ 2)⁻¹ * (E g) z θ'
          + Real.tan θ' * deriv (fun θ'' => (E g) z θ'') θ' :=
      (htan.mul hSd).deriv
    have hL := congrFun hLfun θ'
    rw [hL, hprod]
    ring
  -- the three pointwise bounds on the box
  have hMg := hM g hg z ⟨hz1, hz2⟩
  -- the slice lemma with its explicit constant `6`
  have hkey := slice_second_deriv_le_six (S := fun θ' => (E g) z θ')
      (G := Work.Elliptic.Lzero (E g) z) h2 heq hMnn
      (fun θ' hθ' => (hMg θ' hθ').2.1)
      (fun θ' hθ' => (hMg θ' hθ').1)
      (fun θ' hθ' => (hMg θ' hθ').2.2) θ hθ
  calc |deriv (deriv (fun θ' => (E g) z θ')) θ|
      ≤ 6 * (M * Work.FTS.StrongGlobal.Xn6 α g) := hkey
    _ = (6 * M) * Work.FTS.StrongGlobal.Xn6 α g := by ring

end Work.FTS_EllLimOK.ProducerH.SecondDeriv
