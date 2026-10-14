import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.EllPkgClsSliceAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The `z`-slice at `θ = π/4` of a function which is `C^n` on the open quadrant. -/
theorem contDiffOn_slice_pi_div_four {G : ℝ → ℝ → ℝ} {n : ℕ}
    (hG : ContDiffOn ℝ n (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContDiffOn ℝ n (fun z => G z (π / 4)) (Set.Ioi 0) :=
  (hG.comp (((contDiffOn_id : ContDiffOn ℝ n (fun z : ℝ => z) (Set.Ioi 0))).prodMk
    (contDiffOn_const (c := (π / 4)) : ContDiffOn ℝ n (fun _ : ℝ => (π / 4)) (Set.Ioi 0)))
    (fun z hz => ⟨hz, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩)).congr
      (fun z _ => rfl)

/-- The `z`-slice of a function which is `C^n` on the open quadrant. -/
theorem contDiffOn_slice_z {G : ℝ → ℝ → ℝ} {n : ℕ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hG : ContDiffOn ℝ n (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContDiffOn ℝ n (fun z => G z θ) (Set.Ioi 0) :=
  (hG.comp (((contDiffOn_id : ContDiffOn ℝ n (fun z : ℝ => z) (Set.Ioi 0))).prodMk
    (contDiffOn_const (c := θ) : ContDiffOn ℝ n (fun _ : ℝ => θ) (Set.Ioi 0)))
    (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)

/-- The `θ`-slice of a function which is `C^n` on the open quadrant. -/
theorem contDiffOn_slice_t {G : ℝ → ℝ → ℝ} {n : ℕ} {z : ℝ} (hz : z ∈ Set.Ioi 0)
    (hG : ContDiffOn ℝ n (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContDiffOn ℝ n (fun θ => G z θ) (Set.Ioo 0 (π / 2)) :=
  (hG.comp (((contDiffOn_const (c := z) :
      ContDiffOn ℝ n (fun _ : ℝ => z) (Set.Ioo 0 (π / 2)))).prodMk
    (contDiffOn_id : ContDiffOn ℝ n (fun θ : ℝ => θ) (Set.Ioo 0 (π / 2))))
    (fun θ hθ => ⟨hz, hθ⟩)).congr (fun θ _ => rfl)

/-- The `z`-slices of a `SmoothOpen` datum are differentiable on the open half-line. -/
theorem differentiableAt_zslice {G : Fn} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    DifferentiableAt ℝ (fun z' => G z' θ) z := by
  have hs := contDiffOn_slice_z (n := 1) ⟨h0, h1⟩ (hG.forall 1)
  exact (hs.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-- The `θ`-slices of a `SmoothOpen` datum are differentiable on the open interval. -/
theorem differentiableAt_tslice {G : Fn} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => G z θ') θ := by
  have hs := contDiffOn_slice_t (n := 1) hz (hG.forall 1)
  exact (hs.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds ⟨h0, h1⟩)

/-- The `z`-derivative of a difference of `SmoothOpen` data splits. -/
theorem pz_sub {f g : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ)
    (h1 : θ < π / 2) :
    Work.Spaces.pz (fun z θ => f z θ - g z θ) z θ
      = Work.Spaces.pz f z θ - Work.Spaces.pz g z θ := by
  simp only [Work.Spaces.pz]
  rw [show (fun z' => (fun z θ => f z θ - g z θ) z' θ)
        = (fun z' => f z' θ) - (fun z' => g z' θ) from rfl,
    deriv_sub (differentiableAt_zslice hf hz h0 h1) (differentiableAt_zslice hg hz h0 h1)]

/-- The `θ`-derivative of a difference of `SmoothOpen` data splits. -/
theorem pth_sub {f g : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ)
    (h1 : θ < π / 2) :
    Work.Spaces.pth (fun z θ => f z θ - g z θ) z θ
      = Work.Spaces.pth f z θ - Work.Spaces.pth g z θ := by
  simp only [Work.Spaces.pth]
  rw [show (fun θ' => (fun z θ => f z θ - g z θ) z θ')
        = (fun θ' => f z θ') - (fun θ' => g z θ') from rfl,
    deriv_sub (differentiableAt_tslice hf hz h0 h1) (differentiableAt_tslice hg hz h0 h1)]

/-- The `θ`-derivative of a constant multiple of `sin 2θ`. -/
theorem deriv_const_sin_two_mul (c v θ : ℝ) :
    deriv (fun θ' => c * Real.sin (2 * θ') * v) θ = c * (2 * Real.cos (2 * θ)) * v := by
  have h1 : deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = Real.cos (2 * θ) * 2 := by
    have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id θ).const_mul (2 : ℝ)).sin
    exact h.deriv
  have h2 : deriv (fun θ' : ℝ => c * Real.sin (2 * θ')) θ = c * (Real.cos (2 * θ) * 2) := by
    rw [deriv_const_mul _
      (by fun_prop : DifferentiableAt ℝ (fun θ' : ℝ => Real.sin (2 * θ')) θ), h1]
  rw [show (fun θ' => c * Real.sin (2 * θ') * v)
      = fun θ' => (c * Real.sin (2 * θ')) * v from rfl,
    deriv_mul_const
      (by fun_prop : DifferentiableAt ℝ (fun θ' : ℝ => c * Real.sin (2 * θ')) θ) v, h2]
  ring

/-- `Vop` preserves `SmoothOpen`. -/
theorem smoothOpen_Vop {Ψ : Fn} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Spaces.pth Ψ z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.pth hΨ
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hΨ
  exact Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl h1 h2

end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1

/-- The pointwise/Pi identification of the difference of two profiles. -/
theorem sub_apply' (f g : Work.FTS.Galerkin.Fn) :
    (f - g) = fun z θ => f z θ - g z θ := by
  funext z θ; rfl

/-- `ClassC α` is closed under subtraction, in the ambient (Pi-)difference form. -/
theorem classC_sub' {α : ℝ} {f g : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.ClassC.ClassC α f) (hg : Work.FTS.ClassC.ClassC α g) :
    Work.FTS.ClassC.ClassC α (f - g) := by
  rw [sub_apply' f g]
  exact Work.FTS.StrongEps.EComparison.classC_sub hf hg

/-- **The regularity hypotheses of the class descend to the difference.**  If `f` and `g` are both
in `ClassC α` (which is a subspace: `ClassC.classC_add` / `ClassC.classC_smul` / `EComparison.classC_sub`),
then `f - g` is `C^∞` on the open quadrant, honestly in `ℋ⁴`, and it satisfies the
integration-by-parts boundary traces up to order `4`.  The order is lowered from the class's
`ℋ⁷`/`ℋ⁸` and `BdryTraces … 6`/`… 7` because that is all the `ℋ⁴` estimates consume. -/
theorem classC_sub_hyp {α : ℝ} {f g : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.ClassC.ClassC α f) (hg : Work.FTS.ClassC.ClassC α g) :
    Work.FTS.EllipticEst.SmoothOpen (f - g) ∧ Work.Spaces.HkMem α 4 (f - g) ∧
      Work.FTS.Nonlin.BdryTraces α 4 (f - g) :=
  let hsub := classC_sub' hf hg
  ⟨hsub.reg, Work.FTS.ClassC.classC_hkMem_four hsub, hsub.bdry_le_six (by norm_num)⟩

end Work.FTS_RegExport.RXR1
end
