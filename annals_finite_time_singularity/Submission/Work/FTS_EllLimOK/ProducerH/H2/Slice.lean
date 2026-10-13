/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ProducerH.H2.Slice` — the angular slice of `E g` on the closed interval

Two facts about the `θ`-slice `θ ↦ (E g) z θ` at a fixed radius `z > 0`, for `g` of the source
class and `Ψ = E g` carrying the level-`8` existence class:

* `sliceOde` — the slice solves the `Lzero`-ODE
  `S'' = tan θ · S' + (cos θ)⁻² · S − 6 S − Lzero Ψ z` on `(0,π/2)`;
* `sliceContinuousOn` — the slice is continuous on the *closed* interval `[0,π/2]`, because the
  prescribed (junk) boundary values `0` are the one-sided limits
  (`BoxAux.tendsto_Eg_at_zero`, `BoxAux.tendsto_Eg_at_pi_half`).

This is a compiling replacement of the two lemmas of
`ProducerH/BoxAux/Th2Aux/Setup.lean` (that module does not compile: its endpoint-membership
argument for `π/2` uses `le_of_lt hx.2` where `hx.2.2` is meant).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The angular slice of `E g` solves the `Lzero`-ODE.**  For `Ψ = E g` and
`G = Lzero Ψ z`,

  `S'' = tan θ · S' + (cos θ)⁻² · S − 6 S − G`   on `(0,π/2)`.

This carries no elliptic information: the source `G` is *defined* by this equation. -/
theorem sliceOde {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {E : Fn →ₗ[ℝ] Fn}
    (hE : Ctx α Ce E) {g : Fn} (hg : Work.FTS.ClassC.ClassC α g) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Set.Ioo 0 (π / 2),
      deriv (deriv (fun θ' => (E g) z θ')) θ
        = Real.tan θ * deriv (fun θ' => (E g) z θ') θ
          + ((Real.cos θ) ^ 2)⁻¹ * (E g) z θ - 6 * (E g) z θ
          - Work.Elliptic.Lzero (E g) z θ := by
  have hSsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).1.2.1
  have h2 : ContDiffOn ℝ 2 (fun θ' => (E g) z θ') (Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.SmoothOpen.curry_θ hSsm hz).of_le (by norm_num)
  have hLfun : Work.Elliptic.Lzero (E g) z
      = fun θ => -deriv (deriv (fun θ' => (E g) z θ')) θ
          + deriv (fun θ' => Real.tan θ' * (E g) z θ') θ - 6 * (E g) z θ := by
    funext θ'
    simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Work.Spaces.pth]
  intro θ hθ
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hSd : HasDerivAt (fun θ'' => (E g) z θ'')
      (deriv (fun θ'' => (E g) z θ'') θ) θ :=
    (((h2.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num))).hasDerivAt
  have htan : HasDerivAt Real.tan (((Real.cos θ) ^ 2)⁻¹) θ := by
    simpa only [one_div] using Real.hasDerivAt_tan (ne_of_gt hcos)
  have hprod : deriv (fun θ'' => Real.tan θ'' * (E g) z θ'') θ
      = ((Real.cos θ) ^ 2)⁻¹ * (E g) z θ
        + Real.tan θ * deriv (fun θ'' => (E g) z θ'') θ :=
    (htan.mul hSd).deriv
  have hL := congrFun hLfun θ
  rw [hL, hprod]
  ring

/-- **The slice `θ ↦ (E g) z θ` is continuous on `[0,π/2]`**: on the open interval by
`SmoothOpen`, at the endpoints because the prescribed (junk) values `0` are the one-sided
limits (`BoxAux.tendsto_Eg_at_zero`, `BoxAux.tendsto_Eg_at_pi_half`). -/
theorem sliceContinuousOn {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {E : Fn →ₗ[ℝ] Fn}
    (hE : Ctx α Ce E) {g : Fn} (hg : Work.FTS.ClassC.ClassC α g) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => (E g) z θ) (Set.Icc 0 (π / 2)) := by
  have hSsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).1.2.1
  have hcontIoo : ContinuousOn (fun θ => (E g) z θ) (Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.SmoothOpen.curry_θ hSsm hz).continuousOn
  have hval0 : (E g) z 0 = 0 := (hE g hg).1.1.2.1 z
  have hval1 : (E g) z (π / 2) = 0 := (hE g hg).1.1.2.2.1 z
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    have hIci : ContinuousWithinAt (fun θ => (E g) z θ) (Set.Ici 0) 0 := by
      rw [← continuousWithinAt_Ioi_iff_Ici]
      show Tendsto (fun θ => (E g) z θ) (𝓝[Set.Ioi 0] 0) (𝓝 ((E g) z 0))
      rw [hval0]
      exact Work.FTS_EllLimOK.ProducerH.BoxAux.tendsto_Eg_at_zero hα hα4 hE hg hz
    have hmem : Set.Ici (0 : ℝ) ∈ 𝓝[Set.Icc 0 (π / 2)] 0 := by
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨Set.Ioo (-1) (π / 2 + 1), ?_, ?_⟩
      · exact Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
          (show (0 : ℝ) < π / 2 + 1 by linarith [Real.pi_pos])
      · intro x hx
        exact hx.2.1
    exact ContinuousWithinAt.mono_of_mem_nhdsWithin (s := Set.Icc 0 (π / 2))
      (t := Set.Ici 0) hIci hmem
  · rcases eq_or_lt_of_le hθ.2 with hp | hp
    · subst hp
      have hIic : ContinuousWithinAt (fun θ => (E g) z θ) (Set.Iic (π / 2)) (π / 2) := by
        rw [← continuousWithinAt_Iio_iff_Iic]
        show Tendsto (fun θ => (E g) z θ) (𝓝[Set.Iio (π / 2)] (π / 2)) (𝓝 ((E g) z (π / 2)))
        rw [hval1]
        exact Work.FTS_EllLimOK.ProducerH.BoxAux.tendsto_Eg_at_pi_half hα hα4 hE hg hz
      have hmem : Set.Iic (π / 2) ∈ 𝓝[Set.Icc 0 (π / 2)] (π / 2) := by
        refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
          ⟨Set.Ioo (-1) (π / 2 + 1), ?_, ?_⟩
        · exact Ioo_mem_nhds (show (-1 : ℝ) < π / 2 by linarith [Real.pi_pos])
            (show (π / 2) < π / 2 + 1 by linarith)
        · intro x hx
          exact hx.2.2
      exact ContinuousWithinAt.mono_of_mem_nhdsWithin (s := Set.Icc 0 (π / 2))
        (t := Set.Iic (π / 2)) hIic hmem
    · exact ((hcontIoo.continuousWithinAt ⟨h0, hp⟩).continuousAt
        (isOpen_Ioo.mem_nhds ⟨h0, hp⟩)).continuousWithinAt

end Work.FTS_EllLimOK.ProducerH.H2
