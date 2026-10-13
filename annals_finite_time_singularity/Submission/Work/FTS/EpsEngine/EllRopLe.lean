/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/EllRopLe.lean` — the `EllPkgGo` piece of the `Rop` slot

The second input of `Work.FTS.EpsEngine.Rop_block_abs_le_one`: the pointwise bound of the
`EllPkgGo` piece `Rop α (PhiTil α f (E f))` of the `Rop` slot of `EpsDecay`, from the `R`-field of
`Work.FTS.VocabO.EllPkgGo` (`HQo α 4` plus the norm bound `Xn α (Rop α (PhiTil α f (E f))) ≤
Ce · Xn α f`).

The pointwise extraction from `HQo α 4` (`SmoothOpen` + `ℋ⁴`-honesty) plus a norm bound is taken as
the hypothesis `hpt`, instantiating the proved
`Work.FTS_RegExport.RXT.hkMem_pointwise_min`
(`|D_z^bD_θ^a g z θ| ≤ Cpt · min z 1 · HkNorm α 4 g` for `a + b ≤ 2`, no boundary traces); keeping
it abstract avoids importing the RXT chapter here.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.ClassC.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false

/-- **The `EllPkgGo` piece of the `Rop` slot.** -/
theorem ell_Rop_le {α Ce Cpt : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpt : 0 ≤ Cpt)
    (hpt : ∀ g : Fn, ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 g → ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
        θ < Real.pi / 2 →
        |Work.Spaces.mixed b a g z θ| ≤ Cpt * min z 1 * Work.Spaces.HkNorm α 4 g)
    {f : Fn} {E : Fn → Fn} (hf : Work.FTS.ClassC.ClassC α f)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ|
      ≤ Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 := by
  have hR : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f))) := (hEll f hf).1.R.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f))) := hR.1
  have hmem : Work.Spaces.HkMem α 4
      (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f))) := hR.2
  have h4 : ContDiffOn ℝ 4
      (Function.uncurry (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f))))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm 4
  have h := hpt _ h4 hmem 0 0 (by norm_num) z θ hz hθ.1 hθ.2
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right, Work.Spaces.DthIter_zero,
    Work.Spaces.DzIter_zero] at h
  refine h.trans ?_
  have hmin : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hXn : Work.FTS.Nonlin.Xn α
      (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f))) ≤ Ce * Work.FTS.Nonlin.Xn α f :=
    (hEll f hf).1.R.2
  calc Cpt * min z 1 * Work.Spaces.HkNorm α 4
        (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)))
      = Cpt * min z 1 * Work.FTS.Nonlin.Xn α
          (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f))) := by
        rw [Work.FTS.Nonlin.Xn]
    _ ≤ Cpt * min z 1 * (Ce * Work.FTS.Nonlin.Xn α f) := by
        refine mul_le_mul_of_nonneg_left hXn (by positivity)
    _ = Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 := by ring

end Work.FTS.EpsEngine
