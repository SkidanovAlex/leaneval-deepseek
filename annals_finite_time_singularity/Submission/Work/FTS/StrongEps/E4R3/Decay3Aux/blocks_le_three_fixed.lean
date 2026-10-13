/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/StrongEps/E4R3/Decay3Aux/blocks_le_three_fixed.lean` — the (D2) block leaf, **repaired**

The lemma requested at `FTS/StrongEps/E4R3/Decay3Aux/blocks_le_three` is **ill-typed as filed**:
its third conjunct reads

    |Work.Construction.Vop α (Work.Construction.PhiTil α f (…)) z θ| ≤ 3

but in this workspace `Work.Construction.Vop` takes **one** explicit argument, the profile
(`def Vop (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ`, `Submission/Work/Construction/Defs.lean:102`) — unlike
its siblings `Rop` and `Uop`, which *do* take `α` (`Rop (α) (Ψ)`, `Uop (α) (Ψ)`).  Hence the
requested file does not even elaborate:

    error: …/blocks_le_three.lean:31:29: Application type mismatch: The argument α has type ℝ
    but is expected to have type ℝ → ℝ → ℝ in the application Construction.Vop α

The typo is *only* the extra `α`: the independent review record of that same path
(`.fm3_reviews.json`, entry of 2026-10-12T09:08:20) carries the statement without it, and the
consumer of the leaf, `Submission/Work/FTS/StrongEps/E4R3/BlocksLe3D2.lean` (i.e.
`EpsE4Thr.E4R3.blocksLe3_D2`), also writes `Work.Construction.Vop (Work.Construction.PhiTil α W …)`.

This module proves the statement **with the extra `α` deleted** (same name, hypotheses, order of
conjuncts; the declaration is renamed `blocks_le_three_fixed` so that it cannot clash with the
repaired restatement at the original path).  It is `sorry`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## Route

Nothing new is needed: the three block estimates already exist in `EpsEngine` with `Cpt` as a
*parameter* (`ell_Rop_le`, `uop_slot_abs_le_three`, `vop_slot_abs_le_three`), and the only residual
input of those, the block *decomposition* identity, is produced by `Rop_block_decomp` /
`Uop_div_decomp` / `Vop_decomp` from the eight slice-differentiability facts supplied by
`EpsEngine.BlocksDecompDiffAt` out of `ClassC.reg`/`ClassC.mem` (descended to `ℋ⁴`),
`EllPkgGo.smooth` and `StarPkgo2.smooth`.  This is verbatim the assembly of
`EpsE4Thr/BlocksQuadrant.lean`, except that the constant `Cpt` is *given* (with its `hpt` and its
`hsmall : … ≤ 1/4`) instead of being extracted existentially from `RXT.hkMem_pointwise_min` — which
is what the (D2) leaf `BlocksLe3D2` needs in order to expose the explicit `Cpt(α) = O(α^{-1/2})`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EpsEngine.BlocksConcrete
import Submission.Work.FTS.EpsEngine.BlocksDecompDiffAt
import Submission.Work.FTS.EpsEngine.RopBlockDecomp
import Submission.Work.FTS.StrongEps.EpsE4Thr.BlocksQuadrant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Decay3Aux

theorem blocks_le_three_fixed {α Ce Cs C₀ Cpt : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) (hC₀ : 0 ≤ C₀) (hCpt : 0 ≤ Cpt)
    {f : Work.FTS.Galerkin.Fn} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hpt : ∀ g : Work.FTS.Galerkin.Fn,
      ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 g → ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
        θ < Real.pi / 2 →
        |Work.Spaces.mixed b a g z θ| ≤ Cpt * min z 1 * Work.Spaces.HkNorm α 4 g)
    (hsmall : Cpt * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1 / 4)
    (hf : Work.FTS.ClassC.ClassC α f) (hball : Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.Construction.Rop α (Work.Construction.PhiTil α f
          (fun z θ => Φs z θ + E f z θ)) z θ| ≤ 3 ∧
      |Work.Construction.Uop α (Work.Construction.PhiTil α f
          (fun z θ => Φs z θ + E f z θ)) z θ / Work.Construction.s2 θ| ≤ 3 ∧
      |Work.Construction.Vop (Work.Construction.PhiTil α f
          (fun z θ => Φs z θ + E f z θ)) z θ| ≤ 3 := by
  intro z θ hz hθ
  -- `ℋ⁴`-honesty of `f` from the class's `ℋ⁷`-honesty
  have h4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hf.reg hf.mem
  -- the eight slice-differentiability inputs of the three decompositions
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ :=
    Work.FTS.EpsEngine.BlocksDecompDiffAt hα hα1 hz hθ.1 hθ.2 hf.reg h4
      (hEll f hf).1.smooth hstar.smooth
  -- upgrading the `EllPkgGo` piece from `Xn α f` to `C₀ α²`
  have hup : ∀ X : ℝ,
      |X| ≤ Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 →
      |X| ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 := by
    intro X hX
    refine hX.trans ?_
    have h1 : Ce * Work.FTS.Nonlin.Xn α f ≤ Ce * (C₀ * α ^ 2) :=
      mul_le_mul_of_nonneg_left hball hCe
    have h2 : 0 ≤ min z 1 := le_min hz.le zero_le_one
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCpt) h2
  refine ⟨?_, ?_, ?_⟩
  · -- the `Rop` slot
    have hE := hup _ (Work.FTS.EpsEngine.ell_Rop_le hα hα1 hCpt hpt hf hEll hz hθ)
    have hS := Work.FTS.EpsEngine.star_Rop_le hstar z θ hz hθ.1 hθ.2
    have hdec := Work.FTS.EpsEngine.Rop_block_decomp d1 d2 d3 d4 d5 d6 d7 d8
    exact le_trans (Work.FTS.EpsEngine.Rop_block_abs_le_one hα hα1 hz hθ hCpt hCe hCs hC₀
      hsmall hdec hE hS) (by norm_num)
  · -- the `Uop / sin 2θ` slot
    have hE := hup _ (Work.FTS.EpsEngine.ell_Uop_le hα hα1 hCpt hpt hf hEll hz hθ)
    have hS := Work.FTS.EpsEngine.star_Uop_div_le hα hCs hstar z θ hz hθ.1 hθ.2
    have hdec := Work.FTS.EpsEngine.Uop_div_decomp d1 d2 d3 d4 d5 d6 d7 d8
    exact Work.FTS.EpsEngine.uop_slot_abs_le_three hα hα1 hz hθ hCpt hCe hCs hC₀
      (by linarith) hdec hE hS
  · -- the `Vop` slot
    have hE := hup _ (Work.FTS.EpsEngine.ell_Vop_le hα hα1 hCpt hpt hf hEll hz hθ)
    have hS := Work.FTS.EpsEngine.star_Vop_le hstar z θ hz hθ.1 hθ.2
    have hdec := Work.FTS.EpsEngine.Vop_decomp d1 d2 d3 d4 d5 d6 d7 d8
    exact Work.FTS.EpsEngine.vop_slot_abs_le_three hα hα1 hz hθ hCpt hCe hCs hC₀
      (by linarith) hdec hE hS

end Work.FTS.StrongEps.E4R3.Decay3Aux
