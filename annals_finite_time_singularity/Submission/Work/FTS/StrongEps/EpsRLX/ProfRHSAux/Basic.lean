import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.ZeroOrder
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.StreamOps
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzSlot
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCSinRate
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCThetaHolder
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.theta_holder_of_HkMem
import Submission.Work.Stability.ZcutSmoothCompact
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.blocks_le_three_fixed =====
section

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
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Mem4Glue =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The per-`z` bound of the `ℋ⁴`-integrand of the projected family.**  For the sequence
`ε n ∈ (0,1]`, the families `G n`, a fixed fake time `τ` and datum

* the smoothness of the plain slices (`hsm`, all orders on the open quadrant),
* their honest `ℋ⁶`-membership (`hmem6`) and the uniform bound `Xn6 ≤ B` (`hb6`, `0 ≤ B`),
* the class-`C` clause of the *projected* slices (`hC`, an interface conjunct),

there is at every `z ∈ Iz` a bound of the per-`z` θ-integral of `HkIntegrand α 4` of the projected
slice, **uniform in `n`** — exactly the `hz` input of `EpsLimMem4`/`E5_mem4_JfamP`. -/
theorem hz_of_classC_JfamP {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {G : ℕ → Fam} {ε : ℕ → ℝ} {τ : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hB : 0 ≤ B) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (slice (G n) τ)) Quad)
    (hmem6 : ∀ n : ℕ, Work.Spaces.HkMem α 6 (slice (G n) τ))
    (hb6 : ∀ n : ℕ, Work.FTS.StrongGlobal.Xn6 α (slice (G n) τ) ≤ B)
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε n) (G n)) τ)) :
    ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (slice (JfamP ρ (ε n) (G n)) τ) z θ) ≤ Bz := by
  obtain ⟨A, hA0, hA⟩ := HkNorm_JfamP_le (ρ := ρ) hρ
  obtain ⟨C, hC0, hCb⟩ := E5Aux.HkIntegrand_four_perz_le
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB
  refine fun z hz => ⟨C * (1 + (Work.Spaces.w z) ^ 2) * (1 + A * B) ^ 2, fun n => ?_⟩
  have hXn : Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε n) (G n)) τ) ≤ A * B :=
    le_trans (hA hα (hε n) (hsm n) (hmem6 n)).2
      (mul_le_mul_of_nonneg_left (hb6 n) hA0)
  have h1 := hCb α hα (hC n) z hz
  have h2 : (1 + Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε n) (G n)) τ)) ^ 2
      ≤ (1 + A * B) ^ 2 :=
    pow_le_pow_left₀ (by
        simpa using add_nonneg zero_le_one
          (Work.Spaces.HkNorm_nonneg α 6 (slice (JfamP ρ (ε n) (G n)) τ))) (by linarith) 2
  have h3 : 0 ≤ C * (1 + (Work.Spaces.w z) ^ 2) := by positivity
  calc (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (slice (JfamP ρ (ε n) (G n)) τ) z θ)
      ≤ C * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε n) (G n)) τ)) ^ 2 := h1
    _ ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + A * B) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 h3

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
end
end
