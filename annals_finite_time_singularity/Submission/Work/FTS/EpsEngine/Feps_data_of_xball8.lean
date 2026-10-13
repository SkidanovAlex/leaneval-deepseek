/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/Feps_data_of_xball8.lean`

The order-`8` companion of `Work.FTS.EpsEngine.Feps_data_of_xball`
(`EpsEngine/FepsData.lean`, the `ℋ⁶`-data of `Feps` on the `XBall` class): there is a constant
`Ce8 > 0`, depending only on `α, ε, C₀, Ce, Cs, R`, such that every `u` in the `XBall` invariant
has

* `SmoothOpen (Feps α ρ ε Φs E u)`,
* `HkMem α 8 (Feps α ρ ε Φs E u)`,
* `HkNorm α 8 (Feps α ρ ε Φs E u) ≤ Ce8`.

The proof is the proof of `Feps_data_of_xball` with two changes:

* the uniform `ℋ⁶`-bound `HkSq_JepsPz_le` of `EpsSqTools` is replaced by its order-`8`
  extension `EpsEngine.HkSq_JepsPz_le8` (`k ≤ 8`);
* the mollified gain `TenOfEight.HkMem_Jeps_gain_pos` is invoked with `k = 4`, `m = 4`
  (instead of `k = 4`, `m = 2`), raising the `ℋ⁴`-honesty of `g := profRHS α Φs E W` to the
  `ℋ⁸`-honesty of `J_ε g`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EpsEngine.FepsData
import Submission.Work.FTS.EpsEngine.HkSq_JepsPz_le8

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
set_option linter.unusedVariables false

/-- **The order-`8` data of `Feps` on the `XBall` class.**  There is a constant `Ce8 > 0`,
depending on `α, ε, C₀, Ce, Cs, R` (but *not* on the profile `u`), such that for every `u` in the
`XBall` invariant the right-hand side `Feps α ρ ε Φs E u` is `SmoothOpen`, `ℋ⁸`-honest, and of
`ℋ⁸`-size at most `Ce8`. -/
theorem Feps_data_of_xball8 {α C₀ Ce Cs R ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) :
    ∃ Ce8 : ℝ, 0 < Ce8 ∧ ∀ u : Work.FTS.Galerkin.Fn,
      Work.FTS.EpsEngine.XBall α ρ ε R C₀ u →
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ∧
      Work.Spaces.HkMem α 8 (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ∧
      Work.Spaces.HkNorm α 8 (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ≤ Ce8 := by
  -- ## the order-`8` counterflow constant of `Pz ∘ J_ε`
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.EpsEngine.HkSq_JepsPz_le8 ρ hρ
  have hratio : 0 ≤ CJ / ε := div_nonneg hCJpos.le hε.le
  -- ## the profile data of `profRHS` and its `ε`-space size (both uniform on the `XBall` class)
  obtain ⟨CX, hCX, hX⟩ :=
    Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀)
      (B := Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R)) (Φs := Φs) (E := E)
      hα hEll hstar hml (Real.sqrt_nonneg _)
  obtain ⟨RP, hRP, hProf⟩ :=
    Work.FTS.StrongEps.EpsRLX.ProfRHSEpsData (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (B := Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R)) (Φs := Φs) (E := E)
      hα hEll hstar hml (Real.sqrt_nonneg _)
  refine ⟨Real.sqrt (CJ * (CJ / ε) ^ (2 * 8) * RP), ?_, ?_⟩
  · exact Real.sqrt_pos.mpr (mul_pos (mul_pos hCJpos (pow_pos (div_pos hCJpos hε) _)) hRP)
  · intro u hu
    -- ## the `XBall` data
    have husmo : Work.FTS.EllipticEst.SmoothOpen u := hu.smoothOpen
    have humem : Work.FTS.StrongEps.EpsMem α u := hu.mem
    have husq : Work.FTS.StrongEps.EpsSq α u ≤ R := hu.sq_le
    have huC : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) :=
      hu.classC
    have huball : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u))
        ≤ C₀ * α ^ 2 := hu.ball
    set W : Fn := Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u) with hWdef
    -- ## the uniform `ℋ⁶`-bound of `W` (order `6 ≤ 8` of the counterflow)
    have hW6 : Work.Spaces.HkNorm α 6 W
        ≤ Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R) := by
      have h := hCJ α hα ε hε hε1 6 (by norm_num) u husmo humem
      have hle : Work.Spaces.HkSq α 6 W ≤ CJ * (CJ / ε) ^ (2 * 6) * R :=
        le_trans h (mul_le_mul_of_nonneg_left husq
          (mul_nonneg hCJpos.le (pow_nonneg hratio _)))
      rw [Work.Spaces.HkNorm]
      exact Real.sqrt_le_sqrt hle
    -- ## the pre-mollified right-hand side
    set g : Fn := Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W with hgdef
    obtain ⟨hgsmo, hgmem4, -⟩ := hX (W := W) huC huball hW6
    obtain ⟨hgmeme, hgsq⟩ := hProf (W := W) huC huball hW6
    have hgsmQuad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hgsmo
    -- ## the mollified gain `ℋ⁴ → ℋ⁸`
    have hJ8 : Work.Spaces.HkMem α 8 (Work.FTS.StrongEps.Jeps ρ ε g) :=
      Work.FTS.StrongEps.TenOfEight.HkMem_Jeps_gain_pos hρ α hα.1 hα.2 4 4 (by norm_num)
        ε hε g hgsmQuad hgmem4
    have hJsmo : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε g) :=
      Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hgsmQuad
    have hFeps : Feps α ρ ε Φs E u = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g) :=
      rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hFeps]
      exact Work.FTS.EpsEngine.smoothOpen_Pz_of_smoothOpen hJsmo
    · rw [hFeps]
      exact Work.FTS.EpsEngine.HkMem_Pz_of hJsmo hJ8
    · rw [hFeps, Work.Spaces.HkNorm]
      refine Real.sqrt_le_sqrt ?_
      exact (hCJ α hα ε hε hε1 8 (by norm_num) g hgsmo hgmeme).trans
        (mul_le_mul_of_nonneg_left hgsq (mul_nonneg hCJpos.le (pow_nonneg hratio _)))

end Work.FTS.EpsEngine
