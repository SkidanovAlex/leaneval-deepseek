/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/FepsData.lean` — the `ℋ⁶`-data of the scheme's right-hand side
# `Feps` on the `XBall` class, with (H4)'s `mem`/`bd` fields DISCHARGED

`Work.FTS.EpsEngine.HkMemIterAll` reduced the `(H4)` chapter to the per-curve data
`RHSData α 4 T B F h₀ n` of the right-hand side.  For the scheme's right-hand side
`F = Feps α ρ ε Φs E` (`EpsClass.lean`) several of the seven fields of `RHSData` are about the
*size* of `Feps u`, not about its traces:

* `smo` — `SmoothOpen (Feps u)`,
* `mem` — `HkMem α 4 (Feps u)`,
* `bd`  — `HkNorm α 4 (Feps u) ≤ B`,

and the `perz` field needs, besides the trace data, the `ℋ⁶`-*membership* `HkMem α 6 (Feps u)`
(through `HkIntegrand_perz_RHS` → `HkIntegrand_perz_le_of_traces`).  This module discharges all
four, **uniformly over the `XBall` class**, with no trace hypothesis at all.

The route:

* `W := Pz (J_ε u)` (the projected mollified profile).  `XBall` gives `ClassC α W`,
  `Xn α W ≤ C₀ α²`, `EpsSq α u ≤ R`, `SmoothOpen u`, `EpsMem α u`.
* `HkSq_JepsPz_le` (`EpsSqTools`) turns `EpsSq α u ≤ R` into `HkNorm α 6 W ≤ B` with
  `B = √(CJ (CJ/ε)^{12} R)` — the one *uniform* (in `u`) bound that the class clauses below need;
* `EpsRLX.XDataClean` then gives `SmoothOpen`, `HkMem α 4` and a bound for `HkSq α 4` of the
  *pre-mollified* right-hand side `g := profRHS α Φs E W`; `EpsRLX.ProfRHSEpsData` gives its
  `EpsMem`/`EpsSq`-size;
* `TenOfEight.HkMem_Jeps_gain_pos` (`k = 4`, `m = 2`) raises the `ℋ⁴`-honesty of `g` to `ℋ⁶` of
  `J_ε g` (this is the *unconditional* gain — the sibling `EpsE4Thr.HkMem_Jeps_gain` carries an
  unused vanishing hypothesis which does **not** hold for `profRHS`, see the review of
  `NOTES_HkMemIterAll.md`);
* `Pz` only adds a multiple of the compactly supported `bump`, so `HkMem`/`SmoothOpen` transfer;
* `HkSq_JepsPz_le` at `k = 6` with `f := g` bounds `HkSq α 6 (Feps u)`, hence `HkNorm α 6`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSEpsData
import Submission.Work.FTS.StrongEps.TenOfEight.GainAll
import Submission.Work.FTS.EpsEngine.SmoothOpenFeps

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

/-! ## `Pz` preserves `ℋ^k`-membership -/

/-- **The projection preserves `ℋ^k`-membership.**  `Pz f = f - (L₁₂ f 0 / pzNorm) • bump` and
`bump` is compactly supported and smooth, so `HkMem` transfers by `HkMem_add_open`. -/
theorem HkMem_Pz_of {α : ℝ} {k : ℕ} {f : Fn}
    (hsmo : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (Work.FTS.StrongEps.Pz f) := by
  set c : ℝ := -(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm) with hc
  have hb : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump :=
    Work.FTS.StrongEps.PZeroAux.classC_Pz_hkMem_bump α k
  have hcm : Work.Spaces.HkMem α k (fun z θ => c * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen c hb
  have hscm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen c Work.FTS.StrongEps.smoothOpen_bump
  have hPz : Work.FTS.StrongEps.Pz f
      = fun z θ => f z θ + c * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply, hc]
    ring
  rw [hPz]
  exact Work.FTS.EllipticEst.HkMem_add_open (α := α) (k := k) hsmo hscm hmem hcm

/-! ## The `ℋ⁶`-data of `Feps` on the `XBall` class -/

/-- **The `ℋ⁶`-data of `Feps` on the `XBall` class.**  There is a constant `Ce' > 0`, depending on
`α, ε, C₀, Ce, Cs, R` (but *not* on the profile `u`), such that for every `u` in the `XBall`
invariant the right-hand side `Feps α ρ ε Φs E u` is `SmoothOpen`, `ℋ⁶`-honest, and of
`ℋ⁶`-size at most `Ce'`. -/
theorem Feps_data_of_xball {α C₀ Ce Cs R ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) :
    ∃ Ce' : ℝ, 0 < Ce' ∧ ∀ u : Fn, XBall α ρ ε R C₀ u →
      Work.FTS.EllipticEst.SmoothOpen (Feps α ρ ε Φs E u) ∧
      Work.Spaces.HkMem α 6 (Feps α ρ ε Φs E u) ∧
      Work.Spaces.HkNorm α 6 (Feps α ρ ε Φs E u) ≤ Ce' := by
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  have hratio : 0 ≤ CJ / ε := div_nonneg hCJpos.le hε.le
  have hK60 : 0 ≤ CJ * (CJ / ε) ^ (2 * 6) * R :=
    mul_nonneg (mul_nonneg hCJpos.le (pow_nonneg hratio _)) hR
  -- the `ℋ⁶`-bound `B` of the projected mollified profile `W = Pz (J_ε u)`, uniform in `u`
  obtain ⟨CX, hCX, hX⟩ :=
    Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀)
      (B := Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R)) (Φs := Φs) (E := E)
      hα hEll hstar hml (Real.sqrt_nonneg _)
  obtain ⟨RP, hRP, hProf⟩ :=
    Work.FTS.StrongEps.EpsRLX.ProfRHSEpsData (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (B := Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R)) (Φs := Φs) (E := E)
      hα hEll hstar hml (Real.sqrt_nonneg _)
  refine ⟨Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * RP), ?_, ?_⟩
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
    have husmQuad : ∀ n : ℕ,
        ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall u).mp husmo
    set W : Fn := Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u) with hWdef
    -- ## the `ℋ⁶`-bound of `W`
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
    -- ## the mollified gain `ℋ⁴ → ℋ⁶`
    have hJ6 : Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.Jeps ρ ε g) :=
      Work.FTS.StrongEps.TenOfEight.HkMem_Jeps_gain_pos hρ α hα.1 hα.2 4 2 (by norm_num)
        ε hε g hgsmQuad hgmem4
    have hJsmo : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε g) :=
      Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hgsmQuad
    have hFeps : Feps α ρ ε Φs E u = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g) :=
      rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hFeps]
      exact smoothOpen_Pz_of_smoothOpen hJsmo
    · rw [hFeps]
      exact HkMem_Pz_of hJsmo hJ6
    · rw [hFeps, Work.Spaces.HkNorm]
      refine Real.sqrt_le_sqrt ?_
      exact (hCJ α hα ε hε hε1 6 (by norm_num) g hgsmo hgmeme).trans
        (mul_le_mul_of_nonneg_left hgsq (mul_nonneg hCJpos.le (pow_nonneg hratio _)))

end Work.FTS.EpsEngine
