import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EComparison.E_slots_diff_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.XBallFacts
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaXnBound
import Submission.Work.FTS.StrongEps.EpsRLX.LGTDiffClassC
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.H5.HkMemXnN5
import Submission.Work.FTS.StrongEps.LocUnif.D5.rounds
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.StarPkg6Fields
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXT0.SJC.slotJetLipschitzApprox
import Submission.Work.FTS_RegExport.THL.L.DzDthSG_C1Jet_of_inputs
import Submission.Work.FTS_RegExport.THL.cs7_theta_holder
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.Spaces.SmoothCompact_HkMem
-- ===== merged: Submission.Work.FTS.EpsEngine.profRHSDiffEpsSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open Work.FTS.Galerkin (Fn)

/-! ## The `ε`-energy of the difference of two pre-mollified right-hand sides

Let `Δ = profRHS α Φs E W₁ − profRHS α Φs E W₂` be the difference of the pre-mollified
right-hand side of the projected `ε`-scheme at two class-`C` profiles of `ℋ⁴`-size
`≤ C₀α²` (`EpsRLX.DeltaXnBound` supplies `Δ`'s `C^∞`-regularity on the open quadrant and
its honest `ℋ⁴`-membership with an `α`-dependent constant).

The claim is that `Δ` lies in the weighted space `X` of the scheme with the **sharp**
quadratic dependence on `Δ`'s own `ℋ⁴`-size:

  `EpsMem α Δ` and `EpsSq α Δ ≤ C · (Xn α Δ)²`.

The route is the trace-to-`X` transfer `EpsLocalPStar.TraceToEpsMem`: for an open-smooth
datum with `ℋ¹`-membership whose two angular traces vanish at every `z > 0`,
`EpsSq α f ≤ C/(γ−1)² · HkSq α 1 f` (and `EpsMem α f`).  Both hypotheses hold here:

* the traces of `Δ` vanish — `Δ` is the difference of two profiles whose traces vanish at
  `θ = 0` and `θ = π/2` (`EpsRLX.DiffTraces`, from the elliptic package of the two profiles
  and `StarPkgo2`);
* the `ℋ¹`-slot is dominated by the `ℋ⁴`-slot: `HkSq α 1 Δ ≤ HkSq α 4 Δ = (Xn α Δ)²` by
  monotonicity of the `ℋ`-integrand in the order of the derivatives
  (`CoercivityStep.Norm.HkSq_mono_le`). -/

theorem profRHSDiffEpsSq {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) :
    ∃ C : ℝ, 0 < C ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      Work.FTS.Nonlin.Xn α W₁ ≤ C₀ * α ^ 2 → Work.FTS.Nonlin.Xn α W₂ ≤ C₀ * α ^ 2 →
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ)
        ≤ C * (Work.FTS.Nonlin.Xn α (fun z θ =>
            Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
              - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ)) ^ 2 := by
  have hα0 : 0 < α := hα.1
  -- the `γ`-weight of the scheme is strictly larger than `1`
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα0
    linarith
  -- the two library constants: the trace-to-`X` transfer, and the `ℋ⁴`-data of `Δ`
  obtain ⟨CT, hCTpos, hCT⟩ := Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.StrongEps.EpsRLX.DeltaXnBound (α := α) (C₀ := C₀)
    (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) hα hEll hstar hml
  refine ⟨max 1 (CT / (Work.Spaces.gam α - 1) ^ 2),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro W₁ W₂ hW₁ hW₂ hX₁ hX₂
  -- ## the difference profile and its `ℋ⁴`-data
  set Δ : Fn := fun z θ =>
    Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
      - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ with hΔdef
  obtain ⟨hΔsm₀, hΔmem₀, -⟩ := hK hW₁ hW₂ hX₁ hX₂
  have hΔsm : Work.FTS.EllipticEst.SmoothOpen Δ := by simpa only [hΔdef] using hΔsm₀
  have hΔmem4 : Work.Spaces.HkMem α 4 Δ := by simpa only [hΔdef] using hΔmem₀
  have hΔmem1 : Work.Spaces.HkMem α 1 Δ :=
    Work.FTS.OpenPkg.HkMem_mono_open hΔsm 1 (by norm_num) hΔmem4
  -- ## the two trace hypotheses
  obtain ⟨ht1, ht2⟩ := Work.FTS.StrongEps.EpsRLX.DiffTraces hα hW₁ hW₂
    (hEll W₁ hW₁).1 (hEll W₂ hW₂).1 hstar
  -- ## the transfer to the weighted space `X`
  obtain ⟨hΔepsMem, hΔepsSq⟩ := hCT α hα Δ hΔsm hΔmem1
    (fun z hz => by simpa only [hΔdef] using ht1 z hz)
    (fun z hz => by simpa only [hΔdef] using ht2 z hz)
  -- ## the `ℋ¹`-slot is dominated by the `ℋ⁴`-slot
  have hHk1 : Work.Spaces.HkSq α 1 Δ ≤ (Work.FTS.Nonlin.Xn α Δ) ^ 2 := by
    refine le_trans (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hΔmem4) ?_
    rw [show Work.FTS.Nonlin.Xn α Δ = Work.Spaces.HkNorm α 4 Δ from rfl, Work.Spaces.HkNorm,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 Δ)]
  change Work.FTS.StrongEps.EpsMem α Δ ∧
    Work.FTS.StrongEps.EpsSq α Δ
      ≤ max 1 (CT / (Work.Spaces.gam α - 1) ^ 2) * (Work.FTS.Nonlin.Xn α Δ) ^ 2
  refine ⟨hΔepsMem, ?_⟩
  calc Work.FTS.StrongEps.EpsSq α Δ
      ≤ CT / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 Δ := hΔepsSq
    _ ≤ CT / (Work.Spaces.gam α - 1) ^ 2 * (Work.FTS.Nonlin.Xn α Δ) ^ 2 :=
        mul_le_mul_of_nonneg_left hHk1 (div_nonneg hCTpos.le (sq_nonneg _))
    _ ≤ max 1 (CT / (Work.Spaces.gam α - 1) ^ 2) * (Work.FTS.Nonlin.Xn α Δ) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.rhsFun_lipschitz_H4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The limiting right-hand side at a slice is the profile right-hand side

`rhsFun α Φs E g τ = dynLin α g τ + dynRHS α (PsiCan Φs E g) g τ` depends on the family `g`
only through its slice `slice g τ`, and once `g` is replaced by the constant family generated
by that slice, the two definitions `Galerkin.dynLin`/`Galerkin.dynRHS` and
`StrongPersist.linPart`/`StrongPersist.rhsOf` (`= Construction.gRHS`) agree.  So the limiting
right-hand side *is* `EpsLocalPStar.profRHS` evaluated at the slice — definitionally. -/

/-- `rhsFun α Φs E g τ = profRHS α Φs E (slice g τ)`, by `rfl` (`profRHS` is the same
expression written as a function of the single profile). -/
theorem rhsFun_eq_profRHS (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) (τ : ℝ) :
    Work.FTS.StrongEps.rhsFun α Φs E g τ
      = Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (slice g τ) := rfl

/-- `rhsFun` is Lipschitz in the slice, in the `ℋ⁴`-metric against the `ℋ⁵`-metric of the slice
difference, on the class-`C` small ball where `MuLamOK` forces `|μ| ≤ 1/2`.

This is the *limiting* (mollifier-free) counterpart of the Lipschitz gate of the projected
`ε`-scheme (`EpsLocalPStar.EpsRHSPLipX`): its content is the `ℋ⁴`-difference estimate
`EpsRLX.DeltaXnBound` for the profile right-hand side `profRHS`, transported to `rhsFun`
along the definitional identity `rhsFun_eq_profRHS` above, with the two `ℋ⁵`-sizes of the
slices dominated by their `ℋ⁶`-sizes via the given uniform `ℋ⁶`-bound `B`. -/
theorem rhsFun_lipschitz_H4 {α C₀ Ce Cs B T α₄ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα₄ : 0 < α₄) (hα₄1 : α₄ ≤ 1) (hα : α ∈ Set.Ioc (0 : ℝ) α₄)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hB : 0 ≤ B) :
    ∃ L : ℝ, 0 < L ∧ ∀ (g₁ g₂ : Work.FTS.Galerkin.Fam),
      (∀ τ ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g₁ τ) ∧
        Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice g₁ τ) ∧
        Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice g₁ τ) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice g₁ τ) ≤ C₀ * α ^ 2 ∧
        Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g₁ τ) ≤ B) →
      (∀ τ ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g₂ τ) ∧
        Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice g₂ τ) ∧
        Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice g₂ τ) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice g₂ τ) ≤ C₀ * α ^ 2 ∧
        Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g₂ τ) ≤ B) →
      ∀ τ ∈ Set.Icc (0 : ℝ) T,
        Work.Spaces.HkNorm α 4 (fun z θ => Work.FTS.StrongEps.rhsFun α Φs E g₁ τ z θ
            - Work.FTS.StrongEps.rhsFun α Φs E g₂ τ z θ)
          ≤ L * Work.Spaces.HkNorm α 5 (fun z θ =>
              Work.FTS.Galerkin.slice g₁ τ z θ - Work.FTS.Galerkin.slice g₂ τ z θ) := by
  -- `α` lies in the range of `DeltaXnBound`
  have hα1 : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα.1, le_trans hα.2 hα₄1⟩
  -- the `ℋ⁴`-difference estimate for the profile right-hand side
  obtain ⟨K, hKpos, hK⟩ :=
    Work.FTS.StrongEps.EpsRLX.DeltaXnBound (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (Φs := Φs) (E := E) hα1 hEll hstar hml
  refine ⟨K * (1 + (1 + 2 * B) ^ 2), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 1 + (1 + 2 * B) ^ 2 := by positivity
    exact mul_pos hKpos h1
  · intro g₁ g₂ h₁ h₂ τ hτ
    -- the slice data at `τ`
    have hm1 : Work.Spaces.HkMem α 6 (slice g₁ τ) := (h₁ τ hτ).2.1
    have hm2 : Work.Spaces.HkMem α 6 (slice g₂ τ) := (h₂ τ hτ).2.1
    have hC1 : Work.FTS.ClassC.ClassC α (slice g₁ τ) := (h₁ τ hτ).2.2.1
    have hC2 : Work.FTS.ClassC.ClassC α (slice g₂ τ) := (h₂ τ hτ).2.2.1
    have hX1 : Work.FTS.Nonlin.Xn α (slice g₁ τ) ≤ C₀ * α ^ 2 := (h₁ τ hτ).2.2.2.1
    have hX2 : Work.FTS.Nonlin.Xn α (slice g₂ τ) ≤ C₀ * α ^ 2 := (h₂ τ hτ).2.2.2.1
    have hb1 : Work.Spaces.HkNorm α 5 (slice g₁ τ) ≤ B :=
      le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 5) (by norm_num) hm1)
        (h₁ τ hτ).2.2.2.2
    have hb2 : Work.Spaces.HkNorm α 5 (slice g₂ τ) ≤ B :=
      le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 5) (by norm_num) hm2)
        (h₂ τ hτ).2.2.2.2
    -- the profile right-hand side difference bound
    have hbd := (hK hC1 hC2 hX1 hX2).2.2
    -- `rhsFun` agrees with `profRHS` at the slice, so the `ℋ⁴`-norms agree
    have hfun : (fun z θ => Work.FTS.StrongEps.rhsFun α Φs E g₁ τ z θ
          - Work.FTS.StrongEps.rhsFun α Φs E g₂ τ z θ)
        = fun z θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (slice g₁ τ) z θ
            - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (slice g₂ τ) z θ := by
      funext z θ
      rw [rhsFun_eq_profRHS α Φs E g₁ τ, rhsFun_eq_profRHS α Φs E g₂ τ]
    rw [hfun]
    -- the two `ℋ⁵`-sizes are dominated by `B`
    have hZ : 0 ≤ Work.Spaces.HkNorm α 5 (fun z θ => slice g₁ τ z θ - slice g₂ τ z θ) :=
      Work.Spaces.HkNorm_nonneg α 5 _
    have hP : (1 : ℝ) + Work.Spaces.HkNorm α 5 (slice g₁ τ) + Work.Spaces.HkNorm α 5 (slice g₂ τ)
        ≤ 1 + 2 * B := by linarith
    have hP0 : (0 : ℝ) ≤ 1 + Work.Spaces.HkNorm α 5 (slice g₁ τ)
        + Work.Spaces.HkNorm α 5 (slice g₂ τ) := by
      have h1 := Work.Spaces.HkNorm_nonneg α 5 (slice g₁ τ)
      have h2 := Work.Spaces.HkNorm_nonneg α 5 (slice g₂ τ)
      linarith
    have hsq : ((1 : ℝ) + Work.Spaces.HkNorm α 5 (slice g₁ τ)
          + Work.Spaces.HkNorm α 5 (slice g₂ τ)) ^ 2 ≤ (1 + 2 * B) ^ 2 :=
      pow_le_pow_left₀ hP0 hP 2
    have hsq' : ((1 : ℝ) + Work.Spaces.HkNorm α 5 (slice g₁ τ)
          + Work.Spaces.HkNorm α 5 (slice g₂ τ)) ^ 2 ≤ 1 + (1 + 2 * B) ^ 2 := by
      have h1 : (0 : ℝ) ≤ (1 + 2 * B) ^ 2 := sq_nonneg _
      linarith
    refine le_trans hbd ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq' hKpos.le) hZ

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.ConjTwoSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongEps.EpsRLX (Wp)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem ConjTwoSq {α C₀ Ce Cs R : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 < L ∧
      (∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen u →
        Work.FTS.EllipticEst.SmoothOpen v →
        Work.FTS.StrongEps.EpsMem α u →
        Work.FTS.StrongEps.EpsSq α u ≤ R →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsMem α v → Work.FTS.StrongEps.EpsSq α v ≤ R →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsMem α (fun z θ => u z θ - v z θ) →
        Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
            - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ)
          ≤ L * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
  have hα0 : 0 < α := hα.1
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα0
    linarith
  -- ## the six constants
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Work.FTS.StrongEps.EpsRLX.DeltaXnBound (α := α) (C₀ := C₀)
    (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) hα hEll hstar hml
  obtain ⟨CP, hCPpos, hCP⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_Pz_sub_le
  obtain ⟨CM, hCMpos, hCM⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6 ρ hρ
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.EpsSq_Jeps_le ρ hρ.moll
  obtain ⟨CT, hCTpos, hCT⟩ := Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem
  obtain ⟨CD, hCDpos, hCD⟩ := Work.FTS.StrongEps.EpsLocalPStar.HkSq_Wp_sub_le_of_ClassC ρ hρ
  obtain ⟨CW, hCWpos, hCW⟩ := Work.FTS.StrongEps.EpsLocalPStar.exists_Wp_bound_of_EpsMem ρ hρ
  -- ## the uniform `ℋᵏ`-size (`k ≤ 6`) of an admissible profile, from the `X`-ball
  set BS : ℝ := CW * (CW / ε) ^ 6 * (1 + R) with hBSdef
  have hBS0 : 0 ≤ BS := by
    rw [hBSdef]
    have hdiv : 0 ≤ CW / ε := div_nonneg hCWpos.le hε.le
    exact mul_nonneg (mul_nonneg hCWpos.le (pow_nonneg hdiv 6)) (by linarith)
  have hWp : ∀ {f : Fn}, Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.StrongEps.EpsMem α f →
      Work.FTS.StrongEps.EpsSq α f ≤ R → ∀ k : ℕ, k ≤ 6 →
      Work.Spaces.HkNorm α k (Wp ρ ε f) ≤ BS := by
    intro f hf hm hRf k hk
    exact hCW α hα ε ⟨hε, hε1⟩ R hR f hf hm hRf k hk
  -- ## the uniform a-priori data of `profRHS` at such a profile
  obtain ⟨BR, hBRpos, hRX⟩ := Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs)
    (C₀ := C₀) (B := BS) hα hEll hstar hml hBS0
  -- ## the profile-factor parameter `M₀`
  set M₀ : ℝ := 1 + 2 * BS with hM₀def
  have hM₀1 : 1 ≤ M₀ := by rw [hM₀def]; linarith
  have hM₀0 : 0 ≤ M₀ := le_trans zero_le_one hM₀1
  -- ## the Lipschitz constant
  set L : ℝ := CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2) * K₁ ^ 2 * M₀ ^ 4
    * CD * (CD / ε) ^ 12 with hLdef
  refine ⟨max 1 L, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u v hu hv hmemu hSqu hclu hxnu hmemv hSqv hclv hxnv hmemuv
  -- ## the abbreviations
  set Φu : Fn := profRHS α Φs E (Wp ρ ε u) with hΦudef
  set Φv : Fn := profRHS α Φs E (Wp ρ ε v) with hΦvdef
  set Δ : Fn := fun z θ => Φu z θ - Φv z θ with hΔdef
  set d : Fn := fun z θ => Wp ρ ε u z θ - Wp ρ ε v z θ with hddef
  have hdXN : Work.Spaces.HkNorm α 5 d
      = Work.Spaces.HkNorm α 5 (fun z θ => Wp ρ ε u z θ - Wp ρ ε v z θ) := by rw [hddef]
  -- ## the smoothness / honesty / size of `Δ`
  obtain ⟨hΔsm₀, hΔmem₀, hΔxn₀⟩ :=
    hK₁ (W₁ := Wp ρ ε u) (W₂ := Wp ρ ε v) hclu hclv hxnu hxnv
  have hΔsm : Work.FTS.EllipticEst.SmoothOpen Δ := by
    rw [hΔdef]
    simpa only [hΦudef, hΦvdef, Wp] using hΔsm₀
  have hΔmem4 : Work.Spaces.HkMem α 4 Δ := by
    rw [hΔdef]
    simpa only [hΦudef, hΦvdef, Wp] using hΔmem₀
  have hΔxn : Work.FTS.Nonlin.Xn α Δ
      ≤ K₁ * (1 + Work.Spaces.HkNorm α 5 (Wp ρ ε u)
          + Work.Spaces.HkNorm α 5 (Wp ρ ε v)) ^ 2 * Work.Spaces.HkNorm α 5 d := by
    rw [hΔdef, hdXN]
    simpa only [hΦudef, hΦvdef, Wp] using hΔxn₀
  have hΔmem1 : Work.Spaces.HkMem α 1 Δ :=
    Work.FTS.OpenPkg.HkMem_mono_open hΔsm 1 (by norm_num) hΔmem4
  -- ## `EpsMem`/`EpsSq` of `Δ` via the vanishing traces
  obtain ⟨ht1, ht2⟩ := Work.FTS.StrongEps.EpsRLX.DiffTraces (α := α) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (W₁ := Wp ρ ε u) (W₂ := Wp ρ ε v) (E := E) hα hclu hclv
    ((hEll (Wp ρ ε u) hclu).1) ((hEll (Wp ρ ε v) hclv).1) hstar
  have ht1' : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ => Δ z θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro z hz
    have hfun : (fun θ => Δ z θ) = fun θ : ℝ =>
        profRHS α Φs E (Wp ρ ε u) z θ - profRHS α Φs E (Wp ρ ε v) z θ := by
      funext θ
      simp only [hΔdef, hΦudef, hΦvdef]
    rw [hfun]
    exact ht1 z hz
  have ht2' : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ => Δ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    intro z hz
    have hfun : (fun θ => Δ z θ) = fun θ : ℝ =>
        profRHS α Φs E (Wp ρ ε u) z θ - profRHS α Φs E (Wp ρ ε v) z θ := by
      funext θ
      simp only [hΔdef, hΦudef, hΦvdef]
    rw [hfun]
    exact ht2 z hz
  obtain ⟨hΔepsMem, hΔepsSq⟩ := hCT α hα Δ hΔsm hΔmem1 ht1' ht2'
  -- ## `HkSq α 1 Δ ≤ (Xn α Δ)²`
  have hΔHk : Work.Spaces.HkSq α 1 Δ ≤ (Work.FTS.Nonlin.Xn α Δ) ^ 2 := by
    refine le_trans (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hΔmem4) ?_
    rw [show Work.FTS.Nonlin.Xn α Δ = Work.Spaces.HkNorm α 4 Δ from rfl, Work.Spaces.HkNorm,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 Δ)]
  -- ## the smoothness / honesty of the two pre-mollified profiles
  have hXud := hRX (W := Wp ρ ε u) hclu hxnu (hWp hu hmemu hSqu 6 (by norm_num))
  have hXvd := hRX (W := Wp ρ ε v) hclv hxnv (hWp hv hmemv hSqv 6 (by norm_num))
  have hsmΦu : Work.FTS.EllipticEst.SmoothOpen Φu := by
    rw [hΦudef]; exact hXud.1
  have hsmΦv : Work.FTS.EllipticEst.SmoothOpen Φv := by
    rw [hΦvdef]; exact hXvd.1
  have hmem4Φu : Work.Spaces.HkMem α 4 Φu := by
    rw [hΦudef]; exact hXud.2.1
  have hmem4Φv : Work.Spaces.HkMem α 4 Φv := by
    rw [hΦvdef]; exact hXvd.2.1
  -- ## the mollified profile
  have hsmFact : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Δ) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Δ).mp hΔsm
  have hJepsΔmem : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε Δ) :=
    (hCM α hα ε hε hε1 Δ hsmFact hΔepsMem).1
  have hJepsΔSq : Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Δ)
      ≤ Real.exp (CJ * ε) * Work.FTS.StrongEps.EpsSq α Δ :=
    hCJ α hα ε hε hε1 Δ hΔepsMem hJepsΔmem
  -- ## the `J_ε`-linearity and the `P₀`-bound
  have hJsub : Work.FTS.StrongEps.Jeps ρ ε Φu - Work.FTS.StrongEps.Jeps ρ ε Φv
      = Work.FTS.StrongEps.Jeps ρ ε Δ := by
    rw [hΔdef]
    exact Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll hε hsmΦu hsmΦv
  have hsubMem : Work.FTS.StrongEps.EpsMem α
      (fun z θ => Work.FTS.StrongEps.Jeps ρ ε Φu z θ - Work.FTS.StrongEps.Jeps ρ ε Φv z θ) :=
    Work.FTS.StrongEps.EpsSqTools.EpsMem_congr
      (fun z θ => (congrFun (congrFun hJsub z) θ).symm) hJepsΔmem
  have hPzData := hCP α hα (Work.FTS.StrongEps.Jeps ρ ε Φu) (Work.FTS.StrongEps.Jeps ρ ε Φv)
    (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φu).mp hsmΦu))
    (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φv).mp hsmΦv))
    (Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φu).mp hsmΦu) hmem4Φu)
    (Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φv).mp hsmΦv) hmem4Φv)
    hsubMem
  have hEpsSqJsub : Work.FTS.StrongEps.EpsSq α
      (fun z θ => Work.FTS.StrongEps.Jeps ρ ε Φu z θ - Work.FTS.StrongEps.Jeps ρ ε Φv z θ)
      = Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Δ) :=
    Work.FTS.StrongEps.EpsSq_congr (fun z θ => congrFun (congrFun hJsub z) θ)
  -- ## the two right-hand sides
  have hslice : (fun z θ => Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
        - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ)
      = (fun z θ => Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φu) z θ
        - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φv) z θ) := by
    funext z θ
    simp only [Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS, hΦudef, hΦvdef, Wp]
  -- ## the delta-data bound
  have hDd : (Work.Spaces.HkNorm α 5 d) ^ 2
      ≤ CD * (CD / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
    rw [hddef, Work.Spaces.HkNorm,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 5
        (fun z θ => Wp ρ ε u z θ - Wp ρ ε v z θ))]
    exact hCD α hα ε ⟨hε, hε1⟩ hu hv hclu hclv hmemuv
  -- ## the uniform profile factor
  have hWu : Work.Spaces.HkNorm α 5 (Wp ρ ε u) ≤ BS := hWp hu hmemu hSqu 5 (by norm_num)
  have hWv : Work.Spaces.HkNorm α 5 (Wp ρ ε v) ≤ BS := hWp hv hmemv hSqv 5 (by norm_num)
  have hMle : 1 + Work.Spaces.HkNorm α 5 (Wp ρ ε u) + Work.Spaces.HkNorm α 5 (Wp ρ ε v)
      ≤ M₀ := by
    rw [hM₀def]
    linarith
  have hM0 : 0 ≤ 1 + Work.Spaces.HkNorm α 5 (Wp ρ ε u)
      + Work.Spaces.HkNorm α 5 (Wp ρ ε v) := by
    have h1 : 0 ≤ Work.Spaces.HkNorm α 5 (Wp ρ ε u) := Work.Spaces.HkNorm_nonneg α 5 _
    have h2 : 0 ≤ Work.Spaces.HkNorm α 5 (Wp ρ ε v) := Work.Spaces.HkNorm_nonneg α 5 _
    linarith
  have hXs : (Work.FTS.Nonlin.Xn α Δ) ^ 2 ≤ (K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d) ^ 2 := by
    refine pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 Δ) ?_ 2
    have hM2 : (1 + Work.Spaces.HkNorm α 5 (Wp ρ ε u)
        + Work.Spaces.HkNorm α 5 (Wp ρ ε v)) ^ 2 ≤ M₀ ^ 2 :=
      pow_le_pow_left₀ hM0 hMle 2
    have hZ : 0 ≤ Work.Spaces.HkNorm α 5 d := Work.Spaces.HkNorm_nonneg α 5 d
    calc Work.FTS.Nonlin.Xn α Δ
        ≤ K₁ * (1 + Work.Spaces.HkNorm α 5 (Wp ρ ε u)
            + Work.Spaces.HkNorm α 5 (Wp ρ ε v)) ^ 2 * Work.Spaces.HkNorm α 5 d := hΔxn
      _ ≤ K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM2 hK₁pos.le) hZ
  -- ## the final chain
  have hT0 : 0 ≤ CT / (Work.Spaces.gam α - 1) ^ 2 := div_nonneg hCTpos.le (pow_pos hγ 2).le
  have hE0 : 0 ≤ Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) :=
    Work.FTS.StrongEps.EpsSq_nonneg α _
  have hfinal : Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
          - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ)
      ≤ CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2)
        * K₁ ^ 2 * M₀ ^ 4 * CD * (CD / ε) ^ 12
        * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
    calc Work.FTS.StrongEps.EpsSq α (fun z θ =>
          Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
            - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ)
        = Work.FTS.StrongEps.EpsSq α (fun z θ =>
            Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φu) z θ
              - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φv) z θ) :=
          Work.FTS.StrongEps.EpsSq_congr (fun z θ => congrFun (congrFun hslice z) θ)
      _ ≤ CP * Work.FTS.StrongEps.EpsSq α (fun z θ =>
            Work.FTS.StrongEps.Jeps ρ ε Φu z θ
              - Work.FTS.StrongEps.Jeps ρ ε Φv z θ) := hPzData.2
      _ = CP * Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Δ) := by
          rw [hEpsSqJsub]
      _ ≤ CP * (Real.exp (CJ * ε) * Work.FTS.StrongEps.EpsSq α Δ) :=
          mul_le_mul_of_nonneg_left hJepsΔSq hCPpos.le
      _ ≤ CP * (Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2
            * Work.Spaces.HkSq α 1 Δ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hΔepsSq (Real.exp_pos _).le) hCPpos.le
      _ ≤ CP * (Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2
            * (Work.FTS.Nonlin.Xn α Δ) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔHk hT0)
              (Real.exp_pos _).le) hCPpos.le
      _ = CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2)
            * (Work.FTS.Nonlin.Xn α Δ) ^ 2 := by ring
      _ ≤ CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2)
            * (K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d) ^ 2 :=
          mul_le_mul_of_nonneg_left hXs
            (mul_nonneg (mul_nonneg hCPpos.le (Real.exp_pos _).le) hT0)
      _ = CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2) * K₁ ^ 2 * M₀ ^ 4
            * (Work.Spaces.HkNorm α 5 d) ^ 2 := by ring
      _ ≤ CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2) * K₁ ^ 2 * M₀ ^ 4
            * (CD * (CD / ε) ^ 12
              * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
          refine mul_le_mul_of_nonneg_left hDd ?_
          have h1 : 0 ≤ CP * Real.exp (CJ * ε) :=
            mul_nonneg hCPpos.le (Real.exp_pos _).le
          have h2 : 0 ≤ CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2) :=
            mul_nonneg h1 hT0
          have h3 : 0 ≤ CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2)
              * K₁ ^ 2 := mul_nonneg h2 (pow_nonneg hK₁pos.le 2)
          exact mul_nonneg h3 (pow_nonneg hM₀0 4)
      _ = CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2) * K₁ ^ 2 * M₀ ^ 4
            * CD * (CD / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
          ring
  rw [← hLdef] at hfinal
  exact le_trans hfinal (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) L) hE0)

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.coef_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

/-! ## §1 The three-element set of `RXT.velVanish2`

The `Q` of the `vanish0` leaf lives in a three-element set written with the sanitised family
`GR α g` and the reflected stream function `ΦR α Φs E g`; the coefficients `CoefR`, `CoefV`,
`CoefU` of `ProdDefs` are the *same* objects (`Rop (pExp α) Φ̃_τ`, `Vop Φ̃_τ`,
`Uop (pExp α) Φ̃_τ / sin 2θ`), so membership is `rfl`-level. -/

/-- The three-element set of `RXT.velVanish2`, as a named definition (so that the memberships
below are checked by `rfl` against the leaf's own statement). -/
def coefSet (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (τ : ℝ) : Set (ℝ → ℝ → ℝ) :=
  ({(Work.Construction.Rop (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)),
    Work.Construction.Vop
      (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ),
    fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ / Real.sin (2 * θ)} :
        Set (ℝ → ℝ → ℝ))

theorem coeff_mem_coefSet (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (τ : ℝ) :
    CoefR α Φs E g τ ∈ coefSet α Φs E g τ := by
  simp only [coefSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact Or.inl rfl

theorem coefV_mem_coefSet (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (τ : ℝ) :
    CoefV α Φs E g τ ∈ coefSet α Φs E g τ := by
  simp only [coefSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact Or.inr (Or.inl rfl)

theorem coefU_mem_coefSet (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (τ : ℝ) :
    CoefU α Φs E g τ ∈ coefSet α Φs E g τ := by
  simp only [coefSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact Or.inr (Or.inr rfl)

/-! ## §2 The residual vanishes identically at `z = 0`

`psiR` is *by definition* `Theta (pExp α) (Ftau (pExp α) (GR α g) τ)` on `z ≤ 0`, and `PhiTil`
subtracts exactly that `Theta`; so `PhiT α Φs E g τ 0 θ = 0` for every `θ` — no hypothesis
needed.  Consequently `pth (PhiT α Φs E g τ) 0 θ = 0` (the derivative of a function vanishing
identically in `θ`), and with `z = 0` the `z`-factors of `Rop` and `Uop` die as well. -/

theorem PhiT_zero (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (τ θ : ℝ) : PhiT α Φs E g τ 0 θ = 0 := by
  simp only [PhiT, Work.FTS_RegExport.RXT.v2_PhiT, Work.Construction.PhiTil,
    Work.FTS.Galerkin.slice_apply, Work.FTS.RegExportIface.psiR_of_nonpos (le_refl (0 : ℝ))]
  simp [Work.FTS.RegExportIface.RXT.GR]

theorem pth_PhiT_zero (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (τ θ : ℝ) : Work.Spaces.pth (PhiT α Φs E g τ) 0 θ = 0 := by
  have hfun : (fun θ' => PhiT α Φs E g τ 0 θ') = fun _ => 0 :=
    funext fun θ' => PhiT_zero α Φs E g τ θ'
  simp only [Work.Spaces.pth]
  rw [hfun]
  simp

/-- The `vanish0` coefficient data of the three slots
`CoefR α Φs E g τ = Rop (pExp α) Φ̃_τ`, `CoefV α Φs E g τ = Vop Φ̃_τ`,
`CoefU α Φs E g τ = Uop (pExp α) Φ̃_τ / sin 2θ`:

* order-`0` and first-`D_z`/`D_θ` slot bounds `≤ A·min z 1` on the open quadrant, uniformly in
  `τ ∈ [0,S]` (the `j+i ≤ 1` cases of `RXT.velVanish2`; the `j+i ≤ 2` version is available but only
  `≤ 1` is needed here),
* and the axis values: all three coefficients vanish at `z = 0`.

Route: `RXT.velVanish2` gives, for every `Q` in the three-element set, `∀ j i, j+i ≤ 2 →
|mixed j i Q z θ| ≤ M·min z 1` with `Q` written via
`RegExportIface.phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ` = `PhiT α Φs E g τ` (same object,
`ProdDefs.PhiT`), so the bounds are `rfl`-level after rewriting `mixed 0 0 = id`, `mixed 1 0 = Dz`,
`mixed 0 1 = Dth`.
For `z = 0`: `PhiT α Φs E g τ 0 θ = 0` for **all** `θ` (the `z ≤ 0` branch of `psiR` is exactly the
`Theta (pExp α) (Ftau (pExp α) (GR α g) τ)` subtracted in `PhiTil`), hence also
`pz (PhiT α Φs E g τ) 0 θ = 0` and `pth (PhiT α Φs E g τ) 0 θ = 0` (derivative of an identically
zero function), and each of `Rop`, `Vop`, `Uop` of `Φ̃` then vanishes at `z = 0`. -/
theorem coef_bounds {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∃ A : ℝ, 0 ≤ A ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dth (Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ) z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dz (Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ) z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dth (Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ) z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dz (Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ) z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dth (Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ) z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dz (Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ) z θ| ≤ A * min z 1) ∧
      (∀ θ τ, θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
        Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ 0 θ = 0 ∧
        Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ 0 θ = 0 ∧
        Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ 0 θ = 0) := by
  intro S hS
  -- the `j + i ≤ 2` slot bound of the leaf, sampled at `(j,i) = (0,0), (0,1), (1,0)`
  obtain ⟨M, hM⟩ := Work.FTS_RegExport.RXT.velVanish2 (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS
  have hmm : ∀ z : ℝ, 0 < z → (0 : ℝ) ≤ min z 1 := fun z hz => le_min hz.le zero_le_one
  have hMA : ∀ z : ℝ, 0 < z → M * min z 1 ≤ max M 0 * min z 1 :=
    fun z hz => mul_le_mul_of_nonneg_right (le_max_left M 0) (hmm z hz)
  -- the nine slot bounds, sampled from `hM` at the three slots
  have slot : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ Q ∈ coefSet α Φs E g τ, ∀ z θ,
      0 < z → 0 < θ → θ < π / 2 →
        |Q z θ| ≤ M * min z 1 ∧ |Work.Spaces.Dth Q z θ| ≤ M * min z 1 ∧
          |Work.Spaces.Dz Q z θ| ≤ M * min z 1 := by
    intro τ' hτ' Q hQ z θ hz hθ hθ2
    have h00 := hM τ' hτ' z θ hz hθ hθ2 Q hQ 0 0 (by norm_num)
    have h01 := hM τ' hτ' z θ hz hθ hθ2 Q hQ 0 1 (by norm_num)
    have h10 := hM τ' hτ' z θ hz hθ hθ2 Q hQ 1 0 (by norm_num)
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter, Work.Spaces.DthIter] at h00 h01 h10
    exact ⟨h00, h01, h10⟩
  refine ⟨max M 0, le_max_right M 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `|CoefR|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefR α Φs E g τ) (coeff_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).1 (hMA z hz)
  · -- `|D_θ CoefR|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefR α Φs E g τ) (coeff_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).2.1 (hMA z hz)
  · -- `|D_z CoefR|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefR α Φs E g τ) (coeff_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).2.2 (hMA z hz)
  · -- `|CoefV|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefV α Φs E g τ) (coefV_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).1 (hMA z hz)
  · -- `|D_θ CoefV|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefV α Φs E g τ) (coefV_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).2.1 (hMA z hz)
  · -- `|D_z CoefV|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefV α Φs E g τ) (coefV_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).2.2 (hMA z hz)
  · -- `|CoefU|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefU α Φs E g τ) (coefU_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).1 (hMA z hz)
  · -- `|D_θ CoefU|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefU α Φs E g τ) (coefU_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).2.1 (hMA z hz)
  · -- `|D_z CoefU|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefU α Φs E g τ) (coefU_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).2.2 (hMA z hz)
  · -- the axis values at `z = 0`
    intro θ τ _ _
    exact ⟨by simp [CoefR, Work.Construction.Rop, PhiT_zero, pth_PhiT_zero],
      by simp [CoefV, Work.Construction.Vop, PhiT_zero, pth_PhiT_zero],
      by simp [CoefU, Work.Construction.Uop, PhiT_zero]⟩

end Work.FTS_RegExport.RXR5L

end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.coef_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5L

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-! ## Slice differentiability from `C²` on the open quadrant

The two slices of a function `H` which is `C²` on the open quadrant `Q0` are differentiable at
every point of `Q0`: `Q0` is open, so `ContDiffOn.differentiableOn` gives `DifferentiableAt` of the
uncurried `H`, and a slice is that map composed with `z' ↦ (z', θ)` (resp. `θ' ↦ (z, θ')`). -/

/-- The `z`-slice of a function that is `C²` on the open quadrant is differentiable. -/
theorem differentiableAt_slice_fst_of_contDiffOn_two {H : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 2 (Function.uncurry H) Work.FTS.EllipticEst.Q0) {z θ : ℝ}
    (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    DifferentiableAt ℝ (fun z' => H z' θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry H) (z, θ) :=
    (h.differentiableOn two_ne_zero).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)
  have hlin : DifferentiableAt ℝ (fun z' : ℝ => (z', θ)) z := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using hd.comp z hlin

/-- The `θ`-slice of a function that is `C²` on the open quadrant is differentiable. -/
theorem differentiableAt_slice_snd_of_contDiffOn_two {H : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 2 (Function.uncurry H) Work.FTS.EllipticEst.Q0) {z θ : ℝ}
    (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    DifferentiableAt ℝ (fun θ' => H z θ') θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry H) (z, θ) :=
    (h.differentiableOn two_ne_zero).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)
  have hlin : DifferentiableAt ℝ (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using hd.comp θ hlin

/-- Differentiability of the two slices of the three slots `CoefR/CoefV/CoefU` of
`PhiT α Φs E g τ` on the open quadrant.

Route: `RXT.Sys.coeff_pieces_contDiffOn` (last two conjuncts) supplies
`ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ)) Q0` (and the same for
`Theta (pExp α) (Ftau (pExp α) (GR α g) τ)`) for `τ ≥ 0`; `Q0 = Ioi 0 ×ˢ Ioo 0 (π/2)` is open, so
at `(z,θ) ∈ Q0` the slices `z ↦ Φ̃(z,θ)`, `z ↦ pz Φ̃(z,θ)`, `z ↦ pz(pz Φ̃)(z,θ)`,
`z ↦ pth Φ̃(z,θ)`, `z ↦ pz(pth Φ̃)(z,θ)` (and the `θ`-slices) are differentiable, using
`GalBasis.contDiffAt_slice_fst_of_uncurry` together with
`GalBasis.contDiffOn_uncurry_pzIter_le` / `contDiffOn_uncurry_pthIter_le` (the `z`-slices of the
iterated partials are again smooth of the expected order).  Since `Rop α Ψ = (2 sinθ·Ψ + α sinθ·z·pz Ψ
+ cosθ·pth Ψ)/cosθ`, `Vop Ψ = pth Ψ - tanθ·Ψ`, `Uop α Ψ = -3Ψ - α z·pz Ψ`, the slice
differentiability follows from the chain/product/quotient rules (`cos θ > 0` and `sin 2θ ≠ 0` on the
open interval, so the divisions are honest there). -/
theorem coef_diff {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      DifferentiableAt ℝ (fun z' => Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ z' θ) z ∧
      DifferentiableAt ℝ (fun θ' => Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ z θ') θ ∧
      DifferentiableAt ℝ (fun z' => Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ z' θ) z ∧
      DifferentiableAt ℝ (fun θ' => Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ z θ') θ ∧
      DifferentiableAt ℝ (fun z' => Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ z' θ) z ∧
      DifferentiableAt ℝ (fun θ' => Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ z θ') θ := by
  intro S hS τ hτ z θ hz hθ hθ2
  -- `C³` smoothness of `Φ̃_τ = v2_PhiT α Φs E g τ` on the open quadrant
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hΨ3, -⟩ :=
    Work.FTS_RegExport.RXT.Sys.coeff_pieces_contDiffOn (C₀ := C₀) (Cs := Cs) (g := g)
      hα hα13 hEL3 hStar hOK hτ.1
  have hQ0 : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
  -- the three coefficient *pieces* are `C²` on the open quadrant
  have hR2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Rop
      (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_uncurry_Rop hΨ3
  have hV2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop
      (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_uncurry_Vop hΨ3
  have hU2 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.Construction.Uop
      (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
        / Real.sin (2 * θ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_uncurry_div_sin_two
      (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop
        (α := Work.FTS.Regularity.pExp α) hΨ3)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact differentiableAt_slice_fst_of_contDiffOn_two hR2 hQ0
  · exact differentiableAt_slice_snd_of_contDiffOn_two hR2 hQ0
  · exact differentiableAt_slice_fst_of_contDiffOn_two hV2 hQ0
  · exact differentiableAt_slice_snd_of_contDiffOn_two hV2 hQ0
  · exact differentiableAt_slice_fst_of_contDiffOn_two hU2 hQ0
  · exact differentiableAt_slice_snd_of_contDiffOn_two hU2 hQ0

end Work.FTS_RegExport.RXR5L
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.coef_tau_lip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology Real

namespace Work.FTS_RegExport.RXR5L

open Work.FTS.Galerkin (Fn Fam slice)

/-- The `τ`-Lipschitz data of the three slots `CoefR/CoefV/CoefU` of `PhiT α Φs E g τ`, uniform
in `(z,θ)` on the open quadrant.  This is the *Lipschitz* form of
`RXT.Sys.slot_tau_cont_alpha` (which only states continuity), with the same constant `K`.

Route (`Submission/Work/FTS_RegExport/RXT/Sys/slot_tau_cont_alpha.lean`, whose proof already
establishes these three Lipschitz bounds internally before discarding them in favour of
`ContinuousOn`): on the quadrant `PhiT α Φs E g τ = v2_PhiStar α Φs + v2_PhiPert α E g τ`
(`v2_phiTil_split`), the star slot is `τ`-independent, and the three slots are additive
(`v2_rop_add_at` / `v2_vop_add_at` / `v2_uop_div_add_at`), so it suffices to bound the difference of
the perturbation slots.  The approximants `Ξ_n(τ) = PhiTil (slice (gn n) τ) (E (slice (gn n) τ))`
of `hOK.2 = LimApprox` are uniformly Lipschitz in `τ` with one constant `K` for all `n`
(`SysAux.pertSlot_lip_approx`, from `EllPkgGo` applied to the class-`C` difference
`slice (gn n) τ - slice (gn n) τ'`), and converge pointwise to the limit slots
(`SysAux.pertSlot_tendsto`); `lipschitz_of_approx` then transfers the bound to the limit. -/
theorem coef_tau_lip {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < π / 2 →
      |Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ z θ
          - Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ' z θ| ≤ K * |τ - τ'| ∧
      |Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ z θ
          - Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ' z θ| ≤ K * |τ - τ'| ∧
      |Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ z θ
          - Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ' z θ| ≤ K * |τ - τ'| := by
  intro S hS
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨gn, B, L, hAppx, hLipC, hJetC, _hμc⟩ := hOK.2 S hS
  -- the uniform Lipschitz bound for the approximant slots
  obtain ⟨K, hK0, hB⟩ := Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
    (α := α) (Ce := Ce) (L := L) (E := E) hα hα13 hEll
    (fun n τ hτ => (hAppx n τ hτ).1) (fun n τ hτ τ' hτ' => hLipC n τ hτ τ' hτ')
  refine ⟨K, hK0, ?_⟩
  intro τ hτ τ' hτ' z θ hz hθ hθ2
  -- ## the pointwise convergence of the approximant slots
  have hC : ∀ τ ∈ Set.Icc (0:ℝ) S,
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ))) z θ) Filter.atTop
        (nhds (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ))) ∧
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ))) z θ) Filter.atTop
        (nhds (Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ))) ∧
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ))) z θ / Real.sin (2 * θ)) Filter.atTop
        (nhds (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ / Real.sin (2 * θ)))) :=
    fun τ hτ => Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto
      (α := α) (Ce := Ce) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hOK hS hAppx hJetC hτ z θ hz hθ hθ2
  -- ## regularity of the split pieces
  have hStar3 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).1.of_le
      (by simp [Work.Stability.smoothOrder])
  have hStar1 : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))
      Work.FTS.EllipticEst.Q0 := hStar3.of_le (by norm_num)
  have hTheta3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ))) Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    refine Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta
      (α := Work.FTS.Regularity.pExp α) ?_
    refine Work.FTS_RegExport.RXT.contDiffOn_three_L12 ?_
    obtain ⟨C, _hC0, hCb⟩ := Work.FTS_RegExport.RXT.Ftau_bounds
      (Φs := Φs) (E := E) hα hα13 hOK τ hτ
    exact Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      Work.FTS_RegExport.RXT.v2_continuousOn_K_Iθ
      (Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (Φs := Φs) (E := E) hα hα13 hOK τ hτ)
      (fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => ⟨(hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).1,
        (hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).2.1, (hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).2.2⟩)
  have hFull3 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ))
        Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    have hP := Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0
      (α := α) (C₀ := C₀) (Cs := Cs) hEL3 hStar hOK τ hτ
    exact hP.sub (hTheta3 τ hτ)
  have hPert3 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))
        Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    refine ((hFull3 τ hτ).sub hStar3).congr ?_
    intro p hp
    obtain ⟨z₁, θ₁⟩ := p
    simp only [Function.uncurry]
    linarith [Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁ hp]
  have hPert1 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 1 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))
        Work.FTS.EllipticEst.Q0 := fun τ hτ => (hPert3 τ hτ).of_le (by norm_num)
  -- ## the split identities of the three slots at `(z,θ)`
  have hsplitFun : ∀ τ : ℝ, 0 ≤ τ → Work.FTS_RegExport.RXR5.AgreeOnQ
      (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
      (Work.FTS_RegExport.RXT.v2_PhiStar α Φs + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) :=
    fun τ hτ z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
      Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz₁, hθ₁, hθ₁2⟩)
  have hsplitR : ∀ τ ∈ Set.Icc (0:ℝ) S, Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
      = Work.FTS_RegExport.RXT.v2_SlotR α (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ
        + Work.FTS_RegExport.RXT.v2_SlotR α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ := by
    intro τ hτ
    show Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
      = Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ
        + Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
    rw [Work.FTS_RegExport.RXR5.Rop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
      (h := hsplitFun τ hτ.1) hz hθ hθ2]
    exact Work.FTS_RegExport.RXT.v2_rop_add_at hStar1 (hPert1 τ hτ.1) ⟨hz, hθ, hθ2⟩
  have hsplitV : ∀ τ ∈ Set.Icc (0:ℝ) S, Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
      = Work.FTS_RegExport.RXT.v2_SlotV α (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ
        + Work.FTS_RegExport.RXT.v2_SlotV α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ := by
    intro τ hτ
    show Work.Construction.Vop (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
      = Work.Construction.Vop (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ
        + Work.Construction.Vop (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
    rw [Work.FTS_RegExport.RXR5.Vop_congr_of_agreeOnQ (h := hsplitFun τ hτ.1) hz hθ hθ2]
    exact Work.FTS_RegExport.RXT.v2_vop_add_at hStar1 (hPert1 τ hτ.1) ⟨hz, hθ, hθ2⟩
  have hsplitU : ∀ τ ∈ Set.Icc (0:ℝ) S, Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
      = Work.FTS_RegExport.RXT.v2_SlotU α (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ
        + Work.FTS_RegExport.RXT.v2_SlotU α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ := by
    intro τ hτ
    show Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)
      = Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ / Real.sin (2 * θ)
        + Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ / Real.sin (2 * θ)
    rw [Work.FTS_RegExport.RXR5.Uop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
      (h := hsplitFun τ hτ.1) hz hθ hθ2]
    exact Work.FTS_RegExport.RXT.v2_uop_div_add_at (αG := Work.FTS.Regularity.pExp α)
      hStar1 (hPert1 τ hτ.1) ⟨hz, hθ, hθ2⟩
  -- ## the Lipschitz bound for the limit slot families
  have hLR : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ
        - Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ')
            (E (slice g τ'))) z θ| ≤ K * |τ - τ'| :=
    Work.FTS_RegExport.RXT.Sys.lipschitz_of_approx
      (A := fun n τ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ)
      (Alim := fun τ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ))) z θ)
      (fun n τ hτ τ' hτ' => (hB n τ hτ τ' hτ' z θ hz hθ hθ2).1)
      (fun τ hτ => (hC τ hτ).1)
  have hLV : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ
        - Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ')
            (E (slice g τ'))) z θ| ≤ K * |τ - τ'| :=
    Work.FTS_RegExport.RXT.Sys.lipschitz_of_approx
      (A := fun n τ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ)
      (Alim := fun τ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ))) z θ)
      (fun n τ hτ τ' hτ' => (hB n τ hτ τ' hτ' z θ hz hθ hθ2).2.1)
      (fun τ hτ => (hC τ hτ).2.1)
  have hLU : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ / Real.sin (2 * θ)
        - Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ')
            (E (slice g τ'))) z θ / Real.sin (2 * θ)| ≤ K * |τ - τ'| :=
    Work.FTS_RegExport.RXT.Sys.lipschitz_of_approx
      (A := fun n τ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ / Real.sin (2 * θ))
      (Alim := fun τ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ))) z θ / Real.sin (2 * θ))
      (fun n τ hτ τ' hτ' => (hB n τ hτ τ' hτ' z θ hz hθ hθ2).2.2)
      (fun τ hτ => (hC τ hτ).2.2)
  -- ## the τ-Lipschitz bounds of the perturbation slots at the two times
  have hPR : |Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
      - Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ') z θ| ≤ K * |τ - τ'| := by
    simpa only [Work.FTS_RegExport.RXT.v2_SlotR, Work.FTS_RegExport.RXT.v2_PhiPert]
      using hLR τ hτ τ' hτ'
  have hPV : |Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
      - Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ') z θ| ≤ K * |τ - τ'| := by
    simpa only [Work.FTS_RegExport.RXT.v2_SlotV, Work.FTS_RegExport.RXT.v2_PhiPert]
      using hLV τ hτ τ' hτ'
  have hPU : |Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
      - Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ') z θ| ≤ K * |τ - τ'| := by
    simpa only [Work.FTS_RegExport.RXT.v2_SlotU, Work.FTS_RegExport.RXT.v2_PhiPert]
      using hLU τ hτ τ' hτ'
  -- ## the target slots are the `RXT` slots of `v2_PhiT`, and the star part cancels
  have eR : CoefR α Φs E g τ z θ = Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ := rfl
  have eR' : CoefR α Φs E g τ' z θ = Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ') z θ := rfl
  have eV : CoefV α Φs E g τ z θ = Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ := rfl
  have eV' : CoefV α Φs E g τ' z θ = Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ') z θ := rfl
  have eU : CoefU α Φs E g τ z θ = Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ := rfl
  have eU' : CoefU α Φs E g τ' z θ = Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ') z θ := rfl
  refine ⟨?_, ?_, ?_⟩
  · have harg : CoefR α Φs E g τ z θ - CoefR α Φs E g τ' z θ
        = Work.FTS_RegExport.RXT.v2_SlotR α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
          - Work.FTS_RegExport.RXT.v2_SlotR α
              (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ') z θ := by
      rw [eR, eR', hsplitR τ hτ, hsplitR τ' hτ']
      ring
    rw [harg]
    exact hPR
  · have harg : CoefV α Φs E g τ z θ - CoefV α Φs E g τ' z θ
        = Work.FTS_RegExport.RXT.v2_SlotV α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
          - Work.FTS_RegExport.RXT.v2_SlotV α
              (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ') z θ := by
      rw [eV, eV', hsplitV τ hτ, hsplitV τ' hτ']
      ring
    rw [harg]
    exact hPV
  · have harg : CoefU α Φs E g τ z θ - CoefU α Φs E g τ' z θ
        = Work.FTS_RegExport.RXT.v2_SlotU α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
          - Work.FTS_RegExport.RXT.v2_SlotU α
              (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ') z θ := by
      rw [eU, eU', hsplitU τ hτ, hsplitU τ' hτ']
      ring
    rw [harg]
    exact hPU

end Work.FTS_RegExport.RXR5L
end
