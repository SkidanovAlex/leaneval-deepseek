import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaXnBound
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem
import Submission.Work.FTS.StrongEps.EpsRLX.BasicFacts
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.OpenPkg.Basic

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
