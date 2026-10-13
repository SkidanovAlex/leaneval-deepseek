/-
Copyright: work module for the Elgindi finite-time singularity project.

# `LevelOneAsm/eigFun_parseval`: Parseval's identity for the angular eigenbasis of `L₀`

The angular eigenfunctions `Θ_n(θ) = cos θ · p_n(sin θ)` of `EigBasis` are orthogonal for the
weight `cos θ` on `Iθ = [0, π/2]` (`eigFun_orth`), have positive norm (`eigFun_normSq_pos`) and
their span is dense (`eigFun_span_dense`); consequently (the nonzero ones) form a Hilbert basis
of `L²(Iθ, cos θ dθ)`, and Parseval's identity reads

  `∑_n (∫ f Θ_{n+1} cos θ)(∫ Θ_{n+1} g cos θ)/(∫ Θ_{n+1}² cos θ) = ∫ f g cos θ`

for all `f, g ∈ L²(Iθ, cos θ dθ)`.

## The proof

The Hilbert space is `Lp ℝ 2 angMeasure` with `angMeasure = (volume.restrict Iθ).withDensity
(ofReal ∘ cos)`, whose integral is computed by `integral_angMeasure`:
`∫ F ∂angMeasure = ∫ θ in Iθ, cos θ * F θ` (this holds for every `F`).  The hypotheses
`hme`, `hmg`, `hf`, `hg` turn `f` and `g` into classes `x = MemLp.toLp f hfm`,
`y = MemLp.toLp g hgm` (`memLp_of_hyps`).

The normalised eigenfamily `eigE n = (√(eigDn n))⁻¹ • eigLp (n+1)` is orthonormal
(`eigE_orthonormal`) and total (`eigE_span_orthogonal_eq_bot`), so
`HilbertBasis.mkOfOrthogonalEqBot` produces the Hilbert basis and
`HilbertBasis.hasSum_inner_mul_inner` gives

  `HasSum (fun n => ⟪x, eigE n⟫ * ⟪eigE n, y⟫) ⟪x, y⟫`.

The inner products are computed by `inner_toLp_eigE`, `inner_eigE_toLp` and `inner_toLp_toLp`:

  `⟪x, eigE n⟫ = (√(eigDn n))⁻¹ · ∫ θ in Iθ, f θ * Θ_{n+1} θ * cos θ`,
  `⟪eigE n, y⟫ = (√(eigDn n))⁻¹ · ∫ θ in Iθ, Θ_{n+1} θ * g θ * cos θ`,
  `⟪x, y⟫ = ∫ θ in Iθ, f θ * g θ * cos θ`,

and `(√(eigDn n))⁻¹ · (√(eigDn n))⁻¹ = (eigDn n)⁻¹` (with `eigDn n = ∫ Θ_{n+1}² cos > 0`,
`eigDn_pos`), which identifies the `n`-th summand with
`(∫ f Θ_{n+1} cos)(∫ Θ_{n+1} g cos)/(∫ Θ_{n+1}² cos)`.  Transporting the `HasSum` along this
termwise identity gives both the summability and the value of the series.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_span_dense
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_orth
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_normSq_pos
import Submission.Work.FTS.EllipticEst.LevelOneAsm.EigParsevalDefs
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigE_orthonormal
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigE_span_orthogonal_eq_bot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

local notation "Iθ" => Work.Spaces.Iθ

theorem eigFun_parseval {f g : ℝ → ℝ}
    (hme : MeasureTheory.AEMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hmg : MeasureTheory.AEMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hfg : MeasureTheory.IntegrableOn (fun θ => f θ * g θ * Real.cos θ) Work.Spaces.Iθ) :
    Summable (fun n : ℕ =>
        (∫ θ in Work.Spaces.Iθ,
            f θ * Work.FTS.EllipticEst.LevelOneAsm.eigFun (n + 1) θ * Real.cos θ)
          * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.LevelOneAsm.eigFun (n + 1) θ * g θ * Real.cos θ)
          / (∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.LevelOneAsm.eigFun (n + 1) θ) ^ 2 * Real.cos θ))
      ∧ (∑' n : ℕ,
        (∫ θ in Work.Spaces.Iθ,
            f θ * Work.FTS.EllipticEst.LevelOneAsm.eigFun (n + 1) θ * Real.cos θ)
          * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.LevelOneAsm.eigFun (n + 1) θ * g θ * Real.cos θ)
          / (∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.LevelOneAsm.eigFun (n + 1) θ) ^ 2 * Real.cos θ))
        = ∫ θ in Work.Spaces.Iθ, f θ * g θ * Real.cos θ := by
  have hfm : MemLp f 2 angMeasure := memLp_of_hyps hme hf
  have hgm : MemLp g 2 angMeasure := memLp_of_hyps hmg hg
  have hb := HilbertBasis.hasSum_inner_mul_inner
    (HilbertBasis.mkOfOrthogonalEqBot (v := eigE) eigE_orthonormal
      eigE_span_orthogonal_eq_bot)
    (MeasureTheory.MemLp.toLp f hfm) (MeasureTheory.MemLp.toLp g hgm)
  simp only [HilbertBasis.coe_mkOfOrthogonalEqBot] at hb
  have hterm : ∀ n : ℕ,
      inner ℝ (MeasureTheory.MemLp.toLp f hfm) (eigE n)
        * inner ℝ (eigE n) (MeasureTheory.MemLp.toLp g hgm)
      = (∫ θ in Iθ, f θ * eigFun (n + 1) θ * Real.cos θ)
          * (∫ θ in Iθ, eigFun (n + 1) θ * g θ * Real.cos θ)
          / (∫ θ in Iθ, (eigFun (n + 1) θ) ^ 2 * Real.cos θ) := by
    intro n
    rw [inner_toLp_eigE hfm n, inner_eigE_toLp hgm n]
    rw [show (∫ θ in Iθ, (eigFun (n + 1) θ) ^ 2 * Real.cos θ) = eigDn n from rfl]
    set A := ∫ θ in Iθ, f θ * eigFun (n + 1) θ * Real.cos θ with hA
    set B := ∫ θ in Iθ, eigFun (n + 1) θ * g θ * Real.cos θ with hB
    have hd : (0 : ℝ) < eigDn n := eigDn_pos n
    have hmul : (Real.sqrt (eigDn n))⁻¹ * (Real.sqrt (eigDn n))⁻¹ = (eigDn n)⁻¹ := by
      rw [← mul_inv, ← sq, Real.sq_sqrt hd.le]
    rw [div_eq_mul_inv, show (Real.sqrt (eigDn n))⁻¹ * A * ((Real.sqrt (eigDn n))⁻¹ * B)
      = (Real.sqrt (eigDn n))⁻¹ * (Real.sqrt (eigDn n))⁻¹ * (A * B) from by ring, hmul]
    ring
  have hxy : inner ℝ (MeasureTheory.MemLp.toLp f hfm) (MeasureTheory.MemLp.toLp g hgm)
      = ∫ θ in Iθ, f θ * g θ * Real.cos θ :=
    inner_toLp_toLp hfm hgm
  refine ⟨?_, ?_⟩
  · exact hb.summable.congr (fun n => hterm n)
  · rw [tsum_congr (fun n => (hterm n).symm), hb.tsum_eq]
    exact hxy

end Work.FTS.EllipticEst.LevelOneAsm
