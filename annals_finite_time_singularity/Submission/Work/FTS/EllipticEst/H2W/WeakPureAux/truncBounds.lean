import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.H2W.lzero1SliceGrowth
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthSlice
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `truncBounds`: the truncated (interval) growth bounds for `Dfun` and `Rfun`

The Wronskian-type functionals of `H2W.LzeroGrowth`,

  `Dfun u θ = cos θ · (u θ · 2cos 2θ − u' θ · sin 2θ)`,      `Rfun u θ = u θ / sin 2θ`,

satisfy the two exact identities (`H2W.Lzero1Growth`)

  `(Dfun u)' θ = 2 · Lzero1 u θ · sinθcos²θ`,   `(Rfun u)' θ = − Dfun u θ / (cos θ · sin²2θ)`.

Integrating both against the *absolute values* of the right-hand sides over the interval
between `θ` and the reference point `π/4` (where `sin 2θ = 1`), and using only
`|A − B| ≤ |A| + |B|`, gives the four truncated bounds stated in `truncBounds`: the pointwise
value at `θ` is controlled by the value at `π/4` plus the accumulated growth of the source
`Lzero1 u` resp. of `Dfun u`.

Everything is `C²`: only `Dfun_hasDerivAt`/`Rfun_hasDerivAt` at `ContDiffOn ℝ 2` are used, plus
the fundamental theorem of calculus on a compact subinterval of the *open* interval
`(0, π/2)` (so the endpoints `0`, `π/2`, where the coefficients degenerate, are never touched).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

set_option autoImplicit false

/-- A closed interval `[a,b]`, `a ≤ b`, with `0 < a` and `b < π/2` sits inside `(0, π/2)`. -/
private lemma uIcc_subset_Ioo {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b) :
    Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi / 2) := by
  intro s hs
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hs
  exact ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩

/-- The absolute value of the derivative of `Rfun` is the absolute value of `Dfun` divided by
the (positive) kernel `cos θ · sin²2θ`. -/
private lemma abs_Rderiv (u : ℝ → ℝ) {s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) :
    |-(LzeroGrowth.Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|
      = |LzeroGrowth.Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2) := by
  have hc : 0 < Real.cos s :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hs.1], hs.2⟩
  have hs2 : 0 < Real.sin (2 * s) := LzeroGrowth.sin_two_pos hs
  have hden : 0 < Real.cos s * (Real.sin (2 * s)) ^ 2 := mul_pos hc (pow_pos hs2 2)
  rw [abs_div, abs_neg, abs_of_pos hden]

/-- `|x| ≤ |c| + d` whenever `|x − c| ≤ d`. -/
private lemma abs_le_of_abs_sub_le {x c d : ℝ} (h : |x - c| ≤ d) : |x| ≤ |c| + d := by
  have h1 : |x| ≤ |x - c| + |c| := by
    calc |x| = |(x - c) + c| := by ring_nf
      _ ≤ |x - c| + |c| := abs_add_le _ _
  linarith

/-- **The truncated oscillation of `Dfun`.**  For `a ≤ b` inside `(0, π/2)`,
`|D u b − D u a| ≤ 2 ∫_a^b sinθcos²θ · |Lzero1 u|`. -/
private lemma Dfun_diff_le (u : ℝ → ℝ) (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (hab : a ≤ b) (hsub : Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi / 2)) :
    |LzeroGrowth.Dfun u b - LzeroGrowth.Dfun u a|
      ≤ 2 * ∫ s in a..b, Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s| := by
  have hftc : ∫ s in a..b, 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s
      = LzeroGrowth.Dfun u b - LzeroGrowth.Dfun u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => Lzero1Growth.Dfun_hasDerivAt hu (hsub hs))
      (Lzero1Growth.intervalIntegrable_two_mul hu hsub)
  rw [← hftc]
  calc |∫ s in a..b, 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|
      ≤ ∫ s in a..b, |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ = ∫ s in a..b, 2 * (Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|) := by
        refine intervalIntegral.integral_congr (fun s hs => ?_)
        have hs' : s ∈ Set.Ioo 0 (Real.pi / 2) := hsub hs
        rw [abs_mul, abs_mul,
          abs_of_nonneg (LzeroGrowth.sinCos2_nonneg (LzeroGrowth.mem_Iθ_of_mem_Ioo hs')),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
    _ = 2 * ∫ s in a..b, Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s| :=
        intervalIntegral.integral_const_mul 2 _

/-- **The truncated oscillation of `Rfun`.**  For `a ≤ b` inside `(0, π/2)`,
`|R u b − R u a| ≤ ∫_a^b |D u| /(cos θ · sin²2θ)`. -/
private lemma Rfun_diff_le (u : ℝ → ℝ) (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (hab : a ≤ b) (hsub : Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi / 2)) :
    |LzeroGrowth.Rfun u b - LzeroGrowth.Rfun u a|
      ≤ ∫ s in a..b,
          |LzeroGrowth.Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2) := by
  have hInt : IntervalIntegrable
      (fun s : ℝ => -(LzeroGrowth.Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2))
      volume a b :=
    ((Lzero1Growth.continuousOn_Rderiv hu).mono hsub).intervalIntegrable
  have hftc : ∫ s in a..b, -(LzeroGrowth.Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)
      = LzeroGrowth.Rfun u b - LzeroGrowth.Rfun u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => Lzero1Growth.Rfun_hasDerivAt hu (hsub hs)) hInt
  rw [← hftc]
  calc |∫ s in a..b, -(LzeroGrowth.Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|
      ≤ ∫ s in a..b, |-(LzeroGrowth.Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ = ∫ s in a..b, |LzeroGrowth.Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2) :=
        intervalIntegral.integral_congr (fun s hs => abs_Rderiv u (hsub hs))

theorem truncBounds (u : ℝ → ℝ) (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    (∀ θ ∈ Set.Ioc (0:ℝ) (Real.pi / 4),
        |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u θ| ≤
          |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)|
          + 2 * ∫ s in θ..(Real.pi / 4),
              Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|)
    ∧ (∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u θ| ≤
          |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)|
          + 2 * ∫ s in (Real.pi / 4)..θ,
              Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|)
    ∧ (∀ θ ∈ Set.Ioc (0:ℝ) (Real.pi / 4),
        |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ| ≤
          |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi / 4)|
          + ∫ s in θ..(Real.pi / 4),
              |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s|
                / (Real.cos s * (Real.sin (2 * s)) ^ 2))
    ∧ (∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ| ≤
          |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi / 4)|
          + ∫ s in (Real.pi / 4)..θ,
              |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s|
                / (Real.cos s * (Real.sin (2 * s)) ^ 2)) := by
  have hpi4pos : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `Dfun`, left of the reference point: `|D θ| ≤ |D(π/4)| + 2 ∫_θ^{π/4}`
    intro θ hθ
    have hle : θ ≤ Real.pi / 4 := hθ.2
    have hsub : Set.uIcc θ (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) :=
      uIcc_subset_Ioo hθ.1 hpi4lt hle
    refine abs_le_of_abs_sub_le ?_
    rw [abs_sub_comm]
    exact Dfun_diff_le u hu hle hsub
  · -- `Dfun`, right of the reference point
    intro θ hθ
    have hle : Real.pi / 4 ≤ θ := hθ.1
    have hsub : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo 0 (Real.pi / 2) :=
      uIcc_subset_Ioo hpi4pos hθ.2 hle
    exact abs_le_of_abs_sub_le (Dfun_diff_le u hu hle hsub)
  · -- `Rfun`, left of the reference point
    intro θ hθ
    have hle : θ ≤ Real.pi / 4 := hθ.2
    have hsub : Set.uIcc θ (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) :=
      uIcc_subset_Ioo hθ.1 hpi4lt hle
    refine abs_le_of_abs_sub_le ?_
    rw [abs_sub_comm]
    exact Rfun_diff_le u hu hle hsub
  · -- `Rfun`, right of the reference point
    intro θ hθ
    have hle : Real.pi / 4 ≤ θ := hθ.1
    have hsub : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo 0 (Real.pi / 2) :=
      uIcc_subset_Ioo hpi4pos hθ.2 hle
    exact abs_le_of_abs_sub_le (Rfun_diff_le u hu hle hsub)

end Work.FTS.EllipticEst.H2W.WeakPureAux
