import Mathlib
import Submission.Work.GM.Energy.RLocal.Identity

/-!
# Vocabulary for the second moment of `R` over `v ∈ [1,2]`

GM's Lemma 8.2 (`∫_{v≍1} |R(v)|² dv ≪ |W|`) is proved by smoothing the range of integration
with a flat-top bump and expanding `|R|²` into a double sum over `W × W`, whose values are the
Fourier transform of the bump.  The substitution `v = e^u` turns `R(v)` into the plain exponential
sum `Σ_{t∈W} e^{itu}`, so the whole argument takes place on the `u`-line:

`∫_1^2 ‖R(v)‖² dv = ∫_0^{log 2} e^u ‖F(u)‖² du ≤ 2 ∫_ℝ ψ(u)‖F(u)‖² du = 2 Σ_{t,s∈W} Ψ(t-s)`,

where `F(u) = Σ_{t∈W} e^{itu}`, `ψ` is a flat-top bump equal to `1` on `[0,2π]`, and
`Ψ(δ) = ∫ ψ(u)e^{iδu}du` is (up to scaling) the Fourier transform of `ψ`, hence rapidly decaying.
Since `W` is `1`-separated, `Σ_{s ≠ t} |Ψ(t-s)|` is bounded uniformly in `t`, which gives the
bound `≪ |W|` with an absolute constant.

This file fixes the notation; the facts about it live in the sibling files
`SqBumpFacts`, `SqPsiDecay`, `SqExpansion`, `SumRecipSq`, `SubstExp`.
-/

namespace Work.GM.Energy.RMoments

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform

set_option autoImplicit false

open Work.GM.Energy.RLocal (psiBump psiBump_eq_one psiBump_contDiff psiBump_support_subset
  psiBump_hasCompactSupport)

/-- GM's flat-top bump `psiBump`, rescaled so that it equals `1` on `[0, 2π]`. -/
noncomputable def sqBump (u : ℝ) : ℝ := psiBump (u / (2 * Real.pi))

/-- The complexification of `sqBump`, to which the Fourier transform is applied. -/
noncomputable def sqBumpC (u : ℝ) : ℂ := (sqBump u : ℂ)

/-- The Fourier kernel `Ψ(δ) = ∫ ψ(u) e^{iδu} du` of the bump. -/
noncomputable def sqPsi (δ : ℝ) : ℂ :=
  ∫ u, sqBumpC u * Complex.exp (Complex.I * ((δ * u : ℝ) : ℂ))

/-- The exponential sum `Σ_{t∈W} e^{itu}`, equal to `R(W, e^u)`. -/
noncomputable def sqF (W : Finset ℝ) (u : ℝ) : ℂ :=
  ∑ t ∈ W, Complex.exp (Complex.I * ((t * u : ℝ) : ℂ))

/-- `Rfun W (e^u) = Σ_{t ∈ W} e^{itu}`: on the positive half-line, `R` is the exponential sum. -/
lemma Rfun_exp_eq_sqF (W : Finset ℝ) (u : ℝ) :
    Submission.GM.Rfun W (Real.exp u) = sqF W u := by
  rw [show Real.exp u = 1 * Real.exp u by ring,
    RLocal.Rfun_mul_exp_eq_sum W one_pos u, sqF]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Real.log_one, zero_add]

/-- `sqBump` is `1` on `[0, 2π]`. -/
lemma sqBump_eq_one {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) : sqBump u = 1 := by
  refine psiBump_eq_one ⟨?_, ?_⟩
  · exact div_nonneg hu.1 (by positivity)
  · rw [div_le_one (by positivity)]; exact hu.2

end Work.GM.Energy.RMoments
