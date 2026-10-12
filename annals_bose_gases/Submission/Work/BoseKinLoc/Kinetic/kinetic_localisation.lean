import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Assembly.assembly_symbol_general
import Submission.Work.BoseKinLoc.Gap.gapBound_general
import Submission.Work.BoseKinLoc.Gap.gap_bound
import Submission.Work.BoseKinLoc.Kinetic.kinetic_localisation_of_pieces
import Submission.Work.BoseKinLoc.Momentum.momForm_u_integral_alt
import Submission.Work.BoseKinLoc.Momentum.momentum_bound
import Submission.Work.BoseKinLoc.NeuFrac.neumann_bound
import Submission.Work.BoseKinLoc.Tprime.tprime_two_regime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseKinLoc.Kinetic.kinetic_localisation` — FS `lem:LocKinEn`

The headline of node C: FS's kinetic-energy localisation `∫_u 𝒯_u du ≤ −Δ` at the
**decoupled** parameters (the residual `Work.BoseKinLoc.KineticLocalisation` of
`Submission/Work/BoseKinLoc/Residuals.lean`), in its unconditional form

`∃ c₀ > 0, KineticLocalisation c₀` :  `∫_u fsT ℓ d s ε_T b u ψ ≤ dSpace ψ`
for every smooth compactly supported `ψ` and every `(ℓ,d,s,ε_T,b) ∈ KinRegime c₀`.

## Route

`fsT = neuWord + gapWord + momWord + mainWord` (`Defs.fsT_eq_sum`), and FS prove
`lem:LocKinEn` from five named residuals (`Residuals.lean`), each of which is a *separate*
analytic theorem about the one-body symbols:

| residual | source | proved in |
|---|---|---|
| `NeumannBound` | BS `eq:Neumannineq` = FS `(44)` | `NeuFrac/neumann_bound` |
| `GapBound β` | BS `eq:Quav` + Taylor | `Gap/gap_bound`, `Gap/gapBound_general` |
| `MomBound` | FS `eq:Q1Qslide` | `Momentum/momForm_u_integral_alt` + `momBound_of_u_average` (this module) |
| `TprimeBound C` | BS `lm:kinloc` (two-regime symbol) | `Tprime/tprime_two_regime` |
| `AssemblySymbol β C` | BS `lm:Tu`'s final budget | `Assembly/assembly_two_regime`, `Assembly/assembly_symbol_general` |

The **packaging** — the `u`-integral split of `fsT` into its four words, the termwise
estimates above, and the momentum-space bookkeeping against `AssemblySymbol β C` and
`dSpace ψ = (2π)⁻³∫‖p‖²‖ψ̂(p)‖²` — is the proved lemma
`Kinetic/kinetic_localisation_of_pieces.kinetic_localisation_of_pieces`.

The present module does the **constant alignment** that the packaging needs and that is
*not* supplied by the individual residual files: `kinetic_localisation_of_pieces` takes
`GapBound β`, `TprimeBound C` and `AssemblySymbol β C` **at the same pair `(β,C)`**, while

* `TprimeBound`'s constant is the one produced by the near-region Taylor analysis of
  `Tprime/near_coefficient` (a `C ≥ 1`, in general `≫ 1`), and
* `Assembly/two_regime_core` was verified for the *fixed* pair `β = 1/2`, `C = 1`.

So the alignment is: take the pair `(β, C) = (1/2, C_T)` with `C_T` the Tprime constant,
get `GapBound (1/2)` from the sharp-range gap bound (`Gap/gapBound_general`), and get
`AssemblySymbol (1/2) C_T` from the *general-constant* budget
(`Assembly/assembly_symbol_general`, whose `c₀` shrinks with `C_T` and `β`).  Then the
packaging delivers `∃ c₀ > 0, KineticLocalisation c₀` unconditionally.

The one residual that is *not* a single ready-made theorem is the momentum term: FS
`eq:Q1Qslide` is proved in `Momentum/` from two analytic inputs — the exact `u`-average of
the sliding mean-free box family (`Momentum/momForm_u_integral_alt`, the Fourier-diagonal
identity `∫_u momForm = (2π)⁻³∫_s ‖ψ̂(s)‖² msym(ℓ,d,s)`) and the pointwise bound on the
sliding cube symbol (`Momentum/symbol_bound`) — and this module contains the (short)
assembly `momBound_of_u_average` that turns exactly those two into the residual `MomBound`,
using `Momentum/momBound_of_pieces`.  It is stated with the identity as a hypothesis, so it
does not depend on any particular proof of it.

The two termwise lemmas `gap_word_le`, `mom_word_le` below record, for the reader, the
conversion of the residual statements into bounds on the corresponding *words* of `fsT`
(they are the two places where `fsT`'s definitional shape is used); `gapBound_of_le` is
the monotonicity of `GapBound` in `β`, which makes the sharp range `(0,1/2]` of
`Gap/gapBound_general` usable at any `β < 1` produced by the assembly.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic

open Submission.BoseGases

/-- `GapBound` is antitone in the *reverse* direction: a bound at `β` gives one at every
`β' ≤ β` (the symbol `β ↦ β⁻¹x/(x+β)` is decreasing in `β`). -/
theorem gapBound_of_le {β β' : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (h : β' ≤ β)
    (hgap : Work.BoseKinLoc.GapBound β) : Work.BoseKinLoc.GapBound β' := by
  intro ψ hψ hcs ℓ hℓ hint
  refine le_trans (hgap ψ hψ hcs ℓ hℓ hint) ?_
  unfold Work.BoseKinLoc.gapFrac
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hbase : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) := by
    simpa only [Work.BoseKinLoc.fhat] using Work.BSKinetic.integrable_kinFT_sq ψ hψ hcs
  have hInt : ∀ β₀ : ℝ, 0 < β₀ → Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.gapSym ℓ β₀ p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) := by
    intro β₀ hβ₀
    have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.gapSym ℓ β₀ p) := by
      unfold Work.BoseKinLoc.gapSym
      refine continuous_const.mul (Continuous.div ?_ ?_ ?_) <;> try fun_prop
      intro p; positivity
    refine Integrable.mono' (hbase.const_mul β₀⁻¹)
      (hcont.aestronglyMeasurable.mul hbase.aestronglyMeasurable) ?_
    filter_upwards with p
    rw [Real.norm_of_nonneg (mul_nonneg (by unfold Work.BoseKinLoc.gapSym; positivity)
      (sq_nonneg _))]
    have hfrac : (ℓ ^ 2 * ‖p‖ ^ 2) / (ℓ ^ 2 * ‖p‖ ^ 2 + β₀) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [sq_nonneg ℓ, sq_nonneg ‖p‖]
    unfold Work.BoseKinLoc.gapSym
    calc β₀⁻¹ * (ℓ ^ 2 * ‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β₀)) * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2
        = β₀⁻¹ * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 *
            ((ℓ ^ 2 * ‖p‖ ^ 2) / (ℓ ^ 2 * ‖p‖ ^ 2 + β₀)) := by ring
      _ ≤ β₀⁻¹ * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hfrac
            (mul_nonneg (inv_nonneg.mpr hβ₀.le) (sq_nonneg _))
      _ = β₀⁻¹ * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 := by ring
  refine integral_mono_of_nonneg (Eventually.of_forall fun p =>
    mul_nonneg (by unfold Work.BoseKinLoc.gapSym; positivity) (sq_nonneg _)) (hInt β' hβ') ?_
  filter_upwards with p
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  unfold Work.BoseKinLoc.gapSym
  have hx : 0 ≤ ℓ ^ 2 * ‖p‖ ^ 2 := by positivity
  have h1 : 0 < β * (ℓ ^ 2 * ‖p‖ ^ 2 + β) := by positivity
  have h2 : 0 < β' * (ℓ ^ 2 * ‖p‖ ^ 2 + β') := by positivity
  have hden : β' * (ℓ ^ 2 * ‖p‖ ^ 2 + β') ≤ β * (ℓ ^ 2 * ‖p‖ ^ 2 + β) := by
    nlinarith [hx, h, mul_nonneg hx (sub_nonneg.mpr h)]
  rw [show β⁻¹ * (ℓ ^ 2 * ‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β))
        = (ℓ ^ 2 * ‖p‖ ^ 2) / (β * (ℓ ^ 2 * ‖p‖ ^ 2 + β)) from by field_simp,
    show β'⁻¹ * (ℓ ^ 2 * ‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β'))
        = (ℓ ^ 2 * ‖p‖ ^ 2) / (β' * (ℓ ^ 2 * ‖p‖ ^ 2 + β')) from by field_simp]
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [hx, hden]

/-- The gap piece of the assembly: `GapBound β` plus the definitional shape of `gapWord`. -/
theorem gap_word_le {β : ℝ} (hgap : Work.BoseKinLoc.GapBound β)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) (ℓ b : ℝ) (hℓ : 0 < ℓ) (hb : 0 ≤ b)
    (hint : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.gapBare ℓ u ψ)) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.gapWord ℓ b u ψ)
      ≤ b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapFrac ℓ β ψ := by
  have h := hgap ψ hψ hcs ℓ hℓ hint
  have heq : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.gapWord ℓ b u ψ)
      = b * ℓ ^ (-2 : ℤ) *
          ∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.gapBare ℓ u ψ := by
    rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.gapWord ℓ b u ψ)
        = (fun u : EuclideanSpace ℝ (Fin 3) =>
            (b * ℓ ^ (-2 : ℤ)) * Work.BoseKinLoc.gapBare ℓ u ψ) from by
      funext u; rfl]
    rw [integral_const_mul]
  rw [heq]
  exact mul_le_mul_of_nonneg_left h (mul_nonneg hb (by positivity))

/-- The momentum piece of the assembly: `MomBound` at the admissible `b`. -/
theorem mom_word_le {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hmom : ∀ b : ℝ, 0 < b → b ≤ b₀ → ∀ (ψ : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ (⊤ : ENat) ψ → HasCompactSupport ψ → ∀ (ℓ d : ℝ), 0 < ℓ → 0 < d → d ≤ 1 →
        Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.momForm ℓ d u ψ) →
          b * (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momForm ℓ d u ψ)
            ≤ (1 / 2) * Work.BoseKinLoc.raFrac ℓ d ψ)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) (ℓ d εT b : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hε : 0 < εT) (hb : 0 < b) (hbb₀ : b ≤ b₀)
    (hint : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.momForm ℓ d u ψ)) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momWord ℓ d εT b u ψ)
      ≤ (1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.raFrac ℓ d ψ := by
  have h := hmom b hb hbb₀ ψ hψ hcs ℓ d hℓ hd hd1 hint
  have heq : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momWord ℓ d εT b u ψ)
      = b * εT * (d * ℓ) ^ (-2 : ℤ) *
          ∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momForm ℓ d u ψ := by
    rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.momWord ℓ d εT b u ψ)
        = (fun u : EuclideanSpace ℝ (Fin 3) =>
            (b * εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.momForm ℓ d u ψ) from by
      funext u; rfl]
    rw [integral_const_mul]
  rw [heq]
  have hdℓ : 0 < (d * ℓ) ^ (-2 : ℤ) := zpow_pos (mul_pos hd hℓ) _
  nlinarith [h, mul_pos hε hdℓ, hb, hε, mul_pos (mul_pos hb hε) hdℓ]

/-- **The momentum residual `MomBound` from the exact `u`-average identity.**  This is the
assembly of FS `eq:Q1Qslide` from its two analytic inputs that are *not* themselves stated at the
level of `MomBound`: the exact `u`-average identity of the sliding mean-free box family
(`hId`, the Fourier-diagonal form in `Momentum/momForm_u_integral`) and the pointwise bound on
the sliding cube symbol (`Momentum/symbol_bound`).

It is stated with `hId` as a hypothesis so that it is independent of the module that supplies the
identity; fed with `Momentum.momForm_u_integral` it reproduces `Momentum.momentum_bound`. -/
theorem momBound_of_u_average
    (hId : ∀ (ψ : EuclideanSpace ℝ (Fin 3) → ℝ), ContDiff ℝ (⊤ : ENat) ψ →
      HasCompactSupport ψ → ∀ (ℓ d : ℝ), 0 < ℓ → 0 < d →
        (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momForm ℓ d u ψ)
          = ((2 * Real.pi) ^ 3)⁻¹ * ∫ s : EuclideanSpace ℝ (Fin 3),
              ‖Work.BoseKinLoc.fhat ψ s‖ ^ 2 * Work.BoseKinLoc.Momentum.momSym ℓ d s) :
    Work.BoseKinLoc.MomBound := by
  obtain ⟨C₁, hC₁, hM, hH⟩ := Work.BoseKinLoc.Momentum.cubFT_exterior_bounds
  obtain ⟨hTotInt, hTot⟩ := Work.BoseKinLoc.Momentum.cubFT_total
  have hM' : ∀ L : ℝ, 0 < L → ∫ w in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖},
      (Work.BoseKinLoc.Momentum.cubFT w) ^ 2 ≤ max C₁ 4096 / L := fun L hL =>
    le_trans (hM L hL) (div_le_div_of_nonneg_right (le_max_left _ _) hL.le)
  have hH' : ∀ L : ℝ, 0 < L → ∑ i : Fin 3,
      ∫ w in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖},
        (fderiv ℝ Work.BoseKinLoc.Momentum.cubFT w (Submission.BoseGases.kcStdBasis i)) ^ 2
      ≤ max C₁ 4096 / L := fun L hL =>
    le_trans (hH L hL) (div_le_div_of_nonneg_right (le_max_left _ _) hL.le)
  have hTot' : ∫ q : EuclideanSpace ℝ (Fin 3), (Work.BoseKinLoc.Momentum.cubFT q) ^ 2
      ≤ max C₁ 4096 := le_trans hTot (le_max_right _ _)
  obtain ⟨C, hC, hSym⟩ := Work.BoseKinLoc.Momentum.symbol_bound (max C₁ 4096)
    (lt_max_of_lt_left hC₁) hM' hTot' hH' Work.BoseKinLoc.Momentum.abs_one_sub_cubFT_le
  refine Work.BoseKinLoc.Momentum.momBound_of_pieces ?_ ⟨C, hC, hSym⟩ ?_
  · intro ψ hψ hcs ℓ d hℓ hd
    rw [hId ψ hψ hcs ℓ d hℓ hd]
  · exact fun ψ hψ hcs => Work.BoseKinLoc.Momentum.integrable_fhat_sq ψ hψ hcs

/-- **FS `lem:LocKinEn` in its unconditional form.**  There is a universal `c₀ > 0` such that
at every admissible parameter tuple the `u`-average of the localised kinetic word `fsT` is
dominated by the full-space Dirichlet kinetic form `dSpace ψ`:
`∫_u fsT ℓ d s ε_T b u ψ ≤ dSpace ψ`.

The `c₀` is the one of the assembled momentum budget `AssemblySymbol (1/2) C`, with `C` the
near-region constant of the two-regime `T'` bound; `β = 1/2` is the extremal value of the
sharp range of `GapBound` (see `Gap/gapBound_general`). -/
theorem kinetic_localisation : ∃ c₀ : ℝ, 0 < c₀ ∧ Work.BoseKinLoc.KineticLocalisation c₀ := by
  -- the four residual constants: `C` from the two-regime `T'` bound, `β = 1/2` fixed
  obtain ⟨C, hC, htpr⟩ := Work.BoseKinLoc.Tprime.tprime_two_regime
  have hβ : (0 : ℝ) < 1 / 2 := by norm_num
  have hβ1 : (1 / 2 : ℝ) < 1 := by norm_num
  -- `GapBound` at the extremal `β = 1/2` (the residual `Gap/gap_bound` is at the same value)
  have hgap : Work.BoseKinLoc.GapBound (1 / 2) :=
    Work.BoseKinLoc.Gap.gapBound_general (1 / 2) hβ le_rfl
  -- the momentum budget at the *same* pair `(β, C)` as the residuals above
  obtain ⟨c₀, hc₀, hasm⟩ :=
    Work.BoseKinLoc.Assembly.assembly_symbol_general (1 / 2) C hβ hβ1 hC
  -- `MomBound` from the exact `u`-average identity of the sliding box family and the
  -- pointwise bound on the sliding cube symbol
  have hmom : Work.BoseKinLoc.MomBound :=
    momBound_of_u_average fun ψ hψ hcs ℓ d hℓ hd =>
      Work.BoseKinLoc.Momentum.momForm_u_integral_alt ψ hψ hcs ℓ d hℓ hd
  exact kinetic_localisation_of_pieces hβ hβ1 hC hgap
    Work.BoseKinLoc.NeuFrac.neumann_bound hmom htpr hasm

end Work.BoseKinLoc.Kinetic
