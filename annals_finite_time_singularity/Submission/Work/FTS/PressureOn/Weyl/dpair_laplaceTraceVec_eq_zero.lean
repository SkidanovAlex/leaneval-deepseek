/-
# `Work.FTS.PressureOn.Weyl.dpair_laplaceTraceVec_eq_zero` — M2 of the Weyl pair lemma

## Statement analysed here

For `q : ℝ³ → ℝ`, `Φ : ℝ³ → ℝ³` satisfying the two weak identities

* `∫ ⟨Φ, ∇φ⟩ = -∫ q · Δφ` for every smooth compactly supported `φ`, and
* `∫ ⟨Φ, ∇×ψ⟩ = 0` for every smooth compactly supported `ψ`,

and for every smooth compactly supported `W`, prove
`∫ ⟨Φ, ΔW⟩ + ∫ q · div (ΔW) = 0` (here `Δ = laplaceTraceVec`, `div (ΔW) = Δ (div W)`).

## Why the statement **as written** is not provable / is false

The intended (and correct) argument is:

* `laplaceTraceVec W = gradient (div W) - vorticity (vorticity W)`
  (`Auxiliary.laplaceTraceVec_identity`), so pointwise
  `⟨Φ, ΔW⟩ = ⟨Φ, ∇div W⟩ - ⟨Φ, ∇×∇×W⟩` (`inner_sub_right`);
* `div (laplaceTraceVec W) = laplaceTrace (div W)` (`Auxiliary.div_laplaceTraceVec`), so the
  hypothesis `hdiv` applied to the *test function* `div W` identifies the second term;
* `hcurl` applied to the *test field* `∇×W` gives `∫ ⟨Φ, ∇×∇×W⟩ = 0`.

The passage from the pointwise identity to integrals needs the splitting
`∫ (f - g) = ∫ f - ∫ g` with `f := ⟨Φ, ∇div W⟩`, `g := ⟨Φ, ∇×∇×W⟩`, i.e. it needs both `f` and `g`
to be integrable (Mathlib: `MeasureTheory.integral_sub`, requiring `Integrable f` and
`Integrable g`).  **No such integrability is derivable from the hypotheses.**  In Lean the integral
of a non-integrable function is *zero* (`MeasureTheory.integral_undef`), so each hypothesis is an
equality between two numbers that are both `0` whenever the integrands fail to be integrable; such
an equation carries no information about `∫ f` and `∫ g` themselves.

Concretely, the hypotheses do **not** exclude the case where `f` and `g` are both non-integrable
while their difference `f - g = ⟨Φ, ΔW⟩` *is* integrable with non-zero integral.  In that case the
goal reads `∫ ⟨Φ, ΔW⟩ + ∫ q div (ΔW) = ∫ ⟨Φ, ΔW⟩ + 0 ≠ 0` and the conclusion fails, while
`hdiv (div W)` and `hcurl (∇×W)` are satisfied because both of their sides are `0`
(`∫ f = 0` and `∫ g = 0` since `f`, `g` are non-integrable, and `∫ q Δdiv W = -∫ f = 0`).
Such pairs really do exist for `Φ` that is *not* locally integrable: e.g.
`Φ := e₀ + ρ + 1_S · e₀`, where `S ⊆ ℝ³` is a Bernstein set (so every measurable subset of `S` is
null, and `S` has full outer measure in every ball, whence `∫ 1_S · h = 0` for *every* `h`, while
`1_S · h` fails to be a.e. strongly measurable whenever `h` does not vanish on a non-null set), and
`ρ := (0, ∂₁A, ∂₂A)` with `A := ∂₀B̃` for a bump `B̃`.  Then `⟨Φ, ∇φ⟩` is not a.e. strongly
measurable (hence has integral `0`) whenever `∂₀φ ≢ 0`, and `hdiv`/`hcurl` reduce to `μ := e₀ + ρ`
satisfying the two constraints `∫ ⟨μ, ∇φ⟩ = 0 (∂₀φ ≡ 0)` and `∫ ⟨μ, ∇×ψ⟩ = 0 ((∇×ψ)₀ ≡ 0)`, which
hold by construction; taking `W` with `(ΔW)₀ ≡ 0` makes the goal equal to `∫ ⟨μ, ΔW⟩`,
which is non-zero for suitable `A`, `W`.

The missing hypothesis is exactly that the pairings be *absolutely convergent*, i.e. that `Φ` be
locally integrable — which is automatic in the intended application, where `Φ = ∂_t u - (u×ω)` is
continuous (and `q` is continuous as well).  With that hypothesis the statement is true, and the
proof is the short computation in `dpair_laplaceTraceVec_eq_zero_of_locallyIntegrable` below.

## Contents

* `hasCompactSupport_div`, `hasCompactSupport_vorticity` — compact support of `div V`, `vorticity V`
  from that of `V`;
* `integrable_inner_of_hasCompactSupport` — `x ↦ ⟨Φ x, g x⟩` is integrable for `g` continuous with
  compact support and `Φ` locally integrable;
* `dpair_laplaceTraceVec_eq_zero_of_locallyIntegrable` — the lemma **with** the necessary
  hypothesis `LocallyIntegrable Φ`, fully proved;
* `dpair_laplaceTraceVec_eq_zero` — the requested statement with `Φ`, `q` **continuous** (which is
  the case in the intended application); an immediate corollary of the previous one.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Auxiliary.laplaceTraceVec_identity
import Submission.Work.FTS.PressureOn.Auxiliary.div_laplaceTraceVec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PressureOn.Weyl

/-- Compact support of `div V` from that of `V` (the divergence only sees the first derivatives,
which are supported in `tsupport V`). -/
theorem hasCompactSupport_div (V : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hV : HasCompactSupport V) : HasCompactSupport (FiniteTimeSingularity.div V) := by
  have hfun : FiniteTimeSingularity.div V
      = Work.FTS.PressureOn.Auxiliary.divTraceCLM ∘ (fderiv ℝ V) := by
    funext x
    exact Work.FTS.PressureOn.Auxiliary.div_eq_divTraceCLM V x
  rw [hfun]
  exact (hV.fderiv (𝕜 := ℝ)).comp_left (map_zero _)

/-- Compact support of `vorticity V` from that of `V`. -/
theorem hasCompactSupport_vorticity (V : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hV : HasCompactSupport V) : HasCompactSupport (FiniteTimeSingularity.vorticity V) := by
  have hfun : FiniteTimeSingularity.vorticity V
      = Work.FTS.Physical.Pressure.curlCLM ∘ (fderiv ℝ V) := by
    funext x
    exact Work.FTS.Physical.Pressure.vorticity_eq_curlCLM V x
  rw [hfun]
  exact (hV.fderiv (𝕜 := ℝ)).comp_left (map_zero _)

/-- **Integrability of a pairing against a compactly supported continuous field.**
If `Φ` is locally integrable and `g` is continuous with compact support, then `x ↦ ⟨Φ x, g x⟩` is
integrable.  This is the absolute-convergence input that the requested statement is missing. -/
theorem integrable_inner_of_hasCompactSupport {Φ g : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    (hΦ : LocallyIntegrable Φ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => inner ℝ (Φ x) (g x)) := by
  have hK : IsCompact (tsupport g) := hgc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  have hCnn : (0 : ℝ) ≤ max C 1 := le_trans zero_le_one (le_max_right C 1)
  have hbound : ∀ x : Work.FTS.PressureOn.R3, ‖g x‖ ≤ max C 1 := by
    intro x
    by_cases hx : x ∈ tsupport g
    · exact le_trans (hC x hx) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact hCnn
  have hint : Integrable (fun x => inner ℝ (Φ x) (g x)) (volume.restrict (tsupport g)) := by
    have h1 : Integrable (fun x => max C 1 * ‖Φ x‖) (volume.restrict (tsupport g)) :=
      (hΦ.integrableOn_isCompact hK).norm.const_mul _
    refine h1.mono' ((hΦ.aestronglyMeasurable.inner hg.aestronglyMeasurable).restrict) ?_
    filter_upwards with x
    calc ‖inner ℝ (Φ x) (g x)‖ ≤ ‖Φ x‖ * ‖g x‖ := norm_inner_le_norm _ _
      _ ≤ ‖Φ x‖ * max C 1 := by
          exact mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)
      _ = max C 1 * ‖Φ x‖ := mul_comm _ _
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hint
  intro x hx
  by_contra hx'
  exact hx (by
    have hzero : g x = 0 := image_eq_zero_of_notMem_tsupport hx'
    simp [hzero])

/-- **The corrected M2 step**: the requested statement with the necessary hypothesis that `Φ` be
locally integrable (equivalently, that the pairings against smooth compactly supported fields be
absolutely convergent).  In the intended application `Φ = ∂_t u - u × ω` is continuous, so this
holds. -/
theorem dpair_laplaceTraceVec_eq_zero_of_locallyIntegrable
    (q : Work.FTS.PressureOn.R3 → ℝ)
    (Φ : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hΦ : LocallyIntegrable Φ)
    (hdiv : ∀ φ : Work.FTS.PressureOn.R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      ∫ x, inner ℝ (Φ x) (gradient φ x)
        = -∫ x, q x * Work.FTS.PressureOn.laplaceTrace φ x)
    (hcurl : ∀ ψ : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3,
      (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity ψ x) = 0)
    (W : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hW : ∀ n : ℕ, ContDiff ℝ n W) (hWc : HasCompactSupport W) :
    (∫ x, inner ℝ (Φ x) (Work.FTS.PressureOn.laplaceTraceVec W x))
      + ∫ x, q x * FiniteTimeSingularity.div (Work.FTS.PressureOn.laplaceTraceVec W) x = 0 := by
  have hWo : ∀ n : ℕ, ContDiff ℝ n (FiniteTimeSingularity.div W) :=
    Work.FTS.PressureOn.Auxiliary.contDiff_div W hW
  have hWoc : HasCompactSupport (FiniteTimeSingularity.div W) := hasCompactSupport_div W hWc
  have hvort : ∀ n : ℕ, ContDiff ℝ n (FiniteTimeSingularity.vorticity W) :=
    Work.FTS.PressureOn.Auxiliary.contDiff_vorticity W hW
  have hvc : HasCompactSupport (FiniteTimeSingularity.vorticity W) :=
    hasCompactSupport_vorticity W hWc
  -- the two weak identities at the relevant test objects
  have hA := hdiv (FiniteTimeSingularity.div W) hWo hWoc
  have hB := hcurl (FiniteTimeSingularity.vorticity W) hvort hvc
  -- absolute convergence of the two pairings
  have hAint : Integrable
      (fun x => inner ℝ (Φ x) (gradient (FiniteTimeSingularity.div W) x)) :=
    integrable_inner_of_hasCompactSupport hΦ
      ((Green.contDiff_gradient (FiniteTimeSingularity.div W) (hWo 2)).continuous)
      ((hWoc.fderiv (𝕜 := ℝ)).comp_left (map_zero _))
  have hBint : Integrable
      (fun x => inner ℝ (Φ x) (FiniteTimeSingularity.vorticity
        (FiniteTimeSingularity.vorticity W) x)) :=
    integrable_inner_of_hasCompactSupport hΦ
      ((Work.FTS.PressureOn.Auxiliary.contDiff_vorticity _ hvort 1).continuous)
      (hasCompactSupport_vorticity _ hvc)
  -- the two pointwise identities
  have hpt : ∀ x, inner ℝ (Φ x) (Work.FTS.PressureOn.laplaceTraceVec W x)
      = inner ℝ (Φ x) (gradient (FiniteTimeSingularity.div W) x)
        - inner ℝ (Φ x) (FiniteTimeSingularity.vorticity
            (FiniteTimeSingularity.vorticity W) x) := by
    intro x
    rw [Work.FTS.PressureOn.Auxiliary.laplaceTraceVec_identity W hW x, inner_sub_right]
  have hdiv_eq : ∀ x, FiniteTimeSingularity.div (Work.FTS.PressureOn.laplaceTraceVec W) x
      = Work.FTS.PressureOn.laplaceTrace (FiniteTimeSingularity.div W) x :=
    fun x => Work.FTS.PressureOn.Auxiliary.div_laplaceTraceVec W hW x
  have hfirst : (∫ x, inner ℝ (Φ x) (Work.FTS.PressureOn.laplaceTraceVec W x))
      = (∫ x, inner ℝ (Φ x) (gradient (FiniteTimeSingularity.div W) x))
        - ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity
            (FiniteTimeSingularity.vorticity W) x) := by
    rw [show (fun x => inner ℝ (Φ x) (Work.FTS.PressureOn.laplaceTraceVec W x))
        = fun x => inner ℝ (Φ x) (gradient (FiniteTimeSingularity.div W) x)
            - inner ℝ (Φ x) (FiniteTimeSingularity.vorticity
                (FiniteTimeSingularity.vorticity W) x) from funext hpt]
    exact integral_sub hAint hBint
  have hsecond : (∫ x, q x * FiniteTimeSingularity.div
        (Work.FTS.PressureOn.laplaceTraceVec W) x)
      = ∫ x, q x * Work.FTS.PressureOn.laplaceTrace (FiniteTimeSingularity.div W) x := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [hdiv_eq x]
  rw [hfirst, hsecond, hA, hB]
  ring

/-- **M2, in the form consumed by the assembly.**  The version above with the local-integrability
hypothesis replaced by the *continuity* of `Φ` and `q` (which is what holds for the pair
`(q, Φ) = (pressurePotential (u × ω), ∂_t u - u × ω)` of `weyl_pair`).  Continuity implies local
integrability, so this is an immediate corollary of
`dpair_laplaceTraceVec_eq_zero_of_locallyIntegrable`. -/
theorem dpair_laplaceTraceVec_eq_zero
    (q : Work.FTS.PressureOn.R3 → ℝ)
    (Φ : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hq : Continuous q) (hΦ : Continuous Φ)
    (hdiv : ∀ φ : Work.FTS.PressureOn.R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      ∫ x, inner ℝ (Φ x) (gradient φ x)
        = -∫ x, q x * Work.FTS.PressureOn.laplaceTrace φ x)
    (hcurl : ∀ ψ : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3,
      (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity ψ x) = 0)
    (W : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hW : ∀ n : ℕ, ContDiff ℝ n W) (hWc : HasCompactSupport W) :
    (∫ x, inner ℝ (Φ x) (Work.FTS.PressureOn.laplaceTraceVec W x))
      + ∫ x, q x * FiniteTimeSingularity.div (Work.FTS.PressureOn.laplaceTraceVec W) x = 0 :=
  dpair_laplaceTraceVec_eq_zero_of_locallyIntegrable q Φ hΦ.locallyIntegrable hdiv hcurl W hW hWc

end Work.FTS.PressureOn.Weyl
