import ChallengeDeps
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.CentredGap
import Submission.PotWords
import Submission.Symmetry
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The trial-state upper-bound segment: definitions

FS `final_v2.tex` `eq:aprioriPsi` (the *energy hypothesis* of
`thm:aprioribounds`) is the statement that the box Hamiltonian
`H_Λ(μ)` has a normalized state with energy at most
`−4πμ²aℓ³(1 − J(μa³)^{1/2})` — the variational (upper-bound) side of the
a-priori chain.  The corpus consumes this as the field `hEgc` of
`APrioriSkeleton.APrioriData` and (via `Assembly.cnPlus_and_R_le`) as the
hypothesis `hE` of the window assembly.  This module fixes the *vocabulary*
of that segment:

* `cutBump r` — the smooth cutoff `≡ 1` on `ball 0 (r/2)`, `≡ 0` outside
  `ball 0 r`;
* `pairCorr r ω := 1 − ω·cutBump r` — FS's pair-correlation function
  `f = 1 − ω` with the long-range tail cut at `r` (the cutoff is what makes
  the trial state admissible in the dilute regime; `ω` itself has the
  non-integrable `a/‖x‖` tail);
* `trial N φ f` — the **product-type trial state** on the centred box:
  the condensate orbital `∏ᵢ φ(xᵢ)` times the pair-correlation factor
  `∏_{i<j} f(xᵢ − xⱼ)` (corpus `pairSet` ordering);
* `trialZ`, `trialE` — its box norm and its `H_Λ(μ)`-energy word
  (`kinWord + qLHSword` at the chosen kernels `wPairC ℓ v`, `wPairC ℓ g₀`);
* `SecondOrderUpperBound` — **the named residual input** of the segment:
  the second-order (Bogoliubov/Yau–Yin) variational upper bound, i.e. the
  existence of a normalized state with
  `kinWord + qLHSword ≤ −4πμ²aℓ³(1 − C(μa³)^{1/2})`.

The consumer-facing shape of the deliverable is `hEgc` of
`APrioriSkeleton.APrioriData`; `Main.lean` derives it from
`SecondOrderUpperBound` (the J-lever: any `J ≥ C`) and documents the residual.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.TrialState

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The cutoff and the pair-correlation function -/

/-- The smooth cutoff of radius `r`: a `ContDiffBump` with `rIn = r/2`,
`rOut = r` (so `≡ 1` on `ball 0 (r/2)`, `0` outside `ball 0 r`). -/
noncomputable def cutData (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ³) :=
  { rIn := r / 2, rOut := r, rIn_pos := by positivity, rIn_lt_rOut := by linarith }

/-- The cutoff function `χ_r` (as a function). -/
noncomputable def cutBump (r : ℝ) (hr : 0 < r) (z : ℝ³) : ℝ := cutData r hr z

/-- FS's pair-correlation function with the long-range tail cut at `r`:
`f(z) = 1 − ω(z)·χ_r(z)`. -/
noncomputable def pairCorr (r : ℝ) (hr : 0 < r) (w : ℝ³ → ℝ) : ℝ³ → ℝ :=
  fun z => 1 - w z * cutBump r hr z

/-- The constant condensate orbital on the centred box `Λ(ℓ) = acube ℓ`,
normalized so that `∫_{acube ℓ} φ² = 1`. -/
noncomputable def constOrb (ℓ : ℝ) : ℝ³ → ℝ := fun _ => (Real.sqrt (ℓ ^ 3))⁻¹

/-- The condensate orbital `φ ≡ c` with a prescribed constant `c`. -/
noncomputable def orbConst (c : ℝ) : ℝ³ → ℝ := fun _ => c

/-! ## The product-type trial state -/

/-- The **product-type trial state**: condensate orbital `∏ᵢ φ(xᵢ)` times the
pair-correlation factor `∏_{i<j} f(xᵢ − xⱼ)` (over the corpus's ordered
`pairSet`, so each unordered pair occurs twice). -/
noncomputable def trial (N : ℕ) (φ f : ℝ³ → ℝ) : X N → ℝ :=
  fun x => (∏ i : Fin N, φ (x i)) * ∏ p ∈ pairSet N, f (x p.1 - x p.2)

/-- The `L²`-norm square of the trial state over the centred box (the
denominator of its Rayleigh quotient). -/
noncomputable def trialZ (N : ℕ) (ℓ : ℝ) (φ f : ℝ³ → ℝ) : ℝ :=
  ∫ x in abox N ℓ, (trial N φ f x) ^ 2

/-- The `H_Λ(μ)`-energy word of the trial state: the corpus kinetic word plus
the corpus potential word at the chosen kernels `w = wPairC ℓ v`,
`w₁ = wPairC ℓ (g₀)`.  This is the left-hand side of FS `eq:aprioriPsi` in the
corpus's per-sector vocabulary. -/
noncomputable def trialE (N : ℕ) (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (φ f : ℝ³ → ℝ) : ℝ :=
  kinWord N ℓ (trial N φ f)
    + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) (trial N φ f)

/-! ## The energy hypothesis `eq:aprioriPsi` -/

/-- **FS `eq:aprioriPsi`** in the corpus's per-sector vocabulary: the state
`trial N φ f` is normalized on the box and its `H_Λ(μ)`-energy is at most
`−4πμ²(a v)ℓ³(1 − J(μ(a v)³)^{1/2})`. -/
def AprioriPsiBound (N : ℕ) (ℓ μ J : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (φ f : ℝ³ → ℝ) : Prop :=
  (∫ x in abox N ℓ, (trial N φ f x) ^ 2) = 1 ∧
    trialE N ℓ μ v h φ f
      ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))

/-- **The named residual input of this segment.**  The *second-order*
(Bogoliubov / Yau–Yin–ESY) variational upper bound for the box Hamiltonian in
the corpus's per-sector vocabulary: there is a normalized continuous state on
the box whose `H_Λ(μ)`-energy is at most
`−4πμ²(a v)ℓ³(1 − C(μ(a v)³)^{1/2})`.

This is *not* a consequence of the corpus's existing estimate library (all of
which bounds the energy from below); it is the analytic content of the upper
half of FS `thm:LHY-Box`.  See `NOTES.md` for the exact gap and the roadmap.
Note the exponent: a state whose energy is only known to first order (relative
error `(μa³)^{1/3}`, the Dyson/Jastrow level) is *useless* here — see
`NOTES.md` §2 — the `1/2`-rate is the irreducible requirement. -/
def SecondOrderUpperBound (N : ℕ) (ℓ μ C : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  ∃ Φ : X N → ℝ, Continuous Φ ∧
    (∫ x in abox N ℓ, (Φ x) ^ 2) = 1 ∧
      kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
        ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))

end Work.TrialState
