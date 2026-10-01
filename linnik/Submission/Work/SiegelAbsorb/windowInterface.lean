import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikContract.Defs

/-!
# `Work.SiegelAbsorb.windowInterface` — the shared interface of `highMassRep2` and
`RestHighBGTZSiegel`

`Work.LinnikAreas.BGTZ.highMassRepC` (`BGTZ/RestHighBGTZGenC.lean`) is the per-height-window mass
bound for the high zeros of a Siegel datum, with a **single** log-free family count
`famCount q σ T ≤ C₂ e^{(5/2)(1-σ)𝓛}T^{3/2}` for all `σ ∈ [0,1]`.  AREA 6 does not have that
count at coefficient `5/2`; it has it

* at coefficient `5/2` **only on `σ ≥ 93/100`** (`Work.SiegelAbsorb.famCount_nearLine`, U4 of
  `LinnikAreas/AREA6_ROUTE_LEAD.md`), and
* at the *crude* coefficient `9/2` on all of `[0,1]` (`Work.SiegelAbsorb.famCount_crude`, U3).

`WindowBoundHyp C₂ C₃ C₀` below is the statement of `highMassRepC` with those two counts in place
of the single one and with the two new summands of `windowMassFloor2`/`windowMassFree2`
(the second one carries the factor `e^{-(7/250)𝓛} = e^{-(2/5)·(7/100)𝓛}` produced by the crude
count with floor `(7/100)𝓛`).  The two files

* `Submission/Work/SiegelAbsorb/highMassRep2.lean` — `highMassRep2` : proves `WindowBoundHyp`;
* `Submission/Work/SiegelAbsorb/restHighBGTZSiegel.lean` — `RestHighBGTZSiegel_of_window` :
  turns `WindowBoundHyp` (uniformly in `C₂ C₃ C₀`) into `Siegel.RestHighBGTZSpec (-3/2)`, using
  the crude count also for the `λ₁`-free branch (`highFinsetBoundFreeGenAux` at `c₃ = 9/2`) and
  Siegel's `exp (-(7/250)𝓛) ≤ λ₁`;

develop the two halves in parallel, and the constants

`K₂low C₂ C₀` (the `5/2` part, as in `highMassRepC`), `K₃high C₃` (the `9/2` part) and
`windowBound C₂ C₃ C₀ = K₂low C₂ C₀ + K₃high C₃`

are shared here so that the two statements agree by construction.  Both constants are padded
(`max 1` and a factor `2`) so that positivity and the arithmetic comparisons at the end of each
copy-patched proof are immediate.
-/

namespace Work.SiegelAbsorb

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- The `σ ≥ 93/100` (`λ ≤ (7/100)𝓛`) part of the window-bound constant: the constant `Ks` of
`Work.LinnikAreas.BGTZ.highMassRepC` (`4·2^{3/2}C₂e^{5/2}/(1-e^{-12/5})` times the repulsion and
geometric factors), doubled and padded. -/
def K₂low (C₂ C₀ : ℝ) : ℝ :=
  max 1 (8 * (2 : ℝ) ^ (3 / 2 : ℝ) * C₂ * Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))
    * (Real.exp (12 * C₀ / 5) * (2 : ℝ) ^ (5 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-(1 / 4) : ℝ))⁻¹
        + (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹))

/-- The `λ > (7/100)𝓛` (crude `9/2` count) part of the window-bound constant:
`8·2^{3/2}C₃e^{9/2}/(1-e^{-2/5})·(1-2^{-1/2})^{-1}`, doubled and padded. -/
def K₃high (C₃ : ℝ) : ℝ :=
  max 1 (16 * (2 : ℝ) ^ (3 / 2 : ℝ) * C₃ * Real.exp (9 / 2) / (1 - Real.exp (-(2 / 5)))
    * (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹)

/-- The total constant of the two-regime window bound. -/
def windowBound (C₂ C₃ C₀ : ℝ) : ℝ := K₂low C₂ C₀ + K₃high C₃

/-- **The statement of `Work.LinnikAreas.BGTZ.highMassRepC` with two log-free family counts
instead of one.**  All hypotheses are those of `highMassRepC` (`hq`, `hrepq`, `hlam1pos`,
`hsmall`, `hlam1lt`, `hαhalf`, `h𝓛big`, `S`, `hzm`, `hhigh`, `hexc`, `hsep`), except that the
single count `hfam` (coefficient `5/2` on all of `[0,1]`) is replaced by

* `hfam₁`: coefficient `5/2` on `93/100 ≤ σ ≤ 1` (`Work.SiegelAbsorb.famCount_nearLine`),
* `hfam₂`: coefficient `9/2` on `0 ≤ σ ≤ 1` (`Work.SiegelAbsorb.famCount_crude`),

and the conclusion is the sum of the two layer-cake bounds: the low part with the constants of
`highMassRepC` (the `K₂low` summand) and the crude part with the factor `e^{-(7/250)𝓛}`
(the `K₃high` summand) coming from `windowMassFloor2` / `windowMassFree2`.

`C₂ C₃ C₀` are the constants of the two counts and of the repulsion, and are *parameters* so that
the constant of the conclusion is a definite function of them. -/
abbrev WindowBoundHyp (C₂ C₃ C₀ : ℝ) : Prop :=
  ∀ {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ)
    (hfam₁ : ∀ (σ T : ℝ), 93 / 100 ≤ σ → σ ≤ 1 → 1 ≤ T →
      Work.ZeroDensity.famCount q σ T
        ≤ C₂ * Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) * T ^ (3 / 2 : ℝ))
    (hfam₂ : ∀ (σ T : ℝ), 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      Work.ZeroDensity.famCount q σ T
        ≤ C₃ * Real.exp ((9 / 2) * ((1 - σ) * Real.log (q : ℝ))) * T ^ (3 / 2 : ℝ))
    (hrepq : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ Work.LinnikContract.lamOf q ρ →
      (Real.log (1 / Work.LinnikContract.lamOf q (β₁ : ℂ))
          - Real.log (C₀ * ((11 / 5 : ℝ) + (11 / 10 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))))
        / ((11 / 5 : ℝ) + (11 / 10 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))
        ≤ Work.LinnikContract.lamOf q ρ)
    (hlam1pos : 0 < Work.LinnikContract.lamOf q (β₁ : ℂ))
    (hsmall : Work.LinnikContract.lamOf q (β₁ : ℂ) < 1 / (6 * C₀))
    (hlam1lt : Work.LinnikContract.lamOf q (β₁ : ℂ) < 1)
    (hαhalf : Real.log (1 / Work.LinnikContract.lamOf q (β₁ : ℂ)) ≤ Real.log (q : ℝ) / 2)
    (h𝓛big : 20 ≤ Real.log (q : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hhigh : ∀ z ∈ S, 1 < |z.2.im|)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)))
    (hsep : ∀ z ∈ S, Work.LinnikContract.lamOf q z.2 < Work.LinnikContract.lamOf q (β₁ : ℂ) →
      4 * (q : ℝ) ^ 2 ≤ |z.2.im|),
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log (q : ℝ) : ℂ))‖)
      ≤ (K₂low C₂ C₀ * Work.LinnikContract.lamOf q (β₁ : ℂ)
          + K₃high C₃ * Real.exp (-(7 / 250) * Real.log (q : ℝ)))
        * (Real.log (q : ℝ)) ^ (-2 : ℝ)

end

end Work.SiegelAbsorb
