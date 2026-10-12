import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7A.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Statements` — the headline statements, as `Prop`s

Design: `BOSE_3Q_LEAD.md` §2/Appendix A.  The five headline results of the
subproject (`lem:EstimateIntegral` corrected, `eq:EstimateQ3Tilde4`,
`eq:EstimateQ3Tilde2+3`, `eq:EstimateQ3Tilde1`, `thm:Control3Q`, and the
arithmetic leg) are recorded here as **`Prop`-valued definitions**, one per
result.  This is deliberate:

* each is a closed mathematical statement, exactly the `∃ C t₀, 0 ≤ C ∧ 0 < t₀ ∧
  ∀ …` of the design (§2), so a caller may use it as a hypothesis without any
  `sorry` being involved;
* a prover proves `EstQ3fourA K₀ b₀ hb₀` (i.e. supplies the missing theorem
  under that name), and the assembly theorem `control3QA_of_three`
  (`Assembly.lean`) then produces `Control3QA K₀ b₀ hb₀` from the pieces.

Every `C` and `t₀` depends only on `(K₀, b₀)`; `Mode`, `F`, `T`, `E` are
quantified **inside** the `∃`, and no constant is ever defined from an instance.

The universe levels are written explicitly (`FockData.{u, v} Mode`): a `def`
whose type is a `Prop` cannot leave the Fock-space universe implicit (a theorem
would generalise it automatically; a `def` cannot).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

universe u v

/-! ## 1. The estimates -/

/-- **FS `eq:EstimateQ3Tilde4`, absolute** (`estQ3fourA`): the fourth piece plus
the linear term, with the kinetic `(b/100)ℓ⁻²n₊` reserve. -/
def EstQ3fourA (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Prop :=
  ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
    ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : FockData.{u, v} Mode) (T : TildeData.{u, v} F) (E : Q3Env.{u} Mode)
      (hv : FSParamsView E),
      hv.t ≤ t₀ → b₀ ≤ E.b → Q3Kernel K₀ F T E →
      ∀ Φ : F.H, T.NWindow E.bigM Φ →
        -(C * e4A E) * F.normSq Φ ≤
          F.qw Φ (T.Q3fourT E + T.linOpT E + (E.b / 100 * E.ell ^ (-(2 : ℝ))) • T.N)

/-- **FS `eq:EstimateQ3Tilde2+3`, absolute** (`estQ3twoThreeA`): the second and
third pieces, with the kinetic reserve on the quarter region `P_H^q`. -/
def EstQ3twoThreeA (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Prop :=
  ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
    ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : FockData.{u, v} Mode) (T : TildeData.{u, v} F) (E : Q3Env.{u} Mode)
      (hv : FSParamsView E),
      hv.t ≤ t₀ → b₀ ≤ E.b → Q3Kernel K₀ F T E →
      ∀ Φ : F.H, T.NWindow E.bigM Φ →
        -(C * e23A E) * F.normSq Φ ≤
          F.qw Φ (T.Q3twoT E + T.Q3threeT E +
            (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat))

/-- **FS `eq:EstimateQ3Tilde1`, absolute** (`estQ3oneA`): the first piece, with
the kinetic `(1−𝓁²)` on `P_H` and `𝓁²/2` on `P_H^q`, `Q₂^ex` and the gap. -/
def EstQ3oneA (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Prop :=
  ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
    ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : FockData.{u, v} Mode) (T : TildeData.{u, v} F) (E : Q3Env.{u} Mode)
      (hv : FSParamsView E),
      hv.t ≤ t₀ → b₀ ≤ E.b → Q3Kernel K₀ F T E →
      ∀ Φ : F.H, T.NWindow E.bigM Φ →
        -(C * e1A E) * F.normSq Φ ≤
          F.qw Φ (T.Q3oneT E + (1 - E.lille ^ 2) • F.dNumOpR E (F.PH E.KH E.aScat) +
            (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat) + F.Q2ex E +
            (E.b / 100) • T.gapOpT E)

/-- **FS `thm:Control3Q` (`eq:Q3Cancels`), absolute** (`control3QA`). -/
def Control3QA (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Prop :=
  ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
    ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : FockData.{u, v} Mode) (T : TildeData.{u, v} F) (E : Q3Env.{u} Mode)
      (hv : FSParamsView E),
      hv.t ≤ t₀ → b₀ ≤ E.b → Q3Kernel K₀ F T E →
      ∀ Φ : F.H, T.NWindow E.bigM Φ →
        -(C * controlErrA E) * F.normSq Φ ≤ F.qw Φ (T.controlWordT E)

/-- **FS `lem:EstimateIntegral` (`eq:CompIntegrals-Final`), corrected and
absolute** (`estIntegralOneA`): with the `ℓ⁻³` of `(2π)⁻³∫dk = ℓ⁻³Σ_k` restored
and the full `K_H⁻¹`. -/
def EstIntegralOneA (K₀ : ℝ) : Prop :=
  ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
    ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : FockData.{u, v} Mode) (E : Q3Env.{u} Mode) (hv : FSParamsView E)
      (R : ℝ) (gHat : Mode → ℝ),
      hv.t ≤ t₀ → (R / E.ell) ^ 2 ≤ E.KH⁻¹ → IntKernel K₀ R F E gHat →
      |E.rho * E.W1omega0 - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
        ≤ C * E.rho * E.aScat * E.KH⁻¹

/-- **The second claim of `lem:EstimateIntegral` (`eq:CompIntegrals-Final-2`),
corrected**: `Ŵ₁ω(0)` against its `P_H` lattice sum, with the `ℓ⁻³` and the full
`K_H⁻¹`.  It is `EstIntegralOneA` divided by `ρ_z > 0` (design §1.1:
`Ŵ₁α_k = ρ_zŴ₁²/(2𝒟_k)`), and the reduction is
`EstIntegralTwoA_of_EstIntegralOneA`. -/
def EstIntegralTwoA (K₀ : ℝ) : Prop :=
  ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
    ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : FockData.{u, v} Mode) (E : Q3Env.{u} Mode) (hv : FSParamsView E)
      (R : ℝ) (gHat : Mode → ℝ),
      hv.t ≤ t₀ → (R / E.ell) ^ 2 ≤ E.KH⁻¹ → IntKernel K₀ R F E gHat →
      |E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ F.PHset E, E.W1 k ^ 2 / (2 * E.D k)| ≤ C * E.aScat * E.KH⁻¹

/-- **The arithmetic leg (node `N1`)**: at FS's parameters the three brackets are
dominated by `controlErrA`, for *arbitrary* constants `C₁, C₂₃, C₄`. -/
def ErrALe (b₀ : ℝ) (hb₀ : 0 < b₀) (C₁ C₂₃ C₄ : ℝ) : Prop :=
  ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode]
      (E : Q3Env.{u} Mode) (hv : FSParamsView E),
      hv.t ≤ t₀ → b₀ ≤ E.b →
      C₁ * e1A E + C₂₃ * e23A E + C₄ * e4A E ≤ controlErrA E

/-! ## 2. The splitting, and the `𝓁 ≤ 1` smallness, as a preparation bundle

`Q3T_split` is not a hypothesis of the design's estimate statements: it is
*derivable* from `Q3Kernel` + `FSParamsView` at small `t` (nodes `N0` + `N2`: the
substitution `a_k = (1−α_k²)⁻¹(b_k − α_k b_{−k}†)` has denominators `≥ 1/2` on
the pairs used, because `2|ℬ| ≤ 𝒜` on `P_H^q` once `64K₀𝓁 ≤ 1`).  Since that
derivation carries its own threshold, it is bundled here as a `Type`-valued
hypothesis, so that the final assembly `control3QA_of_three` can name one
threshold for all of it. -/
structure SplitQ3A (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) where
  /-- the smallness threshold. -/
  t₀ : ℝ
  t₀_pos : 0 < t₀
  /-- FS `lem:EstimatesOnQ3-js`: the Bogoliubov substitution splits `Q₃`. -/
  split : ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : FockData.{u, v} Mode) (T : TildeData.{u, v} F) (E : Q3Env.{u} Mode)
      (hv : FSParamsView E),
      hv.t ≤ t₀ → b₀ ≤ E.b → Q3Kernel K₀ F T E →
      T.Q3T E = T.Q3oneT E + T.Q3twoT E + T.Q3threeT E + T.Q3fourT E
  /-- `𝓁² ≤ 1` (FS §9 uses `𝓁 ≤ δ ≤ 1`; here `𝓁 = X^{97/2}`). -/
  lille_sq_le_one : ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (E : Q3Env.{u} Mode) (hv : FSParamsView E), hv.t ≤ t₀ → E.lille ^ 2 ≤ 1

end Work.BoseB7A
