import ChallengeDeps
import Submission.Work.BoseFixB1B.lowMaxDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.flatBranchMaxFreeDefs` — the `J`-free flat branch at a **free** `c₁`

Written by the holder of `Submission/Work/BoseFixB1B/lowState_count_leAlt.lean`.

## Why

The count cap's flat residual is `Work.BoseFixB1B.FlatBranchLowMax v h R`, the `J`-free
`LowMax`-restricted version of `Work.BoseFixB1B.flatBranchLowB`, whose conclusion is
`Work.BoseFixB1.PerBoxF v h R (1/4) C μ n Φ u` — the mean-field coefficient of the `F`-credit is
**hard-wired to `1/4`**.

That hard-wiring is *not* needed by the chain:

* `PerBoxF` is **antitone in `c₁`** (`Work.BoseFixB1B.perBoxF_mono`): the credit
  `c₁·(∬w_{1,B})·∫Φ²ψ(ρ)` sits on the *demand* side, so a *smaller* `c₁` makes the statement
  strictly **easier**;
* the chain (`perBoxIntegratedCollectedMax` → `collectedUnif_of_lowMax` →
  `aprioriUnifOfCollectedUnif`) is parameterised by `c₁` and only requires `0 < c₁`
  (`arith_absorb` never mentions `c₁`, and the final bound on `R_Ψ` has a free constant, so the
  factor `1/c₁` is absorbed);
* the corpus's own `J`-indexed twin of this residual,
  `Work.BoseFixB1B.FlatBranchFree` (`Submission/Work/BoseFixB1B/flatBranchFree.lean`), made
  exactly this choice ("`PerBoxF` is antitone in `c₁` … this file *only* weakens the hypothesis of
  the chain").

So the *correct* residual to prove — strictly weaker than `FlatBranchLowMax`, and sufficient for
the count cap — is `FlatBranchMaxFree` below, in which `c₁` is existentially quantified instead of
being frozen at `1/4`.  Everything else is verbatim `FlatBranchLowMax`'s body.

## Contents

* `FlatBranchMaxFree` — the residual;
* `flatBranchMaxFree_of_flatBranchLowMax` — `FlatBranchLowMax ⟹ FlatBranchMaxFree` (take
  `c₁ = 1/4`), so the new residual is *strictly weaker* and nothing is lost by proving it instead.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `J`-free flat branch of FS `thm:smallbox` at the sliding box, at a FREE mean-field
coefficient `c₁`.**

Verbatim the body of `Work.BoseFixB1B.FlatBranchLowMax` (`Submission/Work/BoseFixB1B/lowMaxDefs.lean`)
— the same hypotheses (`Adm`, `0 < μ`, `0 < normB`, `LowMax`, `u ∈ goodSet`, the thin-box exclusion
and the flat occupancy bound) — except that the coefficient `c₁` of `Work.BoseFixB1.PerBoxF` is
existentially quantified instead of being frozen at `1/4`.  Since `PerBoxF` is antitone in `c₁`
(`Work.BoseFixB1B.perBoxF_mono`), this is *strictly weaker* than `FlatBranchLowMax` and is exactly
what the count cap's chain needs (it consumes `PerBoxF` at whatever positive `c₁` the flat arm
provides). -/
def FlatBranchMaxFree (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ γ₀ ε₀ c₁ C : ℝ, 0 < γ₀ ∧ 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → 0 < μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v))),
        0 < normB v μ n (Φ : X n → ℝ) →
        LowMax v h μ n (Φ : X n → ℝ) →
        ∀ u ∈ goodSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ,
        ¬ IsThinBox v h μ u →
        UBBInputs8.cnPlusBoxInd (sideAt μ (_root_.BoseGases.a v))
            (dlBox (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u)
            (boxMass (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u)
            (Φ : X n → ℝ)
          < γ₀ * (n : ℝ) * normB v μ n (Φ : X n → ℝ) →
        PerBoxF v h R c₁ C μ n Φ u

/-- `FlatBranchLowMax` gives `FlatBranchMaxFree` (take `c₁ = 1/4`): the free-`c₁` residual is
*strictly weaker*, so a proof of either closes the count cap. -/
theorem flatBranchMaxFree_of_flatBranchLowMax {v : E3 → ℝ} {h : ScatSol v} {R : ℝ}
    (hflat : FlatBranchLowMax v h R) : FlatBranchMaxFree v h R := by
  obtain ⟨γ₀, ε₀, C, hγ₀, hε₀, hC, hbody⟩ := hflat
  exact ⟨γ₀, ε₀, 1 / 4, C, hγ₀, hε₀, by norm_num, hC,
    fun μ hAdm hμ n Φ hN hlow u hu hthin hocc => hbody μ hAdm hμ n Φ hN hlow u hu hthin hocc⟩

end Work.BoseFixB1B
