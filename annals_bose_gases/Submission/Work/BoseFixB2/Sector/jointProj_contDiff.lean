import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixB2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `jointProj_contDiff`

The joint sector projection `E_S = ∏_{i∈S} Q_i ∏_{j∉S} P_j` (`Work.BoseFixB2.jointProj`)
preserves smoothness: if `Φ : X n → ℝ` is `C^∞` then so is `E_S Φ`.

The proof is an induction on the recursion `blockOp`: each slot operator is the box
mean `aP ℓ ⟨j,_⟩` — an average of `Φ` over the centred box in slot `j`, smooth by
differentiation under the integral sign — or its complement
`aQ ℓ ⟨j,_⟩ = id − aP ℓ ⟨j,_⟩`.  Smoothness of both is the corpus lemma
`Submission.BoseGases.contDiff_aP` / `contDiff_aQ`
(`Submission/Work/SmallBoxKinBridge.lean`, `Submission/Work/SmallBoxPairMomentum.lean`).
-/

noncomputable section

open scoped ContDiff

namespace Work.BoseFixB2.Sector

open Submission.BoseGases

/-- **Smoothness is preserved by the iterated slot operator.**  For every `k`, if `Φ`
is `C^∞` then so is `blockOp ℓ S k Φ`: each step applies the slot operator
`aP ℓ ⟨j,_⟩` or `aQ ℓ ⟨j,_⟩` (for `j < n`), and both preserve `C^∞` (`contDiff_aP`,
`contDiff_aQ`); once `j ≥ n` the operator is the identity. -/
lemma contDiff_blockOp {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (S : Finset ℕ) :
    ∀ (k : ℕ) {Φ : Submission.BoseGases.X n → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Φ → ContDiff ℝ (⊤ : ℕ∞) (blockOp ℓ S k Φ) := by
  intro k
  induction k with
  | zero =>
      intro Φ hΦ
      simpa using hΦ
  | succ k ih =>
      intro Φ hΦ
      by_cases hkn : k < n
      · rw [blockOp_succ S hkn]
        by_cases hmem : k ∈ S
        · rw [if_pos hmem]
          exact contDiff_aQ hℓ ⟨k, hkn⟩ (ih hΦ)
        · rw [if_neg hmem]
          exact contDiff_aP hℓ ⟨k, hkn⟩ (ih hΦ)
      · have hstep : blockOp ℓ S (k + 1) Φ = blockOp ℓ S k Φ := by
          rw [blockOp]
          simp only [dif_neg hkn]
        rw [hstep]
        exact ih hΦ

theorem jointProj_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (S : Finset ℕ) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.jointProj ℓ S Φ) := by
  rw [Work.BoseFixB2.jointProj_eq_blockOp]
  exact contDiff_blockOp hℓ S n hΦ

end Work.BoseFixB2.Sector
