/-
# `Work.FTS.GalBasis.cc.psiCut_spec` — the specification of the cutoff family

This module assembles `Work.FTS.GalBasis.cc.psiCut_spec` from its pieces:

* `psiCut_basic` — joint smoothness of `(z,θ) ↦ psiCut N z θ`, the range `[0,1]`, the value `1`
  on the plateau `InPlateau N` and the value `0` off the outer box `OffBox N`;
* `psiCut_mixed_factor` — the factorisation `mixed j i (psiCut N) z θ = DzIter j (cutA N) z ·
  DthIter i (cutB N) θ` of the mixed derivatives through the two one-dimensional steps;
* `Zbound`, `Tbound` (`PsiCutBounds`) — the uniform-in-`N` bounds on the iterated derivatives
  of the two steps, of order `≤ 4` (the scale-invariant mesh `1/(N+1)` is what makes a single
  constant work for all `N`);
* `psiCut_layer_zero'` (`PsiCutLayer`) — the vanishing of the `θ`-derivatives of positive order
  outside the two angular layers of `cutB N`.

Note the statement is *proved* here with no `axiom` involved: this module is what
`cc.CutSpec.exists_cutSpec` consumes.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.GalBasis.cc.CutDefs
import Submission.Work.FTS.GalBasis.cc.psiCut_basic
import Submission.Work.FTS.GalBasis.cc.psiCut_mixed_factor
import Submission.Work.FTS.GalBasis.cc.PsiCutBounds
import Submission.Work.FTS.GalBasis.cc.PsiCutLayer

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

theorem psiCut_spec :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (psiCut N)) ∧
      (∀ z θ : ℝ, 0 ≤ psiCut N z θ ∧ psiCut N z θ ≤ 1) ∧
      (∀ z θ : ℝ, InPlateau N z θ → psiCut N z θ = 1) ∧
      (∀ z θ : ℝ, OffBox N z θ → psiCut N z θ = 0) ∧
      (∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, |Work.Spaces.mixed j i (psiCut N) z θ| ≤ K) ∧
      (∀ j i : ℕ, 1 ≤ i → ∀ z θ : ℝ, NotInThetaLayer N θ →
        Work.Spaces.mixed j i (psiCut N) z θ = 0) := by
  obtain ⟨KA, hKApos, hKA⟩ := Zbound
  obtain ⟨KB, hKBpos, hKB⟩ := Tbound
  refine ⟨max KA 1 * max KB 1, by positivity, fun N => ?_⟩
  obtain ⟨hb1, hb2, hb3, hb4⟩ := psiCut_basic N
  refine ⟨hb1, hb2, hb3, hb4, ?_, ?_⟩
  · intro j i hji z θ
    rw [psiCut_mixed_factor N j i z θ, abs_mul]
    calc |Work.Spaces.DzIter j (fun z' (_ : ℝ) => cutA N z') z θ|
            * |Work.Spaces.DthIter i (fun (_ : ℝ) θ' => cutB N θ') z θ|
        ≤ KA * KB :=
          mul_le_mul (hKA N j (by omega) z θ) (hKB N i (by omega) z θ)
            (abs_nonneg _) (le_of_lt hKApos)
      _ ≤ max KA 1 * max KB 1 :=
          mul_le_mul (le_max_left _ _) (le_max_left _ _) (le_of_lt hKBpos)
            (le_trans (le_of_lt hKApos) (le_max_left _ _))
  · intro j i hi z θ h
    rw [psiCut_layer_zero' N j i hi z θ h]

end Work.FTS.GalBasis.cc
