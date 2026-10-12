import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseFixB2.Sector.jointProj_contDiff
import Submission.Work.BoseFixB2.Sector.secPermConj
import Submission.Work.BoseFixB2.Sector.slotMap_sum_reindex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Sector.secProj_contDiff_symm`

The `n₊ = k` sector `secProj ℓ k Φ = Σ_{|S| = k} E_S Φ` of a smooth state is smooth
(finite sum of `jointProj_contDiff`) and, when `Φ` is permutation invariant, it is
again permutation invariant.

The invariance is the content: a *single* joint sector projection `E_S` is **not**
symmetric (it is `Q_0P_1` for `n = 2`, `S = {0}`), but the sum over all `k`-subsets
is, because

* conjugating `E_S` by the relabelling `actPerm σ` transports its slot set
  `S ↦ slotMap σ S` (`jointProj_actPerm'`, `secPermConj`), and
* `S ↦ slotMap σ S` is a bijection of the `k`-subsets of `{0,…,n−1}`
  (`slotMap_sum_reindex`).

Hence `Σ_{|S|=k} E_S Φ ∘ σ = Σ_{|S|=k} E_{slotMap σ S} Φ = Σ_{|S|=k} E_S Φ`.
-/

namespace Work.BoseFixB2.Sector

open Submission.BoseGases

set_option linter.unusedVariables false

theorem secProj_contDiff_symm {ℓ : ℝ} (hℓ : 0 < ℓ) {n k : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hσ : Submission.BoseGases.PermInvariant n Φ) : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.secProj ℓ k Φ) ∧ Submission.BoseGases.PermInvariant n (Work.BoseFixB2.secProj ℓ k Φ) := by
  constructor
  · have hsum : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => ∑ S ∈ (Finset.range n).powersetCard k, Work.BoseFixB2.jointProj ℓ S Φ x) :=
      ContDiff.sum (fun S _ => jointProj_contDiff hℓ S hΦ)
    rw [Work.BoseFixB2.secProj, Finset.sum_fn]
    exact hsum
  · intro σ x
    show (Finset.sum ((Finset.range n).powersetCard k) (fun S => Work.BoseFixB2.jointProj ℓ S Φ))
        (Submission.BoseGases.actPerm n σ x)
      = (Finset.sum ((Finset.range n).powersetCard k)
          (fun S => Work.BoseFixB2.jointProj ℓ S Φ)) x
    rw [Finset.sum_apply, Finset.sum_apply,
      Finset.sum_congr rfl (fun S hS =>
        jointProj_actPerm' hℓ σ (Finset.mem_powersetCard.mp hS).1 hΦ.continuous hσ x)]
    simpa only [Finset.sum_apply] using
      congrFun (Work.BoseFixB2.Sector.slotMap_sum_reindex (n := n) (k := k) σ
        (fun S => Work.BoseFixB2.jointProj ℓ S Φ)) x

end Work.BoseFixB2.Sector
