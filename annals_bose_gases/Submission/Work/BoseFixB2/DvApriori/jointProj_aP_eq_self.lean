import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.jointProj_aP_eq_self`

The joint sector projection `E_S = ∏_{i∈S}Q_i ∏_{j∉S}P_j` (`Work.BoseFixB2.jointProj`)
is fixed by the slot mean `P_m` whenever the slot `m` is *not* in the sector:

  `aP ℓ m (jointProj ℓ S Φ) = jointProj ℓ S Φ   (m ∉ S, m < n)`.

In the recursion `blockOp = jointProj` the slot `m ∉ S` contributes the mean `P_m`
at step `m+1`, so from that step on the state is independent of the `m`-th
configuration variable; every later slot operator sits in a different slot and
preserves that independence.  Hence `P_m` acts as the identity on the output.

This is the stated form (`ContDiff` input, `Sector`-style conclusion) of the
corpus lemma `Work.BoseFixB2.Sector.aP_jointProj_eq_self`, whose hypotheses are
`k < n`, `k ∉ T` and mere continuity of the input; we only supply
`ContDiff ℝ ⊤ Φ → Continuous Φ`.

Together with the companion
`Work.BoseFixB2.Sector.jointProj_aP_eq_zero` (`m ∈ S` ⟹ `P_m E_S Φ = 0`) this
says that `P_m` acts on the sector `E_S Φ` as the identity exactly when `m ∉ S`:
`jointProj = ∏_{j∉S} P_j ∏_{i∈S} Q_i` has the slot-`m` factor `P_m` in its image.
-/

namespace Work.BoseFixB2.DvApriori

set_option autoImplicit false
set_option linter.unusedVariables false

theorem jointProj_aP_eq_self {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} {m : ℕ}
    (hm : m ∉ S) (hmn : m < n) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Submission.BoseGases.aP ℓ ⟨m, hmn⟩ (Work.BoseFixB2.jointProj ℓ S Φ)
      = Work.BoseFixB2.jointProj ℓ S Φ :=
  Work.BoseFixB2.Sector.aP_jointProj_eq_self hℓ hmn hm hΦ.continuous

end Work.BoseFixB2.DvApriori
