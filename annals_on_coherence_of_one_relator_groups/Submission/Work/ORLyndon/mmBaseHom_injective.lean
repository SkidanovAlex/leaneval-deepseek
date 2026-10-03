import Mathlib
import Submission.Work.ORLyndon.mmConnDefs
-- `weinbaum_sigma_zero_half` reaches `Submission.Work.OROneRel.mrslAux`, which currently redeclares
-- `Work.OROneRel.toWord_pow_of_isCyclicallyReduced` (already declared in `magnus_step_root`); any
-- module importing both copies fails to elaborate.  `halfAtPrelude` declares the same
-- `Work.OROneRel.mmBaseHom_injective` and lies outside that import closure.
import Submission.Work.OROneRel.halfAtPrelude
-- import-hygiene: the `OROneRel` original reaches `OROneRel.mrslAux` (duplicate declaration of
-- `toWord_pow_of_isCyclicallyReduced`); see `relatorLetters_pow_clean.lean`.
import Submission.Work.ORLyndon.relatorLetters_pow_clean
import Submission.Work.OROneRel.isCyclicallyReducedRelator_pow
import Submission.Work.OROneRel.ne_one_of_not_isProperPower
import Submission.Work.OROneRel.relatorNorm_pow_of_isCyclicallyReduced

/-!
# Injectivity of the canonical map from the Magnus base, specialized to `u ^ l`

In the exponent-sum-zero Magnus step for a root `u` (`Work.OROneRel.magnus_step_root_eps_zero`) the
one-relator group `G = ⟨α | u ^ l⟩` is an HNN extension of the one-relator group
`H = ⟨β | mmW t (u ^ l)⟩` on the occurring decorated alphabet `β = mmBeta t (u ^ l)`, and the
canonical map `Work.OROneRel.mmBaseHom : H →* G` is the composite `mmPsi ∘ HNNExtension.of`.  Since
`HNNExtension.of` is injective and `mmPsi` is injective (it has the left inverse `mmTheta`,
`Work.OROneRel.mmTheta_comp_mmPsi`), `mmBaseHom` is injective.

The general form of this statement is `Work.OROneRel.mmBaseHom_injective` (in the colleague module
`Submission.Work.OROneRel.weinbaum_sigma_zero_half`); this file specializes it to the relator
`R = u ^ l` of the Cohen--Lyndon induction and to the hypotheses on the *root* `u` under which the
induction runs.

Injectivity is what allows the induction hypothesis at the Magnus base to be *transported* to `G`:
the base regularity statement `c * (∂v/∂q) = 0 → c = 0` of the base group is moved along `mmBaseHom`
by `Work.ORLyndon.base_regularity_transport_of_le`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

/-- **The canonical map from the Magnus base is injective** (specialized to `u ^ l`). -/
theorem mmBaseHom_injective {α : Type*} [DecidableEq α] (t : α) (u : FreeGroup α) (l : ℕ)
    (hl : 1 ≤ l) (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0) :
    Function.Injective (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l)
      (Work.ORLyndon.mmEpsPow t u l he)) := by
  have hu1 : u ≠ 1 := Work.OROneRel.ne_one_of_not_isProperPower hu
  have hpow1 : u ^ l ≠ 1 := by
    intro h
    have h1 : Work.OROneRel.relatorNorm (u ^ l) = 0 := by
      rw [h]
      simp [Work.OROneRel.relatorNorm, FreeGroup.norm]
    rw [Work.OROneRel.relatorNorm_pow_of_isCyclicallyReduced u hcyc l] at h1
    rcases Nat.mul_eq_zero.mp h1 with h2 | h2
    · omega
    · refine hu1 ?_
      have h3 : FreeGroup.norm u = 0 := by simpa [Work.OROneRel.relatorNorm] using h2
      exact FreeGroup.norm_eq_zero.mp h3
  have htr : t ∈ Work.OROneRel.relatorLetters (u ^ l) := by
    rw [Work.ORLyndon.relatorLetters_pow u hl]
    exact ht
  have hcycr : Work.OROneRel.IsCyclicallyReducedRelator (u ^ l) :=
    Work.OROneRel.isCyclicallyReducedRelator_pow hcyc l
  exact Work.OROneRel.mmBaseHom_injective hpow1 htr (Work.ORLyndon.mmEpsPow t u l he) hcycr

end Work.ORLyndon
