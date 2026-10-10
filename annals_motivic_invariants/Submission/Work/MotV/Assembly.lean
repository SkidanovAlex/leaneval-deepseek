import Mathlib
import ChallengeDeps
import Submission.Work.MotV.Defs
import Submission.Work.MotV.not_gen_of_certN
import Submission.Work.MotV.certN_of_linkCert
import Submission.Work.MotV.constantsOnly_twist
import Submission.Work.MotV.rigidity

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero
open MotivicInvariants (GenByPseudoRegularizable)

/-!
# Assembly of the characteristic-`≠ 5` branch of route V (`not_gen_charNeFive`)

Every node of the design `MOTIVIC_S45_LEAD.md` §4 is proved in this area:

* KDATA is the K-route's `Work.MotK.ExistsKleinData` (`Submission/Work/MotK/ExistsKleinData.lean`);
* LK_T is the K-route's `Work.MotK.LinkCertT` (`Submission/Work/MotK/LinkCertT.lean`);
* CERT (`Work.MotV.not_gen_of_certN`), SPREAD (`Work.MotV.certN_of_linkCert`),
  CO (`Work.MotV.constantsOnly_twist`) and RIG (`Work.MotV.rigidity`) are proved here.

The two external inputs are kept as explicit hypotheses below, so that this file stays
`sorry`-free and axiom-clean; feeding it the K-route's two declarations (once they are proved)
yields the unconditional statement.

* `Work.MotV.not_gen_charNeFive_of` — the assembly, with KDATA and LK_T as hypotheses,
* `Work.MotV.not_gen_charNeFive_of_inputs` — the same, in the "global" form in which the two
  inputs are statements of the K-route,
* `Work.MotV.theorem_1_2_2'_of` / `Work.MotV.theorem_1_2_3'_of` — the challenge's Theorems 1.2 (2)
  and 1.2 (3) from the two characteristic branches.
-/

noncomputable section

namespace Work.MotV

/-- **The assembly of the characteristic-`≠ 5` branch** (`not_gen_charNeFive` of the design), with
the two external inputs as hypotheses: good Klein data, and the T-twisted Crauder–Katz link
certificate over `𝕜(t)` for `h = t(t-1)`. -/
theorem not_gen_charNeFive_of (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] (hk : ringChar 𝕜 ≠ 5) {n : ℕ}
    (hn : 4 ≤ n)
    (hKD : ∃ D : KleinData 𝕜, D.Good)
    (hLK : ∀ (D : KleinData 𝕜) (hD : D.Good),
      Nonempty (LinkCert (RatFunc 𝕜) (twistFieldT D (hT 𝕜)) (twistFieldT D (hT 𝕜 ^ 2)))) :
    ¬ GenByPseudoRegularizable 𝕜 n := by
  obtain ⟨D, hD⟩ := hKD
  obtain ⟨L⟩ := hLK D hD
  obtain ⟨c⟩ := certN_of_linkCert 𝕜 L (constantsOnly_twist D hD hk (hT 𝕜) (Or.inl rfl))
    (rigidity D hD hk) n hn
  exact not_gen_of_certN c

/-- The characteristic-`≠ 5` branch, in the form in which the K-route states its two
deliverables (nodes KDATA and LK_T).  Feeding it `Work.MotK.ExistsKleinData` and
`Work.MotK.LinkCertT` gives the unconditional `not_gen_charNeFive`. -/
theorem not_gen_charNeFive_of_inputs
    (hKD : ∀ (𝕜 : Type) [Field 𝕜] [Infinite 𝕜], ringChar 𝕜 ≠ 5 → ∃ D : KleinData 𝕜, D.Good)
    (hLK : ∀ (𝕜 : Type) [Field 𝕜] (hk : ringChar 𝕜 ≠ 5) (D : KleinData 𝕜), D.Good →
      Nonempty (LinkCert (RatFunc 𝕜) (twistFieldT D (hT 𝕜)) (twistFieldT D (hT 𝕜 ^ 2)))) :
    ∀ (𝕜 : Type) [Field 𝕜] [Infinite 𝕜], ringChar 𝕜 ≠ 5 → ∀ {n : ℕ}, 4 ≤ n →
      ¬ GenByPseudoRegularizable 𝕜 n :=
  fun 𝕜 _ _ hk {n} hn => not_gen_charNeFive_of 𝕜 hk hn (hKD 𝕜 hk) (hLK 𝕜 hk)

/-- Theorem 1.2 (2) of Lin–Shinder from the characteristic-`≠ 5` branch (this area's assembly) and
the characteristic-`5` branch (the sibling area `Work.MotV5`, node `not_gen_charFive`). -/
theorem theorem_1_2_2'_of
    (hNe : ∀ (𝕜 : Type) [Field 𝕜] [Infinite 𝕜], ringChar 𝕜 ≠ 5 → ∀ {n : ℕ}, 4 ≤ n →
      ¬ GenByPseudoRegularizable 𝕜 n)
    {n : ℕ} (hn : 4 ≤ n) (𝕜 : Subfield ℂ) : ¬ GenByPseudoRegularizable 𝕜 n := by
  have : Infinite 𝕜 := Infinite.of_injective (fun m : ℕ => (m : 𝕜)) Nat.cast_injective
  refine hNe 𝕜 ?_ hn
  rw [ringChar.eq_zero]; norm_num

/-- Theorem 1.2 (3) of Lin–Shinder from the two characteristic branches. -/
theorem theorem_1_2_3'_of
    (hNe : ∀ (𝕜 : Type) [Field 𝕜] [Infinite 𝕜], ringChar 𝕜 ≠ 5 → ∀ {n : ℕ}, 4 ≤ n →
      ¬ GenByPseudoRegularizable 𝕜 n)
    (hFive : ∀ (𝕜 : Type) [Field 𝕜] [Infinite 𝕜], ringChar 𝕜 = 5 → ∀ {n : ℕ}, 4 ≤ n →
      ¬ GenByPseudoRegularizable 𝕜 n)
    (𝕜 : Type) [Field 𝕜] {n : ℕ} (hn : 5 ≤ n) [Infinite 𝕜] :
    ¬ GenByPseudoRegularizable 𝕜 n := by
  by_cases h5 : ringChar 𝕜 = 5
  · exact hFive 𝕜 h5 (by omega)
  · exact hNe 𝕜 h5 (by omega)

end Work.MotV
