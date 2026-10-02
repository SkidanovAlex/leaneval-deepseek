import Mathlib
import Submission.Work.SignatureBordism.EndgameDischarged
import Submission.Work.CharacteristicClasses.Capped

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The corrected interface for the remaining gap: the dimension-`8` Hirzebruch congruence

`Submission/NOTES.md` §15.10 records a defect of the interface built in
`Submission/Work/TangentClasses/Bordism.lean`: the structure
`Work.TangentClasses.ClosedOriented8Manifold` carries *no* condition tying `p₁`, `p₂` to the
tangent bundle of a manifold, so the statement `Work.TangentClasses.HirzebruchIdentity8`
(`∀ M : ClosedOriented8Manifold, M.hirzebruch`) is **refutable** (take `p₁ = p₂ = 0` on the
singular simplicial set of any closed `8`-manifold with `σ ≠ 0`) and can never be proved.

This module supplies the *correct* form of the remaining input.  The genuine mathematical statement
is the dimension-`8` Hirzebruch identity `45 σ(M) = 7 p₂(M) − p₁(M)²` for every closed oriented
smooth `8`-manifold with the Pontryagin classes of its tangent bundle; its formalisation needs a
*general* construction of the Pontryagin classes of the tangent bundle of a general manifold, which
the library does not yet have.  What can be stated now, and is *true*, is its instance for the
family of capped manifolds `X = D(ξ) ∪_F D⁸` — the only family the endgame needs — expressed in the
*pontryagin-class-free* congruence form `7 ∣ p₁² − 4σ` (the two are equivalent given the identity;
`Work.SignatureBordism.hirzebruchEightManifold_congruence`).

* `Work.Milnor.CappedCongruence` — the statement: for every capping datum
  (`F hF`) and every fundamental class `c` of `X = D(ξ) ∪_F D⁸`, the congruence
  `7 ∣ ⟨p₁(TX) ⌣ p₁(TX), [X]⟩ − 4 σ(X)` holds, with `p₁(TX) = cappedPontryaginClass F hF`.
  It is **true** (no capping diffeomorphism exists, so the quantification is over the empty type),
  it is **non-vacuous as a target** (it follows from the general dimension-`8` signature theorem
  instantiated at `X`, which *is* a genuine closed oriented smooth `8`-manifold with these tangent
  classes), and it **implies** `Work.Milnor.no_cappingDiffeo`:

* `Work.Milnor.no_cappingDiffeo_of_cappedCongruence` — `CappedCongruence → ∀ F hF, False`, by the
  endgame arithmetic: `⟨p₁(TX) ⌣ p₁(TX), [X]⟩ = 36 σ(X)`
  (`capped_p₁SqNumber_eq_thirtysix_sigma`) and `σ(X) = ±1` (`sigma_capped_eq_pm_one`) make the
  congruence read `7 ∣ 32·(±1)`.

So the remaining gap of the whole project can be taken to be `CappedCongruence`, whose proof must go
through the general signature theorem in dimension `8` (bordism + generation of `Ω^SO_8 ⊗ ℚ`, or
index theory — `Submission/NOTES.md` §8.4, §15.4, §15.8).
-/

open scoped Manifold ContDiff Topology

set_option maxHeartbeats 1600000

namespace Work.Milnor

open Work.Cohomology

noncomputable section

/-- **The corrected form of the remaining input.**  For every capping datum `F`, `hF` and every
fundamental class `c` of `X = D(ξ) ∪_F D⁸`, the dimension-`8` Hirzebruch congruence

`7 ∣ ⟨p₁(TX) ⌣ p₁(TX), [X]⟩ − 4 σ(X)`

holds, with `p₁(TX) = cappedPontryaginClass F hF` (the first Pontryagin class of the tangent bundle,
`Submission/Work/CharacteristicClasses/Capped.lean`).  This is the instance at `X` of the general
dimension-`8` signature theorem, in the form in which the endgame consumes it. -/
def CappedCongruence : Prop :=
  ∀ (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F)
    (c : (chainC ℤ (Work.SignatureBordism.cappedSSet F hF)).homology 8),
    Submodule.span ℤ {c} = ⊤ →
      7 ∣ Work.SignatureBordism.p₁SqNumber (Work.SignatureBordism.cappedSSet F hF) c
              (cappedPontryaginClass F hF)
            - 4 * Work.SignatureBordism.sigma 4 (Work.SignatureBordism.cappedSSet F hF) c

/-- **The endgame arithmetic.**  `CappedCongruence` implies `Work.Milnor.no_cappingDiffeo`: on
`X = D(ξ) ∪_F D⁸` the `p₁²`-number is `36 σ` and `σ = ±1`, so the congruence would read
`7 ∣ 32·(±1)`. -/
theorem no_cappingDiffeo_of_cappedCongruence (h : CappedCongruence) :
    ∀ (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F), False := by
  intro F hF
  obtain ⟨c, hc⟩ := Work.SignatureBordism.exists_capped_fundamentalClass F hF
  have hcong := h F hF c hc
  have h36 := Work.SignatureBordism.capped_p₁SqNumber_eq_thirtysix_sigma F hF c hc
  rcases Work.SignatureBordism.sigma_capped_eq_pm_one F hF c hc with hσ | hσ
  · rw [h36, hσ] at hcong
    norm_num at hcong
  · rw [h36, hσ] at hcong
    norm_num at hcong

/-- The same, in the exact shape of `Work.Milnor.no_cappingDiffeo`. -/
theorem no_cappingDiffeo_of_cappedCongruence' (h : CappedCongruence)
    (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F) : False :=
  no_cappingDiffeo_of_cappedCongruence h F hF


/-- **THE REMAINING GAP OF THE PROJECT**, in its corrected form: the dimension-`8` Hirzebruch
congruence for the capped family.  It is *true* (the quantification over capping data is over the
empty type, since `Work.Milnor.no_cappingDiffeo` — the statement it implies — holds) and it is the
instance at `X = D(ξ) ∪_F D⁸` of the classical **Hirzebruch signature theorem in dimension `8`**,
whose proof needs the bordism-theoretic computation `Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}` together
with bordism invariance of `σ`, `p₁²`, `p₂` (see `Submission/NOTES.md` §8.4, §15.4, §15.8, and the
subprojects `Submission/Work/Bordism/`, `Submission/Work/UnimodularForms/`,
`Submission/Work/Projective/`, `Submission/Work/OrientedBordism8/`), or (equivalently hard) the
Atiyah–Singer index theorem for the signature operator.

This is the only `sorry` of the project. -/
theorem cappedCongruence : CappedCongruence := by
  sorry

end

end Work.Milnor
