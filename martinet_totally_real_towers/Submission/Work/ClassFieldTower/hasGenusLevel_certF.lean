import Mathlib
import Submission.Work.ClassFieldTower.ProTwoGenus
import Submission.Work.ClassFieldTower.ProTwoGeneratorRank
import Submission.Work.ClassFieldTower.differentIdeal_eq_top_of_isUnramifiedAtFinitePrimes
import Submission.Work.ClassFieldTower.multiQuad_aut_pow_two
import Submission.Work.ClassFieldTower.classGroupTwoRank_eq_finrank_modN
import Submission.Work.QuadraticFields.CertificateSummary
import Submission.Work.QuadraticFields.ClassGroupBridge

/-!
# `Work.ClassFieldTower.hasGenusLevel_certF` -- the genus level of `ℚ(√-3556995)`

`Submission/Work/QuadraticFields` builds a second explicit imaginary quadratic certificate,

  `F = ℚ(√-3556995)`,  `disc F = -3556995 = -3·5·13·17·29·37`,

with the unramified multiquadratic extension `M = ℚ(√-3,√5,√13,√17,√29,√37)` of degree
`2^5 = 32` (`cert_full`, `cert_five_generators`).  The numerical *class-group* form of their
certificate (`rankTwo_classGroup_certificate`) is conditional on their Artin-reciprocity bridge
`Work.QuadraticFields.UnramifiedRankBridge`; the *genus-level* form is unconditional.

This module transfers their certificate into the vocabulary of the class-field-tower chapter:

* `hasGenusLevel_certF` -- `HasGenusLevel ↥certF`, i.e. `ℚ(√-3556995)` has an unramified
  exponent-`2` Galois extension of degree `2^5`, with NO class field theory (this is what
  `Work.QuadraticFields.GenusCertificate` proves, read through the different of a finitely
  ramified extension);
* `hasFiveIndependentUnramifiedQuadratics_certF` -- hence `G_∅ ↠ (𝔽₂)^5` for every maximal
  unramified pro-`2` extension of `↥certF`, i.e. `d(G_∅) ≥ 5` there;
* `infiniteProTwoExtension_certF_of_shafarevichKoch` -- the Shafarevich--Koch input for their
  field implies an infinite unramified pro-`2` extension, exactly as for `Kc = ℚ(√-30030)`
  (`Wall.lean`);
* `five_le_classGroupTwoRank_certF_of_artin` -- the class-group form of their numerical
  certificate, in this chapter's normalisation `classGroupTwoRank` (the `2`-rank of the class
  group), still conditional on their bridge.

So the chapter is field-agnostic: any field with a genus level plus the Shafarevich--Koch
relation bound has an infinite unramified pro-`2` extension. -/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **The genus level of `↥certF = ℚ(√-3556995)`.**

`Work.QuadraticFields.cert_full` gives that `certM = ℚ(√-3,√5,√13,√17,√29,√37)` is unramified over
`certF` (at all finite primes) of degree `2^5 = 32`; the multiquadratic structure gives exponent
`2` (`multiQuad_aut_pow_two`), and the unramifiedness in terms of ramification indices is converted
into the triviality of the relative different
(`differentIdeal_eq_top_of_isUnramifiedAtFinitePrimes`). -/
theorem hasGenusLevel_certF : HasGenusLevel ↥(Work.QuadraticFields.certF) := by
  classical
  obtain ⟨hunr, -, hfr⟩ := Work.QuadraticFields.cert_full
  haveI hgalM : IsGalois ℚ Work.QuadraticFields.certM :=
    Work.QuadraticFields.multiQuad_isGalois Work.QuadraticFields.certPrimesQ
  haveI hgal : IsGalois ↥(Work.QuadraticFields.certF) Work.QuadraticFields.certM :=
    IsGalois.tower_top_of_isGalois ℚ ↥(Work.QuadraticFields.certF) Work.QuadraticFields.certM
  haveI hfd : FiniteDimensional ↥(Work.QuadraticFields.certF) Work.QuadraticFields.certM :=
    Module.Finite.right ℚ ↥(Work.QuadraticFields.certF) Work.QuadraticFields.certM
  refine ⟨Work.QuadraticFields.certM, inferInstance, inferInstance, inferInstance, hfd, hgal,
    differentIdeal_eq_top_of_isUnramifiedAtFinitePrimes hunr, ?_, ?_⟩
  · -- exponent `2`: every automorphism of the multiquadratic field is an involution
    intro σ
    have h := multiQuad_aut_pow_two Work.QuadraticFields.certPrimesQ (σ.restrictScalars ℚ)
    have hfun : ∀ x : Work.QuadraticFields.certM, σ (σ x) = x := by
      intro x
      have h2 := congrFun (congrArg
        (fun f : Work.QuadraticFields.certM ≃ₐ[ℚ] Work.QuadraticFields.certM =>
          (f : Work.QuadraticFields.certM → Work.QuadraticFields.certM)) h) x
      simpa using h2
    exact AlgEquiv.ext hfun
  · -- the Galois group has order `2^5 = [certM : ↥certF]`
    calc Nat.card (Work.QuadraticFields.certM ≃ₐ[↥(Work.QuadraticFields.certF)]
            Work.QuadraticFields.certM)
        = Module.finrank ↥(Work.QuadraticFields.certF) Work.QuadraticFields.certM :=
          IsGalois.card_aut_eq_finrank _ _
      _ = 32 := hfr
      _ = 2 ^ 5 := by norm_num

/-- **`G_∅ ↠ (𝔽₂)^5` for every maximal unramified pro-`2` extension of `ℚ(√-3556995)`.**

Unconditional (genus theory only): the generator half of the Golod--Shafarevich input for the
second explicit imaginary quadratic field of the project. -/
theorem hasFiveIndependentUnramifiedQuadratics_certF
    (M : MaximalUnramifiedProP.{0} ↥(Work.QuadraticFields.certF) 2) :
    HasFiveIndependentUnramifiedQuadratics M :=
  hasFiveIndependentUnramifiedQuadratics_of_genusLevel M hasGenusLevel_certF

/-- **The Shafarevich--Koch input for `ℚ(√-3556995)` implies an infinite unramified pro-`2`
extension thereof** (with no further numerical input, since the generator bound comes from the
genus level).  Compare `Work.ClassFieldTower.KcWall` for `ℚ(√-30030)`. -/
theorem infiniteProTwoExtension_certF_of_shafarevichKoch
    (h : ProTwoShafarevichKochInput ↥(Work.QuadraticFields.certF)) :
    InfiniteProTwoExtension ↥(Work.QuadraticFields.certF) :=
  infiniteProTwoExtension_of_shafarevichKoch_and_genusLevel h hasGenusLevel_certF

/-- **Their numerical certificate, in this chapter's normalisation.**  Under the
Artin-reciprocity bridge of `Work.QuadraticFields` (`UnramifiedRankBridge`), the unramified degree
`32` extension of `ℚ(√-3556995)` gives `5 ≤ classGroupTwoRank` for that field.  The two notions of
`2`-rank agree because `Work.QuadraticFields.rankTwo A` is by definition
`Module.finrank (ZMod 2) (ModN (Additive A) 2)`, which is `classGroupTwoRank` up to the
identification `classGroupTwoRank_eq_finrank_modN`. -/
theorem five_le_classGroupTwoRank_certF_of_artin
    (h : Work.QuadraticFields.UnramifiedRankBridge ↥(Work.QuadraticFields.certF) 5) :
    5 ≤ classGroupTwoRank ↥(Work.QuadraticFields.certF) := by
  have h5 := Work.QuadraticFields.rankTwo_classGroup_certificate h
  rw [classGroupTwoRank_eq_finrank_modN]
  exact h5

end Work.ClassFieldTower
