import Submission.Work.Wire123.not_totaroInput
import Submission.Work.Totaro.Interface

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.CohomologicalObstruction` — the cohomological inputs are uninstantiable too

The brief for the wiring of Theorem 1.2 (3) suggests producing Totaro's input `T` either from the
cohomological input or from the paper's corollary:

```lean
Work.Totaro.totaroInput_CY3            (h : CohDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜))
Work.Totaro.totaroInput_CY3_of_CorCYnSB (h : CorCYnSB 𝕜 (Work.CY3.PicardRankOne 𝕜))
```

Both `h`'s are of the same shape as `Work.CY3.TotaroInput 𝕜` and are refutable for the same
reason: every field of `CohDistinguishing`, `CohSeparationDistinguishing` and `CorCYnSB` quantifies
over *all* pairs of `𝕜`-varieties whose geometric hypotheses are carried by the **fieldless**
predicates `Work.K3.IsKTrivial`, `Work.K3.PicardRankOneGeom`, `Work.CY3.PicardRankOne` — hence
satisfied by every variety.  A single stably birational, non-isomorphic pair therefore refutes all
of them:

* `Work.Wire123.not_isoOver_affineSpace_zero_one` — `𝔸⁰` and `𝔸¹` are not isomorphic over `𝕜`
  (an isomorphism would give a ring isomorphism `𝕜[X] ≅ 𝕜`);
* `Work.Wire123.stablyBirational_affineSpace_zero_one` — they are stably birational
  (exponents `1`, `0`: both products are the same pullback in the two orders).

Consequently **none** of the four producer routes for `T` listed in the brief
(`totaroInput_CY3`, `…_of_CorCYnSB`, `…_of_separation`, and their `K3` analogues) can be
instantiated, and the repairs are the per-pair interfaces
(`Work.Wire123.TotaroInputAt`, `Work.Wire123.CentreSeparation`) together with the chain of
`Submission/Work/Wire123/Chain.lean`.

The general principle, isolated: a *cohomological certificate for every pair* is inconsistent with
the existence of a stably birational pair of non-isomorphic varieties, because the certificate's
own product-decomposition argument (`CohKunneth.affine_eq`, `CohSeparation.affine_eq`) collapses
the cylinder relation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- The two test varieties: `𝔸⁰` and `𝔸¹` over `𝕜`. -/
abbrev A0 (𝕜 : Type) [Field 𝕜] : Scheme.{0} := 𝔸(Fin 0; Spec (.of 𝕜))
abbrev A1 (𝕜 : Type) [Field 𝕜] : Scheme.{0} := 𝔸(Fin 1; Spec (.of 𝕜))

/-- **A `CohKunneth` certificate for a stably birational pair is contradictory**: its
product-decomposition argument identifies the invariant on `X` and on `Y`. -/
theorem not_cohkunneth_of_stablyBirational (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}}
    [Variety 𝕜 X] [Variety 𝕜 Y] (hsb : Work.CY3.StablyBirational 𝕜 X Y) :
    ¬ Nonempty (Work.Totaro.CohKunneth 𝕜 X Y) :=
  fun ⟨K⟩ => K.not_stablyBirational hsb

/-- **A `CohSeparation` certificate for a stably birational pair is contradictory.** -/
theorem not_cohseparation_of_stablyBirational (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}}
    [Variety 𝕜 X] [Variety 𝕜 Y] (hsb : Work.CY3.StablyBirational 𝕜 X Y) :
    ¬ Nonempty (Work.Totaro.CohSeparation 𝕜 X Y) :=
  fun ⟨C⟩ => C.not_stablyBirational hsb

/-- **The Künneth-form cohomological input is refutable at the CY3 Picard-rank-one predicate.** -/
theorem not_cohdDistinguishing_CY3 (𝕜 : Type) [Field 𝕜] :
    ¬ Work.Totaro.CohDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜) := fun h =>
  not_cohkunneth_of_stablyBirational 𝕜 (stablyBirational_affineSpace_zero_one 𝕜)
    (h (A0 𝕜) (A1 𝕜) ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ (not_isoOver_affineSpace_zero_one 𝕜))

/-- **The Künneth-form cohomological input is refutable at the K3 Picard-rank-one predicate.** -/
theorem not_cohdDistinguishing_K3 (𝕜 : Type) [Field 𝕜] :
    ¬ Work.Totaro.CohDistinguishing 𝕜 (Work.K3.PicardRankOneGeom 𝕜) := fun h =>
  not_cohkunneth_of_stablyBirational 𝕜 (stablyBirational_affineSpace_zero_one 𝕜)
    (h (A0 𝕜) (A1 𝕜) ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ (not_isoOver_affineSpace_zero_one 𝕜))

/-- **The per-pair cohomological input is refutable at the CY3 predicate.** -/
theorem not_cohdSeparationDistinguishing_CY3 (𝕜 : Type) [Field 𝕜] :
    ¬ Work.Totaro.CohSeparationDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜) := fun h =>
  not_cohseparation_of_stablyBirational 𝕜 (stablyBirational_affineSpace_zero_one 𝕜)
    (h (A0 𝕜) (A1 𝕜) ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ (not_isoOver_affineSpace_zero_one 𝕜))

/-- **The per-pair cohomological input is refutable at the K3 predicate.** -/
theorem not_cohdSeparationDistinguishing_K3 (𝕜 : Type) [Field 𝕜] :
    ¬ Work.Totaro.CohSeparationDistinguishing 𝕜 (Work.K3.PicardRankOneGeom 𝕜) := fun h =>
  not_cohseparation_of_stablyBirational 𝕜 (stablyBirational_affineSpace_zero_one 𝕜)
    (h (A0 𝕜) (A1 𝕜) ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ (not_isoOver_affineSpace_zero_one 𝕜))

/-- **The paper's corollary `cor-CYnSB`, as recorded, is refutable at the CY3 predicate**: its
`not_birational_affine` field, applied to `𝔸⁰` and `𝔸¹` with the exponents `1` and `0`, forbids the
birational map of the two cylinders which exists. -/
theorem not_corCYnSB_CY3 (𝕜 : Type) [Field 𝕜] :
    ¬ Work.Totaro.CorCYnSB 𝕜 (Work.CY3.PicardRankOne 𝕜) := by
  intro h
  have hV1 : Variety 𝕜 (Work.K3.prodOver 𝕜 (A0 𝕜) (A1 𝕜)) :=
    Classical.choice (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 (A0 𝕜) 1)
  have hV0 : Variety 𝕜 (Work.K3.prodOver 𝕜 (A1 𝕜) (A0 𝕜)) :=
    Classical.choice (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 (A1 𝕜) 0)
  haveI := hV1
  haveI := hV0
  have hzero := h.not_birational_affine (A0 𝕜) (A1 𝕜) ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩
    (not_isoOver_affineSpace_zero_one 𝕜) 1 0 hV1 hV0
  haveI h1 : Variety 𝕜 (pullback ((A0 𝕜) ↘ Spec (.of 𝕜)) ((A1 𝕜) ↘ Spec (.of 𝕜))) :=
    Classical.choice (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 (A0 𝕜) 1)
  haveI h2 : Variety 𝕜 (pullback ((A1 𝕜) ↘ Spec (.of 𝕜)) ((A0 𝕜) ↘ Spec (.of 𝕜))) :=
    Classical.choice (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 (A1 𝕜) 0)
  exact hzero ⟨(PartialIso.ofIso (pullbackSymmetry ((A0 𝕜) ↘ Spec (.of 𝕜))
    ((A1 𝕜) ↘ Spec (.of 𝕜)))).toBirationalMap⟩

/-- **The K3 chapter's universal Totaro input is refutable for the same reason.**  It has the shape
of `Work.CY3.TotaroInput` at the (fieldless) K3 Picard-rank-one predicate, so the pair `𝔸⁰`, `𝔸¹`
refutes it.  This is relevant beyond the present area: the `n ≥ 4` wiring of the challenge
(`Work.K3.not_gen_of_K3_kSubC`, `Work.K3Inputs.HLPayoff`) consumes `Work.K3.TotaroInput`, so it is
blocked in the same way as the `n ≥ 5` case. -/
theorem not_k3TotaroInput (𝕜 : Type) [Field 𝕜] : ¬ Work.K3.TotaroInput 𝕜 := fun T =>
  T.not_stablyBirat_of_not_iso (A0 𝕜) (A1 𝕜) ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩
    (not_isoOver_affineSpace_zero_one 𝕜) (stablyBirational_affineSpace_zero_one 𝕜)

end

end Work.Wire123
