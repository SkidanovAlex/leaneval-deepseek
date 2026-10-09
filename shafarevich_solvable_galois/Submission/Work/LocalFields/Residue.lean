/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The residue field of a completion

For a finite prime `v` of a number field `K`, the residue field `κ_v = 𝒪_v/𝔪_v` of the
`v`-adic completion is canonically the residue field of `𝓞 K` at `v`, hence finite.  This file
sets up the reduction map and the induced isomorphism; the two facts about the reduction map
(surjectivity and kernel) are proven in the sibling files and give
`Work.LocalFields.instIsLocalFieldCompletion`.

## Main definitions

* `Work.LocalFields.residueMap` : the reduction map `𝓞 K →+* κ_v`.
* `Work.LocalFields.residueMap_apply` : its computation rule.

## Main results

* `Work.LocalFields.residueMap_surjective` (file `LocalFields/residueMap_surjective.lean`)
* `Work.LocalFields.residueMap_ker` (file `LocalFields/residueMap_ker.lean`)
* `Work.LocalFields.residueEquiv` : the induced isomorphism `𝓞 K ⧸ v ≃+* κ_v`.
* `Work.LocalFields.Finite_residueFieldOf`,
  `Work.LocalFields.instIsLocalFieldCompletion`
  (file `LocalFields/CompletionLocalField.lean`)
-/
import Submission.Work.LocalFields.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


namespace Work.LocalFields

open scoped NumberField Valued WithZero

section

variable {K : Type*} [Field K] [NumberField K] (v : FinitePrime K)

/-- The structure map of `𝒪_v` as an `𝓞 K`-algebra (through the inclusion
`𝓞 K → 𝒪_v`), obtained from the corresponding structure on
`IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers`. -/
noncomputable instance instAlgebraIntRing : Algebra (𝓞 K) (intRing K v) :=
  inferInstanceAs (Algebra (𝓞 K) (v.adicCompletionIntegers K))

/-- The canonical reduction map from the ring of integers of a number field to the residue
field of the completion at `v`: reduce first into `𝒪_v` (possible since the `v`-adic valuation
of an algebraic integer is `≤ 1`), then modulo the maximal ideal. -/
noncomputable def residueMap : 𝓞 K →+* residueFieldOf K v where
  toFun x := IsLocalRing.residue (intRing K v) (algebraMap (𝓞 K) (intRing K v) x)
  map_one' := rfl
  map_mul' := fun x y => by simp only [map_mul]
  map_zero' := rfl
  map_add' := fun x y => by simp only [map_add]

@[simp] theorem residueMap_apply (x : 𝓞 K) :
    residueMap v x = IsLocalRing.residue (intRing K v)
      (algebraMap (𝓞 K) (intRing K v) x) := rfl

end

end Work.LocalFields
