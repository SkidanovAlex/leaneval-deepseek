import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
