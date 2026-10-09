import Mathlib
import Submission.NK.NUV2.RouteB.RayModulus.Defs
import Submission.NK.NUV2.RouteB.CongClassSetup
import Submission.NK.NUV2.RouteB.RayModulus.CosetCountDefs
import Submission.NK.NUV2.RouteB.latticeCosetCount_cone_isBigO
import Submission.NK.NUV2.RouteB.Dict.latticeCosetCount_halfspaces_isBigO
import Submission.Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The ray-class/lattice dictionary: vocabulary

For a number field `K` and a modulus `𝔪` (a finitely supported exponent function plus a set `pos`
of real places), this file fixes the vocabulary used to express the count of the ideals of `𝓞 K`
in a ray class of the congruence subgroup `CongSubgroup K 𝔪` as a sum of lattice-coset counts in
the mixed space.

The dictionary (proved downstream) is

`torsionOrder K * rayClassCnt K 𝔪 𝔡 X = ∑ q : (𝓞 K)ˣ ⧸ congUnit K 𝔪, cosetConeCnt K 𝔪 𝔡 (out q)⁻¹ (X / absNorm 𝔡)`

where `congUnit K 𝔪` is the group of units congruent to `1` modulo the support of `𝔪` and positive
at the places of `𝔪.pos`, and `cosetConeCnt` is the number of points of the lattice coset
`γ + 𝔪·𝔡⁻¹` lying in the fundamental cone, satisfying the sign conditions of `γ`, with norm `≤ t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

noncomputable section

namespace NK.NUV2.HeckeAnalytic

variable {K : Type} [Field K] [NumberField K]

/-- The real-valued unit map at a real place `w`, as a monoid homomorphism. -/
noncomputable def unitToReal (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) : (𝓞 K)ˣ →* ℝˣ :=
  (Units.map (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw :
    w.Completion →+* ℝ).toMonoidHom).comp
    ((Units.map (algebraMap K w.Completion).toMonoidHom).comp
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom))

/-- The subgroup of the units of `𝓞 K` which are positive at every real place of `pos`. -/
noncomputable def posUnits (K : Type) [Field K] [NumberField K]
    (pos : Set (InfinitePlace K)) : Subgroup (𝓞 K)ˣ :=
  ⨅ (w : {w : InfinitePlace K // w ∈ pos ∧ w.IsReal}),
    (Units.posSubgroup ℝ).comap (unitToReal K w.1 w.2.2)

/-- The group `Λ` of units congruent to `1` modulo the ideal of the modulus and positive at
`𝔪.pos`.  These are the units acting trivially on the ray classes. -/
def congUnit (𝔪 : NK.NUV2.RouteB.Modulus K) : Subgroup (𝓞 K)ˣ :=
  NK.NUV2.RouteB.unitCongOne 𝔪.ideal ⊓ posUnits K 𝔪.pos

/-- The lattice `𝔪.ideal · 𝔡⁻¹` attached to the modulus `𝔪` and the base ideal `𝔡`. -/
noncomputable def dictLattice (𝔪 : NK.NUV2.RouteB.Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ :=
  NK.NUV2.RouteB.Modulus.fracIdeal 𝔪 𝔡

/-- The number of points of the coset `mixedEmbedding γ + L(𝔪·𝔡⁻¹)` of the lattice of the
fractional ideal `𝔪·𝔡⁻¹` that lie in the fundamental cone, satisfy the sign conditions of `γ` at
the places of `𝔪.pos`, and have norm `≤ t`. -/
noncomputable def cosetConeCnt (𝔪 : NK.NUV2.RouteB.Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (γ : K) (t : ℝ) : ℕ :=
  Nat.card {y : mixedSpace K //
    y - mixedEmbedding K γ ∈ (idealLattice K (dictLattice 𝔪 𝔡) : Set (mixedSpace K)) ∧
    y ∈ fundamentalCone K ∧
    (∀ w : {w : InfinitePlace K // w ∈ 𝔪.pos ∧ w.IsReal},
      ((mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ > 0 ∧ y.1 ⟨w.1, w.2.2⟩ > 0) ∨
      ((mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ < 0 ∧ y.1 ⟨w.1, w.2.2⟩ < 0)) ∧
    mixedEmbedding.norm y ≤ t}

end NK.NUV2.HeckeAnalytic
