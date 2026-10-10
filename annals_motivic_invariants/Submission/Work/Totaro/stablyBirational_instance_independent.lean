import Mathlib
import Submission.Work.Totaro.Defs
import Submission.Work.Totaro.partialIso_prod_affine
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Totaro

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants

noncomputable section

set_option linter.style.haveILetI false

variable {𝕜 : Type} [Field 𝕜]

/-! ## The `Spec ℤ`-model of `X × 𝔸ⁿ`

`Work.K3.prodOver 𝕜 X 𝔸ⁿ` is the fibre product of `X ⟶ Spec 𝕜` and `𝔸ⁿ ⟶ Spec 𝕜`, so it
depends on the chosen structure morphism `X ⟶ Spec 𝕜`.  Since `Spec ℤ` is terminal, `X` has a
unique morphism to `Spec ℤ`, and `X ×_𝕜 𝔸ⁿ` is canonically isomorphic to the base change of `X`
(over `Spec ℤ`) along `𝔸ⁿ_ℤ ⟶ Spec ℤ` — an object which mentions no `𝕜`-structure on `X`. -/

/-- The canonical (`Spec ℤ`-based) model of `X × 𝔸ⁿ`: the base change of `X` (over `Spec ℤ`,
along the unique morphism `X ⟶ Spec ℤ`) of the affine space `𝔸ⁿ_ℤ ⟶ Spec ℤ`. -/
noncomputable def canonProd (X : Scheme.{0}) (n : ℕ) : Scheme.{0} :=
  pullback (affineNZMap n) (AlgebraicGeometry.specZIsTerminal.from X)

/-- **`X ×_𝕜 𝔸ⁿ` is the `Spec ℤ`-model of `X × 𝔸ⁿ`, for any `𝕜`-structure on `X`.**  This
is `Work.Totaro.prodOver_affineN_iso` followed by the identification of the two morphisms
`X ⟶ Spec ℤ` (`Work.Totaro.specZ_hom_ext`). -/
noncomputable def prodOver_iso_canonProd (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (n : ℕ) :
    Work.K3.prodOver 𝕜 X (AffineN 𝕜 n) ≅ canonProd X n := by
  have h : (X ↘ Spec (.of 𝕜)) ≫ specZMap (𝕜 := 𝕜) = specZIsTerminal.from X :=
    specZ_hom_ext _ _
  exact prodOver_affineN_iso X n ≪≫ eqToIso (by unfold canonProd; rw [h])

/-- **Stable birationality, in the form that mentions no `Variety`/`Over` instance**: `X` and `Y`
are stably birational when the canonical models `X × 𝔸ⁿ` and `Y × 𝔸ᵐ` are birational for some
`n`, `m`.  This is a statement about the two schemes `X`, `Y` alone. -/
def CanSB (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) : Prop :=
  ∃ n m : ℕ, Scheme.Birational (canonProd X n) (canonProd Y m)

/-- **`Work.K3.StablyBirational` agrees with the instance-free form `Work.Totaro.CanSB`.**

Both directions only use the canonical isomorphism `Work.Totaro.prodOver_iso_canonProd`
(transported through `Scheme.Birational`, which is a statement about the underlying schemes and
therefore insensitive to the `Over`-structure of the two products): the `Variety` instances
bound in the existential of `Work.K3.StablyBirational` supply exactly the irreducibility needed
to turn a `BirationalMap` into a partial isomorphism
(`Work.Motivic.exists_partialIso_toBirationalMap`), and in the converse direction the `Variety`
instances of the products are produced by `Work.K3Inputs.exists_variety_prodOver_affineSpace`. -/
theorem stablyBirational_iff_canSB (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y] :
    Work.K3.StablyBirational 𝕜 X Y ↔ CanSB 𝕜 X Y := by
  constructor
  · rintro ⟨n, m, hvX, hvY, φ⟩
    obtain ⟨φ⟩ := φ
    haveI := hvX.isIntegral
    haveI := hvY.isIntegral
    obtain ⟨i, -⟩ := Work.Motivic.exists_partialIso_toBirationalMap φ
    exact ⟨n, m, ⟨(PartialIso.ofIso (prodOver_iso_canonProd X n).symm).trans
      (i.trans (PartialIso.ofIso (prodOver_iso_canonProd Y m)))⟩⟩
  · rintro ⟨n, m, hb⟩
    obtain ⟨i⟩ := hb
    haveI hvX : Variety 𝕜 (Work.K3.prodOver 𝕜 X (AffineN 𝕜 n)) :=
      Classical.choice (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 X n)
    haveI hvY : Variety 𝕜 (Work.K3.prodOver 𝕜 Y (AffineN 𝕜 m)) :=
      Classical.choice (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 Y m)
    exact ⟨n, m, hvX, hvY,
      ⟨((PartialIso.ofIso (prodOver_iso_canonProd X n)).trans
        (i.trans (PartialIso.ofIso (prodOver_iso_canonProd Y m).symm))).toBirationalMap⟩⟩

/-- **Stable birationality does not depend on the chosen `𝕜`-structure of the two schemes.**  The relation `Work.Totaro.StablyBirational 𝕜 X Y` takes `Variety 𝕜 X`, `Variety 𝕜 Y` as instance arguments and its products `X ×_𝕜 𝔸ⁿ` are fibre products over `Spec 𝕜`, hence depend on the structure morphisms.  But `Spec ℤ` is the terminal scheme, so `X ×_{s} 𝔸ⁿ` is canonically isomorphic to `X ×_ℤ 𝔸ⁿ_ℤ` (`Work.Totaro.prodOver_affineN_iso`, the two morphisms `X ⟶ Spec ℤ` being equal by `Work.Totaro.specZ_hom_ext`), which does not depend on `s`: hence the proposition is the same for every choice of the two instances.  This is what allows an invariant which is a function of the *scheme* alone (as `Work.Totaro.CohSeparation.toFun` is) to be compared with the relation of the two chapters. -/
theorem stablyBirational_instance_independent {𝕜 : Type} [Field 𝕜]
    (X Y : AlgebraicGeometry.Scheme.{0})
    (hX : MotivicInvariants.Variety 𝕜 X) (hY : MotivicInvariants.Variety 𝕜 Y)
    (hX' : MotivicInvariants.Variety 𝕜 X) (hY' : MotivicInvariants.Variety 𝕜 Y) :
    (@Work.Totaro.StablyBirational 𝕜 _ X Y hX hY ↔
      @Work.Totaro.StablyBirational 𝕜 _ X Y hX' hY') := by
  have e1 : @Work.K3.StablyBirational 𝕜 _ X Y hX hY ↔ CanSB 𝕜 X Y :=
    @stablyBirational_iff_canSB 𝕜 _ X Y hX hY
  have e2 : @Work.K3.StablyBirational 𝕜 _ X Y hX' hY' ↔ CanSB 𝕜 X Y :=
    @stablyBirational_iff_canSB 𝕜 _ X Y hX' hY'
  exact e1.trans e2.symm

end

end Work.Totaro
