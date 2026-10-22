import Mathlib
import Submission.Work.ANALYTIC.Basic

/-!
# `∏_{OnePoint ℕ} ℤ ≅ ℤ ⊞ ∏_ℕ ℤ`

The countable product `∏_{i : OnePoint ℕ} ℤ` (with `OnePoint ℕ = Option ℕ`) is the product over the
index set `{∞} ⊔ ℕ`, hence is the binary product `ℤ ⨯ ∏_ℕ ℤ`; since `ℤ ⊞ ∏_ℕ ℤ` is a binary
biproduct, and binary biproducts of an additive category are binary products
(`biprod.isoProd`), we obtain `∏_{OnePoint ℕ} ℤ ≅ ℤ ⊞ ∏_ℕ ℤ`.

The decomposition of the product is proved via the limit cone `optionFan` on `ℤ ⨯ ∏_ℕ ℤ` whose
`∞`-projection is `prod.fst` and whose `n`-projection is `prod.snd ≫ Pi.π _ n`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint _root_.LightCondensed

noncomputable section

namespace Work.ANALYTIC

/-- The canonical projections of `Z ⨯ ∏_ℕ Z` indexed by `OnePoint ℕ = Option ℕ`: the `∞`-component
is the first projection and the `n`-th component is the `n`-th coordinate of the second
projection. -/
def optionProj (i : OnePoint ℕ) : (Z ⨯ prodZ) ⟶ Z :=
  OnePoint.elim i prod.fst (fun n => prod.snd ≫ Pi.π (fun _ : ℕ => Z) n)

@[simp]
theorem optionProj_infty : optionProj ∞ = prod.fst := rfl

@[simp]
theorem optionProj_some (n : ℕ) :
    optionProj (OnePoint.some n) = prod.snd ≫ Pi.π (fun _ : ℕ => Z) n := rfl

/-- `Z ⨯ ∏_ℕ Z`, regarded as a fan over `OnePoint ℕ` with the constant value `Z`. -/
def optionFan : Fan (fun _ : OnePoint ℕ => Z) := Fan.mk (Z ⨯ prodZ) optionProj

@[simp]
theorem optionFan_proj (i : OnePoint ℕ) : optionFan.proj i = optionProj i := rfl

/-- **The product `∏_{OnePoint ℕ} ℤ` splits as `ℤ ⨯ ∏_ℕ ℤ`.**  This is the fan `optionFan`
exhibited as a limit fan: a cone over the discrete index set `OnePoint ℕ` is exactly a pair of
maps into `Z` and into `∏_ℕ Z`. -/
def isLimit_optionFan : IsLimit optionFan :=
  Fan.IsLimit.mk optionFan
    (fun s => prod.lift (s.proj ∞) (Pi.lift (fun n => s.proj (OnePoint.some n))))
    (fun _ i => by
      induction i using OnePoint.rec with
      | infty => simp [optionFan, optionProj]
      | coe n => simp [optionFan, optionProj])
    (fun s m hm => by
      apply prod.hom_ext
      · rw [prod.lift_fst]
        exact hm ∞
      · rw [prod.lift_snd]
        apply Pi.hom_ext
        intro n
        rw [Pi.lift_comp_π]
        exact (Category.assoc m prod.snd (Pi.π (fun _ : ℕ => Z) n)).trans
          (hm (OnePoint.some n)))

/-- **`∏_{OnePoint ℕ} ℤ ≅ ℤ ⨯ ∏_ℕ ℤ`.** -/
def piOnePointIsoProd : (∏ᶜ (fun _ : OnePoint ℕ => Z)) ≅ Z ⨯ prodZ :=
  IsLimit.conePointUniqueUpToIso (productIsProduct (fun _ : OnePoint ℕ => Z)) isLimit_optionFan

theorem pi_option_iso_biprod :
    Nonempty (CategoryTheory.Iso (∏ᶜ (fun _ : OnePoint ℕ => Work.ANALYTIC.Z))
      (CategoryTheory.Limits.biprod Work.ANALYTIC.Z Work.ANALYTIC.prodZ)) :=
  ⟨piOnePointIsoProd.trans (biprod.isoProd Z prodZ).symm⟩

end Work.ANALYTIC
