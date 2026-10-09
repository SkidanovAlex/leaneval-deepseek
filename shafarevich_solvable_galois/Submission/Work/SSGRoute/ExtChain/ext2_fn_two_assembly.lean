import Mathlib
import Submission.Work.ExtChain.PtorExtTools
import Submission.Work.SSGRoute.ExtChain.twoTorsionDecomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Assembly of the `p = 2` transfer of the degree-two Hasse principle

Two pieces:

* `ext_injective_of_two_block`: injectivity of `z ↦ z.comp (mk₀ φ)` on `Ext²(X,·)` follows from the
  corresponding statement on two blocks `T`, `R` of a decomposition
  `X ≅ T ⊕ R` (recorded as maps `inclT, projT, inclR, projR` with
  `projT ≫ inclT + projR ≫ inclR = 𝟙 X`), by reconstructing a class from its two projections;
* transfers of the two block statements from the `Finsupp`-models `trivPow 2 H a`, `regPow 2 H b`
  to the transparent abbreviations `trivPow' a`, `regPow' b` used in the structure theorem.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

noncomputable section

attribute [local instance] Classical.decEq

attribute [local instance 2000] Rep.hV2

/-! ## Injectivity from a two-block decomposition -/

/-- **Injectivity from a two-block decomposition.**  If `Ext²(T,A) → Ext²(T,B)` and
`Ext²(R,A) → Ext²(R,B)` are injective, and `X` is the sum of the two blocks `T, R` (witnessed by
`projT ≫ inclT + projR ≫ inclR = 𝟙 X`), then `Ext²(X,A) → Ext²(X,B)` is injective. -/
theorem ext_injective_of_two_block {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X T R A B : C} (φ : A ⟶ B) (inclT : T ⟶ X) (projT : X ⟶ T)
    (inclR : R ⟶ X) (projR : X ⟶ R)
    (hsplit : projT ≫ inclT + projR ≫ inclR = 𝟙 X)
    (hT : Function.Injective (fun z : Abelian.Ext T A 2 =>
      z.comp (Abelian.Ext.mk₀ φ) (add_zero 2)))
    (hR : Function.Injective (fun z : Abelian.Ext R A 2 =>
      z.comp (Abelian.Ext.mk₀ φ) (add_zero 2))) :
    Function.Injective (fun z : Abelian.Ext X A 2 =>
      z.comp (Abelian.Ext.mk₀ φ) (add_zero 2)) := by
  -- the reconstruction identity from the two projections
  have hsum : Abelian.Ext.mk₀ (projT ≫ inclT) + Abelian.Ext.mk₀ (projR ≫ inclR)
      = Abelian.Ext.mk₀ (𝟙 X) := by
    rw [← Abelian.Ext.mk₀_add, hsplit]
  have hstepT : ∀ z : Abelian.Ext X A 2,
      (Abelian.Ext.mk₀ (projT ≫ inclT)).comp z (zero_add 2)
        = (Abelian.Ext.mk₀ projT).comp ((Abelian.Ext.mk₀ inclT).comp z (zero_add 2))
            (zero_add 2) := by
    intro z
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    exact Abelian.Ext.comp_assoc_of_second_deg_zero (Abelian.Ext.mk₀ projT)
      (Abelian.Ext.mk₀ inclT) z (zero_add 2)
  have hstepR : ∀ z : Abelian.Ext X A 2,
      (Abelian.Ext.mk₀ (projR ≫ inclR)).comp z (zero_add 2)
        = (Abelian.Ext.mk₀ projR).comp ((Abelian.Ext.mk₀ inclR).comp z (zero_add 2))
            (zero_add 2) := by
    intro z
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    exact Abelian.Ext.comp_assoc_of_second_deg_zero (Abelian.Ext.mk₀ projR)
      (Abelian.Ext.mk₀ inclR) z (zero_add 2)
  have key : ∀ z : Abelian.Ext X A 2,
      z = (Abelian.Ext.mk₀ projT).comp ((Abelian.Ext.mk₀ inclT).comp z (zero_add 2))
            (zero_add 2)
        + (Abelian.Ext.mk₀ projR).comp ((Abelian.Ext.mk₀ inclR).comp z (zero_add 2))
            (zero_add 2) := by
    intro z
    have h2 : (Abelian.Ext.mk₀ (projT ≫ inclT) + Abelian.Ext.mk₀ (projR ≫ inclR)).comp z
          (zero_add 2)
        = (Abelian.Ext.mk₀ (projT ≫ inclT)).comp z (zero_add 2)
          + (Abelian.Ext.mk₀ (projR ≫ inclR)).comp z (zero_add 2) :=
      Abelian.Ext.add_comp _ _ z (zero_add 2)
    calc z = (Abelian.Ext.mk₀ (𝟙 X)).comp z (zero_add 2) :=
          (Abelian.Ext.mk₀_id_comp z).symm
      _ = (Abelian.Ext.mk₀ (projT ≫ inclT) + Abelian.Ext.mk₀ (projR ≫ inclR)).comp z
            (zero_add 2) := by rw [hsum]
      _ = (Abelian.Ext.mk₀ (projT ≫ inclT)).comp z (zero_add 2)
          + (Abelian.Ext.mk₀ (projR ≫ inclR)).comp z (zero_add 2) := h2
      _ = (Abelian.Ext.mk₀ projT).comp ((Abelian.Ext.mk₀ inclT).comp z (zero_add 2))
            (zero_add 2)
          + (Abelian.Ext.mk₀ projR).comp ((Abelian.Ext.mk₀ inclR).comp z (zero_add 2))
            (zero_add 2) := by rw [hstepT z, hstepR z]
  intro z w hzw
  have hzw' : z.comp (Abelian.Ext.mk₀ φ) (add_zero 2)
      = w.comp (Abelian.Ext.mk₀ φ) (add_zero 2) := hzw
  -- the two blocks agree
  have hT' : (Abelian.Ext.mk₀ inclT).comp z (zero_add 2)
      = (Abelian.Ext.mk₀ inclT).comp w (zero_add 2) := by
    apply hT
    change ((Abelian.Ext.mk₀ inclT).comp z (zero_add 2)).comp (Abelian.Ext.mk₀ φ) (add_zero 2)
      = ((Abelian.Ext.mk₀ inclT).comp w (zero_add 2)).comp (Abelian.Ext.mk₀ φ) (add_zero 2)
    have e1 : ((Abelian.Ext.mk₀ inclT).comp z (zero_add 2)).comp (Abelian.Ext.mk₀ φ)
          (add_zero 2)
        = (Abelian.Ext.mk₀ inclT).comp (z.comp (Abelian.Ext.mk₀ φ) (add_zero 2))
            (zero_add 2) :=
      Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ inclT) z
        (Abelian.Ext.mk₀ φ) (zero_add 2)
    have e2 : ((Abelian.Ext.mk₀ inclT).comp w (zero_add 2)).comp (Abelian.Ext.mk₀ φ)
          (add_zero 2)
        = (Abelian.Ext.mk₀ inclT).comp (w.comp (Abelian.Ext.mk₀ φ) (add_zero 2))
            (zero_add 2) :=
      Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ inclT) w
        (Abelian.Ext.mk₀ φ) (zero_add 2)
    rw [e1, e2, hzw']
  have hR' : (Abelian.Ext.mk₀ inclR).comp z (zero_add 2)
      = (Abelian.Ext.mk₀ inclR).comp w (zero_add 2) := by
    apply hR
    change ((Abelian.Ext.mk₀ inclR).comp z (zero_add 2)).comp (Abelian.Ext.mk₀ φ) (add_zero 2)
      = ((Abelian.Ext.mk₀ inclR).comp w (zero_add 2)).comp (Abelian.Ext.mk₀ φ) (add_zero 2)
    have e1 : ((Abelian.Ext.mk₀ inclR).comp z (zero_add 2)).comp (Abelian.Ext.mk₀ φ)
          (add_zero 2)
        = (Abelian.Ext.mk₀ inclR).comp (z.comp (Abelian.Ext.mk₀ φ) (add_zero 2))
            (zero_add 2) :=
      Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ inclR) z
        (Abelian.Ext.mk₀ φ) (zero_add 2)
    have e2 : ((Abelian.Ext.mk₀ inclR).comp w (zero_add 2)).comp (Abelian.Ext.mk₀ φ)
          (add_zero 2)
        = (Abelian.Ext.mk₀ inclR).comp (w.comp (Abelian.Ext.mk₀ φ) (add_zero 2))
            (zero_add 2) :=
      Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ inclR) w
        (Abelian.Ext.mk₀ φ) (add_zero 2)
    rw [e1, e2, hzw']
  rw [key z, key w, hT', hR']

/-! ## Transfer of the block statements to the transparent abbreviations -/

/-- Injectivity transfers from the trivial coefficient `𝔽₂ = trivOne 2 H` to `trivPow' a`. -/
theorem ext_injective_trivPow' {H : Type} [Group H] (a : ℕ)
    (A B : Rep.{0} Coeff H) (φ : A ⟶ B)
    (htriv : Function.Injective (fun z : Abelian.Ext.{0}
        (Rep.trivial Coeff H (ZMod 2)) A 2 =>
      z.comp (Abelian.Ext.mk₀ φ) (add_zero 2))) :
    Function.Injective (fun z : Abelian.Ext.{0} (trivPow' (H := H) a) A 2 =>
      z.comp (Abelian.Ext.mk₀ φ) (add_zero 2)) :=
  Work.ExtChain.ext_injective_trivPow (p := 2) a A B φ htriv

/-- `Ext²` of the regular block `regPow' b` vanishes. -/
theorem subsingleton_regPow' {H : Type} [Group H] (b : ℕ) (A : Rep.{0} Coeff H) :
    Subsingleton (Abelian.Ext.{0} (regPow' (H := H) b) A 2) :=
  Work.ExtChain.subsingleton_ext_regPow (p := 2) b A

/-- Injectivity on `Ext²(regPow' b, ·)` is automatic. -/
theorem ext_injective_regPow' {H : Type} [Group H] (b : ℕ)
    (A B : Rep.{0} Coeff H) (φ : A ⟶ B) :
    Function.Injective (fun z : Abelian.Ext.{0} (regPow' (H := H) b) A 2 =>
      z.comp (Abelian.Ext.mk₀ φ) (add_zero 2)) :=
  Work.ExtChain.ext_injective_regPow (p := 2) b A B φ

end

end Work.SSGRoute.ExtChain
