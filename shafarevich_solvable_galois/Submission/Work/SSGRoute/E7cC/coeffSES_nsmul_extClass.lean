import Mathlib
import Submission.Work.SSGRoute.phi1_defs
import Submission.Work.SSGRoute.ext_zmod_prime_iso_corrected
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The extension class of the coefficient sequence is annihilated by `p`

For a group `H` and a prime `p`, the short exact sequence of trivial `H`-representations

`0 → ℤ --p--> ℤ --red--> 𝔽_p → 0`

(whose two middle terms are the trivial representation `unitRep H` and whose right term is the
trivial representation on `ZMod p`) has extension class

`(SSGRoute.Phi1.coeffSES_shortExact H p).extClass ∈ Ext¹_H(𝔽_p, ℤ)`.

The theorem below shows that `p` kills this class.

The proof is elementary and uses no coefficient arithmetic on the sequence: for **any** `Ext`-group
element `x : Ext X Y n` and any natural number `p`, the iterated sum `p • x` (the `nsmul` of the
abelian group `Ext X Y n`) equals the Yoneda composite `x.comp (mk₀ (p • 𝟙 Y))`, because
composition of `Ext` is additive in its second variable (`Ext.comp_add`) and `mk₀` is additive
(`Ext.mk₀_add`).  Specialising to `x = extClass` and `Y = unitRep H` leaves the class
`mk₀ (p • 𝟙 (unitRep H)) = mk₀ (unitMulByP H p) = mk₀ S.f`, i.e. the first map of the coefficient
sequence itself, and `ShortComplex.ShortExact.extClass_comp` says exactly that the extension class
composed with `mk₀ S.f` vanishes.
-/

namespace Work.SSGRoute.E7cC

open CategoryTheory

/-- **The `nsmul` of an `Ext`-group is composition with the `p`-fold multiple of the identity.**
For `x : Ext X Y n` and `p : ℕ` one has `p • x = x.comp (mk₀ (p • 𝟙 Y)) (add_zero n)`, where the
scalars on the left are the additive `nsmul` of the abelian group `Ext X Y n` and on the right the
additive `nsmul` of the endomorphism group `Y ⟶ Y`. -/
lemma nsmul_comp_mk₀_id (p : ℕ) {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} {n : ℕ} (x : Abelian.Ext X Y n) :
    p • x = x.comp (Abelian.Ext.mk₀ (p • 𝟙 Y)) (add_zero n) := by
  induction p with
  | zero => simp only [zero_nsmul, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  | succ k ih =>
      simp only [succ_nsmul, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add, ih,
        Abelian.Ext.comp_mk₀_id]

theorem coeffSES_nsmul_extClass (p : ℕ) [Fact p.Prime] (H : Type) [Group H] :
    p • (SSGRoute.Phi1.coeffSES_shortExact H p).extClass = 0 := by
  rw [nsmul_comp_mk₀_id]
  rw [← Nat.cast_smul_eq_nsmul SSGRoute.PTExt.Coeff p]
  have h : (↑p : SSGRoute.PTExt.Coeff) • 𝟙 ((SSGRoute.Phi1.coeffSES H p).X₁)
      = SSGRoute.Phi1.unitMulByP H p := (SSGRoute.extFp_unitMulByP_eq_smul p H).symm
  rw [h]
  exact ShortComplex.ShortExact.extClass_comp _

end Work.SSGRoute.E7cC
