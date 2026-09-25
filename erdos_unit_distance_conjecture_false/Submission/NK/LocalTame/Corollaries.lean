/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.LocalTame.Corollaries`: the local correspondence, summarised

This file collects the local input of the Neukirch–Uchida theorem in one statement: an isomorphism
`Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)` of the absolute Galois groups of two `p`-adic fields forces

* the residue characteristics to be equal (`p = p₂`),
* the residue field cardinalities to be equal (`q = q₂`, whence also the residue *degrees*),
* the "ζ_p ∈ κ" indicators to be equal (`δ = ε`),
* the absolute degrees over `ℚ_p` to be equal (`d = e`), and
* the Frobenius lifts to correspond under `Φ`.

The first two are proved here from `NK.LocalTame.TameData`; the indicators and the absolute
degrees are the sibling chapter `NK.LocalAnabelian` (`PadicGaloisInputs`, Ivanov's detection of
the residue characteristic and local reciprocity for the abelianised rank), and are quoted rather
than re-derived.  The Frobenius correspondence is `NK.LocalTame.isFrobeniusFor_map_iff`.

For an isomorphism `Φ` of absolute Galois groups of *number* fields, this is applied at
corresponding places in `NK.LocalTame.Global`.
-/
import Submission.NK.LocalTame.Main

open scoped Classical
open NK.LocalAnabelian

namespace NK.LocalTame

universe u

noncomputable section

variable {κ κ₂ K' L' : Type*} [Field κ] [Field κ₂] [Field K'] [Field L']
  [Algebra κ K'] [Algebra κ₂ L'] [IsSepClosure κ K'] [IsSepClosure κ₂ L']

/-- **The local correspondence of the Neukirch–Uchida theorem.**  An isomorphism of absolute
Galois groups of `p`-adic fields matches the residue characteristics, the residue field
cardinalities, the `ζ_p`-indicators and the absolute degrees, and maps the Frobenius lifts onto the
Frobenius lifts.

All the notions used are invariants of the *abstract* group (`NK.LocalTame.Basic`), so `Φ` is an
arbitrary group isomorphism: no continuity is needed or assumed. -/
theorem local_correspondence {p q p₂ q₂ d e δ ε : ℕ} (h : TameData p q κ K')
    (h₂ : TameData p₂ q₂ κ₂ L') (hP : PadicGaloisInputs p d δ κ K')
    (hP₂ : PadicGaloisInputs p₂ e ε κ₂ L') (hZ : Zl2ResidueChar p κ K')
    (hZ₂ : Zl2ResidueChar p₂ κ₂ L') (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) :
    p = p₂ ∧ q = q₂ ∧ d = e ∧ δ = ε ∧
      ∀ τ : Gal(K'/κ), IsFrobeniusFor p q τ ↔ IsFrobeniusFor p₂ q₂ (Φ τ) := by
  have hpq : p = p₂ := residueChar_eq_of_zl2 hZ hZ₂ Φ
  subst hpq
  refine ⟨rfl, residueCard_eq_of_tameData h h₂ rfl Φ, ?_, ?_, ?_⟩
  · exact degree_eq_of_padicGaloisInputs hP hP₂ Φ
  · exact delta_eq_of_padicGaloisInputs hP hP₂ Φ
  · intro τ
    exact isFrobeniusFor_map_iff_of_eq h h₂ rfl (residueCard_eq_of_tameData h h₂ rfl Φ) Φ τ

/-- The residue field cardinalities coincide, in the form of the concrete quantity
`#(𝓞 K ⧸ 𝔭)` of the two local fields. -/
theorem local_residueCard_eq {p q p₂ q₂ : ℕ} (h : TameData p q κ K')
    (h₂ : TameData p₂ q₂ κ₂ L') (hZ : Zl2ResidueChar p κ K') (hZ₂ : Zl2ResidueChar p₂ κ₂ L')
    (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) : q = q₂ :=
  residueCard_eq_of_tameData h h₂ (residueChar_eq_of_zl2 hZ hZ₂ Φ) Φ

/-- The residue *degrees* coincide: if `q = p^f` and `q₂ = p^g`, then `f = g`. -/
theorem local_residueDeg_eq {p q p₂ q₂ : ℕ} (h : TameData p q κ K') (h₂ : TameData p₂ q₂ κ₂ L')
    (hZ : Zl2ResidueChar p κ K') (hZ₂ : Zl2ResidueChar p₂ κ₂ L')
    (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) {f g : ℕ} (hf : q = p ^ f) (hg : q₂ = p ^ g) : f = g :=
  residueDeg_eq_of_tameData h h₂ (residueChar_eq_of_zl2 hZ hZ₂ Φ) Φ f g hf hg

end

end NK.LocalTame
