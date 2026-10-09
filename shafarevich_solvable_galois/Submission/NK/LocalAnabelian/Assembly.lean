/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Part (D): the local invariants are invariants of the absolute Galois group

Assembling (A) and (B): if `κ` and `λ` are `p`-adic fields whose absolute Galois groups
are isomorphic (as abstract groups — a fortiori as profinite groups), then

* the residue characteristics coincide,
* the indicator `δ = 1 ⟺ ζ_p ∈ κ` coincides (it is the `p`-torsion of the
  abelianisation), and
* the absolute degrees `[κ : ℚ_p]`, `[λ : ℚ_q]` coincide.

The residue characteristic is read off from the `ℓ`-tower rank predicate (part (B),
`ResidueCharDetectedBy`); the degree is read off from the abelianised `p`-Frattini rank
`HasAbelianFrattiniRank p (d+1+δ)`, since `Gal(κ̄/κ)^{ab} ≅ Ẑ × \hat{μ_κ} × ℤ_p^d`.  Note
that both invariants are invariant under an *arbitrary* group isomorphism, so no
continuity is required.

This is the local input used in CoNF XII (12.1.9)/(12.1.10) to see that an isomorphism
of absolute Galois groups of local fields preserves the residue characteristic and the
absolute degree of the primes.
-/
import Submission.NK.LocalAnabelian.PadicField.FrattiniRank
import Submission.NK.LocalAnabelian.ResidueChar.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.LocalAnabelian

noncomputable section

/-- **Part (D).**  Isomorphic absolute Galois groups of `p`-adic fields have the same
residue characteristic. -/
theorem residueChar_eq_of_padicGaloisInputs {κ κ₂ K' L' : Type*} [Field κ] [Field κ₂] [Field K']
    [Field L'] [Algebra κ K'] [Algebra κ₂ L'] [IsSepClosure κ K'] [IsSepClosure κ₂ L']
    {p d δ q e ε : ℕ} (h : PadicGaloisInputs p d δ κ K')
    (h' : PadicGaloisInputs q e ε κ₂ L') (ϕ : Gal(K'/κ) ≃* Gal(L'/κ₂)) : p = q :=
  residueCharDetectedBy_unique ϕ h.hp h'.hp h.residueChar_detected h'.residueChar_detected

/-- **Part (D).**  The indicator `δ = 1 ⟺ ζ_p ∈ κ` is an invariant of the absolute Galois
group: it is exactly the `p`-torsion of the abelianisation. -/
theorem delta_eq_of_padicGaloisInputs {κ κ₂ K' L' : Type*} [Field κ] [Field κ₂] [Field K']
    [Field L'] [Algebra κ K'] [Algebra κ₂ L'] [IsSepClosure κ K'] [IsSepClosure κ₂ L']
    {p d δ q e ε : ℕ} (h : PadicGaloisInputs p d δ κ K')
    (h' : PadicGaloisInputs q e ε κ₂ L') (ϕ : Gal(K'/κ) ≃* Gal(L'/κ₂)) : δ = ε := by
  have hpq : p = q := residueChar_eq_of_padicGaloisInputs h h' ϕ
  subst hpq
  have htor : HasPTorsionAbelianization p (Gal(K'/κ)) ↔
      HasPTorsionAbelianization p (Gal(L'/κ₂)) :=
    hasPTorsionAbelianization_congr_iff ϕ p
  have hδε1 : δ = 1 ↔ ε = 1 := by rw [h.p_torsion_iff, h'.p_torsion_iff]; exact htor
  have hδ1 : δ ≤ 1 := h.hδ
  have hε1 : ε ≤ 1 := h'.hδ
  have hd : δ = 0 ∨ δ = 1 := by omega
  have he : ε = 0 ∨ ε = 1 := by omega
  rcases hd with hd | hd <;> rcases he with he | he
  · omega
  · rw [hd] at hδε1; exact absurd (hδε1.mpr he) (by omega)
  · rw [he] at hδε1; exact absurd (hδε1.mp hd) (by omega)
  · omega

/-- **Part (D).**  Isomorphic absolute Galois groups of `p`-adic fields have the same
absolute degree over `ℚ_p`.  The invariant used is the abelianised pro-`p` rank
`ℤ_p^d × (ℤ/p)^δ`; the `δ` is then removed using `delta_eq_of_padicGaloisInputs`. -/
theorem degree_eq_of_padicGaloisInputs {κ κ₂ K' L' : Type*} [Field κ] [Field κ₂] [Field K']
    [Field L'] [Algebra κ K'] [Algebra κ₂ L'] [IsSepClosure κ K'] [IsSepClosure κ₂ L']
    {p d δ q e ε : ℕ} (h : PadicGaloisInputs p d δ κ K')
    (h' : PadicGaloisInputs q e ε κ₂ L') (ϕ : Gal(K'/κ) ≃* Gal(L'/κ₂)) : d = e := by
  have hδε : δ = ε := delta_eq_of_padicGaloisInputs h h' ϕ
  have hpq : p = q := residueChar_eq_of_padicGaloisInputs h h' ϕ
  subst hpq
  have h1 : HasAbelianFrattiniRank p (d + 1 + δ) (Gal(L'/κ₂)) :=
    hasAbelianFrattiniRank_congr ϕ h.abelian_rank
  have h2 : d + 1 + δ = e + 1 + ε :=
    eq_of_hasAbelianFrattiniRank h.hp h1 h'.abelian_rank
  omega

/-- **Part (D), combined.**  An isomorphism of absolute Galois groups of `p`-adic
fields preserves the residue characteristic, the `δ`-indicator and the absolute degree. -/
theorem residueChar_and_degree_eq_of_padicGaloisInputs {κ κ₂ K' L' : Type*} [Field κ] [Field κ₂]
    [Field K'] [Field L'] [Algebra κ K'] [Algebra κ₂ L'] [IsSepClosure κ K']
    [IsSepClosure κ₂ L'] {p d δ q e ε : ℕ} (h : PadicGaloisInputs p d δ κ K')
    (h' : PadicGaloisInputs q e ε κ₂ L') (ϕ : Gal(K'/κ) ≃* Gal(L'/κ₂)) :
    p = q ∧ δ = ε ∧ d = e :=
  ⟨residueChar_eq_of_padicGaloisInputs h h' ϕ, delta_eq_of_padicGaloisInputs h h' ϕ,
    degree_eq_of_padicGaloisInputs h h' ϕ⟩

/-- The abelianised Frattini rank `d + 1 + δ` is likewise an invariant, so an isomorphism
of absolute Galois groups also matches `[κ : ℚ_p] + 1 + δ`. -/
theorem frattiniRank_eq_of_padicGaloisInputs {κ κ₂ K' L' : Type*} [Field κ] [Field κ₂] [Field K']
    [Field L'] [Algebra κ K'] [Algebra κ₂ L'] [IsSepClosure κ K'] [IsSepClosure κ₂ L']
    {p d δ q e ε : ℕ} (h : PadicGaloisInputs p d δ κ K')
    (h' : PadicGaloisInputs q e ε κ₂ L') (ϕ : Gal(K'/κ) ≃* Gal(L'/κ₂)) :
    d + 1 + δ = e + 1 + ε := by
  have hpq : p = q := residueChar_eq_of_padicGaloisInputs h h' ϕ
  subst hpq
  have h1 : HasAbelianFrattiniRank p (d + 1 + δ) (Gal(L'/κ₂)) :=
    hasAbelianFrattiniRank_congr ϕ h.abelian_rank
  exact eq_of_hasAbelianFrattiniRank h.hp h1 h'.abelian_rank

end

end NK.LocalAnabelian
