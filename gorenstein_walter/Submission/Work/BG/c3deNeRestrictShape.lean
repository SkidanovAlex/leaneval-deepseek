import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.CharBridge
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

section Helpers

variable {G : Type} [Group G] [Finite G]

/-- `restrictU C` is the transport of the ordinary restriction `ClassFunction.restrict (Uin C)`
along the canonical identification `↥C.P.U ≃* ↥(Uin C)` (in the direction `U → Uin`). -/
private lemma c3de_restrictU_eq (C : Sec2Ctx G) (φ : ClassFunction ↥C.P.H0 ℂ) :
    restrictU C φ = ClassFunction.compHom
      (Subgroup.subgroupOfEquivOfLe C.P.U_le_H0).symm.toMonoidHom
      (ClassFunction.restrict (Uin C) φ) := by
  ext u
  rfl

private lemma c3de_restrictU_mul (C : Sec2Ctx G) (φ ψ : ClassFunction ↥C.P.H0 ℂ) :
    restrictU C (φ * ψ) = restrictU C φ * restrictU C ψ :=
  ClassFunction.compHom_mul (Subgroup.inclusion C.P.U_le_H0) φ ψ

/-- Every inflated linear character `λ_β` of `H₀` is trivial on `U`, hence restricts to the
trivial class function of `U`. -/
private lemma c3de_restrictU_lamCF (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) :
    restrictU C (lamCF C β) = trivialClassFunction ↥C.P.U := by
  ext u
  rw [restrictU_apply, trivialClassFunction_apply]
  have hq : quotMk C.P (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) = 1 :=
    (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) _).mpr u.2
  rw [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply, hq, map_one]
  rfl

/-- Multiplying by an element `λ_β` of `Λ` (a `Λ`-orbit step) does not change the restriction
to `U`, since `λ_β` is trivial on `U`. -/
private lemma c3de_restrictU_lamCF_mul (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    (ν : ClassFunction ↥C.P.H0 ℂ) :
    restrictU C (lamCF C β * ν) = restrictU C ν := by
  rw [c3de_restrictU_mul, c3de_restrictU_lamCF]
  ext u
  rw [ClassFunction.mul_apply, trivialClassFunction_apply, one_mul]

end Helpers

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- In the exceptional configuration `(D.n = 4, |Λν| = 4, third member ξ s-fixed with
`|Λξ| ≠ 4`) the restrictions to `U` have the shapes `ν|_U = (ν^s)|_U = β` (single
irreducible) and `ξ|_U = α₁ + α₂` (two distinct irreducibles of equal degree), and
`|Λξ| = 2`. -/
theorem c3deNeRestrictShape {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥(C.P.U)] [Invertible (Nat.card ↥(C.P.U) : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      D.n = 4 →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
        Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard ≠ 4 →
        (∃ β : ClassFunction ↥(C.P.U) ℂ, IsIrreducibleCharacter β ∧
            restrictU C ν = β ∧ restrictU C (Work.BG.sconj C ν) = β) ∧
        (∃ α₁ α₂ : ClassFunction ↥(C.P.U) ℂ, IsIrreducibleCharacter α₁ ∧
            IsIrreducibleCharacter α₂ ∧ α₁ ≠ α₂ ∧ α₁ 1 = α₂ 1 ∧
            restrictU C ξ = α₁ + α₂) ∧
        (Work.BG.lamOrbit C ξ).ncard = 2 := by
  intro hComp hS3 f hf χ hχ ν hν hνne hdisj hνcard hνimg hn4 ξ hξ hξneν hξneνs hξfix hξcard
  have hνirr : IsIrreducibleCharacter ν := hν.1
  have hξirr : IsIrreducibleCharacter ξ := hξ.1
  -- ### the third character `ξ`
  -- Remark 3.1 at `ξ`: since `|Λξ| ≠ 4 = D.n`, the second alternative (a sum of two distinct
  -- irreducibles of equal degree, with `2 |Λξ| = D.n`) must hold.
  obtain ⟨aξ, haξ, hξc⟩ := rem31Shape D C hComp hS3 ξ hξirr
  obtain ⟨bξ, hbξ, hbne, hbdeg, hresξ, hcardξ⟩ : ∃ b : ClassFunction ↥(Uin C) ℂ,
      IsIrreducibleCharacter b ∧ b ≠ aξ ∧ b 1 = aξ 1 ∧
        ClassFunction.restrict (Uin C) ξ = aξ + b ∧ 2 * (lamOrbit C ξ).ncard = D.n := by
    rcases hξc with ⟨-, hcard⟩ | h
    · exact absurd (hcard.trans hn4) hξcard
    · exact h
  have hξcard2 : (lamOrbit C ξ).ncard = 2 := by omega
  -- ### the character `ν`
  -- Remark 3.1 at `ν`: `|Λν| = 4 = D.n` forces the first alternative, i.e. `ν|_U` irreducible.
  obtain ⟨aν, haν, hνc⟩ := rem31Shape D C hComp hS3 ν hνirr
  have hresν : ClassFunction.restrict (Uin C) ν = aν := by
    rcases hνc with ⟨h, -⟩ | ⟨b, hb, hbne', hbdeg', hres, hcard⟩
    · exact h
    · rw [hνcard, hn4] at hcard
      omega
  -- `ν^s` lies in `Λν` (it is the image of `ν` under the map whose image is `Λν`), so it is a
  -- `Λ`-multiple of `ν`; the multiplier is trivial on `U`, whence equal restrictions.
  have hνs : restrictU C (sconj C ν) = restrictU C ν := by
    have hmem : sconj C ν ∈ lamOrbit C ν := by
      have h1 : sconj C ν ∈ sconj C '' lamOrbit C ν := ⟨ν, s02c_LamEquiv_refl C ν, rfl⟩
      rwa [hνimg] at h1
    obtain ⟨β, hβ⟩ := hmem
    rw [hβ, c3de_restrictU_lamCF_mul]
  -- the transport of the restriction statement for `ν` to `U = C.P.U`
  let e : ↥C.P.U ≃* ↥(Uin C) := (Subgroup.subgroupOfEquivOfLe C.P.U_le_H0).symm
  have hνirrU : IsIrreducibleCharacter (restrictU C ν) := by
    rw [c3de_restrictU_eq, hresν]
    exact IsIrreducibleCharacter.compHom_of_surjective e.surjective haν
  -- the two constituents of `ξ|_U`
  have hα₁ : IsIrreducibleCharacter (ClassFunction.compHom e.toMonoidHom aξ) :=
    IsIrreducibleCharacter.compHom_of_surjective e.surjective haξ
  have hα₂ : IsIrreducibleCharacter (ClassFunction.compHom e.toMonoidHom bξ) :=
    IsIrreducibleCharacter.compHom_of_surjective e.surjective hbξ
  have hαne : ClassFunction.compHom e.toMonoidHom aξ
      ≠ ClassFunction.compHom e.toMonoidHom bξ :=
    fun h => hbne (compHom_injective e.toMonoidHom e.surjective h).symm
  have hαdeg : (ClassFunction.compHom e.toMonoidHom aξ) 1
      = (ClassFunction.compHom e.toMonoidHom bξ) 1 := by
    simp only [ClassFunction.compHom_apply, map_one]
    exact hbdeg.symm
  have hξres : restrictU C ξ = ClassFunction.compHom e.toMonoidHom aξ
      + ClassFunction.compHom e.toMonoidHom bξ := by
    rw [c3de_restrictU_eq, hresξ, ClassFunction.compHom_add]
  exact ⟨⟨restrictU C ν, hνirrU, rfl, hνs⟩,
    ⟨ClassFunction.compHom e.toMonoidHom aξ, ClassFunction.compHom e.toMonoidHom bξ,
      hα₁, hα₂, hαne, hαdeg, hξres⟩, hξcard2⟩

end Work.BG
