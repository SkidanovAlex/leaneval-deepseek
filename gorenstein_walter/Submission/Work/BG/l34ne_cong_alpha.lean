import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.lemma24
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.CharBridge
import Submission.Work.BG.bset_orbit_struct

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem l34ne_cong_alpha {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hDC : Work.GW2.C16.Compat D C) (hS3 : Work.GW2.C16.Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : Work.BG.IsPmIrr χ)
    {ν ξ : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ Work.GW2.C16.bset C f χ)
    (hξ : ξ ∈ Work.GW2.C16.bset C f χ)
    (hνs : Work.BG.sconj C ν ≠ ν) (hξν : ξ ≠ ν) (hξνs : ξ ≠ Work.BG.sconj C ν)
    (hbset : Work.GW2.C16.bset C f χ = {ν, Work.BG.sconj C ν, ξ})
    {β α₁ α₂ : ClassFunction ↥(C.P.U) ℂ} (hβ : IsIrreducibleCharacter β)
    (hνβ : restrictU C ν = β) (hsνβ : restrictU C (Work.BG.sconj C ν) = β)
    (hξα : restrictU C ξ = α₁ + α₂) :
    ∀ u : ↥(C.P.U), Work.BG.AlgIntModTwo (χ (u : G)) (α₁ u + α₂ u) := by
  -- BG Lemma 2.4, congruence clause: `χ ≡ Σ_{ν ∈ 𝒮(χ)} ν (mod 2)` on `U`.
  intro u
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  have hcong := (Work.BG.lemma24 C) f hf χ hχ
  obtain ⟨_, _, hcong3⟩ := hcong
  have h1 : Work.BG.AlgIntModTwo (χ (u : G))
      (∑ᶠ ν' ∈ Work.GW2.C16.bset C f χ, ν' ⟨(u : G), C.P.U_le_H0 u.2⟩) :=
    hcong3 ⟨(u : G), C.P.U_le_H0 u.2⟩ u.2
  -- `𝒮(χ) = {ν, ν^s, ξ}` is a three-element set
  rw [hbset] at h1
  -- evaluate the two `finsum`s (each insertion is a new element)
  have hsumeval : (∑ᶠ ν' ∈ ({ν, Work.BG.sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)),
        ν' ⟨(u : G), C.P.U_le_H0 u.2⟩)
      = ν ⟨(u : G), C.P.U_le_H0 u.2⟩ + (Work.BG.sconj C ν ⟨(u : G), C.P.U_le_H0 u.2⟩
          + ξ ⟨(u : G), C.P.U_le_H0 u.2⟩) := by
    have hA : ν ∉ insert (Work.BG.sconj C ν) ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hνs h.symm, fun h => hξν h.symm⟩
    have hB : Work.BG.sconj C ν ∉ ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      simp only [Set.mem_singleton_iff]
      exact fun h => hξνs h.symm
    rw [show ({ν, Work.BG.sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ))
          = insert ν (insert (Work.BG.sconj C ν) ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)))
            from rfl,
      finsum_mem_insert _ hA (Set.Finite.insert _ (Set.finite_singleton _)),
      finsum_mem_insert _ hB (Set.finite_singleton _), finsum_mem_singleton]
  rw [hsumeval] at h1
  -- the individual values on `U`: `ν|_U = ν^s|_U = β`, `ξ|_U = α₁ + α₂`
  have hνval : ν ⟨(u : G), C.P.U_le_H0 u.2⟩ = β u := by
    rw [← Work.BG.restrictU_apply C ν u, hνβ]
  have hsνval : Work.BG.sconj C ν ⟨(u : G), C.P.U_le_H0 u.2⟩ = β u := by
    rw [← Work.BG.restrictU_apply C (Work.BG.sconj C ν) u, hsνβ]
  have hξval : ξ ⟨(u : G), C.P.U_le_H0 u.2⟩ = α₁ u + α₂ u := by
    rw [← Work.BG.restrictU_apply C ξ u, hξα, ClassFunction.add_apply]
  rw [hνval, hsνval, hξval] at h1
  -- `β u + (β u + (α₁ u + α₂ u)) ≡ α₁ u + α₂ u` since `β u` is an algebraic integer
  refine h1.trans ⟨β u, ?_, ?_⟩
  · exact OddOrder.Algebra.isIntegral_apply_of_mem_ZIrr (IsIrreducibleCharacter.mem_ZIrr hβ) u
  · ring

end Work.BG
