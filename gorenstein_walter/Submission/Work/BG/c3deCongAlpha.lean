import Mathlib
import Submission.Work.BG.lemma24
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- In the exceptional configuration with `𝒮(χ) = {ν, ν^s, ξ}` and restriction shapes
`ν|_U = (ν^s)|_U = β`, `ξ|_U = α₁ + α₂`, Lemma 2.4 gives `χ ≡ α₁ + α₂ (mod 2)` on `U`. -/
theorem c3deCongAlpha {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
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
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  intro u
  -- view `u` as an element of `H₀`; Lemma 2.4 applies there
  set u' : ↥C.P.H0 := ⟨(u : G), C.P.U_le_H0 u.2⟩ with hu'def
  have hUu := (lemma24 C f hf χ hχ).2.2 u' (by simpa [hu'def] using u.2)
  -- values of `β` on `U` are algebraic integers
  have hint : IsIntegral ℤ (β u) :=
    OddOrder.Algebra.isIntegral_apply_of_mem_ZIrr
      (G := ↥C.P.U) (IsIrreducibleCharacter.mem_ZIrr hβ) u
  -- the three restricted characters at `u`
  have hν_val : ν u' = β u := by
    rw [hu'def]; rw [← restrictU_apply C ν u, hνβ]
  have hsν_val : Work.BG.sconj C ν u' = β u := by
    rw [hu'def]; rw [← restrictU_apply C (Work.BG.sconj C ν) u, hsνβ]
  have hξ_val : ξ u' = α₁ u + α₂ u := by
    rw [hu'def]; rw [← restrictU_apply C ξ u, hξα, ClassFunction.add_apply]
  have hmain : Work.BG.AlgIntModTwo (χ (u : G))
      (∑ᶠ η ∈ Work.GW2.C16.bset C f χ, η u') := by
    simpa [hu'def] using hUu
  -- the sum over `𝒮(χ) = {ν, ν^s, ξ}` is `β(u) + β(u) + (α₁(u) + α₂(u))`
  have hstep : Work.BG.AlgIntModTwo (∑ᶠ η ∈ Work.GW2.C16.bset C f χ, η u')
      (α₁ u + α₂ u) := by
    have hnot1 : ν ∉ ({Work.BG.sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hνs h.symm, fun h => hξν h.symm⟩
    have hnot2 : Work.BG.sconj C ν ∉ ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      simp only [Set.mem_singleton_iff]
      exact fun h => hξνs h.symm
    rw [hbset,
      finsum_mem_insert (f := fun η => η u') (a := ν)
        (s := ({Work.BG.sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ))) hnot1
        (Set.toFinite _),
      finsum_mem_insert (f := fun η => η u') (a := Work.BG.sconj C ν)
        (s := ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ))) hnot2 (Set.toFinite _),
      finsum_mem_singleton, hν_val, hsν_val, hξ_val]
    exact ⟨β u, hint, by ring⟩
  exact hmain.trans hstep

end Work.BG
