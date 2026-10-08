import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.hatInjCore
import Submission.Work.BG.hatInjCountAlt
import Submission.Work.BG.hatInjParity
import Submission.Work.BG.glaubCorrDistinct
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.CharBridge
import Submission.Work.BG.Defs
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.s02_bset_finite

/-!
# Area BG: helpers for `Work.BG.l34ExcNeFour`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G]

section HelperSec

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- `𝒮(χ) = bset C f χ` is stable under `s`-conjugation (coherence clause (ii)). -/
theorem l34ExcNeFour_sconj_mem_bset (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) {η : ClassFunction ↥C.P.H0 ℂ} (hη : η ∈ bset C f χ) :
    sconj C η ∈ bset C f χ := by
  refine ⟨IsIrreducibleCharacter.conjByH C.P C.s hη.1, ?_⟩
  have hk : η ∈ orbitKey C η := Or.inl (s02c_LamEquiv_refl C η)
  have hfix : f (sconj C η) = f η := ((hf.1 η hη.1) η hk η hk hη.1 hη.1).2.1
  rw [hfix]
  exact hη.2

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- In the standing configuration `Λν` is `s`-stable with `ν^s ≠ ν` and `|Λν| = 4`, so the
standing disjunction forces `D.n = 4`. -/
theorem l34ExcNeFour_n_eq_four (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {ν : ClassFunction ↥C.P.H0 ℂ}
    (hdisj : sconj C ν ∉ lamOrbit C ν ∨ (lamOrbit C ν).ncard = D.n)
    (hinv : sconj C '' lamOrbit C ν = lamOrbit C ν)
    (h4 : (lamOrbit C ν).ncard = 4) : D.n = 4 := by
  have hm : ν ∈ lamOrbit C ν := mem_lamOrbit_self C ν
  have hs : sconj C ν ∈ sconj C '' lamOrbit C ν := ⟨ν, hm, rfl⟩
  rw [hinv] at hs
  rcases hdisj with h | h
  · exact absurd hs h
  · rw [h4] at h
    exact h.symm

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- `𝒮(χ) = {ν, ν^s, ξ}` in the standing configuration. -/
theorem l34ExcNeFour_bset_eq (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hDC : Compat D C) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    {ν ξ : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ bset C f χ) (hne : sconj C ν ≠ ν)
    (hξ : ξ ∈ bset C f χ) (hξν : ξ ≠ ν) (hξνs : ξ ≠ sconj C ν) :
    bset C f χ = {ν, sconj C ν, ξ} := by
  have h2 : sconj C ν ∈ bset C f χ := l34ExcNeFour_sconj_mem_bset C f hf χ hν
  have hsub : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
    intro η hη
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hη
    rcases hη with rfl | rfl | rfl
    · exact hν
    · exact h2
    · exact hξ
  have hsν : sconj C ν ≠ ν := hne
  have h1 : ν ∉ ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hsν h.symm, fun h => hξν h.symm⟩
  have h2' : sconj C ν ∉ ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    simp only [Set.mem_singleton_iff]
    exact fun h => hξνs h.symm
  have hcard : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
    rw [show ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ))
        = insert ν (insert (sconj C ν) ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ))) from rfl,
      Set.ncard_insert_of_notMem h1 (Set.toFinite _),
      Set.ncard_insert_of_notMem h2' (Set.toFinite _), Set.ncard_singleton]
  have hle : (bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
  have hge : 3 ≤ (bset C f χ).ncard := by
    rw [← hcard]
    exact Set.ncard_le_ncard hsub hfin
  have hb : (bset C f χ).ncard ≤ ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard := by
    rw [hcard]; exact hle
  exact (Set.eq_of_subset_of_ncard_le hsub hb hfin).symm


end HelperSec

open OddOrder.RepresentationTheory Work.BG in
theorem l34ExcNeFour_glauberman_contra {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1)
    [Fintype ↥(fixedSubgroup σ)]
    [Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ)]
    {α₁ α₂ : ClassFunction U ℂ} (hα₁ : IsIrreducibleCharacter α₁)
    (hα₂ : IsIrreducibleCharacter α₂)
    (hinv₁ : ∀ u : U, α₁ (σ u) = α₁ u) (hinv₂ : ∀ u : U, α₂ (σ u) = α₂ u)
    (hne : α₁ ≠ α₂)
    (hcong : ∀ c : ↥(fixedSubgroup σ),
      AlgIntModTwo (α₁ (c : U) + α₂ (c : U)) 0) : False := by
  have hcong' : ∀ c : ↥(fixedSubgroup σ), AlgIntModTwo (α₁ (c : U)) (α₂ (c : U)) := by
    intro c
    obtain ⟨z, hz, hzc⟩ := hcong c
    exact ⟨z - α₂ (c : U), hz.sub (isIntegral_apply_of_isIrreducibleCharacter hα₂ (c : U)),
      by linear_combination hzc⟩
  refine hne (glauberman_injective hU σ hσ (hatInjCountAlt hU σ hσ)
    (fun β => hatInjParity hU σ hσ β) hα₁ hinv₁ hα₂ hinv₂ (fun c => hcong' c))


end Work.BG
