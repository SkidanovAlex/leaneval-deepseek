import Mathlib
import Submission.Work.Tame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The "conjugate into the support" condition of Feit–Thompson's Lemma 9.1

Feit–Thompson state Lemma 9.1 for `A ∈ 𝔄_L` and for elements `X` which are *not* conjugate to
an element of any `𝔄_L`; `inConjAU` is that condition, and this file identifies it with
conjugacy to an element of the support set `AU`.
-/

namespace Work.Tame

theorem inConjAU_iff {X : Type*} [Group X] {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    {x : X} (h : IsTamelyImbedded Lhat n Hs) :
    inConjAU Lhat n Hs x ↔ ∃ a ∈ AU Lhat n Hs, IsConj x a := by
  constructor
  · rintro ⟨j, L, hL, A, hA, hc⟩
    cases j with
    | none =>
        exact ⟨A, Set.mem_iUnion.mpr ⟨none,
          Set.mem_iUnion₂.mpr ⟨(L : X), by simpa only [LofIdx] using hL, hA⟩⟩, hc⟩
    | some i =>
        exact ⟨A, Set.mem_iUnion.mpr ⟨some i,
          Set.mem_iUnion₂.mpr ⟨(L : X), by simpa only [LofIdx] using hL, hA⟩⟩, hc⟩
  · rintro ⟨a, ha, hc⟩
    rw [AU, Set.mem_iUnion] at ha
    obtain ⟨j, ha⟩ := ha
    rw [Set.mem_iUnion₂] at ha
    obtain ⟨L, hL, hA⟩ := ha
    cases j with
    | none =>
        simp only [LofIdx] at hL
        exact ⟨none, ⟨L, h.sub_norm hL.1⟩, by simpa only [LofIdx] using hL, a, hA, hc⟩
    | some i =>
        simp only [LofIdx] at hL
        exact ⟨some i, ⟨L, h.sub_norm hL.1.1⟩, by simpa only [LofIdx] using hL, a, hA, hc⟩

end Work.Tame
