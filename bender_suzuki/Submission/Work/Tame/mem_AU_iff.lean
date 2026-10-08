import Mathlib
import Submission.Work.Tame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The support set `AU` of Feit–Thompson's Lemma 9.1

`AU Lhat n Hs` is the union `⋃_{i=0}^{n} ⋃_{L ∈ 𝔏_i} 𝔄_L` of p. 805: for `i = 0` (i.e.
`𝔎_0 = 1`, `𝔏_0 = {L ∈ L̂ | C(L) ⊆ 𝔏}`, `𝔄_L = {L}`) this contributes the set `L0set Lhat` of
Definition 9.1; for a supporting subgroup `𝔎_i` it contributes `L{𝔎_i ∩ C(L)}` for
`L ∈ 𝔏_i = {L ∈ 𝔇 | C(L) ⊆ 𝔑_i}`.
-/

namespace Work.Tame

theorem mem_AU_iff {X : Type*} [Group X] {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    {x : X} :
    x ∈ AU Lhat n Hs ↔ x ∈ L0set Lhat ∨
      ∃ i : Fin n, ∃ L : X, L ∈ Lset Lhat (Hs i) ∧
        ∃ H : X, H ∈ Hs i ∧ L * H = H * L ∧ x = L * H := by
  constructor
  · intro hx
    rw [AU, Set.mem_iUnion] at hx
    obtain ⟨j, hx⟩ := hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨L, hL, hx⟩ := hx
    cases j with
    | none =>
        simp only [LofIdx, ALofIdx, Set.mem_singleton_iff] at hL hx
        exact Or.inl (hx ▸ hL)
    | some i =>
        simp only [LofIdx, ALofIdx] at hL
        exact Or.inr ⟨i, L, hL, hx⟩
  · rintro (hx | ⟨i, L, hL, H, hH, hcomm, rfl⟩)
    · exact Set.mem_iUnion.mpr ⟨none, Set.mem_iUnion₂.mpr ⟨x, by simpa only [LofIdx] using hx,
        by simp [ALofIdx]⟩⟩
    · exact Set.mem_iUnion.mpr ⟨some i, Set.mem_iUnion₂.mpr ⟨L, by simpa only [LofIdx] using hL,
        ⟨H, hH, hcomm, rfl⟩⟩⟩

end Work.Tame
