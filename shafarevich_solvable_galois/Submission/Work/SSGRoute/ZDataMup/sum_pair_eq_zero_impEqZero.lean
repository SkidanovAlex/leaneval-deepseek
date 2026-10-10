import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataMup.LocalData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open _root_.SSGRoute

/-- **The local pairing vanishes on the zero cocycle in the second variable.**  This is
`IsLocalTateSystem.additive_right` on `b = b' = 0`, i.e. the collapse of `x = x + x` in the additive
group `ZMod p`. -/
theorem pair_zero_right_of_isLocalTateSystem {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p}
    (hpair : IsLocalTateSystem p k Ω K pair) {H : Subgroup (Ω ≃ₐ[k] Ω)}
    (hH : ∃ A : ValuationSubring Ω, IsFinPlace k A ∧ H = decomp k A ⊓ K.fixingSubgroup)
    {a : (Ω ≃ₐ[k] Ω) → ZMod p}
    (ha : IsCocycleOn (res k K) H a ∧ IsLocConstOn H a) :
    pair H a 0 = 0 := by
  have h0 : IsCocycleOn (res k K) H (0 : (Ω ≃ₐ[k] Ω) → ZMod p) ∧
      IsLocConstOn H (0 : (Ω ≃ₐ[k] Ω) → ZMod p) :=
    ⟨isCocycleOn_zero H, isLocConstOn_zero H⟩
  have h := hpair.additive_right H hH a 0 0 ha h0 h0
  have h2 : pair H a 0 = pair H a 0 + pair H a 0 := by
    simpa only [Pi.zero_apply, add_zero] using h
  have h3 : pair H a 0 + pair H a 0 = pair H a 0 + 0 := by
    rw [add_zero]; exact h2.symm
  exact add_left_cancel h3

/-- **Non-degeneracy of the sum pairing on the local-data space.**  If a local datum `a` pairs
trivially against *every* datum `b` (the sum over the places of `T` of the local pairings vanishes),
then every local component `a A` vanishes on the level-`K` local group
`decomp k A ⊓ K.fixingSubgroup`.  This is the product form of `pair_nondegenerate_of_perfect`: test
against the delta datum which equals `b` at the place `A` and `0` elsewhere. -/
theorem sum_pair_eq_zero_impEqZero {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p}
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    {T : Finset (ValuationSubring Ω)} (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    {a : {A : ValuationSubring Ω // A ∈ T} → (Ω ≃ₐ[k] Ω) → ZMod p}
    (ha : a ∈ Work.SSGRoute.ZDataMup.localDataSpace (p := p) K T)
    (h : ∀ b ∈ Work.SSGRoute.ZDataMup.localDataSpace (p := p) K T,
      ∑ A : {A : ValuationSubring Ω // A ∈ T},
        pair (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) (a A) (b A) = 0) :
    ∀ A : {A : ValuationSubring Ω // A ∈ T}, ∀ g : Ω ≃ₐ[k] Ω,
      g ∈ SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup → a A g = 0 := by
  classical
  intro A g hg
  refine pair_nondegenerate_of_perfect (p := p) hpair ⟨A.1, hTfin A.1 A.2, rfl⟩ (ha A) ?_ g hg
  intro b hbc hblc
  -- the delta datum: `b` at the place `A`, `0` at all other places
  let F : {A' : ValuationSubring Ω // A' ∈ T} → (Ω ≃ₐ[k] Ω) → ZMod p :=
    fun A' => if A' = A then b else 0
  have hFA : F A = b := by simp [F]
  have hbFull : F ∈ localDataSpace (p := p) K T := by
    intro A'
    by_cases hA' : A' = A
    · subst hA'
      rw [hFA]
      exact ⟨hbc, hblc⟩
    · rw [show F A' = 0 by simp [F, hA']]
      exact ⟨isCocycleOn_zero _, isLocConstOn_zero _⟩
  have hsum := h F hbFull
  have hcollapse : (∑ A' : {A' : ValuationSubring Ω // A' ∈ T},
      pair (decomp k A'.1 ⊓ K.fixingSubgroup) (a A') (F A'))
      = pair (decomp k A.1 ⊓ K.fixingSubgroup) (a A) b := by
    rw [Finset.sum_eq_single A]
    · rw [hFA]
    · intro A' _ hA'ne
      rw [show F A' = 0 by simp [F, hA'ne]]
      exact pair_zero_right_of_isLocalTateSystem (p := p) hpair
        ⟨A'.1, hTfin A'.1 A'.2, rfl⟩ (ha A')
    · intro hnot
      exact absurd (Finset.mem_univ A) hnot
  rw [hcollapse] at hsum
  exact hsum

end Work.SSGRoute.ZDataMup
