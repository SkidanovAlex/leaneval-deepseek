import Mathlib

namespace Commons.GroupTheory.GroupAction

theorem sum_smul_card_smul {G X A : Type*} [Group G] [Fintype G] [MulAction G X] [DecidableEq X]
    [AddCommMonoid A] (f : X → A) (x : X) (S : Finset X) (hmem : ∀ σ : G, σ • x ∈ S)
    (hsurj : ∀ y ∈ S, ∃ σ : G, σ • x = y) :
    S.card • (∑ σ : G, f (σ • x)) = Fintype.card G • ∑ y ∈ S, f y := by
  classical
  -- Every element of `S` is the image of `x` under the orbit map `σ ↦ σ • x`.
  have hmaps : Set.MapsTo (fun σ : G => σ • x) (↑(Finset.univ : Finset G)) (↑S) :=
    fun σ _ => hmem σ
  -- All fibres of the orbit map over `S` have the same cardinality (that of the fibre over `x`),
  -- because they are translates of one another.
  have hcard : ∀ y ∈ S,
      (Finset.univ.filter (fun σ : G => σ • x = y)).card =
        (Finset.univ.filter (fun σ : G => σ • x = x)).card := by
    intro y hy
    obtain ⟨τ, hτ⟩ := hsurj y hy
    refine Finset.card_nbij' (fun σ : G => τ⁻¹ * σ) (fun ρ : G => τ * ρ) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      rw [mul_smul, hσ, ← hτ, inv_smul_smul]
    · intro ρ hρ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
      rw [mul_smul, hρ, hτ]
    · intro σ _
      group
    · intro ρ _
      group
  -- Rewriting the sum over `G` as a sum over the fibres above `S`.
  have hsum : (∑ σ : G, f (σ • x)) =
      (Finset.univ.filter (fun σ : G => σ • x = x)).card • (∑ y ∈ S, f y) := by
    rw [← Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset G)) (t := S)
          (g := fun σ : G => σ • x) (fun σ _ => hmem σ) f]
    trans ∑ y ∈ S, (Finset.univ.filter (fun σ : G => σ • x = x)).card • f y
    · apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_const, hcard y hy]
    · rw [Finset.smul_sum]
  -- Counting `G` by the fibres above `S`.
  have hcardG : Fintype.card G =
      S.card * (Finset.univ.filter (fun σ : G => σ • x = x)).card := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmaps]
    exact Finset.sum_const_nat (fun y hy => hcard y hy)
  rw [hsum, hcardG, mul_nsmul']

end Commons.GroupTheory.GroupAction
