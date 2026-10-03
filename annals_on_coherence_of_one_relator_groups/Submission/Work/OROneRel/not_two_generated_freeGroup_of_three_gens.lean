import Mathlib

/-!
# A free group of rank at least three is not 2-generated

The requested lemma: if `a b c : ι` are three *distinct* elements, then the free group
`FreeGroup ι` is not generated (as a subgroup) by two elements.

The argument is the standard rank obstruction, phrased so that no rank theory of free groups is
needed.  Suppose `FreeGroup ι = closure {g₁, g₂}`.  For every triple
`p = (p₀, p₁, p₂) ∈ (ZMod 2)³` let `χ p : FreeGroup ι →* Multiplicative (ZMod 2)` be the
homomorphism sending the three generators `a`, `b`, `c` to `p₀`, `p₁`, `p₂` (additively) and all
other generators to `1`.  Any two such homomorphisms that agree on the two generators `g₁`, `g₂`
agree on `closure {g₁, g₂} = ⊤`, hence are equal; so the evaluation map
`p ↦ (χ p g₁, χ p g₂)` is injective.  But its domain has `2³ = 8` elements and its codomain
`Multiplicative (ZMod 2) × Multiplicative (ZMod 2)` has `2² = 4`, a contradiction.
-/

namespace Work.OROneRel

universe u

theorem not_two_generated_freeGroup_of_three_gens {ι : Type u} (a b c : ι) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ∃ g₁ g₂ : FreeGroup ι,
      (⊤ : Subgroup (FreeGroup ι)) = Subgroup.closure ({g₁, g₂} : Set (FreeGroup ι)) := by
  classical
  rintro ⟨g₁, g₂, hgen⟩
  -- The family of homomorphisms `χ p`, indexed by the `8 = 2 ^ 3` triples `p`.
  let χ : (ZMod 2 × ZMod 2 × ZMod 2) → (FreeGroup ι →* Multiplicative (ZMod 2)) :=
    fun p => FreeGroup.lift fun i =>
      if i = a then Multiplicative.ofAdd p.1
      else if i = b then Multiplicative.ofAdd p.2.1
      else if i = c then Multiplicative.ofAdd p.2.2
      else 1
  have hχa : ∀ p, χ p (FreeGroup.of a) = Multiplicative.ofAdd p.1 := by
    intro p; simp [χ]
  have hχb : ∀ p, χ p (FreeGroup.of b) = Multiplicative.ofAdd p.2.1 := by
    intro p; simp [χ, Ne.symm hab]
  have hχc : ∀ p, χ p (FreeGroup.of c) = Multiplicative.ofAdd p.2.2 := by
    intro p; simp [χ, Ne.symm hac, Ne.symm hbc]
  -- Two homomorphisms agreeing on the two generators `g₁`, `g₂` are equal.
  have key : ∀ χ₁ χ₂ : FreeGroup ι →* Multiplicative (ZMod 2),
      χ₁ g₁ = χ₂ g₁ → χ₁ g₂ = χ₂ g₂ → χ₁ = χ₂ := by
    intro χ₁ χ₂ h₁ h₂
    have hle : (⊤ : Subgroup (FreeGroup ι)) ≤ MonoidHom.eqLocus χ₁ χ₂ := by
      rw [hgen]
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact h₁
      · exact h₂
    exact MonoidHom.ext (fun z => hle (Subgroup.mem_top z))
  -- Evaluation of the pair `(χ p g₁, χ p g₂)` is injective, so `8 ≤ 4`.
  let E : (ZMod 2 × ZMod 2 × ZMod 2) → Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    fun p => (χ p g₁, χ p g₂)
  have hE : Function.Injective E := by
    intro p q hpq
    have h1 : χ p g₁ = χ q g₁ := congrArg Prod.fst hpq
    have h2 : χ p g₂ = χ q g₂ := congrArg Prod.snd hpq
    have hχ : χ p = χ q := key (χ p) (χ q) h1 h2
    have hp0 : p.1 = q.1 := by
      have h := congrArg (fun f : FreeGroup ι →* Multiplicative (ZMod 2) => f (FreeGroup.of a)) hχ
      rw [hχa p, hχa q] at h
      exact Multiplicative.ofAdd.injective h
    have hp1 : p.2.1 = q.2.1 := by
      have h := congrArg (fun f : FreeGroup ι →* Multiplicative (ZMod 2) => f (FreeGroup.of b)) hχ
      rw [hχb p, hχb q] at h
      exact Multiplicative.ofAdd.injective h
    have hp2 : p.2.2 = q.2.2 := by
      have h := congrArg (fun f : FreeGroup ι →* Multiplicative (ZMod 2) => f (FreeGroup.of c)) hχ
      rw [hχc p, hχc q] at h
      exact Multiplicative.ofAdd.injective h
    exact Prod.ext hp0 (Prod.ext hp1 hp2)
  have hcard := Fintype.card_le_of_injective E hE
  simp only [Fintype.card_prod, Fintype.card_multiplicative, ZMod.card] at hcard
  norm_num at hcard

end Work.OROneRel
