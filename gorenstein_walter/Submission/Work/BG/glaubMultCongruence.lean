import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory

/-!
# Area BG: the multiplicity-to-value congruence (Lemma 1.9, value form)

If `α` is an irreducible character of a finite group `U` and `β` is the **unique**
irreducible character of a subgroup `K ≤ U` occurring with **odd multiplicity** in the
restriction `α|_K`, then `α` and `β` agree modulo `2` on `K`:

`α(b) ≡ β(b) (mod 2)` for every `b : K`.

Equivalently: `α|_K − β` is twice a virtual character of `K`, and values of virtual
characters are algebraic integers.

This is the "value form" companion of `Work.GW2.C16.GlaubValueProp` (the Glauberman
correspondence `α ↦ β` of Bender–Glauberman 1981, Lemma 1.9), stated without any
reference to the 2-group acting on `U`: only the resulting uniqueness of the odd
constituent is used.
-/

/-- Values of virtual characters are algebraic integers: every irreducible character
value is a sum of roots of unity (`character_isIntegral`), and `IsIntegral ℤ` is closed
under the `ℤ`-span operations.  (Local copy of
`OddOrder.Algebra.isIntegral_apply_of_mem_ZIrr`, which lives in an unimported leaf of the
Feit–Thompson closure.) -/
theorem isIntegral_apply_of_mem_ZIrr_aux {G : Type*} [Group G] [Finite G]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (g : G) : IsIntegral ℤ (φ g) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨V, _, _, _, ρ, hchar⟩ :=
        IsIrreducibleCharacter.isCharacter (mem_irreducibleCharacters.mp hx)
      rw [show x g = ρ.character g from congrFun hchar g]
      exact character_isIntegral ρ g
  | zero => rw [ClassFunction.zero_apply]; exact isIntegral_zero
  | add a b _ _ ha hb => rw [ClassFunction.add_apply]; exact ha.add hb
  | smul n a _ ha =>
      rw [ClassFunction.zsmul_apply, zsmul_eq_mul]
      exact (isIntegral_algebraMap (x := n)).mul ha

/-- **Even Fourier coefficients give divisibility by `2` of the values.**  If a virtual
character `ψ ∈ ℤ[Irr G]` has all its Fourier coefficients `⟨ψ, θ⟩` (`θ ∈ Irr G`) even
integers, then at every `g` its value is twice an algebraic integer.

Indeed `mem_ZIrr_repr` writes `ψ = ∑_a c_a · a` with `c_a ∈ ℤ` and
`inner_eq_coeff_of_repr` identifies `c_a = ⟨ψ, a⟩`; `heven` makes each `c_a` even, so
`ψ = 2 · (∑ (c_a/2) · a)` with `∑ (c_a/2) · a ∈ ZIrr G`, and values of virtual
characters are algebraic integers. -/
theorem zirrEvenValue_aux {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {ψ : ClassFunction G ℂ} (hψ : ψ ∈ ZIrr G)
    (heven : ∀ θ : IrreducibleCharacter G,
      ∃ m : ℤ, ClassFunction.inner ψ (θ : ClassFunction G ℂ) = (2 * m : ℂ))
    (g : G) : ∃ z : ℂ, IsIntegral ℤ z ∧ ψ g = 2 * z := by
  classical
  obtain ⟨c, hsupp, hc⟩ := mem_ZIrr_repr hψ
  have hcoe : ∀ θ : IrreducibleCharacter G,
      ClassFunction.inner ψ (θ : ClassFunction G ℂ) =
        (c (θ : ClassFunction G ℂ) : ℂ) := by
    intro θ
    rw [hc]
    exact inner_eq_coeff_of_repr θ hsupp
  -- every coefficient is even
  have hev : ∀ a ∈ c.support, ∃ m : ℤ, c a = 2 * m := by
    intro a ha
    have hsup : a ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr ha)
    obtain ⟨m, hm⟩ := heven ⟨a, hsup⟩
    rw [hcoe ⟨a, hsup⟩] at hm
    exact ⟨m, by exact_mod_cast hm⟩
  -- half-coefficients
  set e : ClassFunction G ℂ → ℤ :=
    fun a => if ha : a ∈ c.support then Classical.choose (hev a ha) else 0 with hedef
  have hee : ∀ a (ha : a ∈ c.support), e a = Classical.choose (hev a ha) := by
    intro a ha
    rw [hedef]
    exact dite_eq_left ha
  have he : ∀ a (ha : a ∈ c.support), c a = 2 * e a := by
    intro a ha
    rw [hee a ha]
    exact Classical.choose_spec (hev a ha)
  refine ⟨∑ a ∈ c.support, (e a : ℂ) * (a g), ?_, ?_⟩
  · refine IsIntegral.sum (fun a => (e a : ℂ) * (a g)) (fun a ha => ?_)
    have hsup : a ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr ha)
    exact (isIntegral_algebraMap (x := e a)).mul
      (isIntegral_apply_of_mem_ZIrr_aux
        (IsIrreducibleCharacter.mem_ZIrr (mem_irreducibleCharacters.mp hsup)) g)
  · rw [hc, ClassFunction.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [ClassFunction.smul_apply, he a ha]
    push_cast
    ring

open OddOrder.RepresentationTheory Work.BG in
/-- **The multiplicity-to-value congruence (Bender–Glauberman 1981, Lemma 1.9, value
form).**  If `α` is an irreducible character of `U` and `β` is the unique irreducible
character of `K ≤ U` whose multiplicity in `α|_K` is odd, then `α(b) ≡ β(b) (mod 2)` for
every `b : K`.

All constituents of `α|_K` other than `β` have even multiplicity, so `α|_K − β` has only
even Fourier coefficients; `zirrEvenValue_aux` then exhibits its values as twice an
algebraic integer. -/
theorem glaubMultCongruence {U : Type} [Group U] [Finite U] [Fintype U] [Invertible (Nat.card U : ℂ)]
    (K : Subgroup U) [Fintype K] [Invertible (Nat.card K : ℂ)]
    (α : ClassFunction U ℂ) (hα : IsIrreducibleCharacter α) (β : IrreducibleCharacter K)
    (huniq : ∀ θ : IrreducibleCharacter K,
      (∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict K α) (θ : ClassFunction K ℂ) =
        (2 * k + 1 : ℂ)) ↔ θ = β) :
    ∀ b : K, AlgIntModTwo (α (b : U)) ((β : ClassFunction K ℂ) b) := by
  classical
  intro b
  have hAZ : ClassFunction.restrict K α ∈ ZIrr K :=
    ClassFunction.restrict_mem_ZIrr K (IsIrreducibleCharacter.mem_ZIrr hα)
  have hβZ : (β : ClassFunction K ℂ) ∈ ZIrr K := IrreducibleCharacter.mem_ZIrr β
  have hψZ : ClassFunction.restrict K α - (β : ClassFunction K ℂ) ∈ ZIrr K :=
    Submodule.sub_mem _ hAZ hβZ
  -- all Fourier coefficients of `α|_K − β` are even
  have heven : ∀ θ : IrreducibleCharacter K, ∃ m : ℤ,
      ClassFunction.inner (ClassFunction.restrict K α - (β : ClassFunction K ℂ))
        (θ : ClassFunction K ℂ) = (2 * m : ℂ) := by
    intro θ
    obtain ⟨m, hm⟩ := mem_ZIrr_inner_int θ hAZ
    have hsub : ClassFunction.inner
          (ClassFunction.restrict K α - (β : ClassFunction K ℂ)) (θ : ClassFunction K ℂ) =
        (m : ℂ) - (if (β : IrreducibleCharacter K) = θ then 1 else 0) := by
      rw [ClassFunction.inner_sub_left, irreducibleCharacter_inner_eq_ite, hm]
    rw [hsub]
    by_cases hθ : θ = β
    · obtain ⟨k, hk⟩ := (huniq θ).mpr hθ
      exact ⟨k, by rw [ite_eq_left hθ.symm, ← hm, hk]; ring⟩
    · have hnot : ¬ ∃ k : ℤ,
          ClassFunction.inner (ClassFunction.restrict K α) (θ : ClassFunction K ℂ) =
            (2 * k + 1 : ℂ) :=
        fun h => hθ ((huniq θ).mp h)
      have hmne : ¬ Odd m := by
        rintro ⟨k, hk⟩
        exact hnot ⟨k, by rw [hm, hk]; push_cast; ring⟩
      obtain ⟨d, hd⟩ := Int.not_odd_iff_even.mp hmne
      exact ⟨d, by rw [ite_eq_right (fun h => hθ h.symm), hd]; push_cast; ring⟩
  obtain ⟨z, hz, hval⟩ := zirrEvenValue_aux hψZ heven b
  refine ⟨z, hz, ?_⟩
  rw [← hval, ClassFunction.sub_apply, ClassFunction.restrict_apply]

end Work.BG
