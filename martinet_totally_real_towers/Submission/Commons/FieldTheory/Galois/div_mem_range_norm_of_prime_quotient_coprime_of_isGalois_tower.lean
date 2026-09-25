import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Norm.Basic
import Submission.Commons.GroupTheory.pow_eq_one_of_coprime_exp

set_option linter.style.haveILetI false

/-!
# The coprime-action mechanism for the norm kernel condition

This file proves `Commons.FieldTheory.Galois.div_mem_range_norm_of_prime_quotient_coprime_of_isGalois_tower`.

The mathematical content is a group-theoretic one: if a finite group `A` acts by automorphisms on
a *cyclic* group `Q` of prime order `q`, and `gcd (#A, q-1) = 1`, then the action is trivial
(because `#Aut(Q) = q - 1`, Mathlib's `IsCyclic.card_mulAut`).

We apply this to the tower `B ⊆ B₁ ⊆ E` with `B₁/B` finite Galois and `E/B` finite Galois: the
group `A = Gal(B₁/B)` acts on `B₁ˣ`, the subgroup `N = N_{E/B₁}(Eˣ)` is `A`-stable (because every
`σ ∈ Gal(B₁/B)` lifts to `Gal(E/B)`, along which the norm is equivariant), and hence `A` acts on
the quotient `Q = B₁ˣ ⧸ N`.  If `Q` has prime order `q` with `gcd (#A, q-1) = 1` the action is
trivial, which is precisely `σ x / x ∈ N`.
-/

namespace Commons.FieldTheory.Galois

open scoped Pointwise

/-- **Group-theoretic core.**  A group `A` acting by automorphisms on a group `Q` of prime
order `q`; if `gcd (#A, q-1) = 1` then the action is trivial.

A group of prime order is cyclic, so `#Aut(Q) = q - 1` for a group `Q` of prime order
(`IsCyclic.card_mulAut` together with `Nat.totient_prime`).  Hence for `a : A` the automorphism
`φ a` has order dividing both `#A` (it is killed by the exponent of `A`) and `#(MulAut Q) = q-1`,
so its order divides `gcd (#A, q-1) = 1`; thus `φ a = 1`. -/
theorem monoidHom_eq_one_of_prime_card_coprime
    {Q A : Type*} [Group Q] [Group A]
    {q : ℕ} (hcard : Nat.card Q = q) (hprime : Nat.Prime q)
    (hcop : (Nat.card A).Coprime (q - 1))
    (φ : A →* MulAut Q) : φ = 1 := by
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hprime.ne_zero)
  haveI : Fact (Nat.Prime q) := ⟨hprime⟩
  haveI : IsCyclic Q := isCyclic_of_prime_card hcard
  have hAut : Nat.card (MulAut Q) = q - 1 := by
    rw [IsCyclic.card_mulAut Q, hcard, Nat.totient_prime hprime]
  apply MonoidHom.ext
  intro a
  refine Commons.GroupTheory.pow_eq_one_of_coprime_exp (φ a) (Nat.card A) (q - 1) ?_ ?_ hcop
  · rw [← map_pow, pow_card_eq_one', map_one]
  · rw [← hAut]; exact pow_card_eq_one'

/-- **Norm equivariance.**  If `τ` is a lift of `σ ∈ Gal(B₁/B)` to `Gal(E/B)`, then for every
`x : E` the norm from `E` down to `B₁` satisfies `σ (N_{E/B₁} x) = N_{E/B₁} (τ x)`. -/
lemma norm_apply_restrictNormal_eq
    {B B₁ E : Type*} [Field B] [Field B₁] [Field E]
    [Algebra B B₁] [Algebra B E] [Algebra B₁ E] [IsScalarTower B B₁ E]
    [IsGalois B B₁] [IsGalois B E]
    (σ : B₁ ≃ₐ[B] B₁) (τ : E ≃ₐ[B] E) (hτ : τ.restrictNormal B₁ = σ) (x : E) :
    σ (Algebra.norm B₁ x) = Algebra.norm B₁ (τ x) := by
  have he : RingHom.comp (algebraMap B₁ E) (σ.toRingEquiv : B₁ →+* B₁) =
      RingHom.comp (τ.toRingEquiv : E →+* E) (algebraMap B₁ E) := by
    ext y
    simp only [RingHom.comp_apply]
    have h := AlgEquiv.restrictNormal_commutes τ B₁ y
    rw [hτ] at h
    exact h
  have h := Algebra.norm_eq_of_equiv_equiv σ.toRingEquiv τ.toRingEquiv he x
  have h2 : σ.toRingEquiv ((Algebra.norm B₁) x) = (Algebra.norm B₁) (τ.toRingEquiv x) := by
    rw [h, RingEquiv.apply_symm_apply]
  simpa using h2

/-- The coprime-action mechanism for the abelian-case norm kernel condition, **with the tower
structure that makes it well-posed**: `B ⊆ B₁ ⊆ E`, `B₁/B` finite Galois, `E/B₁` finite, and
`E/B` finite Galois (so that every `σ ∈ Gal(B₁/B)` lifts to `Gal(E/B)`, making
`N_{E/B₁}(Eˣ)` stable under `Gal(B₁/B)`).  If the quotient `B₁ˣ ⧸ N_{E/B₁}(Eˣ)` has prime order
`q` and `q - 1` is coprime to `#Gal(B₁/B)`, then the induced action on the quotient is trivial:
`σ x / x ∈ N_{E/B₁}(Eˣ)` for all `σ`, `x`. -/
theorem div_mem_range_norm_of_prime_quotient_coprime_of_isGalois_tower
    {B B₁ E : Type*} [Field B] [Field B₁] [Field E]
    [Algebra B B₁] [Algebra B E] [Algebra B₁ E] [IsScalarTower B B₁ E]
    [FiniteDimensional B B₁] [IsGalois B B₁] [FiniteDimensional B₁ E] [IsGalois B E]
    (hprime : Nat.Prime (Nat.card (B₁ˣ ⧸
      MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁)))))
    (hcop : (Nat.card (B₁ ≃ₐ[B] B₁)).Coprime
      (Nat.card (B₁ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁))) - 1))
    (σ : B₁ ≃ₐ[B] B₁) (x : B₁ˣ) :
    Units.map σ.toRingEquiv.toMonoidHom x / x ∈
      MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁)) := by
  set N : Subgroup B₁ˣ := MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁)) with hN
  haveI : N.Normal := inferInstance
  -- The action `α ρ` of `ρ` on `B₁ˣ`
  let α : (B₁ ≃ₐ[B] B₁) → B₁ˣ →* B₁ˣ := fun ρ => Units.map ρ.toRingEquiv.toMonoidHom
  -- `N` is stable under this action
  have hstab : ∀ (ρ : B₁ ≃ₐ[B] B₁), ∀ n ∈ N, α ρ n ∈ N := by
    intro ρ n hn
    rw [hN, MonoidHom.mem_range] at hn
    obtain ⟨w, hw⟩ := hn
    obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := B) (K₁ := B₁) (E := E) ρ
    refine MonoidHom.mem_range.mpr ⟨Units.map τ.toRingEquiv.toMonoidHom w, ?_⟩
    rw [← hw]
    ext
    simp only [α, Units.coe_map]
    have h := norm_apply_restrictNormal_eq ρ τ hτ (w : E)
    simpa using h.symm
  -- The action preserves `N`, so it descends to `Q = B₁ˣ ⧸ N`
  have hker : ∀ ρ : B₁ ≃ₐ[B] B₁, N ≤ ((QuotientGroup.mk' N).comp (α ρ)).ker := by
    intro ρ n hn
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hstab ρ n hn
  let Φ : (B₁ ≃ₐ[B] B₁) → (B₁ˣ ⧸ N) →* (B₁ˣ ⧸ N) :=
    fun ρ => QuotientGroup.lift N ((QuotientGroup.mk' N).comp (α ρ)) (hker ρ)
  have hΦ : ∀ (ρ : B₁ ≃ₐ[B] B₁) (u : B₁ˣ),
      Φ ρ (↑u : B₁ˣ ⧸ N) = (↑(α ρ u) : B₁ˣ ⧸ N) := by
    intro ρ u
    show (QuotientGroup.lift N ((QuotientGroup.mk' N).comp (α ρ)) (hker ρ)) (↑u) = _
    rw [QuotientGroup.lift_mk']
    rfl
  -- `α` is multiplicative, pointwise
  have hα_mul : ∀ (ρ ρ' : B₁ ≃ₐ[B] B₁) (u : B₁ˣ), α (ρ * ρ') u = α ρ (α ρ' u) := by
    intro ρ ρ' u
    ext
    simp only [α, Units.coe_map]
    rfl
  -- `α ρ⁻¹` inverts `α ρ`, pointwise
  have hα_inv : ∀ (ρ : B₁ ≃ₐ[B] B₁) (u : B₁ˣ), α ρ⁻¹ (α ρ u) = u := by
    intro ρ u
    ext
    simp only [α, Units.coe_map]
    simp
  have hα_inv' : ∀ (ρ : B₁ ≃ₐ[B] B₁) (u : B₁ˣ), α ρ (α ρ⁻¹ u) = u := by
    intro ρ u
    ext
    simp only [α, Units.coe_map]
    simp
  -- `Φ σ⁻¹` is a left inverse of `Φ σ`
  have hleft : ∀ (ρ : B₁ ≃ₐ[B] B₁) (y : B₁ˣ ⧸ N), Φ ρ⁻¹ (Φ ρ y) = y := by
    intro ρ y
    induction y using Quotient.inductionOn with
    | h u =>
      rw [hΦ, hΦ, hα_inv ρ u]
  -- `Φ σ⁻¹` is a right inverse of `Φ σ`
  have hright : ∀ (ρ : B₁ ≃ₐ[B] B₁) (y : B₁ˣ ⧸ N), Φ ρ (Φ ρ⁻¹ y) = y := by
    intro ρ y
    induction y using Quotient.inductionOn with
    | h u =>
      rw [hΦ, hΦ, hα_inv' ρ u]
  have hbij : ∀ ρ : B₁ ≃ₐ[B] B₁, Function.Bijective (Φ ρ) := by
    intro ρ
    exact ⟨fun y z h => by rw [← hleft ρ y, h, hleft ρ z],
      fun y => ⟨Φ ρ⁻¹ y, hright ρ y⟩⟩
  -- The action as a group homomorphism `Gal(B₁/B) →* MulAut Q`
  let φ : (B₁ ≃ₐ[B] B₁) →* MulAut (B₁ˣ ⧸ N) :=
    MonoidHom.mk' (fun ρ => (MulEquiv.ofBijective (Φ ρ) (hbij ρ) : MulAut (B₁ˣ ⧸ N))) (by
      intro ρ ρ'
      ext y
      induction y using Quotient.inductionOn with
      | h u =>
        rw [MulEquiv.ofBijective_apply, MulAut.mul_apply, MulEquiv.ofBijective_apply,
          MulEquiv.ofBijective_apply, hΦ, hΦ, hΦ, hα_mul ρ ρ' u])
  -- The group-theoretic core: the action is trivial
  have hφ1 : φ = 1 :=
    monoidHom_eq_one_of_prime_card_coprime (Q := B₁ˣ ⧸ N) (A := B₁ ≃ₐ[B] B₁)
      (q := Nat.card (B₁ˣ ⧸ N)) rfl hprime hcop φ
  -- hence `Φ σ` fixes the class of `x`
  have hfix : Φ σ (↑x : B₁ˣ ⧸ N) = (↑x : B₁ˣ ⧸ N) := by
    have h1 := congrArg (fun e : MulAut (B₁ˣ ⧸ N) => e (↑x : B₁ˣ ⧸ N))
      (show (φ : (B₁ ≃ₐ[B] B₁) →* MulAut (B₁ˣ ⧸ N)) σ = 1 by rw [hφ1]; rfl)
    simpa [φ, MonoidHom.mk'_apply, MulEquiv.ofBijective_apply, MonoidHom.one_apply] using h1
  have hcl : (↑(α σ x) : B₁ˣ ⧸ N) = (↑x : B₁ˣ ⧸ N) := by
    rw [← hΦ]; exact hfix
  -- conclude
  have hgoal : (α σ x) * x⁻¹ ∈ N := by
    have h2 : (↑((α σ x) * x⁻¹) : B₁ˣ ⧸ N) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcl, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h2
  simpa [α, div_eq_mul_inv] using hgoal

end Commons.FieldTheory.Galois