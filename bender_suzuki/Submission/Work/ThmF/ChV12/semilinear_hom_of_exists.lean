import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

open Additive

/-- Flattening of a "semilinear" action: if every element of `D` acts on the
additive group `K` as `x ↦ a · σ x` for some `a ∈ Kˣ` and ring automorphism `σ`,
then this data can be organised into a genuine monoid homomorphism `D →* K ≃+* K`
together with a `Kˣ`-valued cocycle. -/
theorem semilinear_hom_of_exists {A D K : Type*} [Group A] [Group D] [DivisionRing K]
    (e : Additive A ≃+ K) (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (he : ∀ d : D, ∃ (a : Kˣ) (σ : K ≃+* K),
        ∀ x : A, e (Additive.ofMul (ρ d x)) = (a : K) * σ (e (Additive.ofMul x))) :
    ∃ (φ : D →* (K ≃+* K)) (c : D → Kˣ),
      (∀ d x, e (Additive.ofMul (ρ d x)) = (c d : K) * φ d (e (Additive.ofMul x))) ∧
      (∀ d d', (c (d * d') : K) = (c d : K) * φ d (c d' : K)) ∧
      (c 1 : K) = 1 ∧
      (∀ d, φ d = 1 → c d = 1 → d = 1) := by
  classical
  -- Extract, for every `d : D`, a pair `(a d, σ d)` witnessing the semilinearity.
  choose a σ hσ using he
  -- Uniqueness of the pair `(b, τ)` representing the action of `ρ d`.
  have key : ∀ (d : D) (b b' : K) (τ τ' : K ≃+* K), b ≠ 0 →
      (∀ x : A, e (Additive.ofMul (ρ d x)) = b * τ (e (Additive.ofMul x))) →
      (∀ x : A, e (Additive.ofMul (ρ d x)) = b' * τ' (e (Additive.ofMul x))) →
      b = b' ∧ τ = τ' := by
    intro d b b' τ τ' hb0 hb hb'
    -- `e ∘ ofMul` is surjective, so the two functions `b * τ ·` and `b' * τ' ·` agree everywhere.
    have hpt : ∀ y : K, b * τ y = b' * τ' y := by
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← ofMul_toMul z, ← hb (Additive.toMul z), ← hb' (Additive.toMul z)]
    have h1 : b = b' := by have h := hpt 1; simpa using h
    have h2 : τ = τ' := by
      ext y
      have h := hpt y
      rw [← h1] at h
      exact mul_left_cancel₀ hb0 h
    exact ⟨h1, h2⟩
  -- The composite of the two semilinear maps is again semilinear.
  have hcomp : ∀ d d' : D, ∀ x : A,
      e (Additive.ofMul (ρ (d * d') x)) =
        ((a d : K) * σ d (a d' : K)) * (σ d * σ d') (e (Additive.ofMul x)) := by
    intro d d' x
    rw [RingAut.mul_apply, mul_assoc, ← (σ d).map_mul, ← hσ d' x, ← hσ d (ρ d' x),
        map_mul ρ d d', MulAut.mul_apply]
  -- Comparing with the defining pair of `d * d'` gives the cocycle and multiplicativity.
  have hkey : ∀ d d' : D,
      (a (d * d') : K) = (a d : K) * σ d (a d' : K) ∧ σ (d * d') = σ d * σ d' := by
    intro d d'
    exact key (d * d') (a (d * d') : K) ((a d : K) * σ d (a d' : K))
      (σ (d * d')) (σ d * σ d') (Units.ne_zero (a (d * d'))) (hσ (d * d')) (hcomp d d')
  refine ⟨MonoidHom.mk' σ (fun d d' => (hkey d d').2), a, hσ, ?_, ?_, ?_⟩
  · intro d d'
    exact (hkey d d').1
  · have h := (key 1 (1 : K) (a 1 : K) (1 : K ≃+* K) (σ 1) one_ne_zero ?_ (hσ 1)).1
    · exact h.symm
    · intro x; simp
  · intro d hφ hc
    have hσd : σ d = 1 := by
      have := hφ
      rwa [MonoidHom.mk'_apply] at this
    have hρ : ρ d = 1 := by
      ext x
      have h := hσ d x
      rw [hσd, hc] at h
      have h2 : e (Additive.ofMul (ρ d x)) = e (Additive.ofMul x) := by simpa using h
      exact Additive.ofMul.injective (e.injective h2)
    exact hfaith (by rw [hρ, map_one])

end Work.ThmF.ChV12
