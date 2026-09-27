import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.Cone.Setup
import Submission.Work.KT.Cone.mv_surj
import Submission.Work.KT.Cone.mv_inj

/-!
# `Work.KT.Cone.Milnor` — Milnor's exactness in the two forms the cone needs

* `milnor_square` is the Mayer–Vietoris surjectivity onto the compatible pairs of a cartesian
  square of rings (Milnor patching); it is `Work.KT.Cone.mv_surj` verbatim.
* `milnor_mid` and `milnor_inj` are the middle exactness and the injectivity of the reduced part
  of the ideal sequence `K₀(U) → K₀(A) → K₀(B)`, for a surjection `π : A → B` and
  `U = ℂ·1 + ker π`; they are obtained from `mv_surj` and `mv_inj` applied to the (transposed)
  cartesian square

      U --ε--> ℂ
      |        |
    U.val    ofId
      v        v
      A --π--> B
-/

namespace Work.KT.Cone

open _root_.Matrix

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

/-- `algebraMap ℂ B` is injective for a nontrivial `ℂ`-algebra `B`. -/
lemma algebraMap_injective_of_nontrivial (B : Type) [Ring B] [Algebra ℂ B] [Nontrivial B] :
    Function.Injective (algebraMap ℂ B) := by
  intro c d h
  have h1 : algebraMap ℂ B (c - d) = 0 := by
    rw [_root_.map_sub (algebraMap ℂ B) c d, h, sub_self]
  have hc : c - d = 0 := by
    by_contra hne
    have hsm : (c - d) • (1 : B) = 0 := by
      rw [← Algebra.algebraMap_eq_smul_one (c - d), h1]
    have h4 : (1 : B) = 0 := by
      have h5 := congrArg (fun x : B => (c - d)⁻¹ • x) hsm
      rw [smul_zero, smul_smul, inv_mul_cancel₀ hne, one_smul] at h5
      exact h5
    exact absurd h4 one_ne_zero
  exact sub_eq_zero.mp hc

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] [Nontrivial B]

/-- **The cartesian square of the ideal sequence.**  For `U = ℂ·1 + ker π`, the square
`U → ℂ`, `U → A`, `ℂ → B`, `A → B` is a pull-back square. -/
lemma ideal_pullback (π : A →ₐ[ℂ] B) (U : Subalgebra ℂ A)
    (hU : ∀ r : A, r ∈ U ↔ ∃ c : ℂ, π r = algebraMap ℂ B c)
    (ε : U →ₐ[ℂ] ℂ) (hε : ∀ u : U, π u = algebraMap ℂ B (ε u)) :
    ∀ x₁ x₂, (Algebra.ofId ℂ B).toRingHom x₁ = π.toRingHom x₂ →
      ∃! u : U, ε.toRingHom u = x₁ ∧ U.val.toRingHom u = x₂ := by
  intro x₁ x₂ h
  have hx₂ : x₂ ∈ U := (hU x₂).mpr ⟨x₁, h.symm⟩
  have hεx : ε ⟨x₂, hx₂⟩ = x₁ := by
    have h1 : π x₂ = algebraMap ℂ B (ε ⟨x₂, hx₂⟩) := hε ⟨x₂, hx₂⟩
    have h2 : π x₂ = algebraMap ℂ B x₁ := h.symm
    exact algebraMap_injective_of_nontrivial B (h1.symm.trans h2)
  refine ⟨⟨x₂, hx₂⟩, ⟨hεx, rfl⟩, ?_⟩
  rintro u ⟨_hu1, hu2⟩
  exact Subtype.ext hu2

/-- **Middle exactness** of the ideal sequence `K₀(U) → K₀(A) → K₀(B)`, from Mayer–Vietoris
surjectivity applied to the cartesian square of the ideal sequence. -/
lemma milnor_mid (π : A →ₐ[ℂ] B) (hπ : Function.Surjective π)
    (U : Subalgebra ℂ A) (hU : ∀ r : A, r ∈ U ↔ ∃ c : ℂ, π r = algebraMap ℂ B c)
    (ε : U →ₐ[ℂ] ℂ) (hε : ∀ u : U, π u = algebraMap ℂ B (ε u)) :
    ∀ z : K0 A, K0.mapA π z = 0 → ∃ w : K0 U, K0.mapA ε w = 0 ∧ K0.mapA U.val w = z := by
  intro z hz
  have hcomm : (Algebra.ofId ℂ B).toRingHom.comp ε.toRingHom = π.toRingHom.comp U.val.toRingHom := by
    apply RingHom.ext
    intro u
    exact (hε u).symm
  obtain ⟨w, hw1, hw2⟩ := mv_surj ε.toRingHom U.val.toRingHom (Algebra.ofId ℂ B).toRingHom
    π.toRingHom hπ hcomm (ideal_pullback π U hU ε hε) 0 z (by
      rw [map_zero]
      exact hz.symm)
  exact ⟨w, hw1, hw2⟩

/-- **Injectivity of the reduced part** `K₀(U) → K₀(A)`, from Mayer–Vietoris injectivity applied
to the cartesian square of the ideal sequence, under the stable lifting hypothesis for
`π : A → B`. -/
lemma milnor_inj (π : A →ₐ[ℂ] B) (hπ : Function.Surjective π)
    (U : Subalgebra ℂ A) (hU : ∀ r : A, r ∈ U ↔ ∃ c : ℂ, π r = algebraMap ℂ B c)
    (ε : U →ₐ[ℂ] ℂ) (hε : ∀ u : U, π u = algebraMap ℂ B (ε u))
    (hlift : ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) B), IsUnit u →
      ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) A), IsUnit v ∧
        v.map π = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1)) :
    ∀ w : K0 U, K0.mapA ε w = 0 → K0.mapA U.val w = 0 → w = 0 := by
  have hcomm : (Algebra.ofId ℂ B).toRingHom.comp ε.toRingHom = π.toRingHom.comp U.val.toRingHom := by
    apply RingHom.ext
    intro u
    exact (hε u).symm
  exact mv_inj ε.toRingHom U.val.toRingHom (Algebra.ofId ℂ B).toRingHom π.toRingHom hπ hcomm
    (ideal_pullback π U hU ε hε) hlift

/-- **Mayer–Vietoris surjectivity** for a cartesian square of rings (Milnor patching): the map
`K₀(P) → K₀(P₁) × K₀(P₂)` is surjective onto the pairs that agree in `K₀(Q)`. -/
lemma milnor_square (P P₁ P₂ Q : Type) [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hσ₂ : Function.Surjective σ₂) (hc : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpull : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂) :
    ∀ z₁ z₂, K0.map σ₁ z₁ = K0.map σ₂ z₂ → ∃ z, K0.map ρ₁ z = z₁ ∧ K0.map ρ₂ z = z₂ :=
  mv_surj ρ₁ ρ₂ σ₁ σ₂ hσ₂ hc hpull

end

end Work.KT.Cone
