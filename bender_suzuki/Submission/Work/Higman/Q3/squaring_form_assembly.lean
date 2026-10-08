/-
# From the squaring form to the normal form

The classification of `Work.Higman.cocycle_normal_form` is entirely about the *squaring form*
`Q u = b u u` of the cocycle: two biadditive maps with the same squaring form differ by an
alternating form, i.e. by a coboundary (`Work.Higman.coboundary_of_form_match`).  Consequently,
once additive coordinate changes `φ : V ≃+ 𝔽 × 𝔽`, `ψ : W ≃+ 𝔽` have been found which carry `Q`
to the squaring form of one of Higman's Column-II laws (`bCocycle`, `cCocycle`, `dCocycle`), the
cocycle `b` is in the corresponding Column-V normal form, up to a coboundary.

This file performs that last step.  What remains for `cocycle_normal_form` is the classification
of the squaring form (`Work.Higman.Q3.cocycle_diagonal_pinning` for the structure of `Q` in the
`ξ`-eigenbasis, and the case analysis of Higman's Lemma 12).
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.Q3.form_match
import Submission.Work.Higman.Family

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Higman

/-- **The normal form from the squaring form.**  If the squaring form `u ↦ b u u` is carried by
additive coordinate changes `φ`, `ψ` to the squaring form of `B(n,θ,ε)`, `C(n,ε)` or `D(n,θ,ε)`
(with the Column-III conditions on `ε`), then `b` itself is in the corresponding normal form, up
to a coboundary. -/
theorem cocycle_normal_form_of_squaring_form
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    {b : V → V → W} [Biadd b] [Finite V]
    (h : ∃ (n : ℕ) (φ : V ≃+ (GaloisField 2 n × GaloisField 2 n)) (ψ : W ≃+ GaloisField 2 n)
        (θ : GaloisField 2 n ≃+* GaloisField 2 n) (ε : GaloisField 2 n),
        Nat.card W = 2 ^ n ∧ Odd (orderOf θ) ∧
        ((ε ≠ 0 ∧ (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ) ∧
            ∀ u : V, ψ (b u u) = bCocycle (GaloisField 2 n) θ ε (φ u) (φ u))
          ∨ ((∀ a : GaloisField 2 n, (θ (θ a)) ^ 2 = a) ∧
              (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ ^ 2 * ρ) ∧
              ∀ u : V, ψ (b u u) = cCocycle (GaloisField 2 n) θ ε (φ u) (φ u))
          ∨ (θ ^ 5 = 1 ∧ θ ≠ RingEquiv.refl _ ∧ 5 ∣ n ∧
              (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ (θ (θ (θ ρ))) * θ ρ * ρ⁻¹) ∧
              ∀ u : V, ψ (b u u) = dCocycle (GaloisField 2 n) θ ε (φ u) (φ u)))) :
    ∃ (n : ℕ) (φ : V ≃+ (GaloisField 2 n × GaloisField 2 n)) (ψ : W ≃+ GaloisField 2 n)
      (θ : GaloisField 2 n ≃+* GaloisField 2 n) (ε : GaloisField 2 n)
      (c : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n),
      Nat.card W = 2 ^ n ∧ Odd (orderOf θ) ∧
      ((ε ≠ 0 ∧ (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ) ∧
          ∀ u v : V, ψ (b u v) = bCocycle (GaloisField 2 n) θ ε (φ u) (φ v) +
            (c (φ u) + c (φ v) + c (φ u + φ v)))
        ∨ ((∀ a : GaloisField 2 n, (θ (θ a)) ^ 2 = a) ∧
            (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ ^ 2 * ρ) ∧
            ∀ u v : V, ψ (b u v) = cCocycle (GaloisField 2 n) θ ε (φ u) (φ v) +
              (c (φ u) + c (φ v) + c (φ u + φ v)))
        ∨ (θ ^ 5 = 1 ∧ θ ≠ RingEquiv.refl _ ∧ 5 ∣ n ∧
            (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ (θ (θ (θ ρ))) * θ ρ * ρ⁻¹) ∧
            ∀ u v : V, ψ (b u v) = dCocycle (GaloisField 2 n) θ ε (φ u) (φ v) +
              (c (φ u) + c (φ v) + c (φ u + φ v)))) := by
  obtain ⟨n, φ, ψ, θ, ε, hcard, hodd, hcase⟩ := h
  rcases hcase with ⟨hε, hρ, hQ⟩ | ⟨hθ, hρ, hQ⟩ | ⟨hθ5, hθ1, h5, hρ, hQ⟩
  · obtain ⟨c, hc⟩ := coboundary_of_form_match (n := n) (bc := bCocycle (GaloisField 2 n) θ ε)
      φ ψ hQ
    exact ⟨n, φ, ψ, θ, ε, c, hcard, hodd, Or.inl ⟨hε, hρ, hc⟩⟩
  · obtain ⟨c, hc⟩ := coboundary_of_form_match (n := n) (bc := cCocycle (GaloisField 2 n) θ ε)
      φ ψ hQ
    exact ⟨n, φ, ψ, θ, ε, c, hcard, hodd, Or.inr (Or.inl ⟨hθ, hρ, hc⟩)⟩
  · obtain ⟨c, hc⟩ := coboundary_of_form_match (n := n) (bc := dCocycle (GaloisField 2 n) θ ε)
      φ ψ hQ
    exact ⟨n, φ, ψ, θ, ε, c, hcard, hodd, Or.inr (Or.inr ⟨hθ5, hθ1, h5, hρ, hc⟩)⟩

end Work.Higman
