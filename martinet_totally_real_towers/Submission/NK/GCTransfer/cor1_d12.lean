import Mathlib
import Submission.NK.GCTransfer.Defs
import Submission.NK.GCTransfer.Coset

open CategoryTheory Representation Rep

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

namespace NK.GCTransfer

variable {Γ : Type u} [Group Γ] [Fintype Γ] (S : Subgroup Γ)
variable {k : Type u} [CommRing k] (A : Rep.{u,u,u} k Γ)

omit [Fintype Γ] in
/-- The action of `σ` composed with the inverse of the coset representative of `a σ` equals the
inverse of the action of the inverse of the representative of `a`, followed by the action of the
"defect" `sX S a σ = a σ (rep (aσ))⁻¹ ∈ S`.

This is the only group-theoretic input of the cochain-level identity `d₁₂ ∘ cor1 = cor2 ∘ d₁₂`:
it is what allows the first sum of `d₁₂ (cor1 b) (σ, τ)` to be reindexed by the bijection
`c ↦ c σ` of the coset space. -/
lemma rho_shift_apply (a σ : Γ) (v : A) :
    A.ρ σ (A.ρ (sRep S (a * σ))⁻¹ v) = A.ρ a⁻¹ (A.ρ (sX S a σ) v) := by
  calc A.ρ σ (A.ρ (sRep S (a * σ))⁻¹ v)
      = A.ρ (σ * (sRep S (a * σ))⁻¹) v := by
        rw [← Module.End.mul_apply, ← map_mul]
    _ = A.ρ (a⁻¹ * sX S a σ) v := by
        rw [show σ * (sRep S (a * σ))⁻¹ = a⁻¹ * sX S a σ from by
          rw [show sX S a σ = a * σ * (sRep S (a * σ))⁻¹ from rfl]; group]
    _ = A.ρ a⁻¹ (A.ρ (sX S a σ) v) := by
        rw [map_mul, Module.End.mul_apply]

/-- **The transfer of `1`-cochains commutes with the differential.**  For a `1`-cochain `b` on the
subgroup `S ≤ Γ` and coefficients in an arbitrary representation `A` of `Γ`, the transfer of the
`1`-cochain `b` has differential equal to the transfer of the differential of `b`. -/
theorem cor1_d12 {Γ : Type u} [Group Γ] [Fintype Γ] (S : Subgroup Γ) {k : Type u} [CommRing k]
    (A : Rep.{u,u,u} k Γ) (b : S → A) (σ τ : Γ) :
    (groupCohomology.d₁₂ A).hom (NK.GCTransfer.cor1 S A b) (σ, τ)
      = NK.GCTransfer.cor2 S A
          (fun s t => (groupCohomology.d₁₂ (Rep.res S.subtype A)).hom b (s, t)) σ τ := by
  classical
  -- The first sum of `d₁₂ (cor1 b) (σ, τ)`, reindexed by `c ↦ c σ`, is the first sum of
  -- `cor2 (d₁₂ b) σ τ`.
  have hF : (∑ c : Quotient (QuotientGroup.rightRel S),
        A.ρ σ (A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) τ))))
      = ∑ c : Quotient (QuotientGroup.rightRel S),
        A.ρ (Quotient.out c)⁻¹
          (A.ρ (sX S (Quotient.out c) σ) (b (sXS S (sRep S (Quotient.out c * σ)) τ))) := by
    rw [← csSum_shift S σ
      (fun c => A.ρ σ (A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) τ))))]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [sRep_shift]
    exact rho_shift_apply S A (Quotient.out c) σ
      (b (sXS S (sRep S (Quotient.out c * σ)) τ))
  -- Unfolding the left-hand side.
  have hL : (groupCohomology.d₁₂ A).hom (NK.GCTransfer.cor1 S A b) (σ, τ)
      = (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ σ (A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) τ))))
        - (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) (σ * τ))))
        + (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) σ))) := by
    rw [groupCohomology.d₁₂_hom_apply]
    simp only [cor1]
    rw [map_sum]
  -- Unfolding the right-hand side; the middle and last sums agree with those of `hL` by
  -- `sXS_mul` and `sXS_coe`.
  have hR : NK.GCTransfer.cor2 S A
        (fun s t => (groupCohomology.d₁₂ (Rep.res S.subtype A)).hom b (s, t)) σ τ
      = (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ (Quotient.out c)⁻¹ (A.ρ (sX S (Quotient.out c) σ)
              (b (sXS S (sRep S (Quotient.out c * σ)) τ))))
        - (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) (σ * τ))))
        + (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) σ))) := by
    simp only [cor2]
    have hper : ∀ c : Quotient (QuotientGroup.rightRel S),
        A.ρ (Quotient.out c)⁻¹
          ((groupCohomology.d₁₂ (Rep.res S.subtype A)).hom b
            (sXS S (Quotient.out c) σ, sXS S (sRep S (Quotient.out c * σ)) τ))
        = A.ρ (Quotient.out c)⁻¹ (A.ρ (sX S (Quotient.out c) σ)
              (b (sXS S (sRep S (Quotient.out c * σ)) τ)))
          - A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) (σ * τ)))
          + A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) σ)) := by
      intro c
      simp only [groupCohomology.d₁₂_hom_apply, MonoidHom.comp_apply, Subgroup.subtype_apply,
        sXS_coe, sXS_mul, map_add, map_sub]
    rw [Finset.sum_congr rfl (fun c _ => hper c), Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  calc (groupCohomology.d₁₂ A).hom (NK.GCTransfer.cor1 S A b) (σ, τ)
      = (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ σ (A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) τ))))
        - (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) (σ * τ))))
        + (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) σ))) := hL
    _ = (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ (Quotient.out c)⁻¹ (A.ρ (sX S (Quotient.out c) σ)
              (b (sXS S (sRep S (Quotient.out c * σ)) τ))))
        - (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) (σ * τ))))
        + (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ (Quotient.out c)⁻¹ (b (sXS S (Quotient.out c) σ))) := by rw [hF]
    _ = NK.GCTransfer.cor2 S A
          (fun s t => (groupCohomology.d₁₂ (Rep.res S.subtype A)).hom b (s, t)) σ τ := hR.symm

end NK.GCTransfer
