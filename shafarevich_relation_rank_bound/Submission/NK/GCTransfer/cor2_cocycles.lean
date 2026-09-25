/-
The cochain-level transfer (corestriction) identity
`res ≫ cor = [Γ : S] • 𝟙` for `2`-cocycles with coefficients in an arbitrary `Rep k Γ`.

For a finite-index subgroup `S ≤ Γ`, a `2`-cocycle `z` of `Γ`, and `σ τ : Γ` one has

`cor2 (z|_S) σ τ = [Γ : S] • z (σ, τ) + d¹² (Ξ - P) (σ, τ)`,

where `Ξ` and `P` are the auxiliary `1`-cochains of `Submission.NK.GCTransfer.Defs`
(this is the classical computation showing that the transfer of the restriction of a
`2`-cocycle is `[Γ : S]` times the cocycle, up to a coboundary).
-/
import Mathlib
import Submission.NK.GCTransfer.Defs
import Submission.NK.GCTransfer.Coset

open CategoryTheory Representation

set_option maxHeartbeats 1600000

universe u

namespace NK.GCTransfer

/-! ### The local form of the cocycle identity

For a coset representative `x` with `a = sX S x σ = x σ (sRep S (x * σ))⁻¹`,
`y = sRep S (x * σ)`, `b = sX S y τ` and `w = sRep S (y * τ)` the `2`-cocycle identity
for `z` (applied to the pairs `(a, y, τ)` and `(a, b, w)`) gives

`z (a, b) = z (x σ, τ) - ρ a (z (y, τ)) - z (a b, w) + ρ a (z (b, w)) + z (a, y)`.

This is the per-coset identity which, summed over the cosets `c ∈ S \ Γ`, yields the
transfer identity. -/
private lemma local_cocycle_id {Γ : Type u} [Group Γ] [Fintype Γ] (S : Subgroup Γ) {k : Type u}
    [CommRing k] (A : Rep.{u,u,u} k Γ) (z : groupCohomology.cocycles₂ A) (x σ τ : Γ) :
    z (sX S x σ, sX S (sRep S (x * σ)) τ)
      = z (x * σ, τ)
        - A.ρ (sX S x σ) (z (sRep S (x * σ), τ))
        - z (sX S x σ * sX S (sRep S (x * σ)) τ, sRep S (sRep S (x * σ) * τ))
        + A.ρ (sX S x σ) (z (sX S (sRep S (x * σ)) τ, sRep S (sRep S (x * σ) * τ)))
        + z (sX S x σ, sRep S (x * σ)) := by
  have h1 := (groupCohomology.mem_cocycles₂_iff z).1 z.2 (sX S x σ) (sRep S (x * σ)) τ
  rw [sX_mul_rep] at h1
  have h2 := (groupCohomology.mem_cocycles₂_iff z).1 z.2 (sX S x σ) (sX S (sRep S (x * σ)) τ)
    (sRep S (sRep S (x * σ) * τ))
  rw [sX_mul_rep] at h2
  have H1 : z (sX S x σ, sRep S (x * σ) * τ)
      = z (x * σ, τ) + z (sX S x σ, sRep S (x * σ))
        - A.ρ (sX S x σ) (z (sRep S (x * σ), τ)) := by
    rw [eq_sub_iff_add_eq]
    exact (add_comm _ _).trans h1.symm
  have H2 : z (sX S x σ, sX S (sRep S (x * σ)) τ)
      = A.ρ (sX S x σ) (z (sX S (sRep S (x * σ)) τ, sRep S (sRep S (x * σ) * τ)))
        + z (sX S x σ, sRep S (x * σ) * τ)
        - z (sX S x σ * sX S (sRep S (x * σ)) τ, sRep S (sRep S (x * σ) * τ)) := by
    rw [eq_sub_iff_add_eq]
    exact (add_comm _ _).trans h2
  rw [H2, H1]
  abel

/-! ### Reindexing a coset sum

Right multiplication by `σ` permutes the cosets; the corresponding "twisted" reindexing
of a sum of coefficients is the following identity (it is applied below to the `P`- and
`Ξ`-terms of the correction cocycle). -/
private lemma sum_rho_reindex {Γ : Type u} [Group Γ] [Fintype Γ] (S : Subgroup Γ) {k : Type u}
    [CommRing k] (A : Rep.{u,u,u} k Γ) (σ : Γ)
    (F : Quotient (QuotientGroup.rightRel S) → A) :
    (∑ c : Quotient (QuotientGroup.rightRel S),
        A.ρ ((Quotient.out c)⁻¹) (A.ρ (sX S (Quotient.out c) σ) (F (csShift S σ c))))
      = A.ρ σ (∑ c, A.ρ ((Quotient.out c)⁻¹) (F c)) := by
  have step : ∀ c : Quotient (QuotientGroup.rightRel S),
      A.ρ ((Quotient.out c)⁻¹) (A.ρ (sX S (Quotient.out c) σ) (F (csShift S σ c)))
        = A.ρ σ (A.ρ ((Quotient.out (csShift S σ c))⁻¹) (F (csShift S σ c))) := by
    intro c
    simp only [sRep_shift, sX]
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Rep.ρ_mul, ← Rep.ρ_mul]
    congr 1
    group
  rw [Finset.sum_congr rfl (fun c _ => step c), ← map_sum]
  congr 1
  exact csSum_shift S σ (fun c => A.ρ ((Quotient.out c)⁻¹) (F c))

/-! ### The four terms of the summed identity -/

/-- Sum of the first terms: `Σ_c ρ(x_c)⁻¹ z (x_c σ, τ) = [Γ : S] z (σ,τ) + P(στ) - P(σ)`. -/
private lemma sum_T1 {Γ : Type u} [Group Γ] [Fintype Γ] (S : Subgroup Γ) {k : Type u}
    [CommRing k] (A : Rep.{u,u,u} k Γ) (z : groupCohomology.cocycles₂ A) (σ τ : Γ) :
    (∑ c : Quotient (QuotientGroup.rightRel S),
        A.ρ ((Quotient.out c)⁻¹) (z (Quotient.out c * σ, τ)))
      = (Subgroup.index S) • z (σ, τ) + Pb S A (⇑z) (σ * τ) - Pb S A (⇑z) σ := by
  have step : ∀ c : Quotient (QuotientGroup.rightRel S),
      A.ρ ((Quotient.out c)⁻¹) (z (Quotient.out c * σ, τ))
        = z (σ, τ) + A.ρ ((Quotient.out c)⁻¹) (z (Quotient.out c, σ * τ))
          - A.ρ ((Quotient.out c)⁻¹) (z (Quotient.out c, σ)) := by
    intro c
    have h1 := (groupCohomology.mem_cocycles₂_iff z).1 z.2 (Quotient.out c) σ τ
    have h2 : z (Quotient.out c * σ, τ)
        = A.ρ (Quotient.out c) (z (σ, τ)) + z (Quotient.out c, σ * τ)
          - z (Quotient.out c, σ) := by
      rw [eq_sub_iff_add_eq]
      exact h1
    rw [h2, LinearMap.map_sub, LinearMap.map_add]
    have hx : A.ρ ((Quotient.out c)⁻¹) (A.ρ (Quotient.out c) (z (σ, τ))) = z (σ, τ) := by
      rw [← LinearMap.comp_apply, ← Rep.ρ_mul, inv_mul_cancel, map_one]
      rfl
    rw [hx]
  rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, cs_card_eq_index]
  rw [Pb, Pb]

/-- Sum of the third terms: `Σ_c ρ(x_c)⁻¹ z (a_c(σ) a_{cσ}(τ), x_{cστ}) = Ξ(στ)`. -/
private lemma sum_T3 {Γ : Type u} [Group Γ] [Fintype Γ] (S : Subgroup Γ) {k : Type u}
    [CommRing k] (A : Rep.{u,u,u} k Γ) (z : groupCohomology.cocycles₂ A) (σ τ : Γ) :
    (∑ c : Quotient (QuotientGroup.rightRel S),
        A.ρ ((Quotient.out c)⁻¹)
          (z (sX S (Quotient.out c) σ * sX S (sRep S (Quotient.out c * σ)) τ,
              sRep S (sRep S (Quotient.out c * σ) * τ))))
      = Xi S A (⇑z) (σ * τ) := by
  rw [Xi]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [sX_mul, sRep_mul_right, sRep_mul_assoc_rep]

/-- Sum of the fifth terms: `Σ_c ρ(x_c)⁻¹ z (a_c(σ), x_{cσ}) = Ξ(σ)`. -/
private lemma sum_T5 {Γ : Type u} [Group Γ] [Fintype Γ] (S : Subgroup Γ) {k : Type u}
    [CommRing k] (A : Rep.{u,u,u} k Γ) (z : groupCohomology.cocycles₂ A) (σ : Γ) :
    (∑ c : Quotient (QuotientGroup.rightRel S),
        A.ρ ((Quotient.out c)⁻¹) (z (sX S (Quotient.out c) σ, sRep S (Quotient.out c * σ))))
      = Xi S A (⇑z) σ := by
  rw [Xi]

/-- **The cochain-level transfer (corestriction) identity for `2`-cocycles.**
For a finite-index subgroup `S ≤ Γ` and a `2`-cocycle `z` of `Γ`, the transfer of the
restriction of `z` to `S` equals `[Γ : S] • z` plus the coboundary of the correction
`1`-cochain `Ξ - P`. -/
theorem cor2_cocycles {Γ : Type u} [Group Γ] [Fintype Γ] (S : Subgroup Γ) {k : Type u}
    [CommRing k] (A : Rep.{u,u,u} k Γ) (z : groupCohomology.cocycles₂ A) (σ τ : Γ) :
    NK.GCTransfer.cor2 S A (fun s t => z ((s : Γ), (t : Γ))) σ τ
      = (Subgroup.index S) • (z (σ, τ))
        + (groupCohomology.d₁₂ A).hom
            (fun γ => NK.GCTransfer.Xi S A (⇑z) γ - NK.GCTransfer.Pb S A (⇑z) γ) (σ, τ) := by
  classical
  have push : ∀ (f : A →ₗ[k] A) (a b c' d e : A),
      f (a - b - c' + d + e) = f a - f b - f c' + f d + f e := by
    intro f a b c' d e
    rw [map_add, map_add, LinearMap.map_sub, LinearMap.map_sub]
  have hcor2 : cor2 S A (fun s t => z ((s : Γ), (t : Γ))) σ τ
      = ∑ c : Quotient (QuotientGroup.rightRel S),
          A.ρ ((Quotient.out c)⁻¹)
            (z (sX S (Quotient.out c) σ, sX S (sRep S (Quotient.out c * σ)) τ)) := by
    rw [cor2]
    rfl
  have hstep : ∀ c : Quotient (QuotientGroup.rightRel S),
      A.ρ ((Quotient.out c)⁻¹) (z (sX S (Quotient.out c) σ, sX S (sRep S (Quotient.out c * σ)) τ))
      = A.ρ ((Quotient.out c)⁻¹) (z (Quotient.out c * σ, τ))
        - A.ρ ((Quotient.out c)⁻¹)
            (A.ρ (sX S (Quotient.out c) σ) (z (sRep S (Quotient.out c * σ), τ)))
        - A.ρ ((Quotient.out c)⁻¹)
            (z (sX S (Quotient.out c) σ * sX S (sRep S (Quotient.out c * σ)) τ,
                sRep S (sRep S (Quotient.out c * σ) * τ)))
        + A.ρ ((Quotient.out c)⁻¹)
            (A.ρ (sX S (Quotient.out c) σ)
              (z (sX S (sRep S (Quotient.out c * σ)) τ,
                  sRep S (sRep S (Quotient.out c * σ) * τ))))
        + A.ρ ((Quotient.out c)⁻¹) (z (sX S (Quotient.out c) σ, sRep S (Quotient.out c * σ))) := by
    intro c
    rw [local_cocycle_id, push]
  have hdelta : (∑ c : Quotient (QuotientGroup.rightRel S),
          A.ρ ((Quotient.out c)⁻¹) (z (sX S (Quotient.out c) σ, sX S (sRep S (Quotient.out c * σ)) τ)))
      = (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ ((Quotient.out c)⁻¹) (z (Quotient.out c * σ, τ)))
        - (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ ((Quotient.out c)⁻¹)
              (A.ρ (sX S (Quotient.out c) σ) (z (sRep S (Quotient.out c * σ), τ))))
        - (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ ((Quotient.out c)⁻¹)
              (z (sX S (Quotient.out c) σ * sX S (sRep S (Quotient.out c * σ)) τ,
                  sRep S (sRep S (Quotient.out c * σ) * τ))))
        + (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ ((Quotient.out c)⁻¹)
              (A.ρ (sX S (Quotient.out c) σ)
                (z (sX S (sRep S (Quotient.out c * σ)) τ,
                    sRep S (sRep S (Quotient.out c * σ) * τ)))))
        + (∑ c : Quotient (QuotientGroup.rightRel S),
            A.ρ ((Quotient.out c)⁻¹) (z (sX S (Quotient.out c) σ, sRep S (Quotient.out c * σ)))) := by
    rw [Finset.sum_congr rfl (fun c _ => hstep c), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have h2 : (∑ c : Quotient (QuotientGroup.rightRel S),
        A.ρ ((Quotient.out c)⁻¹)
          (A.ρ (sX S (Quotient.out c) σ) (z (sRep S (Quotient.out c * σ), τ))))
      = A.ρ σ (Pb S A (⇑z) τ) := by
    have h := sum_rho_reindex S A σ (fun c => z (Quotient.out c, τ))
    simpa only [sRep_shift, Pb] using h
  have h4 : (∑ c : Quotient (QuotientGroup.rightRel S),
        A.ρ ((Quotient.out c)⁻¹)
          (A.ρ (sX S (Quotient.out c) σ)
            (z (sX S (sRep S (Quotient.out c * σ)) τ,
                sRep S (sRep S (Quotient.out c * σ) * τ)))))
      = A.ρ σ (Xi S A (⇑z) τ) := by
    have h := sum_rho_reindex S A σ
      (fun c => z (sX S (Quotient.out c) τ, sRep S (Quotient.out c * τ)))
    simpa only [sRep_shift, Xi] using h
  rw [hcor2, hdelta, sum_T1 S A z σ τ, h2, sum_T3 S A z σ τ, h4, sum_T5 S A z σ]
  rw [groupCohomology.d₁₂_hom_apply]
  simp only [Prod.fst, Prod.snd]
  rw [LinearMap.map_sub]
  abel

end NK.GCTransfer
