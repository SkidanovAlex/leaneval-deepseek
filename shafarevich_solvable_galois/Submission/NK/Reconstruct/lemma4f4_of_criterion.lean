import Submission.NK.Reconstruct.hausMk_galToGamma_iff_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shimizu's Lemma 4f.4 from the criterion at the middle field

Shimizu's Lemma 4f.4 (arXiv:2009.10431) states: for number fields `K₁, K₂`, a finite extension
`L/K₁K₂` and an isomorphism `σ̄ : Γ_{K₁} ≅ Γ_{K₂}` with `σ̄ ∘ π_{L/K₁} = π_{L/K₂}`, one has
`K₁^{(∞,ℓ)}K₂ = K₁K₂^{(∞,ℓ)}`.

This file proves the Lemma **for arbitrary number fields `K₁, K₂ ⊆ L` as base fields, from the
single pointwise criterion at the middle field** `N = K₁L ⊔ K₂L` (the hypotheses `K_i.L ≤ N` and
`N ≤ K₁.L ⊔ K₂.L` say precisely that) with `N ≤ L`:

  `(C)`  for every `h : Ω ≃ₐ[↥N] Ω`, the classes `galToGamma (h|_{K₁})` and `galToGamma (h|_{K₂})`
         are simultaneously invisible.

Everything else in the proof of the Lemma — the Galois correspondence between the fixing subgroups
and the two composita, and the `γ^m`-argument that upgrades the criterion to the level `L` — is
independent of the shape of the base fields, and is what is formalised here.  In the classical
situation `N = K₁L ⊔ K₂L` and the criterion is *derived* from Shimizu's identity by the descent step
(step 2 of the proof, cf. the discussion in `Submission/Work/Reconstruct/lemma4f4.lean` and README
§24.4); that descent is the one place where the general base change `π_{M/K}` for an arbitrary finite
extension `M/K` of number fields is needed.

## Contents

* `NK.Reconstruct.lemma4f4_of_criterion` — Shimizu's Lemma 4f.4 for arbitrary base fields, from
  the criterion at the middle field.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, Lemma 4f.4.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

open NK.Chebotarev
open scoped NumberField

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **Shimizu's Lemma 4f.4 for arbitrary base fields, from the criterion at the middle field.** -/
theorem lemma4f4_of_criterion (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥(K₁.L) Ω] [IsSepClosure ↥(K₂.L) Ω]
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime]
    (N : IntermediateField ℚ Ω) [IsSepClosure ↥N Ω]
    (hN₁ : K₁.L ≤ N) (hN₂ : K₂.L ≤ N) (hNL : N ≤ L.L)
    (hNsup : N ≤ (K₁.L ⊔ K₂.L : IntermediateField ℚ Ω))
    (hcriterion : ∀ h : Ω ≃ₐ[↥N] Ω,
      gammaHausMk (K := ↥(K₁.L)) (K' := Ω) (ℓ := ℓ)
          (galToGamma (K := ↥(K₁.L)) (K' := Ω) ℓ
            (galRestrict (E := K₁.L) (F := N) hN₁ h)) = 1
        ↔ gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ)
          (galToGamma (K := ↥(K₂.L)) (K' := Ω) ℓ
            (galRestrict (E := K₂.L) (F := N) hN₂ h)) = 1) :
    (levelInfinityOf K₁ ℓ ⊔ K₂.L : IntermediateField ℚ Ω)
      = (K₁.L ⊔ levelInfinityOf K₂ ℓ : IntermediateField ℚ Ω) := by
  -- the equality of fixing subgroups
  have hfix : (levelInfinityOf K₁ ℓ ⊔ K₂.L).fixingSubgroup
      = (K₁.L ⊔ levelInfinityOf K₂ ℓ).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_sup,
      fixingSubgroup_levelInfinityOf K₁ ℓ, fixingSubgroup_levelInfinityOf K₂ ℓ]
    refine le_antisymm ?_ ?_
    · rintro σ ⟨hσ₁, hσ₂⟩
      obtain ⟨hC, hCeq, hCinv⟩ := (mem_invisibleSub_iff K₁ ℓ σ).mp hσ₁
      have hσC : σ ∈ (K₁.L).fixingSubgroup := by
        rw [← range_restrictScalarsHom K₁.L]
        exact ⟨hC, hCeq⟩
      have hσN : σ ∈ N.fixingSubgroup := by
        have hσle : σ ∈ (K₁.L ⊔ K₂.L : IntermediateField ℚ Ω).fixingSubgroup := by
          rw [IntermediateField.fixingSubgroup_sup]
          exact ⟨hσC, hσ₂⟩
        rw [IntermediateField.mem_fixingSubgroup_iff] at hσle ⊢
        intro x hx
        exact hσle x (hNsup hx)
      set hN : Ω ≃ₐ[↥N] Ω := (IntermediateField.fixingSubgroupEquiv N) ⟨σ, hσN⟩ with hNdef'
      have hNcoe : ⇑hN = ⇑σ := rfl
      have hrest₁ : galRestrict (E := K₁.L) (F := N) hN₁ hN = hC := by
        ext x
        exact (congrFun hNcoe x).trans (congrFun (congrArg (fun f : Ω ≃ₐ[ℚ] Ω => ⇑f) hCeq) x).symm
      have hrest₂ : restrictScalarsHom K₂.L (galRestrict (E := K₂.L) (F := N) hN₂ hN) = σ := by
        ext x
        exact congrFun hNcoe x
      refine ⟨hσC, ?_⟩
      change σ ∈ invisibleSub K₂ ℓ
      rw [mem_invisibleSub_iff]
      exact ⟨galRestrict (E := K₂.L) (F := N) hN₂ hN, hrest₂,
        (hcriterion hN).mp (by rw [hrest₁]; exact hCinv)⟩
    · rintro σ ⟨hσ₁, hσ₂⟩
      obtain ⟨hD, hDeq, hDinv⟩ := (mem_invisibleSub_iff K₂ ℓ σ).mp hσ₂
      have hσD : σ ∈ (K₂.L).fixingSubgroup := by
        rw [← range_restrictScalarsHom K₂.L]
        exact ⟨hD, hDeq⟩
      have hσN : σ ∈ N.fixingSubgroup := by
        have hσle : σ ∈ (K₁.L ⊔ K₂.L : IntermediateField ℚ Ω).fixingSubgroup := by
          rw [IntermediateField.fixingSubgroup_sup]
          exact ⟨hσ₁, hσD⟩
        rw [IntermediateField.mem_fixingSubgroup_iff] at hσle ⊢
        intro x hx
        exact hσle x (hNsup hx)
      set hN : Ω ≃ₐ[↥N] Ω := (IntermediateField.fixingSubgroupEquiv N) ⟨σ, hσN⟩ with hNdef'
      have hNcoe : ⇑hN = ⇑σ := rfl
      have hrest₂ : galRestrict (E := K₂.L) (F := N) hN₂ hN = hD := by
        ext x
        exact (congrFun hNcoe x).trans (congrFun (congrArg (fun f : Ω ≃ₐ[ℚ] Ω => ⇑f) hDeq) x).symm
      have hrest₁ : restrictScalarsHom K₁.L (galRestrict (E := K₁.L) (F := N) hN₁ hN) = σ := by
        ext x
        exact congrFun hNcoe x
      refine ⟨?_, hσD⟩
      change σ ∈ invisibleSub K₁ ℓ
      rw [mem_invisibleSub_iff]
      exact ⟨galRestrict (E := K₁.L) (F := N) hN₁ hN, hrest₁,
        (hcriterion hN).mpr (by rw [hrest₂]; exact hDinv)⟩
  calc (levelInfinityOf K₁ ℓ ⊔ K₂.L : IntermediateField ℚ Ω)
      = IntermediateField.fixedField ((levelInfinityOf K₁ ℓ ⊔ K₂.L).fixingSubgroup) :=
        (InfiniteGalois.fixedField_fixingSubgroup _).symm
    _ = IntermediateField.fixedField ((K₁.L ⊔ levelInfinityOf K₂ ℓ).fixingSubgroup) := by
        rw [hfix]
    _ = (K₁.L ⊔ levelInfinityOf K₂ ℓ : IntermediateField ℚ Ω) :=
        InfiniteGalois.fixedField_fixingSubgroup _

end NK.Reconstruct
