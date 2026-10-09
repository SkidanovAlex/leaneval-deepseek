import Mathlib
import Submission.Work.SSGRoute.E1aClean.decompDatumFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The henselisation embedding is `D_q`-equivariant

For a finite place `A` of `Ω` over the prime `q` of `K`, an isomorphism `e : D_q ≃* Gal(K^h/k^h)`
which restricts to the identity identification on `K` (`he`), and an embedding
`φ : K^h →+* K_q` of the henselisation into the completion which is the identity on `K` (`hφ`) and
fixes the image of the decomposition field under the local action (`hfix`), the action of `τ` on
`K^h` and the local action of `τ` on `K_q` correspond.

This is what makes `Units.map φ : (K^h)ˣ → K_qˣ` a morphism of `D_q`-representations, which the
coefficient push `(PUSH)` of the local dictionary of
`Work.SSGRoute.E1aClean.localDictionary_natural_family` needs.

The proof is bookkeeping: both sides are ring homomorphisms `K^h →+* K_q` and `K^h = k^h ⊔ K`
(`Work.SSGRoute.E1aClean.henselField_eq_sup`), so it suffices to check them on the two parts.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped Pointwise

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- The local field `K_q` of the place `ofFinite q`. -/
abbrev localFieldAt (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Type :=
  NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)

theorem henselEmb_equivariant (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
        ((e τ) ⟨(x : Ω), le_henselField k Ω K A x.2⟩ : Ω) = ((τ : K ≃ₐ[k] K) x : Ω))
    (φ : ↥(henselOverDecomp k Ω K A) →+*
        (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)))
    (hφ : ∀ x : ↥K, φ ⟨(x : Ω), le_henselField k Ω K A x.2⟩ =
        algebraMap ↥K (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)) x)
    (hfix : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
        (x : ↥(decompField k Ω A)),
        NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
            (NK.GlobalCFT.Place.ofFinite q) τ
            (φ ⟨(x : Ω), decompField_le_henselField k Ω K A x.2⟩)
          = φ ⟨(x : Ω), decompField_le_henselField k Ω K A x.2⟩) :
    ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
      (x : ↥(henselOverDecomp k Ω K A)),
      φ ((e τ) x) =
        NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) τ (φ x) := by
  classical
  intro τ x
  let f₁ : ↥(henselOverDecomp k Ω K A) →+*
      (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)) :=
    φ.comp (e τ).toRingEquiv.toRingHom
  let f₂ : ↥(henselOverDecomp k Ω K A) →+*
      (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)) :=
    (NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
      (NK.GlobalCFT.Place.ofFinite q) τ).toRingHom.comp φ
  have hLAmap : ∀ (σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
      (y : ↥K),
      NK.HassePrinciple.localAutHom (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) σ
        (algebraMap ↥K (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)) y)
      = algebraMap ↥K (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)) ((σ : K ≃ₐ[k] K) y) :=
    fun σ y => NK.HassePrinciple.localAut_algebraMap (K := k) (L := ↥K)
      (NK.GlobalCFT.Place.ofFinite q) σ y
  have hS : (↑(decompField k Ω A) ∪ (↑K : Set Ω)) ⊆ (henselField k Ω K A : Set Ω) := by
    rintro z (hz | hz)
    · exact decompField_le_henselField k Ω K A hz
    · exact le_henselField k Ω K A hz
  have hS_le : IntermediateField.adjoin k (↑(decompField k Ω A) ∪ (↑K : Set Ω))
      ≤ henselField k Ω K A := IntermediateField.adjoin_le_iff.mpr hS
  have hgen : (x : Ω) ∈ IntermediateField.adjoin k
      (↑(decompField k Ω A) ∪ (↑K : Set Ω)) := by
    have hy : (x : Ω) ∈ henselField k Ω K A := x.2
    rw [henselField_eq_sup k Ω K A] at hy
    exact hy
  have key : ∀ z ∈ IntermediateField.adjoin k (↑(decompField k Ω A) ∪ (↑K : Set Ω)),
      ∀ hz : z ∈ henselField k Ω K A, f₁ ⟨z, hz⟩ = f₂ ⟨z, hz⟩ := by
    intro z hz0
    refine IntermediateField.adjoin_induction (p := fun z _ =>
      ∀ hz : z ∈ henselField k Ω K A, f₁ ⟨z, hz⟩ = f₂ ⟨z, hz⟩)
      (mem := ?_) (algebraMap := ?_) (add := ?_) (inv := ?_) (mul := ?_) (h := hz0)
    · -- generators, `z ∈ k^h`
      intro z hzg hz
      change φ ((e τ) ⟨z, hz⟩) = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
        (NK.GlobalCFT.Place.ofFinite q) τ (φ ⟨z, hz⟩)
      rcases hzg with hzD | hzK
      · have h1 : (⟨z, hz⟩ : ↥(henselOverDecomp k Ω K A)) =
            ⟨z, decompField_le_henselField k Ω K A hzD⟩ := Subtype.ext rfl
        have h2 : (⟨z, decompField_le_henselField k Ω K A hzD⟩ :
              ↥(henselOverDecomp k Ω K A)) =
            algebraMap ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) ⟨z, hzD⟩ :=
          Subtype.ext rfl
        rw [h1, h2, AlgEquiv.commutes]
        exact (hfix τ ⟨z, hzD⟩).symm
      · -- generators, `z ∈ K`
        have h1 : (⟨z, hz⟩ : ↥(henselOverDecomp k Ω K A)) =
            ⟨(⟨z, hzK⟩ : ↥K), le_henselField k Ω K A hzK⟩ := Subtype.ext rfl
        have h2 : (e τ) ⟨(⟨z, hzK⟩ : ↥K), le_henselField k Ω K A hzK⟩ =
            ⟨(((τ : K ≃ₐ[k] K) ⟨z, hzK⟩ : K)),
              le_henselField k Ω K A ((τ : K ≃ₐ[k] K) ⟨z, hzK⟩).2⟩ :=
          Subtype.ext (he τ ⟨z, hzK⟩)
        have h3 : φ ⟨(⟨z, hzK⟩ : ↥K), le_henselField k Ω K A hzK⟩ =
            algebraMap ↥K (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q))
              ⟨z, hzK⟩ := hφ ⟨z, hzK⟩
        calc φ ((e τ) ⟨z, hz⟩)
            = φ ((e τ) ⟨(⟨z, hzK⟩ : ↥K), le_henselField k Ω K A hzK⟩) := by rw [h1]
          _ = φ ⟨(((τ : K ≃ₐ[k] K) ⟨z, hzK⟩ : K)),
                le_henselField k Ω K A ((τ : K ≃ₐ[k] K) ⟨z, hzK⟩).2⟩ := by rw [h2]
          _ = algebraMap ↥K (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q))
                ((τ : K ≃ₐ[k] K) ⟨z, hzK⟩) := hφ ((τ : K ≃ₐ[k] K) ⟨z, hzK⟩)
          _ = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
                (NK.GlobalCFT.Place.ofFinite q) τ
                (algebraMap ↥K (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q))
                  ⟨z, hzK⟩) := (hLAmap τ ⟨z, hzK⟩).symm
          _ = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
                (NK.GlobalCFT.Place.ofFinite q) τ
                (φ ⟨(⟨z, hzK⟩ : ↥K), le_henselField k Ω K A hzK⟩) := by rw [h3]
          _ = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
                (NK.GlobalCFT.Place.ofFinite q) τ (φ ⟨z, hz⟩) := by rw [h1]
    · -- constants
      intro c hz
      change φ ((e τ) ⟨algebraMap k Ω c, hz⟩) = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
        (NK.GlobalCFT.Place.ofFinite q) τ (φ ⟨algebraMap k Ω c, hz⟩)
      have h1 : (⟨algebraMap k Ω c, hz⟩ : ↥(henselOverDecomp k Ω K A)) =
          ⟨(algebraMap k ↥K c : ↥K), le_henselField k Ω K A (algebraMap k ↥K c).2⟩ :=
        Subtype.ext rfl
      have h2 : (e τ) ⟨(algebraMap k ↥K c : ↥K), le_henselField k Ω K A
            (algebraMap k ↥K c).2⟩ =
          ⟨(algebraMap k ↥K c : ↥K), le_henselField k Ω K A (algebraMap k ↥K c).2⟩ := by
        rw [show (⟨(algebraMap k ↥K c : ↥K), le_henselField k Ω K A
              (algebraMap k ↥K c).2⟩ : ↥(henselOverDecomp k Ω K A)) =
            algebraMap ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)
              (algebraMap k ↥(decompField k Ω A) c) from Subtype.ext rfl]
        exact AlgEquiv.commutes _ _
      rw [h1, h2, hφ]
      exact (congrArg (algebraMap ↥K (NK.GlobalCFT.Place.localField K
          (NK.GlobalCFT.Place.ofFinite q))) (AlgEquiv.commutes (τ : K ≃ₐ[k] K) c)).symm.trans
        ((hLAmap τ (algebraMap k ↥K c)).symm)
    · -- addition
      intro z w hz hw ihz ihw hz'
      change φ ((e τ) ⟨z + w, hz'⟩) = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
        (NK.GlobalCFT.Place.ofFinite q) τ (φ ⟨z + w, hz'⟩)
      have hihz : φ ((e τ) ⟨z, hS_le hz⟩) = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) τ (φ ⟨z, hS_le hz⟩) := ihz (hS_le hz)
      have hihw : φ ((e τ) ⟨w, hS_le hw⟩) = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) τ (φ ⟨w, hS_le hw⟩) := ihw (hS_le hw)
      rw [show (⟨z + w, hz'⟩ : ↥(henselOverDecomp k Ω K A)) =
        ⟨z, hS_le hz⟩ + ⟨w, hS_le hw⟩ from Subtype.ext rfl]
      simp only [map_add, hihz, hihw]
    · -- inverse
      intro z hz ihz hz'
      change φ ((e τ) ⟨z⁻¹, hz'⟩) = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
        (NK.GlobalCFT.Place.ofFinite q) τ (φ ⟨z⁻¹, hz'⟩)
      have hihz : φ ((e τ) ⟨z, hS_le hz⟩) = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) τ (φ ⟨z, hS_le hz⟩) := ihz (hS_le hz)
      rw [show (⟨z⁻¹, hz'⟩ : ↥(henselOverDecomp k Ω K A)) = (⟨z, hS_le hz⟩)⁻¹ from
        Subtype.ext rfl]
      simp only [map_inv₀, hihz]
    · -- multiplication
      intro z w hz hw ihz ihw hz'
      change φ ((e τ) ⟨z * w, hz'⟩) = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
        (NK.GlobalCFT.Place.ofFinite q) τ (φ ⟨z * w, hz'⟩)
      have hihz : φ ((e τ) ⟨z, hS_le hz⟩) = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) τ (φ ⟨z, hS_le hz⟩) := ihz (hS_le hz)
      have hihw : φ ((e τ) ⟨w, hS_le hw⟩) = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) τ (φ ⟨w, hS_le hw⟩) := ihw (hS_le hw)
      rw [show (⟨z * w, hz'⟩ : ↥(henselOverDecomp k Ω K A)) =
        ⟨z, hS_le hz⟩ * ⟨w, hS_le hw⟩ from Subtype.ext rfl]
      simp only [map_mul, hihz, hihw]
  exact key (x : Ω) hgen x.2

end

end Work.SSGRoute.E1aClean
