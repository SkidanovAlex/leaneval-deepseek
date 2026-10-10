import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.isT1Place_of_isConjPlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

/-!
# Transfer of the `T¹`-place clause along conjugation of a place

This is the variant of `Work.SSGRoute.clauseData_conj_transfer` in which the first hypothesis
`hI` (and the first conclusion) are additionally restricted to the `T¹`-places: the clause

  `IsT1Place p K A → ∀ σ ∈ D_A, σ ∈ G_K → ψ σ = 1`

is transferred from `A` to any `G_ℚ`-conjugate place `B = g · A`.  The point is that (a) `T¹`-ness
is conjugation invariant (`Work.SSGRoute.isT1Place_of_isConjPlace`) and (b) all the local data
(decomposition group, inertia, `G_K`-membership) is transported across `g` by conjugation, while
`ψ`/`ρ` are group homomorphisms, so the value of `ψ` on a conjugate of an element is the conjugate
of the value.

Concretely, for `B = g · A`:

* `D_B = g D_A g⁻¹` (`Work.SSGRoute.decomp_conj`), `I_B = g I_A g⁻¹`
  (`Work.SSGRoute.isInertia_conj`), and `G_K` is normal in `G_ℚ`
  (`Work.SSGRoute.fixingSubgroup_normal_of_normal`), so conjugation moves each of the predicates
  `σ ∈ D_A`, `σ ∈ I_A`, `σ ∈ G_K` back and forth;
* the image `ψ(D_B) = (ψ g) · ψ(D_A) · (ψ g)⁻¹` is a conjugate of `ψ(D_A)`, hence cyclic as soon
  as `ψ(D_A)` is.
-/

/-- The value of a group homomorphism on a conjugate: `f (g x g⁻¹) = f g · f x · (f g)⁻¹`. -/
private theorem map_conj_apply_aux {G H : Type*} [Group G] [Group H] (f : G →* H) (g x : G) :
    f (g * x * g⁻¹) = f g * f x * (f g)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

/-- The image of a cyclic subgroup under a group homomorphism is cyclic. -/
private theorem isCyclic_map_aux {G H : Type*} [Group G] [Group H] (f : G →* H)
    (S : Subgroup G) (h : IsCyclic ↥S) : IsCyclic ↥(S.map f) := by
  let F : ↥S →* ↥(S.map f) :=
    { toFun := fun x => ⟨f x.1, Subgroup.mem_map_of_mem f x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a.1 b.1) }
  have hsurj : Function.Surjective F := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact isCyclic_of_surjective F hsurj

/-- The image under `ψ` of the decomposition group of `g · A` is the image of `ψ(D_A)` under the
inner automorphism `conj (ψ g)`: `ψ(D_B) = (ψ g) · ψ(D_A) · (ψ g)⁻¹`. -/
private theorem map_decomp_smul_eq_aux (A : ValuationSubring QBar) (g : GalQ) {H : Type} [Group H]
    (ψ : GalQ →* H) :
    (decomp ℚ (g • A)).map ψ
      = ((decomp ℚ A).map ψ).map (MulAut.conj (ψ g)).toMonoidHom := by
  rw [decomp_conj, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  change ψ ((MulAut.conj g) x) = (MulAut.conj (ψ g)) (ψ x)
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem clauseData_conj_transfer_T1 (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] {n i j : ℕ}
    (ψ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (ρ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (A B : ValuationSubring SSGRoute.QBar) (hconj : SSGRoute.IsConjPlace ℚ A B)
    (hI : SSGRoute.IsT1Place p K A → ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1)
    (hII : (∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → σ ∈ K.fixingSubgroup → ψ σ = 1) ∨
      ((∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
        ((∀ σ ∈ SSGRoute.decomp ℚ A, ρ σ = 1) ∨
          (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
            ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ)))) :
    (SSGRoute.IsT1Place p K B → ∀ σ ∈ SSGRoute.decomp ℚ B, σ ∈ K.fixingSubgroup → ψ σ = 1) ∧
      ((∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ B σ → σ ∈ K.fixingSubgroup → ψ σ = 1) ∨
        ((∀ σ ∈ SSGRoute.decomp ℚ B, σ ∈ K.fixingSubgroup) ∧
          ((∀ σ ∈ SSGRoute.decomp ℚ B, ρ σ = 1) ∨
            (IsCyclic ((SSGRoute.decomp ℚ B).map ψ) ∧
              ∀ σ ∈ SSGRoute.decomp ℚ B, ∃ τ, SSGRoute.IsInertia ℚ B τ ∧ ψ τ = ψ σ)))) := by
  obtain ⟨g, rfl⟩ := hconj
  have hNorm : K.fixingSubgroup.Normal := fixingSubgroup_normal_of_normal K
  -- membership in `D_{g · A}` is conjugation by `g`
  have hdecomp : ∀ σ : GalQ, σ ∈ decomp ℚ (g • A) ↔ g⁻¹ * σ * g ∈ decomp ℚ A := by
    intro σ
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      rw [mul_smul, mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
    · intro h
      have h2 : g • ((g⁻¹ * σ * g) • A) = g • A := by rw [h]
      rw [← mul_smul] at h2
      rw [show g * (g⁻¹ * σ * g) = σ * g from by group, mul_smul] at h2
      exact h2
  -- membership in `G_K` is invariant under conjugation, `G_K` being normal
  have hfix : ∀ σ : GalQ, g⁻¹ * σ * g ∈ K.fixingSubgroup ↔ σ ∈ K.fixingSubgroup :=
    fun σ => conj_mem_iff hNorm g⁻¹ σ
  have hconjm : ∀ σ : GalQ, g * (g⁻¹ * σ * g) * g⁻¹ = σ := fun σ => by group
  constructor
  · -- clause (i): `T¹`-places
    intro hB σ hσ hσfix
    have hA : IsT1Place p K A :=
      isT1Place_of_isConjPlace p K ⟨g⁻¹, by rw [smul_smul, inv_mul_cancel, one_smul]⟩ hB
    have hmem : g⁻¹ * σ * g ∈ decomp ℚ A := (hdecomp σ).mp hσ
    have hfix' : g⁻¹ * σ * g ∈ K.fixingSubgroup := (hfix σ).mpr hσfix
    have h1 : ψ (g⁻¹ * σ * g) = 1 := hI hA _ hmem hfix'
    rw [← hconjm σ, map_conj_apply_aux, h1, mul_one, mul_inv_cancel]
  · -- clause (ii)
    rcases hII with hin | ⟨hAd, hrest⟩
    · -- inertia clause
      refine Or.inl ?_
      intro σ hσin hσfix
      have hinA : IsInertia ℚ A (g⁻¹ * σ * g) :=
        (isInertia_conj A g (g⁻¹ * σ * g)).mp (by rwa [← hconjm σ] at hσin)
      have hfixA : g⁻¹ * σ * g ∈ K.fixingSubgroup := (hfix σ).mpr hσfix
      have h1 : ψ (g⁻¹ * σ * g) = 1 := hin _ hinA hfixA
      rw [← hconjm σ, map_conj_apply_aux, h1, mul_one, mul_inv_cancel]
    · refine Or.inr ⟨?_, ?_⟩
      · -- complete splitting
        intro σ hσ
        have hmem : g⁻¹ * σ * g ∈ decomp ℚ A := (hdecomp σ).mp hσ
        exact (hfix σ).mp (hAd _ hmem)
      · rcases hrest with hρ | ⟨hcyc, hex⟩
        · -- `ρ` vanishes on `D_A`
          refine Or.inl ?_
          intro σ hσ
          have hmem : g⁻¹ * σ * g ∈ decomp ℚ A := (hdecomp σ).mp hσ
          have h1 : ρ (g⁻¹ * σ * g) = 1 := hρ _ hmem
          rw [← hconjm σ, map_conj_apply_aux, h1, mul_one, mul_inv_cancel]
        · -- cyclicity and dominance by inertia
          refine Or.inr ⟨?_, ?_⟩
          · rw [map_decomp_smul_eq_aux A g ψ]
            exact isCyclic_map_aux _ _ hcyc
          · intro σ hσ
            have hmem : g⁻¹ * σ * g ∈ decomp ℚ A := (hdecomp σ).mp hσ
            obtain ⟨τ, hτin, hτψ⟩ := hex _ hmem
            refine ⟨g * τ * g⁻¹, (isInertia_conj A g τ).mpr hτin, ?_⟩
            rw [map_conj_apply_aux, hτψ, ← map_conj_apply_aux, hconjm]

end Work.SSGRoute
