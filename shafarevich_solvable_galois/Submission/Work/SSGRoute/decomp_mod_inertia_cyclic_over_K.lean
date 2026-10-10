import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.decomp_mod_inertia_cyclic
import Submission.Work.SSGRoute.sha2_restrict_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

namespace Work.SSGRoute

section Transport

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- An element `g` of `Gal(Ω/↥K)` lies in the image under `K.fixingSubgroup ≃* Gal(Ω/↥K)` of the
trace `U ⊓ G_K` of a subgroup `U ≤ G_k` if and only if `toGkHom K g ∈ U`. -/
lemma mem_map_fixingSubgroupEquiv_comap_subtype (K : IntermediateField k Ω)
    (U : Subgroup (Ω ≃ₐ[k] Ω)) (g : Ω ≃ₐ[↥K] Ω) :
    g ∈ (U.comap (Subgroup.subtype K.fixingSubgroup)).map
        (IntermediateField.fixingSubgroupEquiv K).toMonoidHom ↔ toGkHom K g ∈ U := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hh' : (h : Ω ≃ₐ[k] Ω) ∈ U := hh
    have h2 : (toGkHom K) ((IntermediateField.fixingSubgroupEquiv K).toMonoidHom h) =
        (h : Ω ≃ₐ[k] Ω) := toGkHom_fixingSubgroupEquiv K h
    rw [h2]
    exact hh'
  · intro hg
    refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm g, ?_,
      (IntermediateField.fixingSubgroupEquiv K).apply_symm_apply g⟩
    have hg' : (((IntermediateField.fixingSubgroupEquiv K).symm g : ↥(K.fixingSubgroup)) :
        Ω ≃ₐ[k] Ω) ∈ U := hg
    exact hg'

end Transport

-- Over-`K` form of `Work.SSGRoute.decomp_mod_inertia_cyclic`: apply the base statement at the
-- number field `K` and transport through `IntermediateField.fixingSubgroupEquiv K`
-- (`decomp ↥K B` corresponds to `decomp k B ⊓ K.fixingSubgroup`, and `IsInertia ↥K B σ` to
-- `IsInertia k B σ ∧ σ ∈ K.fixingSubgroup`).  Needed hypotheses:
-- `NumberField ↥K` (`NumberField.of_module_finite`), `IsAlgClosure ↥K Ω` (build from the
-- `IsAlgClosure k Ω` instance: `IsAlgClosed Ω` and `Algebra.IsAlgebraic ↥K Ω`), and
-- `IsFinPlace ↥K B` (immediate from `hB : IsFinPlace k B`).
theorem decomp_mod_inertia_cyclic_over_K (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (V : Subgroup (Ω ≃ₐ[k] Ω)) (hV : IsOpen (V : Set (Ω ≃ₐ[k] Ω)))
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (hI : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → σ ∈ K.fixingSubgroup →
      σ ∈ V ⊓ SSGRoute.decomp k B ⊓ K.fixingSubgroup) :
    ∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V ⊓ SSGRoute.decomp k B ⊓ K.fixingSubgroup := by
  classical
  -- `↥K` is again a number field and `Ω` is still an algebraic closure of it
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hACK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  -- a finite place over `k` is a finite place over `K`
  have hBK : SSGRoute.IsFinPlace ↥K B := by
    intro htop
    apply hB
    rw [eq_top_iff]
    intro r _
    rw [ValuationSubring.mem_comap]
    have h1 : algebraMap ↥K Ω (algebraMap k K r) ∈ B := by
      have h2 : algebraMap k K r ∈ B.comap (algebraMap ↥K Ω) := by rw [htop]; trivial
      rwa [ValuationSubring.mem_comap] at h2
    rwa [IsScalarTower.algebraMap_apply k K Ω]
  -- the transported subgroups
  let A : Subgroup ↥(K.fixingSubgroup) := V.comap (Subgroup.subtype K.fixingSubgroup)
  let C : Subgroup ↥(K.fixingSubgroup) :=
    (V ⊓ SSGRoute.decomp k B).comap (Subgroup.subtype K.fixingSubgroup)
  let VK : Subgroup (Ω ≃ₐ[↥K] Ω) :=
    A.map (IntermediateField.fixingSubgroupEquiv K).toMonoidHom
  let WK : Subgroup (Ω ≃ₐ[↥K] Ω) :=
    C.map (IntermediateField.fixingSubgroupEquiv K).toMonoidHom
  have hVKopen : IsOpen (VK : Set (Ω ≃ₐ[↥K] Ω)) := by
    have hAopen : IsOpen (A : Set ↥(K.fixingSubgroup)) := by
      rw [show (A : Set ↥(K.fixingSubgroup)) =
          (Subtype.val : ↥(K.fixingSubgroup) → Ω ≃ₐ[k] Ω) ⁻¹' (V : Set (Ω ≃ₐ[k] Ω)) from by
        ext x
        simp only [A, SetLike.mem_coe, Set.mem_preimage, Subgroup.mem_comap,
          Subgroup.subtype_apply]]
      exact hV.preimage (continuous_subtype_val :
        Continuous (Subtype.val : ↥(K.fixingSubgroup) → Ω ≃ₐ[k] Ω))
    have hmap := isOpen_map_fixingSubgroupEquiv K A hAopen
    simpa only [VK, A] using hmap
  have hWKeq : WK = VK ⊓ SSGRoute.decomp ↥K B := by
    ext g
    rw [Subgroup.mem_inf]
    have h1 := mem_map_fixingSubgroupEquiv_comap_subtype K V g
    have h2 := mem_map_fixingSubgroupEquiv_comap_subtype K (V ⊓ SSGRoute.decomp k B) g
    have h3 := toGkHom_mem_decomp K B g
    exact ⟨fun hg => ⟨h1.mpr (h2.mp hg).1, h3.mp (h2.mp hg).2⟩,
      fun hg => h2.mpr ⟨h1.mp hg.1, h3.mpr hg.2⟩⟩
  -- the inertia hypothesis, transported
  have hI' : ∀ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia ↥K B σ → σ ∈ WK := by
    intro σ hσ
    rw [hWKeq]
    refine ⟨?_, hσ.1⟩
    refine (mem_map_fixingSubgroupEquiv_comap_subtype K V σ).mpr ?_
    have hinert : SSGRoute.IsInertia k B (toGkHom K σ) := by
      refine ⟨(toGkHom_mem_decomp K B σ).mpr hσ.1, ?_⟩
      intro x hx
      simpa only [toGkHom_apply] using hσ.2 x hx
    exact (hI (toGkHom K σ) hinert (Subtype.mem _)).1.1
  -- the base statement over `↥K`
  obtain ⟨g, hg, hgprop⟩ :=
    decomp_mod_inertia_cyclic ↥K Ω B hBK WK ⟨VK, hVKopen, hWKeq⟩ hI'
  refine ⟨toGkHom K g, ⟨(toGkHom_mem_decomp K B g).mpr hg, Subtype.mem _⟩, ?_⟩
  intro δ hδ
  set δ' : Ω ≃ₐ[↥K] Ω := (IntermediateField.fixingSubgroupEquiv K) ⟨δ, hδ.2⟩ with hδ'def
  have htoGk : toGkHom K δ' = δ := by
    rw [hδ'def]
    exact toGkHom_fixingSubgroupEquiv K ⟨δ, hδ.2⟩
  have hδ'dec : δ' ∈ SSGRoute.decomp ↥K B :=
    (toGkHom_mem_decomp K B δ').mp (by rw [htoGk]; exact hδ.1)
  obtain ⟨m, hm⟩ := hgprop δ' hδ'dec
  refine ⟨m, ?_⟩
  have hfin : toGkHom K (δ'⁻¹ * g ^ m) ∈ V ⊓ SSGRoute.decomp k B ⊓ K.fixingSubgroup :=
    ⟨(mem_map_fixingSubgroupEquiv_comap_subtype K (V ⊓ SSGRoute.decomp k B)
        (δ'⁻¹ * g ^ m)).mp hm, Subtype.mem _⟩
  rwa [map_mul, map_inv, map_zpow, htoGk] at hfin

end Work.SSGRoute
