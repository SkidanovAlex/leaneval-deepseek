import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.EscapeCoreLib.baseChange_over_K
import Submission.Work.SSGRoute.N2v2.kummerField_le_of_vanishes_on_fixingSubgroup
import Submission.Work.SSGRoute.myv2.Sep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option maxHeartbeats 1000000

/-!
# The final separation (P-E): Kummer characters of `M ⊓ (L₁L₂)` determine the automorphism

If `Gal(M/↥K)` is a finite abelian group of exponent `p` and a global automorphism `α` of `M` is
killed by every Kummer character `χ_c` with `KummerField c ≤ M ⊓ baseChange K (L₁ ⊔ L₂)`, then `α`
fixes `M ⊓ (L₁ ⊔ L₂)` pointwise.  The proof is the character separation of
`Work.SSGRoute.N2v2.mem_of_forall_monoidHom_eq_one` together with Kummer surjectivity
(`kummerCharZMod_surjective_levelK`) at the level `M`.
-/

open scoped NumberField

namespace Work.SSGRoute.N2v2

open NumberField IsDedekindDomain

theorem alpha_fixes_of_kummerChars
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [IsMulCommutative (↥M ≃ₐ[↥K] ↥M)]
    (hexpM : ∀ g : (↥M ≃ₐ[↥K] ↥M), g ^ p = 1)
    (α : ↥M ≃ₐ[↥K] ↥M)
    (hmain : ∀ c : (↥K)ˣ,
      NK.LocalAnabelian.kummerField (K' := Ω) p c ≤
        M ⊓ Work.SSGRoute.EscapeCoreLib.baseChange K (L₁ ⊔ L₂) (hKL₁.trans le_sup_left) →
      ∀ σ : Ω ≃ₐ[↥K] Ω, AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ = α →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ = 0) :
    ∀ x : ↥M, ((x : Ω) ∈ (L₁ ⊔ L₂)) → α x = x := by
  classical
  haveI hAlgK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hSepK : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  haveI hFinM : Finite (↥M ≃ₐ[↥K] ↥M) := Finite.of_fintype _
  letI hMcg : CommGroup (↥M ≃ₐ[↥K] ↥M) :=
    { mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  set hK : K ≤ L₁ ⊔ L₂ := hKL₁.trans le_sup_left with hKdef
  set N' : IntermediateField ↥K Ω := Work.SSGRoute.EscapeCoreLib.baseChange K (L₁ ⊔ L₂) hK
    with hN'def
  set F₀ : IntermediateField ↥K Ω := M ⊓ N' with hF₀def
  -- the subfield of `↥M` cut out by `F₀`
  set FM : IntermediateField ↥K ↥M :=
    F₀.comap (IsScalarTower.toAlgHom ↥K ↥M Ω) with hFMdef
  intro x hx
  have hxmem : x ∈ FM := by
    show (IsScalarTower.toAlgHom ↥K ↥M Ω) x ∈ F₀
    rw [show (IsScalarTower.toAlgHom ↥K ↥M Ω) x = (x : Ω) from rfl, hF₀def,
      IntermediateField.mem_inf]
    exact ⟨x.2, (Work.SSGRoute.EscapeCoreLib.mem_baseChange K (L₁ ⊔ L₂) hK).mpr hx⟩
  suffices hfix : α ∈ FM.fixingSubgroup by
    exact (IntermediateField.mem_fixingSubgroup_iff FM α).mp hfix x hxmem
  -- character separation
  refine mem_of_forall_monoidHom_eq_one hexpM (show Subgroup (↥M ≃ₐ[↥K] ↥M) from
    FM.fixingSubgroup) (fun ψ hψ => ?_)
  -- the `k`-level additive function defined by `ψ`
  let z : (Ω ≃ₐ[k] Ω) → ZMod p := fun σ =>
    if hσ : σ ∈ K.fixingSubgroup then
      (ψ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))).toAdd
    else 0
  have hzapply : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), z σ =
      (ψ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))).toAdd := by
    intro σ hσ
    simp only [z, dif_pos hσ]
  have hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h := by
    intro g hg h hh
    have key : (⟨g * h, K.fixingSubgroup.mul_mem hg hh⟩ : ↥(K.fixingSubgroup)) =
        ⟨g, hg⟩ * ⟨h, hh⟩ := Subtype.ext rfl
    rw [hzapply (g * h) (K.fixingSubgroup.mul_mem hg hh), hzapply g hg, hzapply h hh, key,
      map_mul (IntermediateField.fixingSubgroupEquiv K),
      map_mul (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M),
      map_mul ψ, toAdd_mul]
  -- local constancy: `z` factors through `M`
  -- local constancy: `z` factors through the finite group `Gal(M/↥K)`
  -- a finite `k`-level field `L` containing `M`
  let b : Module.Basis (Fin (Module.finrank ↥K ↥M)) ↥K ↥M := Module.finBasis ↥K ↥M
  let S : Set Ω := Set.range (fun i => ((b i : ↥M) : Ω))
  haveI hSfin : Finite ↑S := Set.finite_range _
  let N : IntermediateField k Ω := IntermediateField.adjoin k S
  haveI hNfin : FiniteDimensional k ↥N :=
    IntermediateField.finiteDimensional_adjoin (K := k) (L := Ω) (S := S)
      (fun x _ => (Algebra.IsAlgebraic.isIntegral (K := k) (A := Ω)).isIntegral x)
  let L : IntermediateField k Ω := K ⊔ N
  haveI hLfin : FiniteDimensional k ↥L := IntermediateField.finiteDimensional_sup K N
  have hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z := by
    refine ⟨L.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen L, ?_⟩
    intro gg hg u hu huH
    have huK : u ∈ K.fixingSubgroup := huH
    have hcoeeq : (((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩) : Ω → Ω) = ⇑u :=
      funext fun _ => rfl
    have hures : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M
        ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩) = 1 := by
      have hfixb : ∀ i, u (((b i : ↥M) : Ω)) = ((b i : ↥M) : Ω) := fun i =>
        (IntermediateField.mem_fixingSubgroup_iff L u).mp hu _
          ((le_sup_right : N ≤ L) (IntermediateField.subset_adjoin k S (Set.mem_range_self i)))
      refine AlgEquiv.ext fun y => ?_
      have hspan : Submodule.span ↥K (Set.range b) ≤
          LinearMap.eqLocus (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M
            ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩)).toLinearMap LinearMap.id := by
        rw [Submodule.span_le]
        rintro w ⟨i, rfl⟩
        show (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M
          ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩)) (b i) = b i
        apply Subtype.ext
        rw [AlgEquiv.restrictNormalHom_apply, hcoeeq]
        exact hfixb i
      have hymem : y ∈ Submodule.span ↥K (Set.range b) := by
        rw [b.span_eq]; exact Submodule.mem_top
      have := hspan hymem
      rw [AlgEquiv.one_apply]
      exact this
    have key : (⟨gg * u, K.fixingSubgroup.mul_mem hg huK⟩ : ↥(K.fixingSubgroup)) =
        ⟨gg, hg⟩ * ⟨u, huK⟩ := Subtype.ext rfl
    rw [hzapply (gg * u) (K.fixingSubgroup.mul_mem hg huK), hzapply gg hg, key,
      map_mul (IntermediateField.fixingSubgroupEquiv K),
      map_mul (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M), hures, mul_one]
  -- Kummer surjectivity at the level `↥K`
  obtain ⟨β, hβ⟩ := Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
    p k Ω K ζ hζ z hzadd hzloc
  -- `KummerField β ≤ F₀`
  have hβle : NK.LocalAnabelian.kummerField (K' := Ω) p β ≤ F₀ := by
    refine Work.SSGRoute.N2v2.kummerField_le_of_vanishes_on_fixingSubgroup p k Ω K ζ hζ β F₀ ?_
    intro σ hσ
    let σk : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm σ
    have hσkK : (σk : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := σk.2
    have hσkeq : (IntermediateField.fixingSubgroupEquiv K)
        ⟨(σk : Ω ≃ₐ[k] Ω), hσkK⟩ = σ :=
      MulEquiv.apply_symm_apply _ _
    have hβapp := hβ (σk : Ω ≃ₐ[k] Ω) hσkK
    have hres_mem : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ ∈ FM.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      have hzF₀ : ((z : ↥M) : Ω) ∈ F₀ := by
        have := hz
        rw [hFMdef] at this
        exact this
      apply Subtype.ext
      rw [AlgEquiv.restrictNormalHom_apply]
      exact (IntermediateField.mem_fixingSubgroup_iff F₀ σ).mp hσ _ hzF₀
    have hψ1 : ψ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ) = 1 := hψ hres_mem
    have key : z (σk : Ω ≃ₐ[k] Ω) =
        (ψ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ)).toAdd := by
      rw [hzapply (σk : Ω ≃ₐ[k] Ω) hσkK, hσkeq]
    rw [hσkeq] at hβapp
    rw [← hβapp, key, hψ1]
    simp
  -- lift `α`
  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := M) (E := Ω) α
  let σk₀ : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm σ₀
  have hσk₀K : (σk₀ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := σk₀.2
  have hσk₀eq : (IntermediateField.fixingSubgroupEquiv K)
      ⟨(σk₀ : Ω ≃ₐ[k] Ω), hσk₀K⟩ = σ₀ :=
    MulEquiv.apply_symm_apply _ _
  have hval : ψ α = Multiplicative.ofAdd
      (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ β σ₀) := by
    have h1 := hβ (σk₀ : Ω ≃ₐ[k] Ω) hσk₀K
    rw [hσk₀eq] at h1
    have h2 : z (σk₀ : Ω ≃ₐ[k] Ω) =
        (ψ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ₀)).toAdd := by
      rw [hzapply (σk₀ : Ω ≃ₐ[k] Ω) hσk₀K, hσk₀eq]
    have h1 : z (σk₀ : Ω ≃ₐ[k] Ω) = Work.SSGRoute.kummerCharZMod
        (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ β σ₀ := by
      have := hβ (σk₀ : Ω ≃ₐ[k] Ω) hσk₀K
      rwa [hσk₀eq] at this
    calc ψ α = ψ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ₀) := by rw [hσ₀]
      _ = Multiplicative.ofAdd
            ((ψ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ₀)).toAdd) :=
          (ofAdd_toAdd _).symm
      _ = Multiplicative.ofAdd (z (σk₀ : Ω ≃ₐ[k] Ω)) := by rw [← h2]
      _ = Multiplicative.ofAdd (Work.SSGRoute.kummerCharZMod
            (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ β σ₀) := by rw [h1]
  rw [hval, hmain β hβle σ₀ hσ₀]
  simp

end Work.SSGRoute.N2v2
