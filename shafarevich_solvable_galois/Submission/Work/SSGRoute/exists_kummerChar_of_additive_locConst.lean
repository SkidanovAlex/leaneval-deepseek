import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.exists_kummerCharacter_of_zmod
import Submission.Work.SSGRoute.grunwald_surjective_two
import Submission.Work.SSGRoute.isOpen_map_fixingSubgroupEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped Topology Pointwise

/-- **Naturality of `zr` under the algebra map.**  The `zr`-isomorphism of `ZMod 2` with the
square roots of unity commutes with the algebra map `F → E`. -/
lemma units_map_zr_eq {F E : Type*} [Field F] [Field E] [Algebra F E]
    {ζ : F} (hζ : IsPrimitiveRoot ζ 2) (k : Multiplicative (ZMod 2)) :
    Units.map (algebraMap F E)
        (((zr (isPrimitiveRoot_primRootUnit (F := F) (p := 2) hζ) k :
            ↥(rootsOfUnity 2 F)) : Fˣ))
      = ((zr (isPrimitiveRoot_mappedRoot (E := E) (p := 2) hζ) k :
            ↥(rootsOfUnity 2 E)) : Eˣ) := by
  rw [zr_apply_toAdd (isPrimitiveRoot_primRootUnit (F := F) (p := 2) hζ) k,
    zr_apply_toAdd (isPrimitiveRoot_mappedRoot (E := E) (p := 2) hζ) k, map_zpow]
  rfl

/-- **The Kummer correspondence for additive, locally constant cochains on `G_K`.**  Every cochain
`z : G_k → 𝔽₂` which is additive on `G_K` and locally constant on `G_K` is the global Kummer
character of some `a ∈ Kˣ`. -/
theorem exists_kummerChar_of_additive_locConst
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (z : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hz : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hzc : SSGRoute.IsLocConstOn K.fixingSubgroup z) :
    ∃ a : (↥K)ˣ, ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      z σ = Work.SSGRoute.kummerChar (Ω := Ω) ζ hζ a
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) := by
  classical
  -- `z` vanishes at `1` (it is `2`-torsion)
  have hz_one : z 1 = 0 := by
    have h := hz 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    simp only [mul_one] at h
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h, ← two_mul, h2, zero_mul]
  -- the additive character on `G_K`, first as a homomorphism on `K.fixingSubgroup`
  let f : ↥(K.fixingSubgroup) →* Multiplicative (ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd (z g)
      map_one' := by simp [hz_one]
      map_mul' := fun g h => by
        show Multiplicative.ofAdd (z (g * h)) =
          Multiplicative.ofAdd (z g) * Multiplicative.ofAdd (z h)
        rw [hz g g.2 h h.2, ofAdd_add] }
  -- the kernel of `f` is open: it contains the traces of an open subgroup of `G_k`
  have hopen_f : IsOpen (f.ker : Set ↥(K.fixingSubgroup)) := by
    obtain ⟨U, hUopen, hU⟩ := hzc
    refine Subgroup.isOpen_of_mem_nhds f.ker (g := 1) ?_
    refine Filter.mem_of_superset
      ((hUopen.preimage continuous_subtype_val).mem_nhds ?_) ?_
    · simpa using U.one_mem
    · intro u hu
      show Multiplicative.ofAdd (z (u : Ω ≃ₐ[k] Ω)) = 1
      have h0 : z (u : Ω ≃ₐ[k] Ω) = 0 := by
        have h := hU 1 (Subgroup.one_mem _) (u : Ω ≃ₐ[k] Ω) hu u.2
        simpa [hz_one] using h
      simp [h0]
  -- transport to `G_K = Gal(Ω/K)`
  let zK : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod 2) :=
    f.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom
  have hker_map : (zK.ker : Subgroup (Ω ≃ₐ[K] Ω)) =
      f.ker.map (IntermediateField.fixingSubgroupEquiv K).toMonoidHom := by
    ext σ
    rw [MonoidHom.mem_ker, Subgroup.mem_map]
    constructor
    · intro hσ
      exact ⟨(IntermediateField.fixingSubgroupEquiv K).symm σ, hσ,
        (IntermediateField.fixingSubgroupEquiv K).apply_symm_apply σ⟩
    · rintro ⟨x, hx, hxσ⟩
      rw [← hxσ]
      show f ((IntermediateField.fixingSubgroupEquiv K).symm
        ((IntermediateField.fixingSubgroupEquiv K) x)) = 1
      rw [MulEquiv.symm_apply_apply]
      exact hx
  have hopen_zK : IsOpen (zK.ker : Set (Ω ≃ₐ[K] Ω)) := by
    have h := isOpen_map_fixingSubgroupEquiv K f.ker hopen_f
    have hset : ((f.ker.map (IntermediateField.fixingSubgroupEquiv K).toMonoidHom :
        Subgroup (Ω ≃ₐ[K] Ω)) : Set (Ω ≃ₐ[K] Ω)) = (zK.ker : Set (Ω ≃ₐ[K] Ω)) := by
      rw [hker_map]
    rwa [hset] at h
  -- the `μ₂`-valued character
  let zrK : Multiplicative (ZMod 2) ≃* ↥(rootsOfUnity 2 ↥K) :=
    zr (isPrimitiveRoot_primRootUnit (F := ↥K) (p := 2) hζ)
  let ω : (Ω ≃ₐ[K] Ω) →* ↥(rootsOfUnity 2 ↥K) := zrK.toMonoidHom.comp zK
  have hopen_ω : IsOpen (ω.ker : Set (Ω ≃ₐ[K] Ω)) := by
    have hkerω : (ω.ker : Subgroup (Ω ≃ₐ[K] Ω)) = zK.ker := by
      ext σ
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      show zrK (zK σ) = 1 ↔ zK σ = 1
      constructor
      · intro h
        have h' : zrK (zK σ) = zrK 1 := by rw [h, map_one]
        exact zrK.injective h'
      · intro h; rw [h, map_one]
    rw [show (ω.ker : Set (Ω ≃ₐ[K] Ω)) = (zK.ker : Set (Ω ≃ₐ[K] Ω)) from by rw [hkerω]]
    exact hopen_zK
  -- realisation of the character by a Kummer resolvent
  haveI hsepK : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  obtain ⟨γ, hγmem, hγdiv⟩ :=
    kummer_character_realization_inf (U := ↥K) (L := Ω) (n := 2) (by norm_num) ω hopen_ω
  -- `γ ^ 2 = algebraMap x` for some `x ∈ Kˣ`
  obtain ⟨x, hx⟩ := hγmem
  have hγ0 : γ ≠ 0 := by
    have h1 : γ / γ = 1 := by simpa using hγdiv 1
    intro h0
    rw [h0, div_zero] at h1
    exact zero_ne_one h1
  have hx0 : x ≠ 0 := by
    intro h0
    refine hγ0 ?_
    have h2 : γ * γ = 0 := by rw [← pow_two, ← hx, h0, map_zero]
    exact (mul_eq_zero.mp h2).elim id id
  let a : (↥K)ˣ := Units.mk0 x hx0
  let γu : Ωˣ := Units.mk0 γ hγ0
  have hγu : γu ^ 2 = Units.map (algebraMap ↥K Ω) a := by
    apply Units.ext
    show γ ^ 2 = (algebraMap ↥K Ω) x
    exact hx.symm
  refine ⟨a, ?_⟩
  intro σ hσ
  set σK : Ω ≃ₐ[K] Ω := (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ with hσK
  have hω_apply : ∀ τ : Ω ≃ₐ[K] Ω, ω τ = zrK (zK τ) := fun τ => rfl
  have hzKσ : zK σK = Multiplicative.ofAdd (z σ) := by
    show f ((IntermediateField.fixingSubgroupEquiv K).symm σK) = Multiplicative.ofAdd (z σ)
    rw [hσK, MulEquiv.symm_apply_apply]
    rfl
  have hratio : Work.Kummer.kummerRatio σK γu
      = Units.map (algebraMap ↥K Ω) (((ω σK : ↥(rootsOfUnity 2 ↥K)) : (↥K)ˣ)) := by
    apply Units.ext
    rw [Work.Kummer.kummerRatio_coe, Units.coe_map]
    show (σK : Ω → Ω) γ / γ =
      algebraMap ↥K Ω (((ω σK : ↥(rootsOfUnity 2 ↥K)) : (↥K)ˣ) : ↥K)
    exact hγdiv σK
  rw [Work.SSGRoute.kummerChar_apply]
  rw [kummerIdx_congr 2 hζ a (kummerSqrt_pow (Ω := Ω) a) hγu σK]
  have hkey : (zr (isPrimitiveRoot_mappedRoot (E := Ω) (p := 2) hζ)
        (Multiplicative.ofAdd (kummerIdx 2 hζ a γu hγu σK)) : Ωˣ)
      = (zr (isPrimitiveRoot_mappedRoot (E := Ω) (p := 2) hζ)
        (Multiplicative.ofAdd (z σ)) : Ωˣ) := by
    rw [← kummerIdx_spec 2 hζ a γu hγu σK, hratio, hω_apply σK, hzKσ]
    exact units_map_zr_eq (E := Ω) hζ (Multiplicative.ofAdd (z σ))
  have hfin : Multiplicative.ofAdd (kummerIdx 2 hζ a γu hγu σK)
      = Multiplicative.ofAdd (z σ) :=
    (zr (isPrimitiveRoot_mappedRoot (E := Ω) (p := 2) hζ)).injective (Subtype.ext hkey)
  exact (congrArg Multiplicative.toAdd hfin).symm

end Work.SSGRoute
