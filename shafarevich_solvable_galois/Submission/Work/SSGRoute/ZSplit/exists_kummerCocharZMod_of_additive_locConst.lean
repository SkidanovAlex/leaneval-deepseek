import Mathlib
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
import Submission.Work.SSGRoute.kummer_character_realization_inf
import Submission.Work.SSGRoute.exists_kummerCharacter_of_zmod
import Submission.Work.SSGRoute.isOpen_map_fixingSubgroupEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZSplit

open scoped Pointwise
open _root_.SSGRoute

/-- **The Kummer correspondence for additive, locally constant cochains on `G_K`**, for a general
prime `p` with `ζ_p ∈ K`.  Every cochain `z : G_k → 𝔽_p` which is additive on `G_K` and locally
constant on `G_K` is the level-`K` Kummer cochain of some `β ∈ Kˣ`
(`Work.SSGRoute.ZSplit.nodeKummerCocharZMod`).  This is the general-`p` companion of
`Work.SSGRoute.exists_kummerChar_of_additive_locConst`. -/
theorem exists_kummerCocharZMod_of_additive_locConst (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ p)
    (z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hz : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hzc : SSGRoute.IsLocConstOn K.fixingSubgroup z) :
    ∃ β : (↥K)ˣ, ∀ σ ∈ K.fixingSubgroup,
      z σ = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β σ := by
  classical
  -- the root of unity, viewed in `K`
  have hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- `z` vanishes at `1`
  have hz_one : z 1 = 0 := by
    have h := hz 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [one_mul] at h
    exact add_left_cancel (by rw [add_zero]; exact h.symm)
  -- the additive character on `G_K`, first as a homomorphism on `K.fixingSubgroup`
  let f : ↥(K.fixingSubgroup) →* Multiplicative (ZMod p) :=
    { toFun := fun g => Multiplicative.ofAdd (z g)
      map_one' := by simp [hz_one]
      map_mul' := fun g h => by
        show Multiplicative.ofAdd (z (g * h)) =
          Multiplicative.ofAdd (z g) * Multiplicative.ofAdd (z h)
        rw [hz g g.2 h h.2, ofAdd_add] }
  -- the kernel of `f` is open
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
  let zK : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod p) :=
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
  -- the `μ_p`-valued character
  let zrK : Multiplicative (ZMod p) ≃* ↥(rootsOfUnity p ↥K) :=
    zr (isPrimitiveRoot_primRootUnit (F := ↥K) (p := p) hζK')
  let ω : (Ω ≃ₐ[K] Ω) →* ↥(rootsOfUnity p ↥K) := zrK.toMonoidHom.comp zK
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
    kummer_character_realization_inf (U := ↥K) (L := Ω) (n := p)
      (Fact.out : p.Prime).ne_zero ω hopen_ω
  -- `γ ^ p = algebraMap x` for some `x ∈ Kˣ`
  obtain ⟨x, hx⟩ := hγmem
  have hγ0 : γ ≠ 0 := by
    have h1 : γ / γ = 1 := by simpa using hγdiv 1
    intro h0
    rw [h0, div_zero] at h1
    exact zero_ne_one h1
  have hx0 : x ≠ 0 := by
    intro h0
    refine hγ0 ?_
    have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have h2 : γ ^ p = 0 := by rw [← hx, h0, map_zero]
    exact (pow_eq_zero_iff hp).mp h2
  let β : (↥K)ˣ := Units.mk0 x hx0
  let γu : Ωˣ := Units.mk0 γ hγ0
  have hγu : γu ^ p = Units.map (algebraMap ↥K Ω) β := by
    apply Units.ext
    show γ ^ p = (algebraMap ↥K Ω) x
    exact hx.symm
  refine ⟨β, ?_⟩
  intro σ hσ
  rw [nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := β) hσ]
  set σK : Ω ≃ₐ[K] Ω := (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ with hσK
  have hω_apply : ∀ τ : Ω ≃ₐ[K] Ω, ω τ = zrK (zK τ) := fun τ => rfl
  have hzKσ : zK σK = Multiplicative.ofAdd (z σ) := by
    show f ((IntermediateField.fixingSubgroupEquiv K).symm σK) = Multiplicative.ofAdd (z σ)
    rw [hσK, MulEquiv.symm_apply_apply]
    rfl
  have hratio : Work.Kummer.kummerRatio σK γu
      = Units.map (algebraMap ↥K Ω) (((ω σK : ↥(rootsOfUnity p ↥K)) : (↥K)ˣ)) := by
    apply Units.ext
    rw [Work.Kummer.kummerRatio_coe, Units.coe_map]
    show (σK : Ω → Ω) γ / γ =
      algebraMap ↥K Ω (((ω σK : ↥(rootsOfUnity p ↥K)) : (↥K)ˣ) : ↥K)
    exact hγdiv σK
  rw [Work.SSGRoute.kummerCharZMod_apply]
  rw [Work.SSGRoute.kummerIdx_congr p hζK' β
    (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) p β) hγu σK]
  have hkey : ((zr (Work.SSGRoute.isPrimitiveRoot_mappedRoot (F := ↥K) (E := Ω) (p := p) hζK')
        (Multiplicative.ofAdd
          (Work.SSGRoute.kummerIdx p hζK' β γu hγu σK)) : ↥(rootsOfUnity p Ω)) : Ωˣ)
      = ((zr (Work.SSGRoute.isPrimitiveRoot_mappedRoot (F := ↥K) (E := Ω) (p := p) hζK')
        (Multiplicative.ofAdd (z σ)) : ↥(rootsOfUnity p Ω)) : Ωˣ) := by
    rw [← Work.SSGRoute.kummerIdx_spec p hζK' β γu hγu σK, hratio, hω_apply σK, hzKσ]
    exact (Work.SSGRoute.zr_map_eq (F := ↥K) (E := Ω) p hζK' (Multiplicative.ofAdd (z σ))).symm
  have hfin : Multiplicative.ofAdd (Work.SSGRoute.kummerIdx p hζK' β γu hγu σK)
      = Multiplicative.ofAdd (z σ) :=
    (zr (Work.SSGRoute.isPrimitiveRoot_mappedRoot (F := ↥K) (E := Ω) (p := p)
      hζK')).injective (Subtype.ext hkey)
  exact (congrArg Multiplicative.toAdd hfin).symm

end Work.SSGRoute.ZSplit
