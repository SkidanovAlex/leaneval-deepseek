import Mathlib
import Submission.Work.SSGRoute.zmod_roots_of_unity
import Submission.Work.SSGRoute.zr_pow_castHom
import Submission.Work.SSGRoute.isOpen_map_fixingSubgroupEquiv
import Submission.Work.SSGRoute.kummer_character_realization_inf
import Submission.Work.SSGRoute.local_lifting_setup

/-!
# Local lifting of a character of the inertia subgroup

Given a `p`-adic local field `κ` with residue characteristic `l ≠ p`, the inertia subgroup
`I = Gal(κ̄/κ^ur)` is (pro-)cyclic modulo the wild inertia and pro-prime-to-`l`; since moreover
`κ^ur` contains all `p`-power roots of unity, every continuous character `I → ℤ/p^a` is the
reduction of a continuous character `I → ℤ/p^(a+1)`.

The proof realises the character as a Kummer character: using `I = Gal(K'/κ^ur)` and the
primitive `p^(a+1)`-st root of unity `ζ ∈ κ^ur` supplied by the hypothesis `hμ`, the
Kummer/Hilbert-90 realisation `kummer_character_realization_inf` produces `γ ∈ K'` with
`γ^(p^a) ∈ κ^ur` and `σγ/γ = ζ^(p·χ(σ))`.  A `p`-th root `β` of `γ` then gives the lift
`χ'(σ) =` the exponent of `ζ` in `σβ/β`.
-/

open scoped Classical
open IntermediateField

namespace Work.SSGRoute

lemma isOpen_map_subgroupCongr {G : Type*} [Group G] [TopologicalSpace G]
    {H K : Subgroup G} (h : H = K) (S : Subgroup ↥H) :
    IsOpen (S : Set ↥H) ↔
      IsOpen ((S.map (MulEquiv.subgroupCongr h).toMonoidHom : Subgroup ↥K) : Set ↥K) := by
  have hset : (H : Set G) = (K : Set G) := by rw [h]
  let φ : ↥H ≃ₜ ↥K := Homeomorph.setCongr hset
  have hφ : (Subgroup.map (MulEquiv.subgroupCongr h).toMonoidHom S : Set ↥K) = φ '' (S : Set ↥H) := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, by rw [← hyx]; rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by rfl⟩
  rw [hφ]
  exact φ.isOpen_image.symm

theorem local_inertia_char_lift
    {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K'] [IsSepClosure κ K']
    (l q : ℕ) (hl : l.Prime) (hT : NK.LocalTame.TameData l q κ K')
    {p a : ℕ} (hp : p.Prime) (hne : p ≠ l)
    (hμ : ∃ ζ : K', ζ ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') l ∧
      IsPrimitiveRoot ζ (p ^ (a + 1)))
    (χ : ↥(NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') l) →*
      Multiplicative (ZMod (p ^ a)))
    (hopen : IsOpen (χ.ker : Set ↥(NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') l))) :
    ∃ χ' : ↥(NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') l) →*
        Multiplicative (ZMod (p ^ (a + 1))),
      IsOpen (χ'.ker : Set ↥(NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') l)) ∧
      ∀ σ : ↥(NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') l),
        Multiplicative.toAdd (χ σ) =
          ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))
            (Multiplicative.toAdd (χ' σ)) := by

  obtain ⟨ζ, hζU, hζ⟩ := hμ
  have hp_pos : 0 < p := hp.pos
  haveI : NeZero (p ^ (a + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpK' : (p : K') ≠ 0 := by
    have h : ((p ^ (a+1) : ℕ) : K') ≠ 0 := (hζ.neZero').out
    rw [Nat.cast_pow] at h
    exact fun h0 => h (by rw [h0]; exact zero_pow (by omega : a + 1 ≠ 0))
  haveI : NeZero (p : K') := ⟨hpK'⟩
  let U : IntermediateField κ K' := NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') l
  let I : Subgroup (K' ≃ₐ[κ] K') := NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') l
  have hI : I = U.fixingSubgroup :=
    NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure l
  haveI hSepU : IsSepClosure ↥U K' :=
    IsSepClosure.mk (IsSepClosure.sep_closed (k := κ) (K := K'))
      (Algebra.isSeparable_tower_top_of_isSeparable κ ↥U K')
  haveI hSepClosedK' : IsSepClosed K' := IsSepClosure.sep_closed (k := κ) (K := K')
  -- ζ as an element of U and the units on the U- and K'-sides
  let ζu : ↥U := ⟨ζ, hζU⟩
  have hζu : IsPrimitiveRoot ζu (p ^ (a+1)) := by
    rw [IsPrimitiveRoot.iff_orderOf, ← orderOf_submonoid (H := U.toSubmonoid) ζu]
    exact (IsPrimitiveRoot.iff_orderOf).mp hζ
  let ζuU : (↥U)ˣ := Units.mk0 ζu (hζu.ne_zero (by positivity))
  have hζuU : IsPrimitiveRoot ζuU (p ^ (a+1)) :=
    (IsPrimitiveRoot.coe_units_iff (ζ := ζuU)).mp (by rw [Units.val_mk0]; exact hζu)
  let ζaU : (↥U)ˣ := ζuU ^ p
  have hζaU : IsPrimitiveRoot ζaU (p ^ a) := hζuU.pow (by positivity) (by ring)
  -- the K'-side units
  let ηU : K'ˣ := Units.map (algebraMap ↥U K').toMonoidHom ζuU
  have hηU : IsPrimitiveRoot ηU (p ^ (a+1)) :=
    hζuU.map_of_injective (f := Units.map (algebraMap ↥U K').toMonoidHom)
      (Units.map_injective (f := (algebraMap ↥U K').toMonoidHom) (algebraMap ↥U K').injective)
  have hηpU : IsPrimitiveRoot (Units.map (algebraMap ↥U K').toMonoidHom ζaU) (p ^ a) :=
    hζaU.map_of_injective (f := Units.map (algebraMap ↥U K').toMonoidHom)
      (Units.map_injective (f := (algebraMap ↥U K').toMonoidHom) (algebraMap ↥U K').injective)
  have hηcast : Units.map (algebraMap ↥U K').toMonoidHom ζaU = ηU ^ p := by
    rw [show ζaU = ζuU ^ p from rfl, show ηU = Units.map (algebraMap ↥U K').toMonoidHom ζuU from rfl,
      map_pow]
  -- the isomorphism e : I ≃* Gal(K'/U)
  let e : ↥I ≃* Gal(K'/↥U) :=
    (MulEquiv.subgroupCongr hI).trans (IntermediateField.fixingSubgroupEquiv U)
  let χU : Gal(K'/↥U) →* Multiplicative (ZMod (p ^ a)) := χ.comp e.symm.toMonoidHom
  have hχUopen : IsOpen (χU.ker : Set Gal(K'/↥U)) := by
    have hker : χU.ker = χ.ker.map e.toMonoidHom := by
      ext x
      simp only [χU, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_map]
      constructor
      · intro hx; exact ⟨e.symm x, hx, by simp⟩
      · rintro ⟨y, hy, hyx⟩
        have : x = e y := by rw [← hyx]; simp
        rw [this]; simpa using hy
    rw [hker]
    rw [show χ.ker.map e.toMonoidHom
        = (χ.ker.map (MulEquiv.subgroupCongr hI).toMonoidHom).map
            (IntermediateField.fixingSubgroupEquiv U).toMonoidHom from by
      ext x
      simp only [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        exact ⟨_, ⟨y, hy, rfl⟩, hyx⟩
      · rintro ⟨z, ⟨y, hy, hyz⟩, hzx⟩
        exact ⟨y, hy, by rw [← hzx, ← hyz]; rfl⟩]
    exact isOpen_map_fixingSubgroupEquiv U _ ((isOpen_map_subgroupCongr hI χ.ker).mp hopen)
  -- the character ω over U
  let e_ro : ↥(rootsOfUnity (p^a) ↥U) ≃* ↥(rootsOfUnity (p^a) K') :=
    rootsOfUnityEquivOfPrimitiveRoots (f := algebraMap ↥U K') (algebraMap ↥U K').injective
      ⟨ζaU, (mem_primitiveRoots (by positivity)).mpr (IsPrimitiveRoot.coe_units_iff.mpr hζaU)⟩
  let ωU : Gal(K'/↥U) →* ↥(rootsOfUnity (p^a) ↥U) :=
    e_ro.symm.toMonoidHom.comp ((zr hηpU).toMonoidHom.comp χU)
  have hωrel : ∀ σ : Gal(K'/↥U),
      algebraMap ↥U K' (((ωU σ : ↥(rootsOfUnity (p^a) ↥U)) : (↥U)ˣ) : ↥U)
        = (((zr hηpU (χU σ) : ↥(rootsOfUnity (p^a) K')) : K'ˣ) : K') := by
    intro σ
    exact rootsOfUnityEquivOfPrimitiveRoots_symm_apply (f := algebraMap ↥U K')
      (algebraMap ↥U K').injective ⟨ζaU, (mem_primitiveRoots (by positivity)).mpr
        (IsPrimitiveRoot.coe_units_iff.mpr hζaU)⟩ (zr hηpU (χU σ))
  have hωU : IsOpen (ωU.ker : Set Gal(K'/↥U)) := by
    have : ωU.ker = χU.ker := by
      ext x
      simp only [ωU, MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact ⟨fun h => by simpa using congrArg (zr hζaU).symm h, fun h => by simp [h]⟩
    rw [this]; exact hχUopen
  -- Kummer realization
  obtain ⟨γ, hγU, hγrel⟩ :=
    kummer_character_realization_inf (U := ↥U) (L := K') (n := p^a)
      (pow_ne_zero _ hp.ne_zero) ωU hωU
  -- beta : p-th root of gamma
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq (k := K') γ p
  -- helpers
  obtain ⟨u₀, hu₀⟩ := hγU
  have hγne : γ ≠ 0 := by
    intro h0
    have h1 : γ / γ = algebraMap ↥U K'
        (((ωU 1 : ↥(rootsOfUnity (p^a) ↥U)) : (↥U)ˣ) : ↥U) := by
      simpa using hγrel 1
    rw [h0, zero_div] at h1
    exact (Units.ne_zero (((ωU 1 : ↥(rootsOfUnity (p^a) ↥U)) : (↥U)ˣ)))
      ((algebraMap ↥U K').injective h1.symm)
  have hβne : β ≠ 0 := by
    rintro h0
    rw [h0, zero_pow hp.ne_zero] at hβ
    exact hγne hβ.symm
  have hu₀ne : u₀ ≠ 0 := by
    rintro h
    rw [h, map_zero] at hu₀
    exact hγne (eq_zero_of_pow_eq_zero hu₀.symm)
  have hβpow : β ^ (p^(a+1)) = algebraMap ↥U K' u₀ := by
    have hpoweq : p^(a+1) = p * p^a := by ring
    rw [hpoweq, pow_mul, hβ]
    exact hu₀.symm
  -- Ω : I →* μ_{p^(a+1)}(K')
  have hmem : algebraMap ↥U K' u₀ ∈ U := by simpa using u₀.2
  have hΩpow : ∀ σ : ↥I, (((σ : K' ≃ₐ[κ] K') β) / β) ^ (p^(a+1)) = 1 := by
    intro σ
    rw [div_pow, ← map_pow, hβpow]
    have hfix : (σ : K' ≃ₐ[κ] K') (algebraMap ↥U K' u₀) = algebraMap ↥U K' u₀ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp
        (hI ▸ σ.2 : (σ : K' ≃ₐ[κ] K') ∈ U.fixingSubgroup) _ hmem
    rw [hfix]
    exact div_self (fun h => hu₀ne ((algebraMap ↥U K').injective (by rw [h, map_zero])))
  have hζfix : ∀ σ : ↥I, (σ : K' ≃ₐ[κ] K') ζ = ζ := by
    intro σ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp
      (hI ▸ σ.2 : (σ : K' ≃ₐ[κ] K') ∈ U.fixingSubgroup) ζ hζU
  have hΩfix : ∀ σ τ : ↥I,
      (σ : K' ≃ₐ[κ] K') (((τ : K' ≃ₐ[κ] K') β) / β) = ((τ : K' ≃ₐ[κ] K') β) / β := by
    intro σ τ
    obtain ⟨i, -, hi⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hζ (by simpa using hΩpow τ)
    rw [← hi, map_pow, hζfix σ]
  have hΩmul : ∀ σ τ : ↥I,
      (((σ * τ : ↥I) : K' ≃ₐ[κ] K') β) / β
        = (((σ : K' ≃ₐ[κ] K') β) / β) * (((τ : K' ≃ₐ[κ] K') β) / β) := by
    intro σ τ
    have h3 : (τ : K' ≃ₐ[κ] K') β = (((τ : K' ≃ₐ[κ] K') β) / β) * β := by
      rw [div_mul_cancel₀ _ hβne]
    have h1 : (σ : K' ≃ₐ[κ] K') ((τ : K' ≃ₐ[κ] K') β)
        = (((τ : K' ≃ₐ[κ] K') β) / β) * ((σ : K' ≃ₐ[κ] K') β) := by
      conv_lhs => rw [h3]
      rw [map_mul, hΩfix σ τ]
    change ((σ : K' ≃ₐ[κ] K') * (τ : K' ≃ₐ[κ] K')) β / β = _
    rw [AlgEquiv.mul_apply, h1]
    field_simp
  let Ω : ↥I →* ↥(rootsOfUnity (p^(a+1)) K') :=
  { toFun := fun σ => rootsOfUnity.mkOfPowEq (((σ : K' ≃ₐ[κ] K') β) / β) (hΩpow σ)
    map_one' := by
      apply Subtype.ext; apply Units.ext
      rw [rootsOfUnity.coe_mkOfPowEq]
      simp [hβne]
    map_mul' := fun σ τ => by
      apply Subtype.ext; apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, rootsOfUnity.coe_mkOfPowEq]
      exact hΩmul σ τ }
  refine ⟨(zr hηU).symm.toMonoidHom.comp Ω, ?_, ?_⟩
  · -- openness
    have hker : ((zr hηU).symm.toMonoidHom.comp Ω).ker = Ω.ker := by
      ext x; simp [MonoidHom.mem_ker]
    rw [hker]
    haveI : IsGalois κ K' := IsSepClosure.isGalois
    have hΩcoe : ∀ σ : ↥I, (((Ω σ : ↥(rootsOfUnity (p^(a+1)) K')) : K'ˣ) : K')
        = (((σ : K' ≃ₐ[κ] K') β) / β) := fun σ => rootsOfUnity.coe_mkOfPowEq _
    have hset : (Ω.ker : Set ↥I)
        = (↑) ⁻¹' ((IntermediateField.adjoin κ ({β} : Set K')).fixingSubgroup :
            Set (K' ≃ₐ[κ] K')) := by
      ext σ
      change Ω σ = 1 ↔ (σ : K' ≃ₐ[κ] K') ∈ (IntermediateField.adjoin κ ({β} : Set K')).fixingSubgroup
      constructor
      · intro hσ
        have hβ : (σ : K' ≃ₐ[κ] K') β = β := by
          have h1 : (((σ : K' ≃ₐ[κ] K') β) / β) = 1 := by
            have := congrArg (fun u : ↥(rootsOfUnity (p^(a+1)) K') => ((u : K'ˣ) : K')) hσ
            rw [hΩcoe σ] at this
            simpa using this
          rwa [div_eq_one_iff_eq hβne] at h1
        have hstab : Subgroup.zpowers (σ : K' ≃ₐ[κ] K')
            ≤ MulAction.stabilizer (K' ≃ₐ[κ] K') β := Subgroup.zpowers_le.mpr (by
              rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hβ)
        have hmem : β ∈ IntermediateField.fixedField (Subgroup.zpowers (σ : K' ≃ₐ[κ] K')) := by
          rw [IntermediateField.mem_fixedField_iff]
          intro τ hτ
          have := hstab hτ
          rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
          exact this
        have hle : IntermediateField.adjoin κ ({β} : Set K')
            ≤ IntermediateField.fixedField (Subgroup.zpowers (σ : K' ≃ₐ[κ] K')) := by
          rw [IntermediateField.adjoin_le_iff]
          intro x hx
          rw [Set.mem_singleton_iff] at hx; subst hx
          exact hmem
        exact (IntermediateField.le_iff_le (Subgroup.zpowers (σ : K' ≃ₐ[κ] K'))
          (IntermediateField.adjoin κ ({β} : Set K'))).mp hle (Subgroup.mem_zpowers _)
      · intro hσ
        rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
        have hβ : (σ : K' ≃ₐ[κ] K') β = β := hσ β (IntermediateField.mem_adjoin_simple_self κ β)
        apply Subtype.ext; apply Units.ext
        rw [hΩcoe σ, hβ, div_self hβne]
        rfl
    have hclosed : IsClosed (Ω.ker : Set ↥I) := by
      rw [hset]
      exact (InfiniteGalois.fixingSubgroup_isClosed
        (IntermediateField.adjoin κ ({β} : Set K'))).preimage continuous_subtype_val
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex Ω.ker hclosed
  · -- reduction
    intro σ
    have hχσ : χ σ = χU (e σ) := rfl
    have heσc : ∀ x : K', (e σ : K' ≃ₐ[↥U] K') x = (σ : K' ≃ₐ[κ] K') x := fun x => rfl
    have hcompat := zr_pow_castHom (R := K') (p := p) (a := a) hηU hηpU hηcast.symm
      (((zr hηU).symm.toMonoidHom.comp Ω) σ)
    have hzr1 : ((zr hηU (((zr hηU).symm.toMonoidHom.comp Ω) σ) :
          ↥(rootsOfUnity (p^(a+1)) K')) : K'ˣ)
        = ((Ω σ : ↥(rootsOfUnity (p^(a+1)) K')) : K'ˣ) := by
      simp
    have hkey : ((zr hηpU (Multiplicative.ofAdd (ZMod.castHom (pow_dvd_pow p (Nat.le_succ a))
            (ZMod (p^a)) (Multiplicative.toAdd (((zr hηU).symm.toMonoidHom.comp Ω) σ)))) :
          ↥(rootsOfUnity (p^a) K')) : K'ˣ)
        = ((zr hηpU (χU (e σ)) : ↥(rootsOfUnity (p^a) K')) : K'ˣ) := by
      rw [← hcompat, hzr1]
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val]
      have hΩσ : (((Ω σ : ↥(rootsOfUnity (p^(a+1)) K')) : K'ˣ) : K')
          = (((σ : K' ≃ₐ[κ] K') β) / β) := rootsOfUnity.coe_mkOfPowEq _
      rw [hΩσ, ← hωrel (e σ), ← hγrel (e σ), heσc γ, div_pow, ← map_pow, hβ]
    have hEq : Multiplicative.ofAdd (ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p^a))
          (Multiplicative.toAdd (((zr hηU).symm.toMonoidHom.comp Ω) σ))) = χU (e σ) := by
      apply (zr hηpU).injective
      apply Subtype.val_injective
      exact hkey
    rw [hχσ, ← hEq]
    rfl


end Work.SSGRoute
