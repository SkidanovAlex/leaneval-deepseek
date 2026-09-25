import Mathlib
import Submission.NK.NUV2.ideleDefectData
import Submission.NK.NUV2.ideleDefs
import Submission.NK.NUV2.rank_addMonoidHom_units_eq_rank
import Submission.NK.NUV2.unitDual_finite
import Submission.NK.NUV2.exists_continuous_ideleIncl
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_principalIdele
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_mem_localUnits

/-!
# Naturality of `unitsImgRank` (CoNF Ch. X §10.3)

`NK.NUV2.unitsImgRank K = u_K` is the `ℤ₂`-rank of the image of the restriction map
`Hom_cts(𝕀_int K, ℤ₂) → Hom(𝒪_Kˣ, ℤ₂)`.  `NK.NUV2.defectRho K = ρ_K = r₁(K) + r₂(K) - 1` is
the unit rank.  The defect `δ_K = ρ_K - u_K` is the `2`-adic Leopoldt defect, and CoNF (10.3.7)
Cor. says that it is monotone in `K`; equivalently `u_N - u_M ≤ ρ_N - ρ_M` for `M ⊆ N`, which is
the statement proved here.

The proof is the flatness/diagonal argument transported to the dual side:

* the transpose `ι* : Hom(𝒪_Nˣ, ℤ₂) → Hom(𝒪_Mˣ, ℤ₂)` of the inclusion `𝒪_Mˣ → 𝒪_Nˣ` carries the
  image of `restrictUnits_N` into the image of `restrictUnits_M`, because the idèle inclusion
  `𝕀_int M → 𝕀_int N` (continuous, and compatible with the diagonal embeddings of the units by
  `globalCFT_ideleInclusion_principalIdele`) is compatible with the two restriction maps;
* the norm `N : 𝒪_Nˣ → 𝒪_Mˣ` satisfies `N(ι u) = u ^ [N : M]`, so `ι* ∘ N* = [N : M] • id`; hence
  `[N : M] • Hom(𝒪_Mˣ, ℤ₂) ⊆ range ι*` and `ker ι*` has rank `ρ_N - ρ_M`;
* rank–nullity for the restriction of `ι*` to `range restrictUnits_N` finishes the proof.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

namespace NK.NUV2

open NK.GlobalCFT


/-! ## The `ℤ₂`-dual of the unit group and maps induced by unit homomorphisms -/

/-- The `ℤ₂`-module `Hom(𝒪_Kˣ, ℤ₂)`: the (additive) dual of the unit group of the ring of
integers. -/
abbrev unitDual (K : Type*) [Field K] [NumberField K] : Type _ :=
  Additive ((𝓞 K)ˣ) →+ PadicInt 2

/-- Precomposition with a homomorphism of abelian groups, as a `ℤ₂`-linear map between the duals
into `ℤ₂`. -/
noncomputable def dualPrecomp {A B : Type*} [CommGroup A] [CommGroup B] (f : A →* B) :
    (Additive B →+ PadicInt 2) →ₗ[PadicInt 2] (Additive A →+ PadicInt 2) where
  toFun ψ := ψ.comp (MonoidHom.toAdditive f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem dualPrecomp_apply {A B : Type*} [CommGroup A] [CommGroup B] (f : A →* B)
    (ψ : Additive B →+ PadicInt 2) (x : A) :
    dualPrecomp f ψ (Additive.ofMul x) = ψ (Additive.ofMul (f x)) := rfl

/-- The inclusion `𝒪_Mˣ →* 𝒪_Nˣ` for an extension of number fields. -/
noncomputable def unitsIncl (M N : Type*) [Field M] [NumberField M] [Field N] [NumberField N]
    [Algebra M N] : (𝓞 M)ˣ →* (𝓞 N)ˣ :=
  Units.map (algebraMap (𝓞 M) (𝓞 N))

/-- The norm `𝒪_Nˣ →* 𝒪_Mˣ` for an extension of number fields. -/
noncomputable def unitsNorm (M N : Type*) [Field M] [Field N] [Algebra M N] :
    (𝓞 N)ˣ →* (𝓞 M)ˣ :=
  Units.map (RingOfIntegers.norm M)

/-- The transpose of the inclusion of unit groups. -/
noncomputable def unitsInclDual (M N : Type*) [Field M] [NumberField M] [Field N] [NumberField N]
    [Algebra M N] : unitDual N →ₗ[PadicInt 2] unitDual M :=
  dualPrecomp (unitsIncl M N)

/-- The transpose of the norm of unit groups. -/
noncomputable def unitsNormDual (M N : Type*) [Field M] [NumberField M] [Field N] [NumberField N]
    [Algebra M N] : unitDual M →ₗ[PadicInt 2] unitDual N :=
  dualPrecomp (unitsNorm M N)

@[simp] theorem unitsIncl_apply (M N : Type*) [Field M] [NumberField M] [Field N] [NumberField N]
    [Algebra M N] (u : (𝓞 M)ˣ) :
    ((unitsIncl M N u : (𝓞 N)ˣ) : 𝓞 N) = algebraMap (𝓞 M) (𝓞 N) (u : 𝓞 M) := rfl

@[simp] theorem unitsNorm_apply (M N : Type*) [Field M] [Field N] [Algebra M N] (u : (𝓞 N)ˣ) :
    ((unitsNorm M N u : (𝓞 M)ˣ) : 𝓞 M) = RingOfIntegers.norm M (u : 𝓞 N) := rfl

@[simp] theorem unitsInclDual_apply (M N : Type*) [Field M] [NumberField M] [Field N]
    [NumberField N] [Algebra M N] (ψ : unitDual N) (u : (𝓞 M)ˣ) :
    unitsInclDual M N ψ (Additive.ofMul u) = ψ (Additive.ofMul (unitsIncl M N u)) := rfl

@[simp] theorem unitsNormDual_apply (M N : Type*) [Field M] [NumberField M] [Field N]
    [NumberField N] [Algebra M N] (ψ : unitDual M) (u : (𝓞 N)ˣ) :
    unitsNormDual M N ψ (Additive.ofMul u) = ψ (Additive.ofMul (unitsNorm M N u)) := rfl

/-! ## The key identity `ι* ∘ N* = [N : M]` -/

/-- The norm of an embedded unit is the degree-th power. -/
theorem unitsNorm_unitsIncl (M N : Type*) [Field M] [NumberField M] [Field N] [NumberField N]
    [Algebra M N] (u : (𝓞 M)ˣ) :
    unitsNorm M N (unitsIncl M N u) = u ^ Module.finrank M N := by
  apply Units.ext
  rw [unitsNorm_apply, unitsIncl_apply, RingOfIntegers.norm_algebraMap]
  simp

/-- **The norm is the transpose-inverse of the inclusion up to the degree**: the composite
`ι* ∘ N*` of the transposes of the norm and of the inclusion of unit groups is multiplication by
the degree `[N : M]`. -/
theorem unitsInclDual_unitsNormDual (M N : Type*) [Field M] [NumberField M] [Field N]
    [NumberField N] [Algebra M N] (ψ : unitDual M) :
    unitsInclDual M N (unitsNormDual M N ψ) = (Module.finrank M N : PadicInt 2) • ψ := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨u, rfl⟩ := Additive.ofMul.surjective x
  rw [unitsInclDual_apply, unitsNormDual_apply, unitsNorm_unitsIncl]
  have hpow : Additive.ofMul (u ^ Module.finrank M N) = Module.finrank M N • Additive.ofMul u :=
    rfl
  rw [hpow, map_nsmul, nsmul_eq_mul]
  rfl

/-! ## The unit rank as the finrank of the unit dual -/

/-- `ρ_K = r₁(K) + r₂(K) - 1` is Mathlib's `NumberField.Units.rank`. -/
theorem defectRho_eq_unitsRank_aux (K : Type) [Field K] [NumberField K] :
    defectRho K = NumberField.Units.rank K := by
  rw [defectRho, NumberField.Units.rank,
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]

/-- The `ℤ₂`-rank of `Hom(𝒪_Kˣ, ℤ₂)` is the unit rank `ρ_K`. -/
theorem unitDual_rank (K : Type) [Field K] [NumberField K] :
    Module.rank (PadicInt 2) (unitDual K) = (defectRho K : Cardinal) := by
  rw [defectRho_eq_unitsRank_aux]
  exact rank_addMonoidHom_units_eq_rank K

/-- The `ℤ₂`-finrank of `Hom(𝒪_Kˣ, ℤ₂)` is the unit rank `ρ_K`. -/
theorem unitDual_finrank_eq_defectRho (K : Type) [Field K] [NumberField K] :
    Module.finrank (PadicInt 2) (unitDual K) = defectRho K :=
  Module.finrank_eq_of_rank_eq (unitDual_rank K)

/-! ## Rank of the range and kernel of the transpose of the norm and of the inclusion -/

section Rank

variable {M N : Type} [Field M] [NumberField M] [Field N] [NumberField N] [Algebra M N]

/-- The finrank of the top submodule is the finrank of the ambient module. -/
theorem finrank_top (S : Type*) [AddCommMonoid S] [Module (PadicInt 2) S] :
    Module.finrank (PadicInt 2) ↥(⊤ : Submodule (PadicInt 2) S) = Module.finrank (PadicInt 2) S :=
  LinearEquiv.finrank_eq Submodule.topEquiv

/-- **The range of `ι*` contains `[N : M] • Hom(𝒪_Mˣ, ℤ₂)`**, since `ι* ∘ N* = [N : M]`; hence its
finrank is at least the finrank of `Hom(𝒪_Mˣ, ℤ₂)`, which is `ρ_M`. -/
theorem defectRho_le_finrank_range_unitsInclDual [Module.Finite M N]
    [Module.Finite (PadicInt 2) (unitDual M)] [Module.Finite (PadicInt 2) (unitDual N)] :
    defectRho M ≤ Module.finrank (PadicInt 2) ↥(LinearMap.range (unitsInclDual M N)) := by
  haveI : IsNoetherian (PadicInt 2) (unitDual N) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  set d : PadicInt 2 := (Module.finrank M N : PadicInt 2) with hd
  have hd0 : d ≠ 0 := by
    haveI : Nontrivial N := inferInstance
    rw [hd]
    exact Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := M) (M := N)))
  have hinj : Function.Injective (LinearMap.lsmul (PadicInt 2) (unitDual M) d) := by
    intro ψ χ h
    have h' : d • ψ = d • χ := h
    apply AddMonoidHom.ext
    intro x
    have hx := congrArg (fun f : unitDual M => f x) h'
    exact mul_left_cancel₀ hd0 hx
  have hrange : LinearMap.range (LinearMap.lsmul (PadicInt 2) (unitDual M) d)
      ≤ LinearMap.range (unitsInclDual M N) := by
    rintro _ ⟨ψ, rfl⟩
    exact ⟨unitsNormDual M N ψ, by
      rw [LinearMap.lsmul_apply, unitsInclDual_unitsNormDual]⟩
  calc defectRho M = Module.finrank (PadicInt 2) (unitDual M) := (unitDual_finrank_eq_defectRho M).symm
    _ = Module.finrank (PadicInt 2)
          ↥(LinearMap.range (LinearMap.lsmul (PadicInt 2) (unitDual M) d)) :=
        LinearEquiv.finrank_eq (LinearEquiv.ofInjective _ hinj)
    _ ≤ Module.finrank (PadicInt 2) ↥(LinearMap.range (unitsInclDual M N)) :=
        Submodule.finrank_mono hrange

/-- **The kernel of the transpose of the inclusion has finrank `ρ_N - ρ_M`** (at most):
rank–nullity together with the previous lemma. -/
theorem finrank_ker_unitsInclDual_le [Module.Finite M N]
    [Module.Finite (PadicInt 2) (unitDual M)] [Module.Finite (PadicInt 2) (unitDual N)] :
    Module.finrank (PadicInt 2) ↥(LinearMap.ker (unitsInclDual M N))
      ≤ defectRho N - defectRho M := by
  haveI : IsNoetherian (PadicInt 2) (unitDual M) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian (PadicInt 2) (unitDual N) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  have hnull : Module.finrank (PadicInt 2) ↥(LinearMap.range (unitsInclDual M N))
      + Module.finrank (PadicInt 2) ↥(LinearMap.ker (unitsInclDual M N)) = defectRho N := by
    have h := Submodule.finrank_quotient_add_finrank (R := PadicInt 2) (M := unitDual N)
      (LinearMap.ker (unitsInclDual M N))
    rw [(LinearMap.quotKerEquivRange (unitsInclDual M N)).finrank_eq, unitDual_finrank_eq_defectRho N] at h
    exact h
  have him := defectRho_le_finrank_range_unitsInclDual (M := M) (N := N)
  omega

end Rank

/-! ## The idèle inclusion, its restriction to the integral idèles and its transpose -/

section Idele

variable {M N : Type} [Field M] [NumberField M] [Field N] [NumberField N] [Algebra M N]
  [FiniteDimensional M N]

/-- **The idèle inclusion carries integral idèles to integral idèles.** -/
theorem ideleIncl_mem_integralIdeles (φ : 𝕀[M] →* 𝕀[N])
    (u : Place N → Place M) (hu : ∀ w, Place.LiesOver w (u w))
    (hφ : ∀ (x : 𝕀[M]) (w : Place N),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w))) :
    ∀ x ∈ Idele.integralIdeles M, φ x ∈ Idele.integralIdeles N := by
  intro x hx
  rw [Idele.mem_integralIdeles] at hx ⊢
  intro w hw
  rw [hφ x w]
  exact Inclusion.globalCFT_localAlgebraMapUnits_mem_localUnits (hu w)
    (hx (u w) ((Place.isFinite_of_liesOver (hu w)).mp hw))

/-- The idèle inclusion, restricted to the integral idèles. -/
noncomputable def ideleInclInt (φ : 𝕀[M] →* 𝕀[N])
    (hmem : ∀ x ∈ Idele.integralIdeles M, φ x ∈ Idele.integralIdeles N) :
    ↥(Idele.integralIdeles M) →* ↥(Idele.integralIdeles N) :=
  MonoidHom.codRestrict (φ.comp (Idele.integralIdeles M).subtype) (Idele.integralIdeles N)
    (fun x => hmem x x.2)

@[simp] theorem ideleInclInt_apply (φ : 𝕀[M] →* 𝕀[N])
    (hmem : ∀ x ∈ Idele.integralIdeles M, φ x ∈ Idele.integralIdeles N)
    (x : ↥(Idele.integralIdeles M)) :
    ((ideleInclInt φ hmem x : ↥(Idele.integralIdeles N)) : 𝕀[N]) = φ x := rfl

theorem continuous_ideleInclInt (φ : 𝕀[M] →* 𝕀[N])
    (hmem : ∀ x ∈ Idele.integralIdeles M, φ x ∈ Idele.integralIdeles N)
    (hφ : Continuous φ) : Continuous (ideleInclInt φ hmem) := by
  refine Continuous.subtype_mk ?_ _
  simpa [ideleInclInt_apply] using hφ.comp continuous_subtype_val

/-- The transpose of the restriction of the idèle inclusion to the integral idèles. -/
noncomputable def ideleInclIntDual (φ : 𝕀[M] →* 𝕀[N])
    (hmem : ∀ x ∈ Idele.integralIdeles M, φ x ∈ Idele.integralIdeles N)
    (hcont : Continuous (ideleInclInt φ hmem)) :
    NK.Reconstruct.Dual ↥(Idele.integralIdeles N) 2 →ₗ[PadicInt 2]
      NK.Reconstruct.Dual ↥(Idele.integralIdeles M) 2 where
  toFun ψ := NK.Reconstruct.dualMap 2 (ideleInclInt φ hmem) hcont ψ
  map_add' := NK.Reconstruct.dualMap_add 2 (ideleInclInt φ hmem) hcont
  map_smul' := fun a x => by
    simpa using NK.RankTheoryDeep.dualMap_smul (ideleInclInt φ hmem) hcont a x

@[simp] theorem ideleInclIntDual_apply (φ : 𝕀[M] →* 𝕀[N])
    (hmem : ∀ x ∈ Idele.integralIdeles M, φ x ∈ Idele.integralIdeles N)
    (hcont : Continuous (ideleInclInt φ hmem))
    (ψ : NK.Reconstruct.Dual ↥(Idele.integralIdeles N) 2)
    (x : ↥(Idele.integralIdeles M)) :
    ideleInclIntDual φ hmem hcont ψ (Additive.ofMul x)
      = ψ (Additive.ofMul (ideleInclInt φ hmem x)) := by
  show NK.Reconstruct.dualMap 2 (ideleInclInt φ hmem) hcont ψ (Additive.ofMul x) = _
  rw [NK.Reconstruct.dualMap_apply]
  rfl

/-- **The diagonal embeddings are compatible with the idèle inclusion.** -/
theorem ideleInclInt_unitsToIntegral (φ : 𝕀[M] →* 𝕀[N])
    (hmem : ∀ x ∈ Idele.integralIdeles M, φ x ∈ Idele.integralIdeles N)
    (u : Place N → Place M) (hu : ∀ w, Place.LiesOver w (u w))
    (hφ : ∀ (x : 𝕀[M]) (w : Place N),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (y : (𝓞 M)ˣ) :
    ideleInclInt φ hmem (unitsToIntegral M y) = unitsToIntegral N (unitsIncl M N y) := by
  apply Subtype.ext
  rw [ideleInclInt_apply, unitsToIntegral_coe, unitsToIntegral_coe,
    Inclusion.globalCFT_ideleInclusion_principalIdele u hu φ hφ]
  congr 1

/-- **The transpose of the inclusion commutes with the two restriction maps.** -/
theorem restrictUnits_ideleInclIntDual (φ : 𝕀[M] →* 𝕀[N])
    (hmem : ∀ x ∈ Idele.integralIdeles M, φ x ∈ Idele.integralIdeles N)
    (hcont : Continuous (ideleInclInt φ hmem))
    (u : Place N → Place M) (hu : ∀ w, Place.LiesOver w (u w))
    (hφ : ∀ (x : 𝕀[M]) (w : Place N),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (ψ : NK.Reconstruct.Dual ↥(Idele.integralIdeles N) 2) :
    restrictUnits (K := M) (ideleInclIntDual φ hmem hcont ψ)
      = unitsInclDual M N (restrictUnits (K := N) ψ) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Additive.ofMul.surjective x
  simp only [restrictUnits_apply, ideleInclIntDual_apply, unitsInclDual_apply,
    ideleInclInt_unitsToIntegral φ hmem u hu hφ y]

/-- **The transpose of the inclusion of unit groups carries the range for `N` into the range for
`M`.** -/
theorem map_range_le_of_ideleIncl (φ : 𝕀[M] →* 𝕀[N]) (hφcont : Continuous φ)
    (u : Place N → Place M) (hu : ∀ w, Place.LiesOver w (u w))
    (hφ : ∀ (x : 𝕀[M]) (w : Place N),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w))) :
    Submodule.map (unitsInclDual M N) (LinearMap.range (restrictUnits (K := N)))
      ≤ LinearMap.range (restrictUnits (K := M)) := by
  set hmem := ideleIncl_mem_integralIdeles φ u hu hφ with hmemdef
  have hcont : Continuous (ideleInclInt φ hmem) := continuous_ideleInclInt φ hmem hφcont
  rintro χ ⟨ψ, hψ, rfl⟩
  obtain ⟨ξ, rfl⟩ := hψ
  exact ⟨ideleInclIntDual φ hmem hcont ξ,
    restrictUnits_ideleInclIntDual φ hmem hcont u hu hφ ξ⟩

end Idele

/-! ## The final inequality -/

section Final

variable {M N : Type} [Field M] [NumberField M] [Field N] [NumberField N] [Algebra M N]

/-- **The analytic core**: the containment of the two ranges implies the inequality.

The proof avoids all linear algebra on submodule *types*: the bound
`rank (comap ι* (range restrictUnits_M)) ≤ rank (range restrictUnits_M) + rank (ker ι*)` is the
lifted rank–nullity lemma `LinearMap.lift_rank_comap_le` for the (unproblematic) map
`ι* : unitDual N →ₗ unitDual M` between the two unit duals. -/
theorem unitsImgRank_le_of_containment [Module.Finite M N]
    (hcont : Submodule.map (unitsInclDual M N) (LinearMap.range (restrictUnits (K := N)))
      ≤ LinearMap.range (restrictUnits (K := M)))
    [Module.Finite (PadicInt 2) (unitDual M)] [Module.Finite (PadicInt 2) (unitDual N)] :
    unitsImgRank N ≤ unitsImgRank M + (defectRho N - defectRho M) := by
  haveI : IsNoetherian (PadicInt 2) (unitDual M) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian (PadicInt 2) (unitDual N) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  -- the range for `N` is contained in the preimage of the range for `M`
  have hle : LinearMap.range (restrictUnits (K := N))
      ≤ Submodule.comap (unitsInclDual M N) (LinearMap.range (restrictUnits (K := M))) := by
    intro x hx
    exact hcont ⟨x, hx, rfl⟩
  -- the cardinal rank bound for the preimage
  have hcard : Module.rank (PadicInt 2)
        ↥(Submodule.comap (unitsInclDual M N) (LinearMap.range (restrictUnits (K := M))))
      ≤ Module.rank (PadicInt 2) ↥(LinearMap.range (restrictUnits (K := M)))
        + Module.rank (PadicInt 2) ↥(LinearMap.ker (unitsInclDual M N)) := by
    have hlift := LinearMap.lift_rank_comap_le (f := unitsInclDual M N)
      (LinearMap.range (restrictUnits (K := M)))
    rw [← Cardinal.lift_add] at hlift
    exact Cardinal.lift_le.mp hlift
  have hfin : Module.finrank (PadicInt 2)
        ↥(Submodule.comap (unitsInclDual M N) (LinearMap.range (restrictUnits (K := M))))
      ≤ Module.finrank (PadicInt 2) ↥(LinearMap.range (restrictUnits (K := M)))
        + Module.finrank (PadicInt 2) ↥(LinearMap.ker (unitsInclDual M N)) := by
    refine Module.finrank_le_of_rank_le (le_trans hcard ?_)
    rw [Nat.cast_add]
    simp only [Module.finrank_eq_rank]
    exact le_refl _
  have hpre : unitsImgRank N ≤ Module.finrank (PadicInt 2)
      ↥(Submodule.comap (unitsInclDual M N) (LinearMap.range (restrictUnits (K := M)))) :=
    Submodule.finrank_mono hle
  have hker := finrank_ker_unitsInclDual_le (M := M) (N := N)
  have heM : Module.finrank (PadicInt 2) ↥(LinearMap.range (restrictUnits (K := M)))
      = unitsImgRank M := rfl
  have heN : Module.finrank (PadicInt 2) ↥(LinearMap.range (restrictUnits (K := N)))
      = unitsImgRank N := rfl
  omega

end Final

/-- **The naturality of `u_K = unitsImgRank K`** (CoNF (10.3.7) Cor.): for number fields
`M ⊆ N` inside `Ω`, `u_N - u_M ≤ ρ_N - ρ_M`.  Equivalently, the `2`-adic Leopoldt defect
`δ_K = ρ_K - u_K` is monotone. -/
theorem unitsImgRank_naturality (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (M N : IntermediateField ℚ Ω) [NumberField ↥M] [NumberField ↥N] (hMN : M ≤ N) :
    NK.NUV2.unitsImgRank ↥N
      ≤ NK.NUV2.unitsImgRank ↥M + (NK.NUV2.defectRho ↥N - NK.NUV2.defectRho ↥M) := by
  haveI : Algebra ↥M ↥N := (IntermediateField.inclusion hMN).toAlgebra
  haveI : IsScalarTower ℚ ↥M ↥N := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    ext
    simp [IntermediateField.inclusion, RingHom.algebraMap_toAlgebra]
  haveI : FiniteDimensional ↥M ↥N := inferInstance
  haveI hfinM : Module.Finite (PadicInt 2) (unitDual ↥M) := unitDual_finite ↥M
  haveI hfinN : Module.Finite (PadicInt 2) (unitDual ↥N) := unitDual_finite ↥N
  choose u hu using fun w : Place ↥N =>
    Inclusion.globalCFT_exists_placeUnder (K := ↥M) (L := ↥N) w
  obtain ⟨φ, hcont, hφ⟩ := exists_continuous_ideleIncl u hu
  exact unitsImgRank_le_of_containment (map_range_le_of_ideleIncl φ hcont u hu hφ)

end NK.NUV2
