import Mathlib
import Submission.NK.CFTLib.roquetteDefs
import Submission.NK.CFTLib.roquette_plan
import Submission.NK.CFTLib.tateCohomology_neg_one_idele_of_isUnramified
import Submission.NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_principalIdele
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_smul
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective

/-!
# Step 2 of Roquette's idèle computation: `Ĥ⁻¹(Gal(K/F), C_K) ≅ (Fˣ ∩ N 𝕀_K)/N Kˣ`

Let `K/F` be a finite Galois extension of number fields which is unramified at every place
(`CFTLib.IsUnramified F K`).  Then the `(-1)`-st Tate cohomology of the idèle class group `C_K` is
the concrete quotient

`(Fˣ ∩ N_{K/F} 𝕀_K) / N_{K/F} Kˣ = NK.CFTLib.normQuotient F K`,

the main theorem of this file.

## The proof

Write `G = Gal(K/F)`, `ρ_C` for the `ℤ[G]`-module `Additive (C_K)` and `ρ_𝕀` for
`Additive (𝕀_K)`.

* `Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso` describes `Ĥ⁻¹` of a
  `ℤ[G]`-module as `ker N ⧸ I_G`, and the norm of the representations at hand is the product of
  the Galois translates (`classRep_norm_ofMul`, `ideleRep_norm_ofMul`).
* **Step 1** (`tateCohomology_neg_one_idele_of_isUnramified`, imported) says that
  `Ĥ⁻¹(G, 𝕀_K) = 0` when `K/F` is unramified; in kernel form
  (`le_coinvariantsKer_of_subsingleton`) this is the statement that an idèle `z` with
  `∏_σ σ • z = 1`, equivalently `N_{K/F} z = 1`, is a Galois coboundary: its class in `C_K`
  lies in the augmentation subgroup `I_G C_K` (`mk_mem_augSub_of_normIdeleHom_eq_one`).
* The comparison map `Ψ : ker(N_{C_K}) → (Fˣ ∩ N𝕀_K)/N Kˣ` sends an idèle class `q` to the
  element `a` of `Fˣ` determined by `N_{K/F} y = (a)` for any lift `y ∈ 𝕀_K` of `q`
  (`normUnits`, `Ψfun`); it kills `I_G`, and its kernel is exactly `I_G` — this is where Step 1
  is used (`ker_le_comap_augSub`).  It is surjective because every element of `Fˣ ∩ N𝕀_K` is the
  norm of an idèle (`ΨHom_surj`).
* The resulting `ℤ`-linear isomorphism `Ĥ⁻¹(G, C_K) ≅ (Fˣ ∩ N𝕀_K)/N Kˣ` is the final theorem
  `tateCohomology_neg_one_iso_normQuotient`, whose statement is the interface used by
  `NK.CFTLib.roquette_bound`.

The auxiliary results live in the namespace `NK.CFTLib.NormQuotientIso` so that they do not
collide with the identically named statements in the sibling Step-1 development.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K]

namespace NormQuotientIso

abbrev ρC : Representation ℤ (K ≃ₐ[F] K) (Additive (C[K])) :=
  Representation.ofMulDistribMulAction (K ≃ₐ[F] K) (IdeleClassGroup K)

abbrev ρI : Representation ℤ (K ≃ₐ[F] K) (Additive (𝕀[K])) :=
  Representation.ofMulDistribMulAction (K ≃ₐ[F] K) (Idele K)

theorem classRep_norm_ofMul (q : C[K]) :
    (ρC F K).norm (Additive.ofMul q) = Additive.ofMul (∏ σ : K ≃ₐ[F] K, σ • q) :=
  Representation.norm_ofMulDistribMulAction_eq (G := K ≃ₐ[F] K) (M := IdeleClassGroup K)
    (Additive.ofMul q)

theorem ideleRep_norm_ofMul (y : 𝕀[K]) :
    (ρI F K).norm (Additive.ofMul y) = Additive.ofMul (∏ σ : K ≃ₐ[F] K, σ • y) :=
  Representation.norm_ofMulDistribMulAction_eq (G := K ≃ₐ[F] K) (M := Idele K) (Additive.ofMul y)

/-- A vanishing `Ĥ⁻¹` is a statement about the kernel of the norm. -/
theorem le_coinvariantsKer_of_subsingleton {G : Type} [Group G] [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℤ V] (ρ : Representation ℤ G V)
    (h : Subsingleton (tateCohomology (Rep.of ρ) (-1))) :
    LinearMap.ker ρ.norm ≤ Representation.Coinvariants.ker ρ := by
  letI : Module ℤ ↥(LinearMap.ker (Representation.norm ρ)) :=
    (LinearMap.ker (Representation.norm ρ)).module
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso ρ
  haveI hsub : Subsingleton ((LinearMap.ker (Representation.norm ρ)) ⧸
      (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
        (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2)))) :=
    e.symm.injective.subsingleton
  have htop : (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
      (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2))) = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hsub
  intro x hx
  have hmem : (⟨x, hx⟩ : LinearMap.ker (Representation.norm ρ)) ∈
      (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
        (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2))) := by
    rw [htop]; exact Submodule.mem_top
  simpa [Representation.Coinvariants.ker] using hmem

theorem principalIdele_injective (F : Type) [Field F] [NumberField F] :
    Function.Injective (Idele.principalIdele F) := by
  intro x y h
  obtain ⟨v⟩ := (inferInstance : Nonempty (Place F))
  have h' : (Idele.principalIdele F x) v = (Idele.principalIdele F y) v := by rw [h]
  rw [Idele.principalIdele_apply, Idele.principalIdele_apply] at h'
  exact Units.map_injective (RingHom.injective (algebraMap F (Place.localField F v))) h'

theorem exists_placeOver (v : Place F) : ∃ w : Place K, Place.LiesOver w v :=
  Inclusion.globalCFT_exists_placeOver_of_finiteDimensional (K := F) (L := K) v

noncomputable def placeOver (v : Place F) : Place K := Classical.choose (exists_placeOver F K v)

theorem liesOver_placeOver (v : Place F) : Place.LiesOver (placeOver F K v) v :=
  Classical.choose_spec (exists_placeOver F K v)

noncomputable def placeUnder (w : Place K) : Place F :=
  Classical.choose (Inclusion.globalCFT_exists_placeUnder (K := F) (L := K) w)

theorem liesOver_placeUnder (w : Place K) : Place.LiesOver w (placeUnder F K w) :=
  Classical.choose_spec (Inclusion.globalCFT_exists_placeUnder (K := F) (L := K) w)

noncomputable def ideleInclusion : 𝕀[F] →* 𝕀[K] :=
  Classical.choose (Inclusion.globalCFT_ideleInclusion_exists (K := F) (L := K)
    (placeUnder F K) (liesOver_placeUnder F K))

theorem ideleInclusion_apply (x : 𝕀[F]) (w : Place K) :
    ideleInclusion F K x w =
      Place.localAlgebraMapUnits w (placeUnder F K w) (liesOver_placeUnder F K w)
        (x (placeUnder F K w)) :=
  Classical.choose_spec (Inclusion.globalCFT_ideleInclusion_exists (K := F) (L := K)
    (placeUnder F K) (liesOver_placeUnder F K)) x w

theorem ideleInclusion_principalIdele (a : Fˣ) :
    ideleInclusion F K (Idele.principalIdele F a) =
      Idele.principalIdele K (Units.map (algebraMap F K).toMonoidHom a) :=
  Inclusion.globalCFT_ideleInclusion_principalIdele (placeUnder F K) (liesOver_placeUnder F K)
    (ideleInclusion F K) (ideleInclusion_apply F K) a

theorem ideleInclusion_smul (σ : K ≃ₐ[F] K) (x : 𝕀[F]) :
    σ • ideleInclusion F K x = ideleInclusion F K x :=
  Inclusion.globalCFT_ideleInclusion_smul (placeUnder F K) (liesOver_placeUnder F K)
    (ideleInclusion F K) (ideleInclusion_apply F K) σ x

theorem component_transport (x : 𝕀[F]) {a b : Place F} (h : a = b) : x b = h ▸ x a := by
  cases h; rfl

theorem rec_symm_rec {α : Sort*} {β : α → Sort*} {a b : α} (h : a = b) (x : β a) :
    h.symm ▸ (h ▸ x) = x := by
  cases h; rfl

theorem rec_rec_symm {α : Sort*} {β : α → Sort*} {a b : α} (h : a = b) (x : β b) :
    h ▸ (h.symm ▸ x) = x := by
  cases h; rfl

theorem transport_component (x : 𝕀[F]) {a b : Place F} (h : a = b) : h ▸ x a = x b := by
  cases h; rfl

theorem ideleInclusion_injective : Function.Injective (ideleInclusion F K) := by
  intro x y hxy
  apply Idele.ext
  intro v
  obtain ⟨w, hw⟩ := exists_placeOver F K v
  have hcomp' : (Place.localAlgebraMapUnits w (placeUnder F K w) (liesOver_placeUnder F K w))
      (x (placeUnder F K w)) =
    (Place.localAlgebraMapUnits w (placeUnder F K w) (liesOver_placeUnder F K w))
      (y (placeUnder F K w)) := by
    have h := congrArg (fun z : 𝕀[K] => z w) hxy
    rwa [ideleInclusion_apply, ideleInclusion_apply] at h
  have hcomp : x (placeUnder F K w) = y (placeUnder F K w) :=
    Inclusion.globalCFT_localAlgebraMapUnits_injective (liesOver_placeUnder F K w) hcomp'
  have huw : placeUnder F K w = v :=
    Inclusion.globalCFT_liesOver_unique (liesOver_placeUnder F K w) hw
  have h4 : huw ▸ x (placeUnder F K w) = huw ▸ y (placeUnder F K w) :=
    congrArg (fun t => huw ▸ t) hcomp
  rw [transport_component F x huw, transport_component F y huw] at h4
  exact h4

theorem prod_smul_eq_ideleInclusion_normIdeleHom (y : 𝕀[K]) :
    (∏ σ : K ≃ₐ[F] K, σ • y) = ideleInclusion F K (Idele.normIdeleHom F K y) :=
  Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom (placeUnder F K) (liesOver_placeUnder F K)
    (ideleInclusion F K) (ideleInclusion_apply F K) y

theorem prod_smul_eq_one_iff_normIdeleHom_eq_one (y : 𝕀[K]) :
    (∏ σ : K ≃ₐ[F] K, σ • y) = 1 ↔ Idele.normIdeleHom F K y = 1 := by
  rw [prod_smul_eq_ideleInclusion_normIdeleHom F K y]
  constructor
  · intro h
    exact ideleInclusion_injective F K (by rw [h, map_one])
  · intro h
    rw [h, map_one]

theorem normIdeleHom_smul (σ : K ≃ₐ[F] K) (y : 𝕀[K]) :
    Idele.normIdeleHom F K (σ • y) = Idele.normIdeleHom F K y := by
  apply ideleInclusion_injective F K
  rw [← prod_smul_eq_ideleInclusion_normIdeleHom F K (σ • y),
    ← prod_smul_eq_ideleInclusion_normIdeleHom F K y]
  rw [show (∏ τ : K ≃ₐ[F] K, τ • (σ • y)) = ∏ τ : K ≃ₐ[F] K, (τ * σ) • y from
    Finset.prod_congr rfl (fun τ _ => (mul_smul τ σ y).symm)]
  exact Equiv.prod_comp (Equiv.mulRight σ) (fun τ : K ≃ₐ[F] K => τ • y)

theorem normIdeleHom_mul_smul_inv (σ : K ≃ₐ[F] K) (y : 𝕀[K]) :
    Idele.normIdeleHom F K (σ • y * y⁻¹) = 1 := by
  rw [map_mul, map_inv, normIdeleHom_smul, mul_inv_cancel]

theorem exists_principalIdele_of_mem_principalSubgroup {z : 𝕀[F]}
    (hz : ideleInclusion F K z ∈ Idele.principalSubgroup K) :
    ∃ a : Fˣ, Idele.principalIdele F a = z := by
  obtain ⟨a, ha⟩ := Idele.mem_principalSubgroup.mp hz
  have hfix : ∀ σ : K ≃ₐ[F] K, Units.map σ.toMonoidHom a = a := by
    intro σ
    apply principalIdele_injective K
    rw [← Galois.globalCFT_smul_principalIdele σ a]
    have h2 : σ • Idele.principalIdele K a = Idele.principalIdele K a := by
      rw [ha, ideleInclusion_smul]
    exact h2
  obtain ⟨b, hb⟩ : ∃ b : F, algebraMap F K b = (a : K) :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := F) (E := K) (a : K)).mpr (fun σ => by
      have h := congrArg (fun u : Kˣ => (u : K)) (hfix σ)
      simpa using h)
  have hb0 : b ≠ 0 := by
    intro h0
    have h : (a : K) = 0 := by rw [← hb, h0, map_zero]
    exact Units.ne_zero a h
  refine ⟨Units.mk0 b hb0, ?_⟩
  apply ideleInclusion_injective F K
  rw [ideleInclusion_principalIdele, ← ha]
  congr 1
  exact Units.ext (by simpa using hb)

/-! ## The norm is invariant, and the augmentation submodule of `C_K` -/

theorem norm_apply_comm {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V] [Module ℤ V]
    (ρ : Representation ℤ G V) (σ : G) (v : V) : ρ.norm (ρ σ v) = ρ.norm v := by
  have h1 : ρ.norm (ρ σ v) = ∑ g : G, ρ (g * σ) v := by
    simp only [Representation.norm, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun g _ => by rw [map_mul]; rfl)
  have h2 : ρ.norm v = ∑ g : G, ρ g v := by
    simp only [Representation.norm, LinearMap.sum_apply]
  rw [h1, h2]
  exact Equiv.sum_comp (Equiv.mulRight σ) (fun g : G => ρ g v)

theorem sub_mem_ker (σ : K ≃ₐ[F] K) (v : Additive (C[K])) :
    (ρC F K) σ v - v ∈ LinearMap.ker (ρC F K).norm := by
  rw [LinearMap.mem_ker, map_sub, norm_apply_comm, sub_self]

theorem ofMul_sub_ofMul {α : Type*} [Group α] (a b : α) :
    Additive.ofMul a - Additive.ofMul b = Additive.ofMul (a * b⁻¹) := by
  rw [sub_eq_add_neg, ← ofMul_inv, ← ofMul_mul]

theorem mem_toIntSubmodule {M : Type*} [AddCommGroup M] (S : AddSubgroup M) (x : M) :
    x ∈ S.toIntSubmodule ↔ x ∈ S := by
  rw [show x ∈ S.toIntSubmodule ↔ x ∈ (S.toIntSubmodule : Set M) from Iff.rfl,
    AddSubgroup.coe_toIntSubmodule]
  rfl

/-- The augmentation submodule of the idèle class group: the span of the elements `σ • q - q`. -/
def augSub : Submodule ℤ (Additive (C[K])) :=
  Submodule.span ℤ (Set.range fun p : (K ≃ₐ[F] K) × Additive (C[K]) =>
    (ρC F K) p.1 p.2 - p.2)

theorem gen_eq_rep {V : Type} [CommGroup V] [MulDistribMulAction (K ≃ₐ[F] K) V]
    (σ : K ≃ₐ[F] K) (v : Additive V) :
    (Representation.ofMulDistribMulAction (K ≃ₐ[F] K) V) σ v - v =
      Additive.ofMul (σ • Additive.toMul v * (Additive.toMul v)⁻¹) := by
  conv_lhs => rw [← ofMul_toMul v]
  rw [Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul, ofMul_sub_ofMul]

theorem gen_eq (σ : K ≃ₐ[F] K) (v : Additive (C[K])) :
    (ρC F K) σ v - v = Additive.ofMul (σ • Additive.toMul v * (Additive.toMul v)⁻¹) := by
  conv_lhs => rw [← ofMul_toMul v]
  rw [Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul, ofMul_sub_ofMul]

theorem gen_eq_idele (σ : K ≃ₐ[F] K) (v : Additive (𝕀[K])) :
    (ρI F K) σ v - v = Additive.ofMul (σ • Additive.toMul v * (Additive.toMul v)⁻¹) := by
  conv_lhs => rw [← ofMul_toMul v]
  rw [Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul, ofMul_sub_ofMul]

theorem gen_eq_ofMul (σ : K ≃ₐ[F] K) (q : C[K]) :
    (ρC F K) σ (Additive.ofMul q) - Additive.ofMul q = Additive.ofMul (σ • q * q⁻¹) := by
  rw [gen_eq, toMul_ofMul]

theorem augSub_eq_span_closure :
    augSub F K = Submodule.span ℤ (Set.range fun p : (K ≃ₐ[F] K) × C[K] =>
      Additive.ofMul (p.1 • p.2 * p.2⁻¹)) := by
  apply le_antisymm
  · rw [augSub, Submodule.span_le]
    rintro _ ⟨⟨σ, v⟩, rfl⟩
    show (ρC F K) σ v - v ∈ Submodule.span ℤ (Set.range fun p : (K ≃ₐ[F] K) × C[K] =>
      Additive.ofMul (p.1 • p.2 * p.2⁻¹))
    rw [gen_eq]
    exact Submodule.subset_span ⟨(σ, Additive.toMul v), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨σ, q⟩, rfl⟩
    show Additive.ofMul (σ • q * q⁻¹) ∈ augSub F K
    rw [← gen_eq_ofMul]
    exact Submodule.subset_span ⟨(σ, Additive.ofMul q), rfl⟩

/-- The additive map `𝕀_K → C_K` induced by the quotient map. -/
def mkAdd : Additive (𝕀[K]) →+ Additive (C[K]) where
  toFun y := Additive.ofMul (IdeleClassGroup.mk K (Additive.toMul y))
  map_zero' := by rw [toMul_zero, map_one, ofMul_one]
  map_add' x y := by rw [toMul_add, map_mul, ofMul_mul]

theorem mkAdd_ofMul (y : 𝕀[K]) :
    mkAdd K (Additive.ofMul y) = Additive.ofMul (IdeleClassGroup.mk K y) := rfl

theorem toMul_mkAdd (v : Additive (𝕀[K])) :
    Additive.toMul (mkAdd K v) = IdeleClassGroup.mk K (Additive.toMul v) := rfl

theorem mkAdd_gen (σ : K ≃ₐ[F] K) (v : Additive (𝕀[K])) :
    mkAdd K ((ρI F K) σ v - v) = (ρC F K) σ (mkAdd K v) - mkAdd K v := by
  rw [gen_eq_idele, mkAdd_ofMul, gen_eq, toMul_mkAdd, map_mul, map_inv,
    IdeleClassGroup.smul_mk]

/-! ## The vanishing `Ĥ⁻¹(G, 𝕀_K) = 0` in the form used below -/

theorem mk_mem_augSub_of_normIdeleHom_eq_one (hunr : _root_.CFTLib.IsUnramified F K)
    {z : 𝕀[K]} (hz : Idele.normIdeleHom F K z = 1) :
    Additive.ofMul (IdeleClassGroup.mk K z) ∈ augSub F K := by
  haveI hsub : Subsingleton (tateCohomology (ideleRep F K) (-1)) :=
    tateCohomology_neg_one_idele_of_isUnramified F K hunr
  have hzprod : (∏ σ : K ≃ₐ[F] K, σ • z) = 1 :=
    (prod_smul_eq_one_iff_normIdeleHom_eq_one F K z).mpr hz
  have hker : Additive.ofMul z ∈ LinearMap.ker (ρI F K).norm := by
    rw [LinearMap.mem_ker, ideleRep_norm_ofMul, hzprod]
    rfl
  have hcoin : Additive.ofMul z ∈ Representation.Coinvariants.ker (ρI F K) :=
    le_coinvariantsKer_of_subsingleton (ρI F K) hsub hker
  have hle : Representation.Coinvariants.ker (ρI F K) ≤
      Submodule.comap (mkAdd K).toIntLinearMap (augSub F K) := by
    rw [Representation.Coinvariants.ker, Submodule.span_le]
    rintro _ ⟨⟨σ, v⟩, rfl⟩
    show mkAdd K ((ρI F K) σ v - v) ∈ augSub F K
    rw [mkAdd_gen]
    exact Submodule.subset_span ⟨(σ, mkAdd K v), rfl⟩
  exact hle hcoin

/-! ## The comparison map `ker(N_C) → (Fˣ ∩ N𝕀_K)/(N Kˣ)` -/

def normPreimage : Subgroup 𝕀[K] :=
  (Idele.principalSubgroup F).comap (Idele.normIdeleHom F K)

theorem mem_normPreimage {y : 𝕀[K]} :
    y ∈ normPreimage F K ↔ Idele.normIdeleHom F K y ∈ Idele.principalSubgroup F := Iff.rfl

noncomputable def normUnits (y : 𝕀[K]) (hy : y ∈ normPreimage F K) : Fˣ :=
  Classical.choose (Idele.mem_principalSubgroup.mp ((mem_normPreimage F K).mp hy))

theorem principalIdele_normUnits (y : 𝕀[K]) (hy : y ∈ normPreimage F K) :
    Idele.principalIdele F (normUnits F K y hy) = Idele.normIdeleHom F K y :=
  Classical.choose_spec (Idele.mem_principalSubgroup.mp ((mem_normPreimage F K).mp hy))

theorem normUnits_mul {y y' : 𝕀[K]} (hy : y ∈ normPreimage F K) (hy' : y' ∈ normPreimage F K) :
    normUnits F K (y * y') (mul_mem hy hy') = normUnits F K y hy * normUnits F K y' hy' := by
  apply principalIdele_injective F
  rw [map_mul, principalIdele_normUnits, principalIdele_normUnits, principalIdele_normUnits,
    map_mul]

theorem normUnits_mem (y : 𝕀[K]) (hy : y ∈ normPreimage F K) :
    normUnits F K y hy ∈ normPrincipalPreimage F K := by
  rw [normPrincipalPreimage, Subgroup.mem_comap, Idele.normImage_eq_map, MonoidHom.mem_range]
  exact ⟨y, (principalIdele_normUnits F K y hy).symm⟩

theorem normUnits_one (h : (1 : 𝕀[K]) ∈ normPreimage F K) : normUnits F K 1 h = 1 := by
  apply principalIdele_injective F
  rw [principalIdele_normUnits, map_one, map_one]

theorem mem_normPreimage_mul_smul_inv (σ : K ≃ₐ[F] K) (y : 𝕀[K]) :
    σ • y * y⁻¹ ∈ normPreimage F K :=
  (mem_normPreimage F K).mpr (by
    rw [normIdeleHom_mul_smul_inv]
    exact Subgroup.one_mem _)

/-- The norm of an idèle whose norm is principal, as an element of `Fˣ ∩ N𝕀_K`. -/
noncomputable def normUnitsHom : normPreimage F K →* normPrincipalPreimage F K where
  toFun y := ⟨normUnits F K y.1 y.2, normUnits_mem F K y.1 y.2⟩
  map_one' := by
    apply Subtype.ext
    change normUnits F K 1 (Subgroup.one_mem (normPreimage F K)) = 1
    exact normUnits_one F K _
  map_mul' y y' := by
    apply Subtype.ext
    change normUnits F K (y.1 * y'.1) (mul_mem y.2 y'.2) =
      normUnits F K y.1 y.2 * normUnits F K y'.1 y'.2
    exact normUnits_mul F K y.2 y'.2

theorem mk_eq_mk_of_mul_mem (a a' : Fˣ) (ha : a ∈ normPrincipalPreimage F K)
    (ha' : a' ∈ normPrincipalPreimage F K) (h : a * a'⁻¹ ∈ unitsNormSubgroup F K) :
    (QuotientAddGroup.mk (Additive.ofMul (⟨a, ha⟩ : normPrincipalPreimage F K)) :
        normQuotient F K) =
      QuotientAddGroup.mk (Additive.ofMul (⟨a', ha'⟩ : normPrincipalPreimage F K)) := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  have hsub : Additive.ofMul (⟨a, ha⟩ : normPrincipalPreimage F K) -
      Additive.ofMul (⟨a', ha'⟩ : normPrincipalPreimage F K) =
      Additive.ofMul (⟨a * a'⁻¹, mul_mem ha (inv_mem ha')⟩ : normPrincipalPreimage F K) := by
    rw [ofMul_sub_ofMul]
    congr 1
  rw [hsub]
  simpa only [Additive.mem_toAddSubgroup, Subgroup.mem_subgroupOf, toMul_ofMul] using h

noncomputable def kerLift (x : ↥(LinearMap.ker (ρC F K).norm)) : 𝕀[K] :=
  Classical.choose (IdeleClassGroup.mk_surjective K (Additive.toMul (x : Additive (C[K]))))

theorem mk_kerLift (x : ↥(LinearMap.ker (ρC F K).norm)) :
    IdeleClassGroup.mk K (kerLift F K x) = Additive.toMul (x : Additive (C[K])) :=
  Classical.choose_spec (IdeleClassGroup.mk_surjective K (Additive.toMul (x : Additive (C[K]))))

theorem kerLift_mem (x : ↥(LinearMap.ker (ρC F K).norm)) : kerLift F K x ∈ normPreimage F K := by
  rw [mem_normPreimage]
  have h1 : IdeleClassGroup.mk K (∏ σ : K ≃ₐ[F] K, σ • kerLift F K x) = 1 := by
    rw [map_prod]
    rw [Finset.prod_congr rfl (fun σ _ => (IdeleClassGroup.smul_mk σ (kerLift F K x)).symm)]
    rw [mk_kerLift F K x]
    have h3 := classRep_norm_ofMul F K (Additive.toMul (x : Additive (C[K])))
    rw [ofMul_toMul, x.2] at h3
    exact Additive.ofMul.injective (h3.symm.trans (ofMul_one (α := C[K])).symm)
  have hmem : (∏ σ : K ≃ₐ[F] K, σ • kerLift F K x) ∈ Idele.principalSubgroup K :=
    (QuotientGroup.eq_one_iff _).mp h1
  rw [prod_smul_eq_ideleInclusion_normIdeleHom F K (kerLift F K x)] at hmem
  obtain ⟨a, ha⟩ := exists_principalIdele_of_mem_principalSubgroup F K hmem
  rw [← ha]
  exact Idele.mem_principalSubgroup.mpr ⟨a, rfl⟩

/-- The comparison map `ker(N_C) → (Fˣ ∩ N𝕀_K)/(N Kˣ)`. -/
noncomputable def Ψfun (x : ↥(LinearMap.ker (ρC F K).norm)) : normQuotient F K :=
  QuotientAddGroup.mk (Additive.ofMul
    (normUnitsHom F K ⟨kerLift F K x, kerLift_mem F K x⟩))

theorem mk_kerUnits_eq_of_mk_eq {y y' : 𝕀[K]} (hy : y ∈ normPreimage F K)
    (hy' : y' ∈ normPreimage F K) (h : IdeleClassGroup.mk K y = IdeleClassGroup.mk K y') :
    (QuotientAddGroup.mk (Additive.ofMul (normUnitsHom F K ⟨y, hy⟩)) : normQuotient F K) =
      QuotientAddGroup.mk (Additive.ofMul (normUnitsHom F K ⟨y', hy'⟩)) := by
  have hmem : y⁻¹ * y' ∈ Idele.principalSubgroup K := IdeleClassGroup.mk_eq_mk_iff.mp h
  obtain ⟨b, hb⟩ := Idele.mem_principalSubgroup.mp hmem
  have hb' : y' = y * Idele.principalIdele K b := by rw [hb]; group
  have hkey : (normUnitsHom F K ⟨y', hy'⟩ : Fˣ) =
      (normUnitsHom F K ⟨y, hy⟩ : Fˣ) * Units.map (Algebra.norm F) b := by
    show normUnits F K y' hy' = normUnits F K y hy * Units.map (Algebra.norm F) b
    apply principalIdele_injective F
    rw [map_mul, principalIdele_normUnits, principalIdele_normUnits,
      ← Idele.normIdeleHom_principalIdele, hb', map_mul]
  refine mk_eq_mk_of_mul_mem F K _ _ _ _ ?_
  show (normUnitsHom F K ⟨y, hy⟩ : Fˣ) * ((normUnitsHom F K ⟨y', hy'⟩ : normPrincipalPreimage F K) : Fˣ)⁻¹ ∈ unitsNormSubgroup F K
  rw [hkey]
  have h1 : (normUnitsHom F K ⟨y, hy⟩ : Fˣ) *
      ((normUnitsHom F K ⟨y, hy⟩ : Fˣ) * Units.map (Algebra.norm F) b)⁻¹ =
      (Units.map (Algebra.norm F) b)⁻¹ := by
    simp [mul_inv_rev, mul_comm, mul_left_comm]
  rw [h1]
  exact inv_mem (MonoidHom.mem_range.mpr ⟨b, rfl⟩)

theorem Ψfun_zero : Ψfun F K 0 = 0 := by
  have h : IdeleClassGroup.mk K (kerLift F K 0) = IdeleClassGroup.mk K 1 := by
    rw [mk_kerLift]; rfl
  show QuotientAddGroup.mk (Additive.ofMul
    (normUnitsHom F K ⟨kerLift F K 0, kerLift_mem F K 0⟩)) = 0
  rw [mk_kerUnits_eq_of_mk_eq F K (kerLift_mem F K 0) (Subgroup.one_mem _) h]
  have hsub : (normUnitsHom F K ⟨(1 : 𝕀[K]), Subgroup.one_mem (normPreimage F K)⟩ :
      normPrincipalPreimage F K) = 1 := by
    apply Subtype.ext
    change normUnits F K 1 (Subgroup.one_mem (normPreimage F K)) = 1
    exact normUnits_one F K _
  rw [hsub]
  rfl

theorem Ψfun_add (x x' : ↥(LinearMap.ker (ρC F K).norm)) :
    Ψfun F K (x + x') = Ψfun F K x + Ψfun F K x' := by
  have hmk : IdeleClassGroup.mk K (kerLift F K (x + x')) =
      IdeleClassGroup.mk K (kerLift F K x * kerLift F K x') := by
    rw [map_mul, mk_kerLift, mk_kerLift, mk_kerLift]
    rw [show (↑(x + x') : Additive (C[K])) = ↑x + ↑x' from rfl, toMul_add]
  show QuotientAddGroup.mk (Additive.ofMul
      (normUnitsHom F K ⟨kerLift F K (x + x'), kerLift_mem F K (x + x')⟩)) =
    QuotientAddGroup.mk (Additive.ofMul
      (normUnitsHom F K ⟨kerLift F K x, kerLift_mem F K x⟩)) +
    QuotientAddGroup.mk (Additive.ofMul
      (normUnitsHom F K ⟨kerLift F K x', kerLift_mem F K x'⟩))
  rw [mk_kerUnits_eq_of_mk_eq F K (kerLift_mem F K (x + x'))
    (mul_mem (kerLift_mem F K x) (kerLift_mem F K x')) hmk]
  rw [show (⟨kerLift F K x * kerLift F K x',
      mul_mem (kerLift_mem F K x) (kerLift_mem F K x')⟩ : normPreimage F K) =
      ⟨kerLift F K x, kerLift_mem F K x⟩ * ⟨kerLift F K x', kerLift_mem F K x'⟩ from
    Subtype.ext rfl]
  rw [map_mul (normUnitsHom F K)]
  change (QuotientAddGroup.mk' ((unitsNormSubgroup F K).subgroupOf
      (normPrincipalPreimage F K)).toAddSubgroup)
      (Additive.ofMul ((normUnitsHom F K) ⟨kerLift F K x, kerLift_mem F K x⟩ *
        (normUnitsHom F K) ⟨kerLift F K x', kerLift_mem F K x'⟩)) =
    (QuotientAddGroup.mk' ((unitsNormSubgroup F K).subgroupOf
      (normPrincipalPreimage F K)).toAddSubgroup)
      (Additive.ofMul ((normUnitsHom F K) ⟨kerLift F K x, kerLift_mem F K x⟩)) +
    (QuotientAddGroup.mk' ((unitsNormSubgroup F K).subgroupOf
      (normPrincipalPreimage F K)).toAddSubgroup)
      (Additive.ofMul ((normUnitsHom F K) ⟨kerLift F K x', kerLift_mem F K x'⟩))
  rw [← map_add, ← ofMul_mul]

noncomputable def ΨHom : ↥(LinearMap.ker (ρC F K).norm) →+ normQuotient F K :=
  AddMonoidHom.mk' (Ψfun F K) (fun x y => Ψfun_add F K x y)

theorem ΨHom_gen (σ : K ≃ₐ[F] K) (v : Additive (C[K]))
    (hv : (ρC F K) σ v - v ∈ LinearMap.ker (ρC F K).norm) :
    ΨHom F K ⟨(ρC F K) σ v - v, hv⟩ = 0 := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : 𝕀[K], IdeleClassGroup.mk K w = Additive.toMul v :=
    IdeleClassGroup.mk_surjective K _
  have hmk : IdeleClassGroup.mk K (kerLift F K ⟨(ρC F K) σ v - v, hv⟩) =
      IdeleClassGroup.mk K (σ • w * w⁻¹) := by
    rw [mk_kerLift, show (Additive.toMul ((⟨(ρC F K) σ v - v, hv⟩ :
        ↥(LinearMap.ker (ρC F K).norm)) : Additive (C[K]))) =
        Additive.toMul ((ρC F K) σ v - v) from rfl, gen_eq, toMul_ofMul, ← hw, map_mul,
      map_inv, IdeleClassGroup.smul_mk]
  have hunits : (normUnitsHom F K ⟨σ • w * w⁻¹, mem_normPreimage_mul_smul_inv F K σ w⟩ :
      normPrincipalPreimage F K) = 1 := by
    apply Subtype.ext
    show normUnits F K (σ • w * w⁻¹) (mem_normPreimage_mul_smul_inv F K σ w) = 1
    apply principalIdele_injective F
    rw [principalIdele_normUnits, map_one, normIdeleHom_mul_smul_inv]
  show QuotientAddGroup.mk (Additive.ofMul (normUnitsHom F K
      ⟨kerLift F K ⟨(ρC F K) σ v - v, hv⟩,
        kerLift_mem F K ⟨(ρC F K) σ v - v, hv⟩⟩)) = 0
  rw [mk_kerUnits_eq_of_mk_eq F K (kerLift_mem F K _)
    (mem_normPreimage_mul_smul_inv F K σ w) hmk, hunits]
  rfl

theorem comap_augSub_le_ker :
    Submodule.comap (LinearMap.ker (ρC F K).norm).subtype (augSub F K) ≤
      (ΨHom F K).ker.toIntSubmodule := by
  have hmap : augSub F K ≤ Submodule.map (LinearMap.ker (ρC F K).norm).subtype
      ((ΨHom F K).ker.toIntSubmodule) := by
    rw [augSub, Submodule.span_le]
    rintro _ ⟨⟨σ, v⟩, rfl⟩
    refine Submodule.mem_map.mpr ⟨⟨(ρC F K) σ v - v, sub_mem_ker F K σ v⟩, ?_, rfl⟩
    rw [mem_toIntSubmodule, AddMonoidHom.mem_ker]
    exact ΨHom_gen F K σ v (sub_mem_ker F K σ v)
  intro x hx
  rw [Submodule.mem_comap] at hx
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hmap hx)
  have hyx' : (y : Additive (C[K])) = (x : Additive (C[K])) := by simpa using hyx
  have : y = x := Subtype.ext hyx'
  rw [mem_toIntSubmodule] at hy ⊢
  simpa [this] using hy

theorem ker_le_comap_augSub (hunr : _root_.CFTLib.IsUnramified F K) :
    (ΨHom F K).ker.toIntSubmodule ≤
      Submodule.comap (LinearMap.ker (ρC F K).norm).subtype (augSub F K) := by
  intro x hx
  rw [mem_toIntSubmodule, AddMonoidHom.mem_ker] at hx
  rw [Submodule.mem_comap]
  have hU : ((normUnitsHom F K ⟨kerLift F K x, kerLift_mem F K x⟩ :
      normPrincipalPreimage F K) : Fˣ) ∈ unitsNormSubgroup F K := by
    have h : QuotientAddGroup.mk (Additive.ofMul (normUnitsHom F K
        ⟨kerLift F K x, kerLift_mem F K x⟩)) = (0 : normQuotient F K) := hx
    rw [QuotientAddGroup.eq_zero_iff, Additive.mem_toAddSubgroup,
      Subgroup.mem_subgroupOf] at h
    exact h
  obtain ⟨b, hb⟩ := hU
  have hb' : Units.map (Algebra.norm F) b =
      normUnits F K (kerLift F K x) (kerLift_mem F K x) := by
    rw [hb]; rfl
  have hnorm : Idele.normIdeleHom F K (kerLift F K x * (Idele.principalIdele K b)⁻¹) = 1 := by
    rw [map_mul, map_inv, Idele.normIdeleHom_principalIdele,
      ← principalIdele_normUnits F K (kerLift F K x) (kerLift_mem F K x), hb', mul_inv_cancel]
  have haug := mk_mem_augSub_of_normIdeleHom_eq_one F K hunr hnorm
  rw [map_mul, map_inv,
    show IdeleClassGroup.mk K (Idele.principalIdele K b) = 1 from
      (QuotientGroup.eq_one_iff _).mpr ⟨b, rfl⟩, inv_one, mul_one, mk_kerLift] at haug
  exact haug

theorem ΨHom_surj : Function.Surjective (ΨHom F K) := by
  intro z
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective
    ((unitsNormSubgroup F K).subgroupOf (normPrincipalPreimage F K)).toAddSubgroup z
  set a₀ : normPrincipalPreimage F K := Additive.toMul a with ha₀
  have hmem : Idele.principalIdele F (a₀ : Fˣ) ∈ Idele.normImage F K :=
    Subgroup.mem_comap.mp a₀.2
  rw [Idele.normImage_eq_map, MonoidHom.mem_range] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hy_mem : y ∈ normPreimage F K := (mem_normPreimage F K).mpr (by
    rw [hy]
    exact Idele.mem_principalSubgroup.mpr ⟨(a₀ : Fˣ), rfl⟩)
  have hker : Additive.ofMul (IdeleClassGroup.mk K y) ∈ LinearMap.ker (ρC F K).norm := by
    rw [LinearMap.mem_ker, classRep_norm_ofMul]
    rw [Finset.prod_congr rfl (fun σ _ => IdeleClassGroup.smul_mk σ y), ← map_prod,
      prod_smul_eq_ideleInclusion_normIdeleHom F K y, hy, ideleInclusion_principalIdele]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨Units.map (algebraMap F K).toMonoidHom (a₀ : Fˣ), rfl⟩
  refine ⟨⟨Additive.ofMul (IdeleClassGroup.mk K y), hker⟩, ?_⟩
  have h0 : IdeleClassGroup.mk K (kerLift F K ⟨Additive.ofMul (IdeleClassGroup.mk K y), hker⟩)
      = IdeleClassGroup.mk K y := by
    rw [mk_kerLift]; rfl
  show QuotientAddGroup.mk (Additive.ofMul (normUnitsHom F K
      ⟨kerLift F K ⟨Additive.ofMul (IdeleClassGroup.mk K y), hker⟩,
        kerLift_mem F K ⟨Additive.ofMul (IdeleClassGroup.mk K y), hker⟩⟩)) = z
  rw [mk_kerUnits_eq_of_mk_eq F K (kerLift_mem F K _) hy_mem h0]
  have hval : normUnitsHom F K ⟨y, hy_mem⟩ = a₀ := by
    apply Subtype.ext
    show (normUnits F K y hy_mem : Fˣ) = (a₀ : Fˣ)
    refine principalIdele_injective F ?_
    rw [principalIdele_normUnits]
    exact hy
  rw [hval, ha₀, ofMul_toMul]
  simpa using ha

end NormQuotientIso

/-- **Step 2 of Roquette's computation.**  For `K/F` a finite Galois extension of number fields
unramified at every place, the `(-1)`-st Tate cohomology of the idèle class group `C_K` is the
quotient `(Fˣ ∩ N_{K/F} 𝕀_K) / N_{K/F} Kˣ`. -/
theorem tateCohomology_neg_one_iso_normQuotient (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (hunr : _root_.CFTLib.IsUnramified F K) :
    Nonempty (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep F K) (-1) ≃ₗ[ℤ]
      NK.CFTLib.normQuotient F K) := by
  obtain ⟨e1⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso
    ((IdeleClassGroup.rep F K).ρ)
  have hker : (NormQuotientIso.ΨHom F K).ker.toIntSubmodule =
      Submodule.comap (LinearMap.ker (NormQuotientIso.ρC F K).norm).subtype (NormQuotientIso.augSub F K) :=
    le_antisymm (NormQuotientIso.ker_le_comap_augSub F K hunr) (NormQuotientIso.comap_augSub_le_ker F K)
  have hkerA : (NormQuotientIso.ΨHom F K).ker =
      (Submodule.comap (LinearMap.ker (NormQuotientIso.ρC F K).norm).subtype (NormQuotientIso.augSub F K)).toAddSubgroup := by
    rw [show (NormQuotientIso.ΨHom F K).ker = ((NormQuotientIso.ΨHom F K).ker.toIntSubmodule).toAddSubgroup from
      (AddSubgroup.toIntSubmodule_toAddSubgroup _).symm, hker]
  have hle : (Submodule.comap (LinearMap.ker (NormQuotientIso.ρC F K).norm).subtype (NormQuotientIso.augSub F K)).toAddSubgroup
      ≤ (NormQuotientIso.ΨHom F K).ker := hkerA.ge
  have hbij : Function.Bijective
      (QuotientAddGroup.lift
        ((Submodule.comap (LinearMap.ker (NormQuotientIso.ρC F K).norm).subtype (NormQuotientIso.augSub F K)).toAddSubgroup)
        (NormQuotientIso.ΨHom F K) hle) := by
    constructor
    · intro a b hab
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective b
      rw [QuotientAddGroup.lift_mk, QuotientAddGroup.lift_mk] at hab
      rw [QuotientAddGroup.eq_iff_sub_mem]
      have hx : x - y ∈ (NormQuotientIso.ΨHom F K).ker := by
        rw [AddMonoidHom.mem_ker, map_sub, hab, sub_self]
      rwa [hkerA] at hx
    · intro y
      obtain ⟨x, rfl⟩ := NormQuotientIso.ΨHom_surj F K y
      exact ⟨QuotientAddGroup.mk x, by rw [QuotientAddGroup.lift_mk]⟩
  exact ⟨e1.trans ((AddEquiv.ofBijective _ hbij).toIntLinearEquiv
    (modM := inferInstance) (modM₂ := inferInstance))⟩

end NK.CFTLib
