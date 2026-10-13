import Submission.Work.DSM5b.HCF.Sorted
import Submission.Work.DSM5b.HCF.Filtration
import Submission.Work.DSM5b.HCF.stcD_comp


/-!
# The honest and sorted complexes as cochain complexes, and their functoriality

This file packages the honest tuple complex `CoeffSys.Htc` and the sorted (increasing tuple)
complex `Work.DSM5b.Stc` of a coefficient system as cochain complexes of `R`-modules, and it
provides the comparison map `toStc` as a morphism of complexes.

The main structural tool is `CoeffSys.Hom`, a morphism of coefficient systems (a family of linear
maps commuting with the restriction maps); it induces morphisms of the two complexes, and the
comparison map `toStc` is natural with respect to these.

The size filtration of a coefficient system (see `Submission/Work/DSM5b/HCF/Filtration.lean`) is
then exhibited as a short exact sequence of complexes for *both* the honest and the sorted complex;
the resulting commutative ladder of short exact sequences is what lets the comparison
`H^•(Htc 𝒜) ≅ H^•(Stc 𝒜)` be proved by descending induction on the filtration index.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

variable {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]

/-- The sorted differential, evaluated at an increasing tuple. -/
@[simp] lemma stcD_apply [LinearOrder ι] (𝒜 : CoeffSys R ι) (m : ℕ) (z : Stc 𝒜 m)
    (τ : IncrTuple (ι := ι) (m + 1)) :
    stcD 𝒜 m z τ = ∑ i : Fin (m + 2),
      ((-1 : R) ^ ((i : ℕ))) •
        𝒜.res (tupRng_del_subset i τ.1) (z ⟨tupDel i τ.1, τ.2.tupDel i⟩) := rfl

/-- The comparison map `toStc`, evaluated at an increasing tuple. -/
@[simp] lemma toStc_apply' [LinearOrder ι] (𝒜 : CoeffSys R ι) (m : ℕ) (z : 𝒜.Htc m)
    (τ : IncrTuple (ι := ι) m) : toStc 𝒜 m z τ = z τ.1 := rfl

namespace CoeffSys

/-- A morphism of coefficient systems: a family of `R`-linear maps compatible with the restriction
maps. -/
structure Hom (𝒜 ℬ : CoeffSys R ι) where
  φ : ∀ S : Finset ι, 𝒜.M S →ₗ[R] ℬ.M S
  comm : ∀ ⦃S T : Finset ι⦄ (h : S ⊆ T) (x : 𝒜.M S), φ T (𝒜.res h x) = ℬ.res h (φ S x)

namespace Hom

variable {𝒜 ℬ : CoeffSys R ι}

/-- The map induced by a morphism of coefficient systems on the honest tuple complexes. -/
noncomputable def htcMap (φ : Hom 𝒜 ℬ) (m : ℕ) : 𝒜.Htc m →ₗ[R] ℬ.Htc m where
  toFun z := fun τ => φ.φ (tupRng τ) (z τ)
  map_add' z z' := by
    funext τ
    simp only [Pi.add_apply, map_add]
  map_smul' r z := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]

@[simp] lemma htcMap_apply (φ : Hom 𝒜 ℬ) (m : ℕ) (z : 𝒜.Htc m) (τ : Fin (m + 1) → ι) :
    htcMap φ m z τ = φ.φ (tupRng τ) (z τ) := rfl

/-- The induced maps commute with the honest tuple differentials. -/
theorem htcMap_comm (φ : Hom 𝒜 ℬ) (m : ℕ) :
    (htcMap φ (m + 1)).comp (𝒜.htcD m) = (ℬ.htcD m).comp (htcMap φ m) := by
  apply LinearMap.ext
  intro z
  funext τ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, htcMap_apply, htcD_apply, htcD_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_smul, φ.comm, htcMap_apply]

section Sorted

variable [LinearOrder ι]

/-- The map induced by a morphism of coefficient systems on the sorted (increasing tuple)
complexes. -/
noncomputable def stcMap (φ : Hom 𝒜 ℬ) (m : ℕ) : Stc 𝒜 m →ₗ[R] Stc ℬ m where
  toFun z := fun τ => φ.φ (tupRng τ.1) (z τ)
  map_add' z z' := by
    funext τ
    simp only [Pi.add_apply, map_add]
  map_smul' r z := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]

@[simp] lemma stcMap_apply (φ : Hom 𝒜 ℬ) (m : ℕ) (z : Stc 𝒜 m) (τ : IncrTuple (ι := ι) m) :
    stcMap φ m z τ = φ.φ (tupRng τ.1) (z τ) := rfl

/-- The induced maps commute with the sorted differentials. -/
theorem stcMap_comm (φ : Hom 𝒜 ℬ) (m : ℕ) :
    (stcMap φ (m + 1)).comp (stcD 𝒜 m) = (stcD ℬ m).comp (stcMap φ m) := by
  apply LinearMap.ext
  intro z
  funext τ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, stcMap_apply, stcD_apply, stcD_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_smul, φ.comm, stcMap_apply]

/-- The comparison map `toStc` is natural with respect to morphisms of coefficient systems. -/
theorem toStc_natural (φ : Hom 𝒜 ℬ) (m : ℕ) :
    (stcMap φ m).comp (toStc 𝒜 m) = (toStc ℬ m).comp (htcMap φ m) := by
  apply LinearMap.ext
  intro z
  funext τ
  rfl

end Sorted

end Hom

/-- The sub-system of coefficients supported on the subsets of size at least `k`, as a coefficient
system. -/
noncomputable abbrev subCF (𝒜 : CoeffSys R ι) (k : ℕ) : CoeffSys R ι := (sizeSubSys 𝒜 k).toCoeff 𝒜

/-- The inclusion of the `(k+1)`-st into the `k`-th stage of the size filtration, as a morphism of
coefficient systems. -/
noncomputable def subInclHom (𝒜 : CoeffSys R ι) (k : ℕ) : Hom (subCF 𝒜 (k + 1)) (subCF 𝒜 k) where
  φ S := Submodule.inclusion (sizeSubSys_mono 𝒜 k S)
  comm := by
    intro S T h x
    exact sizeRestrict_inclusion 𝒜 k h x

/-- The quotient map onto the `k`-th graded piece of the size filtration, as a morphism of
coefficient systems. -/
noncomputable def subQuotHom (𝒜 : CoeffSys R ι) (k : ℕ) : Hom (subCF 𝒜 k) (exactlyCoeff 𝒜 k) where
  φ S := Submodule.mkQ (Submodule.inclusion (sizeSubSys_mono 𝒜 k S)).range
  comm := by
    intro S T h x
    exact exactlyCoeffRes_mkQ 𝒜 k h x

/-- The composite of the inclusion and the quotient map of the size filtration is zero (the
inclusion lands in the range that is being quotiented out). -/
lemma subQuot_comp_subIncl (𝒜 : CoeffSys R ι) (k : ℕ) (S : Finset ι)
    (x : (subCF 𝒜 (k + 1)).M S) :
    (subQuotHom 𝒜 k).φ S ((subInclHom 𝒜 k).φ S x) = 0 := by
  simp only [subQuotHom, subInclHom, Submodule.mkQ_apply]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ x)

end CoeffSys

open CoeffSys

/-- The honest tuple complex of a coefficient system, as a cochain complex of `R`-modules. -/
noncomputable abbrev htcComplex (𝒜 : CoeffSys R ι) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun m => ModuleCat.of R (𝒜.Htc m))
    (fun m => ModuleCat.ofHom (𝒜.htcD m))
    (fun m => by rw [← ModuleCat.ofHom_comp, 𝒜.htcD_comp, ModuleCat.ofHom_zero])

@[simp] lemma htcComplex_X (𝒜 : CoeffSys R ι) (m : ℕ) :
    (htcComplex 𝒜).X m = ModuleCat.of R (𝒜.Htc m) := by
  simp only [htcComplex, CochainComplex.of_X]

@[simp] lemma htcComplex_d (𝒜 : CoeffSys R ι) (m : ℕ) :
    (htcComplex 𝒜).d m (m + 1) = ModuleCat.ofHom (𝒜.htcD m) := by
  simp only [htcComplex, CochainComplex.of_d]

/-- The morphism of honest tuple complexes induced by a morphism of coefficient systems. -/
noncomputable def htcHom {𝒜 ℬ : CoeffSys R ι} (φ : CoeffSys.Hom 𝒜 ℬ) :
    htcComplex 𝒜 ⟶ htcComplex ℬ :=
  CochainComplex.ofHom (fun m => ModuleCat.ofHom (CoeffSys.Hom.htcMap φ m))
    (fun m => by
      simp only [htcComplex, CochainComplex.of_d, ← ModuleCat.ofHom_comp]
      rw [CoeffSys.Hom.htcMap_comm])

@[simp] lemma htcHom_f {𝒜 ℬ : CoeffSys R ι} (φ : CoeffSys.Hom 𝒜 ℬ) (m : ℕ) :
    (htcHom φ).f m = ModuleCat.ofHom (CoeffSys.Hom.htcMap φ m) := rfl

/-- The composite of the inclusion and the quotient morphisms of the size filtration of the honest
complex is zero. -/
theorem htc_subIncl_comp_subQuot (𝒜 : CoeffSys R ι) (k : ℕ) :
    htcHom (CoeffSys.subInclHom 𝒜 k) ≫ htcHom (CoeffSys.subQuotHom 𝒜 k) = 0 := by
  apply HomologicalComplex.hom_ext
  intro m
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f, htcHom_f, htcHom_f,
    ← ModuleCat.ofHom_comp]
  have hX : (CoeffSys.Hom.htcMap (CoeffSys.subQuotHom 𝒜 k) m).comp
      (CoeffSys.Hom.htcMap (CoeffSys.subInclHom 𝒜 k) m) = 0 := by
    apply LinearMap.ext
    intro x
    funext τ
    exact CoeffSys.subQuot_comp_subIncl 𝒜 k (tupRng τ) (x τ)
  rw [hX, ModuleCat.ofHom_zero]


section Sorted

variable [LinearOrder ι]

/-- The sorted (increasing tuple) complex of a coefficient system, as a cochain complex. -/
noncomputable abbrev stcComplex (𝒜 : CoeffSys R ι) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun m => ModuleCat.of R (Stc 𝒜 m))
    (fun m => ModuleCat.ofHom (stcD 𝒜 m))
    (fun m => by rw [← ModuleCat.ofHom_comp, HCF.stcD_comp 𝒜 m, ModuleCat.ofHom_zero])

@[simp] lemma stcComplex_X (𝒜 : CoeffSys R ι) (m : ℕ) :
    (stcComplex 𝒜).X m = ModuleCat.of R (Stc 𝒜 m) := by
  simp only [stcComplex, CochainComplex.of_X]

@[simp] lemma stcComplex_d (𝒜 : CoeffSys R ι) (m : ℕ) :
    (stcComplex 𝒜).d m (m + 1) = ModuleCat.ofHom (stcD 𝒜 m) := by
  simp only [stcComplex, CochainComplex.of_d]

/-- The morphism of sorted complexes induced by a morphism of coefficient systems. -/
noncomputable abbrev stcHom {𝒜 ℬ : CoeffSys R ι} (φ : CoeffSys.Hom 𝒜 ℬ) :
    stcComplex 𝒜 ⟶ stcComplex ℬ :=
  CochainComplex.ofHom (fun m => ModuleCat.ofHom (CoeffSys.Hom.stcMap φ m))
    (fun m => by
      simp only [stcComplex, CochainComplex.of_d, ← ModuleCat.ofHom_comp]
      rw [CoeffSys.Hom.stcMap_comm])

@[simp] lemma stcHom_f {𝒜 ℬ : CoeffSys R ι} (φ : CoeffSys.Hom 𝒜 ℬ) (m : ℕ) :
    (stcHom φ).f m = ModuleCat.ofHom (CoeffSys.Hom.stcMap φ m) := rfl

/-- The comparison morphism from the honest tuple complex to the sorted complex. -/
noncomputable abbrev toStcHom (𝒜 : CoeffSys R ι) : htcComplex 𝒜 ⟶ stcComplex 𝒜 :=
  CochainComplex.ofHom (fun m => ModuleCat.ofHom (toStc 𝒜 m))
    (fun m => by
      simp only [htcComplex, stcComplex, CochainComplex.of_d, ← ModuleCat.ofHom_comp]
      rw [toStc_comm])

@[simp] lemma toStcHom_f (𝒜 : CoeffSys R ι) (m : ℕ) :
    (toStcHom 𝒜).f m = ModuleCat.ofHom (toStc 𝒜 m) := rfl

/-- The composite of the inclusion and the quotient morphisms of the size filtration of the sorted
complex is zero. -/
theorem stcSubIncl_comp_subQuot (𝒜 : CoeffSys R ι) (k : ℕ) :
    stcHom (CoeffSys.subInclHom 𝒜 k) ≫ stcHom (CoeffSys.subQuotHom 𝒜 k) = 0 := by
  apply HomologicalComplex.hom_ext
  intro m
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f, stcHom_f, stcHom_f,
    ← ModuleCat.ofHom_comp]
  have hX : (CoeffSys.Hom.stcMap (CoeffSys.subQuotHom 𝒜 k) m).comp
      (CoeffSys.Hom.stcMap (CoeffSys.subInclHom 𝒜 k) m) = 0 := by
    apply LinearMap.ext
    intro x
    funext τ
    exact CoeffSys.subQuot_comp_subIncl 𝒜 k (tupRng τ.1) (x τ)
  rw [hX, ModuleCat.ofHom_zero]

/-- The comparison morphism is natural with respect to morphisms of coefficient systems. -/
theorem toStcHom_natural {𝒜 ℬ : CoeffSys R ι} (φ : CoeffSys.Hom 𝒜 ℬ) :
    htcHom φ ≫ toStcHom ℬ = toStcHom 𝒜 ≫ stcHom φ := by
  apply HomologicalComplex.hom_ext
  intro m
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, toStcHom_f, toStcHom_f,
    htcHom_f, stcHom_f]
  rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
  rw [show (CoeffSys.Hom.stcMap φ m).comp (toStc 𝒜 m) =
      (toStc ℬ m).comp (CoeffSys.Hom.htcMap φ m) from CoeffSys.Hom.toStc_natural φ m]

end Sorted

end Work.DSM5b
