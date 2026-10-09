import Mathlib
import Submission.NK.CFTLib.HRclean.ARLClean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary structure of the level-change maps `restrictHom` / `inclMK`

For a tower of number fields `K ⊆ M ⊆ E` with `M/K` and `E/K` Galois (and `E/M` Galois, which is a
consequence for the applications but not needed here), this file records:

* the identification `restrictHom = AlgEquiv.restrictNormalHom` of the "restrict to the image of
  `M` in `E`" map with Mathlib's restriction map to a normal subfield;
* the description of the kernel of `restrictHom` as the image of `Gal(E/M) ↪ Gal(E/K)`, i.e. as the
  subgroup of automorphisms fixing `M` pointwise, and the two canonical isomorphisms
  `Gal(E/M) ≃* ker(restrictHom)` and `Gal(E/K) ⧸ ker(restrictHom) ≃* Gal(M/K)`.

These are the bookkeeping facts needed to compare the concrete level-change maps of
`NK.CFTLib.HRclean.ARL.TransferSupport` (`resToGal`, `inflation`) with the abstract
inflation–restriction sequence for the normal subgroup `ker(restrictHom) ◁ Gal(E/K)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open NK.GlobalCFT CategoryTheory

namespace NK.CFTLib.HRclean.ARL

section Basic

variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field E]
  [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E]
  [IsScalarTower K M E] [FiniteDimensional K M] [FiniteDimensional K E]
  [IsGalois K M] [IsGalois K E] [IsGalois M E]

/-- **Surjectivity of the restriction map**: every `K`-automorphism of the normal subfield `M`
extends to `E`. -/
theorem restrictHom_surjective :
    Function.Surjective (restrictHom (K := K) (L := M) (E := E)) := by
  rw [NK.CFTLib.HRclean.ARL.restrictHom_eq_restrictNormalHom]
  exact AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := E)

/-- **The kernel of the restriction map is the subgroup of automorphisms fixing `M` pointwise.** -/
theorem mem_ker_restrictHom_iff (σ : Gal(E/K)) :
    σ ∈ (restrictHom (K := K) (L := M) (E := E)).ker ↔
      ∀ m : M, σ (algebraMap M E m) = algebraMap M E m := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h m
    rw [← restrictHom_apply_coe (K := K) (L := M) (E := E) σ m, h]
    rfl
  · intro h
    ext x
    apply (algebraMap M E).injective
    rw [restrictHom_apply_coe (K := K) (L := M) (E := E) σ x, h x]
    rfl

/-- **A `K`-automorphism of `E` lies in the image of `Gal(E/M)` iff it fixes `M` pointwise.** -/
theorem mem_range_inclMK_iff (σ : Gal(E/K)) :
    σ ∈ (inclMK (K := K) (M := M) (E := E)).range ↔
      ∀ m : M, σ (algebraMap M E m) = algebraMap M E m := by
  constructor
  · rintro ⟨g, rfl⟩ m
    exact g.commutes m
  · intro h
    refine ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun m => h m), ?_⟩
    ext x
    rfl

/-- **The kernel of the restriction map is the image of `Gal(E/M)`.** -/
theorem ker_restrictHom_eq_range_inclMK :
    (restrictHom (K := K) (L := M) (E := E)).ker = (inclMK (K := K) (M := M) (E := E)).range := by
  ext σ
  rw [mem_ker_restrictHom_iff, mem_range_inclMK_iff]

/-- **`Gal(E/M)` is the kernel of the restriction map**, as a group isomorphism, with the
computation rule `g ↦ inclMK g`. -/
theorem exists_rangeRestrictMulEquiv :
    ∃ e : Gal(E/M) ≃* (restrictHom (K := K) (L := M) (E := E)).ker,
      ∀ g : Gal(E/M), (e g : Gal(E/K)) = inclMK (K := K) (M := M) (E := E) g := by
  have hmem : ∀ g : Gal(E/M), inclMK (K := K) (M := M) (E := E) g
      ∈ (restrictHom (K := K) (L := M) (E := E)).ker := by
    intro g
    rw [mem_ker_restrictHom_iff]
    intro m
    exact g.commutes m
  let f : Gal(E/M) →* (restrictHom (K := K) (L := M) (E := E)).ker :=
    { toFun := fun g => ⟨inclMK (K := K) (M := M) (E := E) g, hmem g⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun g h => Subtype.ext (map_mul _ g h) }
  refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩, fun g => rfl⟩
  · intro g h gh
    have h2 : inclMK (K := K) (M := M) (E := E) g = inclMK (K := K) (M := M) (E := E) h :=
      congrArg Subtype.val gh
    ext x
    exact congrArg (fun (φ : E ≃ₐ[K] E) => φ x) h2
  · intro σ
    have hσ : (σ : Gal(E/K)) ∈ (inclMK (K := K) (M := M) (E := E)).range := by
      rw [mem_range_inclMK_iff]
      exact (mem_ker_restrictHom_iff (K := K) (M := M) (E := E) σ).1 σ.2
    obtain ⟨g, hg⟩ := hσ
    exact ⟨g, Subtype.ext hg⟩

/-- **The quotient by the restriction kernel is `Gal(M/K)`**, with the computation rule
`σ ↦ restrictHom σ`. -/
theorem exists_quotientRestrictMulEquiv :
    ∃ f : Gal(E/K) ⧸ (restrictHom (K := K) (L := M) (E := E)).ker ≃* Gal(M/K),
      ∀ σ : Gal(E/K),
        f (QuotientGroup.mk' (restrictHom (K := K) (L := M) (E := E)).ker σ)
          = restrictHom (K := K) (L := M) (E := E) σ := by
  refine ⟨QuotientGroup.liftEquiv (restrictHom (K := K) (L := M) (E := E)).ker
    restrictHom_surjective rfl, fun σ => ?_⟩
  exact QuotientGroup.liftEquiv_mk (N := (restrictHom (K := K) (L := M) (E := E)).ker)
    (hφ := restrictHom_surjective) (HN := rfl) σ

end Basic

end NK.CFTLib.HRclean.ARL
