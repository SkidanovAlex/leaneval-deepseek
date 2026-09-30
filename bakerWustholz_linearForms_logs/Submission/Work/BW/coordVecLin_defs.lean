import Mathlib
import Submission.Work.BW.kcb_defs
import Submission.Work.BW.coordVec_kerVecs_of_mem_kerLattice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `ℤ`-linear map `x ↦ coordVec x`, and the pullback of the kernel lattice

`Work.BW.coordVec` sends an integral vector `x ∈ (𝓞 F)^N` to its mixed coordinates in
`CoordSpace F N = ℝ^{[F:ℚ]·N}`.  This file packages it as a `ℤ`-linear map `coordVecLin`, proves
that it is injective, and identifies the pullback `(kerLattice a).comap coordVecLin` with the set
`kerVecs a` of integral kernel vectors of the matrix `a`.

The pullback `kerVecs a` is the "unmixed" model of the kernel lattice: it is a `ℤ`-submodule of
the free `ℤ`-module `(𝓞 F)^N`, and `coordVecLin` restricts to an isomorphism
`(kerLattice a).comap coordVecLin ≃ kerLattice a`.
-/

namespace Work.BW

open Module NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- `x ↦ coordVec x`, as a `ℤ`-linear map from integral vectors to the coordinate space. -/
noncomputable def coordVecLin {N : ℕ} :
    (Fin N → RingOfIntegers F) →ₗ[ℤ] CoordSpace F N where
  toFun := coordVec (F := F)
  map_add' x y := coordVec_add (F := F) x y
  map_smul' n x := coordVec_zsmul (F := F) n x

@[simp] lemma coordVecLin_apply {N : ℕ} (x : Fin N → RingOfIntegers F) :
    coordVecLin (F := F) x = coordVec (F := F) x := rfl

/-- `coordVec` is injective. -/
lemma coordVec_injective {N : ℕ} : Function.Injective (coordVec (F := F) (N := N)) := by
  intro x y h
  funext j
  apply Subtype.ext
  apply NumberField.mixedEmbedding_injective F
  apply coord_injective (F := F)
  exact congrFun h j

lemma coordVecLin_injective {N : ℕ} : Function.Injective (coordVecLin (F := F) (N := N)) :=
  coordVec_injective

lemma coordVecLin_ker {N : ℕ} : LinearMap.ker (coordVecLin (F := F) (N := N)) = ⊥ :=
  LinearMap.ker_eq_bot.mpr coordVecLin_injective

/-- The pullback of the kernel lattice along `coordVecLin` is exactly the set of integral kernel
vectors of the matrix `a`. -/
lemma mem_comap_coordVecLin_iff {M N : ℕ} (a : Fin M → Fin N → F)
    (x : Fin N → RingOfIntegers F) :
    x ∈ (kerLattice (F := F) a).comap (coordVecLin (F := F)) ↔ x ∈ kerVecs (F := F) a := by
  show coordVecLin (F := F) x ∈ kerLattice (F := F) a ↔ x ∈ kerVecs (F := F) a
  constructor
  · intro hx
    have h := (mem_kerLattice_iff (F := F) a (coordVecLin (F := F) x)).mp hx
    intro i
    have hi : (phiMap a (coordVecLin (F := F) x)) i = 0 := by rw [h.2]; rfl
    have hi2 : coord (F := F) (NumberField.mixedEmbedding F
        (∑ j, a i j * ((x j : RingOfIntegers F) : F))) = 0 := by
      rw [coordVecLin_apply, phiMap_coordVec] at hi
      exact hi
    exact coord_mixedEmbedding_eq_zero (F := F) hi2
  · intro hx
    refine (mem_kerLattice_iff (F := F) a (coordVecLin (F := F) x)).mpr ⟨?_, ?_⟩
    · show coordVec (F := F) x ∈ latL F N
      exact Submodule.subset_span (Set.mem_range_self x)
    · rw [coordVecLin_apply, phiMap_coordVec]
      funext i
      rw [hx i, map_zero]
      simp [coord]

/-- `coordVecLin` maps the pullback of the kernel lattice onto the kernel lattice. -/
theorem map_comap_coordVecLin {M N : ℕ} (a : Fin M → Fin N → F) :
    ((kerLattice (F := F) a).comap (coordVecLin (F := F))).map (coordVecLin (F := F))
      = kerLattice (F := F) a := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
  · rintro y hy
    obtain ⟨x, hx, hxy⟩ := coordVec_kerVecs_of_mem_kerLattice (F := F) a hy
    refine ⟨x, ?_, ?_⟩
    · show coordVecLin (F := F) x ∈ kerLattice (F := F) a
      rw [coordVecLin_apply, ← hxy]
      exact hy
    · rw [coordVecLin_apply, hxy]

/-- The elements `(B j : M)` of a basis `B` of a submodule `L` span `L` over `R`. -/
theorem span_range_coe_basis {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {ι : Type*} [Fintype ι] (L : Submodule R M) (B : Basis ι R L) :
    Submodule.span R (Set.range (fun j => (B j : M))) = L := by
  have h : L = Submodule.span R ((Submodule.subtype L) '' Set.range B) := by
    have h1 := Submodule.map_span (Submodule.subtype L) (Set.range B)
    rw [B.span_eq, Submodule.map_top, Submodule.range_subtype] at h1
    exact h1
  have h' : Set.range (fun j => (B j : M)) = (Submodule.subtype L) '' Set.range B :=
    Set.range_comp (Submodule.subtype L) (fun j => (B j : ↥L))
  rw [h']
  exact h.symm

end Work.BW
