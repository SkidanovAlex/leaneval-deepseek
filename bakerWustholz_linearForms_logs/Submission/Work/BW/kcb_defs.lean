import Mathlib
import Submission.Work.BW.siegel_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the kernel-lattice covolume bound

This file fixes the vocabulary used by `Submission/Work/BW/kernel_covolume_bound.lean`
(the lemma `Work.BW.kernel_covolume_bound`).

The mixed space `E = mixedSpace F` of a number field `F` is identified with `ℝ^{index F}` by
the standard basis `mixedEmbedding.stdBasis F`; the corresponding coordinate space is
`CoordSpace F N = ℝ^{d·N}` with `d = [F : ℚ]`.

* `mulCoord α` : multiplication by `α : F` on `E`, in coordinates;
* `phiMap a` : the `ℝ`-linear map `E^N → E^M` given by the rows `a i`, in coordinates;
* `latL N` : the coordinate model of the lattice `(𝓞 F)^N ⊆ E^N`;
* `mem_kerLattice_iff` : the kernel lattice is `latL N ⊓ ker (phiMap a)`.
-/

namespace Work.BW

open NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- The coordinate model of `E^N` for `E = mixedSpace F`. -/
abbrev CoordSpace (F : Type*) [Field F] (N : ℕ) :=
  Fin N → (NumberField.mixedEmbedding.index F → ℝ)

/-- Multiplication by `α : F` on the mixed space, in standard-basis coordinates:
`mulCoord α (coord v) = coord (mixedEmbedding F α * v)`. -/
noncomputable def mulCoord (α : F) :
    (NumberField.mixedEmbedding.index F → ℝ) →ₗ[ℝ]
      (NumberField.mixedEmbedding.index F → ℝ) :=
  (Finsupp.linearEquivFunOnFinite ℝ ℝ (NumberField.mixedEmbedding.index F)).toLinearMap ∘ₗ
    ((NumberField.mixedEmbedding.stdBasis F).repr).toLinearMap ∘ₗ
      (LinearMap.mulLeft ℝ (NumberField.mixedEmbedding F α)) ∘ₗ
        ((NumberField.mixedEmbedding.stdBasis F).repr).symm.toLinearMap ∘ₗ
          (Finsupp.linearEquivFunOnFinite ℝ ℝ
            (NumberField.mixedEmbedding.index F)).symm.toLinearMap

lemma mulCoord_apply_coord (α : F) (v : NumberField.mixedEmbedding.mixedSpace F) :
    mulCoord α (coord (F := F) v) = coord (F := F) (NumberField.mixedEmbedding F α * v) := by
  funext k
  simp only [mulCoord, LinearMap.comp_apply, LinearEquiv.coe_coe, coord,
    Finsupp.linearEquivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply,
    Finsupp.linearEquivFunOnFinite_apply, LinearMap.mulLeft_apply]

lemma coord_zero : coord (F := F) (0 : NumberField.mixedEmbedding.mixedSpace F) = 0 := by
  funext k; simp [coord]

lemma coord_sum {ι : Type*} [Fintype ι] (f : ι → NumberField.mixedEmbedding.mixedSpace F) :
    coord (F := F) (∑ i, f i) = ∑ i, coord (F := F) (f i) := by
  funext k
  simp only [coord, map_sum, Finset.sum_apply]
  rw [Finsupp.finsetSum_apply Finset.univ]

lemma coord_injective : Function.Injective (coord (F := F)) :=
  fun _ _ h => (NumberField.mixedEmbedding.stdBasis F).repr.injective (DFunLike.coe_fn_eq.mp h)

lemma coord_mixedEmbedding_eq_zero {x : F}
    (h : coord (F := F) (NumberField.mixedEmbedding F x) = 0) : x = 0 := by
  have h2 : NumberField.mixedEmbedding F x = 0 := coord_injective (h.trans coord_zero.symm)
  exact (NumberField.mixedEmbedding F).injective (by simpa using h2)

/-- The `ℝ`-linear map `E^N → E^M` given by the rows `a i`, in coordinates. -/
noncomputable def phiMap {M N : ℕ} (a : Fin M → Fin N → F) :
    CoordSpace F N →ₗ[ℝ] CoordSpace F M where
  toFun x := fun i => ∑ j, mulCoord (a i j) (x j)
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul, Finset.smul_sum]

lemma phiMap_coordVec {M N : ℕ} (a : Fin M → Fin N → F)
    (y : Fin N → NumberField.RingOfIntegers F) :
    phiMap a (coordVec (F := F) y) =
      fun i => coord (F := F) (NumberField.mixedEmbedding F
        (∑ j, a i j * ((y j : NumberField.RingOfIntegers F) : F))) := by
  funext i
  simp only [phiMap, LinearMap.coe_mk, AddHom.coe_mk, coordVec]
  calc ∑ j, mulCoord (a i j) (coord (F := F)
          (NumberField.mixedEmbedding F ((y j : NumberField.RingOfIntegers F) : F)))
      = ∑ j, coord (F := F) (NumberField.mixedEmbedding F (a i j) *
          NumberField.mixedEmbedding F ((y j : NumberField.RingOfIntegers F) : F)) :=
        Finset.sum_congr rfl (fun j _ => mulCoord_apply_coord (F := F) (a i j) _)
    _ = coord (F := F) (∑ j, NumberField.mixedEmbedding F (a i j) *
          NumberField.mixedEmbedding F ((y j : NumberField.RingOfIntegers F) : F)) :=
        (coord_sum _).symm
    _ = coord (F := F) (NumberField.mixedEmbedding F
          (∑ j, a i j * ((y j : NumberField.RingOfIntegers F) : F))) := by
        congr 1
        rw [map_sum]
        exact Finset.sum_congr rfl (fun j _ => (map_mul (NumberField.mixedEmbedding F) _ _).symm)

lemma coordVec_zero {N : ℕ} :
    coordVec (F := F) (0 : Fin N → NumberField.RingOfIntegers F) = 0 := by
  funext j k
  simp only [coordVec, Pi.zero_apply, map_zero, coord]
  simp

lemma coordVec_add {N : ℕ} (x y : Fin N → NumberField.RingOfIntegers F) :
    coordVec (F := F) (x + y) = coordVec (F := F) x + coordVec (F := F) y := by
  funext j k
  simp only [coordVec, Pi.add_apply, map_add, coord, Finsupp.add_apply]

lemma coordVec_zsmul {N : ℕ} (n : ℤ) (x : Fin N → NumberField.RingOfIntegers F) :
    coordVec (F := F) (n • x) = n • coordVec (F := F) x := by
  funext j k
  simp only [coordVec, Pi.smul_apply, coord, map_zsmul, Finsupp.smul_apply]

/-- The coordinate model of the lattice `(𝓞 F)^N ⊆ E^N`. -/
noncomputable def latL (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    Submodule ℤ (CoordSpace F N) :=
  Submodule.span ℤ (Set.range (coordVec (F := F) (N := N)))

/-- The lattice `(𝓞 F)^N`, in coordinates, is exactly the range of `coordVec`. -/
lemma latL_eq_range {N : ℕ} :
    (latL F N : Set (CoordSpace F N)) = Set.range (coordVec (F := F) (N := N)) := by
  let P : Submodule ℤ (CoordSpace F N) :=
    { carrier := Set.range (coordVec (F := F) (N := N))
      zero_mem' := ⟨0, coordVec_zero (F := F)⟩
      add_mem' := by
        intro x y hx hy
        obtain ⟨u, rfl⟩ := hx
        obtain ⟨v, rfl⟩ := hy
        exact ⟨u + v, coordVec_add u v⟩
      smul_mem' := by
        intro n x hx
        obtain ⟨u, rfl⟩ := hx
        exact ⟨n • u, coordVec_zsmul n u⟩ }
  have hP : (P : Set (CoordSpace F N)) = Set.range (coordVec (F := F) (N := N)) := rfl
  rw [latL, ← hP]
  exact congrArg (fun Q : Submodule ℤ (CoordSpace F N) => (Q : Set (CoordSpace F N)))
    (Submodule.span_eq P)

/-- The kernel lattice is the intersection of the lattice `(𝓞 F)^N` with the kernel of `phiMap`. -/
theorem mem_kerLattice_iff {M N : ℕ} (a : Fin M → Fin N → F) (x : CoordSpace F N) :
    x ∈ kerLattice (F := F) a ↔ x ∈ latL F N ∧ phiMap a x = 0 := by
  constructor
  · intro hx
    refine ⟨Submodule.span_mono (Set.image_subset_range _ _) hx, ?_⟩
    have hgen : ∀ y ∈ coordVec (F := F) '' kerVecs (F := F) a, phiMap a y = 0 := by
      rintro y ⟨z, hz, rfl⟩
      rw [phiMap_coordVec]
      funext i
      rw [hz i, map_zero, coord_zero]
      simp
    have hle : Submodule.span ℤ (coordVec (F := F) '' kerVecs (F := F) a) ≤
        (LinearMap.ker (phiMap a)).restrictScalars ℤ :=
      Submodule.span_le.mpr (fun y hy => by
        rw [SetLike.mem_coe]
        exact hgen y hy)
    exact LinearMap.mem_ker.mp (hle hx)
  · rintro ⟨hxlat, hxker⟩
    have hx' : x ∈ Set.range (coordVec (F := F) (N := N)) := by
      rw [← latL_eq_range]
      exact hxlat
    obtain ⟨y, rfl⟩ := hx'
    rw [phiMap_coordVec] at hxker
    refine Submodule.subset_span ⟨y, fun i => ?_, rfl⟩
    exact coord_mixedEmbedding_eq_zero (congrFun hxker i)

end Work.BW
