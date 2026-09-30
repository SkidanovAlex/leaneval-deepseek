import Mathlib
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.sieg2Defs
import Submission.Work.BW.sieg2_PhiE_aux
import Submission.Work.BW.PhiE_ofLp_mulVec
import Submission.Work.BW.psiAssemble_mulVec
import Submission.Work.BW.sieg2_det_ne_zero
import Submission.Work.BW.TV.mem_intLatE_iff_latL
import Submission.Work.BW.TV.kerLatE_coord_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bridges for `Work.BW.sieg2_kerLatE_family`

The main theorem `Work.BW.sieg2_kerLatE_family` extracts, from a `ℤ`-basis `b` of the kernel
lattice `kerLatK a`, a family of *integral kernel tuples* `v i : (𝓞 F)^N` whose mixed coordinates
`siegCoord (v i)` are the vectors `kerLatEval a (b i)` themselves.

This file collects the coordinate bridges: the map `siegCoordE` that assembles the mixed
coordinates of an integral tuple into the Euclidean coordinate space
`EuclideanSpace ℝ (Fin N × index F)`, its surjectivity onto the integral lattice `intLatE F N`,
and the identifications

* `psiAssemble_PhiE` : the coordinate model `PhiE a` is the conjugation of `Phi a`;
* `psiAssemble_siegCoord` : `siegCoord` are the coordinates in the orthonormal basis, so their
  expansion is `meK`;
* `Phi_meK_sum` : `Phi a` applied to a tuple of `meK`s is `meK` of the row combinations;
* `meK_eq_zero` : `meK` vanishes only at `0`;
* `inner_siegCoordE` : the Euclidean inner product of two such vectors is `siegInner` of their
  mixed coordinates.
-/

open NumberField
open scoped Classical

noncomputable section

namespace Work.BW

variable {F : Type*} [Field F] [NumberField F]

/-- The mixed coordinates of an integral tuple, assembled into the Euclidean coordinate space
`EuclideanSpace ℝ (Fin N × index F)`.  This is the map whose values are exactly the points of the
integral lattice `intLatE F N`. -/
abbrev siegCoordE {N : ℕ} (v : Fin N → NumberField.RingOfIntegers F) :
    EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) :=
  WithLp.toLp 2 (fun p : Fin N × NumberField.mixedEmbedding.index F => siegCoord v p.1 p.2)

@[simp] theorem siegCoordE_ofLp {N : ℕ} (v : Fin N → NumberField.RingOfIntegers F) :
    (siegCoordE v).ofLp = fun p : Fin N × NumberField.mixedEmbedding.index F =>
      siegCoord v p.1 p.2 := rfl

/-- `siegCoord` of a tuple of algebraic integers is `coordVec` of that tuple. -/
theorem siegCoord_eq_coordVec {N : ℕ} (v : Fin N → NumberField.RingOfIntegers F) :
    siegCoord v = coordVec (F := F) v := rfl

/-- The `ℤ`-linear uncurrying of `Work.BW.TV.ofLpMap`, applied to `siegCoord`, is `siegCoordE`. -/
@[simp] theorem TV_toEMap_siegCoord {N : ℕ} (v : Fin N → NumberField.RingOfIntegers F) :
    TV.toEMap F N (siegCoord v) = siegCoordE v := rfl

/-- **The range of `siegCoordE` is the integral lattice**: every point of `intLatE F N` is the
mixed coordinate vector of an integral tuple. -/
theorem siegCoordE_surjective_intLatE (N : ℕ) :
    ∀ y ∈ intLatE F N, ∃ v : Fin N → NumberField.RingOfIntegers F, siegCoordE v = y := by
  intro y hy
  have hy' : TV.ofLpMap F N y ∈ latL F N := (TV.mem_intLatE_iff_latL (F := F) y).mp hy
  have hy'' : TV.ofLpMap F N y ∈ Set.range (coordVec (F := F) (N := N)) := by
    rw [← latL_eq_range]
    exact hy'
  obtain ⟨v, hv⟩ := hy''
  refine ⟨v, ?_⟩
  rw [(TV_toEMap_siegCoord (F := F) (N := N) v).symm, siegCoord_eq_coordVec, hv,
    TV.toEMap_ofLpMap]

/-- The coordinate model `PhiE a` is the conjugate of the mixed-space model `Phi a` by the
assembly of coordinates in the orthonormal basis. -/
theorem psiAssemble_PhiE {M N : ℕ} (a : Fin M → Fin N → F)
    (x : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) :
    psiAssemble (F := F) M (WithLp.ofLp (PhiE a x)) =
      Phi a (psiAssemble (F := F) N (WithLp.ofLp x)) := by
  rw [PhiE_ofLp_mulVec]
  exact psiAssemble_mulVec a (WithLp.ofLp x)

/-- Expanding the mixed coordinates of an integral tuple in the orthonormal basis gives the tuple
of its `meK`-images. -/
theorem psiAssemble_siegCoord {N : ℕ} (v : Fin N → NumberField.RingOfIntegers F) :
    psiAssemble (F := F) N (fun p : Fin N × NumberField.mixedEmbedding.index F =>
        siegCoord v p.1 p.2)
      = fun j => meK (((v j : NumberField.RingOfIntegers F)) : F) := by
  funext j
  rw [psiAssemble_apply]
  have hc : ∀ c : NumberField.mixedEmbedding.index F,
      siegCoord v (j, c).1 (j, c).2
        = WithLp.ofLp ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).repr
            (meK (((v j : NumberField.RingOfIntegers F)) : F))) c := by
    intro c
    rw [show siegCoord v (j, c).1 (j, c).2 = coord (F := F)
        (NumberField.mixedEmbedding F (((v j : NumberField.RingOfIntegers F)) : F)) c from rfl]
    rw [← TV.zz_coord_toMixed (F := F) (meK (F := F)
        (((v j : NumberField.RingOfIntegers F)) : F))]
    simp [meK]
  rw [← OrthonormalBasis.sum_repr (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F)
    (meK (((v j : NumberField.RingOfIntegers F)) : F))]
  apply Finset.sum_congr rfl
  intro c _
  rw [hc c]

/-- `meK` is additive. -/
theorem sieg2_meK_sum {ι : Type*} (s : Finset ι) (f : ι → F) :
    meK (∑ i ∈ s, f i) = ∑ i ∈ s, meK (f i) := by
  simp only [meK, map_sum]

/-- Multiplication by `a : F` sends the image of `b` under `meK` to the image of `a * b`. -/
theorem sieg2_mulK_meK (a b : F) : mulK a (meK b) = meK (a * b) := by
  simp only [mulK_apply, meK]; simp

/-- The row map `Phi a` applied to a tuple of `meK`-images is `meK` of the row combinations. -/
theorem Phi_meK_sum {M N : ℕ} (a : Fin M → Fin N → F)
    (v : Fin N → NumberField.RingOfIntegers F) :
    Phi a (fun j => meK (((v j : NumberField.RingOfIntegers F)) : F)) =
      fun i => meK (∑ j, a i j * (((v j : NumberField.RingOfIntegers F)) : F)) := by
  funext i
  rw [Phi_apply]
  rw [Finset.sum_congr rfl (fun j _ => sieg2_mulK_meK (a i j) _)]
  rw [← sieg2_meK_sum Finset.univ]

/-- `meK` vanishes only at `0`. -/
theorem meK_eq_zero {x : F} : meK x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h2 : NumberField.mixedEmbedding F x = 0 := by
      have h3 := congrArg (NumberField.mixedEmbedding.euclidean.toMixed F) h
      simpa [meK] using h3
    exact NumberField.mixedEmbedding_injective F (by simpa using h2)
  · rintro rfl
    simp [meK]

/-- The Euclidean inner product of two mixed coordinate vectors is `siegInner`. -/
theorem inner_siegCoordE {N : ℕ} (v w : Fin N → NumberField.RingOfIntegers F) :
    inner ℝ (siegCoordE v) (siegCoordE w) = siegInner (siegCoord v) (siegCoord w) := by
  rw [siegInner_eq_sum]
  rw [show inner ℝ (siegCoordE v) (siegCoordE w)
      = ∑ p : Fin N × NumberField.mixedEmbedding.index F,
          (siegCoordE v).ofLp p * (siegCoordE w).ofLp p from by
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]]

/-- Coercing a linearly independent family of a submodule into its ambient module preserves
`ℤ`-linear independence. -/
theorem linearIndependent_coe_submodule {R : Type*} [Ring R] {V : Type*} [AddCommGroup V]
    [Module R V] {L : Submodule R V} {ι : Type*} {w : ι → L} (h : LinearIndependent R w) :
    LinearIndependent R (fun i => (w i : V)) :=
  h.map' (Submodule.subtype L) (Submodule.ker_subtype L)

/-- The mixed coordinate vectors of a `ℤ`-basis of the kernel lattice are `ℤ`-linearly
independent. -/
theorem linearIndependent_kerLatEval {M N : ℕ} (a : Fin M → Fin N → F) {ι : Type*}
    (b : Module.Basis ι ℤ ↥(kerLatK (F := F) a)) :
    LinearIndependent ℤ (fun i => kerLatEval (F := F) a (b i)) := by
  have h1 : LinearIndependent ℤ (fun i =>
      (((b i : kerLatK (F := F) a)) : ↥(LinearMap.ker
        (PhiE a : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F))))) :=
    linearIndependent_coe_submodule (R := ℤ) (L := kerLatK (F := F) a)
      (w := fun i => b i) b.linearIndependent
  have h2 := linearIndependent_coe_submodule (R := ℤ)
    (L := (LinearMap.ker (PhiE a : EuclideanSpace ℝ
      (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F))).restrictScalars ℤ)
    (w := fun i => (((b i : kerLatK (F := F) a)) : ↥(LinearMap.ker
      (PhiE a : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F))))) h1
  simpa only [kerLatEval] using h2

end Work.BW

end
