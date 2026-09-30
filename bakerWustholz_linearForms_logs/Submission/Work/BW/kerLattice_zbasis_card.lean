import Mathlib
import Submission.Work.BW.siegel_defs
import Submission.Work.BW.finrank_ker_mulVecLin_fin
import Submission.Work.BW.exists_int_mul_mem_ringOfIntegers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `ℤ`-rank of the kernel lattice

`Work.BW.kerLattice F a` is the `ℤ`-span of the coordinate vectors of the mixed images of the
integral kernel vectors `{x ∈ (𝓞 F)^N : ∀ i, ∑ j, a i j * x j = 0}` of an `M × N` matrix `a` with
`F`-linearly independent rows.  This file computes its `ℤ`-rank: any `ℤ`-basis of the kernel
lattice has exactly `[F : ℚ] * (N - M)` elements.

The proof does not use any lattice-covolume theory.  The `ℚ`-linear map

`Ψ : F^N → (Fin N → index F → ℝ)`,  `Ψ y j t = (stdBasis F).repr (mixedEmbedding F (y j)) t`

is injective, and its restriction to the `F`-kernel `K = ker (a ·)` of `a` (of `F`-dimension
`N - M`, hence `ℚ`-dimension `[F : ℚ] * (N - M)`) lands inside the `ℚ`-span of any family `v` with
`span ℤ (range v) = kerLattice F a`.  Indeed, for `y ∈ K` one finds `0 ≠ m ∈ ℤ` with `m • y` an
integral vector (hence a kernel vector, since `a` has coefficients in `F`), so that
`m • Ψ y = coordVec (m • y)` lies in the kernel lattice; dividing by `m` gives `Ψ y` in the
`ℚ`-span of `v`, since the latter is a `ℚ`-submodule.  Finally, the `ℚ`-span of `k` vectors has
`ℚ`-dimension at most `k`.
-/

namespace Work.BW

open NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- The coordinate functional of the mixed space `(stdBasis F).repr`, as an `ℝ`-linear map. -/
noncomputable def mixedCoordR : NumberField.mixedEmbedding.mixedSpace F →ₗ[ℝ]
    (NumberField.mixedEmbedding.index F → ℝ) :=
  ((Finsupp.linearEquivFunOnFinite ℝ ℝ (NumberField.mixedEmbedding.index F)).toLinearMap).comp
    ((NumberField.mixedEmbedding.stdBasis F).repr).toLinearMap

/-- The composite `x ↦ (stdBasis F).repr (mixedEmbedding F x)`, as a `ℚ`-linear map. -/
noncomputable def mixedCoord : F →ₗ[ℚ] (NumberField.mixedEmbedding.index F → ℝ) :=
  (mixedCoordR (F := F)).restrictScalars ℚ |>.comp
    (AddMonoidHom.toRatLinearMap (NumberField.mixedEmbedding F).toAddMonoidHom)

lemma mixedCoord_apply (x : F) :
    mixedCoord (F := F) x
      = (NumberField.mixedEmbedding.stdBasis F).repr (NumberField.mixedEmbedding F x) := rfl

lemma mixedCoord_injective : Function.Injective (mixedCoord (F := F)) := by
  intro x y h
  exact NumberField.mixedEmbedding_injective F
    (((NumberField.mixedEmbedding.stdBasis F).repr).injective
      (by simpa [mixedCoord, mixedCoordR] using h))

/-- The `ℚ`-linear map `y ↦ (coordVec)` on `N`-tuples: the mixed coordinates of `y`. -/
noncomputable def mixedCoordVec {N : ℕ} :
    (Fin N → F) →ₗ[ℚ] (Fin N → (NumberField.mixedEmbedding.index F → ℝ)) :=
  LinearMap.pi fun j => (mixedCoord (F := F)).comp (LinearMap.proj j)

lemma mixedCoordVec_apply {N : ℕ} (y : Fin N → F) (j : Fin N) :
    mixedCoordVec (F := F) y j = mixedCoord (F := F) (y j) := rfl

lemma mixedCoordVec_injective {N : ℕ} :
    Function.Injective (mixedCoordVec (F := F) (N := N)) := by
  intro x y h
  funext j
  exact mixedCoord_injective (F := F) (congrFun h j)

theorem kerLattice_zbasis_card {F : Type*} [Field F] [NumberField F] {M N : ℕ} (hMN : M < N)
    (a : Fin M → Fin N → F) (hind : LinearIndependent F a) {k : ℕ}
    (v : Fin k → (Fin N → (NumberField.mixedEmbedding.index F → ℝ)))
    (hli : LinearIndependent ℤ v)
    (hspan : Submodule.span ℤ (Set.range v) = Work.BW.kerLattice (F := F) a) :
    Module.finrank ℚ F * (N - M) ≤ k := by
  classical
  -- The `ℚ`-span `W` of `v`, and its dimension bound.
  set W : Submodule ℚ (Fin N → (NumberField.mixedEmbedding.index F → ℝ)) :=
    Submodule.span ℚ (Set.range v) with hW
  haveI hWfin : Module.Finite ℚ ↥W := by
    rw [hW]; exact Module.Finite.span_of_finite ℚ (Set.finite_range v)
  have hWk : Module.finrank ℚ ↥W ≤ k := by
    have h := finrank_range_le_card (R := ℚ) v
    simpa [Set.finrank, hW, Fintype.card_fin] using h
  -- The kernel lattice is contained in `W`.
  have hkerLe : ∀ x, x ∈ Work.BW.kerLattice (F := F) a → x ∈ W := by
    intro x hx
    rw [← hspan] at hx
    exact Submodule.span_subset_span ℤ ℚ (Set.range v) hx
  -- The `F`-kernel of the matrix, of `F`-dimension `N - M`.
  set K : Submodule F (Fin N → F) := LinearMap.ker ((Matrix.of a).mulVecLin) with hK
  have hKfin : Module.finrank F ↥K = N - M := by
    rw [hK]; exact finrank_ker_mulVecLin_fin a hind
  haveI hKfinrat : Module.Finite ℚ ↥K :=
    FiniteDimensional.finiteDimensional_submodule (K.restrictScalars ℚ)
  have hKdim : Module.finrank ℚ ↥K = Module.finrank ℚ F * (N - M) := by
    have h := Module.finrank_mul_finrank ℚ F ↥K
    rw [hKfin] at h
    exact h.symm
  -- The mixed coordinate map.
  set Ψ : (Fin N → F) →ₗ[ℚ] (Fin N → (NumberField.mixedEmbedding.index F → ℝ)) :=
    mixedCoordVec (F := F) (N := N) with hΨ
  have hmemW : ∀ y : Fin N → F, y ∈ K → Ψ y ∈ W := by
    intro y hy
    -- clear denominators: `m • y` is an integral vector
    obtain ⟨m, hm0, z, hz⟩ := exists_int_mul_mem_ringOfIntegers (F := F) y
    have hy0 : ∀ i, ∑ j, a i j * y j = 0 := by
      intro i
      have h1 : (Matrix.of a).mulVecLin y = 0 := by
        have h := hy; rw [hK, LinearMap.mem_ker] at h; exact h
      have h2 := congrFun h1 i
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using h2
    -- so `z` is an integral kernel vector
    have hzker : z ∈ Work.BW.kerVecs (F := F) a := by
      intro i
      have hsum : ∑ j, a i j * ((z j : NumberField.RingOfIntegers F) : F)
          = (m : F) * ∑ j, a i j * y j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [hz j]; ring)
      rw [hsum, hy0 i, mul_zero]
    -- its coordinate vector lies in the kernel lattice, hence in `W`
    have hcoord : Work.BW.coordVec (F := F) z ∈ Work.BW.kerLattice (F := F) a :=
      Submodule.subset_span (Set.mem_image_of_mem (Work.BW.coordVec (F := F)) hzker)
    have hcoordW : Work.BW.coordVec (F := F) z ∈ W := hkerLe _ hcoord
    -- and it equals `m • Ψ y`
    have hzc : Work.BW.coordVec (F := F) z = (m : ℚ) • Ψ y := by
      funext j
      have hzj : ((z j : NumberField.RingOfIntegers F) : F) = (m : ℚ) • y j := by
        rw [hz j, Algebra.smul_def]
        norm_num
      show Work.BW.coord (F := F) (NumberField.mixedEmbedding F
              ((z j : NumberField.RingOfIntegers F) : F)) = ((m : ℚ) • Ψ y) j
      rw [hzj]
      show mixedCoord (F := F) ((m : ℚ) • y j) = ((m : ℚ) • Ψ y) j
      rw [map_smul, Pi.smul_apply]
      rfl
    rw [hzc] at hcoordW
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
    have := W.smul_mem ((m : ℚ)⁻¹) hcoordW
    simpa [smul_smul, inv_mul_cancel₀ hmq] using this
  -- restrict `Ψ` to `K`
  set ΨK : ↥K →ₗ[ℚ] (Fin N → (NumberField.mixedEmbedding.index F → ℝ)) :=
    Ψ.comp ((Submodule.subtype K).restrictScalars ℚ) with hΨK
  have hΨKapp : ∀ x : ↥K, ΨK x = Ψ x := fun x => rfl
  have hinj : Function.Injective ΨK := by
    intro x y hxy
    have h2 : Ψ (x : Fin N → F) = Ψ (y : Fin N → F) := by
      rw [← hΨKapp x, ← hΨKapp y]; exact hxy
    exact Subtype.ext (mixedCoordVec_injective h2)
  have hrangeLe : LinearMap.range ΨK ≤ W := by
    rintro z ⟨y, hy⟩
    rw [← hy, hΨKapp y]
    exact hmemW _ y.2
  have hrn := LinearMap.finrank_range_add_finrank_ker ΨK
  have hkerbot : LinearMap.ker ΨK = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  rw [hkerbot, finrank_bot, add_zero] at hrn
  calc Module.finrank ℚ F * (N - M) = Module.finrank ℚ ↥K := hKdim.symm
    _ = Module.finrank ℚ ↥(LinearMap.range ΨK) := hrn.symm
    _ ≤ Module.finrank ℚ ↥W := Submodule.finrank_mono hrangeLe
    _ ≤ k := hWk

end Work.BW
