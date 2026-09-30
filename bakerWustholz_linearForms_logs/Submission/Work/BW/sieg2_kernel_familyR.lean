import Mathlib
import Submission.Work.BW.sieg2Defs
import Submission.Work.BW.gramHadamard
import Submission.Work.BW.sieg2_kernel_family
import Submission.Work.BW.linearIndependent_ratCast
import Submission.Work.BW.linearIndependent_rat_coords

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The integral kernel family with `ℝ`-independent mixed coordinates

`Work.BW.sieg2_kernel_family` produces, for `M < N` `F`-linearly independent rows `a`,
`d (N-M)` integral kernel vectors (`d = [F:ℚ]`) whose mixed coordinates are `ℤ`-independent and
whose Gram determinant is at most the sharp Bombieri–Vaaler bound `γ`.

The present file strengthens the independence statement from `ℤ` to `ℝ`, using the fact that the
mixed embedding of the ring of integers `𝓞 F` is a *full* lattice in the mixed space: a `ℤ`-basis
of `𝓞 F` is an `ℝ`-basis of the mixed space (`NumberField.mixedEmbedding.latticeBasis`).  Hence
the coordinates of an integral vector in that basis are rational numbers, and
`ℤ`-independence of integral vectors implies `ℚ`-independence of those rational coordinates, which
in turn gives `ℝ`-independence of the mixed coordinates by base change `ℚ → ℝ`.

The two mathematical inputs are delegated:
* `Work.BW.linearIndependent_rat_coords` : `ℚ`-independence of the mixed coordinates implies
  `ℚ`-independence of the coordinates in the integral basis of `F`;
* `Work.BW.linearIndependent_ratCast` : base change `ℚ → ℝ` for families of rational-valued
  functions.
-/

open NumberField
open scoped NumberField

namespace Work.BW

variable {F : Type*} [Field F] [NumberField F]

/-- The `ℝ`-basis of the coordinate space `ℝ^{index F}` of the mixed space given by the standard
coordinates of the mixed images of the integral basis of `F`.  Since the mixed images of a
`ℤ`-basis of `𝓞 F` form an `ℝ`-basis of the mixed space
(`NumberField.mixedEmbedding.latticeBasis`), this is a basis. -/
noncomputable def sieg2KernelDeltaBasis :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ
      (NumberField.mixedEmbedding.index F → ℝ) :=
  (NumberField.mixedEmbedding.latticeBasis F).map (NumberField.mixedEmbedding.stdBasis F).equivFun

/-- The coordinates of a tuple of `N` points of the mixed space in the basis
`sieg2KernelDeltaBasis`, as a linear equivalence. -/
noncomputable def sieg2KernelCoordEquiv (N : ℕ) :
    (Fin N → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ) ≃ₗ[ℝ] SiegCoord F N :=
  LinearEquiv.piCongrRight (fun _ : Fin N =>
    (sieg2KernelDeltaBasis (F := F)).equivFun.symm)

theorem sieg2KernelCoordEquiv_apply (N : ℕ)
    (y : Fin N → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ) (j : Fin N) :
    sieg2KernelCoordEquiv (F := F) N y j
      = ∑ l, y j l • (NumberField.mixedEmbedding.stdBasis F).equivFun
          ((NumberField.mixedEmbedding.latticeBasis F) l) := by
  rw [sieg2KernelCoordEquiv, LinearEquiv.piCongrRight_apply, Module.Basis.equivFun_symm_apply]
  simp [sieg2KernelDeltaBasis, Module.Basis.map_apply]

/-- On the coordinates of a tuple of algebraic integers in the integral basis, the linear
equivalence `sieg2KernelCoordEquiv` computes the `siegCoord` of the tuple. -/
theorem sieg2KernelCoordEquiv_coord (N : ℕ) (v : Fin N → 𝓞 F) :
    sieg2KernelCoordEquiv (F := F) N (fun j l =>
        ((NumberField.integralBasis F).repr ((v j : 𝓞 F) : F) l : ℝ)) = siegCoord v := by
  have key : ∀ j : Fin N, (∑ l,
        (((NumberField.integralBasis F).repr ((v j : 𝓞 F) : F)) l : ℝ) •
        (NumberField.mixedEmbedding.latticeBasis F) l)
      = NumberField.mixedEmbedding F ((v j : 𝓞 F) : F) := by
    intro j
    rw [← Module.Basis.sum_repr (NumberField.mixedEmbedding.latticeBasis F)
        (NumberField.mixedEmbedding F ((v j : 𝓞 F) : F))]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [NumberField.mixedEmbedding.latticeBasis_repr_apply]
  ext j k
  rw [sieg2KernelCoordEquiv_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show siegCoord v j k = (NumberField.mixedEmbedding.stdBasis F).repr
      (NumberField.mixedEmbedding F ((v j : 𝓞 F) : F)) k from rfl]
  rw [← key j, map_sum]
  simp only [map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Module.Basis.equivFun_apply]

/-- **`ℤ`-independence of integral vectors implies `ℝ`-independence of their mixed coordinates.**

This is the only place where the "integrality" of the vectors is used: it makes the coordinates in
the integral basis rational, so that `ℤ`-independence (equivalently `ℚ`-independence, since the
mixed space is a `ℚ`-vector space) is preserved under the base change `ℚ → ℝ`, and the coordinate
map is an `ℝ`-linear isomorphism onto `SiegCoord F N`. -/
theorem sieg2RealLI_of_intLI {k N : ℕ} (v : Fin k → (Fin N → 𝓞 F))
    (h : LinearIndependent ℤ (fun i => siegCoord (v i))) :
    LinearIndependent ℝ (fun i => siegCoord (v i)) := by
  -- `ℤ`-independence gives `ℚ`-independence, the ambient space being a `ℚ`-vector space
  have hwℚ : LinearIndependent ℚ (fun i => siegCoord (v i)) :=
    (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).mp h
  -- the coordinates of the vectors in the integral basis of `F`
  let z : Fin k → (Fin N → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℚ) :=
    fun i j l => (NumberField.integralBasis F).repr (((v i j : 𝓞 F)) : F) l
  have hzℚ : LinearIndependent ℚ z := by
    simpa only [z] using linearIndependent_rat_coords (F := F) v hwℚ
  -- base change `ℚ → ℝ`
  have hzℝ : LinearIndependent ℝ (fun i => fun (j : Fin N)
      (l : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) => ((z i j l : ℚ) : ℝ)) :=
    (linearIndependent_ratCast (v := z)).mpr hzℚ
  -- the coordinate map identifies this family with the mixed coordinates
  have hrel : (fun i => sieg2KernelCoordEquiv (F := F) N
        (fun (j : Fin N) (l : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) => ((z i j l : ℚ) : ℝ)))
      = fun i => siegCoord (v i) := by
    funext i
    dsimp only [z]
    exact sieg2KernelCoordEquiv_coord (F := F) N (v i)
  rw [← hrel]
  exact hzℝ.map' (sieg2KernelCoordEquiv (F := F) N).toLinearMap
    (by rw [LinearMap.ker_eq_bot]; exact (sieg2KernelCoordEquiv (F := F) N).injective)

theorem sieg2_kernel_familyR {F : Type*} [Field F] [NumberField F] {M N : ℕ} (hMN : M < N)
    (a : Fin M → Fin N → F) (hli : LinearIndependent F a) :
    ∃ v : Fin (Module.finrank ℚ F * (N - M)) → (Fin N → NumberField.RingOfIntegers F),
      (∀ i n, ∑ m, a n m * (((v i m : NumberField.RingOfIntegers F)) : F) = 0) ∧
      LinearIndependent ℝ (fun i => Work.BW.siegCoord (v i)) ∧
      Work.BW.siegGramDet v ≤
        (((1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) *
            Real.sqrt |((NumberField.discr F : ℤ) : ℝ)|) ^ (N - M)) *
          (∏ i, (N : ℝ) ^ ((Module.finrank ℚ F : ℝ) / 2) *
            ∏ w : NumberField.InfinitePlace F, (⨆ j : Fin N, w (a i j)) ^ w.mult) *
          (∏ i, ∏ᶠ w : NumberField.FinitePlace F, (⨆ j : Fin N, w (a i j))) := by
  obtain ⟨v, hker, hliZ, hb⟩ := sieg2_kernel_family (F := F) hMN a hli
  exact ⟨v, hker, sieg2RealLI_of_intLI (F := F) v hliZ, hb⟩

end Work.BW
