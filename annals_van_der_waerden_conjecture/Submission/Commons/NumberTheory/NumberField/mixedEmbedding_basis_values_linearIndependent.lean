import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

open scoped NumberField BigOperators

noncomputable section

open Module Module.Free

namespace Commons.NumberTheory.NumberField

variable {K : Type*} [Field K] [NumberField K]
variable {κ : Type*} [Fintype κ]

/-- Coordinates of `mixedEmbedding K a` w.r.t. the real basis `L` are the rational
coordinates of `a` w.r.t. the rational basis `B`, cast to `ℝ`. -/
private lemma equivFun_mixedEmbedding_coord (B : Basis κ ℚ K)
    (L : Basis κ ℝ (NumberField.mixedEmbedding.mixedSpace K))
    (hL : ∀ j : κ, L j = NumberField.mixedEmbedding K (B j)) (a : K) :
    L.equivFun (NumberField.mixedEmbedding K a) =
      fun j : κ => ((B.equivFun a) j : ℝ) := by
  have ha : (∑ j : κ, (B.equivFun a) j • B j) = a := by
    calc
      (∑ j : κ, (B.equivFun a) j • B j) = B.equivFun.symm (B.equivFun a) := by
          rw [← Basis.equivFun_symm_apply]
      _ = a := by simp
  have hsum : NumberField.mixedEmbedding K a = ∑ j : κ, (((B.equivFun a) j : ℚ) : ℝ) • L j := by
    calc
      NumberField.mixedEmbedding K a
          = NumberField.mixedEmbedding K (∑ j : κ, (B.equivFun a) j • B j) := by rw [ha]
      _ = ∑ j : κ, NumberField.mixedEmbedding K ((B.equivFun a) j • B j) := by
            rw [map_sum]
      _ = ∑ j : κ, ((B.equivFun a) j : ℝ) • NumberField.mixedEmbedding K (B j) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact map_ratCast_smul (NumberField.mixedEmbedding K) ℚ ℝ ((B.equivFun a) j) (B j)
      _ = ∑ j : κ, ((B.equivFun a) j : ℝ) • L j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← hL j]
  calc
    L.equivFun (NumberField.mixedEmbedding K a)
        = L.equivFun (∑ j : κ, ((B.equivFun a) j : ℝ) • L j) := by
            rw [hsum]
    _ = (fun j : κ => ((B.equivFun a) j : ℝ)) := by
            have hsum2 : L.repr (∑ j : κ, ((B.equivFun a) j : ℝ) • L j) =
                (fun j : κ => ((B.equivFun a) j : ℝ)) := by
              simpa using (L.repr_sum_self (fun j : κ => ((B.equivFun a) j : ℝ)))
            rw [L.equivFun_apply]
            exact hsum2

/-- If the images of elements of the ring of integers under the mixed embedding are
`ℚ`-linearly independent in `K`, then they are `ℝ`-linearly independent in the mixed space. -/
theorem mixedEmbedding_basis_values_linearIndependent {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] (x : ι → NumberField.RingOfIntegers K)
    (h : LinearIndependent ℚ (fun i : ι => (x i : K))) :
    LinearIndependent ℝ (fun i : ι => NumberField.mixedEmbedding K (x i : K)) := by
  classical
  let IB := NumberField.integralBasis K
  let LB := NumberField.mixedEmbedding.latticeBasis K
  -- coordinates of the (x i) w.r.t. the ℚ-basis IB: ℚ-independent
  have hcQ : LinearIndependent ℚ (fun i : ι => IB.equivFun (x i : K)) := by
    have hker : (IB.equivFun).toLinearMap.ker = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      exact (IB.equivFun).injective
    change LinearIndependent ℚ
      (fun i : ι => (NumberField.integralBasis K).equivFun (x i : K))
    exact (LinearMap.linearIndependent_iff
      ((NumberField.integralBasis K).equivFun).toLinearMap hker).mpr h
  -- cast ℚ-coordinates to ℝ: still independent
  have hcR : LinearIndependent ℝ
      (fun i : ι => algebraMap ℚ ℝ ∘ (IB.equivFun (x i : K))) := by
    change LinearIndependent ℝ
      (fun i : ι => algebraMap ℚ ℝ ∘ (NumberField.integralBasis K).equivFun (x i : K))
    exact (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ)
      (v := fun i : ι => (NumberField.integralBasis K).equivFun (x i : K))).mpr hcQ
  -- the mixed embeddings have exactly these real coordinates w.r.t. the ℝ-basis LB
  have hcoord : ∀ i : ι, LB.equivFun (NumberField.mixedEmbedding K (x i : K)) =
      (fun j : Module.Free.ChooseBasisIndex ℤ (𝓞 K) => ((IB.equivFun (x i : K)) j : ℝ)) := by
    intro i
    exact equivFun_mixedEmbedding_coord (κ := Module.Free.ChooseBasisIndex ℤ (𝓞 K))
      IB LB
      (fun j => NumberField.mixedEmbedding.latticeBasis_apply (K := K) j) (x i : K)
  -- hcR' : independence of the LB.equivFun images
  have hcR' : LinearIndependent ℝ
      (fun i : ι => LB.equivFun (NumberField.mixedEmbedding K (x i : K))) := by
    convert hcR using 1
    ext i j
    rw [hcoord i]
    simp
  -- LB.equivFun is an ℝ-linear equivalence, hence preserves linear independence
  have hker : (LB.equivFun).toLinearMap.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (LB.equivFun).injective
  change LinearIndependent ℝ
    (fun i : ι => NumberField.mixedEmbedding K (x i : K))
  exact (LinearMap.linearIndependent_iff
    (NumberField.mixedEmbedding.latticeBasis K).equivFun.toLinearMap hker).mp hcR'

end Commons.NumberTheory.NumberField
