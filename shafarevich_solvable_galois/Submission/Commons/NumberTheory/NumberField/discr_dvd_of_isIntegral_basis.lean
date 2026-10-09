import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Module

namespace Commons.NumberTheory.NumberField

theorem discr_dvd_of_isIntegral_basis {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ K)
    (hb : ∀ i : ι, IsIntegral ℤ (b i)) :
    ∃ m : ℤ, Algebra.discr ℚ b = (NumberField.discr K : ℚ) * m := by
  classical
  let κ := Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)
  let c : Basis κ ℚ K := NumberField.integralBasis K
  let e : κ ≃ ι := (Module.Basis.indexEquiv c b)
  let c' : Basis ι ℚ K := c.reindex e
  have hcoords : ∀ i j : ι, IsIntegral ℤ (c'.toMatrix b i j) := by
    intro i j
    let y : NumberField.RingOfIntegers K := ⟨b j, hb j⟩
    have hy_elem : algebraMap (NumberField.RingOfIntegers K) K y = b j := by
      rfl
    rw [Module.Basis.toMatrix_apply, Module.Basis.repr_reindex_apply, ← hy_elem]
    rw [NumberField.integralBasis_repr_apply]
    exact isIntegral_algebraMap
  have hdet : IsIntegral ℤ (c'.toMatrix b).det := IsIntegral.det hcoords
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hdet
  have hz' : (z : ℚ) = (c'.toMatrix b).det := by
    simpa using hz
  have hc' : Algebra.discr ℚ c' = Algebra.discr ℚ c := by
    calc
      Algebra.discr ℚ c' = Algebra.discr ℚ (⇑c ∘ ⇑e.symm) := by
        congr 1
        ext x
        simp [c', Module.Basis.reindex_apply]
      _ = Algebra.discr ℚ c := Algebra.discr_reindex (A := ℚ) (B := K) c e
  have hD : Algebra.discr ℚ c' = (NumberField.discr K : ℚ) := by
    rw [hc']
    exact (NumberField.coe_discr K).symm
  refine ⟨z * z, ?_⟩
  calc
    Algebra.discr ℚ b
        = Algebra.discr ℚ (Matrix.vecMul (⇑c' : ι → K)
            ((c'.toMatrix b).map (algebraMap ℚ K))) := by
          rw [Module.Basis.toMatrix_map_vecMul]
    _ = ((c'.toMatrix b).det ^ 2) * Algebra.discr ℚ c' := by
          exact Algebra.discr_of_matrix_vecMul (A := ℚ) (B := K) (b := (⇑c' : ι → K))
            (P := c'.toMatrix b)
    _ = ((z : ℚ) ^ 2) * Algebra.discr ℚ c' := by
          rw [← hz']
    _ = ((z : ℚ) ^ 2) * (NumberField.discr K : ℚ) := by
          rw [hD]
    _ = (NumberField.discr K : ℚ) * ((z * z : ℤ) : ℚ) := by
          rw [mul_comm, Int.cast_mul, pow_two]

end Commons.NumberTheory.NumberField