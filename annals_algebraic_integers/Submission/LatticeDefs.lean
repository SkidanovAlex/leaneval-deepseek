import Mathlib
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

noncomputable section

open scoped BigOperators RealInnerProductSpace
open Module Submodule MeasureTheory MeasureTheory.Measure Metric Filter

/-!
# Shared lattice-theory infrastructure

Definitions of the Euclidean bilinear form `euclForm`, the dual lattice `ldual`, and
covolume/measure facts used by the covering-radius development
(`Submission.CovRadius.coverRadius_bound`) and by the final application
(`Submission.GeoCore.geo_core`).
-/

namespace Submission.LatticeDefs

section Volume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

-- the fundamental domain of a real basis is well-behaved for volume
lemma measureReal_fundamentalDomain_of_isAddHaar {μ : Measure E} [μ.IsAddHaarMeasure]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b b₀ : Basis ι ℝ E) :
    μ.real (ZSpan.fundamentalDomain b) = |b₀.det b| * μ.real (ZSpan.fundamentalDomain b₀) := by
  simpa using ZSpan.measureReal_fundamentalDomain b μ b₀

end Volume

section Covol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [ProperSpace E] [MeasurableSpace E] [BorelSpace E]

/-- covolume of a lattice = volume of the fundamental domain of the real extension of a Z-basis -/
lemma covol_eq_fund {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (bz : Basis ι ℤ Λ) :
    ZLattice.covolume Λ = (volume.real (ZSpan.fundamentalDomain (bz.ofZLatticeBasis ℝ))) := by
  exact ZLattice.covolume_eq_measure_fundamentalDomain (μ := volume) Λ
    (ZLattice.isAddFundamentalDomain (μ := volume) bz)

end Covol
section DualLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner product, viewed as a real bilinear form. -/
abbrev euclForm (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    LinearMap.BilinForm ℝ E :=
  innerₗ E

theorem euclForm_apply (x y : E) : euclForm E x y = ⟪x, y⟫ := rfl

theorem euclForm_nondegenerate (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    (euclForm E).Nondegenerate := by
  rw [LinearMap.BilinForm.Nondegenerate]
  constructor <;> intro z hz
  · have h : ⟪z, z⟫ = 0 := by
      simpa [euclForm] using hz z
    rw [real_inner_self_eq_norm_sq] at h
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)
  · have h : ⟪z, z⟫ = 0 := by
      simpa [euclForm] using hz z
    rw [real_inner_self_eq_norm_sq] at h
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)

/-- The dual (orthogonal) lattice of a `ℤ`-submodule with respect to the inner product. -/
def ldual (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) : Submodule ℤ E :=
  (euclForm E).dualSubmodule L

theorem mem_ldual {L : Submodule ℤ E} {x : E} :
    x ∈ ldual E L ↔ ∀ y : E, y ∈ L → ∃ z : ℤ, ⟪x, y⟫ = (z : ℝ) := by
  unfold ldual euclForm
  simp only [LinearMap.BilinForm.mem_dualSubmodule]
  constructor <;> intro h y hy
  · rcases h y hy with ⟨z, hz⟩
    exact ⟨z, by simpa using hz.symm⟩
  · rcases h y hy with ⟨z, hz⟩
    exact ⟨z, by simpa using hz.symm⟩


/-- The dual of the `ℤ`-span of a real basis is the `ℤ`-span of the dual basis. -/
theorem ldual_span_basis {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    ldual E (span ℤ (Set.range b)) =
      span ℤ (Set.range ((euclForm E).dualBasis (euclForm_nondegenerate E) b)) := by
  unfold ldual
  simpa [euclForm] using
    (LinearMap.BilinForm.dualSubmodule_span_of_basis (euclForm E)
      (euclForm_nondegenerate E) b)

end DualLattice


/-- The lattice condition: `Bᵀ·x` is integer-valued, i.e. for every row-index `i`,
`∑ j, B j i * x j` is an integer. -/
def InLattice (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, ∃ z : ℤ, (∑ j : Fin n, B j i * x j) = (z : ℝ)


end Submission.LatticeDefs
