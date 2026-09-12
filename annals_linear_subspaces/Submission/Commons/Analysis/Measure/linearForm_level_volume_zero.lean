import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace Commons.Analysis.Measure

open MeasureTheory

/-- The level set `{y : Fin n → ℝ | ∑ i, aᵢ * yᵢ = b}` of a non-zero integer linear form has
Lebesgue measure zero.

Indeed, the linear form `L y = ∑ i, aᵢ * yᵢ` is a non-zero linear functional on the
finite-dimensional real vector space `Fin n → ℝ`, so its level sets are affine subspaces with
direction the strict subspace `ker L`; strict affine subspaces of a finite-dimensional real
vector space have zero Haar measure (`MeasureTheory.Measure.addHaar_affineSubspace`). -/
theorem linearForm_level_volume_zero {n : ℕ} (a : Fin n → ℤ) (ha : ∃ i, a i ≠ 0) (b : ℝ) :
    MeasureTheory.volume {y : Fin n → ℝ | (∑ i, (a i : ℝ) * y i) = b} = 0 := by
  classical
  obtain ⟨i0, hi0⟩ := ha
  -- The linear form `y ↦ ∑ i, aᵢ * yᵢ`.
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun y => ∑ i, (a i : ℝ) * y i
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring) }
  have hL_apply : ∀ y : Fin n → ℝ, L y = ∑ i, (a i : ℝ) * y i := fun y => rfl
  -- `L` is non-zero because `L (single i₀ 1) = a i₀ ≠ 0`.
  have hsingle : L (Pi.single i0 (1 : ℝ)) = (a i0 : ℝ) := by
    rw [hL_apply]
    rw [Finset.sum_eq_single i0]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i0) h
  have hLne : L ≠ 0 := by
    intro h
    have h1 : L (Pi.single i0 (1 : ℝ)) = 0 := by simp [h]
    rw [hsingle] at h1
    exact hi0 (by exact_mod_cast h1)
  -- hence `ker L` is a strict subspace.
  have hker : LinearMap.ker L ≠ ⊤ := fun h => hLne (LinearMap.ker_eq_top.mp h)
  have hset : {y : Fin n → ℝ | (∑ i, (a i : ℝ) * y i) = b} = {y : Fin n → ℝ | L y = b} := by
    ext y
    simp only [Set.mem_ofPred_eq, hL_apply]
  rw [hset]
  by_cases hb : b ∈ Set.range L
  · -- If `b = L y₀`, the level set is the affine subspace `y₀ +ᵥ ker L`.
    obtain ⟨y₀, hy₀⟩ := hb
    have hA : {y : Fin n → ℝ | L y = b} = ↑(AffineSubspace.mk' y₀ (LinearMap.ker L)) := by
      ext q
      show L q = b ↔ q ∈ AffineSubspace.mk' y₀ (LinearMap.ker L)
      rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker, map_sub, hy₀]
      exact sub_eq_zero.symm
    rw [hA]
    refine Measure.addHaar_affineSubspace volume _ (fun htop => hker ?_)
    rw [← AffineSubspace.direction_mk' y₀ (LinearMap.ker L), htop, AffineSubspace.direction_top]
  · -- If `b ∉ range L` the level set is empty.
    have hS : {y : Fin n → ℝ | L y = b} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      exact hb ⟨y, hy⟩
    rw [hS, measure_empty]

end Commons.Analysis.Measure