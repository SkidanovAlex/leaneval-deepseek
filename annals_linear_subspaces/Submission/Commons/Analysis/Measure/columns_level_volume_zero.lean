import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Commons.Analysis.Measure.linearForm_level_volume_zero

namespace Commons.Analysis.Measure

open MeasureTheory

theorem columns_level_volume_zero {l m : ℕ} (hm : 0 < m) (a : Fin l → ℤ)
    (ha : ∃ i, a i ≠ 0) (b : Fin m → ℤ) :
    MeasureTheory.volume {c : Fin l → Fin m → ℝ |
      ∀ j, (∑ i, (a i : ℝ) * c i j) = (b j : ℝ)} = 0 := by
  classical
  obtain ⟨i0, hi0⟩ := ha
  -- choose a column index (exists because `m > 0`)
  let j0 : Fin m := ⟨0, hm⟩
  -- the linear form picking out the `j0`-th column
  let L : (Fin l → Fin m → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun c => ∑ i, (a i : ℝ) * c i j0
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro t x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring) }
  have hL_apply : ∀ c : Fin l → Fin m → ℝ, L c = ∑ i, (a i : ℝ) * c i j0 := fun _ => rfl
  -- `L` is non-zero: evaluate on a matrix with a single non-zero entry.
  have hsingle : L (Pi.single i0 (Pi.single j0 (1 : ℝ))) = (a i0 : ℝ) := by
    rw [hL_apply]
    rw [Finset.sum_eq_single i0]
    · simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
    · intro h; exact absurd (Finset.mem_univ i0) h
  have hLne : L ≠ 0 := by
    intro h
    have h1 : L (Pi.single i0 (Pi.single j0 (1 : ℝ))) = 0 := by simp [h]
    rw [hsingle] at h1
    exact hi0 (by exact_mod_cast h1)
  have hker : LinearMap.ker L ≠ ⊤ := fun h => hLne (LinearMap.ker_eq_top.mp h)
  -- the level set of `L` at `b j0` has measure zero
  have hlevel : MeasureTheory.volume {c : Fin l → Fin m → ℝ | L c = (b j0 : ℝ)} = 0 := by
    by_cases hb : (b j0 : ℝ) ∈ Set.range L
    · obtain ⟨c0, hc0⟩ := hb
      have hA : {c : Fin l → Fin m → ℝ | L c = (b j0 : ℝ)}
          = ↑(AffineSubspace.mk' c0 (LinearMap.ker L)) := by
        ext q
        show L q = (b j0 : ℝ) ↔ q ∈ AffineSubspace.mk' c0 (LinearMap.ker L)
        rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker, map_sub, hc0]
        exact sub_eq_zero.symm
      rw [hA]
      refine Measure.addHaar_affineSubspace volume _ (fun htop => hker ?_)
      rw [← AffineSubspace.direction_mk' c0 (LinearMap.ker L), htop, AffineSubspace.direction_top]
    · have hS : {c : Fin l → Fin m → ℝ | L c = (b j0 : ℝ)} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro c hc
        exact hb ⟨c, hc⟩
      rw [hS, measure_empty]
  -- the target set is contained in this level set
  have hsub : {c : Fin l → Fin m → ℝ | ∀ j, (∑ i, (a i : ℝ) * c i j) = (b j : ℝ)}
      ⊆ {c : Fin l → Fin m → ℝ | L c = (b j0 : ℝ)} := by
    intro c hc
    show L c = (b j0 : ℝ)
    rw [hL_apply]
    exact hc j0
  have hle : MeasureTheory.volume {c : Fin l → Fin m → ℝ |
        ∀ j, (∑ i, (a i : ℝ) * c i j) = (b j : ℝ)} ≤ 0 := by
    calc MeasureTheory.volume {c : Fin l → Fin m → ℝ |
          ∀ j, (∑ i, (a i : ℝ) * c i j) = (b j : ℝ)}
        ≤ MeasureTheory.volume {c : Fin l → Fin m → ℝ | L c = (b j0 : ℝ)} :=
          measure_mono hsub
      _ = 0 := hlevel
  exact le_antisymm hle (by simp)

end Commons.Analysis.Measure