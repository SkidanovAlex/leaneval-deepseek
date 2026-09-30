import Mathlib
import Submission.Work.BMF.grid_iUnion_Ico
import Submission.Work.BMF.grid_pairwiseDisjoint
import Submission.Work.BMF.grid_measure_shift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A grid-averaging lemma (`Work.BMF.exists_grid_shift`)

For a measurable set `A ⊆ [0, N h)` and `h > 0`, some shift `y ∈ [0, h)` detects at least the
average density `vol(A)/h` of `A` on the arithmetic grid `{ℓ h + y : ℓ < N}`.

The proof is the usual "average over the fundamental domain" argument: integrating the counting
function `y ↦ Σ_{ℓ<N} 1_A(ℓ h + y)` over `y ∈ [0, h)` gives exactly `vol A` (the translates
`[ℓ h, (ℓ+1) h)` tile `[0, N h)`), while the counting function is bounded by its (attained)
integer maximum `m`; hence `vol A ≤ m h`, i.e. `vol A / h ≤ m`.
-/

namespace Work.BMF

open Finset Real MeasureTheory
open scoped ENNReal

/-- Averaging identity: the `ν`-integral (over the fundamental domain `[0, h)`) of the counting
function of the grid points `ℓ h + y` equals the measure of `A`. -/
theorem grid_lintegral (A : Set ℝ) (h : ℝ) (hh : 0 < h) (hA : MeasurableSet A) (N : ℕ)
    (hN : ∀ x ∈ A, 0 ≤ x ∧ x < (N : ℝ) * h) :
    ∫⁻ y, (∑ l ∈ Finset.range N,
        ({y : ℝ | (l : ℝ) * h + y ∈ A}).indicator (1 : ℝ → ℝ≥0∞) y)
      ∂(volume.restrict (Set.Ico 0 h)) = volume A := by
  let J : ℕ → Set ℝ := fun l => Set.Ico ((l : ℝ) * h) (((l : ℝ) + 1) * h)
  have hAsub : A ⊆ Set.Ico 0 ((N : ℝ) * h) := fun x hx => ⟨(hN x hx).1, (hN x hx).2⟩
  have hT : ∀ l : ℕ, MeasurableSet ({y : ℝ | (l : ℝ) * h + y ∈ A}) := by
    intro l
    exact hA.preimage (by fun_prop)
  have hstep1 : ∫⁻ y, (∑ l ∈ Finset.range N,
        ({y : ℝ | (l : ℝ) * h + y ∈ A}).indicator (1 : ℝ → ℝ≥0∞) y)
      ∂(volume.restrict (Set.Ico 0 h))
      = ∑ l ∈ Finset.range N, ∫⁻ y,
        ({y : ℝ | (l : ℝ) * h + y ∈ A}).indicator (1 : ℝ → ℝ≥0∞) y
        ∂(volume.restrict (Set.Ico 0 h)) := by
    rw [lintegral_finsetSum]
    intro b hb
    exact measurable_const.indicator (hT b)
  have hstep2 : ∀ l : ℕ, ∫⁻ y, ({y : ℝ | (l : ℝ) * h + y ∈ A}).indicator
        (1 : ℝ → ℝ≥0∞) y ∂(volume.restrict (Set.Ico 0 h))
      = volume (A ∩ J l) := by
    intro l
    rw [lintegral_indicator_one (hT l), Measure.restrict_apply (hT l)]
    exact grid_measure_shift A h hh l
  have hunion : (⋃ l : Fin N, (A ∩ J (l : ℕ))) = A := by
    rw [← Set.inter_iUnion]
    have hJ : (⋃ l : Fin N, J (l : ℕ)) = Set.Ico 0 ((N : ℝ) * h) := by
      have := grid_iUnion_Ico h hh N
      simpa [J] using this
    rw [hJ, Set.inter_eq_left.mpr hAsub]
  have hmu : volume (⋃ l : Fin N, (A ∩ J (l : ℕ))) = ∑ l : Fin N, volume (A ∩ J (l : ℕ)) := by
    have hpw : Pairwise (Function.onFun Disjoint (fun l : Fin N => A ∩ J (l : ℕ))) := by
      intro i j hij
      exact Disjoint.mono inf_le_right inf_le_right (by
        have hh' := grid_pairwiseDisjoint h hh N hij
        simpa [J] using hh')
    have hmeas : ∀ i : Fin N, MeasurableSet (A ∩ J (i : ℕ)) := fun i => hA.inter measurableSet_Ico
    rw [measure_iUnion hpw hmeas, tsum_fintype]
  have hsum_conv : ∑ l ∈ Finset.range N, volume (A ∩ J l)
      = ∑ l : Fin N, volume (A ∩ J (l : ℕ)) :=
    (Fin.sum_univ_eq_sum_range (fun l => volume (A ∩ J l)) N).symm
  calc ∫⁻ y, (∑ l ∈ Finset.range N,
        ({y : ℝ | (l : ℝ) * h + y ∈ A}).indicator (1 : ℝ → ℝ≥0∞) y)
      ∂(volume.restrict (Set.Ico 0 h))
      = ∑ l ∈ Finset.range N, ∫⁻ y,
        ({y : ℝ | (l : ℝ) * h + y ∈ A}).indicator (1 : ℝ → ℝ≥0∞) y
        ∂(volume.restrict (Set.Ico 0 h)) := hstep1
    _ = ∑ l ∈ Finset.range N, volume (A ∩ J l) := Finset.sum_congr rfl (fun l _ => hstep2 l)
    _ = ∑ l : Fin N, volume (A ∩ J (l : ℕ)) := hsum_conv
    _ = volume (⋃ l : Fin N, (A ∩ J (l : ℕ))) := hmu.symm
    _ = volume A := by rw [hunion]

theorem exists_grid_shift (A : Set ℝ) (h : ℝ) (hh : 0 < h) (hA : MeasurableSet A) (N : ℕ)
    (hN : ∀ x ∈ A, 0 ≤ x ∧ x < N * h) :
    ∃ y ∈ Set.Ico (0:ℝ) h, (volume A).toReal / h ≤
      ∑ ℓ ∈ Finset.range N, A.indicator (fun _ => (1:ℝ)) (ℓ * h + y) := by
  classical
  let G : ℝ → ℕ := fun y => ∑ l ∈ Finset.range N, if (l : ℝ) * h + y ∈ A then 1 else 0
  let H : ℝ → ℝ≥0∞ := fun y => ∑ l ∈ Finset.range N,
      ({y : ℝ | (l : ℝ) * h + y ∈ A}).indicator (1 : ℝ → ℝ≥0∞) y
  have hG_le : ∀ y, G y ≤ N := by
    intro y
    simp only [G]
    calc ∑ l ∈ Finset.range N, (if (l : ℝ) * h + y ∈ A then 1 else 0 : ℕ)
        ≤ ∑ l ∈ Finset.range N, 1 := Finset.sum_le_sum (fun l _ => by split <;> omega)
      _ = N := by simp
  have term_eq : ∀ (l : ℕ) (y : ℝ),
      ({y : ℝ | (l : ℝ) * h + y ∈ A}).indicator (1 : ℝ → ℝ≥0∞) y
        = ((if (l : ℝ) * h + y ∈ A then 1 else 0 : ℕ) : ℝ≥0∞) := by
    intro l y
    by_cases hmem : (l : ℝ) * h + y ∈ A
    · simp [hmem]
    · simp [hmem]
  have hH_eq : ∀ y, H y = (G y : ℝ≥0∞) := by
    intro y
    simp only [H, G]
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun l _ => term_eq l y)
  let S : Finset ℕ := (Finset.range (N + 1)).filter
      (fun n => ∃ y ∈ Set.Ico (0:ℝ) h, G y = n)
  have hS_nonempty : S.Nonempty := by
    refine ⟨G 0, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hG_le 0), 0, Set.left_mem_Ico.mpr hh, rfl⟩
  let m : ℕ := S.max' hS_nonempty
  have hG_attain : ∃ y0 ∈ Set.Ico (0:ℝ) h, G y0 = m := by
    have hmem : m ∈ S := by
      rw [show m = S.max' hS_nonempty from rfl]
      exact Finset.max'_mem S hS_nonempty
    simp only [S, Finset.mem_filter, Finset.mem_range] at hmem
    obtain ⟨-, y0, hy0, hy0eq⟩ := hmem
    exact ⟨y0, hy0, hy0eq⟩
  have hG_bound : ∀ y ∈ Set.Ico (0:ℝ) h, G y ≤ m := by
    intro y hy
    have hmem : G y ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (hG_le y), y, hy, rfl⟩
    rw [show m = S.max' hS_nonempty from rfl]
    exact Finset.le_max' S (G y) hmem
  obtain ⟨y0, hy0mem, hy0eq⟩ := hG_attain
  have hae : ∀ᵐ y ∂(volume.restrict (Set.Ico 0 h)), H y ≤ (m : ℝ≥0∞) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    rw [hH_eq y]
    exact Nat.cast_le.mpr (hG_bound y hy)
  have hInt_eq : ∫⁻ y, H y ∂(volume.restrict (Set.Ico 0 h)) = volume A := by
    simpa only [H] using grid_lintegral A h hh hA N hN
  have hInt_le : ∫⁻ y, H y ∂(volume.restrict (Set.Ico 0 h))
      ≤ (m : ℝ≥0∞) * ENNReal.ofReal h := by
    calc ∫⁻ y, H y ∂(volume.restrict (Set.Ico 0 h))
        ≤ ∫⁻ y, (m : ℝ≥0∞) ∂(volume.restrict (Set.Ico 0 h)) := lintegral_mono_ae hae
      _ = (m : ℝ≥0∞) * (volume.restrict (Set.Ico 0 h)) Set.univ := lintegral_const _
      _ = (m : ℝ≥0∞) * ENNReal.ofReal h := by
            rw [Measure.restrict_apply_univ, Real.volume_Ico, sub_zero]
  have hvol : volume A ≤ (m : ℝ≥0∞) * ENNReal.ofReal h := by
    rw [← hInt_eq]; exact hInt_le
  have hreal : (volume A).toReal ≤ (m : ℝ) * h := by
    have hne : (m : ℝ≥0∞) * ENNReal.ofReal h ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) ENNReal.ofReal_ne_top
    have := ENNReal.toReal_mono hne hvol
    simpa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hh.le] using this
  have hdiv : (volume A).toReal / h ≤ (m : ℝ) := by
    rw [div_le_iff₀ hh]; exact hreal
  have hFG : ∀ y, (∑ l ∈ Finset.range N, A.indicator (fun _ => (1:ℝ)) ((l : ℝ) * h + y))
      = (G y : ℝ) := by
    intro y
    simp only [G]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hmem : (l : ℝ) * h + y ∈ A
    · simp [hmem]
    · simp [hmem]
  refine ⟨y0, hy0mem, ?_⟩
  have : (∑ ℓ ∈ Finset.range N, A.indicator (fun _ => (1:ℝ)) (ℓ * h + y0)) = (m : ℝ) := by
    rw [hFG y0, hy0eq]
  rw [this]
  exact hdiv

end Work.BMF
