import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Commons.Measure.Real

open MeasureTheory
open scoped ENNReal

/-- `A` contains a `δ`-separated tuple of length `k`. -/
def Sep (A : Set ℝ) (δ : ℝ) (k : ℕ) : Prop :=
  ∃ t : Fin k → ℝ, (∀ i, t i ∈ A) ∧ ∀ i j, i ≠ j → δ ≤ |t i - t j|

/-- If `A` contains no `(n+1)`-point `δ`-separated set then it is covered by `n` open balls
of radius `δ`. -/
lemma sep_cover (δ : ℝ) : ∀ (n : ℕ) (A : Set ℝ), ¬ Sep A δ (n + 1) →
    ∃ m : ℕ, m ≤ n ∧ ∃ x : Fin m → ℝ, A ⊆ ⋃ i, Metric.ball (x i) δ := by
  intro n
  induction n with
  | zero =>
    intro A hA
    have hAe : A = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro a ha
      exact hA ⟨fun _ => a, fun _ => ha, fun i j hij => absurd (Fin.ext (by omega)) hij⟩
    exact ⟨0, le_refl 0, Fin.elim0, by rw [hAe]; exact Set.empty_subset _⟩
  | succ n ih =>
    intro A hA
    by_cases hAe : A = ∅
    · exact ⟨0, Nat.zero_le _, Fin.elim0, by rw [hAe]; exact Set.empty_subset _⟩
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hAe
      set A' : Set ℝ := {y ∈ A | δ ≤ |y - x|} with hA'def
      have hA' : ¬ Sep A' δ (n + 1) := by
        rintro ⟨s, hsA', hsep⟩
        apply hA
        refine ⟨Fin.cons x s, ?_, ?_⟩
        · intro i
          cases i using Fin.cases with
          | zero => simpa using hx
          | succ k => exact (hsA' k).1
        · intro i j hij
          cases i using Fin.cases with
          | zero =>
            cases j using Fin.cases with
            | zero => exact absurd rfl hij
            | succ l =>
              rw [Fin.cons_zero, Fin.cons_succ, abs_sub_comm]
              exact (hsA' l).2
          | succ k =>
            cases j using Fin.cases with
            | zero =>
              rw [Fin.cons_zero, Fin.cons_succ]
              exact (hsA' k).2
            | succ l =>
              rw [Fin.cons_succ, Fin.cons_succ]
              exact hsep k l (fun hkl => hij (by rw [hkl]))
      obtain ⟨m, hm, x', hcov'⟩ := ih A' hA'
      refine ⟨m + 1, by omega, Fin.cons x x', ?_⟩
      intro y hy
      by_cases hb : y ∈ Metric.ball x δ
      · exact Set.mem_iUnion.mpr ⟨0, by simpa using hb⟩
      · have hyA' : y ∈ A' := by
          refine ⟨hy, ?_⟩
          have h1 : ¬ dist y x < δ := fun h => hb (by simpa [Metric.mem_ball] using h)
          have h2 : δ ≤ dist y x := not_lt.mp h1
          rwa [Real.dist_eq] at h2
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov' hyA')
        exact Set.mem_iUnion.mpr ⟨j.succ, by simpa [Fin.cons_succ] using hj⟩

theorem separated_points_of_measure (A : Set ℝ) (hA : MeasurableSet A)
    (hfin : MeasureTheory.volume A ≠ ⊤) (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hcard : 2 * (n : ℝ) * δ < (MeasureTheory.volume A).toReal) :
    ∃ t : Fin (n + 1) → ℝ, (∀ i, t i ∈ A) ∧ ∀ i j, i ≠ j → δ ≤ |t i - t j| := by
  by_contra hcon
  obtain ⟨m, hm, x, hcov⟩ := sep_cover δ n A hcon
  have hvol : MeasureTheory.volume A ≤ ENNReal.ofReal (2 * (n : ℝ) * δ) := by
    calc MeasureTheory.volume A
        ≤ MeasureTheory.volume (⋃ i : Fin m, Metric.ball (x i) δ) := measure_mono hcov
      _ ≤ ∑ i : Fin m, MeasureTheory.volume (Metric.ball (x i) δ) :=
            measure_iUnion_fintype_le _ _
      _ = ∑ _i : Fin m, ENNReal.ofReal (2 * δ) := by simp
      _ = m • ENNReal.ofReal (2 * δ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ n • ENNReal.ofReal (2 * δ) :=
            nsmul_le_nsmul_left (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * δ)) hm
      _ = (n : ℝ≥0∞) * ENNReal.ofReal (2 * δ) := by rw [nsmul_eq_mul]
      _ = ENNReal.ofReal (2 * (n : ℝ) * δ) := by
            rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
            congr 1
            ring
  have htoReal : (MeasureTheory.volume A).toReal ≤ 2 * (n : ℝ) * δ := by
    calc (MeasureTheory.volume A).toReal
        ≤ (ENNReal.ofReal (2 * (n : ℝ) * δ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
      _ = 2 * (n : ℝ) * δ := ENNReal.toReal_ofReal (by positivity)
  linarith [hcard, htoReal]

end Commons.Measure.Real