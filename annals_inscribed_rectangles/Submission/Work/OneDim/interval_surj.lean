import Mathlib
import Submission.Work.OneDim.ArcDefs

/-!
# Every nonempty open interval is the range of an injective global local diffeomorphism `ℝ → ℝ`

Used to reparametrise arcs so that they are defined on all of `ℝ`.
-/

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

namespace Work.OneDim

/-- A nonempty open preconnected subset of `ℝ` admits an injective global local diffeomorphism
`e : ℝ → ℝ` with `range e = I`. -/
theorem interval_surj {I : Set ℝ} (hopen : IsOpen I)
    (hconn : IsPreconnected I) (hne : I.Nonempty) :
    ∃ e : ℝ → ℝ, Function.Injective e ∧
      IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm e ∧
      Set.range e = I := by
  have hmem := hconn.mem_intervals
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  obtain ⟨x0, hx0⟩ := hne
  rcases hmem with h | h | h | h | h | h | h | h | h | h
  · -- Icc
    exfalso
    have hsub : I ⊆ Set.Icc (sInf I) (sSup I) := le_of_eq h
    have hsub' : Set.Icc (sInf I) (sSup I) ⊆ I := ge_of_eq h
    have hx : x0 ∈ Set.Icc (sInf I) (sSup I) := hsub hx0
    have hle : sInf I ≤ sSup I := le_trans hx.1 hx.2
    have hmem' : sInf I ∈ I := hsub' ⟨le_rfl, hle⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (sInf I) hmem'
    have hnew : sInf I - ε / 2 ∈ I := by
      apply hball; rw [Metric.mem_ball]; rw [dist_eq_norm, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have h' : sInf I - ε / 2 ∈ Set.Icc (sInf I) (sSup I) := hsub hnew
    linarith [h'.1]
  · -- Ico
    exfalso
    have hsub : I ⊆ Set.Ico (sInf I) (sSup I) := le_of_eq h
    have hsub' : Set.Ico (sInf I) (sSup I) ⊆ I := ge_of_eq h
    have hx : x0 ∈ Set.Ico (sInf I) (sSup I) := hsub hx0
    have hle : sInf I < sSup I := lt_of_le_of_lt hx.1 hx.2
    have hmem' : sInf I ∈ I := hsub' ⟨le_rfl, hle⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (sInf I) hmem'
    have hnew : sInf I - ε / 2 ∈ I := by
      apply hball; rw [Metric.mem_ball]; rw [dist_eq_norm, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have h' : sInf I - ε / 2 ∈ Set.Ico (sInf I) (sSup I) := hsub hnew
    linarith [h'.1]
  · -- Ioc
    exfalso
    have hsub : I ⊆ Set.Ioc (sInf I) (sSup I) := le_of_eq h
    have hsub' : Set.Ioc (sInf I) (sSup I) ⊆ I := ge_of_eq h
    have hx : x0 ∈ Set.Ioc (sInf I) (sSup I) := hsub hx0
    have hle : sInf I < sSup I := lt_of_lt_of_le hx.1 hx.2
    have hmem' : sSup I ∈ I := hsub' ⟨hle, le_rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (sSup I) hmem'
    have hnew : sSup I + ε / 2 ∈ I := by
      apply hball; rw [Metric.mem_ball]; rw [dist_eq_norm, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have h' : sSup I + ε / 2 ∈ Set.Ioc (sInf I) (sSup I) := hsub hnew
    linarith [h'.2]
  · -- Ioo
    have hab : sInf I < sSup I := by
      have hx : x0 ∈ Set.Ioo (sInf I) (sSup I) := le_of_eq h hx0
      exact lt_trans hx.1 hx.2
    refine ⟨fun t => sInf I + (sSup I - sInf I) * (1 / (1 + Real.exp (-t))),
      injective_logistic _ _ hab, isLocalDiffeomorph_logistic _ _ hab, ?_⟩
    rw [range_logistic _ _ hab]
    exact h.symm
  · -- Ici
    exfalso
    have hsub : I ⊆ Set.Ici (sInf I) := le_of_eq h
    have hsub' : Set.Ici (sInf I) ⊆ I := ge_of_eq h
    have hmem' : sInf I ∈ I := hsub' (Set.mem_Ici.mpr le_rfl)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (sInf I) hmem'
    have hnew : sInf I - ε / 2 ∈ I := by
      apply hball; rw [Metric.mem_ball]; rw [dist_eq_norm, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have h' : sInf I ≤ sInf I - ε / 2 := hsub hnew
    linarith
  · -- Ioi
    refine ⟨fun t => sInf I + Real.exp t, injective_expShift _, isLocalDiffeomorph_expShift _,
      ?_⟩
    rw [range_expShift _]
    exact h.symm
  · -- Iic
    exfalso
    have hsub : I ⊆ Set.Iic (sSup I) := le_of_eq h
    have hsub' : Set.Iic (sSup I) ⊆ I := ge_of_eq h
    have hmem' : sSup I ∈ I := hsub' (Set.mem_Iic.mpr le_rfl)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (sSup I) hmem'
    have hnew : sSup I + ε / 2 ∈ I := by
      apply hball; rw [Metric.mem_ball]; rw [dist_eq_norm, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have h' : sSup I + ε / 2 ≤ sSup I := hsub hnew
    linarith
  · -- Iio
    refine ⟨fun t => sSup I - Real.exp (-t), injective_expNegShift _,
      isLocalDiffeomorph_expNegShift _, ?_⟩
    rw [range_expNegShift _]
    exact h.symm
  · -- univ
    exact ⟨id, Function.injective_id, isLocalDiffeomorph_id, Set.range_id.trans h.symm⟩
  · -- ∅
    exact absurd (h ▸ hx0) (Set.notMem_empty x0)

end Work.OneDim
