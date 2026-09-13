import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.CompletePartialOrder

set_option linter.unusedVariables false

namespace Commons.Measure.HardyLittlewood

open Metric

theorem good_balls_cover_F {d : ℕ} {R : ℝ} (hR : 0 < R)
    {F : Set (EuclideanSpace ℝ (Fin d))} (hFopen : IsOpen F)
    (hFB : F ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)
    (hprop : F ≠ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R) :
    F ⊆ ⋃ x ∈ {x ∈ F | Metric.infDist x (Fᶜ) < R - ‖x‖},
          Metric.ball x (Metric.infDist x (Fᶜ)) := by
  intro z hz
  rw [Set.mem_iUnion₂]
  simp only [exists_prop]
  -- Fᶜ is nonempty
  have hFcne : (Fᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro hFuniv
    apply hprop
    have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← hFuniv]; exact hFB
    rw [hFuniv, hball]
  have hzR : ‖z‖ < R := by
    have := Metric.mem_ball.mp (hFB hz)
    simpa [dist_eq_norm] using this
  -- a point outside F but inside the ball
  have hnotsub : ¬ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R ⊆ F) := by
    intro hsub
    exact hprop (le_antisymm hFB hsub)
  obtain ⟨p, hpball, hpF⟩ := Set.not_subset.mp hnotsub
  have hpc : p ∈ Fᶜ := hpF
  have hr0_lt : Metric.infDist (0 : EuclideanSpace ℝ (Fin d)) (Fᶜ) < R :=
    lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hpc)
      (by simpa [dist_comm] using Metric.mem_ball.mp hpball)
  -- infDist to Fᶜ is positive on F
  have hposF : ∀ y ∈ F, 0 < Metric.infDist y (Fᶜ) := by
    intro y hy
    have hyc : y ∉ closure (Fᶜ) := by
      rw [hFopen.isClosed_compl.closure_eq]; exact fun hh => hh hy
    exact (Metric.infDist_pos_iff_notMem_closure hFcne).mp hyc
  by_cases hgood : Metric.infDist z (Fᶜ) < R - ‖z‖
  · exact ⟨z, ⟨hz, hgood⟩, by rw [Metric.mem_ball]; simpa using hposF z hz⟩
  · replace hgood : R - ‖z‖ ≤ Metric.infDist z (Fᶜ) := not_lt.mp hgood
    have hDpos : 0 < R - ‖z‖ := by linarith
    set g : ℝ → ℝ := fun t => Metric.infDist ((1 - t) • z) (Fᶜ) - t * ‖z‖ with hgdef
    have hcontt : Continuous fun t : ℝ => ((1 - t) • z : EuclideanSpace ℝ (Fin d)) := by
      fun_prop
    have hgcont : Continuous g := by rw [hgdef]; fun_prop
    have hg0 : g 0 = Metric.infDist z (Fᶜ) := by rw [hgdef]; simp
    -- key lemma producing a witness from a suitable parameter
    have key : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → g t = (R - ‖z‖)/2 → (1 - t) • z ∈ F →
        ∃ x, x ∈ {x ∈ F | Metric.infDist x (Fᶜ) < R - ‖x‖} ∧
          z ∈ Metric.ball x (Metric.infDist x (Fᶜ)) := by
      intro t htIcc hgt hytF
      have ht0 : 0 ≤ t := htIcc.1
      have ht1 : t ≤ 1 := htIcc.2
      have h1t : 0 ≤ 1 - t := by linarith
      set y : EuclideanSpace ℝ (Fin d) := (1 - t) • z with hydef
      have hynorm : ‖y‖ = (1 - t) * ‖z‖ := by
        rw [hydef, norm_smul, Real.norm_of_nonneg h1t]
      have hzy : dist z y = t * ‖z‖ := by
        rw [hydef, dist_eq_norm]
        have hv : z - (1 - t) • z = t • z := by
          have h2 : (1 - t) • z = z - t • z := by rw [sub_smul, one_smul]
          rw [h2]; abel
        rw [hv, norm_smul, Real.norm_of_nonneg ht0]
      have hh : Metric.infDist ((1 - t) • z) (Fᶜ) - t * ‖z‖ = (R - ‖z‖)/2 := hgt
      rw [← hydef] at hh
      have hgt' : Metric.infDist y (Fᶜ) = (R - ‖z‖)/2 + t * ‖z‖ := by linarith
      refine ⟨y, ⟨hytF, ?_⟩, ?_⟩
      · rw [hgt', hynorm]; linarith
      · rw [Metric.mem_ball, hzy, hgt']; linarith
    -- exit set
    set E : Set ℝ := {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ (1 - t) • z ∈ Fᶜ} with hEdef
    have hEclosed : IsClosed E := by
      rw [hEdef]
      exact isClosed_Icc.inter (IsClosed.preimage hcontt hFopen.isClosed_compl)
    by_cases hEne : E.Nonempty
    · -- there is a first exit point
      have hbddE : BddBelow E := ⟨0, by rintro t ⟨ht, _⟩; exact ht.1⟩
      have hτmem : sInf E ∈ E := hEclosed.csInf_mem hEne hbddE
      have hτIcc : sInf E ∈ Set.Icc (0:ℝ) 1 := hτmem.1
      have hτc : (1 - sInf E) • z ∈ Fᶜ := hτmem.2
      have hτpos : 0 < sInf E := by
        rcases lt_or_eq_of_le hτIcc.1 with h | h
        · exact h
        · exfalso
          have hz' : (1 - sInf E) • z = z := by rw [← h]; simp
          rw [hz'] at hτc
          exact hτc hz
      have hmemF : ∀ t : ℝ, t < sInf E → t ∈ Set.Icc (0:ℝ) 1 → (1 - t) • z ∈ F := by
        intro t ht htic
        by_contra htc
        have htE : t ∈ E := by rw [hEdef]; exact ⟨htic, htc⟩
        have hs : sInf E ≤ t := csInf_le hbddE htE
        exact (not_lt.mpr hs) ht
      have hgτ : g (sInf E) ≤ 0 := by
        show Metric.infDist ((1 - sInf E) • z) (Fᶜ) - sInf E * ‖z‖ ≤ 0
        rw [Metric.infDist_zero_of_mem hτc]
        have : 0 ≤ sInf E * ‖z‖ := mul_nonneg hτIcc.1 (norm_nonneg z)
        linarith
      obtain ⟨t, htIcc, hgt⟩ := (Set.mem_image g (Set.Icc (0:ℝ) (sInf E)) ((R - ‖z‖)/2)).mp
        ((intermediate_value_Icc' hτIcc.1 hgcont.continuousOn)
          (show (R - ‖z‖)/2 ∈ Set.Icc (g (sInf E)) (g 0) from
            ⟨by linarith [hgτ, hDpos], by rw [hg0]; linarith [hgood, hDpos]⟩))
      have htlt : t < sInf E := by
        rcases lt_or_eq_of_le htIcc.2 with h | h
        · exact h
        · exfalso; rw [h] at hgt; linarith [hgτ, hDpos]
      exact key t ⟨htIcc.1, le_trans htIcc.2 hτIcc.2⟩ hgt
        (hmemF t htlt ⟨htIcc.1, le_trans htIcc.2 hτIcc.2⟩)
    · -- the whole segment lies in F
      have hallF : ∀ t ∈ Set.Icc (0:ℝ) 1, (1 - t) • z ∈ F := by
        intro t ht
        by_contra htc
        exact hEne ⟨t, by rw [hEdef]; exact ⟨ht, htc⟩⟩
      have h0F : (0 : EuclideanSpace ℝ (Fin d)) ∈ F := by
        have := hallF 1 (by norm_num)
        simpa using this
      have hg1 : g 1 = Metric.infDist (0 : EuclideanSpace ℝ (Fin d)) (Fᶜ) - ‖z‖ := by
        rw [hgdef]; simp
      by_cases hpos : 0 < g 1
      · refine ⟨0, ⟨h0F, by simpa using hr0_lt⟩, ?_⟩
        rw [Metric.mem_ball]
        have : ‖z‖ < Metric.infDist (0 : EuclideanSpace ℝ (Fin d)) (Fᶜ) := by
          rw [hg1] at hpos; linarith
        simpa [dist_eq_norm] using this
      · have hle1 : g 1 ≤ 0 := le_of_not_gt hpos
        obtain ⟨t, htIcc, hgt⟩ := (Set.mem_image g (Set.Icc (0:ℝ) 1) ((R - ‖z‖)/2)).mp
          ((intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hgcont.continuousOn)
            (show (R - ‖z‖)/2 ∈ Set.Icc (g 1) (g 0) from
              ⟨by linarith [hle1, hDpos], by rw [hg0]; linarith [hgood, hDpos]⟩))
        exact key t htIcc hgt (hallF t htIcc)

end Commons.Measure.HardyLittlewood