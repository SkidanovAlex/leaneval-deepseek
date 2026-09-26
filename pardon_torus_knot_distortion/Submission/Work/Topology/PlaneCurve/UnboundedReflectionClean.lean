import Mathlib
import Submission.Work.Topology.PlaneCurve.WindingTrapClean
import Submission.Work.Smooth.JordanSeparation.ComplHelpers
import Submission.Work.Smooth.JordanSeparation.janiszewski_disjoint
import Submission.Work.Topology.PlaneCurve.compl_jordan_atMostTwo
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range

namespace Work.Smooth.SphereJordan

open Set

-- For a continuous 2*pi-periodic curve `η : ℝ → ℂ` injective on one period (a Jordan curve)
-- which avoids `0` and is antipodal-free (`η s ≠ -η t` for all `s`, `t`), the connected
-- component of `0` in the complement of `Set.range η ∪ Set.range (-η)` is UNBOUNDED.
--
-- Proof.  Write `K = range η` and `K' = range (-η)`.  The two sets are compact and disjoint, and
-- `0` lies in neither.  By `antipodal_free_false_of_bounded_component` (applied to `η` and to
-- `-η`) the component of `0` in `Kᶜ` and the component of `0` in `K'ᶜ` are both *unbounded*; since
-- all points of large norm lie in a single component, this means that `0` and every point of large
-- norm lie in the same component of `Kᶜ`, and likewise for `K'ᶜ`.  Phragmén--Brouwer (the disjoint
-- case of Janiszewski's theorem, `janiszewski_disjoint`) applied to the disjoint compact sets `K`
-- and `K'` then shows that `0` and every point of large norm lie in the same component of
-- `(K ∪ K')ᶜ`, which is therefore unbounded.
--
-- Do NOT derive the result from anything proved with `sorry` (in particular not from
-- `Work.Smooth.SphereJordan.exists_jsep` or `Work.Smooth.SphereJordan.exists_windNumber_ne_zero`);
-- the proof must be free of `sorryAx`.
theorem unbounded_component_of_curve_and_reflection {η : ℝ → ℂ} (hη : Continuous η)
    (hper : Function.Periodic η (2 * Real.pi))
    (hinj : Set.InjOn η (Set.Ico 0 (2 * Real.pi)))
    (h0 : (0 : ℂ) ∉ Set.range η)
    (hanti : ∀ s t : ℝ, η s ≠ -η t) :
    ¬ Bornology.IsBounded
      (connectedComponentIn (Set.range η ∪ Set.range (fun t : ℝ => -η t))ᶜ (0 : ℂ)) := by
  classical
  -- ## The reflected curve
  have hμcont : Continuous fun t : ℝ => -η t := hη.neg
  have hμper : Function.Periodic (fun t : ℝ => -η t) (2 * Real.pi) := fun t => by
    simp only [hper t]
  have hμinj : Set.InjOn (fun t : ℝ => -η t) (Set.Ico 0 (2 * Real.pi)) :=
    fun a ha b hb hab => hinj ha hb (neg_inj.mp hab)
  have h0' : ∀ t : ℝ, η t ≠ 0 := fun t ht => h0 ⟨t, ht⟩
  have h0μ' : ∀ t : ℝ, -η t ≠ 0 := fun t => neg_ne_zero.mpr (h0' t)
  have hantiμ : ∀ s t : ℝ, -η s ≠ -(-η t) := by
    intro s t h
    exact hanti t s (by simpa using h.symm)
  -- ## Compactness and a bound for the norms of the traces
  have hKisc : IsCompact (Set.range η) :=
    Work.Topology.PlaneCurve.isCompact_range_of_periodic hη hper
  have hKμisc : IsCompact (Set.range (fun t : ℝ => -η t)) :=
    Work.Topology.PlaneCurve.isCompact_range_of_periodic hμcont hμper
  obtain ⟨M, hM⟩ := hKisc.isBounded.exists_norm_le
  set R : ℝ := max M 1 with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef]; exact le_trans zero_le_one (le_max_right _ _)
  have hRK : ∀ z ∈ Set.range η, ‖z‖ ≤ R := fun z hz =>
    le_trans (hM z hz) (le_max_left _ _)
  have hRKμ : ∀ z ∈ Set.range (fun t : ℝ => -η t), ‖z‖ ≤ R := by
    rintro z ⟨t, rfl⟩
    rw [norm_neg]
    exact hRK (η t) ⟨t, rfl⟩
  -- ## The far region
  have hfar_pre : IsPreconnected {z : ℂ | R < ‖z‖} :=
    Work.Smooth.JordanSeparation.isPreconnected_lt_norm_compl R hR0
  have hfar_K : {z : ℂ | R < ‖z‖} ⊆ (Set.range η)ᶜ := by
    intro z hz hcon
    rw [Set.mem_setOf_eq] at hz
    obtain ⟨t, ht⟩ := hcon
    have h1 := hRK (η t) ⟨t, rfl⟩
    rw [ht] at h1
    linarith
  have hfar_Kμ : {z : ℂ | R < ‖z‖} ⊆ (Set.range (fun t : ℝ => -η t))ᶜ := by
    intro z hz hcon
    rw [Set.mem_setOf_eq] at hz
    obtain ⟨t, ht⟩ := hcon
    have h1 := hRKμ z ⟨t, ht⟩
    linarith
  -- ## Both complements have an unbounded component of `0`
  have hunbddK : ¬ Bornology.IsBounded (connectedComponentIn (Set.range η)ᶜ (0 : ℂ)) :=
    fun hb => antipodal_free_false_of_bounded_component hη hper hinj h0' hb hanti
  have hunbddKμ : ¬ Bornology.IsBounded
      (connectedComponentIn (Set.range (fun t : ℝ => -η t))ᶜ (0 : ℂ)) :=
    fun hb => antipodal_free_false_of_bounded_component hμcont hμper hμinj h0μ' hb hantiμ
  -- ## The two traces are disjoint compact sets avoiding `0`
  have hdisj : Disjoint (Set.range η) (Set.range (fun t : ℝ => -η t)) := by
    rw [Set.disjoint_left]
    rintro z ⟨s, hs⟩ ⟨t, ht⟩
    exact hanti s t (hs.trans ht.symm)
  have h0U : (0 : ℂ) ∉ Set.range η ∪ Set.range (fun t : ℝ => -η t) := by
    rintro (h | h)
    · exact h0 h
    · obtain ⟨t, ht⟩ := h
      exact h0' t (neg_eq_zero.mp ht)
  -- ## Every point of large norm lies in the component of `0` off both traces
  have hkey : ∀ w : ℂ, R < ‖w‖ →
      w ∈ connectedComponentIn (Set.range η ∪ Set.range (fun t : ℝ => -η t))ᶜ (0 : ℂ) := by
    intro w hw
    have hwfar : w ∈ {z : ℂ | R < ‖z‖} := hw
    have hwK : w ∉ Set.range η := fun h => absurd (hRK w h) (not_le.mpr hw)
    have hwKμ : w ∉ Set.range (fun t : ℝ => -η t) :=
      fun h => absurd (hRKμ w h) (not_le.mpr hw)
    -- a point of large norm in the component of `0` off `range η`
    obtain ⟨z, hzmem, hzgt⟩ : ∃ z ∈ connectedComponentIn (Set.range η)ᶜ (0 : ℂ), R < ‖z‖ := by
      by_contra hcon
      push_neg at hcon
      exact hunbddK ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset
        (fun z hz => by rw [Metric.mem_closedBall, dist_zero_right]; exact hcon z hz))
    have hwA : w ∈ connectedComponentIn (Set.range η)ᶜ (0 : ℂ) := by
      rw [connectedComponentIn_eq hzmem]
      exact hfar_pre.subset_connectedComponentIn hzgt hfar_K hwfar
    -- likewise for the reflected curve
    obtain ⟨z', hz'mem, hz'gt⟩ :
        ∃ z' ∈ connectedComponentIn (Set.range (fun t : ℝ => -η t))ᶜ (0 : ℂ), R < ‖z'‖ := by
      by_contra hcon
      push_neg at hcon
      exact hunbddKμ ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset
        (fun z hz => by rw [Metric.mem_closedBall, dist_zero_right]; exact hcon z hz))
    have hwB : w ∈ connectedComponentIn (Set.range (fun t : ℝ => -η t))ᶜ (0 : ℂ) := by
      rw [connectedComponentIn_eq hz'mem]
      exact hfar_pre.subset_connectedComponentIn hz'gt hfar_Kμ hwfar
    exact Work.Smooth.JordanSeparation.janiszewski_disjoint hKisc hKμisc hdisj h0U
      (fun hcon => hcon.elim hwK hwKμ) hwA hwB
  -- ## Conclusion
  intro hb
  obtain ⟨M₂, hM₂⟩ := hb.exists_norm_le
  set w : ℂ := (((max M₂ R) + 1 : ℝ) : ℂ) with hwdef
  have hwnorm : ‖w‖ = max M₂ R + 1 := by
    rw [hwdef, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [le_max_right M₂ R, hR0])]
  have hwbig : R < ‖w‖ := by rw [hwnorm]; linarith [le_max_right M₂ R]
  have h1 := hM₂ w (hkey w hwbig)
  rw [hwnorm] at h1
  linarith [le_max_left M₂ R]

end Work.Smooth.SphereJordan
