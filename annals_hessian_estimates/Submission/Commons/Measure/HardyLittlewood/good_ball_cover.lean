import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Measure.HardyLittlewood.weak_type_one_finite_balls

namespace Commons.Measure.HardyLittlewood

open MeasureTheory Metric
open scoped ENNReal BigOperators

/-- Intersection of a sequence of open balls about `x` with radii shrinking down to `r` (from
above) is the closed ball of radius `r`. -/
theorem iInter_ball_eq_closedBall {α : Type*} [PseudoMetricSpace α] {x : α} {s : ℕ → ℝ} {r : ℝ}
    (hr : ∀ n, r < s n) (htend : Filter.Tendsto s Filter.atTop (nhds r)) :
    (⋂ n, Metric.ball x (s n)) = Metric.closedBall x r := by
  ext y
  simp only [Set.mem_iInter, mem_ball, mem_closedBall]
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    obtain ⟨n, hn⟩ := (htend.eventually (isOpen_Iio.mem_nhds hc)).exists
    exact absurd (h n) (not_lt.mpr hn.le)
  · intro h n
    exact lt_of_le_of_lt h (hr n)

/-- In `ℝ≥0∞`, if `y + z = 1` (encoded as `z = 1 - y`), `x` is finite and `x ≤ y * x + c`, then
`(1 - y) * x ≤ c`. -/
theorem one_sub_mul_le {x y c : ℝ≥0∞} (hy : y ≤ 1) (hx : x ≠ ⊤)
    (h : x ≤ y * x + c) : (1 - y) * x ≤ c := by
  have hyx_le : y * x ≤ x := by
    calc y * x ≤ 1 * x := mul_le_mul_of_nonneg_right hy zero_le
      _ = x := one_mul x
  have hyx : y * x ≠ ⊤ := ne_top_of_le_ne_top hx hyx_le
  have hx_eq : x = y * x + (1 - y) * x := by
    rw [← add_mul, add_tsub_cancel_of_le hy, one_mul]
  have key : y * x + (1 - y) * x ≤ y * x + c := by rw [← hx_eq]; exact h
  exact (ENNReal.add_le_add_iff_left hyx).mp key

theorem good_ball_cover {d : ℕ} {R δ : ℝ} (hR : 0 < R) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {E F : Set (EuclideanSpace ℝ (Fin d))} (hFopen : IsOpen F)
    (hFB : F ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R) (hEF : E ⊆ F)
    (hmain : ∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      Metric.ball x r ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R →
      ENNReal.ofReal (1 - δ) * MeasureTheory.volume (Metric.ball x r)
        < MeasureTheory.volume (Metric.ball x r ∩ E) → Metric.ball x r ⊆ F) :
    ENNReal.ofReal δ * MeasureTheory.volume
        (⋃ x ∈ {x ∈ F | Metric.infDist x (Fᶜ) < R - ‖x‖},
          Metric.ball x (Metric.infDist x (Fᶜ)))
      ≤ ENNReal.ofReal (5 ^ d) * MeasureTheory.volume (F \ E) := by
  set G : Set (EuclideanSpace ℝ (Fin d)) := {x | x ∈ F ∧ Metric.infDist x (Fᶜ) < R - ‖x‖} with hG
  by_cases hd : d = 0
  · subst hd
    have hempty : (⋃ x ∈ G, Metric.ball x (Metric.infDist x (Fᶜ))) = ∅ := by
      rw [Set.iUnion_eq_empty]
      intro x
      rw [Set.iUnion_eq_empty]
      intro hx
      have hxF : x ∈ F := hx.1
      have hFu : F = Set.univ :=
        Set.eq_univ_of_forall (fun y => by rw [Subsingleton.elim y x]; exact hxF)
      rw [hFu, Set.compl_univ, Metric.infDist_empty, Metric.ball_zero]
    rw [hempty, measure_empty, mul_zero]
    exact bot_le
  · have : NeZero d := ⟨hd⟩
    have hfrac : ∀ x ∈ G, MeasureTheory.volume (Metric.ball x (Metric.infDist x (Fᶜ)) ∩ E) ≤
        ENNReal.ofReal (1 - δ) * MeasureTheory.volume (Metric.ball x (Metric.infDist x (Fᶜ))) := by
      intro x hxG
      rw [hG] at hxG
      simp only [Set.mem_ofPred_eq] at hxG
      obtain ⟨_, hxR⟩ := hxG
      rcases eq_or_lt_of_le (Metric.infDist_nonneg (x := x) (s := Fᶜ)) with h0 | hpos
      · rw [← h0, Metric.ball_zero, Set.empty_inter, measure_empty, mul_zero]
      · have hne : (Fᶜ).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          intro hemp
          rw [hemp, Metric.infDist_empty] at hpos
          exact lt_irrefl 0 hpos
        have hc : 0 < R - ‖x‖ - Metric.infDist x (Fᶜ) := by linarith
        let s : ℕ → ℝ := fun n => Metric.infDist x (Fᶜ) + (R - ‖x‖ - Metric.infDist x (Fᶜ)) / ((n : ℝ) + 2)
        have hs_gt : ∀ n, Metric.infDist x (Fᶜ) < s n := by
          intro n
          simp only [s]
          have : 0 < (R - ‖x‖ - Metric.infDist x (Fᶜ)) / ((n : ℝ) + 2) := by positivity
          linarith
        have hs_lt : ∀ n, s n < R - ‖x‖ := by
          intro n
          simp only [s]
          have h2 : 0 < ((n : ℝ) + 2) := by positivity
          have h1 : (R - ‖x‖ - Metric.infDist x (Fᶜ)) / ((n : ℝ) + 2)
              < R - ‖x‖ - Metric.infDist x (Fᶜ) := by
            rw [div_lt_iff₀ h2]
            nlinarith [hc, (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
          linarith
        have hs_tend : Filter.Tendsto s Filter.atTop (nhds (Metric.infDist x (Fᶜ))) := by
          have hg : Filter.Tendsto (fun n : ℕ => n + 2) Filter.atTop Filter.atTop :=
            Filter.tendsto_add_atTop_nat 2
          have hzero : Filter.Tendsto
              (fun n : ℕ => (R - ‖x‖ - Metric.infDist x (Fᶜ)) / ((n : ℝ) + 2))
              Filter.atTop (nhds 0) := by
            have h := (tendsto_const_div_atTop_nhds_zero_nat (R - ‖x‖ - Metric.infDist x (Fᶜ))).comp hg
            simp only [Function.comp_def] at h
            simpa using h
          have hconst : Filter.Tendsto (fun _ : ℕ => Metric.infDist x (Fᶜ)) Filter.atTop
              (nhds (Metric.infDist x (Fᶜ))) := tendsto_const_nhds
          simpa only [s, add_zero] using hconst.add hzero
        have hs_anti : Antitone s := by
          intro m n hmn
          simp only [s]
          have hnm : ((m : ℝ) + 2) ≤ ((n : ℝ) + 2) := by
            exact_mod_cast (Nat.add_le_add_right hmn 2)
          have := div_le_div_of_nonneg_left hc.le (by positivity : (0 : ℝ) < (m : ℝ) + 2) hnm
          linarith
        have hball_sub : ∀ n, Metric.ball x (s n) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R := by
          intro n y hy
          rw [mem_ball] at hy ⊢
          calc dist y 0 = ‖y‖ := dist_zero_right y
            _ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
            _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
            _ = dist y x + ‖x‖ := by rw [dist_eq_norm]
            _ < (R - ‖x‖) + ‖x‖ := by linarith [hs_lt n]
            _ = R := by ring
        have hnotsub : ∀ n, ¬ (Metric.ball x (s n) ⊆ F) := by
          intro n hsub
          obtain ⟨y, hyc, hyx⟩ := (Metric.infDist_lt_iff hne).mp (hs_gt n)
          exact hyc (hsub (by rw [mem_ball, dist_comm]; exact hyx))
        have hfrac_n : ∀ n, MeasureTheory.volume (Metric.ball x (s n) ∩ E) ≤
            ENNReal.ofReal (1 - δ) * MeasureTheory.volume (Metric.ball x (s n)) := by
          intro n
          by_contra hcon
          rw [not_le] at hcon
          exact hnotsub n (hmain x (s n)
            (by linarith [hs_gt n, Metric.infDist_nonneg (x := x) (s := Fᶜ)]) (hball_sub n) hcon)
        have hmono : ∀ n, MeasureTheory.volume (Metric.ball x (Metric.infDist x (Fᶜ)) ∩ E) ≤
            ENNReal.ofReal (1 - δ) * MeasureTheory.volume (Metric.ball x (s n)) := by
          intro n
          calc MeasureTheory.volume (Metric.ball x (Metric.infDist x (Fᶜ)) ∩ E)
              ≤ MeasureTheory.volume (Metric.ball x (s n) ∩ E) :=
                measure_mono (Set.inter_subset_inter_left E (ball_subset_ball (hs_gt n).le))
            _ ≤ ENNReal.ofReal (1 - δ) * MeasureTheory.volume (Metric.ball x (s n)) := hfrac_n n
        have hanti : Antitone (fun n => Metric.ball x (s n)) :=
          fun m n hmn => ball_subset_ball (hs_anti hmn)
        have hden : ⨅ n, MeasureTheory.volume (Metric.ball x (s n))
            = MeasureTheory.volume (Metric.ball x (Metric.infDist x (Fᶜ))) := by
          rw [← hanti.measure_iInter (fun n => measurableSet_ball.nullMeasurableSet)
              ⟨0, (measure_ball_lt_top).ne⟩,
            iInter_ball_eq_closedBall hs_gt hs_tend,
            Measure.addHaar_closedBall_eq_addHaar_ball]
        have hmul : ENNReal.ofReal (1 - δ) * ⨅ n, MeasureTheory.volume (Metric.ball x (s n))
            = ⨅ n, ENNReal.ofReal (1 - δ) * MeasureTheory.volume (Metric.ball x (s n)) :=
          ENNReal.mul_iInf (fun h => absurd h ENNReal.ofReal_ne_top)
        calc MeasureTheory.volume (Metric.ball x (Metric.infDist x (Fᶜ)) ∩ E)
            ≤ ⨅ n, ENNReal.ofReal (1 - δ) * MeasureTheory.volume (Metric.ball x (s n)) :=
              le_iInf hmono
          _ = ENNReal.ofReal (1 - δ) * ⨅ n, MeasureTheory.volume (Metric.ball x (s n)) := hmul.symm
          _ = ENNReal.ofReal (1 - δ) * MeasureTheory.volume (Metric.ball x (Metric.infDist x (Fᶜ))) := by
              rw [hden]
    -- good centres with positive radius
    let S : Set (EuclideanSpace ℝ (Fin d)) := {x | x ∈ G ∧ 0 < Metric.infDist x (Fᶜ)}
    have hSG : S ⊆ G := fun x hx => hx.1
    have hSpos : ∀ x ∈ S, 0 < Metric.infDist x (Fᶜ) := fun x hx => hx.2
    have hRle : ∀ a ∈ S, Metric.infDist a (Fᶜ) ≤ R := by
      intro a ha
      have haG : a ∈ G := ha.1
      rw [hG] at haG
      simp only [Set.mem_ofPred_eq] at haG
      have h1 := haG.2
      have h2 : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
      linarith
    obtain ⟨u, huS, hu_disj, hu_cov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (t := S) (fun x : EuclideanSpace ℝ (Fin d) => x) (fun x => Metric.infDist x (Fᶜ)) R hRle 5
      (by norm_num)
    have hu_count : u.Countable :=
      hu_disj.countable_of_nonempty_interior (fun i hi => ⟨i, by
        rw [(isOpen_ball).interior_eq]
        exact mem_ball_self (hSpos i (huS hi))⟩)
    have : Countable u := hu_count.to_subtype
    have hcover : (⋃ x ∈ G, Metric.ball x (Metric.infDist x (Fᶜ))) ⊆
        (⋃ b ∈ u, Metric.ball b (5 * Metric.infDist b (Fᶜ))) := by
      intro y hy
      rw [Set.mem_iUnion] at hy
      obtain ⟨x, hyx⟩ := hy
      rw [Set.mem_iUnion] at hyx
      obtain ⟨hxG, hyx⟩ := hyx
      rcases eq_or_lt_of_le (Metric.infDist_nonneg (x := x) (s := Fᶜ)) with h0 | hpos
      · rw [← h0, Metric.ball_zero] at hyx
        exact absurd hyx (Set.notMem_empty y)
      · obtain ⟨b, hbu, hbsub⟩ := hu_cov x ⟨hxG, hpos⟩
        exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hbu, hbsub hyx⟩⟩
    have hWmeas : MeasureTheory.volume (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ)))
        = ∑' b : u, MeasureTheory.volume
            (Metric.ball (b : EuclideanSpace ℝ (Fin d)) (Metric.infDist (b : EuclideanSpace ℝ (Fin d)) (Fᶜ))) :=
      measure_biUnion hu_count hu_disj (fun b _ => measurableSet_ball)
    have hstep1 : MeasureTheory.volume (⋃ x ∈ G, Metric.ball x (Metric.infDist x (Fᶜ))) ≤
        ENNReal.ofReal (5 ^ d) * MeasureTheory.volume (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) := by
      calc MeasureTheory.volume (⋃ x ∈ G, Metric.ball x (Metric.infDist x (Fᶜ)))
          ≤ MeasureTheory.volume (⋃ b ∈ u, Metric.ball b (5 * Metric.infDist b (Fᶜ))) :=
            measure_mono hcover
        _ ≤ ∑' b : u, MeasureTheory.volume
              (Metric.ball (b : EuclideanSpace ℝ (Fin d)) (5 * Metric.infDist (b : EuclideanSpace ℝ (Fin d)) (Fᶜ))) := by
            rw [Set.biUnion_eq_iUnion]
            exact measure_iUnion_le _
        _ = ∑' b : u, ENNReal.ofReal (5 ^ d) * MeasureTheory.volume
              (Metric.ball (b : EuclideanSpace ℝ (Fin d)) (Metric.infDist (b : EuclideanSpace ℝ (Fin d)) (Fᶜ))) := by
            apply tsum_congr
            intro b
            exact volume_ball_mul_of_pos d (b : EuclideanSpace ℝ (Fin d)) (by norm_num)
              (Metric.infDist (b : EuclideanSpace ℝ (Fin d)) (Fᶜ))
        _ = ENNReal.ofReal (5 ^ d) * ∑' b : u, MeasureTheory.volume
              (Metric.ball (b : EuclideanSpace ℝ (Fin d)) (Metric.infDist (b : EuclideanSpace ℝ (Fin d)) (Fᶜ))) :=
            ENNReal.tsum_mul_left
        _ = ENNReal.ofReal (5 ^ d) * MeasureTheory.volume
              (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) := by rw [hWmeas]
    have hcap : MeasureTheory.volume ((⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) ∩ E) ≤
        ENNReal.ofReal (1 - δ) * MeasureTheory.volume
          (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) := by
      have h1 : MeasureTheory.volume ((⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) ∩ E) ≤
          ∑' b : u, MeasureTheory.volume
            (Metric.ball (b : EuclideanSpace ℝ (Fin d)) (Metric.infDist (b : EuclideanSpace ℝ (Fin d)) (Fᶜ)) ∩ E) := by
        rw [Set.biUnion_eq_iUnion u (fun b _ => Metric.ball b (Metric.infDist b (Fᶜ))),
          Set.iUnion_inter]
        exact measure_iUnion_le _
      calc MeasureTheory.volume ((⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) ∩ E)
          ≤ ∑' b : u, MeasureTheory.volume
              (Metric.ball (b : EuclideanSpace ℝ (Fin d)) (Metric.infDist (b : EuclideanSpace ℝ (Fin d)) (Fᶜ)) ∩ E) := h1
        _ ≤ ∑' b : u, ENNReal.ofReal (1 - δ) * MeasureTheory.volume
              (Metric.ball (b : EuclideanSpace ℝ (Fin d)) (Metric.infDist (b : EuclideanSpace ℝ (Fin d)) (Fᶜ))) :=
            ENNReal.tsum_le_tsum (fun b => hfrac (b : EuclideanSpace ℝ (Fin d)) (hSG (huS b.2)))
        _ = ENNReal.ofReal (1 - δ) * ∑' b : u, MeasureTheory.volume
              (Metric.ball (b : EuclideanSpace ℝ (Fin d)) (Metric.infDist (b : EuclideanSpace ℝ (Fin d)) (Fᶜ))) :=
            ENNReal.tsum_mul_left
        _ = ENNReal.ofReal (1 - δ) * MeasureTheory.volume
              (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) := by rw [hWmeas]
    have hWF : (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) ⊆ F := by
      apply Set.iUnion_subset
      intro b
      apply Set.iUnion_subset
      intro _
      exact ball_infDist_compl_subset
    have hWfin : MeasureTheory.volume (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) ≠ ⊤ :=
      ne_top_of_lt (lt_of_le_of_lt (measure_mono (hWF.trans hFB)) measure_ball_lt_top)
    have hWineq : ENNReal.ofReal δ * MeasureTheory.volume
        (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) ≤ MeasureTheory.volume (F \ E) := by
      have hδeq : ENNReal.ofReal δ = 1 - ENNReal.ofReal (1 - δ) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by linarith)]
        congr 1
        ring
      have hy1 : ENNReal.ofReal (1 - δ) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      have hsplit : ((⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) ∩ E) ∪
          ((⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) \ E)
          = (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) := by
        ext z
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
        tauto
      have hmain_ineq : MeasureTheory.volume (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) ≤
          ENNReal.ofReal (1 - δ) * MeasureTheory.volume (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ)))
            + MeasureTheory.volume ((⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) \ E) := by
        refine le_trans ?_ (add_le_add hcap le_rfl)
        calc MeasureTheory.volume (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ)))
            = MeasureTheory.volume (((⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) ∩ E) ∪
                ((⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) \ E)) := by rw [hsplit]
          _ ≤ _ := measure_union_le _ _
      have h2 : ENNReal.ofReal δ * MeasureTheory.volume
          (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ)))
          ≤ MeasureTheory.volume ((⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ))) \ E) := by
        rw [hδeq]
        exact one_sub_mul_le hy1 hWfin hmain_ineq
      exact le_trans h2 (measure_mono (fun z hz => ⟨hWF hz.1, hz.2⟩))
    calc ENNReal.ofReal δ * MeasureTheory.volume (⋃ x ∈ G, Metric.ball x (Metric.infDist x (Fᶜ)))
        ≤ ENNReal.ofReal δ * (ENNReal.ofReal (5 ^ d) * MeasureTheory.volume
            (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ)))) :=
          mul_le_mul_of_nonneg_left hstep1 zero_le
      _ = ENNReal.ofReal (5 ^ d) * (ENNReal.ofReal δ * MeasureTheory.volume
            (⋃ b ∈ u, Metric.ball b (Metric.infDist b (Fᶜ)))) := by ring
      _ ≤ ENNReal.ofReal (5 ^ d) * MeasureTheory.volume (F \ E) :=
          mul_le_mul_of_nonneg_left hWineq zero_le

end Commons.Measure.HardyLittlewood