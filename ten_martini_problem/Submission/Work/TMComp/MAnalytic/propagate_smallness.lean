import Mathlib
import Submission.Work.TMComp.MAnalytic.propagate_defs
import Submission.Work.TMComp.MAnalytic.S_cover_defs
import Submission.Work.TMComp.MAnalytic.annulus_step
import Submission.Work.TMComp.MAnalytic.grow_inplace_geom

namespace Work.TMComp.MAnalytic

-- ===== unfolding lemmas =====
theorem ps_mem_G_zero {W : Set ℂ} {r : ℝ} {a : ℂ} {z : ℂ} {R : ℝ} :
    (z, R) ∈ G W r a 0 ↔ z = a ∧ 0 < R ∧ R ≤ r / 2 := Iff.rfl

theorem ps_mem_G_succ {W : Set ℂ} {r : ℝ} {a : ℂ} {z : ℂ} {n : ℕ} {R : ℝ} :
    (z, R) ∈ G W r a (n + 1) ↔
      (z, R) ∈ G W r a n ∨ ∃ q ∈ G W r a n, Step W q.1 q.2 z R := Iff.rfl

theorem ps_norm_sub_triangle (x y z : ℂ) : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
  simpa only [dist_eq_norm] using dist_triangle x y z

-- ===== geometric lemmas =====
theorem ps_exists_good_witness {W : Set ℂ} {a : ℂ} {r : ℝ}
    (hball : Metric.closedBall a r ⊆ W) :
    ∀ (n : ℕ) (p : ℂ × ℝ), p ∈ G W r a n →
      ∃ q ∈ G W r a n, Metric.closedBall q.1 (2 * q.2) ⊆ W ∧
        p.1 ∈ Metric.ball q.1 (q.2 * Real.sqrt 2) := by
  intro n
  induction n with
  | zero =>
    rintro ⟨z, R⟩ hp
    obtain ⟨hza, hRpos, hRle⟩ := ps_mem_G_zero.mp hp
    refine ⟨(z, R), ps_mem_G_zero.mpr ⟨hza, hRpos, hRle⟩, ?_, ?_⟩
    · subst hza
      refine subset_trans (fun w hw => ?_) hball
      rw [Metric.mem_closedBall, dist_eq_norm] at hw ⊢
      linarith
    · rw [Metric.mem_ball, dist_self]
      exact mul_pos hRpos (Real.sqrt_pos_of_pos (by norm_num))
  | succ n ih =>
    rintro ⟨z, R⟩ hp
    rcases ps_mem_G_succ.mp hp with hp | ⟨q, hq, hstep⟩
    · obtain ⟨q', hq', hdeep, hmem⟩ := ih (z, R) hp
      exact ⟨q', G_mono W r a n hq', hdeep, hmem⟩
    · obtain ⟨hRpos, hdeep, hdist⟩ := hstep
      refine ⟨q, G_mono W r a n hq, hdeep, ?_⟩
      rw [Metric.mem_ball, dist_eq_norm]
      linarith

theorem ps_step_ball_subset_S {W : Set ℂ} {r : ℝ} {a : ℂ} {n : ℕ} {y : ℂ} {R : ℝ}
    (hy : (y, R) ∈ G W r a n) (hgood : Metric.closedBall y (2 * R) ⊆ W) :
    Metric.ball y (R * Real.sqrt 2) ⊆ S W r a (n + 1) := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  refine ⟨R * Real.sqrt 2 - ‖z - y‖, ?_⟩
  have hpos : 0 < R * Real.sqrt 2 - ‖z - y‖ := by linarith
  refine ps_mem_G_succ.mpr (Or.inr ⟨(y, R), hy, ?_⟩)
  refine ⟨hpos, hgood, ?_⟩
  have h : ‖z - y‖ + (R * Real.sqrt 2 - ‖z - y‖) = R * Real.sqrt 2 := by ring
  linarith [h]

theorem ps_Dset_isOpen (W : Set ℂ) (r : ℝ) (a : ℂ) : IsOpen (Dset W r a) := by
  rw [Metric.isOpen_iff]
  intro y hy
  obtain ⟨m, R, hG, hdeep⟩ := mem_Dset.mp hy
  have hR : 0 < R := mem_G_pos m hG
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  refine ⟨R * Real.sqrt 2, mul_pos hR hsqrt2pos, ?_⟩
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hsqrt2lt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hdz2R : ‖z - y‖ < 2 * R := by
    have : R * Real.sqrt 2 < 2 * R := by nlinarith
    linarith
  refine mem_Dset.mpr ⟨m + 1,
    min ((2 * R - ‖z - y‖) / 2) ((R * Real.sqrt 2 - ‖z - y‖) / 2), ?_, ?_⟩
  · refine ps_mem_G_succ.mpr (Or.inr ⟨(y, R), hG, ?_⟩)
    have hR'pos : 0 < min ((2 * R - ‖z - y‖) / 2) ((R * Real.sqrt 2 - ‖z - y‖) / 2) :=
      lt_min (by linarith) (by linarith)
    refine ⟨hR'pos, hdeep, ?_⟩
    have hle : min ((2 * R - ‖z - y‖) / 2) ((R * Real.sqrt 2 - ‖z - y‖) / 2)
        ≤ (R * Real.sqrt 2 - ‖z - y‖) / 2 := min_le_right _ _
    linarith
  · refine subset_trans (fun w hw => ?_) hdeep
    rw [Metric.mem_closedBall, dist_eq_norm] at hw ⊢
    have hle : min ((2 * R - ‖z - y‖) / 2) ((R * Real.sqrt 2 - ‖z - y‖) / 2)
        ≤ (2 * R - ‖z - y‖) / 2 := min_le_left _ _
    have h1 : ‖w - y‖ ≤ ‖w - z‖ + ‖z - y‖ := ps_norm_sub_triangle w z y
    linarith

theorem ps_Dset_subset_W {W : Set ℂ} {r : ℝ} {a : ℂ} : Dset W r a ⊆ W := by
  rintro y ⟨m, R, hG, hdeep⟩
  have hR : 0 < R := mem_G_pos m hG
  exact hdeep (Metric.mem_closedBall_self (by linarith))

theorem ps_Dset_compl_isOpen {W : Set ℂ} (hWo : IsOpen W) {r : ℝ} {a : ℂ} :
    IsOpen (W \ Dset W r a) := by
  rw [Metric.isOpen_iff]
  rintro z ⟨hzW, hzD⟩
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hWo z hzW
  refine ⟨ε / 16, by positivity, ?_⟩
  intro u hu
  rw [Metric.mem_ball, dist_eq_norm] at hu
  refine ⟨?_, ?_⟩
  · exact hεW (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
  · intro huD
    rw [mem_Dset] at huD
    obtain ⟨m, R, hG, hdeep⟩ := huD
    have hR : 0 < R := mem_G_pos m hG
    have hroom : Metric.closedBall u (3 * ε / 4) ⊆ W := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      apply hεW
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : ‖w - z‖ ≤ ‖w - u‖ + ‖u - z‖ := ps_norm_sub_triangle w u z
      linarith
    obtain ⟨m', R', hG', hdeep', hR'sqrt⟩ :=
      grow_inplace_geom hG hR (by linarith : (0:ℝ) < 3 * ε / 4) hdeep hroom
    have hdz : ‖u - z‖ < R' * Real.sqrt 2 := by linarith
    have hpos : 0 < (1 / 2) * min (ε / 2) (R' * Real.sqrt 2 - ‖u - z‖) :=
      mul_pos (by norm_num) (lt_min (by linarith) (by linarith))
    have hle : (1 / 2) * min (ε / 2) (R' * Real.sqrt 2 - ‖u - z‖)
        ≤ (1 / 2) * (R' * Real.sqrt 2 - ‖u - z‖) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
    have hle2 : 2 * ((1 / 2) * min (ε / 2) (R' * Real.sqrt 2 - ‖u - z‖)) ≤ ε / 2 := by
      have := min_le_left (ε / 2) (R' * Real.sqrt 2 - ‖u - z‖)
      linarith
    have hnz : ‖z - u‖ = ‖u - z‖ := norm_sub_rev z u
    have hstep : Step W u R' z ((1 / 2) * min (ε / 2) (R' * Real.sqrt 2 - ‖u - z‖)) := by
      refine ⟨hpos, hdeep', ?_⟩
      rw [hnz]
      linarith [hle, hdz]
    have hzG : (z, (1 / 2) * min (ε / 2) (R' * Real.sqrt 2 - ‖u - z‖)) ∈
        G W r a (m' + 1) :=
      ps_mem_G_succ.mpr (Or.inr ⟨(u, R'), hG', hstep⟩)
    have hzdeep : Metric.closedBall z
        (2 * ((1 / 2) * min (ε / 2) (R' * Real.sqrt 2 - ‖u - z‖))) ⊆ W := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      apply hεW
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [hw, hle2, hε]
    exact hzD (mem_Dset.mpr ⟨m' + 1, _, hzG, hzdeep⟩)

theorem ps_S_cover {W : Set ℂ} (hWo : IsOpen W) (hWc : IsPreconnected W)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall a r ⊆ W) :
    ∀ z ∈ W, ∃ n, z ∈ S W r a n := by
  have haW : a ∈ W := hball (Metric.mem_closedBall_self (le_of_lt hr))
  have haD : a ∈ Dset W r a := by
    refine ⟨0, r / 2, ps_mem_G_zero.mpr ⟨rfl, by linarith, le_refl _⟩, ?_⟩
    have h : 2 * (r / 2) = r := by ring
    rw [h]; exact hball
  have hDW : Dset W r a = W := by
    refine Set.eq_of_subset_of_subset ps_Dset_subset_W ?_
    by_contra hsub
    rw [Set.not_subset] at hsub
    obtain ⟨z, hzW, hzD⟩ := hsub
    have hsub2 : W ⊆ Dset W r a ∪ (W \ Dset W r a) := by
      intro x hx
      by_cases hx' : x ∈ Dset W r a
      · exact Or.inl hx'
      · exact Or.inr ⟨hx, hx'⟩
    have hne1 : (W ∩ Dset W r a).Nonempty := ⟨a, haW, haD⟩
    have hne2 : (W ∩ (W \ Dset W r a)).Nonempty := ⟨z, hzW, hzW, hzD⟩
    obtain ⟨w, hw⟩ := hWc (Dset W r a) (W \ Dset W r a) (ps_Dset_isOpen W r a)
      (ps_Dset_compl_isOpen hWo) hsub2 hne1 hne2
    simp only [Set.mem_inter_iff, Set.mem_sdiff] at hw
    obtain ⟨hwW, hwD, hwW2, hwD'⟩ := hw
    exact hwD' hwD
  intro z hz
  exact mem_Eset.mp (Dset_subset_Eset W r a (hDW.ge hz))

theorem ps_S_interior {W : Set ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r ⊆ W) :
    ∀ n, S W r a n ⊆ interior (S W r a (n + 1)) := by
  have _ := hr
  intro n z hz
  obtain ⟨R, hR⟩ := hz
  obtain ⟨q, hqG, hqgood, hzball⟩ := ps_exists_good_witness hball n (z, R) hR
  have hsub : Metric.ball q.1 (q.2 * Real.sqrt 2) ⊆ S W r a (n + 1) :=
    ps_step_ball_subset_S hqG hqgood
  have hzball' : z ∈ interior (Metric.ball q.1 (q.2 * Real.sqrt 2)) := by
    rwa [Metric.isOpen_ball.interior_eq]
  exact interior_mono hsub hzball'

theorem ps_S_mono_le {W : Set ℂ} {r : ℝ} {a : ℂ} {m n : ℕ} (h : m ≤ n) :
    S W r a m ⊆ S W r a n := by
  induction h with
  | refl => exact subset_rfl
  | step h ih => exact ih.trans S_mono

theorem ps_G_decay {W : Set ℂ} {a : ℂ} {r : ℝ} {g : ℂ → ℂ} {s : ℝ}
    (hs : 0 ≤ s) (han : AnalyticOnNhd ℂ g W) (h1 : ∀ z ∈ W, ‖g z‖ ≤ 1)
    (hsm : ∀ z ∈ Metric.closedBall a r, ‖g z‖ ≤ Real.exp (-s)) :
    ∀ n (y : ℂ) (R : ℝ), (y, R) ∈ G W r a n →
      ∀ w ∈ Metric.closedBall y R, ‖g w‖ ≤ Real.exp (-(s / 2 ^ n)) := by
  intro n
  induction n with
  | zero =>
    intro y R h w hw
    obtain ⟨hy, hRpos, hRle⟩ := ps_mem_G_zero.mp h
    have hw' : w ∈ Metric.closedBall a r := by
      rw [Metric.mem_closedBall] at hw ⊢
      rw [hy] at hw
      linarith
    simpa using hsm w hw'
  | succ n ih =>
    intro y R h w hw
    rcases ps_mem_G_succ.mp h with h | ⟨q, hq, hstep⟩
    · have h' := ih y R h w hw
      refine h'.trans (Real.exp_le_exp.mpr ?_)
      have h2n : (2:ℝ)^n ≤ 2^(n+1) := by
        rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]
      have hdiv := div_le_div_of_nonneg_left hs (pow_pos (by norm_num : (0:ℝ)<2) n) h2n
      exact neg_le_neg hdiv
    · obtain ⟨hR', hW', hdist⟩ := hstep
      have hqpos : 0 < q.2 := mem_G_pos n hq
      have hδ : 0 ≤ s / 2 ^ n := div_nonneg hs (by positivity)
      have hstep_lem := annulus_step (W := W) (a := q.1) (R := q.2) (δ := s / 2 ^ n)
        hqpos hδ han hW' (fun z hz => h1 z (hW' hz)) (ih q.1 q.2 hq)
      have hwq : w ∈ Metric.closedBall q.1 (q.2 * Real.sqrt 2) := by
        simp only [Metric.mem_closedBall] at hw ⊢
        have h2 : dist y q.1 + R ≤ q.2 * Real.sqrt 2 := by
          simpa only [dist_eq_norm, norm_sub_rev] using hdist
        calc dist w q.1 ≤ dist w y + dist y q.1 := dist_triangle _ _ _
          _ ≤ R + dist y q.1 := by linarith
          _ ≤ q.2 * Real.sqrt 2 := by linarith [h2]
      have heq : (s / 2 ^ n) / 2 = s / 2 ^ (n + 1) := by
        rw [pow_succ]; ring
      rw [heq] at hstep_lem
      exact hstep_lem w hwq

theorem propagate_smallness {W : Set ℂ} (hWo : IsOpen W) (hWc : IsPreconnected W)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall a r ⊆ W) :
    ∀ K ⊆ W, IsCompact K → ∃ c : ℝ, 0 < c ∧ ∀ (g : ℂ → ℂ) (s : ℝ), 0 ≤ s →
      AnalyticOnNhd ℂ g W → (∀ z ∈ W, ‖g z‖ ≤ 1) →
      (∀ z ∈ Metric.closedBall a r, ‖g z‖ ≤ Real.exp (-s)) →
      ∀ z ∈ K, ‖g z‖ ≤ Real.exp (-(c * s)) := by
  intro K hKW hK
  have hcov : K ⊆ ⋃ n, interior (S W r a n) := by
    intro z hz
    obtain ⟨n, hn⟩ := ps_S_cover hWo hWc hr hball z (hKW hz)
    exact Set.mem_iUnion.mpr ⟨n + 1, ps_S_interior hr hball n hn⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun n => interior (S W r a n))
    (fun n => isOpen_interior) hcov
  refine ⟨(1 / 2 : ℝ) ^ t.sup id, pow_pos (by norm_num) _, ?_⟩
  intro g s hs han h1 hsm z hz
  have hKN : z ∈ S W r a (t.sup id) := by
    have hzt := ht hz
    simp only [Set.mem_iUnion, exists_prop] at hzt
    obtain ⟨n, hnt, hzn⟩ := hzt
    exact ps_S_mono_le (Finset.le_sup (f := id) hnt) (interior_subset hzn)
  obtain ⟨R, hR⟩ := hKN
  have hRpos : 0 < R := mem_G_pos (t.sup id) hR
  have hdec := ps_G_decay hs han h1 hsm (t.sup id) z R hR z
    (Metric.mem_closedBall_self (le_of_lt hRpos))
  have he : (1 / 2 : ℝ) ^ (t.sup id) * s = s / 2 ^ (t.sup id) := by
    rw [one_div, inv_pow, inv_mul_eq_div]
  rw [he]
  exact hdec

end Work.TMComp.MAnalytic
