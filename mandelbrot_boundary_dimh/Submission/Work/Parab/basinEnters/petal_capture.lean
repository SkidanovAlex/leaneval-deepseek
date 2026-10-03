import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ

/-!
# Petal capture for a parabolic germ (the correct form of `basin_enters_petal`)

The requested statement `Work.Parab.basinEnters.basin_enters_petal` is false as written: the
basin `MandelDim.ParabolicBasin f D` is a *locally uniform* notion and `IsParabolicGerm f D`
constrains `f` only on the (not necessarily connected) open set `D`, so `D` may contain a point
`z` at which `f` is *locally constant* and `≡ 0`, whence the whole neighbourhood collapses to `0`
and the orbit of `z` hits `0` at time `1` and stays there (see
`Submission/Work/Parab/basinEnters/counterexample.lean` for a machine-checked refutation).

This file proves the mathematical content that is actually true, and isolates the missing
hypothesis: if the orbit of `z` never hits `0` then it eventually enters the petal.  The proof is
the classical one, in the chart `w = -1/z`: along the orbit the chart coordinates satisfy
`w_{n+1} - w_n = h(z_n)/(1 + z_n h(z_n)) → h(0) = 1`, so `Re w_n → +∞` and the orbit enters every
sector `Re w > M`, `|w| > 1/r`, i.e. every petal `Petal r M`.

Main results:

* `Work.Parab.basinEnters.exists_iterate_mem_petal` — the sequence form;
* `Work.Parab.basinEnters.basin_enters_petal_of_avoids_zero` — the germ-level form, which is the
  requested statement with the single extra hypothesis `∀ n, f^[n] z ≠ 0`.
-/

open Complex Set Metric Filter
open scoped Topology

namespace Work.Parab.basinEnters

open Work.FatouCoord

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r r' A A' M : ℝ} {z z' w : ℂ}

/-! ## Restricting the quantitative hypotheses -/

lemma parabolicBounds_mono (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    (hr' : 0 < r') (hle : r' ≤ r) : Work.FatouCoord.ParabolicBounds f h a r' A A' :=
  ⟨hr', hb.hA, hb.hA', fun z hz => hb.f_eq z (ball_subset_ball hle hz),
    hb.h_diff.mono (ball_subset_ball hle),
    fun z hz => hb.h_close z (ball_subset_ball hle hz),
    fun z hz => hb.h_bound z (ball_subset_ball hle hz),
    fun z hz => hb.h_deriv_bound z (ball_subset_ball hle hz)⟩

/-! ## The chart increment -/

/-- In the chart `w = -1/z`, one step of the dynamics changes `w` by
`h z / (1 + z h z)`, which tends to `h 0 = 1` as `z → 0`. -/
lemma chart_increment (hb : Work.FatouCoord.ParabolicBounds f h a r A A') {z : ℂ}
    (hz : z ∈ ball 0 r) (hz0 : z ≠ 0) (hden : 1 + z * h z ≠ 0) :
    chart (f z) - chart z = h z / (1 + z * h z) := by
  have hf : f z = z * (1 + z * h z) := by rw [hb.f_eq z hz]; ring
  rw [chart, chart, hf]
  field_simp
  ring

/-! ## Quantitative bounds at a small radius -/

lemma norm_h_sub_one (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (hr : r ≤ 1 / 16)
    (hsmall : A * r ^ 2 + ‖a‖ * r ≤ 1 / 8) {z : ℂ} (hz : z ∈ ball 0 r) :
    ‖h z - 1‖ ≤ 1 / 8 := by
  have hzr : ‖z‖ ≤ r := le_of_lt (by simpa [mem_ball_zero_iff] using hz)
  have h1 : ‖h z - 1 - a * z‖ ≤ A * r ^ 2 :=
    le_trans (hb.h_close z hz) (mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg z]) hb.hA)
  have h2 : ‖a * z‖ ≤ ‖a‖ * r := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hzr (norm_nonneg a)
  have h3 : ‖h z - 1‖ ≤ ‖h z - 1 - a * z‖ + ‖a * z‖ :=
    calc ‖h z - 1‖ = ‖(h z - 1 - a * z) + a * z‖ := by congr 1; ring
      _ ≤ ‖h z - 1 - a * z‖ + ‖a * z‖ := norm_add_le _ _
  linarith

/-- **The increment is close to `1`**: on a small disc, `h z / (1 + z h z)` has real part at
least `1/2`. -/
lemma increment_re_ge (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (hr : r ≤ 1 / 16)
    (hsmall : A * r ^ 2 + ‖a‖ * r ≤ 1 / 8) {z : ℂ} (hz : z ∈ ball 0 r) :
    1 / 2 ≤ (h z / (1 + z * h z)).re := by
  have hzr : ‖z‖ < r := by simpa [mem_ball_zero_iff] using hz
  have hzr' : ‖z‖ ≤ r := le_of_lt hzr
  have hzh : ‖z * h z‖ ≤ 2 * r := by
    rw [norm_mul]
    calc ‖z‖ * ‖h z‖ ≤ r * 2 :=
          mul_le_mul hzr' (hb.h_bound z hz) (norm_nonneg _) (le_of_lt hb.hr)
      _ = 2 * r := by ring
  have hr16 : 2 * r ≤ 1 / 8 := by linarith
  have hden : 1 + z * h z ≠ 0 := by
    intro h0
    have : ‖z * h z‖ = 1 := by
      have : z * h z = -1 := by linear_combination h0
      rw [this, norm_neg, norm_one]
    linarith
  have hden' : 7 / 8 ≤ ‖1 + z * h z‖ := by
    have h5 := norm_sub_le (1 + z * h z) (z * h z)
    have h1 : (1 + z * h z) - z * h z = (1 : ℂ) := by ring
    rw [h1, norm_one] at h5
    linarith
  have hkey : ‖h z / (1 + z * h z) - 1‖ ≤ 2 / 7 := by
    have hnum : ‖h z - (1 + z * h z)‖ ≤ 1 / 4 :=
      calc ‖h z - (1 + z * h z)‖ = ‖(h z - 1) - z * h z‖ := by congr 1; ring
        _ ≤ ‖h z - 1‖ + ‖z * h z‖ := norm_sub_le _ _
        _ ≤ 1 / 8 + 2 * r := add_le_add (norm_h_sub_one hb hr hsmall hz) hzh
        _ ≤ 1 / 4 := by linarith
    have hdiv : h z / (1 + z * h z) - 1 = (h z - (1 + z * h z)) / (1 + z * h z) := by
      rw [sub_div, div_self hden]
    rw [hdiv, norm_div]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖1 + z * h z‖)]
    nlinarith [hnum, hden', norm_nonneg (h z - (1 + z * h z))]
  have h2 : (h z / (1 + z * h z)).re = 1 + (h z / (1 + z * h z) - 1).re := by
    rw [Complex.sub_re, Complex.one_re]
    ring
  have h3 := Complex.abs_re_le_norm (h z / (1 + z * h z) - 1)
  rw [abs_le] at h3
  have h4 : -(2 / 7 : ℝ) ≤ (h z / (1 + z * h z) - 1).re :=
    le_trans (neg_le_neg hkey) h3.1
  rw [h2]
  linarith

/-! ## Petal capture -/

/-- **Petal capture.**  If the orbit of `z` under a parabolic germ converges to `0` and never
hits `0`, then some iterate of `z` lies in the petal `Petal r M` (`M > 0` arbitrary). -/
theorem exists_iterate_mem_petal (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    (hr : r ≤ 1 / 16) (hsmall : A * r ^ 2 + ‖a‖ * r ≤ 1 / 8) (hM : 0 < M) {z : ℂ}
    (hconv : Tendsto (fun n : ℕ => f^[n] z) atTop (nhds (0 : ℂ)))
    (hne : ∀ n : ℕ, f^[n] z ≠ 0) :
    ∃ n : ℕ, f^[n] z ∈ Work.FatouCoord.Petal r M := by
  set w : ℕ → ℂ := fun n => chart (f^[n] z) with hw
  -- the orbit eventually stays in the disc and the increments are `≥ 1/2`
  have hev : ∀ᶠ n : ℕ in atTop,
      ‖f^[n] z‖ < r ∧ 1 / 2 ≤ (w (n + 1) - w n).re := by
    have hnorm : Tendsto (fun n : ℕ => ‖f^[n] z‖) atTop (nhds (0 : ℝ)) := by
      simpa using hconv.norm
    filter_upwards [hnorm.eventually (Metric.ball_mem_nhds (0 : ℝ) hb.hr)] with n hn
    have hnr : ‖f^[n] z‖ < r := by simpa [mem_ball_zero_iff] using hn
    refine ⟨hnr, ?_⟩
    have hzball : f^[n] z ∈ ball 0 r := by simpa [mem_ball_zero_iff] using hnr
    have hden : 1 + f^[n] z * h (f^[n] z) ≠ 0 := by
      intro h0
      have h1 : ‖f^[n] z * h (f^[n] z)‖ = 1 := by
        have : f^[n] z * h (f^[n] z) = -1 := by linear_combination h0
        rw [this, norm_neg, norm_one]
      have h2 : ‖f^[n] z * h (f^[n] z)‖ ≤ 2 * r := by
        rw [norm_mul]
        calc ‖f^[n] z‖ * ‖h (f^[n] z)‖ ≤ r * 2 :=
              mul_le_mul (le_of_lt hnr) (hb.h_bound _ hzball) (norm_nonneg _) (le_of_lt hb.hr)
          _ = 2 * r := by ring
      have h3 : (2 : ℝ) * r ≤ 1 / 8 := by linarith
      linarith
    have hci := chart_increment hb hzball (hne n) hden
    have hsucc : w (n + 1) = chart (f (f^[n] z)) := by
      simp only [hw, Function.iterate_succ_apply']
    rw [hsucc, hci]
    exact increment_re_ge hb hr hsmall hzball
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hincr : ∀ n ≥ N, (w n).re + 1 / 2 ≤ (w (n + 1)).re := by
    intro n hn
    have h := (hN n hn).2
    rw [Complex.sub_re] at h
    linarith
  have hgrowth : ∀ n ≥ N, (w N).re + ((n : ℝ) - (N : ℝ)) / 2 ≤ (w n).re := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
        have h1 : (w k).re + 1 / 2 ≤ (w (k + 1)).re := hincr k hk
        have h2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [h2]
        push_cast
        linarith
  -- choose an iterate with `Re w > M` and `‖w‖ > 1/r`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, max M (1 / r) < (w N).re + (K : ℝ) / 2 := by
    obtain ⟨K, hK⟩ := exists_nat_gt (2 * (max M (1 / r) - (w N).re))
    refine ⟨K, ?_⟩
    linarith
  refine ⟨N + K, ?_⟩
  have hgrow := hgrowth (N + K) (Nat.le_add_right N K)
  have hcast : (((N + K : ℕ) : ℝ) - (N : ℝ)) = (K : ℝ) := by push_cast; ring
  rw [hcast] at hgrow
  have hRe : M < (w (N + K)).re :=
    lt_of_le_of_lt (le_max_left M (1 / r)) (lt_of_lt_of_le hK hgrow)
  have hnorm : 1 / r < ‖w (N + K)‖ :=
    lt_of_le_of_lt (le_max_right M (1 / r))
      (lt_of_lt_of_le hK (le_trans hgrow (Complex.re_le_norm _)))
  have hz0 : f^[N + K] z ≠ 0 := hne _
  rw [Work.FatouCoord.chart_mem_Petal_iff hb.hr hz0, Work.FatouCoord.mem_PetalChart]
  exact ⟨hRe, hnorm⟩

/-! ## From the germ class to the quantitative hypotheses

This is `Work.Parab.exists_parabolicBounds_of_germ` (established elsewhere in the project),
reproved here so that this file does not depend on `Submission.Work.Parab.germ`. -/

theorem exists_parabolicBounds_of_germ {f : ℂ → ℂ} {D : Set ℂ}
    (hg : MandelDim.IsParabolicGerm f D) :
    ∃ (h : ℂ → ℂ) (a : ℂ) (r A A' : ℝ),
      Work.FatouCoord.ParabolicBounds f h a r A A' ∧ ball (0 : ℂ) r ⊆ D := by
  obtain ⟨hDopen, h0D, hdiff, hf0, hd1, hd2⟩ := hg
  obtain ⟨ρ, hρpos, hρ⟩ : ∃ ρ > 0, ball (0 : ℂ) ρ ⊆ D := by
    obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds h0D)
    exact ⟨ρ, hρpos, hρ⟩
  have hfan : AnalyticAt ℂ f 0 := hdiff.analyticAt (hDopen.mem_nhds h0D)
  have hd1' : iteratedDeriv 1 f 0 = 1 := by rw [iteratedDeriv_one]; exact hd1
  have hd2' : iteratedDeriv 2 f 0 = 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact hd2
  obtain ⟨hF, r', A'', A''', hr', hA'', hA''', hEq, hDiff, hClose, hBound, hDeriv⟩ :=
    Work.FatouCoord.Petal.exists_parabolic_germ_bounds (b := iteratedDeriv 3 f 0 / 6)
      hfan hf0 hd1' hd2' (by ring)
  refine ⟨hF, iteratedDeriv 3 f 0 / 6, min r' ρ, A'', A''', ?_, ?_⟩
  · exact Work.FatouCoord.ParabolicBounds.mk (lt_min hr' hρpos) hA'' hA'''
      (fun u hu => hEq u (ball_subset_ball (min_le_left _ _) hu))
      (hDiff.mono (ball_subset_ball (min_le_left _ _)))
      (fun u hu => hClose u (ball_subset_ball (min_le_left _ _) hu))
      (fun u hu => hBound u (ball_subset_ball (min_le_left _ _) hu))
      (fun u hu => hDeriv u (ball_subset_ball (min_le_left _ _) hu))
  · intro u hu
    exact hρ (ball_subset_ball (min_le_right _ _) hu)

/-! ## The germ-level form -/

/-- The parabolic basin pointwise lemma: a point of the basin has a neighbourhood on which the
iterates converge uniformly to `0`, hence its own orbit converges to `0`. -/
lemma tendsto_iterate_of_mem_basin {f : ℂ → ℂ} {D : Set ℂ} {z : ℂ}
    (hz : z ∈ MandelDim.ParabolicBasin f D) :
    Tendsto (fun n : ℕ => f^[n] z) atTop (nhds (0 : ℂ)) := by
  obtain ⟨U, hU, -, hunif⟩ := hz
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif ε hε)
  exact ⟨N, fun n hn => by simpa [dist_comm] using hN n hn z (mem_of_mem_nhds hU)⟩

/-- **`basin_enters_petal`, corrected.**  The only missing hypothesis is that the orbit of the
basin point never hits `0`; everything else of the requested statement is proved literally.

This is false without the extra hypothesis: see
`Work.Parab.basinEnters.basin_enters_petal_statement_false`. -/
theorem basin_enters_petal_of_avoids_zero {f : ℂ → ℂ} {D : Set ℂ}
    (hg : MandelDim.IsParabolicGerm f D) :
    ∃ (h : ℂ → ℂ) (a : ℂ) (r A A' M : ℝ),
      Work.FatouCoord.ParabolicBounds f h a r A A' ∧ Metric.ball 0 r ⊆ D ∧ 0 < M ∧
      (∀ z ∈ MandelDim.ParabolicBasin f D, (∀ n : ℕ, f^[n] z ≠ 0) →
        ∃ n : ℕ, f^[n] z ∈ Work.FatouCoord.Petal r M) ∧
      (∀ z ∈ MandelDim.ParabolicBasin f D,
        Filter.Tendsto (fun n : ℕ => f^[n] z) Filter.atTop (nhds (0 : ℂ))) := by
  obtain ⟨h, a, r₀, A, A', hb, hball⟩ := exists_parabolicBounds_of_germ hg
  set r : ℝ := min r₀ (min (1 / 16) (1 / (16 * (‖a‖ + A + 1)))) with hr
  have hA0 : 0 ≤ A := hb.hA
  have hA1 : A ≤ ‖a‖ + A + 1 := by linarith [norm_nonneg a]
  have hρ : 0 < 1 / (16 * (‖a‖ + A + 1)) := by positivity
  have hrpos : 0 < r := lt_min hb.hr (lt_min (by norm_num) hρ)
  have hrle : r ≤ r₀ := le_trans (min_le_left _ _) le_rfl
  have hr16 : r ≤ 1 / 16 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrbig : r ≤ 1 / (16 * (‖a‖ + A + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hb' : Work.FatouCoord.ParabolicBounds f h a r A A' := parabolicBounds_mono hb hrpos hrle
  have hball' : ball (0 : ℂ) r ⊆ D := fun z hz => hball (ball_subset_ball hrle hz)
  have hsmall : A * r ^ 2 + ‖a‖ * r ≤ 1 / 8 := by
    have hpos : 0 < 16 * (‖a‖ + A + 1) := by positivity
    have hAr : A * r ≤ 1 / 16 := by
      have h1 : A * r ≤ A * (1 / (16 * (‖a‖ + A + 1))) :=
        mul_le_mul_of_nonneg_left hrbig hA0
      have h2 : A * (1 / (16 * (‖a‖ + A + 1))) ≤ (‖a‖ + A + 1) * (1 / (16 * (‖a‖ + A + 1))) :=
        mul_le_mul_of_nonneg_right hA1 (by positivity)
      have h3 : (‖a‖ + A + 1) * (1 / (16 * (‖a‖ + A + 1))) = 1 / 16 := by
        field_simp
      linarith [h1, h2, h3]
    have hair : ‖a‖ * r ≤ 1 / 16 := by
      have h1 : ‖a‖ * r ≤ ‖a‖ * (1 / (16 * (‖a‖ + A + 1))) :=
        mul_le_mul_of_nonneg_left hrbig (norm_nonneg a)
      have h2 : ‖a‖ * (1 / (16 * (‖a‖ + A + 1))) ≤ (‖a‖ + A + 1) * (1 / (16 * (‖a‖ + A + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith [hA0]) (by positivity)
      have h3 : (‖a‖ + A + 1) * (1 / (16 * (‖a‖ + A + 1))) = 1 / 16 := by
        field_simp
      linarith [h1, h2, h3]
    have hsq : A * r ^ 2 ≤ 1 / 16 := by
      have : r ^ 2 ≤ r * (1 / 16) := by nlinarith [hrpos]
      calc A * r ^ 2 ≤ A * (r * (1 / 16)) := mul_le_mul_of_nonneg_left this hA0
        _ = (A * r) * (1 / 16) := by ring
        _ ≤ (1 / 16) * (1 / 16) := mul_le_mul_of_nonneg_right hAr (by norm_num)
        _ ≤ 1 / 16 := by norm_num
    linarith
  refine ⟨h, a, r, A, A', 1, hb', hball', one_pos, ?_, ?_⟩
  · intro z hzbasin hne
    exact exists_iterate_mem_petal hb' hr16 hsmall one_pos
      (tendsto_iterate_of_mem_basin hzbasin) hne
  · intro z hzbasin
    exact tendsto_iterate_of_mem_basin hzbasin

end
end Work.Parab.basinEnters
