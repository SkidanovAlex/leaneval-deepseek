import Mathlib
import Submission.Work.EQ.Ladf.wsec_tails
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.fan_base

/-!
# The tails at depth `M` of a local section (the principal descent)

`wsec_tails_ball`: for a local analytic section `g` of `⁰H` through a witness `p` whose own tails
at depth `M` are the germs (the junction identity at the base point), both tails of every chain
`g u` for `u` in a neighbourhood of the base point are the germs **from depth `M` on**.

The proof is the downward induction over the window `[M, max N₁ M₁]` described in
`WITNESS_SECTION_PLAN.md`: the uniform tail depths `N₁, M₁` of `H0_tail_bounded` seed the level
`K = max N₁ M₁`, and `wsec_step_fwd` / `wsec_step_bwd` descend one level at a time, the excluded
branch being separated from `A₁` / `A₂` by `invBranch_false_far_A1` / `fwdAlt_far_A2`.
-/

namespace Work.EQ.Ladf

open Work.EQ Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-- `germC a h w` lies within `1/8` of `A₁ = (-1/2, 0)` for small `w`. -/
theorem germC_close_A1 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : ℂ, ‖w‖ < ρ → ‖germC a h w - ((-1 / 2 : ℂ), (0 : ℂ))‖ < 1 / 8 := by
  have hcont := continuousAt_germC_zero (a := a) (h := h) (r := r) ha0 ha1 hh
  have hval := germC_value (a := a) (h := h) (r := r) ha0 ha1 hh
  have hev : ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖germC a h w - ((-1 / 2 : ℂ), (0 : ℂ))‖ < 1 / 8 := by
    have h1 : ∀ᶠ w in 𝓝 (0 : ℂ), germC a h w ∈ Metric.ball (germC a h 0) (1 / 8) :=
      hcont.eventually (Metric.ball_mem_nhds _ (by norm_num))
    filter_upwards [h1] with w hw
    have h2 : dist (germC a h w) (germC a h 0) < 1 / 8 := Metric.mem_ball.mp hw
    rw [hval] at h2
    rwa [dist_eq_norm] at h2
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hev
  exact ⟨ρ, hρ, fun w hw => hsub (by rwa [Metric.mem_ball, dist_zero_right])⟩

/-- `ugermC a h w` lies within `1/8` of `A₂ = (1/2, 0)` for small `w`. -/
theorem ugermC_close_A2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : ℂ, ‖w‖ < ρ → ‖ugermC a h w - ((1 / 2 : ℂ), (0 : ℂ))‖ < 1 / 8 := by
  have hcont := continuousAt_ugermC_zero (a := a) (h := h) (r := r) ha0 ha1 hh
  have hval := ugermC_zero (a := a) (h := h) (r := r) ha0 ha1 hh
  have hev : ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖ugermC a h w - ((1 / 2 : ℂ), (0 : ℂ))‖ < 1 / 8 := by
    have h1 : ∀ᶠ w in 𝓝 (0 : ℂ), ugermC a h w ∈ Metric.ball (ugermC a h 0) (1 / 8) :=
      hcont.eventually (Metric.ball_mem_nhds _ (by norm_num))
    filter_upwards [h1] with w hw
    have h2 : dist (ugermC a h w) (ugermC a h 0) < 1 / 8 := Metric.mem_ball.mp hw
    rw [hval] at h2
    rwa [dist_eq_norm] at h2
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hev
  exact ⟨ρ, hρ, fun w hw => hsub (by rwa [Metric.mem_ball, dist_zero_right])⟩

/-- **Box uniformity of an analytic section.**  On a small ball around `u₀`, all the coordinates of
the section up to level `K` (in modulus) and both parameters are `ε`-close to their values at
`u₀`. -/
theorem wsec_box {a : ℝ} {h : ℂ → ℂ} {g : ℂ → ChainData} {u₀ : ℂ} {ρ : ℝ}
    (hg : IsSectAt a h g u₀ ρ) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ u ∈ Metric.ball u₀ ρ',
      (∀ k : ℤ, |k| ≤ (K : ℤ) → ‖(g u).1 k - (g u₀).1 k‖ < ε) ∧
      ‖(g u).2.1 - (g u₀).2.1‖ < ε ∧ ‖(g u).2.2 - (g u₀).2.2‖ < ε := by
  classical
  have hρ : 0 < ρ := hg.1
  have h0mem : u₀ ∈ Metric.ball u₀ ρ := Metric.mem_ball_self hρ
  have hcoord : ∀ k : ℤ, ∀ᶠ u in 𝓝 u₀, ‖(g u).1 k - (g u₀).1 k‖ < ε := by
    intro k
    have hcont : ContinuousAt (fun u => (g u).1 k) u₀ :=
      ((hg.2.2.2.1 k) u₀ h0mem).continuousAt
    have h1 : ∀ᶠ u in 𝓝 u₀, (g u).1 k ∈ Metric.ball ((g u₀).1 k) ε :=
      hcont.eventually (Metric.ball_mem_nhds _ hε)
    filter_upwards [h1] with u hu
    have h2 : dist ((g u).1 k) ((g u₀).1 k) < ε := Metric.mem_ball.mp hu
    rwa [dist_eq_norm] at h2
  have hpsi2 : ∀ᶠ u in 𝓝 u₀, ‖(g u).2.2 - (g u₀).2.2‖ < ε := by
    have hcont : ContinuousAt (fun u => (g u).2.2) u₀ :=
      ((hg.2.2.2.2) u₀ h0mem).continuousAt
    have h1 : ∀ᶠ u in 𝓝 u₀, (g u).2.2 ∈ Metric.ball ((g u₀).2.2) ε :=
      hcont.eventually (Metric.ball_mem_nhds _ hε)
    filter_upwards [h1] with u hu
    have h2 : dist ((g u).2.2) ((g u₀).2.2) < ε := Metric.mem_ball.mp hu
    rwa [dist_eq_norm] at h2
  have hall : ∀ᶠ u in 𝓝 u₀,
      (∀ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖(g u).1 k - (g u₀).1 k‖ < ε) :=
    (Finset.eventually_all (Finset.Icc (-(K : ℤ)) (K : ℤ))).mpr (fun k _ => hcoord k)
  obtain ⟨ρ₁, hρ₁, hρ₁b⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hall hpsi2)
  refine ⟨min ρ₁ (min ε ρ), lt_min hρ₁ (lt_min hε hρ),
    le_trans (min_le_right ρ₁ (min ε ρ)) (min_le_right ε ρ), ?_⟩
  intro u hu
  have hu0 : dist u u₀ < min ρ₁ (min ε ρ) := Metric.mem_ball.mp hu
  have huρ₁ : dist u u₀ < ρ₁ := lt_of_lt_of_le hu0 (min_le_left ρ₁ (min ε ρ))
  have hu1 : dist u u₀ < min ε ρ := lt_of_lt_of_le hu0 (min_le_right ρ₁ (min ε ρ))
  have huε : dist u u₀ < ε := lt_of_lt_of_le hu1 (min_le_left ε ρ)
  have huρ : dist u u₀ < ρ := lt_of_lt_of_le hu1 (min_le_right ε ρ)
  have hu' : u ∈ Metric.ball u₀ ρ₁ := Metric.mem_ball.mpr huρ₁
  obtain ⟨hA, hB⟩ := hρ₁b hu'
  refine ⟨fun k hk => hA k (by simpa only [Finset.mem_Icc] using (abs_le.mp hk)), ?_, hB⟩
  have h1 : (g u).2.1 = u := (hg.2.2.1 u (Metric.mem_ball.mpr huρ)).2
  have h2 : (g u₀).2.1 = u₀ := (hg.2.2.1 u₀ h0mem).2
  rw [h1, h2]
  rwa [dist_eq_norm] at huε


/-- **Both tails at depth `M` for a local section through a witness.**

If `g` is an analytic local section of `⁰H` through the witness `p = candChain a h f [] b M c u₀`
(value `c`), and the witness itself has its *backward* tail at depth `M` (the junction identity
`bwdP a b (fan a h f u₀) = ugermC a h (λ^M (c/u₀))` — its forward tail at depth `M` is automatic),
then on a neighbourhood of `u₀` both tails of every chain `g u` are the germs from depth `M` on. -/
theorem wsec_tails_ball {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (M : ℕ) (f b : List Bool) {c u₀ : ℂ} {ρ : ℝ} {g : ℂ → ChainData},
      f.length = M → b.length = M → u₀ ≠ 0 →
      IsSectAt a h g u₀ ρ → g u₀ = candChain a h f [] b M c u₀ →
      (∀ u ∈ Metric.ball u₀ ρ, (g u).2.1 * (g u).2.2 = c) →
      bwdP a b (fan a h f u₀) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / u₀)) →
      (eqLam a) ^ M * ‖u₀‖ < δ → (eqLam a) ^ M * ‖c / u₀‖ < δ →
      ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ u ∈ Metric.ball u₀ ρ',
        (∀ n : ℕ, M ≤ n → (g u).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * u)) ∧
        (∀ n : ℕ, M ≤ n → (g u).1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (c / u))) := by
  obtain ⟨δ₁, hδ₁, hstep1⟩ := wsec_step_fwd (a := a) ha0 ha1 (h := h) (r := r) hh
  obtain ⟨δ₂, hδ₂, hstep2⟩ := wsec_step_bwd (a := a) ha0 ha1 (h := h) (r := r) hh
  obtain ⟨ρg, hρg, hgclose⟩ := germC_close_A1 (a := a) (h := h) (r := r) ha0 ha1 hh
  obtain ⟨ρu, hρu, huclose⟩ := ugermC_close_A2 (a := a) (h := h) (r := r) ha0 ha1 hh
  have hlam : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a ≤ 1 := le_of_lt (eqLam_lt_one' ha0 ha1)
  have hΔδ₁ : (min (min δ₁ δ₂) (min ρg ρu)) ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hΔδ₂ : (min (min δ₁ δ₂) (min ρg ρu)) ≤ δ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hΔρg : (min (min δ₁ δ₂) (min ρg ρu)) ≤ ρg := le_trans (min_le_right _ _) (min_le_left _ _)
  have hΔρu : (min (min δ₁ δ₂) (min ρg ρu)) ≤ ρu := le_trans (min_le_right _ _) (min_le_right _ _)
  have hΔpos : 0 < min (min δ₁ δ₂) (min ρg ρu) := lt_min (lt_min hδ₁ hδ₂) (lt_min hρg hρu)
  refine ⟨(min (min δ₁ δ₂) (min ρg ρu)) / 2, by positivity, ?_⟩
  intro M f b c u₀ ρ g hf hb hu₀ne hg hgu₀ hval hjun hsm1 hsm2
  have hp_mem : candChain a h f [] b M c u₀ ∈ H0 a h := by
    rw [← hgu₀]; exact hg.2.1
  obtain ⟨N₁, M₁, K₀, ε₀, hε₀, hN₁K₀, hM₁K₀, htb⟩ := H0_tail_bounded ha0 ha1 hh _ hp_mem
  have hεbpos : 0 < min ε₀ (1 / 8 : ℝ) := lt_min hε₀ (by norm_num)
  obtain ⟨ρb, hρbpos, -, hbox⟩ := wsec_box (h := h) hg K₀ hεbpos
  have hψ2u₀ : (g u₀).2.2 = c / u₀ := by rw [hgu₀]; simp
  have hcontψ2 : ContinuousAt (fun u => (g u).2.2) u₀ :=
    ((hg.2.2.2.2) u₀ (Metric.mem_ball_self hg.1)).continuousAt
  have hsmallF : ∀ᶠ u in 𝓝 u₀,
      (eqLam a) ^ M * ‖u‖ < min (min δ₁ δ₂) (min ρg ρu) := by
    have h1 : ∀ᶠ u in 𝓝 u₀,
        u ∈ Metric.ball u₀ ((min (min δ₁ δ₂) (min ρg ρu)) / 2 / (eqLam a) ^ M) :=
      Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [h1] with u hu
    have h2 : ‖u - u₀‖ < (min (min δ₁ δ₂) (min ρg ρu)) / 2 / (eqLam a) ^ M := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hu
    have h3 : ‖u‖ ≤ ‖u₀‖ + ‖u - u₀‖ := by
      have h4 : ‖u‖ = ‖u₀ + (u - u₀)‖ := by
        congr 1
        ring
      rw [h4]
      exact norm_add_le _ _
    have h5 : (eqLam a) ^ M * ‖u - u₀‖ < (min (min δ₁ δ₂) (min ρg ρu)) / 2 := by
      have h6 := mul_lt_mul_of_pos_left h2 (pow_pos hlam M)
      rw [mul_comm ((eqLam a) ^ M) ((min (min δ₁ δ₂) (min ρg ρu)) / 2 / (eqLam a) ^ M),
        div_mul_cancel₀ _ (pow_ne_zero M (ne_of_gt hlam))] at h6
      exact h6
    have h7 : (eqLam a) ^ M * ‖u‖ ≤ (eqLam a) ^ M * (‖u₀‖ + ‖u - u₀‖) :=
      mul_le_mul_of_nonneg_left h3 (pow_nonneg (le_of_lt hlam) M)
    have h8 : (eqLam a) ^ M * (‖u₀‖ + ‖u - u₀‖)
        = (eqLam a) ^ M * ‖u₀‖ + (eqLam a) ^ M * ‖u - u₀‖ := by ring
    linarith [h7, h8.le, h8.ge, h5, hsm1]
  have hsmallB : ∀ᶠ u in 𝓝 u₀,
      (eqLam a) ^ M * ‖(g u).2.2‖ < min (min δ₁ δ₂) (min ρg ρu) := by
    have h1 : ∀ᶠ u in 𝓝 u₀,
        (g u).2.2 ∈ Metric.ball ((fun u => (g u).2.2) u₀)
          ((min (min δ₁ δ₂) (min ρg ρu)) / 2 / (eqLam a) ^ M) :=
      hcontψ2.eventually (Metric.ball_mem_nhds _ (by positivity))
    filter_upwards [h1] with u hu
    have h2 : dist ((g u).2.2) ((g u₀).2.2)
        < (min (min δ₁ δ₂) (min ρg ρu)) / 2 / (eqLam a) ^ M := Metric.mem_ball.mp hu
    rw [dist_eq_norm] at h2
    have h3 : ‖(g u).2.2‖ ≤ ‖(g u₀).2.2‖ + ‖(g u).2.2 - (g u₀).2.2‖ := by
      have h4 : ‖(g u).2.2‖ = ‖(g u₀).2.2 + ((g u).2.2 - (g u₀).2.2)‖ := by
        congr 1
        ring
      rw [h4]
      exact norm_add_le _ _
    have h5 : (eqLam a) ^ M * ‖(g u).2.2 - (g u₀).2.2‖
        < (min (min δ₁ δ₂) (min ρg ρu)) / 2 := by
      have h6 := mul_lt_mul_of_pos_left h2 (pow_pos hlam M)
      rw [mul_comm ((eqLam a) ^ M) ((min (min δ₁ δ₂) (min ρg ρu)) / 2 / (eqLam a) ^ M),
        div_mul_cancel₀ _ (pow_ne_zero M (ne_of_gt hlam))] at h6
      exact h6
    have h7 : (eqLam a) ^ M * ‖(g u).2.2‖
        ≤ (eqLam a) ^ M * (‖(g u₀).2.2‖ + ‖(g u).2.2 - (g u₀).2.2‖) :=
      mul_le_mul_of_nonneg_left h3 (pow_nonneg (le_of_lt hlam) M)
    have h8 : (eqLam a) ^ M * (‖(g u₀).2.2‖ + ‖(g u).2.2 - (g u₀).2.2‖)
        = (eqLam a) ^ M * ‖(g u₀).2.2‖ + (eqLam a) ^ M * ‖(g u).2.2 - (g u₀).2.2‖ := by ring
    have h9 : (eqLam a) ^ M * ‖(g u₀).2.2‖ = (eqLam a) ^ M * ‖c / u₀‖ := by rw [hψ2u₀]
    linarith [h7, h8.le, h8.ge, h5, h9.le, h9.ge, hsm2]
  obtain ⟨ρs, hρspos, hρsb⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hsmallF hsmallB)
  have hnu₀ : 0 < ‖u₀‖ := norm_pos_iff.mpr hu₀ne
  refine ⟨min (min ρb ρs) (min ρ (‖u₀‖ / 2)),
    lt_min (lt_min hρbpos hρspos) (lt_min hg.1 (by positivity)),
    le_trans (min_le_right _ _) (min_le_left _ _), ?_⟩
  intro u hu
  have hu0 : dist u u₀ < min (min ρb ρs) (min ρ (‖u₀‖ / 2)) := Metric.mem_ball.mp hu
  have huρb : u ∈ Metric.ball u₀ ρb :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hu0 (le_trans (min_le_left _ _) (min_le_left _ _)))
  have huρs : u ∈ Metric.ball u₀ ρs :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hu0 (le_trans (min_le_left _ _) (min_le_right _ _)))
  have huρ : u ∈ Metric.ball u₀ ρ :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hu0 (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hu2 : dist u u₀ < ‖u₀‖ / 2 :=
    lt_of_lt_of_le hu0 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hune : u ≠ 0 := by
    intro h0
    have h1 : dist u u₀ = ‖u₀‖ := by rw [h0, dist_zero_left]
    linarith [hu2, h1.le, h1.ge]
  have hquH0 : g u ∈ H0 a h := (hg.2.2.1 u huρ).1
  have hqchain : IsChain a h (g u) := isChain_of_mem_H0 hquH0
  have hquψ1 : (g u).2.1 = u := (hg.2.2.1 u huρ).2
  have hpsi2val : (g u).2.2 = c / u := IsSectAt.psi2 hg hval huρ hune
  obtain ⟨hcoord, hpsi1, hpsi2c⟩ := hbox u huρb
  have hsmallFu : (eqLam a) ^ M * ‖u‖ < min (min δ₁ δ₂) (min ρg ρu) := (hρsb huρs).1
  have hsmallBu : (eqLam a) ^ M * ‖(g u).2.2‖ < min (min δ₁ δ₂) (min ρg ρu) := (hρsb huρs).2
  -- H0_tail_bounded's box, expressed through the witness
  have hcoorde : ∀ k : ℤ, |k| ≤ (K₀ : ℤ) →
      ‖(g u).1 k - (candChain a h f [] b M c u₀).1 k‖ < ε₀ := by
    intro k hk
    have h1 := hcoord k hk
    have h2 : (g u₀).1 k = (candChain a h f [] b M c u₀).1 k := by rw [hgu₀]
    rw [h2] at h1
    exact lt_of_lt_of_le h1 (min_le_left _ _)
  have hpsi1e : ‖(g u).2.1 - (candChain a h f [] b M c u₀).2.1‖ < ε₀ := by
    have h2 : (candChain a h f [] b M c u₀).2.1 = u₀ := rfl
    have h3 : (g u₀).2.1 = u₀ := (hg.2.2.1 u₀ (Metric.mem_ball_self hg.1)).2
    have h4 : ‖(g u).2.1 - u₀‖ < min ε₀ (1 / 8 : ℝ) := by
      rw [← h3]; exact hpsi1
    rw [h2]
    exact lt_of_lt_of_le h4 (min_le_left _ _)
  have hpsi2e : ‖(g u).2.2 - (candChain a h f [] b M c u₀).2.2‖ < ε₀ := by
    have h2 : (candChain a h f [] b M c u₀).2.2 = c / u₀ := rfl
    rw [h2, ← hψ2u₀]
    exact lt_of_lt_of_le hpsi2c (min_le_left _ _)
  obtain ⟨hseed_f, hseed_b⟩ := htb (g u) hquH0 hcoorde hpsi1e hpsi2e
  have hKN : N₁ ≤ max N₁ M₁ := le_max_left _ _
  have hKM : M₁ ≤ max N₁ M₁ := le_max_right _ _
  have hKK₀ : max N₁ M₁ ≤ K₀ := max_le hN₁K₀ hM₁K₀
  have hp_fwd_val : ∀ n : ℕ, M ≤ n →
      (candChain a h f [] b M c u₀).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * u₀) :=
    fun n hn => candChain_fwd_tail (a := a) (h := h) hf c u₀ hn
  have hp_bwd_val : ∀ n : ℕ, M ≤ n →
      (candChain a h f [] b M c u₀).1 (-(n : ℤ)) =
        ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (c / u₀)) := by
    intro n hn
    rcases lt_or_eq_of_le hn with hlt | heq
    · exact candChain_bwd_tail (a := a) (h := h) c u₀ hlt
    · subst heq
      rw [candChain_fst_neg a h f [] b M c u₀ (j := M) le_rfl,
        List.take_of_length_le (le_of_eq hb)]
      exact hjun
  have hbound_f : ∀ n : ℕ, M ≤ n →
      ‖(((eqLam a : ℝ) : ℂ)) ^ n * u₀‖ < min (min δ₁ δ₂) (min ρg ρu) := by
    intro n hn
    have h1 : ‖(((eqLam a : ℝ) : ℂ)) ^ n * u₀‖ ≤ (eqLam a) ^ n * ‖u₀‖ := by
      rw [norm_mul, norm_pow, Complex.norm_of_nonneg (le_of_lt hlam)]
    have h2 : (eqLam a) ^ n ≤ (eqLam a) ^ M := pow_le_pow_of_le_one (le_of_lt hlam) hlam1 hn
    have h3 : (eqLam a) ^ n * ‖u₀‖ ≤ (eqLam a) ^ M * ‖u₀‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg u₀)
    linarith [h1, h3, hsm1]
  have hbound_b : ∀ n : ℕ, M ≤ n →
      ‖(((eqLam a : ℝ) : ℂ)) ^ n * (c / u₀)‖ < min (min δ₁ δ₂) (min ρg ρu) := by
    intro n hn
    have h1 : ‖(((eqLam a : ℝ) : ℂ)) ^ n * (c / u₀)‖ ≤ (eqLam a) ^ n * ‖c / u₀‖ := by
      rw [norm_mul, norm_pow, Complex.norm_of_nonneg (le_of_lt hlam)]
    have h2 : (eqLam a) ^ n ≤ (eqLam a) ^ M := pow_le_pow_of_le_one (le_of_lt hlam) hlam1 hn
    have h3 : (eqLam a) ^ n * ‖c / u₀‖ ≤ (eqLam a) ^ M * ‖c / u₀‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    linarith [h1, h3, hsm2]
  have hnear_f : ∀ n : ℕ, M ≤ n → n ≤ max N₁ M₁ →
      ‖(g u).1 (n : ℤ) - ((-1 / 2 : ℂ), (0 : ℂ))‖ < 1 / 2 := by
    intro n hn hnK
    have h1 : ‖(g u).1 (n : ℤ) - (g u₀).1 (n : ℤ)‖ < min ε₀ (1 / 8 : ℝ) :=
      hcoord (n : ℤ) (by
        rw [abs_of_nonneg (Int.natCast_nonneg n)]
        exact_mod_cast (le_trans hnK hKK₀))
    have h2 : (g u₀).1 (n : ℤ) = (candChain a h f [] b M c u₀).1 (n : ℤ) := by rw [hgu₀]
    have h3 : ‖(candChain a h f [] b M c u₀).1 (n : ℤ) - ((-1 / 2 : ℂ), (0 : ℂ))‖ < 1 / 8 := by
      rw [hp_fwd_val n hn]
      exact hgclose _ (lt_of_lt_of_le (hbound_f n hn) hΔρg)
    rw [h2] at h1
    have h4 : ‖(g u).1 (n : ℤ) - ((-1 / 2 : ℂ), (0 : ℂ))‖
        ≤ ‖(g u).1 (n : ℤ) - (candChain a h f [] b M c u₀).1 (n : ℤ)‖
          + ‖(candChain a h f [] b M c u₀).1 (n : ℤ) - ((-1 / 2 : ℂ), (0 : ℂ))‖ := by
      have h5 : (g u).1 (n : ℤ) - ((-1 / 2 : ℂ), (0 : ℂ))
          = ((g u).1 (n : ℤ) - (candChain a h f [] b M c u₀).1 (n : ℤ))
            + ((candChain a h f [] b M c u₀).1 (n : ℤ) - ((-1 / 2 : ℂ), (0 : ℂ))) := by ring
      rw [h5]
      exact norm_add_le _ _
    have h5 : min ε₀ (1 / 8 : ℝ) ≤ 1 / 8 := min_le_right _ _
    linarith [h1, h3, h4, h5]
  have hnear_b : ∀ n : ℕ, M ≤ n → n ≤ max N₁ M₁ →
      ‖(g u).1 (-(n : ℤ)) - ((1 / 2 : ℂ), (0 : ℂ))‖ < 1 / 2 := by
    intro n hn hnK
    have h1 : ‖(g u).1 (-(n : ℤ)) - (g u₀).1 (-(n : ℤ))‖ < min ε₀ (1 / 8 : ℝ) :=
      hcoord (-(n : ℤ)) (by
        rw [abs_neg, abs_of_nonneg (Int.natCast_nonneg n)]
        exact_mod_cast (le_trans hnK hKK₀))
    have h2 : (g u₀).1 (-(n : ℤ)) = (candChain a h f [] b M c u₀).1 (-(n : ℤ)) := by rw [hgu₀]
    have h3 : ‖(candChain a h f [] b M c u₀).1 (-(n : ℤ)) - ((1 / 2 : ℂ), (0 : ℂ))‖ < 1 / 8 := by
      rw [hp_bwd_val n hn]
      exact huclose _ (lt_of_lt_of_le (hbound_b n hn) hΔρu)
    rw [h2] at h1
    have h4 : ‖(g u).1 (-(n : ℤ)) - ((1 / 2 : ℂ), (0 : ℂ))‖
        ≤ ‖(g u).1 (-(n : ℤ)) - (candChain a h f [] b M c u₀).1 (-(n : ℤ))‖
          + ‖(candChain a h f [] b M c u₀).1 (-(n : ℤ)) - ((1 / 2 : ℂ), (0 : ℂ))‖ := by
      have h5 : (g u).1 (-(n : ℤ)) - ((1 / 2 : ℂ), (0 : ℂ))
          = ((g u).1 (-(n : ℤ)) - (candChain a h f [] b M c u₀).1 (-(n : ℤ)))
            + ((candChain a h f [] b M c u₀).1 (-(n : ℤ)) - ((1 / 2 : ℂ), (0 : ℂ))) := by ring
      rw [h5]
      exact norm_add_le _ _
    have h5 : min ε₀ (1 / 8 : ℝ) ≤ 1 / 8 := min_le_right _ _
    linarith [h1, h3, h4, h5]
  have step_f : ∀ m : ℕ, M ≤ m → m < max N₁ M₁ →
      (g u).1 ((((m + 1 : ℕ)) : ℤ)) = germC a h (((eqLam a : ℝ) : ℂ) ^ (m + 1) * u) →
      (g u).1 ((m : ℕ) : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ m * u) := by
    intro m hmM hmK hidx
    have hidx' : (g u).1 ((m : ℤ) + 1) = germC a h (((eqLam a : ℝ) : ℂ) ^ (m + 1) * u) := by
      simpa only [Nat.cast_succ] using hidx
    have hsmall : ‖(((eqLam a : ℝ) : ℂ)) ^ (m + 1) * u‖ < δ₁ := by
      have h1 : ‖(((eqLam a : ℝ) : ℂ)) ^ (m + 1) * u‖ ≤ (eqLam a) ^ (m + 1) * ‖u‖ := by
        rw [norm_mul, norm_pow, Complex.norm_of_nonneg (le_of_lt hlam)]
      have h2 : (eqLam a) ^ (m + 1) ≤ (eqLam a) ^ M :=
        pow_le_pow_of_le_one (le_of_lt hlam) hlam1 (by omega)
      have h3 : (eqLam a) ^ (m + 1) * ‖u‖ ≤ (eqLam a) ^ M * ‖u‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg u)
      linarith [h1, h3, hsmallFu, hΔδ₁]
    exact hstep1 hqchain hidx' hsmall (hnear_f m hmM (le_of_lt hmK))
  have step_b : ∀ m : ℕ, M ≤ m → m < max N₁ M₁ →
      (g u).1 (-(((m + 1 : ℕ)) : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ (m + 1) * (c / u)) →
      (g u).1 (-((m : ℕ) : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * (c / u)) := by
    intro m hmM hmK hidx
    have hidx' : (g u).1 (-((m : ℤ) + 1)) =
        ugermC a h (((eqLam a : ℝ) : ℂ) ^ (m + 1) * (c / u)) := by
      simpa only [Nat.cast_succ] using hidx
    have hsmall : ‖(((eqLam a : ℝ) : ℂ)) ^ (m + 1) * (c / u)‖ < δ₂ := by
      have h1 : ‖(((eqLam a : ℝ) : ℂ)) ^ (m + 1) * (c / u)‖ ≤ (eqLam a) ^ (m + 1) * ‖c / u‖ := by
        rw [norm_mul, norm_pow, Complex.norm_of_nonneg (le_of_lt hlam)]
      have h2 : (eqLam a) ^ (m + 1) ≤ (eqLam a) ^ M :=
        pow_le_pow_of_le_one (le_of_lt hlam) hlam1 (by omega)
      have h3 : (eqLam a) ^ (m + 1) * ‖c / u‖ ≤ (eqLam a) ^ M * ‖c / u‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      have h4 : (eqLam a) ^ M * ‖c / u‖ = (eqLam a) ^ M * ‖(g u).2.2‖ := by rw [hpsi2val]
      linarith [h1, h3, h4.le, h4.ge, hsmallBu, hΔδ₂]
    exact hstep2 hqchain hidx' hsmall (hnear_b m hmM (le_of_lt hmK))
  have key : ∀ j n : ℕ, max N₁ M₁ = n + j → M ≤ n →
      ((g u).1 ((n : ℕ) : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * u) ∧
       (g u).1 (-((n : ℕ) : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (c / u))) := by
    intro j
    induction j with
    | zero =>
      intro n hn hMn
      have hnK : n = max N₁ M₁ := by omega
      subst hnK
      refine ⟨?_, ?_⟩
      · have h1 : (g u).1 ((max N₁ M₁ : ℕ) : ℤ)
            = germC a h (((eqLam a : ℝ) : ℂ) ^ (max N₁ M₁) * (g u).2.1) :=
          hseed_f (max N₁ M₁) hKN
        rwa [hquψ1] at h1
      · have h1 : (g u).1 (-((max N₁ M₁ : ℕ) : ℤ))
            = ugermC a h (((eqLam a : ℝ) : ℂ) ^ (max N₁ M₁) * (g u).2.2) :=
          hseed_b (max N₁ M₁) hKM
        rwa [hpsi2val] at h1
    | succ j ih =>
      intro n hn hMn
      have hnK : n < max N₁ M₁ := by omega
      have hnext : ((g u).1 ((((n + 1 : ℕ)) : ℤ)) = germC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1) * u) ∧
          (g u).1 (-(((n + 1 : ℕ)) : ℤ)) =
            ugermC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1) * (c / u))) :=
        ih (n + 1) (by omega) (by omega)
      exact ⟨step_f n hMn hnK hnext.1, step_b n hMn hnK hnext.2⟩
  constructor
  · intro n hn
    by_cases hnK : n ≤ max N₁ M₁
    · exact (key (max N₁ M₁ - n) n (by omega) hn).1
    · push_neg at hnK
      have h1 : (g u).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (g u).2.1) :=
        hseed_f n (le_trans hKN (le_of_lt hnK))
      rwa [hquψ1] at h1
  · intro n hn
    by_cases hnK : n ≤ max N₁ M₁
    · exact (key (max N₁ M₁ - n) n (by omega) hn).2
    · push_neg at hnK
      have h1 : (g u).1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (g u).2.2) :=
        hseed_b n (le_trans hKM (le_of_lt hnK))
      rwa [hpsi2val] at h1

end

end Work.EQ.Ladf
