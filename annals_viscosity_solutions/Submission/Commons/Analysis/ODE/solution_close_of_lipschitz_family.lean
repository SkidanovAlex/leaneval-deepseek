import Mathlib
import Submission.Commons.Analysis.ODE.dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le
import Submission.Commons.Analysis.ODE.limit_at_right_of_lipschitzOnWith_of_lt
import Submission.Commons.Analysis.ODE.exists_solution_Icc_of_lipschitz_ball_strict
import Submission.Commons.Analysis.ODE.dist_f_add_le_of_lipschitzOn_balls

open Set Metric Filter
open scoped Topology NNReal

namespace Commons.Analysis.ODE

/-- **Continuity at interior points of a ball on which a map is Lipschitz.** -/
private theorem continuousAt_of_dist_le_mul {E : Type*} [PseudoMetricSpace E]
    {g : E → E} {c : E} {r K : ℝ}
    (h : ∀ x y : E, dist x c ≤ r → dist y c ≤ r → dist (g x) (g y) ≤ K * dist x y)
    {p : E} (hp : dist p c < r) : ContinuousAt g p := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hρ : 0 < r - dist p c := by linarith
  refine ⟨min ((r - dist p c) / 2) (ε / (|K| + 1)), lt_min (by linarith) (by positivity), ?_⟩
  intro y hy
  have hyc : dist y c < r := by
    have h1 : dist y p < (r - dist p c) / 2 := lt_of_lt_of_le hy (min_le_left _ _)
    calc dist y c ≤ dist y p + dist p c := dist_triangle _ _ _
      _ < (r - dist p c) / 2 + dist p c := by linarith
      _ < r := by linarith
  have h2 : dist (g y) (g p) ≤ K * dist y p := h y p (le_of_lt hyc) (le_of_lt hp)
  have h3 : K * dist y p ≤ |K| * dist y p :=
    mul_le_mul_of_nonneg_right (le_abs_self K) dist_nonneg
  have h4 : |K| * dist y p < ε := by
    have h5 : dist y p < ε / (|K| + 1) := lt_of_lt_of_le hy (min_le_right _ _)
    have h6 : (0:ℝ) < |K| + 1 := by positivity
    have h7 : |K| / (|K| + 1) < 1 := by rw [div_lt_one h6]; linarith
    calc |K| * dist y p ≤ |K| * (ε / (|K| + 1)) :=
          mul_le_mul_of_nonneg_left (le_of_lt h5) (abs_nonneg K)
      _ = ε * (|K| / (|K| + 1)) := by ring
      _ < ε * 1 := mul_lt_mul_of_pos_left h7 hε
      _ = ε := by ring
  linarith

/-- Two solutions of `w' = H t w` which both stay in the closed ball of radius `r` about `0` and
which agree at the left endpoint coincide on the common interval. -/
private theorem eqOn_of_hasDerivAt_of_lipschitz_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : ℝ → E → E} {r K : ℝ} (hK : 0 ≤ K)
    (hH_lip : ∀ t, ∀ w w' : E, ‖w‖ ≤ r → ‖w'‖ ≤ r → ‖H t w - H t w'‖ ≤ K * ‖w - w'‖)
    {a c₁ c₂ : ℝ} {w₁ w₂ : ℝ → E}
    (h₁ : ∀ t ∈ Set.Icc a c₁, HasDerivAt w₁ (H t (w₁ t)) t)
    (h₂ : ∀ t ∈ Set.Icc a c₂, HasDerivAt w₂ (H t (w₂ t)) t)
    (hb₁ : ∀ t ∈ Set.Icc a c₁, ‖w₁ t‖ ≤ r) (hb₂ : ∀ t ∈ Set.Icc a c₂, ‖w₂ t‖ ≤ r)
    (h0 : w₁ a = w₂ a) :
    Set.EqOn w₁ w₂ (Set.Icc a (min c₁ c₂)) := by
  intro t ht
  have ht1 : t ≤ c₁ := le_trans ht.2 (min_le_left c₁ c₂)
  have ht2 : t ≤ c₂ := le_trans ht.2 (min_le_right c₁ c₂)
  have hmain := dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le (x := w₁) (y := w₂)
    (x' := fun s => H s (w₁ s)) (y' := fun s => H s (w₂ s)) (L := K) (a := a) (b := t)
    ht.1 hK
    (fun s hs => h₁ s ⟨hs.1, le_trans hs.2 ht1⟩)
    (fun s hs => h₂ s ⟨hs.1, le_trans hs.2 ht2⟩)
    (fun s hs => hH_lip s (w₁ s) (w₂ s) (hb₁ s ⟨hs.1, le_trans hs.2 ht1⟩)
        (hb₂ s ⟨hs.1, le_trans hs.2 ht2⟩))
  rw [h0, dist_self, zero_mul] at hmain
  exact dist_eq_zero.mp (le_antisymm hmain dist_nonneg)

/-- **Existence on a half-open interval in a tube (Grönwall envelope).** -/
private theorem exists_solution_Ico_of_lipschitz_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : ℝ → E → E} {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hH0 : ∀ t, H t 0 = 0)
    (hH_lip : ∀ t, ∀ w w' : E, ‖w‖ ≤ r → ‖w'‖ ≤ r → ‖H t w - H t w'‖ ≤ K * ‖w - w'‖)
    (hH_cont : ∀ t, ∀ w : E, ‖w‖ < r → ContinuousAt (Function.uncurry H) (t, w))
    {a b c₀ : ℝ} (hab : a < b) (hc₀ : 0 ≤ c₀)
    (henv : ∀ t ∈ Set.Ico a b, c₀ * Real.exp (K * (t - a)) < r)
    {w₀ : E} (hw₀ : ‖w₀‖ ≤ c₀) :
    ∃ w : ℝ → E, w a = w₀ ∧ (∀ t ∈ Set.Ioo a b, HasDerivAt w (H t (w t)) t) ∧
      (∀ t ∈ Set.Ico a b, ‖w t‖ ≤ c₀ * Real.exp (K * (t - a))) ∧
      Tendsto w (𝓝[>] a) (𝓝 w₀) ∧
      ∃ L : E, Tendsto w (𝓝[<] b) (𝓝 L) ∧ ‖L‖ ≤ c₀ * Real.exp (K * (b - a)) := by
  set F : ℝ → ℝ := fun t => c₀ * Real.exp (K * (t - a)) with hFdef
  have hFmono : Monotone F := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right hst a) hK)) hc₀
  have hstep : ∀ c : ℝ, ∃ w : ℝ → E, a < c → c < b →
      (w a = w₀ ∧ (∀ t ∈ Set.Icc a c, HasDerivAt w (H t (w t)) t) ∧
        (∀ t ∈ Set.Icc a c, ‖w t‖ ≤ F t)) := by
    intro c
    by_cases h : a < c ∧ c < b
    · obtain ⟨w, hw⟩ :=
        exists_solution_Icc_of_lipschitz_ball_strict hr hK hH0 hH_lip hH_cont h.1 hc₀
          (fun t ht => henv t ⟨ht.1, lt_of_le_of_lt ht.2 h.2⟩) hw₀
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨fun _ => w₀, fun hac hcb => absurd ⟨hac, hcb⟩ h⟩
  choose W hW using hstep
  have hmidmem : ∀ t ∈ Set.Ico a b, a < (t + b) / 2 ∧ (t + b) / 2 < b := by
    intro t ht
    exact ⟨by linarith [ht.1, hab], by linarith [ht.2]⟩
  set wh : ℝ → E := fun t => W ((t + b) / 2) t with hwhdef
  have hagree : ∀ t ∈ Set.Ico a b, Set.EqOn wh (W ((t + b) / 2)) (Set.Icc a ((t + b) / 2)) := by
    intro t ht
    obtain ⟨hac, hcb⟩ := hmidmem t ht
    have h2 := hW ((t + b) / 2) hac hcb
    intro s hs
    have hsub : s ∈ Set.Ico a b := ⟨hs.1, lt_of_le_of_lt hs.2 hcb⟩
    obtain ⟨hsac, hscb⟩ := hmidmem s hsub
    have h1 := hW ((s + b) / 2) hsac hscb
    have hsmem : s ∈ Set.Icc a (min ((s + b) / 2) ((t + b) / 2)) :=
      ⟨hs.1, le_min (by linarith [hsub.2]) hs.2⟩
    have heq := eqOn_of_hasDerivAt_of_lipschitz_ball hK hH_lip h1.2.1 h2.2.1
      (fun u hu => le_of_lt (lt_of_le_of_lt (le_trans (h1.2.2 u hu) (hFmono hu.2))
        (henv ((s + b) / 2) ⟨hsac.le, hscb⟩)))
      (fun u hu => le_of_lt (lt_of_le_of_lt (le_trans (h2.2.2 u hu) (hFmono hu.2))
        (henv ((t + b) / 2) ⟨hac.le, hcb⟩)))
      (by rw [h1.1, h2.1])
    exact heq hsmem
  have hwh_mid : ∀ t ∈ Set.Ico a ((a + b) / 2), wh t = W ((a + b) / 2) t := by
    intro t ht
    have htb : t ∈ Set.Ico a b := ⟨ht.1, by linarith [ht.2, hab]⟩
    obtain ⟨hac, hcb⟩ := hmidmem t htb
    have hab2 : a < (a + b) / 2 := by linarith
    have hab2' : (a + b) / 2 < b := by linarith
    have h1 := hW ((t + b) / 2) hac hcb
    have h2 := hW ((a + b) / 2) hab2 hab2'
    have htmem : t ∈ Set.Icc a (min ((t + b) / 2) ((a + b) / 2)) :=
      ⟨ht.1, le_min (by linarith [htb.2]) ht.2.le⟩
    have heq := eqOn_of_hasDerivAt_of_lipschitz_ball hK hH_lip h1.2.1 h2.2.1
      (fun u hu => le_of_lt (lt_of_le_of_lt (le_trans (h1.2.2 u hu) (hFmono hu.2))
        (henv ((t + b) / 2) ⟨hac.le, hcb⟩)))
      (fun u hu => le_of_lt (lt_of_le_of_lt (le_trans (h2.2.2 u hu) (hFmono hu.2))
        (henv ((a + b) / 2) ⟨hab2.le, hab2'⟩)))
      (by rw [h1.1, h2.1])
    exact heq htmem
  have hwa : wh a = w₀ := (hW ((a + b) / 2) (by linarith) (by linarith)).1
  have hwa_tend : Tendsto wh (𝓝[>] a) (𝓝 w₀) := by
    have hab2 : a < (a + b) / 2 := by linarith
    have hab2' : (a + b) / 2 < b := by linarith
    have hcont : ContinuousAt (W ((a + b) / 2)) a :=
      ((hW ((a + b) / 2) hab2 hab2').2.1 a ⟨le_rfl, hab2.le⟩).continuousAt
    have h1 : Tendsto (W ((a + b) / 2)) (𝓝[>] a) (𝓝 (W ((a + b) / 2) a)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    rw [(hW ((a + b) / 2) hab2 hab2').1] at h1
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by linarith : a < (a + b) / 2)] with t ht
    exact (hwh_mid t ⟨ht.1.le, ht.2⟩).symm
  have hwderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt wh (H t (wh t)) t := by
    intro t ht
    obtain ⟨hac, hcb⟩ := hmidmem t ⟨ht.1.le, ht.2⟩
    have htlt : t < (t + b) / 2 := by linarith
    have hmem : Set.Ioo a ((t + b) / 2) ∈ 𝓝 t := Ioo_mem_nhds ht.1 htlt
    have hev : wh =ᶠ[𝓝 t] W ((t + b) / 2) := by
      filter_upwards [hmem] with s hs
      exact hagree t ⟨ht.1.le, ht.2⟩ ⟨hs.1.le, le_of_lt hs.2⟩
    have hd := ((hW ((t + b) / 2) hac hcb).2.1 t ⟨ht.1.le, htlt.le⟩).congr_of_eventuallyEq hev
    have heqt : wh t = W ((t + b) / 2) t := hev.eq_of_nhds
    rwa [← heqt] at hd
  have hwhbound : ∀ t ∈ Set.Ico a b, ‖wh t‖ ≤ F t := by
    intro t ht
    obtain ⟨hac, hcb⟩ := hmidmem t ht
    have heqt : wh t = W ((t + b) / 2) t := (hagree t ht) ⟨ht.1, by linarith⟩
    rw [heqt]
    exact (hW ((t + b) / 2) hac hcb).2.2 t ⟨ht.1, by linarith⟩
  have hdiff : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ wh t := fun t ht =>
    (hwderiv t ht).differentiableAt
  have hderivbound : ∀ t ∈ Set.Ioo a b, ‖deriv wh t‖ ≤ K * r := by
    intro t ht
    have hd := hwderiv t ht
    rw [hd.deriv]
    have hwtr : ‖wh t‖ ≤ r :=
      le_of_lt (lt_of_le_of_lt (hwhbound t ⟨ht.1.le, ht.2⟩) (henv t ⟨ht.1.le, ht.2⟩))
    have hHbound : ‖H t (wh t)‖ ≤ K * ‖wh t‖ := by
      have h := hH_lip t (wh t) 0 hwtr (by simpa using hr.le)
      simpa [hH0] using h
    calc ‖H t (wh t)‖ ≤ K * ‖wh t‖ := hHbound
      _ ≤ K * r := by gcongr
  have hLip : LipschitzOnWith ⟨K * r, mul_nonneg hK hr.le⟩ wh (Set.Ioo a b) := by
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le hdiff ?_ (convex_Ioo a b)
    intro t ht
    exact hderivbound t ht
  obtain ⟨L, hL⟩ := limit_at_right_of_lipschitzOnWith_of_lt hab hLip
  refine ⟨wh, hwa, hwderiv, hwhbound, hwa_tend, L, hL, ?_⟩
  have hlimnorm : Tendsto (fun t => ‖wh t‖) (𝓝[<] b) (𝓝 ‖L‖) := hL.norm
  refine le_of_tendsto hlimnorm ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  have h1 := hwhbound t ⟨ht.1.le, ht.2⟩
  have h2 : F t ≤ F b := hFmono ht.2.le
  exact le_trans h1 h2

/-- **Continuous dependence on initial data (Grönwall form, ball family).**

Let `u` be a solution of `u' = f u` on `Icc a b`, and suppose `f` is `K`-Lipschitz on the ball of
radius `r` around `u t`, uniformly in `t ∈ Icc a b`.  Then every initial datum `z` with
`dist z (u a) * exp (K * (b - a)) ≤ r` gives rise to a solution `v` of `v' = f v` on all of
`Icc a b` with `v a = z`, and `dist (v t) (u t) ≤ dist z (u a) * exp (K * (t - a))` for all
`t ∈ Icc a b`. -/
theorem solution_close_of_lipschitz_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {u : ℝ → E} {a b : ℝ} (hab : a ≤ b) {r : ℝ} (hr : 0 < r) {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ t ∈ Set.Icc a b, ∀ x y : E, dist x (u t) ≤ r → dist y (u t) ≤ r →
      dist (f x) (f y) ≤ K * dist x y)
    (hu : ∀ t ∈ Set.Icc a b, HasDerivAt u (f (u t)) t) :
    ∀ z : E, dist z (u a) * Real.exp (K * (b - a)) ≤ r →
      ∃ v : ℝ → E, v a = z ∧ (∀ t ∈ Set.Icc a b, HasDerivAt v (f (v t)) t) ∧
        (∀ t ∈ Set.Icc a b, dist (v t) (u t) ≤ dist z (u a) * Real.exp (K * (t - a))) := by
  intro z hz
  by_cases hK0 : K = 0
  · -- Case `K = 0`: the translate of `u` by `z - u a` is a solution.
    have hc₀r : dist z (u a) ≤ r := by
      have h : dist z (u a) * 1 ≤ r := by simpa [hK0] using hz
      simpa using h
    refine ⟨fun t => u t + (z - u a), ?_, ?_, ?_⟩
    · simp
    · intro t ht
      have heq : f (u t + (z - u a)) = f (u t) := by
        have hd : dist (u t + (z - u a)) (u t) = dist z (u a) := by
          rw [dist_eq_norm, dist_eq_norm]
          congr 1
          abel
        have h := hLip t ht (u t + (z - u a)) (u t) (by rw [hd]; exact hc₀r)
          (by simpa using hr.le)
        have h0 : dist (f (u t + (z - u a))) (f (u t)) ≤ 0 := by simpa [hK0] using h
        exact dist_eq_zero.mp (le_antisymm h0 dist_nonneg)
      rw [heq]
      exact (hu t ht).add_const (z - u a)
    · intro t ht
      have hd : ‖u t + (z - u a) - u t‖ = ‖z - u a‖ := by
        congr 1
        abel
      rw [dist_eq_norm, hd, dist_eq_norm]
      refine le_of_eq ?_
      rw [hK0, zero_mul, Real.exp_zero, mul_one]
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    by_cases hab_eq : a = b
    · -- Case `a = b`: only the derivative at `a` matters.
      have hab_le : b ≤ a := le_of_eq hab_eq.symm
      refine ⟨fun s => z + (s - a) • f z, ?_, ?_, ?_⟩
      · simp
      · intro t ht
        have ht' : t = a := le_antisymm (le_trans ht.2 hab_le) ht.1
        rw [ht']
        simp only [sub_self, zero_smul, add_zero]
        have h2 : HasDerivAt (fun s : ℝ => s - a) (1 : ℝ) a := (hasDerivAt_id a).sub_const a
        have h3 : HasDerivAt (fun s : ℝ => (s - a) • f z) ((1 : ℝ) • f z) a := h2.smul_const (f z)
        simpa using h3.const_add z
      · intro t ht
        have ht' : t = a := le_antisymm (le_trans ht.2 hab_le) ht.1
        rw [ht']
        simp only [sub_self, zero_smul, add_zero]
        refine le_of_eq ?_
        rw [mul_zero, Real.exp_zero, mul_one]
    · -- Main case: `K > 0` and `a < b`.
      have hab' : a < b := lt_of_le_of_ne hab hab_eq
      -- (1) a Lipschitz constant for `u` on `[a,b]`
      have hu_contOn : ContinuousOn (fun t : ℝ => f (u t)) (Set.Icc a b) := by
        intro t ht
        exact ((continuousAt_of_dist_le_mul (h := hLip t ht) (p := u t) (by simpa using hr)).comp
          (hu t ht).continuousAt).continuousWithinAt
      obtain ⟨t₀, ht₀mem, ht₀max⟩ :=
        isCompact_Icc.exists_isMaxOn (f := fun t : ℝ => ‖f (u t)‖) ⟨a, le_rfl, hab⟩ hu_contOn.norm
      set B : ℝ := ‖f (u t₀)‖ with hBdef
      have hBnn : 0 ≤ B := norm_nonneg _
      have hBbound : ∀ t ∈ Set.Icc a b, ‖f (u t)‖ ≤ B := fun t ht => ht₀max ht
      -- (2) the clamped trajectory and the relative field
      set c : ℝ → E := fun t => u (max a (min b t)) with hcdef
      have hc_mem : ∀ t : ℝ, max a (min b t) ∈ Set.Icc a b := fun t =>
        ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
      have hc_eq : ∀ t ∈ Set.Icc a b, c t = u t := by
        intro t ht
        simp only [hcdef]
        rw [min_eq_right ht.2, max_eq_right ht.1]
      have hc_cont : Continuous c := by
        rw [continuous_iff_continuousAt]
        intro t
        rw [hcdef]
        show Tendsto (fun s : ℝ => u (max a (min b s))) (𝓝 t) (𝓝 (u (max a (min b t))))
        exact ((hu _ (hc_mem t)).continuousAt.tendsto).comp
          (ContinuousAt.tendsto (by fun_prop : ContinuousAt (fun s : ℝ => max a (min b s)) t))
      have hc_lip : ∀ t : ℝ, ∀ x y : E, dist x (c t) ≤ r → dist y (c t) ≤ r →
          dist (f x) (f y) ≤ K * dist x y := fun t x y hx hy =>
        hLip (max a (min b t)) (hc_mem t) x y hx hy
      have hc_deriv : ∀ t ∈ Set.Ioo a b, HasDerivAt c (f (c t)) t := by
        intro t ht
        have hev : c =ᶠ[𝓝 t] u := by
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
          exact hc_eq s ⟨hs.1.le, hs.2.le⟩
        have h1 : HasDerivAt u (f (u t)) t := hu t ⟨ht.1.le, ht.2.le⟩
        have h2 : HasDerivAt c (f (u t)) t := h1.congr_of_eventuallyEq hev
        rw [← hc_eq t ⟨ht.1.le, ht.2.le⟩] at h2
        exact h2
      -- (3) the solution in the relative variable
      set c₀ : ℝ := dist z (u a) with hc₀def
      have hc₀nn : 0 ≤ c₀ := dist_nonneg
      set F : ℝ → ℝ := fun t => c₀ * Real.exp (K * (t - a)) with hFdef
      have henv : ∀ t ∈ Set.Ico a b, F t < r := by
        intro t ht
        rcases eq_or_lt_of_le hc₀nn with h0 | hpos
        · have h1 : F t = 0 := by simp [hFdef, ← h0]
          rw [h1]
          exact hr
        · have hexp : Real.exp (K * (t - a)) < Real.exp (K * (b - a)) :=
            Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left (by linarith [ht.2]) hKpos)
          calc F t = c₀ * Real.exp (K * (t - a)) := rfl
            _ < c₀ * Real.exp (K * (b - a)) := mul_lt_mul_of_pos_left hexp hpos
            _ ≤ r := hz
      have hw₀ : ‖z - u a‖ ≤ c₀ := by rw [hc₀def, dist_eq_norm]
      obtain ⟨w, hwa, hwderiv, hwbound, hwa_tend₀, L, hLlim, hLb⟩ :=
        exists_solution_Ico_of_lipschitz_ball (H := fun t w => f (c t + w) - f (c t)) hr hK
          (by intro t; rw [add_zero, sub_self])
          (fun t w w' hw hw' => by
            have h1 : f (c t + w) - f (c t) - (f (c t + w') - f (c t))
                = f (c t + w) - f (c t + w') := by abel
            have h := hc_lip t (c t + w) (c t + w')
              (by rw [dist_eq_norm, show c t + w - c t = w from by abel]; exact hw)
              (by rw [dist_eq_norm, show c t + w' - c t = w' from by abel]; exact hw')
            rw [h1]
            calc ‖f (c t + w) - f (c t + w')‖ = dist (f (c t + w)) (f (c t + w')) := by
                  rw [dist_eq_norm]
              _ ≤ K * dist (c t + w) (c t + w') := h
              _ = K * ‖w - w'‖ := by
                  rw [dist_eq_norm]
                  congr 1
                  abel)
          (fun t w hw => by
            have hfirst : ContinuousAt (fun p : ℝ × E => f (c p.1 + p.2)) (t, w) := by
              have h1 : Tendsto (fun p : ℝ × E => c p.1 + p.2) (𝓝 (t, w)) (𝓝 (c t + w)) :=
                ((hc_cont.continuousAt.tendsto.comp continuous_fst.continuousAt.tendsto).add
                  (continuous_snd.continuousAt.tendsto))
              exact (continuousAt_of_dist_le_mul (h := hc_lip t) (p := c t + w)
                (by rw [dist_eq_norm, show c t + w - c t = w from by abel]; exact hw)).tendsto.comp h1
            have hsecond : ContinuousAt (fun p : ℝ × E => f (c p.1)) (t, w) := by
              have h1 : Tendsto (fun p : ℝ × E => c p.1) (𝓝 (t, w)) (𝓝 (c t)) :=
                hc_cont.continuousAt.tendsto.comp continuous_fst.continuousAt.tendsto
              exact (continuousAt_of_dist_le_mul (h := hc_lip t) (p := c t)
                (by rw [dist_eq_norm, sub_self, norm_zero]; exact hr)).tendsto.comp h1
            show ContinuousAt (fun p : ℝ × E => f (c p.1 + p.2) - f (c p.1)) (t, w)
            exact hfirst.sub hsecond)
          hab' hc₀nn henv hw₀
      have hwa_tend : Tendsto w (𝓝[>] a) (𝓝 (w a)) := by
        rw [hwa]
        exact hwa_tend₀
      -- (4) the assembled curve
      set vb : E := u b + L with hvbdef
      have hdv : dist vb (u b) = ‖L‖ := by
        rw [hvbdef, dist_eq_norm]
        congr 1
        abel
      let v : ℝ → E := fun t =>
        if t < a then z + (t - a) • f z else if t < b then c t + w t else vb + (t - b) • f vb
      have hv_a : v a = z := by
        have h1 : ¬ (a < a) := lt_irrefl a
        have h2 : a < b := hab'
        simp only [v, if_neg h1, if_pos h2, hc_eq a ⟨le_rfl, hab⟩, hwa]
        abel
      have hv_int : ∀ t ∈ Set.Ioo a b, v t = c t + w t := by
        intro t ht
        simp only [v, if_neg (not_lt.mpr ht.1.le), if_pos ht.2]
      have hv_b : v b = vb := by
        simp only [v, if_neg (not_lt.mpr hab), if_neg (lt_irrefl b), sub_self, zero_smul, add_zero]
      have hcaw : c a + w a = z := by rw [hc_eq a ⟨le_rfl, hab⟩, hwa]; abel
      have hval_b : c b + L = vb := by rw [hc_eq b ⟨hab, le_rfl⟩, hvbdef]
      have hvlim : Tendsto v (𝓝[<] b) (𝓝 vb) := by
        have h1 : Tendsto (fun t : ℝ => c t + w t) (𝓝[<] b) (𝓝 (c b + L)) :=
          (hc_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add hLlim
        rw [hval_b] at h1
        refine h1.congr' ?_
        filter_upwards [Ioo_mem_nhdsLT hab'] with t ht
        exact (hv_int t ht).symm
      have hvlim_a : Tendsto v (𝓝[>] a) (𝓝 (v a)) := by
        have h1 : Tendsto (fun t : ℝ => c t + w t) (𝓝[>] a) (𝓝 (c a + w a)) :=
          (hc_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add hwa_tend
        rw [hcaw] at h1
        have h2 : Tendsto (fun t : ℝ => c t + w t) (𝓝[>] a) (𝓝 (v a)) := by
          rw [hv_a]
          exact h1
        refine h2.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hab'] with t ht
        exact (hv_int t ht).symm
      have hv_deriv_int : ∀ t ∈ Set.Ioo a b, HasDerivAt v (f (v t)) t := by
        intro t ht
        have hev : v =ᶠ[𝓝 t] (fun s => c s + w s) := by
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
          exact hv_int s hs
        have hd : HasDerivAt (fun s => c s + w s)
            (f (c t) + (f (c t + w t) - f (c t))) t :=
          (hc_deriv t ht).add (hwderiv t ht)
        have hd2 : HasDerivAt v (f (c t) + (f (c t + w t) - f (c t))) t :=
          hd.congr_of_eventuallyEq hev
        have hval : f (c t) + (f (c t + w t) - f (c t)) = f (v t) := by
          rw [hv_int t ht]
          abel
        rwa [hval] at hd2
      -- (5) the estimate
      have hvest : ∀ t ∈ Set.Icc a b, dist (v t) (u t) ≤ F t := by
        intro t ht
        rcases eq_or_lt_of_le ht.1 with heq | hlt
        · rw [← heq, hv_a]
          simp [hFdef, hc₀def, sub_self]
        · rcases lt_or_eq_of_le ht.2 with hlt2 | heq2
          · rw [hv_int t ⟨hlt, hlt2⟩]
            have h1 : c t + w t - u t = w t := by rw [hc_eq t ht]; abel
            rw [dist_eq_norm, h1]
            exact hwbound t ⟨ht.1, hlt2⟩
          · rw [heq2, hv_b, hvbdef]
            have h1 : dist (u b + L) (u b) = ‖L‖ := by
              rw [dist_eq_norm]
              congr 1
              abel
            rw [h1]
            exact hLb
      -- (6) the trend of `f ∘ v` at `b`
      have hclamp : ∀ s t : ℝ, |max a (min b s) - max a (min b t)| ≤ |s - t| := by
        intro s t
        calc |max a (min b s) - max a (min b t)|
            ≤ max |a - a| |min b s - min b t| := abs_max_sub_max_le_max _ _ _ _
          _ = |min b s - min b t| := by simp
          _ ≤ |s - t| := by
              have h := ((LipschitzWith.const b).min LipschitzWith.id).dist_le_mul s t
              simpa [Real.dist_eq, one_mul] using h
      have hu_lip_Icc : ∀ p ∈ Set.Icc a b, ∀ q ∈ Set.Icc a b, dist (u p) (u q) ≤ B * |p - q| := by
        intro p hp q hq
        have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := u) (s := Set.Icc a b)
          (x := p) (y := q) (C := B) (fun s hs => (hu s hs).differentiableAt)
          (fun s hs => by rw [(hu s hs).deriv]; exact hBbound s hs) (convex_Icc a b) hp hq
        rw [Real.norm_eq_abs] at h
        calc dist (u p) (u q) = ‖u p - u q‖ := by rw [dist_eq_norm]
          _ = ‖u q - u p‖ := by rw [norm_sub_rev]
          _ ≤ B * ‖q - p‖ := h
          _ = B * |p - q| := by rw [Real.norm_eq_abs, abs_sub_comm]
      have hc_lipschitz : ∀ s t : ℝ, dist (c s) (c t) ≤ B * |s - t| := by
        intro s t
        simp only [hcdef]
        calc dist (u (max a (min b s))) (u (max a (min b t)))
            ≤ B * |max a (min b s) - max a (min b t)| := hu_lip_Icc _ (hc_mem s) _ (hc_mem t)
          _ ≤ B * |s - t| := mul_le_mul_of_nonneg_left (hclamp s t) hBnn
      have htrend : Tendsto (fun x => f (v x)) (𝓝[<] b) (𝓝 (f vb)) := by
        have hbound : ∀ᶠ x in 𝓝[<] b,
            dist (f (v x)) (f vb) ≤ K * (B * (b - x) + dist (w x) L) := by
          filter_upwards [Ioo_mem_nhdsLT hab'] with x hx
          have hx1 : x ∈ Set.Ico a b := ⟨hx.1.le, hx.2⟩
          have hxr : ‖w x‖ < r := lt_of_le_of_lt (hwbound x hx1) (henv x hx1)
          have hxle : ‖w x‖ ≤ r := le_of_lt hxr
          have hvx : v x = c x + w x := hv_int x hx
          have hucx : c x = u x := hc_eq x ⟨hx.1.le, hx.2.le⟩
          have hchain : dist (f (u x + w x)) (f (u b + w x)) ≤ K * B * (b - x) := by
            have h := dist_f_add_le_of_lipschitzOn_balls hK hBnn hc_lipschitz
              (fun σ => hc_lip σ) hxr hx.2.le
            rw [hc_eq b ⟨hab, le_rfl⟩, hucx] at h
            exact h
          have hdirect : dist (f (u b + w x)) (f (u b + L)) ≤ K * dist (w x) L := by
            have h := hLip b ⟨hab, le_rfl⟩ (u b + w x) (u b + L)
              (by rw [dist_eq_norm, show u b + w x - u b = w x from by abel]; exact hxle)
              (by rw [dist_eq_norm, show u b + L - u b = L from by abel]; exact le_trans hLb hz)
            have h2 : dist (u b + w x) (u b + L) = dist (w x) L := by
              rw [dist_eq_norm, dist_eq_norm]
              congr 1
              abel
            rwa [h2] at h
          calc dist (f (v x)) (f vb)
              = dist (f (u x + w x)) (f (u b + L)) := by rw [hvx, hucx, hvbdef]
            _ ≤ dist (f (u x + w x)) (f (u b + w x))
                  + dist (f (u b + w x)) (f (u b + L)) := dist_triangle _ _ _
            _ ≤ K * B * (b - x) + K * dist (w x) L := add_le_add hchain hdirect
            _ = K * (B * (b - x) + dist (w x) L) := by ring
        refine tendsto_iff_dist_tendsto_zero.mpr ?_
        refine squeeze_zero' (g := fun x => K * (B * (b - x) + dist (w x) L))
          (Filter.Eventually.of_forall (fun x => dist_nonneg)) hbound ?_
        have hb1 : Tendsto (fun x : ℝ => b - x) (𝓝[<] b) (𝓝 0) := by
          have hid : Tendsto (fun x : ℝ => x) (𝓝[<] b) (𝓝 b) :=
            tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id
          simpa using (tendsto_const_nhds.sub hid :
            Tendsto (fun x : ℝ => b - x) (𝓝[<] b) (𝓝 (b - b)))
        have hb2 : Tendsto (fun x : ℝ => dist (w x) L) (𝓝[<] b) (𝓝 0) := by
          have h := hLlim.dist (tendsto_const_nhds : Tendsto (fun _ : ℝ => L) (𝓝[<] b) (𝓝 L))
          simpa using h
        have h4 : Tendsto (fun x : ℝ => B * (b - x) + dist (w x) L) (𝓝[<] b) (𝓝 0) := by
          simpa using ((hb1.const_mul B).add hb2)
        simpa using h4.const_mul K
      -- (7) the derivative of `v` at the endpoints
      have hbleft : HasDerivWithinAt v (f vb) (Set.Iic b) b := by
        have hlim_trend : Tendsto (fun x => deriv v x) (𝓝[<] b) (𝓝 (f vb)) := by
          refine htrend.congr' ?_
          filter_upwards [Ioo_mem_nhdsLT hab'] with x hx
          exact ((hv_deriv_int x hx).deriv).symm
        refine hasDerivWithinAt_Iic_of_tendsto_deriv ?_ ?_ (Ioo_mem_nhdsLT hab') hlim_trend
        · intro x hx
          exact (hv_deriv_int x hx).differentiableAt.differentiableWithinAt
        · have h1 : Tendsto v (𝓝[Set.Ioo a b] b) (𝓝 vb) :=
            hvlim.mono_left (nhdsWithin_mono b Ioo_subset_Iio_self)
          rw [ContinuousWithinAt, hv_b]
          exact h1
      have hbright : HasDerivWithinAt v (f vb) (Set.Ici b) b := by
        have hlin : HasDerivAt (fun t : ℝ => vb + (t - b) • f vb) (f vb) b := by
          have h1 : HasDerivAt (fun t : ℝ => t - b) (1 : ℝ) b := (hasDerivAt_id b).sub_const b
          have h2 : HasDerivAt (fun t : ℝ => (t - b) • f vb) ((1 : ℝ) • f vb) b :=
            h1.smul_const (f vb)
          simpa using h2.const_add vb
        refine (hlin.hasDerivWithinAt).congr ?_ ?_
        · intro t ht
          rcases lt_or_eq_of_le (show b ≤ t from ht) with hlt | heq
          · simp only [v, if_neg (not_lt.mpr (by linarith : a ≤ t)),
              if_neg (not_lt.mpr (le_of_lt hlt))]
          · subst heq
            rw [hv_b]
            simp
        · rw [hv_b]
          simp
      have hb_deriv : HasDerivAt v (f (v b)) b := by
        have h := hbleft.union hbright
        rw [Iic_union_Ici] at h
        have h2 : HasDerivAt v (f vb) b := h.hasDerivAt univ_mem
        rwa [← hv_b] at h2
      have ha_left : HasDerivWithinAt v (f z) (Set.Iic a) a := by
        have hlin : HasDerivAt (fun t : ℝ => z + (t - a) • f z) (f z) a := by
          have h1 : HasDerivAt (fun t : ℝ => t - a) (1 : ℝ) a := (hasDerivAt_id a).sub_const a
          have h2 : HasDerivAt (fun t : ℝ => (t - a) • f z) ((1 : ℝ) • f z) a :=
            h1.smul_const (f z)
          simpa using h2.const_add z
        refine (hlin.hasDerivWithinAt).congr ?_ ?_
        · intro t ht
          rcases lt_or_eq_of_le (show t ≤ a from ht) with hlt | heq
          · simp only [v, if_pos hlt]
          · subst heq
            rw [hv_a]
            simp
        · rw [hv_a]
          simp
      have hc₀lt : c₀ < r := by
        rcases eq_or_lt_of_le hc₀nn with h0 | hpos
        · rw [← h0]; exact hr
        · have hE : (1 : ℝ) < Real.exp (K * (b - a)) :=
            Real.one_lt_exp_iff.mpr (mul_pos hKpos (by linarith))
          calc c₀ = c₀ * 1 := (mul_one _).symm
            _ < c₀ * Real.exp (K * (b - a)) := mul_lt_mul_of_pos_left hE hpos
            _ ≤ r := hz
      have hfz : ContinuousAt f z :=
        continuousAt_of_dist_le_mul (h := hLip a ⟨le_rfl, hab⟩) (p := z)
          (by rw [← hc₀def]; exact hc₀lt)
      have ha_right : HasDerivWithinAt v (f z) (Set.Ici a) a := by
        have hlim_trend : Tendsto (fun x => deriv v x) (𝓝[>] a) (𝓝 (f z)) := by
          have hvz : Tendsto v (𝓝[>] a) (𝓝 z) := by simpa [hv_a] using hvlim_a
          have hfv : Tendsto (fun x => f (v x)) (𝓝[>] a) (𝓝 (f z)) := hfz.tendsto.comp hvz
          refine hfv.congr' ?_
          filter_upwards [Ioo_mem_nhdsGT hab'] with x hx
          exact ((hv_deriv_int x hx).deriv).symm
        refine hasDerivWithinAt_Ici_of_tendsto_deriv ?_ ?_ (Ioo_mem_nhdsGT hab') hlim_trend
        · intro x hx
          exact (hv_deriv_int x hx).differentiableAt.differentiableWithinAt
        · have h1 : Tendsto (fun t : ℝ => c t + w t) (𝓝[>] a) (𝓝 (c a + w a)) :=
            (hc_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add hwa_tend
          rw [hcaw] at h1
          have h2 : Tendsto (fun t : ℝ => c t + w t) (𝓝[Set.Ioo a b] a) (𝓝 (v a)) := by
            rw [hv_a]
            exact h1.mono_left (nhdsWithin_mono a Ioo_subset_Ioi_self)
          refine h2.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact (hv_int t ht).symm
      have ha_deriv : HasDerivAt v (f (v a)) a := by
        have h := ha_left.union ha_right
        rw [Iic_union_Ici] at h
        have h2 : HasDerivAt v (f z) a := h.hasDerivAt univ_mem
        rw [hv_a]
        exact h2
      refine ⟨v, hv_a, ?_, ?_⟩
      · intro t ht
        rcases lt_or_eq_of_le ht.1 with hlt | heq
        · rcases lt_or_eq_of_le ht.2 with hlt2 | heq2
          · exact hv_deriv_int t ⟨hlt, hlt2⟩
          · rw [heq2]
            exact hb_deriv
        · rw [← heq]
          exact ha_deriv
      · intro t ht
        exact hvest t ht

end Commons.Analysis.ODE
