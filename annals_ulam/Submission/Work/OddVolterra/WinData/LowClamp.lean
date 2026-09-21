import Mathlib
import Submission.Work.OddVolterra.WinData.LowData
import Submission.Work.OddVolterra.Existence.aw_contDiffOn_awGodd

/-!
# The clamped data of the low-slope piece

The clamped state datum `lcGodd` and clamped kernel `lcTheta` for the low slope window
`[1/4, 4/5]`: the manifest data of `h ≡ 0`, multiplied by a smooth cut-off in the slope and by
`cz2 ∘ wsq` in the state.  They are globally `C^∞`, coincide with the paper's data on the window
(once `h` is supported to the right of `4/5`), and satisfy the Lipschitz/differentiability
properties the long-interval engine needs — with constants that do not depend on `h`.
-/

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra

/-! ## Definitions -/

/-- The state cut-off of the low-slope data. -/
def lcChiG (s : ℝ) (z : St) : ℝ := lcS s * (Window.cz2 : ℝ → ℝ) (Window.wsq s z)

/-- The kernel cut-off of the low-slope data. -/
def lcChiT (s σ : ℝ) (z : St) : ℝ :=
  lcS s * lcS σ * (Window.cz2 : ℝ → ℝ) (Window.wsq σ z)

/-- The clamped state datum of the low-slope piece. -/
def lcGodd (n : ℕ) (s : ℝ) (z : St) : St := lcChiG s z • KernelExt.GoddM n 0 s z

/-- The clamped kernel datum of the low-slope piece. -/
def lcTheta (n : ℕ) (s σ : ℝ) (z : St) : St := lcChiT s σ z • KernelExt.ThetaM n 0 s σ z

/-- The closed region containing the support of the state cut-off. -/
def lcSuppG : Set (ℝ × St) :=
  {p | |p.1 - lcCenter| ≤ lcRout ∧ Window.wsq p.1 p.2 ≤ 4 / 25}

/-- The closed region containing the support of the kernel cut-off. -/
def lcSuppT : Set (ℝ × (ℝ × St)) :=
  {q | |q.1 - lcCenter| ≤ lcRout ∧ |q.2.1 - lcCenter| ≤ lcRout ∧
    Window.wsq q.2.1 q.2.2 ≤ 4 / 25}

/-! ## Elementary consequences of the support conditions -/

lemma lcSuppG_slope {p : ℝ × St} (hp : p ∈ lcSuppG) :
    p.1 ∈ Set.Icc (9 / 40 : ℝ) (33 / 40) := by
  obtain ⟨h1, -⟩ := hp
  have hc : lcCenter = 21 / 40 := rfl
  have hr : lcRout = 3 / 10 := rfl
  rw [hc, hr, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

lemma lcSuppT_slopes {q : ℝ × (ℝ × St)} (hq : q ∈ lcSuppT) :
    q.1 ∈ Set.Icc (9 / 40 : ℝ) (33 / 40) ∧ q.2.1 ∈ Set.Icc (9 / 40 : ℝ) (33 / 40) := by
  obtain ⟨h1, h2, -⟩ := hq
  have hc : lcCenter = 21 / 40 := rfl
  have hr : lcRout = 3 / 10 := rfl
  rw [hc, hr, abs_le] at h1 h2
  exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩

lemma lcSuppG_norm {p : ℝ × St} (hp : p ∈ lcSuppG) :
    ‖p.2 - baseState p.1‖ ≤ 2 / 5 := by
  obtain ⟨-, h2⟩ := hp
  have h := Window.sq_norm_le_wsq p.1 p.2
  nlinarith [norm_nonneg (p.2 - baseState p.1), h, h2]

lemma lcSuppT_norm {q : ℝ × (ℝ × St)} (hq : q ∈ lcSuppT) :
    ‖q.2.2 - baseState q.2.1‖ ≤ 2 / 5 := by
  obtain ⟨-, -, h2⟩ := hq
  have h := Window.sq_norm_le_wsq q.2.1 q.2.2
  nlinarith [norm_nonneg (q.2.2 - baseState q.2.1), h, h2]

/-- The two chord endpoints of a state within `2/5` of `baseState σ`, for `σ ∈ [9/40, 33/40]`,
have modulus `> 1/5`. -/
lemma lc_coord_bounds {σ : ℝ} (hσ : σ ∈ Set.Icc (9 / 40 : ℝ) (33 / 40)) {z : St}
    (hz : ‖z - baseState σ‖ ≤ 2 / 5) :
    1 / 5 < |z 0| ∧ 1 / 5 < |z 1| := by
  have hpx : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX σ :=
    Window.seven_tenths_le_profileX (by linarith [hσ.1]) (by linarith [hσ.2])
  have hbd : ∀ i : Fin 4, |z i - baseState σ i| ≤ 2 / 5 := by
    intro i
    have h := norm_le_pi_norm (z - baseState σ) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_trans h hz
  have hb0 : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
  have hb1 : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
  refine ⟨?_, ?_⟩
  · have h := hbd 0
    rw [hb0] at h
    have h' := (abs_le.mp h).1
    have hpos : (0 : ℝ) < z 0 := by linarith
    rw [abs_of_pos hpos]; linarith
  · have h := hbd 1
    rw [hb1] at h
    have h' := (abs_le.mp h).1
    have hpos : (0 : ℝ) < z 1 := by linarith
    rw [abs_of_pos hpos]; linarith

lemma lcSuppG_subset_lcV : lcSuppG ⊆ lcV := by
  intro p hp
  obtain ⟨hs, hz⟩ := hp
  have hs' := lcSuppG_slope ⟨hs, hz⟩
  have hz' := lcSuppG_norm ⟨hs, hz⟩
  obtain ⟨h1, h2⟩ := lc_coord_bounds hs' hz'
  exact ⟨⟨by linarith [hs'.1], by linarith [hs'.2]⟩, h1, h2⟩

lemma lcSuppT_subset_lcU : lcSuppT ⊆ lcU := by
  intro q hq
  obtain ⟨hs, hσ, hz⟩ := hq
  have hs' := lcSuppT_slopes ⟨hs, hσ, hz⟩
  have hz' := lcSuppT_norm ⟨hs, hσ, hz⟩
  obtain ⟨h1, h2⟩ := lc_coord_bounds hs'.2 hz'
  exact ⟨⟨by linarith [hs'.1.1], by linarith [hs'.1.2]⟩,
    ⟨by linarith [hs'.2.1], by linarith [hs'.2.2]⟩, h1, h2⟩

/-- Off the support region the clamped state datum vanishes. -/
lemma lcGodd_eq_zero_off {n : ℕ} {p : ℝ × St} (hp : p ∉ lcSuppG) :
    lcGodd n p.1 p.2 = 0 := by
  have hp' : ¬ (|p.1 - lcCenter| ≤ lcRout ∧ Window.wsq p.1 p.2 ≤ 4 / 25) := hp
  rcases not_and_or.mp hp' with h1 | h2
  · rw [lcGodd, lcChiG, lcS_eq_zero_of_le_dist (le_of_lt (not_le.mp h1)), zero_mul, zero_smul]
  · rw [lcGodd, lcChiG, Window.cz2_eq_zero_of_le (le_of_lt (not_le.mp h2)), mul_zero,
      zero_smul]

/-- Off the support region the clamped kernel datum vanishes. -/
lemma lcTheta_eq_zero_off {n : ℕ} {q : ℝ × (ℝ × St)} (hq : q ∉ lcSuppT) :
    lcTheta n q.1 q.2.1 q.2.2 = 0 := by
  have hq' : ¬ (|q.1 - lcCenter| ≤ lcRout ∧ |q.2.1 - lcCenter| ≤ lcRout ∧
      Window.wsq q.2.1 q.2.2 ≤ 4 / 25) := hq
  rcases not_and_or.mp hq' with h1 | h2
  · rw [lcTheta, lcChiT, lcS_eq_zero_of_le_dist (le_of_lt (not_le.mp h1)), zero_mul, zero_mul,
      zero_smul]
  · rcases not_and_or.mp h2 with h2 | h3
    · rw [lcTheta, lcChiT, lcS_eq_zero_of_le_dist (le_of_lt (not_le.mp h2)), mul_zero, zero_mul,
        zero_smul]
    · rw [lcTheta, lcChiT, Window.cz2_eq_zero_of_le (le_of_lt (not_le.mp h3)), mul_zero,
        zero_smul]

/-! ## Smoothness of the cut-offs -/

lemma contDiff_wsq : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => Window.wsq p.1 p.2) := by
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => baseState p.1) :=
    Work.OddVolterra.Existence.contDiff_baseState_comp
  simp only [Window.wsq]
  fun_prop

lemma contDiff_wsq_T :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × St) => Window.wsq q.2.1 q.2.2) := by
  have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × St) => (q.2.1, q.2.2)) := by fun_prop
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × St) => baseState q.2.1) :=
    Work.OddVolterra.Existence.contDiff_baseState_comp.comp hpair
  simp only [Window.wsq]
  fun_prop

lemma contDiff_lcChiG : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => lcChiG p.1 p.2) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => lcS p.1) :=
    contDiff_lcS.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × St => (Window.cz2 : ℝ → ℝ) (Window.wsq p.1 p.2)) :=
    (ContDiffBump.contDiff Window.cz2).comp contDiff_wsq
  simpa only [lcChiG] using h1.mul h2

lemma contDiff_lcChiT :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × St) => lcChiT q.1 q.2.1 q.2.2) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × St) => lcS q.1) :=
    contDiff_lcS.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × St) => lcS q.2.1) :=
    contDiff_lcS.comp (contDiff_fst.comp contDiff_snd)
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St) => (Window.cz2 : ℝ → ℝ) (Window.wsq q.2.1 q.2.2)) :=
    (ContDiffBump.contDiff Window.cz2).comp contDiff_wsq_T
  simpa only [lcChiT, mul_assoc] using h1.mul (h2.mul h3)

/-! ## The support regions are compact -/

lemma isClosed_lcSuppG : IsClosed lcSuppG := by
  have h1 : IsClosed {p : ℝ × St | |p.1 - lcCenter| ≤ lcRout} :=
    isClosed_le (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const
  have h2 : IsClosed {p : ℝ × St | Window.wsq p.1 p.2 ≤ 4 / 25} :=
    isClosed_le contDiff_wsq.continuous continuous_const
  have heq : lcSuppG = {p : ℝ × St | |p.1 - lcCenter| ≤ lcRout} ∩
      {p : ℝ × St | Window.wsq p.1 p.2 ≤ 4 / 25} := by
    ext p; simp only [lcSuppG, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [heq]; exact h1.inter h2

lemma isClosed_lcSuppT : IsClosed lcSuppT := by
  have h1 : IsClosed {q : ℝ × (ℝ × St) | |q.1 - lcCenter| ≤ lcRout} :=
    isClosed_le (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const
  have h2 : IsClosed {q : ℝ × (ℝ × St) | |q.2.1 - lcCenter| ≤ lcRout} :=
    isClosed_le (continuous_abs.comp ((continuous_fst.comp continuous_snd).sub continuous_const))
      continuous_const
  have h3 : IsClosed {q : ℝ × (ℝ × St) | Window.wsq q.2.1 q.2.2 ≤ 4 / 25} :=
    isClosed_le contDiff_wsq_T.continuous continuous_const
  have heq : lcSuppT = {q : ℝ × (ℝ × St) | |q.1 - lcCenter| ≤ lcRout} ∩
      ({q : ℝ × (ℝ × St) | |q.2.1 - lcCenter| ≤ lcRout} ∩
        {q : ℝ × (ℝ × St) | Window.wsq q.2.1 q.2.2 ≤ 4 / 25}) := by
    ext q; simp only [lcSuppT, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [heq]; exact h1.inter (h2.inter h3)

/-- The ball state is bounded by `1` in the sup norm. -/
lemma norm_baseState_le_one (s : ℝ) : ‖baseState s‖ ≤ 1 := by
  have hpx : |Commons.Geometry.Ulam.profileX s| ≤ 1 := by
    rw [Commons.Geometry.Ulam.profileX, abs_of_pos (by positivity)]
    rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s])
  have hdpx : |deriv Commons.Geometry.Ulam.profileX s| ≤ 1 := by
    rw [Commons.Geometry.Ulam.deriv_profileX_eq s, abs_mul, abs_neg]
    have h1 : |s / (1 + s ^ 2)| ≤ 1 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + s ^ 2), div_le_one (by positivity)]
      nlinarith [sq_nonneg s, sq_abs s, abs_nonneg s, sq_nonneg (|s| - 1 / 2)]
    have h2 : |Commons.Geometry.Ulam.profileX s| ≤ 1 := hpx
    have h3 : |s / (1 + s ^ 2)| * |Commons.Geometry.Ulam.profileX s| ≤ 1 * 1 :=
      mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    linarith
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
  intro i
  fin_cases i <;>
    simp only [baseState, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    first
      | exact hpx
      | exact hdpx

lemma lcSuppG_bound {p : ℝ × St} (hp : p ∈ lcSuppG) : ‖p‖ ≤ 7 / 5 := by
  obtain ⟨h1, h2⟩ := hp
  have hs : ‖p.1‖ ≤ 7 / 5 := by
    have h := lcSuppG_slope ⟨h1, h2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [h.1])]
    linarith [h.2]
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · exact hs
  · have hz := lcSuppG_norm ⟨h1, h2⟩
    have hb := norm_baseState_le_one p.1
    have hsplit : ‖p.2‖ ≤ ‖baseState p.1‖ + ‖p.2 - baseState p.1‖ := by
      have h := norm_add_le (baseState p.1) (p.2 - baseState p.1)
      rw [add_sub_cancel] at h
      exact h
    linarith

lemma lcSuppT_bound {q : ℝ × (ℝ × St)} (hq : q ∈ lcSuppT) : ‖q‖ ≤ 7 / 5 := by
  obtain ⟨h1, h2, h3⟩ := hq
  have hs := lcSuppT_slopes ⟨h1, h2, h3⟩
  have hq1 : ‖q.1‖ ≤ 7 / 5 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.1.1])]; linarith [hs.1.2]
  have hq2 : ‖q.2.1‖ ≤ 7 / 5 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2.1])]; linarith [hs.2.2]
  have hq3 : ‖q.2.2‖ ≤ 7 / 5 := by
    have hz := lcSuppT_norm ⟨h1, h2, h3⟩
    have hb := norm_baseState_le_one q.2.1
    have hsplit : ‖q.2.2‖ ≤ ‖baseState q.2.1‖ + ‖q.2.2 - baseState q.2.1‖ := by
      have h := norm_add_le (baseState q.2.1) (q.2.2 - baseState q.2.1)
      rw [add_sub_cancel] at h
      exact h
    linarith
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le hq1 (max_le hq2 hq3)

lemma isCompact_lcSuppG : IsCompact lcSuppG :=
  (isCompact_closedBall (0 : ℝ × St) (7 / 5)).of_isClosed_subset isClosed_lcSuppG
    (fun p hp => by rw [Metric.mem_closedBall, dist_zero_right]; exact lcSuppG_bound hp)

lemma isCompact_lcSuppT : IsCompact lcSuppT :=
  (isCompact_closedBall (0 : ℝ × (ℝ × St)) (7 / 5)).of_isClosed_subset isClosed_lcSuppT
    (fun q hq => by rw [Metric.mem_closedBall, dist_zero_right]; exact lcSuppT_bound hq)

/-! ## Global smoothness of the clamped data -/

lemma contDiffOn_lcV_lcGodd (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => lcGodd n p.1 p.2) lcV := by
  refine (contDiff_lcChiG.contDiffOn.smul (contDiffOn_lcV_GoddM n)).congr (fun p _ => ?_)
  rfl

lemma contDiffOn_lcU_lcTheta (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × St) => lcTheta n q.1 q.2.1 q.2.2) lcU := by
  refine (contDiff_lcChiT.contDiffOn.smul (contDiffOn_lcU_ThetaM n)).congr (fun q _ => ?_)
  rfl

theorem contDiff_lcGodd (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => lcGodd n p.1 p.2) := by
  rw [← contDiffOn_univ]
  have hgood := contDiffOn_lcV_lcGodd n
  have hzero : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => lcGodd n p.1 p.2) lcSuppGᶜ :=
    (contDiffOn_const (c := (0 : St))).congr
      (fun p hp => lcGodd_eq_zero_off (n := n) hp)
  refine contDiffOn_of_locally_contDiffOn (fun p _ => ?_)
  by_cases hp : p ∈ lcV
  · exact ⟨lcV, isOpen_lcV, hp, hgood.mono Set.inter_subset_right⟩
  · exact ⟨lcSuppGᶜ, isClosed_lcSuppG.isOpen_compl, fun hc => hp (lcSuppG_subset_lcV hc),
      hzero.mono Set.inter_subset_right⟩

theorem contDiff_lcTheta (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × St) => lcTheta n q.1 q.2.1 q.2.2) := by
  rw [← contDiffOn_univ]
  have hgood := contDiffOn_lcU_lcTheta n
  have hzero : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St) => lcTheta n q.1 q.2.1 q.2.2) lcSuppTᶜ :=
    (contDiffOn_const (c := (0 : St))).congr
      (fun q hq => lcTheta_eq_zero_off (n := n) hq)
  refine contDiffOn_of_locally_contDiffOn (fun q _ => ?_)
  by_cases hq : q ∈ lcU
  · exact ⟨lcU, isOpen_lcU, hq, hgood.mono Set.inter_subset_right⟩
  · exact ⟨lcSuppTᶜ, isClosed_lcSuppT.isOpen_compl, fun hc => hq (lcSuppT_subset_lcU hc),
      hzero.mono Set.inter_subset_right⟩

lemma support_lcGodd_subset (n : ℕ) :
    Function.support (fun p : ℝ × St => lcGodd n p.1 p.2) ⊆ lcSuppG := by
  intro p hp
  by_contra hcon
  exact hp (lcGodd_eq_zero_off (n := n) hcon)

lemma support_lcTheta_subset (n : ℕ) :
    Function.support (fun q : ℝ × (ℝ × St) => lcTheta n q.1 q.2.1 q.2.2) ⊆ lcSuppT := by
  intro q hq
  by_contra hcon
  exact hq (lcTheta_eq_zero_off (n := n) hcon)

lemma hasCompactSupport_lcGodd (n : ℕ) :
    HasCompactSupport (fun p : ℝ × St => lcGodd n p.1 p.2) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_lcSuppG) (support_lcGodd_subset n)

lemma hasCompactSupport_lcTheta (n : ℕ) :
    HasCompactSupport (fun q : ℝ × (ℝ × St) => lcTheta n q.1 q.2.1 q.2.2) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_lcSuppT) (support_lcTheta_subset n)

/-! ## The Lipschitz constants of the engine data -/

theorem lc_godd_lipschitz_constants (n : ℕ) (hn : 1 ≤ n) :
    (∃ L : ℝ, 0 ≤ L ∧ ∀ s σ : ℝ, ∀ z z' : St,
        ‖lcTheta n s σ z - lcTheta n s σ z'‖ ≤ L * ‖z - z'‖) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, ∀ z : St,
        ‖fderiv ℝ (fun w : St => lcGodd n s w) z‖ ≤ C) := by
  obtain ⟨L₀, hL₀⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ)
    (hasCompactSupport_lcTheta n) (contDiff_lcTheta n) (by simp)
  obtain ⟨C₀, hC₀⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ)
    (hasCompactSupport_lcGodd n) (contDiff_lcGodd n) (by simp)
  refine ⟨⟨max (L₀ : ℝ) 0, le_max_right _ _, ?_⟩, ⟨max (C₀ : ℝ) 0, le_max_right _ _, ?_⟩⟩
  · intro s σ z z'
    have h1 : ‖(s, (σ, z)) - (s, (σ, z'))‖ = ‖z - z'‖ := by
      have h2 : ((s, (σ, z)) - (s, (σ, z')) : ℝ × (ℝ × St)) = (0, (0, z - z')) := by
        ext i <;> simp
      rw [h2, Prod.norm_def, Prod.norm_def]
      simp
    have := hL₀.dist_le_mul (s, (σ, z)) (s, (σ, z'))
    rw [dist_eq_norm, dist_eq_norm, h1] at this
    calc ‖lcTheta n s σ z - lcTheta n s σ z'‖ ≤ (L₀ : ℝ) * ‖z - z'‖ := this
      _ ≤ max (L₀ : ℝ) 0 * ‖z - z'‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · intro s z
    have hf : LipschitzWith (1 : NNReal) (fun w : St => (s, w)) := by
      refine LipschitzWith.of_dist_le_mul ?_
      intro a b
      simpa using le_of_eq (show dist (s, a) (s, b) = dist a b by
        rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm, Prod.norm_def]; simp)
    have hlip : LipschitzWith C₀ (fun w : St => lcGodd n s w) := by
      have hcomp := hC₀.comp hf
      rw [mul_one] at hcomp
      exact hcomp
    have h : ‖fderiv ℝ (fun w : St => lcGodd n s w) z‖ ≤ (C₀ : ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ hlip
    exact le_trans h (le_max_left _ _)

/-! ## The values of the clamped data at the base state -/

lemma lcGodd_baseState (n : ℕ) {s : ℝ} (hs : s ∈ Set.Icc lcA lcB) :
    lcGodd n s (baseState s) = Godd n 0 s (baseState s) := by
  have h1 : lcS s = 1 := lcS_eq_one_of_mem hs
  have h2 : (Window.cz2 : ℝ → ℝ) (Window.wsq s (baseState s)) = 1 := by
    refine Window.cz2_eq_one_of_le ?_ ?_
    · simp [Window.wsq]
    · simp [Window.wsq]
  rw [lcGodd, lcChiG, h1, h2, one_mul, one_smul]
  exact Window.GoddM_eq_Godd n contDiff_const s (baseState s)

lemma lcTheta_baseState (n : ℕ) {s σ : ℝ} (hs : s ∈ Set.Icc lcA lcB)
    (hσ : σ ∈ Set.Icc lcA lcB) :
    lcTheta n s σ (baseState σ) = KernelExt.ThetaM n 0 s σ (baseState σ) := by
  have h1 : lcS s = 1 := lcS_eq_one_of_mem hs
  have h2 : lcS σ = 1 := lcS_eq_one_of_mem hσ
  have h3 : (Window.cz2 : ℝ → ℝ) (Window.wsq σ (baseState σ)) = 1 := by
    refine Window.cz2_eq_one_of_le ?_ ?_
    · simp [Window.wsq]
    · simp [Window.wsq]
  rw [lcTheta, lcChiT, h1, h2, h3, one_mul, one_mul, one_smul]

end

end Work.OddVolterra.WinData
