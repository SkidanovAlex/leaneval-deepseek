import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.JM_diag
import Submission.Work.OddVolterra.KernelExt.KvecM_eq_Kvec
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddVolterra.Existence.krad_pos_state_region

/-!
# The localised data of the odd-case anchor window

This file sets up the *localised* (compactly supported) data used to run the long-interval fixed
point engine `Work.VolterraLong.volterra_long_exists_bump` on the slope window `[1/2, 19/20]`.

The raw odd data (`Godd`, `Theta`, `Xi`) is not regular enough for the engine: `Godd` is not
globally continuous, `Theta` involves the derivative of the Abel average `G2` and is singular where
the kernel radicands vanish, and `Xi` involves the derivative of an Abel transform and is
singular at `s = 1`.  The remedy is to multiply the *manifest* representatives
(`KernelExt.GoddM`, `KernelExt.ThetaM`) by explicite smooth cutoffs:

* `awCs` — a bump in the slope variable, `= 1` on `[1/2, 1]` and `= 0` off `(19/40, 41/40)`;
* `awCsX` — a bump in the slope variable for the source, `= 1` on `[1/2, 19/20]` and `= 0` off
  `(12/25, 97/100)`;
* `awCz` — a bump in the state variable, `= 1` on the closed ball of radius `1/5` around `0` and
  `= 0` off the ball of radius `2/5`.

On the region where the cutoffs are `1` the manifest data equals the paper's data
(`KernelExt.GoddM_eq_Godd`, `Window.ThetaM_eq_Theta`), and the kernel radicands are positive
(`krad_pos_state_region`), so a solution of the localised system on `[1/2, 19/20]` is a solution of
the paper's system on the window of interest.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Existence

open Work.OddVolterra

noncomputable section

/-! ## The cutoffs -/

/-- The slope cutoff: a `C^∞` bump, `= 1` on `[1/2, 1]` and `= 0` off `(19/40, 41/40)`. -/
def awCs : ContDiffBump (3 / 4 : ℝ) := ⟨1 / 4, 11 / 40, by norm_num, by norm_num⟩

/-- The slope cutoff of the source: `= 1` on `[1/2, 19/20]` and `= 0` off `(12/25, 97/100)`. -/
def awCsX : ContDiffBump (29 / 40 : ℝ) := ⟨9 / 40, 49 / 200, by norm_num, by norm_num⟩

/-- The state cutoff: `= 1` on the closed ball of radius `1/5` and `= 0` off the ball of radius
`2/5`. -/
def awCz : ContDiffBump (0 : St) := ⟨1 / 5, 2 / 5, by norm_num, by norm_num⟩

lemma awCs_rIn : awCs.rIn = 1 / 4 := rfl
lemma awCs_rOut : awCs.rOut = 11 / 40 := rfl
lemma awCsX_rIn : awCsX.rIn = 9 / 40 := rfl
lemma awCsX_rOut : awCsX.rOut = 49 / 200 := rfl
lemma awCz_rIn : awCz.rIn = 1 / 5 := rfl
lemma awCz_rOut : awCz.rOut = 2 / 5 := rfl

/-- The slope cutoff equals `1` on `[1/2, 1]`. -/
lemma awCs_eq_one {s : ℝ} (hs : s ∈ Set.Icc (1 / 2 : ℝ) 1) : (awCs : ℝ → ℝ) s = 1 := by
  refine ContDiffBump.one_of_mem_closedBall awCs ?_
  rw [awCs_rIn, Metric.mem_closedBall, Real.dist_eq]
  rw [Set.mem_Icc] at hs
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2]

/-- The slope cutoff vanishes off `(19/40, 41/40)`. -/
lemma awCs_eq_zero {s : ℝ} (hs : 11 / 40 ≤ |s - 3 / 4|) : (awCs : ℝ → ℝ) s = 0 := by
  refine ContDiffBump.zero_of_le_dist awCs ?_
  rw [awCs_rOut, Real.dist_eq]
  exact hs

/-- The source cutoff equals `1` on `[1/2, 19/20]`. -/
lemma awCsX_eq_one {s : ℝ} (hs : s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20)) :
    (awCsX : ℝ → ℝ) s = 1 := by
  refine ContDiffBump.one_of_mem_closedBall awCsX ?_
  rw [awCsX_rIn, Metric.mem_closedBall, Real.dist_eq]
  rw [Set.mem_Icc] at hs
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2]

/-- The state cutoff equals `1` on the closed ball of radius `1/5`. -/
lemma awCz_eq_one {w : St} (hw : ‖w‖ ≤ 1 / 5) : (awCz : St → ℝ) w = 1 := by
  refine ContDiffBump.one_of_mem_closedBall awCz ?_
  rw [awCz_rIn, Metric.mem_closedBall, dist_zero_right]
  exact hw

/-- The state cutoff vanishes off the ball of radius `2/5`. -/
lemma awCz_eq_zero {w : St} (hw : 2 / 5 ≤ ‖w‖) : (awCz : St → ℝ) w = 0 := by
  refine ContDiffBump.zero_of_le_dist awCz ?_
  rw [awCz_rOut, dist_zero_right]
  exact hw

lemma awCs_nonneg (s : ℝ) : 0 ≤ (awCs : ℝ → ℝ) s := ContDiffBump.nonneg awCs
lemma awCs_le_one (s : ℝ) : (awCs : ℝ → ℝ) s ≤ 1 := ContDiffBump.le_one awCs
lemma awCsX_nonneg (s : ℝ) : 0 ≤ (awCsX : ℝ → ℝ) s := ContDiffBump.nonneg awCsX
lemma awCsX_le_one (s : ℝ) : (awCsX : ℝ → ℝ) s ≤ 1 := ContDiffBump.le_one awCsX
lemma awCz_nonneg (w : St) : 0 ≤ (awCz : St → ℝ) w := ContDiffBump.nonneg awCz
lemma awCz_le_one (w : St) : (awCz : St → ℝ) w ≤ 1 := ContDiffBump.le_one awCz

/-! ## The localised data -/

/-- The cutoff multiplying the state data. -/
def awChiG (s : ℝ) (z : St) : ℝ := (awCs : ℝ → ℝ) s * (awCz : St → ℝ) (z - baseState s)

/-- The cutoff multiplying the `Θ` data. -/
def awChiT (s σ : ℝ) (z : St) : ℝ :=
  (awCs : ℝ → ℝ) s * (awCs : ℝ → ℝ) σ * (awCz : St → ℝ) (z - baseState σ)

/-- The localised state data. -/
def awGodd (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : St) : St :=
  awChiG s z • Work.OddVolterra.KernelExt.GoddM n h s z

/-- The localised `Θ` data. -/
def awTheta (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : St) : St :=
  awChiT s σ z • Work.OddVolterra.KernelExt.ThetaM n h s σ z

/-- The localised source: the paper's `Ξ` plus the frozen tail from `b` to `1`, cut off. -/
def awXi (n : ℕ) (h : ℝ → ℝ) (b s : ℝ) : St :=
  (awCsX : ℝ → ℝ) s •
    (Work.OddVolterra.Xi n h s +
      ∫ σ in b..(1 : ℝ), Work.OddVolterra.KernelExt.ThetaM n h s σ (baseState σ))

/-! ## Elementary properties of the cutoffs -/

lemma awChiG_eq_one {s : ℝ} (hs : s ∈ Set.Icc (1 / 2 : ℝ) 1) {z : St}
    (hz : ‖z - baseState s‖ ≤ 1 / 5) : awChiG s z = 1 := by
  rw [awChiG, awCs_eq_one hs, awCz_eq_one hz, mul_one]

lemma awChiG_eq_zero {s : ℝ} {z : St} (hz : 2 / 5 ≤ ‖z - baseState s‖) : awChiG s z = 0 := by
  rw [awChiG, awCz_eq_zero hz, mul_zero]

lemma awChiT_eq_one {s σ : ℝ} (hs : s ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) {z : St} (hz : ‖z - baseState σ‖ ≤ 1 / 5) :
    awChiT s σ z = 1 := by
  rw [awChiT, awCs_eq_one hs, awCs_eq_one hσ, awCz_eq_one hz]
  ring

lemma awChiT_eq_zero {s σ : ℝ} {z : St} (hz : 2 / 5 ≤ ‖z - baseState σ‖) :
    awChiT s σ z = 0 := by
  simp [awChiT, awCz_eq_zero hz]

lemma awChiG_nonneg (s : ℝ) (z : St) : 0 ≤ awChiG s z :=
  mul_nonneg (awCs_nonneg s) (awCz_nonneg _)

lemma awChiG_le_one (s : ℝ) (z : St) : awChiG s z ≤ 1 := by
  rw [awChiG]
  exact mul_le_one₀ (awCs_le_one s) (awCz_nonneg _) (awCz_le_one _)

lemma awChiT_nonneg (s σ : ℝ) (z : St) : 0 ≤ awChiT s σ z := by
  rw [awChiT]
  exact mul_nonneg (mul_nonneg (awCs_nonneg s) (awCs_nonneg σ)) (awCz_nonneg _)

lemma awChiT_le_one (s σ : ℝ) (z : St) : awChiT s σ z ≤ 1 := by
  rw [awChiT]
  refine mul_le_one₀ (mul_le_one₀ (awCs_le_one s) (awCs_nonneg σ) (awCs_le_one σ))
    (awCz_nonneg _) (awCz_le_one _)

/-! ## The localised data agrees with the paper's data on the region of use -/

/-- On the slope window `[1/2, 1]` and inside the state ball of radius `1/5`, the localised state
data is the paper's `Godd`. -/
lemma awGodd_eq_Godd {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s : ℝ}
    (hs : s ∈ Set.Icc (1 / 2 : ℝ) 1) {z : St} (hz : ‖z - baseState s‖ ≤ 1 / 5) :
    awGodd n h s z = Godd n h s z := by
  rw [awGodd, awChiG_eq_one hs hz, one_smul,
    Work.OddVolterra.Window.GoddM_eq_Godd n hh s z]

/-- The radicand `krad h σ t a` is positive on the whole box `[19/40, 41/40]²` (in both orders
of `a` and `σ`) whenever `1/5 ≤ |t|` and `h` is supported in `[4/5, 9/10]` with `C¹`-norm at most
`1/100`. -/
theorem aw_krad_pos_box {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∀ a σ t : ℝ, 19 / 40 ≤ a → a ≤ 41 / 40 → 19 / 40 ≤ σ → σ ≤ 41 / 40 →
      1 / 5 ≤ |t| → 0 < Work.OddVolterra.krad h σ t a := by
  have hh0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => hsmall 0 (by norm_num) x
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := by
    intro x; simpa using hsmall 1 (by norm_num) x
  have htau1 : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by
    rw [Work.OddVolterra.tau]; norm_num
  have htau2 : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := by
    rw [Work.OddVolterra.tau]; norm_num
  have hzero : ∀ x : ℝ, x < 4 / 5 → h x = 0 := by
    intro x hx
    by_contra hne
    have hmem := hsupp (Function.mem_support.mpr hne)
    rw [htau1, htau2] at hmem
    linarith [hmem.1]
  intro a σ t ha ha' hσ hσ' ht
  have hS : 0 < σ + a := by linarith
  have hquotbd : |Work.OddVolterra.hquot h a σ| ≤ 1 / 100 :=
    Work.OddVolterra.Existence.abs_hquot_le_state hh1
  have hbnd := abs_le.mp hquotbd
  have hhl : |h σ + h a| ≤ 1 / 50 := by
    have h1 := abs_le.mp (hh0 σ)
    have h2 := abs_le.mp (hh0 a)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hsumlt : |h σ + h a| < (σ + a) * (1 / 5) := by
    have h1 : (19 : ℝ) / 20 * (1 / 5) ≤ (σ + a) * (1 / 5) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have h25 : (19 : ℝ) / 20 * (1 / 5) = 19 / 100 := by norm_num
    have h50 : (1 : ℝ) / 50 < 19 / 100 := by norm_num
    linarith
  have hhline : Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t
      = (σ + a) * t + (h σ + h a) := by
    unfold Work.OddVolterra.line; ring
  rw [Work.OddVolterra.krad_apply, hhline]
  rcases lt_trichotomy t 0 with htn | htz | htp
  · have htle : t ≤ -(1 / 5) := by
      have h := ht; rw [abs_of_neg htn] at h; linarith
    have h1 : t + Work.OddVolterra.hquot h a σ < 0 := by linarith [hbnd.2]
    have hlt' : h σ + h a < (σ + a) * (1 / 5) := lt_of_le_of_lt (le_abs_self _) hsumlt
    have hmul : (σ + a) * t ≤ -((σ + a) * (1 / 5)) := by
      have h := mul_le_mul_of_nonneg_left htle (le_of_lt hS)
      rwa [show (σ + a) * (-(1 / 5)) = -((σ + a) * (1 / 5)) by ring] at h
    have h2 : (σ + a) * t + (h σ + h a) < 0 := by linarith
    exact mul_pos_of_neg_of_neg h1 h2
  · rw [htz] at ht; norm_num at ht
  · have htge : 1 / 5 ≤ t := by
      have h := ht; rwa [abs_of_pos htp] at h
    have h1 : 0 < t + Work.OddVolterra.hquot h a σ := by linarith [hbnd.1]
    have hnegabs : -((σ + a) * (1 / 5)) < -|h σ + h a| := by linarith
    have hgt' : -((σ + a) * (1 / 5)) < h σ + h a :=
      lt_of_lt_of_le hnegabs (neg_abs_le _)
    have hmul : (σ + a) * (1 / 5) ≤ (σ + a) * t :=
      mul_le_mul_of_nonneg_left htge (le_of_lt hS)
    have h2 : 0 < (σ + a) * t + (h σ + h a) := by linarith
    exact mul_pos h1 h2

/-- `profileX σ ≥ 1/2` for `σ ≤ 1`. -/
lemma profileX_ge_half {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1) :
    1 / 2 ≤ Commons.Geometry.Ulam.profileX σ := by
  have hs2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have h1 : Real.sqrt (1 + σ ^ 2) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (by nlinarith [hσ, hσ0, sq_nonneg σ])
  have h2 : 0 < Real.sqrt (1 + σ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h3 : (1 : ℝ) / 2 ≤ 1 / Real.sqrt 2 := by
    rw [one_div, one_div, inv_le_inv₀ (by norm_num) (Real.sqrt_pos.mpr (by norm_num))]
    exact hs2
  have h4 : 1 / Real.sqrt 2 ≤ 1 / Real.sqrt (1 + σ ^ 2) :=
    one_div_le_one_div_of_le h2 h1
  unfold Commons.Geometry.Ulam.profileX
  linarith

/-- **The localised `Θ` data is the paper's `Θ` on the region of use**, for `s < σ ≤ 1` inside
the slope window and inside the state ball of radius `1/5`.  The kernel radicands are positive
along the segment `[s-δ, σ]` by `krad_pos_state_region`. -/
lemma awTheta_eq_Theta (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s σ : ℝ} (hs : s ∈ Set.Icc (1 / 2 : ℝ) 1) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hsσ : s < σ) {z : St} (hz : ‖z - baseState σ‖ ≤ 1 / 5) :
    awTheta n h s σ z = Theta n h s σ z := by
  have hs0 : 0 < s := by linarith [hs.1]
  have hσ1 : σ ≤ 1 := hσ.2
  have hbase1 : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
  have hbase0 : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
  have hσ0 : 0 ≤ σ := by linarith [hσ.1]
  have hprof : 1 / 2 ≤ baseState σ 1 := by rw [hbase1]; exact profileX_ge_half hσ0 hσ1
  have hprof0 : 1 / 2 ≤ baseState σ 0 := by rw [hbase0]; exact profileX_ge_half hσ0 hσ1
  have key : ∀ {w : ℝ} (hw : |w - baseState σ 1| ≤ 1 / 5), 1 / 5 ≤ |w| := by
    intro w hw
    have h1 : |baseState σ 1| ≤ |w| + |w - baseState σ 1| := by
      have h : baseState σ 1 = w - (w - baseState σ 1) := by ring
      rw [h]
      simpa [abs_sub_comm] using abs_sub_le w 0 (w - baseState σ 1)
    rw [abs_of_nonneg (by linarith)] at h1
    linarith
  have key0 : ∀ {w : ℝ} (hw : |w - baseState σ 0| ≤ 1 / 5), 1 / 5 ≤ |w| := by
    intro w hw
    have h1 : |baseState σ 0| ≤ |w| + |w - baseState σ 0| := by
      have h : baseState σ 0 = w - (w - baseState σ 0) := by ring
      rw [h]
      simpa [abs_sub_comm] using abs_sub_le w 0 (w - baseState σ 0)
    rw [abs_of_nonneg (by linarith)] at h1
    linarith
  have hz1 : 1 / 5 ≤ |z 1| := by
    refine key ?_
    have h2 := norm_le_pi_norm (z - baseState σ) 1
    rw [Pi.sub_apply, Real.norm_eq_abs] at h2
    exact le_trans h2 hz
  have hz0 : 1 / 5 ≤ |z 0| := by
    refine key0 ?_
    have h2 := norm_le_pi_norm (z - baseState σ) 0
    rw [Pi.sub_apply, Real.norm_eq_abs] at h2
    exact le_trans h2 hz
  have hs02 : (0 : ℝ) < s / 2 := by linarith
  rw [awTheta, awChiT_eq_one hs hσ hz, one_smul]
  refine Work.OddVolterra.Window.ThetaM_eq_Theta (n := n) (hn := hn) (hh := hh)
    (s := s) (σ := σ) (δ := s / 2) hsσ hs02 z (fun a ha => ?_) (fun a ha => ?_)
  · refine Work.OddVolterra.Existence.krad_pos_state_region hsupp hsmall hs02 ?_ ?_ ?_
      (by simpa using hz0)
    · linarith [ha.1]
    · exact ha.2
    · linarith [ha.2, hσ1]
  · refine Work.OddVolterra.Existence.krad_pos_state_region hsupp hsmall hs02 ?_ ?_ ?_ hz1
    · linarith [ha.1]
    · exact ha.2
    · linarith [ha.2, hσ1]

/-- The state data vanishes unless `|s - 3/4| < 11/40` and `‖z - baseState s‖ < 2/5`. -/
lemma awGodd_eq_zero_of_not_mem {n : ℕ} {h : ℝ → ℝ} {s : ℝ} {z : St}
    (hns : ¬ (|s - 3 / 4| < 11 / 40 ∧ ‖z - baseState s‖ < 2 / 5)) : awGodd n h s z = 0 := by
  by_cases h1 : |s - 3 / 4| < 11 / 40
  · have h2 : ¬ (‖z - baseState s‖ < 2 / 5) := fun h2 => hns ⟨h1, h2⟩
    have h2' : 2 / 5 ≤ ‖z - baseState s‖ := le_of_not_gt h2
    rw [awGodd, awChiG_eq_zero h2', zero_smul]
  · have h1' : 11 / 40 ≤ |s - 3 / 4| := le_of_not_gt h1
    rw [awGodd, awChiG, awCs_eq_zero h1', zero_mul, zero_smul]

end

end Work.OddVolterra.Existence
