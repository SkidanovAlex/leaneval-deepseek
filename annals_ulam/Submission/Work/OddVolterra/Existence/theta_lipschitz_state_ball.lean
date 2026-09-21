import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.KvecM_eq_Kvec
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.Existence.base_volterra
import Submission.Work.OddVolterra.Existence.krad_pos_state_region
import Submission.Work.OddVolterra.KernelExt.KvecM_contDiffOn_box
import Submission.Work.OddVolterra.Existence.continuousOn_deriv_G2_apply

/-!
# The state-ball Lipschitz/bound/continuity data of the odd-case kernel `Θ`

This file proves `Work.OddVolterra.Existence.theta_lipschitz_state_ball`: on the state ball
`closedBall (baseState σ) (1/2)` (`σ ∈ [b,1]`, `s ∈ [b,1]`) the last two rows of the paper's
kernel `𝚯 n h s σ ·` — the `u`-derivatives at `u = s` of the Abel average `G₂` — are Lipschitz
in the state, bounded, and jointly continuous in `(σ,z)`.

The analytic input is `ktext_data`: on the compact trapezium `b/2 ≤ a ≤ σ ≤ 1`,
`t ∈ [c1,c2]` (with `1/5 ≤ |t|` on it), the manifest kernel extensions `k1ext`, `k2ext` and their
first `a`-derivatives (`k1v`, `k2v`, `k1d`, `k2d` below) are bounded, and the `a`-derivative
fields are Lipschitz in `t`.  Everything else is bookkeeping: the paper's kernels agree with the
manifest ones off the diagonal (`K1_eq_k1ext`, `K2_eq_k2ext`, `deriv_K1_eq_k1d`,
`deriv_K2_eq_k2d`), the state ball forces `z 0, z 1 ≥ 1/5` and `|z i| ≤ 2` (`state_ball_box`),
and `deriv_G2_apply_eq_integral` writes the last two rows of `Θ` as Abel-weighted integrals of
`∂_a Kvec`, with the weight integrating to `π` (`abel_weight_integral`).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Existence

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The state ball -/

/-- On the state ball `closedBall (baseState σ) (1/2)` (`σ ∈ [b,1]`, `0 < b ≤ 1`) the first two
state coordinates are bounded below by `1/5` and all four by `2` in absolute value. -/
lemma state_ball_box {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∀ σ ∈ Set.Icc b 1, ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2),
      (1 / 5 : ℝ) ≤ z 0 ∧ (1 / 5 : ℝ) ≤ z 1 ∧ (∀ i : Fin 4, |z i| ≤ 2) := by
  intro σ hσ z hz
  have hcoord : ∀ i : Fin 4, |z i - Work.OddVolterra.baseState σ i| ≤ 1 / 2 := by
    intro i
    have h := dist_le_pi_dist z (Work.OddVolterra.baseState σ) i
    rw [Real.dist_eq] at h
    linarith [Metric.mem_closedBall.mp hz]
  have hbase : ∀ i : Fin 4, |Work.OddVolterra.baseState σ i| ≤ 1 := by
    intro i
    fin_cases i
    · show |Work.OddVolterra.baseState σ 0| ≤ 1
      rw [show Work.OddVolterra.baseState σ 0 = Commons.Geometry.Ulam.profileX σ from rfl]
      exact abs_le.mpr ⟨(Commons.Geometry.Ulam.profileX_mem_Icc σ).1,
        (Commons.Geometry.Ulam.profileX_mem_Icc σ).2⟩
    · show |Work.OddVolterra.baseState σ 1| ≤ 1
      rw [show Work.OddVolterra.baseState σ 1 = Commons.Geometry.Ulam.profileX σ from rfl]
      exact abs_le.mpr ⟨(Commons.Geometry.Ulam.profileX_mem_Icc σ).1,
        (Commons.Geometry.Ulam.profileX_mem_Icc σ).2⟩
    · show |Work.OddVolterra.baseState σ 2| ≤ 1
      rw [show Work.OddVolterra.baseState σ 2 = deriv Commons.Geometry.Ulam.profileX σ from rfl]
      linarith [Commons.Geometry.Ulam.abs_deriv_profileX_le σ]
    · show |Work.OddVolterra.baseState σ 3| ≤ 1
      rw [show Work.OddVolterra.baseState σ 3 = deriv Commons.Geometry.Ulam.profileX σ from rfl]
      linarith [Commons.Geometry.Ulam.abs_deriv_profileX_le σ]
  have hprof : (1 : ℝ) / 5 ≤ Commons.Geometry.Ulam.profileX σ - 1 / 2 := by
    have h0 : 0 ≤ σ := le_trans hb.le hσ.1
    have h1 : Commons.Geometry.Ulam.profileX 1 ≤ Commons.Geometry.Ulam.profileX σ :=
      Commons.Geometry.Ulam.profileX_le_profileX' h0 hσ.2
    have h2 : Commons.Geometry.Ulam.profileX 1 = 1 / Real.sqrt 2 := by
      simp only [Commons.Geometry.Ulam.profileX]; norm_num
    have h3 : Real.sqrt 2 < 10 / 7 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h4 : (7 : ℝ) / 10 < 1 / Real.sqrt 2 := by
      rw [lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      nlinarith [h3]
    rw [h2] at h1
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := hcoord 0
    rw [show Work.OddVolterra.baseState σ 0 = Commons.Geometry.Ulam.profileX σ from rfl] at h
    linarith [abs_le.mp h]
  · have h := hcoord 1
    rw [show Work.OddVolterra.baseState σ 1 = Commons.Geometry.Ulam.profileX σ from rfl] at h
    linarith [abs_le.mp h]
  · intro i
    have h := abs_le.mp (hcoord i)
    have hb' := abs_le.mp (hbase i)
    rw [abs_le]
    constructor <;> linarith

/-! ## The kernel data on a compact trapezium of slopes -/

/-- The compact trapezium `b/2 ≤ a ≤ σ`, `σ ∈ [b,1]`, `t ∈ [c1,c2]` in the `((σ,t),a)`
coordinates of the Abel kernel extensions `k1ext`, `k2ext`. -/
def ktextRegion (b c1 c2 : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {q | q.1.1 ∈ Set.Icc b 1 ∧ q.1.2 ∈ Set.Icc c1 c2 ∧ q.2 ∈ Set.Icc (b / 2) q.1.1}

/-- The manifest first Abel kernel in the `((σ,t),a)` coordinates. -/
def k1v (n : ℕ) (h : ℝ → ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ := Work.OddVolterra.k1ext n h q.1.1 q.1.2 q.2

/-- The manifest second Abel kernel in the `((σ,t),a)` coordinates. -/
def k2v (n : ℕ) (h : ℝ → ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ := Work.OddVolterra.k2ext n h q.1.1 q.1.2 q.2

/-- The `a`-derivative field of `k1ext` in the `((σ,t),a)` coordinates. -/
def k1d (n : ℕ) (h : ℝ → ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ :=
  deriv (fun a' => Work.OddVolterra.k1ext n h q.1.1 q.1.2 a') q.2

/-- The `a`-derivative field of `k2ext` in the `((σ,t),a)` coordinates. -/
def k2d (n : ℕ) (h : ℝ → ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ :=
  deriv (fun a' => Work.OddVolterra.k2ext n h q.1.1 q.1.2 a') q.2

@[simp] lemma k1v_apply (n : ℕ) (h : ℝ → ℝ) (σ t a : ℝ) :
    k1v n h ((σ, t), a) = Work.OddVolterra.k1ext n h σ t a := rfl

@[simp] lemma k2v_apply (n : ℕ) (h : ℝ → ℝ) (σ t a : ℝ) :
    k2v n h ((σ, t), a) = Work.OddVolterra.k2ext n h σ t a := rfl

@[simp] lemma k1d_apply (n : ℕ) (h : ℝ → ℝ) (σ t a : ℝ) :
    k1d n h ((σ, t), a) = deriv (fun a' => Work.OddVolterra.k1ext n h σ t a') a := rfl

@[simp] lemma k2d_apply (n : ℕ) (h : ℝ → ℝ) (σ t a : ℝ) :
    k2d n h ((σ, t), a) = deriv (fun a' => Work.OddVolterra.k2ext n h σ t a') a := rfl

lemma ktextRegion_convex (b c1 c2 : ℝ) : Convex ℝ (ktextRegion b c1 c2) := by
  rw [convex_iff_forall_pos]
  unfold ktextRegion
  rintro q ⟨h1, h2, h3⟩ q' ⟨h1', h2', h3'⟩ u v hu hv huv
  refine ⟨?_, ?_, ?_⟩
  · have hgoal : ((u • q + v • q') : (ℝ × ℝ) × ℝ).1.1 = u * q.1.1 + v * q'.1.1 := by simp
    rw [hgoal]
    constructor
    · have hs : u * b + v * b = b := by rw [← add_mul, huv, one_mul]
      nlinarith [h1.1, h1'.1, hu, hv, hs]
    · have hs : u * 1 + v * 1 = 1 := by rw [← add_mul, huv, one_mul]
      nlinarith [h1.2, h1'.2, hu, hv, hs]
  · have hgoal : ((u • q + v • q') : (ℝ × ℝ) × ℝ).1.2 = u * q.1.2 + v * q'.1.2 := by simp
    rw [hgoal]
    constructor
    · have hs : u * c1 + v * c1 = c1 := by rw [← add_mul, huv, one_mul]
      nlinarith [h2.1, h2'.1, hu, hv, hs]
    · have hs : u * c2 + v * c2 = c2 := by rw [← add_mul, huv, one_mul]
      nlinarith [h2.2, h2'.2, hu, hv, hs]
  · have hgoal2 : ((u • q + v • q') : (ℝ × ℝ) × ℝ).2 = u * q.2 + v * q'.2 := by simp
    have hgoal1 : ((u • q + v • q') : (ℝ × ℝ) × ℝ).1.1 = u * q.1.1 + v * q'.1.1 := by simp
    rw [hgoal2, hgoal1]
    constructor
    · have hs : u * (b / 2) + v * (b / 2) = b / 2 := by rw [← add_mul, huv, one_mul]
      nlinarith [h3.1, h3'.1, hu, hv, hs]
    · nlinarith [h3.2, h3'.2, hu, hv]

lemma ktextRegion_compact (b c1 c2 : ℝ) : IsCompact (ktextRegion b c1 c2) := by
  have hclosed : IsClosed (ktextRegion b c1 c2) := by
    have h1 : IsClosed {q : (ℝ × ℝ) × ℝ | q.1.1 ∈ Set.Icc b 1} :=
      IsClosed.preimage (by fun_prop) isClosed_Icc
    have h2 : IsClosed {q : (ℝ × ℝ) × ℝ | q.1.2 ∈ Set.Icc c1 c2} :=
      IsClosed.preimage (by fun_prop) isClosed_Icc
    have h3 : IsClosed {q : (ℝ × ℝ) × ℝ | b / 2 ≤ q.2} :=
      isClosed_le continuous_const (by fun_prop)
    have h4 : IsClosed {q : (ℝ × ℝ) × ℝ | q.2 ≤ q.1.1} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have heq : ktextRegion b c1 c2
        = {q : (ℝ × ℝ) × ℝ | q.1.1 ∈ Set.Icc b 1} ∩ {q | q.1.2 ∈ Set.Icc c1 c2}
          ∩ {q | b / 2 ≤ q.2} ∩ {q | q.2 ≤ q.1.1} := by
      unfold ktextRegion
      ext q; simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_inter_iff]; tauto
    rw [heq]
    exact ((h1.inter h2).inter h3).inter h4
  have hbox : IsCompact ((Set.Icc b 1 ×ˢ Set.Icc c1 c2) ×ˢ Set.Icc (b / 2) 1) :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  refine IsCompact.of_isClosed_subset hbox hclosed ?_
  unfold ktextRegion
  intro q hq
  exact ⟨⟨hq.1, hq.2.1⟩, hq.2.2.1, le_trans hq.2.2.2 hq.1.2⟩

lemma ktextRegion_pos {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b c1 c2 : ℝ} (hb : 0 < b)
    (hct : ∀ t ∈ Set.Icc c1 c2, (1 / 5 : ℝ) ≤ |t|) :
    ∀ q ∈ ktextRegion b c1 c2, 0 < Work.OddVolterra.krad h q.1.1 q.1.2 q.2 := by
  intro q hq
  unfold ktextRegion at hq
  exact krad_pos_state_region hsupp hsmall (by linarith : 0 < b / 2) hq.2.2.1 hq.2.2.2 hq.1.2
    (hct q.1.2 hq.2.1)

lemma contDiffOn_k1v (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ ∞ (k1v n h) (Work.OddVolterra.extGood h) :=
  Work.OddVolterra.contDiffOn_k1ext n hh

lemma contDiffOn_k2v (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ ∞ (k2v n h) (Work.OddVolterra.extGood h) :=
  Work.OddVolterra.contDiffOn_k2ext n hh

lemma contDiffOn_k1d (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ ∞ (k1d n h) (Work.OddVolterra.extGood h) :=
  Work.OddVolterra.contDiffOn_deriv_snd_gen (Work.OddVolterra.isOpen_extGood h hh)
    (Work.OddVolterra.contDiffOn_k1ext n hh)

lemma contDiffOn_k2d (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ ∞ (k2d n h) (Work.OddVolterra.extGood h) :=
  Work.OddVolterra.contDiffOn_deriv_snd_gen (Work.OddVolterra.isOpen_extGood h hh)
    (Work.OddVolterra.contDiffOn_k2ext n hh)

lemma fderiv_k1d_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ ∞ (fderiv ℝ (k1d n h)) (Work.OddVolterra.extGood h) :=
  (contDiffOn_k1d n hh).fderiv_of_isOpen (Work.OddVolterra.isOpen_extGood h hh) (by simp)

lemma fderiv_k2d_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ ∞ (fderiv ℝ (k2d n h)) (Work.OddVolterra.extGood h) :=
  (contDiffOn_k2d n hh).fderiv_of_isOpen (Work.OddVolterra.isOpen_extGood h hh) (by simp)

lemma k1d_differentiableOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    DifferentiableOn ℝ (k1d n h) (Work.OddVolterra.extGood h) :=
  (contDiffOn_k1d n hh).differentiableOn (by simp)

lemma k2d_differentiableOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    DifferentiableOn ℝ (k2d n h) (Work.OddVolterra.extGood h) :=
  (contDiffOn_k2d n hh).differentiableOn (by simp)

lemma norm_pair_sub (σ t t' a : ℝ) :
    ‖(((σ, t), a) : (ℝ × ℝ) × ℝ) - ((σ, t'), a)‖ = |t - t'| := by
  have heq : (((σ, t), a) : (ℝ × ℝ) × ℝ) - ((σ, t'), a) = ((0, t - t'), (0 : ℝ)) := by
    ext <;> simp
  rw [heq, Prod.norm_def, Prod.norm_def]
  simp

/-- **The kernel data on a compact trapezium of slopes.**  If `1/5 ≤ |t|` on the `t`-interval
`[c1,c2]`, then on the trapezium `b/2 ≤ a ≤ σ ≤ 1`, `t ∈ [c1,c2]` the manifest Abel kernels
`k1v`, `k2v` and their first `a`-derivatives `k1d`, `k2d` are bounded by `K`, and the
`a`-derivative fields are `B`-Lipschitz in `t`. -/
theorem ktext_data (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b c1 c2 : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hc12 : c1 ≤ c2)
    (hct : ∀ t ∈ Set.Icc c1 c2, (1 / 5 : ℝ) ≤ |t|) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ σ ∈ Set.Icc b 1, ∀ a ∈ Set.Ico (b / 2) σ, ∀ t ∈ Set.Icc c1 c2,
        |k1v n h ((σ, t), a)| ≤ K ∧ |k2v n h ((σ, t), a)| ≤ K ∧
        |k1d n h ((σ, t), a)| ≤ K ∧ |k2d n h ((σ, t), a)| ≤ K ∧
        (∀ t' ∈ Set.Icc c1 c2,
          |k1d n h ((σ, t), a) - k1d n h ((σ, t'), a)| ≤ B * |t - t'|) ∧
        (∀ t' ∈ Set.Icc c1 c2,
          |k2d n h ((σ, t), a) - k2d n h ((σ, t'), a)| ≤ B * |t - t'|) := by
  have hRsub : ktextRegion b c1 c2 ⊆ Work.OddVolterra.extGood h :=
    ktextRegion_pos hsupp hsmall hb hct
  have hRc := ktextRegion_compact b c1 c2
  have hRconv := ktextRegion_convex b c1 c2
  obtain ⟨Kv1, hKv1⟩ := hRc.exists_bound_of_continuousOn
    ((contDiffOn_k1v n hh).continuousOn.mono hRsub)
  obtain ⟨Kv2, hKv2⟩ := hRc.exists_bound_of_continuousOn
    ((contDiffOn_k2v n hh).continuousOn.mono hRsub)
  obtain ⟨Kd1, hKd1⟩ := hRc.exists_bound_of_continuousOn
    ((contDiffOn_k1d n hh).continuousOn.mono hRsub)
  obtain ⟨Kd2, hKd2⟩ := hRc.exists_bound_of_continuousOn
    ((contDiffOn_k2d n hh).continuousOn.mono hRsub)
  obtain ⟨Bb1, hBb1⟩ := hRc.exists_bound_of_continuousOn
    ((fderiv_k1d_contDiffOn n hh).continuousOn.mono hRsub)
  obtain ⟨Bb2, hBb2⟩ := hRc.exists_bound_of_continuousOn
    ((fderiv_k2d_contDiffOn n hh).continuousOn.mono hRsub)
  have hdiff1 : ∀ q ∈ ktextRegion b c1 c2, DifferentiableAt ℝ (k1d n h) q :=
    fun q hq => (k1d_differentiableOn n hh).differentiableAt
      ((Work.OddVolterra.isOpen_extGood h hh).mem_nhds (hRsub hq))
  have hdiff2 : ∀ q ∈ ktextRegion b c1 c2, DifferentiableAt ℝ (k2d n h) q :=
    fun q hq => (k2d_differentiableOn n hh).differentiableAt
      ((Work.OddVolterra.isOpen_extGood h hh).mem_nhds (hRsub hq))
  refine ⟨max 1 (max (max Kv1 Kv2) (max Kd1 Kd2)), max 1 (max Bb1 Bb2),
    lt_of_lt_of_le one_pos (le_max_left _ _), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro σ hσ a ha t ht
  have hq : ((σ, t), a) ∈ ktextRegion b c1 c2 := ⟨hσ, ht, ⟨ha.1, le_of_lt ha.2⟩⟩
  have hle1 : Kv1 ≤ max 1 (max (max Kv1 Kv2) (max Kd1 Kd2)) :=
    le_trans (le_max_left Kv1 Kv2)
      (le_trans (le_max_left (max Kv1 Kv2) (max Kd1 Kd2)) (le_max_right _ _))
  have hle2 : Kv2 ≤ max 1 (max (max Kv1 Kv2) (max Kd1 Kd2)) :=
    le_trans (le_max_right Kv1 Kv2)
      (le_trans (le_max_left (max Kv1 Kv2) (max Kd1 Kd2)) (le_max_right _ _))
  have hle3 : Kd1 ≤ max 1 (max (max Kv1 Kv2) (max Kd1 Kd2)) :=
    le_trans (le_max_left Kd1 Kd2)
      (le_trans (le_max_right (max Kv1 Kv2) (max Kd1 Kd2)) (le_max_right _ _))
  have hle4 : Kd2 ≤ max 1 (max (max Kv1 Kv2) (max Kd1 Kd2)) :=
    le_trans (le_max_right Kd1 Kd2)
      (le_trans (le_max_right (max Kv1 Kv2) (max Kd1 Kd2)) (le_max_right _ _))
  have hleB1 : Bb1 ≤ max 1 (max Bb1 Bb2) :=
    le_trans (le_max_left Bb1 Bb2) (le_max_right _ _)
  have hleB2 : Bb2 ≤ max 1 (max Bb1 Bb2) :=
    le_trans (le_max_right Bb1 Bb2) (le_max_right _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Real.norm_eq_abs]; exact le_trans (hKv1 _ hq) hle1
  · rw [← Real.norm_eq_abs]; exact le_trans (hKv2 _ hq) hle2
  · rw [← Real.norm_eq_abs]; exact le_trans (hKd1 _ hq) hle3
  · rw [← Real.norm_eq_abs]; exact le_trans (hKd2 _ hq) hle4
  · intro t' ht'
    have hq' : ((σ, t'), a) ∈ ktextRegion b c1 c2 := ⟨hσ, ht', ⟨ha.1, le_of_lt ha.2⟩⟩
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff1
      (fun q hq => le_trans (hBb1 q hq) hleB1) hRconv hq' hq
    rw [norm_pair_sub σ t t' a, Real.norm_eq_abs] at hmv
    exact hmv
  · intro t' ht'
    have hq' : ((σ, t'), a) ∈ ktextRegion b c1 c2 := ⟨hσ, ht', ⟨ha.1, le_of_lt ha.2⟩⟩
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff2
      (fun q hq => le_trans (hBb2 q hq) hleB2) hRconv hq' hq
    rw [norm_pair_sub σ t t' a, Real.norm_eq_abs] at hmv
    exact hmv

/-- The positive-`t` instance of `ktext_data`: `t ∈ [1/5, 2]`. -/
theorem ktext_data_pos (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ σ ∈ Set.Icc b 1, ∀ a ∈ Set.Ico (b / 2) σ, ∀ t ∈ Set.Icc (1 / 5 : ℝ) 2,
        |k1v n h ((σ, t), a)| ≤ K ∧ |k2v n h ((σ, t), a)| ≤ K ∧
        |k1d n h ((σ, t), a)| ≤ K ∧ |k2d n h ((σ, t), a)| ≤ K ∧
        (∀ t' ∈ Set.Icc (1 / 5 : ℝ) 2,
          |k1d n h ((σ, t), a) - k1d n h ((σ, t'), a)| ≤ B * |t - t'|) ∧
        (∀ t' ∈ Set.Icc (1 / 5 : ℝ) 2,
          |k2d n h ((σ, t), a) - k2d n h ((σ, t'), a)| ≤ B * |t - t'|) :=
  ktext_data n hn hh hsupp hsmall hb hb1 (by norm_num) (fun t ht => by
    rw [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t)]; exact ht.1)

/-- The negative-`t` instance of `ktext_data`: `t ∈ [-2, -1/5]`. -/
theorem ktext_data_neg (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ σ ∈ Set.Icc b 1, ∀ a ∈ Set.Ico (b / 2) σ, ∀ t ∈ Set.Icc (-2 : ℝ) (-1 / 5),
        |k1v n h ((σ, t), a)| ≤ K ∧ |k2v n h ((σ, t), a)| ≤ K ∧
        |k1d n h ((σ, t), a)| ≤ K ∧ |k2d n h ((σ, t), a)| ≤ K ∧
        (∀ t' ∈ Set.Icc (-2 : ℝ) (-1 / 5),
          |k1d n h ((σ, t), a) - k1d n h ((σ, t'), a)| ≤ B * |t - t'|) ∧
        (∀ t' ∈ Set.Icc (-2 : ℝ) (-1 / 5),
          |k2d n h ((σ, t), a) - k2d n h ((σ, t'), a)| ≤ B * |t - t'|) :=
  ktext_data n hn hh hsupp hsmall hb hb1 (by norm_num) (fun t ht => by
    rw [abs_of_nonpos (by linarith [ht.2] : t ≤ 0)]; linarith [ht.2])

/-! ## Transfer to the paper's kernels and the state-independent `Kvec` data -/

/-- The `a`-derivative of the paper's first kernel agrees with the manifest `a`-derivative field
off the diagonal, where the Abel denominator is positive. -/
lemma deriv_K1_eq_k1d (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a σ t : ℝ}
    (ha : a < σ) (hR : 0 < Work.OddVolterra.krad h σ t a) :
    deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ t) a = k1d n h ((σ, t), a) := by
  rw [k1d_apply]
  refine Filter.EventuallyEq.deriv_eq ?_
  have hnhds : {u : ℝ | u < σ ∧ 0 < Work.OddVolterra.krad h σ t u} ∈ 𝓝 a :=
    ((isOpen_lt continuous_id continuous_const).inter
      (isOpen_lt continuous_const (Work.OddVolterra.continuous_krad hh σ t))).mem_nhds
        ⟨ha, hR⟩
  filter_upwards [hnhds] with u hu
  exact Work.OddVolterra.K1_eq_k1ext hh n hu.1 hu.2

/-- The `a`-derivative of the paper's second kernel agrees with the manifest `a`-derivative field
off the diagonal, where the Abel denominator is positive. -/
lemma deriv_K2_eq_k2d (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a σ t : ℝ}
    (ha : a < σ) (hR : 0 < Work.OddVolterra.krad h σ t a) :
    deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ t) a = k2d n h ((σ, t), a) := by
  rw [k2d_apply]
  refine Filter.EventuallyEq.deriv_eq ?_
  have hnhds : {u : ℝ | u < σ ∧ 0 < Work.OddVolterra.krad h σ t u} ∈ 𝓝 a :=
    ((isOpen_lt continuous_id continuous_const).inter
      (isOpen_lt continuous_const (Work.OddVolterra.continuous_krad hh σ t))).mem_nhds
        ⟨ha, hR⟩
  filter_upwards [hnhds] with u hu
  exact Work.OddVolterra.K2_eq_k2ext hh n hn hu.1 hu.2

lemma abs_mul_sub_mul_le {B K δ ε x x' c c' : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hxx : |x - x'| ≤ B * δ) (hx : |x'| ≤ K) (hc : |c| ≤ 2) (hcc : |c - c'| ≤ ε) :
    |x * c - x' * c'| ≤ 2 * B * δ + K * ε := by
  have h1 : x * c - x' * c' = (x - x') * c + x' * (c - c') := by ring
  rw [h1]
  calc |(x - x') * c + x' * (c - c')| ≤ |(x - x') * c| + |x' * (c - c')| := abs_add_le _ _
    _ = |x - x'| * |c| + |x'| * |c - c'| := by rw [abs_mul, abs_mul]
    _ ≤ (B * δ) * 2 + K * ε := add_le_add
        (mul_le_mul hxx hc (abs_nonneg _) (le_trans (abs_nonneg _) hxx))
        (mul_le_mul hx hcc (abs_nonneg _) hK)
    _ = 2 * B * δ + K * ε := by ring

/-- **Uniform data for the paper's kernel `Kvec` and its first-argument derivative on the state
region.**  The constant `Cm` bounds `Kvec` and `∂_a Kvec` on the trapezium
`b/2 ≤ a ≤ σ ≤ 1` for every state in the box `z 0, z 1 ≥ 1/5`, `|z i| ≤ 2`, and `Bs` is a uniform
Lipschitz constant in the state of the `a`-derivative field. -/
lemma kvec_state_data (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ Cm Bs : ℝ, 0 < Cm ∧ 0 < Bs ∧
      (∀ σ ∈ Set.Icc b 1, ∀ a ∈ Set.Ico (b / 2) σ, ∀ z : Work.OddVolterra.St,
        (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
        ‖Work.OddVolterra.Kvec n h a σ (z 0) (z 1) (z 2) (z 3)‖ ≤ Cm ∧
        ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a‖
          ≤ Cm) ∧
      (∀ σ ∈ Set.Icc b 1, ∀ a ∈ Set.Ico (b / 2) σ, ∀ z z' : Work.OddVolterra.St,
        (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
        (1 / 5 : ℝ) ≤ z' 0 → (1 / 5 : ℝ) ≤ z' 1 → (∀ i : Fin 4, |z' i| ≤ 2) →
        ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a
          - deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) a‖
          ≤ Bs * ‖z - z'‖) := by
  obtain ⟨Kp, Bp, hKp, hBp, hdatap⟩ := ktext_data_pos n hn hh hsupp hsmall hb hb1
  obtain ⟨Kn, Bn, hKn, hBn, hdatan⟩ := ktext_data_neg n hn hh hsupp hsmall hb hb1
  set K : ℝ := max Kp Kn with hKdef
  set B : ℝ := max Bp Bn with hBdef
  have hKpos : 0 < K := lt_of_lt_of_le hKp (le_max_left _ _)
  have hBpos : 0 < B := lt_of_lt_of_le hBp (le_max_left _ _)
  have hKpn : Kp ≤ K := le_max_left _ _
  have hKnn : Kn ≤ K := le_max_right _ _
  have hBpn : Bp ≤ B := le_max_left _ _
  have hBnn : Bn ≤ B := le_max_right _ _
  refine ⟨4 * K + 1, 4 * B + 2 * K, by positivity, by positivity, ?_, ?_⟩
  · intro σ hσ a ha z hz0 hz1 hzb
    have hz0' : 0 < z 0 := lt_of_lt_of_le (by norm_num) hz0
    have hz1' : 0 < z 1 := lt_of_lt_of_le (by norm_num) hz1
    have hkradn : 0 < Work.OddVolterra.krad h σ (-(z 0)) a :=
      krad_pos_state_region hsupp hsmall (by linarith : 0 < b / 2) ha.1 (le_of_lt ha.2) hσ.2
        (by rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ z 0)]; exact hz0)
    have hkradp : 0 < Work.OddVolterra.krad h σ (z 1) a :=
      krad_pos_state_region hsupp hsmall (by linarith : 0 < b / 2) ha.1 (le_of_lt ha.2) hσ.2
        (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z 1)]; exact hz1)
    have htn : (-(z 0)) ∈ Set.Icc (-2 : ℝ) (-1 / 5) :=
      ⟨by linarith [(abs_le.mp (hzb 0)).2], by linarith⟩
    have htp : z 1 ∈ Set.Icc (1 / 5 : ℝ) 2 :=
      ⟨hz1, by linarith [(abs_le.mp (hzb 1)).2]⟩
    have hKn1 : |k1v n h ((σ, -(z 0)), a)| ≤ K :=
      le_trans ((hdatan σ hσ a ha (-(z 0)) htn).1) hKnn
    have hKn2 : |k2v n h ((σ, -(z 0)), a)| ≤ K :=
      le_trans ((hdatan σ hσ a ha (-(z 0)) htn).2.1) hKnn
    have hKn3 : |k1d n h ((σ, -(z 0)), a)| ≤ K :=
      le_trans ((hdatan σ hσ a ha (-(z 0)) htn).2.2.1) hKnn
    have hKn4 : |k2d n h ((σ, -(z 0)), a)| ≤ K :=
      le_trans ((hdatan σ hσ a ha (-(z 0)) htn).2.2.2.1) hKnn
    have hKp1 : |k1v n h ((σ, z 1), a)| ≤ K :=
      le_trans ((hdatap σ hσ a ha (z 1) htp).1) hKpn
    have hKp2 : |k2v n h ((σ, z 1), a)| ≤ K :=
      le_trans ((hdatap σ hσ a ha (z 1) htp).2.1) hKpn
    have hKp3 : |k1d n h ((σ, z 1), a)| ≤ K :=
      le_trans ((hdatap σ hσ a ha (z 1) htp).2.2.1) hKpn
    have hKp4 : |k2d n h ((σ, z 1), a)| ≤ K :=
      le_trans ((hdatap σ hσ a ha (z 1) htp).2.2.2.1) hKpn
    have hK1n : |Work.OddVolterra.K1 n h a σ (-(z 0))| ≤ K := by
      rw [Work.OddVolterra.K1_eq_k1ext hh n ha.2 hkradn, ← k1v_apply]; exact hKn1
    have hK2n : |Work.OddVolterra.K2 n h a σ (-(z 0))| ≤ K := by
      rw [Work.OddVolterra.K2_eq_k2ext hh n hn ha.2 hkradn, ← k2v_apply]; exact hKn2
    have hK1p : |Work.OddVolterra.K1 n h a σ (z 1)| ≤ K := by
      rw [Work.OddVolterra.K1_eq_k1ext hh n ha.2 hkradp, ← k1v_apply]; exact hKp1
    have hK2p : |Work.OddVolterra.K2 n h a σ (z 1)| ≤ K := by
      rw [Work.OddVolterra.K2_eq_k2ext hh n hn ha.2 hkradp, ← k2v_apply]; exact hKp2
    have hd1n : |deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (-(z 0))) a| ≤ K := by
      rw [deriv_K1_eq_k1d n hh ha.2 hkradn]; exact hKn3
    have hd2n : |deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (-(z 0))) a| ≤ K := by
      rw [deriv_K2_eq_k2d n hn hh ha.2 hkradn]; exact hKn4
    have hd1p : |deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (z 1)) a| ≤ K := by
      rw [deriv_K1_eq_k1d n hh ha.2 hkradp]; exact hKp3
    have hd2p : |deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (z 1)) a| ≤ K := by
      rw [deriv_K2_eq_k2d n hn hh ha.2 hkradp]; exact hKp4
    have hKval : ∀ x y : ℝ, |x| ≤ K → |y| ≤ K → |x * z 2 + y * z 3| ≤ 4 * K := by
      intro x y hx hy
      have h2 : |z 2| ≤ 2 := hzb 2
      have h3 : |z 3| ≤ 2 := hzb 3
      have hx2 : |x * z 2| ≤ K * 2 := by
        rw [abs_mul]
        exact mul_le_mul hx h2 (abs_nonneg _) (le_trans (abs_nonneg x) hx)
      have hy2 : |y * z 3| ≤ K * 2 := by
        rw [abs_mul]
        exact mul_le_mul hy h3 (abs_nonneg _) (le_trans (abs_nonneg y) hy)
      calc |x * z 2 + y * z 3| ≤ |x * z 2| + |y * z 3| := abs_add_le _ _
        _ ≤ K * 2 + K * 2 := add_le_add hx2 hy2
        _ = 4 * K := by ring
    have hh0 : |-(Work.OddVolterra.K1 n h a σ (-(z 0)) * z 2
        + Work.OddVolterra.K1 n h a σ (z 1) * z 3)| ≤ 4 * K + 1 := by
      rw [abs_neg]
      linarith [hKval _ _ hK1n hK1p]
    have hh1 : |-(Work.OddVolterra.K2 n h a σ (-(z 0)) * z 2
        + Work.OddVolterra.K2 n h a σ (z 1) * z 3)| ≤ 4 * K + 1 := by
      rw [abs_neg]
      linarith [hKval _ _ hK2n hK2p]
    have hdv0 : |-(deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (-(z 0))) a * z 2
        + deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (z 1)) a * z 3)| ≤ 4 * K + 1 := by
      rw [abs_neg]
      linarith [hKval _ _ hd1n hd1p]
    have hdv1 : |-(deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (-(z 0))) a * z 2
        + deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (z 1)) a * z 3)| ≤ 4 * K + 1 := by
      rw [abs_neg]
      linarith [hKval _ _ hd2n hd2p]
    constructor
    · rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      fin_cases i
      · simpa [Work.OddVolterra.Kvec] using hh0
      · simpa [Work.OddVolterra.Kvec] using hh1
    · rw [deriv_Kvec_eq n hn hh z ha.2 hkradn hkradp]
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      fin_cases i
      · simpa using hdv0
      · simpa using hdv1
  · intro σ hσ a ha z z' hz0 hz1 hzb hz'0 hz'1 hz'b
    have hkradn : 0 < Work.OddVolterra.krad h σ (-(z 0)) a :=
      krad_pos_state_region hsupp hsmall (by linarith : 0 < b / 2) ha.1 (le_of_lt ha.2) hσ.2
        (by rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ z 0)]; exact hz0)
    have hkradn' : 0 < Work.OddVolterra.krad h σ (-(z' 0)) a :=
      krad_pos_state_region hsupp hsmall (by linarith : 0 < b / 2) ha.1 (le_of_lt ha.2) hσ.2
        (by rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ z' 0)]; exact hz'0)
    have hkradp : 0 < Work.OddVolterra.krad h σ (z 1) a :=
      krad_pos_state_region hsupp hsmall (by linarith : 0 < b / 2) ha.1 (le_of_lt ha.2) hσ.2
        (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z 1)]; exact hz1)
    have hkradp' : 0 < Work.OddVolterra.krad h σ (z' 1) a :=
      krad_pos_state_region hsupp hsmall (by linarith : 0 < b / 2) ha.1 (le_of_lt ha.2) hσ.2
        (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z' 1)]; exact hz'1)
    have htn : (-(z 0)) ∈ Set.Icc (-2 : ℝ) (-1 / 5) :=
      ⟨by linarith [(abs_le.mp (hzb 0)).2], by linarith⟩
    have htn' : (-(z' 0)) ∈ Set.Icc (-2 : ℝ) (-1 / 5) :=
      ⟨by linarith [(abs_le.mp (hz'b 0)).2], by linarith⟩
    have htp : z 1 ∈ Set.Icc (1 / 5 : ℝ) 2 :=
      ⟨hz1, by linarith [(abs_le.mp (hzb 1)).2]⟩
    have htp' : z' 1 ∈ Set.Icc (1 / 5 : ℝ) 2 :=
      ⟨hz'1, by linarith [(abs_le.mp (hz'b 1)).2]⟩
    have hdiff : ∀ i : Fin 4, |z i - z' i| ≤ ‖z - z'‖ := by
      intro i
      have h := dist_le_pi_dist z z' i
      rwa [Real.dist_eq] at h
    -- the four Lipschitz slots
    have hLn : |k1d n h ((σ, -(z 0)), a)
        - k1d n h ((σ, -(z' 0)), a)|
        ≤ B * |(z 0) - (z' 0)| := by
      have h := (hdatan σ hσ a ha (-(z 0)) htn).2.2.2.2.1 (-(z' 0)) htn'
      refine le_trans h ?_
      rw [neg_sub_neg, abs_sub_comm]
      exact mul_le_mul_of_nonneg_right hBnn (abs_nonneg _)
    have hLp : |k1d n h ((σ, z 1), a)
        - k1d n h ((σ, z' 1), a)| ≤ B * |z 1 - z' 1| := by
      have h := (hdatap σ hσ a ha (z 1) htp).2.2.2.2.1 (z' 1) htp'
      exact le_trans h (mul_le_mul_of_nonneg_right hBpn (abs_nonneg _))
    have hMn : |k2d n h ((σ, -(z 0)), a)
        - k2d n h ((σ, -(z' 0)), a)|
        ≤ B * |(z 0) - (z' 0)| := by
      have h := (hdatan σ hσ a ha (-(z 0)) htn).2.2.2.2.2 (-(z' 0)) htn'
      refine le_trans h ?_
      rw [neg_sub_neg, abs_sub_comm]
      exact mul_le_mul_of_nonneg_right hBnn (abs_nonneg _)
    have hMp : |k2d n h ((σ, z 1), a)
        - k2d n h ((σ, z' 1), a)| ≤ B * |z 1 - z' 1| := by
      have h := (hdatap σ hσ a ha (z 1) htp).2.2.2.2.2 (z' 1) htp'
      exact le_trans h (mul_le_mul_of_nonneg_right hBpn (abs_nonneg _))
    -- rewrite the derivatives
    have htr1 : deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (-(z 0))) a
        = k1d n h ((σ, -(z 0)), a) := deriv_K1_eq_k1d n hh ha.2 hkradn
    have htr1' : deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (-(z' 0))) a
        = k1d n h ((σ, -(z' 0)), a) := deriv_K1_eq_k1d n hh ha.2 hkradn'
    have htr2 : deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (-(z 0))) a
        = k2d n h ((σ, -(z 0)), a) := deriv_K2_eq_k2d n hn hh ha.2 hkradn
    have htr2' : deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (-(z' 0))) a
        = k2d n h ((σ, -(z' 0)), a) := deriv_K2_eq_k2d n hn hh ha.2 hkradn'
    have htr3 : deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (z 1)) a
        = k1d n h ((σ, z 1), a) := deriv_K1_eq_k1d n hh ha.2 hkradp
    have htr3' : deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (z' 1)) a
        = k1d n h ((σ, z' 1), a) := deriv_K1_eq_k1d n hh ha.2 hkradp'
    have htr4 : deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (z 1)) a
        = k2d n h ((σ, z 1), a) := deriv_K2_eq_k2d n hn hh ha.2 hkradp
    have htr4' : deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (z' 1)) a
        = k2d n h ((σ, z' 1), a) := deriv_K2_eq_k2d n hn hh ha.2 hkradp'
    have hvaln : ∀ t ∈ Set.Icc (-2 : ℝ) (-1 / 5), |k1d n h ((σ, t), a)| ≤ K :=
      fun t ht => le_trans ((hdatan σ hσ a ha t ht).2.2.1) hKnn
    have hvalp : ∀ t ∈ Set.Icc (1 / 5 : ℝ) 2, |k1d n h ((σ, t), a)| ≤ K :=
      fun t ht => le_trans ((hdatap σ hσ a ha t ht).2.2.1) hKpn
    have hvaln2 : ∀ t ∈ Set.Icc (-2 : ℝ) (-1 / 5), |k2d n h ((σ, t), a)| ≤ K :=
      fun t ht => le_trans ((hdatan σ hσ a ha t ht).2.2.2.1) hKnn
    have hvalp2 : ∀ t ∈ Set.Icc (1 / 5 : ℝ) 2, |k2d n h ((σ, t), a)| ≤ K :=
      fun t ht => le_trans ((hdatap σ hσ a ha t ht).2.2.2.1) hKpn
    have hstep1 : |k1d n h ((σ, -(z 0)), a) * z 2
        - k1d n h ((σ, -(z' 0)), a) * z' 2| ≤ (2 * B + K) * ‖z - z'‖ := by
      have h1 := abs_mul_sub_mul_le (B := B) (K := K) (δ := |z 0 - z' 0|) (ε := ‖z - z'‖)
        hBpos.le hKpos.le hLn ((hvaln (-(z' 0)) htn')) (hzb 2) (hdiff 2)
      calc |k1d n h ((σ, -(z 0)), a) * z 2
            - k1d n h ((σ, -(z' 0)), a) * z' 2|
          ≤ 2 * B * |z 0 - z' 0| + K * ‖z - z'‖ := h1
        _ ≤ 2 * B * ‖z - z'‖ + K * ‖z - z'‖ := by
            refine add_le_add ?_ le_rfl
            exact mul_le_mul_of_nonneg_left (hdiff 0) (by linarith [hBpos])
        _ = (2 * B + K) * ‖z - z'‖ := by ring
    have hstep2 : |k1d n h ((σ, z 1), a) * z 3
        - k1d n h ((σ, z' 1), a) * z' 3| ≤ (2 * B + K) * ‖z - z'‖ := by
      have h1 := abs_mul_sub_mul_le (B := B) (K := K) (δ := |z 1 - z' 1|) (ε := ‖z - z'‖)
        hBpos.le hKpos.le hLp ((hvalp (z' 1) htp')) (hzb 3) (hdiff 3)
      calc |k1d n h ((σ, z 1), a) * z 3
            - k1d n h ((σ, z' 1), a) * z' 3|
          ≤ 2 * B * |z 1 - z' 1| + K * ‖z - z'‖ := h1
        _ ≤ 2 * B * ‖z - z'‖ + K * ‖z - z'‖ := by
            refine add_le_add ?_ le_rfl
            exact mul_le_mul_of_nonneg_left (hdiff 1) (by linarith [hBpos])
        _ = (2 * B + K) * ‖z - z'‖ := by ring
    have hstep3 : |k2d n h ((σ, -(z 0)), a) * z 2
        - k2d n h ((σ, -(z' 0)), a) * z' 2| ≤ (2 * B + K) * ‖z - z'‖ := by
      have h1 := abs_mul_sub_mul_le (B := B) (K := K) (δ := |z 0 - z' 0|) (ε := ‖z - z'‖)
        hBpos.le hKpos.le hMn ((hvaln2 (-(z' 0)) htn')) (hzb 2) (hdiff 2)
      calc |k2d n h ((σ, -(z 0)), a) * z 2
            - k2d n h ((σ, -(z' 0)), a) * z' 2|
          ≤ 2 * B * |z 0 - z' 0| + K * ‖z - z'‖ := h1
        _ ≤ 2 * B * ‖z - z'‖ + K * ‖z - z'‖ := by
            refine add_le_add ?_ le_rfl
            exact mul_le_mul_of_nonneg_left (hdiff 0) (by linarith [hBpos])
        _ = (2 * B + K) * ‖z - z'‖ := by ring
    have hstep4 : |k2d n h ((σ, z 1), a) * z 3
        - k2d n h ((σ, z' 1), a) * z' 3| ≤ (2 * B + K) * ‖z - z'‖ := by
      have h1 := abs_mul_sub_mul_le (B := B) (K := K) (δ := |z 1 - z' 1|) (ε := ‖z - z'‖)
        hBpos.le hKpos.le hMp ((hvalp2 (z' 1) htp')) (hzb 3) (hdiff 3)
      calc |k2d n h ((σ, z 1), a) * z 3
            - k2d n h ((σ, z' 1), a) * z' 3|
          ≤ 2 * B * |z 1 - z' 1| + K * ‖z - z'‖ := h1
        _ ≤ 2 * B * ‖z - z'‖ + K * ‖z - z'‖ := by
            refine add_le_add ?_ le_rfl
            exact mul_le_mul_of_nonneg_left (hdiff 1) (by linarith [hBpos])
        _ = (2 * B + K) * ‖z - z'‖ := by ring
    have hdz : deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a
        = ![ - (k1d n h ((σ, -(z 0)), a) * z 2
                + k1d n h ((σ, z 1), a) * z 3),
              - (k2d n h ((σ, -(z 0)), a) * z 2
                + k2d n h ((σ, z 1), a) * z 3) ] := by
      rw [deriv_Kvec_eq n hn hh z ha.2 hkradn hkradp]
      rw [htr1, htr3, htr2, htr4]
    have hdz' : deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) a
        = ![ - (k1d n h ((σ, -(z' 0)), a) * z' 2
                + k1d n h ((σ, z' 1), a) * z' 3),
              - (k2d n h ((σ, -(z' 0)), a) * z' 2
                + k2d n h ((σ, z' 1), a) * z' 3) ] := by
      rw [deriv_Kvec_eq n hn hh z' ha.2 hkradn' hkradp']
      rw [htr1', htr3', htr2', htr4']
    have hcomp : ∀ i : Fin 2,
        ‖(deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a
          - deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) a) i‖
          ≤ (4 * B + 2 * K) * ‖z - z'‖ := by
      intro i
      rw [hdz, hdz']
      fin_cases i
      · have h0 : |-(k1d n h ((σ, -(z 0)), a) * z 2 + k1d n h ((σ, z 1), a) * z 3)
            - -(k1d n h ((σ, -(z' 0)), a) * z' 2 + k1d n h ((σ, z' 1), a) * z' 3)|
            ≤ (4 * B + 2 * K) * ‖z - z'‖ := by
          rw [show -(k1d n h ((σ, -(z 0)), a) * z 2 + k1d n h ((σ, z 1), a) * z 3)
              - -(k1d n h ((σ, -(z' 0)), a) * z' 2 + k1d n h ((σ, z' 1), a) * z' 3)
              = -((k1d n h ((σ, -(z 0)), a) * z 2 - k1d n h ((σ, -(z' 0)), a) * z' 2)
                + (k1d n h ((σ, z 1), a) * z 3 - k1d n h ((σ, z' 1), a) * z' 3)) by ring,
            abs_neg]
          exact le_trans (abs_add_le _ _) (by linarith [hstep1, hstep2])
        simpa [Real.norm_eq_abs] using h0
      · have h0 : |-(k2d n h ((σ, -(z 0)), a) * z 2 + k2d n h ((σ, z 1), a) * z 3)
            - -(k2d n h ((σ, -(z' 0)), a) * z' 2 + k2d n h ((σ, z' 1), a) * z' 3)|
            ≤ (4 * B + 2 * K) * ‖z - z'‖ := by
          rw [show -(k2d n h ((σ, -(z 0)), a) * z 2 + k2d n h ((σ, z 1), a) * z 3)
              - -(k2d n h ((σ, -(z' 0)), a) * z' 2 + k2d n h ((σ, z' 1), a) * z' 3)
              = -((k2d n h ((σ, -(z 0)), a) * z 2 - k2d n h ((σ, -(z' 0)), a) * z' 2)
                + (k2d n h ((σ, z 1), a) * z 3 - k2d n h ((σ, z' 1), a) * z' 3)) by ring,
            abs_neg]
          exact le_trans (abs_add_le _ _) (by linarith [hstep3, hstep4])
        simpa [Real.norm_eq_abs] using h0
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    exact hcomp

/-! ## The `τ`-integrand of the `s`-derivative of `G₂` in a constant state -/

/-- The scalar `τ`-integrand of the `s`-derivative of the `i`-th component of `G₂` at the state
`w`: `(√(τ(1-τ)))⁻¹ (1-τ) ∂_a (Kvec ·)_i`. -/
def thetaI (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (i : Fin 2) (w : Work.OddVolterra.St) (τ : ℝ) : ℝ :=
  (Real.sqrt (τ * (1 - τ)))⁻¹ *
    ((1 - τ) * ((deriv (fun u : ℝ =>
      Work.OddVolterra.Kvec n h u σ (w 0) (w 1) (w 2) (w 3)) (s + τ * (σ - s))) i))

@[simp] lemma thetaI_apply (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (i : Fin 2)
    (w : Work.OddVolterra.St) (τ : ℝ) :
    thetaI n h s σ i w τ = (Real.sqrt (τ * (1 - τ)))⁻¹ *
      ((1 - τ) * ((deriv (fun u : ℝ =>
        Work.OddVolterra.Kvec n h u σ (w 0) (w 1) (w 2) (w 3)) (s + τ * (σ - s))) i)) := rfl

lemma thetaI_aestronglyMeasurable (n : ℕ) {h : ℝ → ℝ} (s σ : ℝ) (i : Fin 2)
    (w : Work.OddVolterra.St) :
    AEStronglyMeasurable (thetaI n h s σ i w) (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
  refine Measurable.aestronglyMeasurable ?_
  have hm : Measurable (fun τ : ℝ => (deriv (fun u : ℝ =>
      Work.OddVolterra.Kvec n h u σ (w 0) (w 1) (w 2) (w 3)) (s + τ * (σ - s))) i) :=
    (measurable_pi_apply i).comp ((measurable_deriv (𝕜 := ℝ) (fun u : ℝ =>
      Work.OddVolterra.Kvec n h u σ (w 0) (w 1) (w 2) (w 3))).comp
        (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s)))
  have hw : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
    (Real.continuous_sqrt.measurable.comp
      (measurable_id.mul (measurable_const.sub measurable_id))).inv
  exact hw.mul ((measurable_const.sub measurable_id).mul hm)

/-- The pointwise bound on the `τ`-integrand coming from the uniform `Kvec` data. -/
lemma thetaI_bound (n : ℕ) {h : ℝ → ℝ} {b Cm : ℝ}
    (hval : ∀ σ ∈ Set.Icc b 1, ∀ a ∈ Set.Ico (b / 2) σ, ∀ z : Work.OddVolterra.St,
      (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
      ‖Work.OddVolterra.Kvec n h a σ (z 0) (z 1) (z 2) (z 3)‖ ≤ Cm ∧
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ Cm)
    {s σ : ℝ} (hb : 0 < b) (hbs : b ≤ s) (hsσ : s < σ) (hσ1 : σ < 1)
    {w : Work.OddVolterra.St} (hw0 : (1 / 5 : ℝ) ≤ w 0) (hw1 : (1 / 5 : ℝ) ≤ w 1)
    (hwb : ∀ i : Fin 4, |w i| ≤ 2) (i : Fin 2) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖thetaI n h s σ i w τ‖ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm := by
  intro τ hτ
  by_cases h1 : τ = 1
  · subst h1; simp
  · have hτlt : τ < 1 := lt_of_le_of_ne hτ.2 h1
    have hσIcc : σ ∈ Set.Icc b 1 := ⟨le_trans hbs (le_of_lt hsσ), le_of_lt hσ1⟩
    have ha : s + τ * (σ - s) ∈ Set.Ico (b / 2) σ := by
      constructor
      · have h1 : (0 : ℝ) ≤ τ * (σ - s) := mul_nonneg hτ.1 (le_of_lt (sub_pos.mpr hsσ))
        have h2 : b / 2 ≤ s := by linarith
        linarith
      · have h1 : τ * (σ - s) < 1 * (σ - s) :=
          mul_lt_mul_of_pos_right hτlt (sub_pos.mpr hsσ)
        linarith
    have hd := (hval σ hσIcc _ ha w hw0 hw1 hwb).2
    have hcomp : ‖((deriv (fun u : ℝ =>
        Work.OddVolterra.Kvec n h u σ (w 0) (w 1) (w 2) (w 3))
          (s + τ * (σ - s))) i)‖ ≤ Cm := le_trans (norm_le_pi_norm _ i) hd
    have hwt : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hτ0 : (0 : ℝ) ≤ τ := hτ.1
    have h1t : 0 ≤ 1 - τ := by linarith
    rw [thetaI_apply, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hwt, abs_of_nonneg h1t]
    refine mul_le_mul_of_nonneg_left ?_ hwt
    calc (1 - τ) * ‖((deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (w 0) (w 1) (w 2) (w 3))
            (s + τ * (σ - s))) i)‖
        ≤ 1 * Cm := mul_le_mul (by linarith [hτ0]) hcomp (norm_nonneg _) (by norm_num)
      _ = Cm := one_mul _

/-- Integrability of the `τ`-integrand. -/
lemma thetaI_intervalIntegrable (n : ℕ) {h : ℝ → ℝ} {b Cm : ℝ}
    (hval : ∀ σ ∈ Set.Icc b 1, ∀ a ∈ Set.Ico (b / 2) σ, ∀ z : Work.OddVolterra.St,
      (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
      ‖Work.OddVolterra.Kvec n h a σ (z 0) (z 1) (z 2) (z 3)‖ ≤ Cm ∧
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ Cm)
    {s σ : ℝ} (hb : 0 < b) (hCm : 0 ≤ Cm) (hbs : b ≤ s) (hsσ : s < σ) (hσ1 : σ < 1)
    {w : Work.OddVolterra.St} (hw0 : (1 / 5 : ℝ) ≤ w 0) (hw1 : (1 / 5 : ℝ) ≤ w 1)
    (hwb : ∀ i : Fin 4, |w i| ≤ 2) (i : Fin 2) :
    IntervalIntegrable (thetaI n h s σ i w) volume (0 : ℝ) 1 := by
  have hbd := thetaI_bound n hval hb hbs hsσ hσ1 hw0 hw1 hwb i
  refine (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm).mono_fun'
    (thetaI_aestronglyMeasurable n s σ i w) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
  exact hbd τ ⟨le_of_lt hτ.1, hτ.2⟩

/-- **The `s`-derivative of `G₂` at a constant state as an Abel average.** -/
lemma G2_deriv_state_eq_integral (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b Cm : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hCm : 0 < Cm)
    (hval : ∀ σ ∈ Set.Icc b 1, ∀ a ∈ Set.Ico (b / 2) σ, ∀ z : Work.OddVolterra.St,
      (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
      ‖Work.OddVolterra.Kvec n h a σ (z 0) (z 1) (z 2) (z 3)‖ ≤ Cm ∧
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ Cm)
    {s : ℝ} (hs : s ∈ Set.Icc b 1) {σ : ℝ} (hσ : σ ∈ Set.Ioo s 1)
    {w : Work.OddVolterra.St} (hw0 : (1 / 5 : ℝ) ≤ w 0) (hw1 : (1 / 5 : ℝ) ≤ w 1)
    (hwb : ∀ i : Fin 4, |w i| ≤ 2) (i : Fin 2) :
    deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (w 0) (w 1) (w 2) (w 3)) i) s =
      ∫ τ in (0 : ℝ)..1, thetaI n h s σ i w τ := by
  have hs0 : 0 < s := lt_of_lt_of_le hb hs.1
  have hsb : b ≤ s := hs.1
  refine (deriv_G2_apply_eq_integral (n := n) hn hh (Z := fun _ : ℝ => w)
    contDiffOn_const ⟨hs0, lt_trans hσ.1 hσ.2⟩ i (δ := b / 2) (Cm := Cm) (by linarith) hCm ?_ ?_ ?_
    hσ).trans
    (intervalIntegral.integral_congr (fun τ _ => rfl))
  · intro σ' hσ' a ha
    refine ⟨?_, ?_⟩
    · exact krad_pos_state_region hsupp hsmall (by linarith : 0 < b / 2)
        (by linarith [ha.1]) ha.2 hσ'.2
        (by rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ w 0)]; exact hw0)
    · exact krad_pos_state_region hsupp hsmall (by linarith : 0 < b / 2)
        (by linarith [ha.1]) ha.2 hσ'.2
        (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w 1)]; exact hw1)
  · intro σ' hσ' a ha
    exact (hval σ' ⟨le_trans hsb hσ'.1, hσ'.2⟩ a ⟨by linarith [ha.1], ha.2⟩ w hw0 hw1 hwb).1
  · intro σ' hσ' a ha
    exact (hval σ' ⟨le_trans hsb hσ'.1, hσ'.2⟩ a ⟨by linarith [ha.1], ha.2⟩ w hw0 hw1 hwb).2

/-- **Bound of the `s`-derivative of `G₂` in a constant state.** -/
lemma G2_deriv_bound_state (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b Cm : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hCm : 0 < Cm)
    (hval : ∀ σ ∈ Set.Icc b 1, ∀ a ∈ Set.Ico (b / 2) σ, ∀ z : Work.OddVolterra.St,
      (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
      ‖Work.OddVolterra.Kvec n h a σ (z 0) (z 1) (z 2) (z 3)‖ ≤ Cm ∧
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ Cm)
    {s : ℝ} (hs : s ∈ Set.Icc b 1) {σ : ℝ} (hσ : σ ∈ Set.Ioo s 1)
    {w : Work.OddVolterra.St} (hw0 : (1 / 5 : ℝ) ≤ w 0) (hw1 : (1 / 5 : ℝ) ≤ w 1)
    (hwb : ∀ i : Fin 4, |w i| ≤ 2) (i : Fin 2) :
    |deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (w 0) (w 1) (w 2) (w 3)) i) s|
      ≤ Real.pi * Cm := by
  rw [G2_deriv_state_eq_integral n hn hh hsupp hsmall hb hb1 hCm hval hs hσ hw0 hw1 hwb i]
  have hint := thetaI_intervalIntegrable n hval hb hCm.le hs.1 hσ.1 hσ.2 hw0 hw1 hwb i
  have hbd := thetaI_bound n hval hb hs.1 hσ.1 hσ.2 hw0 hw1 hwb i
  calc |∫ τ in (0 : ℝ)..1, thetaI n h s σ i w τ|
      = ‖∫ τ in (0 : ℝ)..1, thetaI n h s σ i w τ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ τ in (0 : ℝ)..1, ‖thetaI n h s σ i w τ‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm :=
        intervalIntegral.integral_mono_on (by norm_num) hint.norm
          (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm)
          (fun τ hτ => hbd τ hτ)
    _ = Real.pi * Cm := by
        rw [intervalIntegral.integral_mul_const, abel_weight_integral]

/-- The pointwise Lipschitz bound on the `τ`-integrand in the state. -/
lemma thetaI_diff_bound (n : ℕ) {h : ℝ → ℝ} {b Bs : ℝ}
    (hlip : ∀ σ ∈ Set.Icc b 1, ∀ a ∈ Set.Ico (b / 2) σ, ∀ z z' : Work.OddVolterra.St,
      (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
      (1 / 5 : ℝ) ≤ z' 0 → (1 / 5 : ℝ) ≤ z' 1 → (∀ i : Fin 4, |z' i| ≤ 2) →
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a
        - deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) a‖
        ≤ Bs * ‖z - z'‖)
    {s σ : ℝ} (hb : 0 < b) (hbs : b ≤ s) (hsσ : s < σ) (hσ1 : σ < 1)
    {w w' : Work.OddVolterra.St} (hw0 : (1 / 5 : ℝ) ≤ w 0) (hw1 : (1 / 5 : ℝ) ≤ w 1)
    (hwb : ∀ i : Fin 4, |w i| ≤ 2) (hw'0 : (1 / 5 : ℝ) ≤ w' 0) (hw'1 : (1 / 5 : ℝ) ≤ w' 1)
    (hw'b : ∀ i : Fin 4, |w' i| ≤ 2) (i : Fin 2) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖thetaI n h s σ i w τ - thetaI n h s σ i w' τ‖
        ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * (Bs * ‖w - w'‖) := by
  intro τ hτ
  by_cases h1 : τ = 1
  · subst h1; simp
  · have hτlt : τ < 1 := lt_of_le_of_ne hτ.2 h1
    have hσIcc : σ ∈ Set.Icc b 1 := ⟨le_trans hbs (le_of_lt hsσ), le_of_lt hσ1⟩
    have ha : s + τ * (σ - s) ∈ Set.Ico (b / 2) σ := by
      constructor
      · have h1 : (0 : ℝ) ≤ τ * (σ - s) := mul_nonneg hτ.1 (le_of_lt (sub_pos.mpr hsσ))
        have h2 : b / 2 ≤ s := by linarith
        linarith
      · have h1 : τ * (σ - s) < 1 * (σ - s) :=
          mul_lt_mul_of_pos_right hτlt (sub_pos.mpr hsσ)
        linarith
    have hd := hlip σ hσIcc _ ha w w' hw0 hw1 hwb hw'0 hw'1 hw'b
    have hcomp : ‖((deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (w 0) (w 1) (w 2) (w 3)) (s + τ * (σ - s)))
        - (deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) (s + τ * (σ - s)))) i‖
        ≤ Bs * ‖w - w'‖ := le_trans (norm_le_pi_norm _ i) hd
    have hwt : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hτ0 : (0 : ℝ) ≤ τ := hτ.1
    have h1t : 0 ≤ 1 - τ := by linarith
    have hdiff : thetaI n h s σ i w τ - thetaI n h s σ i w' τ
        = (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * (((deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (w 0) (w 1) (w 2) (w 3))
                (s + τ * (σ - s))) i)
            - ((deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (w' 0) (w' 1) (w' 2) (w' 3))
                (s + τ * (σ - s))) i))) := by
      rw [thetaI_apply, thetaI_apply]; ring
    rw [hdiff, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hwt, abs_of_nonneg h1t]
    refine mul_le_mul_of_nonneg_left ?_ hwt
    calc (1 - τ) * |((deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (w 0) (w 1) (w 2) (w 3))
            (s + τ * (σ - s))) i)
        - ((deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (w' 0) (w' 1) (w' 2) (w' 3))
            (s + τ * (σ - s))) i)|
        ≤ 1 * (Bs * ‖w - w'‖) := by
          refine mul_le_mul (by linarith [hτ0]) ?_ (abs_nonneg _) (by norm_num)
          rw [← Real.norm_eq_abs]
          exact hcomp
      _ = Bs * ‖w - w'‖ := one_mul _

/-- **Lipschitz bound of the `s`-derivative of `G₂` in the state.** -/
lemma G2_deriv_lipschitz_state (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b Cm Bs : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hCm : 0 < Cm)
    (hval : ∀ σ ∈ Set.Icc b 1, ∀ a ∈ Set.Ico (b / 2) σ, ∀ z : Work.OddVolterra.St,
      (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
      ‖Work.OddVolterra.Kvec n h a σ (z 0) (z 1) (z 2) (z 3)‖ ≤ Cm ∧
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ Cm)
    (hlip : ∀ σ ∈ Set.Icc b 1, ∀ a ∈ Set.Ico (b / 2) σ, ∀ z z' : Work.OddVolterra.St,
      (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
      (1 / 5 : ℝ) ≤ z' 0 → (1 / 5 : ℝ) ≤ z' 1 → (∀ i : Fin 4, |z' i| ≤ 2) →
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a
        - deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) a‖
        ≤ Bs * ‖z - z'‖)
    {s : ℝ} (hs : s ∈ Set.Icc b 1) {σ : ℝ} (hσ : σ ∈ Set.Ioo s 1)
    {w w' : Work.OddVolterra.St} (hw0 : (1 / 5 : ℝ) ≤ w 0) (hw1 : (1 / 5 : ℝ) ≤ w 1)
    (hwb : ∀ i : Fin 4, |w i| ≤ 2) (hw'0 : (1 / 5 : ℝ) ≤ w' 0) (hw'1 : (1 / 5 : ℝ) ≤ w' 1)
    (hw'b : ∀ i : Fin 4, |w' i| ≤ 2) (i : Fin 2) :
    |deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (w 0) (w 1) (w 2) (w 3)) i) s
      - deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) i) s|
      ≤ Real.pi * Bs * ‖w - w'‖ := by
  rw [G2_deriv_state_eq_integral n hn hh hsupp hsmall hb hb1 hCm hval hs hσ hw0 hw1 hwb i,
    G2_deriv_state_eq_integral n hn hh hsupp hsmall hb hb1 hCm hval hs hσ hw'0 hw'1 hw'b i]
  have hint := thetaI_intervalIntegrable n hval hb hCm.le hs.1 hσ.1 hσ.2 hw0 hw1 hwb i
  have hint' := thetaI_intervalIntegrable n hval hb hCm.le hs.1 hσ.1 hσ.2 hw'0 hw'1 hw'b i
  have hbd := thetaI_diff_bound n hlip hb hs.1 hσ.1 hσ.2 hw0 hw1 hwb hw'0 hw'1 hw'b i
  have hsub : (∫ τ in (0 : ℝ)..1, thetaI n h s σ i w τ)
      - (∫ τ in (0 : ℝ)..1, thetaI n h s σ i w' τ)
      = ∫ τ in (0 : ℝ)..1, (thetaI n h s σ i w τ - thetaI n h s σ i w' τ) :=
    (intervalIntegral.integral_sub hint hint').symm
  rw [hsub]
  calc |∫ τ in (0 : ℝ)..1, (thetaI n h s σ i w τ - thetaI n h s σ i w' τ)|
      = ‖∫ τ in (0 : ℝ)..1, (thetaI n h s σ i w τ - thetaI n h s σ i w' τ)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ τ in (0 : ℝ)..1, ‖thetaI n h s σ i w τ - thetaI n h s σ i w' τ‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * (Bs * ‖w - w'‖) :=
        intervalIntegral.integral_mono_on (by norm_num)
          (hint.sub hint').norm
          (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const (Bs * ‖w - w'‖))
          (fun τ hτ => hbd τ hτ)
    _ = Real.pi * (Bs * ‖w - w'‖) := by
        rw [intervalIntegral.integral_mul_const, abel_weight_integral]
    _ = Real.pi * Bs * ‖w - w'‖ := by ring

/-! ## The main theorem -/

/-- **`Θ` is Lipschitz in the state variable, uniformly on the compact state region.** -/
theorem theta_lipschitz_state_ball (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ C : ℝ, 0 < C ∧
      (∀ s ∈ Set.Icc b 1, ∀ σ ∈ Set.Ioo s 1,
        ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2),
        ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2),
        ‖Work.OddVolterra.Theta n h s σ z - Work.OddVolterra.Theta n h s σ z'‖ ≤ L * ‖z - z'‖) ∧
      (∀ s ∈ Set.Icc b 1, ∀ σ ∈ Set.Ioo s 1,
        ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2),
        ‖Work.OddVolterra.Theta n h s σ z‖ ≤ C) ∧
      (∀ s ∈ Set.Icc b 1,
        ContinuousOn (fun p : ℝ × Work.OddVolterra.St => Work.OddVolterra.Theta n h s p.1 p.2)
          {p : ℝ × Work.OddVolterra.St | p.1 ∈ Set.Ioo s 1 ∧
            p.2 ∈ Metric.closedBall (Work.OddVolterra.baseState p.1) (1 / 2)}) := by
  have hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall k (le_trans hk (by norm_num)) s
  obtain ⟨Cm, Bs, hCm, hBs, hval, hlip⟩ := kvec_state_data n hn hh hsupp hsm1 hb hb1
  refine ⟨Real.pi * Bs + 1, by positivity, Real.pi * Cm + 3, by positivity, ?_, ?_, ?_⟩
  · -- (1) Lipschitz in the state
    intro s hs σ hσ z hz z' hz'
    have hσIcc : σ ∈ Set.Icc b 1 := ⟨le_trans hs.1 (le_of_lt hσ.1), le_of_lt hσ.2⟩
    obtain ⟨hz0, hz1, hzb⟩ := state_ball_box hb hb1 σ hσIcc z hz
    obtain ⟨hz'0, hz'1, hz'b⟩ := state_ball_box hb hb1 σ hσIcc z' hz'
    have hdiff : ∀ i : Fin 4, |z i - z' i| ≤ ‖z - z'‖ := by
      intro i
      have h := dist_le_pi_dist z z' i
      rwa [Real.dist_eq] at h
    have hLB1 : (1 : ℝ) ≤ Real.pi * Bs + 1 := by
      have := Real.pi_pos; nlinarith [hBs]
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    fin_cases i
    · show ‖(Work.OddVolterra.Theta n h s σ z - Work.OddVolterra.Theta n h s σ z') (0 : Fin 4)‖
        ≤ (Real.pi * Bs + 1) * ‖z - z'‖
      have h0 : |(-z 2) - (-z' 2)| ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := by
        rw [neg_sub_neg, abs_sub_comm]
        calc |z 2 - z' 2| ≤ ‖z - z'‖ := hdiff 2
          _ ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := le_mul_of_one_le_left (norm_nonneg _) hLB1
      simpa [Work.OddVolterra.Theta, Real.norm_eq_abs] using h0
    · show ‖(Work.OddVolterra.Theta n h s σ z - Work.OddVolterra.Theta n h s σ z') (1 : Fin 4)‖
        ≤ (Real.pi * Bs + 1) * ‖z - z'‖
      have h1 : |(-z 3) - (-z' 3)| ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := by
        rw [neg_sub_neg, abs_sub_comm]
        calc |z 3 - z' 3| ≤ ‖z - z'‖ := hdiff 3
          _ ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := le_mul_of_one_le_left (norm_nonneg _) hLB1
      simpa [Work.OddVolterra.Theta, Real.norm_eq_abs] using h1
    · show ‖(Work.OddVolterra.Theta n h s σ z - Work.OddVolterra.Theta n h s σ z') (2 : Fin 4)‖
        ≤ (Real.pi * Bs + 1) * ‖z - z'‖
      have h2 : |(-deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s)
          - (-deriv (fun u : ℝ =>
              (Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 0) s)|
          ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := by
        rw [neg_sub_neg, abs_sub_comm]
        have h := G2_deriv_lipschitz_state n hn hh hsupp hsm1 hb hb1 hCm hval hlip hs hσ
          hz0 hz1 hzb hz'0 hz'1 hz'b (0 : Fin 2)
        refine le_trans h ?_
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      simpa [Work.OddVolterra.Theta, Real.norm_eq_abs] using h2
    · show ‖(Work.OddVolterra.Theta n h s σ z - Work.OddVolterra.Theta n h s σ z') (3 : Fin 4)‖
        ≤ (Real.pi * Bs + 1) * ‖z - z'‖
      have h3 : |(-deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s)
          - (-deriv (fun u : ℝ =>
              (Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 1) s)|
          ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := by
        rw [neg_sub_neg, abs_sub_comm]
        have h := G2_deriv_lipschitz_state n hn hh hsupp hsm1 hb hb1 hCm hval hlip hs hσ
          hz0 hz1 hzb hz'0 hz'1 hz'b (1 : Fin 2)
        refine le_trans h ?_
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      simpa [Work.OddVolterra.Theta, Real.norm_eq_abs] using h3
  · -- (2) uniform bound
    intro s hs σ hσ z hz
    have hσIcc : σ ∈ Set.Icc b 1 := ⟨le_trans hs.1 (le_of_lt hσ.1), le_of_lt hσ.2⟩
    obtain ⟨hz0, hz1, hzb⟩ := state_ball_box hb hb1 σ hσIcc z hz
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    fin_cases i
    · show ‖Work.OddVolterra.Theta n h s σ z (0 : Fin 4)‖ ≤ Real.pi * Cm + 3
      have h0 : |(-z 2)| ≤ Real.pi * Cm + 3 := by
        rw [abs_neg]
        have hpi : (0 : ℝ) ≤ Real.pi * Cm := mul_nonneg Real.pi_pos.le hCm.le
        linarith [hzb 2, hpi]
      simpa [Work.OddVolterra.Theta, Real.norm_eq_abs] using h0
    · show ‖Work.OddVolterra.Theta n h s σ z (1 : Fin 4)‖ ≤ Real.pi * Cm + 3
      have h1 : |(-z 3)| ≤ Real.pi * Cm + 3 := by
        rw [abs_neg]
        have hpi : (0 : ℝ) ≤ Real.pi * Cm := mul_nonneg Real.pi_pos.le hCm.le
        linarith [hzb 3, hpi]
      simpa [Work.OddVolterra.Theta, Real.norm_eq_abs] using h1
    · show ‖Work.OddVolterra.Theta n h s σ z (2 : Fin 4)‖ ≤ Real.pi * Cm + 3
      have h2 : |(-deriv (fun u : ℝ =>
          (Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s)| ≤ Real.pi * Cm + 3 := by
        rw [abs_neg]
        have h := G2_deriv_bound_state n hn hh hsupp hsm1 hb hb1 hCm hval hs hσ hz0 hz1 hzb
          (0 : Fin 2)
        linarith
      simpa [Work.OddVolterra.Theta, Real.norm_eq_abs] using h2
    · show ‖Work.OddVolterra.Theta n h s σ z (3 : Fin 4)‖ ≤ Real.pi * Cm + 3
      have h3 : |(-deriv (fun u : ℝ =>
          (Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s)| ≤ Real.pi * Cm + 3 := by
        rw [abs_neg]
        have h := G2_deriv_bound_state n hn hh hsupp hsm1 hb hb1 hCm hval hs hσ hz0 hz1 hzb
          (1 : Fin 2)
        linarith
      simpa [Work.OddVolterra.Theta, Real.norm_eq_abs] using h3
  · -- (3) joint continuity in `(σ, z)`
    intro s hs
    set T : Set (ℝ × Work.OddVolterra.St) :=
      {p : ℝ × Work.OddVolterra.St | p.1 ∈ Set.Ioo s 1 ∧
        p.2 ∈ Metric.closedBall (Work.OddVolterra.baseState p.1) (1 / 2)} with hTdef
    rw [continuousOn_pi]
    intro i
    fin_cases i
    · show ContinuousOn (fun p : ℝ × Work.OddVolterra.St =>
          (Work.OddVolterra.Theta n h s p.1 p.2) (0 : Fin 4)) T
      have hc : ContinuousOn (fun p : ℝ × Work.OddVolterra.St => -(p.2 2)) T :=
        (((continuous_apply (2 : Fin 4)).comp continuous_snd).neg).continuousOn
      refine hc.congr ?_
      intro p hp
      simp [Work.OddVolterra.Theta]
    · show ContinuousOn (fun p : ℝ × Work.OddVolterra.St =>
          (Work.OddVolterra.Theta n h s p.1 p.2) (1 : Fin 4)) T
      have hc : ContinuousOn (fun p : ℝ × Work.OddVolterra.St => -(p.2 3)) T :=
        (((continuous_apply (3 : Fin 4)).comp continuous_snd).neg).continuousOn
      refine hc.congr ?_
      intro p hp
      simp [Work.OddVolterra.Theta]
    · show ContinuousOn (fun p : ℝ × Work.OddVolterra.St =>
          (Work.OddVolterra.Theta n h s p.1 p.2) (2 : Fin 4)) T
      have hconta : ContinuousOn (fun p : ℝ × Work.OddVolterra.St =>
          deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3)) 0) s) T := by
        have hintcont : ContinuousOn (fun p : ℝ × Work.OddVolterra.St =>
            ∫ τ in (0 : ℝ)..1, thetaI n h s p.1 0 p.2 τ) T := by
          intro p₀ hp₀
          obtain ⟨hp₀1, hp₀2⟩ := hp₀
          obtain ⟨hp₀0, hp₀1', hp₀b⟩ := state_ball_box hb hb1 p₀.1
            ⟨le_trans hs.1 (le_of_lt hp₀1.1), le_of_lt hp₀1.2⟩ p₀.2 hp₀2
          refine intervalIntegral.continuousWithinAt_of_dominated_interval
            (μ := volume) (a := (0 : ℝ)) (b := 1) (s := T) (x₀ := p₀)
            (F := fun p τ => thetaI n h s p.1 0 p.2 τ)
            (bound := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm) ?_ ?_ ?_ ?_
          · exact Filter.Eventually.of_forall
              (fun p => thetaI_aestronglyMeasurable n s p.1 0 p.2)
          · filter_upwards [self_mem_nhdsWithin] with p hp
            refine Filter.Eventually.of_forall (fun τ hτ => ?_)
            rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
            obtain ⟨hp0, hp1, hpb⟩ := state_ball_box hb hb1 p.1
              ⟨le_trans hs.1 (le_of_lt hp.1.1), le_of_lt hp.1.2⟩ p.2 hp.2
            exact thetaI_bound n hval hb hs.1 hp.1.1 hp.1.2 hp0 hp1 hpb 0 τ
              ⟨le_of_lt hτ.1, hτ.2⟩
          · exact Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm
          · refine Filter.Eventually.of_forall (fun τ hτ => ?_)
            rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
            by_cases h1 : τ = 1
            · subst h1
              have hzero : (fun p : ℝ × Work.OddVolterra.St => thetaI n h s p.1 0 p.2 1)
                  = fun _ => (0 : ℝ) := by
                funext p; simp
              rw [hzero]
              exact continuousWithinAt_const
            · have hτlt : τ < 1 := lt_of_le_of_ne hτ.2 h1
              have hcurve : ContinuousWithinAt (fun p : ℝ × Work.OddVolterra.St =>
                  ((s + τ * (p.1 - s), p.1), p.2)) T p₀ := by
                refine ContinuousWithinAt.prodMk ?_ continuous_snd.continuousWithinAt
                refine ContinuousWithinAt.prodMk ?_ continuous_fst.continuousWithinAt
                exact (by fun_prop : Continuous fun p : ℝ × Work.OddVolterra.St =>
                  s + τ * (p.1 - s)).continuousWithinAt
              have hMT : Set.MapsTo (fun p : ℝ × Work.OddVolterra.St =>
                  ((s + τ * (p.1 - s), p.1), p.2)) T (kvecRegion h) := by
                intro p hp
                obtain ⟨hp1, hp2⟩ := hp
                obtain ⟨hp0, hp1', hpb⟩ := state_ball_box hb hb1 p.1
                  ⟨le_trans hs.1 (le_of_lt hp1.1), le_of_lt hp1.2⟩ p.2 hp2
                have hlt : s + τ * (p.1 - s) < p.1 := by
                  have h : τ * (p.1 - s) < 1 * (p.1 - s) :=
                    mul_lt_mul_of_pos_right hτlt (sub_pos.mpr hp1.1)
                  linarith
                have hge : b / 2 ≤ s + τ * (p.1 - s) := by
                  have h : (0 : ℝ) ≤ τ * (p.1 - s) :=
                    mul_nonneg (le_of_lt hτ.1) (le_of_lt (sub_pos.mpr hp1.1))
                  have h2 : b / 2 ≤ s := by linarith [hs.1]
                  linarith
                exact ⟨hlt,
                  krad_pos_state_region hsupp hsm1 (by linarith : 0 < b / 2) hge (le_of_lt hlt)
                    (le_of_lt hp1.2)
                      (by rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.2 0)]; exact hp0),
                  krad_pos_state_region hsupp hsm1 (by linarith : 0 < b / 2) hge (le_of_lt hlt)
                    (le_of_lt hp1.2)
                      (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.2 1)]; exact hp1')⟩
              have hjc := (continuousOn_deriv_Kvec n hn hh).continuousWithinAt (hMT ⟨hp₀1, hp₀2⟩)
              have hcomp : ContinuousWithinAt (fun p : ℝ × Work.OddVolterra.St =>
                  deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u p.1
                    (p.2 0) (p.2 1) (p.2 2) (p.2 3)) (s + τ * (p.1 - s))) T p₀ := by
                have h := hjc.comp (f := fun p : ℝ × Work.OddVolterra.St =>
                  ((s + τ * (p.1 - s), p.1), p.2)) hcurve hMT
                simpa [Function.comp_def] using h
              have hproj : ContinuousWithinAt (fun p : ℝ × Work.OddVolterra.St =>
                  ((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u p.1
                    (p.2 0) (p.2 1) (p.2 2) (p.2 3)) (s + τ * (p.1 - s))) 0)) T p₀ :=
                ((continuous_apply (0 : Fin 2)).continuousAt).comp_continuousWithinAt hcomp
              have hmul := (hproj.const_mul (1 - τ)).const_mul ((Real.sqrt (τ * (1 - τ)))⁻¹)
              simpa [thetaI] using hmul
        exact hintcont.congr (fun p hp => by
          obtain ⟨hp1, hp2⟩ := hp
          obtain ⟨hp0, hp1', hpb⟩ := state_ball_box hb hb1 p.1
            ⟨le_trans hs.1 (le_of_lt hp1.1), le_of_lt hp1.2⟩ p.2 hp2
          exact G2_deriv_state_eq_integral n hn hh hsupp hsm1 hb hb1 hCm hval hs hp1
            hp0 hp1' hpb (0 : Fin 2))
      refine (hconta.neg).congr ?_
      intro p hp
      simp [Work.OddVolterra.Theta]
    · show ContinuousOn (fun p : ℝ × Work.OddVolterra.St =>
          (Work.OddVolterra.Theta n h s p.1 p.2) (3 : Fin 4)) T
      have hconta : ContinuousOn (fun p : ℝ × Work.OddVolterra.St =>
          deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3)) 1) s) T := by
        have hintcont : ContinuousOn (fun p : ℝ × Work.OddVolterra.St =>
            ∫ τ in (0 : ℝ)..1, thetaI n h s p.1 1 p.2 τ) T := by
          intro p₀ hp₀
          obtain ⟨hp₀1, hp₀2⟩ := hp₀
          obtain ⟨hp₀0, hp₀1', hp₀b⟩ := state_ball_box hb hb1 p₀.1
            ⟨le_trans hs.1 (le_of_lt hp₀1.1), le_of_lt hp₀1.2⟩ p₀.2 hp₀2
          refine intervalIntegral.continuousWithinAt_of_dominated_interval
            (μ := volume) (a := (0 : ℝ)) (b := 1) (s := T) (x₀ := p₀)
            (F := fun p τ => thetaI n h s p.1 1 p.2 τ)
            (bound := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm) ?_ ?_ ?_ ?_
          · exact Filter.Eventually.of_forall
              (fun p => thetaI_aestronglyMeasurable n s p.1 1 p.2)
          · filter_upwards [self_mem_nhdsWithin] with p hp
            refine Filter.Eventually.of_forall (fun τ hτ => ?_)
            rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
            obtain ⟨hp0, hp1, hpb⟩ := state_ball_box hb hb1 p.1
              ⟨le_trans hs.1 (le_of_lt hp.1.1), le_of_lt hp.1.2⟩ p.2 hp.2
            exact thetaI_bound n hval hb hs.1 hp.1.1 hp.1.2 hp0 hp1 hpb 1 τ
              ⟨le_of_lt hτ.1, hτ.2⟩
          · exact Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm
          · refine Filter.Eventually.of_forall (fun τ hτ => ?_)
            rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
            by_cases h1 : τ = 1
            · subst h1
              have hzero : (fun p : ℝ × Work.OddVolterra.St => thetaI n h s p.1 1 p.2 1)
                  = fun _ => (0 : ℝ) := by
                funext p; simp
              rw [hzero]
              exact continuousWithinAt_const
            · have hτlt : τ < 1 := lt_of_le_of_ne hτ.2 h1
              have hcurve : ContinuousWithinAt (fun p : ℝ × Work.OddVolterra.St =>
                  ((s + τ * (p.1 - s), p.1), p.2)) T p₀ := by
                refine ContinuousWithinAt.prodMk ?_ continuous_snd.continuousWithinAt
                refine ContinuousWithinAt.prodMk ?_ continuous_fst.continuousWithinAt
                exact (by fun_prop : Continuous fun p : ℝ × Work.OddVolterra.St =>
                  s + τ * (p.1 - s)).continuousWithinAt
              have hMT : Set.MapsTo (fun p : ℝ × Work.OddVolterra.St =>
                  ((s + τ * (p.1 - s), p.1), p.2)) T (kvecRegion h) := by
                intro p hp
                obtain ⟨hp1, hp2⟩ := hp
                obtain ⟨hp0, hp1', hpb⟩ := state_ball_box hb hb1 p.1
                  ⟨le_trans hs.1 (le_of_lt hp1.1), le_of_lt hp1.2⟩ p.2 hp2
                have hlt : s + τ * (p.1 - s) < p.1 := by
                  have h : τ * (p.1 - s) < 1 * (p.1 - s) :=
                    mul_lt_mul_of_pos_right hτlt (sub_pos.mpr hp1.1)
                  linarith
                have hge : b / 2 ≤ s + τ * (p.1 - s) := by
                  have h : (0 : ℝ) ≤ τ * (p.1 - s) :=
                    mul_nonneg (le_of_lt hτ.1) (le_of_lt (sub_pos.mpr hp1.1))
                  have h2 : b / 2 ≤ s := by linarith [hs.1]
                  linarith
                exact ⟨hlt,
                  krad_pos_state_region hsupp hsm1 (by linarith : 0 < b / 2) hge (le_of_lt hlt)
                    (le_of_lt hp1.2)
                      (by rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.2 0)]; exact hp0),
                  krad_pos_state_region hsupp hsm1 (by linarith : 0 < b / 2) hge (le_of_lt hlt)
                    (le_of_lt hp1.2)
                      (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.2 1)]; exact hp1')⟩
              have hjc := (continuousOn_deriv_Kvec n hn hh).continuousWithinAt (hMT ⟨hp₀1, hp₀2⟩)
              have hcomp : ContinuousWithinAt (fun p : ℝ × Work.OddVolterra.St =>
                  deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u p.1
                    (p.2 0) (p.2 1) (p.2 2) (p.2 3)) (s + τ * (p.1 - s))) T p₀ := by
                have h := hjc.comp (f := fun p : ℝ × Work.OddVolterra.St =>
                  ((s + τ * (p.1 - s), p.1), p.2)) hcurve hMT
                simpa [Function.comp_def] using h
              have hproj : ContinuousWithinAt (fun p : ℝ × Work.OddVolterra.St =>
                  ((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u p.1
                    (p.2 0) (p.2 1) (p.2 2) (p.2 3)) (s + τ * (p.1 - s))) 1)) T p₀ :=
                ((continuous_apply (1 : Fin 2)).continuousAt).comp_continuousWithinAt hcomp
              have hmul := (hproj.const_mul (1 - τ)).const_mul ((Real.sqrt (τ * (1 - τ)))⁻¹)
              simpa [thetaI] using hmul
        exact hintcont.congr (fun p hp => by
          obtain ⟨hp1, hp2⟩ := hp
          obtain ⟨hp0, hp1', hpb⟩ := state_ball_box hb hb1 p.1
            ⟨le_trans hs.1 (le_of_lt hp1.1), le_of_lt hp1.2⟩ p.2 hp2
          exact G2_deriv_state_eq_integral n hn hh hsupp hsm1 hb hb1 hCm hval hs hp1
            hp0 hp1' hpb (1 : Fin 2))
      refine (hconta.neg).congr ?_
      intro p hp
      simp [Work.OddVolterra.Theta]


end

end Work.OddVolterra.Existence
