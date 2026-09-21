import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.window2_data
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.KvecM_eq_Kvec
import Submission.Work.OddVolterra.KernelExt.KvecM_contDiffOn_box
import Submission.Work.OddVolterra.KernelExt.Rnu_contDiff
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.Existence.krad_pos_state_region
import Submission.Work.OddVolterra.Existence.diag_K1_explicit
import Submission.Work.OddVolterra.Existence.diag_K2_explicit
import Submission.Work.OddVolterra.Existence.Godd_zero_diag
import Submission.Work.OddVolterra.Existence.deriv_G2_apply_eq_integral
import Submission.Work.OddVolterra.Smooth.Q_regularity
import Submission.Work.OddVolterra.Existence.Theta_integrand_intervalIntegrable
import Submission.Work.OddVolterra.Window.WindowFed
import Submission.Work.Anchor.ThetaM_contDiffOn_wide
import Submission.Work.OddVolterra.Existence.aw_contDiffOn_awGodd
import Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_of_le
import Submission.Commons.Analysis.Abel.continuousOn_abel_K

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! # Regularity of the localised odd window data

The three data of the odd transition window — `Work.OddVolterra.Existence.GoddW`, `ThetaW`,
`XiW`, defined in `Existence/window2_data.lean` as the manifest kernels cut off to the window
`[wA, wC] = [7/10, 19/20]` — are continuous; the `Θ`-datum is Lipschitz in the state with a
constant uniform over the slope window, and the state-differentiability of the `G`-datum holds on
the whole ball of radius `1`.

The cutoffs are the bumps `cs` (slope) and `cz` (state, applied to the *squared* Euclidean
distance `wsq`); the manifest kernels `GoddM ≃ Godd` and `ThetaM` are smooth on the regions on
which the cutoffs live, and the only input that is not a consequence of smoothness times compact
support is the continuity of the source `Xi`, whose last two components are the derivative of the
Abel transform of `Q` — see `wdr_continuousOn_deriv_abel_transform` and
`wdr_continuous_Xi` below.
-/

/-! ## Elementary order facts -/

lemma wdr_isOpen_gt {α : Type*} [TopologicalSpace α] {f : α → ℝ} (hf : Continuous f) (c : ℝ) :
    IsOpen {x | c < f x} := isOpen_lt continuous_const hf

lemma wdr_isOpen_lt {α : Type*} [TopologicalSpace α] {f : α → ℝ} (hf : Continuous f) (c : ℝ) :
    IsOpen {x | f x < c} := isOpen_lt hf continuous_const

/-! ## The ball profile and the base state -/

/-- On `|s| ≤ 21/20` the ball profile stays above `17/25`. -/
lemma wdr_profileX_ge_17_25 {s : ℝ} (hs : |s| ≤ 21 / 20) :
    17 / 25 ≤ Commons.Geometry.Ulam.profileX s := by
  have hs2 : s ^ 2 ≤ (21 / 20 : ℝ) ^ 2 := by
    have h := abs_le.mp hs
    nlinarith [h.1, h.2]
  have hsq : Real.sqrt (1 + s ^ 2) ≤ 25 / 17 := by
    have hle : 1 + s ^ 2 ≤ (25 / 17 : ℝ) ^ 2 := by nlinarith [hs2]
    calc Real.sqrt (1 + s ^ 2) ≤ Real.sqrt ((25 / 17 : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 25 / 17 := Real.sqrt_sq (by norm_num)
  rw [Commons.Geometry.Ulam.profileX, le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  calc 17 / 25 * Real.sqrt (1 + s ^ 2) ≤ 17 / 25 * (25 / 17) :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 1 := by norm_num

lemma wdr_contDiff_baseState : ContDiff ℝ (⊤ : ℕ∞) baseState := by
  have hpx : ContDiff ℝ (⊤ : ℕ∞) Commons.Geometry.Ulam.profileX :=
    Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX
  have hdpx : ContDiff ℝ (⊤ : ℕ∞) (deriv Commons.Geometry.Ulam.profileX) := by
    have h := hpx.iterate_deriv 1
    simpa [Function.iterate_one] using h
  rw [show baseState = fun s : ℝ => ![
      Commons.Geometry.Ulam.profileX s, Commons.Geometry.Ulam.profileX s,
      deriv Commons.Geometry.Ulam.profileX s,
      deriv Commons.Geometry.Ulam.profileX s] from rfl]
  exact contDiff_pi.mpr (fun i => by
    fin_cases i <;> simp [hpx, hdpx])

lemma wdr_continuous_baseState : Continuous baseState := wdr_contDiff_baseState.continuous

lemma wdr_continuous_wsq : Continuous (fun p : ℝ × St => Existence.wsq p.1 p.2) := by
  have hsum : Continuous
      (fun p : ℝ × St => ∑ i : Fin 4, (p.2 i - baseState p.1 i) ^ 2) :=
    continuous_finset_sum _ (fun i _ =>
      (((continuous_apply i).comp continuous_snd).sub
        ((continuous_apply i).comp (wdr_continuous_baseState.comp continuous_fst))).pow 2)
  simpa only [Existence.wsq] using hsum

/-! ## The support regions of the cutoffs -/

/-- The region containing the support of the state cutoff `chiG`: the slope within `4/25` of
`wCenter` and the squared distance to the base state at most `4/25`. -/
def wdrSuppG : Set (ℝ × St) :=
  {p | |p.1 - Existence.wCenter| ≤ 4 / 25 ∧ Existence.wsq p.1 p.2 ≤ 4 / 25}

/-- The region containing the support of the `Θ`-cutoff `chiT`. -/
def wdrSuppT : Set ((ℝ × ℝ) × St) :=
  {q | |q.1.1 - Existence.wCenter| ≤ 4 / 25 ∧ |q.1.2 - Existence.wCenter| ≤ 4 / 25 ∧
        Existence.wsq q.1.2 q.2 ≤ 4 / 25}

/-- An open region on which the diagonal state data `Godd` is smooth: the slope is past `1/20`
and the two chord endpoints are more than `1/5` away from the axis. -/
def wdrGoodG : Set (ℝ × St) :=
  {p | 1 / 20 < p.1 ∧ 1 / 5 < |p.2 0| ∧ 1 / 5 < |p.2 1|}

/-- An open region on which the manifest `Θ`-datum is smooth. -/
def wdrGoodT : Set ((ℝ × ℝ) × St) :=
  {q | 9 / 20 < q.1.1 ∧ q.1.1 < 21 / 20 ∧ 9 / 20 < q.1.2 ∧ q.1.2 < 21 / 20 ∧
        1 / 5 < |q.2 0| ∧ 1 / 5 < |q.2 1|}

lemma wdr_abs_le_of_wsq {σ : ℝ} {z : St} (h : Existence.wsq σ z ≤ 4 / 25) (i : Fin 4) :
    |z i - baseState σ i| ≤ 2 / 5 := by
  have h1 : (z i - baseState σ i) ^ 2 ≤ (2 / 5 : ℝ) ^ 2 := by
    have h2 : (z i - baseState σ i) ^ 2 ≤ Existence.wsq σ z := by
      rw [Existence.wsq]
      exact Finset.single_le_sum (f := fun j : Fin 4 => (z j - baseState σ j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [h2, h]
  have h3 : |z i - baseState σ i| ≤ |(2 / 5 : ℝ)| := sq_le_sq.mp h1
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 / 5 : ℝ))] at h3
  exact h3

lemma wdr_one_fifth_lt_abs_zero {σ : ℝ} (hσ : |σ| ≤ 21 / 20) {z : St}
    (h : Existence.wsq σ z ≤ 4 / 25) : 1 / 5 < |z 0| := by
  have h0 := wdr_abs_le_of_wsq h 0
  have hb : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
  rw [hb] at h0
  have hpx : 17 / 25 ≤ Commons.Geometry.Ulam.profileX σ := wdr_profileX_ge_17_25 hσ
  have h7 : (7 : ℝ) / 25 ≤ z 0 := by
    have := (abs_le.mp h0).1
    linarith
  have h5 : (1 : ℝ) / 5 < 7 / 25 := by norm_num
  exact lt_of_lt_of_le (lt_of_lt_of_le h5 h7) (le_abs_self _)

lemma wdr_one_fifth_lt_abs_one {σ : ℝ} (hσ : |σ| ≤ 21 / 20) {z : St}
    (h : Existence.wsq σ z ≤ 4 / 25) : 1 / 5 < |z 1| := by
  have h0 := wdr_abs_le_of_wsq h 1
  have hb : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
  rw [hb] at h0
  have hpx : 17 / 25 ≤ Commons.Geometry.Ulam.profileX σ := wdr_profileX_ge_17_25 hσ
  have h7 : (7 : ℝ) / 25 ≤ z 1 := by
    have := (abs_le.mp h0).1
    linarith
  have h5 : (1 : ℝ) / 5 < 7 / 25 := by norm_num
  exact lt_of_lt_of_le (lt_of_lt_of_le h5 h7) (le_abs_self _)

lemma wdr_abs_le_21_20_of_supp {s : ℝ} (h : |s - Existence.wCenter| ≤ 4 / 25) :
    |s| ≤ 21 / 20 := by
  have h := abs_le.mp h
  rw [Existence.wCenter] at h
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

lemma wdrSuppG_subset_awSupp : wdrSuppG ⊆ Existence.awSupp := by
  rintro ⟨s, z⟩ ⟨h1, h2⟩
  have h1' := abs_le.mp h1
  rw [Existence.wCenter] at h1'
  have hnorm : ‖z - baseState s‖ ≤ 2 / 5 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 5)]
    intro i
    rw [Real.norm_eq_abs]
    exact wdr_abs_le_of_wsq h2 i
  exact ⟨by rw [abs_le]; constructor <;> linarith [h1'.1, h1'.2], hnorm⟩

lemma wdrSuppG_subset_wdrGoodG : wdrSuppG ⊆ wdrGoodG := by
  rintro ⟨s, z⟩ hp
  have h1 : |s - Existence.wCenter| ≤ 4 / 25 := hp.1
  have h2 := hp.2
  have hs := wdr_abs_le_21_20_of_supp h1
  refine ⟨?_, wdr_one_fifth_lt_abs_zero hs h2, wdr_one_fifth_lt_abs_one hs h2⟩
  have h := abs_le.mp h1
  rw [Existence.wCenter] at h
  linarith [h.1]

lemma wdrSuppT_subset_wdrGoodT : wdrSuppT ⊆ wdrGoodT := by
  rintro ⟨⟨s, σ⟩, z⟩ ⟨h1, h2, h3⟩
  have hs := wdr_abs_le_21_20_of_supp h1
  have hσ := wdr_abs_le_21_20_of_supp h2
  refine ⟨?_, ?_, ?_, ?_, wdr_one_fifth_lt_abs_zero hσ h3, wdr_one_fifth_lt_abs_one hσ h3⟩
  · have h := abs_le.mp h1; rw [Existence.wCenter] at h; linarith [h.1]
  · have h := abs_le.mp h1; rw [Existence.wCenter] at h; linarith [h.2]
  · have h := abs_le.mp h2; rw [Existence.wCenter] at h; linarith [h.1]
  · have h := abs_le.mp h2; rw [Existence.wCenter] at h; linarith [h.2]

lemma isOpen_wdrGoodG : IsOpen wdrGoodG := by
  have h : wdrGoodG = ({p : ℝ × St | 1 / 20 < p.1} ∩ {p : ℝ × St | 1 / 5 < |p.2 0|}) ∩
      {p : ℝ × St | 1 / 5 < |p.2 1|} := by
    ext p
    simp only [wdrGoodG, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [h]
  exact IsOpen.inter
    (IsOpen.inter (wdr_isOpen_gt continuous_fst _)
      (wdr_isOpen_gt (continuous_abs.comp ((continuous_apply 0).comp continuous_snd)) _))
    (wdr_isOpen_gt (continuous_abs.comp ((continuous_apply 1).comp continuous_snd)) _)

lemma isOpen_wdrGoodT : IsOpen wdrGoodT := by
  have h : wdrGoodT = ({q : (ℝ × ℝ) × St | 9 / 20 < q.1.1} ∩ {q | q.1.1 < 21 / 20}) ∩
      (({q : (ℝ × ℝ) × St | 9 / 20 < q.1.2} ∩ {q | q.1.2 < 21 / 20}) ∩
        ({q : (ℝ × ℝ) × St | 1 / 5 < |q.2 0|} ∩ {q | 1 / 5 < |q.2 1|})) := by
    ext q
    simp only [wdrGoodT, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [h]
  refine IsOpen.inter (IsOpen.inter ?_ ?_) (IsOpen.inter (IsOpen.inter ?_ ?_) ?_)
  · exact wdr_isOpen_gt (continuous_fst.comp continuous_fst) _
  · exact wdr_isOpen_lt (continuous_fst.comp continuous_fst) _
  · exact wdr_isOpen_gt (continuous_snd.comp continuous_fst) _
  · exact wdr_isOpen_lt (continuous_snd.comp continuous_fst) _
  · exact IsOpen.inter
      (wdr_isOpen_gt (continuous_abs.comp ((continuous_apply 0).comp continuous_snd)) _)
      (wdr_isOpen_gt (continuous_abs.comp ((continuous_apply 1).comp continuous_snd)) _)

/-! ## The cutoffs vanish off the support regions -/

lemma wdr_chiG_eq_zero_of_not_mem {s : ℝ} {z : St} (h : (s, z) ∉ wdrSuppG) :
    Existence.chiG s z = 0 := by
  by_cases h1 : |s - Existence.wCenter| ≤ 4 / 25
  · have h2 : 4 / 25 < Existence.wsq s z := by
      by_contra h2
      exact h ⟨h1, le_of_not_gt h2⟩
    rw [Existence.chiG, show ((Existence.cz : ℝ → ℝ) (Existence.wsq s z)) = 0 from
      Existence.cz_zero (by rw [abs_of_nonneg (Existence.wsq_nonneg s z)]; exact le_of_lt h2)]
    ring
  · rw [Existence.chiG, show ((Existence.cs : ℝ → ℝ) s) = 0 from
      Existence.cs_zero (le_of_not_ge h1)]
    ring

lemma wdr_chiT_eq_zero_of_not_mem {s σ : ℝ} {z : St} (h : ((s, σ), z) ∉ wdrSuppT) :
    Existence.chiT s σ z = 0 := by
  by_cases h1 : |s - Existence.wCenter| ≤ 4 / 25
  · by_cases h2 : |σ - Existence.wCenter| ≤ 4 / 25
    · have h3 : 4 / 25 < Existence.wsq σ z := by
        by_contra h3
        exact h ⟨h1, h2, le_of_not_gt h3⟩
      rw [Existence.chiT, show ((Existence.cz : ℝ → ℝ) (Existence.wsq σ z)) = 0 from
        Existence.cz_zero (by rw [abs_of_nonneg (Existence.wsq_nonneg σ z)]; exact le_of_lt h3)]
      ring
    · rw [Existence.chiT, show ((Existence.cs : ℝ → ℝ) σ) = 0 from
        Existence.cs_zero (le_of_not_ge h2)]
      ring
  · rw [Existence.chiT, show ((Existence.cs : ℝ → ℝ) s) = 0 from
      Existence.cs_zero (le_of_not_ge h1)]
    ring

lemma isClosed_wdrSuppG : IsClosed wdrSuppG := by
  have h : wdrSuppG = {p : ℝ × St | |p.1 - Existence.wCenter| ≤ 4 / 25} ∩
      {p : ℝ × St | Existence.wsq p.1 p.2 ≤ 4 / 25} := by
    ext p
    simp only [wdrSuppG, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [h]
  exact IsClosed.inter
    (isClosed_le (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const)
    (isClosed_le wdr_continuous_wsq continuous_const)

lemma isClosed_wdrSuppT : IsClosed wdrSuppT := by
  have h : wdrSuppT = ({q : (ℝ × ℝ) × St | |q.1.1 - Existence.wCenter| ≤ 4 / 25} ∩
      {q | |q.1.2 - Existence.wCenter| ≤ 4 / 25}) ∩
      {q | Existence.wsq q.1.2 q.2 ≤ 4 / 25} := by
    ext q
    simp only [wdrSuppT, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [h]
  exact IsClosed.inter
    (IsClosed.inter
      (isClosed_le (continuous_abs.comp ((continuous_fst.comp continuous_fst).sub
        continuous_const)) continuous_const)
      (isClosed_le (continuous_abs.comp ((continuous_snd.comp continuous_fst).sub
        continuous_const)) continuous_const))
    (isClosed_le (wdr_continuous_wsq.comp (continuous_snd.comp continuous_fst |>.prodMk
      continuous_snd)) continuous_const)

lemma isCompact_wdrSuppT : IsCompact wdrSuppT := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    wdr_continuous_baseState.continuousOn
  have hle1 : ∀ q ∈ wdrSuppT, |q.1.1| ≤ 2 := by
    intro q hq
    have h := abs_le.mp hq.1
    rw [Existence.wCenter] at h
    rw [abs_le]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hle2 : ∀ q ∈ wdrSuppT, |q.1.2| ≤ 2 := by
    intro q hq
    have h := abs_le.mp hq.2.1
    rw [Existence.wCenter] at h
    rw [abs_le]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hsub : wdrSuppT ⊆
      (Set.Icc (-2 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) 2) ×ˢ Metric.closedBall (0 : St) (C + 1) := by
    intro q hq
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h := hle1 q hq; rw [abs_le] at h; exact h
    · have h := hle2 q hq; rw [abs_le] at h; exact h
    · rw [Metric.mem_closedBall, dist_zero_right]
      have h2 : ‖q.2‖ ≤ ‖baseState q.1.2‖ + ‖q.2 - baseState q.1.2‖ := by
        calc ‖q.2‖ = ‖(q.2 - baseState q.1.2) + baseState q.1.2‖ := by ring_nf
          _ ≤ ‖q.2 - baseState q.1.2‖ + ‖baseState q.1.2‖ := norm_add_le _ _
          _ = ‖baseState q.1.2‖ + ‖q.2 - baseState q.1.2‖ := by ring
      have h3 : ‖baseState q.1.2‖ ≤ C := by
        refine hC q.1.2 ?_
        have h := hle2 q hq
        rw [abs_le] at h
        exact h
      have h4 := norm_le_pi_norm (q.2 - baseState q.1.2) 0
      rw [Pi.sub_apply, Real.norm_eq_abs] at h4
      have h5 : ‖q.2 - baseState q.1.2‖ ≤ 2 / 5 := by
        rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2/5)]
        intro i
        rw [Real.norm_eq_abs]
        exact wdr_abs_le_of_wsq hq.2.2 i
      linarith
  exact ((isCompact_Icc.prod isCompact_Icc).prod
    (isCompact_closedBall (0 : St) (C + 1))).of_isClosed_subset isClosed_wdrSuppT hsub

/-! ## Support of the cut-off functions -/

lemma tsupport_chiG_subset : tsupport (fun p : ℝ × St => Existence.chiG p.1 p.2) ⊆ wdrSuppG := by
  refine closure_minimal (fun p hp => ?_) isClosed_wdrSuppG
  by_contra h
  exact hp (wdr_chiG_eq_zero_of_not_mem h)

lemma tsupport_chiT_subset :
    tsupport (fun q : (ℝ × ℝ) × St => Existence.chiT q.1.1 q.1.2 q.2) ⊆ wdrSuppT := by
  refine closure_minimal (fun q hq => ?_) isClosed_wdrSuppT
  by_contra h
  exact hq (wdr_chiT_eq_zero_of_not_mem h)


/-! ## Smoothness of the cutoffs and of the glued data -/

lemma wdr_contDiff_wsq : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => Existence.wsq p.1 p.2) := by
  have hsum : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × St => ∑ i : Fin 4, (p.2 i - baseState p.1 i) ^ 2) := by
    refine ContDiff.sum (fun i _ => ?_)
    exact (((contDiff_apply ℝ ℝ i).comp contDiff_snd).sub
      ((contDiff_apply ℝ ℝ i).comp (wdr_contDiff_baseState.comp contDiff_fst))).pow 2
  simpa only [Existence.wsq] using hsum

lemma wdr_contDiff_chiG : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => Existence.chiG p.1 p.2) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => (Existence.cs : ℝ → ℝ) p.1) :=
    (ContDiffBump.contDiff Existence.cs).comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × St => (Existence.cz : ℝ → ℝ) (Existence.wsq p.1 p.2)) :=
    (ContDiffBump.contDiff Existence.cz).comp wdr_contDiff_wsq
  simpa only [Existence.chiG] using h1.mul h2

lemma wdr_contDiff_chiT : ContDiff ℝ (⊤ : ℕ∞)
    (fun q : (ℝ × ℝ) × St => Existence.chiT q.1.1 q.1.2 q.2) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × St => (Existence.cs : ℝ → ℝ) q.1.1) :=
    (ContDiffBump.contDiff Existence.cs).comp (contDiff_fst.comp contDiff_fst)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × St => (Existence.cs : ℝ → ℝ) q.1.2) :=
    (ContDiffBump.contDiff Existence.cs).comp (contDiff_snd.comp contDiff_fst)
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ) × St => (Existence.cz : ℝ → ℝ) (Existence.wsq q.1.2 q.2)) :=
    (ContDiffBump.contDiff Existence.cz).comp
      (wdr_contDiff_wsq.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
  simpa only [Existence.chiT, mul_assoc] using h1.mul (h2.mul h3)

/-- Gluing a cutoff with a function known smooth on a neighbourhood of its support. -/
lemma wdr_contDiff_smul_of_contDiffOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → ℝ} {g : X → E} {U : Set X} (hU : IsOpen U)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (hsub : tsupport f ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => f x • g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport f := fun h => hx (hsub h)
    have hmem : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx'
    refine (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with y hy
    have hy' : f y = 0 := by
      by_contra h
      exact hy (subset_tsupport f (Function.mem_support.mpr h))
    rw [hy', zero_smul]

/-- The continuous version of `wdr_contDiff_smul_of_contDiffOn`. -/
lemma wdr_continuous_smul_of_continuousOn {X : Type*} [TopologicalSpace X]
    {E : Type*} [TopologicalSpace E] [Zero E] [SMulWithZero ℝ E] [ContinuousSMul ℝ E]
    {f : X → ℝ} {g : X → E} {U : Set X} (hU : IsOpen U)
    (hf : Continuous f) (hg : ContinuousOn g U) (hsub : tsupport f ⊆ U) :
    Continuous (fun x => f x • g x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact hf.continuousAt.smul (hg.continuousAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport f := fun h => hx (hsub h)
    have hmem : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx'
    refine (continuousAt_const (y := (0 : E))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with y hy
    have hy' : f y = 0 := by
      by_contra h
      exact hy (subset_tsupport f (Function.mem_support.mpr h))
    rw [hy', zero_smul]

/-! ## Smoothness of the diagonal state data on `wdrGoodG` -/

/-- On `wdrGoodG` neither factor of `L(s,t)∂_sL(s,t)` vanishes at the two chord endpoints. -/
lemma wdr_line_prod_ne_zero {h : ℝ → ℝ} {s t : ℝ}
    (hh0 : |h s| ≤ 1 / 100) (hh1 : |deriv h s| ≤ 1 / 100)
    (hs : 1 / 20 < s) (ht : 1 / 5 < |t|) :
    line h s t * lineSlope h s t ≠ 0 := by
  have hline : line h s t ≠ 0 := by
    intro hzero
    have hs0 : 0 < s := by linarith
    have h1 : |h s| < |s * t| := by
      rw [abs_mul, abs_of_pos hs0]
      have h2 : s * (1 / 5) < s * |t| := mul_lt_mul_of_pos_left ht hs0
      have h3 : (1 : ℝ) / 100 < s * (1 / 5) := by nlinarith
      linarith [(abs_le.mp hh0).2]
    rw [line] at hzero
    have h2 : s * t = -h s := by linarith
    rw [h2, abs_neg] at h1
    exact lt_irrefl _ h1
  have hslope : lineSlope h s t ≠ 0 := by
    intro hzero
    have h1 : |deriv h s| < |t| := by
      have h3 : (1 : ℝ) / 100 < 1 / 5 := by norm_num
      linarith [(abs_le.mp hh1).2]
    rw [lineSlope] at hzero
    have h2 : t = -deriv h s := by linarith
    rw [h2, abs_neg] at h1
    exact lt_irrefl _ h1
  exact mul_ne_zero hline hslope

lemma wdr_radicands_ne {h : ℝ → ℝ}
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {p : ℝ × St} (hp : p ∈ wdrGoodG) :
    line h p.1 (-(p.2 0)) * lineSlope h p.1 (-(p.2 0)) ≠ 0 ∧
      line h p.1 (p.2 1) * lineSlope h p.1 (p.2 1) ≠ 0 := by
  have hh0 : |h p.1| ≤ 1 / 100 := by simpa using hsmall 0 (by norm_num) p.1
  have hh1 : |deriv h p.1| ≤ 1 / 100 := by
    have h := hsmall 1 (le_refl 1) p.1
    simpa [iteratedDeriv_one] using h
  have h0 : 1 / 5 < |-(p.2 0)| := by simpa only [abs_neg] using hp.2.1
  exact ⟨wdr_line_prod_ne_zero hh0 hh1 hp.1 h0,
    wdr_line_prod_ne_zero hh0 hh1 hp.1 hp.2.2⟩

/-- **Smoothness of the diagonal odd data on the good region.**  `GoddM` is `C^∞` on `awGood`
(where the two chord-endpoint radicands are positive) and `GoddM = Godd` unconditionally. -/
lemma wdr_contDiffOn_godd (n : ℕ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => Godd n h p.1 p.2) Existence.awGood :=
  (Existence.contDiffOn_GoddM_diag n hh hsupp hsmall).congr
    (fun p _ => (GoddM_eq_Godd n hh p.1 p.2).symm)

/-! ## Smoothness of the manifest `Θ`-datum on `wdrGoodT` -/

lemma wdrGoodT_subset_preimage_Good :
    wdrGoodT ⊆ {q : (ℝ × ℝ) × St | (q.1.1, q.1.2, q.2) ∈ Work.Anchor.Good} := by
  intro q hq
  exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2⟩

lemma wdr_contDiffOn_thetaM (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ) × St => KernelExt.ThetaM n h q.1.1 q.1.2 q.2) wdrGoodT := by
  have hpre : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ) × St => KernelExt.ThetaM n h q.1.1 q.1.2 q.2)
      {q : (ℝ × ℝ) × St | (q.1.1, q.1.2, q.2) ∈ Work.Anchor.Good} :=
    (Work.Anchor.ThetaM_contDiffOn_Good n hh hsmall).comp
      (f := fun q : (ℝ × ℝ) × St => (q.1.1, q.1.2, q.2)) (by fun_prop)
      (fun q hq => hq)
  exact hpre.mono wdrGoodT_subset_preimage_Good

/-! ## Smoothness of the cut-off data -/

lemma wdr_contDiff_goddW (n : ℕ) (_hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => Existence.GoddW n h p.1 p.2) := by
  have hg := wdr_contDiffOn_godd n hh hsupp hsmall
  have hsub : tsupport (fun p : ℝ × St => Existence.chiG p.1 p.2) ⊆ Existence.awGood :=
    fun x hx => Existence.awSupp_subset_awGood (wdrSuppG_subset_awSupp (tsupport_chiG_subset hx))
  have h := wdr_contDiff_smul_of_contDiffOn (U := Existence.awGood) Existence.isOpen_awGood
    wdr_contDiff_chiG hg hsub
  convert h using 1
  ext p
  rw [Existence.GoddW, GoddM_eq_Godd n hh p.1 p.2]

lemma wdr_contDiff_thetaW (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ) × St => Existence.ThetaW n h q.1.1 q.1.2 q.2) := by
  have hg := wdr_contDiffOn_thetaM n hh hsmall
  have hsub : tsupport (fun q : (ℝ × ℝ) × St => Existence.chiT q.1.1 q.1.2 q.2) ⊆ wdrGoodT :=
    fun x hx => wdrSuppT_subset_wdrGoodT (tsupport_chiT_subset hx)
  exact wdr_contDiff_smul_of_contDiffOn (U := wdrGoodT) isOpen_wdrGoodT
    wdr_contDiff_chiT hg hsub

/-! ## Compact support and Lipschitz continuity of the `Θ`-datum -/

lemma wdr_thetaW_eq_zero_of_not_mem {n : ℕ} {h : ℝ → ℝ} {q : (ℝ × ℝ) × St}
    (hq : q ∉ wdrSuppT) : Existence.ThetaW n h q.1.1 q.1.2 q.2 = 0 := by
  rw [Existence.ThetaW, wdr_chiT_eq_zero_of_not_mem hq, zero_smul]

lemma wdr_hasCompactSupport_thetaW (n : ℕ) (h : ℝ → ℝ) :
    HasCompactSupport (fun q : (ℝ × ℝ) × St => Existence.ThetaW n h q.1.1 q.1.2 q.2) := by
  have hsub : tsupport (fun q : (ℝ × ℝ) × St => Existence.ThetaW n h q.1.1 q.1.2 q.2)
      ⊆ wdrSuppT := by
    refine closure_minimal (fun q hq => ?_) isClosed_wdrSuppT
    by_contra hmem
    exact hq (wdr_thetaW_eq_zero_of_not_mem hmem)
  exact isCompact_wdrSuppT.of_isClosed_subset (isClosed_tsupport _) hsub


/-! ## Non-degeneracy of the ball section (the `hmid` hypothesis of `Q_regularity`) -/

/-- For a bump `h` supported in `[4/5, 9/10]` with `|h| ≤ 1/100`, the affine lines
`t ↦ s t + h s` stay strictly inside the unit semicircle on the fixed interval `[-X₁, X₁]`,
`X₁ = profileX 1 = 1/√2`. -/
lemma wdr_psi_semicircle_pos_small {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1))
        (Commons.Geometry.Ulam.profileX 1),
        0 < psi h Commons.Geometry.Ulam.semicircle s t := by
  intro s hs t ht
  obtain ⟨hs0, hs1⟩ := hs
  have hX2 : (Commons.Geometry.Ulam.profileX 1) ^ 2 = (1 : ℝ) / 2 := by
    rw [Commons.Geometry.Ulam.profileX_sq]; norm_num
  have hXpos : 0 < Commons.Geometry.Ulam.profileX 1 :=
    Commons.Geometry.Ulam.profileX_pos 1 (by norm_num)
  have hXlt : Commons.Geometry.Ulam.profileX 1 < 3 / 4 := by nlinarith
  have htabs : |t| ≤ Commons.Geometry.Ulam.profileX 1 := by
    rw [abs_le]; exact ⟨ht.1, ht.2⟩
  have ht2 : t ^ 2 ≤ (1 : ℝ) / 2 := by
    have h := mul_self_le_mul_self (abs_nonneg t) htabs
    have h2 : |t| * |t| = t ^ 2 := by rw [← sq, sq_abs]
    rw [h2] at h
    rw [← sq, hX2] at h
    exact h
  have hsem : Commons.Geometry.Ulam.semicircle t ^ 2 = 1 - t ^ 2 := by
    rw [Commons.Geometry.Ulam.semicircle, Real.sq_sqrt]; linarith
  have hpsi : psi h Commons.Geometry.Ulam.semicircle s t = 1 - t ^ 2 - (s * t + h s) ^ 2 := by
    simp only [psi, hsem, line]
  rw [hpsi]
  by_cases hsle : s ≤ 9 / 10
  · have hh : |h s| ≤ 1 / 100 := hsmall s
    have h1 : |s * t + h s| ≤ s * |t| + |h s| := by
      calc |s * t + h s| ≤ |s * t| + |h s| := abs_add_le _ _
        _ = s * |t| + |h s| := by rw [abs_mul, abs_of_pos hs0]
    have h6 : s * |t| < (9 / 10) * (3 / 4) := by
      have h5 : s * |t| ≤ (9 / 10) * Commons.Geometry.Ulam.profileX 1 :=
        mul_le_mul hsle htabs (abs_nonneg t) (by norm_num)
      nlinarith [h5, hXlt]
    have h2 : s * |t| + |h s| < 9 / 10 * (3 / 4) + 1 / 100 := by
      linarith [(abs_le.mp hh).2]
    have h3 : (s * t + h s) ^ 2 < (9 / 10 * (3 / 4) + 1 / 100) ^ 2 := by
      calc (s * t + h s) ^ 2 = |s * t + h s| ^ 2 := (sq_abs _).symm
        _ < _ := pow_lt_pow_left₀ (by linarith) (abs_nonneg _) (by norm_num)
    have h4 : (9 / 10 * (3 / 4) + 1 / 100 : ℝ) ^ 2 < 1 / 2 := by norm_num
    linarith
  · push_neg at hsle
    have hhs : h s = 0 := by
      by_contra hne
      have hmem : s ∈ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) :=
        hsupp (Function.mem_support.mpr hne)
      rw [Work.OddVolterra.tau] at hmem
      norm_num at hmem
      linarith [hmem.2]
    rw [hhs, add_zero]
    nlinarith [ht2, hs0, hs1, sq_nonneg s]


/-! ## Continuity of the derivative of the Abel transform

The last two components of the source `Xi` are `deriv (u ↦ ∫_u^1 Q v / √(v-u) dv)`.  The
following lemma shows that this is continuous on `(a,c) ⊂ (0,1)` for a function `Q` that is
continuous on `[a,1]` and `C¹` on `(a,e)` with `e > c`.

The proof splits the integral at a point `c'` with `c < c' < min e 1`:

* the piece `∫_{c'}^1 (√(v-u))⁻¹ Q v dv` has no singularity for `u ≤ c` (`v - u ≥ c' - c > 0`),
  so it may be differentiated under the integral sign;
* the piece `∫_u^{c'} (√(v-u))⁻¹ Q v dv = 2 √(c'-u) ∫_0^1 Q (u + (c'-u)t²) dt`, and the
  arguments `u + (c'-u)t²` all lie in `[u,c'] ⊂ (a,e)` where `Q` is `C¹`; the product rule and
  differentiation under the integral sign (the weight `1 - t²` vanishes at `t = 1`, so only
  interior points matter) give the derivative.
-/

theorem wdr_continuousOn_deriv_abel_transform {a c e : ℝ} (ha : 0 < a) (hac : a < c)
    (hc1 : c < 1) (hce : c < e) {Q : ℝ → ℝ} (hQcont : ContinuousOn Q (Set.Icc a 1))
    (hQsmooth : ContDiffOn ℝ 1 Q (Set.Ioo a e)) :
    ContinuousOn (fun s : ℝ => deriv (fun u : ℝ => ∫ v in u..1, Q v / Real.sqrt (v - u)) s)
      (Set.Ioo a c) := by
  have hQderiv_cont : ContinuousOn (deriv Q) (Set.Ioo a e) :=
    hQsmooth.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hQderiv : ∀ w ∈ Set.Ioo a e, HasDerivAt Q (deriv Q w) w := by
    intro w hw
    exact ((hQsmooth.contDiffAt (isOpen_Ioo.mem_nhds hw)).differentiableAt (by norm_num)).hasDerivAt
  -- the split point
  set c' : ℝ := (c + min e 1) / 2 with hc'def
  have hcc' : c < c' := by rw [hc'def]; linarith [lt_min hce hc1]
  have hc'e : c' < e := by rw [hc'def]; linarith [min_le_left e 1]
  have hc'1 : c' < 1 := by rw [hc'def]; linarith [min_le_right e 1]
  have hc'a : a < c' := lt_trans hac hcc'
  -- the manifest pieces
  set F : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..1, Q (s + (c' - s) * u ^ 2) with hFdef
  set F' : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..1, deriv Q (s + (c' - s) * u ^ 2) * (1 - u ^ 2)
    with hF'def
  set G : ℝ → ℝ := fun s => ∫ v in c'..1, Q v / Real.sqrt (v - s) with hGdef
  set G' : ℝ → ℝ := fun s => ∫ v in c'..1, (2 * (Real.sqrt (v - s)) ^ 3)⁻¹ * Q v with hG'def
  set T : ℝ → ℝ := fun u => ∫ v in u..1, Q v / Real.sqrt (v - u) with hTdef
  set R : ℝ → ℝ := fun s => -(1 / Real.sqrt (c' - s)) * F s + 2 * Real.sqrt (c' - s) * F' s
    + G' s with hRdef
  -- the arguments of `Q` stay inside `(a,e)` on a closed subinterval of `(a,c)`
  have hargs : ∀ {s₁ s₂ s u : ℝ}, a < s₁ → s₂ < c → s ∈ Set.Icc s₁ s₂ →
      u ∈ Set.Icc (0 : ℝ) 1 → s + (c' - s) * u ^ 2 ∈ Set.Ioo a e := by
    intro s₁ s₂ s u hs₁ hs₂ hs hu
    have hu0 : 0 ≤ u ^ 2 := sq_nonneg u
    have hu1 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    have hsc' : s < c' := lt_trans (lt_of_le_of_lt hs.2 hs₂) hcc'
    have hnonneg : 0 ≤ (c' - s) * u ^ 2 := mul_nonneg (by linarith) hu0
    have hmul : (c' - s) * u ^ 2 ≤ c' - s := by
      have h := mul_le_mul_of_nonneg_left hu1 (by linarith : (0 : ℝ) ≤ c' - s)
      simpa using h
    exact ⟨by linarith [hs.1], by linarith⟩
  -- ## the two manifest derivatives
  have hF_deriv : ∀ s₀ ∈ Set.Ioo a c, HasDerivAt F (F' s₀) s₀ := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    set δ : ℝ := min (s₀ - a) (c - s₀) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min (by linarith) (by linarith))
    have hs₁a : a < s₀ - δ := by
      have h := min_le_left (s₀ - a) (c - s₀)
      rw [hδdef]; linarith
    have hs₂c : s₀ + δ < c := by
      have h := min_le_right (s₀ - a) (c - s₀)
      rw [hδdef]; linarith
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Q (p.1 + (c' - p.1) * p.2 ^ 2))
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
      refine hQsmooth.continuousOn.comp (by fun_prop) ?_
      rintro ⟨s, u⟩ ⟨hs, hu⟩
      exact hargs hs₁a hs₂c hs ⟨hu.1, hu.2⟩
    have hcont' : ContinuousOn (fun p : ℝ × ℝ =>
        deriv Q (p.1 + (c' - p.1) * p.2 ^ 2) * (1 - p.2 ^ 2))
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => deriv Q (p.1 + (c' - p.1) * p.2 ^ 2))
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
        refine hQderiv_cont.comp (by fun_prop) ?_
        rintro ⟨s, u⟩ ⟨hs, hu⟩
        exact hargs hs₁a hs₂c hs ⟨hu.1, hu.2⟩
      exact h1.mul (by fun_prop)
    have hpt : ∀ s ∈ Set.Icc (s₀ - δ) (s₀ + δ), ∀ u ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun y : ℝ => Q (y + (c' - y) * u ^ 2))
          (deriv Q (s + (c' - s) * u ^ 2) * (1 - u ^ 2)) s := by
      intro s hs u hu
      have hinner : HasDerivAt (fun y : ℝ => y + (c' - y) * u ^ 2) (1 - u ^ 2) s := by
        have h1 : HasDerivAt (fun y : ℝ => (c' - y) * u ^ 2) (-(u ^ 2)) s := by
          have h := ((hasDerivAt_id s).const_sub c').mul_const (u ^ 2)
          simpa using h
        have h2 : HasDerivAt (fun y : ℝ => y + (c' - y) * u ^ 2) (1 + -(u ^ 2)) s :=
          (hasDerivAt_id s).add h1
        exact h2.congr_deriv (by ring)
      have houter : HasDerivAt Q (deriv Q (s + (c' - s) * u ^ 2))
          (s + (c' - s) * u ^ 2) :=
        hQderiv _ (hargs hs₁a hs₂c hs ⟨hu.1, hu.2⟩)
      exact houter.comp s hinner
    have h := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_of_le
      (F := fun s u => Q (s + (c' - s) * u ^ 2))
      (F' := fun s u => deriv Q (s + (c' - s) * u ^ 2) * (1 - u ^ 2))
      (s₀ := s₀) (s₁ := s₀ - δ) (s₂ := s₀ + δ) (a := (0 : ℝ)) (b := 1)
      (by linarith) (by linarith) (by norm_num) hcont hcont' hpt
    simpa only [hFdef, hF'def] using h
  have hG_deriv : ∀ s₀ ∈ Set.Ioo a c, HasDerivAt G (G' s₀) s₀ := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    set δ : ℝ := min (s₀ - a) (c - s₀) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min (by linarith) (by linarith))
    have hs₂c : s₀ + δ < c := by
      have h := min_le_right (s₀ - a) (c - s₀)
      rw [hδdef]; linarith
    have hQbox : ContinuousOn Q (Set.Icc c' 1) :=
      hQcont.mono (fun x hx => ⟨le_trans hc'a.le hx.1, hx.2⟩)
    have hpos : ∀ s ∈ Set.Icc (s₀ - δ) (s₀ + δ), ∀ v ∈ Set.Icc c' 1, 0 < v - s := by
      intro s hs v hv
      have h2 := hs.2
      linarith [hv.1, hs₂c, hcc']
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Q p.2 / Real.sqrt (p.2 - p.1))
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) := by
      have hnum : ContinuousOn (fun p : ℝ × ℝ => Q p.2)
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) :=
        hQbox.comp (by fun_prop) (fun p hp => ⟨hp.2.1, hp.2.2⟩)
      have hden : ContinuousOn (fun p : ℝ × ℝ => Real.sqrt (p.2 - p.1))
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) := by fun_prop
      exact hnum.div hden (fun p hp => ne_of_gt (Real.sqrt_pos.mpr (hpos p.1 hp.1 p.2 hp.2)))
    have hcont' : ContinuousOn (fun p : ℝ × ℝ =>
        (2 * (Real.sqrt (p.2 - p.1)) ^ 3)⁻¹ * Q p.2)
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) := by
      have hnum : ContinuousOn (fun p : ℝ × ℝ => Q p.2)
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) :=
        hQbox.comp (by fun_prop) (fun p hp => ⟨hp.2.1, hp.2.2⟩)
      have hden : ContinuousOn (fun p : ℝ × ℝ => (2 * (Real.sqrt (p.2 - p.1)) ^ 3)⁻¹)
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) := by
        refine ContinuousOn.inv₀ (by fun_prop) ?_
        intro p hp
        have hp0 : 0 < p.2 - p.1 := hpos p.1 hp.1 p.2 hp.2
        exact ne_of_gt (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr hp0) 3))
      exact hden.mul hnum
    have hpt : ∀ s ∈ Set.Icc (s₀ - δ) (s₀ + δ), ∀ v ∈ Set.Icc c' 1,
        HasDerivAt (fun y : ℝ => Q v / Real.sqrt (v - y))
          ((2 * (Real.sqrt (v - s)) ^ 3)⁻¹ * Q v) s := by
      intro s hs v hv
      have hvs : 0 < v - s := hpos s hs v hv
      have hsne : Real.sqrt (v - s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hvs)
      have hlin : HasDerivAt (fun y : ℝ => v - y) (-1) s := (hasDerivAt_id s).const_sub v
      have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (v - s))) (v - s) :=
        Real.hasDerivAt_sqrt (ne_of_gt hvs)
      have hkey : (-((Real.sqrt (v - s)) ^ 2)⁻¹) * ((1 / (2 * Real.sqrt (v - s))) * (-1))
          = (2 * (Real.sqrt (v - s)) ^ 3)⁻¹ := by
        have hr2 : (Real.sqrt (v - s)) ^ 2 ≠ 0 := pow_ne_zero _ hsne
        have hr3 : 2 * (Real.sqrt (v - s)) ^ 3 ≠ 0 := by
          exact ne_of_gt (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr hvs) 3))
        field_simp
      have hk : HasDerivAt (fun y : ℝ => (Real.sqrt (v - y))⁻¹)
          ((2 * (Real.sqrt (v - s)) ^ 3)⁻¹) s :=
        ((hasDerivAt_inv hsne).comp s (hsqrt.comp s hlin)).congr_deriv hkey
      have hk' := hk.mul_const (Q v)
      refine hk'.congr_of_eventuallyEq ?_
      filter_upwards with y
      rw [div_eq_mul_inv, mul_comm]
    have h := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_of_le
      (F := fun s v => Q v / Real.sqrt (v - s))
      (F' := fun s v => (2 * (Real.sqrt (v - s)) ^ 3)⁻¹ * Q v)
      (s₀ := s₀) (s₁ := s₀ - δ) (s₂ := s₀ + δ) (a := c') (b := 1)
      (by linarith) (by linarith) (le_of_lt hc'1) hcont hcont' hpt
    simpa only [hGdef, hG'def] using h
  -- ## the splitting identity and the product rule for the moving piece
  have habel : ∀ s ≤ c',
      (∫ v in s..c', Q v / Real.sqrt (v - s)) = 2 * Real.sqrt (c' - s) * F s := by
    intro s hsc'
    have h := Commons.Analysis.Abel.intervalIntegral_abel_subst (x := s) (b := c') hsc'
      (K := fun _ v => Q v)
    have hcongr : (∫ v in s..c', Q v / Real.sqrt (v - s))
        = ∫ σ in s..c', (Real.sqrt (σ - s))⁻¹ * Q σ := by
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      rw [div_eq_mul_inv, mul_comm]
    rw [hcongr, hFdef]
    simpa only [smul_eq_mul] using h
  have hA_deriv : ∀ s₀ ∈ Set.Ioo a c,
      HasDerivAt (fun s : ℝ => ∫ v in s..c', Q v / Real.sqrt (v - s))
        (2 * Real.sqrt (c' - s₀) * F' s₀ - F s₀ / Real.sqrt (c' - s₀)) s₀ := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    have hs₀c' : s₀ < c' := lt_trans hs₀c hcc'
    have hne : c' - s₀ ≠ 0 := ne_of_gt (by linarith)
    have hr : Real.sqrt (c' - s₀) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
    have hsqrt : HasDerivAt (fun s : ℝ => 2 * Real.sqrt (c' - s))
        (-(1 / Real.sqrt (c' - s₀))) s₀ := by
      have h1 : HasDerivAt (fun s : ℝ => c' - s) (-1) s₀ := (hasDerivAt_id s₀).const_sub c'
      have h2 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (c' - s₀))) (c' - s₀) :=
        Real.hasDerivAt_sqrt hne
      have h3 := (h2.comp s₀ h1).const_mul 2
      refine h3.congr_deriv ?_
      field_simp
    have hprod : HasDerivAt (fun s : ℝ => 2 * Real.sqrt (c' - s) * F s)
        (2 * Real.sqrt (c' - s₀) * F' s₀ - F s₀ / Real.sqrt (c' - s₀)) s₀ :=
      (hsqrt.mul (hF_deriv s₀ ⟨hs₀a, hs₀c⟩)).congr_deriv (by rw [div_eq_mul_inv]; ring)
    refine hprod.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds hs₀c'] with s hs
    exact habel s (le_of_lt hs)
  -- ## the derivative of `T`
  have hsplit : ∀ s ∈ Set.Ioo a c, T s = (∫ v in s..c', Q v / Real.sqrt (v - s)) + G s := by
    intro s hs
    obtain ⟨hsa, hsc⟩ := hs
    have hsc' : s ≤ c' := le_of_lt (lt_trans hsc hcc')
    have hcontQ : ContinuousOn Q (Set.uIcc s c') := by
      rw [Set.uIcc_of_le hsc']
      exact hQcont.mono (fun x hx => ⟨le_trans hsa.le hx.1, le_trans hx.2 hc'1.le⟩)
    have hg : ContinuousOn (fun v : ℝ => Q v - 0) (Set.uIcc s c') :=
      hcontQ.sub continuousOn_const
    have hint1 : IntervalIntegrable (fun v : ℝ => Q v / Real.sqrt (v - s)) volume s c' := by
      have h := (Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub
        (lt_trans hsc hcc')).smul_continuousOn hg
      have h2 : (fun v : ℝ => (Real.sqrt (v - s))⁻¹ • (Q v - 0))
          = fun v : ℝ => Q v / Real.sqrt (v - s) := by
        funext v
        rw [smul_eq_mul, sub_zero, div_eq_mul_inv, mul_comm]
      rw [← h2]
      exact h
    have hint2 : IntervalIntegrable (fun v : ℝ => Q v / Real.sqrt (v - s)) volume c' 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (le_of_lt hc'1)]
      refine ContinuousOn.div ?_ ?_ ?_
      · exact hQcont.mono (fun x hx => ⟨le_trans hc'a.le hx.1, hx.2⟩)
      · exact (Real.continuous_sqrt.comp_continuousOn (continuousOn_id.sub continuousOn_const))
      · intro v hv
        exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hv.1, hsc, hcc']))
    have h := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    rw [hTdef, hGdef]
    exact h.symm
  have hT_deriv : ∀ s₀ ∈ Set.Ioo a c, HasDerivAt T (R s₀) s₀ := by
    intro s₀ hs₀
    have hsum := (hA_deriv s₀ hs₀).add (hG_deriv s₀ hs₀)
    have hR : (2 * Real.sqrt (c' - s₀) * F' s₀ - F s₀ / Real.sqrt (c' - s₀)) + G' s₀ = R s₀ := by
      simp only [hRdef, div_eq_mul_inv]
      ring
    refine (hsum.congr_of_eventuallyEq ?_).congr_deriv hR
    filter_upwards [isOpen_Ioo.mem_nhds hs₀] with s hs
    exact hsplit s hs
  -- ## continuity of the manifest derivative
  have hF_cont : ContinuousOn F (Set.Ioo a c) := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    set δ : ℝ := min (s₀ - a) (c - s₀) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min (by linarith) (by linarith))
    have hs₁a : a < s₀ - δ := by
      have h := min_le_left (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hs₂c : s₀ + δ < c := by
      have h := min_le_right (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hmem : Set.Icc (s₀ - δ) (s₀ + δ) ∈ 𝓝 s₀ :=
      Icc_mem_nhds (by linarith) (by linarith)
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Q (p.1 + (c' - p.1) * p.2 ^ 2))
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      refine hQsmooth.continuousOn.comp (by fun_prop) ?_
      rintro ⟨s, u⟩ ⟨hs, hu⟩
      exact hargs hs₁a hs₂c hs ⟨hu.1, hu.2⟩
    have h := Commons.Analysis.Abel.continuousOn_intervalIntegral_of_continuousOn_compact
      (s := Set.Icc (s₀ - δ) (s₀ + δ)) isCompact_Icc (A := (0 : ℝ)) (B := 1)
      (by norm_num) (F := fun s u => Q (s + (c' - s) * u ^ 2)) hcont
    have h2 : ContinuousOn F (Set.Icc (s₀ - δ) (s₀ + δ)) := by
      simpa only [hFdef] using h
    exact (h2.continuousAt hmem).continuousWithinAt
  have hF'_cont : ContinuousOn F' (Set.Ioo a c) := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    set δ : ℝ := min (s₀ - a) (c - s₀) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min (by linarith) (by linarith))
    have hs₁a : a < s₀ - δ := by
      have h := min_le_left (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hs₂c : s₀ + δ < c := by
      have h := min_le_right (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hmem : Set.Icc (s₀ - δ) (s₀ + δ) ∈ 𝓝 s₀ :=
      Icc_mem_nhds (by linarith) (by linarith)
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        deriv Q (p.1 + (c' - p.1) * p.2 ^ 2) * (1 - p.2 ^ 2))
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      have h1 : ContinuousOn (fun p : ℝ × ℝ => deriv Q (p.1 + (c' - p.1) * p.2 ^ 2))
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
        refine hQderiv_cont.comp (by fun_prop) ?_
        rintro ⟨s, u⟩ ⟨hs, hu⟩
        exact hargs hs₁a hs₂c hs ⟨hu.1, hu.2⟩
      exact h1.mul (by fun_prop)
    have h := Commons.Analysis.Abel.continuousOn_intervalIntegral_of_continuousOn_compact
      (s := Set.Icc (s₀ - δ) (s₀ + δ)) isCompact_Icc (A := (0 : ℝ)) (B := 1)
      (by norm_num) (F := fun s u => deriv Q (s + (c' - s) * u ^ 2) * (1 - u ^ 2)) hcont
    have h2 : ContinuousOn F' (Set.Icc (s₀ - δ) (s₀ + δ)) := by
      simpa only [hF'def] using h
    exact (h2.continuousAt hmem).continuousWithinAt
  have hG'_cont : ContinuousOn G' (Set.Ioo a c) := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    set δ : ℝ := min (s₀ - a) (c - s₀) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min (by linarith) (by linarith))
    have hs₂c : s₀ + δ < c := by
      have h := min_le_right (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hmem : Set.Icc (s₀ - δ) (s₀ + δ) ∈ 𝓝 s₀ :=
      Icc_mem_nhds (by linarith) (by linarith)
    have hQbox : ContinuousOn Q (Set.Icc c' 1) :=
      hQcont.mono (fun x hx => ⟨le_trans hc'a.le hx.1, hx.2⟩)
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (2 * (Real.sqrt (p.2 - p.1)) ^ 3)⁻¹ * Q p.2)
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.uIcc c' 1) := by
      rw [Set.uIcc_of_le (le_of_lt hc'1)]
      have hnum : ContinuousOn (fun p : ℝ × ℝ => Q p.2)
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) :=
        hQbox.comp (by fun_prop) (fun p hp => ⟨hp.2.1, hp.2.2⟩)
      have hden : ContinuousOn (fun p : ℝ × ℝ => (2 * (Real.sqrt (p.2 - p.1)) ^ 3)⁻¹)
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) := by
        refine ContinuousOn.inv₀ (by fun_prop) ?_
        intro p hp
        have hp0 : 0 < p.2 - p.1 := by linarith [hp.2.1, hp.1.2, hs₂c, hcc']
        exact ne_of_gt (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr hp0) 3))
      exact hden.mul hnum
    have h := Commons.Analysis.Abel.continuousOn_intervalIntegral_of_continuousOn_compact
      (s := Set.Icc (s₀ - δ) (s₀ + δ)) isCompact_Icc (A := c') (B := 1)
      (le_of_lt hc'1) (F := fun s v => (2 * (Real.sqrt (v - s)) ^ 3)⁻¹ * Q v) hcont
    have h2 : ContinuousOn G' (Set.Icc (s₀ - δ) (s₀ + δ)) := by
      simpa only [hG'def] using h
    exact (h2.continuousAt hmem).continuousWithinAt
  have hR_cont : ContinuousOn R (Set.Ioo a c) := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    set δ : ℝ := min (s₀ - a) (c - s₀) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min (by linarith) (by linarith))
    have hs₁a : a < s₀ - δ := by
      have h := min_le_left (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hs₂c : s₀ + δ < c := by
      have h := min_le_right (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hmem : Set.Icc (s₀ - δ) (s₀ + δ) ∈ 𝓝 s₀ :=
      Icc_mem_nhds (by linarith) (by linarith)
    have hsub : Set.Icc (s₀ - δ) (s₀ + δ) ⊆ Set.Ioo a c :=
      fun s hs => ⟨lt_of_lt_of_le hs₁a hs.1, lt_of_le_of_lt hs.2 hs₂c⟩
    have hFac : ContinuousOn F (Set.Icc (s₀ - δ) (s₀ + δ)) := hF_cont.mono hsub
    have hFac' : ContinuousOn F' (Set.Icc (s₀ - δ) (s₀ + δ)) := hF'_cont.mono hsub
    have hGac : ContinuousOn G' (Set.Icc (s₀ - δ) (s₀ + δ)) := hG'_cont.mono hsub
    have hsqrtc : ContinuousOn (fun s : ℝ => Real.sqrt (c' - s)) (Set.Icc (s₀ - δ) (s₀ + δ)) :=
      Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub continuousOn_id)
    have hne : ∀ s ∈ Set.Icc (s₀ - δ) (s₀ + δ), Real.sqrt (c' - s) ≠ 0 := by
      intro s hs
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hs.2, hs₂c, hcc']))
    have h1 : ContinuousOn (fun s : ℝ => -(1 / Real.sqrt (c' - s))) (Set.Icc (s₀ - δ) (s₀ + δ)) :=
      (continuousOn_const.div hsqrtc hne).neg
    have h2 : ContinuousOn (fun s : ℝ => 2 * Real.sqrt (c' - s) * F' s)
        (Set.Icc (s₀ - δ) (s₀ + δ)) :=
      (continuousOn_const.mul hsqrtc).mul hFac'
    have hA : ContinuousOn (fun s : ℝ => -(1 / Real.sqrt (c' - s)) * F s)
        (Set.Icc (s₀ - δ) (s₀ + δ)) :=
      h1.mul hFac
    have hK : ContinuousOn R (Set.Icc (s₀ - δ) (s₀ + δ)) := by
      rw [hRdef]
      exact (hA.add h2).add hGac
    exact (hK.continuousAt hmem).continuousWithinAt
  -- ## conclusion
  refine hR_cont.congr (fun s hs => ?_)
  exact (hT_deriv s hs).deriv


/-! ## Continuity of the source `Xi`

`Xi n h s = ![(profileX 1), (profileX 1), (Qtilde n h s) 0, (Qtilde n h s) 1]`, and the last two
components are the derivative of the Abel transform of the components of `Q n h`.  `Q` is
continuous on `[13/20, 1]` and `C²` on every `[13/20, b]` with `b < 1` (`Q_regularity`, whose
non-degeneracy hypothesis is `wdr_psi_semicircle_pos_small`), so
`wdr_continuousOn_deriv_abel_transform` applies with `a = 13/20`, `c = 99/100`,
`e = 997/1000`.
-/

lemma wdr_continuousOn_Xi (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContinuousOn (fun s : ℝ => Xi n h s) (Set.Ioo (13 / 20 : ℝ) (99 / 100)) := by
  have h0 : (0 : ℝ) < 13 / 20 := by norm_num
  have hlt1 : (99 / 100 : ℝ) < 1 := by norm_num
  have hlt : (99 / 100 : ℝ) < 997 / 1000 := by norm_num
  have hsmall0 : ∀ t : ℝ, |h t| ≤ 1 / 100 := fun t => by
    simpa using hsmall 0 (by norm_num) t
  have hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1))
        (Commons.Geometry.Ulam.profileX 1),
      0 < psi h Commons.Geometry.Ulam.semicircle s t :=
    wdr_psi_semicircle_pos_small hsupp hsmall0
  obtain ⟨hQcont, hQsmooth⟩ := Smooth.Q_regularity n hn hh h0 hsupp hsmall0 hmid
  have hQtilde : ∀ i : Fin 2, ContinuousOn (fun s : ℝ =>
      deriv (fun u : ℝ => ∫ v in u..1, (Q n h v) i / Real.sqrt (v - u)) s)
      (Set.Ioo (13 / 20 : ℝ) (99 / 100)) := by
    intro i
    have hcont_i : ContinuousOn (fun v : ℝ => (Q n h v) i) (Set.Icc (13 / 20) 1) :=
      (continuousOn_pi.mp hQcont) i
    have hsm2 : ContDiffOn ℝ 2 (Q n h) (Set.Icc (13 / 20) (999 / 1000)) :=
      hQsmooth (999 / 1000) (by norm_num) (by norm_num)
    have hsm1 : ContDiffOn ℝ 1 (fun v : ℝ => (Q n h v) i)
        (Set.Ioo (13 / 20 : ℝ) (997 / 1000)) := by
      refine ((contDiffOn_pi.mp (hsm2.mono ?_)) i).of_le ?_
      · intro x hx
        exact ⟨le_of_lt hx.1, by linarith [hx.2]⟩
      · norm_num
    exact wdr_continuousOn_deriv_abel_transform h0 (by norm_num) hlt1 hlt hcont_i hsm1
  rw [continuousOn_pi]
  intro i
  fin_cases i
  · show ContinuousOn (fun s : ℝ => (Xi n h s) 0) (Set.Ioo (13 / 20 : ℝ) (99 / 100))
    have h : (fun s : ℝ => (Xi n h s) 0) = fun _ : ℝ => Commons.Geometry.Ulam.profileX 1 := by
      funext s; simp [Xi]
    rw [h]; exact continuousOn_const
  · show ContinuousOn (fun s : ℝ => (Xi n h s) 1) (Set.Ioo (13 / 20 : ℝ) (99 / 100))
    have h : (fun s : ℝ => (Xi n h s) 1) = fun _ : ℝ => Commons.Geometry.Ulam.profileX 1 := by
      funext s; simp [Xi]
    rw [h]; exact continuousOn_const
  · show ContinuousOn (fun s : ℝ => (Xi n h s) 2) (Set.Ioo (13 / 20 : ℝ) (99 / 100))
    have h : (fun s : ℝ => (Xi n h s) 2) = fun s : ℝ =>
        deriv (fun u : ℝ => ∫ v in u..1, (Q n h v) 0 / Real.sqrt (v - u)) s := by
      funext s; simp [Xi, Qtilde]
    rw [h]; exact hQtilde 0
  · show ContinuousOn (fun s : ℝ => (Xi n h s) 3) (Set.Ioo (13 / 20 : ℝ) (99 / 100))
    have h : (fun s : ℝ => (Xi n h s) 3) = fun s : ℝ =>
        deriv (fun u : ℝ => ∫ v in u..1, (Q n h v) 1 / Real.sqrt (v - u)) s := by
      funext s; simp [Xi, Qtilde]
    rw [h]; exact hQtilde 1

/-- Continuity of the frozen tail `s ↦ ∫_{wC}^1 Θ(s,σ,baseState σ)dσ`. -/
lemma wdr_continuousOn_tail (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContinuousOn (fun s : ℝ =>
        ∫ σ in Existence.wC..(1 : ℝ), KernelExt.ThetaM n h s σ (baseState σ))
      (Set.Ioo (13 / 20 : ℝ) (99 / 100)) := by
  have hmap : Continuous (fun p : ℝ × ℝ => (p.1, p.2, baseState p.2)) :=
    continuous_fst.prodMk (continuous_snd.prodMk (wdr_continuous_baseState.comp continuous_snd))
  have hK : ContinuousOn (fun p : ℝ × ℝ => KernelExt.ThetaM n h p.1 p.2 (baseState p.2))
      (Set.Icc (13 / 20 : ℝ) (99 / 100) ×ˢ Set.uIcc (19 / 20 : ℝ) 1) := by
    refine (Work.Anchor.ThetaM_contDiffOn_Good n hh hsmall).continuousOn.comp hmap.continuousOn ?_
    rintro ⟨s, σ⟩ ⟨hs, hσ⟩
    rw [Set.uIcc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)] at hσ
    have hσabs : |σ| ≤ 21 / 20 := by
      rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
    have hpx : 17 / 25 ≤ Commons.Geometry.Ulam.profileX σ := wdr_profileX_ge_17_25 hσabs
    have hb : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
    have hb1 : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
    refine ⟨by linarith [hs.1], by linarith [hs.2], by linarith [hσ.1], by linarith [hσ.2],
      ?_, ?_⟩
    · show (1 : ℝ) / 5 < |baseState σ 0|
      rw [hb, abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 17 / 25) hpx)]
      linarith
    · show (1 : ℝ) / 5 < |baseState σ 1|
      rw [hb1, abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 17 / 25) hpx)]
      linarith
  have h := Commons.Analysis.Abel.continuousOn_intervalIntegral_of_continuousOn_compact
    (s := Set.Icc (13 / 20 : ℝ) (99 / 100)) isCompact_Icc (A := Existence.wC) (B := 1)
    (by rw [Existence.wC]; norm_num)
    (F := fun s σ => KernelExt.ThetaM n h s σ (baseState σ)) hK
  exact h.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)

/-! ## The regularity package -/

lemma wdr_tsupport_cs_subset :
    tsupport (fun s : ℝ => (Existence.cs : ℝ → ℝ) s) ⊆ Set.Ioo (13 / 20 : ℝ) (99 / 100) := by
  have hsupp_cs : Function.support (fun s : ℝ => (Existence.cs : ℝ → ℝ) s) ⊆
      Set.Icc (Existence.wCenter - 4 / 25) (Existence.wCenter + 4 / 25) := by
    intro s hs
    have h : |s - Existence.wCenter| < 4 / 25 := by
      by_contra h
      exact hs (Existence.cs_zero (le_of_not_gt h))
    rw [abs_lt] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hts := closure_minimal hsupp_cs isClosed_Icc
  refine fun s hs => ?_
  have h := hts hs
  rw [Existence.wCenter] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem window_data_regular (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    (Continuous (fun p : ℝ × Work.OddVolterra.St =>
        Work.OddVolterra.Existence.GoddW n h p.1 p.2)) ∧
    (Continuous (fun p : (ℝ × ℝ) × Work.OddVolterra.St =>
        Work.OddVolterra.Existence.ThetaW n h p.1.1 p.1.2 p.2)) ∧
    (Continuous (Work.OddVolterra.Existence.XiW n h)) ∧
    (∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC,
      ∀ σ ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC,
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) 1,
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState σ) 1,
      ‖Work.OddVolterra.Existence.ThetaW n h s σ z -
        Work.OddVolterra.Existence.ThetaW n h s σ z'‖ ≤ L * ‖z - z'‖) ∧
    (∀ s ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC,
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) 1,
      DifferentiableAt ℝ
        (fun w : Work.OddVolterra.St => Work.OddVolterra.Existence.GoddW n h s w) z) := by
  have hcontG := wdr_contDiff_goddW n hn hh hsupp hsmall
  have hcontT := wdr_contDiff_thetaW n hh hsmall
  refine ⟨hcontG.continuous, hcontT.continuous, ?_, ?_, ?_⟩
  · -- continuity of the cut-off source
    have hXi := (wdr_continuousOn_Xi n hn hh hsupp hsmall).add (wdr_continuousOn_tail n hh hsmall)
    have hcs : Continuous (fun s : ℝ => (Existence.cs : ℝ → ℝ) s) :=
      ContDiffBump.continuous Existence.cs
    have h := wdr_continuous_smul_of_continuousOn (X := ℝ) (E := St)
      (f := fun s : ℝ => (Existence.cs : ℝ → ℝ) s)
      (g := fun s : ℝ => Xi n h s +
        ∫ σ in Existence.wC..(1 : ℝ), KernelExt.ThetaM n h s σ (baseState σ))
      (U := Set.Ioo (13 / 20 : ℝ) (99 / 100)) isOpen_Ioo hcs hXi wdr_tsupport_cs_subset
    exact h.congr (fun s => by rw [Existence.XiW])
  · -- Lipschitz continuity of the `Θ`-datum in the state
    obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
      (wdr_hasCompactSupport_thetaW n h) hcontT (by simp)
    refine ⟨(C : ℝ), C.coe_nonneg, ?_⟩
    intro s hs σ hσ z hz z' hz'
    have hdist := hC.dist_le_mul (x := ((s, σ), z)) (y := ((s, σ), z'))
    have h1 : dist (Existence.ThetaW n h s σ z) (Existence.ThetaW n h s σ z')
        = ‖Existence.ThetaW n h s σ z - Existence.ThetaW n h s σ z'‖ := dist_eq_norm _ _
    have h2 : dist (((s, σ), z) : (ℝ × ℝ) × St) (((s, σ), z')) = ‖z - z'‖ := by
      rw [dist_eq_norm, Prod.norm_def, Prod.norm_def]
      simp
    rw [h1, h2] at hdist
    exact hdist
  · -- state-differentiability of the `G`-datum
    intro s hs z hz
    have hd : DifferentiableAt ℝ (fun p : ℝ × St => Existence.GoddW n h p.1 p.2) (s, z) :=
      (hcontG.differentiable (by simp)).differentiableAt
    have hmap : DifferentiableAt ℝ (fun w : St => (s, w)) z :=
      (differentiableAt_const s).prodMk differentiableAt_id
    exact hd.comp z hmap

end

end Work.OddVolterra.Window
