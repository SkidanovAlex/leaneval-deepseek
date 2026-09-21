import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Window.WindowDefs
import Submission.Work.Anchor.deriv_close
import Submission.Work.OddVolterra.Window.window_data_regular

/-!
# Closeness of the differential of the cut-off window datum `GW`

`Work.OddVolterra.Window.GW n h s z = chiG s z • Godd n h s z` is the state datum fed to the
long-interval Volterra engine for the odd transition-slope window `[7/10, 19/20]`
(`Work.OddVolterra.Window.WindowDefs`).  The engine needs the estimate

`‖fderiv (GW n h s) z - fderiv (GW n 0 s) (baseState s)‖ ≤ Cg ‖z - baseState s‖ + ε`

for `s ∈ [7/10, 19/20]` and `z` in the ball of radius `1` around the base state, uniformly over
perturbations `h` supported in `[1 - 2τ, 1 - τ]` and small in `C^{n+2}`.

The proof splits the ball around the base state.

* For `‖z - baseState s‖ < 1/5` the state cut-off `chiG` is locally `1` (it equals
  `cs s * cz ‖· - baseState s‖` with `cs s = 1` on the window and `cz = 1` on the ball of radius
  `1/5`), so `GW n h s` agrees with `Godd n h s` near `z`; there the estimate is exactly
  `Work.Anchor.deriv_close`.
* For `‖z - baseState s‖ ≥ 1/5` we merely need *some* bound, since `Cg` may be chosen large.
  For `‖z - baseState s‖ > 2/5` the cut-off `cz` vanishes on a neighbourhood, so the differential
  vanishes; for `‖z - baseState s‖ ≤ 2/5` the bound is the Lipschitz constant of
  `GW n h s` on the tube `‖z - baseState s‖ ≤ 7/16`, obtained from the joint smoothness of
  `Godd` (`wdr_contDiffOn_godd` on `Existence.awGood`) and the Lipschitz property of `cz`.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## The base state is continuous, and the good region is open -/

lemma continuous_baseState_win : Continuous (baseState : ℝ → Work.OddVolterra.St) :=
  Work.OddCurveB.Est.continuous_baseState

lemma isOpen_awGood : IsOpen (Work.OddVolterra.Existence.awGood : Set (ℝ × Work.OddVolterra.St)) := by
  have h : Work.OddVolterra.Existence.awGood =
      {p : ℝ × Work.OddVolterra.St | (9 / 20 : ℝ) < p.1} ∩
      {p : ℝ × Work.OddVolterra.St | p.1 < 21 / 20} ∩
      {p : ℝ × Work.OddVolterra.St | (1 / 5 : ℝ) < |p.2 0|} ∩
      {p : ℝ × Work.OddVolterra.St | (1 / 5 : ℝ) < |p.2 1|} := by
    ext p
    simp only [Work.OddVolterra.Existence.awGood, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [h]
  refine IsOpen.inter (IsOpen.inter (IsOpen.inter ?_ ?_) ?_) ?_
  · exact isOpen_lt continuous_const continuous_fst
  · exact isOpen_lt continuous_fst continuous_const
  · exact isOpen_lt continuous_const (continuous_abs.comp ((continuous_apply 0).comp continuous_snd))
  · exact isOpen_lt continuous_const (continuous_abs.comp ((continuous_apply 1).comp continuous_snd))

/-! ## The state bump `cz` is globally Lipschitz -/

lemma deriv_cz_zero_of_one_lt_abs {x : ℝ} (hx : 1 < |x|) : deriv (cz : ℝ → ℝ) x = 0 := by
  have hopen : IsOpen {y : ℝ | 1 < |y|} := isOpen_lt continuous_const continuous_abs
  have hev : (cz : ℝ → ℝ) =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hx) fun y hy => ?_
    have hy' : 1 < |y| := hy
    exact cz_eq_zero (by linarith)
  rw [hev.deriv_eq]
  simp

lemma exists_deriv_cz_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖deriv (cz : ℝ → ℝ) x‖ ≤ C := by
  have hcont : Continuous (deriv (cz : ℝ → ℝ)) :=
    (ContDiffBump.contDiff cz : ContDiff ℝ (⊤ : ℕ∞) (cz : ℝ → ℝ)).continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · exact le_trans (hC x hx) (le_max_left _ _)
  · have hx' : 1 < |x| := by
      rw [Set.mem_Icc, not_and_or] at hx
      rcases hx with h | h
      · have h1 : ¬((-1 : ℝ) ≤ x) := h
        rw [abs_of_neg (by linarith [not_le.mp h1])]
        linarith [not_le.mp h1]
      · have h1 : ¬(x ≤ (1 : ℝ)) := h
        rw [abs_of_pos (by linarith [not_le.mp h1])]
        linarith [not_le.mp h1]
    rw [deriv_cz_zero_of_one_lt_abs hx', norm_zero]
    exact le_max_right _ _

/-- The state bump `cz` is globally Lipschitz. -/
theorem cz_lipschitz : ∃ L : NNReal, LipschitzWith L (cz : ℝ → ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_deriv_cz_bound
  refine ⟨C.toNNReal, lipschitzWith_of_nnnorm_deriv_le
    ((ContDiffBump.contDiff cz : ContDiff ℝ (⊤ : ℕ∞) (cz : ℝ → ℝ)).differentiable (by simp))
    (fun x => ?_)⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC0]
  exact hC x

/-- The cut-off function `z ↦ cz ‖z - baseState s‖` is Lipschitz with the constant of `cz`. -/
lemma cz_comp_norm_lipschitz {L : NNReal} (hL : LipschitzWith L (cz : ℝ → ℝ)) (s : ℝ) :
    LipschitzWith L (fun z : Work.OddVolterra.St => (cz : ℝ → ℝ) ‖z - baseState s‖) := by
  refine lipschitzWith_iff_dist_le_mul.mpr fun u v => ?_
  have h1 : dist ((cz : ℝ → ℝ) ‖u - baseState s‖) ((cz : ℝ → ℝ) ‖v - baseState s‖)
      ≤ (L : ℝ) * |‖u - baseState s‖ - ‖v - baseState s‖| := by
    simpa only [Real.dist_eq] using hL.dist_le_mul _ _
  have h2 : |‖u - baseState s‖ - ‖v - baseState s‖| ≤ dist u v := by
    rw [dist_eq_norm]
    refine (abs_norm_sub_norm_le _ _).trans_eq ?_
    rw [show (u - baseState s) - (v - baseState s) = u - v by abel]
  calc dist ((cz : ℝ → ℝ) ‖u - baseState s‖) ((cz : ℝ → ℝ) ‖v - baseState s‖)
      ≤ (L : ℝ) * |‖u - baseState s‖ - ‖v - baseState s‖| := h1
    _ ≤ (L : ℝ) * dist u v := mul_le_mul_of_nonneg_left h2 L.coe_nonneg

/-! ## The tube of radius `7/16` around the base state -/

/-- The tube of radius `7/16` around the base state. -/
def tube (s : ℝ) : Set (Work.OddVolterra.St) := Metric.closedBall (baseState s) (7 / 16)

/-- The paired tube of radii `[7/10, 19/20] × (7/16)`. -/
def tubePair : Set (ℝ × Work.OddVolterra.St) :=
  {p | p.1 ∈ Set.Icc wLeft wRight} ∩ {p | ‖p.2 - baseState p.1‖ ≤ 7 / 16}

lemma mem_tubePair {p : ℝ × Work.OddVolterra.St} :
    p ∈ tubePair ↔ p.1 ∈ Set.Icc wLeft wRight ∧ ‖p.2 - baseState p.1‖ ≤ 7 / 16 := Iff.rfl

lemma mem_awGood_of_tubePair {p : ℝ × Work.OddVolterra.St} (hp : p ∈ tubePair) :
    p ∈ Work.OddVolterra.Existence.awGood := by
  obtain ⟨hp1, hp2⟩ := mem_tubePair.mp hp
  have hs : p.1 ∈ Set.Icc (1 / 2 : ℝ) (19 / 20) :=
    ⟨by have := hp1.1; rw [wLeft] at this; linarith, by have := hp1.2; rw [wRight] at this; linarith⟩
  have hpx : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX p.1 :=
    Work.Anchor.DClose.profileX_lower hs
  have hcoord : ∀ i : Fin 4, |p.2 i - baseState p.1 i| ≤ 7 / 16 := by
    intro i
    have h := norm_le_pi_norm (p.2 - baseState p.1) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_trans h hp2
  refine ⟨by have := hp1.1; rw [wLeft] at this; linarith,
    by have := hp1.2; rw [wRight] at this; linarith, ?_, ?_⟩
  · have h := hcoord 0
    rw [show baseState p.1 0 = Commons.Geometry.Ulam.profileX p.1 from rfl] at h
    have h2 := neg_abs_le (p.2 0 - Commons.Geometry.Ulam.profileX p.1)
    have hpos : (0 : ℝ) < p.2 0 := by linarith
    rw [abs_of_pos hpos]
    linarith
  · have h := hcoord 1
    rw [show baseState p.1 1 = Commons.Geometry.Ulam.profileX p.1 from rfl] at h
    have h2 := neg_abs_le (p.2 1 - Commons.Geometry.Ulam.profileX p.1)
    have hpos : (0 : ℝ) < p.2 1 := by linarith
    rw [abs_of_pos hpos]
    linarith

lemma isClosed_tubePair : IsClosed tubePair := by
  have h1 : IsClosed {p : ℝ × Work.OddVolterra.St | p.1 ∈ Set.Icc wLeft wRight} :=
    isClosed_Icc.preimage continuous_fst
  have h2 : IsClosed {p : ℝ × Work.OddVolterra.St | ‖p.2 - baseState p.1‖ ≤ 7 / 16} :=
    isClosed_le ((continuous_snd.sub (continuous_baseState_win.comp continuous_fst)).norm)
      continuous_const
  exact h1.inter h2

lemma isCompact_tubePair : IsCompact tubePair := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := wLeft) (b := wRight)).exists_bound_of_continuousOn
    continuous_baseState_win.continuousOn
  have hcomp : IsCompact (Set.Icc (-1 : ℝ) 2 ×ˢ Metric.closedBall (0 : Work.OddVolterra.St) (C + 1)) :=
    isCompact_Icc.prod (isCompact_closedBall 0 (C + 1))
  refine hcomp.of_isClosed_subset isClosed_tubePair ?_
  intro p hp
  obtain ⟨hp1, hp2⟩ := mem_tubePair.mp hp
  have hb : ‖baseState p.1‖ ≤ C := hC p.1 hp1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have := hp1.1; rw [wLeft] at this; linarith
  · have := hp1.2; rw [wRight] at this; linarith
  · rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖p.2‖ = ‖(p.2 - baseState p.1) + baseState p.1‖ := by rw [sub_add_cancel]
      _ ≤ ‖p.2 - baseState p.1‖ + ‖baseState p.1‖ := norm_add_le _ _
      _ ≤ 7 / 16 + C := by linarith
      _ ≤ C + 1 := by linarith

/-! ## The slice of the joint data -/

lemma differentiableAt_Godd_slice {n : ℕ} {h : ℝ → ℝ}
    (hCD : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.Godd n h p.1 p.2) Work.OddVolterra.Existence.awGood)
    {s : ℝ} {z : Work.OddVolterra.St}
    (hmem : ((s, z) : ℝ × Work.OddVolterra.St) ∈ Work.OddVolterra.Existence.awGood) :
    DifferentiableAt ℝ (fun w : Work.OddVolterra.St => Work.OddVolterra.Godd n h s w) z := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.Godd n h p.1 p.2) (s, z) :=
    ((hCD.contDiffAt (isOpen_awGood.mem_nhds hmem))).differentiableAt (by simp)
  have h1 : DifferentiableAt ℝ (fun w : Work.OddVolterra.St => ((s, w) : ℝ × Work.OddVolterra.St)) z :=
    (hasFDerivAt_prodMk_right s z).differentiableAt
  have h := hd.comp z h1
  simpa only [Function.comp_def] using h

lemma fderiv_Godd_slice {n : ℕ} {h : ℝ → ℝ}
    (hCD : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.Godd n h p.1 p.2) Work.OddVolterra.Existence.awGood)
    {s : ℝ} {z : Work.OddVolterra.St}
    (hmem : ((s, z) : ℝ × Work.OddVolterra.St) ∈ Work.OddVolterra.Existence.awGood) :
    fderiv ℝ (fun w : Work.OddVolterra.St => Work.OddVolterra.Godd n h s w) z =
      (fderiv ℝ (fun p : ℝ × Work.OddVolterra.St =>
        Work.OddVolterra.Godd n h p.1 p.2) (s, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ Work.OddVolterra.St) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.Godd n h p.1 p.2) (s, z) :=
    ((hCD.contDiffAt (isOpen_awGood.mem_nhds hmem))).differentiableAt (by simp)
  have h1 : DifferentiableAt ℝ (fun w : Work.OddVolterra.St => ((s, w) : ℝ × Work.OddVolterra.St)) z :=
    (hasFDerivAt_prodMk_right s z).differentiableAt
  have h := fderiv_comp (x := z) (f := fun w : Work.OddVolterra.St => ((s, w) : ℝ × Work.OddVolterra.St))
    (g := fun p : ℝ × Work.OddVolterra.St => Work.OddVolterra.Godd n h p.1 p.2) hd h1
  simp only [Function.comp_def] at h
  rw [h, (hasFDerivAt_prodMk_right s z).fderiv]

/-! ## Uniform bounds for `Godd` on the tube -/

theorem Godd_tube_bound (n : ℕ) (hn : 1 ≤ n) (h : ℝ → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ s ∈ Set.Icc wLeft wRight, ∀ z : Work.OddVolterra.St,
        ‖z - baseState s‖ ≤ 7 / 16 →
        ‖Work.OddVolterra.Godd n h s z‖ ≤ K ∧
        ‖fderiv ℝ (fun w => Work.OddVolterra.Godd n h s w) z‖ ≤ K := by
  have hCD : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.Godd n h p.1 p.2) Work.OddVolterra.Existence.awGood :=
    wdr_contDiffOn_godd n hh hsupp hsmall
  have hsub : tubePair ⊆ Work.OddVolterra.Existence.awGood := fun p hp => mem_awGood_of_tubePair hp
  obtain ⟨C₁, hC₁⟩ := isCompact_tubePair.exists_bound_of_continuousOn (hCD.continuousOn.mono hsub)
  have hcont_fderiv : ContinuousOn (fderiv ℝ (fun p : ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.Godd n h p.1 p.2)) Work.OddVolterra.Existence.awGood :=
    hCD.continuousOn_fderiv_of_isOpen isOpen_awGood (by norm_num)
  obtain ⟨C₂, hC₂⟩ := isCompact_tubePair.exists_bound_of_continuousOn (hcont_fderiv.mono hsub)
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun s hs z hz => ?_⟩
  have hmem : ((s, z) : ℝ × Work.OddVolterra.St) ∈ tubePair := mem_tubePair.mpr ⟨hs, hz⟩
  have hmem' : ((s, z) : ℝ × Work.OddVolterra.St) ∈ Work.OddVolterra.Existence.awGood := hsub hmem
  refine ⟨le_trans (hC₁ _ hmem) (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  rw [fderiv_Godd_slice hCD hmem']
  calc ‖(fderiv ℝ (fun p : ℝ × Work.OddVolterra.St =>
          Work.OddVolterra.Godd n h p.1 p.2) (s, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ Work.OddVolterra.St)‖
      ≤ ‖fderiv ℝ (fun p : ℝ × Work.OddVolterra.St =>
          Work.OddVolterra.Godd n h p.1 p.2) (s, z)‖ *
          ‖ContinuousLinearMap.inr ℝ ℝ Work.OddVolterra.St‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ (fun p : ℝ × Work.OddVolterra.St =>
          Work.OddVolterra.Godd n h p.1 p.2) (s, z)‖ := by
        rw [ContinuousLinearMap.norm_inr, mul_one]
    _ ≤ C₂ := hC₂ _ hmem
    _ ≤ max (max C₁ C₂) 0 := le_trans (le_max_right _ _) (le_max_left _ _)

/-! ## Lipschitz constants on the tube -/

theorem Godd_lipschitz_tube (n : ℕ) (hn : 1 ≤ n) (h : ℝ → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∃ L : NNReal, ∀ s ∈ Set.Icc wLeft wRight,
      LipschitzOnWith L (fun z => Work.OddVolterra.Godd n h s z) (tube s) := by
  obtain ⟨K, hK0, hK⟩ := Godd_tube_bound n hn h hh hsupp hsmall
  have hCD : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.Godd n h p.1 p.2) Work.OddVolterra.Existence.awGood :=
    wdr_contDiffOn_godd n hh hsupp hsmall
  refine ⟨K.toNNReal, fun s hs => ?_⟩
  have hconv : Convex ℝ (tube s) := by rw [tube]; exact convex_closedBall (baseState s) (7 / 16)
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (s := tube s)
    (f := fun z => Work.OddVolterra.Godd n h s z) (C := K.toNNReal)
    (fun z hz => ?_) (fun z hz => ?_) hconv
  · have hmem : ((s, z) : ℝ × Work.OddVolterra.St) ∈ Work.OddVolterra.Existence.awGood :=
      mem_awGood_of_tubePair (mem_tubePair.mpr ⟨hs, by
        rwa [tube, Metric.mem_closedBall, dist_eq_norm] at hz⟩)
    exact differentiableAt_Godd_slice hCD hmem
  · rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal K hK0]
    exact (hK s hs z (by rwa [tube, Metric.mem_closedBall, dist_eq_norm] at hz)).2

/-- `GW n h s` is Lipschitz on the tube, uniformly in `s` in the window (for fixed `h`). -/
theorem GW_lipschitz_tube (n : ℕ) (hn : 1 ≤ n) (h : ℝ → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∃ M : NNReal, ∀ s ∈ Set.Icc wLeft wRight,
      LipschitzOnWith M (fun z => GW n h s z) (tube s) := by
  obtain ⟨K, hK0, hK⟩ := Godd_tube_bound n hn h hh hsupp hsmall
  obtain ⟨L, hL⟩ := cz_lipschitz
  obtain ⟨Lg, hLg⟩ := Godd_lipschitz_tube n hn h hh hsupp hsmall
  have hKnn : ((K.toNNReal : NNReal) : ℝ) = K := Real.coe_toNNReal K hK0
  refine ⟨Lg + L * K.toNNReal, fun s hs => ?_⟩
  have hcs : (cs : ℝ → ℝ) s = 1 := cs_eq_one_of_mem hs
  have hcl : LipschitzOnWith L (fun z : Work.OddVolterra.St => (cz : ℝ → ℝ) ‖z - baseState s‖)
      (tube s) := (cz_comp_norm_lipschitz hL s).lipschitzOnWith
  have hG := hLg s hs
  refine lipschitzOnWith_iff_norm_sub_le.mpr fun u hu v hv => ?_
  have hGWu : GW n h s u = (cz : ℝ → ℝ) ‖u - baseState s‖ • Work.OddVolterra.Godd n h s u := by
    rw [GW, chiG, hcs, one_mul]
  have hGWv : GW n h s v = (cz : ℝ → ℝ) ‖v - baseState s‖ • Work.OddVolterra.Godd n h s v := by
    rw [GW, chiG, hcs, one_mul]
  rw [hGWu, hGWv]
  have hsplit : (cz : ℝ → ℝ) ‖u - baseState s‖ • Work.OddVolterra.Godd n h s u -
        (cz : ℝ → ℝ) ‖v - baseState s‖ • Work.OddVolterra.Godd n h s v
      = (cz : ℝ → ℝ) ‖u - baseState s‖ •
          (Work.OddVolterra.Godd n h s u - Work.OddVolterra.Godd n h s v) +
        ((cz : ℝ → ℝ) ‖u - baseState s‖ - (cz : ℝ → ℝ) ‖v - baseState s‖) •
          Work.OddVolterra.Godd n h s v := by
    rw [smul_sub, sub_smul]
    abel
  rw [hsplit]
  have hcU : |(cz : ℝ → ℝ) ‖u - baseState s‖| ≤ 1 := abs_cz_le_one _
  have hcd : ‖(cz : ℝ → ℝ) ‖u - baseState s‖ - (cz : ℝ → ℝ) ‖v - baseState s‖‖
      ≤ (L : ℝ) * ‖u - v‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using hcl.dist_le_mul u hu v hv
  have hgd : ‖Work.OddVolterra.Godd n h s u - Work.OddVolterra.Godd n h s v‖
      ≤ (Lg : ℝ) * ‖u - v‖ := by
    simpa only [dist_eq_norm] using hG.dist_le_mul u hu v hv
  have hgv : ‖Work.OddVolterra.Godd n h s v‖ ≤ ((K.toNNReal : NNReal) : ℝ) := by
    rw [hKnn]
    exact (hK s hs v (by rwa [tube, Metric.mem_closedBall, dist_eq_norm] at hv)).1
  have hgnn : (0 : ℝ) ≤ ((K.toNNReal : NNReal) : ℝ) := by rw [hKnn]; exact hK0
  have hLgnn : (0 : ℝ) ≤ (Lg : ℝ) := Lg.coe_nonneg
  calc ‖(cz : ℝ → ℝ) ‖u - baseState s‖ •
          (Work.OddVolterra.Godd n h s u - Work.OddVolterra.Godd n h s v) +
        ((cz : ℝ → ℝ) ‖u - baseState s‖ - (cz : ℝ → ℝ) ‖v - baseState s‖) •
          Work.OddVolterra.Godd n h s v‖
      ≤ ‖(cz : ℝ → ℝ) ‖u - baseState s‖ •
            (Work.OddVolterra.Godd n h s u - Work.OddVolterra.Godd n h s v)‖ +
        ‖((cz : ℝ → ℝ) ‖u - baseState s‖ - (cz : ℝ → ℝ) ‖v - baseState s‖) •
            Work.OddVolterra.Godd n h s v‖ := norm_add_le _ _
    _ ≤ |(cz : ℝ → ℝ) ‖u - baseState s‖| *
            ‖Work.OddVolterra.Godd n h s u - Work.OddVolterra.Godd n h s v‖ +
        ‖(cz : ℝ → ℝ) ‖u - baseState s‖ - (cz : ℝ → ℝ) ‖v - baseState s‖‖ *
            ‖Work.OddVolterra.Godd n h s v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ((Lg : ℝ) * ‖u - v‖) +
        ((L : ℝ) * ‖u - v‖) * ((K.toNNReal : NNReal) : ℝ) :=
        add_le_add (mul_le_mul hcU hgd (norm_nonneg _) (by norm_num))
          (mul_le_mul hcd hgv (norm_nonneg _) (by positivity))
    _ = ((Lg : ℝ) + (L : ℝ) * ((K.toNNReal : NNReal) : ℝ)) * ‖u - v‖ := by ring
    _ = ((Lg + L * K.toNNReal : NNReal) : ℝ) * ‖u - v‖ := by
        rw [NNReal.coe_add, NNReal.coe_mul]

/-! ## The cut-off is locally `1` near the base state and locally `0` far from it -/

lemma eventuallyEq_GW_Godd {n : ℕ} {h : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight)
    {z : Work.OddVolterra.St} (hz : ‖z - baseState s‖ < 1 / 5) :
    (fun w : Work.OddVolterra.St => GW n h s w) =ᶠ[𝓝 z]
      (fun w : Work.OddVolterra.St => Work.OddVolterra.Godd n h s w) := by
  refine Filter.eventually_of_mem
    (Metric.ball_mem_nhds z (by linarith : 0 < (1 / 5 - ‖z - baseState s‖) / 2)) fun w hw => ?_
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h1 : ‖w - baseState s‖ < 1 / 5 := by
    calc ‖w - baseState s‖ ≤ ‖w - z‖ + ‖z - baseState s‖ := by
          rw [show w - baseState s = (w - z) + (z - baseState s) by abel]
          exact norm_add_le _ _
      _ < 1 / 5 := by linarith
  have h1' : |‖w - baseState s‖| ≤ 1 / 5 := by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact le_of_lt h1
  simp only [GW, chiG, cs_eq_one_of_mem hs, one_mul, cz_eq_one h1', one_smul]

lemma eventuallyEq_GW_zero {n : ℕ} {h : ℝ → ℝ} {s : ℝ} {z : Work.OddVolterra.St}
    (hz : 2 / 5 < ‖z - baseState s‖) :
    (fun w : Work.OddVolterra.St => GW n h s w) =ᶠ[𝓝 z] (fun _ => 0) := by
  refine Filter.eventually_of_mem
    (Metric.ball_mem_nhds z (by linarith : 0 < (‖z - baseState s‖ - 2 / 5) / 2)) fun w hw => ?_
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h1 : 2 / 5 ≤ ‖w - baseState s‖ := by
    have h2 := abs_norm_sub_norm_le (z - baseState s) (z - w)
    rw [show (z - baseState s) - (z - w) = w - baseState s by abel] at h2
    have h3 : ‖z - baseState s‖ - ‖z - w‖ ≤ ‖w - baseState s‖ := (le_abs_self _).trans h2
    have h4 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev _ _
    linarith [hw, h4]
  have h1' : 2 / 5 ≤ |‖w - baseState s‖| := by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact h1
  simp only [GW, chiG, cz_eq_zero h1', mul_zero, zero_smul]

/-! ## The estimate -/

theorem GW_fderiv_close (n : ℕ) (hn : 1 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∃ Cg : ℝ, 0 ≤ Cg ∧
        ∀ s ∈ Set.Icc Work.OddVolterra.Window.wLeft Work.OddVolterra.Window.wRight,
        ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) 1,
          ‖fderiv ℝ (fun w => Work.OddVolterra.Window.GW n h s w) z -
             fderiv ℝ (fun w => Work.OddVolterra.Window.GW n 0 s w)
               (Work.OddVolterra.baseState s)‖
            ≤ Cg * ‖z - Work.OddVolterra.baseState s‖ + ε := by
  intro ε hε
  obtain ⟨C₁, C₂, hC1, hC2, hdc⟩ := Work.Anchor.deriv_close n hn
  set δ : ℝ := min (1 / 100 : ℝ) (ε / (2 * C₂)) with hδdef
  have hδpos : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ100 : δ ≤ 1 / 100 := min_le_left _ _
  have hδeps : C₂ * δ ≤ ε / 2 := by
    have h1 : C₂ * δ ≤ C₂ * (ε / (2 * C₂)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hC2.le
    have h2 : C₂ * (ε / (2 * C₂)) = ε / 2 := by
      field_simp
    rw [h2] at h1
    exact h1
  refine ⟨δ, hδpos, ?_⟩
  intro h hh hsupp hjet
  have hjet100 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hjet k (by omega) s) hδ100
  have hjet100_0 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ,
      |iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) s| ≤ 1 / 100 := by
    intro k hk s
    rw [iteratedDeriv_const]
    split_ifs <;> norm_num
  obtain ⟨M, hM⟩ := GW_lipschitz_tube n hn h hh hsupp hjet100
  obtain ⟨M₀, hM₀⟩ := GW_lipschitz_tube n hn (fun _ : ℝ => (0 : ℝ)) contDiff_const (by simp)
    hjet100_0
  refine ⟨max (C₁ + 1) (5 * ((M : ℝ) + (M₀ : ℝ) + 1)), le_max_of_le_left (by linarith), ?_⟩
  intro s hs z hz
  have hz1 : ‖z - baseState s‖ ≤ 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact hz
  have hCgnn : (0 : ℝ) ≤ max (C₁ + 1) (5 * ((M : ℝ) + (M₀ : ℝ) + 1)) :=
    le_max_of_le_left (by linarith)
  have hs' : s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20) :=
    ⟨by have := hs.1; rw [wLeft] at this; linarith,
     by have := hs.2; rw [wRight] at this; linarith⟩
  rcases lt_or_ge ‖z - baseState s‖ (1 / 5) with hlt | hge
  · have heq1 : (fun w : Work.OddVolterra.St => GW n h s w) =ᶠ[𝓝 z]
        (fun w : Work.OddVolterra.St => Work.OddVolterra.Godd n h s w) :=
      eventuallyEq_GW_Godd hs hlt
    have heq0 : (fun w : Work.OddVolterra.St => GW n 0 s w) =ᶠ[𝓝 (baseState s)]
        (fun w : Work.OddVolterra.St => Work.OddVolterra.Godd n 0 s w) :=
      eventuallyEq_GW_Godd hs (by simp)
    rw [heq1.fderiv_eq, heq0.fderiv_eq]
    have hz4 : ‖z - baseState s‖ ≤ 1 / 4 := by linarith
    have hb := hdc h hh hsupp δ hδpos hδ100 hjet s hs' z hz4
    have hCg1 : C₁ ≤ max (C₁ + 1) (5 * ((M : ℝ) + (M₀ : ℝ) + 1)) :=
      le_trans (by linarith) (le_max_left _ _)
    have h3 : C₁ * ‖z - baseState s‖
        ≤ max (C₁ + 1) (5 * ((M : ℝ) + (M₀ : ℝ) + 1)) * ‖z - baseState s‖ :=
      mul_le_mul_of_nonneg_right hCg1 (norm_nonneg _)
    have h2 : C₂ * δ ≤ ε := le_trans hδeps (by linarith)
    linarith
  · have hbound : ‖fderiv ℝ (fun w => GW n h s w) z‖ ≤ (M : ℝ) := by
      by_cases hr : ‖z - baseState s‖ ≤ 2 / 5
      · have hnb : tube s ∈ 𝓝 z := by
          refine Filter.mem_of_superset
            (Metric.ball_mem_nhds z (by linarith : 0 < 7 / 16 - ‖z - baseState s‖)) fun w hw => ?_
          rw [Metric.mem_ball, dist_eq_norm] at hw
          rw [tube, Metric.mem_closedBall, dist_eq_norm]
          calc ‖w - baseState s‖ ≤ ‖w - z‖ + ‖z - baseState s‖ := by
                rw [show w - baseState s = (w - z) + (z - baseState s) by abel]
                exact norm_add_le _ _
            _ ≤ 7 / 16 := by linarith
        exact norm_fderiv_le_of_lipschitzOn ℝ hnb (hM s hs)
      · have hr' : 2 / 5 < ‖z - baseState s‖ := lt_of_not_ge hr
        rw [(eventuallyEq_GW_zero (h := h) hr').fderiv_eq]
        simp
    have hbound0 : ‖fderiv ℝ (fun w => GW n 0 s w) (baseState s)‖ ≤ (M₀ : ℝ) :=
      norm_fderiv_le_of_lipschitzOn ℝ (Metric.closedBall_mem_nhds _ (by norm_num)) (hM₀ s hs)
    have hCg2 : 5 * ((M : ℝ) + (M₀ : ℝ) + 1) ≤ max (C₁ + 1) (5 * ((M : ℝ) + (M₀ : ℝ) + 1)) :=
      le_max_right _ _
    have hkey : (M : ℝ) + (M₀ : ℝ) ≤ max (C₁ + 1) (5 * ((M : ℝ) + (M₀ : ℝ) + 1)) *
        ‖z - baseState s‖ := by
      have hr5 : (1 : ℝ) / 5 ≤ ‖z - baseState s‖ := hge
      have h5 : (0 : ℝ) ≤ 5 * ((M : ℝ) + (M₀ : ℝ) + 1) := by positivity
      have h1 : (1 : ℝ) / 5 * (5 * ((M : ℝ) + (M₀ : ℝ) + 1))
          ≤ ‖z - baseState s‖ * (5 * ((M : ℝ) + (M₀ : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hr5 h5
      have h2 : 5 * ((M : ℝ) + (M₀ : ℝ) + 1) * ‖z - baseState s‖
          ≤ max (C₁ + 1) (5 * ((M : ℝ) + (M₀ : ℝ) + 1)) * ‖z - baseState s‖ :=
        mul_le_mul_of_nonneg_right hCg2 (norm_nonneg _)
      nlinarith [h1, h2]
    calc ‖fderiv ℝ (fun w => GW n h s w) z -
          fderiv ℝ (fun w => GW n 0 s w) (baseState s)‖
        ≤ ‖fderiv ℝ (fun w => GW n h s w) z‖ +
          ‖fderiv ℝ (fun w => GW n 0 s w) (baseState s)‖ := norm_sub_le _ _
      _ ≤ (M : ℝ) + (M₀ : ℝ) := add_le_add hbound hbound0
      _ ≤ max (C₁ + 1) (5 * ((M : ℝ) + (M₀ : ℝ) + 1)) * ‖z - baseState s‖ + ε := by
          linarith [hkey, hε]

end

end Work.OddVolterra.Window
