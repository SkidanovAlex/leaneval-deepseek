import Mathlib
import Submission.Work.OddVolterra.WinData.win_data
import Submission.Work.OddVolterra.WinData.fderiv_godd_close_box
import Submission.Work.OddVolterra.WinData.gcl_contDiffOn

/-!
# Closeness of the differential of the clamped window datum `Gcl` in the perturbation

`Work.OddVolterra.WinData.clamped_hder_unit`: there is `Cg > 0` such that for every smooth `h`
supported in the transition window `[1 - 2τ, 1 - τ]` with `‖h‖_{C^{n+2}} ≤ δ ≤ 1/100`, every
slope `s ∈ [1/4, 19/20]` and every state `z` in the ball of radius `1` around `baseState s`,

`‖fderiv (Gcl n h s ·) z - fderiv (Gcl n 0 s ·) (baseState s)‖ ≤ Cg ‖z - baseState s‖ + Cg δ`.

This is the estimate the long-interval Volterra engine needs for the clamped state datum.

The clamped datum is `Gcl n h s z = wChiG s z • diagForm n h s z` with
`wChiG s z = wCs s · wCz (z - baseState s)`, where `wCs` equals `1` on `[1/4, 19/20]` and
`wCz` equals `1` on the ball of radius `1/2` around the origin and vanishes outside the ball of
radius `101/200`.  The proof splits the state ball:

* For `‖z - baseState s‖ < 1/2` the cut-off `wChiG s ·` is `1` near `z` (and near `baseState s`),
  so the clamped data agree with `Godd` there and the estimate is `fderiv_godd_close_box`.
* For `‖z - baseState s‖ ≥ 1/2` it suffices to bound both differentials by a constant, since
  the right-hand side is at least `Cg / 2`.  On the tube `‖z - baseState s‖ ≤ wCzR = 101/200`
  the product rule expresses the differential of `Gcl` through the (uniformly bounded) values
  and differentials of `Godd` and of the bump `wCz`; beyond that tube `Gcl` vanishes on a
  neighbourhood of `z`.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open Work.OddCurveB.Existence
open Work.Anchor.DClose
open scoped Topology ContDiff

noncomputable section

/-! ## 1. Elementary bounds on the profile -/

/-- On the window `[1/4, 19/20]` the ball profile is at most `199/200`; this leaves room for
the tube of radius `wCzR = 101/200` inside the box `Zbox`. -/
lemma hder_profileX_le {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20)) :
    Commons.Geometry.Ulam.profileX s ≤ 199 / 200 := by
  rw [Commons.Geometry.Ulam.profileX]
  rw [div_le_iff₀ (Real.sqrt_pos.2 (by positivity))]
  have hs2 : ((1 : ℝ) / 4) ^ 2 ≤ s ^ 2 := by nlinarith [hs.1]
  have h1 : ((200 : ℝ) / 199) ≤ Real.sqrt (1 + s ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [hs2]
  have h2 : ((199 : ℝ) / 200) * (200 / 199) ≤ (199 / 200) * Real.sqrt (1 + s ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  linarith

/-! ## 2. Positivity of the two radicands on the window box -/

/-- On the box `[1/4, 19/20] × [-1/100, 1/100]² × Zbox C` both radicands of the diagonal system
are strictly positive. -/
lemma hder_D1D2_pos (C : ℝ) :
    ∀ q ∈ Qbox (1 / 4) (19 / 20) (-(1 / 100)) (1 / 100) (-(1 / 100)) (1 / 100) C,
      0 < D1 q ∧ 0 < D2 q := by
  intro q hq
  obtain ⟨⟨s, a, b⟩, z⟩ := q
  rw [mem_Qbox] at hq
  obtain ⟨⟨hs1, hs2⟩, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hz⟩ := hq
  obtain ⟨⟨hz0a, hz0b⟩, ⟨hz1a, hz1b⟩, -, -⟩ := mem_Zbox.mp hz
  constructor
  · have h1 : 0 < z 0 - b := by linarith
    have h2 : 0 < s * z 0 - a := by nlinarith [hs1, hz0a, ha2]
    have key : D1 (((s, a, b), z) : (ℝ × ℝ × ℝ) × St) = (z 0 - b) * (s * z 0 - a) := by
      rw [D1, Drad]; ring
    rw [key]; exact mul_pos h1 h2
  · have h1 : 0 < z 1 + b := by linarith
    have h2 : 0 < s * z 1 + a := by nlinarith [hs1, hz1a, ha1]
    have key : D2 (((s, a, b), z) : (ℝ × ℝ × ℝ) × St) = (z 1 + b) * (s * z 1 + a) := by
      rw [D2, Drad]
    rw [key]; exact mul_pos h1 h2

/-! ## 3. Uniform bounds for `Gdiag` and `Pdiag` on the box -/

/-- The diagonal system and its differential are bounded on the window box. -/
lemma hder_Gdiag_bounds (n : ℕ) (hn : 1 ≤ n) (C : ℝ) :
    ∃ KD KG : ℝ, 0 ≤ KD ∧ 0 ≤ KG ∧
      (∀ q ∈ Qbox (1 / 4) (19 / 20) (-(1 / 100)) (1 / 100) (-(1 / 100)) (1 / 100) C,
        ‖Gdiag n q‖ ≤ KD) ∧
      (∀ q ∈ Qbox (1 / 4) (19 / 20) (-(1 / 100)) (1 / 100) (-(1 / 100)) (1 / 100) C,
        ‖Pdiag n q‖ ≤ KG) := by
  have hsub : Qbox (1 / 4) (19 / 20) (-(1 / 100)) (1 / 100) (-(1 / 100)) (1 / 100) C ⊆ Upos :=
    hder_D1D2_pos C
  obtain ⟨KD, hKD⟩ := (isCompact_Qbox (1 / 4) (19 / 20) (-(1 / 100)) (1 / 100) (-(1 / 100))
      (1 / 100) C).exists_bound_of_continuousOn
    ((contDiffOn_Gdiag_Upos n hn).continuousOn.mono hsub)
  obtain ⟨KF, hKF⟩ := (isCompact_Qbox (1 / 4) (19 / 20) (-(1 / 100)) (1 / 100) (-(1 / 100))
      (1 / 100) C).exists_bound_of_continuousOn
    (((contDiffOn_fderiv_Gdiag_Upos n hn).continuousOn).mono hsub)
  refine ⟨max KD 0, max KF 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro q hq
    exact le_trans (hKD q hq) (le_max_left _ _)
  · intro q hq
    calc ‖Pdiag n q‖
        = ‖(fderiv ℝ (Gdiag n) q).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) St)‖ := rfl
      _ ≤ ‖fderiv ℝ (Gdiag n) q‖ * ‖ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) St‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖fderiv ℝ (Gdiag n) q‖ := by rw [ContinuousLinearMap.norm_inr, mul_one]
      _ ≤ KF := hKF q hq
      _ ≤ max KF 0 := le_max_left _ _

/-! ## 4. The state bump `wCz` has a bounded differential -/

lemma hder_wCz_fderiv_bound :
    ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ y : St, ‖fderiv ℝ (wCz : St → ℝ) y‖ ≤ Kf := by
  have hcont : Continuous (fun y : St => fderiv ℝ (wCz : St → ℝ) y) :=
    wCz_contDiff.continuous_fderiv (by simp)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : St) wCzR).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : ‖y‖ ≤ wCzR
  · exact le_trans (hK y (by rwa [Metric.mem_closedBall, dist_zero_right])) (le_max_left _ _)
  · have hy' : wCzR < ‖y‖ := lt_of_not_ge hy
    have hev : (wCz : St → ℝ) =ᶠ[𝓝 y] (fun _ : St => (0 : ℝ)) := by
      refine Filter.eventually_of_mem
        ((isOpen_lt continuous_const continuous_norm).mem_nhds hy') fun v hv => ?_
      exact wCz_eq_zero (le_of_lt hv)
    rw [hev.fderiv_eq]
    have h0 : fderiv ℝ (fun _ : St => (0 : ℝ)) y = 0 := by simp
    rw [h0, norm_zero]
    exact le_trans (le_of_eq rfl) (le_max_right _ _)

/-! ## 5. Membership in the box -/

/-- A state in the tube of radius `wCzR = 101/200` around `baseState s` lies in `Zbox (B + 1)`
whenever `B` bounds `(profileX)'` on the window. -/
lemma hder_mem_box {B : ℝ}
    (hB : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      |deriv Commons.Geometry.Ulam.profileX s| ≤ B)
    {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20)) {z : St} {a b : ℝ}
    (ha : |a| ≤ 1 / 100) (hb : |b| ≤ 1 / 100) (hz : ‖z - baseState s‖ ≤ wCzR) :
    (((s, a, b), z) : (ℝ × ℝ × ℝ) × St) ∈
      Qbox (1 / 4) (19 / 20) (-(1 / 100)) (1 / 100) (-(1 / 100)) (1 / 100) (B + 1) := by
  rw [mem_Qbox]
  refine ⟨⟨hs.1, hs.2⟩, ⟨by linarith [(abs_le.mp ha).1], by linarith [(abs_le.mp ha).2]⟩,
    ⟨by linarith [(abs_le.mp hb).1], by linarith [(abs_le.mp hb).2]⟩, ?_⟩
  rw [mem_Zbox]
  have hz' : ‖z - baseState s‖ ≤ 101 / 200 := by simpa only [wCzR] using hz
  have hcoord : ∀ i : Fin 4, |z i - baseState s i| ≤ 101 / 200 := by
    intro i
    have h := norm_le_pi_norm (z - baseState s) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_trans h hz'
  have hprof_lo : (18 / 25 : ℝ) ≤ Commons.Geometry.Ulam.profileX s :=
    gcl_profileX_ge (by rw [abs_le]; constructor <;> linarith [hs.1, hs.2])
  have hprof_hi : Commons.Geometry.Ulam.profileX s ≤ 199 / 200 := hder_profileX_le hs
  have hb0 : |deriv Commons.Geometry.Ulam.profileX s| ≤ B := hB s hs
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have h := (abs_le.mp (hcoord 0)).1
    rw [show baseState s 0 = Commons.Geometry.Ulam.profileX s from rfl] at h
    linarith
  · have h := (abs_le.mp (hcoord 0)).2
    rw [show baseState s 0 = Commons.Geometry.Ulam.profileX s from rfl] at h
    linarith
  · have h := (abs_le.mp (hcoord 1)).1
    rw [show baseState s 1 = Commons.Geometry.Ulam.profileX s from rfl] at h
    linarith
  · have h := (abs_le.mp (hcoord 1)).2
    rw [show baseState s 1 = Commons.Geometry.Ulam.profileX s from rfl] at h
    linarith
  · have h := (abs_le.mp (hcoord 2)).1
    rw [show baseState s 2 = deriv Commons.Geometry.Ulam.profileX s from rfl] at h
    have h2 := neg_le_of_abs_le hb0
    linarith
  · have h := (abs_le.mp (hcoord 2)).2
    rw [show baseState s 2 = deriv Commons.Geometry.Ulam.profileX s from rfl] at h
    have h2 := le_of_abs_le hb0
    linarith
  · have h := (abs_le.mp (hcoord 3)).1
    rw [show baseState s 3 = deriv Commons.Geometry.Ulam.profileX s from rfl] at h
    have h2 := neg_le_of_abs_le hb0
    linarith
  · have h := (abs_le.mp (hcoord 3)).2
    rw [show baseState s 3 = deriv Commons.Geometry.Ulam.profileX s from rfl] at h
    have h2 := le_of_abs_le hb0
    linarith

/-! ## 6. The cut-off is locally `1` near the base state, locally `0` far from it -/

lemma hder_Gcl_eventuallyEq_Godd {n : ℕ} {h : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20)) {z : St} (hz : ‖z - baseState s‖ < 1 / 2) :
    (fun w : St => Gcl n h s w) =ᶠ[𝓝 z] (fun w : St => Godd n h s w) := by
  have hs' : s ∈ Set.Icc wLo wHi := by rw [wLo, wHi]; exact hs
  refine Filter.eventually_of_mem
    (Metric.ball_mem_nhds z (by linarith : 0 < ((1 / 2 : ℝ) - ‖z - baseState s‖) / 2))
    fun w hw => ?_
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h1 : ‖w - baseState s‖ < wRho := by
    rw [wRho]
    calc ‖w - baseState s‖ ≤ ‖w - z‖ + ‖z - baseState s‖ := by
          rw [show w - baseState s = (w - z) + (z - baseState s) by abel]
          exact norm_add_le _ _
      _ < 1 / 2 := by linarith
  have hchi : wChiG s w = 1 := by
    rw [wChiG, wCs_eq_one hs', wCz_eq_one (le_of_lt h1), mul_one]
  simp only [Gcl, hchi, one_smul, Godd_eq_diagForm]

lemma hder_Gcl_eventuallyEq_zero {n : ℕ} {h : ℝ → ℝ} {s : ℝ} {z : St}
    (hz : wCzR < ‖z - baseState s‖) :
    (fun w : St => Gcl n h s w) =ᶠ[𝓝 z] (fun _ => 0) := by
  refine Filter.eventually_of_mem
    (Metric.ball_mem_nhds z (by linarith : 0 < (‖z - baseState s‖ - wCzR) / 2))
    fun w hw => ?_
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h1 : wCzR ≤ ‖w - baseState s‖ := by
    have h2 := abs_norm_sub_norm_le (z - baseState s) (z - w)
    rw [show (z - baseState s) - (z - w) = w - baseState s by abel] at h2
    have h3 : ‖z - baseState s‖ - ‖z - w‖ ≤ ‖w - baseState s‖ := (le_abs_self _).trans h2
    have h4 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev _ _
    linarith [hw, h4]
  have hzero : (wCz : St → ℝ) (w - baseState s) = 0 := wCz_eq_zero h1
  simp only [Gcl, wChiG, hzero, mul_zero, zero_smul]

/-! ## 6b. Two elementary chain-rule lemmas for the translation of the state -/

lemma hder_differentiableAt_comp_sub {f : St → ℝ} {c z : St} (hf : DifferentiableAt ℝ f (z - c)) :
    DifferentiableAt ℝ (fun w : St => f (w - c)) z := by
  have h2 := hf.comp z (differentiableAt_id.sub_const c)
  simpa [Function.comp_def] using h2

lemma hder_fderiv_comp_sub {f : St → ℝ} {c z : St} (hf : DifferentiableAt ℝ f (z - c)) :
    fderiv ℝ (fun w : St => f (w - c)) z
      = (fderiv ℝ f (z - c)).comp (ContinuousLinearMap.id ℝ St) := by
  have h1 : fderiv ℝ (fun w : St => w - c) z = ContinuousLinearMap.id ℝ St := by
    simpa using ((hasFDerivAt_id z).sub_const c).fderiv
  have h2 := fderiv_comp (x := z) (g := f) (f := fun w : St => w - c) hf
    (differentiableAt_id.sub_const c)
  rw [h1] at h2
  simpa only [Function.comp_def] using h2

/-! ## 7. A uniform bound for the differential of `Gcl` on the tube -/

lemma hder_Gcl_fderiv_bound {n : ℕ} (hn : 1 ≤ n) {B Kf KD KG : ℝ}
    (hB : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      |deriv Commons.Geometry.Ulam.profileX s| ≤ B)
    (hKf : ∀ y : St, ‖fderiv ℝ (wCz : St → ℝ) y‖ ≤ Kf)
    (hKD : ∀ q ∈ Qbox (1 / 4) (19 / 20) (-(1 / 100)) (1 / 100) (-(1 / 100)) (1 / 100) (B + 1),
      ‖Gdiag n q‖ ≤ KD)
    (hKG : ∀ q ∈ Qbox (1 / 4) (19 / 20) (-(1 / 100)) (1 / 100) (-(1 / 100)) (1 / 100) (B + 1),
      ‖Pdiag n q‖ ≤ KG)
    {h : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20))
    (hhs : |h s| ≤ 1 / 100) (hhp : |deriv h s| ≤ 1 / 100)
    {z : St} (hz : ‖z - baseState s‖ ≤ wCzR) :
    ‖fderiv ℝ (fun w : St => Gcl n h s w) z‖ ≤ KG + Kf * KD := by
  have hq : (((s, h s, deriv h s), z) : (ℝ × ℝ × ℝ) × St) ∈
      Qbox (1 / 4) (19 / 20) (-(1 / 100)) (1 / 100) (-(1 / 100)) (1 / 100) (B + 1) :=
    hder_mem_box hB hs hhs hhp hz
  have hpos : 0 < D1 (((s, h s, deriv h s), z) : (ℝ × ℝ × ℝ) × St) ∧
      0 < D2 (((s, h s, deriv h s), z) : (ℝ × ℝ × ℝ) × St) := hder_D1D2_pos (B + 1) _ hq
  have hqU : (((s, h s, deriv h s), z) : (ℝ × ℝ × ℝ) × St) ∈ Upos := hpos
  -- differentiability of the two factors
  have hdiffG : DifferentiableAt ℝ (fun w : St => Godd n h s w) z := by
    have hjoint : DifferentiableAt ℝ (Gdiag n) (((s, h s, deriv h s), z) : (ℝ × ℝ × ℝ) × St) :=
      ((contDiffOn_Gdiag_Upos n hn).contDiffAt (isOpen_Upos.mem_nhds hqU)).differentiableAt
        (by simp)
    have hslice := hjoint.comp z (hasFDerivAt_prodMk_right (s, h s, deriv h s) z).differentiableAt
    have heqfun : (Gdiag n ∘ (fun w : St => (((s, h s, deriv h s), w) : (ℝ × ℝ × ℝ) × St)))
        = (fun w : St => Godd n h s w) := by
      funext w
      simp [Gdiag, Godd_eq_GoddDiag]
    rwa [heqfun] at hslice
  have hdiff_wCz : DifferentiableAt ℝ (wCz : St → ℝ) (z - baseState s) :=
    (wCz_contDiff.differentiable (by simp)).differentiableAt
  have hdiffchi : DifferentiableAt ℝ (fun w : St => (wCz : St → ℝ) (w - baseState s)) z :=
    hder_differentiableAt_comp_sub hdiff_wCz
  -- the product rule
  have hprod := fderiv_smul (x := z) (f := fun w : St => Godd n h s w)
    (c := fun w : St => (wCz : St → ℝ) (w - baseState s)) hdiffchi hdiffG
  have hGcl : (fun w : St => Gcl n h s w)
      = wCs s • ((fun w : St => (wCz : St → ℝ) (w - baseState s)) •
          (fun w : St => Godd n h s w)) := by
    funext w
    show wChiG s w • diagForm n h s w
        = wCs s • ((wCz : St → ℝ) (w - baseState s) • Godd n h s w)
    rw [wChiG, Godd_eq_diagForm, mul_smul]
  rw [hGcl, fderiv_const_smul (hdiffchi.smul hdiffG) (wCs s), hprod, norm_smul, Real.norm_eq_abs]
  -- the two summands
  have hc1 : |wCs s| ≤ 1 := by rw [abs_of_nonneg (wCs_nonneg s)]; exact wCs_le_one s
  have hchi1 : ‖(wCz : St → ℝ) (z - baseState s)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (wCz_nonneg _)]
    exact wCz_le_one _
  have hderG : ‖fderiv ℝ (fun w : St => Godd n h s w) z‖ ≤ KG := by
    rw [← Pdiag_Godd n hn h hpos.1 hpos.2]
    exact hKG _ hq
  have hvalG : ‖Godd n h s z‖ ≤ KD := by
    have := hKD (((s, h s, deriv h s), z) : (ℝ × ℝ × ℝ) × St) hq
    simpa only [Gdiag, Godd_eq_GoddDiag] using this
  have hderchi : ‖fderiv ℝ (fun w : St => (wCz : St → ℝ) (w - baseState s)) z‖ ≤ Kf := by
    rw [hder_fderiv_comp_sub hdiff_wCz]
    calc ‖(fderiv ℝ (wCz : St → ℝ) (z - baseState s)).comp
            (ContinuousLinearMap.id ℝ St)‖
        ≤ ‖fderiv ℝ (wCz : St → ℝ) (z - baseState s)‖ *
            ‖ContinuousLinearMap.id ℝ St‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖fderiv ℝ (wCz : St → ℝ) (z - baseState s)‖ := by
          rw [ContinuousLinearMap.norm_id, mul_one]
      _ ≤ Kf := hKf _
  have hterm1 : ‖(wCz : St → ℝ) (z - baseState s) • fderiv ℝ (fun w : St => Godd n h s w) z‖
      ≤ KG := by
    rw [norm_smul]
    calc ‖(wCz : St → ℝ) (z - baseState s)‖ * ‖fderiv ℝ (fun w : St => Godd n h s w) z‖
        ≤ 1 * KG := mul_le_mul hchi1 hderG (norm_nonneg _) (by norm_num)
      _ = KG := one_mul _
  have hterm2 : ‖(fderiv ℝ (fun w : St => (wCz : St → ℝ) (w - baseState s)) z).smulRight
      (Godd n h s z)‖ ≤ Kf * KD := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul hderchi hvalG (norm_nonneg _) (le_trans (norm_nonneg _) hderchi)
  calc |wCs s| * ‖(wCz : St → ℝ) (z - baseState s) • fderiv ℝ (fun w : St => Godd n h s w) z
          + (fderiv ℝ (fun w : St => (wCz : St → ℝ) (w - baseState s)) z).smulRight
              (Godd n h s z)‖
      ≤ 1 * (KG + Kf * KD) := by
        refine mul_le_mul hc1 ?_ (norm_nonneg _) (by norm_num)
        exact le_trans (norm_add_le _ _) (add_le_add hterm1 hterm2)
    _ = KG + Kf * KD := one_mul _

/-! ## 8. The estimate -/

theorem clamped_hder_unit (n : ℕ) (hn : 1 ≤ n) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) 1,
        ‖fderiv ℝ (fun w => Work.OddVolterra.WinData.Gcl n h s w) z -
         fderiv ℝ (fun w => Work.OddVolterra.WinData.Gcl n 0 s w)
            (Work.OddVolterra.baseState s)‖
          ≤ Cg * ‖z - Work.OddVolterra.baseState s‖ + Cg * δ := by
  -- a bound for the derivative of the profile on the window
  obtain ⟨B, hB1, hB⟩ : ∃ B : ℝ, 1 ≤ B ∧
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), |deriv Commons.Geometry.Ulam.profileX s| ≤ B := by
    have hcont : Continuous (deriv Commons.Geometry.Ulam.profileX) :=
      Work.OddCurveB.Est.contDiff_profileX_est.continuous_deriv (by simp)
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
      (s := Set.Icc (1 / 4 : ℝ) (19 / 20))
    refine ⟨max B 1, le_max_right _ _, fun s hs => ?_⟩
    have h := hB s hs
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  -- the sharp estimate for `Godd` on the closed ball of radius `1/2`
  obtain ⟨Cg₁, hCg₁, hdc⟩ := fderiv_godd_close_box n hn (a := (1 / 4 : ℝ)) (b := (19 / 20 : ℝ))
    (ρ := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- the uniform auxiliary bounds
  obtain ⟨Kf, hKf0, hKf⟩ := hder_wCz_fderiv_bound
  obtain ⟨KD, KG, hKD0, hKG0, hKD, hKG⟩ := hder_Gdiag_bounds n hn (B + 1)
  -- the constants
  have hM1 : (0 : ℝ) ≤ KG + Kf * KD := by
    have : 0 ≤ Kf * KD := mul_nonneg hKf0 hKD0
    linarith
  have hCgp : 0 < max Cg₁ (4 * (KG + Kf * KD)) + 1 := by
    have h : (0 : ℝ) ≤ max Cg₁ (4 * (KG + Kf * KD)) := le_trans (le_of_lt hCg₁) (le_max_left _ _)
    linarith
  refine ⟨max Cg₁ (4 * (KG + Kf * KD)) + 1, hCgp, ?_⟩
  intro h δ hh hδ hδ100 hsupp hjet s hs z hz
  have hCg₁le : Cg₁ ≤ max Cg₁ (4 * (KG + Kf * KD)) + 1 := by
    have h : Cg₁ ≤ max Cg₁ (4 * (KG + Kf * KD)) := le_max_left _ _
    linarith
  have hCg2le : 2 * (KG + Kf * KD) ≤ max Cg₁ (4 * (KG + Kf * KD)) + 1 := by
    have : (0 : ℝ) ≤ KG + Kf * KD := hM1
    have h4 : 4 * (KG + Kf * KD) ≤ max Cg₁ (4 * (KG + Kf * KD)) := le_max_right _ _
    linarith
  have hCgnn : (0 : ℝ) ≤ max Cg₁ (4 * (KG + Kf * KD)) + 1 := le_of_lt hCgp
  have hhsδ : |h s| ≤ δ := by
    have h0 := hjet 0 (by omega) s
    rwa [iteratedDeriv_zero] at h0
  have hhpδ : |deriv h s| ≤ δ := by
    have h1 := hjet 1 (by omega) s
    rwa [iteratedDeriv_one] at h1
  have hhs : |h s| ≤ 1 / 100 := le_trans hhsδ hδ100
  have hhp : |deriv h s| ≤ 1 / 100 := le_trans hhpδ hδ100
  have hz1 : ‖z - baseState s‖ ≤ 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact hz
  rcases lt_or_ge ‖z - baseState s‖ (1 / 2) with hlt | hge
  · -- ## inner case: the two clamped data agree with `Godd` near the two points
    have heq1 : (fun w : St => Gcl n h s w) =ᶠ[𝓝 z] (fun w : St => Godd n h s w) :=
      hder_Gcl_eventuallyEq_Godd hs hlt
    have heq0 : (fun w : St => Gcl n 0 s w) =ᶠ[𝓝 (baseState s)] (fun w : St => Godd n 0 s w) :=
      hder_Gcl_eventuallyEq_Godd (n := n) (h := fun _ : ℝ => (0 : ℝ)) (s := s) hs
        (by simp)
    rw [heq1.fderiv_eq, heq0.fderiv_eq]
    have hz4 : ‖z - baseState s‖ ≤ 1 / 2 := le_of_lt hlt
    have hmain := hdc h hh hsupp δ hδ hδ100 hjet s hs z hz4
    calc ‖fderiv ℝ (fun w : St => Godd n h s w) z -
          fderiv ℝ (fun w : St => Godd n 0 s w) (baseState s)‖
        ≤ Cg₁ * ‖z - baseState s‖ + Cg₁ * δ := hmain
      _ ≤ (max Cg₁ (4 * (KG + Kf * KD)) + 1) * ‖z - baseState s‖ +
          (max Cg₁ (4 * (KG + Kf * KD)) + 1) * δ := by
          have h1 : Cg₁ * ‖z - baseState s‖ ≤
              (max Cg₁ (4 * (KG + Kf * KD)) + 1) * ‖z - baseState s‖ :=
            mul_le_mul_of_nonneg_right hCg₁le (norm_nonneg _)
          have h2 : Cg₁ * δ ≤ (max Cg₁ (4 * (KG + Kf * KD)) + 1) * δ :=
            mul_le_mul_of_nonneg_right hCg₁le hδ.le
          linarith
  · -- ## outer case: bound both differentials by the constant `KG + Kf * KD`
    have hbound : ∀ (g : ℝ → ℝ), (|g s| ≤ 1 / 100) → (|deriv g s| ≤ 1 / 100) → ∀ w : St,
        ‖w - baseState s‖ ≤ wCzR →
        ‖fderiv ℝ (fun u : St => Gcl n g s u) w‖ ≤ KG + Kf * KD :=
      fun g hg1 hg2 w hw => hder_Gcl_fderiv_bound (n := n) hn hB hKf hKD hKG hs hg1 hg2 hw
    have hb1 : ‖fderiv ℝ (fun w : St => Gcl n h s w) z‖ ≤ KG + Kf * KD := by
      by_cases hzR : ‖z - baseState s‖ ≤ wCzR
      · exact hbound h hhs hhp z hzR
      · have hzR' : wCzR < ‖z - baseState s‖ := lt_of_not_ge hzR
        rw [(hder_Gcl_eventuallyEq_zero (n := n) (h := h) hzR').fderiv_eq]
        have h0 : fderiv ℝ (fun _ : St => (0 : St)) z = 0 := by simp
        rw [h0, norm_zero]
        exact hM1
    have hb0 : ‖fderiv ℝ (fun w : St => Gcl n 0 s w) (baseState s)‖ ≤ KG + Kf * KD := by
      refine hbound (fun _ : ℝ => (0 : ℝ)) (by norm_num) (by simp) (baseState s) ?_
      rw [sub_self, norm_zero]
      norm_num [wCzR]
    calc ‖fderiv ℝ (fun w : St => Gcl n h s w) z -
          fderiv ℝ (fun w : St => Gcl n 0 s w) (baseState s)‖
        ≤ ‖fderiv ℝ (fun w : St => Gcl n h s w) z‖ +
          ‖fderiv ℝ (fun w : St => Gcl n 0 s w) (baseState s)‖ := norm_sub_le _ _
      _ ≤ (KG + Kf * KD) + (KG + Kf * KD) := add_le_add hb1 hb0
      _ ≤ (max Cg₁ (4 * (KG + Kf * KD)) + 1) * ‖z - baseState s‖ +
          (max Cg₁ (4 * (KG + Kf * KD)) + 1) * δ := by
          have hCg4 : 4 * (KG + Kf * KD) ≤ max Cg₁ (4 * (KG + Kf * KD)) + 1 := by
            have h : 4 * (KG + Kf * KD) ≤ max Cg₁ (4 * (KG + Kf * KD)) := le_max_right _ _
            linarith
          have h1 : 2 * (KG + Kf * KD) ≤
              (max Cg₁ (4 * (KG + Kf * KD)) + 1) * ‖z - baseState s‖ := by
            have hge' : (1 / 2 : ℝ) ≤ ‖z - baseState s‖ := hge
            nlinarith [hCg4, hge', hM1, hCgnn]
          have h2 : (0 : ℝ) ≤ (max Cg₁ (4 * (KG + Kf * KD)) + 1) * δ :=
            mul_nonneg hCgnn hδ.le
          linarith

end

end Work.OddVolterra.WinData
