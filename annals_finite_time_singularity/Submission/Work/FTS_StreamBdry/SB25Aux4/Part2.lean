import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.law_psiP
import Submission.Work.FTS_StreamBdry.SB25.axis_d2_bound
import Submission.Work.FTS_StreamBdry.SB25Aux4.EdgeAxisAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux4.psiP_edge_axis_pthth`

`∂_θ²P → 0` at `(z₀, π/2)`, uniformly in `z` near `z₀ > 0` (the hard limit of leaf B6).

The route: `∂_θ²P = ∂_θ(V(P)) + ∂_θ(tan θ·P)` and, per `z`-slice, `SB25.axis_d2_bound` bounds
`|∂_θ²P| ≤ 6ε + |Vb z|(π/2 - θ)` where `ε` is the *sharp* supremum of `|∂_θV(P)|` on the
remaining interval.  By `law_psiP` (`∂_θV(P) = -(αG²D_z²P + 5αG D_zP + 6P) - F`) and
`psiP_DzLe`, `ε ≤ 2K_S δ + η` on `[π/2 - δ, π/2)`, with `K_S = (αG²+5αG+6)M` and `η` an
`F`-bound near the axis coming from `SrcOK` (`F` continuous on the closed strip, `F(z,π/2) = 0`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux4

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

set_option maxHeartbeats 2000000 in
theorem psiP_edge_axis_pthth {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M)
    (hsrc : SrcOK F L Mf)
    (Vb : ℝ → ℝ) (hVbc : ContinuousOn Vb (Set.Ioi 0))
    (hVb : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Construction.Vop (psiP αG Ψ) z θ - Vb z|
        ≤ ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ)) :
    ∀ z0 : ℝ, 0 < z0 →
      Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth (psiP αG Ψ))))
        (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) := by
  have hMnn : 0 ≤ M := by
    have h1 := Work.FTS_StreamBdry.SlotBd.Dz_le hslot (z := 1) (θ := Real.pi / 4)
      Work.FTS_StreamBdry.SB1.Qd_nonempty (j := 0) (by norm_num)
    exact le_trans (abs_nonneg _) h1
  have hDz := Work.FTS_StreamBdry.SB3.psiP_DzLe (αG := αG) (M := M) hαG h3 hslot
  have hlaw := Work.FTS_StreamBdry.SB3.law_psiP (αG := αG) (M := M) hαG hsol h3 hslot
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 (αG := αG) (M := M) hαG h3 hslot
  have hpth1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (psiP αG Ψ)))
      Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.contDiffOn_uncurry_pth_qd (G := psiP αG Ψ) (n := 1) hP2
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  intro z0 hz0
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hηpos : 0 < ε / 24 := by linarith
  -- `F` is small near the axis
  have hF0 : Function.uncurry F (z0, Real.pi / 2) = 0 := by
    have h := (hsrc.2.2.2.1 z0 hz0).2
    simpa [Function.uncurry] using h
  have hFmem : (z0, Real.pi / 2) ∈ Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ :=
    ⟨hz0, ⟨by linarith [Real.pi_pos], le_rfl⟩⟩
  have hFlim : Tendsto (Function.uncurry F) (𝓝[Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ]
      (z0, Real.pi / 2)) (𝓝 0) := by
    have h := hsrc.1.continuousWithinAt hFmem
    simpa only [ContinuousWithinAt, hF0] using h
  obtain ⟨δF, hδFpos, hδF⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp hFlim) (ε / 24) hηpos
  set KL := (αG ^ 2 + 5 * αG + 6) * M with hKL
  have hKLnn : 0 ≤ KL := by rw [hKL]; nlinarith [hMnn, sq_nonneg αG]
  have hVbc_at : ContinuousAt Vb z0 := hVbc.continuousAt (isOpen_Ioi.mem_nhds hz0)
  set CV := |Vb z0| + 1 with hCV
  have hCVnn : 0 ≤ CV := by rw [hCV]; positivity
  set δ := min (min (z0 / 2) (δF / 2))
    (min (Real.pi / 4) (ε / (4 * (12 * KL + CV + 1)))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    refine lt_min (lt_min (by linarith) (by linarith))
      (lt_min (by linarith [Real.pi_pos]) (by positivity))
  obtain ⟨δV, hδVpos, hδV⟩ := Metric.continuousAt_iff.mp hVbc_at 1 one_pos
  refine ⟨min δ (δV / 2), ?_, ?_⟩
  · exact lt_min hδpos (by linarith)
  · intro p hp hdist
    obtain ⟨z, θ⟩ := p
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hdist
    obtain ⟨hdz, hdθ⟩ := hdist
    have hznear : |z - z0| < δ := lt_of_lt_of_le hdz (min_le_left δ (δV / 2))
    have hznearV : |z - z0| < δV :=
      lt_of_lt_of_le (lt_of_lt_of_le hdz (min_le_right δ (δV / 2))) (by linarith)
    have hθnear : |θ - Real.pi / 2| < δ := lt_of_lt_of_le hdθ (min_le_left δ (δV / 2))
    have hθm := Work.FTS_StreamBdry.Qd_theta_mem hp
    have hzpos : 0 < z := Work.FTS_StreamBdry.Qd_pos hp
    have hδF2 : δ ≤ δF / 2 := by
      rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hδz : δ ≤ z0 / 2 := by
      rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hδ1 : δ ≤ Real.pi / 4 := by
      rw [hδdef]
      exact le_trans (min_le_right _ _) (min_le_left (Real.pi / 4) (ε / (4 * (12 * KL + CV + 1))))
    have hδeps : δ ≤ ε / (4 * (12 * KL + CV + 1)) := by
      rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hzlo : z0 / 2 < z := by have := (abs_lt.mp hznear).1; linarith
    have hthlo : Real.pi / 2 - δ < θ := by have := (abs_lt.mp hθnear).1; linarith
    have hspos : 0 < Real.pi / 2 - δ := by linarith [Real.pi_pos, hδ1]
    have hθ0mem : Real.pi / 2 - δ ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hspos, by linarith [hδpos]⟩
    set E := 2 * KL * δ + ε / 24 with hEdef
    have hEnn : 0 ≤ E := by rw [hEdef]; positivity
    have hFsmall : ∀ t ∈ Ico (Real.pi / 2 - δ) (Real.pi / 2), |F z t| < ε / 24 := by
      intro t ht
      have hmem : (z, t) ∈ Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ :=
        ⟨hzpos, ⟨by linarith [hspos, ht.1], le_of_lt ht.2⟩⟩
      have hdist : dist (z, t) (z0, Real.pi / 2) < δF := by
        rw [Prod.dist_eq, max_lt_iff]
        constructor
        · rw [Real.dist_eq]
          exact lt_of_lt_of_le hznear (by linarith [hδF2])
        · rw [Real.dist_eq]
          have h1 : |t - Real.pi / 2| ≤ δ := by
            rw [abs_of_nonpos (by linarith [ht.2] : t - Real.pi / 2 ≤ 0), neg_sub]
            linarith [ht.1]
          linarith [h1, hδF2]
      have h := hδF (x := (z, t)) hmem hdist
      simpa [Function.uncurry] using h
    have hdV : ∀ t ∈ Ico (Real.pi / 2 - δ) (Real.pi / 2),
        |Work.Spaces.pth (Work.Construction.Vop (psiP αG Ψ)) z t| ≤ E := by
      intro t ht
      have htmem : (z, t) ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, by linarith [hspos, ht.1], ht.2⟩
      rw [hlaw z t htmem]
      have h2 := hDz z t htmem 2 (by norm_num)
      have h1 := hDz z t htmem 1 (by norm_num)
      have h0 := hDz z t htmem 0 (by norm_num)
      rw [Work.Spaces.DzIter_zero] at h0
      have hs : Work.Construction.s2 t ≤ 2 * (Real.pi / 2 - t) :=
        s2_le_two_sub (Work.FTS_StreamBdry.Qd_theta_mem htmem)
      have htri : |-(αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z t
            + 5 * αG * Work.Spaces.DzIter 1 (psiP αG Ψ) z t
            + 6 * psiP αG Ψ z t) - F z t|
          ≤ (αG ^ 2 * (M * (2 * (Real.pi / 2 - t))) + 5 * αG * (M * (2 * (Real.pi / 2 - t)))
              + 6 * (M * (2 * (Real.pi / 2 - t)))) + ε / 24 := by
        have hA : |αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z t|
            ≤ αG ^ 2 * (M * (2 * (Real.pi / 2 - t))) := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg αG)]
          exact mul_le_mul_of_nonneg_left (le_trans h2 (mul_le_mul_of_nonneg_left hs hMnn))
            (sq_nonneg αG)
        have hB : |5 * αG * Work.Spaces.DzIter 1 (psiP αG Ψ) z t|
            ≤ 5 * αG * (M * (2 * (Real.pi / 2 - t))) := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 5 * αG)]
          exact mul_le_mul_of_nonneg_left (le_trans h1 (mul_le_mul_of_nonneg_left hs hMnn))
            (by linarith)
        have hC : |6 * psiP αG Ψ z t| ≤ 6 * (M * (2 * (Real.pi / 2 - t))) := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
          exact mul_le_mul_of_nonneg_left (le_trans h0 (mul_le_mul_of_nonneg_left hs hMnn))
            (by norm_num)
        have hstep : |-(αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z t
              + 5 * αG * Work.Spaces.DzIter 1 (psiP αG Ψ) z t
              + 6 * psiP αG Ψ z t) - F z t|
            ≤ |αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z t
              + 5 * αG * Work.Spaces.DzIter 1 (psiP αG Ψ) z t
              + 6 * psiP αG Ψ z t| + |F z t| := by
          have h := abs_add_le (-(αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z t
              + 5 * αG * Work.Spaces.DzIter 1 (psiP αG Ψ) z t
              + 6 * psiP αG Ψ z t)) (-(F z t))
          rw [abs_neg, abs_neg] at h
          simpa [sub_eq_add_neg] using h
        have h3 := abs_add_three (αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z t)
          (5 * αG * Work.Spaces.DzIter 1 (psiP αG Ψ) z t) (6 * psiP αG Ψ z t)
        have hFs : |F z t| ≤ ε / 24 := le_of_lt (hFsmall t ht)
        linarith [hstep, h3, hA, hB, hC, hFs]
      have hE : (αG ^ 2 * (M * (2 * (Real.pi / 2 - t))) + 5 * αG * (M * (2 * (Real.pi / 2 - t)))
            + 6 * (M * (2 * (Real.pi / 2 - t)))) + ε / 24 ≤ E := by
        have hpm : Real.pi / 2 - t ≤ δ := by linarith [ht.1]
        have hc : M * (2 * (Real.pi / 2 - t)) ≤ M * (2 * δ) :=
          mul_le_mul_of_nonneg_left (by linarith) hMnn
        have h1' : αG ^ 2 * (M * (2 * (Real.pi / 2 - t))) ≤ αG ^ 2 * (M * (2 * δ)) :=
          mul_le_mul_of_nonneg_left hc (sq_nonneg αG)
        have h2' : 5 * αG * (M * (2 * (Real.pi / 2 - t))) ≤ 5 * αG * (M * (2 * δ)) :=
          mul_le_mul_of_nonneg_left hc (by linarith)
        have h3' : 6 * (M * (2 * (Real.pi / 2 - t))) ≤ 6 * (M * (2 * δ)) :=
          mul_le_mul_of_nonneg_left hc (by norm_num)
        have h4' : αG ^ 2 * (M * (2 * δ)) + 5 * αG * (M * (2 * δ)) + 6 * (M * (2 * δ))
            = 2 * KL * δ := by rw [hKL]; ring
        rw [hEdef]; linarith [h1', h2', h3', h4']
      exact le_trans htri hE
    have hrate : ∀ t ∈ Ico (Real.pi / 2 - δ) (Real.pi / 2),
        |Work.Construction.Vop (psiP αG Ψ) z t - Vb z| ≤ E * (Real.pi / 2 - t) := by
      refine rate_of_deriv_le hθ0mem hEnn ?_ ?_ ?_
      · intro t ht
        show DifferentiableAt ℝ (fun t' => Work.Construction.Vop (psiP αG Ψ) z t') t
        have htmem : (z, t) ∈ Work.Construction.Qd :=
          Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, by linarith [hspos, ht.1], ht.2⟩
        have hdP : DifferentiableAt ℝ (fun t' => psiP αG Ψ z t') t :=
          Work.Spaces.differentiableAt_curry_right
            ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds htmem))
        have hdpth : DifferentiableAt ℝ (fun t' => Work.Spaces.pth (psiP αG Ψ) z t') t :=
          Work.Spaces.differentiableAt_curry_right
            ((hpth1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds htmem))
        have htan : DifferentiableAt ℝ Real.tan t :=
          Real.differentiableAt_tan.mpr (ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd htmem))
        have hfun : (fun t' => Work.Construction.Vop (psiP αG Ψ) z t')
            = fun t' => Work.Spaces.pth (psiP αG Ψ) z t'
              - Real.tan t' * psiP αG Ψ z t' := by
          funext t'; rw [Work.Construction.Vop]
        rw [hfun]
        exact hdpth.sub (htan.mul hdP)
      · intro t ht
        show |Work.Spaces.pth (Work.Construction.Vop (psiP αG Ψ)) z t| ≤ E
        exact hdV t ⟨le_of_lt ht.1, ht.2⟩
      · have hlt : ∀ᶠ t in 𝓝[Iio (Real.pi / 2)] (Real.pi / 2), Real.pi / 2 - δ < t :=
          (eventually_gt_nhds (by linarith [hδpos])).filter_mono nhdsWithin_le_nhds
        have hlt2 : ∀ᶠ t in 𝓝[Iio (Real.pi / 2)] (Real.pi / 2), 0 < t :=
          (eventually_gt_nhds (by linarith [Real.pi_pos])).filter_mono nhdsWithin_le_nhds
        have h0 : Tendsto (fun t => Work.Construction.Vop (psiP αG Ψ) z t - Vb z)
            (𝓝[Iio (Real.pi / 2)] (Real.pi / 2)) (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          refine squeeze_zero' (Eventually.of_forall fun t => abs_nonneg _) ?_
            ((tendsto_const_mul_sub_zero ((αG ^ 2 + 5 * αG + 6) * M + Mf)
              (Real.pi / 2)).mono_left nhdsWithin_le_nhds)
          filter_upwards [hlt, hlt2, self_mem_nhdsWithin] with t ht1 ht2 ht3
          have htmem : (z, t) ∈ Work.Construction.Qd :=
            Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, ht2, ht3⟩
          have h := hVb z t htmem
          simpa [Real.norm_eq_abs] using h
        have h1 := h0.add_const (Vb z)
        simpa using h1
    have hB4 := Work.FTS_StreamBdry.SB25.axis_d2_bound
      (fun t => psiP αG Ψ z t) (Vb z) M E θ
    simp only [Work.FTS_StreamBdry.SB25.AxisD2Bound] at hB4
    have hdiff2 : ∀ θ' ∈ Ioo (0 : ℝ) (Real.pi / 2),
        DifferentiableAt ℝ (fun t => psiP αG Ψ z t) θ'
          ∧ DifferentiableAt ℝ (deriv (fun t => psiP αG Ψ z t)) θ' := by
      intro θ' hθ'
      have hmem' : (z, θ') ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩
      refine ⟨Work.Spaces.differentiableAt_curry_right
          ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem')), ?_⟩
      show DifferentiableAt ℝ (fun t => Work.Spaces.pth (psiP αG Ψ) z t) θ'
      exact Work.Spaces.differentiableAt_curry_right
        ((hpth1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem'))
    have hbd2 : ∀ θ' ∈ Ioo (0 : ℝ) (Real.pi / 2), |(fun t => psiP αG Ψ z t) θ'| ≤ M := by
      intro θ' hθ'
      have hmem' : (z, θ') ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩
      have h0 := hDz z θ' hmem' 0 (by norm_num)
      rw [Work.Spaces.DzIter_zero] at h0
      have hs1 : Work.Construction.s2 θ' ≤ 1 := by
        rw [Work.Construction.s2_eq]; exact Real.sin_le_one _
      exact le_trans h0 (by simpa using mul_le_of_le_one_right hMnn hs1)
    have hVrate : ∀ t ∈ Ico θ (Real.pi / 2),
        |deriv (fun t' => psiP αG Ψ z t') t
          - Real.tan t * (fun t' => psiP αG Ψ z t') t - Vb z| ≤ E * (Real.pi / 2 - t) := by
      intro t ht
      show |Work.Construction.Vop (psiP αG Ψ) z t - Vb z| ≤ E * (Real.pi / 2 - t)
      exact hrate t ⟨by linarith [hthlo, ht.1], ht.2⟩
    have hVbd : ∀ t ∈ Ico θ (Real.pi / 2),
        |deriv (fun s => deriv (fun t' => psiP αG Ψ z t') s
          - Real.tan s * (fun t' => psiP αG Ψ z t') s) t| ≤ E := by
      intro t ht
      show |Work.Spaces.pth (Work.Construction.Vop (psiP αG Ψ)) z t| ≤ E
      exact hdV t ⟨by linarith [hthlo, ht.1], ht.2⟩
    have hres := hB4 hθm hdiff2 hbd2 hVrate hVbd
    have hCVb : |Vb z| ≤ CV := by
      have h := hδV hznearV
      rw [Real.dist_eq] at h
      rw [hCV]
      have h2 : |Vb z| ≤ |Vb z - Vb z0| + |Vb z0| := by
        calc |Vb z| = |(Vb z - Vb z0) + Vb z0| := by ring_nf
          _ ≤ |Vb z - Vb z0| + |Vb z0| := abs_add_le _ _
      linarith [h]
    have hbound2 : |Work.Spaces.pth (Work.Spaces.pth (psiP αG Ψ)) z θ| ≤ 6 * E + CV * δ := by
      have h1 : |Vb z| * (Real.pi / 2 - θ) ≤ CV * δ := by
        have hp : Real.pi / 2 - θ ≤ δ := by linarith [hthlo]
        have hp0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθm.2]
        nlinarith [hCVb, hp, hp0, hCVnn, hδpos]
      have hres' : |Work.Spaces.pth (Work.Spaces.pth (psiP αG Ψ)) z θ|
          ≤ 6 * E + |Vb z| * (Real.pi / 2 - θ) := hres
      linarith [hres', h1]
    have hfin : 6 * E + CV * δ < ε := by
      have hEeq : E = 2 * KL * δ + ε / 24 := hEdef
      have hd1 : δ * (12 * KL + CV) ≤ ε / 4 := by
        have hD : 0 < 4 * (12 * KL + CV + 1) := by positivity
        have h2 := (le_div_iff₀ hD).mp hδeps
        nlinarith [h2, hδpos]
      rw [hEeq]; nlinarith [hd1, hε]
    show dist (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth (psiP αG Ψ))) (z, θ)) 0 < ε
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt hbound2 hfin

end Work.FTS_StreamBdry.SB25Aux4
