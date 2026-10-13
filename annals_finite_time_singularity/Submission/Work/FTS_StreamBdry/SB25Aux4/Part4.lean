import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB25.axis_tan_bound
import Submission.Work.FTS_StreamBdry.SB25Aux4.EdgeAxisAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux4.psiP_edge_axis_mixed`

The mixed second partials of `P := psiP αG Ψ` at `(z₀, π/2)`.

By Clairaut (`∂_z∂_θP = ∂_θ∂_zP`, `P` being `C²`), it suffices to handle `∂_θ∂_zP`, and

  `∂_θ∂_zP = (D_z(V(P)) + tan θ·D_zP)/z`

(`pth_pz_eq`).  `SB25.axis_tan_bound` applied to the slice `θ ↦ D_zP(z,θ)` — whose "`V`" is
`D_z(V(P))/z`, with the edge trace `DVb` and rate `|K'|/z` — gives
`tan θ·D_zP → -DVb z/(2z)`; together with `D_z(V(P)) → DVb z` this yields
`∂_θ∂_zP → DVb z₀/(2z₀)`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux4

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

theorem psiP_edge_axis_mixed {αG M K' : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M)
    (hK' : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K')
    (DVb : ℝ → ℝ) (hDVbc : ContinuousOn DVb (Set.Ioi 0))
    (hDVb : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 1 (Work.Construction.Vop (psiP αG Ψ)) z θ - DVb z|
        ≤ |K'| * (Real.pi / 2 - θ)) :
    ∀ z0 : ℝ, 0 < z0 →
      ∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth (psiP αG Ψ))))
          (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l) ∧
        Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ))))
          (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l) := by
  have hMnn : 0 ≤ M := by
    have h1 := Work.FTS_StreamBdry.SlotBd.Dz_le hslot (z := 1) (θ := Real.pi / 4)
      Work.FTS_StreamBdry.SB1.Qd_nonempty (j := 0) (by norm_num)
    exact le_trans (abs_nonneg _) h1
  have hDz := Work.FTS_StreamBdry.SB3.psiP_DzLe (αG := αG) (M := M) hαG h3 hslot
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 (αG := αG) (M := M) hαG h3 hslot
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (psiP αG Ψ)))
      Work.Construction.Qd := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ (Function.uncurry (psiP αG Ψ)))
        Work.Construction.Qd := hP2.fderiv_of_isOpen hQd (m := 1) (by norm_num)
    refine (hfd.clm_apply (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ))))).congr (fun p hp => ?_)
    simp only [Function.uncurry]
    exact Work.Spaces.pz_eq_fderiv
      ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hp))
  intro z0 hz0
  have hK'nn : 0 ≤ K' := by
    have h1 := hK' 1 (Real.pi / 4) Work.FTS_StreamBdry.SB1.Qd_nonempty
    exact le_trans (abs_nonneg _) h1
  have hDVbc_at : ContinuousAt DVb z0 := hDVbc.continuousAt (isOpen_Ioi.mem_nhds hz0)
  set CDV := |DVb z0| + 1 with hCDV
  have hCDVnn : 0 ≤ CDV := by rw [hCDV]; positivity
  have hCDV_ev : ∀ᶠ p : ℝ × ℝ in 𝓝 (z0, Real.pi / 2), |DVb p.1| ≤ CDV := by
    have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (z0, Real.pi / 2), dist (DVb p.1) (DVb z0) < 1 :=
      hDVbc_at.tendsto.comp (tendsto_fst' (a := z0) (b := Real.pi / 2))
        |>.eventually (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [h1] with p hp
    rw [Real.dist_eq] at hp
    have h2 : |DVb p.1| ≤ |DVb p.1 - DVb z0| + |DVb z0| := by
      calc |DVb p.1| = |(DVb p.1 - DVb z0) + DVb z0| := by ring_nf
        _ ≤ |DVb p.1 - DVb z0| + |DVb z0| := abs_add_le _ _
    rw [hCDV]; linarith
  set CV2 := 4 * |K'| + CDV * (Real.pi / 2) with hCV2
  have hCV2nn : 0 ≤ CV2 := by rw [hCV2]; positivity
  have hgoal2 : Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ))))
      (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 (DVb z0 / (2 * z0))) := by
    refine tendsto_nhdsWithin_of_abs_le (L := DVb z0 / (2 * z0))
      (g := fun p : ℝ × ℝ => |DVb p.1 / (2 * p.1) - DVb z0 / (2 * z0)|
        + (2 / z0) * CV2 * (Real.pi / 2 - p.2)) ?_ ?_
    · have hc : ContinuousAt (fun z : ℝ => DVb z / (2 * z)) z0 := by
        have hnum : ContinuousAt DVb z0 := hDVbc_at
        have hden : ContinuousAt (fun z : ℝ => 2 * z) z0 :=
          continuousAt_const.mul continuousAt_id
        exact hnum.div hden (by positivity)
      have h1 : Tendsto (fun p : ℝ × ℝ => |DVb p.1 / (2 * p.1) - DVb z0 / (2 * z0)|)
          (𝓝 (z0, Real.pi / 2)) (𝓝 0) := tendsto_abs_sub_const hc
      have h2 := tendsto_const_mul_sub_snd_zero ((2 / z0) * CV2) z0
      simpa using h1.add h2
    · refine eventually_nhdsWithin_iff.mpr ?_
      have hz_ev : ∀ᶠ p : ℝ × ℝ in 𝓝 (z0, Real.pi / 2), z0 / 2 < p.1 :=
        (tendsto_fst' (a := z0) (b := Real.pi / 2)).eventually
          ((isOpen_Ioi (a := z0 / 2)).mem_nhds (by linarith : z0 / 2 < z0))
      filter_upwards [hCDV_ev, hz_ev] with p hpV hpz hmem
      obtain ⟨z, θ⟩ := p
      have hpV' : |DVb z| ≤ CDV := hpV
      have hpz' : z0 / 2 < z := hpz
      have hθ := Work.FTS_StreamBdry.Qd_theta_mem hmem
      have hzpos : 0 < z := Work.FTS_StreamBdry.Qd_pos hmem
      have hb3 := Work.FTS_StreamBdry.SB25.axis_tan_bound
        (fun θ' => Work.Spaces.pz (psiP αG Ψ) z θ') (DVb z / z) (|K'| / z) (M / z)
      simp only [Work.FTS_StreamBdry.SB25.AxisTanBound] at hb3
      have hdiff : ∀ θ' ∈ Ioo (0 : ℝ) (Real.pi / 2),
          DifferentiableAt ℝ (fun θ'' => Work.Spaces.pz (psiP αG Ψ) z θ'') θ' := by
        intro θ' hθ'
        have hmem' : (z, θ') ∈ Work.Construction.Qd :=
          Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩
        exact Work.Spaces.differentiableAt_curry_right
          ((hpz1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem'))
      have hbd : ∀ θ' ∈ Ioo (0 : ℝ) (Real.pi / 2),
          |(fun θ'' => Work.Spaces.pz (psiP αG Ψ) z θ'') θ'| ≤ M / z := by
        intro θ' hθ'
        have hmem' : (z, θ') ∈ Work.Construction.Qd :=
          Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩
        have h1 := hDz z θ' hmem' 1 (by norm_num)
        have h1' : |z * Work.Spaces.pz (psiP αG Ψ) z θ'| ≤ M * Work.Construction.s2 θ' := by
          rwa [show Work.Spaces.DzIter 1 (psiP αG Ψ) z θ'
            = z * Work.Spaces.pz (psiP αG Ψ) z θ' from rfl] at h1
        rw [abs_mul, abs_of_pos hzpos] at h1'
        rw [le_div_iff₀ hzpos]
        have hs1 : Work.Construction.s2 θ' ≤ 1 := by
          rw [Work.Construction.s2_eq]; exact Real.sin_le_one _
        calc |Work.Spaces.pz (psiP αG Ψ) z θ'| * z
            = z * |Work.Spaces.pz (psiP αG Ψ) z θ'| := by ring
          _ ≤ M * Work.Construction.s2 θ' := h1'
          _ ≤ M * 1 := mul_le_mul_of_nonneg_left hs1 hMnn
          _ = M := mul_one M
      have hcl : ∀ θ' ∈ Ioo (0 : ℝ) (Real.pi / 2),
          |deriv (fun θ'' => Work.Spaces.pz (psiP αG Ψ) z θ'') θ'
              - Real.tan θ' * Work.Spaces.pz (psiP αG Ψ) z θ' - DVb z / z|
            ≤ (|K'| / z) * (Real.pi / 2 - θ') := by
        intro θ' hθ'
        have hmem' : (z, θ') ∈ Work.Construction.Qd :=
          Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩
        show |Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ)) z θ'
          - Real.tan θ' * Work.Spaces.pz (psiP αG Ψ) z θ' - DVb z / z| ≤ _
        have h1 := pth_pz_eq (P := psiP αG Ψ) hP2 hmem'
        have h2 : Work.Spaces.pz (psiP αG Ψ) z θ'
            = Work.Spaces.DzIter 1 (psiP αG Ψ) z θ' / z := by
          rw [show Work.Spaces.DzIter 1 (psiP αG Ψ) z θ'
              = z * Work.Spaces.pz (psiP αG Ψ) z θ' from rfl]
          field_simp
        have h3 : Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ)) z θ'
              - Real.tan θ' * Work.Spaces.pz (psiP αG Ψ) z θ'
            = Work.Spaces.DzIter 1 (Work.Construction.Vop (psiP αG Ψ)) z θ' / z := by
          rw [h1, h2]; field_simp; ring
        rw [h3, ← sub_div, abs_div, abs_of_pos hzpos]
        calc |Work.Spaces.DzIter 1 (Work.Construction.Vop (psiP αG Ψ)) z θ' - DVb z| / z
            ≤ (|K'| * (Real.pi / 2 - θ')) / z :=
              div_le_div_of_nonneg_right (hDVb z θ' hmem') (le_of_lt hzpos)
          _ = (|K'| / z) * (Real.pi / 2 - θ') := by ring
      have hres := hb3 hdiff hbd hcl θ hθ
      have hVbd2 : |(Work.Spaces.DzIter 1 (Work.Construction.Vop (psiP αG Ψ)) z θ - DVb z) / z|
          ≤ |K'| * (Real.pi / 2 - θ) / z := by
        rw [abs_div, abs_of_pos hzpos]
        exact div_le_div_of_nonneg_right (hDVb z θ hmem) (le_of_lt hzpos)
      have hsq : (Real.pi / 2 - θ) ^ 2 ≤ (Real.pi / 2) * (Real.pi / 2 - θ) := by
        have hp0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
        have hp1 : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
        nlinarith
      have hmid : |Real.tan θ * Work.Spaces.pz (psiP αG Ψ) z θ + DVb z / (2 * z)|
          ≤ |DVb z| / z * ((Real.pi / 2) * (Real.pi / 2 - θ))
            + 3 * (|K'| / z) * (Real.pi / 2 - θ) := by
        have hp0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
        have hv : |DVb z / z| = |DVb z| / z := by rw [abs_div, abs_of_pos hzpos]
        have h2 : |DVb z / z| * (Real.pi / 2 - θ) ^ 2
            ≤ |DVb z| / z * ((Real.pi / 2) * (Real.pi / 2 - θ)) := by
          rw [hv]
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
        have hres' : |Real.tan θ * Work.Spaces.pz (psiP αG Ψ) z θ + DVb z / (2 * z)|
            ≤ |DVb z / z| * (Real.pi / 2 - θ) ^ 2 + 3 * (|K'| / z) * (Real.pi / 2 - θ) := by
          have h := hres
          rw [show DVb z / z / 2 = DVb z / (2 * z) from by ring] at h
          exact h
        linarith [hres', h2]
      have hident : Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ)) z θ - DVb z0 / (2 * z0)
          = (Work.Spaces.DzIter 1 (Work.Construction.Vop (psiP αG Ψ)) z θ - DVb z) / z
            + (Real.tan θ * Work.Spaces.pz (psiP αG Ψ) z θ + DVb z / (2 * z))
            + (DVb z / (2 * z) - DVb z0 / (2 * z0)) := by
        have h1 := pth_pz_eq (P := psiP αG Ψ) hP2 hmem
        have h2 : Work.Spaces.pz (psiP αG Ψ) z θ
            = Work.Spaces.DzIter 1 (psiP αG Ψ) z θ / z := by
          rw [show Work.Spaces.DzIter 1 (psiP αG Ψ) z θ
              = z * Work.Spaces.pz (psiP αG Ψ) z θ from rfl]
          field_simp
        rw [h1, h2]; field_simp; ring
      have hgoal : |Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ)) z θ - DVb z0 / (2 * z0)|
          ≤ |DVb z / (2 * z) - DVb z0 / (2 * z0)| + (2 / z0) * CV2 * (Real.pi / 2 - θ) := by
        rw [hident]
        calc |(Work.Spaces.DzIter 1 (Work.Construction.Vop (psiP αG Ψ)) z θ - DVb z) / z
                + (Real.tan θ * Work.Spaces.pz (psiP αG Ψ) z θ + DVb z / (2 * z))
                + (DVb z / (2 * z) - DVb z0 / (2 * z0))|
            ≤ |(Work.Spaces.DzIter 1 (Work.Construction.Vop (psiP αG Ψ)) z θ - DVb z) / z|
              + |Real.tan θ * Work.Spaces.pz (psiP αG Ψ) z θ + DVb z / (2 * z)|
              + |DVb z / (2 * z) - DVb z0 / (2 * z0)| := by
              linarith [abs_add_three ((Work.Spaces.DzIter 1
                  (Work.Construction.Vop (psiP αG Ψ)) z θ - DVb z) / z)
                (Real.tan θ * Work.Spaces.pz (psiP αG Ψ) z θ + DVb z / (2 * z))
                (DVb z / (2 * z) - DVb z0 / (2 * z0))]
          _ ≤ |DVb z / (2 * z) - DVb z0 / (2 * z0)| + (2 / z0) * CV2 * (Real.pi / 2 - θ) := by
              have hp0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
              have hzge : z0 / 2 ≤ z := le_of_lt hpz'
              have h1z : 1 / z ≤ 2 / z0 := by
                have h := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < z0 / 2) hzge
                rwa [one_div_div] at h
              have hKz : |K'| / z ≤ (2 / z0) * |K'| := by
                calc |K'| / z = |K'| * (1 / z) := by ring
                  _ ≤ |K'| * (2 / z0) := mul_le_mul_of_nonneg_left h1z (abs_nonneg _)
                  _ = (2 / z0) * |K'| := by ring
              have h1 : |K'| * (Real.pi / 2 - θ) / z
                  ≤ (2 / z0) * |K'| * (Real.pi / 2 - θ) := by
                calc |K'| * (Real.pi / 2 - θ) / z
                    = (|K'| / z) * (Real.pi / 2 - θ) := by ring
                  _ ≤ ((2 / z0) * |K'|) * (Real.pi / 2 - θ) :=
                      mul_le_mul_of_nonneg_right hKz hp0
                  _ = (2 / z0) * |K'| * (Real.pi / 2 - θ) := by ring
              have h2a : |DVb z| / z ≤ CDV * (2 / z0) := by
                calc |DVb z| / z = |DVb z| * (1 / z) := by ring
                  _ ≤ CDV * (2 / z0) :=
                      mul_le_mul hpV' h1z (by positivity) (le_trans (abs_nonneg _) hpV')
              have h2 : |DVb z| / z * ((Real.pi / 2) * (Real.pi / 2 - θ))
                  ≤ (2 / z0) * (CDV * (Real.pi / 2)) * (Real.pi / 2 - θ) := by
                have h2b : 0 ≤ (Real.pi / 2) * (Real.pi / 2 - θ) := by positivity
                calc |DVb z| / z * ((Real.pi / 2) * (Real.pi / 2 - θ))
                    ≤ (CDV * (2 / z0)) * ((Real.pi / 2) * (Real.pi / 2 - θ)) :=
                      mul_le_mul_of_nonneg_right h2a h2b
                  _ = (2 / z0) * (CDV * (Real.pi / 2)) * (Real.pi / 2 - θ) := by ring
              have h3 : 3 * (|K'| / z) * (Real.pi / 2 - θ)
                  ≤ 3 * ((2 / z0) * |K'| * (Real.pi / 2 - θ)) := by
                calc 3 * (|K'| / z) * (Real.pi / 2 - θ)
                    = 3 * ((|K'| / z) * (Real.pi / 2 - θ)) := by ring
                  _ ≤ 3 * (((2 / z0) * |K'|) * (Real.pi / 2 - θ)) :=
                      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKz hp0)
                        (by norm_num)
                  _ = 3 * ((2 / z0) * |K'| * (Real.pi / 2 - θ)) := by ring
              have h4 : |K'| * (Real.pi / 2 - θ) / z
                    + (|DVb z| / z * ((Real.pi / 2) * (Real.pi / 2 - θ))
                        + 3 * (|K'| / z) * (Real.pi / 2 - θ))
                  ≤ (2 / z0) * CV2 * (Real.pi / 2 - θ) := by
                rw [hCV2]
                linarith [h1, h2, h3]
              linarith [hVbd2, hmid, h4]
      simpa [Function.uncurry] using hgoal
  have hgoal1 : Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth (psiP αG Ψ))))
      (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 (DVb z0 / (2 * z0))) := by
    have hev : Function.uncurry (Work.Spaces.pz (Work.Spaces.pth (psiP αG Ψ)))
        =ᶠ[𝓝[Work.Construction.Qd] (z0, Real.pi / 2)]
        Function.uncurry (Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ))) := by
      refine eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun p hp => ?_)
      obtain ⟨z, θ⟩ := p
      have hcl := Work.Spaces.pz_pth_comm (f := psiP αG Ψ)
        ((hP2.contDiffAt (hQd.mem_nhds hp)).of_le (le_refl (2 : WithTop ℕ∞)))
      simp only [Function.uncurry]
      exact hcl
    exact hgoal2.congr' hev.symm
  exact ⟨DVb z0 / (2 * z0), hgoal1, hgoal2⟩

end Work.FTS_StreamBdry.SB25Aux4
