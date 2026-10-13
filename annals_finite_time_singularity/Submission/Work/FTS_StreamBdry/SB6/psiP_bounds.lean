import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.infra
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.pth_DzIter_le
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.AsmSupport
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.pthIter2_eq
import Submission.Work.FTS_StreamBdry.sb1_gauge_proved
import Submission.Work.FTS_StreamBdry.SB5Aux.unif_decay_ratio_proved

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.psiP_bounds` — pointwise decay and `θ`-bounds for `psiP`

* `psiP_tendsto_atTop`: `psiP z θ → 0` as `z → ∞` (gauge decomposition + decay of `Ψ`);
* `psiP_pthIter2_le`: `|∂_θ² psiP| ≤ K` from the identity `pthIter2_eq` and a bound on
  `∂_θ(psiP/sin 2θ)`;
* `psiP_unif_decay`: the uniform-in-`θ` smallness `|psiP z θ| ≤ ε·sin 2θ` for `z ≥ R` (leaf E5).
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-- The pointwise decay of the `U`-slot part at `z → ∞`, from the gauge decomposition
`Ψ = psiP + κ·gaugeMode` and the decay of `Ψ`. -/
theorem psiP_tendsto_atTop {αG M : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z => psiP αG Ψ z θ) Filter.atTop (nhds 0) := by
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.sb1_gauge_proved (αG := αG) (M := M) hαG h3 hslot
  intro θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Ioo hθ)
  -- `Ψ (·, θ) → 0`
  have h1 : Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0) := hsol.2.2.2 θ hθI
  -- `gaugeMode αG (·, θ) → 0`
  have h2 : Filter.Tendsto (fun z => Work.FTS.StreamBdryIface.gaugeMode αG z θ)
      Filter.atTop (nhds 0) := by
    have hexp : 0 < 3 / αG := by positivity
    have hz0 : Filter.Tendsto (fun z : ℝ => z ^ (-(3 / αG))) Filter.atTop (nhds 0) :=
      tendsto_rpow_neg_atTop hexp
    have h4 := hz0.div_const (Real.cos θ)
    simpa only [Work.FTS.StreamBdryIface.gaugeMode, zero_div] using h4
  have h5 : Filter.Tendsto (fun z => Ψ z θ - κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ)
      Filter.atTop (nhds (0 - κ * 0)) := h1.sub (h2.const_mul κ)
  simp only [mul_zero, sub_zero] at h5
  refine h5.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with z hz
  have hmem : (z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨by linarith, hθ.1, hθ.2⟩
  rw [hκ z θ hmem]
  ring

/-- **The second `θ`-derivative of `psiP` is bounded**, given a uniform bound `Ku` on
`∂_θ(psiP/sin 2θ)` (which is what the ground-state ODE `Lgs u = F/s2` provides).

The identity is `pthIter2_eq`: for `u = psiP/sin 2θ`,
`∂_θ² psiP = -4 sin 2θ·u + 2 sin²θ·u' - F - sin 2θ·(α²D_z²u + 5α D_zu)`; the fields `u`, `D_zu`,
`D_z²u` are bounded by `M` on the quadrant (`psiP_DzLe` + the division identities) and `|F| ≤ Mf`
(`SrcOK`). -/
theorem psiP_pthIter2_le {αG M L Mf Ku : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hu : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ| ≤ Ku) :
    ∃ K : ℝ, 0 < K ∧ ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pthIter 2 (psiP αG Ψ) z θ| ≤ K := by
  have hM : 0 ≤ M := M_nonneg hslot
  have hMf : 0 ≤ Mf := by
    have hθ : (Real.pi / 4 : ℝ) ∈ Work.Spaces.Iθ :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (Work.FTS_StreamBdry.SrcOK.F_le hF (z := 1) (by norm_num) hθ)
  have hP3 : ContDiffOn ℝ 3 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.P2Aux.psiP_c3 hαG h3 hslot
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hCt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (Function.uncurry (psiP αG Ψ)) (z, θ) :=
    fun z θ h => hP2.contDiffAt (hQd.mem_nhds h)
  have hlaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp αG (psiP αG Ψ) z θ = F z θ :=
    Work.FTS_StreamBdry.SB3.P2Aux.bslOp_psiP hαG hsol h3 hslot
  have hdiv := Work.FTS_StreamBdry.SB3.P2Aux.div_identities (P := psiP αG Ψ) hP3
  have hDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ :=
    fun z θ h j hj => Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot z θ h j hj
  have hsp1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Construction.s2 θ ≤ 1 := by
    intro z θ _
    rw [Work.Construction.s2_eq]
    exact Real.sin_le_one _
  -- the `D_z`-bounds for `u = psiP/s2`
  have hu0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |psiP αG Ψ z θ / Work.Construction.s2 θ| ≤ M := by
    intro z θ h
    have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd h
    rw [abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
    exact hDz z θ h 0 (by norm_num)
  have hdiv1 := fun (z θ : ℝ) (h : (z, θ) ∈ Work.Construction.Qd) =>
    hdiv.1 z θ h 1 (by norm_num)
  have hdiv2 := fun (z θ : ℝ) (h : (z, θ) ∈ Work.Construction.Qd) =>
    hdiv.1 z θ h 2 (by norm_num)
  have hu1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.Dz (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ M := by
    intro z θ h
    have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd h
    have heq : Work.Spaces.Dz (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
        = Work.Spaces.DzIter 1 (psiP αG Ψ) z θ / Work.Construction.s2 θ := by
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hdiv1 z θ h
    rw [heq, abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
    exact hDz z θ h 1 (by norm_num)
  have hu2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 2 (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ M := by
    intro z θ h
    have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd h
    rw [hdiv2 z θ h, abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
    exact hDz z θ h 2 (by norm_num)
  have hKun : 0 ≤ Ku := by
    have h1 : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr
        ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (hu 1 (Real.pi / 4) h1)
  have hKpos : (0 : ℝ) < 4 * M + 2 * Ku + Mf + (αG ^ 2 + 5 * |αG|) * M + 1 := by
    have hc : 0 ≤ (αG ^ 2 + 5 * |αG|) * M := by positivity
    linarith
  refine ⟨_, hKpos, ?_⟩
  intro z θ hmem
  have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
  have hs2nn : 0 ≤ Work.Construction.s2 θ := le_of_lt hsp
  have hs2le : Work.Construction.s2 θ ≤ 1 := hsp1 z θ hmem
  rw [Work.FTS_StreamBdry.SB3.P2Aux.pthIter2_eq hCt hlaw z θ hmem]
  have h1 : |-4 * Work.Construction.s2 θ * (psiP αG Ψ z θ / Work.Construction.s2 θ)|
      ≤ 4 * M := by
    have habs : |(-4 : ℝ)| = 4 := by norm_num
    rw [abs_mul, abs_mul, habs, abs_of_nonneg hs2nn]
    calc 4 * Work.Construction.s2 θ * |psiP αG Ψ z θ / Work.Construction.s2 θ|
        ≤ 4 * 1 * M := by
          refine mul_le_mul (by linarith) (hu0 z θ hmem) (abs_nonneg _) (by norm_num)
      _ = 4 * M := by ring
  have h2 : |2 * Real.sin θ ^ 2
      * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ| ≤ 2 * Ku := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sin θ ^ 2)]
    have hs : Real.sin θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ, sq_nonneg (Real.sin θ)]
    calc 2 * Real.sin θ ^ 2 * |deriv (fun θ' => psiP αG Ψ z θ'
          / Work.Construction.s2 θ') θ|
        ≤ 2 * 1 * Ku :=
          mul_le_mul (by linarith) (hu z θ hmem) (abs_nonneg _) (by norm_num)
      _ = 2 * Ku := by ring
  have h3' : |F z θ| ≤ Mf :=
    Work.FTS_StreamBdry.SrcOK.F_le hF (Work.FTS_StreamBdry.Qd_pos hmem)
      (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)
  have h4 : |Work.Construction.s2 θ
      * (αG ^ 2 * Work.Spaces.DzIter 2 (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
        + 5 * αG * Work.Spaces.Dz
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ)|
      ≤ (αG ^ 2 + 5 * |αG|) * M := by
    have hb1 : |αG ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ|
        ≤ αG ^ 2 * M := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ αG ^ 2)]
      exact mul_le_mul_of_nonneg_left (hu2 z θ hmem) (by positivity)
    have hb2 : |5 * αG * Work.Spaces.Dz
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ 5 * |αG| * M := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 5)]
      exact mul_le_mul_of_nonneg_left (hu1 z θ hmem) (by positivity)
    have hb : |αG ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
          + 5 * αG * Work.Spaces.Dz
            (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ|
        ≤ (αG ^ 2 + 5 * |αG|) * M :=
      (abs_add_le _ _).trans (by linarith [hb1, hb2])
    rw [abs_mul, abs_of_nonneg hs2nn]
    calc Work.Construction.s2 θ * |αG ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
        + 5 * αG * Work.Spaces.Dz
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ|
        ≤ 1 * ((αG ^ 2 + 5 * |αG|) * M) :=
          mul_le_mul hs2le hb (abs_nonneg _) (by positivity)
      _ = (αG ^ 2 + 5 * |αG|) * M := by ring
  have htot := abs_four_sub_le h1 h2 h3' h4
  linarith [htot]

/-- **The uniform decay of `psiP` in `θ`**: pointwise decay in `z` together with the uniform
`θ`-bounds (`SB5Aux.unif_decay_ratio_proved`, leaf E5) gives
`|psiP z θ| ≤ ε·sin 2θ` for `z ≥ R`. -/
theorem psiP_unif_decay {αG M L Mf Ku : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hu : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ| ≤ Ku) :
    ∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |psiP αG Ψ z θ| ≤ ε * Work.Construction.s2 θ := by
  obtain ⟨K2, hK2pos, hK2⟩ := psiP_pthIter2_le (Ku := Ku) hαG hsol h3 hslot hF hu
  have hM : 0 ≤ M := M_nonneg hslot
  have hDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 3,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ max M (2 * M / αG) * Work.Construction.s2 θ := by
    intro z θ h j hj
    have hs2nn : 0 ≤ Work.Construction.s2 θ :=
      Work.FTS_StreamBdry.s2_nonneg_of_Iθ (Work.FTS_StreamBdry.Qd_theta_Iθ h)
    rcases Nat.lt_or_ge j 3 with hj3 | hj3
    · have hj2 : j ≤ 2 := by omega
      exact (Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot z θ h j hj2).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hs2nn)
    · have hj3' : j = 3 := by omega
      subst hj3'
      exact (Work.FTS_StreamBdry.SB3.psiP_D3_le hαG h3 hslot z θ h).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hs2nn)
  obtain ⟨K1, hK1⟩ := Work.FTS_StreamBdry.SB3.pth_DzIter_le (Sg := max M (2 * M / αG))
    hαG h3 hslot hDz
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot
  have hPth1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (psiP αG Ψ)))
      Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.contDiffOn_uncurry_pth_qd hP2
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hdiff : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun θ' => psiP αG Ψ z θ') θ ∧
        DifferentiableAt ℝ (fun θ' => Work.Spaces.pth (psiP αG Ψ) z θ') θ := by
    intro z θ h
    refine ⟨Work.Spaces.differentiableAt_curry_right
        ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds h)),
      Work.Spaces.differentiableAt_curry_right
        ((hPth1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds h))⟩
  have hlim : ∀ z, 0 < z → Filter.Tendsto (fun θ => psiP αG Ψ z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ => psiP αG Ψ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    intro z hz
    have hzQd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (z, θ) ∈ Work.Construction.Qd := fun θ hθ =>
      Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩
    have hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |psiP αG Ψ z θ| ≤ M * Work.Construction.s2 θ :=
      fun θ hθ => Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot z θ (hzQd θ hθ) 0
        (by norm_num)
    exact ⟨tendsto_zero_of_abs_le_s2_left hM hb, tendsto_zero_of_abs_le_s2_right hM hb⟩
  have hdec : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z => psiP αG Ψ z θ) Filter.atTop (nhds 0) :=
    psiP_tendsto_atTop hαG hsol h3 hslot
  have hK1nn : 0 ≤ K1 := by
    have h1 : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr
        ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (hK1 1 (Real.pi / 4) h1 0 (by norm_num))
  have hmain := Work.FTS_StreamBdry.SB5Aux.unif_decay_ratio_proved (psiP αG Ψ) (max K1 K2)
    hdiff
    (fun z θ h => (hK1 z θ h 0 (by norm_num)).trans (le_max_left _ _))
    (fun z θ h => (hK2 z θ h).trans (le_max_right _ _))
    hlim hdec
  exact hmain


end Work.FTS_StreamBdry.SB6
