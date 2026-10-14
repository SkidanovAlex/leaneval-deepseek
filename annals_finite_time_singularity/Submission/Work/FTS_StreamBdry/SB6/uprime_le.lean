import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25Aux4.Part2
import Submission.Work.FTS_StreamBdry.SB25Aux4.Part4
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound2
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.clauses3
import Submission.Work.FTS_StreamBdry.SBpsiP.DzJ_crux
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.FTS_StreamBdry.sb2_dthDV_proved
import Submission.Work.FTS_StreamBdry.sb5_barrier_proved
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux4.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux4.psiP_edge_axis_aux`

Assembly of the three parts into the full `θ = π/2` edge-limit statement for
`P := psiP αG Ψ`, with the edge traces `Vb` (of `V(P)`) and `DVb` (of `D_z(V(P))`) as inputs.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux4

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

theorem psiP_edge_axis_aux {αG M L Mf K' : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M)
    (hsrc : SrcOK F L Mf)
    (hK' : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K')
    (Vb : ℝ → ℝ) (hVbc : ContinuousOn Vb (Set.Ioi 0))
    (hVb : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Construction.Vop (psiP αG Ψ) z θ - Vb z|
        ≤ ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ))
    (DVb : ℝ → ℝ) (hDVbc : ContinuousOn DVb (Set.Ioi 0))
    (hDVb : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 1 (Work.Construction.Vop (psiP αG Ψ)) z θ - DVb z|
        ≤ |K'| * (Real.pi / 2 - θ)) :
    ∀ z0 : ℝ, 0 < z0 →
      (Tendsto (Function.uncurry (psiP αG Ψ)) (𝓝[Work.Construction.Qd] (z0, Real.pi / 2))
          (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pz (psiP αG Ψ)))
            (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) ∧
          Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ))))
            (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) ∧
            Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth (psiP αG Ψ))))
              (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) ∧
              (∃ l, Tendsto (Function.uncurry (Work.Spaces.pth (psiP αG Ψ)))
                (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l)) ∧
                ∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth (psiP αG Ψ))))
                    (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l) ∧
                  Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ))))
                    (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l)) := by
  intro z0 hz0
  obtain ⟨h1, h2, h3'⟩ := psiP_edge_axis_zero123 hαG h3 hslot z0 hz0
  exact ⟨h1, h2, h3',
    psiP_edge_axis_pthth hαG hsol h3 hslot hsrc Vb hVbc hVb z0 hz0,
    psiP_edge_axis_pth hαG h3 hslot Vb hVbc hVb z0 hz0,
    psiP_edge_axis_mixed (K' := K') hαG h3 hslot hK' DVb hDVbc hDVb z0 hz0⟩

end Work.FTS_StreamBdry.SB25Aux4
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB5.Prep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB5.Prep` — elementary facts, dilations and the `bslOp`-harmonicity of the difference quotients.
-/

namespace Work.FTS_StreamBdry.SB5

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false

noncomputable section




/-! ## §1 Elementary facts about `s2` and the quadrant -/

theorem isOpen_Qd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

theorem continuous_s2 : Continuous Work.Construction.s2 := by
  rw [show Work.Construction.s2 = fun θ : ℝ => Real.sin (2 * θ) from
    funext fun θ => Work.Construction.s2_eq θ]
  fun_prop

theorem s2_zero : Work.Construction.s2 0 = 0 := by
  rw [Work.Construction.s2_eq]; simp

theorem s2_pi_div_two : Work.Construction.s2 (π / 2) = 0 := by
  rw [Work.Construction.s2_eq]
  have h : 2 * (π / 2) = π := by ring
  rw [h, Real.sin_pi]

theorem tendsto_s2_zero_right : Tendsto Work.Construction.s2 (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h : Tendsto Work.Construction.s2 (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h' := continuous_s2.tendsto (0 : ℝ)
    rwa [s2_zero] at h'
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_s2_zero_left : Tendsto Work.Construction.s2 (𝓝[<] (π / 2)) (𝓝 0) := by
  have h : Tendsto Work.Construction.s2 (𝓝 (π / 2 : ℝ)) (𝓝 0) := by
    have h' := continuous_s2.tendsto (π / 2 : ℝ)
    rwa [s2_pi_div_two] at h'
  exact h.mono_left nhdsWithin_le_nhds

/-- **Endpoint vanishing from a `sin 2θ` bound.**  If `|Q z θ| ≤ M sin 2θ` on the quadrant then
the `θ`-slice of `Q` at a fixed `z > 0` vanishes at both ends. -/
theorem tendsto_zero_endpoints_of_abs_le_s2 {Q : ℝ → ℝ → ℝ} {M z : ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Q z θ| ≤ M * Work.Construction.s2 θ)
    (hz : 0 < z) :
    Tendsto (fun θ => Q z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun θ => Q z θ) (𝓝[<] (π / 2)) (𝓝 0) := by
  have hlt : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < π / 2 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)] with θ hθ _
    exact hθ
  have hgt : ∀ᶠ θ in 𝓝[<] (π / 2), (0 : ℝ) < θ := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)] with θ hθ _
    exact hθ
  have hb : Tendsto (fun θ => M * Work.Construction.s2 θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_s2_zero_right.const_mul M
  have hb' : Tendsto (fun θ => M * Work.Construction.s2 θ) (𝓝[<] (π / 2)) (𝓝 0) := by
    simpa using tendsto_s2_zero_left.const_mul M
  constructor
  · refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin, hlt] with θ hθ hθ2
    rw [Real.norm_eq_abs]
    exact h z θ (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθ, hθ2⟩)
  · refine squeeze_zero_norm' ?_ hb'
    filter_upwards [self_mem_nhdsWithin, hgt] with θ hθ hθ2
    rw [Real.norm_eq_abs]
    exact h z θ (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθ2, hθ⟩)

/-- Continuity on `Ici L` of a slice `z ↦ Q z θ` of a `C¹` function on the quadrant. -/
theorem continuousOn_slice_of_contDiffOn {Q : ℝ → ℝ → ℝ} {L θ : ℝ} (hL : 0 < L)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (hQ : ContDiffOn ℝ 1 (Function.uncurry Q) Work.Construction.Qd) :
    ContinuousOn (fun z => Q z θ) (Ici L) := by
  intro z hz
  have hmem : (z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨lt_of_lt_of_le hL hz, hθ.1, hθ.2⟩
  have hd : DifferentiableAt ℝ (Function.uncurry Q) (z, θ) :=
    (hQ.contDiffAt (isOpen_Qd.mem_nhds hmem)).differentiableAt (by norm_num)
  exact (Work.Spaces.differentiableAt_curry_left hd).continuousAt.continuousWithinAt

/-! ## §2 Dilation, difference quotients, and their smoothness -/

/-- A dilation of the first variable preserves `ContDiffOn` on the quadrant (it maps the
quadrant into itself when the factor is positive). -/
theorem contDiffOn_dilate {P : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 < c) {n : WithTop ℕ∞}
    (h : ContDiffOn ℝ n (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => P (c * z) θ)) Work.Construction.Qd := by
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (c * p.1, p.2)) Work.Construction.Qd
      Work.Construction.Qd := by
    intro p hp
    rw [Work.FTS_StreamBdry.mem_Qd] at hp ⊢
    exact ⟨mul_pos hc hp.1, hp.2⟩
  have hf : ContDiffOn ℝ n (fun p : ℝ × ℝ => (c * p.1, p.2)) Work.Construction.Qd := by
    fun_prop
  have hcomp := h.comp hf hmaps
  convert hcomp using 1
  funext p
  rfl

/-- Pointwise version of `contDiffOn_dilate`. -/
theorem contDiffAt_dilate {P : ℝ → ℝ → ℝ} {c z θ : ℝ} {n : ℕ}
    (h : ContDiffAt ℝ (n : WithTop ℕ∞) (Function.uncurry P) (c * z, θ)) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (Function.uncurry (fun z θ => P (c * z) θ)) (z, θ) := by
  have hf : ContDiffAt ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => (c * p.1, p.2)) (z, θ) := by
    fun_prop
  have hcomp := h.comp (z, θ) hf
  convert hcomp using 1
  funext p
  rfl

/-- Multiplying a `ContDiffOn` function by a constant (in the `curry`-form). -/
theorem contDiffOn_const_mul_field {A : ℝ → ℝ → ℝ} {a : ℝ} {n : WithTop ℕ∞}
    (hA : ContDiffOn ℝ n (Function.uncurry A) Work.Construction.Qd) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => a * A z θ)) Work.Construction.Qd := by
  refine (hA.const_smul a).congr ?_
  intro p hp
  dsimp only [Function.uncurry, Pi.smul_apply]
  rw [smul_eq_mul]

/-- Multiplying a `ContDiffAt` function by a constant (in the `curry`-form). -/
theorem contDiffAt_const_mul_field {A : ℝ → ℝ → ℝ} {a z θ : ℝ}
    (hA : ContDiffAt ℝ 2 (Function.uncurry A) (z, θ)) :
    ContDiffAt ℝ 2 (Function.uncurry (fun z θ => a * A z θ)) (z, θ) := by
  refine (hA.const_smul a).congr_of_eventuallyEq ?_
  filter_upwards with p
  dsimp only [Function.uncurry, Pi.smul_apply]
  rw [smul_eq_mul]

/-- The first logarithmic difference quotient of `P` at step `h`. -/
def dilDiff (P : ℝ → ℝ → ℝ) (h : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (P (Real.exp h * z) θ - P z θ) / h

/-- The second logarithmic difference quotient of `P` at step `h`. -/
def dilDiff2 (P : ℝ → ℝ → ℝ) (h : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (P (Real.exp (2 * h) * z) θ - 2 * P (Real.exp h * z) θ + P z θ) / h ^ 2

theorem contDiffOn_dilDiff {P : ℝ → ℝ → ℝ} {h : ℝ} {n : WithTop ℕ∞}
    (hP : ContDiffOn ℝ n (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ n (Function.uncurry (dilDiff P h)) Work.Construction.Qd := by
  have hA : ContDiffOn ℝ n (Function.uncurry (fun z θ => P (Real.exp h * z) θ))
      Work.Construction.Qd := contDiffOn_dilate (Real.exp_pos h) hP
  have hsub : ContDiffOn ℝ n (Function.uncurry (fun z θ => P (Real.exp h * z) θ)
      - Function.uncurry P) Work.Construction.Qd := hA.sub hP
  refine (hsub.div_const h).congr ?_
  intro p hp
  simp only [Function.uncurry, Pi.sub_apply, dilDiff]

theorem contDiffOn_dilDiff2 {P : ℝ → ℝ → ℝ} {h : ℝ} {n : WithTop ℕ∞}
    (hP : ContDiffOn ℝ n (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ n (Function.uncurry (dilDiff2 P h)) Work.Construction.Qd := by
  have hA2 : ContDiffOn ℝ n (Function.uncurry (fun z θ => P (Real.exp (2 * h) * z) θ))
      Work.Construction.Qd := contDiffOn_dilate (Real.exp_pos (2 * h)) hP
  have hA1 : ContDiffOn ℝ n (Function.uncurry (fun z θ => P (Real.exp h * z) θ))
      Work.Construction.Qd := contDiffOn_dilate (Real.exp_pos h) hP
  have hc : ContDiffOn ℝ n (Function.uncurry (fun z θ => (2 : ℝ) * P (Real.exp h * z) θ))
      Work.Construction.Qd := contDiffOn_const_mul_field (a := (2 : ℝ)) hA1
  have hmain : ContDiffOn ℝ n (Function.uncurry (fun z θ =>
      P (Real.exp (2 * h) * z) θ - 2 * P (Real.exp h * z) θ + P z θ))
      Work.Construction.Qd := by
    refine ((hA2.sub hc).add hP).congr ?_
    intro p hp
    dsimp only [Function.uncurry, Pi.sub_apply, Pi.add_apply]
  refine (hmain.div_const (h ^ 2)).congr ?_
  intro p hp
  dsimp only [Function.uncurry, dilDiff2]

/-! ## §3 `bslOp` of the difference quotients -/

/-- The three-term linearity of `bslOp` at a point of the quadrant. -/
theorem bslOp_lin3 {α a b c : ℝ} {A B C : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hQd : (z, θ) ∈ Work.Construction.Qd)
    (hA : ContDiffAt ℝ 2 (Function.uncurry A) (z, θ))
    (hB : ContDiffAt ℝ 2 (Function.uncurry B) (z, θ))
    (hC : ContDiffAt ℝ 2 (Function.uncurry C) (z, θ)) :
    Work.Elliptic.bslOp α (fun z θ => a * A z θ + b * B z θ + c * C z θ) z θ
      = a * Work.Elliptic.bslOp α A z θ + b * Work.Elliptic.bslOp α B z θ
        + c * Work.Elliptic.bslOp α C z θ := by
  have hAB : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => a * A z θ + b * B z θ)) (z, θ) := by
    have h1 : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => a * A z θ)) (z, θ) :=
      contDiffAt_const_mul_field (a := a) hA
    have h2 : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => b * B z θ)) (z, θ) :=
      contDiffAt_const_mul_field (a := b) hB
    refine (h1.add h2).congr_of_eventuallyEq ?_
    filter_upwards with p
    dsimp only [Function.uncurry, Pi.add_apply]
  have h1 := Work.FTS_StreamBdry.SB25.bslOp_lincombQd α a b A B z θ hQd hA hB
  have h2 := Work.FTS_StreamBdry.SB25.bslOp_lincombQd α 1 c
    (fun z θ => a * A z θ + b * B z θ) C z θ hQd hAB hC
  have hc : Work.Elliptic.bslOp α (fun z θ => a * A z θ + b * B z θ + c * C z θ) z θ
      = Work.Elliptic.bslOp α (fun z θ =>
          1 * (fun z θ => a * A z θ + b * B z θ) z θ + c * C z θ) z θ := by
    apply Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq
    filter_upwards with q
    ring
  rw [hc, h2, h1]
  ring

/-- `bslOp` of the first difference quotient vanishes above `z = L`. -/
theorem bslOp_dilDiff_eq_zero {α L : ℝ} (hL : 0 < L) {P F : ℝ → ℝ → ℝ}
    (hP3 : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd)
    (hbsl : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Elliptic.bslOp α P z θ = F z θ)
    (hF0 : ∀ z θ, L ≤ z → θ ∈ Work.Spaces.Iθ → F z θ = 0)
    {h : ℝ} (hh : 0 < h) {z θ : ℝ} (hz : L < z) (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    Work.Elliptic.bslOp α (dilDiff P h) z θ = 0 := by
  have hz0 : 0 < z := lt_trans hL hz
  have hV : IsOpen Work.Construction.Qd := isOpen_Qd
  have hexp1 : 1 ≤ Real.exp h := Real.one_le_exp (le_of_lt hh)
  have hQd : (z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz0, hθ.1, hθ.2⟩
  have hmemA : (Real.exp h * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr
      ⟨mul_pos (lt_of_lt_of_le one_pos hexp1) hz0, hθ.1, hθ.2⟩
  have hA2 : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => P (Real.exp h * z) θ)) (z, θ) :=
    contDiffAt_dilate ((hP3.contDiffAt (hV.mem_nhds hmemA)).of_le (by norm_num))
  have hB2 : ContDiffAt ℝ 2 (Function.uncurry P) (z, θ) :=
    (hP3.contDiffAt (hV.mem_nhds hQd)).of_le (by norm_num)
  have hlin := Work.FTS_StreamBdry.SB25.bslOp_lincombQd α (1 / h) (-(1 / h))
    (fun z θ => P (Real.exp h * z) θ) P z θ hQd hA2 hB2
  have hdil := Work.FTS_StreamBdry.SB25.bslOp_dilate α (Real.exp h) P z θ
  have hcongr : Work.Elliptic.bslOp α (dilDiff P h) z θ
      = Work.Elliptic.bslOp α
          (fun z θ => (1 / h) * P (Real.exp h * z) θ + (-(1 / h)) * P z θ) z θ := by
    apply Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq
    filter_upwards with q
    simp only [dilDiff]
    ring
  have hA0 : Work.Elliptic.bslOp α (fun z θ => P (Real.exp h * z) θ) z θ = 0 := by
    rw [hdil, hbsl _ _ hmemA]
    exact hF0 _ _ (le_trans (le_of_lt hz)
      (le_mul_of_one_le_left (le_of_lt hz0) hexp1)) (Work.FTS_StreamBdry.Qd_theta_Iθ hmemA)
  have hB0 : Work.Elliptic.bslOp α P z θ = 0 := by
    rw [hbsl _ _ hQd]
    exact hF0 _ _ (le_of_lt hz) (Work.FTS_StreamBdry.Qd_theta_Iθ hQd)
  rw [hcongr, hlin, hA0, hB0, mul_zero, neg_mul, mul_zero, neg_zero, add_zero]

/-- `bslOp` of the second difference quotient vanishes above `z = L`. -/
theorem bslOp_dilDiff2_eq_zero {α L : ℝ} (hL : 0 < L) {P F : ℝ → ℝ → ℝ}
    (hP3 : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd)
    (hbsl : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Elliptic.bslOp α P z θ = F z θ)
    (hF0 : ∀ z θ, L ≤ z → θ ∈ Work.Spaces.Iθ → F z θ = 0)
    {h : ℝ} (hh : 0 < h) {z θ : ℝ} (hz : L < z) (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    Work.Elliptic.bslOp α (dilDiff2 P h) z θ = 0 := by
  have hz0 : 0 < z := lt_trans hL hz
  have hV : IsOpen Work.Construction.Qd := isOpen_Qd
  have h1 : (1 : ℝ) ≤ Real.exp h := Real.one_le_exp (le_of_lt hh)
  have h2 : (1 : ℝ) ≤ Real.exp (2 * h) := Real.one_le_exp (by positivity)
  have hQd : (z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz0, hθ.1, hθ.2⟩
  have hm2 : (Real.exp (2 * h) * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (lt_of_lt_of_le one_pos h2) hz0, hθ.1, hθ.2⟩
  have hm1 : (Real.exp h * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (lt_of_lt_of_le one_pos h1) hz0, hθ.1, hθ.2⟩
  have hA2 : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => P (Real.exp (2 * h) * z) θ)) (z, θ) :=
    contDiffAt_dilate ((hP3.contDiffAt (hV.mem_nhds hm2)).of_le (by norm_num))
  have hA1 : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => P (Real.exp h * z) θ)) (z, θ) :=
    contDiffAt_dilate ((hP3.contDiffAt (hV.mem_nhds hm1)).of_le (by norm_num))
  have hB2 : ContDiffAt ℝ 2 (Function.uncurry P) (z, θ) :=
    (hP3.contDiffAt (hV.mem_nhds hQd)).of_le (by norm_num)
  have hlin := bslOp_lin3 (α := α) (a := 1 / h ^ 2) (b := -(2 / h ^ 2)) (c := 1 / h ^ 2)
    (A := fun z θ => P (Real.exp (2 * h) * z) θ) (B := fun z θ => P (Real.exp h * z) θ)
    (C := P) hQd hA2 hA1 hB2
  have hcongr : Work.Elliptic.bslOp α (dilDiff2 P h) z θ
      = Work.Elliptic.bslOp α (fun z θ => (1 / h ^ 2) * P (Real.exp (2 * h) * z) θ
          + (-(2 / h ^ 2)) * P (Real.exp h * z) θ + (1 / h ^ 2) * P z θ) z θ := by
    apply Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq
    filter_upwards with q
    simp only [dilDiff2]
    ring
  have hA20 : Work.Elliptic.bslOp α (fun z θ => P (Real.exp (2 * h) * z) θ) z θ = 0 := by
    rw [Work.FTS_StreamBdry.SB25.bslOp_dilate α (Real.exp (2 * h)) P z θ, hbsl _ _ hm2]
    exact hF0 _ _ (le_trans (le_of_lt hz)
      (le_mul_of_one_le_left (le_of_lt hz0) h2)) (Work.FTS_StreamBdry.Qd_theta_Iθ hm2)
  have hA10 : Work.Elliptic.bslOp α (fun z θ => P (Real.exp h * z) θ) z θ = 0 := by
    rw [Work.FTS_StreamBdry.SB25.bslOp_dilate α (Real.exp h) P z θ, hbsl _ _ hm1]
    exact hF0 _ _ (le_trans (le_of_lt hz)
      (le_mul_of_one_le_left (le_of_lt hz0) h1)) (Work.FTS_StreamBdry.Qd_theta_Iθ hm1)
  have hB0 : Work.Elliptic.bslOp α P z θ = 0 := by
    rw [hbsl _ _ hQd]
    exact hF0 _ _ (le_of_lt hz) (Work.FTS_StreamBdry.Qd_theta_Iθ hQd)
  rw [hcongr, hlin, hA20, hA10, hB0]
  ring


end

end Work.FTS_StreamBdry.SB5
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.Vop_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.Vop_deriv` — `∂_θV(psiP)` in the far field
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-- **The `θ`-derivative of `V(psiP)` in the far field**: the law in `D`-form
`∂_θV(P) = -(α²D_z²P + 5αD_zP + 6P) - F` together with the far-field decay of `D_z^jP` (`j ≤ 2`)
and the vanishing of `F` above `L`. -/
theorem Vop_deriv_le {αG M L Mf Kf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hKf : 0 ≤ Kf)
    (hfar : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG)) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
      |deriv (fun t => Work.Construction.Vop (psiP αG Ψ) z t) θ|
        ≤ (αG ^ 2 + 5 * |αG| + 6) * Kf * (L / z) ^ (4 / αG) * Work.Construction.s2 θ := by
  intro z θ hmem hzL
  have hL : 0 < L := hF.2.2.2.2.1
  have hzpos : 0 < z := Work.FTS_StreamBdry.Qd_pos hmem
  have hθI : θ ∈ Work.Spaces.Iθ := Work.FTS_StreamBdry.Qd_theta_Iθ hmem
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot
  have hlaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp αG (psiP αG Ψ) z θ = F z θ :=
    Work.FTS_StreamBdry.SB3.P2Aux.bslOp_psiP hαG hsol h3 hslot
  have hkey := Work.FTS_StreamBdry.SB25.law_Dform αG F (psiP αG Ψ) hP2 hlaw z θ hmem
  have hb0 := hfar z θ hmem hzL 0 (by norm_num)
  have hb1 := hfar z θ hmem hzL 1 (by norm_num)
  have hb2 := hfar z θ hmem hzL 2 (by norm_num)
  have hb1' : |Work.Spaces.Dz (psiP αG Ψ) z θ|
      ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hb1
  have hF0 : F z θ = 0 := hF.2.2.2.2.2 z θ hzL hθI
  have hkey' : deriv (fun t => Work.Construction.Vop (psiP αG Ψ) z t) θ
      = -(αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
          + 5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ + 6 * psiP αG Ψ z θ) - F z θ := by
    simpa only [Work.Spaces.pth] using hkey
  rw [hkey', hF0, sub_zero]
  set A : ℝ := Work.Spaces.DzIter 2 (psiP αG Ψ) z θ with hA
  set B : ℝ := Work.Spaces.Dz (psiP αG Ψ) z θ with hB
  set C : ℝ := psiP αG Ψ z θ with hC
  have hb2' : |A| ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by
    rw [hA]; exact hb2
  have hb1'' : |B| ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by
    rw [hB]; exact hb1'
  have hb0' : |C| ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by
    rw [hC]; exact hb0
  have h1 : |αG ^ 2 * A| = αG ^ 2 * |A| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ αG ^ 2)]
  have h2 : |5 * αG * B| = 5 * |αG| * |B| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
  have h3 : |(6 : ℝ) * C| = 6 * |C| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
  have hb2'' : |A| ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := hb2'
  have htri : |-(αG ^ 2 * A + 5 * αG * B + 6 * C)|
      ≤ αG ^ 2 * |A| + 5 * |αG| * |B| + 6 * |C| := by
    rw [abs_neg]
    refine (abs_three_le (a := αG ^ 2 * A) (b := 5 * αG * B) (c := 6 * C)).trans ?_
    rw [h1, h2, h3]
  have hstep : αG ^ 2 * |A| + 5 * |αG| * |B| + 6 * |C|
      ≤ αG ^ 2 * (Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG))
        + 5 * |αG| * (Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG))
        + 6 * (Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG)) := by
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact mul_le_mul_of_nonneg_left hb2'' (by positivity)
    · exact mul_le_mul_of_nonneg_left hb1'' (by positivity)
    · exact mul_le_mul_of_nonneg_left hb0' (by norm_num)
  refine htri.trans (hstep.trans (le_of_eq ?_))
  ring

end Work.FTS_StreamBdry.SB6
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.uprime_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.uprime_le` — `∂_θ (psiP αG Ψ / sin 2θ)` is bounded on the quadrant

The object `u := psiP αG Ψ / sin 2θ` is the `U`-slot part of the stream function divided by
`sin 2θ`.  By the elliptic law for `psiP` (`SB3.P2Aux.bslOp_div_s2_hasDerivAt`) it solves the
singular second-order ODE

  `u'' + (4 cos 2θ / sin 2θ - tan θ) u' = -(α² D_z² u + 5 α D_z u) - F/sin 2θ`

on the open quadrant.  The right hand side is controlled by `|F| ≤ Mf` and `|D_z^j u| ≤ M`
(`j ≤ 2`, from `SB3.psiP_DzLe`), and the derivative itself by `|∂_θ psiP| ≤ K'`
(`SB3.pth_DzIter_le`) through `sin 2θ · u' = ∂_θ psiP - 2 cos 2θ · u`.  The abstract
singular-ODE bound `UprimeAux.ode_deriv_bound_fam` then gives the result.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The `θ`-identity `sin 2θ · u' = ∂_θ psiP - 2 cos 2θ · u`. -/
lemma s2_mul_u1 {αG : ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hCt : ContDiffAt ℝ 2 (Function.uncurry (psiP αG Ψ)) (z, θ))
    (hsne : Work.Construction.s2 θ ≠ 0) :
    Work.Construction.s2 θ * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ
      = deriv (fun θ' => psiP αG Ψ z θ') θ
        - 2 * Real.cos (2 * θ) * (psiP αG Ψ z θ / Work.Construction.s2 θ) := by
  have hslice : ContDiffAt ℝ 2 (fun θ' => psiP αG Ψ z θ') θ := by
    have h2 := hCt.comp θ (ContDiffAt.prodMk contDiffAt_const contDiffAt_id)
    convert h2 using 1
    funext x; rfl
  have hP : HasDerivAt (fun θ' => psiP αG Ψ z θ') (deriv (fun θ' => psiP αG Ψ z θ') θ) θ :=
    (hslice.differentiableAt (by norm_num)).hasDerivAt
  have hs : HasDerivAt (fun θ' : ℝ => Work.Construction.s2 θ') (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    have h3 : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
    rw [h3] at h2
    exact h2
  have hdiv := hP.div hs hsne
  have hf : ((fun θ' => psiP αG Ψ z θ') / (fun θ' => Work.Construction.s2 θ'))
      = (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') := by
    funext x; rfl
  have hval : deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ
      = (deriv (fun θ' => psiP αG Ψ z θ') θ * Work.Construction.s2 θ
          - psiP αG Ψ z θ * (2 * Real.cos (2 * θ))) / Work.Construction.s2 θ ^ 2 := by
    have h := hdiv.deriv
    rw [hf] at h
    exact h
  rw [hval]
  field_simp
  try ring


theorem uprime_le {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf) :
    ∃ K : ℝ, 0 < K ∧ ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |deriv (fun θ' => Work.FTS.StreamBdryIface.psiP αG Ψ z θ'
        / Work.Construction.s2 θ') θ| ≤ K := by
  have hQdopen : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB3.P2Aux.isOpen_Qd_asm
  have hC3 : ContDiffOn ℝ 3 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.P2Aux.psiP_c3 hαG h3 hslot
  have hslaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp αG (psiP αG Ψ) z θ = F z θ :=
    Work.FTS_StreamBdry.SB3.P2Aux.bslOp_psiP hαG hsol h3 hslot
  have hCt2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (Function.uncurry (psiP αG Ψ)) (z, θ) := fun z θ hmem =>
    (hC3.contDiffAt (hQdopen.mem_nhds hmem)).of_le (by norm_num)
  have hode0 := Work.FTS_StreamBdry.SB3.P2Aux.bslOp_div_s2_hasDerivAt
    (α := αG) (Q := psiP αG Ψ) (F := F) hCt2 hslaw
  -- the membership witness `(1, π/4) ∈ Qd`
  have hmem0 : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd := by
    rw [Work.FTS_StreamBdry.mem_Qd]
    exact ⟨by norm_num, by positivity, by linarith [Real.pi_pos]⟩
  have hM_nonneg : 0 ≤ M := by
    have h := (hslot 1 (Real.pi / 4) hmem0).1 0 (by norm_num)
    rw [Work.Spaces.DzIter_zero] at h
    exact le_trans (abs_nonneg _) h
  have hMf_nonneg : 0 ≤ Mf := by
    have h1 : |F 1 0| ≤ Mf :=
      (hF.2.2.1 1 0 (by norm_num) ⟨le_refl (0 : ℝ), by positivity⟩).1
    have h2 : F 1 0 = 0 := (hF.2.2.2.1 1 (by norm_num)).1
    rw [h2, abs_zero] at h1
    exact h1
  -- the `D_z`-bounds on `u`
  have hdiv := Work.FTS_StreamBdry.SB3.P2Aux.div_identities (P := psiP αG Ψ) hC3
  have hDzLe : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ :=
    fun z θ hmem => (Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot) z θ hmem
  have huDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ M := by
    intro z θ hmem j hj
    have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
    have h := hdiv.1 z θ hmem j (by omega)
    rw [h, abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
    exact hDzLe z θ hmem j hj
  -- the `H` of the abstract ODE bound
  have hH : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |-(F z θ) / Work.Construction.s2 θ
        - (αG ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
          + 5 * αG * Work.Spaces.Dz
            (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ)|
        ≤ Mf / Work.Construction.s2 θ + (αG ^ 2 * M + 5 * αG * M) := by
    intro z θ hmem
    have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
    have hFle : |F z θ| ≤ Mf :=
      (hF.2.2.1 z θ (Work.FTS_StreamBdry.Qd_pos hmem) (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)).1
    have h1 : |Work.Spaces.DzIter 2
        (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ M :=
      huDz z θ hmem 2 (by norm_num)
    have h2 : |Work.Spaces.Dz
        (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ M :=
      huDz z θ hmem 1 (by norm_num)
    have habs : |F z θ / Work.Construction.s2 θ| ≤ Mf / Work.Construction.s2 θ := by
      rw [abs_div, abs_of_pos hsp]
      exact div_le_div_of_nonneg_right hFle hsp.le
    have h4 : |αG ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
        + 5 * αG * Work.Spaces.Dz
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ αG ^ 2 * M + 5 * αG * M := by
      refine (abs_add_le _ _).trans ?_
      have ha : |αG ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ αG ^ 2 * M := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ αG ^ 2)]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hb : |5 * αG * Work.Spaces.Dz
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ 5 * αG * M := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 5 * αG)]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith
    have heq : -(F z θ) / Work.Construction.s2 θ
          - (αG ^ 2 * Work.Spaces.DzIter 2
              (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
            + 5 * αG * Work.Spaces.Dz
              (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ)
        = -((F z θ / Work.Construction.s2 θ)
            + (αG ^ 2 * Work.Spaces.DzIter 2
                (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
              + 5 * αG * Work.Spaces.Dz
                (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ)) := by ring
    rw [heq, abs_neg]
    exact (abs_add_le _ _).trans (add_le_add habs h4)
  -- the crude bound on `u'`
  have hSg : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 3,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ max M (2 * M / αG) * Work.Construction.s2 θ := by
    intro z θ hmem j hj
    have hsp : 0 ≤ Work.Construction.s2 θ := le_of_lt (Work.FTS_StreamBdry.s2_pos_of_Qd hmem)
    rcases (by omega : j ≤ 2 ∨ j = 3) with hj2 | hj3
    · have h := hDzLe z θ hmem j hj2
      have hMM : M ≤ max M (2 * M / αG) := le_max_left _ _
      nlinarith [h, hMM, hsp]
    · subst hj3
      have h := Work.FTS_StreamBdry.SB3.psiP_D3_le hαG h3 hslot z θ hmem
      have hMM : 2 * M / αG ≤ max M (2 * M / αG) := le_max_right _ _
      nlinarith [h, hMM, hsp]
  obtain ⟨Kp, hKp⟩ := Work.FTS_StreamBdry.SB3.pth_DzIter_le (Sg := max M (2 * M / αG))
    hαG h3 hslot hSg
  have hcrude : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Construction.s2 θ
        * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ| ≤ Kp + 2 * M := by
    intro z θ hmem
    have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
    have hsne : Work.Construction.s2 θ ≠ 0 := ne_of_gt hsp
    have hid : Work.Construction.s2 θ
          * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ
        = deriv (fun θ' => psiP αG Ψ z θ') θ
          - 2 * Real.cos (2 * θ) * (psiP αG Ψ z θ / Work.Construction.s2 θ) :=
      s2_mul_u1 (hCt := hCt2 z θ hmem) hsne
    have h1 : |deriv (fun θ' => psiP αG Ψ z θ') θ| ≤ Kp := hKp z θ hmem 0 (by norm_num)
    have h2 : |psiP αG Ψ z θ / Work.Construction.s2 θ| ≤ M := by
      rw [abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
      exact hDzLe z θ hmem 0 (by norm_num)
    have h3 : |2 * Real.cos (2 * θ) * (psiP αG Ψ z θ / Work.Construction.s2 θ)| ≤ 2 * M := by
      have hc : |Real.cos (2 * θ)| ≤ 1 := by
        rw [abs_le]
        exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      have h1 : |2 * Real.cos (2 * θ)| ≤ 2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        linarith [hc]
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    calc |Work.Construction.s2 θ
          * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ|
        = |deriv (fun θ' => psiP αG Ψ z θ') θ
            - 2 * Real.cos (2 * θ) * (psiP αG Ψ z θ / Work.Construction.s2 θ)| := by rw [hid]
      _ ≤ |deriv (fun θ' => psiP αG Ψ z θ') θ|
            + |2 * Real.cos (2 * θ) * (psiP αG Ψ z θ / Work.Construction.s2 θ)| := by
          simpa using abs_sub_le (deriv (fun θ' => psiP αG Ψ z θ') θ) 0
            (2 * Real.cos (2 * θ) * (psiP αG Ψ z θ / Work.Construction.s2 θ))
      _ ≤ Kp + 2 * M := add_le_add h1 h3
  -- the ODE in the exact shape of `ode_deriv_bound_fam`
  have hode : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ'))
        ((fun z θ => -(F z θ) / Work.Construction.s2 θ
            - (αG ^ 2 * Work.Spaces.DzIter 2
                (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
              + 5 * αG * Work.Spaces.Dz
                (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ)) z θ
          - (4 * Real.cos (2 * θ) / Work.Construction.s2 θ - Real.tan θ)
            * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ) θ := by
    intro z θ hmem
    refine (hode0 z θ hmem).congr_deriv ?_
    ring
  -- assemble
  have hKp_nonneg : 0 ≤ Kp := le_trans (abs_nonneg _) (hKp 1 (Real.pi / 4) hmem0 0 (by norm_num))
  have hC_nonneg : 0 ≤ αG ^ 2 * M + 5 * αG * M := by nlinarith [hM_nonneg, hαG]
  have hC1_nonneg : 0 ≤ Kp + 2 * M := by linarith [hKp_nonneg, hM_nonneg]
  obtain ⟨K, hK0, hK⟩ := Work.FTS_StreamBdry.SB6.UprimeAux.ode_deriv_bound_fam
    (u := fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ)
    (H := fun z θ => -(F z θ) / Work.Construction.s2 θ
      - (αG ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
        + 5 * αG * Work.Spaces.Dz
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ))
    hMf_nonneg hC_nonneg hC1_nonneg hode
    (fun z θ hmem => hH z θ hmem) hcrude
  exact ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun z θ hmem => by
    have h := hK z θ hmem
    exact le_trans h (le_max_left _ _)⟩

end Work.FTS_StreamBdry.SB6
end
end
