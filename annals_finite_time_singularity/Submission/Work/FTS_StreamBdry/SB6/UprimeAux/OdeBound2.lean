import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Sb5CmpCore
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.clauses3
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.FTS_StreamBdry.sb5_barrier_proved
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS_StreamBdry.SB2.sb2_dthDV =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB2

open scoped Real Topology
open Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `Work.FTS_StreamBdry.SB2.sb2_dthDV` — the angular Lipschitz bound for `D_z V(psiP)`

The SB2 sub-leaf of the StreamBdry chain: on the open quadrant `Qd = (0,∞) × (0,π/2)`, the
angular derivative of `D_z V(P)` is bounded, where `P = psiP αG Ψ`, `V = Construction.Vop`.

The mechanism is the `D`-form of the elliptic law for `P` (`SB3.law_psiP`, from
`SB25.law_Dform` + SB1′),

  `∂_θ V(P) = -(αG² D_z²P + 5αG D_zP + 6P) - F`   on `Qd`,

differentiated once in `z` (Clairaut on `V(P)`, which is `C²` on `Qd`):

  `∂_θ D_z V(P) = z ∂_z ∂_θV(P) = -(αG² D_z³P + 5αG D_z²P + 6D_zP) - D_zF`.

The right side is bounded by `(αG²+5αG+6)·K + Mf` as soon as `|D_z^jP| ≤ K·sin 2θ` for `j ≤ 3`
(the hypothesis `hD3`) and `|D_zF| ≤ Mf` (`SrcOK`), because `sin 2θ ≤ 1` on the quadrant.
-/

/-! ## §0 Finite-order smoothness of the partial derivatives on an open set

These four lemmas are the finite-order form of the `D`-calculus: each of `∂_z`, `∂_θ`, `D_z`
lowers the differentiability order by one on an open set, and `D_z^j` lowers it by `j`. -/

private theorem contDiffOn_uncurry_pz_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

private theorem contDiffOn_uncurry_pth_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

private theorem contDiffOn_uncurry_Dz_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hpz := contDiffOn_uncurry_pz_fin hV h
  have hfun : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p) V :=
    contDiff_fst.contDiffOn.mul hpz
  exact hfun.congr (fun p hp => rfl)

private theorem contDiffOn_uncurry_DzIter_shift {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (i n : ℕ) (h : ContDiffOn ℝ (n + i) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter i G)) V := by
  induction i generalizing n with
  | zero => simpa using h
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ]
      refine contDiffOn_uncurry_Dz_fin hV (ih (n + 1) ?_)
      exact h.of_le (Nat.cast_le.mpr (by omega : n + 1 + i ≤ n + (i + 1)))

/-! ## §0b The smoothness of `psiP`, `V(psiP)` and the relevant partials -/

/-- **Smoothness of `psiP`, of `V(psiP)` and of the relevant partials.**  `psiP αG Ψ` is `C³`
on the open quadrant (from the SB1′ gauge decomposition `Ψ = psiP + κ·gaugeMode`), hence
`V(psiP) = ∂_θ psiP - tan θ·psiP` is `C²`, `D_z^j psiP` is `C¹` for `j ≤ 2` and `∂_θV(psiP)`
is `C¹`. -/
private theorem smooth_inputs {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.StreamBdryIface.psiP αG Ψ))
        Work.Construction.Qd ∧
      ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop
        (Work.FTS.StreamBdryIface.psiP αG Ψ))) Work.Construction.Qd ∧
      (∀ j ≤ 2, ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter j
        (Work.FTS.StreamBdryIface.psiP αG Ψ))) Work.Construction.Qd) ∧
      ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Construction.Vop
        (Work.FTS.StreamBdryIface.psiP αG Ψ)))) Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  -- (1) `psiP` is `C³`, because `Ψ = psiP + κ·gaugeMode` on `Qd`
  have hP3 : ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS.StreamBdryIface.psiP αG Ψ)) Work.Construction.Qd := by
    obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M)
      hαG h3 hslot
      (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
      (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
      (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
    have hg : ContDiffOn ℝ 3
        (Function.uncurry (Work.FTS.StreamBdryIface.gaugeMode αG)) Work.Construction.Qd :=
      (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode αG).of_le le_top
    have hsub : ContDiffOn ℝ 3
        (fun p : ℝ × ℝ => Function.uncurry Ψ p
          - κ * Function.uncurry (Work.FTS.StreamBdryIface.gaugeMode αG) p)
        Work.Construction.Qd := h3.sub (contDiffOn_const.mul hg)
    refine hsub.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    have h := hκ z θ hp
    simp only [Function.uncurry]
    linarith
  -- (2) `V(psiP) = ∂_θ psiP - tan θ·psiP` is `C²`
  have hV2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop
      (Work.FTS.StreamBdryIface.psiP αG Ψ))) Work.Construction.Qd := by
    have hP2 : ContDiffOn ℝ 2
        (Function.uncurry (Work.FTS.StreamBdryIface.psiP αG Ψ)) Work.Construction.Qd :=
      hP3.of_le (by norm_num)
    have hpthP : ContDiffOn ℝ 2
        (Function.uncurry (Work.Spaces.pth (Work.FTS.StreamBdryIface.psiP αG Ψ)))
        Work.Construction.Qd := contDiffOn_uncurry_pth_fin hQd hP3
    have htan : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.tan p.2) Work.Construction.Qd := by
      have hsin : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2) Work.Construction.Qd :=
        Real.contDiff_sin.comp_contDiffOn contDiff_snd.contDiffOn
      have hcos : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.cos p.2) Work.Construction.Qd :=
        Real.contDiff_cos.comp_contDiffOn contDiff_snd.contDiffOn
      refine (hsin.div hcos (fun p hp =>
        ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Ioo hp.2))).congr ?_
      intro p _
      exact Real.tan_eq_sin_div_cos p.2
    exact hpthP.sub (htan.mul hP2)
  have hDz : ∀ j ≤ 2, ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter j
      (Work.FTS.StreamBdryIface.psiP αG Ψ))) Work.Construction.Qd := fun j hj =>
    contDiffOn_uncurry_DzIter_shift hQd j 1 (hP3.of_le (Nat.cast_le.mpr (by omega : 1 + j ≤ 3)))
  exact ⟨hP3, hV2, hDz, contDiffOn_uncurry_pth_fin hQd hV2⟩

/- **The `z`-derivative of the `D`-form of the law** (delegated; proved in
`Submission/Work/FTS_StreamBdry/SB2/sb2_deriv_law_rhs.lean` as
`Work.FTS_StreamBdry.SB2.sb2_deriv_law_rhs`).  Pure calculus: `D_z = z ∂_z` shifts the
iterated operator, so differentiating the right-hand side
`-(αG² D_z²P + 5αG D_zP + 6P) - F` of the law in `z` and multiplying by `z` gives
`-(αG² D_z³P + 5αG D_z²P + 6D_zP) - D_zF`. -/

/-! ## §1 The main theorem -/

theorem sb2_dthDV {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hD3 : ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 3,
      |Work.Spaces.DzIter j (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
        ≤ K * Work.Construction.s2 θ) :
    ∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ))) z θ| ≤ K' := by
  obtain ⟨K, hK⟩ := hD3
  -- the constant of the `D_z³`-bound is nonnegative (test at `(1, π/4)`, where `s2 = 1`)
  have hKnn : 0 ≤ K := by
    have hmem : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr
        ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have h1 := hK 1 (Real.pi / 4) hmem 0 (by norm_num)
    have h2 : Work.Construction.s2 (Real.pi / 4) = 1 := by
      rw [Work.Construction.s2_eq,
        show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
    rw [Work.Spaces.DzIter_zero, h2, mul_one] at h1
    exact le_trans (abs_nonneg _) h1
  obtain ⟨hP3, hV2, hDzC1, hpthVC1⟩ := smooth_inputs hαG h3 hslot
  refine ⟨(αG ^ 2 + 5 * αG + 6) * K + Mf, ?_⟩
  intro z θ hmem
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hnb : Work.Construction.Qd ∈ 𝓝 (z, θ) := hQd.mem_nhds hmem
  have hz : 0 < z := (Work.FTS_StreamBdry.mem_Qd.mp hmem).1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := (Work.FTS_StreamBdry.mem_Qd.mp hmem).2
  set P : ℝ → ℝ → ℝ := Work.FTS.StreamBdryIface.psiP αG Ψ with hP
  -- the smoothness facts, restated for the local abbreviation `P`
  have hP3' : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd := by
    rw [hP]; exact hP3
  have hV2' : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop P))
      Work.Construction.Qd := by
    rw [hP]; exact hV2
  have hDzC1' : ∀ j ≤ 2, ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter j P))
      Work.Construction.Qd := by
    intro j hj; rw [hP]; exact hDzC1 j hj
  have hpthVC1' : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Construction.Vop P)))
      Work.Construction.Qd := by
    rw [hP]; exact hpthVC1
  -- the elliptic law in `D`-form for `P`
  have hlaw := Work.FTS_StreamBdry.SB3.law_psiP (αG := αG) (M := M) hαG hsol h3 hslot
  -- the pointwise identity: `∂_θ D_z V(P)` equals the `z`-derivative of the law's right side
  have hident : Work.Spaces.pth (Work.Spaces.DzIter 1 (Work.Construction.Vop P)) z θ
      = -(αG ^ 2 * Work.Spaces.DzIter 3 P z θ + 5 * αG * Work.Spaces.DzIter 2 P z θ
          + 6 * Work.Spaces.DzIter 1 P z θ) - Work.Spaces.Dz F z θ := by
    -- step 1: `D_z V(P) = z · ∂_z V(P)`, so the `θ`-derivative pulls the constant `z` out
    have hstep1 : Work.Spaces.pth (Work.Spaces.DzIter 1 (Work.Construction.Vop P)) z θ
        = z * Work.Spaces.pth (Work.Spaces.pz (Work.Construction.Vop P)) z θ := by
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
        Work.Spaces.pth]
      rw [deriv_const_mul_field]
    -- step 2: Clairaut for `V(P)`, which is `C²` on `Qd`
    have hcl : Work.Spaces.pth (Work.Spaces.pz (Work.Construction.Vop P)) z θ
        = Work.Spaces.pz (Work.Spaces.pth (Work.Construction.Vop P)) z θ :=
      (Work.Spaces.pz_pth_comm (hV2'.contDiffAt hnb)).symm
    -- step 3: replace `∂_θV(P)` by the law's right-hand side (a germ identity on `Qd`)
    have hev : (fun z' => Work.Spaces.pth (Work.Construction.Vop P) z' θ)
        =ᶠ[𝓝 z] (fun z' => -(αG ^ 2 * Work.Spaces.DzIter 2 P z' θ
            + 5 * αG * Work.Spaces.DzIter 1 P z' θ + 6 * P z' θ) - F z' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      have h := hlaw z' θ ⟨hz', hθ.1, hθ.2⟩
      simpa only [hP, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h
    have hstep3 : Work.Spaces.pz (Work.Spaces.pth (Work.Construction.Vop P)) z θ
        = Work.Spaces.pz (fun z θ => -(αG ^ 2 * Work.Spaces.DzIter 2 P z θ
            + 5 * αG * Work.Spaces.DzIter 1 P z θ + 6 * P z θ) - F z θ) z θ := by
      show deriv (fun z' => Work.Spaces.pth (Work.Construction.Vop P) z' θ) z
        = deriv (fun z' => -(αG ^ 2 * Work.Spaces.DzIter 2 P z' θ
            + 5 * αG * Work.Spaces.DzIter 1 P z' θ + 6 * P z' θ) - F z' θ) z
      exact hev.deriv_eq
    -- differentiability of the four `z`-slices at `z`
    have hslice : ∀ {G : ℝ → ℝ → ℝ}, ContDiffOn ℝ 1 (Function.uncurry G)
        Work.Construction.Qd → DifferentiableAt ℝ (fun z' => G z' θ) z := fun {G} hG =>
      Work.Spaces.differentiableAt_curry_left
        ((hG.differentiableOn (by norm_num)).differentiableAt hnb)
    have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter 2 P z' θ) z :=
      hslice (hDzC1' 2 le_rfl)
    have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter 1 P z' θ) z :=
      hslice (hDzC1' 1 (by norm_num))
    have hd0 : DifferentiableAt ℝ (fun z' => P z' θ) z :=
      hslice (hDzC1' 0 (by norm_num))
    have hdVF : DifferentiableAt ℝ
        (fun z' => Work.Spaces.pth (Work.Construction.Vop P) z' θ) z := hslice hpthVC1'
    -- `F` is differentiable in `z` at `z`, by the law
    have hdF : DifferentiableAt ℝ (fun z' => F z' θ) z := by
      have hevF : (fun z' => F z' θ) =ᶠ[𝓝 z]
          (fun z' => -(αG ^ 2 * Work.Spaces.DzIter 2 P z' θ
              + 5 * αG * Work.Spaces.DzIter 1 P z' θ + 6 * P z' θ)
            - Work.Spaces.pth (Work.Construction.Vop P) z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        have h := hlaw z' θ ⟨hz', hθ.1, hθ.2⟩
        have h' : Work.Spaces.pth (Work.Construction.Vop P) z' θ
            = -(αG ^ 2 * Work.Spaces.DzIter 2 P z' θ
                + 5 * αG * Work.Spaces.DzIter 1 P z' θ + 6 * P z' θ) - F z' θ := by
          simpa only [hP, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h
        linarith
      refine hevF.differentiableAt_iff.mpr ?_
      have hS : DifferentiableAt ℝ (fun z' => αG ^ 2 * Work.Spaces.DzIter 2 P z' θ
          + 5 * αG * Work.Spaces.DzIter 1 P z' θ + 6 * P z' θ) z :=
        ((hd2.const_mul (αG ^ 2)).add (hd1.const_mul (5 * αG))).add (hd0.const_mul 6)
      exact hS.neg.sub hdVF
    -- the derivative computation
    have hmain := sb2_deriv_law_rhs (αG := αG) (P := P) (F := F) (z := z) (θ := θ)
      hd2 hd1 hd0 hdF
    calc Work.Spaces.pth (Work.Spaces.DzIter 1 (Work.Construction.Vop P)) z θ
        = z * Work.Spaces.pth (Work.Spaces.pz (Work.Construction.Vop P)) z θ := hstep1
      _ = z * Work.Spaces.pz (Work.Spaces.pth (Work.Construction.Vop P)) z θ := by rw [hcl]
      _ = z * Work.Spaces.pz (fun z θ => -(αG ^ 2 * Work.Spaces.DzIter 2 P z θ
            + 5 * αG * Work.Spaces.DzIter 1 P z θ + 6 * P z θ) - F z θ) z θ := by rw [hstep3]
      _ = -(αG ^ 2 * Work.Spaces.DzIter 3 P z θ + 5 * αG * Work.Spaces.DzIter 2 P z θ
            + 6 * Work.Spaces.DzIter 1 P z θ) - Work.Spaces.Dz F z θ := hmain
  rw [hident]
  -- the bounds
  have hs2nn : 0 ≤ Work.Construction.s2 θ := le_of_lt (Work.FTS_StreamBdry.s2_pos_of_Qd hmem)
  have hs2le : Work.Construction.s2 θ ≤ 1 := by
    rw [Work.Construction.s2_eq]
    exact Real.sin_le_one (2 * θ)
  have hs2K : K * Work.Construction.s2 θ ≤ K := by
    simpa using mul_le_mul_of_nonneg_left hs2le hKnn
  have hb3 : |Work.Spaces.DzIter 3 P z θ| ≤ K * Work.Construction.s2 θ := by
    rw [hP]; exact hK z θ hmem 3 (by norm_num)
  have hb2 : |Work.Spaces.DzIter 2 P z θ| ≤ K * Work.Construction.s2 θ := by
    rw [hP]; exact hK z θ hmem 2 (by norm_num)
  have hb1 : |Work.Spaces.DzIter 1 P z θ| ≤ K * Work.Construction.s2 θ := by
    rw [hP]; exact hK z θ hmem 1 (by norm_num)
  have hFb : |Work.Spaces.Dz F z θ| ≤ Mf :=
    Work.FTS_StreamBdry.SrcOK.Dz_le hF hz (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)
  have hA2 : (0 : ℝ) ≤ αG ^ 2 := by positivity
  have hA5 : (0 : ℝ) ≤ 5 * αG := by linarith
  have hA6 : (0 : ℝ) ≤ (6 : ℝ) := by norm_num
  have hbA : |αG ^ 2 * Work.Spaces.DzIter 3 P z θ| ≤ αG ^ 2 * (K * Work.Construction.s2 θ) := by
    rw [abs_mul, abs_of_nonneg hA2]
    exact mul_le_mul_of_nonneg_left hb3 hA2
  have hbB : |5 * αG * Work.Spaces.DzIter 2 P z θ| ≤ 5 * αG * (K * Work.Construction.s2 θ) := by
    rw [abs_mul, abs_of_nonneg hA5]
    exact mul_le_mul_of_nonneg_left hb2 hA5
  have hbC : |6 * Work.Spaces.DzIter 1 P z θ| ≤ 6 * (K * Work.Construction.s2 θ) := by
    rw [abs_mul, abs_of_nonneg hA6]
    exact mul_le_mul_of_nonneg_left hb1 hA6
  have hsum : |αG ^ 2 * Work.Spaces.DzIter 3 P z θ + 5 * αG * Work.Spaces.DzIter 2 P z θ
      + 6 * Work.Spaces.DzIter 1 P z θ| ≤ (αG ^ 2 + 5 * αG + 6) * K := by
    have h2 : |αG ^ 2 * Work.Spaces.DzIter 3 P z θ + 5 * αG * Work.Spaces.DzIter 2 P z θ|
        ≤ αG ^ 2 * (K * Work.Construction.s2 θ) + 5 * αG * (K * Work.Construction.s2 θ) :=
      (abs_add_le _ _).trans (add_le_add hbA hbB)
    have h3 : |αG ^ 2 * Work.Spaces.DzIter 3 P z θ + 5 * αG * Work.Spaces.DzIter 2 P z θ
          + 6 * Work.Spaces.DzIter 1 P z θ|
        ≤ (αG ^ 2 * (K * Work.Construction.s2 θ)
            + 5 * αG * (K * Work.Construction.s2 θ)) + 6 * (K * Work.Construction.s2 θ) :=
      (abs_add_le _ _).trans (add_le_add h2 hbC)
    refine h3.trans ?_
    have hcast : (αG ^ 2 * (K * Work.Construction.s2 θ)
        + 5 * αG * (K * Work.Construction.s2 θ)) + 6 * (K * Work.Construction.s2 θ)
        = (αG ^ 2 + 5 * αG + 6) * (K * Work.Construction.s2 θ) := by ring
    rw [hcast]
    exact mul_le_mul_of_nonneg_left hs2K (by nlinarith [hαG])
  calc |-(αG ^ 2 * Work.Spaces.DzIter 3 P z θ + 5 * αG * Work.Spaces.DzIter 2 P z θ
          + 6 * Work.Spaces.DzIter 1 P z θ) - Work.Spaces.Dz F z θ|
      = |(αG ^ 2 * Work.Spaces.DzIter 3 P z θ + 5 * αG * Work.Spaces.DzIter 2 P z θ
          + 6 * Work.Spaces.DzIter 1 P z θ) + Work.Spaces.Dz F z θ| := by
        rw [show -(αG ^ 2 * Work.Spaces.DzIter 3 P z θ + 5 * αG * Work.Spaces.DzIter 2 P z θ
              + 6 * Work.Spaces.DzIter 1 P z θ) - Work.Spaces.Dz F z θ
            = -((αG ^ 2 * Work.Spaces.DzIter 3 P z θ + 5 * αG * Work.Spaces.DzIter 2 P z θ
              + 6 * Work.Spaces.DzIter 1 P z θ) + Work.Spaces.Dz F z θ) from by ring,
          abs_neg]
    _ ≤ |αG ^ 2 * Work.Spaces.DzIter 3 P z θ + 5 * αG * Work.Spaces.DzIter 2 P z θ
          + 6 * Work.Spaces.DzIter 1 P z θ| + |Work.Spaces.Dz F z θ| := abs_add_le _ _
    _ ≤ (αG ^ 2 + 5 * αG + 6) * K + Mf := add_le_add hsum hFb

end Work.FTS_StreamBdry.SB2
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.pze_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.pze_aux` — helper lemmas for the leaf B5 (`psiP_edge_zero`)

Elementary one-variable bounds, filter (squeezing) lemmas along `𝓝[Qd] (z₀,0)`, smoothness of
`θ ↦ tan θ` / of `Vop` / of `pz` on the open quadrant, congruence of partial derivatives on an open
set, and the two second-derivative identities
`∂_z²P = (D_z²P - D_zP)/z²`, `∂_θ²P = ∂_θ(V P) + (1/cos²θ + tan²θ)P + tan θ·(V P)`.
-/


noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


/-! ## §1 Elementary one-variable bounds -/

/-- `|tan θ| ≤ 2θ` on `[0, 1/2]` (from `cos θ ≥ 1 - θ²/2 ≥ 7/8` and `sin θ ≤ θ`). -/
lemma pze_tan_abs_le_two_mul {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    |Real.tan θ| ≤ 2 * θ := by
  rcases lt_or_eq_of_le h0 with hlt | heq
  · have hcos : (7 : ℝ) / 8 ≤ Real.cos θ := by
      have hx := Real.one_sub_sq_div_two_le_cos (x := θ)
      have h2 : θ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
      linarith
    have hcospos : 0 < Real.cos θ := by linarith
    have htanpos : 0 < Real.tan θ :=
      Real.tan_pos_of_pos_of_lt_pi_div_two hlt (by linarith [h1, Real.pi_gt_three])
    rw [abs_of_pos htanpos, Real.tan_eq_sin_div_cos, div_le_iff₀ hcospos]
    have hsin : Real.sin θ ≤ θ := Real.sin_le h0
    have hc1 : (1 : ℝ) ≤ 2 * Real.cos θ := by linarith
    have hθ2 : θ ≤ 2 * θ * Real.cos θ := by
      calc θ = θ * 1 := by ring
        _ ≤ θ * (2 * Real.cos θ) := mul_le_mul_of_nonneg_left hc1 h0
        _ = 2 * θ * Real.cos θ := by ring
    linarith
  · subst heq; simp

/-- `1/cos²θ ≤ 2` on `[0, 1/2]`. -/
lemma pze_one_div_cos_sq_le_two {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    1 / Real.cos θ ^ 2 ≤ 2 := by
  have hcos : (7 : ℝ) / 8 ≤ Real.cos θ := by
    have hx := Real.one_sub_sq_div_two_le_cos (x := θ)
    have h2 : θ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
    linarith
  have hsq : ((7 : ℝ) / 8) ^ 2 ≤ Real.cos θ ^ 2 := by nlinarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.cos θ ^ 2)]
  nlinarith

/-- `tan²θ ≤ 1` on `[0, 1/2]`. -/
lemma pze_tan_sq_le_one {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    Real.tan θ ^ 2 ≤ 1 := by
  have h := pze_tan_abs_le_two_mul h0 h1
  have h2 : (2 * θ) ^ 2 ≤ 1 := by nlinarith
  nlinarith [abs_nonneg (Real.tan θ), sq_abs (Real.tan θ)]

/-- The coefficient `1/cos²θ + tan²θ` is bounded by `3` on `[0, 1/2]`. -/
lemma pze_one_div_cos_sq_add_tan_sq_abs_le_three {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    |1 / Real.cos θ ^ 2 + Real.tan θ ^ 2| ≤ 3 := by
  have ha := pze_one_div_cos_sq_le_two h0 h1
  have hb := pze_tan_sq_le_one h0 h1
  have hc : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [abs_of_nonneg (by positivity)]
  linarith


/-! ## §2 Filters: squeezing along `𝓝[Qd] (z₀,0)` -/

/-- A function eventually bounded by `u(θ)` with `u` continuous and `u 0 = 0` tends to `0`. -/
lemma pze_tendsto_zero_of_eventually_le {g : ℝ × ℝ → ℝ} {z0 : ℝ} {u : ℝ → ℝ}
    (hu : Continuous u) (hu0 : u 0 = 0)
    (h : ∀ᶠ p in 𝓝[Work.Construction.Qd] (z0, 0), |g p| ≤ u p.2) :
    Filter.Tendsto g (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
  have hcont : Continuous fun p : ℝ × ℝ => u p.2 := hu.comp continuous_snd
  have h1 : Filter.Tendsto (fun p : ℝ × ℝ => u p.2)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    have h2 := hcont.tendsto (z0, 0)
    have h3 : Filter.Tendsto (fun p : ℝ × ℝ => u p.2)
        (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (u 0)) := h2.mono_left nhdsWithin_le_nhds
    simpa [hu0] using h3
  have h4 : Filter.Tendsto (fun p : ℝ × ℝ => |g p|)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun p => abs_nonneg _) h h1
  have h5 : Filter.Tendsto (fun p : ℝ × ℝ => ‖g p - 0‖)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    simpa only [sub_zero, Real.norm_eq_abs] using h4
  exact tendsto_iff_norm_sub_tendsto_zero.mpr h5

/-- A function agreeing with a continuous `c` up to `u(θ)` (with `u` continuous, `u 0 = 0`) tends
to the value of `c` at the corner point. -/
lemma pze_tendsto_of_eventually_le_add {g c : ℝ × ℝ → ℝ} {z0 : ℝ} {u : ℝ → ℝ}
    (hz0 : 0 < z0)
    (hc : ContinuousOn c (Ioi 0 ×ˢ (Set.univ : Set ℝ)))
    (hu : Continuous u) (hu0 : u 0 = 0)
    (h : ∀ᶠ p in 𝓝[Work.Construction.Qd] (z0, 0), |g p - c p| ≤ u p.2) :
    Filter.Tendsto g (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (c (z0, 0))) := by
  have hmem : (Ioi 0 ×ˢ (Set.univ : Set ℝ)) ∈ 𝓝 ((z0, 0) : ℝ × ℝ) :=
    (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hz0, trivial⟩
  have hct : Filter.Tendsto c (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (c (z0, 0))) :=
    (hc.continuousAt hmem).tendsto.mono_left nhdsWithin_le_nhds
  have hzero : Filter.Tendsto (fun p : ℝ × ℝ => g p - c p)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) :=
    pze_tendsto_zero_of_eventually_le hu hu0 h
  have hsum : Filter.Tendsto (fun p : ℝ × ℝ => c p + (g p - c p))
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (c (z0, 0))) := by
    simpa using hct.add hzero
  exact hsum.congr (fun p => by ring)

/-- A pointwise fact on the quadrant is eventually true along `𝓝[Qd] (z₀,0)`. -/
lemma pze_eventually_of_mem_Qd {z0 : ℝ} {p : ℝ × ℝ → Prop}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → p (z, θ)) :
    ∀ᶠ q in 𝓝[Work.Construction.Qd] (z0, 0), p q :=
  Eventually.mono self_mem_nhdsWithin fun q hq => h q.1 q.2 hq

/-- Eventually, the second coordinate is `< c` for any `c > 0`. -/
lemma pze_eventually_snd_lt {z0 c : ℝ} (hc : 0 < c) :
    ∀ᶠ p : ℝ × ℝ in 𝓝[Work.Construction.Qd] (z0, 0), p.2 < c := by
  have h : Iio c ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds hc
  exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
    ((continuous_snd.continuousAt (x := (z0, 0))).preimage_mem_nhds h)

/-- Eventually, the first coordinate exceeds `z₀/2`. -/
lemma pze_eventually_fst_gt {z0 : ℝ} (hz0 : 0 < z0) :
    ∀ᶠ p : ℝ × ℝ in 𝓝[Work.Construction.Qd] (z0, 0), z0 / 2 < p.1 := by
  have hmem : (z0 : ℝ) ∈ Ioi (z0 / 2) := by show z0 / 2 < z0; linarith
  have h : Ioi (z0 / 2) ∈ 𝓝 z0 := isOpen_Ioi.mem_nhds hmem
  exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
    ((continuous_fst.continuousAt (x := (z0, 0))).preimage_mem_nhds h)

/-! ## §2b Coordinate facts at a point of the quadrant -/

/-- At a point of the quadrant the first coordinate is positive. -/
lemma pze_pos_fst {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) : 0 < p.1 := (mem_Qd.mp hp).1

/-- At a point of the quadrant the second coordinate is positive. -/
lemma pze_pos_snd {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) : 0 < p.2 := (mem_Qd.mp hp).2.1

/-- At a point of the quadrant the second coordinate is `< π/2`. -/
lemma pze_snd_lt {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) : p.2 < π / 2 :=
  (mem_Qd.mp hp).2.2

/-- At a point of the quadrant the second coordinate lies in `(0,π/2)`. -/
lemma pze_theta_mem {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) : p.2 ∈ Ioo (0 : ℝ) (π / 2) :=
  ⟨pze_pos_snd hp, pze_snd_lt hp⟩

/-- At a point of the quadrant the second coordinate lies in the closed strip `Iθ`. -/
lemma pze_theta_Iθ {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) : p.2 ∈ Work.Spaces.Iθ :=
  ⟨le_of_lt (pze_pos_snd hp), le_of_lt (pze_snd_lt hp)⟩

/-- `s2 = sin 2θ` is positive on the quadrant. -/
lemma pze_s2_pos {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) :
    0 < Work.Construction.s2 p.2 :=
  s2_pos_of_Ioo (pze_theta_mem hp)

/-- `s2 = sin 2θ` is nonnegative on the quadrant. -/
lemma pze_s2_nonneg {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) :
    0 ≤ Work.Construction.s2 p.2 := le_of_lt (pze_s2_pos hp)

/-- `cos θ` is positive on the quadrant. -/
lemma pze_cos_pos {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) : 0 < Real.cos p.2 :=
  cos_pos_of_Ioo (pze_theta_mem hp)

/-! ## §3 Smoothness on the quadrant -/

/-- `θ ↦ tan θ` is `C^n` on the open quadrant. -/
lemma pze_contDiffOn_tan_Qd {n : ℕ} :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.tan p.2) Work.Construction.Qd := by
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2) Work.Construction.Qd :=
    Real.contDiff_sin.comp_contDiffOn contDiff_snd.contDiffOn
  have hcos : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.cos p.2) Work.Construction.Qd :=
    Real.contDiff_cos.comp_contDiffOn contDiff_snd.contDiffOn
  refine (hsin.div hcos (fun p hp => ne_of_gt (cos_pos_of_Qd hp))).congr (fun p _ => ?_)
  exact Real.tan_eq_sin_div_cos p.2

/-- The `z`-partial of a `C²` function on the quadrant is `C¹`. -/
lemma pze_contDiffOn_uncurry_pz_Qd {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 2 (Function.uncurry G) Work.Construction.Qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz G)) Work.Construction.Qd :=
  Work.FTS_StreamBdry.SB3.psiP_D3_aux_pz_smooth Work.FTS_StreamBdry.SB1.isOpen_Qd
    (n := 1) h

/-- `Vop` of a `C³` function on the quadrant is `C²`. -/
lemma pze_contDiffOn_uncurry_Vop_Qd {Ψ : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop Ψ)) Work.Construction.Qd := by
  have hpth : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.contDiffOn_uncurry_pth_qd (n := 2) h
  have h2 : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd := h.of_le (by norm_num)
  refine (hpth.sub ((pze_contDiffOn_tan_Qd (n := 2)).mul h2)).congr (fun p _ => ?_)
  simp only [Function.uncurry, Work.Construction.Vop]

/-! ## §4 Congruence of partial derivatives on the quadrant -/

/-- Partial `z`-derivatives agree for functions agreeing on an open set. -/
lemma pze_pz_congr_of_isOpen {f g : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ∀ p ∈ U, f p.1 p.2 = g p.1 p.2) {z θ : ℝ} (hmem : (z, θ) ∈ U) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hev : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) := by
    filter_upwards [(continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => θ)).continuousAt.preimage_mem_nhds
      (hU.mem_nhds hmem)] with z' hz'
    exact h (z', θ) hz'
  exact hev.deriv_eq

/-- Partial `θ`-derivatives agree for functions agreeing on an open set. -/
lemma pze_pth_congr_of_isOpen {f g : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ∀ p ∈ U, f p.1 p.2 = g p.1 p.2) {z θ : ℝ} (hmem : (z, θ) ∈ U) :
    Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') := by
    filter_upwards [((continuous_const : Continuous fun _ : ℝ => z).prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hU.mem_nhds hmem)] with θ' hθ'
    exact h (z, θ') hθ'
  exact hev.deriv_eq

/-! ## §5 The two second-derivative identities -/

/-- `∂_z²P = (D_z²P - D_zP)/z²` on the quadrant, from the product rule. -/
lemma pze_pz_pz_eq {P : ℝ → ℝ → ℝ}
    (hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {z θ : ℝ} (hmem : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.pz (Work.Spaces.pz P) z θ
      = (Work.Spaces.DzIter 2 P z θ - Work.Spaces.DzIter 1 P z θ) / z ^ 2 := by
  have hz : z ≠ 0 := ne_of_gt (Qd_pos hmem)
  have hQd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz P)) Work.Construction.Qd :=
    pze_contDiffOn_uncurry_pz_Qd hP2
  have hpzdiff : DifferentiableAt ℝ (fun z' => Work.Spaces.pz P z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hpz1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem))
  have h2 : Work.Spaces.pz (Work.Spaces.DzIter 1 P) z θ
      = Work.Spaces.pz P z θ + z * Work.Spaces.pz (Work.Spaces.pz P) z θ := by
    show deriv (fun z' => Work.Spaces.DzIter 1 P z' θ) z = _
    have hev : (fun z' => Work.Spaces.DzIter 1 P z' θ)
        = fun z' => z' * Work.Spaces.pz P z' θ := by
      funext z'; rfl
    have hdm : deriv (fun z' => z' * Work.Spaces.pz P z' θ) z
        = deriv (fun z' : ℝ => z') z * Work.Spaces.pz P z θ
          + z * deriv (fun z' => Work.Spaces.pz P z' θ) z :=
      deriv_mul differentiableAt_id hpzdiff
    rw [hev, hdm, deriv_id'']
    simp only [one_mul]
    rfl
  have hmain : Work.Spaces.DzIter 2 P z θ
      = z * Work.Spaces.pz P z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz P) z θ := by
    show z * Work.Spaces.pz (Work.Spaces.DzIter 1 P) z θ = _
    rw [h2]; ring
  have h1 : Work.Spaces.DzIter 1 P z θ = z * Work.Spaces.pz P z θ := rfl
  rw [hmain, h1, eq_div_iff (pow_ne_zero 2 hz)]
  ring

/-- The `θ`-derivative split `∂_θ²P = ∂_θ(V P) + (1/cos²θ + tan²θ)·P + tan θ·(V P)`. -/
lemma pze_pth_pth_eq {P : ℝ → ℝ → ℝ}
    (hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {z θ : ℝ} (hmem : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.pth (Work.Spaces.pth P) z θ
      = Work.Spaces.pth (Work.Construction.Vop P) z θ
        + (1 / Real.cos θ ^ 2 + Real.tan θ ^ 2) * P z θ
        + Real.tan θ * Work.Construction.Vop P z θ := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (cos_pos_of_Qd hmem)
  have hQd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hPdiff : DifferentiableAt ℝ (fun θ' => P z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem))
  have hpth1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth P)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.contDiffOn_uncurry_pth_qd (n := 1) hP2
  have hpthdiff : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth P z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpth1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem))
  have htan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  have hd2 : DifferentiableAt ℝ (fun θ' => Real.tan θ' * P z θ') θ := htan.mul hPdiff
  have hd1 : DifferentiableAt ℝ (fun θ' => Work.Construction.Vop P z θ') θ := by
    have h := hpthdiff.sub hd2
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun θ' => ?_))
    show Work.Construction.Vop P z θ' = Work.Spaces.pth P z θ' - Real.tan θ' * P z θ'
    simp only [Work.Construction.Vop]
  have hstep : Work.Spaces.pth (Work.Spaces.pth P) z θ
      = deriv (fun θ' => Work.Construction.Vop P z θ' + Real.tan θ' * P z θ') θ := by
    show deriv (fun θ' => Work.Spaces.pth P z θ') θ = _
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards with θ'
    show Work.Spaces.pth P z θ' = Work.Construction.Vop P z θ' + Real.tan θ' * P z θ'
    rw [Work.Construction.Vop]; ring
  have hstep2 : deriv (fun θ' => Work.Construction.Vop P z θ' + Real.tan θ' * P z θ') θ
      = deriv (fun θ' => Work.Construction.Vop P z θ') θ
        + deriv (fun θ' => Real.tan θ' * P z θ') θ :=
    deriv_add hd1 hd2
  rw [hstep, hstep2]
  have hmul : deriv (fun θ' => Real.tan θ' * P z θ') θ
      = 1 / Real.cos θ ^ 2 * P z θ + Real.tan θ * Work.Spaces.pth P z θ := by
    have hdm : deriv (fun θ' => Real.tan θ' * P z θ') θ
        = deriv Real.tan θ * P z θ + Real.tan θ * deriv (fun θ' => P z θ') θ :=
      deriv_mul htan hPdiff
    rw [hdm, Real.deriv_tan]
    rfl
  rw [hmul]
  have hpthV : Work.Spaces.pth P z θ
      = Work.Construction.Vop P z θ + Real.tan θ * P z θ := by
    rw [Work.Construction.Vop]; ring
  rw [hpthV]
  have hdv : deriv (fun θ' => Work.Construction.Vop P z θ') θ
      = Work.Spaces.pth (Work.Construction.Vop P) z θ := rfl
  rw [hdv]
  ring


end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.sb5_compare =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.sb5_compare` — leaf E4c of the SB2/SB5 plan

The comparison half of the FIX-SB5 barrier: for `Q` of class `C²` on the open quadrant `Qd`,
`bslOp α Q = 0` above the line `z = L`, `|Q| ≤ Mb·sin 2θ` on the half-strip `z ≥ L` and
`|Q| ≤ ε·sin 2θ` beyond some radius (uniformly in `θ`),

`|Q z θ| ≤ Mb · sin 2θ · (L/z)^k`  for `L ≤ z`, `θ ∈ (0, π/2)`.

The proof is a Phragmén--Lindelöf comparison for the ground-state operator
`Lgs α u = bslOp α (s2·u)/s2` (`bslOp_split`).  Writing `u = Q/sin 2θ` and fixing a point
`(z₁,θ₁)`, the barrier `w = (Mb + ρ + δφ θ)(z/L)^{-k} + σ` (with `φ ≥ 0` blowing up at both
ends and `𝓐φ` bounded below, from `SB5Barrier`) is a strict supersolution of `Lgs`
(`Lgs_barrier`), dominates `u` on the boundary of a bounded rectangle and is `C²` on it
(`Sb5CmpAux`); hence `u - w ≤ 0` there by the maximum principle `Lgs_le_zero_of_max`.  Letting
`δ → 0`, then `ρ, σ → 0`, gives `u z₁ θ₁ ≤ Mb (L/z₁)^k`; the same argument for `-u` gives the
absolute value, and a final division by `sin 2θ` the claim for `Q`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem sb5_compare (α k L Mb : ℝ) (Q : ℝ → ℝ → ℝ) :
    Work.FTS_StreamBdry.SB25.Sb5Compare α k L Mb Q := by
  intro hα hL hαk hαk5 hBar hQc2 hbsl hbd hdec
  intro z₁ θ₁ hz₁ hθ₁
  by_cases hMb : Mb < 0
  · exfalso
    have h1 := hbd z₁ θ₁ hz₁ hθ₁
    have h2 : 0 < Work.Construction.s2 θ₁ := sb5c_s2_pos_of_Ioo hθ₁
    have h3 : Mb * Work.Construction.s2 θ₁ < 0 := mul_neg_of_neg_of_pos hMb h2
    linarith [abs_nonneg (Q z₁ θ₁)]
  · have hMb0 : 0 ≤ Mb := not_lt.mp hMb
    obtain ⟨φ, Cφ, hφ2, hφ0, hφtop0, hφtopπ, hφA⟩ := hBar
    have hφe0 : ∀ B : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ θ : ℝ, 0 < θ → θ < ε → B ≤ φ θ := by
      intro B
      have h : ∀ᶠ θ in 𝓝[>] (0 : ℝ), B ≤ φ θ := hφtop0.eventually (eventually_ge_atTop B)
      rw [eventually_nhdsWithin_iff] at h
      have hmem : {x : ℝ | x ∈ Set.Ioi 0 → B ≤ φ x} ∈ 𝓝 (0 : ℝ) := h
      rw [Metric.mem_nhds_iff] at hmem
      obtain ⟨ε, hεpos, hε⟩ := hmem
      refine ⟨ε, hεpos, fun θ hθ0 hθε => ?_⟩
      have hmem : θ ∈ Metric.ball (0 : ℝ) ε := by
        rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, sub_zero, abs_lt]
        exact ⟨by linarith, hθε⟩
      exact hε hmem hθ0
    have hφeπ : ∀ B : ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ θ : ℝ, Real.pi / 2 - ε < θ → θ < Real.pi / 2 → B ≤ φ θ := by
      intro B
      have h : ∀ᶠ θ in 𝓝[<] (Real.pi / 2), B ≤ φ θ := hφtopπ.eventually (eventually_ge_atTop B)
      rw [eventually_nhdsWithin_iff] at h
      have hmem : {x : ℝ | x ∈ Set.Iio (Real.pi / 2) → B ≤ φ x} ∈ 𝓝 (Real.pi / 2) := h
      rw [Metric.mem_nhds_iff] at hmem
      obtain ⟨ε, hεpos, hε⟩ := hmem
      refine ⟨ε, hεpos, fun θ hθ0 hθ1 => ?_⟩
      have hmem : θ ∈ Metric.ball (Real.pi / 2) ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith, by linarith⟩
      exact hε hmem hθ1
    have huC2 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Q z θ / Work.Construction.s2 θ))
        Work.Construction.Qd := by
      have hs : ContDiff ℝ 2 (fun t : ℝ => Work.Construction.s2 t) := by
        change ContDiff ℝ 2 (fun t : ℝ => Real.sin (2 * t))
        fun_prop
      have h2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Work.Construction.s2 p.2)
          Work.Construction.Qd := hs.comp_contDiffOn contDiffOn_snd
      have h3 : ∀ p ∈ Work.Construction.Qd, Work.Construction.s2 p.2 ≠ 0 := by
        intro p hp
        rw [Work.Construction.Qd] at hp
        exact ne_of_gt (sb5c_s2_pos_of_Ioo hp.2)
      have h4 := hQc2.div h2 h3
      have h5 : Function.uncurry (fun z θ => Q z θ / Work.Construction.s2 θ)
          = Function.uncurry Q / (fun p : ℝ × ℝ => Work.Construction.s2 p.2) := by
        funext p; rfl
      rw [h5]
      exact h4
    have huLgs : ∀ z θ, L < z → θ ∈ Ioo 0 (Real.pi / 2) →
        Lgs α (fun z θ => Q z θ / Work.Construction.s2 θ) z θ = 0 := by
      intro z θ hz hθ
      have hzpos : 0 < z := lt_trans hL hz
      have hQd : (z, θ) ∈ Work.Construction.Qd := by
        rw [Work.Construction.Qd]; exact Set.mem_prod.mpr ⟨hzpos, hθ⟩
      have hsplit := bslOp_split α Q hQd (hQc2.contDiffAt (sb5c_Qd_mem_nhds hQd))
      have hz0 : Work.Elliptic.bslOp α Q z θ = 0 := hbsl z θ hz hθ
      have hs2 : Work.Construction.s2 θ ≠ 0 := ne_of_gt (sb5c_s2_pos_of_Ioo hθ)
      have key : Work.Construction.s2 θ *
          Lgs α (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ = 0 := by
        rw [← hsplit, hz0]
      exact (mul_eq_zero.mp key).resolve_left hs2
    have huMb : ∀ z θ, L ≤ z → θ ∈ Ioo 0 (Real.pi / 2) →
        |(fun z θ => Q z θ / Work.Construction.s2 θ) z θ| ≤ Mb := by
      intro z θ hz hθ
      have hs2 : 0 < Work.Construction.s2 θ := sb5c_s2_pos_of_Ioo hθ
      have h := hbd z θ hz hθ
      rw [abs_div, abs_of_pos hs2, div_le_iff₀ hs2]
      exact h
    have huDec : ∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Ioo 0 (Real.pi / 2) →
        |(fun z θ => Q z θ / Work.Construction.s2 θ) z θ| ≤ ε := by
      intro ε hε
      obtain ⟨R, hR⟩ := hdec ε hε
      refine ⟨R, fun z θ hz hθ => ?_⟩
      have hs2 : 0 < Work.Construction.s2 θ := sb5c_s2_pos_of_Ioo hθ
      have h := hR z θ hz hθ
      rw [abs_div, abs_of_pos hs2, div_le_iff₀ hs2]
      exact h
    have huP : (fun z θ => Q z θ / Work.Construction.s2 θ) z₁ θ₁ ≤ Mb * (L / z₁) ^ k := by
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have h := sb5c_core_le α k L Mb φ Cφ (fun z θ => Q z θ / Work.Construction.s2 θ)
        hα hαk hαk5 hL hMb0 hφ2 hφ0 hφe0 hφeπ hφA huC2 huLgs huMb huDec hz₁ hθ₁
        (ε / 4) (ε / 4) (by linarith) (by linarith)
      simp only [] at h ⊢
      linarith
    have hnuC2 : ContDiffOn ℝ 2
        (Function.uncurry (fun z θ => -(Q z θ / Work.Construction.s2 θ)))
        Work.Construction.Qd := by
      have h5 : (Function.uncurry (fun z θ => -(Q z θ / Work.Construction.s2 θ)))
          = -(Function.uncurry (fun z θ => Q z θ / Work.Construction.s2 θ)) := by
        funext p; rfl
      rw [h5]
      exact huC2.neg
    have hnuLgs : ∀ z θ, L < z → θ ∈ Ioo 0 (Real.pi / 2) →
        Lgs α (fun z θ => -(Q z θ / Work.Construction.s2 θ)) z θ = 0 := by
      intro z θ hz hθ
      have h := congrFun (congrFun
        (sb5c_Lgs_neg α (fun z θ => Q z θ / Work.Construction.s2 θ)) z) θ
      rw [h, huLgs z θ hz hθ]
      ring
    have hnuMb : ∀ z θ, L ≤ z → θ ∈ Ioo 0 (Real.pi / 2) →
        |(fun z θ => -(Q z θ / Work.Construction.s2 θ)) z θ| ≤ Mb := by
      intro z θ hz hθ
      simpa using huMb z θ hz hθ
    have hnuDec : ∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Ioo 0 (Real.pi / 2) →
        |(fun z θ => -(Q z θ / Work.Construction.s2 θ)) z θ| ≤ ε := by
      intro ε hε
      obtain ⟨R, hR⟩ := huDec ε hε
      refine ⟨R, fun z θ hz hθ => ?_⟩
      simpa using hR z θ hz hθ
    have huN : -(Q z₁ θ₁ / Work.Construction.s2 θ₁) ≤ Mb * (L / z₁) ^ k := by
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have h := sb5c_core_le α k L Mb φ Cφ (fun z θ => -(Q z θ / Work.Construction.s2 θ))
        hα hαk hαk5 hL hMb0 hφ2 hφ0 hφe0 hφeπ hφA hnuC2 hnuLgs hnuMb hnuDec hz₁ hθ₁
        (ε / 4) (ε / 4) (by linarith) (by linarith)
      try simp only [] at h
      linarith
    have hs2 : 0 < Work.Construction.s2 θ₁ := sb5c_s2_pos_of_Ioo hθ₁
    have habs : |Q z₁ θ₁ / Work.Construction.s2 θ₁| ≤ Mb * (L / z₁) ^ k :=
      abs_le.mpr ⟨by linarith, huP⟩
    calc |Q z₁ θ₁| = |Q z₁ θ₁ / Work.Construction.s2 θ₁| * Work.Construction.s2 θ₁ := by
          rw [abs_div, abs_of_pos hs2, div_mul_cancel₀ _ (ne_of_gt hs2)]
      _ ≤ Mb * (L / z₁) ^ k * Work.Construction.s2 θ₁ :=
          mul_le_mul_of_nonneg_right habs (le_of_lt hs2)
      _ = Mb * Work.Construction.s2 θ₁ * (L / z₁) ^ k := by ring


end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux4.EdgeAxisAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux4.EdgeAxisAux` — helpers for the `θ = π/2` edge limits of `psiP`

Elementary lemmas shared by the three parts of `psiP_edge_axis_aux`:

* `s2_le_two_sub` (`sin 2θ ≤ 2(π/2 - θ)` on `(0, π/2)`);
* the squeezing helpers `tendsto_nhdsWithin_of_abs_le`, `eventually_nhdsWithin_Qd`, and the
  three `Tendsto`-of-majorant lemmas;
* the mean-value rate lemma `rate_of_deriv_le`;
* the differential identities `pz_pth_eq` (`∂_z∂_θP = ∂_z(V(P)) + tan θ ∂_zP`),
  `DzIter_two_eq` (`D_z²P = z∂_zP + z²∂_z²P`) and `pth_pz_eq`
  (`∂_θ∂_zP = (D_z(V(P)) + tan θ·D_zP)/z`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux4

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

/-- `sin 2θ ≤ 2(π/2 - θ)` on `(0, π/2)`. -/
lemma s2_le_two_sub {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Construction.s2 θ ≤ 2 * (Real.pi / 2 - θ) := by
  rw [Work.FTS_StreamBdry.s2_eq_two_sin_cos]
  have hcos : 0 < Real.cos θ := Work.FTS_StreamBdry.cos_pos_of_Ioo hθ
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h1 : 2 * Real.sin θ * Real.cos θ ≤ 2 * Real.cos θ := by nlinarith
  have h2 : Real.cos θ = Real.sin (Real.pi / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
  have h3 : Real.sin (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := Real.sin_le (by linarith [hθ.2])
  linarith

/-- Squeezing inside the open quadrant. -/
lemma tendsto_nhdsWithin_of_abs_le {f : ℝ → ℝ → ℝ} {x : ℝ × ℝ} {L : ℝ} {g : ℝ × ℝ → ℝ}
    (hg : Tendsto g (𝓝 x) (𝓝 0))
    (h : ∀ᶠ p in 𝓝[Work.Construction.Qd] x, |Function.uncurry f p - L| ≤ g p) :
    Tendsto (Function.uncurry f) (𝓝[Work.Construction.Qd] x) (𝓝 L) := by
  have h1 : Tendsto (fun p : ℝ × ℝ => Function.uncurry f p - L)
      (𝓝[Work.Construction.Qd] x) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun p => abs_nonneg _) ?_
      (hg.mono_left nhdsWithin_le_nhds)
    filter_upwards [h] with p hp
    simpa [Real.norm_eq_abs] using hp
  have h3 := h1.add (tendsto_const_nhds :
    Tendsto (fun _ : ℝ × ℝ => L) (𝓝[Work.Construction.Qd] x) (𝓝 L))
  rw [zero_add] at h3
  simpa [sub_add_cancel] using h3

/-- A pointwise bound valid on `Qd` gives an eventual bound within `Qd`. -/
lemma eventually_nhdsWithin_Qd {φ : ℝ × ℝ → Prop} {x : ℝ × ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → φ (z, θ)) :
    ∀ᶠ p in 𝓝[Work.Construction.Qd] x, φ p :=
  eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun p hp => h p.1 p.2 hp)

/-- `Prod.fst` tends to `a` at `(a, b)` (with `𝓝 (a,b)` rather than `𝓝 a ×ˢ 𝓝 b`). -/
lemma tendsto_fst' {a b : ℝ} : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝 (a, b)) (𝓝 a) := by
  rw [nhds_prod_eq]; exact tendsto_fst

/-- The majorant `c * (π/2 - p.2)` tends to `0` at `(z₀, π/2)`. -/
lemma tendsto_const_mul_sub_snd_zero (c z0 : ℝ) :
    Tendsto (fun p : ℝ × ℝ => c * (Real.pi / 2 - p.2)) (𝓝 (z0, Real.pi / 2)) (𝓝 0) := by
  rw [nhds_prod_eq]
  have key : Tendsto (fun p : ℝ × ℝ => c * (Real.pi / 2 - p.2)) (𝓝 z0 ×ˢ 𝓝 (Real.pi / 2))
      (𝓝 (c * (Real.pi / 2 - Real.pi / 2))) :=
    tendsto_const_nhds.mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ × ℝ => Real.pi / 2)
          (𝓝 z0 ×ˢ 𝓝 (Real.pi / 2)) (𝓝 (Real.pi / 2))).sub
        (tendsto_snd : Tendsto (fun p : ℝ × ℝ => p.2) (𝓝 z0 ×ˢ 𝓝 (Real.pi / 2))
          (𝓝 (Real.pi / 2))))
  simpa using key

/-- The one-dimensional analogue: `c * (a - t) → 0` at `a`. -/
lemma tendsto_const_mul_sub_zero (c a : ℝ) :
    Tendsto (fun t : ℝ => c * (a - t)) (𝓝 a) (𝓝 0) := by
  have key : Tendsto (fun t : ℝ => c * (a - t)) (𝓝 a) (𝓝 (c * (a - a))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub tendsto_id)
  simpa using key

/-- `|h p.1 - h z₀| → 0` at `(z₀, π/2)` when `h` is continuous at `z₀`. -/
lemma tendsto_abs_sub_const {h : ℝ → ℝ} {z0 : ℝ} (hh : ContinuousAt h z0) :
    Tendsto (fun p : ℝ × ℝ => |h p.1 - h z0|) (𝓝 (z0, Real.pi / 2)) (𝓝 0) := by
  rw [nhds_prod_eq]
  have h1 : Tendsto (fun p : ℝ × ℝ => h p.1 - h z0) (𝓝 z0 ×ˢ 𝓝 (Real.pi / 2)) (𝓝 0) := by
    have h2 := (hh.tendsto.comp (tendsto_fst : Tendsto (fun p : ℝ × ℝ => p.1)
      (𝓝 z0 ×ˢ 𝓝 (Real.pi / 2)) (𝓝 z0))).sub_const (h z0)
    simpa using h2
  simpa using h1.abs

/-- The mean-value rate lemma: if `|g'| ≤ ε` near `π/2` and `g → v₀` at `π/2`, then
`|g t - v₀| ≤ ε(π/2 - t)` on `[θ₀, π/2)`. -/
lemma rate_of_deriv_le {g : ℝ → ℝ} {θ0 v0 ε : ℝ} (hθ0 : θ0 ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hε : 0 ≤ ε)
    (hd : ∀ t ∈ Ico θ0 (Real.pi / 2), DifferentiableAt ℝ g t)
    (hbd : ∀ t ∈ Ioo θ0 (Real.pi / 2), |deriv g t| ≤ ε)
    (hlim : Tendsto g (𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2)) (𝓝 v0)) :
    ∀ t ∈ Ico θ0 (Real.pi / 2), |g t - v0| ≤ ε * (Real.pi / 2 - t) := by
  have hmid : ∀ t ∈ Ioo θ0 (Real.pi / 2), |g t - v0| ≤ ε * (Real.pi / 2 - t) := by
    intro t ht
    have hmain : ∀ t' ∈ Ioo t (Real.pi / 2), |g t' - g t| ≤ ε * (t' - t) := by
      intro t' ht'
      have hkey := (convex_Ioo θ0 (Real.pi / 2)).norm_image_sub_le_of_norm_deriv_le
        (f := g) (C := ε)
        (fun x hx => hd x ⟨le_of_lt hx.1, hx.2⟩)
        (fun x hx => by rw [Real.norm_eq_abs]; exact hbd x hx) ht ⟨lt_trans ht.1 ht'.1, ht'.2⟩
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hkey
      rw [abs_of_pos (by linarith [ht'.1] : (0 : ℝ) < t' - t)] at hkey
      exact hkey
    have h1 : Tendsto (fun t' => |g t' - g t|) (𝓝[Iio (Real.pi / 2)] (Real.pi / 2))
        (𝓝 |v0 - g t|) := (hlim.sub_const (g t)).abs
    have hb : ∀ᶠ t' in 𝓝[Iio (Real.pi / 2)] (Real.pi / 2),
        |g t' - g t| ≤ ε * (Real.pi / 2 - t) := by
      have hlt : ∀ᶠ t' in 𝓝[Iio (Real.pi / 2)] (Real.pi / 2), t < t' :=
        (eventually_gt_nhds ht.2).filter_mono nhdsWithin_le_nhds
      filter_upwards [hlt, self_mem_nhdsWithin] with t' h1' h2'
      have h2'' : t' < Real.pi / 2 := h2'
      exact le_trans (hmain t' ⟨h1', h2''⟩)
        (mul_le_mul_of_nonneg_left (by linarith) hε)
    haveI : (𝓝[Iio (Real.pi / 2)] (Real.pi / 2)).NeBot := nhdsWithin_Iio_neBot le_rfl
    have := le_of_tendsto h1 hb
    rwa [abs_sub_comm] at this
  intro t ht
  rcases lt_or_eq_of_le ht.1 with hlt | heq
  · exact hmid t ⟨hlt, ht.2⟩
  · subst heq
    have h1 : Tendsto (fun t' => |g t' - v0|) (𝓝[Ioi θ0] θ0) (𝓝 |g θ0 - v0|) :=
      (((hd θ0 ⟨le_refl θ0, hθ0.2⟩).continuousAt.tendsto).mono_left
        (nhdsWithin_le_nhds)).sub_const v0 |>.abs
    have hb : ∀ᶠ t' in 𝓝[Ioi θ0] θ0, |g t' - v0| ≤ ε * (Real.pi / 2 - θ0) := by
      have hlt : ∀ᶠ t' in 𝓝[Ioi θ0] θ0, t' < Real.pi / 2 :=
        (eventually_lt_nhds hθ0.2).filter_mono nhdsWithin_le_nhds
      filter_upwards [hlt, self_mem_nhdsWithin] with t' h1' h2'
      have h1'' : t' < Real.pi / 2 := h1'
      have h2'' : θ0 < t' := h2'
      exact le_trans (hmid t' ⟨h2'', h1''⟩)
        (mul_le_mul_of_nonneg_left (by linarith) hε)
    haveI : (𝓝[Ioi θ0] θ0).NeBot := nhdsWithin_Ioi_neBot le_rfl
    exact le_of_tendsto h1 hb

/-- `∂_z(∂_θP) = ∂_z(V(P)) + tan θ · ∂_zP` at any point of the open quadrant. -/
lemma pz_pth_eq {P : ℝ → ℝ → ℝ} (hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.pz (Work.Spaces.pth P) z θ
      = Work.Spaces.pz (Work.Construction.Vop P) z θ
        + Real.tan θ * Work.Spaces.pz P z θ := by
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hdP : DifferentiableAt ℝ (fun z' => P z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds h))
  have hpth1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth P)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.contDiffOn_uncurry_pth_qd (G := P) (n := 1) hP2
  have hdpth : DifferentiableAt ℝ (fun z' => Work.Spaces.pth P z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hpth1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds h))
  show deriv (fun z' => Work.Spaces.pth P z' θ) z
      = deriv (fun z' => Work.Construction.Vop P z' θ) z
        + Real.tan θ * deriv (fun z' => P z' θ) z
  have hV : deriv (fun z' => Work.Construction.Vop P z' θ) z
      = deriv (fun z' => Work.Spaces.pth P z' θ) z
        - Real.tan θ * deriv (fun z' => P z' θ) z := by
    have hfun : (fun z' => Work.Construction.Vop P z' θ)
        = fun z' => Work.Spaces.pth P z' θ - Real.tan θ * P z' θ := by
      funext z'; rw [Work.Construction.Vop]
    rw [hfun]
    have h2 : HasDerivAt (fun z' => Work.Spaces.pth P z' θ - Real.tan θ * P z' θ)
        (deriv (fun z' => Work.Spaces.pth P z' θ) z
          - Real.tan θ * deriv (fun z' => P z' θ) z) z := by
      have hA : HasDerivAt (fun z' => Work.Spaces.pth P z' θ)
          (deriv (fun z' => Work.Spaces.pth P z' θ) z) z := hdpth.hasDerivAt
      have hB : HasDerivAt (fun z' => Real.tan θ * P z' θ)
          (Real.tan θ * deriv (fun z' => P z' θ) z) z := (hdP.hasDerivAt).const_mul _
      have hsub := hA.sub hB
      have hfun2 : ((fun z' => Work.Spaces.pth P z' θ) - fun z' => Real.tan θ * P z' θ)
          = fun z' => Work.Spaces.pth P z' θ - Real.tan θ * P z' θ := by funext x; rfl
      rwa [hfun2] at hsub
    exact h2.deriv
  rw [hV]; ring

/-- `D_z²P = z·∂_zP + z²·∂_z²P` on the open quadrant. -/
lemma DzIter_two_eq {P : ℝ → ℝ → ℝ} (hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.DzIter 2 P z θ
      = z * Work.Spaces.pz P z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz P) z θ := by
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz P)) Work.Construction.Qd := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ (Function.uncurry P)) Work.Construction.Qd :=
      hP2.fderiv_of_isOpen hQd (m := 1) (by norm_num)
    refine (hfd.clm_apply (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ))))).congr (fun p hp => ?_)
    simp only [Function.uncurry]
    exact Work.Spaces.pz_eq_fderiv
      ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hp))
  have hdiff : DifferentiableAt ℝ (fun t => Work.Spaces.pz P t θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hpz1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds h))
  show z * deriv (fun t => Work.Spaces.DzIter 1 P t θ) z = _
  have hfun : (fun t => Work.Spaces.DzIter 1 P t θ) = fun t => t * Work.Spaces.pz P t θ := by
    funext t; rfl
  rw [hfun]
  have h2 : HasDerivAt (fun t => t * Work.Spaces.pz P t θ)
      (Work.Spaces.pz P z θ + z * deriv (fun t => Work.Spaces.pz P t θ) z) z := by
    have hA : HasDerivAt (fun t : ℝ => t) 1 z := hasDerivAt_id z
    have hB : HasDerivAt (fun t => Work.Spaces.pz P t θ)
        (deriv (fun t => Work.Spaces.pz P t θ) z) z := hdiff.hasDerivAt
    have hmul := hA.mul hB
    have hfun2 : ((fun t : ℝ => t) * fun t => Work.Spaces.pz P t θ)
        = fun t => t * Work.Spaces.pz P t θ := by funext x; rfl
    rw [hfun2] at hmul
    simpa using hmul
  rw [h2.deriv]
  rw [show deriv (fun t => Work.Spaces.pz P t θ) z
      = Work.Spaces.pz (Work.Spaces.pz P) z θ from rfl]
  ring

/-- `∂_θ(∂_zP) = (D_z(V(P)) + tan θ · D_zP)/z` on the open quadrant. -/
lemma pth_pz_eq {P : ℝ → ℝ → ℝ} (hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.pth (Work.Spaces.pz P) z θ
      = (Work.Spaces.DzIter 1 (Work.Construction.Vop P) z θ
          + Real.tan θ * Work.Spaces.DzIter 1 P z θ) / z := by
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hz : z ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.Qd_pos h)
  have hcl := Work.Spaces.pz_pth_comm (f := P)
    ((hP2.contDiffAt (hQd.mem_nhds h)).of_le (le_refl (2 : WithTop ℕ∞)))
  rw [← hcl]
  rw [pz_pth_eq hP2 h]
  have h1 : Work.Spaces.pz (Work.Construction.Vop P) z θ
      = Work.Spaces.DzIter 1 (Work.Construction.Vop P) z θ / z := by
    rw [show Work.Spaces.DzIter 1 (Work.Construction.Vop P) z θ
        = z * Work.Spaces.pz (Work.Construction.Vop P) z θ from rfl]
    field_simp
  have h2 : Work.Spaces.pz P z θ = Work.Spaces.DzIter 1 P z θ / z := by
    rw [show Work.Spaces.DzIter 1 P z θ = z * Work.Spaces.pz P z θ from rfl]
    field_simp
  rw [h1, h2]
  field_simp

end Work.FTS_StreamBdry.SB25Aux4
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.P2Aux.AsmSupport =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB3.P2Aux.AsmSupport` — support lemmas for `pthIter2_le`

Generic helpers used by the assembly of `SB3.pthIter2_le`:

* `psiP_c3` — `psiP αG Ψ` is `C³` on the open quadrant (the `C²` proof `SB3.psiP_c2`,
  with the SB1′ decomposition `Ψ = psiP + κ·gaugeMode` and the analyticity of the gauge mode);
* `bslOp_psiP` — the elliptic law for the `U`-slot part, `bslOp αG (psiP αG Ψ) = F` on `Qd`
  (same proof as `SB3.law_psiP`, stopping one step earlier);
* `Dz_div`, `DzIter_div_eqOn`, `DzIter_congr_isOpen`, `DzIter_Dz_eqOn`, `pz_smooth_of`,
  `Dz_smooth_of`, `div_identities` — the calculus of `D_z^j (Q / s2)` needed to pass the
  bounds on `D_z^j (psiP)` to the functions `u = psiP/s2`, `u₁ = D_zpsiP/s2`;
* `abs_div_s2_le_of`, `abs_s2_mul_le_of`, `abs_two_sin_sq_mul_le_of`, `abs_comb_le_of`,
  `abs_neg_sub_le_of` — pointwise `abs` bookkeeping.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB3.P2Aux

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP gaugeMode)

set_option autoImplicit false

lemma isOpen_Qd_asm : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

/-- `psiP αG Ψ` is `C^3` on the open quadrant. -/
theorem psiP_c3 {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ContDiffOn ℝ 3 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd := by
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M)
    hαG h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
  have hg : ContDiffOn ℝ 3
      (Function.uncurry (gaugeMode αG)) Work.Construction.Qd :=
    (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode αG).of_le le_top
  have hsub : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ =>
        Function.uncurry Ψ p - κ * Function.uncurry (gaugeMode αG) p)
      Work.Construction.Qd :=
    h3.sub (contDiffOn_const.mul hg)
  refine hsub.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  have h := hκ z θ hp
  simp only [Function.uncurry]
  linarith

/-- `bslOp αG (psiP αG Ψ) = F` on the open quadrant. -/
theorem bslOp_psiP {αG M : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp αG (psiP αG Ψ) z θ = F z θ := by
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M)
    hαG h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
  have hC2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot
  have hgau : ContDiffOn ℝ 2 (Function.uncurry (gaugeMode αG)) Work.Construction.Qd :=
    (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode αG).of_le le_top
  intro z θ hmem
  obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem)
  have hnbhd : Work.Construction.Qd ∈ 𝓝 (z, θ) :=
    Work.FTS_StreamBdry.SB25.qd_isOpen.mem_nhds ⟨hz, hθ1, hθ2⟩
  have hev : ∀ᶠ q in 𝓝 (z, θ),
      Ψ q.1 q.2 = (psiP αG Ψ q.1 q.2 + κ * gaugeMode αG q.1 q.2) :=
    Filter.mem_of_superset hnbhd (fun q hq => hκ q.1 q.2 hq)
  have hcongr : Work.Elliptic.bslOp αG Ψ z θ
      = Work.Elliptic.bslOp αG (fun z θ =>
          psiP αG Ψ z θ + κ * gaugeMode αG z θ) z θ :=
    Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq αG hev
  have hg2 : ContDiffAt ℝ 2
      (Function.uncurry (fun z θ => κ * gaugeMode αG z θ)) (z, θ) :=
    (hgau.contDiffAt hnbhd).const_smul κ
  have hadd : Work.Elliptic.bslOp αG (fun z θ =>
        psiP αG Ψ z θ + κ * gaugeMode αG z θ) z θ
      = Work.Elliptic.bslOp αG (psiP αG Ψ) z θ
        + Work.Elliptic.bslOp αG (fun z θ => κ * gaugeMode αG z θ) z θ :=
    Work.Elliptic.bslOp_add αG (psiP αG Ψ)
      (fun z θ => κ * gaugeMode αG z θ) z θ hcos
      (hC2.contDiffAt hnbhd) hg2
  have hD0 : Work.Elliptic.bslOp αG (fun z θ => κ * gaugeMode αG z θ) z θ = 0 := by
    rw [Work.FTS.BSIdent.OddExt.bslOp_const_mul αG κ (gaugeMode αG) z θ,
      ((Work.FTS_StreamBdry.SB25.gaugeMode_facts hαG).2 z θ hmem).2, mul_zero]
  calc Work.Elliptic.bslOp αG (psiP αG Ψ) z θ
      = Work.Elliptic.bslOp αG (fun z θ =>
          psiP αG Ψ z θ + κ * gaugeMode αG z θ) z θ := by
        rw [hadd, hD0, add_zero]
    _ = Work.Elliptic.bslOp αG Ψ z θ := hcongr.symm
    _ = F z θ := hsol.1 z hz θ hθ1 hθ2

/-! ## §2 `D_z` of a division by a `θ`-only function, and its iterates -/

/-- `D_z` of a division by a `θ`-only function. -/
lemma Dz_div {c : ℝ → ℝ} {Q : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => Q z' θ) z) :
    Work.Spaces.Dz (fun z θ' => Q z θ' / c θ') z θ = Work.Spaces.Dz Q z θ / c θ := by
  show z * deriv (fun z' => Q z' θ / c θ) z = z * deriv (fun z' => Q z' θ) z / c θ
  rw [show (fun z' => Q z' θ / c θ) = fun z' => (c θ)⁻¹ * Q z' θ from by
    funext z'; rw [div_eq_inv_mul]]
  rw [deriv_const_mul _ hd]
  ring

/-- Congruence of `D_z^j` on an open set. -/
lemma DzIter_congr_isOpen {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j f))
      (Function.uncurry (Work.Spaces.DzIter j g)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
      intro p hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j f) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j g) p.1 p.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

/-- `D_z^j (D_z Q) = D_z^{j+1} Q` on an open set. -/
lemma DzIter_Dz_eqOn {Q : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.Dz Q)))
      (Function.uncurry (Work.Spaces.DzIter (j + 1) Q)) V := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      intro p hp
      have hc : Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.Dz Q)) p.1 p.2
          = Work.Spaces.Dz (Work.Spaces.DzIter (j + 1) Q) p.1 p.2 := by
        show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.Dz Q)) p.1 p.2
          = p.1 * Work.Spaces.pz (Work.Spaces.DzIter (j + 1) Q) p.1 p.2
        rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]
      exact hc

/-- The division identity for `D_z^j` on an open set. -/
lemma DzIter_div_eqOn {c : ℝ → ℝ} {Q : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {j : ℕ}
    (hd : ∀ i, i < j → ∀ p ∈ V,
      DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter i Q z' p.2) p.1) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (fun z θ => Q z θ / c θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter j Q z θ / c θ)) V := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      intro p hp
      have ihj : Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (fun z θ => Q z θ / c θ)))
          (Function.uncurry (fun z θ => Work.Spaces.DzIter j Q z θ / c θ)) V :=
        ih (fun i hi => hd i (Nat.lt_succ_of_lt hi))
      have hcongr : Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => Q z θ / c θ)) p.1 p.2
          = Work.Spaces.Dz (fun z θ => Work.Spaces.DzIter j Q z θ / c θ) p.1 p.2 := by
        show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j (fun z θ => Q z θ / c θ)) p.1 p.2
          = p.1 * Work.Spaces.pz (fun z θ => Work.Spaces.DzIter j Q z θ / c θ) p.1 p.2
        rw [Work.Spaces.pz_congr_of_isOpen hV ihj hp]
      show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => Q z θ / c θ)) p.1 p.2
        = Work.Spaces.Dz (Work.Spaces.DzIter j Q) p.1 p.2 / c p.2
      rw [hcongr, Dz_div (hd j (Nat.lt_succ_self j) p hp)]

/-- `∂_z` costs one order of smoothness (at finite order) on an open set. -/
lemma pz_smooth_of {Q : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry Q) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz Q)) V :=
  Work.FTS_StreamBdry.SB3.psiP_D3_aux_pz_smooth hV h

/-- `D_z` maps `C^{n+1}` functions to `C^n` functions on an open set. -/
lemma Dz_smooth_of {Q : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry Q) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz Q)) V := by
  have hpz : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz Q)) V := pz_smooth_of hV h
  have hmul : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz Q) p) V :=
    contDiff_fst.contDiffOn.mul hpz
  refine hmul.congr (fun p hp => ?_)
  rfl

/-- **The division identities.**  If `P` is `C^3` on `Qd`, then for `u = P/s2` and
`u₁ = (D_zP)/s2`: `D_z^j u = (D_z^j P)/s2` for `j ≤ 3` and `D_z^j u₁ = (D_z^{j+1} P)/s2` for
`j ≤ 2`, on `Qd`. -/
lemma div_identities {P : ℝ → ℝ → ℝ}
    (hPc3 : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd) :
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 3,
        Work.Spaces.DzIter j (fun z θ => P z θ / Work.Construction.s2 θ) z θ
          = Work.Spaces.DzIter j P z θ / Work.Construction.s2 θ) ∧
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
        Work.Spaces.DzIter j (fun z θ => Work.Spaces.Dz P z θ / Work.Construction.s2 θ) z θ
          = Work.Spaces.DzIter (j + 1) P z θ / Work.Construction.s2 θ) := by
  have hV : IsOpen Work.Construction.Qd := isOpen_Qd_asm
  have h0 : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd := hPc3
  have h1 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DzIter 1 P))
      Work.Construction.Qd := Dz_smooth_of hV h0
  have h2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter 2 P))
      Work.Construction.Qd := Dz_smooth_of hV h1
  have hdiff : ∀ i ≤ 2, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter i P z' θ) z := by
    intro i hi z θ hmem
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact Work.Spaces.differentiableAt_curry_left
        ((h0.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hmem))
    · exact Work.Spaces.differentiableAt_curry_left
        ((h1.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hmem))
    · exact Work.Spaces.differentiableAt_curry_left
        ((h2.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hmem))
  refine ⟨?_, ?_⟩
  · intro z θ h j hj
    have h1' := DzIter_div_eqOn (c := Work.Construction.s2) hV
      (j := j) (fun i hi p hp => hdiff i (by omega) p.1 p.2 hp) h
    simpa only [Function.uncurry] using h1'
  · intro z θ h j hj
    have heq : Set.EqOn
        (Function.uncurry (fun z θ => Work.Spaces.Dz P z θ / Work.Construction.s2 θ))
        (Function.uncurry (Work.Spaces.Dz (fun z θ => P z θ / Work.Construction.s2 θ)))
        Work.Construction.Qd := by
      intro p hp
      exact (Dz_div (c := Work.Construction.s2) (Q := P)
        (hd := hdiff 0 (by norm_num) p.1 p.2 hp)).symm
    have hc := DzIter_congr_isOpen hV heq j h
    have h3 : Work.Spaces.DzIter (j + 1)
        (fun z θ => P z θ / Work.Construction.s2 θ) z θ
        = Work.Spaces.DzIter (j + 1) P z θ / Work.Construction.s2 θ :=
      DzIter_div_eqOn (c := Work.Construction.s2) hV
        (j := j + 1) (fun i hi p hp => hdiff i (by omega) p.1 p.2 hp) h
    have hmid : Work.Spaces.DzIter j
        (Work.Spaces.Dz (fun z θ => P z θ / Work.Construction.s2 θ)) z θ
        = Work.Spaces.DzIter (j + 1) (fun z θ => P z θ / Work.Construction.s2 θ) z θ := by
      simpa only [Function.uncurry] using
        DzIter_Dz_eqOn (Q := fun z θ => P z θ / Work.Construction.s2 θ) hV j h
    have hc' : Work.Spaces.DzIter j
        (fun z θ => Work.Spaces.Dz P z θ / Work.Construction.s2 θ) z θ
        = Work.Spaces.DzIter j
            (Work.Spaces.Dz (fun z θ => P z θ / Work.Construction.s2 θ)) z θ := by
      simpa only [Function.uncurry] using hc
    calc Work.Spaces.DzIter j (fun z θ => Work.Spaces.Dz P z θ / Work.Construction.s2 θ) z θ
        = Work.Spaces.DzIter j
            (Work.Spaces.Dz (fun z θ => P z θ / Work.Construction.s2 θ)) z θ := hc'
      _ = Work.Spaces.DzIter (j + 1)
            (fun z θ => P z θ / Work.Construction.s2 θ) z θ := hmid
      _ = Work.Spaces.DzIter (j + 1) P z θ / Work.Construction.s2 θ := h3

/-! ## §3 Pointwise `abs` bookkeeping -/









end Work.FTS_StreamBdry.SB3.P2Aux
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound2` — the two endpoint representations

At the left end we use a point `ξ ∈ (0, θ)` so close to `0` that `|G ξ| ≤ ε` (possible because
`|G ξ| ≤ C₁ · sin ξ cos²ξ / 2 ≤ C₁ ξ / 2`); the two-point bound then gives
`|G θ| ≤ ε + ∫_ξ^θ gwt ≤ ε + ∫_0^θ gwt`.  At the right end we use `ξ ∈ (θ, π/2)` with
`π/2 - ξ` so small that `|G ξ| ≤ ε` and conclude `|G θ| ≤ ε + ∫_θ^{π/2} gwt`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6.UprimeAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **Left representation**: for `θ ∈ (0, π/4]`, `|G θ| ≤ ∫_0^θ gwt A C`. -/
lemma left_rep {u H : ℝ → ℝ → ℝ} {z A C C₁ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hode : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (u1fun u z)
        (H z θ - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * u1fun u z θ) θ)
    (hH : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |H z θ| ≤ A / Real.sin (2 * θ) + C)
    (hcrude : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.sin (2 * θ) * u1fun u z θ| ≤ C₁)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4)) :
    |wfun θ * u1fun u z θ| ≤ ∫ t in (0 : ℝ)..θ, gwt A C t := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hθpos : 0 < θ := hθ.1
  have hθlt : θ < Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
  have hC₁1 : 0 < C₁ + 1 := by linarith
  set ξ : ℝ := min (θ / 2) (ε / (C₁ + 1)) with hξdef
  have hξpos : 0 < ξ := by
    rw [hξdef]; exact lt_min (by linarith) (div_pos hε hC₁1)
  have hξlt : ξ < θ := by
    rw [hξdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hξε : ξ ≤ ε / (C₁ + 1) := by rw [hξdef]; exact min_le_right _ _
  have hξmem : ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hξpos, lt_trans hξlt hθlt⟩
  have hcr := crude_G (u := u) (H := H) (z := z) hC₁ hcrude hξmem
  have hle : wfun ξ / Real.sin (2 * ξ) ≤ ξ / 2 := Wdiv_le_theta hξmem
  have hsmall : |wfun ξ * u1fun u z ξ| ≤ ε := by
    have h1 : C₁ * (wfun ξ / Real.sin (2 * ξ)) ≤ C₁ * (ξ / 2) :=
      mul_le_mul_of_nonneg_left hle hC₁
    have h2 : C₁ * (ξ / 2) ≤ ε := by
      have h3 : ξ / 2 ≤ ε / (C₁ + 1) / 2 := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hC₁
      have h5 : C₁ * (ε / (C₁ + 1) / 2) ≤ ε := by
        have h6 : C₁ / (C₁ + 1) ≤ 1 := by rw [div_le_one hC₁1]; linarith
        have h7 : C₁ * (ε / (C₁ + 1) / 2) = (C₁ / (C₁ + 1)) * (ε / 2) := by
          field_simp
          try ring
        rw [h7]
        calc (C₁ / (C₁ + 1)) * (ε / 2) ≤ 1 * ε :=
              mul_le_mul h6 (by linarith [hε]) (by positivity) (by norm_num)
          _ = ε := one_mul ε
      linarith
    linarith
  have htp := two_point (u := u) (H := H) (z := z) (A := A) (C := C) hode hH hξpos
    (le_of_lt hξlt) hθlt
  have htri : |wfun θ * u1fun u z θ| ≤ ε + ∫ t in ξ..θ, gwt A C t := by
    have h1 : |wfun θ * u1fun u z θ| ≤
        |wfun θ * u1fun u z θ - wfun ξ * u1fun u z ξ| + |wfun ξ * u1fun u z ξ| := by
      have := abs_add_le (wfun θ * u1fun u z θ - wfun ξ * u1fun u z ξ)
        (wfun ξ * u1fun u z ξ)
      simpa only [sub_add_cancel] using this
    linarith
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..ξ, gwt A C t := by
    refine intervalIntegral.integral_nonneg (le_of_lt hξpos) (fun u' hu' => ?_)
    exact gwt_nonneg_Icc hA hC ⟨hu'.1, le_trans hu'.2 (le_of_lt (lt_trans hξlt hθlt))⟩
  have hadd : (∫ t in (0 : ℝ)..ξ, gwt A C t) + ∫ t in ξ..θ, gwt A C t
      = ∫ t in (0 : ℝ)..θ, gwt A C t :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((continuous_gwt A C).intervalIntegrable 0 ξ)
      ((continuous_gwt A C).intervalIntegrable ξ θ)
  linarith

/-- **Right representation**: for `θ ∈ [π/4, π/2)`, `|G θ| ≤ ∫_θ^{π/2} gwt A C`. -/
lemma right_rep {u H : ℝ → ℝ → ℝ} {z A C C₁ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hode : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (u1fun u z)
        (H z θ - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * u1fun u z θ) θ)
    (hH : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |H z θ| ≤ A / Real.sin (2 * θ) + C)
    (hcrude : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.sin (2 * θ) * u1fun u z θ| ≤ C₁)
    {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    |wfun θ * u1fun u z θ| ≤ ∫ t in θ..(Real.pi / 2), gwt A C t := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hθpos : 0 < θ := by linarith [hθ.1, Real.pi_pos]
  have hθlt : θ < Real.pi / 2 := hθ.2
  have hC₁1 : 0 < C₁ + 1 := by linarith
  have harg : 0 < 2 * ε / (C₁ + 1) := by positivity
  have hs : 0 < Real.sqrt (2 * ε / (C₁ + 1)) := Real.sqrt_pos.mpr harg
  set d : ℝ := min ((Real.pi / 2 - θ) / 2) (Real.sqrt (2 * ε / (C₁ + 1))) with hddef
  have hdpos : 0 < d := by rw [hddef]; exact lt_min (by linarith) hs
  have hdle : d ≤ (Real.pi / 2 - θ) / 2 := by rw [hddef]; exact min_le_left _ _
  have hdlt : d < Real.pi / 2 - θ := lt_of_le_of_lt hdle (by linarith)
  have hd2 : d ^ 2 ≤ 2 * ε / (C₁ + 1) := by
    have h := min_le_right ((Real.pi / 2 - θ) / 2) (Real.sqrt (2 * ε / (C₁ + 1)))
    rw [← hddef] at h
    have h' := mul_self_le_mul_self (le_of_lt hdpos) h
    rw [Real.mul_self_sqrt (le_of_lt harg)] at h'
    simpa [pow_two] using h'
  set ξ : ℝ := Real.pi / 2 - d with hξdef
  have hξgt : θ < ξ := by rw [hξdef]; linarith
  have hξlt : ξ < Real.pi / 2 := by rw [hξdef]; linarith
  have hξpos : 0 < ξ := lt_trans hθpos hξgt
  have hξmem : ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hξpos, hξlt⟩
  have hπξ : Real.pi / 2 - ξ = d := by rw [hξdef]; ring
  have hcr := crude_G (u := u) (H := H) (z := z) hC₁ hcrude hξmem
  have hle : wfun ξ / Real.sin (2 * ξ) ≤ (Real.pi / 2 - ξ) ^ 2 / 2 :=
    Wdiv_le_right ⟨le_trans hθ.1 (le_of_lt hξgt), hξlt⟩
  have hsmall : |wfun ξ * u1fun u z ξ| ≤ ε := by
    have h1 : C₁ * (wfun ξ / Real.sin (2 * ξ)) ≤ C₁ * ((Real.pi / 2 - ξ) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hle hC₁
    have h2 : C₁ * ((Real.pi / 2 - ξ) ^ 2 / 2) ≤ ε := by
      rw [hπξ]
      have h3 : d ^ 2 / 2 ≤ (2 * ε / (C₁ + 1)) / 2 := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hC₁
      have h5 : C₁ * ((2 * ε / (C₁ + 1)) / 2) ≤ ε := by
        have h6 : C₁ / (C₁ + 1) ≤ 1 := by rw [div_le_one hC₁1]; linarith
        have h7 : C₁ * ((2 * ε / (C₁ + 1)) / 2) = (C₁ / (C₁ + 1)) * ε := by
          field_simp
          try ring
        rw [h7]
        calc (C₁ / (C₁ + 1)) * ε ≤ 1 * ε :=
              mul_le_mul h6 (le_refl ε) (by positivity) (by norm_num)
          _ = ε := one_mul ε
      linarith
    linarith
  have htp := two_point (u := u) (H := H) (z := z) (A := A) (C := C) hode hH hθpos
    (le_of_lt hξgt) hξlt
  have htri : |wfun θ * u1fun u z θ| ≤ ε + ∫ t in θ..ξ, gwt A C t := by
    have h2 : |wfun θ * u1fun u z θ| ≤
        |wfun θ * u1fun u z θ - wfun ξ * u1fun u z ξ| + |wfun ξ * u1fun u z ξ| := by
      have := abs_add_le (wfun θ * u1fun u z θ - wfun ξ * u1fun u z ξ)
        (wfun ξ * u1fun u z ξ)
      simpa only [sub_add_cancel] using this
    rw [abs_sub_comm] at h2
    linarith
  have hnn : 0 ≤ ∫ t in ξ..(Real.pi / 2), gwt A C t := by
    refine intervalIntegral.integral_nonneg (le_of_lt hξlt) (fun u' hu' => ?_)
    exact gwt_nonneg_Icc hA hC ⟨le_trans (le_of_lt hξpos) hu'.1, hu'.2⟩
  have hadd : (∫ t in θ..ξ, gwt A C t) + ∫ t in ξ..(Real.pi / 2), gwt A C t
      = ∫ t in θ..(Real.pi / 2), gwt A C t :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((continuous_gwt A C).intervalIntegrable θ ξ)
      ((continuous_gwt A C).intervalIntegrable ξ (Real.pi / 2))
  linarith

end Work.FTS_StreamBdry.SB6.UprimeAux
end
end
