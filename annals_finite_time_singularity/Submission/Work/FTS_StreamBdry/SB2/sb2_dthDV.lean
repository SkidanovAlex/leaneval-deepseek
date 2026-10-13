import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.law_psiP
import Submission.Work.FTS_StreamBdry.SB25.law_Dform
import Submission.Work.FTS_StreamBdry.SB2.sb2_deriv_law_rhs
import Submission.Work.Spaces.mixed_comm

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
