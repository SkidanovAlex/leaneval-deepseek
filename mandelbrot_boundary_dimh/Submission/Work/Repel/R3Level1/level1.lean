import Mathlib
import Submission.Work.Repel.R3Pre
import Submission.Work.Repel.R3Level0.deriv_lower_of_close
import Submission.Work.Repel.R3Level0v2.target_control_R
import Submission.Work.Repel.deriv_bound_on_ball_explicit
import Submission.Work.Repel.piExp_sub_one_bound
import Submission.Work.Repel.R3Level1.koebe_localize
import Submission.Work.Repel.R3Level1.loc_small
import Submission.Work.Repel.R3Level1.htgt_arith

/-!
# `Work.Repel.R3Level1.level1` : the level-1 data of the §6 assembly

This file proves the contract `Work.Repel.R3Level1.level1`: from the level-0 perturbation data and
its target disc it produces the level-1 perturbation data `P₁` (the perturbed Fatou coordinate of
the rescaled horn germ `germ1 s₀ P₀.R`), the Lemma-6.2 backward chain `W` (through the abstract
`ChainSetup.chain`), the covered disc `ball (d₁.φ cbase) σ₁`, and all the interface conjuncts of
the §6 assembly (the `π`-lifts of the level-0 source and of the level-0 target, the two derivative
comparisons, the `hfit` threshold and the two angle conditions).

The key new ingredient (beyond the bookkeeping) is the level-1 target control
(`∀ w ∈ ball wt₀ ρ₀, P₀.φ w ∈ ball 0 σ₀ → s₀ π w ∈ P₁.φ '' ball cbase CS.ρ`): it combines
* `Work.Repel.R3Level1.koebe_localize` (the localization of the level-0 source from the bound on
  its image),
* the elementary exponential estimate `‖π(w - wt₀) - 1‖ ≤ 4π‖w - wt₀‖`,
* and the level-matching arithmetic `Work.Repel.R3Level1.htgt_arith`.
-/

namespace Work.Repel.R3Level1

open MandelDim Complex Set Metric Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem fit_final {η η₁ Cb C₀ C₁' : ℝ} (hη : 0 < η) (hη₁ : 0 < η₁) (hCb : 0 < Cb)
    (hC₀ : 0 < C₀ + 1) (hC₁' : 0 < C₁' + 1)
    (h : 256 ≤ η ^ 3 * (320 * (C₀ + 1) * (10 ^ 12 * Cb ^ 2 * (C₁' + 1) ^ 2))) :
    η * η₁ ^ 2 / (320 * (C₀ + 1)) ≤ (10 ^ 6 * Cb * (C₁' + 1) * η ^ 2 * η₁) ^ 2 / 256 := by
  have hB : 0 < 320 * (C₀ + 1) := by positivity
  have hE : (0:ℝ) < 256 := by norm_num
  have key : (10 ^ 6 * Cb * (C₁' + 1) * η ^ 2 * η₁) ^ 2 / 256 * (320 * (C₀ + 1))
      = (η ^ 3 * (320 * (C₀ + 1) * (10 ^ 12 * Cb ^ 2 * (C₁' + 1) ^ 2))) * (η * η₁ ^ 2) / 256 := by
    ring
  rw [div_le_iff₀ hB, key, le_div_iff₀ hE]
  nlinarith [h, mul_pos hη (pow_pos hη₁ 2)]

theorem level1 (Bpre : Work.Repel.R3Pre) (a₁ a₂ : ℕ) (β : ℂ)
    (P₀ : MandelDim.PertData Bpre.S.d₀ (Work.Repel.fam (MandelDim.alphaOf a₁ a₂ β)) Set.univ
        Bpre.η Bpre.y₀ Bpre.K (Metric.closedBall Bpre.wt₀ (2 * Bpre.r₀)) Bpre.δ)
    (ρ₀ σ₀ : ℝ) (hρ₀ : 0 < ρ₀) (hρ₀le : ρ₀ ≤ Bpre.r₀ / 2) (hσ₀ : 0 < σ₀) (hσ₀big : 4 / Bpre.η ≤ σ₀)
    (hσ₀le : σ₀ ≤ 64 / Bpre.η)
    (hwt₀ : ‖Bpre.wt₀‖ + ρ₀ ≤ 2 * Bpre.η)
    (hinjφ₀ : Set.InjOn P₀.φ (Metric.ball Bpre.wt₀ ρ₀))
    (hcov₀ : Metric.ball 0 σ₀ ⊆ P₀.φ '' Metric.ball Bpre.wt₀ ρ₀)
    (hsub₀ : Metric.ball Bpre.wt₀ ρ₀ ⊆ P₀.Dφ)
    (hDflatDR : Work.Repel.Dflat Bpre.η ⊆ P₀.DR)
    (hP₀lo : ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀,
      ‖deriv Bpre.S.d₀.φ Bpre.wt₀‖ / 2 ≤ ‖deriv P₀.φ w‖)
    (hNear1 : MandelDim.NearOn (Work.Repel.g0germ Bpre.S.d₀) (Work.Repel.germ1 Bpre.S.s₀ P₀.R)
        (Work.Repel.Dgerm1 Bpre.S.s₀ P₀.DR) Bpre.L₁ Bpre.δ₁₀)
    (hrotgerm : MandelDim.rotOf (Work.Repel.germ1 Bpre.S.s₀ P₀.R) = 1 / ((a₂ : ℂ) + β))
    (hInF1germ : MandelDim.InF1 (MandelDim.rotOf (Work.Repel.germ1 Bpre.S.s₀ P₀.R)))
    (hrotfam : MandelDim.rotOf (Work.Repel.fam (MandelDim.alphaOf a₁ a₂ β)) =
      MandelDim.alphaOf a₁ a₂ β)
    (hexp : ‖Complex.exp (2 * Real.pi * I * (1 / ((a₂ : ℂ) + β))) - 1‖ ≤ 32 / (a₂ : ℝ))
    (ha₁201 : 201 * (Bpre.η + 1) ≤ (a₁ : ℝ))
    (ha₂17 : 17 * Real.exp (2 * Real.pi * Bpre.η) + Bpre.b + 1 ≤ (a₂ : ℝ))
    (ha₂η : 8 * Bpre.η₁ + 1 ≤ (a₂ : ℝ))
    (hcB : 768 * Bpre.cB / Bpre.δ₁₀ + 1 ≤ (a₂ : ℝ))
    (ha₁M : 16 * Real.pi * Bpre.M₀ / Bpre.δ₀₀ + 1 ≤ (a₁ : ℝ))
    (hβre : 0 ≤ β.re) (hβre' : β.re < 1) (hβim : |β.im| ≤ Bpre.b) (hNaa₁ : Bpre.Na ≤ a₁)
    (hxa : |((1 : ℂ) / ((a₂ : ℂ) + β)).re| ≤ 1 / 2)
    (hαre : 0 < (MandelDim.alphaOf a₁ a₂ β).re)
    (hroom : (Bpre.δ₁ + Bpre.D₁ * Bpre.CS.ρ) / ‖Bpre.S.s₀‖ <
      ρ₀ * ‖deriv MandelDim.piExp Bpre.wt₀‖ / 8) 
    (hδsmall : 10 ^ 8 * Real.pi * Bpre.δ * ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖ ≤
      Bpre.g₀ * Bpre.m₁ * Bpre.CS.ρ)
    (hηtgt : 10 ^ 7 * Real.pi * ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖ /
      (Bpre.g₀ * Bpre.m₁ * Bpre.CS.ρ) ≤ Bpre.η) :
    ∃ (P₁ : MandelDim.PertData Bpre.S.d₁ (Work.Repel.germ1 Bpre.S.s₀ P₀.R)
          (Work.Repel.Dgerm1 Bpre.S.s₀ P₀.DR) Bpre.η₁ Bpre.CS.y₁ Bpre.CS.K₂ Bpre.K₂' Bpre.δ₁)
      (W : ℕ → Set ℂ) (sgn σ₁ : ℝ) (cbase : ℂ),
      (cbase = Bpre.S.ζa ∨ cbase = Bpre.S.ζb) ∧
      W 0 = Metric.ball cbase Bpre.CS.ρ ∧
      Metric.closedBall cbase (2 * Bpre.CS.ρ) ⊆ Bpre.K₂' ∧
      Set.InjOn P₁.φ (Metric.ball cbase Bpre.CS.ρ) ∧
      0 < σ₁ ∧ Metric.ball (Bpre.S.d₁.φ cbase) σ₁ ⊆ P₁.φ '' Metric.ball cbase Bpre.CS.ρ ∧
      Metric.ball cbase Bpre.CS.ρ ⊆ P₁.Dφ ∧
      (sgn = 1 ∨ sgn = -1) ∧
      Work.L62.IsChain (fun w => P₁.R w + 1 / MandelDim.rotOf (Work.Repel.germ1 Bpre.S.s₀ P₀.R))
        β P₁.DR Bpre.S.ζa Bpre.S.ζb Bpre.CS.ρ sgn Bpre.CS.C₀ Bpre.CS.C₁ Bpre.CS.C₁' W ∧
      (∃ j₀ : ℕ, ∃ w ∈ W j₀, sgn * w.im < Bpre.η₁ / 4) ∧
      (∀ u' ∈ W 0, ∃ w ∈ Metric.ball Bpre.wt₀ ρ₀, MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀) ∧
      (∀ w ∈ Metric.ball Bpre.wt₀ ρ₀, P₀.φ w ∈ Metric.ball 0 σ₀ →
        Bpre.S.s₀ * MandelDim.piExp w ∈ P₁.φ '' Metric.ball cbase Bpre.CS.ρ) ∧
      (∀ u' ∈ W 0, ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀, MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ →
        ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ ≤
          Bpre.Cb * ‖Bpre.S.s₀‖ * ‖deriv MandelDim.piExp w‖) ∧
      (∀ u' ∈ W 0, ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀, MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ →
        Bpre.cb * ‖Bpre.S.s₀‖ * ‖deriv MandelDim.piExp w‖ ≤
          ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖) ∧
      Bpre.η * Bpre.η₁ ^ 2 / (320 * (Bpre.CS.C₀ + 1)) ≤
        (10 ^ 6 * Bpre.Cb * (Bpre.CS.C₁' + 1) * Bpre.η ^ 2 * Bpre.η₁) ^ 2 / 256 ∧
      (∀ w w' : ℂ, ‖w‖ ≤ 2 * Bpre.η → ‖w'‖ ≤ 2 * Bpre.η →
        |Complex.arg (w' + 1 / (2 * MandelDim.rotOf (Work.Repel.fam (MandelDim.alphaOf a₁ a₂ β)))
          - w)| < 2 * Real.pi / 3) ∧
      (∀ u u' : ℂ, ‖u‖ ≤ 2 * Bpre.η₁ → ‖u'‖ ≤ 2 * Bpre.η₁ →
        |Complex.arg (u' + 1 / (2 * MandelDim.rotOf (Work.Repel.germ1 Bpre.S.s₀ P₀.R)) - u)|
          < 2 * Real.pi / 3) := by
  -- ## the level-1 PertData
  obtain ⟨P₁⟩ := Bpre.hL1uniq (Work.Repel.germ1 Bpre.S.s₀ P₀.R)
    (Work.Repel.Dgerm1 Bpre.S.s₀ P₀.DR) hNear1 (Work.Repel.germ1_zero Bpre.S.s₀ P₀.R) hInF1germ
  -- ## the Lemma-6.2 chain
  set Rm : ℂ → ℂ := fun w => P₁.R w + 1 / MandelDim.rotOf (Work.Repel.germ1 Bpre.S.s₀ P₀.R) with hRmdef
  obtain ⟨W, sgn, hIsChain₀⟩ :=
    Bpre.CS.chain Rm P₁.DR P₁.DR_open
      (by rw [hRmdef]; exact Work.Repel.isTEquivariantOn_add_const _ P₁.R_equiv)
      (by rw [hRmdef]; exact P₁.R_holo.add_const _)
      (fun w hw => P₁.DR_sub hw)
      (by intro w hw; rw [hRmdef]
          exact lt_of_lt_of_le (P₁.R_close w hw) (le_of_lt Bpre.hδ₁ltCS))
      β hβre (le_of_lt hβre') hβim
  rw [hRmdef] at hIsChain₀
  have hIsChain : Work.L62.IsChain
      (fun w => P₁.R w + 1 / MandelDim.rotOf (Work.Repel.germ1 Bpre.S.s₀ P₀.R))
      β P₁.DR Bpre.S.ζa Bpre.S.ζb Bpre.CS.ρ sgn Bpre.CS.C₀ Bpre.CS.C₁ Bpre.CS.C₁' W := hIsChain₀
  have hC₁'pos : 0 < Bpre.CS.C₁' := by
    obtain ⟨z, hz⟩ : ∃ z, z ∈ W 0 := by
      rcases hIsChain.base with hb0 | hb0
      · exact ⟨Bpre.S.ζa, by rw [hb0]; exact Metric.mem_ball_self Bpre.CS.hρ⟩
      · exact ⟨Bpre.S.ζb, by rw [hb0]; exact Metric.mem_ball_self Bpre.CS.hρ⟩
    have h := hIsChain.deriv_bd 0 z hz
    exact lt_of_le_of_lt (norm_nonneg _) h.2
  -- ## the abbreviation `D`
  set D : ℝ := ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖ with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact norm_pos_iff.mpr (mul_ne_zero Bpre.S.hne (Work.Horn.MandelDim.piExp_ne_zero Bpre.wt₀))
  have hDmul : ‖MandelDim.piExp Bpre.wt₀‖ * ‖Bpre.S.s₀‖ = D := by
    rw [hDdef, norm_mul, mul_comm]
  have hDmul2 : ‖Bpre.S.s₀‖ * ‖MandelDim.piExp Bpre.wt₀‖ = D := by
    rw [hDdef, norm_mul]
  have hδsmallD : 10 ^ 8 * Real.pi * Bpre.δ * D ≤ Bpre.g₀ * Bpre.m₁ * Bpre.CS.ρ := hδsmall
  have hηtgtD : 10 ^ 7 * Real.pi * D / (Bpre.g₀ * Bpre.m₁ * Bpre.CS.ρ) ≤ Bpre.η := hηtgt
  -- ## `hanchor`
  have hanchor : ∃ j₀ : ℕ, ∃ w ∈ W j₀, sgn * w.im < Bpre.η₁ / 4 := by
    refine ⟨0, ?_⟩
    rcases hIsChain.base with hb0 | hb0
    · refine ⟨Bpre.S.ζa, ?_, ?_⟩
      · rw [hb0]; exact Metric.mem_ball_self Bpre.CS.hρ
      · have hsgn : sgn * Bpre.S.ζa.im ≤ |Bpre.S.ζa.im| := by
          rcases hIsChain.sign with hs | hs
          · rw [hs]; simp only [one_mul]; exact le_abs_self _
          · rw [hs]; simp only [neg_mul, neg_one_mul, one_mul]; exact neg_le_abs _
        linarith [Bpre.hζa_le, Bpre.hηlt]
    · refine ⟨Bpre.S.ζb, ?_, ?_⟩
      · rw [hb0]; exact Metric.mem_ball_self Bpre.CS.hρ
      · have hsgn : sgn * Bpre.S.ζb.im ≤ |Bpre.S.ζb.im| := by
          rcases hIsChain.sign with hs | hs
          · rw [hs]; simp only [one_mul]; exact le_abs_self _
          · rw [hs]; simp only [neg_mul, neg_one_mul, one_mul]; exact neg_le_abs _
        linarith [Bpre.hζb_le, Bpre.hηlt]
  -- ## the `hfit` conjunct
  have hC₀pos : 0 < Bpre.CS.C₀ := by
    obtain ⟨u, -, u', -, hd⟩ := hIsChain.close 0
    linarith [norm_nonneg (u - u')]
  have hfit : Bpre.η * Bpre.η₁ ^ 2 / (320 * (Bpre.CS.C₀ + 1)) ≤
      (10 ^ 6 * Bpre.Cb * (Bpre.CS.C₁' + 1) * Bpre.η ^ 2 * Bpre.η₁) ^ 2 / 256 := by
    have hη3 : Bpre.Hfit ≤ Bpre.η ^ 3 := by
      have h1 : (1 : ℝ) ≤ Bpre.η := by linarith [Bpre.hη100]
      have h2 : Bpre.η ≤ Bpre.η ^ 3 := by
        have h3 : 0 ≤ (Bpre.η - 1) * (Bpre.η + 1) :=
          mul_nonneg (by linarith) (by linarith [Bpre.hηpos])
        have h4 : 0 ≤ Bpre.η * ((Bpre.η - 1) * (Bpre.η + 1)) :=
          mul_nonneg (le_of_lt Bpre.hηpos) h3
        nlinarith [h4]
      linarith [Bpre.hηHfit, h2]
    exact fit_final Bpre.hηpos Bpre.hη₁pos Bpre.hCbpos (by linarith [hC₀pos]) (by linarith)
      (Work.Repel.fit_threshold (by linarith [hC₀pos]) Bpre.hCbpos hC₁'pos
        Bpre.hHfitdef hη3)
  -- ## the two angle conjuncts
  have hangle₀ : ∀ w w' : ℂ, ‖w‖ ≤ 2 * Bpre.η → ‖w'‖ ≤ 2 * Bpre.η →
      |Complex.arg (w' + 1 / (2 * MandelDim.rotOf (Work.Repel.fam (MandelDim.alphaOf a₁ a₂ β)))
        - w)| < 2 * Real.pi / 3 := by
    intro w w' hw hw'
    rw [hrotfam]
    apply Work.Repel.arg_lt_two_pi_div_three_of_re_pos
    have hre := Work.Repel.re_inv_two_alphaOf a₁ a₂ β hxa
    have hthis : (w' + 1 / (2 * MandelDim.alphaOf a₁ a₂ β) - w).re
        = w'.re + (1 / (2 * MandelDim.alphaOf a₁ a₂ β)).re - w.re := by
      simp only [Complex.sub_re, Complex.add_re]
    rw [hthis]
    have hw1 : w.re ≤ 2 * Bpre.η := le_trans (Complex.re_le_norm w) hw
    have hw1' : -w.re ≤ 2 * Bpre.η := by
      have h := Complex.abs_re_le_norm w; have h2 := neg_le_abs w.re; linarith
    have hw2 : w'.re ≤ 2 * Bpre.η := le_trans (Complex.re_le_norm w') hw'
    have hw2' : -w'.re ≤ 2 * Bpre.η := by
      have h := Complex.abs_re_le_norm w'; have h2 := neg_le_abs w'.re; linarith
    have hbig : 4 * Bpre.η < ((a₁ : ℝ) - 1 / 2) / 2 := by
      have h := ha₁201; nlinarith [Bpre.hη100]
    linarith
  have hangle₁ : ∀ u u' : ℂ, ‖u‖ ≤ 2 * Bpre.η₁ → ‖u'‖ ≤ 2 * Bpre.η₁ →
      |Complex.arg (u' + 1 / (2 * MandelDim.rotOf (Work.Repel.germ1 Bpre.S.s₀ P₀.R)) - u)|
        < 2 * Real.pi / 3 := by
    intro u u' hu hu'
    have hre := Work.Repel.re_inv_two_rotOf a₂ β (g := Work.Repel.germ1 Bpre.S.s₀ P₀.R)
      hrotgerm hβre
    apply Work.Repel.arg_lt_two_pi_div_three_of_re_pos
    have hthis : (u' + 1 / (2 * MandelDim.rotOf (Work.Repel.germ1 Bpre.S.s₀ P₀.R)) - u).re
        = u'.re + (1 / (2 * MandelDim.rotOf (Work.Repel.germ1 Bpre.S.s₀ P₀.R))).re - u.re := by
      simp only [Complex.sub_re, Complex.add_re]
    rw [hthis]
    have hu1 : u.re ≤ 2 * Bpre.η₁ := le_trans (Complex.re_le_norm u) hu
    have hu1' : -u.re ≤ 2 * Bpre.η₁ := by
      have h := Complex.abs_re_le_norm u; have h2 := neg_le_abs u.re; linarith
    have hu2 : u'.re ≤ 2 * Bpre.η₁ := le_trans (Complex.re_le_norm u') hu'
    have hu2' : -u'.re ≤ 2 * Bpre.η₁ := by
      have h := Complex.abs_re_le_norm u'; have h2 := neg_le_abs u'.re; linarith
    have hbig : 4 * Bpre.η₁ < (a₂ : ℝ) / 2 := by
      have h := ha₂η; linarith
    linarith
  -- ## the `cbase`-dependent package
  have hmain : ∀ cbase : ℂ, (cbase = Bpre.S.ζa ∨ cbase = Bpre.S.ζb) →
      W 0 = Metric.ball cbase Bpre.CS.ρ →
      ∃ σ₁ : ℝ, 0 < σ₁ ∧
        Metric.closedBall cbase (2 * Bpre.CS.ρ) ⊆ Bpre.K₂' ∧
        Set.InjOn P₁.φ (Metric.ball cbase Bpre.CS.ρ) ∧
        Metric.ball (Bpre.S.d₁.φ cbase) σ₁ ⊆ P₁.φ '' Metric.ball cbase Bpre.CS.ρ ∧
        Metric.ball cbase Bpre.CS.ρ ⊆ P₁.Dφ ∧
        (∀ u' ∈ Metric.ball cbase Bpre.CS.ρ, ∃ w ∈ Metric.ball Bpre.wt₀ ρ₀,
          MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀) ∧
        (∀ w ∈ Metric.ball Bpre.wt₀ ρ₀, P₀.φ w ∈ Metric.ball 0 σ₀ →
          Bpre.S.s₀ * MandelDim.piExp w ∈ P₁.φ '' Metric.ball cbase Bpre.CS.ρ) ∧
        (∀ u' ∈ Metric.ball cbase Bpre.CS.ρ, ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀,
          MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ →
          ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ ≤ Bpre.Cb * ‖Bpre.S.s₀‖ *
            ‖deriv MandelDim.piExp w‖) ∧
        (∀ u' ∈ Metric.ball cbase Bpre.CS.ρ, ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀,
          MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ →
          Bpre.cb * ‖Bpre.S.s₀‖ * ‖deriv MandelDim.piExp w‖ ≤
            ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖) := by
    intro cbase hcbase hW0
    have hφcbase : Bpre.S.d₁.φ cbase = Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀ := by
      rcases hcbase with h | h
      · rw [h]; exact Bpre.hζaφ
      · rw [h]; exact Bpre.hζbφ
    have hderivcbase : deriv Bpre.S.d₁.φ cbase ≠ 0 := by
      rcases hcbase with h | h
      · rw [h]; exact Bpre.hζaderiv
      · rw [h]; exact Bpre.hζbderiv
    have hK'sub : Metric.closedBall cbase (4 * Bpre.CS.ρ) ⊆ Bpre.K₂' := by
      rcases hcbase with h | h
      · rw [h]; exact Bpre.hK₂'suba
      · rw [h]; exact Bpre.hK₂'subb
    have hsubc : Metric.closedBall cbase (2 * Bpre.CS.ρ) ⊆ Bpre.S.d₁.Dφ := by
      rcases hcbase with h | h
      · rw [h]; exact fun z hz => Bpre.hCSball (Or.inl hz)
      · rw [h]; exact fun z hz => Bpre.hCSball (Or.inr hz)
    have hginj : Set.InjOn Bpre.S.d₁.φ (Metric.ball cbase (2 * Bpre.CS.ρ)) := by
      rcases hcbase with h | h
      · rw [h]; exact Bpre.hinj2ρA.mono Metric.ball_subset_closedBall
      · rw [h]; exact Bpre.hinj2ρB.mono Metric.ball_subset_closedBall
    have hderivlowc : ∀ z ∈ Metric.ball cbase Bpre.CS.ρ,
        ‖deriv Bpre.S.d₁.φ cbase‖ * 2 / 3 ≤ ‖deriv Bpre.S.d₁.φ z‖ := by
      rcases hcbase with h | h
      · rw [h]; exact Bpre.hderivlowA
      · rw [h]; exact Bpre.hderivlowB
    have hnormc : ∀ z ∈ Metric.ball cbase Bpre.CS.ρ,
        ‖Bpre.S.d₁.φ z‖ ≤ 2 * ‖Bpre.S.d₁.φ cbase‖ + 1 := by
      rcases hcbase with h | h
      · rw [h]; exact Bpre.hnormA
      · rw [h]; exact Bpre.hnormB
    have hDbound : ∀ z ∈ Metric.closedBall cbase Bpre.CS.ρ,
        ‖deriv Bpre.S.d₁.φ z‖ ≤ Bpre.D₁ := by
      rcases hcbase with h | h
      · rw [h]; exact Bpre.hDlim
      · rw [h]
        intro z hz
        refine le_trans (Bpre.hDb z ?_) ?_
        · exact Metric.closedBall_subset_closedBall Bpre.hCSρb hz
        · rw [Bpre.hD₁def]; exact le_max_right _ _
    have hm₁le : Bpre.m₁ ≤ ‖deriv Bpre.S.d₁.φ cbase‖ := by
      rw [Bpre.hm₁def]
      rcases hcbase with h | h
      · rw [h]; exact min_le_left _ _
      · rw [h]; exact min_le_right _ _
    have hK₂'sub' : Metric.closedBall cbase (2 * Bpre.CS.ρ) ⊆ Bpre.K₂' :=
      (Metric.closedBall_subset_closedBall (by linarith [Bpre.CS.hρ])).trans hK'sub
    have hballK : ∀ u' ∈ Metric.ball cbase Bpre.CS.ρ, u' ∈ Bpre.K₂' := fun u' hu' =>
      hK₂'sub' (Metric.closedBall_subset_closedBall (by linarith [Bpre.CS.hρ])
        (Metric.ball_subset_closedBall hu'))
    have hm₁D₁ : Bpre.m₁ ≤ Bpre.D₁ :=
      le_trans hm₁le (hDbound cbase (Metric.mem_closedBall_self (le_of_lt Bpre.CS.hρ)))
    have hδ₁le : Bpre.δ₁ ≤ 2 * Bpre.CS.ρ * ‖deriv Bpre.S.d₁.φ cbase‖ / 256 := by
      have h1 : Bpre.δ₁ ≤ Bpre.CS.ρ * Bpre.m₁ / 256 := by
        rw [Bpre.hm₁def]; exact Bpre.hδ₁der
      have h2 : Bpre.CS.ρ * Bpre.m₁ / 256 ≤ 2 * Bpre.CS.ρ * ‖deriv Bpre.S.d₁.φ cbase‖ / 256 := by
        nlinarith [hm₁le, Bpre.CS.hρ, norm_nonneg (deriv Bpre.S.d₁.φ cbase)]
      linarith
    have htcf := Work.Repel.R3Level0v2.target_control_R (d := Bpre.S.d₁) P₁
      (c := cbase) (r := 2 * Bpre.CS.ρ) (R := Bpre.CS.ρ)
      (by linarith [Bpre.CS.hρ]) (by linarith [Bpre.CS.hρ]) (by linarith [Bpre.CS.hρ]) hderivcbase
      (by rw [show 2 * (2 * Bpre.CS.ρ) = 4 * Bpre.CS.ρ by ring]; exact hK'sub)
      hsubc hginj hδ₁le
    set σ₁ : ℝ := (1 / 50 : ℝ) * ‖deriv Bpre.S.d₁.φ cbase‖ * Bpre.CS.ρ - Bpre.δ₁ with hσ₁def
    have hinj1 : Set.InjOn P₁.φ (Metric.ball cbase Bpre.CS.ρ) := htcf.1
    have hcovc : Metric.ball (Bpre.S.d₁.φ cbase) σ₁ ⊆ P₁.φ '' Metric.ball cbase Bpre.CS.ρ :=
      htcf.2.1
    have hsubc' : Metric.ball cbase Bpre.CS.ρ ⊆ P₁.Dφ := htcf.2.2
    have hσ₁pos : 0 < σ₁ := by
      rw [hσ₁def]
      have hX : 0 < (1 / 50 : ℝ) * ‖deriv Bpre.S.d₁.φ cbase‖ * Bpre.CS.ρ :=
        mul_pos (mul_pos (by norm_num) (norm_pos_iff.mpr hderivcbase)) Bpre.CS.hρ
      have h5 : Bpre.δ₁ ≤ (1 / 50 : ℝ) * ‖deriv Bpre.S.d₁.φ cbase‖ * Bpre.CS.ρ / 2 := by
        have h6 : 2 * Bpre.CS.ρ * ‖deriv Bpre.S.d₁.φ cbase‖ / 256
            ≤ (1 / 50 : ℝ) * ‖deriv Bpre.S.d₁.φ cbase‖ * Bpre.CS.ρ / 2 := by
          have hnn : 0 ≤ ‖deriv Bpre.S.d₁.φ cbase‖ * Bpre.CS.ρ :=
            mul_nonneg (norm_nonneg _) (le_of_lt Bpre.CS.hρ)
          linarith
        linarith
      linarith
    have hσ₁ge : (1 / 50 : ℝ) * Bpre.m₁ * Bpre.CS.ρ - Bpre.δ₁ ≤ σ₁ := by
      rw [hσ₁def]; nlinarith [hm₁le, Bpre.CS.hρ]
    have hlip₁ : ∀ u ∈ Metric.closedBall cbase Bpre.CS.ρ, ∀ v ∈ Metric.closedBall cbase Bpre.CS.ρ,
        ‖Bpre.S.d₁.φ u - Bpre.S.d₁.φ v‖ ≤ Bpre.D₁ * ‖u - v‖ :=
      Work.Repel.lipschitz_on_closedBall Bpre.S.d₁.Dφ_open Bpre.S.d₁.φ_holo
        ((Metric.closedBall_subset_closedBall (by linarith [Bpre.CS.hρ]) :
          Metric.closedBall cbase Bpre.CS.ρ ⊆ Metric.closedBall cbase (2 * Bpre.CS.ρ)).trans hsubc)
        hDbound
    have hD1rho : Bpre.D₁ * Bpre.CS.ρ ≤ D / 800 := by
      have hπ4 : Real.pi ≤ 4 := Real.pi_lt_four.le
      have h1 : Bpre.CS.ρ * Bpre.D₁ ≤ (Bpre.r₀ / 2) * Real.pi * D / 8 := by
        have h := Bpre.hCSρD
        rw [show Bpre.r₀ / 2 * Real.pi * ‖MandelDim.piExp Bpre.wt₀‖ * ‖Bpre.S.s₀‖ / 8
            = (Bpre.r₀ / 2) * Real.pi * (‖MandelDim.piExp Bpre.wt₀‖ * ‖Bpre.S.s₀‖) / 8 by ring,
          hDmul] at h
        exact h
      have h2 : (Bpre.r₀ / 2) * Real.pi * D / 8 ≤ D / 800 := by
        have hπr : Bpre.r₀ * Real.pi ≤ 1 / 50 := by
          have h := mul_le_mul Bpre.hr₀le200 hπ4 (le_of_lt Real.pi_pos) (by norm_num)
          linarith [h]
        nlinarith [hπr, hDpos]
      calc Bpre.D₁ * Bpre.CS.ρ = Bpre.CS.ρ * Bpre.D₁ := by ring
        _ ≤ D / 800 := le_trans h1 h2
    have hδ₁D : Bpre.δ₁ ≤ D / (800 * 256) := by
      have h2 : Bpre.δ₁ ≤ Bpre.CS.ρ * Bpre.m₁ / 256 := by
        rw [Bpre.hm₁def]; exact Bpre.hδ₁der
      have h3 : Bpre.CS.ρ * Bpre.m₁ / 256 ≤ Bpre.CS.ρ * Bpre.D₁ / 256 := by
        nlinarith [hm₁D₁, Bpre.CS.hρ]
      have h4 : Bpre.CS.ρ * Bpre.D₁ / 256 ≤ D / (800 * 256) := by
        nlinarith [hD1rho, Bpre.CS.hρ]
      linarith
    have hδD : Bpre.δ₁ + Bpre.D₁ * Bpre.CS.ρ ≤ D / 2 := by
      nlinarith [hD1rho, hδ₁D, hDpos]
    have htgt : ∀ u' ∈ Metric.ball cbase Bpre.CS.ρ,
        ∃ w ∈ Metric.ball Bpre.wt₀ ρ₀, MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ := by
      intro u' hu'
      have hu'K : u' ∈ Bpre.K₂' := hballK u' hu'
      have hu'cl : u' ∈ Metric.closedBall cbase Bpre.CS.ρ := Metric.ball_subset_closedBall hu'
      have hclu : ‖P₁.φ u' - Bpre.S.d₁.φ u'‖ < Bpre.δ₁ := P₁.φ_close u' hu'K
      have hD1 : ‖Bpre.S.d₁.φ u' - Bpre.S.d₁.φ cbase‖ ≤ Bpre.D₁ * Bpre.CS.ρ := by
        have h := hlip₁ u' hu'cl cbase (Metric.mem_closedBall_self (le_of_lt Bpre.CS.hρ))
        have h4 : ‖u' - cbase‖ ≤ Bpre.CS.ρ :=
          le_of_lt (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hu')
        nlinarith [h, h4, Bpre.hD₁pos]
      have hbound : ‖P₁.φ u' / Bpre.S.s₀ - MandelDim.piExp Bpre.wt₀‖
          ≤ (Bpre.δ₁ + Bpre.D₁ * Bpre.CS.ρ) / ‖Bpre.S.s₀‖ := by
        have hspos : 0 < ‖Bpre.S.s₀‖ := Bpre.hs₀pos
        have heq : P₁.φ u' / Bpre.S.s₀ - MandelDim.piExp Bpre.wt₀
            = (P₁.φ u' - Bpre.S.d₁.φ cbase) / Bpre.S.s₀ := by
          rw [hφcbase]
          have hsne : Bpre.S.s₀ ≠ 0 := Bpre.S.hne
          field_simp <;> ring
        rw [heq, norm_div]
        have hnum : ‖P₁.φ u' - Bpre.S.d₁.φ cbase‖ ≤ Bpre.δ₁ + Bpre.D₁ * Bpre.CS.ρ := by
          have h := norm_add_le (P₁.φ u' - Bpre.S.d₁.φ u') (Bpre.S.d₁.φ u' - Bpre.S.d₁.φ cbase)
          have he : (P₁.φ u' - Bpre.S.d₁.φ u') + (Bpre.S.d₁.φ u' - Bpre.S.d₁.φ cbase)
              = P₁.φ u' - Bpre.S.d₁.φ cbase := by ring
          rw [he] at h
          linarith [le_of_lt hclu, hD1]
        exact div_le_div_of_nonneg_right hnum (le_of_lt hspos)
      have hmem : P₁.φ u' / Bpre.S.s₀ ∈
          Metric.ball (MandelDim.piExp Bpre.wt₀) (ρ₀ * ‖deriv MandelDim.piExp Bpre.wt₀‖ / 8) := by
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_le_of_lt hbound hroom
      exact exists_piExp_eq_of_ball hρ₀ (by linarith [Bpre.hr₀le200, hρ₀le]) hmem
    have htgt' : ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀, P₀.φ w ∈ Metric.ball 0 σ₀ →
        Bpre.S.s₀ * MandelDim.piExp w ∈ P₁.φ '' Metric.ball cbase Bpre.CS.ρ := by
      intro w hw hwσ
      have hwσ' : ‖P₀.φ w‖ < σ₀ := by
        have h := Metric.mem_ball.mp hwσ
        rwa [dist_eq_norm, sub_zero] at h
      have hlowP₀ : ∀ z ∈ Metric.ball Bpre.wt₀ ρ₀, Bpre.g₀ / 2 ≤ ‖deriv P₀.φ z‖ := by
        intro z hz
        have h := hP₀lo z hz
        rwa [← Bpre.hg₀def] at h
      have hcφ : ‖P₀.φ Bpre.wt₀‖ < Bpre.δ := by
        have h := P₀.φ_close Bpre.wt₀ (Metric.mem_closedBall_self (by linarith [Bpre.hr₀pos]))
        rwa [Bpre.hφwt₀, sub_zero] at h
      have hd8 := koebe_localize hρ₀ (by linarith [Bpre.hg₀pos]) P₀.φ_holo hsub₀ hinjφ₀
        hlowP₀ hcφ (le_of_lt hσ₀)
      have hd16 : ‖w - Bpre.wt₀‖ ≤ 16 * (σ₀ + Bpre.δ) / Bpre.g₀ := by
        have h := hd8 w hw (le_of_lt hwσ')
        rwa [show (8:ℝ) * (σ₀ + Bpre.δ) / (Bpre.g₀ / 2)
            = 16 * (σ₀ + Bpre.δ) / Bpre.g₀ by ring] at h
      have hdsmall : ‖w - Bpre.wt₀‖ ≤ 1 / (16 * Real.pi) :=
        le_trans hd16 (loc_small Bpre.hg₀pos Bpre.hr₀pos Bpre.hr₀le200 (le_of_lt Bpre.hδpos)
          hσ₀le (by rw [← Bpre.hσLdef]; exact Bpre.hσLbig) Bpre.hδcap)
      have hπb : ‖MandelDim.piExp (w - Bpre.wt₀) - 1‖ ≤ 4 * Real.pi * ‖w - Bpre.wt₀‖ :=
        Work.Repel.piExp_sub_one_bound (e := w - Bpre.wt₀) (δ := ‖w - Bpre.wt₀‖) hdsmall le_rfl
      have hfac : Bpre.S.s₀ * MandelDim.piExp w - Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀
          = Bpre.S.s₀ * (MandelDim.piExp Bpre.wt₀ * (MandelDim.piExp (w - Bpre.wt₀) - 1)) := by
        have h1 : MandelDim.piExp w
            = MandelDim.piExp Bpre.wt₀ * MandelDim.piExp (w - Bpre.wt₀) := by
          rw [← Work.Repel.piExp_add_ball]
          congr 1
          ring
        rw [h1]; ring
      have hdev : ‖Bpre.S.s₀ * MandelDim.piExp w - Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖
          ≤ 64 * Real.pi * D * (σ₀ + Bpre.δ) / Bpre.g₀ := by
        rw [hfac, norm_mul, norm_mul]
        have hAmul : ‖Bpre.S.s₀‖ * (‖MandelDim.piExp Bpre.wt₀‖
            * ‖MandelDim.piExp (w - Bpre.wt₀) - 1‖)
            = D * ‖MandelDim.piExp (w - Bpre.wt₀) - 1‖ := by
          rw [← mul_assoc, hDmul2]
        rw [hAmul]
        calc D * ‖MandelDim.piExp (w - Bpre.wt₀) - 1‖
            ≤ D * (4 * Real.pi * ‖w - Bpre.wt₀‖) :=
              mul_le_mul_of_nonneg_left hπb (le_of_lt hDpos)
          _ ≤ D * (4 * Real.pi * (16 * (σ₀ + Bpre.δ) / Bpre.g₀)) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hDpos)
              nlinarith [hd16, Real.pi_pos, Bpre.hg₀pos]
          _ = 64 * Real.pi * D * (σ₀ + Bpre.δ) / Bpre.g₀ := by ring
      have harith := htgt_arith (D := D) (g := Bpre.g₀) (m := Bpre.m₁) (ρ := Bpre.CS.ρ)
        (η := Bpre.η) (σ₀ := σ₀) (δ := Bpre.δ) (δ₁ := Bpre.δ₁)
        hDpos Bpre.hg₀pos Bpre.hm₁pos Bpre.CS.hρ (le_of_lt Bpre.hδpos) (le_of_lt hσ₀)
        hσ₀le hδsmallD hηtgtD (by rw [Bpre.hm₁def]; exact Bpre.hδ₁der)
      have hlt : ‖Bpre.S.s₀ * MandelDim.piExp w - Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖ < σ₁ :=
        lt_of_lt_of_le (lt_of_le_of_lt hdev harith) hσ₁ge
      have heq : Bpre.S.s₀ * MandelDim.piExp w - Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀
          = Bpre.S.s₀ * MandelDim.piExp w - Bpre.S.d₁.φ cbase := by rw [hφcbase]
      rw [heq] at hlt
      exact hcovc (Metric.mem_ball.mpr (by rwa [dist_eq_norm]))
    have hgeo : ∀ u' ∈ Metric.ball cbase Bpre.CS.ρ, D / 2 ≤ ‖P₁.φ u'‖ := by
      intro u' hu'
      have hu'K : u' ∈ Bpre.K₂' := hballK u' hu'
      have hclu : ‖P₁.φ u' - Bpre.S.d₁.φ u'‖ < Bpre.δ₁ := P₁.φ_close u' hu'K
      have hDeq : ‖Bpre.S.d₁.φ cbase‖ = D := by rw [hφcbase, hDdef]
      have h5 : ‖Bpre.S.d₁.φ cbase - Bpre.S.d₁.φ u'‖ ≤ Bpre.D₁ * Bpre.CS.ρ := by
        have h := hlip₁ u' (Metric.ball_subset_closedBall hu') cbase
          (Metric.mem_closedBall_self (le_of_lt Bpre.CS.hρ))
        rw [norm_sub_rev]
        have h4 : ‖u' - cbase‖ < Bpre.CS.ρ := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hu'
        nlinarith [h, le_of_lt h4, Bpre.hD₁pos]
      have h6 : D - Bpre.D₁ * Bpre.CS.ρ ≤ ‖Bpre.S.d₁.φ u'‖ := by
        have hh : ‖Bpre.S.d₁.φ cbase‖ ≤ ‖Bpre.S.d₁.φ u'‖ + ‖Bpre.S.d₁.φ cbase - Bpre.S.d₁.φ u'‖ := by
          have hn := norm_add_le (Bpre.S.d₁.φ u') (Bpre.S.d₁.φ cbase - Bpre.S.d₁.φ u')
          have he : Bpre.S.d₁.φ u' + (Bpre.S.d₁.φ cbase - Bpre.S.d₁.φ u') = Bpre.S.d₁.φ cbase := by ring
          rwa [he] at hn
        linarith [hh, h5, hDeq]
      have h7 : ‖Bpre.S.d₁.φ u'‖ - Bpre.δ₁ ≤ ‖P₁.φ u'‖ := by
        have hn : ‖Bpre.S.d₁.φ u'‖ ≤ ‖P₁.φ u'‖ + ‖Bpre.S.d₁.φ u' - P₁.φ u'‖ := by
          have hh := norm_add_le (P₁.φ u') (Bpre.S.d₁.φ u' - P₁.φ u')
          have he : P₁.φ u' + (Bpre.S.d₁.φ u' - P₁.φ u') = Bpre.S.d₁.φ u' := by ring
          rwa [he] at hh
        have h8 : ‖Bpre.S.d₁.φ u' - P₁.φ u'‖ ≤ Bpre.δ₁ :=
          le_of_lt (by rw [norm_sub_rev]; exact hclu)
        linarith [hn, h8]
      linarith [h6, h7, hδD]
    have hPreM₀ : ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀, ‖deriv P₀.φ w‖ ≤ Bpre.preM₀ := by
      have hsub : Metric.closedBall Bpre.wt₀ (2 * (Bpre.r₀ / 2)) ⊆ P₀.Dφ := by
        rw [show 2 * (Bpre.r₀ / 2) = Bpre.r₀ by ring]
        exact (Metric.closedBall_subset_closedBall (by linarith [Bpre.hr₀pos])).trans P₀.K'_sub
      have hB : ∀ z ∈ Metric.closedBall Bpre.wt₀ (2 * (Bpre.r₀ / 2)),
          ‖P₀.φ z‖ ≤ Bpre.Bd + Bpre.δb := by
        intro z hz
        rw [show 2 * (Bpre.r₀ / 2) = Bpre.r₀ by ring] at hz
        have hz2 : z ∈ Metric.closedBall Bpre.wt₀ (2 * Bpre.r₀) :=
          Metric.closedBall_subset_closedBall (by linarith [Bpre.hr₀pos]) hz
        have h1 : ‖P₀.φ z - Bpre.S.d₀.φ z‖ ≤ Bpre.δb :=
          le_trans (le_of_lt (P₀.φ_close z hz2)) (by rw [Bpre.hδbdef]; exact Bpre.hδle)
        have h2 : ‖Bpre.S.d₀.φ z‖ ≤ Bpre.Bd :=
          Bpre.hBd z (Metric.closedBall_subset_closedBall (by linarith [Bpre.hr₀pos]) hz)
        have h4 : ‖P₀.φ z‖ = ‖(P₀.φ z - Bpre.S.d₀.φ z) + Bpre.S.d₀.φ z‖ := by ring_nf
        rw [h4]
        linarith [norm_add_le (P₀.φ z - Bpre.S.d₀.φ z) (Bpre.S.d₀.φ z), h1, h2]
      have hb := Work.Repel.deriv_bound_on_ball_explicit P₀.φ_holo (by linarith [Bpre.hr₀pos])
        hsub hB
      intro w hw
      have hw' : w ∈ Metric.closedBall Bpre.wt₀ (Bpre.r₀ / 2) :=
        Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ₀le hw)
      have h := hb w hw'
      rw [Bpre.hpreM₀def]
      exact h
    have hPreM₁ : ∀ u' ∈ Metric.ball cbase Bpre.CS.ρ, ‖deriv P₁.φ u'‖ ≤ Bpre.preM₁ := by
      have hsub : Metric.closedBall cbase (2 * Bpre.CS.ρ) ⊆ P₁.Dφ := hK₂'sub'.trans P₁.K'_sub
      have hB : ∀ z ∈ Metric.closedBall cbase (2 * Bpre.CS.ρ),
          ‖P₁.φ z‖ ≤ Bpre.Bd₁ + Bpre.δ₁ := by
        intro z hz
        have hzK : z ∈ Bpre.K₂' := hK₂'sub' hz
        have h1 : ‖P₁.φ z - Bpre.S.d₁.φ z‖ ≤ Bpre.δ₁ := le_of_lt (P₁.φ_close z hzK)
        have h2 : ‖Bpre.S.d₁.φ z‖ ≤ Bpre.Bd₁ := Bpre.hBd₁ z hzK
        have h4 : ‖P₁.φ z‖ = ‖(P₁.φ z - Bpre.S.d₁.φ z) + Bpre.S.d₁.φ z‖ := by ring_nf
        rw [h4]
        linarith [norm_add_le (P₁.φ z - Bpre.S.d₁.φ z) (Bpre.S.d₁.φ z), h1, h2]
      have hb := Work.Repel.deriv_bound_on_ball_explicit P₁.φ_holo Bpre.CS.hρ hsub hB
      have hδ₁b : Bpre.δ₁ ≤ Bpre.δ₁b := by rw [Bpre.hδ₁bdef]; exact Bpre.hδ₁π
      intro u' hu'
      refine le_trans (hb u' (Metric.ball_subset_closedBall hu')) ?_
      rw [Bpre.hpreM₁def]
      exact div_le_div_of_nonneg_right (max_le_max (by linarith [hδ₁b]) le_rfl)
        (le_of_lt Bpre.CS.hρ)
    have hCbge' : Bpre.preM₀ * Bpre.preM₁ ≤ Bpre.Cb * Real.pi * D := by
      have h := Bpre.hCbge
      have hden : 0 < ‖Bpre.S.s₀‖ * (2 * Real.pi * ‖MandelDim.piExp Bpre.wt₀‖) :=
        mul_pos Bpre.hs₀pos
          (mul_pos (by positivity) (norm_pos_iff.mpr (Work.Horn.MandelDim.piExp_ne_zero Bpre.wt₀)))
      rw [div_le_iff₀ hden] at h
      have hD' : ‖Bpre.S.s₀‖ * (2 * Real.pi * ‖MandelDim.piExp Bpre.wt₀‖) = 2 * Real.pi * D := by
        rw [← hDmul2]; ring
      rw [hD'] at h
      linarith
    have hCbbd : ∀ u' ∈ Metric.ball cbase Bpre.CS.ρ, ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀,
        MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ →
        ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ ≤ Bpre.Cb * ‖Bpre.S.s₀‖ *
          ‖deriv MandelDim.piExp w‖ := by
      intro u' hu' w hw hrel
      have h1 : ‖deriv P₀.φ w‖ ≤ Bpre.preM₀ := hPreM₀ w hw
      have h2 : ‖deriv P₁.φ u'‖ ≤ Bpre.preM₁ := hPreM₁ u' hu'
      have hdw : ‖deriv MandelDim.piExp w‖ = 2 * Real.pi * ‖P₁.φ u'‖ / ‖Bpre.S.s₀‖ := by
        rw [Work.Repel.norm_deriv_piExp w, hrel, norm_div, mul_div_assoc]
      have hge : D ≤ 2 * ‖P₁.φ u'‖ := by
        have h := hgeo u' hu'
        linarith
      calc ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ ≤ Bpre.preM₀ * Bpre.preM₁ :=
            mul_le_mul h1 h2 (norm_nonneg _) (le_of_lt Bpre.hpreM₀pos)
        _ ≤ Bpre.Cb * Real.pi * D := hCbge'
        _ ≤ Bpre.Cb * Real.pi * (2 * ‖P₁.φ u'‖) := by
              exact mul_le_mul_of_nonneg_left hge
                (mul_nonneg (le_of_lt Bpre.hCbpos) (le_of_lt Real.pi_pos))
        _ = Bpre.Cb * ‖Bpre.S.s₀‖ * ‖deriv MandelDim.piExp w‖ := by
              rw [hdw]
              have hsne : ‖Bpre.S.s₀‖ ≠ 0 := ne_of_gt Bpre.hs₀pos
              field_simp <;> ring
    have hcblo : ∀ u' ∈ Metric.ball cbase Bpre.CS.ρ, ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀,
        MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ →
        Bpre.cb * ‖Bpre.S.s₀‖ * ‖deriv MandelDim.piExp w‖ ≤
          ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ := by
      intro u' hu' w hw hrel
      have h1 : Bpre.g₀ / 2 ≤ ‖deriv P₀.φ w‖ := by
        have h := hP₀lo w hw
        rwa [← Bpre.hg₀def] at h
      have hUopen : IsOpen (P₁.Dφ ∩ Bpre.S.d₁.Dφ) := P₁.Dφ_open.inter Bpre.S.d₁.Dφ_open
      have h2 : ‖deriv Bpre.S.d₁.φ cbase‖ / 2 ≤ ‖deriv P₁.φ u'‖ :=
        Work.Repel.R3Level0.deriv_lower_of_close (f := P₁.φ) (g := Bpre.S.d₁.φ)
          (U := P₁.Dφ ∩ Bpre.S.d₁.Dφ) (c := cbase) (r := Bpre.CS.ρ) (δ := Bpre.δ₁)
          hUopen
          (P₁.φ_holo.mono Set.inter_subset_left)
          (Bpre.S.d₁.φ_holo.mono Set.inter_subset_right) Bpre.CS.hρ
          (fun z hz => ⟨P₁.K'_sub (hK₂'sub' (Metric.closedBall_subset_closedBall
              (by linarith [Bpre.CS.hρ]) hz)),
            hsubc (Metric.closedBall_subset_closedBall (by linarith [Bpre.CS.hρ]) hz)⟩)
          (fun z hz => le_of_lt (P₁.φ_close z (hK₂'sub' hz)))
          hderivlowc
          (by
            have h6 : 2 * Bpre.CS.ρ * ‖deriv Bpre.S.d₁.φ cbase‖ / 256
                ≤ Bpre.CS.ρ * ‖deriv Bpre.S.d₁.φ cbase‖ / 8 := by
              nlinarith [norm_nonneg (deriv Bpre.S.d₁.φ cbase), Bpre.CS.hρ]
            linarith)
          u' hu'
      have hdw : ‖deriv MandelDim.piExp w‖ = 2 * Real.pi * ‖P₁.φ u'‖ / ‖Bpre.S.s₀‖ := by
        rw [Work.Repel.norm_deriv_piExp w, hrel, norm_div, mul_div_assoc]
      have hup : ‖P₁.φ u'‖ ≤ 2 * Bpre.B₁ := by
        have hB₁eq : Bpre.B₁ = 2 * D + 1 + Bpre.δ₁b := by
          rw [Bpre.hB₁def, Bpre.hζaφ, ← hDdef]
        have hDeq : ‖Bpre.S.d₁.φ cbase‖ = D := by rw [hφcbase, hDdef]
        have hclu : ‖P₁.φ u' - Bpre.S.d₁.φ u'‖ ≤ Bpre.δ₁ :=
          le_of_lt (P₁.φ_close u' (hballK u' hu'))
        have hnorm := hnormc u' hu'
        have h4 : ‖P₁.φ u'‖ ≤ ‖Bpre.S.d₁.φ u'‖ + ‖P₁.φ u' - Bpre.S.d₁.φ u'‖ := by
          have hh := norm_add_le (Bpre.S.d₁.φ u') (P₁.φ u' - Bpre.S.d₁.φ u')
          have he : Bpre.S.d₁.φ u' + (P₁.φ u' - Bpre.S.d₁.φ u') = P₁.φ u' := by ring
          rwa [he] at hh
        have hδ₁b : Bpre.δ₁ ≤ Bpre.δ₁b := by rw [Bpre.hδ₁bdef]; exact Bpre.hδ₁π
        have hDnn : 0 ≤ D := le_of_lt hDpos
        have hδ₁bnn : 0 ≤ Bpre.δ₁b := le_of_lt Bpre.hδ₁bpos
        rw [hB₁eq]
        linarith [h4, hnorm, hclu, hDeq, hδ₁b, hDnn, hδ₁bnn]
      calc Bpre.cb * ‖Bpre.S.s₀‖ * ‖deriv MandelDim.piExp w‖
          = Bpre.g₀ * Bpre.m₁ * ‖P₁.φ u'‖ / (8 * Bpre.B₁) := by
            rw [hdw, Bpre.hcbdef]
            have hsne : ‖Bpre.S.s₀‖ ≠ 0 := ne_of_gt Bpre.hs₀pos
            field_simp <;> ring
        _ ≤ Bpre.g₀ * Bpre.m₁ / 4 := by
            have h : ‖P₁.φ u'‖ / (8 * Bpre.B₁) ≤ 1 / 4 := by
              rw [div_le_iff₀ (mul_pos (by norm_num) Bpre.hB₁pos)]
              linarith [hup, Bpre.hB₁pos]
            have h2 := mul_le_mul_of_nonneg_left h (le_of_lt (mul_pos Bpre.hg₀pos Bpre.hm₁pos))
            calc Bpre.g₀ * Bpre.m₁ * ‖P₁.φ u'‖ / (8 * Bpre.B₁)
                = Bpre.g₀ * Bpre.m₁ * (‖P₁.φ u'‖ / (8 * Bpre.B₁)) := by ring
              _ ≤ Bpre.g₀ * Bpre.m₁ * (1 / 4) := h2
              _ = Bpre.g₀ * Bpre.m₁ / 4 := by ring
        _ ≤ ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ := by
            have h2' : Bpre.m₁ / 2 ≤ ‖deriv P₁.φ u'‖ := by linarith [h2, hm₁le]
            have hprod : (Bpre.g₀ / 2) * (Bpre.m₁ / 2)
                ≤ ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ :=
              mul_le_mul h1 h2' (by linarith [Bpre.hm₁pos]) (norm_nonneg _)
            linarith [hprod, Bpre.hg₀pos, Bpre.hm₁pos]
    exact ⟨σ₁, hσ₁pos, hK₂'sub', hinj1, hcovc, hsubc', htgt, htgt', hCbbd, hcblo⟩
  -- ## assembly
  rcases hIsChain.base with hb | hb
  · obtain ⟨σ₁, hσ₁, hK, hinj, hcov, hsub, htgt, htgt', hCbbd, hcblo⟩ :=
      hmain Bpre.S.ζa (Or.inl rfl) hb
    have htgtW : ∀ u' ∈ W 0, ∃ w ∈ Metric.ball Bpre.wt₀ ρ₀,
        MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ := fun u' hu' => htgt u' (hb ▸ hu')
    have hCbbdW : ∀ u' ∈ W 0, ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀,
        MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ →
        ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ ≤ Bpre.Cb * ‖Bpre.S.s₀‖ *
          ‖deriv MandelDim.piExp w‖ := fun u' hu' => hCbbd u' (hb ▸ hu')
    have hcbloW : ∀ u' ∈ W 0, ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀,
        MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ →
        Bpre.cb * ‖Bpre.S.s₀‖ * ‖deriv MandelDim.piExp w‖ ≤
          ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ := fun u' hu' => hcblo u' (hb ▸ hu')
    exact ⟨P₁, W, sgn, σ₁, Bpre.S.ζa, Or.inl rfl, hb, hK, hinj, hσ₁, hcov, hsub, hIsChain.sign,
      hIsChain, hanchor, htgtW, htgt', hCbbdW, hcbloW, hfit, hangle₀, hangle₁⟩
  · obtain ⟨σ₁, hσ₁, hK, hinj, hcov, hsub, htgt, htgt', hCbbd, hcblo⟩ :=
      hmain Bpre.S.ζb (Or.inr rfl) hb
    have htgtW : ∀ u' ∈ W 0, ∃ w ∈ Metric.ball Bpre.wt₀ ρ₀,
        MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ := fun u' hu' => htgt u' (hb ▸ hu')
    have hCbbdW : ∀ u' ∈ W 0, ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀,
        MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ →
        ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ ≤ Bpre.Cb * ‖Bpre.S.s₀‖ *
          ‖deriv MandelDim.piExp w‖ := fun u' hu' => hCbbd u' (hb ▸ hu')
    have hcbloW : ∀ u' ∈ W 0, ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀,
        MandelDim.piExp w = P₁.φ u' / Bpre.S.s₀ →
        Bpre.cb * ‖Bpre.S.s₀‖ * ‖deriv MandelDim.piExp w‖ ≤
          ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ := fun u' hu' => hcblo u' (hb ▸ hu')
    exact ⟨P₁, W, sgn, σ₁, Bpre.S.ζb, Or.inr rfl, hb, hK, hinj, hσ₁, hcov, hsub, hIsChain.sign,
      hIsChain, hanchor, htgtW, htgt', hCbbdW, hcbloW, hfit, hangle₀, hangle₁⟩

end
end Work.Repel.R3Level1
