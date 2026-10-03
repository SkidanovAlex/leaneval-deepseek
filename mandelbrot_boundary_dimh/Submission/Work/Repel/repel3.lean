import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.R3Pre
import Submission.Work.Repel.R3Glue
import Submission.Work.Repel.chain_returns_v10
import Submission.Work.Repel.R3Level0v2.level0
import Submission.Work.Repel.R3Level1.level1

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary
open scoped _root_.Topology

noncomputable section

set_option linter.unusedVariables false

theorem repel3 : RepelStatement := by
  intro hParab hPert hHorn hL61 hL62 hF0
  intro ε hε b hb
  obtain ⟨Bpre, hεeq, hbeq⟩ := r3_prelude hParab hPert hHorn hL61 hL62 hF0 ε hε b hb
  have hs₀pos : 0 < ‖Bpre.S.s₀‖ := Bpre.hs₀pos
  refine ⟨Bpre.N₁, Bpre.N₂, ?_⟩
  intro a₁ a₂ ha₁ ha₂ β hβre hβre' hβim
  have hβim' : |β.im| ≤ Bpre.b := by rw [hbeq]; exact hβim
  have hΓ' : ∀ η N K : ℝ, Bpre.Γ ≤ η →
      Bpre.γc * η * (Real.exp (2 * Real.pi * η)) ^ 2 ≤ N →
      K ≤ Bpre.Cconst * η ^ 2 * Real.exp (2 * Real.pi * η) → 1 < K →
      2 - ε ≤ Real.log N / Real.log K := by
    intro η N K h1 h2 h3 h4
    rw [← hεeq]
    exact Bpre.hΓ η N K h1 h2 h3 h4
  have ha₂4 : 4 ≤ a₂ := le_trans Bpre.h4_le ha₂
  have ha₁32 : 32 ≤ a₁ := le_trans Bpre.h32_le ha₁
  have hNaa₁ : Bpre.Na ≤ a₁ := le_trans Bpre.hNa_le ha₁
  have hxa : |((1 : ℂ) / ((a₂ : ℂ) + β)).re| ≤ 1 / 2 :=
    (Bpre.hNa a₁ hNaa₁ a₂ ha₂4 β hβre hβre' hβim').2.2.2.1
  have hρ₀pos : (0 : ℝ) < Bpre.r₀ / 2 := by linarith [Bpre.hr₀pos]
  have hρ₀big : Bpre.r₀ / 4 + 200 / (Bpre.g₀ * Bpre.η) ≤ Bpre.r₀ / 2 := by
    have h2 : 4 / Bpre.η ≤ Bpre.g₀ * Bpre.r₀ / 256 := by
      rw [← Bpre.hσLdef]; exact Bpre.hσLbig
    have hη : 0 < Bpre.η := Bpre.hηpos
    have hg : 0 < Bpre.g₀ := Bpre.hg₀pos
    have hr : 0 < Bpre.r₀ := Bpre.hr₀pos
    have h3 : 800 ≤ Bpre.g₀ * Bpre.r₀ * Bpre.η := by
      rw [div_le_iff₀ hη] at h2
      nlinarith [h2, hg, hr]
    have h4 : 200 / (Bpre.g₀ * Bpre.η) ≤ Bpre.r₀ / 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < Bpre.g₀ * Bpre.η)]
      nlinarith [h3, hg, hr, hη]
    linarith
  have hπpos : 0 < ‖MandelDim.piExp Bpre.wt₀‖ :=
    norm_pos_iff.mpr (Work.Horn.MandelDim.piExp_ne_zero Bpre.wt₀)
  have hroom : (Bpre.δ₁ + Bpre.D₁ * Bpre.CS.ρ) / ‖Bpre.S.s₀‖ <
      (Bpre.r₀ / 2) * ‖deriv MandelDim.piExp Bpre.wt₀‖ / 8 := by
    have hspos : 0 < ‖Bpre.S.s₀‖ := Bpre.hs₀pos
    have hderiv : ‖deriv MandelDim.piExp Bpre.wt₀‖ =
        2 * Real.pi * ‖MandelDim.piExp Bpre.wt₀‖ := norm_deriv_piExp Bpre.wt₀
    rw [hderiv, div_lt_iff₀ hspos]
    have h1 : Bpre.D₁ * Bpre.CS.ρ ≤
        Bpre.r₀ / 2 * Real.pi * ‖MandelDim.piExp Bpre.wt₀‖ * ‖Bpre.S.s₀‖ / 8 := by
      have h := Bpre.hCSρD
      linarith
    have h2 : Bpre.δ₁ ≤
        Bpre.r₀ / 2 * Real.pi * ‖MandelDim.piExp Bpre.wt₀‖ * ‖Bpre.S.s₀‖ / 16 := Bpre.hδ₁π
    have h3 : (0 : ℝ) < Bpre.r₀ / 2 * Real.pi * ‖MandelDim.piExp Bpre.wt₀‖ * ‖Bpre.S.s₀‖ := by
      have hA : (0 : ℝ) < Bpre.r₀ := Bpre.hr₀pos
      positivity
    nlinarith [h1, h2, h3]
  obtain ⟨P₀, σ₀, hσ₀pos, hσ₀big, hσ₀le, hinjφ₀, hcov₀, hsub₀, hDflatDR, hP₀lo, hNear1,
    hrotgerm, hInF1germ, hInF1α, hαnorm, hαre, hrotfam, hfam0, hexp, h201, h17, hcB, hM₀'⟩ :=
    R3Level0v2.level0 Bpre a₁ a₂ ha₁ ha₂ β hβre hβre' hβim' (Bpre.r₀ / 2) hρ₀pos (le_refl _) hρ₀big Bpre.hηwt
  have ha₁201 : 201 * (Bpre.η + 1) ≤ (a₁ : ℝ) := h201
  have ha₂17 : 17 * Real.exp (2 * Real.pi * Bpre.η) + Bpre.b + 1 ≤ (a₂ : ℝ) := h17
  have ha₂η : 8 * Bpre.η₁ + 1 ≤ (a₂ : ℝ) :=
    Nat.ceil_le.mp (le_trans Bpre.hN₂η ha₂)
  obtain ⟨P₁, W, sgn, σ₁, cbase, hcb, hbase, hK₂'sub, hinjφ₁, hσ₁, hcov₁, hsub₁, hsgn, hIsChain,
    hanchor, htgt, htgt', hCbbd, hcblo, hfit, hangle₀, hangle₁⟩ :=
    R3Level1.level1 Bpre a₁ a₂ β P₀ (Bpre.r₀ / 2) σ₀ hρ₀pos (le_refl _) hσ₀pos hσ₀big hσ₀le Bpre.hηwt
      hinjφ₀ hcov₀ hsub₀ hDflatDR hP₀lo hNear1 hrotgerm hInF1germ hrotfam hexp ha₁201 ha₂17 ha₂η hcB hM₀'
      hβre hβre' hβim' hNaa₁ hxa hαre hroom Bpre.hδsmall Bpre.hηtgt
  have hC₀pos : 0 < Bpre.CS.C₀ := by
    obtain ⟨u, -, u', -, hd⟩ := hIsChain.close 0
    linarith [norm_nonneg (u - u')]
  have hC₁'pos : 0 < Bpre.CS.C₁' := by
    obtain ⟨z, hz⟩ : ∃ z, z ∈ W 0 := by
      rcases hIsChain.base with hb0 | hb0
      · exact ⟨Bpre.S.ζa, by rw [hb0]; exact Metric.mem_ball_self Bpre.CS.hρ⟩
      · exact ⟨Bpre.S.ζb, by rw [hb0]; exact Metric.mem_ball_self Bpre.CS.hρ⟩
    have h := hIsChain.deriv_bd 0 z hz
    linarith [h.1, Bpre.CS.hC₁]
  have hcbase : ‖cbase‖ + Bpre.CS.ρ ≤ Bpre.η₁ / 2 := by
    have h1 : ‖cbase‖ ≤ max ‖Bpre.S.ζa‖ ‖Bpre.S.ζb‖ := by
      rcases hcb with h | h
      · rw [h]; exact le_max_left _ _
      · rw [h]; exact le_max_right _ _
    linarith [Bpre.hη₁big]
  obtain ⟨p, r, Kc, hr, hp, RD, hNlink, hKc⟩ :=
    chain_returns_v10 Bpre.S.d₀ Bpre.S.hd₀ (fam (alphaOf a₁ a₂ β)) (differentiable_fam _)
      Bpre.η Bpre.y₀ Bpre.K (Metric.closedBall Bpre.wt₀ (2 * Bpre.r₀)) Bpre.δ P₀ Bpre.wt₀
      Bpre.hφwt₀ Bpre.r₀ Bpre.hr₀pos rfl
      (Bpre.r₀ / 2) σ₀ hρ₀pos (by linarith [Bpre.hr₀le200]) hσ₀pos hσ₀big Bpre.hηwt
      hinjφ₀ hcov₀ hsub₀ hDflatDR
      Bpre.S.s₀ Bpre.S.hne Bpre.η₁ Bpre.CS.y₁ Bpre.CS.K₂ Bpre.K₂' Bpre.δ₁ Bpre.S.d₁ P₁
      (fun w => P₁.R w + 1 / MandelDim.rotOf (germ1 Bpre.S.s₀ P₀.R)) P₁.DR β Bpre.S.ζa Bpre.S.ζb
      Bpre.CS.ρ sgn Bpre.CS.C₀ Bpre.CS.C₁ Bpre.CS.C₁' W Bpre.b Bpre.hb
      rfl ⟨a₂, by omega, by rw [hrotgerm]; simp only [one_div, inv_inv]; ring⟩
      hβre hβre' hβim' P₁.DR_open (isTEquivariantOn_add_const _ P₁.R_equiv)
      (P₁.R_holo.add_const _) (fun _ h => h) hIsChain hanchor hC₀pos Bpre.CS.hC₁ hC₁'pos
      Bpre.hη100 Bpre.hη₁mul Bpre.hsize cbase hbase hK₂'sub σ₁ hσ₁ hinjφ₁ hcov₁ hsub₁ hcbase
      htgt' htgt Bpre.Cb Bpre.hCbpos hCbbd Bpre.cb Bpre.hcbpos hcblo Bpre.hfitlo hfit hangle₀ hangle₁
  have hNge : Bpre.γc * Bpre.η * (Real.exp (2 * Real.pi * Bpre.η)) ^ 2 ≤ (RD.N : ℝ) := by
    have hmax : max Bpre.CS.C₀ 0 + 1 = Bpre.CS.C₀ + 1 := by
      rw [max_eq_left (le_of_lt hC₀pos)]
    have hkey : Bpre.η * Bpre.η₁ ^ 2 / (320 * (Bpre.CS.C₀ + 1)) =
        Bpre.γc * Bpre.η * (Real.exp (2 * Real.pi * Bpre.η)) ^ 2 := by
      rw [Bpre.hγcdef, hmax]
      have h1 : Bpre.η₁ ^ 2 * ‖Bpre.S.s₀‖ ^ 2 = (Real.exp (2 * Real.pi * Bpre.η)) ^ 2 := by
        rw [show Bpre.η₁ ^ 2 * ‖Bpre.S.s₀‖ ^ 2 = (Bpre.η₁ * ‖Bpre.S.s₀‖) ^ 2 by ring,
          Bpre.hη₁mul]
      rw [show (1 / (320 * (Bpre.CS.C₀ + 1) * ‖Bpre.S.s₀‖ ^ 2)) * Bpre.η *
            (Real.exp (2 * Real.pi * Bpre.η)) ^ 2
          = Bpre.η * (Real.exp (2 * Real.pi * Bpre.η)) ^ 2 /
              (320 * (Bpre.CS.C₀ + 1) * ‖Bpre.S.s₀‖ ^ 2) by ring]
      rw [show Bpre.η * Bpre.η₁ ^ 2 / (320 * (Bpre.CS.C₀ + 1))
          = Bpre.η * (Bpre.η₁ ^ 2 * ‖Bpre.S.s₀‖ ^ 2) /
              (320 * (Bpre.CS.C₀ + 1) * ‖Bpre.S.s₀‖ ^ 2) by
            field_simp]
      rw [h1]
    rw [← hkey]
    exact hNlink
  have hKge : max Kc 2 ≤ Bpre.Cconst * Bpre.η ^ 2 * Real.exp (2 * Real.pi * Bpre.η) := by
    rw [Bpre.hCconstdef]
    exact kc_bound_arith hKc Bpre.hη₁mul Bpre.hs₀pos Bpre.hCbpos (by linarith [Bpre.hη100])
  exact r3_glue (alphaOf a₁ a₂ β) ε Bpre.γc Bpre.Cconst hε Bpre.Γ hΓ' Bpre.η Bpre.hΓle RD hr
    hNge hKge
end

end Work.Repel
