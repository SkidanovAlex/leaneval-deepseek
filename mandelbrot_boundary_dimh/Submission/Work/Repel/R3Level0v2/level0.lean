import Mathlib
import Submission.Work.Repel.R3Pre
import Submission.Work.Repel.R3Level0.deriv_lower_of_close
import Submission.Work.Repel.R3Level0.rotOf_germ1_eq
import Submission.Work.Repel.R3Level0v2.target_control_R
import Submission.Work.Repel.R3Level0v2.level0_arith

open MandelDim Complex Set Metric Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary
open Work.Repel

namespace Work.Repel.R3Level0v2

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

theorem level0 (Bpre : Work.Repel.R3Pre) (a₁ a₂ : ℕ) (ha₁ : Bpre.N₁ ≤ a₁) (ha₂ : Bpre.N₂ ≤ a₂)
    (β : ℂ) (hβre : 0 ≤ β.re) (hβre' : β.re < 1) (hβim : |β.im| ≤ Bpre.b)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (hρ₀le : ρ₀ ≤ Bpre.r₀ / 2)
    (hρ₀big : Bpre.r₀ / 4 + 200 / (Bpre.g₀ * Bpre.η) ≤ ρ₀)
    (hwt₀ : ‖Bpre.wt₀‖ + ρ₀ ≤ 2 * Bpre.η) :
    ∃ (P₀ : MandelDim.PertData Bpre.S.d₀ (Work.Repel.fam (MandelDim.alphaOf a₁ a₂ β)) Set.univ
        Bpre.η Bpre.y₀ Bpre.K (Metric.closedBall Bpre.wt₀ (2 * Bpre.r₀)) Bpre.δ) (σ₀ : ℝ),
      0 < σ₀ ∧ 4 / Bpre.η ≤ σ₀ ∧ σ₀ ≤ 64 / Bpre.η ∧
      Set.InjOn P₀.φ (Metric.ball Bpre.wt₀ ρ₀) ∧
      Metric.ball 0 σ₀ ⊆ P₀.φ '' Metric.ball Bpre.wt₀ ρ₀ ∧
      Metric.ball Bpre.wt₀ ρ₀ ⊆ P₀.Dφ ∧
      Work.Repel.Dflat Bpre.η ⊆ P₀.DR ∧
      (∀ w ∈ Metric.ball Bpre.wt₀ ρ₀,
        ‖deriv Bpre.S.d₀.φ Bpre.wt₀‖ / 2 ≤ ‖deriv P₀.φ w‖) ∧
      MandelDim.NearOn (Work.Repel.g0germ Bpre.S.d₀) (Work.Repel.germ1 Bpre.S.s₀ P₀.R)
        (Work.Repel.Dgerm1 Bpre.S.s₀ P₀.DR) Bpre.L₁ Bpre.δ₁₀ ∧
      MandelDim.rotOf (Work.Repel.germ1 Bpre.S.s₀ P₀.R) = 1 / ((a₂ : ℂ) + β) ∧
      MandelDim.InF1 (MandelDim.rotOf (Work.Repel.germ1 Bpre.S.s₀ P₀.R)) ∧
      MandelDim.InF1 (MandelDim.alphaOf a₁ a₂ β) ∧
      ‖MandelDim.alphaOf a₁ a₂ β‖ ≤ 4 / (a₁ : ℝ) ∧
      (0 : ℝ) < (MandelDim.alphaOf a₁ a₂ β).re ∧
      MandelDim.rotOf (Work.Repel.fam (MandelDim.alphaOf a₁ a₂ β)) = MandelDim.alphaOf a₁ a₂ β ∧
      Work.Repel.fam (MandelDim.alphaOf a₁ a₂ β) 0 = 0 ∧
      ‖Complex.exp (2 * Real.pi * I * (1 / ((a₂ : ℂ) + β))) - 1‖ ≤ 32 / (a₂ : ℝ) ∧
      201 * (Bpre.η + 1) ≤ (a₁ : ℝ) ∧
      17 * Real.exp (2 * Real.pi * Bpre.η) + Bpre.b + 1 ≤ (a₂ : ℝ) ∧
      768 * Bpre.cB / Bpre.δ₁₀ + 1 ≤ (a₂ : ℝ) ∧
      16 * Real.pi * Bpre.M₀ / Bpre.δ₀₀ + 1 ≤ (a₁ : ℝ) := by
  -- ## the `a₁ a₂ β` arithmetic
  have ha₁Na : Bpre.Na ≤ a₁ := le_trans Bpre.hNa_le ha₁
  have ha₂4 : 4 ≤ a₂ := le_trans Bpre.h4_le ha₂
  have ha₁32 : 32 ≤ a₁ := le_trans Bpre.h32_le ha₁
  have ha₁32R : (32 : ℝ) ≤ (a₁ : ℝ) := by exact_mod_cast ha₁32
  have ha₁2 : 2 ≤ a₁ := le_trans (by norm_num : 2 ≤ 32) ha₁32
  have ha₁M : 16 * Real.pi * Bpre.M₀ / Bpre.δ₀₀ + 1 ≤ (a₁ : ℝ) :=
    Nat.ceil_le.mp (le_trans Bpre.hM_le ha₁)
  have ha₁201 : 201 * (Bpre.η + 1) ≤ (a₁ : ℝ) :=
    Nat.ceil_le.mp (le_trans Bpre.h201_le ha₁)
  have ha₂17 : 17 * Real.exp (2 * Real.pi * Bpre.η) + Bpre.b + 1 ≤ (a₂ : ℝ) :=
    Nat.ceil_le.mp (le_trans Bpre.h17_le ha₂)
  have ha₂cB : 768 * Bpre.cB / Bpre.δ₁₀ + 1 ≤ (a₂ : ℝ) :=
    Nat.ceil_le.mp (le_trans Bpre.hcB_le ha₂)
  have ha₂b : Bpre.b < (a₂ : ℝ) := by
    have h := Nat.ceil_le.mp (le_trans Bpre.hb_le ha₂)
    push_cast at h ⊢
    linarith
  have ha₁pos : (0 : ℝ) < (a₁ : ℝ) := by positivity
  have ha₂pos : (0 : ℝ) < (a₂ : ℝ) := by positivity
  obtain ⟨hInF1α, hαnorm, -, -, hexp, -, -⟩ := Bpre.hNa a₁ ha₁Na a₂ ha₂4 β hβre hβre' hβim
  have hα_re_le : (MandelDim.alphaOf a₁ a₂ β).re ≤ 1 / 2 := by
    have h2 : 4 / (a₁ : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ ha₁pos]; linarith [ha₁32R]
    exact le_trans (le_trans (Complex.re_le_norm _) hαnorm) h2
  have hα_1_8 : ‖MandelDim.alphaOf a₁ a₂ β‖ ≤ 1 / 8 := by
    have h2 : 4 / (a₁ : ℝ) ≤ 1 / 8 := by
      rw [div_le_iff₀ ha₁pos]; linarith [ha₁32R]
    exact le_trans hαnorm h2
  have hα_re_pos : 0 < (MandelDim.alphaOf a₁ a₂ β).re := lt_of_le_of_lt (abs_nonneg _) hInF1α
  have hrotfam : MandelDim.rotOf (fam (MandelDim.alphaOf a₁ a₂ β)) = MandelDim.alphaOf a₁ a₂ β :=
    rotOf_fam _ (by linarith [hα_re_pos]) hα_re_le
  have hfam_sub : ∀ z : ℂ, fam (MandelDim.alphaOf a₁ a₂ β) z - f0 z =
      (lam (MandelDim.alphaOf a₁ a₂ β) - 1) * z := by
    intro z; simp only [fam, f0]; ring
  -- ## the level-0 closeness, and `P₀`
  have hNear0 : NearOn f0 (fam (MandelDim.alphaOf a₁ a₂ β)) univ Bpre.L₀ Bpre.δ₀₀ := by
    refine ⟨isOpen_univ, Set.subset_univ _, (differentiable_fam _).differentiableOn, ?_⟩
    intro z hz
    rw [hfam_sub z, norm_mul]
    have h1 : ‖lam (MandelDim.alphaOf a₁ a₂ β) - 1‖ ≤
        4 * Real.pi * ‖MandelDim.alphaOf a₁ a₂ β‖ := lam_sub_one_le hα_1_8
    have h3 : (4 * Real.pi * ‖MandelDim.alphaOf a₁ a₂ β‖) * Bpre.M₀ ≤
        (4 * Real.pi * (4 / (a₁ : ℝ))) * Bpre.M₀ := by
      have h4 := mul_le_mul_of_nonneg_left hαnorm (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
      exact mul_le_mul_of_nonneg_right h4 Bpre.hM₀0
    have h4 : (4 * Real.pi * (4 / (a₁ : ℝ))) * Bpre.M₀ = 16 * Real.pi * Bpre.M₀ / (a₁ : ℝ) := by
      ring
    have h5a : 16 * Real.pi * Bpre.M₀ / Bpre.δ₀₀ ≤ (a₁ : ℝ) - 1 := by linarith [ha₁M]
    have h5b : 16 * Real.pi * Bpre.M₀ ≤ ((a₁ : ℝ) - 1) * Bpre.δ₀₀ := by
      rw [div_le_iff₀ Bpre.hδ₀₀pos] at h5a; linarith [h5a]
    have h5 : 16 * Real.pi * Bpre.M₀ / (a₁ : ℝ) < Bpre.δ₀₀ := by
      rw [div_lt_iff₀ ha₁pos]; nlinarith [h5b, Bpre.hδ₀₀pos, ha₁pos]
    calc ‖lam (MandelDim.alphaOf a₁ a₂ β) - 1‖ * ‖z‖ ≤
          (4 * Real.pi * ‖MandelDim.alphaOf a₁ a₂ β‖) * Bpre.M₀ :=
          mul_le_mul h1 (Bpre.hM₀ z hz) (norm_nonneg _) (by positivity)
      _ ≤ (4 * Real.pi * (4 / (a₁ : ℝ))) * Bpre.M₀ := h3
      _ = 16 * Real.pi * Bpre.M₀ / (a₁ : ℝ) := h4
      _ < Bpre.δ₀₀ := h5
  have hfam0 : fam (MandelDim.alphaOf a₁ a₂ β) 0 = 0 := by simp [fam]
  have hInF1rot : InF1 (MandelDim.rotOf (fam (MandelDim.alphaOf a₁ a₂ β))) := by
    rw [hrotfam]; exact hInF1α
  obtain ⟨P₀⟩ := Bpre.hL0uniq (fam (MandelDim.alphaOf a₁ a₂ β)) univ hNear0 hfam0 hInF1rot
  -- ## the level-0 target control at the GIVEN radius `ρ₀ ∈ [r₀/4 + 200/(g₀η), r₀/2]`
  have hRgt : Bpre.r₀ / 4 < ρ₀ := by
    have h : 0 < 200 / (Bpre.g₀ * Bpre.η) :=
      div_pos (by norm_num) (mul_pos Bpre.hg₀pos Bpre.hηpos)
    linarith [hρ₀big]
  have htcf₀ := target_control_R (d := Bpre.S.d₀) P₀ (c := Bpre.wt₀) (r := Bpre.r₀) (R := ρ₀)
    (K := Bpre.K) (K' := Metric.closedBall Bpre.wt₀ (2 * Bpre.r₀)) (η := Bpre.η) (y₁ := Bpre.y₀)
    (δ := Bpre.δ) Bpre.hr₀pos hRgt hρ₀le Bpre.hderwt
    (Metric.closedBall_subset_closedBall (by linarith)) Bpre.hr₀sub' Bpre.hr₀inj
    (by rw [← Bpre.hg₀def, mul_comm Bpre.r₀ Bpre.g₀]; exact Bpre.hδcap)
  have hinjφ₀ : Set.InjOn P₀.φ (Metric.ball Bpre.wt₀ ρ₀) := htcf₀.1
  have hsub₀ : Metric.ball Bpre.wt₀ ρ₀ ⊆ P₀.Dφ := htcf₀.2.2
  set σch : ℝ := (1 / 50 : ℝ) * Bpre.g₀ * ρ₀ - Bpre.δ with hσchdef
  have hcov₀ : Metric.ball 0 σch ⊆ P₀.φ '' Metric.ball Bpre.wt₀ ρ₀ := by
    have h := htcf₀.2.1
    rwa [← Bpre.hg₀def, Bpre.hφwt₀, ← hσchdef] at h
  have harith := level0_arith (g := Bpre.g₀) (r := Bpre.r₀) (η := Bpre.η) (R := ρ₀)
    (δ := Bpre.δ) Bpre.hg₀pos Bpre.hr₀pos Bpre.hηpos Bpre.hδcap hρ₀big
  have hσchpos : 0 < σch := by rw [hσchdef]; exact harith.1
  have hσchbig : 4 / Bpre.η ≤ σch := by rw [hσchdef]; exact harith.2.1
  set σ₀ : ℝ := min σch (64 / Bpre.η) with hσ₀def
  have hσ₀pos : 0 < σ₀ := by
    rw [hσ₀def]; exact lt_min hσchpos (div_pos (by norm_num) Bpre.hηpos)
  have hσ₀le64 : σ₀ ≤ 64 / Bpre.η := by
    rw [hσ₀def]; exact min_le_right _ _
  have hσ₀big : 4 / Bpre.η ≤ σ₀ := by
    rw [hσ₀def]
    refine le_min hσchbig ?_
    rw [div_le_div_iff_of_pos_right Bpre.hηpos]; norm_num
  have hcov₀' : Metric.ball 0 σ₀ ⊆ P₀.φ '' Metric.ball Bpre.wt₀ ρ₀ :=
    (Metric.ball_subset_ball (by rw [hσ₀def]; exact min_le_left _ _)).trans hcov₀
  have hDflatDR : Dflat Bpre.η ⊆ P₀.DR :=
    fun z hz => P₀.DR_sub (Or.inr (Bpre.hDflat z hz))
  -- ## the derivative does not drop by more than a factor `2` on the source disc
  have hderivlow : ∀ w ∈ Metric.ball Bpre.wt₀ ρ₀,
      ‖deriv Bpre.S.d₀.φ Bpre.wt₀‖ / 2 ≤ ‖deriv P₀.φ w‖ := by
    refine Work.Repel.R3Level0.deriv_lower_of_close (f := P₀.φ) (g := Bpre.S.d₀.φ)
      (U := P₀.Dφ ∩ Bpre.S.d₀.Dφ) (c := Bpre.wt₀) (r := ρ₀) (δ := Bpre.δ)
      (P₀.Dφ_open.inter Bpre.S.d₀.Dφ_open)
      (P₀.φ_holo.mono Set.inter_subset_left) (Bpre.S.d₀.φ_holo.mono Set.inter_subset_right)
      hρ₀ ?_ ?_ ?_ ?_
    · intro z hz
      have hz2 : z ∈ Metric.closedBall Bpre.wt₀ (2 * Bpre.r₀) := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
        linarith [hρ₀le]
      exact ⟨P₀.K'_sub hz2, Bpre.hr₀sub hz2⟩
    · intro z hz
      refine le_of_lt (P₀.φ_close z ?_)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
      linarith [hρ₀le]
    · intro z hz
      exact Bpre.hderivlow₀ z
        (Metric.ball_subset_ball (by linarith [hρ₀le, Bpre.hr₀pos]) hz)
    · rw [← Bpre.hg₀def]
      exact harith.2.2.1
  -- ## the level-1 germ `germ1 s₀ P₀.R` is `NearOn`-close to `g0germ d₀`
  have hgerm1 := germ1_differentiableOn (R := P₀.R) (DR := P₀.DR) (s := Bpre.S.s₀)
    (y := Bpre.y₀) (c := 1 / MandelDim.rotOf (fam (MandelDim.alphaOf a₁ a₂ β)))
    Bpre.S.hne P₀.DR_open P₀.R_equiv P₀.R_holo (fun w hw => P₀.DR_sub (Or.inr hw)) P₀.R_upper
  have hcloselift : ∀ w ∈ Bpre.K ∪ {w : ℂ | Bpre.y₀ ≤ |w.im|},
      ‖P₀.R w + 1 / MandelDim.rotOf (fam (MandelDim.alphaOf a₁ a₂ β)) - Bpre.S.d₀.E w‖ <
        Bpre.δ :=
    fun w hw => P₀.R_close w hw
  have hL₁K : ∀ ζ ∈ Bpre.L₁, ζ ≠ 0 →
      Complex.log (ζ / Bpre.S.s₀) / (2 * Real.pi * I) ∈
        Bpre.K ∪ {w : ℂ | Bpre.y₀ ≤ |w.im|} :=
    fun ζ hζ hζne => (Bpre.hcover ζ hζ hζne).elim Or.inl Or.inr
  have hlevel1 := level1_close (d := Bpre.S.d₀)
    (α := MandelDim.rotOf (fam (MandelDim.alphaOf a₁ a₂ β))) (R := P₀.R) (s := Bpre.S.s₀)
    Bpre.S.hne Bpre.hδle Bpre.hB0 hcloselift Bpre.L₁ hL₁K Bpre.hB
  have hL₁sub2 : Bpre.L₁ ⊆ Dgerm1 Bpre.S.s₀ P₀.DR := by
    intro ζ hζ
    change ζ ∈ (fun ζ => Bpre.S.s₀ * ζ) '' (insert 0 (piExp '' P₀.DR))
    by_cases hζ0 : ζ = 0
    · exact ⟨0, Set.mem_insert_iff.mpr (Or.inl rfl), by rw [hζ0]; ring⟩
    · refine ⟨ζ / Bpre.S.s₀, ?_,
        by show Bpre.S.s₀ * (ζ / Bpre.S.s₀) = ζ; rw [mul_div_cancel₀ ζ Bpre.S.hne]⟩
      refine Set.mem_insert_iff.mpr (Or.inr ⟨Complex.log (ζ / Bpre.S.s₀) / (2 * Real.pi * I),
        ?_, ?_⟩)
      · rcases Bpre.hcover ζ hζ hζ0 with h | h
        · exact P₀.DR_sub (Or.inl h)
        · exact P₀.DR_sub (Or.inr h)
      · exact Work.Horn.MandelDim.piExp_log_div (ζ / Bpre.S.s₀) (div_ne_zero hζ0 Bpre.S.hne)
  have hg0 : g0germ Bpre.S.d₀ = germ1 Bpre.S.s₀ Bpre.S.d₀.E := by
    show germ1 (s0 Bpre.S.d₀) Bpre.S.d₀.E = germ1 Bpre.S.s₀ Bpre.S.d₀.E
    rw [Bpre.S.hs₀]
  set q : ℝ := ‖1 - piExp (-(1 / MandelDim.rotOf (fam (MandelDim.alphaOf a₁ a₂ β))))‖
    with hqdef
  have hqsmall : q ≤ 32 / (a₂ : ℝ) := by
    rw [hqdef, hrotfam, piExp_neg_inv_alphaOf a₁ a₂ β]
    show ‖1 - Complex.exp (2 * Real.pi * I * (1 / ((a₂ : ℂ) + β)))‖ ≤ 32 / (a₂ : ℝ)
    rw [norm_sub_rev]
    exact hexp
  have hstep1 : ‖Bpre.S.s₀‖ * Bpre.B * (8 * q) ≤ Bpre.δ₁₀ / 3 := by
    have h1 : 8 * q ≤ 256 / (a₂ : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hqsmall (by norm_num : (0 : ℝ) ≤ 8)
      rw [show 8 * (32 / (a₂ : ℝ)) = 256 / (a₂ : ℝ) by ring] at h
      exact h
    have h2 : Bpre.cB * (256 / (a₂ : ℝ)) ≤ Bpre.δ₁₀ / 3 := by
      rw [show Bpre.cB * (256 / (a₂ : ℝ)) = 256 * Bpre.cB / (a₂ : ℝ) by ring]
      rw [div_le_iff₀ ha₂pos]
      have h3 : 768 * Bpre.cB ≤ (a₂ : ℝ) * Bpre.δ₁₀ := by
        have h4 : 768 * Bpre.cB / Bpre.δ₁₀ ≤ (a₂ : ℝ) := by linarith [ha₂cB]
        rw [div_le_iff₀ Bpre.hδ₁₀pos] at h4
        linarith [h4]
      linarith [h3]
    rw [show ‖Bpre.S.s₀‖ * Bpre.B * (8 * q) = Bpre.cB * (8 * q) by rw [Bpre.hcBdef]]
    exact le_trans (mul_le_mul_of_nonneg_left h1 Bpre.hcB0) h2
  have hstep2 : ‖Bpre.S.s₀‖ * Bpre.B * (32 * Real.pi * Bpre.δ) ≤ Bpre.δ₁₀ / 3 := by
    have h6 : 32 * Real.pi * Bpre.δ ≤ 32 * Real.pi * (Bpre.δ₁₀ / (4096 * (Bpre.cB + 1))) := by
      have h := mul_le_mul_of_nonneg_left Bpre.hδbd (by positivity : (0 : ℝ) ≤ 32 * Real.pi)
      linarith
    rw [show ‖Bpre.S.s₀‖ * Bpre.B * (32 * Real.pi * Bpre.δ) =
      Bpre.cB * (32 * Real.pi * Bpre.δ) by rw [Bpre.hcBdef]]
    refine le_trans (mul_le_mul_of_nonneg_left h6 Bpre.hcB0) ?_
    rw [show Bpre.cB * (32 * Real.pi * (Bpre.δ₁₀ / (4096 * (Bpre.cB + 1)))) =
      32 * Real.pi * Bpre.cB * Bpre.δ₁₀ / (4096 * (Bpre.cB + 1)) by ring]
    rw [div_le_iff₀ (by linarith [Bpre.hcB0] : (0 : ℝ) < 4096 * (Bpre.cB + 1))]
    have h32 : 32 * Real.pi * Bpre.cB ≤ 4096 * (Bpre.cB + 1) / 3 := by
      nlinarith [Real.pi_lt_four, Bpre.hcB0]
    nlinarith [h32, Bpre.hδ₁₀pos]
  have hbound : ∀ ζ ∈ Bpre.L₁, ‖germ1 Bpre.S.s₀ P₀.R ζ - g0germ Bpre.S.d₀ ζ‖ < Bpre.δ₁₀ := by
    intro ζ hζ
    rw [hg0]
    have h := hlevel1 ζ hζ
    have h7 : ‖Bpre.S.s₀‖ * Bpre.B * (8 * q + 32 * Real.pi * Bpre.δ) < Bpre.δ₁₀ := by
      have hsum : ‖Bpre.S.s₀‖ * Bpre.B * (8 * q) +
          ‖Bpre.S.s₀‖ * Bpre.B * (32 * Real.pi * Bpre.δ) < Bpre.δ₁₀ := by
        have h := add_le_add hstep1 hstep2
        linarith [Bpre.hδ₁₀pos]
      have hdist : ‖Bpre.S.s₀‖ * Bpre.B * (8 * q + 32 * Real.pi * Bpre.δ) =
          ‖Bpre.S.s₀‖ * Bpre.B * (8 * q) +
            ‖Bpre.S.s₀‖ * Bpre.B * (32 * Real.pi * Bpre.δ) := by ring
      rw [hdist]; exact hsum
    rw [hqdef] at h7
    exact lt_of_le_of_lt h h7
  have hNear1 : MandelDim.NearOn (g0germ Bpre.S.d₀) (germ1 Bpre.S.s₀ P₀.R)
      (Dgerm1 Bpre.S.s₀ P₀.DR) Bpre.L₁ Bpre.δ₁₀ :=
    ⟨hgerm1.1, hL₁sub2, hgerm1.2.2.1, hbound⟩
  -- ## the level-1 rotation number
  have hrotgerm : MandelDim.rotOf (germ1 Bpre.S.s₀ P₀.R) = 1 / ((a₂ : ℂ) + β) :=
    Work.Repel.R3Level0.rotOf_germ1_eq Bpre.S.d₀ P₀ a₁ a₂ β Bpre.S.s₀ Bpre.S.hne hrotfam
      ha₁2 ha₂4 hβre hβre'
  have hInF1germ : MandelDim.InF1 (MandelDim.rotOf (germ1 Bpre.S.s₀ P₀.R)) := by
    rw [hrotgerm]
    exact inF1_one_div_add a₂ β Bpre.b (by omega) hβre hβim ha₂b
  exact ⟨P₀, σ₀, hσ₀pos, hσ₀big, hσ₀le64, hinjφ₀, hcov₀', hsub₀, hDflatDR, hderivlow,
    hNear1, hrotgerm, hInF1germ, hInF1α, hαnorm, hα_re_pos, hrotfam, hfam0, hexp, ha₁201,
    ha₂17, ha₂cB, ha₁M⟩

end

end Work.Repel.R3Level0v2
