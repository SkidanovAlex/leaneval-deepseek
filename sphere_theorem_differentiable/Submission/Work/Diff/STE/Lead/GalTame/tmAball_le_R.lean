import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.tmA_props
import Submission.Work.Diff.STE.Lead.GalTame.cutEnergyLeibnizOnSupport
import Submission.Work.Diff.STE.Lead.GalTame.CoeffKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

set_option maxHeartbeats 4000000

/-- A continuous function on `Fin n → ℝ` is integrable on any ball (the ball is contained in a
compact cube). -/
private lemma tmA_integrableOn_ball {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) (R : ℝ) :
    MeasureTheory.IntegrableOn f (Metric.ball (0 : Fin n → ℝ) R) MeasureTheory.volume := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-|R|) |R|)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine (ContinuousOn.integrableOn_compact hK hf.continuousOn).mono_set ?_
  intro z hz
  simp only [Metric.mem_ball, dist_zero_right, Set.mem_pi, Set.mem_univ, true_implies] at hz ⊢
  intro i
  exact abs_le.mp (le_trans (norm_le_pi_norm z i) (le_trans (le_of_lt hz) (le_abs_self R)))

/-- The `0`-th iterated partial derivative is the function itself. -/
private lemma tmA_pdVec_zero {n : ℕ} (γ : Fin 0 → Fin n) (f : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pdVec 0 γ f = f := by
  simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]

/-- **Subtracting a constant costs only the `L²`-mass of the constant.**  For a smooth
`g : (Fin n → ℝ) → ℂ`, a constant `c₀` and `R ≤ 1/2`, the sum of the `L²`-norms of all iterated
partial derivatives of `g - c₀` of order `≤ m` is bounded by a constant (depending on `n`, `m`,
`lam'` only) times `1 +` the same sum for `g`.  Only the order-`0` term is affected: differentiating
kills the constant, and the order-`0` term is controlled by
`‖g z - c₀‖² ≤ 2‖g z‖² + 2c₀²` together with the finiteness of `volume (ball 0 (1/2))`. -/
private lemma tmA_sub_const_energy {n : ℕ} (m : ℕ) (lam' : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (R : ℝ) (hR : R ≤ 1 / 2) (c₀ : ℝ) (hc₀ : |c₀| ≤ |lam'|)
        (g : (Fin n → ℝ) → ℂ)
        (hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g),
        ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ∫ z in Metric.ball (0 : Fin n → ℝ) R,
            ‖Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => g y - ((c₀ : ℝ) : ℂ)) z‖ ^ 2
        ≤ K * (1 + ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ∫ z in Metric.ball (0 : Fin n → ℝ) R,
            ‖Work.Diff.STE.pdVec j γ g z‖ ^ 2) := by
  classical
  set V : ℝ := (MeasureTheory.volume (Metric.ball (0 : Fin n → ℝ) (1 / 2))).toReal with hVdef
  set C' : ℝ := 2 + 2 * lam' ^ 2 * V with hC'def
  set Nt : ℝ := ∑ j ∈ Finset.range (m + 1), ∑ _γ : Fin j → Fin n, (1 : ℝ) with hNtdef
  have hV0 : 0 ≤ V := by rw [hVdef]; exact ENNReal.toReal_nonneg
  have hCV : 0 ≤ 2 * lam' ^ 2 * V :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg lam')) hV0
  have hC'0 : 0 ≤ C' := by rw [hC'def]; linarith
  have hC'1 : 1 ≤ C' := by rw [hC'def]; linarith
  have hNt1 : 1 ≤ Nt := by
    rw [hNtdef]
    have h0mem : (0 : ℕ) ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.succ_pos m)
    have hsingle := Finset.single_le_sum
      (f := fun j : ℕ => ∑ _γ : Fin j → Fin n, (1 : ℝ))
      (fun j _ => Finset.sum_nonneg (fun _ _ => by norm_num)) h0mem
    have hz : (∑ _γ : Fin 0 → Fin n, (1 : ℝ)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin]
      norm_num
    linarith
  have hNt0 : 0 ≤ Nt := le_trans (by norm_num) hNt1
  refine ⟨Nt * C', mul_nonneg hNt0 hC'0, ?_⟩
  intro R hR c₀ hc₀ g hg
  set T : ℝ := ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
      ∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖Work.Diff.STE.pdVec j γ g z‖ ^ 2 with hTdef
  have hI0 : ∀ (j : ℕ) (γ : Fin j → Fin n),
      0 ≤ ∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖Work.Diff.STE.pdVec j γ g z‖ ^ 2 :=
    fun j γ => MeasureTheory.setIntegral_nonneg Metric.isOpen_ball.measurableSet
      (fun z _ => sq_nonneg _)
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun γ _ => hI0 j γ))
  have hIT : ∀ (j : ℕ) (hj : j ≤ m) (γ : Fin j → Fin n),
      (∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖Work.Diff.STE.pdVec j γ g z‖ ^ 2) ≤ T := by
    intro j hj γ
    rw [hTdef]
    refine le_trans
      (Finset.single_le_sum (f := fun γ : Fin j → Fin n =>
          ∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖Work.Diff.STE.pdVec j γ g z‖ ^ 2)
        (fun γ _ => hI0 j γ) (Finset.mem_univ γ)) ?_
    refine Finset.single_le_sum
      (f := fun j : ℕ => ∑ γ : Fin j → Fin n,
        ∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖Work.Diff.STE.pdVec j γ g z‖ ^ 2)
      (fun j _ => Finset.sum_nonneg (fun γ _ => hI0 j γ)) ?_
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hVle : (MeasureTheory.volume (Metric.ball (0 : Fin n → ℝ) R)).toReal ≤ V := by
    rw [hVdef]
    exact ENNReal.toReal_mono
      (MeasureTheory.measure_ball_lt_top (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))) (x := 0)
        (r := 1 / 2)).ne
      (MeasureTheory.measure_mono (Metric.ball_subset_ball hR))
  -- the per-term bound
  have hterm : ∀ (j : ℕ) (hj : j ≤ m) (γ : Fin j → Fin n),
      (∫ z in Metric.ball (0 : Fin n → ℝ) R,
          ‖Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => g y - ((c₀ : ℝ) : ℂ)) z‖ ^ 2)
        ≤ C' * (1 + T) := by
    intro j hj γ
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      rw [tmA_pdVec_zero γ (fun y : Fin n → ℝ => g y - ((c₀ : ℝ) : ℂ))]
      have hpt : ∀ z : Fin n → ℝ, ‖g z - ((c₀ : ℝ) : ℂ)‖ ^ 2 ≤ 2 * ‖g z‖ ^ 2 + 2 * lam' ^ 2 := by
        intro z
        have h2 : ‖((c₀ : ℝ) : ℂ)‖ ^ 2 ≤ lam' ^ 2 := by
          have h3 : ‖((c₀ : ℝ) : ℂ)‖ ≤ |lam'| := by
            rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
            exact hc₀
          have h4 := pow_le_pow_left₀ (norm_nonneg ((c₀ : ℝ) : ℂ)) h3 2
          rwa [sq_abs] at h4
        linarith [Kit.normSq_sub_le (g z) ((c₀ : ℝ) : ℂ), h2]
      have hInt1 : MeasureTheory.IntegrableOn (fun z : Fin n → ℝ => ‖g z - ((c₀ : ℝ) : ℂ)‖ ^ 2)
          (Metric.ball (0 : Fin n → ℝ) R) MeasureTheory.volume :=
        tmA_integrableOn_ball ((hg.continuous.sub continuous_const).norm.pow 2) R
      have hInt2 : MeasureTheory.IntegrableOn (fun z : Fin n → ℝ => 2 * ‖g z‖ ^ 2 + 2 * lam' ^ 2)
          (Metric.ball (0 : Fin n → ℝ) R) MeasureTheory.volume :=
        tmA_integrableOn_ball ((((hg.continuous.norm).pow 2).const_mul 2).add continuous_const) R
      have hmono := MeasureTheory.setIntegral_mono_on hInt1 hInt2
        Metric.isOpen_ball.measurableSet (fun z _ => hpt z)
      have hA : MeasureTheory.Integrable (fun z : Fin n → ℝ => 2 * ‖g z‖ ^ 2)
          (MeasureTheory.volume.restrict (Metric.ball (0 : Fin n → ℝ) R)) :=
        tmA_integrableOn_ball (((hg.continuous.norm).pow 2).const_mul 2) R
      have hB : MeasureTheory.Integrable (fun _ : Fin n → ℝ => 2 * lam' ^ 2)
          (MeasureTheory.volume.restrict (Metric.ball (0 : Fin n → ℝ) R)) :=
        tmA_integrableOn_ball continuous_const R
      have hval : ∫ z in Metric.ball (0 : Fin n → ℝ) R, (2 * ‖g z‖ ^ 2 + 2 * lam' ^ 2)
          = 2 * (∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖g z‖ ^ 2)
            + (MeasureTheory.volume (Metric.ball (0 : Fin n → ℝ) R)).toReal * (2 * lam' ^ 2) := by
        rw [MeasureTheory.integral_add hA hB, MeasureTheory.integral_const_mul,
          MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def]
      have hstep : (MeasureTheory.volume (Metric.ball (0 : Fin n → ℝ) R)).toReal * (2 * lam' ^ 2)
          ≤ 2 * lam' ^ 2 * V := by
        calc (MeasureTheory.volume (Metric.ball (0 : Fin n → ℝ) R)).toReal * (2 * lam' ^ 2)
            ≤ V * (2 * lam' ^ 2) :=
              mul_le_mul_of_nonneg_right hVle (mul_nonneg (by norm_num) (sq_nonneg lam'))
          _ = 2 * lam' ^ 2 * V := by ring
      have hle : ∫ z in Metric.ball (0 : Fin n → ℝ) R, (2 * ‖g z‖ ^ 2 + 2 * lam' ^ 2)
          ≤ 2 * (∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖g z‖ ^ 2) + 2 * lam' ^ 2 * V := by
        rw [hval]
        linarith [hstep]
      have hJT : (∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖g z‖ ^ 2) ≤ T := by
        have h0 := hIT 0 (Nat.zero_le m) (fun i : Fin 0 => i.elim0)
        rwa [tmA_pdVec_zero (fun i : Fin 0 => i.elim0) g] at h0
      refine le_trans (le_trans hmono hle) ?_
      rw [hC'def]
      calc 2 * (∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖g z‖ ^ 2) + 2 * lam' ^ 2 * V
          ≤ 2 * T + 2 * lam' ^ 2 * V := by linarith [hJT]
        _ ≤ (2 + 2 * lam' ^ 2 * V) * (1 + T) := by
            have h2T : 2 * T ≤ (2 + 2 * lam' ^ 2 * V) * T := by
              refine mul_le_mul_of_nonneg_right ?_ hT0
              linarith [hCV]
            have h3 : 2 * lam' ^ 2 * V ≤ (2 + 2 * lam' ^ 2 * V) * 1 := by
              calc 2 * lam' ^ 2 * V ≤ 2 + 2 * lam' ^ 2 * V := by linarith [hCV]
                _ = (2 + 2 * lam' ^ 2 * V) * 1 := by ring
            calc 2 * T + 2 * lam' ^ 2 * V
                ≤ (2 + 2 * lam' ^ 2 * V) * T + (2 + 2 * lam' ^ 2 * V) * 1 :=
                  add_le_add h2T h3
              _ = (2 + 2 * lam' ^ 2 * V) * (1 + T) := by ring
    · have hff : (fun y : Fin n → ℝ => g y - ((c₀ : ℝ) : ℂ))
          = fun y : Fin n → ℝ => (-((c₀ : ℝ) : ℂ)) + g y := by
        funext y; ring
      rw [hff, Kit.pdVec_const_add hpos γ (-((c₀ : ℝ) : ℂ)) g]
      have h1 : (∫ z in Metric.ball (0 : Fin n → ℝ) R,
          ‖Work.Diff.STE.pdVec j γ g z‖ ^ 2) ≤ 1 + T := by
        linarith [hIT j hj γ]
      refine le_trans h1 ?_
      have h1T : 0 ≤ 1 + T := by linarith
      calc 1 + T = 1 * (1 + T) := by ring
        _ ≤ C' * (1 + T) := mul_le_mul_of_nonneg_right hC'1 h1T
  have hsum_le : (∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
        ∫ z in Metric.ball (0 : Fin n → ℝ) R,
          ‖Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => g y - ((c₀ : ℝ) : ℂ)) z‖ ^ 2)
      ≤ ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n, C' * (1 + T) :=
    Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun γ _ =>
      hterm j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) γ))
  have hconst : (∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n, C' * (1 + T))
      = Nt * (C' * (1 + T)) := by
    have h_inner : ∀ j : ℕ, (∑ γ : Fin j → Fin n, C' * (1 + T))
        = (∑ _γ : Fin j → Fin n, (1 : ℝ)) * (C' * (1 + T)) := by
      intro j
      rw [Finset.sum_mul]
      simp
    simp_rw [h_inner]
    rw [hNtdef]
    rw [← Finset.sum_mul]
  calc (∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
        ∫ z in Metric.ball (0 : Fin n → ℝ) R,
          ‖Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => g y - ((c₀ : ℝ) : ℂ)) z‖ ^ 2)
      ≤ ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n, C' * (1 + T) := hsum_le
    _ = Nt * (C' * (1 + T)) := hconst
    _ = (Nt * C') * (1 + T) := by ring

theorem tmAball_le_R {n : ℕ} (m : ℕ) (Mφ lam' : ℝ) (hMφ : 0 ≤ Mφ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (R : ℝ) (hR : 0 < R) (hR2 : R ≤ 1 / 2)
        (φ : (Fin n → ℝ) → ℝ)
        (hφ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ)
        (hφ0 : ∀ z : Fin n → ℝ, 0 ≤ φ z)
        (hφ1 : ∀ z : Fin n → ℝ, φ z ≤ 1)
        (hφd : ∀ (r : ℕ), r ≤ m → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
          |Work.Diff.STE.pdRVec r γ φ z| ≤ Mφ)
        (hφts : tsupport φ ⊆ Metric.ball 0 R)
        (Γ : (Fin n → ℝ) → Fin n → Fin n → ℝ)
        (hΓ : ∀ p q : Fin n, ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
          (fun z : Fin n → ℝ => Γ z p q))
        (p q : Fin n) (β : Fin m → Fin n),
        ∫ z in Metric.ball 0 R,
            ‖Work.Diff.STE.pdVec m β
              (fun z : Fin n → ℝ => ((Work.Diff.STE.B3.gm φ Γ lam' p q z : ℝ) : ℂ)) z‖ ^ 2
          ≤ K * (1 + ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
              ∫ z in Metric.ball 0 R,
                ‖Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => ((Γ y p q : ℝ) : ℂ)) z‖ ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := Work.Diff.STE.Lead.GalTame.cutEnergyLeibnizOnSupport (n := n) m
  obtain ⟨Ka, hKa0, hKa⟩ := tmA_sub_const_energy (n := n) m lam'
  refine ⟨C * Mφ ^ 2 * Ka, mul_nonneg (mul_nonneg hC0 (sq_nonneg Mφ)) hKa0, ?_⟩
  intro R hR hR2 φ hφ hφ0 hφ1 hφd hφts Γ hΓ p q β
  have hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y : Fin n → ℝ => ((Γ y p q : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hΓ p q)
  set F : (Fin n → ℝ) → ℂ :=
    fun y => ((Γ y p q : ℝ) : ℂ) - (((if p = q then lam' else 0) : ℝ) : ℂ) with hFdef
  have hF : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) F := by
    rw [hFdef]; exact hg.sub contDiff_const
  have hsupp : Function.support (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * F z)
      ⊆ Metric.ball 0 R := by
    intro z hz
    have hzφ : φ z ≠ 0 := by intro h0; exact hz (by simp [h0])
    exact hφts (subset_tsupport φ (Function.mem_support.mpr hzφ))
  have hmain := hC φ F Mφ R hφ hF hφd hsupp hR2 β
  have hid : (fun z : Fin n → ℝ => ((Work.Diff.STE.B3.gm φ Γ lam' p q z : ℝ) : ℂ))
      = fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * F z := by
    funext z
    simp only [hFdef, Work.Diff.STE.B3.gm]
    push_cast
    ring
  rw [hid]
  have hcomp : (∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
        ∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖Work.Diff.STE.pdVec j γ F z‖ ^ 2)
      ≤ Ka * (1 + ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
        ∫ z in Metric.ball (0 : Fin n → ℝ) R,
          ‖Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => ((Γ y p q : ℝ) : ℂ)) z‖ ^ 2) := by
    have hk := hKa R hR2 (if p = q then lam' else 0)
      (by split_ifs with h
          · rfl
          · simpa using abs_nonneg lam')
      (fun y : Fin n → ℝ => ((Γ y p q : ℝ) : ℂ)) hg
    rw [hFdef]
    exact hk
  refine le_trans hmain ?_
  have hA : 0 ≤ C * Mφ ^ 2 := mul_nonneg hC0 (sq_nonneg Mφ)
  calc C * Mφ ^ 2 * (∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
        ∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖Work.Diff.STE.pdVec j γ F z‖ ^ 2)
      ≤ C * Mφ ^ 2 * (Ka * (1 + ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ∫ z in Metric.ball (0 : Fin n → ℝ) R,
            ‖Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => ((Γ y p q : ℝ) : ℂ)) z‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hcomp hA
    _ = C * Mφ ^ 2 * Ka * (1 + ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ∫ z in Metric.ball (0 : Fin n → ℝ) R,
            ‖Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => ((Γ y p q : ℝ) : ℂ)) z‖ ^ 2) := by
        conv_rhs => rw [mul_assoc]

end Work.Diff.STE.Lead.GalTame
