import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.parChart_algebra
import Submission.Work.PARIMPL.ParSplit.parRho_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 4000
set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-! ## A `range` sum split after its first two terms -/

/-- A sum over `range (n+2)` splits into its first two terms plus the sum over `range n` of the
terms shifted by `2`.  This is the elementary bookkeeping behind "the tail of the germ is
`O(ζ²)`". -/
lemma sum_range_split_two (f : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), f k = f 0 + f 1 + ∑ k ∈ Finset.range n, f (k + 2) := by
  induction n with
  | zero => simp [Finset.sum_range_succ]
  | succ n ih =>
    rw [show n + 1 + 2 = n + 2 + 1 from by ring, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
    ring

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## The germ as an explicit Taylor sum -/

/-- `parHgerm S c ζ = Σ_{k ≤ wallN} psi_k · (parS)^{k+1} · ζ^k`. -/
theorem parHgerm_eq_sum (S : SplitData d) (c ζ : ℂ) :
    parHgerm S c ζ = ∑ k ∈ Finset.range (wallN + 1),
      psi S c k * (parS S c) ^ (k + 1) * ζ ^ k := by
  unfold parHgerm Rfun
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow, pow_succ]
  ring

/-- `parHgerm S c 0 = psi S c 0 · parS S c`, the value of the germ at the origin. -/
theorem parHgerm_at_zero (S : SplitData d) (c : ℂ) :
    parHgerm S c 0 = psi S c 0 * parS S c := by
  rw [parHgerm_eq_sum]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [zero_pow hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos wallN)) h

/-! ## The uniform bounds -/

/-- **Uniform bounds for the germ of the normal form** (`parHgerm` is `s c * R_c (m c + s c * ζ)`
with `R_c(w) = Σ_{k ≤ wallN} psi S c k * w^k`, `parH1 S c = (parS S c)^2 * psi S c 1`).

Since `parHgerm S c ζ = parS S c * Σ_k psi_k (parS S c * ζ)^k`, the difference
`parHgerm ζ - parHgerm 0 - parH1 ζ` equals `Σ_{k ≥ 2} psi_k (parS)^{k+1} ζ^k`, which is `O(ζ²)`
with a constant uniform in `c ∈ ball c₀ ρ'` once `psi_k` and `parS` are uniformly bounded
(compactness/continuity of the `psi_k` and nonvanishing of `parRho = psi_0`). -/
theorem parHgerm_tail_bounds {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∃ r > 0, ∃ A : ℝ, 0 ≤ A ∧ ∃ B : ℝ, 0 ≤ B ∧
      (∀ c ∈ Metric.ball c₀ ρ', ‖Work.PARIMPL.ParSplit.parH1 S c‖ ≤ B) ∧
      (∀ c ∈ Metric.ball c₀ ρ', ∀ ζ : ℂ, ‖ζ‖ < r →
        ‖Work.PARIMPL.ParSplit.parHgerm S c ζ - Work.PARIMPL.ParSplit.parHgerm S c 0
          - Work.PARIMPL.ParSplit.parH1 S c * ζ‖ ≤ A * ‖ζ‖ ^ 2) := by
  -- the radius on which `parRho` does not vanish
  obtain ⟨ρρ, hρρ0, hρρS, hρρne⟩ := parRho_ne_zero S
  set R : ℝ := ρρ / 2 with hRdef
  have hR0 : 0 < R := by rw [hRdef]; linarith
  have hRS : R ≤ S.ρ := by rw [hRdef]; linarith
  have hRlt : R < ρρ := by rw [hRdef]; linarith
  have hKsub : Metric.closedBall c₀ R ⊆ Metric.ball c₀ ρρ :=
    Metric.closedBall_subset_ball hRlt
  have hKsubS : Metric.closedBall c₀ R ⊆ Metric.ball c₀ S.ρ :=
    hKsub.trans (Metric.ball_subset_ball hρρS)
  have hKc : IsCompact (Metric.closedBall c₀ R) := isCompact_closedBall c₀ R
  have hc₀K : c₀ ∈ Metric.closedBall c₀ R := by
    rw [Metric.mem_closedBall]; simpa using hR0.le
  have hKne : (Metric.closedBall c₀ R).Nonempty := ⟨c₀, hc₀K⟩
  -- uniform bounds for the `psi_k` on the closed ball
  have hpsi : ∀ k : ℕ, ∃ M : ℝ, ∀ c ∈ Metric.closedBall c₀ R, ‖psi S c k‖ ≤ M :=
    fun k => hKc.exists_bound_of_continuousOn ((continuousOn_psi S k (le_refl S.ρ)).mono hKsubS)
  choose Mpsi hMpsi using hpsi
  have hMpsi_nn : ∀ k : ℕ, 0 ≤ Mpsi k := fun k =>
    le_trans (norm_nonneg _) (hMpsi k c₀ hc₀K)
  -- uniform bound for `parLam`
  obtain ⟨Mlam₀, hMlam₀⟩ :=
    hKc.exists_bound_of_continuousOn ((continuousOn_parLam S (le_refl S.ρ)).mono hKsubS)
  set Mlam : ℝ := max 0 Mlam₀ with hMlamdef
  have hMlam_nn : 0 ≤ Mlam := le_max_left _ _
  have hMlam : ∀ c ∈ Metric.closedBall c₀ R, ‖parLam S c‖ ≤ Mlam :=
    fun c hc => le_trans (hMlam₀ c hc) (le_max_right _ _)
  -- positive lower bound for `parRho`
  obtain ⟨x₀, hx₀K, hx₀min⟩ :=
    hKc.exists_isMinOn hKne ((continuousOn_parRho S (le_refl S.ρ)).mono hKsubS).norm
  have hx₀ne : parRho S x₀ ≠ 0 := hρρne x₀ (hKsub hx₀K)
  set m : ℝ := ‖parRho S x₀‖ with hmdef
  have hmpos : 0 < m := by rw [hmdef]; exact norm_pos_iff.mpr hx₀ne
  have hmle : ∀ c ∈ Metric.closedBall c₀ R, m ≤ ‖parRho S c‖ := by
    intro c hc
    rw [hmdef]
    exact hx₀min hc
  -- `‖parU0‖² = ‖parLam‖`
  have hu0norm : ∀ c ∈ Metric.ball c₀ ρρ, ‖parU0 S c‖ ^ 2 = ‖parLam S c‖ := by
    intro c hc
    have hρc : ‖parRho S c‖ ≠ 0 := norm_ne_zero_iff.mpr (hρρne c hc)
    have h2 : ‖(Complex.ofReal ‖parRho S c‖ : ℂ) ^ 2‖ = ‖parRho S c‖ ^ 2 := by
      rw [norm_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    calc ‖parU0 S c‖ ^ 2 = ‖(parU0 S c) ^ 2‖ := (norm_pow _ 2).symm
      _ = ‖parLam S c * (parRho S c) ^ 2 / (Complex.ofReal ‖parRho S c‖) ^ 2‖ := by
          rw [parChart_parU0_sq S c]
      _ = ‖parLam S c‖ * ‖(parRho S c) ^ 2‖ / ‖(Complex.ofReal ‖parRho S c‖) ^ 2‖ := by
          rw [norm_div, norm_mul]
      _ = ‖parLam S c‖ * ‖parRho S c‖ ^ 2 / ‖parRho S c‖ ^ 2 := by rw [h2, norm_pow]
      _ = ‖parLam S c‖ := by rw [mul_div_cancel_right₀ _ (pow_ne_zero 2 hρc)]
  -- the uniform bound on the chart scale `parS`
  set Ms : ℝ := Real.sqrt Mlam / m with hMsdef
  have hMs_nn : 0 ≤ Ms := by
    rw [hMsdef]; exact div_nonneg (Real.sqrt_nonneg _) hmpos.le
  have hs_le : ∀ c ∈ Metric.closedBall c₀ R, ‖parS S c‖ ≤ Ms := by
    intro c hcK
    have hcρ : c ∈ Metric.ball c₀ ρρ := hKsub hcK
    have hu : ‖parU0 S c‖ ≤ Real.sqrt Mlam := by
      rw [← Real.sqrt_sq (norm_nonneg (parU0 S c))]
      exact Real.sqrt_le_sqrt (le_trans (le_of_eq (hu0norm c hcρ)) (hMlam c hcK))
    rw [parS, norm_div, hMsdef]
    exact div_le_div₀ (Real.sqrt_nonneg _) hu hmpos (hmle c hcK)
  -- the two constants
  set A : ℝ := ∑ k ∈ Finset.range (wallN - 1), Mpsi (k + 2) * Ms ^ (k + 2 + 1) with hAdef
  have hA_nn : 0 ≤ A := by
    rw [hAdef]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hMpsi_nn _) (pow_nonneg hMs_nn _))
  set B : ℝ := Ms ^ 2 * Mpsi 1 with hBdef
  have hB_nn : 0 ≤ B := by
    rw [hBdef]; exact mul_nonneg (pow_nonneg hMs_nn 2) (hMpsi_nn 1)
  refine ⟨R, hR0, hRS, 1, one_pos, A, hA_nn, B, hB_nn, ?_, ?_⟩
  · -- the uniform bound on `parH1`
    intro c hc
    have hcK : c ∈ Metric.closedBall c₀ R := Metric.ball_subset_closedBall hc
    rw [parH1, hBdef]
    calc ‖(parS S c) ^ 2 * psi S c 1‖ = ‖parS S c‖ ^ 2 * ‖psi S c 1‖ := by
          rw [norm_mul, norm_pow]
      _ ≤ Ms ^ 2 * Mpsi 1 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hs_le c hcK) 2)
            (hMpsi 1 c hcK) (norm_nonneg _) (pow_nonneg hMs_nn 2)
  · -- the `O(ζ²)` bound on the tail
    intro c hc ζ hζ
    have hcK : c ∈ Metric.closedBall c₀ R := Metric.ball_subset_closedBall hc
    have hs := hs_le c hcK
    have hwN : wallN - 1 + 2 = wallN + 1 := by
      have : 1 ≤ wallN := by norm_num [wallN]
      omega
    have hsplit := sum_range_split_two
      (fun k => psi S c k * (parS S c) ^ (k + 1) * ζ ^ k) (wallN - 1)
    rw [hwN] at hsplit
    have key : parHgerm S c ζ
        = psi S c 0 * (parS S c) ^ 1 * ζ ^ 0
          + psi S c 1 * (parS S c) ^ 2 * ζ ^ 1
          + ∑ k ∈ Finset.range (wallN - 1),
              psi S c (k + 2) * (parS S c) ^ (k + 2 + 1) * ζ ^ (k + 2) := by
      rw [parHgerm_eq_sum S c ζ]
      exact hsplit
    have htail_eq : parHgerm S c ζ - parHgerm S c 0 - parH1 S c * ζ
        = ∑ k ∈ Finset.range (wallN - 1),
            psi S c (k + 2) * (parS S c) ^ (k + 2 + 1) * ζ ^ (k + 2) := by
      rw [key, parHgerm_at_zero, parH1]
      simp only [pow_one, pow_zero, mul_one]
      ring
    rw [htail_eq]
    calc ‖∑ k ∈ Finset.range (wallN - 1),
            psi S c (k + 2) * (parS S c) ^ (k + 2 + 1) * ζ ^ (k + 2)‖
        ≤ ∑ k ∈ Finset.range (wallN - 1),
            ‖psi S c (k + 2) * (parS S c) ^ (k + 2 + 1) * ζ ^ (k + 2)‖ :=
          norm_sum_le _ _
      _ = ∑ k ∈ Finset.range (wallN - 1),
            ‖psi S c (k + 2)‖ * ‖parS S c‖ ^ (k + 2 + 1) * ‖ζ‖ ^ (k + 2) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [norm_mul, norm_mul, norm_pow, norm_pow]
      _ ≤ ∑ k ∈ Finset.range (wallN - 1),
            Mpsi (k + 2) * Ms ^ (k + 2 + 1) * ‖ζ‖ ^ (k + 2) := by
          apply Finset.sum_le_sum
          intro k _
          have h1 : ‖psi S c (k + 2)‖ ≤ Mpsi (k + 2) := hMpsi (k + 2) c hcK
          have h5 : ‖parS S c‖ ^ (k + 2 + 1) ≤ Ms ^ (k + 2 + 1) :=
            pow_le_pow_left₀ (norm_nonneg _) hs _
          have hIn : ‖psi S c (k + 2)‖ * ‖parS S c‖ ^ (k + 2 + 1)
              ≤ Mpsi (k + 2) * Ms ^ (k + 2 + 1) :=
            mul_le_mul h1 h5 (pow_nonneg (norm_nonneg _) _) (hMpsi_nn _)
          exact mul_le_mul_of_nonneg_right hIn (pow_nonneg (norm_nonneg ζ) _)
      _ ≤ ∑ k ∈ Finset.range (wallN - 1),
            Mpsi (k + 2) * Ms ^ (k + 2 + 1) * ‖ζ‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro k _
          have h9 : 0 ≤ Mpsi (k + 2) * Ms ^ (k + 2 + 1) :=
            mul_nonneg (hMpsi_nn _) (pow_nonneg hMs_nn _)
          have hp : ‖ζ‖ ^ (k + 2) ≤ ‖ζ‖ ^ 2 :=
            pow_le_pow_of_le_one (norm_nonneg ζ) hζ.le (by omega : 2 ≤ k + 2)
          exact mul_le_mul_of_nonneg_left hp h9
      _ = (∑ k ∈ Finset.range (wallN - 1), Mpsi (k + 2) * Ms ^ (k + 2 + 1)) * ‖ζ‖ ^ 2 := by
          rw [Finset.sum_mul]
      _ = A * ‖ζ‖ ^ 2 := by rw [hAdef]

end Work.PARIMPL.ParSplit
