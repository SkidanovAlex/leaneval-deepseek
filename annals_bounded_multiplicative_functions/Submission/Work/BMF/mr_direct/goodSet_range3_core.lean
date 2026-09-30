import Mathlib
import Submission.Work.BMF.mr_direct.goodSet_bound_range_defs
import Submission.Work.BMF.mr_direct.goodSet_E1_bound
import Submission.Work.BMF.mr_direct.indexSet_winE_exp_neg_sum_le
import Submission.Work.BMF.mr_direct.indexSet_winE_hi_exp_neg_sum_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

noncomputable section

/-! ## Auxiliary lemmas for `goodSet_range3_core` -/

/-- Per-`j` bound for the range-generalised good-set estimate.

For a single `j`, the `L²` norm of `primePoly c K j · remPolyR b P Q K X₁ X₂ j` over a set
`u ⊆ [-S,S]` on which `primePoly` is small (`‖primePoly c K j t‖ ≤ e^{-αj/K}`) is bounded by
`C_W (2S + winHi_j + 1) · e^{-2αj/K} winE_j`:

the pointwise bound contributes the factor `e^{-2αj/K}`, the integral over `u` is enlarged to
`[-S,S]` (nonnegativity), and the mean-value estimate `hCW` is applied to the window
`[winLo K X₁ j, winHi K X₂ j]` of the remainder polynomial. -/
lemma goodSet_range3_core_perj (C_W : ℝ)
    (hCW : ∀ (A B S : ℝ) (a : ℕ → ℂ), 0 < A → 0 ≤ S →
      (∫ t in (-S)..S, ‖∑ m ∈ Work.BMF.natIcc A B, a m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
        ≤ C_W * (2 * S + (B + 1)) * ∑ m ∈ Work.BMF.natIcc A B, ‖a m‖ ^ 2 / (m : ℝ) ^ 2)
    (X₁ X₂ K P Q S α : ℝ) (b c : ℕ → ℂ) (u : Set ℝ) (j : ℕ)
    (hX₁ : 0 < X₁) (hS : 0 ≤ S)
    (hu : u ⊆ Set.Icc (-S) S)
    (hgood : ∀ t ∈ u, ‖mrDirect.primePoly c K j t‖ ≤ Real.exp (-(α * (j : ℝ) / K))) :
    (∫ t in u, ‖mrDirect.primePoly c K j t * mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      ≤ C_W * (2 * S + (X₂ * Real.exp (-(j : ℝ) / K) + 1)) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j) := by
  set E : ℝ := Real.exp (-(2 * α * (j : ℝ) / K)) with hE
  set d : ℕ → ℂ := fun m =>
    b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹ with hd
  have hEnn : 0 ≤ E := by rw [hE]; positivity
  have hApos : 0 < winLo K X₁ j := mul_pos hX₁ (Real.exp_pos _)
  have hcontRP : Continuous fun t : ℝ => mrDirect.remPolyR b P Q K X₁ X₂ j t :=
    continuous_remPolyR b P Q K X₁ X₂ j hX₁
  have hcontPP : Continuous fun t : ℝ => mrDirect.primePoly c K j t := continuous_primePoly c K j
  -- the pointwise bound on `u`
  have hpoint : ∀ t ∈ u, ‖mrDirect.primePoly c K j t *
        mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2
      ≤ E * ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 := by
    intro t ht
    have h1 : ‖mrDirect.primePoly c K j t‖ ≤ Real.exp (-(α * (j : ℝ) / K)) := hgood t ht
    have h2 : ‖mrDirect.primePoly c K j t‖ ^ 2 ≤ (Real.exp (-(α * (j : ℝ) / K))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (Real.exp (-(α * (j : ℝ) / K))) ^ 2 = E := by
      rw [hE, sq, ← Real.exp_add]
      congr 1
      ring
    rw [h3] at h2
    calc ‖mrDirect.primePoly c K j t * mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2
        = ‖mrDirect.primePoly c K j t‖ ^ 2 * ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 := by
          rw [norm_mul, mul_pow]
      _ ≤ E * ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  -- step 1: monotonicity of the set integral
  have hstep2 : (∫ t in u, ‖mrDirect.primePoly c K j t *
        mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      ≤ ∫ t in u, E * ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 := by
    refine setIntegral_mono_of_le_on ?_ ?_ ?_ (fun x => sq_nonneg _) hpoint
    · exact ((hcontPP.mul hcontRP).norm.pow 2).measurable
    · exact (continuous_const.mul (hcontRP.norm.pow 2)).measurable
    · exact ((continuous_const.mul (hcontRP.norm.pow 2)).continuousOn.integrableOn_Icc).mono_set hu
  -- step 2: pull the constant out
  have hstep3 : (∫ t in u, E * ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      = E * ∫ t in u, ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 :=
    MeasureTheory.integral_const_mul E _
  -- step 3: enlarge `u` to `[-S,S]`
  have hstep5 : (∫ t in u, ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      ≤ ∫ t in (-S)..S, ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 :=
    setIntegral_le_intervalIntegral hS hu (hcontRP.norm.pow 2) (fun x _ => sq_nonneg _)
  -- step 4: the mean value bound on the window
  have hWE : (∑ m ∈ Work.BMF.natIcc (winLo K X₁ j) (winHi K X₂ j),
        ‖d m‖ ^ 2 / (m : ℝ) ^ 2) = winE b P Q K X₁ X₂ j := by
    rw [winE]
  have hInt : (∫ t in (-S)..S, ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      = ∫ t in (-S)..S,
          ‖∑ m ∈ Work.BMF.natIcc (winLo K X₁ j) (winHi K X₂ j),
              d m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [remPolyR_eq_sum]
  have hstep4 : (∫ t in (-S)..S, ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      ≤ C_W * (2 * S + (winHi K X₂ j + 1)) * winE b P Q K X₁ X₂ j := by
    rw [hInt]
    calc (∫ t in (-S)..S,
            ‖∑ m ∈ Work.BMF.natIcc (winLo K X₁ j) (winHi K X₂ j),
              d m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
        ≤ C_W * (2 * S + (winHi K X₂ j + 1)) *
            ∑ m ∈ Work.BMF.natIcc (winLo K X₁ j) (winHi K X₂ j),
              ‖d m‖ ^ 2 / (m : ℝ) ^ 2 :=
          hCW (winLo K X₁ j) (winHi K X₂ j) S d hApos hS
      _ = C_W * (2 * S + (winHi K X₂ j + 1)) * winE b P Q K X₁ X₂ j := by rw [hWE]
  -- assembly
  calc (∫ t in u, ‖mrDirect.primePoly c K j t *
        mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      ≤ ∫ t in u, E * ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 := hstep2
    _ = E * ∫ t in u, ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 := hstep3
    _ ≤ E * ∫ t in (-S)..S, ‖mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hstep5 hEnn
    _ ≤ E * (C_W * (2 * S + (winHi K X₂ j + 1)) * winE b P Q K X₁ X₂ j) :=
        mul_le_mul_of_nonneg_left hstep4 hEnn
    _ = C_W * (2 * S + (X₂ * Real.exp (-(j : ℝ) / K) + 1)) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j) := by
        rw [hE]
        simp only [winHi]
        ring

/-- The sum over `j ∈ indexSet K P Q` of `(winHi_j + 1) · e^{-2αj/K} · winE_j` is at most
`54 (K log(Q/P) + 2) (X₂/X₁) P^{-2α}`.

Split the factor `winHi_j + 1` into `X₂ e^{-j/K} + 1`; the first part is estimated by
`indexSet_winE_hi_exp_neg_sum_le` (constant `36`), the second by `winE ≤ 2` together with
`Σ_j e^{-2αj/K} ≤ 3 P^{-2α} (K log(Q/P) + 2)` (constant `6`). Since `X₂/X₁ ≥ 1`, one has
`36 r + 6 ≤ 54 r`, which gives the stated constant. -/
lemma goodSet_range3_core_sum_win_one (b : ℕ → ℂ) (K P Q X₁ X₂ α : ℝ)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hX₁ : 1 ≤ X₁) (hX₁X₂ : X₁ ≤ X₂) (hK : 3 ≤ K) (hP : 2 ≤ P)
    (hPQ : P ≤ Q) (hα0 : 0 < α) (hα1 : α ≤ 1 / 4) :
    (∑ j ∈ mrDirect.indexSet K P Q,
        (X₂ * Real.exp (-(j : ℝ) / K) + 1) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))
      ≤ 54 * (K * Real.log (Q / P) + 2) * ((X₂ / X₁) * P ^ (-(2 * α))) := by
  have hX₁pos : 0 < X₁ := by linarith
  have hX₂pos : 0 < X₂ := by linarith
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  have hLnn : 0 ≤ Real.log (Q / P) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hPpos]; linarith
  have hz : 0 ≤ P ^ (-(2 * α)) := (Real.rpow_pos_of_pos hPpos _).le
  have hLz : 0 ≤ (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)) :=
    mul_nonneg (by nlinarith [hLnn, hKpos]) hz
  -- split the sum
  have hsplit : (∑ j ∈ mrDirect.indexSet K P Q,
        (X₂ * Real.exp (-(j : ℝ) / K) + 1) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))
      = (∑ j ∈ mrDirect.indexSet K P Q,
            (X₂ * Real.exp (-(j : ℝ) / K)) *
              (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))
        + (∑ j ∈ mrDirect.indexSet K P Q,
            Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsplit]
  have h1 : (∑ j ∈ mrDirect.indexSet K P Q,
        (X₂ * Real.exp (-(j : ℝ) / K)) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))
      ≤ 36 * (K * Real.log (Q / P) + 2) * ((X₂ / X₁) * P ^ (-(2 * α))) :=
    indexSet_winE_hi_exp_neg_sum_le b K P Q X₁ X₂ α hb hX₁pos hX₂pos hK hP hPQ hα0 hα1
  have h2 : (∑ j ∈ mrDirect.indexSet K P Q,
        Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
      ≤ 6 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)) := by
    have hE : ∀ j, winE b P Q K X₁ X₂ j ≤ 2 := fun j => winE_le_two b P Q K X₁ X₂ j hb hX₁pos
    calc (∑ j ∈ mrDirect.indexSet K P Q,
          Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
        ≤ ∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * 2 := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hE j) (Real.exp_pos _).le
      _ = 2 * (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K))) := by
          rw [← Finset.sum_mul]; ring
      _ ≤ 2 * (3 * P ^ (-(2 * α)) * (K * Real.log (Q / P) + 2)) :=
          mul_le_mul_of_nonneg_left (indexSet_exp_neg_sum_le K P Q α hK hP hPQ hα0 hα1)
            (by norm_num)
      _ = 6 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)) := by ring
  -- combine
  have hkey : 36 * (K * Real.log (Q / P) + 2) * ((X₂ / X₁) * P ^ (-(2 * α)))
      + 6 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α))
      ≤ 54 * (K * Real.log (Q / P) + 2) * ((X₂ / X₁) * P ^ (-(2 * α))) := by
    have hr1 : 1 ≤ X₂ / X₁ := (one_le_div hX₁pos).mpr hX₁X₂
    have hrf : 36 * (X₂ / X₁) + 6 ≤ 54 * (X₂ / X₁) := by linarith
    have hmm := mul_le_mul_of_nonneg_left hrf hLz
    calc 36 * (K * Real.log (Q / P) + 2) * ((X₂ / X₁) * P ^ (-(2 * α)))
          + 6 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α))
        = ((K * Real.log (Q / P) + 2) * P ^ (-(2 * α))) * (36 * (X₂ / X₁) + 6) := by ring
      _ ≤ ((K * Real.log (Q / P) + 2) * P ^ (-(2 * α))) * (54 * (X₂ / X₁)) := hmm
      _ = 54 * (K * Real.log (Q / P) + 2) * ((X₂ / X₁) * P ^ (-(2 * α))) := by ring
  linarith

theorem goodSet_range3_core (C_W : ℝ) (hCWpos : 0 < C_W)
    (hCW : ∀ (A B S : ℝ) (a : ℕ → ℂ), 0 < A → 0 ≤ S →
      (∫ t in (-S)..S, ‖∑ m ∈ Work.BMF.natIcc A B, a m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
        ≤ C_W * (2 * S + (B + 1)) * ∑ m ∈ Work.BMF.natIcc A B, ‖a m‖ ^ 2 / (m : ℝ) ^ 2) :
    ∀ (X₁ X₂ K P Q S α : ℝ) (b c : ℕ → ℂ) (u : Set ℝ),
      1 ≤ X₁ → X₁ ≤ X₂ → 3 ≤ K → 2 ≤ P → P ≤ Q → 0 ≤ S → 0 < α → α ≤ 1 / 4 →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      u ⊆ Set.Icc (-S) S →
      (∀ t ∈ u, ∀ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        ‖Work.BMF.mrDirect.primePoly c K j t‖ ≤ Real.exp (-(α * (j : ℝ) / K))) →
      (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
            Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
        ≤ C_W * (K * Real.log (Q / P) + 2) *
            (40 * (S * (Q ^ (1 - 2 * α) / X₁)) + 54 * (X₂ / X₁ * P ^ (-(2 * α)))) := by
  intro X₁ X₂ K P Q S α b c u hX₁ hX₁X₂ hK hP hPQ hS hα0 hα1 hb hc hu hgood
  have hX₁pos : 0 < X₁ := by linarith
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  have hLnn : 0 ≤ Real.log (Q / P) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hPpos]; linarith
  -- per-`j` bounds
  have hperj : ∀ j ∈ mrDirect.indexSet K P Q,
      (∫ t in u, ‖mrDirect.primePoly c K j t * mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
        ≤ C_W * (2 * S + (X₂ * Real.exp (-(j : ℝ) / K) + 1)) *
            (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j) :=
    fun j hj => goodSet_range3_core_perj C_W hCW X₁ X₂ K P Q S α b c u j hX₁pos hS hu
      (fun t ht => hgood t ht j hj)
  have hsum : (∑ j ∈ mrDirect.indexSet K P Q,
        ∫ t in u, ‖mrDirect.primePoly c K j t * mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      ≤ ∑ j ∈ mrDirect.indexSet K P Q,
          C_W * (2 * S + (X₂ * Real.exp (-(j : ℝ) / K) + 1)) *
            (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j) :=
    Finset.sum_le_sum hperj
  -- factor `C_W` out of the sum
  have hfact : (∑ j ∈ mrDirect.indexSet K P Q,
          C_W * (2 * S + (X₂ * Real.exp (-(j : ℝ) / K) + 1)) *
            (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))
      = C_W * (2 * S * (∑ j ∈ mrDirect.indexSet K P Q,
              Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
          + (∑ j ∈ mrDirect.indexSet K P Q,
              (X₂ * Real.exp (-(j : ℝ) / K) + 1) *
                (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))) := by
    have hpt : ∀ j ∈ mrDirect.indexSet K P Q,
        C_W * (2 * S + (X₂ * Real.exp (-(j : ℝ) / K) + 1)) *
            (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
          = C_W * (2 * S * (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
              + (X₂ * Real.exp (-(j : ℝ) / K) + 1) *
                (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)) := by
      intro j hj; ring
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  -- bounds on the two sums
  have hS1le : (∑ j ∈ mrDirect.indexSet K P Q,
        Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
      ≤ 20 * (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X₁) :=
    indexSet_winE_exp_neg_sum_le b K P Q X₁ X₂ α hb hX₁pos hK hP hPQ hα0 hα1
  have hSXle : (∑ j ∈ mrDirect.indexSet K P Q,
        (X₂ * Real.exp (-(j : ℝ) / K) + 1) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))
      ≤ 54 * (K * Real.log (Q / P) + 2) * ((X₂ / X₁) * P ^ (-(2 * α))) :=
    goodSet_range3_core_sum_win_one b K P Q X₁ X₂ α hb hX₁ hX₁X₂ hK hP hPQ hα0 hα1
  calc (∑ j ∈ mrDirect.indexSet K P Q,
        ∫ t in u, ‖mrDirect.primePoly c K j t * mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      ≤ ∑ j ∈ mrDirect.indexSet K P Q,
          C_W * (2 * S + (X₂ * Real.exp (-(j : ℝ) / K) + 1)) *
            (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j) := hsum
    _ = C_W * (2 * S * (∑ j ∈ mrDirect.indexSet K P Q,
              Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
          + (∑ j ∈ mrDirect.indexSet K P Q,
              (X₂ * Real.exp (-(j : ℝ) / K) + 1) *
                (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))) := hfact
    _ ≤ C_W * (2 * S * (20 * (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X₁))
          + 54 * (K * Real.log (Q / P) + 2) * ((X₂ / X₁) * P ^ (-(2 * α)))) := by
        apply mul_le_mul_of_nonneg_left _ hCWpos.le
        have h1 : 2 * S * (∑ j ∈ mrDirect.indexSet K P Q,
              Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
            ≤ 2 * S * (20 * (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X₁)) :=
          mul_le_mul_of_nonneg_left hS1le (by linarith)
        linarith
    _ = C_W * (K * Real.log (Q / P) + 2) *
          (40 * (S * (Q ^ (1 - 2 * α) / X₁)) + 54 * (X₂ / X₁ * P ^ (-(2 * α)))) := by ring

end

end Work.BMF.mr_direct
