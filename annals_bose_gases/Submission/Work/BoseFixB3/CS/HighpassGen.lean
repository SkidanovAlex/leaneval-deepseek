import Mathlib.Analysis.Fourier.Notation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.cubInd_kinFT_l2
import Submission.Work.BoseFixB3.CS.Pieces.highpass_difference
import Submission.Work.BoseFixB3.CS.Pieces.hp_kinFT_iteratedDir_basis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.HighpassGen` — the high-pass content bound at an arbitrary order

The high-pass content bound of `CS/Pieces/highpass_content_small` (there at order `40`) is
proved here for an **arbitrary order** `N`: an `ℓ`-smooth bump supported in the ball of radius
`ℓ/2` has high-pass content at the momentum cut-off `κ` bounded by `C_N·M·ℓ³·(ℓκ)^{-N}`,
with `C_N` depending only on `N` (and on nothing else: not on the cut-off `fc`, not on `κ`, `ℓ`,
not on the bump).

This is needed because the leakage term of the `CS` step of the `B3` chapter must beat a
*polynomially* small budget: only an order `N ≥ 83` is large enough (see
`CS/B3CSRoot_ANALYSIS.md`), while the corpus's existing lemma is at the fixed order `40`.

The route is the same as at order `40`, with every `40` replaced by `N` and every `80` by `2N`:

* `kinFT_shell_l2_gen` — the `L²` mass of the `kinFT` transform over the shell `‖p‖ ≥ κ` is
  controlled by the `L²` norm of the `N`-th derivative, with constant `κ^{-2N}`;
* `highpass_content_small_param` — Cauchy–Schwarz against the box indicator's exact `L²` mass
  `(2π)³ℓ³`.

## Main results

* `norm_pow_le_coord` — the coordinate bound `‖p‖^{2N} ≤ 3^{N-1}Σ_k|p_k|^{2N}`;
* `shell_integral_le_gen` — the shell/full-integral comparison at order `2N`;
* `complex_iteratedFDeriv_norm_gen` — the complexification does not increase the norm of the
  `N`-th iterated derivative evaluated on a unit basis direction;
* `kinFT_shell_l2_gen` — the shell `L²` bound at order `N`;
* `highpass_content_small_param` — the high-pass content bound at order `N`.
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators FourierTransform

namespace Work.BoseFixB3.CS.HighpassGen

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 1. The coordinate bound `‖p‖^{2N} ≤ 3^{N-1}Σ_k|p_k|^{2N}` -/

private lemma norm_sq_eq_sum_coord (p : E3) :
    ‖p‖ ^ 2 = ∑ k : Fin 3, |p k| ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl fun k _ => by rw [Real.norm_eq_abs, sq_abs]

/-- The `2N`-th power of the norm is controlled by the sum of the `2N`-th powers of the
coordinates, with the Hölder constant `3^{N-1}`. -/
theorem norm_pow_le_coord (N : ℕ) (p : E3) :
    ‖p‖ ^ (2 * N) ≤ 3 ^ (N - 1) * ∑ k : Fin 3, |p k| ^ (2 * N) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 := norm_sq_eq_sum_coord p
  have key : (∑ k : Fin 3, |p k| ^ 2) ^ N ≤ 3 ^ (N - 1) * ∑ k : Fin 3, |p k| ^ (2 * N) := by
    have h3 := Real.rpow_sum_le_const_mul_sum_rpow (s := (Finset.univ : Finset (Fin 3)))
      (f := fun k : Fin 3 => |p k| ^ 2) (p := (N : ℝ)) hNpos
    simp only [Finset.card_univ, Fintype.card_fin, abs_sq] at h3
    have hsub : ((N : ℝ) - 1) = ((N - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hN]; norm_num
    have h5 : ∀ k : Fin 3, (|p k| ^ 2) ^ (N : ℝ) = |p k| ^ (2 * N) := by
      intro k
      rw [← Real.rpow_natCast (|p k|) 2, ← Real.rpow_mul (abs_nonneg _)]
      rw [show ((2 : ℕ) : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) by push_cast; ring]
      rw [Real.rpow_natCast]
    have hsum : (∑ k : Fin 3, (|p k| ^ 2) ^ (N : ℝ)) = ∑ k : Fin 3, |p k| ^ (2 * N) :=
      Finset.sum_congr rfl (fun k _ => h5 k)
    rw [hsub, hsum] at h3
    simp only [Real.rpow_natCast, Nat.cast_ofNat] at h3
    exact h3
  calc ‖p‖ ^ (2 * N) = (‖p‖ ^ 2) ^ N := by rw [pow_mul]
    _ = (∑ k : Fin 3, |p k| ^ 2) ^ N := by rw [h2]
    _ ≤ _ := key

/-! ## 2. The shell/full comparison at order `2N` -/

/-- `∫_{‖p‖ ≥ κ} f ≤ κ^{-2N}∫ ‖p‖^{2N}f`. -/
theorem shell_integral_le_gen (N : ℕ) (f : E3 → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hf : AEMeasurable f) (hfn : 0 ≤ f)
    (hint : Integrable (fun p : E3 => ‖p‖ ^ (2 * N) * f p)) :
    ∫ p in {q : E3 | κ ≤ ‖q‖}, f p
      ≤ (κ ^ (2 * N))⁻¹ * ∫ p : E3, ‖p‖ ^ (2 * N) * f p := by
  classical
  have hmeas : MeasurableSet {q : E3 | κ ≤ ‖q‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  rw [← integral_indicator hmeas]
  have hle : ∀ p : E3, {q : E3 | κ ≤ ‖q‖}.indicator f p
      ≤ (κ ^ (2 * N))⁻¹ * (‖p‖ ^ (2 * N) * f p) := by
    intro p
    by_cases hp : p ∈ {q : E3 | κ ≤ ‖q‖}
    · rw [Set.indicator_of_mem hp]
      have hpκ : κ ≤ ‖p‖ := hp
      have hpow : κ ^ (2 * N) ≤ ‖p‖ ^ (2 * N) := pow_le_pow_left₀ hκ.le hpκ (2 * N)
      have hpos : (0 : ℝ) < κ ^ (2 * N) := by positivity
      calc f p = (κ ^ (2 * N))⁻¹ * (κ ^ (2 * N) * f p) := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
        _ ≤ (κ ^ (2 * N))⁻¹ * (‖p‖ ^ (2 * N) * f p) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (hfn p))
              (by positivity)
    · rw [Set.indicator_of_notMem hp]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hfn p))
  have hint2 : Integrable (fun p : E3 => (κ ^ (2 * N))⁻¹ * (‖p‖ ^ (2 * N) * f p)) :=
    hint.const_mul _
  calc ∫ p : E3, {q : E3 | κ ≤ ‖q‖}.indicator f p
      ≤ ∫ p : E3, (κ ^ (2 * N))⁻¹ * (‖p‖ ^ (2 * N) * f p) :=
        integral_mono_of_nonneg
          (Eventually.of_forall fun p => Set.indicator_nonneg (fun z _ => hfn z) p)
          hint2 (Eventually.of_forall hle)
    _ = (κ ^ (2 * N))⁻¹ * ∫ p : E3, ‖p‖ ^ (2 * N) * f p := integral_const_mul _ _

/-! ## 3. Complexification of the iterated derivative -/

/-- The complexified `N`-th iterated derivative, evaluated on `N` copies of the unit vector
`kcStdBasis k`, is bounded by the operator norm of the real `N`-th derivative. -/
theorem complex_iteratedFDeriv_norm_gen (N : ℕ) (u : E3 → ℝ) (k : Fin 3)
    (x : E3) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ‖(iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
        (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)‖
      ≤ ‖iteratedFDeriv ℝ N u x‖ := by
  have hv : ‖Submission.BoseGases.kcStdBasis k‖ = 1 := by
    rw [Submission.BoseGases.kcStdBasis]
    simp
  have key : iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x
      = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ).toContinuousLinearMap.compContinuousMultilinearMap
          (iteratedFDeriv ℝ N u x) := by
    have hfun : (fun y : E3 => (u y : ℂ))
        = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ).toContinuousLinearMap ∘ u := by
      funext y; simp [Complex.ofRealLI_apply]
    rw [hfun]
    refine ContinuousLinearMap.iteratedFDeriv_comp_left _ hu.contDiffAt ?_
    exact WithTop.coe_le_coe.mpr le_top
  rw [key]
  rw [show ((Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ).toContinuousLinearMap.compContinuousMultilinearMap
        (iteratedFDeriv ℝ N u x)) (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)
      = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ)
          ((iteratedFDeriv ℝ N u x) (fun _ : Fin N => Submission.BoseGases.kcStdBasis k))
      from rfl]
  rw [LinearIsometry.norm_map]
  calc ‖(iteratedFDeriv ℝ N u x) (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)‖
      ≤ ‖iteratedFDeriv ℝ N u x‖ * ∏ _ : Fin N, (1 : ℝ) :=
        ContinuousMultilinearMap.le_opNorm_mul_prod_of_le _ (fun _ => by rw [hv])
    _ = ‖iteratedFDeriv ℝ N u x‖ := by simp

/-! ## 4. The `kinFT` shell bound at order `N` -/

/-- The `L²` mass of the `p`-convention Fourier transform of `ψ` over the shell `‖p‖ ≥ κ` is
bounded by `3^N(2π)³·κ^{-2N}∫‖D^Nψ‖²`. -/
theorem kinFT_shell_l2_gen (N : ℕ) (hN : 1 ≤ N) (u : E3 → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcs : HasCompactSupport u) :
    ∫ p in {p : E3 | κ ≤ ‖p‖},
        ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
      ≤ 3 ^ N * (2 * Real.pi) ^ 3 * (κ ^ (2 * N))⁻¹
          * ∫ x : E3, ‖iteratedFDeriv ℝ N u x‖ ^ 2 := by
  have hpi3pos : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
  have hge : (1 : ℕ) ≤ 2 * N := by omega
  -- ### 0. basics of the complexified profile
  have hWcd : ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => (u y : ℂ)) := by
    have h := (Complex.ofRealCLM.contDiff).comp hu
    simpa [Function.comp_def] using h
  have hWcs : HasCompactSupport (fun y : E3 => (u y : ℂ)) := by
    have h := hcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    simpa [Function.comp_def] using h
  have hW_int : Integrable (fun x : E3 => (u x : ℂ)) :=
    (hu.continuous.integrable_of_hasCompactSupport hcs).ofReal
  have hkin_cont : Continuous
      (fun p : E3 => Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hW_int
  have hG_ae : AEMeasurable
      (fun p : E3 => ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2) volume :=
    (hkin_cont.norm.pow 2).aemeasurable
  -- ### 1. the order-`N` derivative
  have hTu_cont : Continuous (iteratedFDeriv ℝ N u) :=
    hu.continuous_iteratedFDeriv (m := N) (WithTop.coe_le_coe.mpr le_top)
  have hTu_cs : HasCompactSupport (iteratedFDeriv ℝ N u) := hcs.iteratedFDeriv N
  have hTu_norm_int : Integrable (fun x : E3 => ‖iteratedFDeriv ℝ N u x‖) :=
    hTu_cont.norm.integrable_of_hasCompactSupport (hTu_cs.mono (fun x hx => by
      simp only [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by rw [h0]; simp)))
  have hTu_sq_int : Integrable (fun x : E3 => ‖iteratedFDeriv ℝ N u x‖ ^ 2) :=
    (hTu_cont.norm.pow 2).integrable_of_hasCompactSupport (hTu_cs.mono (fun x hx => by
      simp only [Function.mem_support, Pi.pow_apply] at hx ⊢
      intro h0
      exact hx (by rw [h0]; simp)))
  have hWder_cont : Continuous (iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ))) :=
    hWcd.continuous_iteratedFDeriv (m := N) (WithTop.coe_le_coe.mpr le_top)
  -- ### 2. per-coordinate facts
  have hDk_cont : ∀ k : Fin 3, Continuous (fun x : E3 =>
      (iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
        (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)) := by
    intro k
    have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin N => E3) ℂ
      (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)).continuous.comp hWder_cont
    simpa only [Function.comp_def, ContinuousMultilinearMap.apply_apply] using h
  have hDk_int : ∀ k : Fin 3, Integrable (fun x : E3 =>
      (iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
        (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)) := by
    intro k
    refine Integrable.mono' hTu_norm_int (hDk_cont k).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    exact complex_iteratedFDeriv_norm_gen N u k x hu
  have hDk_sq_int : ∀ k : Fin 3, Integrable (fun x : E3 =>
      ‖(iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
        (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)‖ ^ 2) := by
    intro k
    have hcont : Continuous (fun x : E3 =>
        ‖(iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
          (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)‖ ^ 2) :=
      (hDk_cont k).norm.pow 2
    refine Integrable.mono' hTu_sq_int hcont.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h := complex_iteratedFDeriv_norm_gen N u k x hu
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hDk_mlp2 : ∀ k : Fin 3, MemLp (fun x : E3 =>
      (iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
        (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)) 2 (volume : Measure E3) := by
    intro k
    refine (memLp_two_iff_integrable_sq_norm (hDk_cont k).aestronglyMeasurable).mpr ?_
    exact hDk_sq_int k
  have hDk_kin_sq_int : ∀ k : Fin 3, Integrable (fun p : E3 =>
      ‖Submission.BoseGases.kinFT
        (fun x : E3 => (iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
          (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)) p‖ ^ 2) := by
    intro k
    have hmlp := Work.BoseKinLoc.Momentum.memLp_kinFT (hDk_int k) (hDk_mlp2 k)
    exact (memLp_two_iff_integrable_sq_norm hmlp.aestronglyMeasurable).mp hmlp
  have hplanch : ∀ k : Fin 3,
      ∫ p : E3, ‖Submission.BoseGases.kinFT
          (fun x : E3 => (iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
            (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)) p‖ ^ 2
        = (2 * Real.pi) ^ 3 * ∫ x : E3,
            ‖(iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
              (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)‖ ^ 2 := by
    intro k
    have h := Work.BoseFixB3.HighMassAux.plancherel_L1L2
      (u := fun x : E3 => (iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
        (fun _ : Fin N => Submission.BoseGases.kcStdBasis k))
      (memLp_one_iff_integrable.mpr (hDk_int k)) (hDk_mlp2 k)
    have h2 := congrArg (fun t : ℝ => (2 * Real.pi) ^ 3 * t) h
    rw [mul_inv_cancel_left₀ (ne_of_gt hpi3pos)] at h2
    exact h2
  have hpt : ∀ k : Fin 3, ∀ p : E3,
      |p k| ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        = ‖Submission.BoseGases.kinFT
            (fun x : E3 => (iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
              (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)) p‖ ^ 2 := by
    intro k p
    have h := Work.BoseFixB3.CS.Pieces.hp_kinFT_iteratedDir_basis
      (fun y : E3 => (u y : ℂ)) k N p hWcd hWcs
    rw [h]
    ring
  have hInt_k : ∀ k : Fin 3, Integrable (fun p : E3 =>
      |p k| ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2) := by
    intro k
    refine (hDk_kin_sq_int k).congr (Eventually.of_forall fun p => ?_)
    exact (hpt k p).symm
  have hint_k : ∀ k : Fin 3,
      ∫ p : E3, |p k| ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        = (2 * Real.pi) ^ 3 * ∫ x : E3,
            ‖(iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
              (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)‖ ^ 2 := by
    intro k
    rw [integral_congr_ae (Eventually.of_forall (hpt k))]
    exact hplanch k
  have hbound_k : ∀ k : Fin 3,
      ∫ x : E3, ‖(iteratedFDeriv ℝ N (fun y : E3 => (u y : ℂ)) x)
            (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)‖ ^ 2
        ≤ ∫ x : E3, ‖iteratedFDeriv ℝ N u x‖ ^ 2 := by
    intro k
    refine integral_mono (hDk_sq_int k) hTu_sq_int (fun x => ?_)
    have h := complex_iteratedFDeriv_norm_gen N u k x hu
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  -- ### 3. the weighted integral is integrable and bounded
  have hInt_rhs : Integrable (fun p : E3 =>
      3 ^ (N - 1) * ∑ k : Fin 3,
        |p k| ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2) :=
    (integrable_finsetSum Finset.univ (fun k _ => hInt_k k)).const_mul (3 ^ (N - 1))
  have hpt_rhs : ∀ p : E3,
      ‖p‖ ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        ≤ 3 ^ (N - 1) * ∑ k : Fin 3,
            |p k| ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 := by
    intro p
    have hGnn : (0 : ℝ) ≤ ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 :=
      sq_nonneg _
    calc ‖p‖ ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        ≤ (3 ^ (N - 1) * ∑ k : Fin 3, |p k| ^ (2 * N)) *
            ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (norm_pow_le_coord N p) hGnn
      _ = 3 ^ (N - 1) * ∑ k : Fin 3,
            |p k| ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 := by
          rw [mul_assoc, Finset.sum_mul]
  have hInt_normpow : Integrable (fun p : E3 =>
      ‖p‖ ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2) := by
    have hcont : Continuous (fun p : E3 =>
        ‖p‖ ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2) :=
      (continuous_norm.pow (2 * N)).mul (hkin_cont.norm.pow 2)
    exact Integrable.mono' hInt_rhs hcont.aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) (2 * N)) (sq_nonneg _))]
        exact hpt_rhs p)
  -- ### 4. shell / sum / per-coordinate chain
  have hshell := shell_integral_le_gen N
    (fun p : E3 => ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2) κ hκ hG_ae
    (fun p => sq_nonneg _) hInt_normpow
  have hsum1 : ∫ p : E3, ‖p‖ ^ (2 * N) *
        ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
      ≤ 3 ^ (N - 1) * ∑ k : Fin 3, ∫ p : E3,
          |p k| ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 := by
    calc ∫ p : E3, ‖p‖ ^ (2 * N) *
          ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        ≤ ∫ p : E3, 3 ^ (N - 1) * ∑ k : Fin 3,
            |p k| ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 :=
          integral_mono hInt_normpow hInt_rhs hpt_rhs
      _ = 3 ^ (N - 1) * ∫ p : E3, ∑ k : Fin 3,
            |p k| ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 :=
          integral_const_mul _ _
      _ = 3 ^ (N - 1) * ∑ k : Fin 3, ∫ p : E3,
            |p k| ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 := by
          rw [integral_finsetSum Finset.univ (fun k _ => hInt_k k)]
  have hsum2 : ∑ k : Fin 3, ∫ p : E3,
        |p k| ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
      ≤ 3 * ((2 * Real.pi) ^ 3 * ∫ x : E3, ‖iteratedFDeriv ℝ N u x‖ ^ 2) := by
    have h3 : ∑ k : Fin 3, ((2 * Real.pi) ^ 3 * ∫ x : E3, ‖iteratedFDeriv ℝ N u x‖ ^ 2)
        = 3 * ((2 * Real.pi) ^ 3 * ∫ x : E3, ‖iteratedFDeriv ℝ N u x‖ ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    rw [← h3]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [hint_k k]
    exact mul_le_mul_of_nonneg_left (hbound_k k) hpi3pos.le
  have hmain : ∫ p : E3, ‖p‖ ^ (2 * N) *
        ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
      ≤ 3 ^ N * (2 * Real.pi) ^ 3 * ∫ x : E3, ‖iteratedFDeriv ℝ N u x‖ ^ 2 := by
    calc ∫ p : E3, ‖p‖ ^ (2 * N) *
          ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        ≤ 3 ^ (N - 1) * ∑ k : Fin 3, ∫ p : E3,
            |p k| ^ (2 * N) * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 := hsum1
      _ ≤ 3 ^ (N - 1) * (3 * ((2 * Real.pi) ^ 3 * ∫ x : E3, ‖iteratedFDeriv ℝ N u x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum2 (by positivity)
      _ = 3 ^ N * (2 * Real.pi) ^ 3 * ∫ x : E3, ‖iteratedFDeriv ℝ N u x‖ ^ 2 := by
          have h3 : (3 : ℝ) ^ N = 3 ^ (N - 1) * 3 := by
            rw [← pow_succ, Nat.sub_add_cancel hN]
          conv_rhs => rw [h3]
          ring
  calc ∫ p in {p : E3 | κ ≤ ‖p‖},
        ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
      ≤ (κ ^ (2 * N))⁻¹ * ∫ p : E3, ‖p‖ ^ (2 * N) *
          ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 := hshell
    _ ≤ (κ ^ (2 * N))⁻¹ * (3 ^ N * (2 * Real.pi) ^ 3 *
          ∫ x : E3, ‖iteratedFDeriv ℝ N u x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = 3 ^ N * (2 * Real.pi) ^ 3 * (κ ^ (2 * N))⁻¹ *
          ∫ x : E3, ‖iteratedFDeriv ℝ N u x‖ ^ 2 := by ring

end Work.BoseFixB3.CS.HighpassGen
