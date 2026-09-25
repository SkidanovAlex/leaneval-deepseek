import Mathlib
import Submission.Work.NN.Newton.FTdefs
import Submission.Work.NN.Newton.holderNorm_one_le_of_pointwise_bounds
import Submission.Work.NN.Newton.holderNorm_one_fderiv_coeff_le
import Submission.Work.NN.Core.TelTwoDF.EstimateDefs
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.NN.Core.Lev.sharpCut_fderiv_bounds

namespace Work.NN.Newton.FTs2

open scoped NNReal ENNReal ContDiff
open Set

/-- The coordinate projection `z ↦ z s` of `ℂⁿ`, as a continuous linear map. -/
private noncomputable abbrev projCoord {n : ℕ} (s : Fin n) : (Fin n → ℂ) →L[ℝ] ℂ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) s

private lemma projCoord_apply {n : ℕ} (s : Fin n) (z : Fin n → ℂ) : projCoord s z = z s :=
  ContinuousLinearMap.proj_apply s z

private lemma norm_projCoord_le_one {n : ℕ} (s : Fin n) : ‖projCoord s‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => ?_)
  rw [one_mul, projCoord_apply]
  exact norm_le_pi_norm z s

/-- The `C^{1,α}` norm of the complementary coordinate cutoff `1 - sharpCut a b (· s)` on a
polydisc, bounded by an explicit expression in `C`, `a`, `b`, where `C` controls the first and
second derivatives of the one-variable cutoff `sharpCut a b` on `ℂ`. -/
private theorem holderNorm_one_sub_slice_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ (a b : ℝ), 0 < a → a < b →
      (∀ x : ℂ, ‖fderiv ℝ (Work.NN.Core.sharpCut a b) x‖ ≤ C * (1 / (b - a))) ∧
      (∀ x y : ℂ, ‖Work.NN.Core.sharpCut a b x - Work.NN.Core.sharpCut a b y‖
          ≤ C * (1 / (b - a)) * ‖x - y‖) ∧
      (∀ x y : ℂ, ‖fderiv ℝ (Work.NN.Core.sharpCut a b) x
            - fderiv ℝ (Work.NN.Core.sharpCut a b) y‖
          ≤ C * (1 / (a * (b - a)) + 1 / (b - a) ^ 2) * ‖x - y‖))
    (s : Fin n) {a b : ℝ} (ha : 0 < a) (hab : a < b) (Q : Fin n → ℝ) :
    Work.CR.Flat.holderNorm 1 α (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s))
        (Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q)
      ≤ ENNReal.ofReal (6 + 4 * (C * (1 / (b - a)))
          + max (2 * (C * (1 / (b - a)))) (C * (1 / (a * (b - a)) + 1 / (b - a) ^ 2))) := by
  set M1 : ℝ := C * (1 / (b - a)) with hM1def
  set D : ℝ := C * (1 / (a * (b - a)) + 1 / (b - a) ^ 2) with hDdef
  set M2 : ℝ := max (2 * M1) D with hM2def
  have hbapos : 0 < b - a := by linarith
  have hM1nn : 0 ≤ M1 := by rw [hM1def]; positivity
  have hDnn : 0 ≤ D := by rw [hDdef]; positivity
  have hM2nn : 0 ≤ M2 := by
    rw [hM2def]
    exact le_trans (by linarith : (0 : ℝ) ≤ 2 * M1) (le_max_left _ _)
  obtain ⟨hd1, hdv, hd2⟩ := hC a b ha hab
  have hdiffs : ∀ x : ℂ, DifferentiableAt ℝ (Work.NN.Core.sharpCut a b) x :=
    fun x => ((Work.NN.Core.contDiff_sharpCut (a := a) (b := b)).differentiable (by simp)) x
  have hPnorm : ‖projCoord s‖ ≤ 1 := norm_projCoord_le_one s
  have hPapp : ∀ z : Fin n → ℂ, projCoord s z = z s := fun z => projCoord_apply s z
  have hΦ : ∀ x : Fin n → ℂ, HasFDerivAt (fun z : Fin n → ℂ => z s) (projCoord s) x := by
    intro x
    have h := ContinuousLinearMap.hasFDerivAt (projCoord s) (x := x)
    convert h using 1
    ext z
    exact hPapp z
  have hfd_eq : ∀ x : Fin n → ℂ,
      fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x
        = -((fderiv ℝ (Work.NN.Core.sharpCut a b) (x s)).comp (projCoord s)) := by
    intro x
    exact (((hdiffs (x s)).hasFDerivAt.comp x (hΦ x)).const_sub (1 : ℂ)).fderiv
  have hd1all : ∀ x : Fin n → ℂ,
      ‖fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x‖ ≤ M1 := by
    intro x
    rw [hfd_eq x, norm_neg, hM1def]
    calc ‖(fderiv ℝ (Work.NN.Core.sharpCut a b) (x s)).comp (projCoord s)‖
        ≤ ‖fderiv ℝ (Work.NN.Core.sharpCut a b) (x s)‖ * ‖projCoord s‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * (1 / (b - a))) * 1 :=
          mul_le_mul (hd1 (x s)) hPnorm (norm_nonneg _) (by positivity)
      _ = C * (1 / (b - a)) := by ring
  have hlips : ∀ x y : Fin n → ℂ,
      ‖fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x
        - fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) y‖
      ≤ D * ‖x - y‖ := by
    intro x y
    rw [hfd_eq x, hfd_eq y, hDdef]
    have hneg : -((fderiv ℝ (Work.NN.Core.sharpCut a b) (x s)).comp (projCoord s))
        - -((fderiv ℝ (Work.NN.Core.sharpCut a b) (y s)).comp (projCoord s))
        = -(((fderiv ℝ (Work.NN.Core.sharpCut a b) (x s)).comp (projCoord s))
            - ((fderiv ℝ (Work.NN.Core.sharpCut a b) (y s)).comp (projCoord s))) := by
      abel
    rw [hneg, norm_neg]
    have hcomp : (fderiv ℝ (Work.NN.Core.sharpCut a b) (x s)).comp (projCoord s)
        - (fderiv ℝ (Work.NN.Core.sharpCut a b) (y s)).comp (projCoord s)
        = ((fderiv ℝ (Work.NN.Core.sharpCut a b) (x s))
            - (fderiv ℝ (Work.NN.Core.sharpCut a b) (y s))).comp (projCoord s) := by
      ext v
      rfl
    rw [hcomp]
    have hxs : ‖x s - y s‖ ≤ ‖x - y‖ := by
      have h : x s - y s = (x - y) s := rfl
      rw [h]
      exact norm_le_pi_norm (x - y) s
    calc ‖((fderiv ℝ (Work.NN.Core.sharpCut a b) (x s))
            - (fderiv ℝ (Work.NN.Core.sharpCut a b) (y s))).comp (projCoord s)‖
        ≤ ‖(fderiv ℝ (Work.NN.Core.sharpCut a b) (x s))
            - (fderiv ℝ (Work.NN.Core.sharpCut a b) (y s))‖ * ‖projCoord s‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * (1 / (a * (b - a)) + 1 / (b - a) ^ 2)) * ‖x - y‖ := by
          calc ‖(fderiv ℝ (Work.NN.Core.sharpCut a b) (x s))
                  - (fderiv ℝ (Work.NN.Core.sharpCut a b) (y s))‖ * ‖projCoord s‖
              ≤ (C * (1 / (a * (b - a)) + 1 / (b - a) ^ 2) * ‖x s - y s‖) * 1 :=
                mul_le_mul (hd2 (x s) (y s)) hPnorm (norm_nonneg _) (by positivity)
            _ = (C * (1 / (a * (b - a)) + 1 / (b - a) ^ 2)) * ‖x s - y s‖ := by ring
            _ ≤ (C * (1 / (a * (b - a)) + 1 / (b - a) ^ 2)) * ‖x - y‖ :=
                mul_le_mul_of_nonneg_left hxs (by positivity)
  have hholder : ∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q,
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q,
      ‖fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x
        - fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) y‖
      ≤ M2 * ‖x - y‖ ^ α := by
    intro x _ y _
    by_cases hxy : x = y
    · subst hxy
      have hzero : ‖fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x
          - fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x‖
            = M2 * ‖x - x‖ ^ α := by
        rw [sub_self, norm_zero, sub_self, norm_zero, Real.zero_rpow hα0.ne', mul_zero]
      exact le_of_eq hzero
    · have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hA := hlips x y
      have hA' : ‖fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x
          - fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) y‖
            ≤ D * ‖x - y‖ := hA
      have hB : ‖fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x
          - fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) y‖
            ≤ 2 * M1 := by
        calc ‖fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x
              - fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) y‖
            ≤ ‖fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x‖
              + ‖fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) y‖ :=
              norm_sub_le _ _
          _ ≤ M1 + M1 := add_le_add (hd1all x) (hd1all y)
          _ = 2 * M1 := by ring
      by_cases hd : ‖x - y‖ ≤ 1
      · have hle : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
          have h2 : ‖x - y‖ ^ (1 : ℝ) ≤ ‖x - y‖ ^ α :=
            Real.rpow_le_rpow_of_exponent_ge hdpos hd hα1.le
          rwa [Real.rpow_one] at h2
        calc ‖fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x
              - fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) y‖
            ≤ D * ‖x - y‖ := hA'
          _ ≤ D * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left hle hDnn
          _ ≤ M2 * ‖x - y‖ ^ α :=
              mul_le_mul_of_nonneg_right (by rw [hM2def]; exact le_max_right _ _)
                (Real.rpow_nonneg (norm_nonneg _) _)
      · have hge : 1 ≤ ‖x - y‖ := le_of_lt (not_le.mp hd)
        have hα : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow hge hα0.le
        calc ‖fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x
              - fderiv ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) y‖
            ≤ 2 * M1 := hB
          _ ≤ (2 * M1) * ‖x - y‖ ^ α := le_mul_of_one_le_right (by linarith) hα
          _ ≤ M2 * ‖x - y‖ ^ α :=
              mul_le_mul_of_nonneg_right (by rw [hM2def]; exact le_max_left _ _)
                (Real.rpow_nonneg (norm_nonneg _) _)
  have hg0 : ∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q,
      ‖1 - Work.NN.Core.sharpCut a b (x s)‖ ≤ 2 := by
    intro x _
    calc ‖(1 : ℂ) - Work.NN.Core.sharpCut a b (x s)‖
        ≤ ‖(1 : ℂ)‖ + ‖Work.NN.Core.sharpCut a b (x s)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (le_of_eq (by norm_num)) (Work.NN.Core.norm_sharpCut_le_one a b (x s))
      _ = 2 := by norm_num
  have hgdiff : ∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q,
      DifferentiableAt ℝ (fun z : Fin n → ℂ => 1 - Work.NN.Core.sharpCut a b (z s)) x := by
    intro x _
    have hlin : DifferentiableAt ℝ (fun z : Fin n → ℂ => z s) x := by
      have h := (projCoord s).differentiableAt (x := x)
      convert h using 1
      ext z
      exact hPapp z
    exact (((hdiffs (x s)).comp x hlin)).const_sub 1
  refine le_trans (Work.NN.Newton.holderNorm_one_le_of_pointwise_bounds
    (Ω := Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q)
    (Work.CR.Flat.isOpen_polydisc (0 : Fin n → ℂ) Q)
    (Work.NN.Newton.convex_polydisc_zero Q)
    hα0 hα1 (M₀ := 2) (M₁ := M1) (M₂ := M2)
    (by norm_num) hM1nn hM2nn hgdiff hg0 (fun x _ => hd1all x) hholder) ?_
  rw [hM2def, hM1def, hDdef]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

-- GOAL: the `C^{1,α}` norm of the complementary cutoff `1 - kappa (ftG δ) s` on the tracking
-- polydisc `Eset (ftG δ) s` is `≤ M/δ^6` with `M` INDEPENDENT of `δ` (true size `O(δ^{-2})`;
-- exponent 6 is deliberately generous).
--
-- This is the sibling of `Work.NN.Newton.FTs2.kappa_holderNorm_bound`, and the proof is the same
-- with `1 - κ` in place of `κ`: `D(1-κ) = -Dκ`, so all the derivative/Hölder data are those of
-- `κ`, and only the order-0 value changes (`‖1 - κ‖ ≤ 2` since `0 ≤ σ ≤ 1`).  Concretely:
-- `kappa (ftG δ) s z = Real.smoothTransition ((b^2 - ‖z s‖^2)/(b^2 - a^2))` with `a = 1-15δ/16`,
-- `b = 1-7δ/8` (`Work.NN.Newton.ftG_a`, `ftG_b`, `Work.NN.Core.sharpCutReal`).
--
-- ACTUAL PROOF (the same shape as the recommendation, but it reuses the workspace facts about
-- the one-variable cutoff instead of rederiving its derivative data).  The first and second
-- derivatives of the one-variable cutoff `sharpCut a b : ℂ → ℂ` are already controlled, for
-- `0 < a < b`, by a single constant `C = C(α)` from `Work.NN.Core.Lev.sharpCut_fderiv_bounds`
-- (`Submission/Work/NN/Core/Lev/sharpCut_fderiv_bounds.lean`):
--   `‖fderiv (sharpCut a b) x‖ ≤ C/(b-a)` and
--   `‖fderiv (sharpCut a b) x - fderiv (sharpCut a b) y‖ ≤ C(1/(a(b-a)) + 1/(b-a)^2)‖x-y‖`.
-- Since `kappa G s = sharpCut (G.a s) (G.b s) ∘ (· s)` and the coordinate projection
-- `z ↦ z s` has operator norm `≤ 1`, the chain rule transfers both bounds to `ℂⁿ` with no loss
-- (this is `holderNorm_one_sub_slice_le` below), and
-- `Work.NN.Newton.holderNorm_one_le_of_pointwise_bounds` (explicit constant `3 M₀ + 4 M₁ + M₂`)
-- turns the pointwise data on the open polydisc `Eset G s` into
--   `holderNorm 1 α (1 - κ) (Eset G s) ≤ ofReal (6 + 4 C/(b-a) + 288 C/(b-a)^2)`,
-- the `6` being `3 · 2` (the order-0 bound `‖1 - κ‖ ≤ 2`) and `288` the excess of
-- `max (2 C/(b-a)) (C(1/(a(b-a)) + 1/(b-a)^2))`.  The geometry `b - a = δ/16`, `a ≥ 1/2` gives
-- `1/(b-a) = 16/δ`, `1/(b-a)^2 = 256/δ^2 ≤ 256/δ^6`, `1/(a(b-a)) ≤ 32/δ ≤ 32/δ^6`, whence
--   `holderNorm 1 α (1 - κ) (Eset G s) ≤ ofReal ((6 + 352 C)/δ^6)`,
-- and `(6 + 352 C)` is independent of `δ` (as are `n` and `s`).
theorem one_sub_kappa_holderNorm_bound {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (s : Fin n),
      Work.CR.Flat.holderNorm 1 α
          (fun z => 1 - Work.NN.Core.TelTwoDF.kappa (Work.NN.Newton.ftG (n := n) δ hδ0 hδ4) s z)
          (Work.NN.Core.TelTwoDF.Eset (Work.NN.Newton.ftG (n := n) δ hδ0 hδ4) s)
        ≤ ENNReal.ofReal (M / δ ^ 6) := by
  obtain ⟨C, hCpos, hC⟩ := Work.NN.Core.Lev.sharpCut_fderiv_bounds
  refine ⟨6 + 352 * C, by positivity, ?_⟩
  intro δ hδ0 hδ4 s
  set G : Work.NN.Core.TelTwoDF.Geom n := Work.NN.Newton.ftG (n := n) δ hδ0 hδ4 with hG
  have hδ1 : δ ≤ 1 := by linarith
  have hδ6pos : 0 < δ ^ 6 := pow_pos hδ0 6
  have hδ6le1 : δ ^ 6 ≤ 1 := pow_le_one₀ hδ0.le hδ1
  have hδ6leδ : δ ^ 6 ≤ δ := by
    have h5 : δ ^ 5 ≤ 1 := pow_le_one₀ hδ0.le hδ1
    calc δ ^ 6 = δ * δ ^ 5 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h5 hδ0.le
      _ = δ := by ring
  have hδ6leδ2 : δ ^ 6 ≤ δ ^ 2 := pow_le_pow_of_le_one hδ0.le hδ1 (by norm_num : 2 ≤ 6)
  have hδ2leδ : δ ^ 2 ≤ δ := by
    simpa using pow_le_pow_of_le_one hδ0.le hδ1 (by norm_num : (1 : ℕ) ≤ 2)
  have hbda : G.b s - G.a s = δ / 16 := by
    rw [hG, Work.NN.Newton.ftG_b, Work.NN.Newton.ftG_a]
    ring
  have ha12 : (1 : ℝ) / 2 ≤ G.a s := by
    rw [hG, Work.NN.Newton.ftG_a]
    linarith
  have hapos : 0 < G.a s := by linarith
  have hab : G.a s < G.b s := by
    have h : 0 < δ / 16 := by positivity
    linarith
  have hQle : Work.NN.Core.TelTwoDF.Erad G s s ≤ G.b s := le_of_eq (Work.NN.Core.TelTwoDF.Erad_self G s)
  have hslice := holderNorm_one_sub_slice_le hα0 hα1 hCpos hC s hapos hab
    (Work.NN.Core.TelTwoDF.Erad G s)
  have hM1big : C * (1 / (G.b s - G.a s)) ≤ 16 * C / δ ^ 6 := by
    have h1 : C * (1 / (G.b s - G.a s)) = 16 * C / δ := by
      rw [hbda, one_div, inv_div]
      ring
    rw [h1]
    exact div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 16 * C) hδ6pos hδ6leδ
  have h2M1big : 2 * (C * (1 / (G.b s - G.a s))) ≤ 288 * C / δ ^ 6 := by
    have h1 : 2 * (C * (1 / (G.b s - G.a s))) = 32 * C / δ := by
      rw [hbda, one_div, inv_div]
      ring
    rw [h1]
    calc 32 * C / δ ≤ 32 * C / δ ^ 6 :=
          div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 32 * C) hδ6pos hδ6leδ
      _ ≤ 288 * C / δ ^ 6 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hinv : 1 / (G.a s * (G.b s - G.a s)) ≤ 32 / δ := by
    have hAL : δ / 32 ≤ G.a s * (G.b s - G.a s) := by
      rw [hbda]
      nlinarith
    have h32 : 0 < δ / 32 := by positivity
    calc 1 / (G.a s * (G.b s - G.a s)) ≤ 1 / (δ / 32) :=
          div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) h32 hAL
      _ = 32 / δ := by rw [one_div, inv_div]
  have hinv2 : 1 / (G.b s - G.a s) ^ 2 = 256 / δ ^ 2 := by
    rw [hbda, div_pow, one_div, inv_div]
    norm_num
  have hDbig : C * (1 / (G.a s * (G.b s - G.a s)) + 1 / (G.b s - G.a s) ^ 2)
      ≤ 288 * C / δ ^ 6 := by
    have h3 : (1 : ℝ) / (G.a s * (G.b s - G.a s)) + 1 / (G.b s - G.a s) ^ 2
        ≤ 288 / δ ^ 6 := by
      rw [hinv2]
      calc 1 / (G.a s * (G.b s - G.a s)) + 256 / δ ^ 2 ≤ 32 / δ + 256 / δ ^ 2 :=
            add_le_add hinv le_rfl
        _ ≤ 288 / δ ^ 2 := by
            have h1 : 32 / δ ≤ 32 / δ ^ 2 :=
              div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 32) (pow_pos hδ0 2) hδ2leδ
            calc 32 / δ + 256 / δ ^ 2 ≤ 32 / δ ^ 2 + 256 / δ ^ 2 := add_le_add h1 le_rfl
              _ = 288 / δ ^ 2 := by ring
        _ ≤ 288 / δ ^ 6 :=
            div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 288) hδ6pos hδ6leδ2
    calc C * (1 / (G.a s * (G.b s - G.a s)) + 1 / (G.b s - G.a s) ^ 2)
        ≤ C * (288 / δ ^ 6) := mul_le_mul_of_nonneg_left h3 hCpos.le
      _ = 288 * C / δ ^ 6 := by ring
  have hM2big : max (2 * (C * (1 / (G.b s - G.a s))))
      (C * (1 / (G.a s * (G.b s - G.a s)) + 1 / (G.b s - G.a s) ^ 2)) ≤ 288 * C / δ ^ 6 :=
    max_le h2M1big hDbig
  have h4M1big : 4 * (C * (1 / (G.b s - G.a s))) ≤ 64 * C / δ ^ 6 := by
    calc 4 * (C * (1 / (G.b s - G.a s))) ≤ 4 * (16 * C / δ ^ 6) := by linarith
      _ = 64 * C / δ ^ 6 := by ring
  have h6big : (6 : ℝ) ≤ 6 / δ ^ 6 := by
    rw [le_div_iff₀ hδ6pos]
    nlinarith [hδ6le1]
  have htotal : 6 + 4 * (C * (1 / (G.b s - G.a s)))
      + max (2 * (C * (1 / (G.b s - G.a s))))
          (C * (1 / (G.a s * (G.b s - G.a s)) + 1 / (G.b s - G.a s) ^ 2))
      ≤ (6 + 352 * C) / δ ^ 6 := by
    calc 6 + 4 * (C * (1 / (G.b s - G.a s)))
          + max (2 * (C * (1 / (G.b s - G.a s))))
              (C * (1 / (G.a s * (G.b s - G.a s)) + 1 / (G.b s - G.a s) ^ 2))
        ≤ 6 / δ ^ 6 + (64 * C / δ ^ 6 + 288 * C / δ ^ 6) := by linarith
      _ = (6 + 352 * C) / δ ^ 6 := by
          rw [add_div]
          congr 1
          ring
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal htotal)
  simpa only [Work.NN.Core.TelTwoDF.kappa, Work.NN.Core.TelTwoDF.Eset] using hslice

end Work.NN.Newton.FTs2
