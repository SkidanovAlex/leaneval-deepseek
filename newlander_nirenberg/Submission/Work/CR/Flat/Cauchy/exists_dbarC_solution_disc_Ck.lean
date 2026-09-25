import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.dbarC_cauchyTransform
import Submission.Work.CR.Flat.Cauchy.contDiff_cauchyTransform
import Submission.Work.CR.Flat.Cauchy.dzC_cauchyTransform_T
import Submission.Work.CR.Flat.Cauchy.supportedInBall_deriv
import Submission.Work.CR.Flat.Cauchy.holderNorm_le_wirtinger
import Submission.Work.CR.Flat.Cauchy.holderNorm_dzC_le_uniform
import Submission.Work.CR.Flat.Cauchy.holderNorm_one_disc

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-! ## Auxiliary facts used in the induction

The Hölder norms depend only on the values on the domain, `∂_z` lowers the differentiability
order by one, and a small piece of `ℝ≥0∞`-arithmetic. -/

section Aux

lemma iterDerivNorm_congr {k : ℕ} {f g : ℂ → ℂ} {Ω : Set ℂ} (h : ∀ x ∈ Ω, f x = g x) :
    iterDerivNorm k f Ω = iterDerivNorm k g Ω := by
  have H : ∀ x ∈ Ω, iteratedFDerivWithin ℝ k f Ω x = iteratedFDerivWithin ℝ k g Ω x :=
    fun x hx => iteratedFDerivWithin_congr (fun z hz => h z hz) hx k
  unfold iterDerivNorm
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => ?_
    rw [H x hx]; exact le_iSup₂_of_le x hx le_rfl
  · refine iSup₂_le fun x hx => ?_
    rw [← H x hx]; exact le_iSup₂_of_le x hx le_rfl

lemma holderSeminorm_congr {k : ℕ} {α : ℝ} {f g : ℂ → ℂ} {Ω : Set ℂ}
    (h : ∀ x ∈ Ω, f x = g x) :
    holderSeminorm k α f Ω = holderSeminorm k α g Ω := by
  have H : ∀ x ∈ Ω, iteratedFDerivWithin ℝ k f Ω x = iteratedFDerivWithin ℝ k g Ω x :=
    fun x hx => iteratedFDerivWithin_congr (fun z hz => h z hz) hx k
  unfold holderSeminorm
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [H x hx, H y hy]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [← H x hx, ← H y hy]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

lemma holderNorm_congr {k : ℕ} {α : ℝ} {f g : ℂ → ℂ} {Ω : Set ℂ}
    (h : ∀ x ∈ Ω, f x = g x) : holderNorm k α f Ω = holderNorm k α g Ω := by
  unfold holderNorm
  exact Finset.sum_congr rfl fun i _ => by
    rw [iterDerivNorm_congr (k := i) h, holderSeminorm_congr (k := i) h]

/-- `∂_z` of a `C^{m+1}` function is `C^m`. -/
lemma contDiff_dzC {m : ℕ} {f : ℂ → ℂ} (hf : ContDiff ℝ (m + 1) f) :
    ContDiff ℝ m (fun z => dzC f z) := by
  have hfd : ContDiff ℝ m (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hrw : (fun z => dzC f z)
      = fun z => (1 / 2 : ℂ) *
          ((fderiv ℝ f z) (1 : ℂ) - Complex.I * (fderiv ℝ f z) Complex.I) := by
    funext z; rfl
  rw [hrw]
  exact contDiff_const.mul ((hfd.clm_apply contDiff_const).sub
    (contDiff_const.mul (hfd.clm_apply contDiff_const)))

private lemma ofReal_add_add_one_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (H : ℝ≥0∞) :
    ENNReal.ofReal a * H + ENNReal.ofReal b * H + H = ENNReal.ofReal (a + b + 1) * H := by
  have h1 : ENNReal.ofReal a + ENNReal.ofReal b + 1 = ENNReal.ofReal (a + b + 1) := by
    rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by linarith) zero_le_one]
  calc ENNReal.ofReal a * H + ENNReal.ofReal b * H + H
      = (ENNReal.ofReal a + ENNReal.ofReal b + 1) * H := by rw [add_mul, add_mul, one_mul]
    _ = ENNReal.ofReal (a + b + 1) * H := by rw [h1]

end Aux

/-- **The `∂̄`-equation on a disc with a gain of exactly one derivative, in the
`C^{k,α}` scale.**  For `0 < α < 1` and every `k` there is `C = C(k,ρ,α)` such
that every `C^{k+1}` function `f` supported in the disc of radius `ρ/2` admits a
solution `u` of `∂̄u = f` on the disc of radius `ρ/2` with

`‖u‖_{C^{k+1,α}(ball 0 (ρ/2))} ≤ C ‖f‖_{C^{k,α}(ℂ)}`.

The natural witness is `u = cauchyTransform ρ f` (which solves the equation by
`dbarC_cauchyTransform`); the `k = 0` case is
`holderNorm_one_cauchyTransform_le`, and the general case is the classical
interior Schauder estimate, obtained by differentiating the `k = 0` statement
(the commutator terms produced by localising with a cutoff are absorbed by the
`C^{k,α}` norm on the larger disc).  The constant is uniform in `f`, which is what
an iteration à la Newlander–Nirenberg on Hölder spaces needs. -/
theorem exists_dbarC_solution_disc_Ck (k : ℕ) {ρ α : ℝ} (hρ : 0 < ρ) (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, ContDiff ℝ (k + 1) f → SupportedInBall (ρ / 2) f →
      ∃ u : ℂ → ℂ, (∀ z : ℂ, ‖z‖ < ρ / 2 → dbarC u z = f z) ∧
        holderNorm (k + 1) α u (Metric.ball 0 (ρ / 2))
          ≤ ENNReal.ofReal C * holderNorm k α f Set.univ := by
  -- The Schauder estimate for the Cauchy potential `cauchyTransform ρ f`, by induction on `k`,
  -- with a constant uniform in `f`.
  have key : ∀ k' : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, ContDiff ℝ (k' + 1) f →
      SupportedInBall (ρ / 2) f →
      holderNorm (k' + 1) α (cauchyTransform ρ f) (Metric.ball 0 (ρ / 2))
        ≤ ENNReal.ofReal C * holderNorm k' α f Set.univ := by
    intro k'
    induction k' with
    | zero =>
      exact holderNorm_one_disc hρ hα hα1
    | succ k ih =>
      -- inductive step: differentiate the `k = 0` estimate
      obtain ⟨Ck, hCkpos, hCk⟩ := ih
      obtain ⟨K, hKpos, hKw⟩ :=
        holderNorm_le_wirtinger (Ω := Metric.ball 0 (ρ / 2)) Metric.isOpen_ball (k + 1) α
      obtain ⟨D, hDpos, hDle⟩ := holderNorm_dzC_le_uniform (k := k) (α := α)
      refine ⟨K * (Ck + Ck * D + 1), by positivity, ?_⟩
      intro f hf hfsupp
      have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
      have hfk : ContDiff ℝ (k + 1) f := hf.of_le (by norm_num)
      have hu : ContDiff ℝ ((k + 1) + 1) (cauchyTransform ρ f) :=
        contDiff_cauchyTransform hf hfsupp
      have hgrad := hKw (cauchyTransform ρ f) hu
      have hfdz : ContDiff ℝ (k + 1) (fun z => dzC f z) := contDiff_dzC hf
      have hfsup : SupportedInBall (ρ / 2) (fun z => dzC f z) :=
        supportedInBall_deriv hf1 hfsupp
      -- the three bounds entering the Wirtinger estimate
      have h1 : holderNorm 0 α (cauchyTransform ρ f) (Metric.ball 0 (ρ / 2))
          ≤ ENNReal.ofReal Ck * holderNorm (k + 1) α f Set.univ := by
        refine le_trans (holderNorm_mono_k (Nat.zero_le (k + 1)) α _ _) ?_
        refine le_trans (hCk f hfk hfsupp) ?_
        exact mul_le_mul_right (holderNorm_mono_k (Nat.le_succ k) α f Set.univ) _
      have h2 : holderNorm (k + 1) α (fun z => dzC (cauchyTransform ρ f) z)
            (Metric.ball 0 (ρ / 2))
          ≤ ENNReal.ofReal (Ck * D) * holderNorm (k + 1) α f Set.univ := by
        -- `∂_z` commutes with the Cauchy potential, so `∂_z (T f) = T (∂_z f)`
        have heq : (fun z => dzC (cauchyTransform ρ f) z)
            = fun z => cauchyTransform ρ (fun w => dzC f w) z :=
          funext fun z => dzC_cauchyTransform_T hf1 z
        rw [heq]
        refine le_trans (hCk (fun z => dzC f z) hfdz hfsup) ?_
        refine le_trans (mul_le_mul_right (hDle f hfk) (ENNReal.ofReal Ck)) ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCkpos.le]
      have h3 : holderNorm (k + 1) α (fun z => dbarC (cauchyTransform ρ f) z)
            (Metric.ball 0 (ρ / 2))
          ≤ holderNorm (k + 1) α f Set.univ := by
        -- `∂̄ (T f) = f` on the disc
        rw [holderNorm_congr (k := k + 1) (α := α)
          (f := fun z => dbarC (cauchyTransform ρ f) z) (g := f) (Ω := Metric.ball 0 (ρ / 2))
          (fun z hz => dbarC_cauchyTransform hρ hf1 hfsupp (by
            rw [Metric.mem_ball, dist_zero_right] at hz; exact hz))]
        exact holderNorm_mono_set isOpen_univ Metric.isOpen_ball (Set.subset_univ _) (k + 1) α f
      calc holderNorm ((k + 1) + 1) α (cauchyTransform ρ f) (Metric.ball 0 (ρ / 2))
          ≤ ENNReal.ofReal K *
              (holderNorm 0 α (cauchyTransform ρ f) (Metric.ball 0 (ρ / 2))
                + holderNorm (k + 1) α (fun z => dzC (cauchyTransform ρ f) z)
                    (Metric.ball 0 (ρ / 2))
                + holderNorm (k + 1) α (fun z => dbarC (cauchyTransform ρ f) z)
                    (Metric.ball 0 (ρ / 2))) := hgrad
        _ ≤ ENNReal.ofReal K * (ENNReal.ofReal Ck * holderNorm (k + 1) α f Set.univ
              + ENNReal.ofReal (Ck * D) * holderNorm (k + 1) α f Set.univ
              + holderNorm (k + 1) α f Set.univ) :=
            mul_le_mul_right (add_le_add (add_le_add h1 h2) h3) _
        _ = ENNReal.ofReal (K * (Ck + Ck * D + 1)) * holderNorm (k + 1) α f Set.univ := by
            rw [ofReal_add_add_one_mul (le_of_lt hCkpos) (by positivity)]
            rw [ENNReal.ofReal_mul hKpos.le, mul_assoc]
  obtain ⟨C, hCpos, hC⟩ := key k
  exact ⟨C, hCpos, fun f hf hfsupp =>
    ⟨cauchyTransform ρ f,
      fun z hz => dbarC_cauchyTransform hρ (hf.of_le (by norm_num)) hfsupp hz,
      hC f hf hfsupp⟩⟩

end Work.CR.Flat.Cauchy
