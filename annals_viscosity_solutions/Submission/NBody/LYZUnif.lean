import Submission.NBody.LYZPhaseB
import Submission.Commons.Analysis.InnerProductSpace.lyz_dyadic_induction_restricted
import Mathlib

/-!
# Liu--Yan--Zhou's Lemma `unif` (Section 6)

Combining `exists_lyz_phaseB_aux` with the dyadic induction
`Commons.Analysis.InnerProductSpace.lyz_dyadic_induction_restricted`, we obtain the two
conclusions of Liu--Yan--Zhou's Lemma `unif`: on `[σ n₀, τ]` the mass length of `γ` is bounded
by `‖γ t - x*‖_[m] (1 + Ψ̄²)` and the normalised direction of `γ t - x*` is within `64 Ψ̄` of the
asymptotic direction `a`.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Liu--Yan--Zhou's Lemma `unif`.**  For an `h`-minimiser `γ` on `[0,τ]` running from `γ 0`
to `x* + 2^n • a`, the dyadic crossing times `σ i` exist and, for every `t ∈ [σ n₀, τ]`,

* `massLength m γ 0 t ≤ ‖γ t - x*‖_[m] * (1 + Ψb (‖γ t - x*‖_[m]) ^ 2)`, and
* `‖(‖γ t - x*‖_[m])⁻¹ • (γ t - x*) - a‖_[m] ≤ 64 * Ψb (‖γ t - x*‖_[m])`. -/
theorem exists_lyz_unif {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 < m i)
    {xstar a : EN E N} {A B M θ : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hM0 : 0 ≤ M) (ha : ‖a‖_[m] = 1)
    {Ψ Ψb : ℝ → ℝ} (hΨnn : ∀ T, 0 ≤ T → 0 ≤ Ψ T)
    (hΨmono : ∀ T T', 0 ≤ T → T ≤ T' → Ψ T ≤ Ψ T')
    (hΨbnn : ∀ t, 0 ≤ Ψb t) (hrel : ∀ t, 0 < t → Real.sqrt (Ψ t / t) ≤ Ψb t)
    (hslow : ∀ s t, 0 < s → s ≤ t → t ≤ 2 * s → Ψb t ≤ 2 * Ψb s)
    (hsumm : Summable fun k : ℕ => Real.sqrt (Ψ ((2:ℝ) ^ k) / (2:ℝ) ^ k))
    (htail : ∀ i : ℕ, lyzTail Ψ i ≤ Ψb ((2:ℝ) ^ i))
    {n₀ n : ℕ} (hn : n₀ ≤ n) {τ : ℝ} {γ : ℝ → EN E N}
    (hτ : 0 < τ) (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hfin : actionOn m h γ 0 τ < ⊤) (hmin : IsHMinimizer m h γ 0 τ)
    (hγτ : γ τ = xstar + (2:ℝ) ^ n • a)
    (h0lt : ‖γ 0 - xstar‖_[m] < (2:ℝ) ^ n₀)
    (hΦ : actionPot m h (γ 0) xstar < ⊤)
    (hAφ : (Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal ≤ A)
    (hΨhalf : ∀ i, n₀ ≤ i → i < n → Ψ ((2:ℝ) ^ (i + 1)) ≤ (2:ℝ) ^ (i + 1) / 2)
    (hx0 : ∀ i, n₀ ≤ i → i < n → ‖γ 0 - xstar‖_[m] ≤ Ψ ((2:ℝ) ^ (i + 1)))
    (hpotB : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ T : ℝ, 0 ≤ T →
        ∫ t in (0:ℝ)..T, U m (xstar + t • b) ≤ (2 * h) * B * Real.log (2 * T + 2 * M + 1))
    (hncB : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ t : ℝ, 0 ≤ t →
        WithoutCollisions (xstar + t • b))
    (hΨlyz : ∀ T : ℝ, Ψ T = lyzPsi A B M T)
    (hθ : 50 * lyzTail Ψ (n₀ + 1) ≤ θ) :
    ∃ σ : ℕ → ℝ,
      σ n = τ ∧
      (∀ i, n₀ ≤ i → i ≤ n → σ i ∈ Set.Icc 0 τ ∧ ‖γ (σ i) - xstar‖_[m] = (2:ℝ) ^ i ∧
        (∀ t ∈ Set.Icc (σ i) τ, (2:ℝ) ^ i ≤ ‖γ t - xstar‖_[m])) ∧
      (∀ i, n₀ ≤ i → i < n → σ i ≤ σ (i + 1)) ∧
      (∀ t ∈ Set.Icc (σ n₀) τ,
        massLength m γ 0 t ≤ ‖γ t - xstar‖_[m] * (1 + Ψb (‖γ t - xstar‖_[m]) ^ 2)) ∧
      (∀ t ∈ Set.Icc (σ n₀) τ,
        ‖(‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar) - a‖_[m]
          ≤ 64 * Ψb (‖γ t - xstar‖_[m])) := by
  classical
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  obtain ⟨σ, τhat, hσn, hσv, hσmono, hτv, hmid, hray, hdirP, hconeAll, hlen_bd⟩ :=
    exists_lyz_phaseB_aux hh hm hA0 hB0 hM0 ha hΨnn hΨbnn hrel hslow hsumm htail hn hτ hac
      hfin hmin hγτ h0lt hΦ hAφ hΨhalf hx0 hpotB hncB hΨlyz hθ
  -- the two norm conversions
  have hΓnorm : ∀ t : ℝ, ‖massScale m (γ t) - massScale m xstar‖ = ‖γ t - xstar‖_[m] := by
    intro t
    rw [← massScale_sub m (γ t) xstar, weightedNorm_eq_norm_massScale hm0]
  have hΓτ : massScale m (γ τ) = massScale m xstar + (2:ℝ) ^ n • massScale m a := by
    rw [hγτ, massScale_add, massScale_smul]
  have hσmem : ∀ i, n₀ ≤ i → i ≤ n → σ i ∈ Set.Icc 0 τ := fun i a b => (hσv i a b).1
  have hσval : ∀ i, n₀ ≤ i → i ≤ n → ‖massScale m (γ (σ i)) - massScale m xstar‖ = (2:ℝ) ^ i :=
    fun i a b => (hΓnorm _).trans (hσv i a b).2.1
  have hσle : ∀ i, n₀ ≤ i → i ≤ n → ∀ t ∈ Set.Icc (σ i) τ,
      (2:ℝ) ^ i ≤ ‖massScale m (γ t) - massScale m xstar‖ := by
    intro i hi0 hin t ht
    rw [hΓnorm]
    exact (hσv i hi0 hin).2.2 t ht
  have hlen_add : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c ≤ τ →
      massLength m γ a c = massLength m γ a b + massLength m γ b c := by
    intro a b c h0 hab hbc hc
    exact massLength_add hm0 hab hbc (hac.mono (by
      rw [uIcc_of_le (hab.trans hbc), uIcc_of_le hτ.le]
      exact Set.Icc_subset_Icc h0 hc))
  have hlen_chord : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ τ →
      ‖massScale m (γ b) - massScale m (γ a)‖ ≤ massLength m γ a b := by
    intro a b h0 hab hb
    have hb_ac : AbsolutelyContinuousOnInterval γ a b := hac.mono (by
      rw [uIcc_of_le hab, uIcc_of_le hτ.le]
      exact Set.Icc_subset_Icc h0 hb)
    have hint : IntervalIntegrable (fun t : ℝ => ‖deriv γ t‖_[m]) volume a b :=
      intervalIntegrable_weightedNorm_deriv hm0 hab hb_ac
    rw [← massScale_sub m (γ b) (γ a), ← weightedNorm_eq_norm_massScale hm0]
    exact weightedNorm_sub_le_massLength hm hab hb_ac
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint)
  have hlen_bound' : ∀ t ∈ Set.Icc (σ n₀) τ,
      massLength m γ 0 t ≤ ‖massScale m (γ t) - massScale m xstar‖
        + Ψ (‖massScale m (γ t) - massScale m xstar‖) := by
    intro t ht
    rw [hΓnorm]
    exact hlen_bd t ht
  have hmain := Commons.Analysis.InnerProductSpace.lyz_dyadic_induction_restricted
    (F := EN E N) (Γ := fun t : ℝ => massScale m (γ t)) (len := massLength m γ)
    (xS := massScale m xstar) (aF := massScale m a) (Ψ := Ψ) (Ψb := Ψb)
    (σ := σ) hΨnn hΨmono hΨbnn hrel hslow hsumm (fun i => htail i)
    hn (le_of_lt hτ) hσn hΓτ hσmem hσval hσle hσmono hlen_add hlen_chord hlen_bound'
    hmid hray
  refine ⟨σ, hσn, hσv, hσmono, ?_, ?_⟩
  · intro t ht
    have h := hmain.1 t ht
    rw [hΓnorm] at h
    exact h
  · intro t ht
    have h := hmain.2 t ht
    have hconv : (‖massScale m (γ t) - massScale m xstar‖)⁻¹
          • (massScale m (γ t) - massScale m xstar) - massScale m a
        = massScale m ((‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar) - a) := by
      rw [hΓnorm, ← massScale_sub m (γ t) xstar, ← massScale_smul, ← massScale_sub]
    rw [hconv, ← weightedNorm_eq_norm_massScale hm0, hΓnorm] at h
    exact h

end Submission.NBody
