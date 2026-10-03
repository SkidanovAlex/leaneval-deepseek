import ChallengeDeps
import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Int.Interval
import Submission.ShiftHole
import Submission.Port.Aesm

/-!
# Elementary single-scale estimates for the bilinear averages

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022), use throughout their reduction of Theorem 1.17 to the integer
shift estimate two elementary facts about the (upper half) bilinear averages

`Ã_N(f,g)(x) = (1/⌊N⌋) ∑_{⌊N⌋/2 < n ≤ ⌊N⌋} f(T^{P₁(n)}x) g(T^{P₂(n)}x)`:

* **(anf)** (their equation (anf), for a H\"older tuple): for any `1 ≤ q` with
  `1/q = 1/q₁ + 1/q₂`,
  `‖Ã_N(f,g)‖_{L^q(X)} ≤ ‖f‖_{L^{q₁}(X)} ‖g‖_{L^{q₂}(X)}`,
  and the same for the full average `A_N`.  (Hölder's inequality applied to each term of the
  average, followed by the triangle inequality in `L^q` and the fact that `T^{P(n)}` is measure
  preserving.)
* **(varsum)** (their equation (varsum)): the variational norm of a family of functions supported
  at finitely many scales is dominated by the `ℓ¹` sum of the pointwise norms; at the `L^p` level
  this converts the `(Log N)^{-10}` error terms of their major-arc reduction into a single
  summable contribution.

Nothing here needs more than the elementary theory of `eLpNorm`.
-/

set_option maxHeartbeats 2000000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

/-- The extended norm of the complex number `4`. -/
private lemma enorm_four : ‖(4 : ℂ)‖ₑ = (4 : ℝ≥0∞) := by
  rw [enorm_eq_nnnorm, Complex.nnnorm_ofNat, ENNReal.coe_ofNat]

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {μ : Measure 𝓧}

/-! ## The arithmetic of the normalising factor `⌊N⌋⁻¹` -/

/-- The scalar `((m : ℂ))⁻¹` has extended norm `ofReal (m : ℝ)⁻¹`. -/
lemma enorm_inv_natCast (m : ℕ) : ‖(((m : ℂ))⁻¹)‖ₑ = ENNReal.ofReal ((m : ℝ)⁻¹) := by
  rw [← ofReal_norm]; congr 1; rw [norm_inv, Complex.norm_natCast]

/-- The normalising factor of the halved average, times the number of its terms, is at most one:
`‖⌊N⌋⁻¹‖ · #(Ioc ⌊N⌋/2 ⌊N⌋) ≤ 1`. -/
lemma enorm_inv_mul_card_Ioc_le (m : ℕ) :
    ‖(((m : ℂ))⁻¹)‖ₑ * ((Finset.Ioc (m / 2) m).card : ℝ≥0∞) ≤ 1 := by
  have hcard : ((Finset.Ioc (m / 2) m).card : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by
    exact_mod_cast (show (Finset.Ioc (m / 2) m).card ≤ m from by
      have h : Finset.Ioc (m / 2) m ⊆ Finset.Ioc 0 m := by
        intro n hn; simp only [Finset.mem_Ioc] at hn ⊢; omega
      calc (Finset.Ioc (m / 2) m).card ≤ (Finset.Ioc 0 m).card := Finset.card_le_card h
        _ = m := by simp)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · refine (mul_le_mul' le_rfl hcard).trans ?_
    exact le_of_eq (by
      rw [enorm_inv_natCast, ENNReal.ofReal_inv_of_pos (by exact_mod_cast hm),
        ENNReal.ofReal_natCast]
      exact ENNReal.inv_mul_cancel (by simp [hm.ne']) (by simp))

/-- The normalising factor of the full average, times the number of its terms, is at most one:
`‖⌊N⌋⁻¹‖ · #(Icc 1 ⌊N⌋) ≤ 1`. -/
lemma enorm_inv_mul_card_Icc_le (m : ℕ) :
    ‖(((m : ℂ))⁻¹)‖ₑ * ((Finset.Icc 1 m).card : ℝ≥0∞) ≤ 1 := by
  have hcard : ((Finset.Icc 1 m).card : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by
    exact_mod_cast (show (Finset.Icc 1 m).card ≤ m from by
      have h : Finset.Icc 1 m ⊆ Finset.Ioc 0 m := by
        intro n hn; simp only [Finset.mem_Icc] at hn; simp only [Finset.mem_Ioc]; omega
      calc (Finset.Icc 1 m).card ≤ (Finset.Ioc 0 m).card := Finset.card_le_card h
        _ = m := by simp)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · refine (mul_le_mul' le_rfl hcard).trans ?_
    exact le_of_eq (by
      rw [enorm_inv_natCast, ENNReal.ofReal_inv_of_pos (by exact_mod_cast hm),
        ENNReal.ofReal_natCast]
      exact ENNReal.inv_mul_cancel (by simp [hm.ne']) (by simp))

/-! ## (anf): the single-scale Hölder bound -/

/-- The composition of an `L^q` function with `T^k` is `L^q`, for `T` measure preserving. -/
lemma memLp_comp_zpow {T : 𝓧 ≃ᵐ 𝓧} (hT : MeasurePreserving T μ μ) {f : 𝓧 → ℂ}
    {q : ℝ≥0∞} (hf : MemLp f q μ) (k : ℤ) :
    MemLp (fun y => f ((T ^ k : 𝓧 ≃ 𝓧) y)) q μ := by
  rw [show (fun y => f ((T ^ k : 𝓧 ≃ 𝓧) y))
      = f ∘ (fun y => (T ^ k : 𝓧 ≃ 𝓧) y) from rfl]
  exact hf.comp_measurePreserving (measurePreserving_zpow_apply hT k)

/-- The `L^q` norm of a single product term `x ↦ f(T^a x) g(T^b x)` is at most
`‖f‖_{L^{q₁}} ‖g‖_{L^{q₂}}` when `1/q = 1/q₁ + 1/q₂`, by Hölder and measure preservation. -/
lemma eLpNorm_comp_mul_le (T : 𝓧 ≃ᵐ 𝓧) (hT : MeasurePreserving T μ μ) (P₁ P₂ : ℤ[X]) (n : ℕ)
    {q q₁ q₂ : ℝ≥0∞} (hH : q₁⁻¹ + q₂⁻¹ = q⁻¹)
    {f g : 𝓧 → ℂ} (hf : MemLp f q₁ μ) (hg : MemLp g q₂ μ) :
    eLpNorm (fun y => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)
        * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)) q μ
      ≤ eLpNorm f q₁ μ * eLpNorm g q₂ μ := by
  have hf' := memLp_comp_zpow (μ := μ) hT hf (P₁.eval (n : ℤ))
  have hg' := memLp_comp_zpow (μ := μ) hT hg (P₂.eval (n : ℤ))
  have hcomp₁ : eLpNorm (fun y => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)) q₁ μ
      = eLpNorm f q₁ μ := by
    rw [show (fun y => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y))
        = f ∘ (fun y => (T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y) from rfl]
    exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
      (measurePreserving_zpow_apply hT _)
  have hcomp₂ : eLpNorm (fun y => g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)) q₂ μ
      = eLpNorm g q₂ μ := by
    rw [show (fun y => g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y))
        = g ∘ (fun y => (T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y) from rfl]
    exact eLpNorm_comp_measurePreserving hg.aestronglyMeasurable
      (measurePreserving_zpow_apply hT _)
  have hholder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (fun a b : ℂ => a * b) 1 (by first | fun_prop | exact continuous_mul | exact continuous_inner | (simp only [Function.uncurry_def]; fun_prop)) hf'.aestronglyMeasurable hg'.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => by simp)) (hpqr := ⟨hH⟩)
  rw [hcomp₁, hcomp₂] at hholder
  simpa using hholder

/-- **(anf)** for the upper half average: for a Hölder tuple `1/q = 1/q₁ + 1/q₂` with `1 ≤ q`,
`‖Ã_m(f,g)‖_{L^q} ≤ ‖f‖_{L^{q₁}} ‖g‖_{L^{q₂}}`. -/
theorem eLpNorm_Ahalf_le (T : 𝓧 ≃ᵐ 𝓧) (hT : MeasurePreserving T μ μ) (m : ℕ)
    (P₁ P₂ : ℤ[X]) {q q₁ q₂ : ℝ≥0∞} (hH : q₁⁻¹ + q₂⁻¹ = q⁻¹) (h1q : 1 ≤ q)
    {f g : 𝓧 → ℂ} (hf : MemLp f q₁ μ) (hg : MemLp g q₂ μ) :
    eLpNorm (Ahalf T m P₁ P₂ f g) q μ ≤ eLpNorm f q₁ μ * eLpNorm g q₂ μ := by
  have hsmul : Ahalf T m P₁ P₂ f g
      = ((m : ℂ))⁻¹ • (∑ n ∈ Finset.Ioc (m / 2) m,
          fun y => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)
            * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)) := by
    funext y
    simp only [Ahalf, Ablock, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      Complex.ofReal_inv, Complex.ofReal_natCast]
  have hsum : eLpNorm (∑ n ∈ Finset.Ioc (m / 2) m,
        fun y => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)
          * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)) q μ
      ≤ ((Finset.Ioc (m / 2) m).card : ℝ≥0∞) * (eLpNorm f q₁ μ * eLpNorm g q₂ μ) := by
    refine (eLpNorm_sum_le h1q).trans ?_
    · calc ∑ n ∈ Finset.Ioc (m / 2) m,
            eLpNorm (fun y => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)
              * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)) q μ
          ≤ ∑ _n ∈ Finset.Ioc (m / 2) m, (eLpNorm f q₁ μ * eLpNorm g q₂ μ) :=
            Finset.sum_le_sum (fun n _ => eLpNorm_comp_mul_le T hT P₁ P₂ n hH hf hg)
        _ = ((Finset.Ioc (m / 2) m).card : ℝ≥0∞) * (eLpNorm f q₁ μ * eLpNorm g q₂ μ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  calc eLpNorm (Ahalf T m P₁ P₂ f g) q μ
      = ‖(((m : ℂ))⁻¹)‖ₑ * eLpNorm (∑ n ∈ Finset.Ioc (m / 2) m,
          fun y => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)
            * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)) q μ := by
        rw [hsmul, eLpNorm_const_smul]
    _ ≤ ‖(((m : ℂ))⁻¹)‖ₑ
          * (((Finset.Ioc (m / 2) m).card : ℝ≥0∞) * (eLpNorm f q₁ μ * eLpNorm g q₂ μ)) :=
        mul_le_mul_of_nonneg_left hsum bot_le
    _ = (‖(((m : ℂ))⁻¹)‖ₑ * ((Finset.Ioc (m / 2) m).card : ℝ≥0∞))
          * (eLpNorm f q₁ μ * eLpNorm g q₂ μ) := by rw [mul_assoc]
    _ ≤ 1 * (eLpNorm f q₁ μ * eLpNorm g q₂ μ) :=
        mul_le_mul_of_nonneg_right (enorm_inv_mul_card_Ioc_le m) bot_le
    _ = eLpNorm f q₁ μ * eLpNorm g q₂ μ := one_mul _

/-- **(anf)** for the upper half average at a real scale. -/
theorem eLpNorm_AhalfR_le (T : 𝓧 ≃ᵐ 𝓧) (hT : MeasurePreserving T μ μ) (N : ℝ≥0)
    (P₁ P₂ : ℤ[X]) {q q₁ q₂ : ℝ≥0∞} (hH : q₁⁻¹ + q₂⁻¹ = q⁻¹) (h1q : 1 ≤ q)
    {f g : 𝓧 → ℂ} (hf : MemLp f q₁ μ) (hg : MemLp g q₂ μ) :
    eLpNorm (AhalfR T N P₁ P₂ f g) q μ ≤ eLpNorm f q₁ μ * eLpNorm g q₂ μ :=
  eLpNorm_Ahalf_le T hT (Nat.floor N) P₁ P₂ hH h1q hf hg

/-- **(anf)** for the full average: for a Hölder tuple `1/q = 1/q₁ + 1/q₂` with `1 ≤ q`,
`‖A_N(f,g)‖_{L^q} ≤ ‖f‖_{L^{q₁}} ‖g‖_{L^{q₂}}`. -/
theorem eLpNorm_A_le (T : 𝓧 ≃ᵐ 𝓧) (hT : MeasurePreserving T μ μ) (N : ℝ≥0)
    (P₁ P₂ : ℤ[X]) {q q₁ q₂ : ℝ≥0∞} (hH : q₁⁻¹ + q₂⁻¹ = q⁻¹) (h1q : 1 ≤ q)
    {f g : 𝓧 → ℂ} (hf : MemLp f q₁ μ) (hg : MemLp g q₂ μ) :
    eLpNorm (A T N P₁ P₂ f g) q μ ≤ eLpNorm f q₁ μ * eLpNorm g q₂ μ := by
  set m : ℕ := Nat.floor N with hm
  have hsmul : A T N P₁ P₂ f g
      = ((m : ℂ))⁻¹ • (∑ n ∈ Finset.Icc 1 m,
          fun y => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)
            * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)) := by
    funext y
    simp only [A, hm, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Complex.ofReal_inv,
      Complex.ofReal_natCast]
  have hsum : eLpNorm (∑ n ∈ Finset.Icc 1 m,
        fun y => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)
          * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)) q μ
      ≤ ((Finset.Icc 1 m).card : ℝ≥0∞) * (eLpNorm f q₁ μ * eLpNorm g q₂ μ) := by
    refine (eLpNorm_sum_le h1q).trans ?_
    · calc ∑ n ∈ Finset.Icc 1 m,
            eLpNorm (fun y => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)
              * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)) q μ
          ≤ ∑ _n ∈ Finset.Icc 1 m, (eLpNorm f q₁ μ * eLpNorm g q₂ μ) :=
            Finset.sum_le_sum (fun n _ => eLpNorm_comp_mul_le T hT P₁ P₂ n hH hf hg)
        _ = ((Finset.Icc 1 m).card : ℝ≥0∞) * (eLpNorm f q₁ μ * eLpNorm g q₂ μ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  calc eLpNorm (A T N P₁ P₂ f g) q μ
      = ‖(((m : ℂ))⁻¹)‖ₑ * eLpNorm (∑ n ∈ Finset.Icc 1 m,
          fun y => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)
            * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) y)) q μ := by
        rw [hsmul, eLpNorm_const_smul]
    _ ≤ ‖(((m : ℂ))⁻¹)‖ₑ
          * (((Finset.Icc 1 m).card : ℝ≥0∞) * (eLpNorm f q₁ μ * eLpNorm g q₂ μ)) :=
        mul_le_mul_of_nonneg_left hsum bot_le
    _ = (‖(((m : ℂ))⁻¹)‖ₑ * ((Finset.Icc 1 m).card : ℝ≥0∞))
          * (eLpNorm f q₁ μ * eLpNorm g q₂ μ) := by rw [mul_assoc]
    _ ≤ 1 * (eLpNorm f q₁ μ * eLpNorm g q₂ μ) :=
        mul_le_mul_of_nonneg_right (enorm_inv_mul_card_Icc_le m) bot_le
    _ = eLpNorm f q₁ μ * eLpNorm g q₂ μ := one_mul _

/-! ## (varsum): the `ℓ¹`-bound for the variational norm at finitely many scales -/

/-- A sequence that is a single spike `n ↦ if n = k then c else 0` has variational norm at most
`4‖c‖` (`r ≥ 1`): it is the difference of two step sequences, each of which has variational norm
at most `2‖c‖`. -/
lemma variationalNorm_spike_le {r : ℝ≥0} (hr : 1 ≤ r) (k : ℕ) (c : ℂ) :
    variationalNorm r (fun n => if n = k then c else 0) ≤ 4 * ‖c‖ₑ := by
  have hdecomp : (fun n => if n = k then c else 0)
      = (fun n => if n < k + 1 then c else 0) + (fun n => if n < k then -c else 0) := by
    funext n
    simp only [Pi.add_apply]
    by_cases h1 : n < k
    · rw [if_neg (by omega), if_pos h1, if_pos (by omega)]
      simp
    · by_cases h2 : n = k
      · rw [if_pos h2, if_pos (by omega), if_neg (by omega)]
        simp
      · rw [if_neg h2, if_neg (by omega), if_neg (by omega)]
        simp
  calc variationalNorm r (fun n => if n = k then c else 0)
      = variationalNorm r ((fun n => if n < k + 1 then c else 0)
          + (fun n => if n < k then -c else 0)) := by rw [hdecomp]
    _ ≤ variationalNorm r (fun n => if n < k + 1 then c else 0)
          + variationalNorm r (fun n => if n < k then -c else 0) :=
        variationalNorm_add_le hr _ _
    _ ≤ 2 * ‖c‖ₑ + 2 * ‖-c‖ₑ :=
        add_le_add (variationalNorm_step_le hr (k + 1) c) (variationalNorm_step_le hr k (-c))
    _ = 4 * ‖c‖ₑ := by rw [enorm_neg]; ring

/-- **(varsum)**, pointwise form: a sequence supported in the finite set `s` has variational norm
at most the `ℓ¹`-sum of its nonzero entries. -/
lemma variationalNorm_le_sum_enorm {r : ℝ≥0} (hr : 1 ≤ r) {u : ℕ → ℂ} {s : Finset ℕ}
    (hu : ∀ n, n ∉ s → u n = 0) :
    variationalNorm r u ≤ ∑ n ∈ s, 4 * ‖u n‖ₑ := by
  set b : ℕ → ℕ → ℂ := fun k n => if n = k then u k else 0 with hbdef
  have hb0 : ∀ n, ∃ K, ∀ k ≥ K, b k n = 0 := by
    intro n
    exact ⟨n + 1, fun k hk => by simp only [hbdef]; exact if_neg (by omega)⟩
  have hsum : u = fun n => ∑' k, b k n := by
    funext n
    rw [tsum_eq_single n (fun k hk => by simp only [hbdef]; exact if_neg (Ne.symm hk))]
    simp only [hbdef, if_pos rfl]
  have hspike : ∀ k, variationalNorm r (fun n => b k n) ≤ if k ∈ s then 4 * ‖u k‖ₑ else 0 := by
    intro k
    by_cases hk : k ∈ s
    · rw [if_pos hk]
      exact variationalNorm_spike_le hr k (u k)
    · rw [if_neg hk]
      have hz : u k = 0 := hu k hk
      have hz' : (fun n => b k n) = 0 := by
        funext n; simp only [hbdef]; rw [hz]; simp
      have hzero : variationalNorm r (0 : ℕ → ℂ) = 0 := by
        have h := variationalNorm_smul (r := r) hr (0 : ℂ) (0 : ℕ → ℂ)
        simpa using h
      rw [hz', hzero]
  calc variationalNorm r u
      = variationalNorm r (fun n => ∑' k, b k n) := by rw [hsum]
    _ ≤ ∑' k, variationalNorm r (fun n => b k n) := variationalNorm_tsum_le hr hb0
    _ ≤ ∑' k, (if k ∈ s then 4 * ‖u k‖ₑ else 0) := ENNReal.tsum_le_tsum hspike
    _ = ∑ k ∈ s, 4 * ‖u k‖ₑ := by
        rw [tsum_eq_sum (s := s) (fun k hk => if_neg hk)]
        exact Finset.sum_congr rfl (fun k hk => if_pos hk)

/-- Pointwise form of **(varsum)** with the constant absorbed into a complex scalar. -/
lemma variationalNorm_le_sum_smul_enorm {r : ℝ≥0} (hr : 1 ≤ r) {u : ℕ → ℂ} {s : Finset ℕ}
    (hu : ∀ n, n ∉ s → u n = 0) :
    variationalNorm r u ≤ ∑ n ∈ s, ‖(4 : ℂ) • u n‖ₑ := by
  refine (variationalNorm_le_sum_enorm hr hu).trans (Finset.sum_le_sum ?_)
  intro n _
  rw [enorm_smul, enorm_four]

/-- **(varsum)**, `L^p` form: the `L^p` norm of the variational norm of a family supported at
finitely many scales is at most the sum of the `L^p` norms of its members. -/
theorem eLpNorm_variationalNorm_le_sum {r : ℝ≥0} (hr : 1 ≤ r) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : ℕ → 𝓧 → ℂ} {s : Finset ℕ} (hu : ∀ n, n ∉ s → u n = 0)
    (hmeas : ∀ n ∈ s, AEStronglyMeasurable (u n) μ) :
    eLpNorm (fun x => variationalNorm r (fun n => u n x)) p μ
      ≤ ∑ n ∈ s, 4 * eLpNorm (fun x => u n x) p μ := by
  have hum : ∀ n, AEMeasurable (u n) μ := fun n => by
    by_cases hn : n ∈ s
    · exact (hmeas n hn).aemeasurable
    · rw [hu n hn]; exact aemeasurable_const
  have hpt : ∀ x, ‖(fun x => variationalNorm r (fun n => u n x)) x‖ₑ
      ≤ ‖(∑ n ∈ s, fun x => ‖(4 : ℂ) • u n x‖ₑ) x‖ₑ := fun x => by
    rw [Finset.sum_apply]
    exact variationalNorm_le_sum_smul_enorm (r := r) hr (fun n hn => congrFun (hu n hn) x)
  have hmono : eLpNorm (fun x => variationalNorm r (fun n => u n x)) p μ
      ≤ eLpNorm (∑ n ∈ s, fun x => ‖(4 : ℂ) • u n x‖ₑ) p μ :=
    eLpNorm_mono_enorm (hf := (aemeasurable_variationalNorm
      (lt_of_lt_of_le zero_lt_one hr) hum).aestronglyMeasurable) hpt
  have hsum : eLpNorm (∑ n ∈ s, fun x => ‖(4 : ℂ) • u n x‖ₑ) p μ
      ≤ ∑ n ∈ s, 4 * eLpNorm (fun x => u n x) p μ :=
    (eLpNorm_sum_le hp).trans
      (le_of_eq (Finset.sum_congr rfl (fun n hn => by
        rw [eLpNorm_enorm (f := fun x => (4 : ℂ) • u n x) (hf := ((hmeas n hn).const_smul (4 : ℂ))),
          show (fun x => (4 : ℂ) • u n x) = (4 : ℂ) • (fun x => u n x) from rfl,
          eLpNorm_const_smul, enorm_four])))
  exact hmono.trans hsum

/-! ## The assembly step of §5: major-arc estimate + summable error

Section 5 of the paper splits each halved average `Ã_N(f,g)` into its major arc part and a
minor arc remainder whose `ℓ^p` norm is summable over the lacunary set of scales; the variational
estimate for the halved averages is then read off from the variational estimate for the major arc
parts.  The following lemma is that (purely formal) step: it is stated for an abstract pair of
families `u` (the averages) and `w` (their major arc parts) which agree outside a finite set of
scales, with `eLpNorm` errors `ε n` whose sum is bounded by `C`. -/

/-- **Assembly of §5.**  Let `u` be a family of functions on `ℤ` (the halved averages at the
clamped lacunary scales) and `w` its major arc part, agreeing outside the finite set `s` of scales,
with `‖u n - w n‖_{ℓ^p} ≤ ε n` on `s`.  If the variational estimate `‖V^r(w)‖_{ℓ^p} ≤ M` holds and
`∑_{n ∈ s} ε n ≤ C`, then `‖V^r(u)‖_{ℓ^p} ≤ M + 4C`. -/
theorem eLpNorm_variationalNorm_le_of_approx {p : ℝ≥0∞} (hp : 1 ≤ p) {r : ℝ≥0} (hr : 1 ≤ r)
    {u w : ℕ → ℤ → ℂ} {s : Finset ℕ} {ε : ℕ → ℝ≥0∞} {M C : ℝ≥0∞}
    (hmw : AEStronglyMeasurable (fun x => variationalNorm r (fun n => w n x)) Measure.count)
    (hme : AEStronglyMeasurable
      (fun x => variationalNorm r (fun n => u n x - w n x)) Measure.count)
    (hmeas : ∀ n ∈ s, AEStronglyMeasurable (fun x => u n x - w n x) Measure.count)
    (hsupp : ∀ n, n ∉ s → u n = w n)
    (happrox : ∀ n ∈ s, eLpNorm (fun x => u n x - w n x) p Measure.count ≤ ε n)
    (hsum : ∑ n ∈ s, ε n ≤ C)
    (hmajor : eLpNorm (fun x => variationalNorm r (fun n => w n x)) p Measure.count ≤ M) :
    eLpNorm (fun x => variationalNorm r (fun n => u n x)) p Measure.count ≤ M + 4 * C := by
  have hpt : ∀ x, variationalNorm r (fun n => u n x)
      ≤ variationalNorm r (fun n => w n x) + variationalNorm r (fun n => u n x - w n x) := by
    intro x
    have hdecomp : (fun n => u n x) = (fun n => w n x) + (fun n => u n x - w n x) := by
      funext n
      simp only [Pi.add_apply]
      ring
    rw [hdecomp]
    exact variationalNorm_add_le hr _ _
  have hzero : ∀ n, n ∉ s → (fun x => u n x - w n x) = 0 := by
    intro n hn
    funext x
    simp only [Pi.zero_apply]
    rw [hsupp n hn]
    simp
  calc eLpNorm (fun x => variationalNorm r (fun n => u n x)) p Measure.count
      ≤ eLpNorm (fun x => variationalNorm r (fun n => w n x)
          + variationalNorm r (fun n => u n x - w n x)) p Measure.count :=
        eLpNorm_mono_enorm (hf := by pw_aesm) hpt
    _ ≤ M + eLpNorm (fun x => variationalNorm r (fun n => u n x - w n x)) p Measure.count :=
        (eLpNorm_add_le hp).trans (add_le_add hmajor le_rfl)
    _ ≤ M + ∑ n ∈ s, 4 * eLpNorm (fun x => u n x - w n x) p Measure.count :=
        add_le_add le_rfl (eLpNorm_variationalNorm_le_sum (r := r) (p := p) hr hp
          (u := fun n x => u n x - w n x) hzero hmeas)
    _ ≤ M + (∑ n ∈ s, ε n) * 4 := by
        refine add_le_add le_rfl ?_
        rw [← Finset.mul_sum, mul_comm (∑ n ∈ s, ε n) 4]
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun n hn => happrox n hn)) bot_le
    _ ≤ M + 4 * C := by
        refine add_le_add le_rfl ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hsum (bot_le)

/-! ## The geometric bookkeeping of the paraproduct summation

Section 5 of the paper, after applying the variational paraproduct estimates, has to sum the
geometric weights `2^{-8ρ max(l,s₁,s₂)}` over the scales `s₁, s₂ ∈ [-u, l]`, where `u = ⌊C₂ 2^{2ρl}⌋`
is the number of available continuous scales.  The following lemma is that summation: if
`u + l + 1 ≤ 2^{2ρl}` (which is the paper's cardinality bound for the scales) then the double sum of
the weights is at most `2^{-ρl}`.  This is the elementary estimate that makes the exponential gain
`2^{-ρl}` of `(l1l2-alt)` possible. -/

/-- **The geometric summation of §5.** -/
theorem sum_two_rpow_neg_max_le {ρ : ℝ} (hρ : 0 < ρ) (u l : ℕ)
    (hu : (u : ℝ) + (l : ℝ) + 1 ≤ (2 : ℝ) ^ (2 * ρ * (l : ℝ))) :
    ∑ s₁ ∈ Finset.Icc (-(u : ℤ)) (l : ℤ),
        ∑ s₂ ∈ Finset.Icc (-(u : ℤ)) (l : ℤ),
          (2 : ℝ) ^ (-(8 * ρ * (((max (l : ℤ) (max s₁ s₂) : ℤ)) : ℝ)))
      ≤ (2 : ℝ) ^ (-(ρ * (l : ℝ))) := by
  have hcard : (Finset.Icc (-(u : ℤ)) (l : ℤ)).card = u + l + 1 := by
    rw [Int.card_Icc]
    have h : ((l : ℤ) + 1 - (-(u : ℤ))) = ((u + l + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [h, Int.toNat_natCast]
  have htwo : (1 : ℝ) < 2 := by norm_num
  -- each term is at most `2^{-8ρl}`
  have hterm : ∀ s₁ ∈ Finset.Icc (-(u : ℤ)) (l : ℤ), ∀ s₂ ∈ Finset.Icc (-(u : ℤ)) (l : ℤ),
      (2 : ℝ) ^ (-(8 * ρ * ((((max (l : ℤ) (max s₁ s₂)) : ℤ)) : ℝ)))
        ≤ (2 : ℝ) ^ (-(8 * ρ * (l : ℝ))) := by
    intro s₁ hs₁ s₂ hs₂
    have h1 : (l : ℝ) ≤ (((max (l : ℤ) (max s₁ s₂) : ℤ)) : ℝ) := by
      have : (l : ℤ) ≤ max (l : ℤ) (max s₁ s₂) := le_max_left _ _
      exact_mod_cast this
    refine Real.rpow_le_rpow_of_exponent_le htwo.le ?_
    nlinarith [h1, hρ]
  have hmain : ∑ s₁ ∈ Finset.Icc (-(u : ℤ)) (l : ℤ),
        ∑ s₂ ∈ Finset.Icc (-(u : ℤ)) (l : ℤ),
          (2 : ℝ) ^ (-(8 * ρ * (((max (l : ℤ) (max s₁ s₂) : ℤ)) : ℝ)))
      ≤ (((u + l + 1 : ℕ)) : ℝ) ^ 2 * (2 : ℝ) ^ (-(8 * ρ * (l : ℝ))) := by
    calc ∑ s₁ ∈ Finset.Icc (-(u : ℤ)) (l : ℤ),
          ∑ s₂ ∈ Finset.Icc (-(u : ℤ)) (l : ℤ),
            (2 : ℝ) ^ (-(8 * ρ * (((max (l : ℤ) (max s₁ s₂) : ℤ)) : ℝ)))
        ≤ ∑ _s₁ ∈ Finset.Icc (-(u : ℤ)) (l : ℤ),
            ∑ _s₂ ∈ Finset.Icc (-(u : ℤ)) (l : ℤ), (2 : ℝ) ^ (-(8 * ρ * (l : ℝ))) :=
          Finset.sum_le_sum (fun s₁ hs₁ => Finset.sum_le_sum (fun s₂ hs₂ =>
            hterm s₁ hs₁ s₂ hs₂))
      _ = ((Finset.Icc (-(u : ℤ)) (l : ℤ)).card : ℝ)
            * (((Finset.Icc (-(u : ℤ)) (l : ℤ)).card : ℝ) * (2 : ℝ) ^ (-(8 * ρ * (l : ℝ)))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = (((u + l + 1 : ℕ)) : ℝ) ^ 2 * (2 : ℝ) ^ (-(8 * ρ * (l : ℝ))) := by
          rw [hcard]; ring
  refine hmain.trans ?_
  have hsq : (((u + l + 1 : ℕ)) : ℝ) ^ 2
      ≤ ((2 : ℝ) ^ (2 * ρ * (l : ℝ))) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ((u + l + 1 : ℕ) : ℝ) := by positivity
    have hu' : (((u + l + 1 : ℕ)) : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * (l : ℝ)) := by
      push_cast
      exact hu
    exact pow_le_pow_left₀ h0 hu' 2
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(8 * ρ * (l : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  calc (((u + l + 1 : ℕ)) : ℝ) ^ 2 * (2 : ℝ) ^ (-(8 * ρ * (l : ℝ)))
      ≤ ((2 : ℝ) ^ (2 * ρ * (l : ℝ))) ^ 2 * (2 : ℝ) ^ (-(8 * ρ * (l : ℝ))) :=
        mul_le_mul_of_nonneg_right hsq hpos.le
    _ = (2 : ℝ) ^ (4 * ρ * (l : ℝ)) * (2 : ℝ) ^ (-(8 * ρ * (l : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        ring_nf
    _ = (2 : ℝ) ^ (4 * ρ * (l : ℝ) + -(8 * ρ * (l : ℝ))) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ (-(ρ * (l : ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have : (0 : ℝ) ≤ ρ * (l : ℝ) := by positivity
        linarith

