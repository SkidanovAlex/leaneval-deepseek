import Submission.NBody.LYZNoColl
import Submission.NBody.LYZObsApply
import Submission.NBody.LYZPsi
import Submission.Commons.Analysis.InnerProductSpace.exists_lyz_crossings
import Mathlib

/-!
# The dyadic induction of Liu--Yan--Zhou (Section 6, first half)

For an `h`-minimiser `γ` on `[0,τ]` ending at `x* + 2^n • a`, this module constructs the
last-crossing times `σ i` (`‖γ (σ i) - x*‖_[m] = 2^i`) and `τhat i`, and proves by downward
induction on `i` that

* the mass length of `γ|[0, σ i]` is at most `2^i + Ψ(2^i)`, and
* the normalised direction `2^{-i} (γ (σ i) - x*)` is within `8 · lyzTail Ψ (i+1)` of `a`.

This is Step 1 of Liu--Yan--Zhou's proof of Lemma 6.1.
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

/-- The dyadic tail sums of `Ψ`: `lyzTail Ψ i = ∑_k √(Ψ (2^{i+k}) / 2^{i+k})`. -/
noncomputable def lyzTail (Ψ : ℝ → ℝ) (i : ℕ) : ℝ :=
  ∑' k : ℕ, Real.sqrt (Ψ ((2:ℝ) ^ (i + k)) / (2:ℝ) ^ (i + k))

lemma lyzTail_nonneg {Ψ : ℝ → ℝ} (h : ∀ t, 0 ≤ t → 0 ≤ Ψ t) (i : ℕ) : 0 ≤ lyzTail Ψ i :=
  tsum_nonneg fun k => Real.sqrt_nonneg _

lemma summable_lyzTail {Ψ : ℝ → ℝ}
    (hsumm : Summable fun k : ℕ => Real.sqrt (Ψ ((2:ℝ) ^ k) / (2:ℝ) ^ k)) (i : ℕ) :
    Summable fun k : ℕ => Real.sqrt (Ψ ((2:ℝ) ^ (i + k)) / (2:ℝ) ^ (i + k)) :=
  hsumm.comp_injective (i := fun k : ℕ => i + k) (fun _ _ hab => Nat.add_left_cancel hab)

lemma lyzTail_succ {Ψ : ℝ → ℝ}
    (hsumm : Summable fun k : ℕ => Real.sqrt (Ψ ((2:ℝ) ^ k) / (2:ℝ) ^ k)) (i : ℕ) :
    lyzTail Ψ i = Real.sqrt (Ψ ((2:ℝ) ^ i) / (2:ℝ) ^ i) + lyzTail Ψ (i + 1) := by
  have hs := summable_lyzTail hsumm i
  have h := hs.tsum_eq_zero_add
  have key : (∑' k : ℕ, Real.sqrt (Ψ ((2:ℝ) ^ (i + k)) / (2:ℝ) ^ (i + k)))
      = Real.sqrt (Ψ ((2:ℝ) ^ i) / (2:ℝ) ^ i)
        + (∑' k : ℕ, Real.sqrt (Ψ ((2:ℝ) ^ ((i + 1) + k)) / (2:ℝ) ^ ((i + 1) + k))) := by
    rw [h, Nat.add_zero]
    exact congrArg (fun z => Real.sqrt (Ψ ((2:ℝ) ^ i) / (2:ℝ) ^ i) + z)
      (tsum_congr fun k => by rw [show i + (k + 1) = (i + 1) + k by omega])
  rw [lyzTail, key, lyzTail]

lemma lyzTail_le_succ {Ψ : ℝ → ℝ} (h : ∀ t, 0 ≤ t → 0 ≤ Ψ t)
    (hsumm : Summable fun k : ℕ => Real.sqrt (Ψ ((2:ℝ) ^ k) / (2:ℝ) ^ k)) (i : ℕ) :
    lyzTail Ψ (i + 1) ≤ lyzTail Ψ i := by
  rw [lyzTail_succ hsumm i]
  have h1 := lyzTail_nonneg h (i + 1)
  have h2 := Real.sqrt_nonneg (Ψ ((2:ℝ) ^ i) / (2:ℝ) ^ i)
  linarith

lemma lyzTail_mono {Ψ : ℝ → ℝ} (h : ∀ t, 0 ≤ t → 0 ≤ Ψ t)
    (hsumm : Summable fun k : ℕ => Real.sqrt (Ψ ((2:ℝ) ^ k) / (2:ℝ) ^ k)) {i j : ℕ}
    (hij : i ≤ j) : lyzTail Ψ j ≤ lyzTail Ψ i := by
  induction hij with
  | refl => exact le_rfl
  | step hik ih => exact (lyzTail_le_succ h hsumm _).trans ih

/-- **Direction estimate from a midpoint estimate.** -/
lemma norm_inv_smul_sub_inv_smul_le_half {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u w : F} {r s δ : ℝ} (hr : 0 < r) (hs : 0 < s) (hur : ‖u‖ = r) (hws : ‖w‖ = s)
    (h : ‖u - ((1:ℝ) / 2) • w‖ ≤ δ) :
    ‖r⁻¹ • u - s⁻¹ • w‖ ≤ 2 * δ / r := by
  have hsme : r • (r⁻¹ • u - s⁻¹ • w) = u - (r / s) • w := by
    rw [smul_sub, smul_inv_smul₀ hr.ne', smul_smul, div_eq_mul_inv]
  have h1 : r * ‖r⁻¹ • u - s⁻¹ • w‖ = ‖u - (r / s) • w‖ := by
    rw [← hsme, norm_smul, Real.norm_of_nonneg hr.le]
  have h3 : ‖(((1:ℝ) / 2) - r / s) • w‖ = |s / 2 - r| := by
    rw [norm_smul, Real.norm_eq_abs, hws]
    have hAs : (((1:ℝ) / 2) - r / s) * s = s / 2 - r := by
      rw [sub_mul, div_mul_cancel₀ r hs.ne']; ring
    have habs : |((1:ℝ) / 2) - r / s| * s = |(((1:ℝ) / 2) - r / s) * s| :=
      ((abs_mul (((1:ℝ) / 2) - r / s) s).trans (by rw [abs_of_nonneg hs.le])).symm
    rw [habs, hAs]
  have h4 : |s / 2 - r| ≤ δ := by
    have hw2 : ‖((1:ℝ) / 2) • w‖ = s / 2 := by
      rw [norm_smul, Real.norm_eq_abs, hws,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
      ring
    calc |s / 2 - r| = |‖((1:ℝ) / 2) • w‖ - ‖u‖| := by rw [hw2, hur]
      _ ≤ ‖((1:ℝ) / 2) • w - u‖ := abs_norm_sub_norm_le _ _
      _ = ‖u - ((1:ℝ) / 2) • w‖ := norm_sub_rev _ _
      _ ≤ δ := h
  have h2 : ‖u - (r / s) • w‖ ≤ δ + δ := by
    have : u - (r / s) • w = (u - ((1:ℝ) / 2) • w) + (((1:ℝ) / 2) - r / s) • w := by
      module
    rw [this]
    calc ‖(u - ((1:ℝ) / 2) • w) + (((1:ℝ) / 2) - r / s) • w‖
        ≤ ‖u - ((1:ℝ) / 2) • w‖ + ‖(((1:ℝ) / 2) - r / s) • w‖ := norm_add_le _ _
      _ ≤ δ + δ := by rw [h3]; exact add_le_add h h4
  have h5 : r * ‖r⁻¹ • u - s⁻¹ • w‖ ≤ 2 * δ := by
    rw [h1]; linarith
  rw [le_div_iff₀ hr]
  linarith

/-- **Direction estimate from a ray estimate.** -/
lemma norm_inv_smul_sub_inv_smul_le_ray {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u w : F} {r s δ c : ℝ} (hr : 0 < r) (hs : 0 < s) (hur : ‖u‖ = r) (hws : ‖w‖ = s)
    (hc : 0 ≤ c) (h : ‖u - c • w‖ ≤ δ) :
    ‖r⁻¹ • u - s⁻¹ • w‖ ≤ 2 * δ / r := by
  have hsme : r • (r⁻¹ • u - s⁻¹ • w) = u - (r / s) • w := by
    rw [smul_sub, smul_inv_smul₀ hr.ne', smul_smul, div_eq_mul_inv]
  have h1 : r * ‖r⁻¹ • u - s⁻¹ • w‖ = ‖u - (r / s) • w‖ := by
    rw [← hsme, norm_smul, Real.norm_of_nonneg hr.le]
  have hcs : |c * s - r| ≤ δ := by
    have hcw : ‖c • w‖ = c * s := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, hws]
    calc |c * s - r| = |‖c • w‖ - ‖u‖| := by rw [hcw, hur]
      _ ≤ ‖c • w - u‖ := abs_norm_sub_norm_le _ _
      _ = ‖u - c • w‖ := norm_sub_rev _ _
      _ ≤ δ := h
  have h3 : ‖(c - r / s) • w‖ ≤ δ := by
    rw [norm_smul, Real.norm_eq_abs, hws]
    have hAs : (c - r / s) * s = c * s - r := by
      rw [sub_mul, div_mul_cancel₀ r hs.ne']
    have habs : |c - r / s| * s = |(c - r / s) * s| :=
      ((abs_mul (c - r / s) s).trans (by rw [abs_of_nonneg hs.le])).symm
    rw [habs, hAs]
    exact hcs
  have h2 : ‖u - (r / s) • w‖ ≤ δ + δ := by
    have : u - (r / s) • w = (u - c • w) + (c - r / s) • w := by module
    rw [this]
    calc ‖(u - c • w) + (c - r / s) • w‖ ≤ ‖u - c • w‖ + ‖(c - r / s) • w‖ := norm_add_le _ _
      _ ≤ δ + δ := add_le_add h h3
  have h5 : r * ‖r⁻¹ • u - s⁻¹ • w‖ ≤ 2 * δ := by
    rw [h1]; linarith
  rw [le_div_iff₀ hr]
  linarith

/-- The mass norm of the zero configuration vanishes. -/
lemma weightedNorm_zero (m : Fin N → ℝ) : ‖(0 : EN E N)‖_[m] = 0 := by
  rw [weightedNorm]
  simp

/-! ## The downward induction -/

/-- **Liu--Yan--Zhou, Lemma 6.1, first half.**  Given an `h`-minimiser `γ` on `[0,τ]` ending at
`x* + 2^n • a`, and a bound on the potential integral along every ray from `x*` in the cone of
width `θ` around `a`, one constructs the dyadic crossings `σ i` and proves by downward induction
that the mass length of `γ|[0, σ i]` is at most `2^i + Ψ(2^i)` and that the normalised direction
`2^{-i}(γ (σ i) - x*)` is within `24 · lyzTail Ψ (i+1)` of `a`. -/
theorem exists_lyz_phaseA {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 < m i)
    {xstar a : EN E N} {A B M θ : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hM0 : 0 ≤ M) (ha : ‖a‖_[m] = 1)
    {Ψ Ψb : ℝ → ℝ} (hΨnn : ∀ T, 0 ≤ T → 0 ≤ Ψ T)
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
    (hθ : 24 * lyzTail Ψ (n₀ + 1) ≤ θ) :
    ∃ σ τhat : ℕ → ℝ,
      σ n = τ ∧
      (∀ i, n₀ ≤ i → i ≤ n → σ i ∈ Set.Icc 0 τ ∧ ‖γ (σ i) - xstar‖_[m] = (2:ℝ) ^ i ∧
        (∀ t ∈ Set.Icc (σ i) τ, (2:ℝ) ^ i ≤ ‖γ t - xstar‖_[m])) ∧
      (∀ i, n₀ ≤ i → i < n → σ i ≤ σ (i + 1)) ∧
      (∀ i, n₀ ≤ i → i < n → τhat i ∈ Set.Icc (σ i) (σ (i + 1)) ∧
        ‖γ (τhat i) - xstar‖_[m] = ‖γ (τhat i) - γ (σ (i + 1))‖_[m] ∧
        (2:ℝ) ^ i ≤ ‖γ (τhat i) - xstar‖_[m]) ∧
      (∀ i, n₀ ≤ i → i < n →
        ‖massScale m (γ (σ i)) - (massScale m xstar +
            ((1:ℝ) / 2) • (massScale m (γ (σ (i + 1))) - massScale m xstar))‖
          ≤ 4 * Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1)))) ∧
      (∀ i, n₀ ≤ i → i < n → ∀ t ∈ Set.Icc (σ i) (σ (i + 1)), ∃ c : ℝ, 0 ≤ c ∧
        ‖massScale m (γ t) - (massScale m xstar +
            c • (massScale m (γ (σ (i + 1))) - massScale m xstar))‖
          ≤ 6 * Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1)))) ∧
      (∀ i, n₀ ≤ i → i ≤ n → massLength m γ 0 (σ i) ≤ (2:ℝ) ^ i + lyzPsi A B M ((2:ℝ) ^ i)) ∧
      (∀ i, n₀ ≤ i → i ≤ n →
        ‖((2:ℝ) ^ i)⁻¹ • (γ (σ i) - xstar) - a‖_[m] ≤ 24 * lyzTail Ψ (i + 1)) := by
  classical
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hθ0 : (0:ℝ) ≤ θ := by
    have h1 : (0:ℝ) ≤ 24 * lyzTail Ψ (n₀ + 1) :=
      mul_nonneg (by norm_num) (lyzTail_nonneg (Ψ := Ψ) hΨnn (n₀ + 1))
    linarith [hθ]
  have hms_cont : Continuous (fun x : EN E N => massScale m x) := by
    have hLip : LipschitzWith (⟨Real.sqrt (∑ i, m i), Real.sqrt_nonneg _⟩ : NNReal)
        (fun x : EN E N => massScale m x) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [dist_eq_norm, dist_eq_norm, ← massScale_sub, ← weightedNorm_eq_norm_massScale hm0]
      exact weightedNorm_le_mul_norm hm0 (x - y)
    exact hLip.continuous
  set Γ : ℝ → EN E N := fun t => massScale m (γ t) with hΓdef
  set xS : EN E N := massScale m xstar with hxSdef
  set aF : EN E N := massScale m a with haFdef
  have hΓdef' : ∀ t, Γ t = massScale m (γ t) := fun t => rfl
  have hΓdiff : ∀ s t : ℝ, Γ s - Γ t = massScale m (γ s - γ t) := by
    intro s t; rw [hΓdef', hΓdef', massScale_sub]
  have hΓsub : ∀ t : ℝ, Γ t - xS = massScale m (γ t - xstar) := by
    intro t; rw [hΓdef', hxSdef, massScale_sub]
  have hΓn : ∀ t : ℝ, ‖Γ t - xS‖ = ‖γ t - xstar‖_[m] := by
    intro t; rw [hΓsub t, ← weightedNorm_eq_norm_massScale hm0]
  have hΓτ : Γ τ = xS + (2:ℝ) ^ n • aF := by
    rw [hΓdef', hxSdef, haFdef, hγτ, massScale_add, massScale_smul]
  have haF1 : ‖aF‖ = 1 := by
    rw [haFdef, ← weightedNorm_eq_norm_massScale hm0, ha]
  have hΓ0 : ‖Γ 0 - xS‖ < (2:ℝ) ^ n₀ := by rw [hΓn]; exact h0lt
  have hΓcont : ContinuousOn Γ (Set.Icc 0 τ) := by
    rw [hΓdef]
    have h := hms_cont.comp_continuousOn hac.continuousOn
    rw [Set.uIcc_of_le hτ.le] at h
    exact h
  obtain ⟨σ, τhat, hσn, hσv, hσmono, hτv⟩ :=
    Commons.Analysis.InnerProductSpace.exists_lyz_crossings (F := EN E N) hn hτ.le hΓcont
      haF1 hΓτ hΓ0
  have hσmem : ∀ i, n₀ ≤ i → i ≤ n → σ i ∈ Set.Icc 0 τ := fun i a b => (hσv i a b).1
  have hσval : ∀ i, n₀ ≤ i → i ≤ n → ‖Γ (σ i) - xS‖ = (2:ℝ) ^ i := fun i a b => (hσv i a b).2.1
  have hσle : ∀ i, n₀ ≤ i → i ≤ n → ∀ t ∈ Set.Icc (σ i) τ, (2:ℝ) ^ i ≤ ‖Γ t - xS‖ :=
    fun i a b => (hσv i a b).2.2
  have hτmem : ∀ i, n₀ ≤ i → i < n → τhat i ∈ Set.Icc (σ i) (σ (i + 1)) :=
    fun i a b => (hτv i a b).1
  have hτval : ∀ i, n₀ ≤ i → i < n → ‖Γ (τhat i) - xS‖ = ‖Γ (τhat i) - Γ (σ (i + 1))‖ :=
    fun i a b => (hτv i a b).2.1
  have hτge : ∀ i, n₀ ≤ i → i < n → (2:ℝ) ^ i ≤ ‖Γ (τhat i) - xS‖ :=
    fun i a b => (hτv i a b).2.2
  have hΓdn : ∀ s t : ℝ, ‖γ s - γ t‖_[m] = ‖Γ s - Γ t‖ := by
    intro s t
    rw [weightedNorm_eq_norm_massScale hm0, ← hΓdiff s t]
  have hσval' : ∀ i, n₀ ≤ i → i ≤ n → ‖γ (σ i) - xstar‖_[m] = (2:ℝ) ^ i :=
    fun i a b => (hΓn (σ i)).symm.trans (hσval i a b)
  have hσle' : ∀ i, n₀ ≤ i → i ≤ n → ∀ t ∈ Set.Icc (σ i) τ, (2:ℝ) ^ i ≤ ‖γ t - xstar‖_[m] :=
    fun i a b t ht => (hσle i a b t ht).trans (le_of_eq (hΓn t))
  have hτge' : ∀ i, n₀ ≤ i → i < n → (2:ℝ) ^ i ≤ ‖γ (τhat i) - xstar‖_[m] :=
    fun i a b => (hτge i a b).trans (le_of_eq (hΓn (τhat i)))
  have hτval' : ∀ i, n₀ ≤ i → i < n →
      ‖γ (τhat i) - xstar‖_[m] = ‖γ (τhat i) - γ (σ (i + 1))‖_[m] := by
    intro i a b
    rw [(hΓn (τhat i)).symm, hτval i a b, hΓdn (τhat i) (σ (i + 1))]
  have hlen_add : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c ≤ τ →
      massLength m γ a c = massLength m γ a b + massLength m γ b c := by
    intro a b c h0 hab hbc hc
    exact massLength_add hm0 hab hbc (hac.mono (by
      rw [uIcc_of_le (hab.trans hbc), uIcc_of_le hτ.le]
      exact Set.Icc_subset_Icc h0 hc))
  have hlen_chord : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ τ →
      ‖Γ b - Γ a‖ ≤ massLength m γ a b := by
    intro a b h0 hab hb
    have hb_ac : AbsolutelyContinuousOnInterval γ a b := hac.mono (by
      rw [uIcc_of_le hab, uIcc_of_le hτ.le]
      exact Set.Icc_subset_Icc h0 hb)
    have hint : IntervalIntegrable (fun t : ℝ => ‖deriv γ t‖_[m]) volume a b :=
      intervalIntegrable_weightedNorm_deriv hm0 hab hb_ac
    calc ‖Γ b - Γ a‖ = ‖γ b - γ a‖_[m] := by
          rw [hΓdiff b a, ← weightedNorm_eq_norm_massScale hm0]
      _ ≤ massLength m γ a b := weightedNorm_sub_le_massLength hm hab hb_ac
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint)
  -- base case
  have hbase_len : massLength m γ 0 (σ n) ≤ (2:ℝ) ^ n + lyzPsi A B M ((2:ℝ) ^ n) := by
    rw [hσn]
    have hseg : ∀ t ∈ Set.Icc (0:ℝ) ((2:ℝ) ^ n), WithoutCollisions (xstar + t • a) :=
      fun t ht => hncB a ha (by rw [sub_self, weightedNorm_zero]; exact hθ0) t ht.1
    have hpot : ∫ t in (0:ℝ)..((2:ℝ) ^ n), U m (xstar + t • a) ≤
        (2 * h) * B * Real.log (2 * ((2:ℝ) ^ n) + 2 * M + 1) :=
      hpotB a ha (by rw [sub_self, weightedNorm_zero]; exact hθ0) _ (by positivity)
    have hlog : 0 ≤ Real.log (2 * ((2:ℝ) ^ n) + 2 * M + 1) := by
      apply Real.log_nonneg
      have : (1:ℝ) ≤ (2:ℝ) ^ n := one_le_pow₀ (by norm_num)
      nlinarith
    exact massLength_le_psi' hh hm0 hτ.le (by positivity) hac hfin hmin hγτ ha hseg hΦ hAφ
      hpot hlog
  have hbase_dir : ‖((2:ℝ) ^ n)⁻¹ • (γ (σ n) - xstar) - a‖_[m] ≤ 24 * lyzTail Ψ (n + 1) := by
    have h2n : ((2:ℝ) ^ n) ≠ 0 := by positivity
    rw [hσn, hγτ, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h2n, one_smul, sub_self]
    rw [weightedNorm_zero]
    exact mul_nonneg (by norm_num) (lyzTail_nonneg (Ψ := Ψ) hΨnn _)
  -- induction step
  have hstep : ∀ k, n₀ ≤ k → k < n →
      (massLength m γ 0 (σ (k + 1)) ≤ (2:ℝ) ^ (k + 1) + lyzPsi A B M ((2:ℝ) ^ (k + 1)) ∧
        ‖((2:ℝ) ^ (k + 1))⁻¹ • (γ (σ (k + 1)) - xstar) - a‖_[m]
          ≤ 24 * lyzTail Ψ ((k + 1) + 1)) →
      (massLength m γ 0 (σ k) ≤ (2:ℝ) ^ k + lyzPsi A B M ((2:ℝ) ^ k) ∧
        ‖((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar) - a‖_[m] ≤ 24 * lyzTail Ψ (k + 1)) := by
    intro k hk0 hkn hP1
    have hk1 : n₀ ≤ k + 1 := le_trans hk0 (Nat.le_succ k)
    have hk1n : k + 1 ≤ n := Nat.succ_le_of_lt hkn
    have hkn' : k ≤ n := le_of_lt hkn
    have hS : (0:ℝ) < (2:ℝ) ^ (k + 1) := by positivity
    have hkmono : σ k ≤ σ (k + 1) := hσmono k hk0 hkn
    have hmem1 : σ (k + 1) ∈ Set.Icc 0 τ := hσmem (k + 1) hk1 hk1n
    have him : σ k ≤ τhat k := (hτmem k hk0 hkn).1
    have him2 : τhat k ≤ σ (k + 1) := (hτmem k hk0 hkn).2
    have htotal : massLength m γ 0 (σ (k + 1)) ≤ (2:ℝ) ^ (k + 1) + Ψ ((2:ℝ) ^ (k + 1)) := by
      have h := hP1.1
      rw [← hΨlyz] at h
      exact h
    have hq : ‖Γ (σ k) - xS‖ = (2:ℝ) ^ (k + 1) / 2 := by
      rw [hσval k hk0 hkn']
      rw [show (2:ℝ) ^ (k + 1) = 2 * (2:ℝ) ^ k by rw [pow_succ]; ring]; ring
    have hge : (2:ℝ) ^ (k + 1) / 2 ≤ ‖Γ (τhat k) - xS‖ := by
      rw [show (2:ℝ) ^ (k + 1) / 2 = (2:ℝ) ^ k by rw [pow_succ]; ring]
      exact hτge k hk0 hkn
    have hx0k : ‖Γ 0 - xS‖ ≤ Ψ ((2:ℝ) ^ (k + 1)) := by rw [hΓn]; exact hx0 k hk0 hkn
    have hmidk : ‖Γ (σ k) - (xS + ((1:ℝ) / 2) • (Γ (σ (k + 1)) - xS))‖
        ≤ 4 * Real.sqrt ((2:ℝ) ^ (k + 1) * Ψ ((2:ℝ) ^ (k + 1))) :=
      lyz_obs_midpoint (F := EN E N) (γ := Γ) (len := massLength m γ) (xstar := xS)
        (S := (2:ℝ) ^ (k + 1)) (Ψ := Ψ ((2:ℝ) ^ (k + 1))) (τ := σ (k + 1))
        (τ₁ := σ k) (τ₂ := τhat k) hS (hΨnn _ (by positivity)) (hΨhalf k hk0 hkn)
        (hσmem k hk0 hkn').1 hkmono him him2
        (fun a b c h0 hab hbc hc => hlen_add a b c h0 hab hbc (hc.trans hmem1.2))
        (fun a b h0 hab hb => hlen_chord a b h0 hab (hb.trans hmem1.2))
        htotal hx0k (hσval (k + 1) hk1 hk1n) hq (hτval k hk0 hkn) hge
    -- direction step
    have hdir : ‖((2:ℝ) ^ k)⁻¹ • (Γ (σ k) - xS) - ((2:ℝ) ^ (k + 1))⁻¹ • (Γ (σ (k + 1)) - xS)‖
        ≤ 16 * Real.sqrt (Ψ ((2:ℝ) ^ (k + 1)) / (2:ℝ) ^ (k + 1)) := by
      have hr : (0:ℝ) < (2:ℝ) ^ k := by positivity
      have hsb : (0:ℝ) < (2:ℝ) ^ (k + 1) := by positivity
      have hm' : ‖Γ (σ k) - xS - ((1:ℝ) / 2) • (Γ (σ (k + 1)) - xS)‖
          ≤ 4 * Real.sqrt ((2:ℝ) ^ (k + 1) * Ψ ((2:ℝ) ^ (k + 1))) := by
        have hh := hmidk
        rwa [sub_add_eq_sub_sub] at hh
      have h := norm_inv_smul_sub_inv_smul_le_half (F := EN E N) (u := Γ (σ k) - xS)
        (w := Γ (σ (k + 1)) - xS) (r := (2:ℝ) ^ k) (s := (2:ℝ) ^ (k + 1))
        (δ := 4 * Real.sqrt ((2:ℝ) ^ (k + 1) * Ψ ((2:ℝ) ^ (k + 1)))) hr hsb
        (hσval k hk0 hkn') (hσval (k + 1) hk1 hk1n) hm'
      refine h.trans (le_of_eq ?_)
      have hsq : ((2:ℝ) ^ (k + 1) * Ψ ((2:ℝ) ^ (k + 1)))
          = ((2:ℝ) ^ (k + 1)) ^ 2 * (Ψ ((2:ℝ) ^ (k + 1)) / (2:ℝ) ^ (k + 1)) := by
        field_simp
      rw [hsq, Real.sqrt_mul (by positivity : (0:ℝ) ≤ ((2:ℝ) ^ (k + 1)) ^ 2),
        Real.sqrt_sq (by positivity : (0:ℝ) ≤ (2:ℝ) ^ (k + 1)),
        show (2:ℝ) ^ (k + 1) = 2 * (2:ℝ) ^ k by rw [pow_succ]; ring]
      field_simp
      ring
    have hg1nn : 0 ≤ Real.sqrt (Ψ ((2:ℝ) ^ (k + 1)) / (2:ℝ) ^ (k + 1)) := Real.sqrt_nonneg _
    have hdir2 : ‖((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar) -
        ((2:ℝ) ^ (k + 1))⁻¹ • (γ (σ (k + 1)) - xstar)‖_[m]
        ≤ 16 * Real.sqrt (Ψ ((2:ℝ) ^ (k + 1)) / (2:ℝ) ^ (k + 1)) := by
      calc ‖((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar) -
            ((2:ℝ) ^ (k + 1))⁻¹ • (γ (σ (k + 1)) - xstar)‖_[m]
          = ‖massScale m (((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar) -
              ((2:ℝ) ^ (k + 1))⁻¹ • (γ (σ (k + 1)) - xstar))‖ :=
              weightedNorm_eq_norm_massScale hm0 _
        _ = ‖((2:ℝ) ^ k)⁻¹ • (Γ (σ k) - xS) -
              ((2:ℝ) ^ (k + 1))⁻¹ • (Γ (σ (k + 1)) - xS)‖ := by
              rw [massScale_sub, massScale_smul, massScale_smul, ← hΓsub (σ k),
                ← hΓsub (σ (k + 1))]
        _ ≤ 16 * Real.sqrt (Ψ ((2:ℝ) ^ (k + 1)) / (2:ℝ) ^ (k + 1)) := hdir
    have hdirb : ‖((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar) - a‖_[m] ≤ 24 * lyzTail Ψ (k + 1) := by
      have htri : ‖((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar) - a‖_[m]
          ≤ ‖((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar) -
              ((2:ℝ) ^ (k + 1))⁻¹ • (γ (σ (k + 1)) - xstar)‖_[m]
            + ‖((2:ℝ) ^ (k + 1))⁻¹ • (γ (σ (k + 1)) - xstar) - a‖_[m] := by
        have h : ((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar) - a
            = (((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar) -
                ((2:ℝ) ^ (k + 1))⁻¹ • (γ (σ (k + 1)) - xstar))
              + (((2:ℝ) ^ (k + 1))⁻¹ • (γ (σ (k + 1)) - xstar) - a) := by abel
        rw [h]; exact weightedNorm_add_le hm0 _ _
      refine htri.trans ?_
      rw [lyzTail_succ hsumm (k + 1)]
      linarith [hdir2, hP1.2, hg1nn]
    refine ⟨?_, hdirb⟩
    · -- length bound at k
      have hbnd : ‖((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar)‖_[m] = 1 := by
        rw [weightedNorm_smul hm0]
        rw [(hΓn (σ k)).symm, hσval k hk0 hkn']
        rw [abs_of_nonneg (inv_nonneg.mpr (by positivity : (0:ℝ) ≤ (2:ℝ) ^ k)),
          inv_mul_cancel₀ (by positivity : ((2:ℝ) ^ k) ≠ 0)]
      have hcone : ‖((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar) - a‖_[m] ≤ θ :=
        (hdirb.trans (mul_le_mul_of_nonneg_left
          (lyzTail_mono hΨnn hsumm (Nat.succ_le_succ hk0)) (by norm_num))).trans hθ
      have hD : (0:ℝ) < (2:ℝ) ^ k := by positivity
      have hγσ : γ (σ k) = xstar + (2:ℝ) ^ k • (((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar)) := by
        rw [smul_smul, mul_inv_cancel₀ (by positivity : ((2:ℝ) ^ k) ≠ 0), one_smul]
        abel
      have hseg : ∀ t ∈ Set.Icc (0:ℝ) ((2:ℝ) ^ k),
          WithoutCollisions (xstar + t • (((2:ℝ) ^ k)⁻¹ • (γ (σ k) - xstar))) :=
        fun t ht => hncB _ hbnd hcone t ht.1
      have hpot := hpotB _ hbnd hcone ((2:ℝ) ^ k) (by positivity)
      have hlog : 0 ≤ Real.log (2 * ((2:ℝ) ^ k) + 2 * M + 1) := by
        apply Real.log_nonneg
        have : (1:ℝ) ≤ (2:ℝ) ^ k := one_le_pow₀ (by norm_num)
        nlinarith
      exact massLength_le_psi_sub' hh hm0 (hσmem k hk0 hkn').1 (hσmem k hk0 hkn').2 hD hac
        hfin hmin hγσ hbnd hseg hΦ hAφ hA0 hB0 hM0 hpot hlog
  have hP : ∀ i, n₀ ≤ i → i ≤ n → (massLength m γ 0 (σ i) ≤ (2:ℝ) ^ i + lyzPsi A B M ((2:ℝ) ^ i) ∧
      ‖((2:ℝ) ^ i)⁻¹ • (γ (σ i) - xstar) - a‖_[m] ≤ 24 * lyzTail Ψ (i + 1)) := by
    intro i hi0 hin
    refine Nat.decreasingInduction (motive := fun j (_ : j ≤ n) => n₀ ≤ j →
      (massLength m γ 0 (σ j) ≤ (2:ℝ) ^ j + lyzPsi A B M ((2:ℝ) ^ j) ∧
        ‖((2:ℝ) ^ j)⁻¹ • (γ (σ j) - xstar) - a‖_[m] ≤ 24 * lyzTail Ψ (j + 1))) ?_ ?_ hin hi0
    · intro k hk ih hk0
      exact hstep k hk0 hk (ih (le_trans hk0 (Nat.le_succ k)))
    · intro _; exact ⟨hbase_len, hbase_dir⟩
  refine ⟨σ, τhat, hσn, ?_, hσmono, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi0 hin
    exact ⟨hσmem i hi0 hin, hσval' i hi0 hin, hσle' i hi0 hin⟩
  · intro i hi0 hin
    exact ⟨hτmem i hi0 hin, hτval' i hi0 hin, hτge' i hi0 hin⟩
  · intro i hi0 hin
    have := lyz_obs_midpoint (F := EN E N) (γ := Γ) (len := massLength m γ) (xstar := xS)
      (S := (2:ℝ) ^ (i + 1)) (Ψ := Ψ ((2:ℝ) ^ (i + 1))) (τ := σ (i + 1))
      (τ₁ := σ i) (τ₂ := τhat i) (by positivity) (hΨnn _ (by positivity)) (hΨhalf i hi0 hin)
      (hσmem i hi0 (le_of_lt hin)).1 (hσmono i hi0 hin) (hτmem i hi0 hin).1 (hτmem i hi0 hin).2
      (fun a b c h0 hab hbc hc => hlen_add a b c h0 hab hbc
        (hc.trans (hσmem (i + 1) (le_trans hi0 (Nat.le_succ i))
          (Nat.succ_le_of_lt hin)).2))
      (fun a b h0 hab hb => hlen_chord a b h0 hab
        (hb.trans (hσmem (i + 1) (le_trans hi0 (Nat.le_succ i))
          (Nat.succ_le_of_lt hin)).2))
      (by
        have h := (hP (i + 1) (le_trans hi0 (Nat.le_succ i)) (Nat.succ_le_of_lt hin)).1
        rw [← hΨlyz] at h
        exact h)
      (by rw [hΓn]; exact hx0 i hi0 hin)
      (hσval (i + 1) (le_trans hi0 (Nat.le_succ i)) (Nat.succ_le_of_lt hin))
      (by rw [hσval i hi0 (le_of_lt hin)]
          rw [show (2:ℝ) ^ (i + 1) = 2 * (2:ℝ) ^ i by rw [pow_succ]; ring]; ring)
      (hτval i hi0 hin)
      (by rw [show (2:ℝ) ^ (i + 1) / 2 = (2:ℝ) ^ i by rw [pow_succ]; ring]
          exact hτge i hi0 hin)
    simpa only [hΓdef', hxSdef] using this
  · intro i hi0 hin t ht
    have := lyz_obs_ray (F := EN E N) (γ := Γ) (len := massLength m γ) (xstar := xS)
      (S := (2:ℝ) ^ (i + 1)) (Ψ := Ψ ((2:ℝ) ^ (i + 1))) (τ := σ (i + 1))
      (τ₁ := σ i) (τ₂ := τhat i) (by positivity) (hΨnn _ (by positivity)) (hΨhalf i hi0 hin)
      (hσmem i hi0 (le_of_lt hin)).1 (hσmono i hi0 hin) (hτmem i hi0 hin).1 (hτmem i hi0 hin).2
      ht.1 ht.2
      (fun a b c h0 hab hbc hc => hlen_add a b c h0 hab hbc
        (hc.trans (hσmem (i + 1) (le_trans hi0 (Nat.le_succ i))
          (Nat.succ_le_of_lt hin)).2))
      (fun a b h0 hab hb => hlen_chord a b h0 hab
        (hb.trans (hσmem (i + 1) (le_trans hi0 (Nat.le_succ i))
          (Nat.succ_le_of_lt hin)).2))
      (by
        have h := (hP (i + 1) (le_trans hi0 (Nat.le_succ i)) (Nat.succ_le_of_lt hin)).1
        rw [← hΨlyz] at h
        exact h)
      (by rw [hΓn]; exact hx0 i hi0 hin)
      (hσval (i + 1) (le_trans hi0 (Nat.le_succ i)) (Nat.succ_le_of_lt hin))
      (by rw [hσval i hi0 (le_of_lt hin)]
          rw [show (2:ℝ) ^ (i + 1) = 2 * (2:ℝ) ^ i by rw [pow_succ]; ring]; ring)
      (hτval i hi0 hin)
      (by rw [show (2:ℝ) ^ (i + 1) / 2 = (2:ℝ) ^ i by rw [pow_succ]; ring]
          exact hτge i hi0 hin)
    obtain ⟨c, hc, hcc⟩ := this
    exact ⟨c, hc, by simpa only [hΓdef', hxSdef] using hcc⟩
  · intro i hi0 hin; exact (hP i hi0 hin).1
  · intro i hi0 hin; exact (hP i hi0 hin).2

end Submission.NBody
