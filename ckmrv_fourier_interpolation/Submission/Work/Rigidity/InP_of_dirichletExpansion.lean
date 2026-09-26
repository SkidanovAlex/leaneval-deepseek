import Mathlib
import Submission.Work.Rigidity.ModerateGrowth
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.HolomorphicFourierExpansion
import Submission.Work.Kernels.ModerateGrowth

/-!
# `F = A + 2πiτ·B` lies in `𝒫` whenever `A`, `B` are Dirichlet series with
polynomially bounded coefficients

This file proves `Work.Rigidity.InP_of_dirichletExpansion`: the function

  `τ ↦ ∑_n a_n e^{2πinτ} + (2πiτ) · ∑_n b_n e^{2πinτ}`

lies in the CKMRV class `𝒫 = Work.Kernels.InP` as soon as the coefficients grow at most
polynomially (`‖a n‖, ‖b n‖ ≤ C (n+1)^N`).

The two ingredients are
* holomorphy, which is `Work.FunctionalEquations.differentiableOn_tsum_dirichletTerm`
  (a locally uniform limit of entire functions), and
* moderate growth: on `Im τ > 0` the term `e^{2πinτ}` decays like `e^{-2πn Im τ}`, so
  the series is dominated by `∑_n (n+1)^N e^{-2π n Im τ}`, which is bounded by a constant
  times `(1 + (Im τ)⁻¹)^{N+1} ≤ (scale τ)^{N+1}`.
-/

namespace Work.Rigidity

open UpperHalfPlane
open scoped Manifold

noncomputable section

/-! ## The growth of a Dirichlet series with polynomially bounded coefficients -/

/-- `(m+1)^N ≤ N! · binom(m+N, N)` in `ℕ`, obtained from the product formula for the
ascending factorial `(m+1).ascFactorial N = ∏_{i<N} (m+1+i)`. -/
private lemma nat_add_one_pow_le_factorial_mul_choose (m N : ℕ) :
    (m + 1) ^ N ≤ N.factorial * (m + N).choose N := by
  have hle : ∏ i ∈ Finset.range N, (m + 1) ≤ ∏ i ∈ Finset.range N, (m + 1 + i) :=
    Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) (fun i _ => by omega)
  calc (m + 1) ^ N = ∏ i ∈ Finset.range N, (m + 1) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range N, (m + 1 + i) := hle
    _ = (m + 1).ascFactorial N := (Nat.ascFactorial_eq_prod_range (m + 1) N).symm
    _ = N.factorial * (m + N).choose N := Nat.ascFactorial_eq_factorial_mul_choose m N

/-- `(m+1)^N ≤ N! · binom(m+N, N)`, the elementary bound converting a power into a
binomial coefficient so that Mathlib's binomial geometric series can be applied. -/
private lemma cast_add_one_pow_le_factorial_mul_choose (m N : ℕ) :
    ((m : ℝ) + 1) ^ N ≤ (N.factorial : ℝ) * ((Nat.choose (m + N) N : ℕ) : ℝ) := by
  have h := nat_add_one_pow_le_factorial_mul_choose m N
  have h' : (((m + 1) ^ N : ℕ) : ℝ) ≤ ((N.factorial * (m + N).choose N : ℕ) : ℝ) := by
    exact_mod_cast h
  have e1 : (((m + 1) ^ N : ℕ) : ℝ) = ((m : ℝ) + 1) ^ N := by push_cast; ring
  have e2 : ((N.factorial * (m + N).choose N : ℕ) : ℝ)
      = (N.factorial : ℝ) * ((Nat.choose (m + N) N : ℕ) : ℝ) := by push_cast; ring
  rwa [e1, e2] at h'

/-- `1 / (1 - e^{-a}) ≤ 2 · scale τ` for `a = 2π Im τ`, where `scale τ = 1 + (Im τ)⁻¹ + ‖τ‖`.
This is the elementary estimate `1 - e^{-a} ≥ a/(1+a)` (equivalent to `1 + a ≤ e^a`). -/
private lemma one_div_one_sub_exp_neg_le_scale (τ : UpperHalfPlane) :
    1 / (1 - Real.exp (-(2 * Real.pi * τ.im))) ≤ 2 * Work.Kernels.scale τ := by
  set a : ℝ := 2 * Real.pi * τ.im with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have h1a : 0 < 1 + a := by linarith
  have hkey : a / (1 + a) ≤ 1 - Real.exp (-a) := by
    rw [div_le_iff₀ h1a]
    have hexp : (1 + a) * Real.exp (-a) ≤ 1 := by
      have h := Real.add_one_le_exp a
      have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (-a)).le
      have hcancel : Real.exp a * Real.exp (-a) = 1 := by
        rw [← Real.exp_add]; simp
      rw [hcancel] at hmul
      linarith
    nlinarith [hexp]
  have hpos : 0 < a / (1 + a) := div_pos hapos h1a
  have hstep : 1 / (1 - Real.exp (-a)) ≤ 1 + 1 / a := by
    have h := one_div_le_one_div_of_le hpos hkey
    rw [one_div_div] at h
    have hcalc : (1 + a) / a = 1 + 1 / a := by
      rw [add_div, div_self (ne_of_gt hapos)]; ring
    rwa [hcalc] at h
  have hfin : 1 + 1 / a ≤ 2 * Work.Kernels.scale τ := by
    have h1 : 1 / a ≤ Work.Kernels.scale τ := by
      rw [ha]
      calc 1 / (2 * Real.pi * τ.im) ≤ 1 / τ.im := by
            apply one_div_le_one_div_of_le τ.im_pos
            nlinarith [Real.pi_gt_three, τ.im_pos]
        _ = (τ.im)⁻¹ := one_div _
        _ ≤ Work.Kernels.scale τ := Work.Kernels.inv_im_le_scale τ
    linarith [Work.Kernels.one_le_scale τ]
  exact hstep.trans hfin

/-- **Growth of a Dirichlet series with polynomially bounded coefficients.** -/
private lemma norm_tsum_dirichletTerm_le_aux {k₀ : ℕ} (c : Set.Ici k₀ → ℂ) {C : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hc : ∀ n : Set.Ici k₀, ‖c n‖ ≤ C * ((n.1 : ℝ) + 1) ^ N)
    (τ : UpperHalfPlane) :
    ‖∑' n : Set.Ici k₀, c n * Work.FE.dirichletTerm n.1 (τ : ℂ)‖
      ≤ C * (N.factorial : ℝ) * 2 ^ (N + 1) * Work.Kernels.scale τ ^ (N + 1) := by
  set t : ℝ := Real.exp (-(2 * Real.pi * τ.im)) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := by rw [ht, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
  have ht0' : 0 ≤ t := ht0.le
  have htnorm : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
  -- norm of a single term
  have hnormterm : ∀ n : Set.Ici k₀, ‖c n * Work.FE.dirichletTerm n.1 (τ : ℂ)‖
      = ‖c n‖ * t ^ n.1 := by
    intro n
    rw [norm_mul, Work.FunctionalEquations.norm_dirichletTerm, UpperHalfPlane.coe_im]
    congr 1
    rw [ht, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- summability of the coefficients against the polynomial weight
  have hchoose : Summable fun m : ℕ =>
      (N.factorial : ℝ) * (((m + N).choose N : ℕ) : ℝ) * t ^ m := by
    have h := (summable_choose_mul_geometric_of_norm_lt_one N (r := t) htnorm).mul_left
      (N.factorial : ℝ)
    exact h.congr (fun m => by ring)
  have hfull : Summable fun m : ℕ => ((m : ℝ) + 1) ^ N * t ^ m :=
    Summable.of_nonneg_of_le (fun m => by positivity)
      (fun m => mul_le_mul_of_nonneg_right (cast_add_one_pow_le_factorial_mul_choose m N)
        (pow_nonneg ht0' m))
      hchoose
  have hsub : Summable fun n : Set.Ici k₀ => ((n.1 : ℝ) + 1) ^ N * t ^ n.1 :=
    hfull.comp_injective (Subtype.val_injective (p := fun n : ℕ => k₀ ≤ n))
  have hmid : Summable fun n : Set.Ici k₀ => C * ((n.1 : ℝ) + 1) ^ N * t ^ n.1 :=
    (hsub.mul_left C).congr (fun n => by ring)
  have hAnorm : Summable fun n : Set.Ici k₀ => ‖c n‖ * t ^ n.1 :=
    Summable.of_nonneg_of_le
      (f := fun n : Set.Ici k₀ => C * ((n.1 : ℝ) + 1) ^ N * t ^ n.1)
      (g := fun n : Set.Ici k₀ => ‖c n‖ * t ^ n.1)
      (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg ht0' n.1))
      (fun n => mul_le_mul_of_nonneg_right (hc n) (pow_nonneg ht0' n.1)) hmid
  have hnormsum : Summable fun n : Set.Ici k₀ =>
      ‖c n * Work.FE.dirichletTerm n.1 (τ : ℂ)‖ :=
    hAnorm.congr (fun n => (hnormterm n).symm)
  have h1 : ‖∑' n : Set.Ici k₀, c n * Work.FE.dirichletTerm n.1 (τ : ℂ)‖
      ≤ ∑' n : Set.Ici k₀, ‖c n‖ * t ^ n.1 := by
    refine (norm_tsum_le_tsum_norm hnormsum).trans (le_of_eq ?_)
    exact tsum_congr (fun n => hnormterm n)
  have h2 : ∑' n : Set.Ici k₀, ‖c n‖ * t ^ n.1
      ≤ ∑' n : Set.Ici k₀, C * ((n.1 : ℝ) + 1) ^ N * t ^ n.1 :=
    hAnorm.tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_right (hc n) (pow_nonneg ht0' n.1)) hmid
  have h3 : ∑' n : Set.Ici k₀, C * ((n.1 : ℝ) + 1) ^ N * t ^ n.1
      ≤ C * ∑' m : ℕ, ((m : ℝ) + 1) ^ N * t ^ m := by
    have hle := Summable.tsum_subtype_le (fun m : ℕ => C * (((m : ℝ) + 1) ^ N * t ^ m))
      (Set.Ici k₀) (fun m => by positivity) (hfull.mul_left C)
    have hL : (∑' n : Set.Ici k₀, C * (((n.1 : ℝ) + 1) ^ N * t ^ n.1))
        = ∑' n : Set.Ici k₀, C * ((n.1 : ℝ) + 1) ^ N * t ^ n.1 :=
      tsum_congr (fun n => by ring)
    have hR : (∑' m : ℕ, C * (((m : ℝ) + 1) ^ N * t ^ m))
        = C * ∑' m : ℕ, ((m : ℝ) + 1) ^ N * t ^ m := by rw [tsum_mul_left]
    rw [hL, hR] at hle
    exact hle
  have h4 : (∑' m : ℕ, ((m : ℝ) + 1) ^ N * t ^ m)
      ≤ (N.factorial : ℝ) * (1 / (1 - t) ^ (N + 1)) := by
    have hle := hfull.tsum_le_tsum
      (g := fun m : ℕ => (N.factorial : ℝ) * (((m + N).choose N : ℕ) : ℝ) * t ^ m)
      (fun m => mul_le_mul_of_nonneg_right (cast_add_one_pow_le_factorial_mul_choose m N)
        (pow_nonneg ht0' m))
      hchoose
    have hrhs : (∑' m : ℕ, (N.factorial : ℝ) * (((m + N).choose N : ℕ) : ℝ) * t ^ m)
        = (N.factorial : ℝ) * (1 / (1 - t) ^ (N + 1)) := by
      have h1 : (fun m : ℕ => (N.factorial : ℝ) * (((m + N).choose N : ℕ) : ℝ) * t ^ m)
          = fun m : ℕ => (N.factorial : ℝ) * ((((m + N).choose N : ℕ) : ℝ) * t ^ m) := by
        funext m; ring
      rw [h1, tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one N htnorm]
    rwa [hrhs] at hle
  have h5 : (N.factorial : ℝ) * (1 / (1 - t) ^ (N + 1))
      ≤ (N.factorial : ℝ) * (2 * Work.Kernels.scale τ) ^ (N + 1) := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N.factorial)
    have hbase : 1 / (1 - t) ≤ 2 * Work.Kernels.scale τ := by
      have h := one_div_one_sub_exp_neg_le_scale τ
      rwa [← ht] at h
    have hpos : (0 : ℝ) ≤ 1 / (1 - t) :=
      div_nonneg zero_le_one (by linarith)
    calc 1 / (1 - t) ^ (N + 1) = (1 / (1 - t)) ^ (N + 1) := by rw [div_pow, one_pow]
      _ ≤ (2 * Work.Kernels.scale τ) ^ (N + 1) := pow_le_pow_left₀ hpos hbase _
  calc ‖∑' n : Set.Ici k₀, c n * Work.FE.dirichletTerm n.1 (τ : ℂ)‖
      ≤ ∑' n : Set.Ici k₀, ‖c n‖ * t ^ n.1 := h1
    _ ≤ ∑' n : Set.Ici k₀, C * ((n.1 : ℝ) + 1) ^ N * t ^ n.1 := h2
    _ ≤ C * ∑' m : ℕ, ((m : ℝ) + 1) ^ N * t ^ m := h3
    _ ≤ C * ((N.factorial : ℝ) * (1 / (1 - t) ^ (N + 1))) := mul_le_mul_of_nonneg_left h4 hC
    _ ≤ C * ((N.factorial : ℝ) * (2 * Work.Kernels.scale τ) ^ (N + 1)) :=
          mul_le_mul_of_nonneg_left h5 hC
    _ = C * (N.factorial : ℝ) * 2 ^ (N + 1) * Work.Kernels.scale τ ^ (N + 1) := by
          rw [mul_pow]; ring

/-! ## Holomorphy -/

/-- A Dirichlet series with polynomially bounded coefficients defines a holomorphic
function of moderate growth on `ℍ`. -/
private lemma mdiff_tsum_dirichletTerm {k₀ : ℕ} (c : Set.Ici k₀ → ℂ) {C : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hc : ∀ n : Set.Ici k₀, ‖c n‖ ≤ C * ((n.1 : ℝ) + 1) ^ N) :
    MDiff (fun τ : UpperHalfPlane => ∑' n : Set.Ici k₀, c n * Work.FE.dirichletTerm n.1 (τ : ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (Work.FunctionalEquations.differentiableOn_tsum_dirichletTerm c ⟨C, N, hC, hc⟩).congr
    (fun z hz => ?_)
  simp only [Function.comp_apply]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-! ## The main statement -/

theorem InP_of_dirichletExpansion (k₀ : ℕ) (a b : Set.Ici k₀ → ℂ) {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (ha : ∀ n : Set.Ici k₀, ‖a n‖ ≤ C * ((n.1 : ℝ) + 1) ^ N) (hb : ∀ n : Set.Ici k₀, ‖b n‖ ≤ C * ((n.1 : ℝ) + 1) ^ N) : Work.Kernels.InP (fun τ : UpperHalfPlane => (∑' n : Set.Ici k₀, a n * Work.FE.dirichletTerm n.1 (τ : ℂ)) + (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) * ∑' n : Set.Ici k₀, b n * Work.FE.dirichletTerm n.1 (τ : ℂ)) := by
  set A : UpperHalfPlane → ℂ := fun τ => ∑' n : Set.Ici k₀, a n * Work.FE.dirichletTerm n.1 (τ : ℂ)
    with hA
  set B : UpperHalfPlane → ℂ := fun τ => ∑' n : Set.Ici k₀, b n * Work.FE.dirichletTerm n.1 (τ : ℂ)
    with hB
  have hAmdiff : MDiff A := by rw [hA]; exact mdiff_tsum_dirichletTerm a hC ha
  have hBmdiff : MDiff B := by rw [hB]; exact mdiff_tsum_dirichletTerm b hC hb
  have hAmg : Work.Kernels.ModerateGrowthOn Set.univ A := by
    rw [Work.Kernels.moderateGrowthOn_iff_scale]
    refine ⟨C * (N.factorial : ℝ) * 2 ^ (N + 1), ((N + 1 : ℕ) : ℝ),
      mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (by positivity), Nat.cast_nonneg _, ?_⟩
    intro τ _
    rw [Real.rpow_natCast]
    simp only [hA]
    exact norm_tsum_dirichletTerm_le_aux a hC ha τ
  have hBmg : Work.Kernels.ModerateGrowthOn Set.univ B := by
    rw [Work.Kernels.moderateGrowthOn_iff_scale]
    refine ⟨C * (N.factorial : ℝ) * 2 ^ (N + 1), ((N + 1 : ℕ) : ℝ),
      mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (by positivity), Nat.cast_nonneg _, ?_⟩
    intro τ _
    rw [Real.rpow_natCast]
    simp only [hB]
    exact norm_tsum_dirichletTerm_le_aux b hC hb τ
  have hAInP : Work.Kernels.InP A := ⟨hAmdiff, hAmg⟩
  have hBInP : Work.Kernels.InP B := ⟨hBmdiff, hBmg⟩
  have hcoe : Work.Kernels.InP (fun τ : UpperHalfPlane => (τ : ℂ)) := by
    refine ⟨UpperHalfPlane.mdifferentiable_coe, ?_⟩
    refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, fun τ _ => ?_⟩
    rw [Real.rpow_one, Real.rpow_one, one_mul]
    exact le_add_of_nonneg_left (Work.Kernels.inv_im_nonneg τ)
  have hlin : Work.Kernels.InP (fun τ : UpperHalfPlane =>
      (2 * (Real.pi : ℂ) * Complex.I) * (τ : ℂ)) :=
    hcoe.const_mul (2 * (Real.pi : ℂ) * Complex.I)
  have hall : Work.Kernels.InP (fun τ : UpperHalfPlane =>
      A τ + (2 * (Real.pi : ℂ) * Complex.I) * (τ : ℂ) * B τ) :=
    hAInP.add (hlin.mul hBInP)
  simpa only [hA, hB] using hall

end

end Work.Rigidity
