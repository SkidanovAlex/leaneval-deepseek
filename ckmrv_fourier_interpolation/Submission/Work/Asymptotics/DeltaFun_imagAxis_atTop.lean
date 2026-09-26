import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.Basic

noncomputable section

open scoped Topology Real
open Finset

namespace Work.Asymptotics

/-! ## Auxiliary product estimates

The modular discriminant is `Δ = q ∏' n (1 - q^{n+1})^24` where `q = e^{2πiτ}`.  On the
imaginary axis `τ = it` we have `q = e^{-2πt}`, so the deviations from `e^{-2πt}` are the
values of the infinite product.  The lemmas below control that product from both sides for
`0 ≤ q ≤ 1/3`.
-/

/-- **A finite product dominates the complementary sum.**  For `0 ≤ a i ≤ 1`,
`1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i)`. -/
lemma one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    have hax0 : 0 ≤ a x := ha0 x (Finset.mem_insert_self x s)
    have hax1 : a x ≤ 1 := ha1 x (Finset.mem_insert_self x s)
    have hs0 : ∀ i ∈ s, 0 ≤ a i := fun i hi => ha0 i (Finset.mem_insert_of_mem hi)
    have hs1 : ∀ i ∈ s, a i ≤ 1 := fun i hi => ha1 i (Finset.mem_insert_of_mem hi)
    have hih := ih hs0 hs1
    have hS0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg hs0
    have hfac : 0 ≤ 1 - a x := by linarith
    have hmul := mul_le_mul_of_nonneg_left hih hfac
    have hexp : (1 - a x) * (1 - ∑ i ∈ s, a i)
        = 1 - a x - ∑ i ∈ s, a i + a x * ∑ i ∈ s, a i := by ring
    have hnon : 0 ≤ a x * ∑ i ∈ s, a i := mul_nonneg hax0 hS0
    linarith [hmul, hexp ▸ hmul, hnon]

/-- **Lower bound for the eta product.**  For `0 ≤ q ≤ 1/3` the infinite product
`∏' n (1 - q^{n+1})` is at least `1/2`; the geometric series `∑ q^{n+1} = q/(1-q) ≤ 1/2`. -/
lemma half_le_tprod_one_sub (q : ℝ) (hq0 : 0 ≤ q) (hq3 : q ≤ 1/3) :
    1/2 ≤ ∏' n : ℕ, (1 - q ^ (n + 1)) := by
  have hq1 : q < 1 := by linarith
  have hsumm : Summable (fun n : ℕ => q ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0 hq1)
  have hM : Multipliable (fun n : ℕ => 1 - q ^ (n + 1)) := by
    have h := Real.multipliable_one_add_of_summable (f := fun n : ℕ => -(q ^ (n + 1)))
      hsumm.neg
    simpa only [sub_eq_add_neg] using h
  have hS : ∑' n : ℕ, q ^ (n + 1) ≤ 1/2 := by
    have hgeo : ∑' n : ℕ, q ^ n = (1 - q)⁻¹ :=
      tsum_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
    have hmul : (∑' n : ℕ, q ^ (n + 1)) = q * ∑' n : ℕ, q ^ n :=
      (tsum_congr (fun n => by rw [pow_succ'])).trans tsum_mul_left
    rw [hmul, hgeo, inv_eq_one_div, mul_one_div,
      div_le_iff₀ (by linarith : (0 : ℝ) < 1 - q)]
    linarith
  refine le_hasProd_of_le_prod hM.hasProd (fun s => ?_)
  have h1 := one_sub_sum_le_prod_one_sub s (fun n => q ^ (n + 1))
    (fun n _ => pow_nonneg hq0 _) (fun n _ => pow_le_one₀ hq0 (by linarith))
  have h2 := hsumm.sum_le_tsum s (fun i _ => pow_nonneg hq0 _)
  linarith [h1, h2, hS]

/-- **Upper bound for the eta product.**  For `0 ≤ q < 1` the infinite product
`∏' n (1 - q^{n+1})` is at most `1`. -/
lemma tprod_one_sub_le_one (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∏' n : ℕ, (1 - q ^ (n + 1)) ≤ 1 := by
  have hsumm : Summable (fun n : ℕ => q ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0 hq1)
  have hM : Multipliable (fun n : ℕ => 1 - q ^ (n + 1)) := by
    have hh := Real.multipliable_one_add_of_summable (f := fun n : ℕ => -(q ^ (n + 1)))
      hsumm.neg
    simpa only [sub_eq_add_neg] using hh
  refine hasProd_le_of_prod_le hM.hasProd (fun s => ?_)
  exact Finset.prod_le_one₀
    (fun i _ => by have : q ^ (i + 1) ≤ 1 := pow_le_one₀ hq0 hq1.le; linarith)
    (fun i _ => by have : (0 : ℝ) ≤ q ^ (i + 1) := pow_nonneg hq0 _; linarith)

/-- **Two-sided bound for the 24-th power product.**  For `0 ≤ q ≤ 1/3`,
`(1/2)^24 ≤ ∏' n (1 - q^{n+1})^24 ≤ 1`. -/
lemma tprod_one_sub_pow24_mem (q : ℝ) (hq0 : 0 ≤ q) (hq3 : q ≤ 1/3) :
    (1/2) ^ 24 ≤ ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 ∧
      ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 ≤ 1 := by
  have hq1 : q < 1 := by linarith
  have hsumm : Summable (fun n : ℕ => q ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0 hq1)
  have hM : Multipliable (fun n : ℕ => 1 - q ^ (n + 1)) := by
    have h := Real.multipliable_one_add_of_summable (f := fun n : ℕ => -(q ^ (n + 1)))
      hsumm.neg
    simpa only [sub_eq_add_neg] using h
  have hpow := hM.tprod_pow 24
  have hlo := half_le_tprod_one_sub q hq0 hq3
  have hhi := tprod_one_sub_le_one q hq0 hq1
  rw [hpow]
  refine ⟨?_, ?_⟩
  · exact pow_le_pow_left₀ (by norm_num) hlo 24
  · exact pow_le_one₀ (by linarith) hhi

/-! ## The q-parameter on the imaginary axis -/

/-- The `q`-parameter `q = e^{2πiτ}` at `τ = it` equals the real number `e^{-2πt}`. -/
lemma qParam_imagAxis (t : ℝ) :
    Function.Periodic.qParam 1 ((t : ℂ) * Complex.I) =
      ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ) := by
  rw [Function.Periodic.qParam, Complex.ofReal_exp]
  congr 1
  push_cast
  calc 2 * (Real.pi : ℂ) * Complex.I * ((t : ℂ) * Complex.I) / 1
      = 2 * (Real.pi : ℂ) * (t : ℂ) * (Complex.I * Complex.I) / 1 := by ring
    _ = -(2 * (Real.pi : ℂ) * (t : ℂ)) := by rw [Complex.I_mul_I]; ring

/-- The `q`-term `eta_q n z = q^{n+1}` on the imaginary axis is the cast of the real power
`q^{n+1}` with `q = e^{-2πt}`. -/
lemma eta_q_imagAxis (t : ℝ) (q : ℝ)
    (hq : Function.Periodic.qParam 1 ((t : ℂ) * Complex.I) = ((q : ℝ) : ℂ)) (n : ℕ) :
    ModularForm.eta_q n ((t : ℂ) * Complex.I) = (((q ^ (n + 1) : ℝ)) : ℂ) := by
  have h : ModularForm.eta_q n ((t : ℂ) * Complex.I)
      = Function.Periodic.qParam 1 ((t : ℂ) * Complex.I) ^ (n + 1) := rfl
  rw [h, hq, ← Complex.ofReal_pow]

/-- The infinite product defining `Δ` on the imaginary axis, rewritten in terms of the real
parameter `q = e^{-2πt}`. -/
lemma tprod_eta_q_imagAxis (t : ℝ) (q : ℝ)
    (hq : Function.Periodic.qParam 1 ((t : ℂ) * Complex.I) = ((q : ℝ) : ℂ)) :
    ∏' n : ℕ, (1 - ModularForm.eta_q n ((t : ℂ) * Complex.I)) ^ 24 =
      (((∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 : ℝ)) : ℂ) := by
  have hmap := Function.LeftInverse.map_tprod
    (L := SummationFilter.unconditional ℕ) (f := fun n : ℕ => (1 - q ^ (n + 1)) ^ 24)
    (g := Complex.ofRealHom) Complex.continuous_ofReal Complex.continuous_re
    (fun x => Complex.ofReal_re x)
  have hterm : ∀ n : ℕ, (1 - ModularForm.eta_q n ((t : ℂ) * Complex.I)) ^ 24
      = (((1 - q ^ (n + 1)) ^ 24 : ℝ) : ℂ) := by
    intro n
    rw [eta_q_imagAxis t q hq n]
    push_cast
    rfl
  rw [tprod_congr hterm]
  exact hmap.symm

/-! ## The value of `Δ(it)` -/

/-- On the imaginary axis, `Δ(it) = q ∏' n (1 - q^{n+1})^24` with `q = e^{-2πt}`. -/
lemma DeltaFun_imagAxis_eq (t : ℝ) (ht : 0 < t) :
    Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) =
      ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ) *
        (((∏' n : ℕ, (1 - (Real.exp (-(2 * Real.pi * t))) ^ (n + 1)) ^ 24 : ℝ)) : ℂ) := by
  have hz : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl
  have hD : Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)
      = ModularForm.discriminant (Work.Kernels.imagAxis t ht) := rfl
  rw [hD, ModularForm.discriminant_eq_q_prod, hz, qParam_imagAxis t,
    tprod_eta_q_imagAxis t (Real.exp (-(2 * Real.pi * t))) (qParam_imagAxis t)]

/-- **The cusp asymptotics of `Δ` on the imaginary axis.**  `Δ(it)` is comparable (up to
absolute constants, from both sides) to `e^{-2πt}` for `t ≥ T`.  Together with the modular
transformation law `Δ(-1/τ) = τ^12 Δ(τ)` this gives the behaviour of `Δ` at the *other* cusp
`t → 0`, and it is the input that makes the CKMRV divisor
`Δ(τ)Δ(it)^e (j(τ) - j(it))` controllable on the contour. -/
theorem DeltaFun_imagAxis_atTop :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 0 < T ∧
      ∀ (t : ℝ) (ht : 0 < t), T ≤ t →
        c * Real.exp (-(2 * Real.pi * t)) ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ∧
        ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ≤ C * Real.exp (-(2 * Real.pi * t)) := by
  refine ⟨(1 / 2) ^ 24, 1, 1, by norm_num, one_pos, one_pos, ?_⟩
  intro t ht hT
  have hq0 : 0 ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
  have hq3 : Real.exp (-(2 * Real.pi * t)) ≤ 1 / 3 := by
    have h3 : (3 : ℝ) ≤ Real.exp (2 * Real.pi) := by
      have h1 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ); linarith
      have h2 : Real.exp 2 ≤ Real.exp (2 * Real.pi) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
      linarith
    have hmono : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(2 * Real.pi)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, hT])
    have hexp : Real.exp (-(2 * Real.pi)) = 1 / Real.exp (2 * Real.pi) := by
      rw [Real.exp_neg, inv_eq_one_div]
    rw [hexp] at hmono
    exact le_trans hmono (one_div_le_one_div_of_le (by norm_num) h3)
  obtain ⟨hlo, hhi⟩ := tprod_one_sub_pow24_mem _ hq0 hq3
  have hnorm : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
      = Real.exp (-(2 * Real.pi * t)) *
        ∏' n : ℕ, (1 - (Real.exp (-(2 * Real.pi * t))) ^ (n + 1)) ^ 24 := by
    rw [DeltaFun_imagAxis_eq t ht, norm_mul]
    congr 1
    · rw [Complex.ofReal_exp, Complex.norm_exp, Complex.ofReal_re]
    · simp [abs_of_nonneg (le_trans (by norm_num) hlo)]
  rw [hnorm]
  constructor
  · have := mul_le_mul_of_nonneg_left hlo hq0
    nlinarith [this]
  · have := mul_le_mul_of_nonneg_left hhi hq0
    nlinarith [this]

end Work.Asymptotics
