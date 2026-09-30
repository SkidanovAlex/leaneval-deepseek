import Mathlib
import Submission.Work.BMF.mrlas.Psi2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Assembly helpers for `Work.BMF.mrlas.Psi2_L2_bound`

* `intervalIntegral_mono_of_nonneg`: monotonicity of the interval integral for nonnegative
  functions.
* `continuousOn_gp`: continuity of the local Euler factor on `Re > 1`.
* `intervalIntegrable_gp2_inv`: interval-integrability of `τ ↦ ‖(gp f 2 (a+iτ))⁻¹‖²`.
-/

namespace Work.BMF.mrlas

open MeasureTheory intervalIntegral Real Complex
open scoped BigOperators

noncomputable section

lemma intervalIntegral_mono_of_nonneg {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hgint : IntervalIntegrable g volume a b) (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x)
    (hf0 : ∀ x ∈ Set.Icc a b, 0 ≤ f x) (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by
  by_cases hf : MeasureTheory.AEStronglyMeasurable f (volume.restrict (Set.uIoc a b))
  · refine intervalIntegral.integral_mono_on hab ?_ hgint hfg
    refine IntervalIntegrable.mono_fun' hgint hf ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
    have hx' : x ∈ Set.Icc a b := by rw [Set.uIoc_of_le hab] at hx; exact ⟨le_of_lt hx.1, hx.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x hx')]
    exact hfg x hx'
  · have hni : ¬ MeasureTheory.IntegrableOn f (Set.Ioc a b) volume := by
      intro hint
      exact hf (by rw [Set.uIoc_of_le hab]; exact hint.aestronglyMeasurable)
    have hzero : (∫ x in a..b, f x) = 0 := by
      rw [intervalIntegral.integral_of_le hab]
      exact MeasureTheory.integral_undef (fun h => hni h)
    rw [hzero]
    exact intervalIntegral.integral_nonneg hab hg0

/-- The local Euler factor is continuous on the half-plane `Re > 1`. -/
lemma continuousOn_gp (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : p.Prime) :
    ContinuousOn (gp f p) {w : ℂ | 1 < w.re} := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp1
  have hpinv : ((p:ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ hp1
  have hsum : Summable (fun e : ℕ => ((p:ℝ)⁻¹) ^ e) :=
    summable_geometric_of_norm_lt_one (R := ℝ)
      (by rw [Real.norm_of_nonneg (inv_nonneg.mpr hp0.le)]; exact hpinv)
  have key : ContinuousOn (fun w : ℂ => ∑' e : ℕ, LSeries.term f w (p ^ e))
      {w : ℂ | 1 < w.re} :=
    continuousOn_tsum (s := {w : ℂ | 1 < w.re})
      (f := fun (e:ℕ) (w:ℂ) => LSeries.term f w (p ^ e))
      (u := fun e : ℕ => ((p:ℝ)⁻¹) ^ e)
      (fun e w hw => (LSeries.hasDerivAt_term f (p^e) w).continuousAt.continuousWithinAt)
      hsum (fun e w hw => ?_)
  · exact key
  · have hw1 : 1 < w.re := hw
    rw [term_primePow f hp w e, norm_mul, norm_pow]
    have hnorm : ‖u p w‖ ≤ (p:ℝ)⁻¹ := by
      rw [norm_u hp.pos, ← Real.rpow_neg_one p]
      exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith [hw1])
    calc ‖f (p^e)‖ * ‖u p w‖^e ≤ 1 * ‖u p w‖^e :=
          mul_le_mul_of_nonneg_right (hb _) (pow_nonneg (norm_nonneg _) e)
      _ ≤ 1 * ((p:ℝ)⁻¹)^e :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm e) (by norm_num)
      _ = ((p:ℝ)⁻¹)^e := one_mul _

/-- `τ ↦ ‖(gp f 2 (a+iτ))⁻¹‖²` is interval-integrable. -/
lemma intervalIntegrable_gp2_inv (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {a : ℝ} (ha : 1 < a) (c : ℝ) :
    IntervalIntegrable (fun τ : ℝ => ‖(gp f 2 ((a : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ ^ 2)
      volume c (c+1) := by
  have hcontmap : Continuous (fun τ : ℝ => (a : ℂ) + (τ : ℂ) * Complex.I) :=
    Continuous.add continuous_const
      (Continuous.mul (Complex.continuous_ofReal.comp continuous_id) continuous_const)
  have hmem : ∀ τ : ℝ, (a : ℂ) + (τ : ℂ) * Complex.I ∈ {w : ℂ | 1 < w.re} := by
    intro τ
    have : ((a : ℂ) + (τ : ℂ) * Complex.I).re = a := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero]
      ring
    simp only [Set.mem_ofPred_eq]; rw [this]; exact ha
  have h1 : Continuous (fun τ : ℝ => gp f 2 ((a : ℂ) + (τ : ℂ) * Complex.I)) :=
    (continuousOn_gp f hb Nat.prime_two).comp_continuous hcontmap hmem
  have hne : ∀ τ : ℝ, gp f 2 ((a : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
    intro τ
    refine gp_ne_zero f hf1 hb (σ := (1 + a) / 2) (by linarith) 2 Nat.prime_two ?_
    have hre : ((a : ℂ) + (τ : ℂ) * Complex.I).re = a := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero]
      ring
    rw [hre]; linarith
  exact ((h1.inv₀ hne).norm.pow 2).intervalIntegrable _ _

/-- Assembly of the `L²` bound from a pointwise bound for `Ψ₂` and the resonance bound for the
reciprocal Euler factor at `2`. -/
lemma Psi2_integral_bound_of
    (B K : ℝ) (hB0 : 0 ≤ B) (hK0 : 0 ≤ K)
    (point : ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) → ∀ {s : ℂ}, 1 < s.re →
      ‖Psi2 f s‖ ≤ B * ‖(gp f 2 s)⁻¹‖ + K)
    (Cr : ℝ)
    (res : ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) → ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ c : ℝ,
      (∫ τ in c..(c+1), ‖(gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ ^ 2) ≤ Cr / α)
    (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (c : ℝ) :
    (∫ τ in c..(c+1), ‖Psi2 f ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
      ≤ (2 * B ^ 2 * Cr + 2 * K ^ 2) / α := by
  have ha : 1 < 1 + α := by linarith
  have hs : ∀ τ : ℝ, 1 < ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I).re := by
    intro τ
    have hre : ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I).re = 1 + α := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero]
      ring
    rw [hre]; linarith
  have hpointwise : ∀ τ : ℝ,
      ‖Psi2 f ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
        ≤ 2 * B ^ 2 * ‖(gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ ^ 2 + 2 * K ^ 2 := by
    intro τ
    have hp := point f hf1 hb (hs τ)
    have hx0 : 0 ≤ ‖(gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ := norm_nonneg _
    have key : (B * ‖(gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ + K) ^ 2
        ≤ 2 * B ^ 2 * ‖(gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ ^ 2 + 2 * K ^ 2 := by
      nlinarith [sq_nonneg (B * ‖(gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ - K),
        mul_nonneg hB0 hx0]
    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hp 2) key
  have hXint := intervalIntegrable_gp2_inv f hf1 hb (a := 1 + α) ha c
  have hgint : IntervalIntegrable
      (fun τ : ℝ => 2 * B ^ 2 * ‖(gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ ^ 2
        + 2 * K ^ 2) volume c (c+1) :=
    (hXint.const_mul (2 * B ^ 2)).add intervalIntegrable_const
  have hmain := intervalIntegral_mono_of_nonneg (by linarith : c ≤ c + 1)
    (a := c) (b := c+1) (f := fun τ : ℝ => ‖Psi2 f ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
    (g := fun τ : ℝ => 2 * B ^ 2 * ‖(gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ ^ 2
      + 2 * K ^ 2)
    hgint
    (fun x _ => by positivity)
    (fun x _ => by positivity)
    (fun x _ => hpointwise x)
  calc (∫ τ in c..(c+1), ‖Psi2 f ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
      ≤ ∫ τ in c..(c+1), (2 * B ^ 2
          * ‖(gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ ^ 2 + 2 * K ^ 2) := hmain
    _ = 2 * B ^ 2 * (∫ τ in c..(c+1),
          ‖(gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ ^ 2) + 2 * K ^ 2 := by
        rw [intervalIntegral.integral_add (hXint.const_mul (2 * B ^ 2)) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
    _ ≤ 2 * B ^ 2 * (Cr / α) + 2 * K ^ 2 := by
        have hres := res f hf1 hb α hα hα1 c
        nlinarith [sq_nonneg B, hK0, hα]
    _ ≤ (2 * B ^ 2 * Cr + 2 * K ^ 2) / α := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hle : (1:ℝ) ≤ α⁻¹ := by rw [← inv_one]; exact inv_anti₀ hα hα1
        have h2 : 2 * K ^ 2 ≤ 2 * K ^ 2 * α⁻¹ := by
          nth_rewrite 1 [← mul_one (2 * K ^ 2)]
          exact mul_le_mul_of_nonneg_left hle (by positivity)
        linarith [h2]


/-- For a prime `p ≠ 2`, `‖u p s‖ ≤ 1/3` when `Re s ≥ 1`. -/
lemma norm_u_le_of_ne_two {p : Nat.Primes} (hp : p ≠ (⟨2, Nat.prime_two⟩ : Nat.Primes))
    {s : ℂ} (hs : 1 ≤ s.re) : ‖u (p:ℕ) s‖ ≤ (3:ℝ)⁻¹ := by
  have hpne : (p : ℕ) ≠ 2 := fun h => hp (Subtype.ext h)
  have hp3n : 3 ≤ (p : ℕ) := by have := p.2.two_le; omega
  have hp3 : (3:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast hp3n
  rw [norm_u p.2.pos]
  have h1 : ((p:ℕ):ℝ) ^ (-s.re) ≤ ((p:ℕ):ℝ) ^ ((-1:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : ((p:ℕ):ℝ) ^ ((-1:ℝ)) ≤ (3:ℝ)⁻¹ := by
    rw [Real.rpow_neg_one]
    exact inv_anti₀ (by norm_num) hp3
  linarith

/-- For a prime `p ≠ 2` and `Re s > 1`, `‖(gp f p s)⁻¹‖ ≤ 2`. -/
lemma gp_inv_le_two_of_ne_two (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {p : Nat.Primes} (hp : p ≠ (⟨2, Nat.prime_two⟩ : Nat.Primes)) {s : ℂ} (hs : 1 < s.re) :
    ‖(gp f (p:ℕ) s)⁻¹‖ ≤ 2 := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hu := norm_u_le_of_ne_two hp (le_of_lt hs)
  have hu' : ‖u (p:ℕ) s‖ ≤ (1:ℝ)/3 := by
    rw [show (3:ℝ)⁻¹ = 1/3 by norm_num] at hu; exact hu
  have hlow := gp_lower_bound f hf1 hb p.2 hs0
  have hgp : (1:ℝ)/2 ≤ ‖gp f (p:ℕ) s‖ := by
    have hx : (1:ℝ)/2 ≤ (1 - 2*‖u (p:ℕ) s‖)/(1 - ‖u (p:ℕ) s‖) := by
      rw [le_div_iff₀ (by linarith [norm_nonneg (u (p:ℕ) s), hu'])]
      nlinarith [hu', norm_nonneg (u (p:ℕ) s)]
    linarith
  rw [norm_inv]
  have h := inv_anti₀ (by norm_num : (0:ℝ) < 1/2) hgp
  rw [show ((1:ℝ)/2)⁻¹ = 2 by norm_num] at h
  exact h

/-- Pointwise bound for `Ψ₂` on `Re s > 1`, given the per-prime bound and the summabilities. -/
lemma Psi2_pointwise_of
    (Tpb : ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) → ∀ {p : ℕ}, p.Prime →
      ∀ {s : ℂ}, 1 < s.re →
      ‖deriv (gp f p) s / gp f p s + f p * (Real.log p : ℂ) * (p : ℂ) ^ (-s)‖
        ≤ 16 * Real.log p * (p : ℝ) ^ (-2 * s.re) * ‖(gp f p s)⁻¹‖)
    (hsumm : ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) → ∀ {s : ℂ}, 1 < s.re →
      Summable (fun p : Nat.Primes => deriv (gp f (p : ℕ)) s / gp f (p : ℕ) s) ∧
      Summable (fun p : Nat.Primes =>
        -(f (p : ℕ) * (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s))))
    (K : ℝ)
    (hK : ∀ σ : ℝ, 1 ≤ σ →
      Summable (fun p : Nat.Primes => Real.log p * (p : ℝ) ^ (-2 * σ)) ∧
      (∑' p : Nat.Primes, Real.log p * (p : ℝ) ^ (-2 * σ)) ≤ K)
    (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖Psi2 f s‖ ≤ 16 * Real.log 2 * ‖(gp f 2 s)⁻¹‖ + 32 * K := by
  obtain ⟨hKsum, hKle⟩ := hK s.re (le_of_lt hs)
  obtain ⟨hsA, hsB⟩ := hsumm f hf1 hb hs
  let p₂ : Nat.Primes := ⟨2, Nat.prime_two⟩
  let C2 : ℝ := ‖deriv (gp f 2) s / gp f 2 s + f 2 * (Real.log 2 : ℂ) * (2:ℂ)^(-s)‖
  let m : Nat.Primes → ℝ := fun p => if p = p₂ then C2 else 32 * Real.log p * (p:ℝ)^(-2*s.re)
  have hm_spike : Summable (fun p : Nat.Primes => if p = p₂ then C2 else (0:ℝ)) :=
    (hasSum_ite_eq p₂ C2).summable
  have hm_rest : Summable (fun p : Nat.Primes =>
      if p = p₂ then (0:ℝ) else 32 * Real.log p * (p:ℝ) ^ (-2 * s.re)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hKsum.mul_left 32)
    · split_ifs with h
      · exact le_refl 0
      · exact mul_nonneg (mul_nonneg (by norm_num)
          (Real.log_nonneg (by exact_mod_cast (le_of_lt p.2.one_lt)))) (Real.rpow_nonneg (by positivity) _)
    · split_ifs with h
      · exact mul_nonneg (by norm_num) (mul_nonneg (Real.log_nonneg (by exact_mod_cast (le_of_lt p.2.one_lt)))
          (Real.rpow_nonneg (by positivity) _))
      · exact le_of_eq (by ring)
  have hm : Summable m := by
    have htot := hm_spike.add hm_rest
    rwa [show (fun p : Nat.Primes => (if p = p₂ then C2 else (0:ℝ))
          + (if p = p₂ then (0:ℝ) else 32 * Real.log p * (p:ℝ) ^ (-2 * s.re))) = m from
      funext (fun p => by simp only [m]; split_ifs <;> ring)] at htot
  have hterm : ∀ p : Nat.Primes,
      ‖deriv (gp f (p:ℕ)) s / gp f (p:ℕ) s
        + f (p:ℕ) * (Real.log (p:ℕ) : ℂ) * ((p:ℕ) : ℂ) ^ (-s)‖ ≤ m p := by
    intro p
    by_cases hp : p = p₂
    · subst hp
      show ‖deriv (gp f (p₂:ℕ)) s / gp f (p₂:ℕ) s
        + f (p₂:ℕ) * (Real.log (p₂:ℕ) : ℂ) * ((p₂:ℕ) : ℂ) ^ (-s)‖ ≤ C2
      exact le_of_eq rfl
    · rw [show m p = 32 * Real.log p * (p:ℝ)^(-2*s.re) by
        simp only [m]; exact if_neg hp]
      have hinv := gp_inv_le_two_of_ne_two f hf1 hb hp hs
      refine le_trans (Tpb f hf1 hb p.2 hs) ?_
      have hfac : 0 ≤ 16 * Real.log (p:ℕ) * ((p:ℕ):ℝ) ^ (-2 * s.re) :=
        mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (le_of_lt p.2.one_lt))))
          (Real.rpow_nonneg (by positivity) _)
      calc 16 * Real.log (p:ℕ) * ((p:ℕ):ℝ) ^ (-2 * s.re) * ‖(gp f (p:ℕ) s)⁻¹‖
          ≤ 16 * Real.log (p:ℕ) * ((p:ℕ):ℝ) ^ (-2 * s.re) * 2 :=
            mul_le_mul_of_nonneg_left hinv hfac
        _ = 32 * Real.log (p:ℕ) * ((p:ℕ):ℝ) ^ (-2 * s.re) := by ring
  have hS : Summable (fun p : Nat.Primes => ‖deriv (gp f (p:ℕ)) s / gp f (p:ℕ) s
      + f (p:ℕ) * (Real.log (p:ℕ) : ℂ) * ((p:ℕ) : ℂ) ^ (-s)‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hterm hm
  have ht : Psi2 f s = ∑' p : Nat.Primes, (deriv (gp f (p:ℕ)) s / gp f (p:ℕ) s
      + f (p:ℕ) * (Real.log (p:ℕ) : ℂ) * ((p:ℕ) : ℂ) ^ (-s)) := by
    rw [Psi2, Psi, Psi1, ← Summable.tsum_sub hsA hsB]
    exact tsum_congr (fun p => by ring)
  have h4 : (∑' p : Nat.Primes, (if p = p₂ then (0:ℝ) else 32 * Real.log p * (p:ℝ) ^ (-2 * s.re)))
      ≤ 32 * K := by
    refine le_trans (Summable.tsum_le_tsum (fun p => ?_) hm_rest (hKsum.mul_left 32)) ?_
    · split_ifs with h
      · exact mul_nonneg (by norm_num) (mul_nonneg (Real.log_nonneg (by exact_mod_cast (le_of_lt p.2.one_lt)))
          (Real.rpow_nonneg (by positivity) _))
      · exact le_of_eq (by ring)
    · rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hKle (by norm_num)
  have hC2 : C2 ≤ 16 * Real.log 2 * ‖(gp f 2 s)⁻¹‖ := by
    have hb2 := Tpb f hf1 hb Nat.prime_two hs
    have hle1 : (2:ℝ) ^ (-2 * s.re) ≤ 1 := by
      have h1 : (2:ℝ) ^ (-2 * s.re) = ((2:ℝ) ^ (2 * s.re))⁻¹ := by
        rw [show -2 * s.re = -(2 * s.re) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      rw [h1]
      refine inv_le_one_of_one_le₀ ?_
      calc (1:ℝ) = (1:ℝ) ^ (2 * s.re) := (Real.one_rpow _).symm
        _ ≤ (2:ℝ) ^ (2 * s.re) := Real.rpow_le_rpow (by norm_num) (by norm_num) (by linarith)
    calc C2 ≤ 16 * Real.log 2 * (2:ℝ) ^ (-2 * s.re) * ‖(gp f 2 s)⁻¹‖ := hb2
      _ ≤ 16 * Real.log 2 * 1 * ‖(gp f 2 s)⁻¹‖ := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle1 (by positivity))
          positivity
      _ = 16 * Real.log 2 * ‖(gp f 2 s)⁻¹‖ := by ring
  calc ‖Psi2 f s‖ ≤ ∑' p : Nat.Primes, ‖deriv (gp f (p:ℕ)) s / gp f (p:ℕ) s
        + f (p:ℕ) * (Real.log (p:ℕ) : ℂ) * ((p:ℕ) : ℂ) ^ (-s)‖ := by
        rw [ht]; exact norm_tsum_le_tsum_norm hS
    _ ≤ ∑' p : Nat.Primes, m p := Summable.tsum_le_tsum hterm hS hm
    _ = C2 + ∑' p : Nat.Primes, (if p = p₂ then (0:ℝ) else 32 * Real.log p * (p:ℝ) ^ (-2 * s.re)) := by
        rw [show m = (fun p : Nat.Primes => (if p = p₂ then C2 else (0:ℝ))
            + (if p = p₂ then (0:ℝ) else 32 * Real.log p * (p:ℝ) ^ (-2 * s.re))) from
          funext (fun p => by simp only [m]; split_ifs <;> ring)]
        rw [Summable.tsum_add hm_spike hm_rest, (hasSum_ite_eq p₂ C2).tsum_eq]
    _ ≤ 16 * Real.log 2 * ‖(gp f 2 s)⁻¹‖ + 32 * K := by linarith [hC2, h4]

end

end Work.BMF.mrlas
