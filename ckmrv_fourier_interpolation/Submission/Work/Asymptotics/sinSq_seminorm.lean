/-
# Seminorm bounds for the CKMRV prefactor `sinSq`

The CKMRV `low` part of the layer is `sinSq r · ∫_0^1 K(τ,it) e^{-πr²t} dt` with
`sinSq r = 4 sin²(πr²/2)`.  This file produces the integrand-level seminorm bound

  `|r|^k * ‖∂_r^l (sinSq · e^{-π r² t}) r‖ ≤ Γ * (t^(k+l))⁻¹`   for `t ∈ (0,1]`, `r ∈ ℝ`,

which is what is needed to dominate the differentiated contour integral (the `t`-power is then
absorbed by the flatness of the kernel at the cusp `0`).

The key point is that `sinSq r · e^{-πr²t}` is a sum of three *complex Gaussians*,
`2 e^{-(πt) r²} - e^{-(πt - iπ) r²} - e^{-(πt + iπ) r²}`, so that the complex-parameter Gaussian
bound `Work.Asymptotics.iteratedDeriv_exp_neg_sq_bound` applies to each term.
-/
import Mathlib
import Submission.Work.Asymptotics.gaussian_bound
import Submission.Work.Asymptotics.abs_pow_mul_exp_le

noncomputable section

open scoped Topology

namespace Work.Asymptotics

/-- `sinSq r = 2 - e^{iπr²} - e^{-iπr²}`, the complex-exponential form of `4 sin²(πr²/2)`. -/
lemma sinSq_eq_complex (r : ℝ) :
    sinSq r = 2 - Complex.exp (-((-Complex.I * Real.pi) * (r : ℂ) ^ 2))
      - Complex.exp (-((Complex.I * Real.pi) * (r : ℂ) ^ 2)) := by
  have hy : sinSq r = 2 - 2 * Complex.cos (Real.pi * (r : ℂ) ^ 2) := by
    rw [sinSq]
    have h := Complex.cos_two_mul_eq_one_sub (Real.pi * (r : ℂ) ^ 2 / 2)
    rw [show 2 * (Real.pi * (r : ℂ) ^ 2 / 2) = Real.pi * (r : ℂ) ^ 2 by ring] at h
    rw [h]; ring
  rw [hy, Complex.two_cos]
  have e1 : Complex.exp (Real.pi * (r : ℂ) ^ 2 * Complex.I)
      = Complex.exp (-((-Complex.I * Real.pi) * (r : ℂ) ^ 2)) := by congr 1; ring
  have e2 : Complex.exp (-(Real.pi * (r : ℂ) ^ 2) * Complex.I)
      = Complex.exp (-((Complex.I * Real.pi) * (r : ℂ) ^ 2)) := by congr 1; ring
  rw [e1, e2]; ring

/-- The three-Gaussian decomposition of `sinSq r · e^{-πr²t}`. -/
lemma sinSq_mul_exp_eq (t : ℝ) :
    (fun s : ℝ => sinSq s * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))))
      = fun s : ℝ =>
          2 * Complex.exp (-((((Real.pi * t : ℝ) : ℂ)) * (s : ℂ) ^ 2))
            - Complex.exp (-((((Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ) * Complex.I))
                * (s : ℂ) ^ 2))
            - Complex.exp (-((((Real.pi : ℂ) * (t : ℂ) + (Real.pi : ℂ) * Complex.I))
                * (s : ℂ) ^ 2)) := by
  funext s
  rw [sinSq_eq_complex]
  have h1 : Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))
      = Complex.exp (-((((Real.pi * t : ℝ) : ℂ)) * (s : ℂ) ^ 2)) := by
    congr 1; push_cast; ring
  have hA : Complex.exp (-((-Complex.I * Real.pi) * (s : ℂ) ^ 2))
        * Complex.exp (-((((Real.pi * t : ℝ) : ℂ)) * (s : ℂ) ^ 2))
      = Complex.exp (-((((Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ) * Complex.I))
          * (s : ℂ) ^ 2)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hB : Complex.exp (-((Complex.I * Real.pi) * (s : ℂ) ^ 2))
        * Complex.exp (-((((Real.pi * t : ℝ) : ℂ)) * (s : ℂ) ^ 2))
      = Complex.exp (-((((Real.pi : ℂ) * (t : ℂ) + (Real.pi : ℂ) * Complex.I))
          * (s : ℂ) ^ 2)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [h1, ← hA, ← hB]; ring

/-- Elementary weight bound: `|r|^m e^{-π r² t} ≤ Γ (t^m)⁻¹` for `t ∈ (0,1]`. -/
lemma abs_pow_mul_exp_neg_le (m : ℕ) :
    ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ r : ℝ,
      |r| ^ m * Real.exp (-(Real.pi * r ^ 2 * t)) ≤ Γ * (t ^ m)⁻¹ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨1, zero_le_one, ?_⟩
    intro t ht0 _ r
    simp only [pow_zero, one_mul, inv_one]
    rw [Real.exp_le_one_iff]
    have : (0:ℝ) ≤ Real.pi * r ^ 2 * t := by positivity
    linarith
  · set Γ : ℝ := max 1 (((m : ℝ) / (Real.pi * Real.exp 1)) ^ m) with hΓ
    have hΓ0 : 0 ≤ Γ := le_trans zero_le_one (le_max_left _ _)
    have hΓge : (1:ℝ) ≤ Γ := le_max_left _ _
    refine ⟨Γ, hΓ0, ?_⟩
    intro t ht0 ht1 r
    have hΓle : ((m : ℝ) / (Real.pi * Real.exp 1)) ^ m ≤ Γ := le_max_right _ _
    rcases lt_or_ge |r| 1 with hr | hr
    · have he : Real.exp (-(Real.pi * r ^ 2 * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : (0:ℝ) ≤ Real.pi * r ^ 2 * t := by positivity
        linarith
      have hr1 : |r| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg r) hr.le
      have hle1 : |r| ^ m * Real.exp (-(Real.pi * r ^ 2 * t)) ≤ 1 := by
        calc |r| ^ m * Real.exp (-(Real.pi * r ^ 2 * t)) ≤ 1 * 1 :=
              mul_le_mul hr1 he (Real.exp_nonneg _) (by norm_num)
          _ = 1 := by ring
      have hge : (1 : ℝ) ≤ Γ * (t ^ m)⁻¹ := by
        have h2 : (1 : ℝ) ≤ (t ^ m)⁻¹ := by
          rw [one_le_inv₀ (pow_pos ht0 m)]; exact pow_le_one₀ ht0.le ht1
        nlinarith [hΓge, h2]
      linarith
    · have habs : |r| ^ m ≤ |r| ^ (2 * m) := pow_le_pow_right₀ hr (by omega)
      have h := abs_pow_mul_exp_le (2 * m) ht0 r
      have h2m : ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) := by push_cast; ring
      rw [h2m, Real.rpow_natCast] at h
      have hstep : |r| ^ m * Real.exp (-(Real.pi * r ^ 2 * t))
          ≤ (((2 * m : ℕ) : ℝ) / (2 * Real.pi * Real.exp 1 * t)) ^ m :=
        le_trans (mul_le_mul_of_nonneg_right habs (Real.exp_nonneg _)) h
      have hbase : ((2 * m : ℕ) : ℝ) / (2 * Real.pi * Real.exp 1 * t)
          = ((m : ℝ) / (Real.pi * Real.exp 1)) * t⁻¹ := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
        push_cast
        ring
      rw [hbase, mul_pow, inv_pow] at hstep
      calc |r| ^ m * Real.exp (-(Real.pi * r ^ 2 * t))
          ≤ (((m : ℝ) / (Real.pi * Real.exp 1)) ^ m) * (t ^ m)⁻¹ := hstep
        _ ≤ Γ * (t ^ m)⁻¹ := mul_le_mul_of_nonneg_right hΓle (by positivity)

/-- **Seminorm bound for the integrand `sinSq · e^{-π r² t}`.**  For every `k l` there is `Γ ≥ 0`
with `|r|^k ‖∂_r^l (sinSq · e^{-π r² t}) r‖ ≤ Γ (t^(k+l))⁻¹` for `t ∈ (0,1]` and all `r`. -/
lemma sinSq_gauss_seminorm (k l : ℕ) :
    ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ r : ℝ,
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => sinSq s *
        Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) r‖
        ≤ Γ * (t ^ (k + l))⁻¹ := by
  obtain ⟨Γk, hΓk0, hΓk⟩ := abs_pow_mul_exp_neg_le k
  obtain ⟨Γkl, hΓkl0, hΓkl⟩ := abs_pow_mul_exp_neg_le (k + l)
  set M : ℝ := ((l + 1 : ℕ) : ℝ) * ((l + 2).factorial : ℝ) * (1 + 2 * Real.pi) ^ (2 * l) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hmax1 : (1:ℝ) ≤ max 1 Γkl := le_max_left _ _
  have hmaxΓ : Γkl ≤ max 1 Γkl := le_max_right _ _
  refine ⟨4 * M * 2 ^ l * max 1 Γkl, by positivity, ?_⟩
  intro t ht0 ht1 r
  have htinv : (1:ℝ) ≤ (t ^ (k + l))⁻¹ := by
    rw [one_le_inv₀ (pow_pos ht0 _)]; exact pow_le_one₀ ht0.le ht1
  -- uniform bound for one Gaussian
  have hterm : ∀ a : ℂ, ‖a‖ ≤ 2 * Real.pi → a.re = Real.pi * t →
      ‖iteratedDeriv l (fun s : ℝ => Complex.exp (-(a * (s : ℂ) ^ 2))) r‖
        ≤ M * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)) := by
    intro a ha hre
    have h := iteratedDeriv_exp_neg_sq_bound l a r
    refine le_trans h ?_
    have hkey : (1 + ‖a‖) ^ (2 * l) ≤ (1 + 2 * Real.pi) ^ (2 * l) :=
      pow_le_pow_left₀ (by positivity) (by linarith) (2 * l)
    have hexp : Real.exp (-(a.re) * r ^ 2) = Real.exp (-(Real.pi * r ^ 2 * t)) := by
      rw [hre]; ring_nf
    rw [hexp, hM]
    have hA : (0:ℝ) ≤ ((l + 1 : ℕ) : ℝ) * ((l + 2).factorial : ℝ) := by positivity
    calc ((l + 1 : ℕ) : ℝ) * ((l + 2).factorial : ℝ) * (1 + ‖a‖) ^ (2 * l) * (1 + |r|) ^ l
            * Real.exp (-(Real.pi * r ^ 2 * t))
        = (((l + 1 : ℕ) : ℝ) * ((l + 2).factorial : ℝ))
            * ((1 + ‖a‖) ^ (2 * l) * ((1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)))) := by ring
      _ ≤ (((l + 1 : ℕ) : ℝ) * ((l + 2).factorial : ℝ))
            * ((1 + 2 * Real.pi) ^ (2 * l)
                * ((1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hkey (by positivity)) hA
      _ = ((l + 1 : ℕ) : ℝ) * ((l + 2).factorial : ℝ) * (1 + 2 * Real.pi) ^ (2 * l)
            * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)) := by ring
  -- the three parameters
  rw [sinSq_mul_exp_eq t]
  set a1 : ℂ := ((Real.pi * t : ℝ) : ℂ) with ha1def
  set a2 : ℂ := (Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ) * Complex.I with ha2def
  set a3 : ℂ := (Real.pi : ℂ) * (t : ℂ) + (Real.pi : ℂ) * Complex.I with ha3def
  have hnpi : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by
    rw [show ‖((Real.pi : ℝ) : ℂ)‖ = |Real.pi| from RCLike.norm_ofReal Real.pi,
      abs_of_nonneg Real.pi_pos.le]
  have hnI : ‖(Complex.I : ℂ)‖ = 1 := Complex.norm_I
  have hna1 : ‖a1‖ ≤ 2 * Real.pi := by
    rw [ha1def]
    have hn : ‖(((Real.pi * t : ℝ)) : ℂ)‖ = Real.pi * t := by
      rw [show ‖(((Real.pi * t : ℝ)) : ℂ)‖ = |Real.pi * t| from RCLike.norm_ofReal (Real.pi * t),
        abs_of_nonneg (by positivity)]
    rw [hn]; nlinarith [ht1, Real.pi_pos]
  have hna2 : ‖a2‖ ≤ 2 * Real.pi := by
    rw [ha2def]
    have h1 : ‖(Real.pi : ℂ) * (t : ℂ)‖ = Real.pi * t := by
      rw [norm_mul, hnpi, show ‖((t : ℝ) : ℂ)‖ = |t| from RCLike.norm_ofReal t,
        abs_of_nonneg ht0.le]
    have h2 : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by
      rw [norm_mul, hnpi, hnI, mul_one]
    calc ‖(Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ) * Complex.I‖
        ≤ ‖(Real.pi : ℂ) * (t : ℂ)‖ + ‖(Real.pi : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ = Real.pi * t + Real.pi := by rw [h1, h2]
      _ ≤ 2 * Real.pi := by nlinarith [ht1, Real.pi_pos]
  have hra2 : a2.re = Real.pi * t := by
    rw [ha2def]; simp [Complex.mul_re, Complex.sub_re, Complex.I_re]
  have hna3 : ‖a3‖ ≤ 2 * Real.pi := by
    rw [ha3def]
    have h1 : ‖(Real.pi : ℂ) * (t : ℂ)‖ = Real.pi * t := by
      rw [norm_mul, hnpi, show ‖((t : ℝ) : ℂ)‖ = |t| from RCLike.norm_ofReal t,
        abs_of_nonneg ht0.le]
    have h2 : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by
      rw [norm_mul, hnpi, hnI, mul_one]
    calc ‖(Real.pi : ℂ) * (t : ℂ) + (Real.pi : ℂ) * Complex.I‖
        ≤ ‖(Real.pi : ℂ) * (t : ℂ)‖ + ‖(Real.pi : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = Real.pi * t + Real.pi := by rw [h1, h2]
      _ ≤ 2 * Real.pi := by nlinarith [ht1, Real.pi_pos]
  have hra1 : a1.re = Real.pi * t := by rw [ha1def]; simp
  have hra3 : a3.re = Real.pi * t := by
    rw [ha3def]; simp [Complex.mul_re, Complex.add_re, Complex.I_re]
  have hb1 := hterm a1 hna1 hra1
  have hb2 := hterm a2 hna2 hra2
  have hb3 := hterm a3 hna3 hra3
  have hofR : ContDiff ℝ (↑l : ℕ∞) (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.contDiff
  -- linearity of `iteratedDeriv` on the sum of three Gaussians
  have hc1 : ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => Complex.exp (-(a1 * (s : ℂ) ^ 2))) r := by
    fun_prop
  have hc2 : ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => 2 * Complex.exp (-(a1 * (s : ℂ) ^ 2))) r := by
    fun_prop
  have hc3 : ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2))) r := by
    fun_prop
  have hc4 : ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => Complex.exp (-(a3 * (s : ℂ) ^ 2))) r := by
    fun_prop
  have hlin : iteratedDeriv l (fun s : ℝ => 2 * Complex.exp (-(a1 * (s : ℂ) ^ 2))
        - Complex.exp (-(a2 * (s : ℂ) ^ 2)) - Complex.exp (-(a3 * (s : ℂ) ^ 2))) r
      = 2 * iteratedDeriv l (fun s : ℝ => Complex.exp (-(a1 * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a3 * (s : ℂ) ^ 2))) r := by
    have step1 : iteratedDeriv l (((fun s : ℝ => 2 * Complex.exp (-(a1 * (s : ℂ) ^ 2)))
          - (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2))))
          - (fun s : ℝ => Complex.exp (-(a3 * (s : ℂ) ^ 2)))) r
        = iteratedDeriv l ((fun s : ℝ => 2 * Complex.exp (-(a1 * (s : ℂ) ^ 2)))
            - (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2)))) r
          - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a3 * (s : ℂ) ^ 2))) r :=
      iteratedDeriv_sub (hc2.sub hc3) hc4
    have step2 : iteratedDeriv l ((fun s : ℝ => 2 * Complex.exp (-(a1 * (s : ℂ) ^ 2)))
            - (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2)))) r
        = iteratedDeriv l (fun s : ℝ => 2 * Complex.exp (-(a1 * (s : ℂ) ^ 2))) r
          - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2))) r :=
      iteratedDeriv_sub hc2 hc3
    have step3 : iteratedDeriv l (fun s : ℝ => 2 * Complex.exp (-(a1 * (s : ℂ) ^ 2))) r
        = 2 * iteratedDeriv l (fun s : ℝ => Complex.exp (-(a1 * (s : ℂ) ^ 2))) r :=
      iteratedDeriv_const_mul (2 : ℂ) hc1
    change iteratedDeriv l (((fun s : ℝ => 2 * Complex.exp (-(a1 * (s : ℂ) ^ 2)))
        - (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2))))
        - (fun s : ℝ => Complex.exp (-(a3 * (s : ℂ) ^ 2)))) r
      = 2 * iteratedDeriv l (fun s : ℝ => Complex.exp (-(a1 * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a3 * (s : ℂ) ^ 2))) r
    rw [step1, step2, step3]
  rw [hlin]
  -- norm bound
  have hnorm : ‖2 * iteratedDeriv l (fun s : ℝ => Complex.exp (-(a1 * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a3 * (s : ℂ) ^ 2))) r‖
      ≤ 2 * (M * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)))
        + M * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t))
        + M * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)) := by
    have h1 : ‖2 * iteratedDeriv l (fun s : ℝ => Complex.exp (-(a1 * (s : ℂ) ^ 2))) r‖
        ≤ 2 * (M * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t))) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hb1 (by norm_num)
    have hs1 := norm_sub_le (2 * iteratedDeriv l (fun s : ℝ => Complex.exp (-(a1 * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2))) r)
      (iteratedDeriv l (fun s : ℝ => Complex.exp (-(a3 * (s : ℂ) ^ 2))) r)
    have hs2 := norm_sub_le (2 * iteratedDeriv l (fun s : ℝ => Complex.exp (-(a1 * (s : ℂ) ^ 2))) r)
      (iteratedDeriv l (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2))) r)
    linarith [h1, hb2, hb3, hs1, hs2]
  -- weight bound
  have hweight : |r| ^ k * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t))
      ≤ 2 ^ l * max 1 Γkl * (t ^ (k + l))⁻¹ := by
    have hEl : Real.exp (-(Real.pi * r ^ 2 * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0:ℝ) ≤ Real.pi * r ^ 2 * t := by positivity
      linarith
    rcases lt_or_ge |r| 1 with hr | hr
    · have h1 : |r| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg r) hr.le
      have h2 : (1 + |r|) ^ l ≤ 2 ^ l :=
        pow_le_pow_left₀ (by linarith [abs_nonneg r]) (by linarith [hr.le]) l
      have h3 : |r| ^ k * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)) ≤ 2 ^ l := by
        calc |r| ^ k * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t))
            ≤ 1 * 2 ^ l * 1 := by
              apply mul_le_mul (mul_le_mul h1 h2 (by positivity) (by norm_num)) hEl
              · exact Real.exp_nonneg _
              · positivity
          _ = 2 ^ l := by ring
      calc |r| ^ k * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)) ≤ 2 ^ l := h3
        _ ≤ 2 ^ l * max 1 Γkl * (t ^ (k + l))⁻¹ := by
            have hpos : (0:ℝ) < 2 ^ l := by positivity
            have hmul : (1:ℝ) ≤ max 1 Γkl * (t ^ (k + l))⁻¹ := by
              have := mul_le_mul hmax1 htinv (zero_le_one) (le_trans zero_le_one hmax1)
              simpa using this
            have := mul_le_mul_of_nonneg_left hmul (le_of_lt hpos)
            nlinarith [this]
    · have h1r : (1:ℝ) ≤ |r| := hr
      have h2 : (1 + |r|) ^ l ≤ (2 * |r|) ^ l :=
        pow_le_pow_left₀ (by linarith [abs_nonneg r]) (by linarith) l
      have h3 : |r| ^ k * (1 + |r|) ^ l ≤ 2 ^ l * |r| ^ (k + l) := by
        calc |r| ^ k * (1 + |r|) ^ l ≤ |r| ^ k * (2 * |r|) ^ l :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = 2 ^ l * |r| ^ (k + l) := by rw [mul_pow]; ring
      have h4 : |r| ^ (k + l) * Real.exp (-(Real.pi * r ^ 2 * t))
          ≤ Γkl * (t ^ (k + l))⁻¹ := hΓkl t ht0 ht1 r
      have h5 : |r| ^ k * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t))
          ≤ 2 ^ l * (Γkl * (t ^ (k + l))⁻¹) := by
        calc |r| ^ k * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t))
            ≤ (2 ^ l * |r| ^ (k + l)) * Real.exp (-(Real.pi * r ^ 2 * t)) :=
              mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
          _ = 2 ^ l * (|r| ^ (k + l) * Real.exp (-(Real.pi * r ^ 2 * t))) := by ring
          _ ≤ 2 ^ l * (Γkl * (t ^ (k + l))⁻¹) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
      calc |r| ^ k * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t))
          ≤ 2 ^ l * (Γkl * (t ^ (k + l))⁻¹) := h5
        _ ≤ 2 ^ l * max 1 Γkl * (t ^ (k + l))⁻¹ := by
            have hpos : (0:ℝ) < 2 ^ l := by positivity
            have hmul : Γkl * (t ^ (k + l))⁻¹ ≤ max 1 Γkl * (t ^ (k + l))⁻¹ :=
              mul_le_mul_of_nonneg_right hmaxΓ (by positivity)
            have := mul_le_mul_of_nonneg_left hmul (le_of_lt hpos)
            nlinarith [this]
  -- assembly
  have hE4 : M * (4 * ((1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t))))
      = 4 * M * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)) := by ring
  have hW : |r| ^ k * (M * (4 * ((1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)))))
      ≤ M * (4 * (2 ^ l * max 1 Γkl * (t ^ (k + l))⁻¹)) := by
    rw [hE4]
    calc |r| ^ k * (4 * M * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)))
        = 4 * M * (|r| ^ k * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t))) := by ring
      _ ≤ 4 * M * (2 ^ l * max 1 Γkl * (t ^ (k + l))⁻¹) :=
          mul_le_mul_of_nonneg_left hweight (by positivity)
      _ = M * (4 * (2 ^ l * max 1 Γkl * (t ^ (k + l))⁻¹)) := by ring
  have hnorm' : ‖2 * iteratedDeriv l (fun s : ℝ => Complex.exp (-(a1 * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a3 * (s : ℂ) ^ 2))) r‖
      ≤ M * (4 * ((1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
    have heq : 2 * (M * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)))
        + M * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t))
        + M * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t))
        = M * (4 * ((1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)))) := by ring
    linarith [hnorm, heq ▸ le_refl (M * (4 * ((1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t)))))]
  calc |r| ^ k * ‖2 * iteratedDeriv l (fun s : ℝ => Complex.exp (-(a1 * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a2 * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(a3 * (s : ℂ) ^ 2))) r‖
      ≤ |r| ^ k * (M * (4 * ((1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2 * t))))) :=
        mul_le_mul_of_nonneg_left hnorm' (by positivity)
    _ ≤ M * (4 * (2 ^ l * max 1 Γkl * (t ^ (k + l))⁻¹)) := hW
    _ = 4 * M * 2 ^ l * max 1 Γkl * (t ^ (k + l))⁻¹ := by ring
