import Mathlib
import Submission.Work.Fx.ExpPosDefs
import Submission.Work.Fx.FxTdivReal

/-!
# Final truncation step of the positive exponential field (paper Lemma 2.14)

Given `E = exp(Z/2^Q)` (`Q = 2p+60`), the word output `(U,V)` satisfies
`‖(U+iV)/2^Q - E‖ ≤ 4/2^Q`, i.e. `|U - 2^Q E| ≤ 4` and `|V| ≤ 4`.  With `s = p + 60 + τ`
and the two analytic hypotheses `h2` (`E + 4/2^Q ≤ 2^τ`) and `h3`
(`2^p |2^{-τ} E - 2^{-σ} e^{πj/k}| ≤ 1/2`), the truncation `2^{-s}(U,V)` lies in `C̃◦` and
represents `2^{-σ} e^{πj/k}` up to error `< 2`.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- Coordinate bounds extracted from the complex error bound `hU`: writing `E` for
`Real.exp (Z/2^{epQ p})`, we get `|U - 2^{epQ p} E| ≤ 4` and `|V| ≤ 4`. -/
theorem epHU_aux (p : ℕ) (Z U V : ℤ)
    (hU : ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (epQ p) -
        Complex.exp ((Z : ℂ) / (2 : ℂ) ^ (epQ p))‖ ≤ 4 / (2 : ℝ) ^ (epQ p)) :
    |(U : ℝ) - (2 : ℝ) ^ (epQ p) * Real.exp ((Z : ℝ) / (2 : ℝ) ^ (epQ p))| ≤ 4 ∧
    |(V : ℝ)| ≤ 4 := by
  set D : ℝ := (2 : ℝ) ^ (epQ p) with hD
  have hDpos : 0 < D := by rw [hD]; exact zpow_pos (by norm_num) _
  set E : ℝ := Real.exp ((Z : ℝ) / (2 : ℝ) ^ (epQ p)) with hE
  have hpow : (2 : ℂ) ^ (epQ p) = (D : ℂ) := by rw [hD]; push_cast; ring
  have hexp : Complex.exp ((Z : ℂ) / (2 : ℂ) ^ (epQ p)) = (E : ℂ) := by
    have harg : (Z : ℂ) / (2 : ℂ) ^ (epQ p) = (((Z : ℝ) / D : ℝ) : ℂ) := by
      rw [hpow, show (Z : ℂ) = ((Z : ℝ) : ℂ) by simp, ← Complex.ofReal_div]
    rw [harg, ← Complex.ofReal_exp]
  set w : ℂ := (((U : ℝ) - D * E : ℝ) : ℂ) + ((V : ℝ) : ℂ) * Complex.I with hw
  have hDc : (D : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hDpos
  have hkey : ((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (epQ p) -
      Complex.exp ((Z : ℂ) / (2 : ℂ) ^ (epQ p)) = w / (D : ℂ) := by
    rw [hexp, hpow, hw]
    push_cast
    field_simp [hDc]
    ring
  have hnormD : ‖(D : ℂ)‖ = D := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (le_of_lt hDpos)]
  have hU' : ‖w / (D : ℂ)‖ ≤ 4 / D := by
    rw [← hkey, hD]; exact hU
  have hwle : ‖w‖ ≤ 4 := by
    have h1 : ‖w‖ / D ≤ 4 / D := by rwa [norm_div, hnormD] at hU'
    exact (div_le_div_iff_of_pos_right hDpos).mp h1
  have hre : w.re = (U : ℝ) - D * E := by simp [hw]
  have him : w.im = (V : ℝ) := by simp [hw]
  constructor
  · rw [← hre]
    exact le_trans (Complex.abs_re_le_norm w) hwle
  · rw [← him]
    exact le_trans (Complex.abs_im_le_norm w) hwle

/-- Scaling hypothesis `h2` by `2^{p-τ}`: `2^{p-τ} E ≤ 2^p - 4/2^s`. -/
theorem epH2_aux (p : ℕ) (τ s Z : ℤ) (hs : s = epA p + τ)
    (h2 : Real.exp ((Z : ℝ) / (2 : ℝ) ^ (epQ p)) + 4 / (2 : ℝ) ^ (epQ p)
        ≤ (2 : ℝ) ^ τ) :
    (2 : ℝ) ^ ((p : ℤ) - τ) * Real.exp ((Z : ℝ) / (2 : ℝ) ^ (epQ p))
      ≤ (2 : ℝ) ^ p - 4 / (2 : ℝ) ^ s := by
  set E : ℝ := Real.exp ((Z : ℝ) / (2 : ℝ) ^ (epQ p)) with hE
  set pt : ℝ := (2 : ℝ) ^ ((p : ℤ) - τ) with hpt
  have hptpos : 0 < pt := by rw [hpt]; exact zpow_pos (by norm_num) _
  have h2' : pt * E + pt * (4 / (2 : ℝ) ^ (epQ p)) ≤ pt * (2 : ℝ) ^ τ := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left h2 (le_of_lt hptpos)
  have hptTau : pt * (2 : ℝ) ^ τ = (2 : ℝ) ^ p := by
    rw [hpt, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (p : ℤ) - τ + τ = (p : ℤ) by ring, zpow_natCast]
  have hexp : ((p : ℤ) - τ) - epQ p = -s := by
    rw [hs]; simp only [epA, epQ]; ring
  have hptQ : pt * (4 / (2 : ℝ) ^ (epQ p)) = 4 / (2 : ℝ) ^ s := by
    rw [hpt, div_eq_mul_inv, div_eq_mul_inv, ← zpow_neg, ← zpow_neg]
    rw [show (2 : ℝ) ^ ((p : ℤ) - τ) * (4 * (2 : ℝ) ^ (-epQ p))
        = 4 * ((2 : ℝ) ^ ((p : ℤ) - τ) * (2 : ℝ) ^ (-epQ p)) by ring]
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (p : ℤ) - τ + -(epQ p) = -s by rw [← hexp]; ring]
  rw [hptTau, hptQ] at h2'
  linarith

theorem ExpPosFinal (p j k σ : ℕ) (τ Z s U V : ℤ)
    (hp : 100 ≤ p) (hτ0 : 0 ≤ τ) (hs : s = Work.Fx.epA p + τ)
    (h2 : Real.exp ((Z : ℝ) / (2 : ℝ) ^ (Work.Fx.epQ p)) + 4 / (2 : ℝ) ^ (Work.Fx.epQ p)
        ≤ (2 : ℝ) ^ τ)
    (h3 : (2 : ℝ) ^ p * |(2 : ℝ) ^ (-τ) * Real.exp ((Z : ℝ) / (2 : ℝ) ^ (Work.Fx.epQ p)) -
        (2 : ℝ) ^ (-(σ : ℤ)) * Real.exp (Real.pi * (j : ℝ) / (k : ℝ))| ≤ 1 / 2)
    (hU : ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (Work.Fx.epQ p) -
        Complex.exp ((Z : ℂ) / (2 : ℂ) ^ (Work.Fx.epQ p))‖ ≤ 4 / (2 : ℝ) ^ (Work.Fx.epQ p)) :
    HvdH.inDisc p (Work.Fx.epSh U s, Work.Fx.epSh V s) ∧
    (2 : ℝ) ^ p * ‖HvdH.fxC p (Work.Fx.epSh U s, Work.Fx.epSh V s) -
        (((2 : ℝ) ^ (-(σ : ℤ)) * Real.exp (Real.pi * (j : ℝ) / (k : ℝ)) : ℝ) : ℂ)‖ < 2 := by
  obtain ⟨hUabs, hVabs⟩ := epHU_aux p Z U V hU
  have h2b := epH2_aux p τ s Z hs h2
  -- ## size bookkeeping
  have hs0 : 0 ≤ s := by rw [hs]; simp only [epA]; omega
  have hsnat : ((s.toNat : ℤ)) = s := Int.toNat_of_nonneg hs0
  have hs160 : (160 : ℤ) ≤ s := by rw [hs]; simp only [epA]; omega
  have hsN160 : 160 ≤ s.toNat := (Int.le_toNat hs0).mpr hs160
  set N : ℤ := (2 : ℤ) ^ s.toNat with hN
  have hNpos : 0 < N := by rw [hN]; exact pow_pos (by norm_num) _
  have hNs : (2 : ℝ) ^ s = (2 : ℝ) ^ s.toNat := by
    conv_lhs => rw [← hsnat]
    rw [zpow_natCast]
  have hNcast : (N : ℝ) = (2 : ℝ) ^ s := by
    rw [hN, hNs]; push_cast; ring
  have hNposR : (0 : ℝ) < (N : ℝ) := by rw [hNcast]; exact zpow_pos (by norm_num) _
  have hNgt4z : (4 : ℤ) < N := by
    have h4 : (4 : ℝ) < (N : ℝ) := by
      rw [hNcast, hNs]
      calc (4 : ℝ) < (2 : ℝ) ^ 160 := by norm_num
        _ ≤ (2 : ℝ) ^ s.toNat := pow_le_pow_right₀ (by norm_num) hsN160
    exact_mod_cast h4
  -- ## abbreviations
  set D : ℝ := (2 : ℝ) ^ (Work.Fx.epQ p) with hD
  set E : ℝ := Real.exp ((Z : ℝ) / D) with hE
  set ex : ℝ := Real.exp (Real.pi * (j : ℝ) / (k : ℝ)) with hx
  set c : ℝ := (2 : ℝ) ^ (-(σ : ℤ)) * ex with hc
  have hDpos : 0 < D := by rw [hD]; exact zpow_pos (by norm_num) _
  have hEpos : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hDE : (0 : ℝ) < D * E := mul_pos hDpos hEpos
  have hp_pos : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hDsplit : D / (N : ℝ) = (2 : ℝ) ^ ((p : ℤ) - τ) := by
    rw [hD, hNcast, ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    rw [hs]; simp only [epA, epQ]; ring
  -- ## truncation variables
  set A : ℤ := Int.tdiv U N with hA
  set B : ℤ := Int.tdiv V N with hB
  have hAsh : Work.Fx.epSh U s = A := by simp only [Work.Fx.epSh, hN, hA]
  have hBsh : Work.Fx.epSh V s = B := by simp only [Work.Fx.epSh, hN, hB]
  -- ## `V` truncates to `0`
  have hV4 : (|V| : ℤ) ≤ 4 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hVabs
    exact abs_le.mpr ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hVlt : |V| < N := lt_of_le_of_lt hV4 hNgt4z
  have hB0 : B = 0 := by rw [hB]; exact (FxTdivReal V N hNpos).2 hVlt
  -- ## `U` is bounded below
  have hUlow : (-4 : ℤ) < U := by
    have h1 : (-4 : ℝ) ≤ (U : ℝ) - D * E := (abs_le.mp hUabs).1
    have h2 : (-4 : ℝ) < (U : ℝ) := by linarith
    exact_mod_cast h2
  have hUneg : U < 0 → (|U| : ℤ) < N := by
    intro h
    have hlt : |U| < 4 := abs_lt.mpr ⟨hUlow, by omega⟩
    exact lt_of_lt_of_le hlt (le_of_lt hNgt4z)
  -- ## bounds on `A`
  have hA0 : 0 ≤ A := by
    by_cases hU0 : 0 ≤ U
    · rw [hA]; exact Int.tdiv_nonneg hU0 (le_of_lt hNpos)
    · push_neg at hU0
      have hAz : A = 0 := by rw [hA]; exact (FxTdivReal U N hNpos).2 (hUneg hU0)
      exact le_of_eq hAz.symm
  have hAle : (A : ℝ) ≤ (2 : ℝ) ^ p := by
    by_cases hU0 : 0 ≤ U
    · have hAU : (A : ℝ) * (N : ℝ) ≤ (U : ℝ) := by
        rw [hA]
        have hmul : N * (U.tdiv N) + U.tmod N = U := Int.mul_tdiv_add_tmod U N
        have htmod0 : 0 ≤ U.tmod N := Int.tmod_nonneg N hU0
        have hle : N * (U.tdiv N) ≤ U := by linarith
        have hc' : ((N * (U.tdiv N) : ℤ) : ℝ) ≤ (U : ℝ) := by exact_mod_cast hle
        push_cast at hc'
        linarith
      have hUup : (U : ℝ) ≤ D * E + 4 := by
        have h := (abs_le.mp hUabs).2; linarith
      have h1 : (A : ℝ) ≤ (U : ℝ) / (N : ℝ) := by
        rw [le_div_iff₀ hNposR]; exact hAU
      have h2' : (U : ℝ) / (N : ℝ) ≤ (D * E + 4) / (N : ℝ) :=
        div_le_div_of_nonneg_right hUup (le_of_lt hNposR)
      have hval : (D * E + 4) / (N : ℝ)
          = (2 : ℝ) ^ ((p : ℤ) - τ) * E + 4 / (2 : ℝ) ^ s := by
        rw [add_div, ← div_mul_eq_mul_div, hDsplit, hNcast]
      rw [hval] at h2'
      linarith [h2b]
    · push_neg at hU0
      have hAz : A = 0 := by rw [hA]; exact (FxTdivReal U N hNpos).2 (hUneg hU0)
      rw [hAz, Int.cast_zero]
      exact le_of_lt hp_pos
  have hAleZ : A ≤ (2 : ℤ) ^ p := by
    have h1 : (A : ℝ) ≤ (((2 : ℤ) ^ p : ℤ) : ℝ) := by push_cast; exact hAle
    exact_mod_cast h1
  have h4p : ((2 : ℤ) ^ p) ^ 2 = 4 ^ p := by
    have hp2 : p * 2 = 2 * p := by omega
    rw [← pow_mul, hp2, show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hinD : HvdH.inDisc p (A, B) := by
    show A ^ 2 + B ^ 2 ≤ 4 ^ p
    have hsq : A ^ 2 ≤ 4 ^ p := by
      rw [← h4p]
      exact pow_le_pow_left₀ hA0 hAleZ 2
    rw [hB0]
    simpa using hsq
  -- ## error estimate
  have h1σ : (2 : ℝ) ^ p * (2 : ℝ) ^ (-τ) = (2 : ℝ) ^ ((p : ℤ) - τ) := by
    have he : (p : ℤ) + (-τ) = (p : ℤ) - τ := by ring
    calc (2 : ℝ) ^ p * (2 : ℝ) ^ (-τ)
        = (2 : ℝ) ^ ((p : ℤ)) * (2 : ℝ) ^ (-τ) := by rw [zpow_natCast]
      _ = (2 : ℝ) ^ ((p : ℤ) + (-τ)) := by rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = (2 : ℝ) ^ ((p : ℤ) - τ) := by rw [he]
  have h2σ : (2 : ℝ) ^ p * (2 : ℝ) ^ (-(σ : ℤ)) = (2 : ℝ) ^ ((p : ℤ) - (σ : ℤ)) := by
    have he : (p : ℤ) + (-(σ : ℤ)) = (p : ℤ) - (σ : ℤ) := by ring
    calc (2 : ℝ) ^ p * (2 : ℝ) ^ (-(σ : ℤ))
        = (2 : ℝ) ^ ((p : ℤ)) * (2 : ℝ) ^ (-(σ : ℤ)) := by rw [zpow_natCast]
      _ = (2 : ℝ) ^ ((p : ℤ) + (-(σ : ℤ))) := by
            rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = (2 : ℝ) ^ ((p : ℤ) - (σ : ℤ)) := by rw [he]
  have h3r : |(2 : ℝ) ^ ((p : ℤ) - τ) * E - (2 : ℝ) ^ ((p : ℤ) - (σ : ℤ)) * ex| ≤ 1 / 2 := by
    have heq : (2 : ℝ) ^ p * ((2 : ℝ) ^ (-τ) * E - (2 : ℝ) ^ (-(σ : ℤ)) * ex)
        = (2 : ℝ) ^ ((p : ℤ) - τ) * E - (2 : ℝ) ^ ((p : ℤ) - (σ : ℤ)) * ex := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, h1σ, h2σ]
    have heq2 : (2 : ℝ) ^ p * |(2 : ℝ) ^ (-τ) * E - (2 : ℝ) ^ (-(σ : ℤ)) * ex|
        = |(2 : ℝ) ^ ((p : ℤ) - τ) * E - (2 : ℝ) ^ ((p : ℤ) - (σ : ℤ)) * ex| := by
      calc (2 : ℝ) ^ p * |(2 : ℝ) ^ (-τ) * E - (2 : ℝ) ^ (-(σ : ℤ)) * ex|
          = |(2 : ℝ) ^ p| * |(2 : ℝ) ^ (-τ) * E - (2 : ℝ) ^ (-(σ : ℤ)) * ex| := by
            rw [abs_of_pos hp_pos]
        _ = |(2 : ℝ) ^ p * ((2 : ℝ) ^ (-τ) * E - (2 : ℝ) ^ (-(σ : ℤ)) * ex)| :=
            (abs_mul _ _).symm
        _ = |(2 : ℝ) ^ ((p : ℤ) - τ) * E - (2 : ℝ) ^ ((p : ℤ) - (σ : ℤ)) * ex| := by rw [heq]
    rw [← heq2]; exact h3
  have hAerr : |(A : ℝ) - (2 : ℝ) ^ ((p : ℤ) - τ) * E| ≤ 1 + 4 / (2 : ℝ) ^ s := by
    have ht1 : |(A : ℝ) - (U : ℝ) / (N : ℝ)| ≤ 1 := by
      rw [hA]; exact (FxTdivReal U N hNpos).1
    have ht2 : |(U : ℝ) / (N : ℝ) - (2 : ℝ) ^ ((p : ℤ) - τ) * E| ≤ 4 / (2 : ℝ) ^ s := by
      have hsplit : (U : ℝ) / (N : ℝ) - (2 : ℝ) ^ ((p : ℤ) - τ) * E
          = ((U : ℝ) - D * E) / (N : ℝ) := by
        rw [sub_div, ← hDsplit, div_mul_eq_mul_div]
      rw [hsplit, abs_div, abs_of_pos hNposR, ← hNcast]
      apply div_le_div_of_nonneg_right _ (le_of_lt hNposR)
      exact hUabs
    have htri := abs_sub_le (A : ℝ) ((U : ℝ) / (N : ℝ)) ((2 : ℝ) ^ ((p : ℤ) - τ) * E)
    linarith
  have hflat : (2 : ℝ) ^ p * c = (2 : ℝ) ^ ((p : ℤ) - (σ : ℤ)) * ex := by
    rw [hc, ← mul_assoc, h2σ]
  have hfinal : |(A : ℝ) - (2 : ℝ) ^ p * c| < 2 := by
    have htri := abs_sub_le (A : ℝ) ((2 : ℝ) ^ ((p : ℤ) - τ) * E) ((2 : ℝ) ^ p * c)
    rw [hflat] at htri
    have h4s : 4 / (2 : ℝ) ^ s < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ s)]
      have h8 : (8 : ℝ) < (2 : ℝ) ^ s := by
        rw [hNs]
        calc (8 : ℝ) < (2 : ℝ) ^ 160 := by norm_num
          _ ≤ (2 : ℝ) ^ s.toNat := pow_le_pow_right₀ (by norm_num) hsN160
      linarith
    have hb : |(A : ℝ) - (2 : ℝ) ^ p * c| ≤ 1 + 4 / (2 : ℝ) ^ s + 1 / 2 := by
      rw [hflat]
      linarith [htri, hAerr, h3r]
    linarith
  -- ## assemble
  constructor
  · rw [hAsh, hBsh]; exact hinD
  · have hnormid : (2 : ℝ) ^ p * ‖HvdH.fxC p (A, B) - ((c : ℝ) : ℂ)‖
        = |(A : ℝ) - (2 : ℝ) ^ p * c| := by
      have hnorm : ‖(2 : ℂ) ^ p‖ = (2 : ℝ) ^ p := by rw [norm_pow, Complex.norm_ofNat]
      have h2c : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ (by norm_num)
      have hX : HvdH.fxC p (A, B) - ((c : ℝ) : ℂ)
          = (((((A : ℝ) - (2 : ℝ) ^ p * c : ℝ)) : ℂ)) / (2 : ℂ) ^ p := by
        rw [HvdH.fxC, hB0]
        push_cast
        field_simp [h2c]
        ring
      have hnormY : ‖(((A : ℝ) - (2 : ℝ) ^ p * c : ℝ) : ℂ)‖
          = |(A : ℝ) - (2 : ℝ) ^ p * c| := RCLike.norm_ofReal _
      rw [hX, norm_div, hnorm, hnormY, mul_comm, div_mul_cancel₀ _ (ne_of_gt hp_pos)]
    rw [hAsh, hBsh, hnormid]
    exact hfinal

end Work.Fx
