import Mathlib
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.ph_ge_nineteen
import Submission.Work.BW.sysRow_height_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `log (n!) ≤ n log n` for `n : ℕ` (from `n! ≤ n^n`). -/
private lemma log_factorial_le (n : ℕ) :
    Real.log ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  have h1 : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  have hpos : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  calc Real.log ((n.factorial : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log hpos h1
    _ = (n : ℝ) * Real.log (n : ℝ) := Real.log_pow n n

/-- `log d ≤ X(n,d)` for `n ≥ 2`, `d ≥ 1`, where
`X(n,d) = log C(n,d) − n log d − log(n+d)`.

Indeed `(d)^{n+1}·(n+d) ≤ d^{n+1}·d·(n+1) ≤ C(n,d)`, because `n + d ≤ d(n+1)` and
`(n+1) ≤ 18·(n+1)!·n^{n+1}·32^{n+2}·log(2nd)`; taking logarithms and using
`log(d^{n+1}(n+d)) = (n+1) log d + log(n+d)` gives the claim. -/
private lemma log_le_Xbw (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    Real.log (d : ℝ) ≤ Xbw n d := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hfacle : (n : ℝ) + 1 ≤ (((n + 1).factorial : ℕ) : ℝ) := by
    have h := Nat.self_le_factorial (n + 1)
    exact_mod_cast h
  have hn1p : (1 : ℝ) ≤ (n : ℝ) ^ (n + 1) := one_le_pow₀ hn1
  have h32 : (1 : ℝ) ≤ (32 : ℝ) ^ (n + 2) := one_le_pow₀ (by norm_num)
  have hNpos : (0 : ℝ) < 2 * (n : ℝ) * (d : ℝ) := by nlinarith
  have hN4 : (4 : ℝ) ≤ 2 * (n : ℝ) * (d : ℝ) := by nlinarith
  have hlogN1 : (1 : ℝ) ≤ Real.log (2 * (n : ℝ) * (d : ℝ)) :=
    (Real.le_log_iff_exp_le hNpos).mpr (by linarith [Real.exp_one_lt_three])
  have h12 : (1:ℝ) * ((n:ℝ)+1) ≤ 18 * (((n+1).factorial : ℕ) : ℝ) :=
    mul_le_mul (by norm_num) hfacle (by linarith) (by norm_num)
  have h123 : (1:ℝ) * ((n:ℝ)+1) * 1 ≤ 18 * (((n+1).factorial:ℕ) : ℝ) * (n:ℝ)^(n+1) :=
    mul_le_mul h12 hn1p (by norm_num) (by positivity)
  have h1234 : (1:ℝ) * ((n:ℝ)+1) * 1 * 1
      ≤ 18 * (((n+1).factorial:ℕ):ℝ) * (n:ℝ)^(n+1) * (32:ℝ)^(n+2) :=
    mul_le_mul h123 h32 (by norm_num) (by positivity)
  have hA : (n:ℝ) + 1 ≤ 18 * (((n+1).factorial:ℕ):ℝ) * (n:ℝ)^(n+1) * (32:ℝ)^(n+2)
      * Real.log (2 * (n:ℝ) * (d:ℝ)) := by
    have h12345 := mul_le_mul h1234 hlogN1 (by norm_num) (by positivity)
    calc (n:ℝ)+1 = (1:ℝ) * ((n:ℝ)+1) * 1 * 1 * 1 := by ring
      _ ≤ _ := h12345
  have hCeq : BakerWustholz.C n d = 18 * (((n+1).factorial:ℕ):ℝ) * (n:ℝ)^(n+1) * (32:ℝ)^(n+2)
      * (d:ℝ)^(n+2) * Real.log (2*(n:ℝ)*(d:ℝ)) := by
    rw [BakerWustholz.C, mul_pow]
    ring
  have hCle : ((n:ℝ)+1) * (d:ℝ)^(n+2) ≤ BakerWustholz.C n d := by
    have h1 := mul_le_mul_of_nonneg_right hA (by positivity : (0:ℝ) ≤ (d:ℝ)^(n+2))
    rw [hCeq]
    linarith [h1]
  have hnd : (n : ℝ) + (d : ℝ) ≤ (d : ℝ) * ((n : ℝ) + 1) := by
    have h2 := mul_le_mul_of_nonneg_left hd1 hn0
    nlinarith [h2]
  have hprod : (d:ℝ)^(n+1) * ((n:ℝ)+(d:ℝ)) ≤ BakerWustholz.C n d := by
    have h1 : (d:ℝ)^(n+1) * ((n:ℝ)+(d:ℝ)) ≤ (d:ℝ)^(n+1) * ((d:ℝ)*((n:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hnd (by positivity)
    have h2 : (d:ℝ)^(n+1) * ((d:ℝ)*((n:ℝ)+1)) = ((n:ℝ)+1) * (d:ℝ)^(n+2) := by
      rw [pow_succ]
      ring
    linarith [h1, h2.le, h2.ge, hCle]
  rw [Xbw]
  have hlogmono := Real.log_le_log (by positivity : (0:ℝ) < (d:ℝ)^(n+1) * ((n:ℝ)+(d:ℝ))) hprod
  rw [Real.log_mul (by positivity : (d:ℝ)^(n+1) ≠ 0) (by positivity : (n:ℝ)+(d:ℝ) ≠ 0),
    Real.log_pow] at hlogmono
  push_cast at hlogmono ⊢
  linarith [hlogmono]

/-- **Slack estimate (constant form).**  Under the Baker–Wüstholz standing hypotheses and §11 basic
hypothesis, the §13 "slack" term `0.1·pS·pD` dominates `2·[K:ℚ]·log(([F:ℚ])!)`, where
`F = auxField α'`.

Ingredients: `hBH` gives `hmod(α'ⱼ, …) ≤ σⱼ`, and `Work.BW.one_div_finrank_le_hmod` (import
`BW/sysRow_height_bound`) gives `1/[K:ℚ] ≤ hmod`, so `σⱼ ≥ 1/[K:ℚ]` and `∏σⱼ ≥ (1/[K:ℚ])^r`.
Multiplying out `pS = 16 r d h`, `pD = 2r^r(32d)^{r+1}log(2rd)·∏σ` (`d = [K:ℚ]`) with `0.1` gives
`0.1·pS·pD ≥ 3.2·r·h·r^r·32^{r+1}·d²·log(2rd)`.  Use `h ≥ 19` (`Work.BW.ph_ge_nineteen`, import
`BW/ph_ge_nineteen`), `r ≥ 2`, `[F:ℚ] ≤ d` (`Module.finrank_mul_finrank`) and
`log(d!) ≤ d·log d ≤ d·log(2rd)`; the margin is a factor `≫ 10⁵`. -/
theorem slack_ge_log_factorial {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ) (hst : Standing φ α b k c)
    (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ)
    (hBH : BH φ α b v c r L α' σ) (hr : 2 ≤ r) :
    2 * (Module.finrank ℚ K : ℝ) * Real.log (((Module.finrank ℚ ↥(auxField α')).factorial : ℝ))
      ≤ 0.1 * ((pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℝ) *
          pD r (Module.finrank ℚ K) σ) := by
  set dK : ℕ := Module.finrank ℚ K with hdK
  set dF : ℕ := Module.finrank ℚ ↥(auxField α') with hdF
  set hN : ℕ := ph (hL b dK) v with hhN
  set dR : ℝ := (dK : ℝ) with hdR
  set dFR : ℝ := (dF : ℝ) with hdFR
  set hR : ℝ := (hN : ℝ) with hhR
  set rR : ℝ := (r : ℝ) with hrR
  have hdK1 : 1 ≤ dK := by rw [hdK]; exact Module.finrank_pos (R := ℚ) (M := K)
  have hdRpos : (0:ℝ) < dR := by
    rw [hdR]; exact_mod_cast (show (0:ℕ) < dK from by omega)
  have hdRnn : (0:ℝ) ≤ dR := le_of_lt hdRpos
  have hdR1 : (1:ℝ) ≤ dR := by rw [hdR]; exact_mod_cast hdK1
  have hrR2 : (2:ℝ) ≤ rR := by rw [hrR]; exact_mod_cast hr
  have hrR1 : (1:ℝ) ≤ rR := by linarith
  have hrRnn : (0:ℝ) ≤ rR := by linarith
  have h19 : (19:ℝ) ≤ hR := by
    have h := ph_ge_nineteen φ α b k c v hst
    rw [hhR, hhN]
    exact_mod_cast h
  have hRpos : (0:ℝ) < hR := by linarith
  have hRnn : (0:ℝ) ≤ hR := le_of_lt hRpos
  have hdF1 : 1 ≤ dF := by rw [hdF]; exact Module.finrank_pos
  have hdF_le : dF ≤ dK := by
    have h := Module.finrank_mul_finrank ℚ ↥(auxField α') K
    have h1 : 0 < Module.finrank ↥(auxField α') K := Module.finrank_pos
    have h2 : Module.finrank ℚ ↥(auxField α')
        ≤ Module.finrank ℚ ↥(auxField α') * Module.finrank ↥(auxField α') K :=
      Nat.le_mul_of_pos_right _ h1
    rw [hdF, hdK]
    exact le_trans h2 h.le
  have hdR_le : dFR ≤ dR := by
    rw [hdFR, hdR]; exact_mod_cast hdF_le
  have hdFRnn : (0:ℝ) ≤ dFR := by rw [hdFR]; exact Nat.cast_nonneg dF
  -- `log d ≤ h + 1` via `X(n,d) ≤ h'(L)` and `h'(L) ≤ h + 1`
  have hlogd : Real.log dR ≤ hR + 1 := by
    have hX : Xbw n dK ≤ hL b dK := by rw [hdK]; exact hst.2.2.2.2.2.2.1
    have hlog : Real.log (dK:ℝ) ≤ Xbw n dK := log_le_Xbw n dK hst.1 hdK1
    have hLb : hL b dK ≤ hR + 1 := by
      have hlt : hL b dK + (v:ℝ) * Real.log 2 < (hN : ℝ) + 1 := by
        rw [hhN]; exact Nat.lt_floor_add_one _
      have hv : (0:ℝ) ≤ (v:ℝ) * Real.log 2 :=
        mul_nonneg (Nat.cast_nonneg v) (Real.log_nonneg (by norm_num))
      rw [hhR]
      linarith
    rw [hdR]
    linarith
  have hlogfact : Real.log ((dF.factorial : ℕ) : ℝ) ≤ dR * (hR + 1) := by
    have h1 : Real.log ((dF.factorial : ℕ) : ℝ) ≤ dFR * Real.log dFR := log_factorial_le dF
    have h2 : Real.log dFR ≤ Real.log dR := by
      rw [hdFR, hdR]
      exact Real.log_le_log (by exact_mod_cast (by omega : (0:ℕ) < dF))
        (by exact_mod_cast hdF_le)
    have h3 : dFR * Real.log dFR ≤ dR * Real.log dR := by
      have ha : dFR * Real.log dFR ≤ dFR * Real.log dR := mul_le_mul_of_nonneg_left h2 hdFRnn
      have hb : dFR * Real.log dR ≤ dR * Real.log dR :=
        mul_le_mul_of_nonneg_right hdR_le (Real.log_nonneg hdR1)
      linarith
    have h4 : dR * Real.log dR ≤ dR * (hR + 1) := mul_le_mul_of_nonneg_left hlogd hdRnn
    linarith
  have hpS : ((pS r dK hN : ℕ) : ℝ) = 16 * rR * dR * hR := by
    rw [show pS r dK hN = 16 * r * dK * hN from rfl]
    push_cast
    rw [← hrR, ← hdR, ← hhR]
  have hpDeq : pD r dK σ = 2 * rR^r * (32 * dR)^(r+1) * Real.log (2 * rR * dR) * ∏ j, σ j := by
    rw [pD]
  have hsig : ∀ j : Fin r, (1:ℝ)/dR ≤ σ j := by
    intro j
    have h1 : (1:ℝ) / (Module.finrank ℚ K : ℝ) ≤ hmod (α' j) (lamP φ α v L j) :=
      one_div_finrank_le_hmod (α' j) (lamP φ α v L j)
    have h2 : hmod (α' j) (lamP φ α v L j) ≤ σ j := hBH.2.2.2.2.2.1 j
    have h3 : (1:ℝ) / (Module.finrank ℚ K : ℝ) = (1:ℝ)/dR := by rw [hdR, hdK]
    rw [h3] at h1
    linarith
  have hP : ((1:ℝ)/dR)^r ≤ ∏ j, σ j := by
    have hone : (∏ _j : Fin r, ((1:ℝ)/dR)) ≤ ∏ j, σ j :=
      Finset.prod_le_prod₀ (fun j _ => div_nonneg zero_le_one hdRnn) (fun j _ => hsig j)
    have : (∏ _j : Fin r, ((1:ℝ)/dR)) = ((1:ℝ)/dR)^r := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rwa [this] at hone
  -- lower bound for `D = pD r d σ`
  have hDlow : 2 * rR^r * (32 * dR)^(r+1) * 1 * ((1:ℝ)/dR)^r
      ≤ 2 * rR^r * (32 * dR)^(r+1) * Real.log (2 * rR * dR) * ∏ j, σ j := by
    have hAnn : (0:ℝ) ≤ 2 * rR^r * (32 * dR)^(r+1) :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hrRnn r))
        (pow_nonneg (mul_nonneg (by norm_num) hdRnn) (r+1))
    have hAnn1 : (0:ℝ) ≤ 2 * rR^r * (32 * dR)^(r+1) * 1 := mul_nonneg hAnn (by norm_num)
    have h2rd : (4:ℝ) ≤ 2 * rR * dR := by nlinarith
    have hL1 : (1:ℝ) ≤ Real.log (2 * rR * dR) :=
      (Real.le_log_iff_exp_le (by linarith : (0:ℝ) < 2 * rR * dR)).mpr
        (by linarith [Real.exp_one_lt_three])
    have hAL : 2 * rR^r * (32 * dR)^(r+1) * 1
        ≤ 2 * rR^r * (32 * dR)^(r+1) * Real.log (2 * rR * dR) :=
      mul_le_mul_of_nonneg_left hL1 hAnn
    have hP0nn : (0:ℝ) ≤ ((1:ℝ)/dR)^r := pow_nonneg (div_nonneg zero_le_one hdRnn) r
    have hALnn : (0:ℝ) ≤ 2 * rR^r * (32 * dR)^(r+1) * Real.log (2 * rR * dR) :=
      le_trans hAnn1 hAL
    exact mul_le_mul hAL hP hP0nn hALnn
  have hdivpow : (32 * dR)^(r+1) * ((1:ℝ)/dR)^r = 32^(r+1) * dR := by
    have hxr : dR^r ≠ 0 := pow_ne_zero _ (ne_of_gt hdRpos)
    have h1 : dR^(r+1) * (dR^r)⁻¹ = dR := by
      rw [← div_eq_mul_inv, div_eq_iff hxr, pow_succ']
    rw [mul_pow, one_div_pow, one_div, mul_assoc, h1]
  have hfour : (4:ℝ) ≤ 3.2 * rR * rR^r * 32^(r+1) := by
    have hpow2 : rR^2 ≤ rR^r := pow_le_pow_right₀ hrR1 hr
    have h4r : (4:ℝ) ≤ rR^r := by
      have h44 : (4:ℝ) ≤ rR^2 := by nlinarith
      linarith
    have h32le : (32:ℝ)^3 ≤ 32^(r+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have s1 : (3.2:ℝ) * 2 ≤ 3.2 * rR := mul_le_mul_of_nonneg_left hrR2 (by norm_num)
    have s2 : (3.2:ℝ) * 2 * 4 ≤ 3.2 * rR * rR^r :=
      mul_le_mul s1 h4r (by norm_num) (mul_nonneg (by norm_num) hrRnn)
    have s3 : (3.2:ℝ) * 2 * 4 * (32:ℝ)^3 ≤ 3.2 * rR * rR^r * 32^(r+1) :=
      mul_le_mul s2 h32le (by norm_num)
        (mul_nonneg (mul_nonneg (by norm_num) hrRnn) (pow_nonneg hrRnn r))
    have hc : (4:ℝ) ≤ 3.2 * 2 * 4 * (32:ℝ)^3 := by norm_num
    linarith
  have hnum : 2 * (hR + 1) ≤ 3.2 * rR * rR^r * 32^(r+1) * hR := by
    have h4h : 2 * (hR + 1) ≤ 4 * hR := by linarith
    have hh := mul_le_mul_of_nonneg_right hfour hRnn
    linarith
  have hmain : 2 * dR * dR * (hR + 1) ≤ 0.1 * (↑(pS r dK hN) * pD r dK σ) := by
    rw [hpS, hpDeq]
    have h16 : (0:ℝ) ≤ 16 * rR * dR * hR :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrRnn) hdRnn) hRnn
    have hstep : 0.1 * (16 * rR * dR * hR * (2 * rR^r * (32 * dR)^(r+1) * 1 * ((1:ℝ)/dR)^r))
        ≤ 0.1 * (16 * rR * dR * hR *
            (2 * rR^r * (32 * dR)^(r+1) * Real.log (2 * rR * dR) * ∏ j, σ j)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDlow h16) (by norm_num)
    have hkey : (2 * rR^r * (32 * dR)^(r+1) * 1 * ((1:ℝ)/dR)^r)
        = 2 * rR^r * 32^(r+1) * dR := by
      have h1 : (2 * rR^r * (32 * dR)^(r+1) * 1 * ((1:ℝ)/dR)^r)
          = (2 * rR^r * (32 * dR)^(r+1)) * ((1:ℝ)/dR)^r := by ring
      rw [h1, mul_assoc, hdivpow]
      ring
    have h2 : 0.1 * (16 * rR * dR * hR * (2 * rR^r * (32 * dR)^(r+1) * 1 * ((1:ℝ)/dR)^r))
        = 3.2 * rR * rR^r * 32^(r+1) * (dR * dR) * hR := by
      rw [hkey]; ring
    have h3 : 2 * dR * dR * (hR + 1) ≤ 3.2 * rR * rR^r * 32^(r+1) * (dR * dR) * hR := by
      have hm := mul_le_mul_of_nonneg_right hnum (mul_nonneg hdRnn hdRnn)
      linarith [hm]
    linarith [hstep, h2, h3]
  calc 2 * dR * Real.log ((dF.factorial : ℕ) : ℝ)
      ≤ 2 * dR * (dR * (hR + 1)) :=
        mul_le_mul_of_nonneg_left hlogfact (by linarith : (0:ℝ) ≤ 2 * dR)
    _ = 2 * dR * dR * (hR + 1) := by ring
    _ ≤ 0.1 * (↑(pS r dK hN) * pD r dK σ) := hmain

end Work.BW
