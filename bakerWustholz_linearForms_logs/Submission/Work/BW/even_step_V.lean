import Mathlib
import Submission.Work.BW.even_step_defs
import Submission.Work.BW.num_xi
import Submission.Work.BW.num_T
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.est21

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-! ### The `V`-hypothesis of `extrap_core` in the even step (BW pp. 57-58)

This node is the `hV` block of `extrap_even_step`: `(21)` at level `J+1` applied to
`f = f^{(J+1)}_{μ'}(·;t)`, with `Tp = T' = ⌊(1−ξ)ξ^rT^{(J)}⌋`, `Tpp = ξ^{r+1}T^{(J)}`,
`T* = ξ^rT^{(J)}`, `Tp + Tpp ≤ T*` and the vanishing hypothesis `hodd` at the odd point `l`;
the exponent of the conclusion is bounded by `evV` using `‖l‖ ≤ X` and `|s| ≤ 4S^{(J)}`. -/

/-! #### Bookkeeping used by the proof -/

/-- `d = [K:ℚ] ≥ 1`. -/
lemma even_step_V_one_le_dK (K : Type*) [Field K] [NumberField K] : 1 ≤ dK K := by
  have h := Module.finrank_pos (R := ℚ) (M := K)
  show 1 ≤ Module.finrank ℚ K
  omega

/-- `0 ≤ D`: `D = 2 r^r (32d)^{r+1} log(2rd) ∏σ_j` with `r ≥ 2`, `d ≥ 1`, `log(2rd) > 0` and
`σ_j ≥ 1/d > 0`. -/
lemma even_step_V_pD_nonneg {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) {σ : Fin r → ℝ}
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) : 0 ≤ pD r d σ := by
  have hlog : (0 : ℝ) < Real.log (2 * r * d) := log_2rd_pos hr hd
  have hprod : (0 : ℝ) < ∏ j, σ j :=
    Finset.prod_pos (fun j _ => lt_of_lt_of_le (by positivity) (hσ j))
  rw [pD]
  positivity

/-- `ξ` is nonnegative (`r ≥ 2`). -/
lemma even_step_V_xi_nonneg {r : ℕ} (hr : 2 ≤ r) : (0 : ℝ) ≤ pxi r := (pxi_pos hr).le

/-- `a ≤ 4S^{(J)}` implies `a / 2^{J+1} ≤ 2^r S`: the range hypothesis of `(21)` at level `J+1`
in the form used here.  The descent factor is absorbed by `ξ^{-rJ}2^{-J} = (2ξ^r)^{-J} ≤ 1`
(`num_xi`: `ξ^{-r} ≤ 1.87 ≤ 2`). -/
lemma even_step_V_div_two_pow_le {r : ℕ} (hr : 2 ≤ r) {J : ℕ} {a S : ℝ}
    (ha : a ≤ 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)) (hS : 0 ≤ S) :
    a / 2 ^ (J + 1) ≤ 2 ^ r * S := by
  have hpos : (0 : ℝ) < 2 ^ (J + 1) := by positivity
  have hxi0 : (0 : ℝ) ≤ pxi r := (pxi_pos hr).le
  have hxir : pxi r ^ (-(r : ℤ)) ≤ 1.87 := (num_xi hr).1
  have hpow : pxi r ^ (-((r * J : ℕ) : ℤ)) ≤ (2 : ℝ) ^ J := by
    have key : pxi r ^ (-((r * J : ℕ) : ℤ)) = (pxi r ^ (-(r : ℤ))) ^ J := by
      rw [show -((r * J : ℕ) : ℤ) = -(r : ℤ) * (J : ℤ) by push_cast; ring]
      rw [zpow_mul, zpow_natCast]
    rw [key]
    calc (pxi r ^ (-(r : ℤ))) ^ J ≤ 1.87 ^ J :=
          pow_le_pow_left₀ (zpow_nonneg hxi0 _) hxir J
      _ ≤ (2 : ℝ) ^ J := pow_le_pow_left₀ (by norm_num) (by norm_num) J
  have h2r : (2 : ℝ) ≤ 2 ^ r := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ r)
    simpa using h
  rw [div_le_iff₀ hpos]
  have h1 : 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) ≤ 4 * ((2 : ℝ) ^ J * S) := by
    have h := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4)
    calc 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)
        = (4 * pxi r ^ (-((r * J : ℕ) : ℤ))) * S := by ring
      _ ≤ (4 * (2 : ℝ) ^ J) * S := mul_le_mul_of_nonneg_right h hS
      _ = 4 * ((2 : ℝ) ^ J * S) := by ring
  have h2 : 4 * ((2 : ℝ) ^ J * S) ≤ 2 ^ r * S * ((2 : ℝ) ^ J * 2) := by
    have h4 : (4 : ℝ) ≤ 2 ^ r * 2 := by linarith
    calc 4 * ((2 : ℝ) ^ J * S) ≤ (2 ^ r * 2) * ((2 : ℝ) ^ J * S) :=
          mul_le_mul_of_nonneg_right h4 (mul_nonneg (by positivity) hS)
      _ = 2 ^ r * S * ((2 : ℝ) ^ J * 2) := by ring
  have hstep : 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) ≤ 2 ^ r * S * 2 ^ (J + 1) := by
    rw [pow_succ]
    linarith [h1, h2]
  linarith [ha, hstep]

/-- The `(21)`-exponent at level `J+1` of the even step — `Tst = T* = ξ^rT^{(J)}`, `sz` for
`|s| ≤ 4S^{(J)}`, `‖l‖ ≤ X = evX`, `kumJ` for the Kummer term — is at most `evV r d h σ J`. -/
lemma even_step_V_exp_le_evV {r : ℕ} (hr : 2 ≤ r) {d h J : ℕ} {σ : Fin r → ℝ} {l : ℂ} {sz : ℝ}
    (hl : ‖l‖ ≤ (evX r J (pS r d h : ℝ) : ℝ))
    (hsz : sz ≤ 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) (hD : 0 ≤ pD r d σ) :
    (d : ℝ) * (h : ℝ) * (pxi r ^ r * (pxi r ^ (r * J) * (pT r d σ : ℝ)))
      + (1.133 - 9 * (2 : ℝ) ^ r) * (pS r d h : ℝ) * pD r d σ
      + 1.01 * ((‖l‖ + sz) / 2 ^ (J + 1)) * pD r d σ
      + 0.044 * ((J + 1 : ℕ) : ℝ) / Real.log (2 * r * d) * (pS r d h : ℝ) * pD r d σ
      ≤ evV r d h σ J := by
  rw [evV]
  have hle : ‖l‖ + sz ≤ (evX r J (pS r d h : ℝ) : ℝ)
      + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)) := by linarith
  have h2 : (0 : ℝ) < 2 ^ (J + 1) := by positivity
  have hdiv : (‖l‖ + sz) / 2 ^ (J + 1) ≤ ((evX r J (pS r d h : ℝ) : ℝ)
      + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / 2 ^ (J + 1) :=
    div_le_div_of_nonneg_right hle h2.le
  have hmul : 1.01 * ((‖l‖ + sz) / 2 ^ (J + 1)) * pD r d σ
      ≤ 1.01 * (((evX r J (pS r d h : ℝ) : ℝ)
          + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / 2 ^ (J + 1)) * pD r d σ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv (by norm_num)) hD
  linarith [hmul]

/-- The `V`-hypothesis of `extrap_core` in the even step: `(21)` at level `J+1` applied to
`f = f^{(J+1)}_{μ'}(·;t)`, with `Tp = T' = ⌊(1−ξ)ξ^rT^{(J)}⌋`, `Tpp = ξ^{r+1}T^{(J)}`,
`T* = ξ^rT^{(J)}`, `Tp + Tpp ≤ T*` and the vanishing hypothesis `hodd` at the odd point `l`; the
conclusion's exponent is bounded by `evV` using `‖l‖ ≤ X`, `|s| ≤ 4S^{(J)}`. -/
theorem even_step_V {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J + 1 ≤ pI r (dK K)) (μ' : Fin r → ℕ)
    (hodd : VanSet (fun i => lamP φ α v L i) (QJ φ b k L ι v σ p (J + 1) μ')
      (oddBallZ (4 * SJ K r b v J)) 1 (pxi r ^ r * TJ K σ J))
    (s : ℤ) (hs : ((|s| : ℤ) : ℝ) ≤ 4 * SJ K r b v J) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ pxi r ^ (r + 1) * TJ K σ J)
    (hne : acg φ α b k L ι v σ p (J + 1) μ' t0 t (s : ℂ) ≠ 0) :
    ∀ l ∈ (Finset.Icc (-(((evX r J (acS K r b v)) : ℕ) : ℤ)) ((evX r J (acS K r b v)) : ℕ)).filter Odd,
      ∀ m ≤ evTp r J (acT K σ),
        ‖taylorC (acf φ α b k L ι v σ p (J + 1) μ' t0 t) m (l : ℂ)‖ ≤
          ‖acf φ α b k L ι v σ p (J + 1) μ' t0 t (s : ℂ)‖
            * Real.exp (evV r (dK K) (acH K b v) σ J) := by
  classical
  intro l hl m hm
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := even_step_V_one_le_dK K
  have hD : 0 ≤ pD r (dK K) σ := even_step_V_pD_nonneg hr hd (fun j => sigma_ge H j)
  have hSnn : (0 : ℝ) ≤ acS K r b v := by simp only [acS, pS]; positivity
  have hTnn : (0 : ℝ) ≤ acT K σ := by simp only [acT]; positivity
  obtain ⟨hlI, hlo⟩ := Finset.mem_filter.mp hl
  -- `|l| ≤ X`: the range of the lacunary product
  have hlX : ((|l| : ℤ) : ℝ) ≤ (evX r J (acS K r b v) : ℝ) := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hlI
    have h3 : (|l| : ℤ) ≤ ((evX r J (acS K r b v) : ℕ) : ℤ) := abs_le.mpr ⟨h1, h2⟩
    have h4 : ((|l| : ℤ) : ℝ) ≤ (((evX r J (acS K r b v) : ℕ) : ℤ) : ℝ) := by
      exact_mod_cast h3
    simpa using h4
  -- `X = 2⌊2S^{(J)}⌋ ≤ 4S^{(J)}`
  have hXle : (evX r J (acS K r b v) : ℝ) ≤ 4 * SJ K r b v J := by
    have hsp : (evSP r J (acS K r b v) : ℝ)
        ≤ 2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * acS K r b v) := by
      rw [evSP]
      exact Nat.floor_le (mul_nonneg (by norm_num)
        (mul_nonneg (zpow_nonneg (even_step_V_xi_nonneg hr) _) hSnn))
    have hevX : (evX r J (acS K r b v) : ℝ) = 2 * (evSP r J (acS K r b v) : ℝ) := by
      rw [evX]; push_cast; ring
    rw [hevX, SJ]
    linarith [hsp]
  have hl4 : ((|l| : ℤ) : ℝ) ≤ 4 * SJ K r b v J := le_trans hlX hXle
  -- `ξ^rT^{(J)} ≤ T`: the order `T*` of `(21)` is available at level `J`
  have hTrT : pxi r ^ r * TJ K σ J ≤ acT K σ := by
    have hle : pxi r ^ r * pxi r ^ (r * J) ≤ 1 := by
      rw [← pow_add]
      exact pow_le_one₀ (even_step_V_xi_nonneg hr) (pxi_le_one r)
    rw [TJ]
    calc pxi r ^ r * (pxi r ^ (r * J) * acT K σ)
        = (pxi r ^ r * pxi r ^ (r * J)) * acT K σ := by ring
      _ ≤ 1 * acT K σ := mul_le_mul_of_nonneg_right hle hTnn
      _ = acT K σ := one_mul _
  -- `T' = ⌊(1−ξ)ξ^rT^{(J)}⌋` and `T' + ξ^{r+1}T^{(J)} ≤ ξ^rT^{(J)} = T*`
  have hfloor : ((evTp r J (acT K σ) : ℕ) : ℝ)
      ≤ (1 - pxi r) * pxi r ^ r * (pxi r ^ (r * J) * acT K σ) := by
    rw [evTp]
    refine Nat.floor_le ?_
    have h1 : (0 : ℝ) ≤ 1 - pxi r := by linarith [pxi_le_one r]
    have h2 : (0 : ℝ) ≤ pxi r ^ r := pow_nonneg (even_step_V_xi_nonneg hr) r
    have h3 : (0 : ℝ) ≤ pxi r ^ (r * J) := pow_nonneg (even_step_V_xi_nonneg hr) (r * J)
    exact mul_nonneg (mul_nonneg h1 h2) (mul_nonneg h3 hTnn)
  have hsum : ((evTp r J (acT K σ) : ℕ) : ℝ) + pxi r ^ (r + 1) * TJ K σ J
      ≤ pxi r ^ r * TJ K σ J := by
    rw [TJ]
    rw [pow_succ]
    nlinarith [hfloor]
  -- the vanishing hypothesis of `(21)` at the odd point `l` (this is `hodd`)
  have hvan : ∀ (t0' : ℕ) (t' : Fin (r - 1) → ℕ),
      ((t0' + ∑ m, t' m : ℕ) : ℝ) ≤ ((evTp r J (acT K σ) : ℕ) : ℝ)
        + pxi r ^ (r + 1) * TJ K σ J →
      acg φ α b k L ι v σ p (J + 1) μ' t0' t' (l : ℂ) = 0 := by
    intro t0' t' ht'
    have hmem : l ∈ oddBallZ (4 * SJ K r b v J) := ⟨hlo, hl4⟩
    have hres := hodd l hmem t0' t' (le_trans ht' hsum)
    simpa [acg] using hres
  -- the range hypothesis of `(21)` at the point `s`
  have hs2 : ((|s| : ℤ) : ℝ) / 2 ^ (J + 1) ≤ 2 ^ r * acS K r b v :=
    even_step_V_div_two_pow_le (r := r) (J := J) hr (a := ((|s| : ℤ) : ℝ))
      (by simpa only [SJ] using hs) hSnn
  have hm' : (m : ℝ) ≤ ((evTp r J (acT K σ) : ℕ) : ℝ) := by exact_mod_cast hm
  -- `(21)` at level `J+1`, with `T* = ξ^rT^{(J)}`, `Tp = T'`, `Tpp = ξ^{r+1}T^{(J)}`
  have h21 := est21 H (J + 1) hJ μ' (pxi r ^ r * TJ K σ J) hTrT
      ((evTp r J (acT K σ) : ℕ) : ℝ) (pxi r ^ (r + 1) * TJ K σ J) (by positivity)
      hsum (l : ℂ) hvan t0 t ht m hm' s hs2 hne
  refine le_trans h21 (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
  have hexp := even_step_V_exp_le_evV (r := r) hr (d := dK K) (h := acH K b v) (J := J)
    (σ := σ) (l := (l : ℂ)) (sz := ((|s| : ℤ) : ℝ)) ?_ ?_ hD
  · simpa only [TJ, kumJ, acS, acD, acT] using hexp
  · have h1 : ‖(l : ℂ)‖ = ((|l| : ℤ) : ℝ) := by
      rw [Complex.norm_intCast]
      simp
    rw [h1]
    exact hlX
  · simpa only [SJ, acS] using hs

end Work.BW
