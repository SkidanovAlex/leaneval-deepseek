import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.even_step_defs
import Submission.Work.BW.bprod_circle
import Submission.Work.BW.est14
import Submission.Work.BW.est15
import Submission.Work.BW.extrap_core
import Submission.Work.BW.num_T
import Submission.Work.BW.num_xi
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.even_step_arith
import Submission.Work.BW.est1415_gap
import Submission.Work.BW.card_filter_odd_Icc
import Submission.Work.BW.even_step_U
import Submission.Work.BW.even_step_V
import Submission.Work.BW.even_step_W
import Submission.Work.BW.even_step_Y

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! ### The even step of the Kummer descent (BW pp. 57–58)

`extrap_even_step` extends BW's (29) from odd `s` to all `s` in the ball, at descent level `J+1`,
by the §19 Cauchy/Blaschke extrapolation run with the *lacunary* Blaschke product `B'(·;X)` whose
zeros are the known odd integers (`X = 2S'`, `S' = ⌊2S^{(J)}⌋`, `R = 7.2S'`, `η = 1/3`, `κ = 1`,
`δ = 5S'`).  The four estimates `(16)`, `(21)`, `(23')`, `(25)` at level `J+1` are `even_step_U`,
`even_step_V`, `even_step_W`, `even_step_Y`; the two numerical conditions of `extrap_core` are
`even_step_arith`; `est1415_gap` plus `(14)`, `(15)` provide the bridge `g(s) ≠ 0 ⟹ f(s) ≠ 0`. -/

namespace Work.BW

open Complex MvPolynomial

/-- `z ↦ ptC ℓ z n` is entire. -/
lemma hes_differentiable_ptC {r : ℕ} (ℓ : Fin r → ℂ) (n : Fin (r + 1)) :
    Differentiable ℂ (fun z : ℂ => ptC ℓ z n) := by
  induction n using Fin.cases with
  | zero => simpa [ptC] using (differentiable_id : Differentiable ℂ fun z : ℂ => z)
  | succ j =>
      have h : (fun z : ℂ => ptC ℓ z j.succ) = fun z : ℂ => Complex.exp (z * ℓ j) := by
        funext z
        simp only [ptC, Fin.cons_succ]
      rw [h]
      exact (differentiable_id.mul (differentiable_const (ℓ j))).cexp

/-- `z ↦ P(z, e^{zℓ₁}, …)` is entire. -/
lemma hes_differentiable_fAt {r : ℕ} (ℓ : Fin r → ℂ) (P : MvPolynomial (Fin (r + 1)) ℂ) :
    Differentiable ℂ (fun z : ℂ => fAt ℓ P z) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa [fAt] using (differentiable_const a)
  | add p q hp hq =>
      have h : (fun z : ℂ => fAt ℓ (p + q) z)
          = (fun z : ℂ => fAt ℓ p z) + fun z : ℂ => fAt ℓ q z := by
        funext z
        simp only [fAt, MvPolynomial.eval_add, Pi.add_apply]
      rw [h]
      exact hp.add hq
  | mul_X p m hp =>
      have h : (fun z : ℂ => fAt ℓ (p * MvPolynomial.X m) z)
          = fun z : ℂ => fAt ℓ p z * ptC ℓ z m := by
        funext z
        simp only [fAt, MvPolynomial.eval_mul, MvPolynomial.eval_X]
      rw [h]
      exact hp.mul (hes_differentiable_ptC ℓ m)

/-- `0 < ξ = 1 − 0.536/r` for `r ≥ 2`. -/
lemma hes_pxi_pos {r : ℕ} (hr : 2 ≤ r) : 0 < pxi r := by
  have hr' : (0 : ℝ) < (r : ℝ) := by positivity
  have h2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  rw [pxi, sub_pos, div_lt_one hr']
  linarith

/-- `ξ ≤ 1`. -/
lemma hes_pxi_le_one (r : ℕ) : pxi r ≤ 1 := by
  rw [pxi, sub_le_iff_le_add]
  have : (0 : ℝ) ≤ 0.536 / r := by positivity
  linarith

/-- `ξ^m ≤ 1`. -/
lemma hes_pxi_pow_le_one {r : ℕ} (hr : 2 ≤ r) (m : ℕ) : pxi r ^ m ≤ 1 :=
  pow_le_one₀ (le_of_lt (hes_pxi_pos hr)) (hes_pxi_le_one r)

/-- `ξ^{rJ} ≤ 1`. -/
lemma hes_pxi_rJ_le_one {r : ℕ} (hr : 2 ≤ r) (J : ℕ) : pxi r ^ (r * J) ≤ 1 :=
  hes_pxi_pow_le_one hr (r * J)

/-- `1 ≤ ξ^{-rJ}` (so `S^{(J)} ≥ S`). -/
lemma hes_one_le_xi_zpow {r : ℕ} (hr : 2 ≤ r) (J : ℕ) :
    1 ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) := by
  have h : pxi r ^ (-((r * J : ℕ) : ℤ)) = (pxi r ^ (r * J))⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [h]
  exact (one_le_inv₀ (pow_pos (hes_pxi_pos hr) _)).mpr (hes_pxi_rJ_le_one hr J)

/-- `ξ^{-rJ}·2^{-J} = (2ξ^r)^{-J} ≤ 1`. -/
lemma hes_xi_zpow_two_zpow_le_one {r : ℕ} (hr : 2 ≤ r) (J : ℕ) :
    pxi r ^ (-((r * J : ℕ) : ℤ)) * (2 : ℝ) ^ (-(J : ℤ)) ≤ 1 := by
  have h1 : 1 ≤ 2 * pxi r ^ r := le_trans (by norm_num) (num_xi hr).2.2.2.2
  have key : ((2 * pxi r ^ r) ^ J)⁻¹
      = pxi r ^ (-((r * J : ℕ) : ℤ)) * (2 : ℝ) ^ (-(J : ℤ)) := by
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, mul_pow, mul_inv_rev]
    rw [← pow_mul]
  rw [← key]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)

/-- `a ≤ 4S^{(J)}` implies `a / 2^{J+1} ≤ 2S` (the range hypothesis of `(16)`/`(21)` at level
`J+1`). -/
lemma hes_div_two_pow_le_of_le_four {r : ℕ} (hr : 2 ≤ r) {J : ℕ} {a S : ℝ}
    (ha : a ≤ 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)) (hS : 0 ≤ S) :
    a / 2 ^ (J + 1) ≤ 2 * S := by
  have hp : (0 : ℝ) < 2 ^ (J + 1) := by positivity
  refine le_trans (div_le_div_of_nonneg_right ha hp.le) ?_
  have h4 : 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) / 2 ^ (J + 1)
      = 2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (2 : ℝ) ^ (-(J : ℤ))) * S := by
    have h2 : (2 : ℝ) ^ (J + 1) = 2 ^ J * 2 := by ring
    have h3 : (2 : ℝ) ^ (-(J : ℤ)) = ((2 : ℝ) ^ J)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [h2, h3]
    ring_nf
  rw [h4]
  have hdec : pxi r ^ (-((r * J : ℕ) : ℤ)) * (2 : ℝ) ^ (-(J : ℤ)) ≤ 1 :=
    hes_xi_zpow_two_zpow_le_one hr J
  nlinarith [hdec, hS]

/-- `S' = ⌊2S^{(J)}⌋ ≥ 1216` for `S ≥ 608`. -/
lemma hes_evSP_ge {r : ℕ} (hr : 2 ≤ r) (J : ℕ) {S : ℝ} (hS : 608 ≤ S) : 1216 ≤ evSP r J S := by
  have hS0 : (0 : ℝ) ≤ S := by linarith
  have hzpow : (0 : ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    exact inv_nonneg.mpr (pow_nonneg (hes_pxi_pos hr).le _)
  rw [evSP]
  refine (Nat.le_floor_iff (by positivity)).mpr ?_
  have h1 : (1 : ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) := hes_one_le_xi_zpow hr J
  have h3 : (608 : ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) * S := by
    have := mul_le_mul h1 hS (by norm_num : (0 : ℝ) ≤ 608)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) h1)
    simpa using this
  calc (1216 : ℝ) = 2 * 608 := by norm_num
    _ ≤ 2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) := mul_le_mul_of_nonneg_left h3 (by norm_num)

/-- `4S^{(J)} ≤ X + 2` with `X = 2⌊2S^{(J)}⌋`. -/
lemma hes_four_SJ_le_X_add_two {r J : ℕ} {S : ℝ} :
    4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) ≤ (evX r J S : ℝ) + 2 := by
  rw [evX, evSP]
  have h := Nat.lt_floor_add_one (2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S))
  have h2 : ((2 * ⌊2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)⌋₊ : ℕ) : ℝ)
      = 2 * (⌊2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)⌋₊ : ℝ) := by push_cast; ring
  rw [h2]
  linarith

end Work.BW

namespace Work.BW

theorem extrap_even_step {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J + 1 ≤ pI r (dK K))
    (hnd : ∃ j, (2 : ℝ) ^ J ≤ (pDj r (dK K) σ j : ℝ))
    (μ' : Fin r → ℕ)
    (hodd : VanSet (fun i => lamP φ α v L i) (QJ φ b k L ι v σ p (J + 1) μ')
      (oddBallZ (4 * SJ K r b v J)) 1 (pxi r ^ r * TJ K σ J)) :
    VanSet (fun i => lamP φ α v L i) (QJ φ b k L ι v σ p (J + 1) μ')
      (ballZ (4 * SJ K r b v J)) 1 (pxi r ^ (r + 1) * TJ K σ J) := by
  classical
  have hr : 2 ≤ r := H.hr
  have hdK : 1 ≤ dK K := Module.finrank_pos
  have h19 : 19 ≤ acH K b v := (acH_lower H).1
  have hσge : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hnum := num_T hr hdK h19 σ hσge
  have hS608 : (608 : ℝ) ≤ acS K r b v := by
    change (608 : ℝ) ≤ (pS r (dK K) (acH K b v) : ℝ)
    exact_mod_cast hnum.2.2.2
  have hSpos : 0 < acS K r b v := by linarith
  have hSnn : 0 ≤ acS K r b v := hSpos.le
  have hDnn : 0 ≤ acD K σ := by
    change 0 ≤ pD r (dK K) σ
    rw [pD]
    have hlog : 0 < Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
      apply Real.log_pos
      have h2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      have h3 : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hdK
      nlinarith
    have hprod : 0 < ∏ j, σ j :=
      Finset.prod_pos (fun j _ => lt_of_lt_of_le (div_pos one_pos (by exact_mod_cast hdK)) (hσge j))
    have h1 : 0 ≤ 2 * (r : ℝ) ^ r * (32 * (dK K : ℝ)) ^ (r + 1) :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg r) r))
        (pow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg (dK K))) (r + 1))
    exact mul_nonneg (mul_nonneg h1 hlog.le) hprod.le
  have hTJ0 : 0 ≤ TJ K σ J := by
    rw [TJ]
    exact mul_nonneg (pow_nonneg (hes_pxi_pos hr).le _) (Nat.cast_nonneg _)
  have hTJleT : TJ K σ J ≤ acT K σ := by
    have hp : pxi r ^ (r * J) ≤ 1 := hes_pxi_rJ_le_one hr J
    have hle : 0 ≤ pxi r ^ (r * J) := pow_nonneg (hes_pxi_pos hr).le _
    change pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) ≤ (pT r (dK K) σ : ℝ)
    have hTnn : (0 : ℝ) ≤ (pT r (dK K) σ : ℝ) := Nat.cast_nonneg _
    exact mul_le_of_le_one_left hTnn hp
  have hTleT : pxi r * TJ K σ J ≤ acT K σ :=
    le_trans (mul_le_of_le_one_left hTJ0 (hes_pxi_le_one r)) hTJleT
  have harith := even_step_arith (r := r) (d := dK K) (h := acH K b v) (σ := σ)
    hr hdK h19 hσge J hJ hnd
  intro s hs t0 t ht
  have hgoal : fAt (fun i => lamP φ α v L i) (QJ φ b k L ι v σ p (J + 1) μ' t0 t)
      ((s : ℂ) / (1 : ℂ)) = 0 := by
    by_cases hso : Odd s
    · -- ### odd points: this is BW (29) itself
      have hs' : s ∈ oddBallZ (4 * SJ K r b v J) := ⟨hso, hs⟩
      have hpow : pxi r ^ (r + 1) ≤ pxi r ^ r := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg (hes_pxi_pos hr).le r) (hes_pxi_le_one r)
      have hle : pxi r ^ (r + 1) * TJ K σ J ≤ pxi r ^ r * TJ K σ J :=
        mul_le_mul_of_nonneg_right hpow hTJ0
      simpa using hodd s hs' t0 t (le_trans ht hle)
    · -- ### even points: the Cauchy/Blaschke extrapolation
      by_contra hne
      have hne' : acg φ α b k L ι v σ p (J + 1) μ' t0 t (s : ℂ) ≠ 0 := by
        simpa [acg] using hne
      set Zfin : Finset ℤ :=
        (Finset.Icc (-(((evX r J (acS K r b v)) : ℕ) : ℤ)) ((evX r J (acS K r b v)) : ℕ)).filter Odd
        with hZfin
      -- the four estimates
      have hU : ∀ z : ℂ, ‖z‖ = evR r J (acS K r b v) →
          ‖acf φ α b k L ι v σ p (J + 1) μ' t0 t z‖ ≤
            ‖acf φ α b k L ι v σ p (J + 1) μ' t0 t (s : ℂ)‖
              * Real.exp (evU r (dK K) (acH K b v) σ J) :=
        even_step_U H J hJ μ' s hs t0 t ht hne'
      have hV : ∀ l ∈ Zfin, ∀ m ≤ evTp r J (acT K σ),
          ‖taylorC (acf φ α b k L ι v σ p (J + 1) μ' t0 t) m (l : ℂ)‖ ≤
            ‖acf φ α b k L ι v σ p (J + 1) μ' t0 t (s : ℂ)‖
              * Real.exp (evV r (dK K) (acH K b v) σ J) := by
        rw [hZfin]
        exact even_step_V H J hJ μ' hodd s hs t0 t ht hne'
      have hW : ‖∏ l ∈ Zfin, bfac (evR r J (acS K r b v)) l (s : ℂ) ^
            (evTp r J (acT K σ) + 1)‖
          ≤ Real.exp (-(evW r (dK K) (acH K b v) σ J)) := by
        rw [hZfin]
        exact even_step_W H J s hs
      have hY : ∀ l ∈ Zfin, ∀ z : ℂ, ‖z - (l : ℂ)‖ = 1 / 3 →
          ‖∏ l' ∈ Zfin, bfac (evR r J (acS K r b v)) l' (s : ℂ) ^ (evTp r J (acT K σ) + 1)‖
            ≤ ‖∏ l' ∈ Zfin, bfac (evR r J (acS K r b v)) l' z ^ (evTp r J (acT K σ) + 1)‖
              * Real.exp (evY r (dK K) (acH K b v) σ J) := by
        rw [hZfin]
        exact even_step_Y H J s hs
      -- ### the `(14)`/`(15)` bridge: `g(s) ≠ 0` gives `f(s) ≠ 0`
      have htr : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ pxi r * TJ K σ J := by
        have hp1 : pxi r ^ (r + 1) ≤ pxi r := by
          rw [pow_succ]
          exact mul_le_of_le_one_left (hes_pxi_pos hr).le (hes_pxi_pow_le_one hr r)
        exact le_trans ht (mul_le_mul_of_nonneg_right hp1 hTJ0)
      have hs16 : ((|s| : ℤ) : ℝ) / 2 ^ (J + 1) ≤ 4 * acS K r b v := by
        have ha : ((|s| : ℤ) : ℝ) ≤ 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * acS K r b v) := by
          simpa [SJ, ballZ] using hs
        have h2 := hes_div_two_pow_le_of_le_four hr ha hSnn
        linarith
      have hfne : acf φ α b k L ι v σ p (J + 1) μ' t0 t (s : ℂ) ≠ 0 := by
        intro hf0
        have hgap := est1415_gap H (J + 1) hJ (pxi r * TJ K σ J) hTleT s hs16
        have h14 := est14 H (J + 1) hJ μ' (pxi r * TJ K σ J) hTleT t0 t htr ((s : ℂ))
        have h15 := est15 H (J + 1) μ' (pxi r * TJ K σ J) hTleT t0 t htr s hne'
        rw [hf0, zero_sub, norm_neg] at h14
        have hmono := le_trans h15 h14
        have hnorm : ‖(s : ℂ)‖ = ((|s| : ℤ) : ℝ) := by
          rw [Complex.norm_intCast, Int.cast_abs]
        rw [hnorm] at hmono
        exact absurd (Real.exp_le_exp.mp hmono) (not_le.mpr hgap)
      -- ### the geometry of the parameters
      have hSPge : 1216 ≤ evSP r J (acS K r b v) := hes_evSP_ge hr J hS608
      have hSPgeR : (1216 : ℝ) ≤ (evSP r J (acS K r b v) : ℝ) := by exact_mod_cast hSPge
      have hSP1 : (1 : ℝ) ≤ (evSP r J (acS K r b v) : ℝ) := by linarith
      have hX2 : (evX r J (acS K r b v) : ℝ) = 2 * (evSP r J (acS K r b v) : ℝ) := by
        rw [evX]; push_cast; ring
      have hR7 : evR r J (acS K r b v) = 7.2 * (evSP r J (acS K r b v) : ℝ) := rfl
      have hdel5 : evdelta r J (acS K r b v) = 5 * (evSP r J (acS K r b v) : ℝ) := rfl
      have h4SJ : 4 * SJ K r b v J ≤ (evX r J (acS K r b v) : ℝ) + 2 := hes_four_SJ_le_X_add_two
      have hszX : ((|s| : ℤ) : ℝ) ≤ (evX r J (acS K r b v) : ℝ) + 2 := le_trans hs h4SJ
      have hZ : ∀ l ∈ Zfin, ((|l| : ℤ) : ℝ) + 1 / 3 < evR r J (acS K r b v) := by
        intro l hl
        have hlX : ((|l| : ℤ) : ℝ) ≤ (evX r J (acS K r b v) : ℝ) :=
          abs_le_of_mem_Icc (Finset.mem_of_mem_filter l hl)
        have hlX2 : ((|l| : ℤ) : ℝ) ≤ 2 * (evSP r J (acS K r b v) : ℝ) := by
          rw [hX2] at hlX
          exact hlX
        rw [hR7]
        linarith
      have hsR : ‖(s : ℂ)‖ + evdelta r J (acS K r b v) ≤ evR r J (acS K r b v) := by
        have hnorm : ‖(s : ℂ)‖ = ((|s| : ℤ) : ℝ) := by
          rw [Complex.norm_intCast, Int.cast_abs]
        have hszX' : ((|s| : ℤ) : ℝ) ≤ 2 * (evSP r J (acS K r b v) : ℝ) + 2 := by
          rw [← hX2]; exact hszX
        rw [hnorm, hdel5, hR7]
        linarith
      have hdelta : 0 < evdelta r J (acS K r b v) := by
        rw [hdel5]; linarith
      have hsZ : ∀ l ∈ Zfin, (1 : ℝ) ≤ ‖(s : ℂ) - (l : ℂ)‖ := by
        intro l hl
        have hlo : Odd l := (Finset.mem_filter.mp hl).2
        have hne' : s ≠ l := by intro h; subst h; exact hso hlo
        have hone : (1 : ℤ) ≤ |s - l| := by
          have h0 : (0 : ℤ) < |s - l| := abs_pos.mpr (sub_ne_zero.mpr hne')
          omega
        have hnorm : ‖(s : ℂ) - (l : ℂ)‖ = ((|s - l| : ℤ) : ℝ) := by
          have h1 : (s : ℂ) - (l : ℂ) = ((s - l : ℤ) : ℂ) := (Int.cast_sub s l).symm
          rw [h1, Complex.norm_intCast, Int.cast_abs]
        rw [hnorm]
        exact_mod_cast hone
      -- ### the numerical conditions
      have h1 : Real.log (evR r J (acS K r b v) / evdelta r J (acS K r b v))
          + evU r (dK K) (acH K b v) σ J - evW r (dK K) (acH K b v) σ J < -Real.log 2 := harith.1
      have h2 : Real.log ((Zfin.card : ℝ) * ((evTp r J (acT K σ) : ℝ) + 1))
          + Real.log ((1 / 3) / (1 - 1 / 3)) + evV r (dK K) (acH K b v) σ J
          + evY r (dK K) (acH K b v) σ J < -Real.log 2 := by
        have hc : Zfin.card = evX r J (acS K r b v) := by
          rw [hZfin]
          exact card_filter_odd_Icc (by rw [evX]; exact even_two_mul _)
        rw [hc]
        simpa only [Nat.cast_add, Nat.cast_one] using harith.2
      -- ### the extrapolation
      have hcore : acf φ α b k L ι v σ p (J + 1) μ' t0 t (s : ℂ) = 0 :=
        extrap_core (fun z => acf φ α b k L ι v σ p (J + 1) μ' t0 t z)
          (hes_differentiable_fAt (ellM φ α b k v L) (QJ φ b k L ι v σ p (J + 1) μ' t0 t))
          (evR r J (acS K r b v)) (1 / 3) 1 (evdelta r J (acS K r b v))
          (by norm_num) (by norm_num) Zfin hZ (evTp r J (acT K σ)) (s : ℂ)
          hdelta hsR (by norm_num) hsZ
          (evU r (dK K) (acH K b v) σ J) (evV r (dK K) (acH K b v) σ J)
          (evW r (dK K) (acH K b v) σ J) (evY r (dK K) (acH K b v) σ J)
          hU hV hW hY h1 h2
      exact hfne hcore
  simpa using hgoal

end Work.BW
