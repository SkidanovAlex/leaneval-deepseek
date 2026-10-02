import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.Table4.Engine8
import Submission.Work.ZeroFreeTables.Table4.FarNear
import Submission.Work.ZeroFreeTables.P9.prim.invSqSum_bound
import Submission.Work.ZeroFreeTables.P9.prim.parityBound
import Submission.Work.ZeroFreeTables.P9.invNearSum_eq_tsum
import Submission.Work.ZeroFreeTables.HB95h2.keptEngine

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.HB95h2

/-- Arithmetic bookkeeping for the kept `P₃` master bound: given the scaled far-zero bound
`J ≤ C (L+2)` and the threshold condition on the `λ₁`-bound, the two error terms
`(A/L)²(k₂J + Ct) + (2/3)(A/L)³(k₃J + Ct)` are at most `A·e`. -/
private lemma error_bound_kept {A Amax k2 k3 C Ct J L e : ℝ}
    (hA : 0 ≤ A) (hAle : A ≤ Amax) (hAmax : 0 ≤ Amax) (hk2 : 0 ≤ k2) (hk3 : 0 ≤ k3)
    (hC : 0 ≤ C) (hCt : 0 ≤ Ct) (hJ : J ≤ C * (L + 2))
    (hL2 : 2 ≤ L) (hLpos : 0 < L)
    (hK : 2 * Amax ^ 2 * (k2 * C + Ct) + (4 / 3) * Amax ^ 3 * (k3 * C + Ct) ≤ A * e * L) :
    A ^ 2 / L ^ 2 * (k2 * J + Ct) + (2 / 3) * (A ^ 3 / L ^ 3) * (k3 * J + Ct) ≤ A * e := by
  have hB2 : k2 * J + Ct ≤ (k2 * C + Ct) * (L + 2) := by
    have h1 : k2 * J ≤ k2 * (C * (L + 2)) := mul_le_mul_of_nonneg_left hJ hk2
    have h2 : Ct ≤ Ct * (L + 2) := le_mul_of_one_le_right hCt (by linarith)
    have heq : (k2 * C + Ct) * (L + 2) = k2 * (C * (L + 2)) + Ct * (L + 2) := by ring
    linarith [h1, h2, heq.le, heq.ge]
  have hB3 : k3 * J + Ct ≤ (k3 * C + Ct) * (L + 2) := by
    have h1 : k3 * J ≤ k3 * (C * (L + 2)) := mul_le_mul_of_nonneg_left hJ hk3
    have h2 : Ct ≤ Ct * (L + 2) := le_mul_of_one_le_right hCt (by linarith)
    have heq : (k3 * C + Ct) * (L + 2) = k3 * (C * (L + 2)) + Ct * (L + 2) := by ring
    linarith [h1, h2, heq.le, heq.ge]
  have hC2nn : 0 ≤ k2 * C + Ct := by positivity
  have hC3nn : 0 ≤ k3 * C + Ct := by positivity
  have hC2L2nn : 0 ≤ (k2 * C + Ct) * (L + 2) := mul_nonneg hC2nn (by linarith)
  have hC3L2nn : 0 ≤ (k3 * C + Ct) * (L + 2) := mul_nonneg hC3nn (by linarith)
  have hnum : A ^ 2 ≤ Amax ^ 2 := pow_le_pow_left₀ hA hAle 2
  have hnum3 : A ^ 3 ≤ Amax ^ 3 := pow_le_pow_left₀ hA hAle 3
  have hL2' : (L + 2) / L ^ 2 ≤ 2 / L := by
    rw [div_le_div_iff₀ (pow_pos hLpos 2) hLpos]; nlinarith only [hL2, hLpos]
  have hL3' : (L + 2) / L ^ 3 ≤ 2 / L := by
    rw [div_le_div_iff₀ (pow_pos hLpos 3) hLpos]; nlinarith only [hL2, sq_nonneg L, hLpos]
  have herr2 : A ^ 2 / L ^ 2 * (k2 * J + Ct) ≤ Amax ^ 2 * (k2 * C + Ct) * (2 / L) := by
    calc A ^ 2 / L ^ 2 * (k2 * J + Ct)
        ≤ A ^ 2 / L ^ 2 * ((k2 * C + Ct) * (L + 2)) :=
          mul_le_mul_of_nonneg_left hB2 (by positivity)
      _ ≤ Amax ^ 2 / L ^ 2 * ((k2 * C + Ct) * (L + 2)) := by
          apply mul_le_mul_of_nonneg_right _ hC2L2nn
          exact div_le_div_of_nonneg_right hnum (pow_pos hLpos 2).le
      _ = Amax ^ 2 * (k2 * C + Ct) * ((L + 2) / L ^ 2) := by ring
      _ ≤ Amax ^ 2 * (k2 * C + Ct) * (2 / L) :=
          mul_le_mul_of_nonneg_left hL2' (mul_nonneg (pow_nonneg hAmax 2) hC2nn)
  have herr3 : (2 / 3) * (A ^ 3 / L ^ 3) * (k3 * J + Ct)
      ≤ (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * (2 / L) := by
    calc (2 / 3) * (A ^ 3 / L ^ 3) * (k3 * J + Ct)
        ≤ (2 / 3) * (A ^ 3 / L ^ 3) * ((k3 * C + Ct) * (L + 2)) :=
          mul_le_mul_of_nonneg_left hB3 (by positivity)
      _ ≤ (2 / 3) * (Amax ^ 3 / L ^ 3) * ((k3 * C + Ct) * (L + 2)) := by
          apply mul_le_mul_of_nonneg_right _ hC3L2nn
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hnum3 (pow_pos hLpos 3).le) (by norm_num)
      _ = (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * ((L + 2) / L ^ 3) := by ring
      _ ≤ (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * (2 / L) :=
          mul_le_mul_of_nonneg_left hL3'
            (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hAmax 3)) hC3nn)
  have hsum : Amax ^ 2 * (k2 * C + Ct) * (2 / L) + (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * (2 / L)
      = (2 * Amax ^ 2 * (k2 * C + Ct) + (4 / 3) * Amax ^ 3 * (k3 * C + Ct)) / L := by ring
  have hKL : (2 * Amax ^ 2 * (k2 * C + Ct) + (4 / 3) * Amax ^ 3 * (k3 * C + Ct)) / L ≤ A * e := by
    rw [div_le_iff₀ hLpos]; linarith [hK]
  linarith [herr2, herr3, hsum, hKL]

/-- Summability of the parity ("trivial zero") series `∑_n (s + par + 2n)^{-(k+1)}`. -/
private lemma summable_parity_shift (par : ℕ) {s : ℂ} (hs : 1 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun n : ℕ => (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
  have hs' : 1 < (s + (par : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (par : ℝ) := Nat.cast_nonneg par
    linarith
  have h := (Work.ZeroFreeTables.P9.tsum_inv_add_two_shift k hk (s := s + (par : ℂ)) hs').1
  refine h.congr (fun n => ?_)
  have hh : (s + (par : ℂ)) + ((2 * n : ℕ) : ℂ) = s + ((par + 2 * n : ℕ) : ℂ) := by
    push_cast; ring
  rw [hh]

/-- The `keptInd`-weighted summand is summable whenever the `nearInd`-weighted one is: the
two differ only on the finite set `S`. -/
private lemma kept_summable_of_near {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} {δ : ℝ} {S : Finset ℂ} {f : ℂ → ℝ}
    (hnear : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * Work.ZeroFreeTables.P9.nearInd s δ u * f u)) :
    Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * Work.ZeroFreeTables.Table4.keptInd S s δ u * f u) := by
  classical
  have hsupp : (Function.support (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * (Work.ZeroFreeTables.Table4.keptInd S s δ u - Work.ZeroFreeTables.P9.nearInd s δ u) * f u))
      ⊆ (S : Set ℂ) := by
    intro u hu
    by_contra hnot
    have hk : Work.ZeroFreeTables.Table4.keptInd S s δ u
        = Work.ZeroFreeTables.P9.nearInd s δ u := by
      by_cases hn : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      · rw [Work.ZeroFreeTables.Table4.keptInd_eq_ite, if_pos (Or.inr hn),
            Work.ZeroFreeTables.P9.nearInd_eq_ite, if_pos hn]
      · rw [Work.ZeroFreeTables.Table4.keptInd_eq_ite, if_neg (fun h => h.elim hnot hn),
            Work.ZeroFreeTables.P9.nearInd_eq_ite, if_neg hn]
    exact (Function.mem_support.mp hu) (by rw [hk, sub_self]; ring)
  have hfin : (Function.support (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * (Work.ZeroFreeTables.Table4.keptInd S s δ u
        - Work.ZeroFreeTables.P9.nearInd s δ u) * f u)).Finite :=
    (S.finite_toSet).subset hsupp
  have hdiff : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * (Work.ZeroFreeTables.Table4.keptInd S s δ u
        - Work.ZeroFreeTables.P9.nearInd s δ u) * f u) :=
    summable_of_ne_finset_zero (s := hfin.toFinset) (fun u hu => by
      by_contra hne
      exact hu (by rw [Set.Finite.mem_toFinset, Function.mem_support]; exact hne))
  have hkey : (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
        * Work.ZeroFreeTables.Table4.keptInd S s δ u * f u)
      = (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
          * Work.ZeroFreeTables.P9.nearInd s δ u * f u)
        + (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
          * (Work.ZeroFreeTables.Table4.keptInd S s δ u
            - Work.ZeroFreeTables.P9.nearInd s δ u) * f u) := by
    funext u; simp only [Pi.add_apply]; ring
  rw [hkey]
  exact hnear.add hdiff

/-- Summability of the `keptInd`-weighted `k`-th power summand, by comparison against the
(unweighted) complex power summand. -/
private lemma keptPow_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    {δ : ℝ} (S : Finset ℂ) (k : ℕ)
    (hsum : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ (k + 1))) :
    Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * Work.ZeroFreeTables.Table4.keptInd S s δ u * ((1 / (s - u)) ^ (k + 1)).re) := by
  have hnorm : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * ‖(1 / (s - u)) ^ (k + 1)‖) :=
    hsum.norm.congr (fun u => by rw [norm_mul, Complex.norm_natCast])
  refine Summable.of_norm_bounded hnorm (fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ)),
      abs_of_nonneg (Work.ZeroFreeTables.Table4.keptInd_nonneg S s δ u)]
  calc (Work.LinnikContract.zeroMult χ u : ℝ) * Work.ZeroFreeTables.Table4.keptInd S s δ u
        * |((1 / (s - u)) ^ (k + 1)).re|
      ≤ (Work.LinnikContract.zeroMult χ u : ℝ) * 1 * ‖(1 / (s - u)) ^ (k + 1)‖ := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (Work.ZeroFreeTables.Table4.keptInd_le_one S s δ u)
            (by positivity)
        · exact Complex.abs_re_le_norm _
        · positivity
        · positivity
    _ = (Work.LinnikContract.zeroMult χ u : ℝ) * ‖(1 / (s - u)) ^ (k + 1)‖ := by ring

set_option maxHeartbeats 1000000 in
theorem masterP3kept {a δ c e M : ℝ} (ha : 0 < a) (hδ0 : 0 < δ) (hδ1 : δ < 1) (he : 0 < e) :
    ∃ L₀ : ℝ, ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hprim : χ.IsPrimitive) {L lam₁ : ℝ}, L₀ ≤ L → Real.log (N : ℝ) ≤ L → 0 ≤ lam₁ →
      lam₁ ≤ M → Work.ZeroFreeTables.LogDerivHyp χ δ L c →
      ∀ (S : Finset ℂ) (s : ℂ), s.re = 1 + a / L → |s.im| ≤ 4 →
        Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
          ≤ - Work.ZeroFreeTables.Table4.keptP3Sum N L χ s a lam₁ δ S + (a + lam₁) * (c + e)
            + ((a + lam₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
                * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re))) := by
  obtain ⟨C, hCpos, hC⟩ := Work.ZeroFreeTables.P9.prim.invSqSum_uniform_le
  obtain ⟨Ct, hCtpos, hCt⟩ := Work.ZeroFreeTables.P9.paritySum_re_bound
  have hC2pos : 0 < (1 + 4 / δ ^ 2) * C + Ct := by
    have : (0 : ℝ) ≤ 4 / δ ^ 2 := div_nonneg (by norm_num) (sq_nonneg δ)
    positivity
  have hC3pos : 0 < (2 / δ) * (1 + 4 / δ ^ 2) * C + Ct := by
    have h1 : (0 : ℝ) ≤ 1 + 4 / δ ^ 2 := by
      have : (0 : ℝ) ≤ 4 / δ ^ 2 := div_nonneg (by norm_num) (sq_nonneg δ)
      linarith
    have : 0 < (2 / δ) := by positivity
    positivity
  set K : ℝ := 2 * (a + M) ^ 2 * ((1 + 4 / δ ^ 2) * C + Ct)
    + (4 / 3) * (a + M) ^ 3 * ((2 / δ) * (1 + 4 / δ ^ 2) * C + Ct) with hKdef
  refine ⟨max 4 (max (a + 2) (max (2 * a / δ)
    (max (Real.exp (max a a⁻¹) + 4) (K / (a * e))))), ?_⟩
  intro N _ χ hχ hprim L lam₁ hL hlogN hlam₁ hM hyp S s hsre hsim
  have hX : max (a + 2) (max (2 * a / δ) (max (Real.exp (max a a⁻¹) + 4) (K / (a * e)))) ≤ L :=
    le_trans (le_max_right 4 _) hL
  have hY : max (2 * a / δ) (max (Real.exp (max a a⁻¹) + 4) (K / (a * e))) ≤ L :=
    le_trans (le_max_right (a + 2) _) hX
  have hZ : max (Real.exp (max a a⁻¹) + 4) (K / (a * e)) ≤ L :=
    le_trans (le_max_right (2 * a / δ) _) hY
  have hLge4 : 4 ≤ L := le_trans (le_max_left 4 _) hL
  have hLge2 : 2 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hLge1 : 1 ≤ L := by linarith
  have ha2 : a + 2 ≤ L := le_trans (le_max_left (a + 2) _) hX
  have haL : a ≤ L := by linarith
  have h2aδ : 2 * a ≤ δ * L := by
    have h := le_trans (le_max_left (2 * a / δ) _) hY
    rw [div_le_iff₀ hδ0] at h
    linarith
  have hlogL_ge : max a a⁻¹ ≤ Real.log L := by
    have hexp : Real.exp (max a a⁻¹) ≤ L := by linarith [le_trans (le_max_left _ _) hZ]
    have h := Real.log_le_log (Real.exp_pos (max a a⁻¹)) hexp
    rwa [Real.log_exp] at h
  have hmpos : 0 < max a a⁻¹ := lt_of_lt_of_le ha (le_max_left a a⁻¹)
  have hlogL_pos : 0 < Real.log L := lt_of_lt_of_le hmpos hlogL_ge
  have hKe : K ≤ a * e * L := by
    have h := le_trans (le_max_right _ _) hZ
    rw [div_le_iff₀ (mul_pos ha he)] at h
    linarith
  -- facts at `s`
  have hsre_gt : 1 < s.re := by rw [hsre]; linarith [div_pos ha hLpos]
  have hsδ : s.re ≤ 1 + δ / 2 := by
    rw [hsre]
    have h : a / L ≤ δ / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith
  have hα : 0 ≤ a + lam₁ := by linarith
  obtain ⟨par, hpar0, hpar1⟩ : ∃ par : ℕ, (χ.Even → par = 0) ∧ (χ.Odd → par = 1) := by
    rcases χ.even_or_odd with hE | hO
    · exact ⟨0, fun _ => rfl, fun hO => absurd hO hE.not_odd⟩
    · exact ⟨1, fun hE => absurd hE hO.not_even, fun _ => rfl⟩
  have hpar_le : par ≤ 1 := by
    rcases χ.even_or_odd with hE | hO
    · rw [hpar0 hE]; exact zero_le_one
    · rw [hpar1 hO]
  obtain ⟨hsum2, _⟩ :=
    Work.ZeroFreeTables.P9.lDiffExplicit_gen χ hχ hprim 1 (by norm_num) par hpar0 hpar1 hsre_gt
  obtain ⟨hsum3, _⟩ :=
    Work.ZeroFreeTables.P9.lDiffExplicit_gen χ hχ hprim 2 (by norm_num) par hpar0 hpar1 hsre_gt
  -- the `(L'/L)` slot
  have hbridge := Work.ZeroFreeTables.P9.invNearSum_eq_tsum χ hχ hprim
    (by linarith [hsim] : |s.im| ≤ 10) hδ0 (le_of_lt hδ1)
  have hs1 : 1 + 1 / (L * Real.log L) ≤ s.re := by
    rw [hsre]
    have h1 : 1 ≤ a * Real.log L := by
      have h := mul_le_mul_of_nonneg_left (le_trans (le_max_right a a⁻¹) hlogL_ge) (le_of_lt ha)
      rwa [mul_inv_cancel₀ (ne_of_gt ha)] at h
    have : 1 / (L * Real.log L) ≤ a / L := by
      rw [div_le_div_iff₀ (by positivity : 0 < L * Real.log L) hLpos]
      nlinarith only [mul_le_mul_of_nonneg_left h1 hLpos.le]
    linarith
  have hs2 : s.re ≤ 1 + Real.log L / L := by
    rw [hsre]
    have h2 : a ≤ Real.log L := le_trans (le_max_left a a⁻¹) hlogL_ge
    have : a / L ≤ Real.log L / L := by
      rw [div_le_div_iff₀ hLpos hLpos]; nlinarith only [mul_le_mul_of_nonneg_right h2 hLpos.le]
    linarith
  have hs3 : |s.im| ≤ L := le_trans hsim hLge4
  have hlog := hyp s hs1 hs2 hs3
  have hlog' : (-logDeriv (DirichletCharacter.LFunction χ) s).re
      + Work.ZeroFreeTables.P9.nearInvSum N χ s δ ≤ c * L := by
    rw [← hbridge]; exact hlog
  -- far zeros and parity
  have hnorm_s : ‖s‖ ≤ L + 5 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos (lt_trans zero_lt_one hsre_gt)] at h
    calc ‖s‖ ≤ s.re + |s.im| := h
      _ = 1 + a / L + |s.im| := by rw [hsre]
      _ ≤ 1 + a / L + 4 := by linarith [hsim]
      _ ≤ L + 5 := by
          have hdiv : a / L ≤ a := by rw [div_le_iff₀ hLpos]; nlinarith only [mul_le_mul_of_nonneg_left hLge1 ha.le]
          linarith
  have hJ : Work.ZeroFreeTables.P9.invSqSum N χ s ≤ C * (L + 2) :=
    hC χ hχ hprim hLge1 hlogN hnorm_s
  obtain ⟨hT2abs, hT3abs⟩ := hCt s (by linarith) par hpar_le
  have hp2 : Summable (fun n : ℕ => (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2) := by
    simpa using summable_parity_shift par hsre_gt 1 (by norm_num)
  have hp3 : Summable (fun n : ℕ => (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3) := by
    simpa using summable_parity_shift par hsre_gt 2 (by norm_num)
  have hT2abs' : |∑' n : ℕ, ((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2).re| ≤ Ct := by
    rw [← Complex.re_tsum hp2]; exact hT2abs
  have hT3abs' : |∑' n : ℕ, ((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3).re| ≤ Ct := by
    rw [← Complex.re_tsum hp3]; exact hT3abs
  have hAle : a + lam₁ ≤ a + M := by linarith
  have hAe_pos : 0 < (a + lam₁) * e := mul_pos (by linarith) he
  have hKL : K ≤ (a + lam₁) * e * L := by
    have h1 : a * e ≤ (a + lam₁) * e := by nlinarith only [mul_nonneg hlam₁ he.le]
    have h2 : a * e * L ≤ (a + lam₁) * e * L := mul_le_mul_of_nonneg_right h1 hLpos.le
    linarith [hKe, h2]
  have herr : (a + lam₁) ^ 2 / L ^ 2
        * ((1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
      + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3)
        * ((2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
      ≤ (a + lam₁) * e :=
    error_bound_kept (A := a + lam₁) (Amax := a + M) (k2 := 1 + 4 / δ ^ 2)
      (k3 := (2 / δ) * (1 + 4 / δ ^ 2)) (C := C) (Ct := Ct)
      (J := Work.ZeroFreeTables.P9.invSqSum N χ s) (L := L) (e := e)
      hα hAle (by linarith) (by positivity) (by positivity) hCpos.le hCtpos.le hJ hLge2 hLpos
      (by rw [← hKdef]; exact hKL)
  -- summability and the kept engine
  have h1 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * Work.ZeroFreeTables.Table4.keptInd S s δ u * ((1 / (s - u)).re)) :=
    kept_summable_of_near χ
      (Work.ZeroFreeTables.Table4.nearInvSum_summable χ hχ hprim hδ0 (le_of_lt hδ1))
  have h2 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * Work.ZeroFreeTables.Table4.keptInd S s δ u * ((1 / (s - u)) ^ 2).re) :=
    keptPow_summable χ S 1 hsum2
  have h3 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * Work.ZeroFreeTables.Table4.keptInd S s δ u * ((1 / (s - u)) ^ 3).re) :=
    keptPow_summable χ S 2 hsum3
  have hkeep := keptEngine χ hχ hprim ha hlam₁ hδ0 hδ1 hLpos hsre_gt hsδ hlog'
    par hpar0 hpar1 hT2abs' hT3abs' h1 h2 h3 hsum2 hsum3
  have hcomb : Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      ≤ - Work.ZeroFreeTables.Table4.keptP3Sum N L χ s a lam₁ δ S + (a + lam₁) * c
        + ((a + lam₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
            * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re)))
        + (a + lam₁) * e := by
    linarith [hkeep, herr]
  linarith [hcomb]

end Work.ZeroFreeTables.HB95h2
