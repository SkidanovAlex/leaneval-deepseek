/-
# `Work.ZeroFreeTables.HB95h2.imprimCorr`

The imprimitive correction of HB §9 (the `h2` variant, i.e. with the hypothesis `λ₁ ≤ M`
for a free parameter `M` instead of `λ₁ ≤ a`): for a non-principal Dirichlet character `χ` of
level `q`, a scale `L ≥ log q`, `0 ≤ λ₁ ≤ M`, and `s` on the line `Re s = 1 + a/L` with
`|Im s| ≤ 4`, the `P₃`-sum `Σ(s,χ)` at level `q` is at most the corresponding sum for the
primitive character `χ.primitiveCharacter` (of conductor `χ.conductor`, same scale `L`), plus
the error `(a+λ₁)·e`, uniformly in `q` and `χ ≠ 1` once `L` is large enough.

The analytic input is `Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff` (proved elsewhere in
the workspace): the change-of-level difference is bounded by

  `(12/L)·(α·S₁ + (α²/L)·S₂ + (α³/L²)·S₃)`,  `α = a + λ₁`,  `S_j = ∑_{p | q} (log p)^j / p`,

and `S_j = O((log log q)^{j+1})` uniformly (`Work.ZeroFreeTables.lam0w.pfLogLogBound`), with
`log log q ≤ log L` since `log q ≤ L`.  The only difference from the `λ₁ ≤ a` version is the
numeric core: with `λ₁ ≤ M` the coefficients are compared against `A := a + max M 0` instead
of `2a`, and `K·(1/L)·(α LL² + (α²/L) LL³ + (α³/L²) LL⁴) → 0` as `L → ∞` for any fixed `A`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
import Submission.Work.ZeroFreeTables.lam0w.imprimCorr4

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.HB95h2

open DirichletCharacter

/-! ## Polylogarithmic decay -/

private lemma tendsto_logpow_div (m j : ℕ) (hj : 1 ≤ j) :
    Filter.Tendsto (fun L : ℝ => (Real.log L) ^ m / L ^ j) Filter.atTop (nhds 0) := by
  have hm : Filter.Tendsto (fun L : ℝ => (Real.log L) ^ m / L) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 m one_ne_zero
  have hinv : Filter.Tendsto (fun L : ℝ => (1 : ℝ) / L) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have hpow : Filter.Tendsto (fun L : ℝ => ((1 : ℝ) / L) ^ (j - 1)) Filter.atTop
      (nhds ((0 : ℝ) ^ (j - 1))) := hinv.pow (j - 1)
  have hmul := hm.mul hpow
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with L hL
  rw [one_div_pow]
  rw [div_mul_div_comm, mul_one]
  congr 1
  rw [mul_comm L, ← pow_succ, Nat.sub_add_cancel hj]

private lemma tendsto_M2_div :
    Filter.Tendsto (fun L : ℝ => (Real.log L + 4) ^ 2 / L) Filter.atTop (nhds 0) := by
  have h2 := tendsto_logpow_div 2 1 le_rfl
  have h1 := tendsto_logpow_div 1 1 le_rfl
  have h0 := tendsto_logpow_div 0 1 le_rfl
  have h : Filter.Tendsto
      (fun L : ℝ => (Real.log L) ^ 2 / L + 8 * ((Real.log L) ^ 1 / L)
        + 16 * ((Real.log L) ^ 0 / L)) Filter.atTop (nhds 0) := by
    have h' := (h2.add (h1.const_mul 8)).add (h0.const_mul 16)
    simpa using h'
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with L hL
  rw [pow_one, pow_zero]
  field_simp
  ring

private lemma tendsto_M3_div :
    Filter.Tendsto (fun L : ℝ => (Real.log L + 4) ^ 3 / L ^ 2) Filter.atTop (nhds 0) := by
  have h3 := tendsto_logpow_div 3 2 (by norm_num)
  have h2 := tendsto_logpow_div 2 2 (by norm_num)
  have h1 := tendsto_logpow_div 1 2 (by norm_num)
  have h0 := tendsto_logpow_div 0 2 (by norm_num)
  have h : Filter.Tendsto
      (fun L : ℝ => (Real.log L) ^ 3 / L ^ 2 + 12 * ((Real.log L) ^ 2 / L ^ 2)
        + 48 * ((Real.log L) ^ 1 / L ^ 2) + 64 * ((Real.log L) ^ 0 / L ^ 2))
      Filter.atTop (nhds 0) := by
    have h' := ((h3.add (h2.const_mul 12)).add (h1.const_mul 48)).add (h0.const_mul 64)
    simpa using h'
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with L hL
  rw [pow_one, pow_zero]
  field_simp
  ring

private lemma tendsto_M4_div :
    Filter.Tendsto (fun L : ℝ => (Real.log L + 4) ^ 4 / L ^ 3) Filter.atTop (nhds 0) := by
  have h4 := tendsto_logpow_div 4 3 (by norm_num)
  have h3 := tendsto_logpow_div 3 3 (by norm_num)
  have h2 := tendsto_logpow_div 2 3 (by norm_num)
  have h1 := tendsto_logpow_div 1 3 (by norm_num)
  have h0 := tendsto_logpow_div 0 3 (by norm_num)
  have h : Filter.Tendsto
      (fun L : ℝ => (Real.log L) ^ 4 / L ^ 3 + 16 * ((Real.log L) ^ 3 / L ^ 3)
        + 96 * ((Real.log L) ^ 2 / L ^ 3) + 256 * ((Real.log L) ^ 1 / L ^ 3)
        + 256 * ((Real.log L) ^ 0 / L ^ 3)) Filter.atTop (nhds 0) := by
    have h' := (((h4.add (h3.const_mul 16)).add (h2.const_mul 96)).add
      (h1.const_mul 256)).add (h0.const_mul 256)
    simpa using h'
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with L hL
  rw [pow_one, pow_zero]
  field_simp
  ring

/-! ## The numeric core -/

/-- The numeric core of the imprimitive correction, with the coefficient bound `λ₁ ≤ M`:
for fixed `a`, `M`, `K`, `Cpf` and every `e > 0` there is `L₀` such that for all `L ≥ L₀`,
`0 ≤ LL ≤ log L + 4`, `0 ≤ λ₁ ≤ M` and `s_j ≤ Cpf·LL^(j+1)`,

  `K·(1/L)·(α·s₁ + (α²/L)·s₂ + (α³/L²)·s₃) ≤ α·e`,  `α = a + λ₁`. -/
theorem corr_numeric_M {K a M e : ℝ} (hK : 0 < K) (ha : 0 < a) (he : 0 < e) {Cpf : ℝ}
    (hCpf : 0 < Cpf) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ {L lam₁ LL s1 s2 s3 : ℝ},
      L₀ ≤ L → 0 ≤ LL → LL ≤ Real.log L + 4 → 0 ≤ lam₁ → lam₁ ≤ M →
      s1 ≤ Cpf * LL ^ 2 → s2 ≤ Cpf * LL ^ 3 → s3 ≤ Cpf * LL ^ 4 →
      K * ((1 / L) * ((a + lam₁) * s1 + ((a + lam₁) ^ 2 / L) * s2
        + ((a + lam₁) ^ 3 / L ^ 2) * s3)) ≤ (a + lam₁) * e := by
  set A : ℝ := a + max M 0 with hAdef
  have hApos : 0 < A := by rw [hAdef]; linarith [le_max_right M 0]
  let g : ℝ → ℝ := fun L =>
    (Real.log L + 4) ^ 2 / L + A * ((Real.log L + 4) ^ 3 / L ^ 2)
      + A ^ 2 * ((Real.log L + 4) ^ 4 / L ^ 3)
  have hg : Filter.Tendsto g Filter.atTop (nhds 0) := by
    have h' := (tendsto_M2_div.add (tendsto_M3_div.const_mul A)).add
      (tendsto_M4_div.const_mul (A ^ 2))
    simpa [g] using h'
  have hf : Filter.Tendsto (fun L : ℝ => K * Cpf * g L) Filter.atTop (nhds 0) := by
    simpa using hg.const_mul (K * Cpf)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hf e he
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro L lam₁ LL s1 s2 s3 hL hLL0 hLL hlam0 hlam_M hb1 hb2 hb3
  have hL1le : (1 : ℝ) ≤ L := le_trans (le_max_right N 1) hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1le
  have hXnn : 0 ≤ a + lam₁ := by linarith
  have hX2a : a + lam₁ ≤ A := by
    rw [hAdef]; linarith [le_max_left M 0, hlam_M]
  have hX2 : (a + lam₁) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hXnn hX2a 2
  have hLLpow2 : LL ^ 2 ≤ (Real.log L + 4) ^ 2 := pow_le_pow_left₀ hLL0 hLL 2
  have hLLpow3 : LL ^ 3 ≤ (Real.log L + 4) ^ 3 := pow_le_pow_left₀ hLL0 hLL 3
  have hLLpow4 : LL ^ 4 ≤ (Real.log L + 4) ^ 4 := pow_le_pow_left₀ hLL0 hLL 4
  have hstep3 : (1 / L) * (LL ^ 2 + ((a + lam₁) / L) * LL ^ 3 + ((a + lam₁) ^ 2 / L ^ 2) * LL ^ 4)
      ≤ (1 / L) * ((Real.log L + 4) ^ 2 + (A / L) * (Real.log L + 4) ^ 3
          + (A ^ 2 / L ^ 2) * (Real.log L + 4) ^ 4) := by
    apply mul_le_mul_of_nonneg_left _ (div_nonneg zero_le_one hLpos.le)
    have hm2 : ((a + lam₁) / L) * LL ^ 3 ≤ (A / L) * (Real.log L + 4) ^ 3 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hLpos.le
      exact mul_le_mul hX2a hLLpow3 (pow_nonneg hLL0 3) (by positivity)
    have hm3 : ((a + lam₁) ^ 2 / L ^ 2) * LL ^ 4 ≤ (A ^ 2 / L ^ 2) * (Real.log L + 4) ^ 4 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg L)
      exact mul_le_mul hX2 hLLpow4 (pow_nonneg hLL0 4) (by positivity)
    linarith
  have hs : (a + lam₁) * s1 + ((a + lam₁) ^ 2 / L) * s2 + ((a + lam₁) ^ 3 / L ^ 2) * s3
      ≤ (a + lam₁) * Cpf * (LL ^ 2 + ((a + lam₁) / L) * LL ^ 3
          + ((a + lam₁) ^ 2 / L ^ 2) * LL ^ 4) := by
    have e1 : (a + lam₁) * s1 ≤ (a + lam₁) * (Cpf * LL ^ 2) :=
      mul_le_mul_of_nonneg_left hb1 hXnn
    have e2 : ((a + lam₁) ^ 2 / L) * s2 ≤ ((a + lam₁) ^ 2 / L) * (Cpf * LL ^ 3) :=
      mul_le_mul_of_nonneg_left hb2 (div_nonneg (sq_nonneg _) hLpos.le)
    have e3 : ((a + lam₁) ^ 3 / L ^ 2) * s3 ≤ ((a + lam₁) ^ 3 / L ^ 2) * (Cpf * LL ^ 4) :=
      mul_le_mul_of_nonneg_left hb3 (div_nonneg (pow_nonneg hXnn 3) (sq_nonneg L))
    have heq : (a + lam₁) * Cpf * (LL ^ 2 + ((a + lam₁) / L) * LL ^ 3
          + ((a + lam₁) ^ 2 / L ^ 2) * LL ^ 4)
        = (a + lam₁) * (Cpf * LL ^ 2) + ((a + lam₁) ^ 2 / L) * (Cpf * LL ^ 3)
          + ((a + lam₁) ^ 3 / L ^ 2) * (Cpf * LL ^ 4) := by ring
    linarith [e1, e2, e3, heq.le, heq.ge]
  have hgL : g L = (Real.log L + 4) ^ 2 / L + A * ((Real.log L + 4) ^ 3 / L ^ 2)
      + A ^ 2 * ((Real.log L + 4) ^ 4 / L ^ 3) := rfl
  have hN' : K * Cpf * g L < e := by
    have hd := hN L (le_trans (le_max_left N 1) hL)
    rw [Real.dist_eq, sub_zero] at hd
    exact lt_of_abs_lt hd
  calc K * ((1 / L) * ((a + lam₁) * s1 + ((a + lam₁) ^ 2 / L) * s2
        + ((a + lam₁) ^ 3 / L ^ 2) * s3))
      ≤ K * ((1 / L) * ((a + lam₁) * Cpf * (LL ^ 2 + ((a + lam₁) / L) * LL ^ 3
          + ((a + lam₁) ^ 2 / L ^ 2) * LL ^ 4))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (div_nonneg zero_le_one hLpos.le))
          hK.le
    _ = (a + lam₁) * (K * Cpf) * ((1 / L) * (LL ^ 2 + ((a + lam₁) / L) * LL ^ 3
          + ((a + lam₁) ^ 2 / L ^ 2) * LL ^ 4)) := by ring
    _ ≤ (a + lam₁) * (K * Cpf) * ((1 / L) * ((Real.log L + 4) ^ 2
          + (A / L) * (Real.log L + 4) ^ 3 + (A ^ 2 / L ^ 2) * (Real.log L + 4) ^ 4)) :=
        mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hXnn (mul_nonneg hK.le hCpf.le))
    _ = (a + lam₁) * (K * Cpf * g L) := by rw [hgL]; ring
    _ ≤ (a + lam₁) * e := mul_le_mul_of_nonneg_left hN'.le hXnn

/-! ## The imprimitive correction -/

theorem imprimCorr {a e M : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∃ L₀ : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {L lam₁ : ℝ},
      L₀ ≤ L → Real.log (q : ℝ) ≤ L → 0 ≤ lam₁ → lam₁ ≤ M →
      ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 4 →
        Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
          ≤ @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L
              χ.primitiveCharacter s a lam₁ + (a + lam₁) * e := by
  obtain ⟨C, hCpos, hC⟩ := Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
  obtain ⟨Cpf, hCpfpos, hpf⟩ := Work.ZeroFreeTables.lam0w.pfLogLogBound
  obtain ⟨L0, hL0ge1, hnum⟩ :=
    corr_numeric_M (K := C) (a := a) (M := M) (e := e) (Cpf := Cpf) hCpos ha he hCpfpos
  refine ⟨L0, ?_⟩
  intro q hqne χ hχ L lam₁ hL hlogq hlam0 hlam_M s hsre hsim
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL1le : (1 : ℝ) ≤ L := le_trans hL0ge1 hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1le
  have hsy : 1 < s.re := by
    rw [hsre]
    have h : 0 < a / L := div_pos ha hLpos
    linarith
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hdiff := hC (N := χ.conductor) (q := q) (L := L) (s := s) (a := a) (lam₁ := lam₁)
    χ.conductor_dvd_level χ.primitiveCharacter hL1le hsy ha hlam0
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at hdiff
  set LL : ℝ := Real.log (Real.log (q : ℝ) + 2) + 2 with hLLdef
  set S1 : ℝ := ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) with hS1
  set S2 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) with hS2
  set S3 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) with hS3
  have hLL0 : 0 ≤ LL := by
    rw [hLLdef]
    have h1 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
    have h2 : 0 ≤ Real.log (Real.log (q : ℝ) + 2) := Real.log_nonneg (by linarith)
    linarith
  have hLLle : LL ≤ Real.log L + 4 := by
    rw [hLLdef]
    have h1 : Real.log (q : ℝ) + 2 ≤ 3 * L := by linarith
    have h2 : 0 < Real.log (q : ℝ) + 2 := by
      have h : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
      linarith
    have h3 : Real.log (Real.log (q : ℝ) + 2) ≤ Real.log (3 * L) := Real.log_le_log h2 h1
    have h4 : Real.log (3 * L) = Real.log 3 + Real.log L :=
      Real.log_mul (by norm_num) (ne_of_gt hLpos)
    have h5 : Real.log 3 ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    linarith
  have hb1 : S1 ≤ Cpf * LL ^ 2 := by
    rw [hS1, hLLdef]
    simpa [pow_one] using hpf q hq1 1 (by norm_num)
  have hb2 : S2 ≤ Cpf * LL ^ 3 := by
    rw [hS2, hLLdef]
    simpa using hpf q hq1 2 (by norm_num)
  have hb3 : S3 ≤ Cpf * LL ^ 4 := by
    rw [hS3, hLLdef]
    simpa using hpf q hq1 3 (by norm_num)
  have hnum' := hnum hL hLL0 hLLle hlam0 hlam_M hb1 hb2 hb3
  have heq : (C / L) * ((a + lam₁) * S1 + ((a + lam₁) ^ 2 / L) * S2
        + ((a + lam₁) ^ 3 / L ^ 2) * S3)
      = C * ((1 / L) * ((a + lam₁) * S1 + ((a + lam₁) ^ 2 / L) * S2
        + ((a + lam₁) ^ 3 / L ^ 2) * S3)) := by ring
  have hle : Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
      - @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L χ.primitiveCharacter
          s a lam₁ ≤ (a + lam₁) * e := by
    have h1 : Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
        - @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L
            χ.primitiveCharacter s a lam₁
        ≤ (C / L) * ((a + lam₁) * S1 + ((a + lam₁) ^ 2 / L) * S2
            + ((a + lam₁) ^ 3 / L ^ 2) * S3) := le_trans (le_abs_self _) hdiff
    rw [heq] at h1
    exact le_trans h1 hnum'
  linarith [hle]

end Work.ZeroFreeTables.HB95h2
