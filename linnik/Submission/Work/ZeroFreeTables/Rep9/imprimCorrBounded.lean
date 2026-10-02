import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le

open scoped BigOperators
noncomputable section

set_option maxHeartbeats 1000000

namespace Work.ZeroFreeTables.Rep9

/-! ## The imprimitive correction of HB §9

`SigmaP3L q L χ s a λ₁` is the smoothing functional `Σ(s,χ)` of Heath-Brown (8.4) at the free
logarithmic scale `L`, for a character `χ` of level `q` (see `P3/DefsL.lean`).  When `χ` is
imprimitive it is the `changeLevel` lift of its primitive character `χ.primitiveCharacter` of
level `χ.conductor`, and the two functionals differ: the difference is carried by the prime
powers `p^k` with `p ∣ q` but `p ∤ χ.conductor`.

The already-proved `P9.SigmaP3L_changeLevel_diff` bounds that difference by the prime-divisor
sums `S_j(q) = ∑_{p ∣ q} (log p)^j / p`, and `P9.primeFactors_logPow_div_le` bounds each `S_j`
by `C (log log q)^{j+1}`.  Since `log q ≤ L` and `L → ∞`, the correction is absorbed into
`(a + λ₁) e`: this file carries out that absorption (`imprimAbsorb`) and deduces the requested
`imprimCorrBounded`. -/

/-- For `t ≥ 1`, `(log t)^4 ≤ 4096 √t` (from `log t ≤ 8 t^{1/8}`). -/
private lemma log_fourth_le_sqrt (t : ℝ) (ht : 1 ≤ t) :
    Real.log t ^ 4 ≤ 4096 * Real.sqrt t := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have h1 : Real.log t ≤ 8 * t ^ (1/8:ℝ) := by
    have h := Real.log_le_rpow_div ht0 (show (0:ℝ) < 1/8 by norm_num)
    have he : t ^ (1/8:ℝ) / (1/8:ℝ) = 8 * t ^ (1/8:ℝ) := by ring
    rwa [he] at h
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h2 : (Real.log t)^4 ≤ (8 * t ^ (1/8:ℝ))^4 := pow_le_pow_left₀ hlog0 h1 4
  have key : (t ^ (1/8:ℝ))^4 = Real.sqrt t := by
    rw [(Real.rpow_natCast (t ^ (1/8:ℝ)) 4).symm,
      ← Real.rpow_mul ht0 (1/8:ℝ) ((4:ℕ):ℝ)]
    norm_num
    rw [Real.sqrt_eq_rpow]
  have h3 : (8 * t ^ (1/8:ℝ))^4 = 4096 * Real.sqrt t := by
    rw [mul_pow, key]; norm_num
  rw [h3] at h2
  exact h2

/-- Decay of the iterated logarithm: for `1 ≤ u ≤ T` and `T ≥ 100`,
`(log u)^{j+1} / T^j ≤ 4096 / √T` for `1 ≤ j ≤ 3`. -/
private lemma loglog_pow_div_le (u T : ℝ) (hu1 : 1 ≤ u) (huT : u ≤ T) (hT100 : 100 ≤ T)
    (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) :
    (Real.log u)^(j+1) / T^j ≤ 4096 / Real.sqrt T := by
  have hTpos : 0 < T := by linarith only [hT100]
  have hT1 : 1 ≤ T := by linarith only [hT100]
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hloguT : Real.log u ≤ Real.log T := Real.log_le_log hu0 huT
  have hlogT1 : 1 ≤ Real.log T := by
    have h100 : 1 ≤ Real.log 100 := by
      have h := Real.log_le_log (Real.exp_pos 1)
        (by linarith only [Real.exp_one_lt_three] : Real.exp 1 ≤ 100)
      rwa [Real.log_exp] at h
    exact le_trans h100 (Real.log_le_log (by norm_num) hT100)
  have hkey : Real.log u ^ (j+1) ≤ Real.log T ^ 4 := by
    have ha : Real.log u ^ (j+1) ≤ Real.log T ^ (j+1) := pow_le_pow_left₀ hlogu0 hloguT _
    have hb : Real.log T ^ (j+1) ≤ Real.log T ^ 4 := pow_le_pow_right₀ hlogT1 (by omega)
    linarith only [ha, hb]
  have hnum : Real.log u ^ (j+1) ≤ 4096 * Real.sqrt T :=
    le_trans hkey (log_fourth_le_sqrt T hT1)
  rw [div_le_div_iff₀ (pow_pos hTpos j) (Real.sqrt_pos.mpr hTpos)]
  have hs : Real.log u ^ (j+1) * Real.sqrt T ≤ (4096 * Real.sqrt T) * Real.sqrt T :=
    mul_le_mul_of_nonneg_right hnum (Real.sqrt_nonneg T)
  have hsq : (4096 * Real.sqrt T) * Real.sqrt T = 4096 * T := by
    rw [mul_assoc, Real.mul_self_sqrt (le_of_lt hTpos)]
  rw [hsq] at hs
  have hTL : 4096 * T ≤ 4096 * T^j := by
    have h : T^1 ≤ T^j := pow_le_pow_right₀ hT1 hj1
    simpa using mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 4096)
  linarith only [hs, hTL]

/-- **Absorption of the imprimitive-correction prime-divisor sum.**  For constants `C, a, e > 0`
there is `L₀ ≥ 1` such that whenever `L ≥ L₀`, `log q ≤ L`, `0 ≤ λ₁` and `a + λ₁ ≤ A`, the
prime-divisor tail
`(C/L)·(α S₁ + (α²/L) S₂ + (α³/L²) S₃)`, `α = a + λ₁`, `S_j = ∑_{p ∣ q}(log p)^j/p`,
is at most `α e`. -/
theorem imprimAbsorb {C a e A : ℝ} (hC : 0 < C) (ha : 0 < a) (he : 0 < e) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ {q : ℕ} [NeZero q] {L lam₁ : ℝ},
      L₀ ≤ L → Real.log (q:ℝ) ≤ L → 0 ≤ lam₁ → a + lam₁ ≤ A →
      (C / L) * ((a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p:ℝ) / (p:ℝ))
        + ((a + lam₁)^2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2 / (p:ℝ))
        + ((a + lam₁)^3 / L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3 / (p:ℝ)))
        ≤ (a + lam₁) * e := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 1 (by norm_num)
  obtain ⟨C2, hC2pos, hC2⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨C3, hC3pos, hC3⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 3 (by norm_num)
  set A' : ℝ := max A 0 with hA'def
  have hA'nn : 0 ≤ A' := le_max_right A 0
  have hAle : A ≤ A' := le_max_left A 0
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set Big2 : ℝ := C * (4096 * (C1 + A' * C2 + A'^2 * C3)) with hBig2def
  set Small2 : ℝ := C * (A' * (Real.log 2 / 2) + A'^2 * ((Real.log 2)^2 / 2)
    + A'^3 * ((Real.log 2)^3 / 2)) with hSmall2def
  have hBig2nn : 0 ≤ Big2 := by
    rw [hBig2def]
    refine mul_nonneg (le_of_lt hC) (mul_nonneg (by norm_num) ?_)
    have h2 : 0 ≤ A' * C2 := mul_nonneg hA'nn (le_of_lt hC2pos)
    have h3 : 0 ≤ A'^2 * C3 := mul_nonneg (pow_nonneg hA'nn 2) (le_of_lt hC3pos)
    linarith only [le_of_lt hC1pos, hC1pos, h2, h3]
  set L0 : ℝ := max 100 (max ((Big2/e)^2) (Small2/(a*e))) with hL0def
  have hL0ge100 : 100 ≤ L0 := by rw [hL0def]; exact le_max_left _ _
  have hL0geBig : (Big2/e)^2 ≤ L0 := by
    rw [hL0def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hL0geSmall : Small2/(a*e) ≤ L0 := by
    rw [hL0def]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hL0pos : 0 < L0 := by linarith only [hL0ge100]
  have hL0one : 1 ≤ L0 := by linarith only [hL0ge100]
  refine ⟨L0, hL0one, ?_⟩
  intro q _inst L lam₁ hL0 hlogq hlam0 hαA
  set α : ℝ := a + lam₁ with hαdef
  have hαpos : 0 < α := by rw [hαdef]; linarith only [ha, hlam0]
  have hαnn : 0 ≤ α := le_of_lt hαpos
  have hαA' : α ≤ A' := by rw [hαdef]; exact le_trans hαA hAle
  have hLpos : 0 < L := by linarith only [hL0ge100, hL0]
  by_cases hq3 : 3 ≤ q
  · -- large `q` : use the `log log` decay of the prime-divisor sums
    have hlogq1 : 1 ≤ Real.log (q:ℝ) := by
      have h3 : 1 < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
        exact Real.exp_one_lt_three
      exact le_trans (le_of_lt h3) (Real.log_le_log (by norm_num) (by exact_mod_cast hq3))
    set τ : ℝ := max L0 (Real.log (q:ℝ)) with hτdef
    have hτL : τ ≤ L := max_le hL0 hlogq
    have hτL0 : L0 ≤ τ := le_max_left _ _
    have hτlogq : Real.log (q:ℝ) ≤ τ := le_max_right _ _
    have hτ100 : 100 ≤ τ := le_trans hL0ge100 hτL0
    have hτpos : 0 < τ := by linarith only [hL0ge100, hτL0]
    set w : ℝ := Real.log (Real.log (q:ℝ)) with hwdef
    have hw0 : 0 ≤ w := by rw [hwdef]; exact Real.log_nonneg hlogq1
    have hS1 : (∑ p ∈ q.primeFactors, Real.log (p:ℝ) / (p:ℝ)) ≤ C1 * w^2 := by
      rw [hwdef]; simpa using hC1 q hq3
    have hS2 : (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2 / (p:ℝ)) ≤ C2 * w^3 := by
      rw [hwdef]; simpa using hC2 q hq3
    have hS3 : (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3 / (p:ℝ)) ≤ C3 * w^4 := by
      rw [hwdef]; simpa using hC3 q hq3
    have hW1 : w^2 / L ≤ 4096 / Real.sqrt L0 := by
      have h2 : w^2 / L ≤ w^2 / τ := div_le_div_of_nonneg_left (sq_nonneg w) hτpos hτL
      have h3 : w^2 / τ ≤ 4096 / Real.sqrt τ := by
        have h := loglog_pow_div_le (Real.log (q:ℝ)) τ hlogq1 hτlogq hτ100 1 le_rfl (by norm_num)
        rw [hwdef]; simpa using h
      have h4 : 4096 / Real.sqrt τ ≤ 4096 / Real.sqrt L0 :=
        div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hL0pos) (Real.sqrt_le_sqrt hτL0)
      linarith only [h2, h3, h4]
    have hW2 : w^3 / L^2 ≤ 4096 / Real.sqrt L0 := by
      have h2 : w^3 / L^2 ≤ w^3 / τ^2 :=
        div_le_div_of_nonneg_left (pow_nonneg hw0 3) (pow_pos hτpos 2)
          (pow_le_pow_left₀ hτpos.le hτL 2)
      have h3 : w^3 / τ^2 ≤ 4096 / Real.sqrt τ := by
        have h := loglog_pow_div_le (Real.log (q:ℝ)) τ hlogq1 hτlogq hτ100 2 (by norm_num) (by norm_num)
        rw [hwdef]; simpa using h
      have h4 : 4096 / Real.sqrt τ ≤ 4096 / Real.sqrt L0 :=
        div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hL0pos) (Real.sqrt_le_sqrt hτL0)
      linarith only [h2, h3, h4]
    have hW3 : w^4 / L^3 ≤ 4096 / Real.sqrt L0 := by
      have h2 : w^4 / L^3 ≤ w^4 / τ^3 :=
        div_le_div_of_nonneg_left (pow_nonneg hw0 4) (pow_pos hτpos 3)
          (pow_le_pow_left₀ hτpos.le hτL 3)
      have h3 : w^4 / τ^3 ≤ 4096 / Real.sqrt τ := by
        have h := loglog_pow_div_le (Real.log (q:ℝ)) τ hlogq1 hτlogq hτ100 3 (by norm_num) (by norm_num)
        rw [hwdef]; simpa using h
      have h4 : 4096 / Real.sqrt τ ≤ 4096 / Real.sqrt L0 :=
        div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hL0pos) (Real.sqrt_le_sqrt hτL0)
      linarith only [h2, h3, h4]
    have hBigLe : Big2 / Real.sqrt L0 ≤ e := by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr hL0pos)]
      have hsqrt : Big2 / e ≤ Real.sqrt L0 := by
        have h0 : 0 ≤ Big2 / e := div_nonneg hBig2nn he.le
        have h := Real.sqrt_le_sqrt hL0geBig
        rwa [Real.sqrt_sq h0] at h
      have h := mul_le_mul_of_nonneg_left hsqrt (le_of_lt he)
      have h2 : e * (Big2 / e) = Big2 := by
        rw [mul_comm]; exact div_mul_cancel₀ Big2 (ne_of_gt he)
      rwa [h2] at h
    have hfinal : C * α * ((C1 + A' * C2 + A'^2 * C3) * (4096 / Real.sqrt L0)) ≤ α * e := by
      have heq : C * α * ((C1 + A' * C2 + A'^2 * C3) * (4096 / Real.sqrt L0))
          = α * (Big2 / Real.sqrt L0) := by
        rw [hBig2def]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hBigLe hαnn
    calc (C/L) * (α * (∑ p ∈ q.primeFactors, Real.log (p:ℝ) / (p:ℝ))
            + (α^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2 / (p:ℝ))
            + (α^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3 / (p:ℝ)))
        ≤ (C/L) * (α * (C1*w^2) + (α^2/L) * (C2*w^3) + (α^3/L^2) * (C3*w^4)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hA : α * (∑ p ∈ q.primeFactors, Real.log (p:ℝ) / (p:ℝ)) ≤ α * (C1*w^2) :=
            mul_le_mul_of_nonneg_left hS1 hαnn
          have hB : (α^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2 / (p:ℝ))
              ≤ (α^2/L) * (C2*w^3) := mul_le_mul_of_nonneg_left hS2 (by positivity)
          have hD : (α^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3 / (p:ℝ))
              ≤ (α^3/L^2) * (C3*w^4) := mul_le_mul_of_nonneg_left hS3 (by positivity)
          linarith only [hA, hB, hD]
      _ = C*α*(C1*(w^2/L) + α*(C2*(w^3/L^2)) + α^2*(C3*(w^4/L^3))) := by ring
      _ ≤ C*α*((C1 + α*C2 + α^2*C3) * (4096/Real.sqrt L0)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hb1 : C1*(w^2/L) ≤ C1*(4096/Real.sqrt L0) :=
            mul_le_mul_of_nonneg_left hW1 (le_of_lt hC1pos)
          have hb2 : α*(C2*(w^3/L^2)) ≤ α*(C2*(4096/Real.sqrt L0)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW2 (le_of_lt hC2pos)) hαnn
          have hb3 : α^2*(C3*(w^4/L^3)) ≤ α^2*(C3*(4096/Real.sqrt L0)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW3 (le_of_lt hC3pos))
              (pow_nonneg hαnn 2)
          linarith only [hb1, hb2, hb3]
      _ ≤ C*α*((C1 + A'*C2 + A'^2*C3) * (4096/Real.sqrt L0)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have h2 : α*C2 ≤ A'*C2 := mul_le_mul_of_nonneg_right hαA' (le_of_lt hC2pos)
          have h3 : α^2*C3 ≤ A'^2*C3 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hαnn hαA' 2) (le_of_lt hC3pos)
          linarith only [h2, h3]
      _ ≤ α * e := hfinal
  · -- small `q` (`q ≤ 2`): the prime-divisor sums are bounded by their values at `q = 2`
    have hq1 : 1 ≤ q := by have := NeZero.ne q; omega
    have hq2 : q ≤ 2 := by omega
    have hsq : ∀ j : ℕ, (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^j / (p:ℝ))
        ≤ (Real.log 2)^j / 2 := by
      intro j
      rcases (show q = 1 ∨ q = 2 by omega) with h | h
      · subst h
        simp only [Nat.primeFactors_one, Finset.sum_empty]
        exact div_nonneg (pow_nonneg hlog2nn j) (by norm_num)
      · subst h
        have h2pf : (2:ℕ).primeFactors = ({2} : Finset ℕ) := by
          have h := Nat.primeFactors_prime_pow (p := 2) (k := 1) (by norm_num) (by norm_num)
          simpa using h
        rw [h2pf, Finset.sum_singleton]
        norm_num
    have hS1 : (∑ p ∈ q.primeFactors, Real.log (p:ℝ) / (p:ℝ)) ≤ Real.log 2 / 2 := by
      have h := hsq 1; simpa using h
    have hS2 : (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2 / (p:ℝ))
        ≤ (Real.log 2)^2 / 2 := hsq 2
    have hS3 : (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3 / (p:ℝ))
        ≤ (Real.log 2)^3 / 2 := hsq 3
    have ha1 : 0 ≤ Real.log 2 / 2 := by positivity
    have ha2 : 0 ≤ (Real.log 2)^2 / 2 := by positivity
    have ha3 : 0 ≤ (Real.log 2)^3 / 2 := by positivity
    set a1 : ℝ := Real.log 2 / 2 with ha1def
    set a2 : ℝ := (Real.log 2)^2 / 2 with ha2def
    set a3 : ℝ := (Real.log 2)^3 / 2 with ha3def
    have ha1nn : 0 ≤ a1 := by rw [ha1def]; exact ha1
    have ha2nn : 0 ≤ a2 := by rw [ha2def]; exact ha2
    have ha3nn : 0 ≤ a3 := by rw [ha3def]; exact ha3
    -- (i) replace the three prime-divisor sums by their bounds
    have hstep1 : (C/L) * (α * (∑ p ∈ q.primeFactors, Real.log (p:ℝ) / (p:ℝ))
          + (α^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2 / (p:ℝ))
          + (α^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3 / (p:ℝ)))
        ≤ (C/L) * (α * a1 + (α^2/L) * a2 + (α^3/L^2) * a3) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 : α * (∑ p ∈ q.primeFactors, Real.log (p:ℝ) / (p:ℝ)) ≤ α * a1 :=
        mul_le_mul_of_nonneg_left (by rw [ha1def]; exact hS1) hαnn
      have h2 : (α^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2 / (p:ℝ))
          ≤ (α^2/L) * a2 :=
        mul_le_mul_of_nonneg_left (by rw [ha2def]; exact hS2) (by positivity)
      have h3 : (α^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3 / (p:ℝ))
          ≤ (α^3/L^2) * a3 :=
        mul_le_mul_of_nonneg_left (by rw [ha3def]; exact hS3) (by positivity)
      linarith only [h1, h2, h3]
    -- (ii) expand and bound termwise by `A'/L0`
    have hstep2 : (C/L) * (α * a1 + (α^2/L) * a2 + (α^3/L^2) * a3)
        ≤ Small2 / L0 := by
      have hexp : (C/L) * (α * a1 + (α^2/L) * a2 + (α^3/L^2) * a3)
          = C*α*a1/L + C*α^2*a2/L^2 + C*α^3*a3/L^3 := by
        rw [ha1def, ha2def, ha3def]; ring
      rw [hexp]
      have h1 : C*α*a1/L ≤ C*A'*a1/L0 := by
        have h1a : C*α*a1/L ≤ C*α*a1/L0 :=
          div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg hC.le hαnn) ha1nn) hL0pos hL0
        have h1b : C*α*a1/L0 ≤ C*A'*a1/L0 := by
          have hc : 0 ≤ C*a1/L0 := div_nonneg (mul_nonneg hC.le ha1nn) hL0pos.le
          calc C*α*a1/L0 = (C*a1/L0)*α := by ring
            _ ≤ (C*a1/L0)*A' := mul_le_mul_of_nonneg_left hαA' hc
            _ = C*A'*a1/L0 := by ring
        linarith only [h1a, h1b]
      have h2 : C*α^2*a2/L^2 ≤ C*A'^2*a2/L0^2 := by
        have hα2 : α^2 ≤ A'^2 := pow_le_pow_left₀ hαnn hαA' 2
        have hL2 : L0^2 ≤ L^2 := pow_le_pow_left₀ hL0pos.le hL0 2
        have h2a : C*α^2*a2/L^2 ≤ C*α^2*a2/L0^2 :=
          div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg hC.le (pow_nonneg hαnn 2)) ha2nn)
            (pow_pos hL0pos 2) hL2
        have h2b : C*α^2*a2/L0^2 ≤ C*A'^2*a2/L0^2 := by
          have hc : 0 ≤ C*a2/L0^2 :=
            div_nonneg (mul_nonneg hC.le ha2nn) (pow_nonneg hL0pos.le 2)
          calc C*α^2*a2/L0^2 = (C*a2/L0^2)*α^2 := by ring
            _ ≤ (C*a2/L0^2)*A'^2 := mul_le_mul_of_nonneg_left hα2 hc
            _ = C*A'^2*a2/L0^2 := by ring
        linarith only [h2a, h2b]
      have h3 : C*α^3*a3/L^3 ≤ C*A'^3*a3/L0^3 := by
        have hα3 : α^3 ≤ A'^3 := pow_le_pow_left₀ hαnn hαA' 3
        have hL3 : L0^3 ≤ L^3 := pow_le_pow_left₀ hL0pos.le hL0 3
        have h3a : C*α^3*a3/L^3 ≤ C*α^3*a3/L0^3 :=
          div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg hC.le (pow_nonneg hαnn 3)) ha3nn)
            (pow_pos hL0pos 3) hL3
        have h3b : C*α^3*a3/L0^3 ≤ C*A'^3*a3/L0^3 := by
          have hc : 0 ≤ C*a3/L0^3 :=
            div_nonneg (mul_nonneg hC.le ha3nn) (pow_nonneg hL0pos.le 3)
          calc C*α^3*a3/L0^3 = (C*a3/L0^3)*α^3 := by ring
            _ ≤ (C*a3/L0^3)*A'^3 := mul_le_mul_of_nonneg_left hα3 hc
            _ = C*A'^3*a3/L0^3 := by ring
        linarith only [h3a, h3b]
      have e1 : C*A'^2*a2/L0^2 ≤ C*A'^2*a2/L0 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg hC.le (pow_nonneg hA'nn 2)) ha2nn) hL0pos
          (by nlinarith only [hL0one, hL0ge100])
      have e2 : C*A'^3*a3/L0^3 ≤ C*A'^3*a3/L0 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg hC.le (pow_nonneg hA'nn 3)) ha3nn) hL0pos
          (by nlinarith [hL0one])
      have hfin : C*A'*a1/L0 + C*A'^2*a2/L0 + C*A'^3*a3/L0 = Small2/L0 := by
        rw [hSmall2def, ha1def, ha2def, ha3def]; ring
      linarith only [h1, h2, h3, e1, e2, hfin.le, hfin.ge, hfin]
    -- (iii) `Small2/L0 ≤ a·e ≤ α·e`
    have hSmallLe : Small2 / L0 ≤ a * e := by
      have hae : 0 < a*e := mul_pos ha he
      rw [div_le_iff₀ hL0pos]
      have h := mul_le_mul_of_nonneg_left hL0geSmall hae.le
      have h2 : a*e * (Small2/(a*e)) = Small2 := by
        rw [mul_comm]; exact div_mul_cancel₀ Small2 (ne_of_gt hae)
      rwa [h2] at h
    calc (C/L) * (α * (∑ p ∈ q.primeFactors, Real.log (p:ℝ) / (p:ℝ))
            + (α^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2 / (p:ℝ))
            + (α^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3 / (p:ℝ)))
        ≤ Small2 / L0 := le_trans hstep1 hstep2
      _ ≤ a * e := hSmallLe
      _ ≤ α * e := mul_le_mul_of_nonneg_right (by rw [hαdef]; linarith only [hlam0]) he.le

/-- **The imprimitive correction is bounded.**  For `a, e > 0` and a bound `M` on `λ₁` there is
`L₀` such that for every character `χ` of level `q`, every `L ≥ L₀` with `log q ≤ L`, and every
`λ₁ ≤ M`, the functional `Σ(s,χ)` at the imprimitive level `q` is bounded by its value at the
conductor of `χ` plus `(a+λ₁)·e`. -/
theorem imprimCorrBounded {a e M : ℝ} (ha : 0 < a) (he : 0 < e) (hM : 0 ≤ M) :
    ∃ L₀ : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {L lam₁ : ℝ},
      L₀ ≤ L → Real.log (q:ℝ) ≤ L → 0 ≤ lam₁ → lam₁ ≤ M →
      ∀ s : ℂ, s.re = 1 + a/L → |s.im| ≤ 4 →
        Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
          ≤ @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L χ.primitiveCharacter
              s a lam₁ + (a + lam₁) * e := by
  obtain ⟨C, hCpos, hC⟩ := Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
  obtain ⟨L₀, hL₀1, hAbs⟩ := imprimAbsorb (C := C) (a := a) (e := e) (A := a + M) hCpos ha he
  refine ⟨L₀, ?_⟩
  intro q _inst χ hχ L lam₁ hL0 hlogq hlam0 hlamM s hsre him
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hLpos : 0 < L := by linarith only [hL₀1, hL0]
  have hL1 : 1 ≤ L := le_trans hL₀1 hL0
  have hsre' : 1 < s.re := by
    rw [hsre]
    have : 0 < a/L := div_pos ha hLpos
    linarith only [this]
  have hdiff := hC (N := χ.conductor) (q := q) (χ.conductor_dvd_level) χ.primitiveCharacter
    hL1 hsre' ha hlam0
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at hdiff
  have habs := hAbs (q := q) hL0 hlogq hlam0 (by linarith only [hlamM])
  have hkey : Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
      - @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L χ.primitiveCharacter
          s a lam₁ ≤ (a + lam₁) * e := le_trans (le_trans (le_abs_self _) hdiff) habs
  linarith only [_inst, hkey]

end Work.ZeroFreeTables.Rep9
