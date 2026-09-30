import Mathlib
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.est17_gexp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ### Auxiliary real-analytic facts

For `y > 0`, `b ≥ 0` and an integer exponent `n`, the power `(√y)^n` is controlled by
`exp (b · log⁺ y)` (resp. `exp (b · log⁺ y⁻¹)`) as soon as the half-exponent `|n|/2` is at most
`b`.  These are the elementary inequalities behind the finite-place bound for the `ρ_j`-monomial
factor, the non-archimedean analogue of `rhoE_zpow_w_le`. -/

/-- `(√y)^n ≤ exp (b · log⁺ y)` for `y > 0`, `b ≥ 0`, `0 ≤ n` and `n ≤ 2b`. -/
lemma sqrt_zpow_le_exp_posLog {y b : ℝ} (hy : 0 < y) (hb : 0 ≤ b) (n : ℤ) (hn : 0 ≤ n)
    (h2 : (n : ℝ) ≤ 2 * b) :
    Real.sqrt y ^ n ≤ Real.exp (b * Real.posLog y) := by
  have hspos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hcast : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : (n : ℝ) * (Real.log y / 2) ≤ b * Real.posLog y := by
    rw [Real.posLog]
    rcases lt_or_ge (Real.log y) 0 with h | h
    · rw [max_eq_left h.le]; nlinarith
    · rw [max_eq_right h]; nlinarith
  calc Real.sqrt y ^ n = Real.sqrt y ^ ((n : ℝ)) := (Real.rpow_intCast _ n).symm
    _ = Real.exp ((n : ℝ) * (Real.log y / 2)) := by
          rw [Real.rpow_def_of_pos hspos, Real.log_sqrt hy.le]; ring_nf
    _ ≤ Real.exp (b * Real.posLog y) := Real.exp_le_exp.mpr hlog

/-- `(√y)^n ≤ exp (b · log⁺ y⁻¹)` for `y > 0`, `b ≥ 0`, `n ≤ 0` and `-2b ≤ n`. -/
lemma sqrt_zpow_le_exp_posLog_inv {y b : ℝ} (hy : 0 < y) (hb : 0 ≤ b) (n : ℤ) (hn : n ≤ 0)
    (h2 : -(2 * b) ≤ (n : ℝ)) :
    Real.sqrt y ^ n ≤ Real.exp (b * Real.posLog y⁻¹) := by
  have hspos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hcast : (0 : ℝ) ≤ -(n : ℝ) := by
    have : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    linarith
  have h2' : -(n : ℝ) ≤ 2 * b := by linarith
  have hlog : (-(n : ℝ)) * (Real.log y⁻¹ / 2) ≤ b * Real.posLog y⁻¹ := by
    rw [Real.posLog]
    rcases lt_or_ge (Real.log y⁻¹) 0 with h | h
    · rw [max_eq_left h.le]; nlinarith
    · rw [max_eq_right h]; nlinarith
  calc Real.sqrt y ^ n = Real.sqrt y ^ ((n : ℝ)) := (Real.rpow_intCast _ n).symm
    _ = Real.exp ((-(n : ℝ)) * (Real.log y⁻¹ / 2)) := by
          rw [Real.rpow_def_of_pos hspos, Real.log_sqrt hy.le, Real.log_inv]; ring_nf
    _ ≤ Real.exp (b * Real.posLog y⁻¹) := Real.exp_le_exp.mpr hlog

/-- Single-`j` finite-place bound for the `ρ_j`-monomial factor: with `ρ_j² = φ(α'_j)` in
`L = ℚ(φ(K),ρ)` and `ρ_j ≠ 0`, one has
`w (ρ_j)^{s·⌊λ/2^J⌋} ≤ exp((|s|/2^{J+1})·D·log⁺ w(α'_j)^{±1})` for every real `D ≥ λ`,
the sign chosen by the sign of `s` and the base `w(α'_j)^{±1}` accordingly.  Uses
`w(ρ_j)² = w(α'_j)`, `w(ρ_j) = √(w(α'_j)) ≥ 0`, `⌊λ/2^J⌋ ≤ λ/2^J ≤ D/<2^J>` and the
elementary `(√y)^n ≤ exp(b·log⁺ y^{±1})` above. -/
theorem rhoE_mon_fin_le {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ}
    {ρ : Fin r → ℂ} {α' : Fin r → K} (hρ : ∀ j, ρ j ^ 2 = φ (α' j))
    {j : Fin r} (hρj0 : ρ j ≠ 0)
    [inst : NumberField (EL φ ρ)] (w : NumberField.FinitePlace (EL φ ρ))
    (s : ℤ) (J : ℕ) {L0 : ℕ} {D : ℝ} (hD : 0 ≤ D) (hk : (L0 : ℝ) ≤ D) :
    w (rhoE φ ρ j ^ (s * ((L0 / 2 ^ J : ℕ) : ℤ))) ≤
      Real.exp ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * D
        * (if 0 ≤ s then w (inclE φ ρ (α' j)) else (w (inclE φ ρ (α' j)))⁻¹).posLog) := by
  have hsq : rhoE φ ρ j ^ 2 = inclE φ ρ (α' j) := rhoE_sq hρ j
  have hw2 : w (inclE φ ρ (α' j)) = w (rhoE φ ρ j) ^ 2 := by rw [← hsq, map_pow]
  have hrj : rhoE φ ρ j ≠ 0 := by
    intro h
    apply hρj0
    have hc : (rhoE φ ρ j : ℂ) = 0 := by rw [h]; simp
    rwa [rhoE_coe] at hc
  have ht : 0 < w (rhoE φ ρ j) := NumberField.FinitePlace.pos_iff.mpr hrj
  have hy : 0 < w (inclE φ ρ (α' j)) := by rw [hw2]; exact pow_pos ht 2
  have hsqt : w (rhoE φ ρ j) = Real.sqrt (w (inclE φ ρ (α' j))) :=
    ((Real.sqrt_eq_iff_eq_sq (AbsoluteValue.nonneg _ _) (AbsoluteValue.nonneg _ _)).mpr hw2).symm
  have hkf : (((L0 / 2 ^ J : ℕ)) : ℝ) ≤ D / 2 ^ J := by
    have h1 : (((L0 / 2 ^ J : ℕ)) : ℝ) ≤ (L0 : ℝ) / (2 : ℝ) ^ J := by
      simpa using Nat.cast_div_le (m := L0) (n := 2 ^ J)
    exact le_trans h1 (div_le_div_of_nonneg_right hk (by positivity))
  have hS : (0 : ℝ) ≤ ((|s| : ℤ) : ℝ) := by positivity
  have hmain : ((|s| : ℤ) : ℝ) * (((L0 / 2 ^ J : ℕ)) : ℝ)
      ≤ ((|s| : ℤ) : ℝ) * (D / 2 ^ J) := mul_le_mul_of_nonneg_left hkf hS
  have e2 : 2 * ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * D) = ((|s| : ℤ) : ℝ) * (D / 2 ^ J) := by
    have h2J : (2 : ℝ) ^ J ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  rcases lt_or_ge s 0 with hsneg | hspos
  · have hSneg : ((|s| : ℤ) : ℝ) = -(s : ℝ) := by
      rw [Int.cast_abs, abs_of_neg (by exact_mod_cast hsneg)]
    have hn : s * ((L0 / 2 ^ J : ℕ) : ℤ) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · exact_mod_cast hsneg.le
      · exact_mod_cast Nat.zero_le _
    have hcast : (((s * ((L0 / 2 ^ J : ℕ) : ℤ) : ℤ)) : ℝ)
        = -((( |s| : ℤ) : ℝ) * (((L0 / 2 ^ J : ℕ)) : ℝ)) := by
      rw [Int.cast_mul, Int.cast_natCast, hSneg]; ring
    have h2 : -(2 * ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * D))
        ≤ (((s * ((L0 / 2 ^ J : ℕ) : ℤ) : ℤ)) : ℝ) := by
      rw [e2, hcast]; linarith [hmain]
    have hb : 0 ≤ ((|s| : ℤ) : ℝ) / 2 / 2 ^ J * D := by positivity
    have key := sqrt_zpow_le_exp_posLog_inv hy hb (s * ((L0 / 2 ^ J : ℕ) : ℤ)) hn h2
    rw [if_neg (not_le.mpr hsneg)]
    rw [map_zpow₀, hsqt]; exact key
  · have hSpos : ((|s| : ℤ) : ℝ) = (s : ℝ) := by
      rw [Int.cast_abs, abs_of_nonneg (by exact_mod_cast hspos)]
    have hn : 0 ≤ s * ((L0 / 2 ^ J : ℕ) : ℤ) := by
      apply mul_nonneg
      · exact_mod_cast hspos
      · exact_mod_cast Nat.zero_le _
    have hcast : (((s * ((L0 / 2 ^ J : ℕ) : ℤ) : ℤ)) : ℝ)
        = ((|s| : ℤ) : ℝ) * (((L0 / 2 ^ J : ℕ)) : ℝ) := by
      rw [Int.cast_mul, Int.cast_natCast, hSpos]
    have h2 : (((s * ((L0 / 2 ^ J : ℕ) : ℤ) : ℤ)) : ℝ)
        ≤ 2 * ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * D) := by
      rw [e2, hcast]; linarith [hmain]
    have hb : 0 ≤ ((|s| : ℤ) : ℝ) / 2 / 2 ^ J * D := by positivity
    have key := sqrt_zpow_le_exp_posLog hy hb (s * ((L0 / 2 ^ J : ℕ) : ℤ)) hn h2
    rw [if_pos hspos]
    rw [map_zpow₀, hsqt]; exact key

/-- The `α'`-monomial factor of the expansion of `g(s/2)` at a finite place `w` of the Kummer
extension.  Since `rhoE j ^ 2 = inclE (α' j)` (from `H.hBH`), one has
`w (rhoE j)^{s·k_j} = w(α'_j)^{s·k_j/2}`; and since `k_j = ⌊λ_j/2^J⌋ ≤ D_j/2^J` (because
`λ_j ≤ D_j`), the ceiling is `exp((|s|/2^{J+1})·Σ_j D_j·log⁺ w(α'_j)^{±1})`, the sign chosen
by the sign of `s` (`H` supplies `α'_j ≠ 0` and `exp(lamP j) = φ(α'_j)`). -/
theorem est17_mon_fin_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {Lm : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σl : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl) → K}
    (H : ACHyp φ α b k c v Lm α' σl ι p) (J : ℕ) (s : ℤ)
    [inst : NumberField (EL φ (rhoC φ α v Lm))]
    (w : NumberField.FinitePlace (EL φ (rhoC φ α v Lm)))
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl)) :
    w (∏ j, rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J)))
      ≤ Real.exp ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * ∑ j, (pDj r (dK K) σl j : ℝ)
          * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j))
             else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog) := by
  classical
  have hexp : ∀ j, Complex.exp (lamP φ α v Lm j) = φ (α' j) :=
    fun j => (H.hBH.2.2.1 j).2
  have hρ : ∀ j, (rhoC φ α v Lm j) ^ 2 = φ (α' j) := fun j => rhoC_sq α v Lm hexp j
  have hfac : ∀ j, w (rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J)))
      ≤ Real.exp ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (pDj r (dK K) σl j : ℝ)
          * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j))
             else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog) := by
    intro j
    refine rhoE_mon_fin_le hρ ?_ w s J (by positivity) ?_
    · intro hc
      have hcz : Complex.exp (lamP φ α v Lm j / 2) = 0 := by simpa [rhoC] using hc
      exact Complex.exp_ne_zero _ hcz
    · have hlt : (lm.2.2 j : ℕ) ≤ pDj r (dK K) σl j := Nat.lt_succ_iff.mp (lm.2.2 j).isLt
      exact_mod_cast hlt
  calc w (∏ j, rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J)))
      = ∏ j, w (rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J))) := by
        rw [map_prod]
    _ ≤ ∏ j, Real.exp ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (pDj r (dK K) σl j : ℝ)
          * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j))
             else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog) :=
        Finset.prod_le_prod₀ (fun j _ => AbsoluteValue.nonneg _ _) (fun j _ => hfac j)
    _ = Real.exp ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * ∑ j, (pDj r (dK K) σl j : ℝ)
          * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j))
             else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring

end Work.BW
