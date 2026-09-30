import Mathlib
import Submission.Work.BMF.VKStripDefs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-! ## Elementary real estimates comparing the classical de la Vallée Poussin region with the
region of the target statement.

For `3 ≤ |t| ≤ 10` and `N ≥ 1` all the logarithms below are `≥ 1`, so the denominator
`D = (log (|t|+3))^{6/7} (log (N+2) + log log (|t|+3))` dominates `log (N+2)`; on the other
hand `log (N (|t|+2)) ≤ log (N+2) + log 12 ≤ 12 log (N+2) ≤ 12 D`.  At `N = 1` the same
denominator is `≥ 1` while `log (|t|+3) ≤ log 13 ≤ 12`. -/

/-- `1 ≤ log 6`. -/
private lemma one_le_log_six : (1 : ℝ) ≤ Real.log 6 := by
  have h6 : (6 : ℝ) = 2 * 3 := by norm_num
  rw [h6, Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

/-- `1 ≤ log 3`. -/
private lemma one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  linarith [Real.log_three_gt_d9]

/-- For `3 ≤ |t|`, `1 ≤ log (|t| + 3)`. -/
private lemma one_le_log_abs_add_three {t : ℝ} (ht : 3 ≤ |t|) :
    (1 : ℝ) ≤ Real.log (|t| + 3) := by
  have h6 : (6 : ℝ) ≤ |t| + 3 := by
    have := abs_nonneg t
    linarith
  exact le_trans one_le_log_six (Real.log_le_log (by norm_num) h6)

/-- For `N ≥ 1`, `1 ≤ log (N + 2)`. -/
private lemma one_le_log_nat_cast_add_two {N : ℕ} [NeZero N] :
    (1 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
  have hN : (1 : ℝ) ≤ (N : ℝ) := by
    have : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have h3 : (3 : ℝ) ≤ (N : ℝ) + 2 := by linarith
  exact le_trans one_le_log_three (Real.log_le_log (by norm_num) h3)

/-- `(log (|t|+3))^{6/7} ≥ 1` for `3 ≤ |t|`. -/
private lemma one_le_rpow_log {t : ℝ} (ht : 3 ≤ |t|) :
    (1 : ℝ) ≤ Real.log (|t| + 3) ^ (6 / 7 : ℝ) := by
  have h1 : (1 : ℝ) ≤ Real.log (|t| + 3) := one_le_log_abs_add_three ht
  calc (1 : ℝ) = (1 : ℝ) ^ (6 / 7 : ℝ) := (Real.one_rpow _).symm
    _ ≤ Real.log (|t| + 3) ^ (6 / 7 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) h1 (by norm_num)

/-- The denominator `D` dominates `log (N+2)`. -/
private lemma log_nat_cast_add_two_le_denom {N : ℕ} [NeZero N] {t : ℝ} (ht : 3 ≤ |t|) :
    Real.log ((N : ℝ) + 2) ≤
      Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3))) := by
  have hr := one_le_rpow_log ht
  have hN := one_le_log_nat_cast_add_two (N := N)
  have hL := one_le_log_abs_add_three ht
  have hll : (0 : ℝ) ≤ Real.log (Real.log (|t| + 3)) := Real.log_nonneg hL
  have h1 : Real.log ((N : ℝ) + 2) ≤
      Real.log (|t| + 3) ^ (6 / 7 : ℝ) * Real.log ((N : ℝ) + 2) := by
    nlinarith [hr, hN]
  have h2 : Real.log ((N : ℝ) + 2) ≤
      Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)) := by linarith
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by linarith))

/-- `log (N (|t|+2)) ≤ 12 * D` in the height range `3 ≤ |t| ≤ 10`. -/
private lemma log_mul_le_denom {N : ℕ} [NeZero N] {t : ℝ} (ht : 3 ≤ |t|) (ht10 : |t| ≤ 10) :
    Real.log ((N : ℝ) * (|t| + 2)) ≤
      12 * (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have ht2pos : (0 : ℝ) < |t| + 2 := by
    have := abs_nonneg t
    linarith
  have hlog : Real.log ((N : ℝ) * (|t| + 2)) = Real.log (N : ℝ) + Real.log (|t| + 2) :=
    Real.log_mul (ne_of_gt hNpos) (ne_of_gt ht2pos)
  have hNle : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log hNpos (by linarith)
  have ht2le : Real.log (|t| + 2) ≤ Real.log 12 := by
    apply Real.log_le_log
    · positivity
    · have := abs_nonneg t
      linarith
  have h12 : Real.log 12 ≤ 11 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 12 by norm_num)
    linarith
  have h11 : (11 : ℝ) ≤ 11 * Real.log ((N : ℝ) + 2) := by
    have h := one_le_log_nat_cast_add_two (N := N)
    nlinarith
  have hden := log_nat_cast_add_two_le_denom (N := N) ht
  rw [hlog]
  linarith [hNle, ht2le, h12, h11, hden]

/-- `log (|t|+3) ≤ 100 * D` in the height range (this is the bound needed in the case
`χ = 1`, where the de la Vallée Poussin region is a function of `log (|t|+3)` alone). -/
private lemma log_abs_add_three_le_hundred_denom {N : ℕ} [NeZero N] {t : ℝ}
    (ht : 3 ≤ |t|) (ht10 : |t| ≤ 10) :
    Real.log (|t| + 3) ≤
      100 * (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) := by
  have hL1 : (1 : ℝ) ≤ Real.log (|t| + 3) := one_le_log_abs_add_three ht
  have hr : (1 : ℝ) ≤ Real.log (|t| + 3) ^ (6 / 7 : ℝ) := one_le_rpow_log ht
  have hN2 : (1 : ℝ) ≤ Real.log ((N : ℝ) + 2) := one_le_log_nat_cast_add_two (N := N)
  have hll : (0 : ℝ) ≤ Real.log (Real.log (|t| + 3)) := Real.log_nonneg hL1
  have hLle : Real.log (|t| + 3) ≤ 12 := by
    have h13 : Real.log (|t| + 3) ≤ Real.log 13 := by
      apply Real.log_le_log
      · positivity
      · have := abs_nonneg t
        linarith
    have h12 : Real.log 13 ≤ 12 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 13 by norm_num)
      linarith
    linarith
  have hden : (1 : ℝ) ≤ Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
      (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3))) := by
    nlinarith [hr, hN2, hll]
  nlinarith [hLle, hden]

/-- Comparison of reciprocals: if `c ≤ c'/100`, `0 ≤ c'` and `L ≤ 100 D` with `L, D > 0`,
then `c/D ≤ c'/L`. -/
private lemma div_le_div_of_le_hundred {c c' L D : ℝ} (hc : c ≤ c' / 100) (hc' : 0 ≤ c')
    (hL : 0 < L) (hD : 0 < D) (h : L ≤ 100 * D) : c / D ≤ c' / L := by
  rw [div_le_div_iff₀ hD hL]
  have h1 : c * L ≤ (c' / 100) * L := mul_le_mul_of_nonneg_right hc hL.le
  have h2 : (c' / 100) * L ≤ (c' / 100) * (100 * D) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have h3 : (c' / 100) * (100 * D) = c' * D := by ring
  linarith

/-- **Zero-free region at bounded heights** (`3 ≤ |t| ≤ 10`) for primitive characters,
uniform in the conductor.  The claimed region is a fixed-width (in `σ`) region, because for
`|t| ≤ 10` the denominator `(log(|t|+3))^{6/7} (log(N+2) + log log(|t|+3))` is comparable to
`1 + log N`; hence the classical de la Vallée Poussin type regions suffice.

ROUTE.  *Case `χ ≠ 1`.*  Apply `Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform`
(module `Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform`),
which gives `c₀ > 0` with `L(σ+it,χ) ≠ 0` whenever `χ` is primitive non-principal, `t ≠ 0` and
`σ ≥ 1 - c₀ / log(N(|t|+2))`.  For `3 ≤ |t| ≤ 10` one has
`log(N(|t|+2)) ≤ log(N+2) + log 20 ≤ 4 (log(N+2) + 1)` and
`(log(|t|+3))^{6/7} (log(N+2) + loglog(|t|+3)) ≤ C (log(N+2) + 1)` for an absolute `C`
(use `3 ≤ |t|+3 ≤ 13`, `log(|t|+3) ≥ 1`, and `log(N+2) ≥ log 3 > 1`), so the region below is
contained in the de la Vallée Poussin region for a suitable `c`.
*Case `χ = 1`.*  Then primitivity forces `N = 1` (`DirichletCharacter.isPrimitive_def` and
`DirichletCharacter.conductor_one`), so `L(·,χ) = riemannZeta` (`DirichletCharacter.LFunction_modOne_eq`);
use `Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound` (module
`Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound`), which gives `c > 0`
with `ζ(σ+it) ≠ 0` for `|t| ≥ 1` and `σ ≥ 1 - c/log(|t|+3)`, together with
`(log(|t|+3))^{6/7}(log 3 + loglog(|t|+3)) ≤ C' log(|t|+3)` for `3 ≤ |t| ≤ 10`.  (Add the two
Commons imports to your file.) -/
theorem zeroFree_bounded_height_chi :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ σ t : ℝ, 3 ≤ |t| → |t| ≤ 10 →
        1 - c / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨c₀, hc₀pos, h₀⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  obtain ⟨c₁, C₁, hc₁pos, hC₁pos, hζ, _⟩ :=
    Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound
  refine ⟨min c₀ c₁ / 100, by positivity, ?_⟩
  intro N hN χ hprim σ t ht3 ht10 hσ
  have hc₀le : min c₀ c₁ / 100 ≤ c₀ / 100 := by
    have := min_le_left c₀ c₁
    linarith
  have hc₁le : min c₀ c₁ / 100 ≤ c₁ / 100 := by
    have := min_le_right c₀ c₁
    linarith
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht3
    norm_num at ht3
  have hL1 : (1 : ℝ) ≤ Real.log (|t| + 3) := one_le_log_abs_add_three ht3
  have hLpos : 0 < Real.log (|t| + 3) := by linarith
  have hN2pos : 0 < Real.log ((N : ℝ) + 2) := by
    linarith [one_le_log_nat_cast_add_two (N := N)]
  have hll : (0 : ℝ) ≤ Real.log (Real.log (|t| + 3)) := Real.log_nonneg hL1
  have hrpos : 0 < Real.log (|t| + 3) ^ (6 / 7 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hDpos : 0 < Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
      (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3))) := by
    apply mul_pos hrpos
    linarith
  by_cases hχ1 : χ = 1
  · -- the principal character: primitivity forces `N = 1`
    have hN1 : N = 1 := by
      have h : χ.conductor = N := (DirichletCharacter.isPrimitive_def χ).mp hprim
      rw [hχ1, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN1
    have hLle := log_abs_add_three_le_hundred_denom (N := 1) ht3 ht10
    have hDpos₁ : 0 < Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log (((1 : ℕ) : ℝ) + 2) + Real.log (Real.log (|t| + 3))) := hDpos
    have hcmp : (min c₀ c₁ / 100) / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log (((1 : ℕ) : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤
        c₁ / Real.log (|t| + 3) :=
      div_le_div_of_le_hundred hc₁le hc₁pos.le hLpos hDpos₁ hLle
    have hσz : 1 - c₁ / Real.log (|t| + 3) ≤ σ := by linarith [hσ, hcmp]
    have ht1 : (1 : ℝ) ≤ |t| := by linarith
    have hz := hζ t ht1 σ hσz
    have hz' : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      simpa [mul_comm] using hz
    rw [hχ1]
    simpa using hz'
  · -- generic character: compare the two de la Vallée Poussin type regions
    have hEpos : 0 < Real.log ((N : ℝ) * (|t| + 2)) := by
      apply Real.log_pos
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
        have : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
        exact_mod_cast this
      have h5 : (5 : ℝ) ≤ |t| + 2 := by
        have := abs_nonneg t
        linarith
      nlinarith
    have hE12 := log_mul_le_denom (N := N) ht3 ht10
    have hE100 : Real.log ((N : ℝ) * (|t| + 2)) ≤
        100 * (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) := by
      linarith [hE12, hDpos]
    have hcmp : (min c₀ c₁ / 100) / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤
        c₀ / Real.log ((N : ℝ) * (|t| + 2)) :=
      div_le_div_of_le_hundred hc₀le hc₀pos.le hEpos hDpos hE100
    have hσv : 1 - c₀ / Real.log ((N : ℝ) * (|t| + 2)) ≤ σ := by linarith [hσ, hcmp]
    exact h₀ χ hprim hχ1 σ t ht0 hσv

end Work.BMF
