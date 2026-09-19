import Mathlib
import Submission.ZetaRatioPole
import Submission.ZetaResidueUniform
import Submission.PoleBound

open scoped BigOperators Topology
open Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# P8 (41) for a *family* of moduli `W(x), N(x)`

The sieve applies Lemma 4.1 with moduli growing with the scale:
`W = ∏_{p ≤ w(x)} p` (the `w(x) = logloglog x` primorial) and `q = W·N`.  For
this it is not enough to have the pole ratio (P8 (41)) for a *fixed* modulus;
one needs the uniformity to survive the variation of `q`.  This module proves
the family version of `zetaWN_ratio_pole_uniform`
(`Submission.ZetaRatioPole`):

    ‖ ζ_q(1+z₁+z₂)/(ζ_q(1+z₁)·ζ_q(1+z₂)) · poleFactor W N ξ ξ' x − 1 ‖ ≤ ε(x) ,

uniformly in `ξ, ξ'` in the cube and in `x`, where the error is driven to zero
by the *growth hypothesis* `log(W(x)·N(x)) / √(log x) → 0` — satisfied in the
sieve since `log q ≪ logloglog x`.

The proof uses the explicit per-modulus residue constants of
`zetaWN_residue_uniform_explicit` (`Submission.ZetaResidueUniform`):
`δ_q = min r₀ (1/(2(1+log q)))`, `C_q = 1 + 3C₀ + 4log q + 2C₀log q`, so that
on the cube `C_q·‖z‖ ≤ C_q·ϱ(x)` with `ϱ(x) = 1/log x + 1/√(log x) → 0` while
`C_q ≍ log q`; the hypothesis `log q/√(log x) → 0` makes `C_q·ϱ(x) → 0`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **P8 (41), family form (modified-zeta-side).**  Let `W, N : ℕ → ℕ` be
nonzero moduli, `(W x, N x) = 1`, with `log(W x · N x)/√(log x) → 0`.  Then the
modified-zeta ratio at the sieve's points satisfies the pole asymptotic
uniformly on the cube, with a vanishing error. -/
theorem zetaWN_ratio_pole_uniform_family
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x → ∀ ξ ξ' : ℝ,
        |ξ| ≤ Real.sqrt (Real.log (x : ℝ)) → |ξ'| ≤ Real.sqrt (Real.log (x : ℝ)) →
        ‖zetaWN ((W x) * (N x)) (1 + (logZ ξ x + logZ ξ' x)) /
            (zetaWN ((W x) * (N x)) (1 + logZ ξ x) *
              zetaWN ((W x) * (N x)) (1 + logZ ξ' x)) *
            poleFactor (W x) (N x) ξ ξ' x - 1‖ ≤ ε x := by
  classical
  obtain ⟨C0, r0, hC0pos, hr0pos, hC0⟩ := riemannZeta_residue_uniform_bound_explicit
  -- the vanishing error
  let Lq : ℕ → ℝ := fun x => Real.log (((W x) * (N x) : ℕ) : ℝ)
  let ϱ : ℕ → ℝ := fun x => (Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹
  let K : ℝ := 100 * (1 + C0)
  have hL : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsL : Tendsto (fun x : ℕ => Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hL
  have h1L : Tendsto (fun x : ℕ => (Real.log (x : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hL
  have h1sL : Tendsto (fun x : ℕ => (Real.sqrt (Real.log (x : ℝ)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsL
  have hϱ : Tendsto ϱ atTop (𝓝 0) := by
    have : ϱ = fun x : ℕ => (Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹ := rfl
    rw [this]
    simpa using h1L.add h1sL
  have hϱLq : Tendsto (fun x : ℕ => ϱ x * (1 + Lq x)) atTop (𝓝 0) := by
    have hterm1 : Tendsto (fun x : ℕ => Lq x * (Real.sqrt (Real.log (x : ℝ)))⁻¹)
        atTop (𝓝 0) := by
      simpa [Lq, div_eq_mul_inv] using hlq
    have hterm2 : Tendsto (fun x : ℕ =>
        Lq x * (Real.log (x : ℝ))⁻¹) atTop (𝓝 0) := by
      have h := hlq.mul h1sL
      have h' : Tendsto (fun x : ℕ =>
          (Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ))) *
            (Real.sqrt (Real.log (x : ℝ)))⁻¹) atTop (𝓝 0) := by
        simpa using h
      refine h'.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with x hx
      have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
      have hsq : Real.sqrt (Real.log (x : ℝ)) * Real.sqrt (Real.log (x : ℝ)) =
          Real.log (x : ℝ) := by
        rw [← sq, Real.sq_sqrt hLpos.le]
      dsimp [Lq]
      rw [div_eq_mul_inv, mul_assoc, ← mul_inv, hsq]
    have hsum : Tendsto (fun x : ℕ => (Real.log (x : ℝ))⁻¹ +
        (Real.sqrt (Real.log (x : ℝ)))⁻¹ + Lq x * (Real.log (x : ℝ))⁻¹ +
        Lq x * (Real.sqrt (Real.log (x : ℝ)))⁻¹) atTop (𝓝 0) := by
      have := ((h1L.add h1sL).add hterm2).add hterm1
      simpa only [add_zero] using this
    have heq : (fun x : ℕ => ϱ x * (1 + Lq x)) = fun x : ℕ => (Real.log (x : ℝ))⁻¹ +
        (Real.sqrt (Real.log (x : ℝ)))⁻¹ + Lq x * (Real.log (x : ℝ))⁻¹ +
        Lq x * (Real.sqrt (Real.log (x : ℝ)))⁻¹ := by
      funext x
      dsimp [ϱ]
      ring
    rw [heq]
    exact hsum
  -- the eventual threshold: the "smallness" conditions
  have hsmall : ∀ᶠ x : ℕ in atTop,
      (1 ≤ Real.log (x : ℝ)) ∧
      (2 * ϱ x ≤ min r0 (1 / (2 * (1 + Lq x)))) ∧
      (ϱ x * (1 + 3 * C0 + (4 + 2 * C0) * Lq x) ≤ 1 / 8) := by
    have hC0nn : 0 ≤ C0 := hC0pos.le
    have hηpos : 0 < min (1 / 64 : ℝ) (1 / (64 * (4 + 2 * C0))) := by
      refine lt_min (by norm_num) ?_
      have : 0 < 4 + 2 * C0 := by linarith
      positivity
    have hA : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) := hL.eventually_ge_atTop 1
    have hB : ∀ᶠ x : ℕ in atTop, (4 / r0) ^ 2 ≤ Real.log (x : ℝ) :=
      hL.eventually_ge_atTop _
    have hC : ∀ᶠ x : ℕ in atTop, (64 / 7 : ℝ) ≤ Real.sqrt (Real.log (x : ℝ)) := by
      have h : ∀ᶠ x : ℕ in atTop, ((64 / 7 : ℝ)) ^ 2 ≤ Real.log (x : ℝ) :=
        hL.eventually_ge_atTop _
      filter_upwards [h] with x hx
      calc (64 / 7 : ℝ) = Real.sqrt (((64 / 7 : ℝ)) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
        _ ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_le_sqrt hx
    have hD : ∀ᶠ x : ℕ in atTop, 32 * (1 + 3 * C0) ≤ Real.sqrt (Real.log (x : ℝ)) := by
      have h : ∀ᶠ x : ℕ in atTop, ((32 * (1 + 3 * C0)) ^ 2) ≤ Real.log (x : ℝ) :=
        hL.eventually_ge_atTop _
      filter_upwards [h] with x hx
      calc 32 * (1 + 3 * C0) = Real.sqrt (((32 * (1 + 3 * C0)) ^ 2)) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by nlinarith [hC0nn])]
        _ ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_le_sqrt hx
    have hE : ∀ᶠ x : ℕ in atTop,
        Lq x / Real.sqrt (Real.log (x : ℝ)) ≤ min (1 / 64 : ℝ) (1 / (64 * (4 + 2 * C0))) := by
      have h := hlq.eventually_lt_const hηpos
      filter_upwards [h] with x hx
      exact hx.le
    filter_upwards [hA, hB, hC, hD, hE] with x h1 h2 h3 h4 h5
    have hLpos : 0 < Real.log (x : ℝ) := by linarith
    have hsLpos : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.2 hLpos
    have hsLge : 1 ≤ Real.sqrt (Real.log (x : ℝ)) := by
      have h := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_one] at h
    have hsLr0 : 4 / r0 ≤ Real.sqrt (Real.log (x : ℝ)) := by
      have h := Real.sqrt_le_sqrt h2
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at h
      exact h
    have hϱle : ϱ x ≤ 2 / Real.sqrt (Real.log (x : ℝ)) := by
      dsimp [ϱ]
      have h1' : (Real.log (x : ℝ))⁻¹ ≤ (Real.sqrt (Real.log (x : ℝ)))⁻¹ := by
        rw [inv_le_inv₀ hLpos hsLpos]
        calc Real.sqrt (Real.log (x : ℝ)) ≤ Real.sqrt (Real.log (x : ℝ)) ^ 2 := by
              nlinarith [hsLge]
          _ = Real.log (x : ℝ) := Real.sq_sqrt hLpos.le
      have h2' : 2 / Real.sqrt (Real.log (x : ℝ)) =
          (Real.sqrt (Real.log (x : ℝ)))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹ := by
        rw [div_eq_mul_inv]; ring
      linarith [h1', h2']
    have hηle : min (1 / 64 : ℝ) (1 / (64 * (4 + 2 * C0))) ≤ 1 / (64 * (4 + 2 * C0)) :=
      min_le_right _ _
    have hLq_le : Lq x ≤ min (1 / 64 : ℝ) (1 / (64 * (4 + 2 * C0))) *
        Real.sqrt (Real.log (x : ℝ)) := by
      rw [div_le_iff₀ hsLpos] at h5
      exact h5
    have h32 : 8 * (1 + Lq x) ≤ Real.sqrt (Real.log (x : ℝ)) := by
      have h64 : (1 / 64 : ℝ) ≤ 1 := by norm_num
      have hLq_le' : Lq x ≤ (1 / 64) * Real.sqrt (Real.log (x : ℝ)) :=
        le_trans hLq_le (mul_le_mul_of_nonneg_right (min_le_left _ _) hsLpos.le)
      nlinarith [hLq_le', h3, hsLpos]
    refine ⟨h1, ?_, ?_⟩
    · have h4sL : 4 / Real.sqrt (Real.log (x : ℝ)) ≤ r0 := by
        rw [div_le_iff₀ hsLpos]
        have hmul := mul_le_mul_of_nonneg_left hsLr0 hr0pos.le
        have hcancel : (4 / r0) * r0 = 4 := by field_simp
        linarith [hmul, hcancel]
      have h4sL' : 4 / Real.sqrt (Real.log (x : ℝ)) ≤ 1 / (2 * (1 + Lq x)) := by
        rw [div_le_div_iff₀ hsLpos (by positivity)]
        nlinarith [h32]
      have : 2 * ϱ x ≤ 4 / Real.sqrt (Real.log (x : ℝ)) := by
        have := hϱle
        rw [div_eq_mul_inv] at this ⊢
        nlinarith [hsLpos]
      exact le_trans this (le_min h4sL h4sL')
    · have h32C0 : 2 * (1 + 3 * C0) / Real.sqrt (Real.log (x : ℝ)) ≤ 1 / 16 := by
        rw [div_le_iff₀ hsLpos]
        nlinarith [h4]
      have hLqs : Lq x / Real.sqrt (Real.log (x : ℝ)) ≤ 1 / (64 * (4 + 2 * C0)) :=
        le_trans h5 hηle
      have hC0Lq : (4 + 2 * C0) * (Lq x / Real.sqrt (Real.log (x : ℝ))) ≤ 1 / 64 := by
        have hpos : 0 < 4 + 2 * C0 := by linarith
        calc (4 + 2 * C0) * (Lq x / Real.sqrt (Real.log (x : ℝ)))
            ≤ (4 + 2 * C0) * (1 / (64 * (4 + 2 * C0))) :=
              mul_le_mul_of_nonneg_left hLqs hpos.le
          _ = 1 / 64 := by field_simp
      have hmain : ϱ x * (1 + 3 * C0 + (4 + 2 * C0) * Lq x) ≤ 1 / 8 := by
        have hLq0x : 0 ≤ Lq x := by
          dsimp [Lq]
          refine Real.log_nonneg ?_
          have h1 : 1 ≤ W x := Nat.one_le_iff_ne_zero.mpr (hW x)
          have h2 : 1 ≤ N x := Nat.one_le_iff_ne_zero.mpr (hN x)
          exact_mod_cast (by nlinarith [h1, h2] : (1 : ℕ) ≤ (W x) * (N x))
        have hsplit : ϱ x * (1 + 3 * C0 + (4 + 2 * C0) * Lq x) ≤
            (2 / Real.sqrt (Real.log (x : ℝ))) *
              ((1 + 3 * C0) + (4 + 2 * C0) * Lq x) := by
          refine mul_le_mul_of_nonneg_right hϱle ?_
          nlinarith [hC0nn, hLq0x]
        have hexpand : (2 / Real.sqrt (Real.log (x : ℝ))) *
            ((1 + 3 * C0) + (4 + 2 * C0) * Lq x) =
            2 * (1 + 3 * C0) / Real.sqrt (Real.log (x : ℝ)) +
            2 * ((4 + 2 * C0) * (Lq x / Real.sqrt (Real.log (x : ℝ)))) := by
          field_simp
        rw [hexpand] at hsplit
        have h2C0Lq : 2 * ((4 + 2 * C0) * (Lq x / Real.sqrt (Real.log (x : ℝ)))) ≤ 1 / 32 := by
          nlinarith [hC0Lq]
        linarith [hsplit, h32C0, h2C0Lq]
      exact hmain

  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨x₀, fun x => K * (ϱ x * (1 + Lq x)), ?_, ?_⟩
  · simpa using hϱLq.const_mul K
  · intro x hx ξ ξ' hξ hξ'
    obtain ⟨hL1, hthresh, hsmall2⟩ := hx₀ x hx
    have hLpos : 0 < Real.log (x : ℝ) := by linarith
    set q : ℕ := (W x) * (N x) with hqdef
    have hq0 : q ≠ 0 := mul_ne_zero (hW x) (hN x)
    -- smallness consequences
    have hϱnn : 0 ≤ ϱ x := by
      dsimp [ϱ]
      have hLpos : 0 < Real.log (x : ℝ) := by linarith
      have h1 : 0 ≤ (Real.log (x : ℝ))⁻¹ := inv_nonneg.mpr hLpos.le
      have h2 : 0 ≤ (Real.sqrt (Real.log (x : ℝ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      linarith
    have hϱδ : ϱ x ≤ min r0 (1 / (2 * (1 + Lq x))) := by linarith [hthresh, hϱnn]
    have hCqϱ : ϱ x * (1 + 3 * C0 + (4 + 2 * C0) * Lq x) ≤ 1 / 8 := hsmall2
    have hLq0 : 0 ≤ Lq x := by
      dsimp [Lq]
      refine Real.log_nonneg ?_
      have h1 : 1 ≤ W x := Nat.one_le_iff_ne_zero.mpr (hW x)
      have h2 : 1 ≤ N x := Nat.one_le_iff_ne_zero.mpr (hN x)
      exact_mod_cast (by nlinarith [h1, h2] : (1 : ℕ) ≤ (W x) * (N x))
    -- the three points
    have hz1 : ‖logZ ξ x‖ ≤ ϱ x := by
      have : ϱ x = (Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹ := rfl
      rw [this]
      exact logZ_norm_le_sum_inv ξ x hξ hL1
    have hz2 : ‖logZ ξ' x‖ ≤ ϱ x := by
      have : ϱ x = (Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹ := rfl
      rw [this]
      exact logZ_norm_le_sum_inv ξ' x hξ' hL1
    have hz3 : ‖logZ ξ x + logZ ξ' x‖ ≤ 2 * ϱ x := by
      have h := logZ_add_norm_le ξ ξ' x hξ hξ' hL1
      have : 2 * ((Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹) = 2 * ϱ x := rfl
      rwa [this] at h
    have hz1δ : ‖logZ ξ x‖ ≤ min r0 (1 / (2 * (1 + Lq x))) := hz1.trans hϱδ
    have hz2δ : ‖logZ ξ' x‖ ≤ min r0 (1 / (2 * (1 + Lq x))) := hz2.trans hϱδ
    have hz3δ : ‖logZ ξ x + logZ ξ' x‖ ≤ min r0 (1 / (2 * (1 + Lq x))) := by
      refine hz3.trans ?_
      linarith [hthresh]
    -- nonvanishing
    have hξnz : (1 : ℂ) + ξ * Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re] at this
    have hξnz' : (1 : ℂ) + ξ' * Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re] at this
    have h3nz : (2 : ℂ) + (ξ + ξ') * Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re] at this
    have hlogC : (Real.log (x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
    have hz1nz : logZ ξ x ≠ 0 := by
      dsimp [logZ]; exact div_ne_zero hξnz hlogC
    have hz2nz : logZ ξ' x ≠ 0 := by
      dsimp [logZ]; exact div_ne_zero hξnz' hlogC
    have hz3nz : logZ ξ x + logZ ξ' x ≠ 0 := by
      have hEq : logZ ξ x + logZ ξ' x =
          ((2 : ℂ) + (ξ + ξ') * Complex.I) / (Real.log (x : ℝ) : ℂ) := by
        dsimp [logZ]; rw [← add_div]; congr 1; ring
      rw [hEq]; exact div_ne_zero h3nz hlogC
    have hqC : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hq0
    have hφqC : ((q.totient : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)).ne'
    -- the η's and their bounds
    set η : ℂ → ℂ := fun z => zetaWN q (1 + z) * z * ((q : ℂ) / (q.totient : ℂ)) with hηdef
    have hres := zetaWN_residue_uniform_of q hq0 hC0pos hr0pos hC0
    have hres1 := hres (logZ ξ x) hz1nz hz1δ
    have hres2 := hres (logZ ξ' x) hz2nz hz2δ
    have hres3 := hres (logZ ξ x + logZ ξ' x) hz3nz hz3δ
    have hCqeq : (1 + 3 * C0 + 4 * Real.log (q : ℝ) + 2 * C0 * Real.log (q : ℝ)) =
        1 + 3 * C0 + (4 + 2 * C0) * Lq x := by
      rw [hqdef]
      dsimp [Lq]
      ring
    have he1 : ‖η (logZ ξ x) - 1‖ ≤ (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x := by
      rw [hηdef]
      rw [hCqeq] at hres1
      exact hres1.trans (mul_le_mul_of_nonneg_left hz1 (by positivity))
    have he2 : ‖η (logZ ξ' x) - 1‖ ≤ (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x := by
      rw [hηdef]
      rw [hCqeq] at hres2
      exact hres2.trans (mul_le_mul_of_nonneg_left hz2 (by positivity))
    have he3 : ‖η (logZ ξ x + logZ ξ' x) - 1‖ ≤
        (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * (2 * ϱ x) := by
      rw [hηdef]
      rw [hCqeq] at hres3
      refine hres3.trans ?_
      have := mul_le_mul_of_nonneg_left hz3 (by positivity :
        (0 : ℝ) ≤ 1 + 3 * C0 + (4 + 2 * C0) * Lq x)
      linarith [this]
    have hCqϱ' : (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x ≤ 1 / 8 := by
      linarith [hCqϱ, mul_comm ((1 + 3 * C0 + (4 + 2 * C0) * Lq x)) (ϱ x)]
    have he1' : ‖η (logZ ξ x) - 1‖ ≤ 1 / 8 := he1.trans hCqϱ'
    have he2' : ‖η (logZ ξ' x) - 1‖ ≤ 1 / 8 := he2.trans hCqϱ'
    have he3' : ‖η (logZ ξ x + logZ ξ' x) - 1‖ ≤ 1 / 2 := by
      have h2 : (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * (2 * ϱ x) ≤ 1 / 2 := by
        linarith [hCqϱ']
      exact he3.trans h2
    have hη1nz : η (logZ ξ x) ≠ 0 := by
      intro h
      have h1 : ‖η (logZ ξ x) - 1‖ = 1 := by rw [h]; norm_num
      linarith
    have hη2nz : η (logZ ξ' x) ≠ 0 := by
      intro h
      have h1 : ‖η (logZ ξ' x) - 1‖ = 1 := by rw [h]; norm_num
      linarith
    have hη3nz : η (logZ ξ x + logZ ξ' x) ≠ 0 := by
      intro h
      have h1 : ‖η (logZ ξ x + logZ ξ' x) - 1‖ = 1 := by rw [h]; norm_num
      linarith
    -- ζ-values in terms of η
    have hζ1 : zetaWN q (1 + logZ ξ x) =
        η (logZ ξ x) * ((q.totient : ℂ) / ((q : ℂ) * logZ ξ x)) := by
      rw [hηdef]
      dsimp only
      field_simp [hz1nz, hqC, hφqC]
    have hζ2 : zetaWN q (1 + logZ ξ' x) =
        η (logZ ξ' x) * ((q.totient : ℂ) / ((q : ℂ) * logZ ξ' x)) := by
      rw [hηdef]
      dsimp only
      field_simp [hz2nz, hqC, hφqC]
    have hζ3 : zetaWN q (1 + (logZ ξ x + logZ ξ' x)) =
        η (logZ ξ x + logZ ξ' x) *
          ((q.totient : ℂ) / ((q : ℂ) * (logZ ξ x + logZ ξ' x))) := by
      rw [hηdef]
      dsimp only
      field_simp [hz3nz, hqC, hφqC]
    -- the multiplicative identity
    have hkey := poleFactor_scalar (W x) (N x) (hW x) (hN x) (hcop x) ξ ξ' x hLpos.ne'
    rw [← hqdef] at hkey
    have hmain : (zetaWN q (1 + (logZ ξ x + logZ ξ' x)) /
          (zetaWN q (1 + logZ ξ x) * zetaWN q (1 + logZ ξ' x)) *
          poleFactor (W x) (N x) ξ ξ' x) * (η (logZ ξ x) * η (logZ ξ' x)) =
        η (logZ ξ x + logZ ξ' x) := by
      rw [hζ1, hζ2, hζ3]
      have hstep : (η (logZ ξ x + logZ ξ' x) *
              ((q.totient : ℂ) / ((q : ℂ) * (logZ ξ x + logZ ξ' x)))) /
          ((η (logZ ξ x) * ((q.totient : ℂ) / ((q : ℂ) * logZ ξ x))) *
            (η (logZ ξ' x) * ((q.totient : ℂ) / ((q : ℂ) * logZ ξ' x)))) *
          poleFactor (W x) (N x) ξ ξ' x * (η (logZ ξ x) * η (logZ ξ' x)) =
          η (logZ ξ x + logZ ξ' x) *
            (((q : ℂ) * logZ ξ x * logZ ξ' x * poleFactor (W x) (N x) ξ ξ' x) /
              ((q.totient : ℂ) * (logZ ξ x + logZ ξ' x))) := by
        field_simp [hz1nz, hz2nz, hz3nz, hqC, hφqC, hη1nz, hη2nz, hη3nz]
      rw [hstep, hkey]
      field_simp [hφqC, hz3nz]
    have hG : zetaWN q (1 + (logZ ξ x + logZ ξ' x)) /
          (zetaWN q (1 + logZ ξ x) * zetaWN q (1 + logZ ξ' x)) *
          poleFactor (W x) (N x) ξ ξ' x =
        η (logZ ξ x + logZ ξ' x) / (η (logZ ξ x) * η (logZ ξ' x)) := by
      rw [eq_div_iff (mul_ne_zero hη1nz hη2nz)]
      exact hmain
    rw [hG]
    -- the norm bound
    have hsplit : η (logZ ξ x + logZ ξ' x) - η (logZ ξ x) * η (logZ ξ' x) =
        (η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1) - (η (logZ ξ' x) - 1) -
          (η (logZ ξ x) - 1) * (η (logZ ξ' x) - 1) := by ring
    have htri : ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1) -
        (η (logZ ξ' x) - 1) - (η (logZ ξ x) - 1) * (η (logZ ξ' x) - 1)‖ ≤
        ‖η (logZ ξ x + logZ ξ' x) - 1‖ + ‖η (logZ ξ x) - 1‖ + ‖η (logZ ξ' x) - 1‖ +
          ‖η (logZ ξ x) - 1‖ * ‖η (logZ ξ' x) - 1‖ := by
      have hA : ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1) -
          (η (logZ ξ' x) - 1) - (η (logZ ξ x) - 1) * (η (logZ ξ' x) - 1)‖ ≤
          ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1) - (η (logZ ξ' x) - 1)‖ +
            ‖(η (logZ ξ x) - 1) * (η (logZ ξ' x) - 1)‖ := norm_sub_le _ _
      have hB : ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1) -
          (η (logZ ξ' x) - 1)‖ ≤
          ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1)‖ + ‖η (logZ ξ' x) - 1‖ :=
        norm_sub_le _ _
      have hC : ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1)‖ ≤
          ‖η (logZ ξ x + logZ ξ' x) - 1‖ + ‖η (logZ ξ x) - 1‖ := norm_sub_le _ _
      have hD : ‖(η (logZ ξ x) - 1) * (η (logZ ξ' x) - 1)‖ =
          ‖η (logZ ξ x) - 1‖ * ‖η (logZ ξ' x) - 1‖ := norm_mul _ _
      linarith [hA, hB, hC, hD.le, hD.ge]
    have hDbound : ‖η (logZ ξ x + logZ ξ' x) - η (logZ ξ x) * η (logZ ξ' x)‖ ≤
        10 * ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x) := by
      rw [hsplit]
      have h12 : ‖η (logZ ξ x) - 1‖ * ‖η (logZ ξ' x) - 1‖ ≤
          ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x) *
            ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x) :=
        mul_le_mul he1 he2 (norm_nonneg _) (by positivity)
      have hstep := htri
      have hsum : ‖η (logZ ξ x + logZ ξ' x) - 1‖ + ‖η (logZ ξ x) - 1‖ +
          ‖η (logZ ξ' x) - 1‖ + ‖η (logZ ξ x) - 1‖ * ‖η (logZ ξ' x) - 1‖ ≤
          (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * (2 * ϱ x) +
            (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x +
            (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x +
            ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x) *
              ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x) := by
        linarith [he1, he2, he3, h12]
      have hbound2 : (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * (2 * ϱ x) +
          (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x +
          (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x +
          ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x) *
            ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x) ≤
          10 * ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x) := by
        have hx1 : 0 ≤ (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x := by positivity
        have hx2 : ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x) *
            ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x) ≤
            (1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x := by
          nlinarith [hCqϱ']
        nlinarith [hx1, hx2, hCqϱ']
      linarith [hstep, hsum, hbound2]
    have hη1ge : (7 / 8 : ℝ) ≤ ‖η (logZ ξ x)‖ := by
      have h := abs_norm_sub_norm_le (η (logZ ξ x)) 1
      simp only [norm_one] at h
      have h2 : |‖η (logZ ξ x)‖ - 1| ≤ 1 / 8 := h.trans he1'
      linarith [(abs_le.mp h2).1]
    have hη2ge : (7 / 8 : ℝ) ≤ ‖η (logZ ξ' x)‖ := by
      have h := abs_norm_sub_norm_le (η (logZ ξ' x)) 1
      simp only [norm_one] at h
      have h2 : |‖η (logZ ξ' x)‖ - 1| ≤ 1 / 8 := h.trans he2'
      linarith [(abs_le.mp h2).1]
    have hden : (1 / 2 : ℝ) ≤ ‖η (logZ ξ x) * η (logZ ξ' x)‖ := by
      rw [norm_mul]
      nlinarith [hη1ge, hη2ge]
    have hne : η (logZ ξ x) * η (logZ ξ' x) ≠ 0 := mul_ne_zero hη1nz hη2nz
    have hdiv : η (logZ ξ x + logZ ξ' x) / (η (logZ ξ x) * η (logZ ξ' x)) - 1 =
        (η (logZ ξ x + logZ ξ' x) - η (logZ ξ x) * η (logZ ξ' x)) /
          (η (logZ ξ x) * η (logZ ξ' x)) := by
      field_simp [hne]
    rw [hdiv, norm_div]
    have hstep1 : ‖η (logZ ξ x + logZ ξ' x) - η (logZ ξ x) * η (logZ ξ' x)‖ /
          ‖η (logZ ξ x) * η (logZ ξ' x)‖ ≤
        (10 * ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x)) / (1 / 2) := by
      refine div_le_div₀ (by positivity) hDbound (by norm_num) hden
    have hstep2 : (10 * ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x)) / (1 / 2) ≤
        K * (ϱ x * (1 + Lq x)) := by
      have hCqle : 1 + 3 * C0 + (4 + 2 * C0) * Lq x ≤ (1 + 3 * C0 + (4 + 2 * C0)) * (1 + Lq x) := by
        nlinarith [hLq0, hC0pos]
      have hϱx : 0 ≤ ϱ x := hϱnn
      have h1 : 10 * ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x) / (1 / 2) =
          20 * ((1 + 3 * C0 + (4 + 2 * C0) * Lq x) * ϱ x) := by ring
      rw [h1]
      dsimp [K]
      nlinarith [mul_le_mul_of_nonneg_right hCqle hϱx, hϱx, hC0pos, hLq0]
    linarith [hstep1, hstep2]


end Commons.NumberTheory.MaynardSieve
