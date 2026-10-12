import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseK15.arith_tau_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.arith_tauTilde_ge` — the kinetic domination for `τ̃`

`Work.BoseK15.arith_tau_ge` proves the kinetic domination of FS's **kinked**
symbol `def:tau`: at FS's parameter point, for `r ≥ (4K_Ha)⁻¹`,

`r²/2 + 3ρ_zK₀a ≤ (1-ε_T)(r-(2sℓ)⁻¹)₊² + ε_T(r-(2dsℓ)⁻¹)₊²`,

the right-hand side being the lower bound for `τ` (`φ ≥ (r-1)₊²` with
`x²(r/x-1)₊² = (r-x)₊²`).

The honest model uses the **smoothed** symbol `τ̃` (design §2.2), whose lower bound
is `(1-ε_T)(r-(sℓ)⁻¹)₊² + ε_T(r-(dsℓ)⁻¹)₊²` — the same shape with the thresholds
doubled (`tauTilde_ge_kink`).  Doubling the thresholds makes the one-variable
kinetic gain `max (r - x)₀² ≥ (7r/8)²` need `(sℓ)⁻¹ ≤ r/8`, i.e. the threshold
condition `aK_H/(sℓ) ≤ 1/32` instead of `1/16`; the rest of the argument — the
potential term `3ρ_zK₀a ≤ r²/8` and the coefficient comparison
`5/8 ≤ 49(1-ε_T)/64` — is unchanged.

This is the `htaurad` input of `A_ge_of_taurad` at the honest model, hence the
`A_ge`/`ABq` rows of the gate at `τ̃`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseGateFS

open Work.BoseBox

/-- **The kinetic domination for `τ̃`.** -/
theorem arith_tauTilde_ge (K₀ : ℝ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
      (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
      hv.t ≤ t₀ → E.aScat * E.KH / (E.s * E.ell) ≤ 1 / 32 → ∀ r : ℝ,
      1 / (4 * E.KH * E.aScat) ≤ r →
        r ^ 2 / 2 + 3 * E.rho * K₀ * E.aScat ≤
          (1 - E.eT) * max (r - (E.s * E.ell)⁻¹) 0 ^ 2
            + E.eT * max (r - (E.d * E.s * E.ell)⁻¹) 0 ^ 2 := by
  obtain ⟨t₀, ht₀pos, ht₀⟩ := Work.BoseK15.exists_tau_params K₀
  refine ⟨t₀, ht₀pos, ?_⟩
  intro Mode _ _ E hv ht h16 r hr
  obtain ⟨heT, hKl⟩ := ht₀ E hv ht
  -- positivity of the parameters
  have ha : 0 < E.aScat := hv.a_pos
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have hs : 0 < E.s := by rw [hv.s_eq]; exact fsXp_pos hv.t_pos
  have hell : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hrho : 0 ≤ E.rho := (Work.BoseB7.rho_pos E hv).le
  have heTnn : 0 ≤ E.eT := by rw [hv.eT_eq]; exact fsXp_nonneg hv.t_pos.le
  have h1eT : 0 ≤ 1 - E.eT := by linarith
  have hrnn : 0 ≤ r := le_trans (by positivity) hr
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  -- **Step 1: the kinetic threshold `(sℓ)⁻¹ ≤ r/8`** (the doubled thresholds).
  have hx : (E.s * E.ell)⁻¹ ≤ r / 8 := by
    have hstep : (1 / (E.aScat * E.KH)) * (E.aScat * E.KH / (E.s * E.ell)) ≤
        (1 / (E.aScat * E.KH)) * (1 / 32) :=
      mul_le_mul_of_nonneg_left h16 (by positivity)
    have hL : (1 / (E.aScat * E.KH)) * (E.aScat * E.KH / (E.s * E.ell)) =
        (E.s * E.ell)⁻¹ := by field_simp
    have hR : (1 / (E.aScat * E.KH)) * (1 / 32) = (1 / (4 * (E.KH * E.aScat))) / 8 := by
      field_simp
      ring
    rw [hL, hR] at hstep
    have h4 : 1 / (4 * (E.KH * E.aScat)) ≤ r := by
      convert hr using 2
      ring
    linarith
  -- **Step 2: `τ̃(r) ≥ (49(1 − eT)/64)·r²`.**
  have hmax : 49 * r ^ 2 / 64 ≤ max (r - (E.s * E.ell)⁻¹) 0 ^ 2 :=
    Work.BoseK15.max_sq_lower hx hrnn
  have hRHS : 49 * (1 - E.eT) / 64 * r ^ 2 ≤
      (1 - E.eT) * max (r - (E.s * E.ell)⁻¹) 0 ^ 2
        + E.eT * max (r - (E.d * E.s * E.ell)⁻¹) 0 ^ 2 := by
    have hA : (1 - E.eT) * (49 * r ^ 2 / 64) ≤
        (1 - E.eT) * (max (r - (E.s * E.ell)⁻¹) 0 ^ 2) :=
      mul_le_mul_of_nonneg_left hmax h1eT
    have hB : 0 ≤ E.eT * max (r - (E.d * E.s * E.ell)⁻¹) 0 ^ 2 :=
      mul_nonneg heTnn (sq_nonneg _)
    have hA' : (1 - E.eT) * (49 * r ^ 2 / 64) = 49 * (1 - E.eT) / 64 * r ^ 2 := by ring
    rw [hA'] at hA
    linarith
  -- **Step 3: the potential term is dominated.**
  have hLHS : r ^ 2 / 2 + 3 * E.rho * K₀ * E.aScat ≤ 49 * (1 - E.eT) / 64 * r ^ 2 := by
    have hcoef : (5 / 8 : ℝ) ≤ 49 * (1 - E.eT) / 64 := by linarith
    have hcf : (5 / 8) * r ^ 2 ≤ 49 * (1 - E.eT) / 64 * r ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef hr2
    have hterm : 3 * E.rho * K₀ * E.aScat ≤ r ^ 2 / 8 := by
      rcases le_or_gt K₀ 0 with hK | hK
      · have h3 : 3 * E.rho * K₀ * E.aScat ≤ 0 := by
          have hpos : 0 ≤ 3 * E.rho * E.aScat := by positivity
          nlinarith [hK, hpos]
        linarith
      · have hKA : E.mu * K₀ * E.aScat = K₀ * E.lille / (E.KH * E.aScat) ^ 2 := by
          rw [Work.BoseB7.Q3Env.lille, Work.BoseB7.lille]
          field_simp
        have hlille_nn : 0 ≤ E.lille := by
          rw [Work.BoseB7.lille_val E hv]; exact fsXp_nonneg hv.t_pos.le
        have h4 : 1 ≤ r * (4 * E.KH * E.aScat) := (div_le_iff₀ (by positivity)).mp hr
        have h5 : 1 ≤ (r * (4 * E.KH * E.aScat)) ^ 2 := one_le_pow₀ h4
        have h5' : 1 ≤ 16 * r ^ 2 * (E.KH * E.aScat) ^ 2 := by nlinarith [h5]
        have hinv : 1 / (E.KH * E.aScat) ^ 2 ≤ 16 * r ^ 2 := by
          rw [div_le_iff₀ (by positivity)]
          linarith [h5']
        have hA : 3 * E.rho * K₀ * E.aScat ≤ (9 / 2) * (E.mu * K₀ * E.aScat) := by
          have h1 : 3 * E.rho ≤ 3 * (3 * E.mu / 2) := by
            linarith [Work.BoseB7.rho_le E hv]
          have h2 : 3 * E.rho * K₀ ≤ 3 * (3 * E.mu / 2) * K₀ :=
            mul_le_mul_of_nonneg_right h1 hK.le
          have h3 : 3 * E.rho * K₀ * E.aScat ≤ 3 * (3 * E.mu / 2) * K₀ * E.aScat :=
            mul_le_mul_of_nonneg_right h2 ha.le
          have h4' : 3 * (3 * E.mu / 2) * K₀ * E.aScat = (9 / 2) * (E.mu * K₀ * E.aScat) := by
            ring
          linarith [h3, h4'.le, h4'.ge]
        have hB : (9 / 2) * (E.mu * K₀ * E.aScat) ≤ r ^ 2 / 8 := by
          rw [hKA]
          have hnn : 0 ≤ (9 / 2) * (K₀ * E.lille) :=
            mul_nonneg (by norm_num) (mul_nonneg hK.le hlille_nn)
          calc (9 / 2) * (K₀ * E.lille / (E.KH * E.aScat) ^ 2)
              = (9 / 2) * (K₀ * E.lille) * (1 / (E.KH * E.aScat) ^ 2) := by ring
            _ ≤ (9 / 2) * (K₀ * E.lille) * (16 * r ^ 2) := mul_le_mul_of_nonneg_left hinv hnn
            _ ≤ (9 / 2) * (1 / 576) * (16 * r ^ 2) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKl (by norm_num))
                  (by positivity)
            _ = r ^ 2 / 8 := by ring
        linarith
    linarith
  linarith

/-- **The kinetic domination for `τ̃`, with the potential density as a
parameter.**  The proof of `arith_tauTilde_ge` shows the stronger
`(9/2)μK₀a ≤ r²/8` (via FS `eq:Close`, `E.rho ≤ 3μ/2`), so the potential term
`3ρK₀a` is dominated for every `ρ ≤ 3μ/2`.  This is the form the honest gate
needs, since the gate is applied at `KzEnvAt E ρ` for `ρ` in the admissible
window. -/
theorem arith_tauTilde_ge_rho (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
      (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) (ρ : ℝ),
      0 ≤ ρ → ρ ≤ 3 * E.mu / 2 → hv.t ≤ t₀ →
      E.aScat * E.KH / (E.s * E.ell) ≤ 1 / 32 → ∀ r : ℝ,
      1 / (4 * E.KH * E.aScat) ≤ r →
        r ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤
          (1 - E.eT) * max (r - (E.s * E.ell)⁻¹) 0 ^ 2
            + E.eT * max (r - (E.d * E.s * E.ell)⁻¹) 0 ^ 2 := by
  obtain ⟨t₀, ht₀pos, ht₀⟩ := Work.BoseK15.exists_tau_params K₀
  refine ⟨t₀, ht₀pos, ?_⟩
  intro Mode _ _ E hv ρ hρ0 hρub ht h16 r hr
  obtain ⟨heT, hKl⟩ := ht₀ E hv ht
  have ha : 0 < E.aScat := hv.a_pos
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have hs : 0 < E.s := by rw [hv.s_eq]; exact fsXp_pos hv.t_pos
  have hell : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hrho : 0 ≤ E.rho := (Work.BoseB7.rho_pos E hv).le
  have heTnn : 0 ≤ E.eT := by rw [hv.eT_eq]; exact fsXp_nonneg hv.t_pos.le
  have h1eT : 0 ≤ 1 - E.eT := by linarith
  have hrnn : 0 ≤ r := le_trans (by positivity) hr
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  -- Step 1: the kinetic threshold
  have hx : (E.s * E.ell)⁻¹ ≤ r / 8 := by
    have hstep : (1 / (E.aScat * E.KH)) * (E.aScat * E.KH / (E.s * E.ell)) ≤
        (1 / (E.aScat * E.KH)) * (1 / 32) :=
      mul_le_mul_of_nonneg_left h16 (by positivity)
    have hL : (1 / (E.aScat * E.KH)) * (E.aScat * E.KH / (E.s * E.ell)) =
        (E.s * E.ell)⁻¹ := by field_simp
    have hR : (1 / (E.aScat * E.KH)) * (1 / 32) = (1 / (4 * (E.KH * E.aScat))) / 8 := by
      field_simp
      ring
    rw [hL, hR] at hstep
    have h4 : 1 / (4 * (E.KH * E.aScat)) ≤ r := by
      convert hr using 2
      ring
    linarith
  -- Step 2: the kinetic gain
  have hmax : 49 * r ^ 2 / 64 ≤ max (r - (E.s * E.ell)⁻¹) 0 ^ 2 :=
    Work.BoseK15.max_sq_lower hx hrnn
  have hRHS : 49 * (1 - E.eT) / 64 * r ^ 2 ≤
      (1 - E.eT) * max (r - (E.s * E.ell)⁻¹) 0 ^ 2
        + E.eT * max (r - (E.d * E.s * E.ell)⁻¹) 0 ^ 2 := by
    have hA : (1 - E.eT) * (49 * r ^ 2 / 64) ≤
        (1 - E.eT) * (max (r - (E.s * E.ell)⁻¹) 0 ^ 2) :=
      mul_le_mul_of_nonneg_left hmax h1eT
    have hB : 0 ≤ E.eT * max (r - (E.d * E.s * E.ell)⁻¹) 0 ^ 2 :=
      mul_nonneg heTnn (sq_nonneg _)
    have hA' : (1 - E.eT) * (49 * r ^ 2 / 64) = 49 * (1 - E.eT) / 64 * r ^ 2 := by ring
    rw [hA'] at hA
    linarith
  -- Step 3: the potential term, with the density `ρ ≤ 3μ/2`
  have hLHS : r ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤ 49 * (1 - E.eT) / 64 * r ^ 2 := by
    have hcoef : (5 / 8 : ℝ) ≤ 49 * (1 - E.eT) / 64 := by linarith
    have hcf : (5 / 8) * r ^ 2 ≤ 49 * (1 - E.eT) / 64 * r ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef hr2
    have hterm : 3 * ρ * K₀ * E.aScat ≤ r ^ 2 / 8 := by
      rcases le_or_gt K₀ 0 with hK | hK
      · have h3 : 3 * ρ * K₀ * E.aScat ≤ 0 := by
          have hpos : 0 ≤ 3 * ρ * E.aScat := by positivity
          nlinarith [hK, hpos]
        linarith
      · have hKA : E.mu * K₀ * E.aScat = K₀ * E.lille / (E.KH * E.aScat) ^ 2 := by
          rw [Work.BoseB7.Q3Env.lille, Work.BoseB7.lille]
          field_simp
        have hlille_nn : 0 ≤ E.lille := by
          rw [Work.BoseB7.lille_val E hv]; exact fsXp_nonneg hv.t_pos.le
        have h4 : 1 ≤ r * (4 * E.KH * E.aScat) := (div_le_iff₀ (by positivity)).mp hr
        have h5 : 1 ≤ (r * (4 * E.KH * E.aScat)) ^ 2 := one_le_pow₀ h4
        have h5' : 1 ≤ 16 * r ^ 2 * (E.KH * E.aScat) ^ 2 := by nlinarith [h5]
        have hinv : 1 / (E.KH * E.aScat) ^ 2 ≤ 16 * r ^ 2 := by
          rw [div_le_iff₀ (by positivity)]
          linarith [h5']
        have hB : (9 / 2) * (E.mu * K₀ * E.aScat) ≤ r ^ 2 / 8 := by
          rw [hKA]
          have hnn : 0 ≤ (9 / 2) * (K₀ * E.lille) :=
            mul_nonneg (by norm_num) (mul_nonneg hK.le hlille_nn)
          calc (9 / 2) * (K₀ * E.lille / (E.KH * E.aScat) ^ 2)
              = (9 / 2) * (K₀ * E.lille) * (1 / (E.KH * E.aScat) ^ 2) := by ring
            _ ≤ (9 / 2) * (K₀ * E.lille) * (16 * r ^ 2) := mul_le_mul_of_nonneg_left hinv hnn
            _ ≤ (9 / 2) * (1 / 576) * (16 * r ^ 2) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKl (by norm_num))
                  (by positivity)
            _ = r ^ 2 / 8 := by ring
        have hle : 3 * ρ * K₀ * E.aScat ≤ (9 / 2) * (E.mu * K₀ * E.aScat) := by
          have h7 : 3 * ρ ≤ (9 / 2) * E.mu := by linarith
          have h8 : 3 * ρ * K₀ ≤ (9 / 2) * E.mu * K₀ :=
            mul_le_mul_of_nonneg_right h7 hK.le
          have h9 : 3 * ρ * K₀ * E.aScat ≤ (9 / 2) * E.mu * K₀ * E.aScat :=
            mul_le_mul_of_nonneg_right h8 ha.le
          linarith [h9]
        linarith
    linarith
  linarith

end Work.BoseGateFS
