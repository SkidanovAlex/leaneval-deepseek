import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.arith_tau_ge` — the kinetic symbol dominates `r²/2 + 3ρK₀a`

FS `def:tau`'s kinetic symbol is

`τ(k) = (1 − ε_T)[‖k‖ − (2sℓ)⁻¹]₊² + ε_T[‖k‖ − (2dsℓ)⁻¹]₊²`

(`Work.BoseB4.tauFun`, and `K15Input.tau_eq` identifies `E.tau` with it).  The
chapter `BoseB7` needs the lower bound

`r²/2 + 3ρ_zK₀a ≤ τ(r)`  for `r ≥ (4K_Ha)⁻¹`

at FS's parameter point (`FSParamsView E`), i.e. that the kinetic symbol beats
the potential energy `3ρ_zK₀a` in the region where Bogoliubov's `α` is small.
This is what makes `𝒜 ≥ |k|²/2` on `P_H^q` (the smallness list N1, item S11 of
`BOSE_3Q_LEAD.md`).

## The mathematics

Let `x = (2sℓ)⁻¹`, `y = (2dsℓ)⁻¹`, `M := max K₀ 0`.

* **The kinetic gain.**  `(2sℓ)⁻¹ ≤ (32K_Ha)⁻¹ ≤ r/8`: the hypothesis
  `aK_H/(sℓ) ≤ 1/16` gives `(sℓ)⁻¹ ≤ (16aK_H)⁻¹`, half of which is `(2sℓ)⁻¹`,
  and `r ≥ (4K_Ha)⁻¹` makes the latter `≤ r/8`.  The second threshold `y` is
  *larger* than `x` (`d = X⁶ ≤ 1` for `t ≤ 1`), so it is discarded: the second
  summand of `τ` is nonnegative and contributes nothing to the lower bound.
  Hence, since `eT ≥ 0`,

  `τ(r) ≥ (1 − eT)(r − x)² ≥ (1 − eT)(7r/8)² = (49(1 − eT)/64)·r²`.

* **The potential.**  `ρ_z ≤ (3/2)μ` (FS `eq:Close`, `FSParamsVals.rho_le`), so
  `3ρ_zK₀a ≤ (9/2)μK₀a`, and `μa(K_Ha)² = 𝓁` (FS `eq:DefLille`) with
  `(K_Ha)⁻² ≤ 16r²`, so `3ρ_zK₀a ≤ 72K₀𝓁·r²`.  Fixing `t₀` so that `𝓁 ≤ 1/576`
  (times `K₀`; for `K₀ ≤ 0` the term is negative and needs nothing) gives
  `3ρ_zK₀a ≤ r²/8`.

* **Conclusion.**  `r²/2 + r²/8 = 5r²/8 ≤ (49(1 − eT)/64)r²`, since fixing `t₀`
  so that `eT ≤ 9/49` gives `1 − eT ≥ 40/49` and `49·(40/49)/64 = 5/8` exactly.

Both thresholds are met by FS's monomials: `ε_T = X^{23/4} → 0` and
`𝓁 = (μa³)K_H² = X^{97/2} → 0` as the diluteness `t → 0⁺`, so `t₀` exists (it
depends on `K₀`, which is exactly the quantifier order of the statement).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseK15

open Work.BoseBox

/-- **The `fsXp` threshold lemma.**  For `C > 0` and `c > 0` there is `t₀ ∈ (0,1]`
with `fsXp t c ≤ C` for every `0 < t ≤ t₀`.  Indeed `fsXp t c = t^{c/323}` is
increasing on `(0,∞)` with exponent `c/323 > 0`, so `t₀ = min 1 (C^{323/c})`
works.  (Positivity of the exponent is essential; for `c < 0` the monomial blows
up as `t → 0⁺`.) -/
lemma exists_fsXp_le (C c : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ ≤ 1 ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → fsXp t c ≤ C := by
  refine ⟨min 1 (C ^ (323 / c)), lt_min one_pos (Real.rpow_pos_of_pos hC _),
    min_le_left _ _, ?_⟩
  intro t ht ht0
  have hle : t ≤ C ^ (323 / c) := le_trans ht0 (min_le_right _ _)
  have h1 : fsXp t c ≤ (C ^ (323 / c)) ^ (c / 323) := by
    rw [fsXp]
    exact Real.rpow_le_rpow ht.le hle (by positivity)
  have h2 : (C ^ (323 / c)) ^ (c / 323) = C := by
    rw [← Real.rpow_mul hC.le]
    have h3 : 323 / c * (c / 323) = 1 := by field_simp
    rw [h3, Real.rpow_one]
  exact le_trans h1 h2.le

/-- **The two thresholds of FS's parameters.**  At the parameter point
`FSParamsView E` with diluteness `t ≤ t₀` (small enough) one has
`ε_T ≤ 9/49` and `K₀𝓁 ≤ 1/576`.  The first is `ε_T = X^{23/4}`, the second
`𝓁 = X^{97/2}` (`FSParamsVals.lille_val`); for `K₀ ≤ 0` the second is free
because `𝓁 ≥ 0`. -/
lemma exists_tau_params (K₀ : ℝ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
      (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
      hv.t ≤ t₀ → E.eT ≤ 9 / 49 ∧ K₀ * E.lille ≤ 1 / 576 := by
  have hM : 0 < max K₀ 0 + 1 := by have := le_max_right K₀ 0; linarith
  obtain ⟨t₁, ht₁pos, _, ht₁⟩ :=
    exists_fsXp_le (C := (9 / 49 : ℝ)) (c := (23 / 4 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨t₂, ht₂pos, _, ht₂⟩ :=
    exists_fsXp_le (C := 1 / (576 * (max K₀ 0 + 1))) (c := (97 / 2 : ℝ)) (by positivity)
      (by norm_num)
  refine ⟨min t₁ t₂, lt_min ht₁pos ht₂pos, ?_⟩
  intro Mode _ _ E hv ht
  have ht1 : hv.t ≤ t₁ := le_trans ht (min_le_left _ _)
  have ht2 : hv.t ≤ t₂ := le_trans ht (min_le_right _ _)
  have hA : E.eT ≤ 9 / 49 := by rw [hv.eT_eq]; exact ht₁ hv.t hv.t_pos ht1
  refine ⟨hA, ?_⟩
  have hlille : E.lille ≤ 1 / (576 * (max K₀ 0 + 1)) := by
    rw [Work.BoseB7.lille_val E hv]; exact ht₂ hv.t hv.t_pos ht2
  have hlille_nn : 0 ≤ E.lille := by
    rw [Work.BoseB7.lille_val E hv]; exact fsXp_nonneg hv.t_pos.le
  rcases le_or_gt K₀ 0 with hK | hK
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hK hlille_nn) (by norm_num)
  · have h1 : K₀ * E.lille ≤ K₀ * (1 / (576 * (max K₀ 0 + 1))) :=
      mul_le_mul_of_nonneg_left hlille hK.le
    have h2 : K₀ * (1 / (576 * (max K₀ 0 + 1))) ≤ 1 / 576 := by
      have hKM : K₀ ≤ max K₀ 0 + 1 := by have := le_max_left K₀ 0; linarith
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      have e : (1 / 576 : ℝ) * (576 * (max K₀ 0 + 1)) = max K₀ 0 + 1 := by ring
      rw [e]; exact hKM
    linarith

/-- **The one-variable kinetic gain.**  If `x ≤ r/8` and `r ≥ 0` then
`(max (r − x) 0)² ≥ (7r/8)² = 49r²/64`. -/
lemma max_sq_lower {r x : ℝ} (hx : x ≤ r / 8) (hr : 0 ≤ r) :
    49 * r ^ 2 / 64 ≤ max (r - x) 0 ^ 2 := by
  have h7 : 0 ≤ 7 * r / 8 := by linarith
  have hy : 0 ≤ r - x := by linarith
  rw [max_eq_left hy]
  nlinarith [hx, h7, hy]

theorem arith_tau_ge (K₀ : ℝ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
      (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
      hv.t ≤ t₀ → E.aScat * E.KH / (E.s * E.ell) ≤ 1 / 16 → ∀ r : ℝ,
      1 / (4 * E.KH * E.aScat) ≤ r →
        r ^ 2 / 2 + 3 * E.rho * K₀ * E.aScat ≤
          (1 - E.eT) * max (r - (2 * E.s * E.ell)⁻¹) 0 ^ 2
            + E.eT * max (r - (2 * E.d * E.s * E.ell)⁻¹) 0 ^ 2 := by
  obtain ⟨t₀, ht₀pos, ht₀⟩ := exists_tau_params K₀
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
  -- **Step 1: the kinetic threshold `(2sℓ)⁻¹ ≤ r/8`.**
  have hx : (2 * E.s * E.ell)⁻¹ ≤ r / 8 := by
    have hstep : (1 / (2 * (E.aScat * E.KH))) * (E.aScat * E.KH / (E.s * E.ell)) ≤
        (1 / (2 * (E.aScat * E.KH))) * (1 / 16) :=
      mul_le_mul_of_nonneg_left h16 (by positivity)
    have hL : (1 / (2 * (E.aScat * E.KH))) * (E.aScat * E.KH / (E.s * E.ell)) =
        (2 * E.s * E.ell)⁻¹ := by field_simp
    have hR : (1 / (2 * (E.aScat * E.KH))) * (1 / 16) = (1 / (4 * (E.KH * E.aScat))) / 8 := by
      field_simp
      ring
    rw [hL, hR] at hstep
    have h4 : 1 / (4 * (E.KH * E.aScat)) ≤ r := by
      convert hr using 2
      ring
    linarith
  -- **Step 2: `τ(r) ≥ (49(1 − eT)/64)·r²`.**
  have hmax : 49 * r ^ 2 / 64 ≤ max (r - (2 * E.s * E.ell)⁻¹) 0 ^ 2 := max_sq_lower hx hrnn
  have hRHS : 49 * (1 - E.eT) / 64 * r ^ 2 ≤
      (1 - E.eT) * max (r - (2 * E.s * E.ell)⁻¹) 0 ^ 2
        + E.eT * max (r - (2 * E.d * E.s * E.ell)⁻¹) 0 ^ 2 := by
    have hA : (1 - E.eT) * (49 * r ^ 2 / 64) ≤
        (1 - E.eT) * (max (r - (2 * E.s * E.ell)⁻¹) 0 ^ 2) :=
      mul_le_mul_of_nonneg_left hmax h1eT
    have hB : 0 ≤ E.eT * max (r - (2 * E.d * E.s * E.ell)⁻¹) 0 ^ 2 :=
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

end Work.BoseK15
