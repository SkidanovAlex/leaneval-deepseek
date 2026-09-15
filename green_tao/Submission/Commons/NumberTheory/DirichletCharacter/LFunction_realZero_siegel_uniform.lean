/-
Siegel's uniform real zero-free region for Dirichlet `L`-functions.

Target: for every `ε > 0` there is `C = C(ε) > 0` such that every real zero `β ∈ (0,1)` of
`L(·,χ)`, for a primitive real (quadratic) non-principal Dirichlet character `χ` modulo `N`,
satisfies `1 - β ≥ C · N^{-ε}`.

Proof outline (Montgomery–Vaughan, *Multiplicative Number Theory I*, §11.2):
* Let `δ = ε/100`.  Consider the set of quadratic primitive characters `χ₁ ≠ 1` having a real zero
  in `[1 - δ, 1)`.
* If the set is empty then no such `χ` has a real zero in `[1-δ,1)`, so `1 - β ≥ δ ≥ δ N^{-ε}`.
* Otherwise fix `χ₁` (conductor `M`, zero `β₁`).  For a quadratic primitive `χ` with `χχ₁ ≠ 1`,
  Estermann's lemma (`estermann_positivity`) applied to `f(s) = L(s,χ)L(s,χ₁)L(s,χχ₁)` at
  `σ = β₁` (where `f(β₁) = 0`) gives `‖L(1,χ)‖ ≥ c·N^{-6δ-2λ}` with `c > 0` depending only on
  `ε, M, χ₁, β₁`.
* If `χχ₁ = 1` then `χ = χ₁`; then `‖L(1,χ)‖ = ‖L(1,χ₁)‖ > 0` is a fixed positive number
  (non-vanishing at `s = 1`, `DirichletCharacter.LFunction_apply_one_ne_zero`), used directly.
* `‖L(1,χ)‖ ≥ c N^{-η}` together with the mean value theorem and the uniform bound
  `‖L'(σ,χ)‖ ≤ C (log 2N)²` gives `1 - β ≥ C(ε) N^{-ε}`.

Analytic inputs in the shared commons: `estermann_positivity`,
`LFunction_quadratic_triple_LSeries_coeffs_mixed`, `LFunction_norm_half_plane`,
`LFunction_deriv_bound_near_one_uniform`, `riemannZeta_neg_of_Ioo_half_one`,
`riemannZeta_bound_sphere_two`, `changeLevel_congr`.
-/
import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.estermann_positivity
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_quadratic_triple_LSeries_coeffs_mixed
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_deriv_bound_near_one_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.changeLevel_congr
import Submission.Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one
import Submission.Commons.NumberTheory.Zeta.riemannZeta_bound_sphere_two

open Complex DirichletCharacter Filter
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

set_option maxHeartbeats 3200000

/-! ## Norm bounds on the disc `|z - 2| ≤ 3/2` -/

private lemma thick_re (z : ℂ) (hz : z ∈ Metric.closedBall (2 : ℂ) (3 / 2)) :
    (1 / 2 : ℝ) ≤ z.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h2 : (z - 2).re = z.re - 2 := by simp
  have h : -(z - 2).re ≤ ‖z - 2‖ := by
    have := Complex.abs_re_le_norm (z - 2)
    rw [abs_le] at this
    linarith [this.1]
  linarith

private lemma thick_norm (z : ℂ) (hz : z ∈ Metric.closedBall (2 : ℂ) (3 / 2)) :
    ‖z‖ ≤ 7 / 2 := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h : z = (z - 2) + 2 := by ring
  rw [h]
  calc ‖(z - 2) + 2‖ ≤ ‖z - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
    _ = ‖z - 2‖ + 2 := by rw [Complex.norm_two]
    _ ≤ 3 / 2 + 2 := by linarith
    _ = 7 / 2 := by norm_num

private lemma norm_LFunction_disc {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {z : ℂ} (hz : z ∈ Metric.closedBall (2 : ℂ) (3 / 2)) :
    ‖LFunction χ z‖ ≤ 14 * (N : ℝ) := by
  have hre := thick_re z hz
  have hrepos : 0 < z.re := by linarith
  have hnorm := thick_norm z hz
  have hb := LFunction_norm_half_plane χ hχ hrepos
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : 2 * (N : ℝ) * ‖z‖ / z.re ≤ 14 * (N : ℝ) := by
    rw [div_le_iff₀ hrepos]
    nlinarith [hnorm, hN, hre]
  linarith

/-- A non-trivial character forces its level to be at least `2`. -/
private lemma two_le_level {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    2 ≤ N := by
  rcases Nat.lt_or_ge N 2 with h | h
  · have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hN1 : N = 1 := by omega
    subst hN1
    exact absurd (Subsingleton.elim χ 1) hχ
  · exact h

/-! ## Exponent helpers -/

private lemma natPow_rpow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (e : ℝ) :
    (x ^ k) ^ e = x ^ ((k : ℝ) * e) := by
  rw [← Real.rpow_natCast x k, ← Real.rpow_mul hx (k : ℝ) e]

private lemma rpow_natPow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (e : ℝ) :
    (x ^ e) ^ k = x ^ (e * (k : ℝ)) := by
  rw [← Real.rpow_natCast (x ^ e) k, ← Real.rpow_mul hx e (k : ℝ)]

/-! ## The Estermann input for `χ ≠ χ₁`

Given the auxiliary Siegel character `χ₁` (conductor `M`, real zero `β₁ ∈ [1-δ,1)`) and a
quadratic primitive `χ` of conductor `N` with `χχ₁ ≠ 1`, Estermann's lemma applied to
`f(s) = L(s,χ)L(s,χ₁)L(s,χχ₁)` at `σ = β₁` gives a uniform lower bound for `‖L(1,χ)‖`.

The two auxiliary `L`-values `L(1,χ₁)` and `L(1,χχ₁)` are bounded trivially (uniformly in `χ`)
by `144 log(2M)` and `144 log(2NM)`; the logarithm in the second factor costs a factor
`N^{-2λ}`, which is absorbed in the exponent `6δ + 2λ`. -/

private lemma L_one_lower_of_aux {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M)
    (hχ₁sq : χ₁ * χ₁ = 1) (hχ₁prim : χ₁.IsPrimitive) (hχ₁ne : χ₁ ≠ 1)
    {β₁ δ lam : ℝ} (hβ₁lo : 1 - δ ≤ β₁) (hβ₁hi : β₁ < 1) (hδpos : 0 < δ) (hδ20 : δ ≤ 1 / 20)
    (hlampos : 0 < lam)
    (hβ₁z : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχsq : χ * χ = 1) (hχne : χ ≠ 1)
    (hprod : (χ.changeLevel (Nat.dvd_mul_right N M)) *
        (χ₁.changeLevel (Nat.dvd_mul_left M N)) ≠ 1) :
    (1 / 4) * (1 - β₁) * (14 : ℝ) ^ (-(9 * δ)) * (lam / 144) ^ 2 *
      (M : ℝ) ^ (-(6 * δ + 4 * lam)) * (N : ℝ) ^ (-(6 * δ + 2 * lam)) ≤
      ‖DirichletCharacter.LFunction χ 1‖ := by
  have hM2 : 2 ≤ M := two_le_level χ₁ hχ₁ne
  have hN2 : 2 ≤ N := two_le_level χ hχne
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 2) hM2)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 2) hN2)
  have hM2r : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le zero_lt_one hM1
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hNM2 : 2 ≤ N * M := Nat.le_trans (by norm_num : 2 ≤ 2 * 2) (Nat.mul_le_mul hN2 hM2)
  have hNM2r : (2 : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    have : ((2:ℕ) : ℝ) ≤ ((N*M : ℕ) : ℝ) := by exact_mod_cast hNM2
    simpa using this
  have hβ₁half : (1 : ℝ) / 2 < β₁ := by linarith
  -- ### the triple product and its Estermann input
  set χc : DirichletCharacter ℂ (N * M) :=
    (χ.changeLevel (Nat.dvd_mul_right N M)) *
      (χ₁.changeLevel (Nat.dvd_mul_left M N)) with hχc
  have hχcne : χc ≠ 1 := by rw [hχc]; exact hprod
  obtain ⟨r, hr, hr1, habsc, hFser⟩ :=
    LFunction_quadratic_triple_LSeries_coeffs_mixed χ χ₁ hχsq hχ₁sq
  obtain ⟨K, hKpos, hK⟩ := Commons.NumberTheory.Zeta.riemannZeta_bound_sphere_two
  obtain ⟨c0, hc0neg, hc0eq⟩ :=
    Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one hβ₁half hβ₁hi
  set f : ℂ → ℂ := fun s => LFunction χ s * LFunction χ₁ s * LFunction χc s with hf
  have hfa : AnalyticOnNhd ℂ f (Metric.closedBall 2 (3 / 2)) := by
    intro z _
    simp only [hf]
    exact (((differentiable_LFunction hχne).analyticAt z).mul
        ((differentiable_LFunction hχ₁ne).analyticAt z)).mul
      ((differentiable_LFunction hχcne).analyticAt z)
  set Mbound : ℝ := (14 : ℝ) ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 with hMb
  have hMb1 : 1 ≤ Mbound := by
    rw [hMb]
    have hNM1 : (1 : ℝ) ≤ (N : ℝ) * (M : ℝ) := one_le_mul_of_one_le_of_one_le hN1 hM1
    nlinarith [hNM1]
  have hfb : ∀ z ∈ Metric.closedBall (2 : ℂ) (3 / 2), ‖f z‖ ≤ Mbound := by
    intro z hz
    have h1 := norm_LFunction_disc χ hχne hz
    have h2 := norm_LFunction_disc χ₁ hχ₁ne hz
    have h3 := norm_LFunction_disc χc hχcne hz
    have hNMcast : ((N * M : ℕ) : ℝ) = (N : ℝ) * (M : ℝ) := by push_cast; ring
    rw [hNMcast] at h3
    have step1 : ‖LFunction χ z‖ * ‖LFunction χ₁ z‖ ≤ (14 * (N:ℝ)) * (14 * (M:ℝ)) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have step2 : ‖LFunction χ z‖ * ‖LFunction χ₁ z‖ * ‖LFunction χc z‖ ≤
        (14 * (N:ℝ)) * (14 * (M:ℝ)) * (14 * ((N:ℝ) * (M:ℝ))) :=
      mul_le_mul step1 h3 (norm_nonneg _) (by positivity)
    simp only [hf, norm_mul, hMb]
    calc ‖LFunction χ z‖ * ‖LFunction χ₁ z‖ * ‖LFunction χc z‖
        ≤ (14 * (N:ℝ)) * (14 * (M:ℝ)) * (14 * ((N:ℝ) * (M:ℝ))) := step2
      _ = (14 : ℝ) ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 := by ring
  -- The Dirichlet series identity, in the form needed by Estermann's lemma.
  have hF : ∀ s : ℂ, 1 < s.re →
      riemannZeta s * f s = ∑' n : ℕ, (r n : ℂ) * (n : ℂ) ^ (-s) := by
    intro s hs
    rw [show (∑' n : ℕ, (r n : ℂ) * (n : ℂ) ^ (-s)) =
        LSeries (fun n : ℕ => (r n : ℂ)) s from ?_]
    · simp only [hf]
      exact hFser s hs
    · rw [LSeries]
      refine tsum_congr (fun n => ?_)
      rcases eq_or_ne n 0 with rfl | hn
      · have hs0 : s ≠ 0 := by
          intro h; rw [h] at hs; exact absurd hs (by norm_num)
        simp [LSeries.term_zero, Complex.cpow_neg, Complex.zero_cpow hs0]
      · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, Complex.cpow_neg]
  have hfσ : 0 ≤ (f β₁).re := by
    simp only [hf]
    rw [hβ₁z]
    simp
  have hE := estermann_positivity hKpos hMb1 (by linarith : (19:ℝ)/20 ≤ β₁) hβ₁hi
    hfa hfb hK ⟨c0, hc0neg, hc0eq⟩ hr hr1 habsc hF hfσ
  -- ### bounds for the two remaining factors
  have hlogMpos : 0 < Real.log (2 * (M : ℝ)) := by
    apply Real.log_pos; linarith
  have hlogNMpos : 0 < Real.log (2 * ((N * M : ℕ) : ℝ)) := by
    apply Real.log_pos
    have : (2:ℝ) ≤ ((N*M:ℕ) : ℝ) := by exact_mod_cast hNM2
    linarith
  have hNMlog : (2:ℝ) * ((N * M : ℕ) : ℝ) = (2:ℝ) * (N : ℝ) * (M : ℝ) := by
    push_cast; ring
  have hB1 : ‖LFunction χ₁ 1‖ ≤ 144 * Real.log (2 * (M : ℝ)) := by
    have h5 : 0 < 5 / (4 * Real.log (2 * (M:ℝ))) :=
      div_pos (by norm_num) (mul_pos (by norm_num) hlogMpos)
    have h := LFunction_norm_le_log_near_one χ₁ hχ₁ne (z := 1)
      (by rw [Complex.one_re]; linarith) (by norm_num)
    simpa using h
  have hB2 : ‖LFunction χc 1‖ ≤ 144 * Real.log (2 * ((N * M : ℕ) : ℝ)) := by
    have h5 : 0 < 5 / (4 * Real.log (2 * ((N*M:ℕ):ℝ))) :=
      div_pos (by norm_num) (mul_pos (by norm_num) hlogNMpos)
    have h := LFunction_norm_le_log_near_one χc hχcne (z := 1)
      (by rw [Complex.one_re]; linarith) (by norm_num)
    simpa using h
  have hB1log : 144 * Real.log (2 * (M : ℝ)) ≤ 144 * (M : ℝ) ^ (2 * lam) / lam := by
    have hlog : Real.log (2 * (M:ℝ)) ≤ (2 * (M:ℝ)) ^ lam / lam :=
      Real.log_le_rpow_div (by positivity) hlampos
    have h2M : ((2:ℝ) * (M:ℝ)) ^ lam ≤ ((M:ℝ)^2) ^ lam :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [hM2r]) hlampos.le
    have hM2lam : ((M:ℝ)^2) ^ lam = (M:ℝ) ^ (2 * lam) := by
      rw [natPow_rpow (M:ℝ) hMpos.le 2 lam]; norm_num
    have hfin : Real.log (2 * (M:ℝ)) ≤ (M:ℝ) ^ (2 * lam) / lam := by
      refine le_trans hlog ?_
      rw [div_le_div_iff_of_pos_right hlampos]
      exact le_trans h2M (le_of_eq hM2lam)
    calc 144 * Real.log (2 * (M:ℝ)) ≤ 144 * ((M:ℝ)^(2*lam) / lam) := by linarith
      _ = 144 * (M : ℝ) ^ (2 * lam) / lam := by ring
  have hB2log : 144 * Real.log (2 * ((N * M : ℕ) : ℝ)) ≤
      144 * (N:ℝ) ^ (2 * lam) * (M:ℝ) ^ (2 * lam) / lam := by
    have hlog : Real.log (2 * ((N*M:ℕ):ℝ)) ≤ (2 * ((N*M:ℕ):ℝ)) ^ lam / lam :=
      Real.log_le_rpow_div (by positivity) hlampos
    have h2NM : ((2:ℝ) * (N:ℝ) * (M:ℝ)) ≤ ((N:ℝ) * (M:ℝ))^2 := by
      nlinarith [hNM2r]
    have hstep : ((2:ℝ) * (N:ℝ) * (M:ℝ)) ^ lam ≤ ((N:ℝ) * (M:ℝ)) ^ (2 * lam) := by
      calc ((2:ℝ) * (N:ℝ) * (M:ℝ)) ^ lam ≤ (((N:ℝ) * (M:ℝ))^2) ^ lam :=
            Real.rpow_le_rpow (by positivity) h2NM hlampos.le
        _ = ((N:ℝ) * (M:ℝ)) ^ (2 * lam) := by
            rw [natPow_rpow ((N:ℝ)*(M:ℝ)) (by positivity) 2 lam]; norm_num
    have hsplit : ((N:ℝ) * (M:ℝ)) ^ (2 * lam) =
        (N:ℝ) ^ (2*lam) * (M:ℝ) ^ (2*lam) := by
      rw [Real.mul_rpow hNpos.le hMpos.le]
    have hfin : Real.log (2 * ((N*M:ℕ):ℝ)) ≤
        (N:ℝ) ^ (2*lam) * (M:ℝ) ^ (2*lam) / lam := by
      rw [hNMlog] at hlog ⊢
      refine le_trans hlog ?_
      rw [div_le_div_iff_of_pos_right hlampos]
      exact le_trans hstep (le_of_eq hsplit)
    calc 144 * Real.log (2 * ((N*M:ℕ):ℝ))
        ≤ 144 * ((N:ℝ)^(2*lam) * (M:ℝ)^(2*lam) / lam) := by linarith
      _ = 144 * (N:ℝ) ^ (2*lam) * (M:ℝ) ^ (2*lam) / lam := by ring
  -- ### the exponent bookkeeping
  have hM4 : ((M:ℝ) ^ (2 * lam)) ^ 2 = (M:ℝ) ^ (4 * lam) := by
    rw [rpow_natPow (M:ℝ) hMpos.le 2 (2*lam)]
    ring_nf
  have hMc : (M:ℝ) ^ (-(6 * δ + 4 * lam)) * (M:ℝ) ^ (4 * lam) = (M:ℝ) ^ (-(6 * δ)) := by
    rw [← Real.rpow_add hMpos]
    congr 1; ring
  have hNc : (N:ℝ) ^ (-(6 * δ + 2 * lam)) * (N:ℝ) ^ (2 * lam) = (N:ℝ) ^ (-(6 * δ)) := by
    rw [← Real.rpow_add hNpos]
    congr 1; ring
  have hkey : ((1 / 4) * (1 - β₁) * (14:ℝ) ^ (-(9*δ)) * (lam / 144)^2 *
        (M:ℝ) ^ (-(6*δ + 4*lam)) * (N:ℝ) ^ (-(6*δ + 2*lam))) *
        (144 * (M:ℝ) ^ (2*lam) / lam) *
        (144 * (N:ℝ) ^ (2*lam) * (M:ℝ) ^ (2*lam) / lam)
      = (1/4) * (1 - β₁) * (14:ℝ) ^ (-(9*δ)) * (M:ℝ) ^ (-(6*δ)) * (N:ℝ) ^ (-(6*δ)) := by
    have hfac : ((1 / 4) * (1 - β₁) * (14:ℝ) ^ (-(9*δ)) * (lam / 144)^2 *
          (M:ℝ) ^ (-(6*δ + 4*lam)) * (N:ℝ) ^ (-(6*δ + 2*lam))) *
          (144 * (M:ℝ) ^ (2*lam) / lam) *
          (144 * (N:ℝ) ^ (2*lam) * (M:ℝ) ^ (2*lam) / lam)
        = ((1/4) * (1 - β₁) * (14:ℝ) ^ (-(9*δ))) *
          ((M:ℝ) ^ (-(6*δ + 4*lam)) * ((M:ℝ) ^ (2*lam))^2) *
          ((N:ℝ) ^ (-(6*δ + 2*lam)) * ((N:ℝ) ^ (2*lam))) := by
      field_simp <;> ring
    rw [hfac, hM4, hMc, hNc]
  -- ### the Mbound collapse
  have hMbcol : (14:ℝ) ^ (-(9*δ)) * (N:ℝ) ^ (-(6*δ)) * (M:ℝ) ^ (-(6*δ)) ≤
      Mbound ^ (-(3 * (1 - β₁))) := by
    rw [hMb]
    have hA : ((14:ℝ)^3 * ((N:ℝ)*(M:ℝ))^2) ^ (-(3*(1-β₁))) =
        ((14:ℝ)^3) ^ (-(3*(1-β₁))) * (((N:ℝ)*(M:ℝ))^2) ^ (-(3*(1-β₁))) :=
      Real.mul_rpow (by positivity) (by positivity)
    rw [hA]
    have h1 : ((14:ℝ)^3) ^ (-(3*(1-β₁))) = (14:ℝ) ^ (-(9*(1-β₁))) := by
      rw [natPow_rpow (14:ℝ) (by norm_num) 3 (-(3*(1-β₁)))]
      rw [show ((3:ℕ):ℝ) * (-(3*(1-β₁))) = -(9*(1-β₁)) by push_cast; ring]
    rw [h1]
    have h2 : (((N:ℝ)*(M:ℝ))^2) ^ (-(3*(1-β₁))) = ((N:ℝ)*(M:ℝ)) ^ (-(6*(1-β₁))) := by
      rw [natPow_rpow ((N:ℝ)*(M:ℝ)) (by positivity) 2 (-(3*(1-β₁)))]
      rw [show ((2:ℕ):ℝ) * (-(3*(1-β₁))) = -(6*(1-β₁)) by push_cast; ring]
    rw [h2]
    have h3 : ((N:ℝ)*(M:ℝ)) ^ (-(6*(1-β₁))) =
        (N:ℝ) ^ (-(6*(1-β₁))) * (M:ℝ) ^ (-(6*(1-β₁))) :=
      Real.mul_rpow hNpos.le hMpos.le
    rw [h3]
    have h4 : (14:ℝ) ^ (-(9*δ)) ≤ (14:ℝ) ^ (-(9*(1-β₁))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h5 : (N:ℝ) ^ (-(6*δ)) ≤ (N:ℝ) ^ (-(6*(1-β₁))) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h6 : (M:ℝ) ^ (-(6*δ)) ≤ (M:ℝ) ^ (-(6*(1-β₁))) :=
      Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    calc (14:ℝ) ^ (-(9*δ)) * (N:ℝ) ^ (-(6*δ)) * (M:ℝ) ^ (-(6*δ))
        ≤ (14:ℝ) ^ (-(9*(1-β₁))) * (N:ℝ) ^ (-(6*(1-β₁))) * (M:ℝ) ^ (-(6*(1-β₁))) := by
          apply mul_le_mul (mul_le_mul h4 h5 (by positivity) (by positivity)) h6 (by positivity)
          exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ = (14:ℝ) ^ (-(9*(1-β₁))) * ((N:ℝ) ^ (-(6*(1-β₁))) * (M:ℝ) ^ (-(6*(1-β₁)))) := by ring
  have hΛnonneg : 0 ≤ (1 / 4) * (1 - β₁) * (14:ℝ) ^ (-(9*δ)) * (lam / 144)^2 *
      (M:ℝ) ^ (-(6*δ + 4*lam)) * (N:ℝ) ^ (-(6*δ + 2*lam)) := by positivity
  have hXnonneg : 0 ≤ 144 * (M:ℝ) ^ (2*lam) / lam := by positivity
  have hre : (f 1).re ≤ ‖LFunction χ 1‖ * (144 * Real.log (2 * (M:ℝ))) *
      (144 * Real.log (2 * ((N*M:ℕ):ℝ))) := by
    have h0 : (f 1).re ≤ ‖f 1‖ := Complex.re_le_norm _
    rw [hf, norm_mul, norm_mul] at h0
    refine le_trans h0 ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hB1 (norm_nonneg _)) hB2 (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (by positivity))
  have hMbstep : (1/4) * (1 - β₁) * (14:ℝ) ^ (-(9*δ)) * (M:ℝ) ^ (-(6*δ)) *
      (N:ℝ) ^ (-(6*δ)) ≤ (1/4) * (1 - β₁) * Mbound ^ (-(3 * (1 - β₁))) := by
    have h2 : (1/4) * (1 - β₁) * (14:ℝ) ^ (-(9*δ)) * (M:ℝ)^(-(6*δ)) * (N:ℝ)^(-(6*δ))
        = (1/4) * (1 - β₁) * ((14:ℝ)^(-(9*δ)) * (N:ℝ)^(-(6*δ)) * (M:ℝ)^(-(6*δ))) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left hMbcol (by positivity)
  have hB1Bpos : 0 < 144 * Real.log (2 * (M:ℝ)) := mul_pos (by norm_num) hlogMpos
  have hB2Bpos : 0 < 144 * Real.log (2 * ((N*M:ℕ):ℝ)) := mul_pos (by norm_num) hlogNMpos
  have hchain : ((1 / 4) * (1 - β₁) * (14:ℝ) ^ (-(9*δ)) * (lam / 144)^2 *
      (M:ℝ) ^ (-(6*δ + 4*lam)) * (N:ℝ) ^ (-(6*δ + 2*lam))) *
      (144 * Real.log (2 * (M:ℝ))) * (144 * Real.log (2 * ((N*M:ℕ):ℝ)))
      ≤ ‖LFunction χ 1‖ * (144 * Real.log (2 * (M:ℝ))) *
        (144 * Real.log (2 * ((N*M:ℕ):ℝ))) := by
    have h1 : ((1 / 4) * (1 - β₁) * (14:ℝ) ^ (-(9*δ)) * (lam / 144)^2 *
        (M:ℝ) ^ (-(6*δ + 4*lam)) * (N:ℝ) ^ (-(6*δ + 2*lam))) *
        (144 * Real.log (2 * (M:ℝ))) * (144 * Real.log (2 * ((N*M:ℕ):ℝ)))
        ≤ ((1 / 4) * (1 - β₁) * (14:ℝ) ^ (-(9*δ)) * (lam / 144)^2 *
        (M:ℝ) ^ (-(6*δ + 4*lam)) * (N:ℝ) ^ (-(6*δ + 2*lam))) *
        (144 * (M:ℝ)^(2*lam) / lam) * (144 * Real.log (2 * ((N*M:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB1log hΛnonneg) hB2Bpos.le
    have h2 : ((1 / 4) * (1 - β₁) * (14:ℝ) ^ (-(9*δ)) * (lam / 144)^2 *
        (M:ℝ) ^ (-(6*δ + 4*lam)) * (N:ℝ) ^ (-(6*δ + 2*lam))) *
        (144 * (M:ℝ)^(2*lam) / lam) * (144 * Real.log (2 * ((N*M:ℕ):ℝ)))
        ≤ ((1 / 4) * (1 - β₁) * (14:ℝ) ^ (-(9*δ)) * (lam / 144)^2 *
        (M:ℝ) ^ (-(6*δ + 4*lam)) * (N:ℝ) ^ (-(6*δ + 2*lam))) *
        (144 * (M:ℝ)^(2*lam) / lam) * (144 * (N:ℝ)^(2*lam) * (M:ℝ)^(2*lam) / lam) :=
      mul_le_mul_of_nonneg_left hB2log (mul_nonneg hΛnonneg hXnonneg)
    exact (h1.trans h2).trans ((le_of_eq hkey).trans (hMbstep.trans (hE.trans hre)))
  exact (mul_le_mul_iff_of_pos_right hB1Bpos).mp
    ((mul_le_mul_iff_of_pos_right hB2Bpos).mp hchain)

/-! ## The abstract final step

If `‖L(1,χ)‖ ≥ c N^{-η}` with `2η ≤ ε`, then every real zero `β ∈ (0,1)` of `L(·,χ)` satisfies
`1 - β ≥ C(ε, c) N^{-ε}`. -/

private lemma zero_bound_of_L_one {Cder : ℝ} (hCderpos : 0 < Cder)
    (hCder : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ σ : ℝ, 1 - 1 / Real.log (2 * (N : ℝ)) ≤ σ → σ ≤ 1 →
      ‖deriv (DirichletCharacter.LFunction χ) (σ : ℂ)‖ ≤
        Cder * (Real.log (2 * (N : ℝ))) ^ 2)
    {c η ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hη : 0 < η) (hη2 : 2 * η ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → ∀ β : ℝ, 0 < β → β < 1 →
      c * (N : ℝ) ^ (-η) ≤ ‖DirichletCharacter.LFunction χ 1‖ →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      C * (N : ℝ) ^ (-ε) ≤ 1 - β := by
  refine ⟨min (ε / 2 ^ (ε + 1)) (c * ε ^ 2 / (64 * 2 ^ (ε / 4) * Cder)),
    lt_min (by positivity) (by positivity), ?_⟩
  intro N _ χ hχ hχprim β hβ0 hβ1 hL hz
  have hN2 : 2 ≤ N := two_le_level χ hχ
  have hN1r : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos N)
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1r
  set ℓ : ℝ := Real.log (2 * (N : ℝ)) with hℓ
  have h2Npos : (0 : ℝ) < 2 * (N : ℝ) := by positivity
  have hℓpos : 0 < ℓ := by rw [hℓ]; exact Real.log_pos (by linarith)
  have hlogε : ℓ ≤ 2 ^ ε * (N : ℝ) ^ ε / ε := by
    have h := Real.log_le_rpow_div (le_of_lt h2Npos) hε
    rw [hℓ]
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)] at h
    exact h
  by_cases hcase : 1 / (2 * ℓ) ≤ 1 - β
  · -- Case (i): `1 - β ≥ 1/(2 log(2N)) ≥ (ε/2^{ε+1}) N^{-ε}`.
    have hA : ε / 2 ^ (ε + 1) * (N : ℝ) ^ (-ε) =
        ε / (2 ^ (ε + 1) * (N : ℝ) ^ ε) := by
      rw [Real.rpow_neg (Nat.cast_nonneg N)]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    have hB : ε / (2 ^ (ε + 1) * (N : ℝ) ^ ε) =
        1 / (2 ^ (ε + 1) * (N : ℝ) ^ ε / ε) := by
      rw [one_div_div]
    have hC : 1 / (2 ^ (ε + 1) * (N : ℝ) ^ ε / ε) ≤ 1 / (2 * ℓ) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have h1 : 2 * ℓ ≤ 2 * (2 ^ ε * (N : ℝ) ^ ε / ε) := by linarith [hlogε]
        have h2 : (2 : ℝ) * (2 ^ ε * (N : ℝ) ^ ε / ε) =
            2 ^ (ε + 1) * (N : ℝ) ^ ε / ε := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) ε 1, Real.rpow_one]
          ring
        linarith [h1, h2]
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)) ?_
    rw [hA, hB]
    exact le_trans hC hcase
  · -- Case (ii): the mean value theorem.
    push Not at hcase
    have hβlow : 1 - 1 / ℓ ≤ β := by
      have hlt : 1 / (2 * ℓ) < 1 / ℓ := by
        have hpos : 0 < 1 / ℓ := one_div_pos.mpr hℓpos
        have heq : 1 / (2 * ℓ) = (1 / 2) * (1 / ℓ) := by ring
        rw [heq]
        nlinarith [hpos]
      linarith
    have hmvt : ‖LFunction χ 1 - LFunction χ (β : ℂ)‖ ≤
        Cder * ℓ ^ 2 * ‖(1 : ℂ) - (β : ℂ)‖ := by
      have hconv : Convex ℝ (segment ℝ (β : ℂ) (1 : ℂ)) := convex_segment _ _
      have hdiff : ∀ z ∈ segment ℝ (β : ℂ) (1 : ℂ), DifferentiableAt ℂ (LFunction χ) z :=
        fun z _ => differentiable_LFunction hχ z
      have hbdd : ∀ z ∈ segment ℝ (β : ℂ) (1 : ℂ),
          ‖deriv (LFunction χ) z‖ ≤ Cder * ℓ ^ 2 := by
        intro z hz'
        rw [segment_eq_image'] at hz'
        obtain ⟨θ, hθ, rfl⟩ := hz'
        set τ : ℝ := β + θ * (1 - β) with hτ
        have hzre : (β + θ • ((1 : ℂ) - (β : ℂ))).re = τ := by
          rw [hτ]
          simp [Complex.add_re]
        have hzim : (β + θ • ((1 : ℂ) - (β : ℂ))).im = 0 := by
          simp [Complex.add_im]
        have hzeq : β + θ • ((1 : ℂ) - (β : ℂ)) = (τ : ℂ) := by
          apply Complex.ext
          · simpa using hzre
          · simpa using hzim
        have h1 : 1 - 1 / ℓ ≤ τ := by rw [hτ]; nlinarith [hθ.1, hβlow, hβ1]
        have h2 : τ ≤ 1 := by rw [hτ]; nlinarith [hθ.2, hβ1]
        simpa only [hzeq] using hCder χ hχ hχprim τ h1 h2
      have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbdd hconv
        (left_mem_segment ℝ (β : ℂ) (1 : ℂ)) (right_mem_segment ℝ (β : ℂ) (1 : ℂ))
      simpa using h
    simp only [hz, sub_zero] at hmvt
    have hcast : (1 : ℂ) - (β : ℂ) = ((1 - β : ℝ) : ℂ) := by push_cast; ring
    have hnorm1 : ‖(1 : ℂ) - (β : ℂ)‖ = 1 - β := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    simp only [hnorm1] at hmvt
    have hCpos : 0 < Cder * ℓ ^ 2 := by positivity
    have h1 : c * (N : ℝ) ^ (-η) / (Cder * ℓ ^ 2) ≤ 1 - β := by
      rw [div_le_iff₀ hCpos]
      linarith [le_trans hL hmvt]
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)) ?_
    have hloglam : ℓ ≤ 2 ^ (ε / 8) * (N : ℝ) ^ (ε / 8) / (ε / 8) := by
      have h := Real.log_le_rpow_div (le_of_lt h2Npos) (by positivity : (0 : ℝ) < ε / 8)
      rw [hℓ]
      rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)] at h
      exact h
    -- `log(2N) ≤ 2^{ε/8} N^{ε/8}/(ε/8)`, hence `ℓ² ≤ 64·2^{ε/4} N^{ε/4}/ε²`.
    have hsq : ℓ ^ 2 ≤ 64 * 2 ^ (ε / 4) * (N : ℝ) ^ (ε / 4) / ε ^ 2 := by
      have h1 : ℓ ^ 2 ≤ (2 ^ (ε/8) * (N:ℝ) ^ (ε/8) / (ε/8)) ^ 2 :=
        pow_le_pow_left₀ hℓpos.le hloglam 2
      have h2 : (2 ^ (ε/8) * (N:ℝ) ^ (ε/8) / (ε/8)) ^ 2 =
          64 * 2 ^ (ε/4) * (N:ℝ) ^ (ε/4) / ε^2 := by
        rw [div_pow, mul_pow]
        have e1 : (2 ^ (ε/8)) ^ 2 = (2:ℝ) ^ (ε/4) := by
          rw [rpow_natPow (2:ℝ) (by norm_num) 2 (ε/8)]
          rw [show (ε/8) * ((2:ℕ):ℝ) = ε/4 by push_cast; ring]
        have e2 : ((N:ℝ) ^ (ε/8)) ^ 2 = (N:ℝ) ^ (ε/4) := by
          rw [rpow_natPow (N:ℝ) (Nat.cast_nonneg N) 2 (ε/8)]
          rw [show (ε/8) * ((2:ℕ):ℝ) = ε/4 by push_cast; ring]
        rw [e1, e2]
        field_simp
        ring
      rw [h2] at h1
      exact h1
    have hkey : ε ^ 2 * ℓ ^ 2 * (N : ℝ) ^ (-ε) ≤
        64 * 2 ^ (ε / 4) * (N : ℝ) ^ (-η) := by
      have h3 : ε ^ 2 * ℓ ^ 2 ≤ 64 * 2 ^ (ε/4) * (N:ℝ) ^ (ε/4) := by
        have h4 := mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ ε^2)
        rw [mul_div_cancel₀ _ (by positivity : (ε:ℝ)^2 ≠ 0)] at h4
        exact h4
      have h5 : (N:ℝ) ^ (ε/4) ≤ (N:ℝ) ^ (ε - η) :=
        Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      calc ε ^ 2 * ℓ ^ 2 * (N:ℝ) ^ (-ε)
          ≤ (64 * 2 ^ (ε/4) * (N:ℝ)^(ε-η)) * (N:ℝ)^(-ε) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
            exact le_trans h3 (mul_le_mul_of_nonneg_left h5 (by positivity))
        _ = 64 * 2 ^ (ε/4) * (N:ℝ)^(-η) := by
            rw [mul_assoc, ← Real.rpow_add hNpos, show ε - η + -ε = -η by ring]
    have hdiv : ε ^ 2 * (N : ℝ) ^ (-ε) / (64 * 2 ^ (ε / 4)) ≤
        (N : ℝ) ^ (-η) / ℓ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (pow_pos hℓpos 2)]
      calc ε ^ 2 * (N:ℝ) ^ (-ε) * ℓ ^ 2 = ε^2 * ℓ^2 * (N:ℝ)^(-ε) := by ring
        _ ≤ 64 * 2 ^ (ε/4) * (N:ℝ)^(-η) := hkey
        _ = (N:ℝ)^(-η) * (64 * 2 ^ (ε/4)) := by ring
    calc c * ε ^ 2 / (64 * 2 ^ (ε / 4) * Cder) * (N : ℝ) ^ (-ε)
        = (c / Cder) * (ε ^ 2 * (N : ℝ) ^ (-ε) / (64 * 2 ^ (ε / 4))) := by ring
      _ ≤ (c / Cder) * ((N : ℝ) ^ (-η) / ℓ ^ 2) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = c * (N : ℝ) ^ (-η) / (Cder * ℓ ^ 2) := by ring
    exact h1

/-! ## The core of the main theorem -/

private theorem siegel_small {ε : ℝ} (hε : 0 < ε) (hε5 : ε ≤ 1 / 5) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → χ * χ = 1 → ∀ β : ℝ, 0 < β → β < 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → C * (N : ℝ) ^ (-ε) ≤ 1 - β := by
  set δ : ℝ := ε / 100 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδ20 : δ ≤ 1 / 20 := by rw [hδdef]; linarith
  set η : ℝ := ε / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hη2 : 2 * η ≤ ε := by rw [hηdef]; linarith
  set lam : ℝ := ε / 8 with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; positivity
  have h6δ2lam : 6 * δ + 2 * lam ≤ η := by rw [hδdef, hlamdef, hηdef]; linarith
  obtain ⟨Cder, hCderpos, hCder⟩ := LFunction_deriv_bound_near_one_uniform
  by_cases hS : ∃ (M : ℕ) (_ : NeZero M) (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ),
      χ₁ * χ₁ = 1 ∧ χ₁.IsPrimitive ∧ χ₁ ≠ 1 ∧ 1 - δ ≤ β₁ ∧ β₁ < 1 ∧
        DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0
  · obtain ⟨M, hMinst, χ₁, β₁, hχ₁sq, hχ₁prim, hχ₁ne, hβ₁lo, hβ₁hi, hβ₁z⟩ := hS
    haveI : NeZero M := hMinst
    have hM2 : 2 ≤ M := two_le_level χ₁ hχ₁ne
    have hM1r : (1 : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 2) hM2)
    have hMpos : (0:ℝ) < (M:ℝ) := lt_of_lt_of_le zero_lt_one hM1r
    -- the two constants
    set cE : ℝ := (1 / 4) * (1 - β₁) * (14 : ℝ) ^ (-(9 * δ)) * (lam / 144) ^ 2 *
      (M : ℝ) ^ (-(6 * δ + 4 * lam)) with hcE
    have hcEpos : 0 < cE := by
      rw [hcE]
      positivity
    have hχ₁ne' : DirichletCharacter.LFunction χ₁ 1 ≠ 0 :=
      DirichletCharacter.LFunction_apply_one_ne_zero hχ₁ne
    set cF : ℝ := ‖DirichletCharacter.LFunction χ₁ 1‖ * (M : ℝ) ^ η with hcF
    have hcFpos : 0 < cF := by
      rw [hcF]
      exact mul_pos (norm_pos_iff.mpr hχ₁ne') (Real.rpow_pos_of_pos hMpos η)
    have hcpos : 0 < min cE cF := lt_min hcEpos hcFpos
    obtain ⟨C0, hC0pos, hC0⟩ := zero_bound_of_L_one hCderpos hCder hcpos hε hηpos hη2
    refine ⟨C0, hC0pos, ?_⟩
    intro N hN χ hχprim hχne hχsq β hβ0 hβ1 hz
    haveI : NeZero N := hN
    have hN2 := two_le_level χ hχne
    have hN1r : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 2) hN2)
    have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le zero_lt_one hN1r
    refine hC0 (N := N) χ hχne hχprim β hβ0 hβ1 ?_ hz
    by_cases hprod : (χ.changeLevel (Nat.dvd_mul_right N M)) *
        (χ₁.changeLevel (Nat.dvd_mul_left M N)) = 1
    · -- `χ = χ₁`: the fixed positive value of `‖L(1,χ₁)‖` is used directly.
      have hsq2 : (χ₁.changeLevel (Nat.dvd_mul_left M N)) *
          (χ₁.changeLevel (Nat.dvd_mul_left M N)) = 1 := by
        rw [← map_mul, hχ₁sq, map_one]
      have heq1 : χ.changeLevel (Nat.dvd_mul_right N M) =
          χ₁.changeLevel (Nat.dvd_mul_left M N) := by
        calc χ.changeLevel (Nat.dvd_mul_right N M)
            = χ.changeLevel (Nat.dvd_mul_right N M) * 1 := (mul_one _).symm
          _ = χ.changeLevel (Nat.dvd_mul_right N M) *
                ((χ₁.changeLevel (Nat.dvd_mul_left M N)) *
                 (χ₁.changeLevel (Nat.dvd_mul_left M N))) := by rw [hsq2]
          _ = (χ.changeLevel (Nat.dvd_mul_right N M) *
                (χ₁.changeLevel (Nat.dvd_mul_left M N))) *
                (χ₁.changeLevel (Nat.dvd_mul_left M N)) := by rw [mul_assoc]
          _ = 1 * (χ₁.changeLevel (Nat.dvd_mul_left M N)) := by rw [hprod]
          _ = χ₁.changeLevel (Nat.dvd_mul_left M N) := one_mul _
      have hNM : N = M := by
        have hc := congrArg DirichletCharacter.conductor heq1
        rw [DirichletCharacter.conductor_changeLevel χ (Nat.dvd_mul_right N M),
            DirichletCharacter.conductor_changeLevel χ₁ (Nat.dvd_mul_left M N)] at hc
        rw [(DirichletCharacter.isPrimitive_def χ).mp hχprim,
            (DirichletCharacter.isPrimitive_def χ₁).mp hχ₁prim] at hc
        exact hc
      subst hNM
      have hχeq : χ = χ₁ := by
        refine DirichletCharacter.changeLevel_injective (R := ℂ) (Nat.dvd_mul_right N N) ?_
        exact heq1.trans (Commons.NumberTheory.DirichletCharacter.changeLevel_congr
          (h₁ := Nat.dvd_mul_left N N) (h₂ := Nat.dvd_mul_right N N) χ₁)
      have hval : cF * (N : ℝ) ^ (-η) = ‖DirichletCharacter.LFunction χ 1‖ := by
        rw [hcF, hχeq, mul_assoc, ← Real.rpow_add hNpos,
          show η + -η = 0 by ring, Real.rpow_zero, mul_one]
      have hle : min cE cF * (N : ℝ) ^ (-η) ≤ cF * (N : ℝ) ^ (-η) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _)
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      rw [hval] at hle
      exact hle
    · have hbound := L_one_lower_of_aux χ₁ hχ₁sq hχ₁prim hχ₁ne hβ₁lo hβ₁hi hδpos hδ20
        hlampos hβ₁z χ hχsq hχne hprod
      have hstep : cE * (N : ℝ) ^ (-η) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
        rw [hcE]
        refine le_trans ?_ hbound
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      have hle : min cE cF * (N : ℝ) ^ (-η) ≤ cE * (N : ℝ) ^ (-η) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _)
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      exact hle.trans hstep
  · -- No Siegel-zero character: any zero `β > 1 - δ` would be one.
    refine ⟨δ, hδpos, ?_⟩
    intro N hN χ hχprim hχne hχsq β hβ0 hβ1 hz
    haveI : NeZero N := hN
    by_cases hcase : δ ≤ 1 - β
    · calc δ * (N : ℝ) ^ (-ε) ≤ δ * 1 := by
            apply mul_le_mul_of_nonneg_left _ hδpos.le
            exact Real.rpow_le_one_of_one_le_of_nonpos
              (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) (by linarith)
        _ = δ := mul_one δ
        _ ≤ 1 - β := hcase
    · push Not at hcase
      exact (hS ⟨N, hN, χ, β, hχsq, hχprim, hχne, by linarith, hβ1, hz⟩).elim

/-! ## The main theorem -/

theorem LFunction_realZero_siegel_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → χ * χ = 1 → ∀ β : ℝ, 0 < β → β < 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      C * (N : ℝ) ^ (-ε) ≤ 1 - β := by
  intro ε hε
  set ε' : ℝ := min ε (1 / 5) with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; exact lt_min hε (by norm_num)
  have hε'le : ε' ≤ ε := by rw [hε'def]; exact min_le_left _ _
  obtain ⟨C, hCpos, hC⟩ := siegel_small hε'pos (by rw [hε'def]; exact min_le_right _ _)
  refine ⟨C, hCpos, ?_⟩
  intro N hN χ hχprim hχne hχsq β hβ0 hβ1 hz
  haveI : NeZero N := hN
  refine le_trans ?_ (hC N χ hχprim hχne hχsq β hβ0 hβ1 hz)
  apply mul_le_mul_of_nonneg_left _ hCpos.le
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) (by linarith)

end

end Commons.NumberTheory.DirichletCharacter
