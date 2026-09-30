import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_basic
import Submission.Work.BMF.halasz_avg_bound
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Final reduction for the complex Halász theorem

Given the "majm" bound

`‖Mf f x‖ ≤ C₁ x ((1 + m) e^{-m} + 1/√T + 1/log x)`,  `m = mHal f x (2T)`

(the form produced by the `casdiv` bound together with the sharp crossover evaluation), this file
derives the statement of `halasz_complex`. The extra term `1/log x` is dominated by `(1+m)e^{-m}`
because `m ≤ log log x + O(1)` (`halasz_avg_bound`); the small ranges (`x < 3` or `T < 2`) are handled
by the trivial bound `‖Mf f x‖ ≤ x`.
-/

namespace Work.BMF

open Finset Real
open BoundedMultiplicativeFunctions

/-- For `2 ≤ x < 3` we have `Zrcp x = 1/2`. -/
lemma Zrcp_eq_half {x : ℝ} (h2 : 2 ≤ x) (h3 : x < 3) : Zrcp x = 1 / 2 := by
  have hfloor : ⌊x⌋₊ = 2 := by
    have h1 : (2:ℕ) ≤ ⌊x⌋₊ := Nat.le_floor h2
    have h2' : ⌊x⌋₊ < 3 := (Nat.floor_lt (show (0:ℝ) ≤ x by linarith)).mpr h3
    omega
  have hset : (Nat.primesLE 2 : Finset ℕ) = {2} := by
    ext p
    rw [Nat.mem_primesLE, Finset.mem_singleton]
    constructor
    · rintro ⟨hp2, hpp⟩
      have := hpp.two_le
      omega
    · rintro rfl
      exact ⟨le_rfl, Nat.prime_two⟩
  rw [Zrcp, hfloor, hset]
  norm_num

/-- Elementary arithmetic: `1/log x` may be traded for `(1+m)e^{-m}/c₀`. -/
lemma absorb_le {L c₀ φ s : ℝ} (hL : 0 < L) (hc₀ : 0 < c₀) (hφ : c₀ ≤ L * φ) (hφnn : 0 ≤ φ)
    (hs : 0 ≤ s) : φ + s + 1 / L ≤ (1 + 1 / c₀) * (φ + s) := by
  have h1 : 1 / L ≤ φ / c₀ := by
    field_simp
    linarith
  have h3 : (1 + 1 / c₀) * (φ + s) = (φ + s) + (φ + s) * (1 / c₀) := by ring
  have h5 : φ + s + 1 / L ≤ (φ + s) + φ / c₀ := by linarith
  have h6 : (φ + s) + φ / c₀ ≤ (φ + s) + (φ + s) * (1 / c₀) := by
    have h7 : φ / c₀ ≤ (φ + s) * (1 / c₀) := by
      rw [div_eq_mul_inv, one_div]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hs) (by positivity : (0:ℝ) ≤ c₀⁻¹)
    linarith
  linarith [h3, h5, h6]

/-- If `0 ≤ x`, `4 ≤ C` and `1/4 ≤ u` then `x ≤ C x u`. -/
lemma aux_bound {C x u : ℝ} (hC : 4 ≤ C) (hx : 0 ≤ x) (hu : (1:ℝ) / 4 ≤ u) :
    x ≤ C * x * u := by
  have hcoef : 1 ≤ 4 * u := by linarith
  have h1 : x ≤ 4 * x * u :=
    calc x ≤ (4 * u) * x := le_mul_of_one_le_left hx hcoef
      _ = 4 * x * u := by ring
  have h2 : 4 * x * u ≤ C * x * u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hx) (by linarith : (0:ℝ) ≤ u)
  linarith [h1, h2]

/-- **Final reduction.** The "majm" bound (with `m = mHal f x (2T)`) implies the statement of
`halasz_complex`. -/
theorem halasz_final_reduction (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hmajm : ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
        ‖Mf f x‖ ≤ C₁ * x * ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
          1 / Real.sqrt T + 1 / Real.log x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ (x T : ℝ), 2 ≤ x → 1 ≤ T →
        let M : ℝ := ⨅ (t : {t : ℝ // |t| ≤ 2 * T}),
          BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * t.1)) x ^ 2
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n‖ ≤ C * x * ((1 + M) * Real.exp (-M) + 1 / Real.sqrt T) := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := halasz_avg_bound.2
  have hminpos : 0 < min 1 (Real.exp (-C₂)) := lt_min one_pos (Real.exp_pos _)
  have hminle : min 1 (Real.exp (-C₂)) ≤ 1 := min_le_left _ _
  refine ⟨max 4 (C₁ * (1 + 1 / min 1 (Real.exp (-C₂)))), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  intro f h1 hmul hb x T hx hT
  have hT0 : (0:ℝ) ≤ 2 * T := by linarith
  have hsqrtpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith : (0:ℝ) < T)
  have hsqrtinv : 0 ≤ 1 / Real.sqrt T := by positivity
  have hM : (⨅ (t : {t : ℝ // |t| ≤ 2 * T}),
        BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * t.1)) x ^ 2)
      = mHal f x (2 * T) := by
    unfold mHal
    exact iInf_congr (fun t => target_M_eq_mHal f hb x t.1)
  have hMnn : 0 ≤ mHal f x (2 * T) := mHal_nonneg f hb x (2 * T) hT0
  have hφnn : 0 ≤ (1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) := by
    have : (0:ℝ) ≤ 1 + mHal f x (2 * T) := by linarith
    positivity
  have hx0 : 0 ≤ x := by linarith
  have hC4 : (4:ℝ) ≤ max 4 (C₁ * (1 + 1 / min 1 (Real.exp (-C₂)))) := le_max_left _ _
  have hCmax : C₁ * (1 + 1 / min 1 (Real.exp (-C₂)))
      ≤ max 4 (C₁ * (1 + 1 / min 1 (Real.exp (-C₂)))) := le_max_right _ _
  have hupper : ∀ u : ℝ, (1:ℝ) / 4 ≤ u →
      x ≤ max 4 (C₁ * (1 + 1 / min 1 (Real.exp (-C₂)))) * x * u :=
    fun u hu => aux_bound hC4 hx0 hu
  dsimp only
  rw [hM]
  rcases lt_or_ge T 2 with hT2 | hT2
  · -- `1 ≤ T < 2`: the trivial bound suffices
    have hbnd : ‖Mf f x‖ ≤ x := Mf_norm_le_x f hb x hx0
    have hsqrtT_le : Real.sqrt T ≤ 2 := by
      have h1 : Real.sqrt T < Real.sqrt 4 :=
        Real.sqrt_lt_sqrt (by linarith : (0:ℝ) ≤ T) (by linarith : T < 4)
      rw [show Real.sqrt 4 = 2 by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
      exact h1.le
    have hinv : (1:ℝ) / 4 ≤ 1 / Real.sqrt T := by
      have h := inv_anti₀ hsqrtpos hsqrtT_le
      have h2 : (2:ℝ)⁻¹ = 1 / 2 := by norm_num
      rw [one_div, one_div]
      linarith [h, h2]
    have hquarter : (1:ℝ) / 4 ≤ (1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
        1 / Real.sqrt T := by linarith [hinv, hφnn]
    exact hbnd.trans (hupper _ hquarter)
  · rcases lt_or_ge x 3 with hx3 | hx3
    · -- small range `2 ≤ x < 3`
      have hMle : mHal f x (2 * T) ≤ 1 := by
        have h := mHal_le_two_Zrcp f hb x (2 * T) hT0
        rw [Zrcp_eq_half hx hx3] at h
        linarith
      have hφ : Real.exp (-1) ≤ (1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) := by
        have h1' : (1:ℝ) ≤ 1 + mHal f x (2 * T) := by linarith [hMnn]
        have h2' : Real.exp (-1) ≤ Real.exp (-(mHal f x (2 * T))) :=
          Real.exp_le_exp.mpr (by linarith [hMnn])
        calc Real.exp (-1) = 1 * Real.exp (-1) := (one_mul _).symm
          _ ≤ (1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) :=
              mul_le_mul h1' h2' (Real.exp_pos _).le (by linarith [hMnn])
      have h14 : (1:ℝ) / 4 ≤ Real.exp (-1) := by
        rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos 1)]
        nlinarith [Real.exp_one_lt_d9]
      have hquarter : (1:ℝ) / 4 ≤ (1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
          1 / Real.sqrt T := by linarith [h14, hφ, hsqrtinv]
      exact (Mf_norm_le_x f hb x hx0).trans (hupper _ hquarter)
    · -- main range `x ≥ 3`, `T ≥ 2`
      have hexp3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have h1x : (1:ℝ) < Real.log x := by
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le hexp3 hx3)
      have hlogx : 0 < Real.log x := lt_trans one_pos h1x
      have hmajm3 := hmajm f h1 hmul hb x T hx3 hT2
      have hC₂log : mHal f x (2 * T) ≤ Real.log (Real.log x) + C₂ := hC₂ f hb x T hx3 hT
      have hφlower : min 1 (Real.exp (-C₂)) ≤ Real.log x *
          ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T)))) := by
        rcases le_or_gt (mHal f x (2 * T)) (Real.log (Real.log x)) with hcase | hcase
        · have hexp : (1:ℝ) ≤ Real.log x * Real.exp (-(mHal f x (2 * T))) := by
            have h' : Real.exp (-(Real.log (Real.log x))) ≤
                Real.exp (-(mHal f x (2 * T))) := Real.exp_le_exp.mpr (by linarith)
            have h2' : Real.exp (-(Real.log (Real.log x))) = 1 / Real.log x := by
              rw [Real.exp_neg, Real.exp_log hlogx, inv_eq_one_div]
            rw [h2'] at h'
            calc (1:ℝ) = Real.log x * (1 / Real.log x) := by
                  rw [mul_one_div, div_self (ne_of_gt hlogx)]
              _ ≤ Real.log x * Real.exp (-(mHal f x (2 * T))) :=
                  mul_le_mul_of_nonneg_left h' hlogx.le
          have h3' : (1:ℝ) ≤ 1 + mHal f x (2 * T) := by linarith [hMnn]
          calc min 1 (Real.exp (-C₂)) ≤ 1 := hminle
            _ = 1 * 1 := (one_mul 1).symm
            _ ≤ (Real.log x * Real.exp (-(mHal f x (2 * T)))) * (1 + mHal f x (2 * T)) :=
                mul_le_mul hexp h3' (by norm_num) (mul_nonneg hlogx.le (Real.exp_pos _).le)
            _ = Real.log x *
                ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T)))) := by ring
        · have hexp : Real.exp (-C₂) ≤ Real.log x * Real.exp (-(mHal f x (2 * T))) := by
            have h' : Real.exp (-(Real.log (Real.log x) + C₂)) ≤
                Real.exp (-(mHal f x (2 * T))) := Real.exp_le_exp.mpr (by linarith)
            have h2' : Real.exp (-(Real.log (Real.log x) + C₂)) =
                Real.exp (-C₂) / Real.log x := by
              rw [show -(Real.log (Real.log x) + C₂) = -(Real.log (Real.log x)) + (-C₂) by ring,
                Real.exp_add, Real.exp_neg, Real.exp_log hlogx, div_eq_mul_inv, mul_comm]
            rw [h2'] at h'
            calc Real.exp (-C₂) = Real.log x * (Real.exp (-C₂) / Real.log x) := by
                  field_simp
              _ ≤ Real.log x * Real.exp (-(mHal f x (2 * T))) :=
                  mul_le_mul_of_nonneg_left h' hlogx.le
          have h3' : (1:ℝ) ≤ 1 + mHal f x (2 * T) := by linarith [hMnn]
          calc min 1 (Real.exp (-C₂)) ≤ Real.exp (-C₂) := min_le_right _ _
            _ = Real.exp (-C₂) * 1 := (mul_one _).symm
            _ ≤ (Real.log x * Real.exp (-(mHal f x (2 * T)))) * (1 + mHal f x (2 * T)) :=
                mul_le_mul hexp h3' (by norm_num) (mul_nonneg hlogx.le (Real.exp_pos _).le)
            _ = Real.log x *
                ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T)))) := by ring
      have hsum := absorb_le hlogx hminpos hφlower hφnn hsqrtinv
      have hmul := mul_le_mul_of_nonneg_left hsum (mul_nonneg hC₁.le hx0)
      have hφsnn : 0 ≤ (1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
          1 / Real.sqrt T := by linarith [hφnn, hsqrtinv]
      have hfin : C₁ * x * ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
            1 / Real.sqrt T + 1 / Real.log x)
          ≤ max 4 (C₁ * (1 + 1 / min 1 (Real.exp (-C₂)))) * x *
            ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T) := by
        have h1' : (C₁ * x) * ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
              1 / Real.sqrt T + 1 / Real.log x)
            = C₁ * x * ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
              1 / Real.sqrt T + 1 / Real.log x) := by ring
        have h3' : max 4 (C₁ * (1 + 1 / min 1 (Real.exp (-C₂)))) * x *
            ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T)
            = (max 4 (C₁ * (1 + 1 / min 1 (Real.exp (-C₂)))) * x) *
            ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T) := by ring
        rw [h1', h3']
        calc (C₁ * x) * ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
                1 / Real.sqrt T + 1 / Real.log x)
            ≤ (C₁ * x) * ((1 + 1 / min 1 (Real.exp (-C₂))) *
              ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T)) := hmul
          _ = (C₁ * (1 + 1 / min 1 (Real.exp (-C₂))) * x) *
              ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T) := by ring
          _ ≤ (max 4 (C₁ * (1 + 1 / min 1 (Real.exp (-C₂)))) * x) *
              ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCmax hx0) hφsnn
      exact hmajm3.trans hfin

end Work.BMF
