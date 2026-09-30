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
# The "majm" bound of Halász's theorem (assembly)

`‖Σ_{n ≤ x} f n‖ ≤ C x ((1 + m) e^{-m} + 1/√T + 1/log x)`, `m = mHal f x (2T)`.

This is obtained from

* `Work.BMF.halasz_casdiv`: `‖Mf f x‖ ≤ C (x/log x) (∫_{1/log x}^{1} exp (Wsup f x α (T+1)) dα/α
  + e^Z/√T + e^Z/log x)`;
* the two pointwise bounds for `Wsup` from `Work.BMF.halasz_wsup_bound`;
* the sharp crossover integral (`hcross`, see `Work.BMF.halasz_crossover_aux`);
* Mertens' theorem `e^Z ≤ C log x`.
-/

namespace Work.BMF

open Finset Real
open BoundedMultiplicativeFunctions

/-- Mertens: `exp (Zrcp x) ≤ C log x` for `x ≥ 3`. -/
lemma exp_Zrcp_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → Real.exp (Zrcp x) ≤ C * Real.log x := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  have hC₀' : ∀ y : ℝ, 11 ≤ y → Zrcp y ≤ Real.log (Real.log y) + C₀ := by
    intro y hy
    have h := hC₀ y hy
    rw [abs_le] at h
    have h2 : (∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / p) - Real.log (Real.log y) ≤ C₀ := h.2
    simp only [Zrcp]
    linarith
  refine ⟨max (Real.exp C₀) (Real.exp (Zrcp 11) / Real.log 3), ?_, ?_⟩
  · exact lt_of_lt_of_le (Real.exp_pos C₀) (le_max_left _ _)
  intro x hx3
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  rcases le_or_gt 11 x with h11 | h11
  · have hZ : Zrcp x ≤ Real.log (Real.log x) + C₀ := hC₀' x h11
    have hloglogx : 0 < Real.log (Real.log x) := by
      apply Real.log_pos
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hexp : Real.exp (Zrcp x) ≤ Real.exp (Real.log (Real.log x) + C₀) :=
      Real.exp_le_exp.mpr hZ
    rw [Real.exp_add, Real.exp_log hlogx, mul_comm] at hexp
    calc Real.exp (Zrcp x) ≤ Real.exp C₀ * Real.log x := hexp
      _ ≤ max (Real.exp C₀) (Real.exp (Zrcp 11) / Real.log 3) * Real.log x :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlogx.le
  · have hZmono : Zrcp x ≤ Zrcp 11 := Zrcp_mono h11.le
    have hexp : Real.exp (Zrcp x) ≤ Real.exp (Zrcp 11) := Real.exp_le_exp.mpr hZmono
    have hlog3x : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    have hconst : Real.exp (Zrcp 11) = (Real.exp (Zrcp 11) / Real.log 3) * Real.log 3 := by
      field_simp
    calc Real.exp (Zrcp x) ≤ Real.exp (Zrcp 11) := hexp
      _ = (Real.exp (Zrcp 11) / Real.log 3) * Real.log 3 := hconst
      _ ≤ (Real.exp (Zrcp 11) / Real.log 3) * Real.log x :=
          mul_le_mul_of_nonneg_left hlog3x (by positivity)
      _ ≤ max (Real.exp C₀) (Real.exp (Zrcp 11) / Real.log 3) * Real.log x :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hlogx.le

/-- **The "majm" bound**, assembled from the `casdiv` bound, the two pointwise `Wsup` bounds,
the sharp crossover integral and Mertens' theorem.

`hws` is the pair of pointwise bounds for `Wsup` (see `Work.BMF.halasz_wsup_bound`), stated with the
`mHal` window equal to twice the `Wsup` window; it is applied below with the *same* window `T` as the
one appearing in `hcasdiv` (which is invoked at `T - 1`, so that its `Wsup` window `T - 1 + 1` is `T`). -/
theorem halasz_majm_of_pieces
    (hcasdiv : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
        ‖Mf f x‖ ≤ C * (x / Real.log x) *
          ((∫ α in (1 / Real.log x)..1, Real.exp (Wsup f x α (T + 1)) / α) +
           Real.exp (Zrcp x) / Real.sqrt T +
           Real.exp (Zrcp x) / Real.log x))
    (hws : ∃ Cw : ℝ, 0 < Cw ∧
      (∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x α T : ℝ, 3 ≤ x → 1 ≤ T →
        1 / Real.log x ≤ α → α ≤ 1 →
        Wsup f x α T ≤ Zrcp x - mHal f x (2 * T) + Cw) ∧
      (∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x α T : ℝ, 3 ≤ x → 1 ≤ T →
        1 / Real.log x ≤ α → α ≤ 1 →
        Wsup f x α T ≤ Zrcp x - Real.log (α * Real.log x) + Cw))
    (hcross : ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℝ) (L Z m C₁ : ℝ), 1 ≤ L → 0 ≤ m → 0 ≤ C₁ →
        IntervalIntegrable (fun α : ℝ => Real.exp (g α) / α) MeasureTheory.volume (1 / L) 1 →
        (∀ α : ℝ, 1 / L ≤ α → α ≤ 1 → g α ≤ Z - m + C₁) →
        (∀ α : ℝ, 1 / L ≤ α → α ≤ 1 → g α ≤ Z - Real.log (α * L) + C₁) →
        (∫ α in (1 / L)..1, Real.exp (g α) / α)
          ≤ C * Real.exp (Z + C₁) * ((1 + m) * Real.exp (-m)))
    (hInt : ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (x T : ℝ), 3 ≤ x → 2 ≤ T →
        IntervalIntegrable (fun α : ℝ => Real.exp (Wsup f x α T) / α)
          MeasureTheory.volume (1 / Real.log x) 1) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
        ‖Mf f x‖ ≤ C₂ * x * ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
          1 / Real.sqrt T + 1 / Real.log x) := by
  obtain ⟨Cc, hCcpos, hcasdiv'⟩ := hcasdiv
  obtain ⟨Cw, hCwpos, hws_s, hws_t⟩ := hws
  obtain ⟨Cx, hCxpos, hcross'⟩ := hcross
  obtain ⟨CZ, hCZpos, hZ⟩ := exp_Zrcp_le_log
  refine ⟨max 4 (Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) + 1), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  intro f h1 hmul hb x T hx hT
  have hx0 : 0 ≤ x := by linarith
  have hm0 : 0 ≤ mHal f x (2 * T) := mHal_nonneg f hb x (2 * T) (by linarith)
  have hφnn : 0 ≤ (1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) := by
    have : (0:ℝ) ≤ 1 + mHal f x (2 * T) := by linarith
    positivity
  have hTsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  have hBnn : 0 ≤ (1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
      1 / Real.sqrt T := by
    have := div_nonneg zero_le_one hTsqrt.le
    linarith [hφnn, this]
  rcases lt_or_ge T 3 with hT3 | hT3
  · -- `2 ≤ T < 3`: trivial bound (`1/√T > 1/2 > 1/4`)
    have hbnd : ‖Mf f x‖ ≤ x := Mf_norm_le_x f hb x hx0
    have hsqrtT_le : Real.sqrt T ≤ 2 := by
      have h1 : Real.sqrt T < Real.sqrt 4 :=
        Real.sqrt_lt_sqrt (by linarith : (0:ℝ) ≤ T) (by linarith : T < 4)
      rw [show Real.sqrt 4 = 2 by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
      exact h1.le
    have hinv : (1:ℝ) / 4 ≤ 1 / Real.sqrt T := by
      have h := inv_anti₀ hTsqrt hsqrtT_le
      have h2 : (2:ℝ)⁻¹ = 1 / 2 := by norm_num
      rw [one_div, one_div]
      linarith [h, h2]
    have hquarter : (1:ℝ) / 4 ≤ (1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
        1 / Real.sqrt T := by linarith [hinv, hφnn]
    have hC4 : (4:ℝ) ≤ max 4 (Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) + 1) := le_max_left _ _
    have hcoef : 1 ≤ 4 * ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
        1 / Real.sqrt T) := by linarith [hquarter]
    refine hbnd.trans ?_
    calc x ≤ (4 * ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
            1 / Real.sqrt T)) * x := le_mul_of_one_le_left hx0 hcoef
      _ = 4 * x * ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
            1 / Real.sqrt T) := by ring
      _ ≤ max 4 (Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) + 1) * x *
            ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC4 hx0) hBnn
      _ ≤ max 4 (Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) + 1) * x *
            ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T +
              1 / Real.log x) := by
          have hlogx1 : 0 ≤ 1 / Real.log x := by
            apply div_nonneg zero_le_one
            have h1 : (1:ℝ) ≤ Real.log x := by
              rw [← Real.log_exp 1]
              exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
            linarith
          exact mul_le_mul_of_nonneg_left (by linarith [hlogx1]) (by positivity)
  · -- `T ≥ 3`: apply `casdiv` at `T - 1`
    have hlogx1 : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hlogx : 0 < Real.log x := lt_of_lt_of_le one_pos hlogx1
    have hTsub : 2 ≤ T - 1 := by linarith
    have hTsub1 : T - 1 + 1 = T := by ring
    have hcas := hcasdiv' f h1 hmul hb x (T - 1) hx hTsub
    rw [hTsub1] at hcas
    -- `1/√(T-1) ≤ 2/√T`
    have hinv' : (Real.sqrt (T - 1))⁻¹ ≤ 2 / Real.sqrt T := by
      rw [inv_eq_one_div]
      have h1 : 0 < Real.sqrt (T - 1) := Real.sqrt_pos.mpr (by linarith)
      have h2 : 0 < Real.sqrt T := hTsqrt
      rw [div_le_iff₀ h1, div_mul_eq_mul_div, le_div_iff₀ h2]
      have h3 : Real.sqrt T ≤ Real.sqrt (4 * (T - 1)) :=
        Real.sqrt_le_sqrt (by linarith)
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)] at h3
      rw [show Real.sqrt 4 = 2 by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h3
      linarith
    have hInt' : IntervalIntegrable (fun α : ℝ => Real.exp (Wsup f x α T) / α)
        MeasureTheory.volume (1 / Real.log x) 1 := hInt f hb x T hx (by linarith)
    have hsharp : ∀ α : ℝ, 1 / Real.log x ≤ α → α ≤ 1 →
        Wsup f x α T ≤ Zrcp x - mHal f x (2 * T) + Cw :=
      fun α hα hα1 => hws_s f hb x α T hx (by linarith) hα hα1
    have htriv : ∀ α : ℝ, 1 / Real.log x ≤ α → α ≤ 1 →
        Wsup f x α T ≤ Zrcp x - Real.log (α * Real.log x) + Cw :=
      fun α hα hα1 => hws_t f hb x α T hx (by linarith) hα hα1
    have hI := hcross' (fun α => Wsup f x α T) (Real.log x) (Zrcp x) (mHal f x (2 * T))
      Cw hlogx1 hm0 hCwpos.le hInt' hsharp htriv
    have hZx : Real.exp (Zrcp x) ≤ CZ * Real.log x := hZ x hx
    have hIbound : (∫ α in (1 / Real.log x)..1, Real.exp (Wsup f x α T) / α)
        ≤ (Cx * Real.exp Cw * CZ) * Real.log x *
          ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T)))) := by
      calc (∫ α in (1 / Real.log x)..1, Real.exp (Wsup f x α T) / α)
          ≤ Cx * Real.exp (Zrcp x + Cw) *
              ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T)))) := hI
        _ = (Cx * Real.exp Cw) * Real.exp (Zrcp x) *
              ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T)))) := by
            rw [Real.exp_add]; ring
        _ ≤ (Cx * Real.exp Cw) * (CZ * Real.log x) *
              ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T)))) := by
            apply mul_le_mul_of_nonneg_right _ hφnn
            exact mul_le_mul_of_nonneg_left hZx (by positivity)
        _ = (Cx * Real.exp Cw * CZ) * Real.log x *
              ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T)))) := by ring
    have h2 : Real.exp (Zrcp x) / Real.sqrt (T - 1) ≤ 2 * CZ * Real.log x / Real.sqrt T := by
      calc Real.exp (Zrcp x) / Real.sqrt (T - 1)
          ≤ Real.exp (Zrcp x) * (2 / Real.sqrt T) :=
            mul_le_mul_of_nonneg_left hinv' (Real.exp_pos _).le
        _ = 2 * Real.exp (Zrcp x) / Real.sqrt T := by ring
        _ ≤ 2 * (CZ * Real.log x) / Real.sqrt T := by
            apply div_le_div_of_nonneg_right _ hTsqrt.le
            linarith [hZx]
        _ = 2 * CZ * Real.log x / Real.sqrt T := by ring
    have h3 : Real.exp (Zrcp x) / Real.log x ≤ CZ := by
      rw [div_le_iff₀ hlogx]
      simpa using hZx
    have hlogmul : Real.log x * (1 / Real.log x) = 1 := by
      rw [mul_one_div, div_self (ne_of_gt hlogx)]
    have hB : 0 < Cx * Real.exp Cw * CZ + 4 * CZ := by
      have h1 : 0 < Cx * Real.exp Cw * CZ := by positivity
      have h2 : 0 < 4 * CZ := by positivity
      linarith
    have h4 : CZ ≤ (Cx * Real.exp Cw * CZ + 4 * CZ) * Real.log x * (1 / Real.log x) := by
      rw [mul_assoc, hlogmul, mul_one]
      have hnn : 0 ≤ Cx * Real.exp Cw * CZ := by positivity
      linarith
    have h5 : (Cx * Real.exp Cw * CZ) * Real.log x *
          ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))))
        ≤ (Cx * Real.exp Cw * CZ + 4 * CZ) * Real.log x *
          ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T)))) := by
      apply mul_le_mul_of_nonneg_right _ hφnn
      apply mul_le_mul_of_nonneg_right _ hlogx.le
      have hnn : 0 ≤ 4 * CZ := by positivity
      linarith
    have h6 : 2 * CZ * Real.log x / Real.sqrt T
        ≤ (Cx * Real.exp Cw * CZ + 4 * CZ) * Real.log x * (1 / Real.sqrt T) := by
      rw [div_eq_mul_inv, one_div]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hlogx.le
      have hnn : 0 ≤ Cx * Real.exp Cw * CZ := by positivity
      linarith
    have hbracket : (∫ α in (1 / Real.log x)..1, Real.exp (Wsup f x α T) / α) +
          Real.exp (Zrcp x) / Real.sqrt (T - 1) + Real.exp (Zrcp x) / Real.log x
        ≤ (Cx * Real.exp Cw * CZ + 4 * CZ) * Real.log x *
          ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T +
            1 / Real.log x) := by
      have hexpand : (Cx * Real.exp Cw * CZ + 4 * CZ) * Real.log x *
            ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T +
              1 / Real.log x)
          = (Cx * Real.exp Cw * CZ + 4 * CZ) * Real.log x *
              ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T)))) +
            (Cx * Real.exp Cw * CZ + 4 * CZ) * Real.log x * (1 / Real.sqrt T) +
            (Cx * Real.exp Cw * CZ + 4 * CZ) * Real.log x * (1 / Real.log x) := by ring
      rw [hexpand]
      exact add_le_add (add_le_add (le_trans hIbound h5) (le_trans h2 h6)) (le_trans h3 h4)
    have hstep : ‖Mf f x‖ ≤ Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) * x *
          ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T +
            1 / Real.log x) := by
      have hfinal : Cc * (x / Real.log x) *
            ((Cx * Real.exp Cw * CZ + 4 * CZ) * Real.log x *
              ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T +
                1 / Real.log x))
          = Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) * x *
              ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T +
                1 / Real.log x) := by
        field_simp
      calc ‖Mf f x‖ ≤ Cc * (x / Real.log x) *
            ((∫ α in (1 / Real.log x)..1, Real.exp (Wsup f x α T) / α) +
              Real.exp (Zrcp x) / Real.sqrt (T - 1) + Real.exp (Zrcp x) / Real.log x) := hcas
        _ ≤ Cc * (x / Real.log x) *
            ((Cx * Real.exp Cw * CZ + 4 * CZ) * Real.log x *
              ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T +
                1 / Real.log x)) :=
            mul_le_mul_of_nonneg_left hbracket (by positivity)
        _ = Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) * x *
            ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T +
              1 / Real.log x) := hfinal
    have hCbig : Cc * (Cx * Real.exp Cw * CZ + 4 * CZ)
        ≤ Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) + 1 := by linarith
    have hClt : Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) + 1
        ≤ max 4 (Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) + 1) := le_max_right _ _
    have hBnn' : 0 ≤ (1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
        1 / Real.sqrt T + 1 / Real.log x := by
      have h1 : 0 ≤ 1 / Real.sqrt T := div_nonneg zero_le_one hTsqrt.le
      have h2 : 0 ≤ 1 / Real.log x := div_nonneg zero_le_one hlogx.le
      linarith [hφnn, h1, h2]
    calc ‖Mf f x‖ ≤ Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) * x *
          ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T +
            1 / Real.log x) := hstep
      _ ≤ (Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) + 1) * x *
          ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T +
            1 / Real.log x) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbig hx0) hBnn'
      _ ≤ max 4 (Cc * (Cx * Real.exp Cw * CZ + 4 * CZ) + 1) * x *
          ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) + 1 / Real.sqrt T +
            1 / Real.log x) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hClt hx0) hBnn'

end Work.BMF
