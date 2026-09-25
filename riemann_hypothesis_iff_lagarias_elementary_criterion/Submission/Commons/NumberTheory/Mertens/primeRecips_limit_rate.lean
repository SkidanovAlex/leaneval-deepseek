import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_loglog_diff
import Submission.Commons.Analysis.Real.integral_finite_log10_sqrt_le
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Mertens.logDiv_measurable

open Filter Finset Real MeasureTheory
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

/-- remainder `logDiv t − log t − B₁` of the first-Mertens estimate -/
private def reErr (B₁ t : ℝ) : ℝ := logDiv t - Real.log t - B₁

/-- `primeRecips t − log log t` -/
private def reF (t : ℝ) : ℝ := primeRecips t - Real.log (Real.log t)

/-- `(log x)^m ≤ (log x)^n` for `1 ≤ log x` and `m ≤ n`. -/
private lemma log_pow_le_log {x : ℝ} (hlog : (1 : ℝ) ≤ Real.log x) {m n : ℕ} (hmn : m ≤ n) :
    (Real.log x) ^ m ≤ (Real.log x) ^ n := by
  exact pow_le_pow_right₀ hlog hmn

/-- `(log x)^n / √x → 0` as `x → ∞` for `n ≠ 0`. -/
private lemma tendsto_log_pow_div_sqrt (n : ℕ) (hn : n ≠ 0) :
    Tendsto (fun x : ℝ => (Real.log x) ^ n / Real.sqrt x) atTop (𝓝 0) := by
  let r : ℝ := 1 / (2 * (n : ℝ))
  have hr : 0 < r := by
    dsimp [r]
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    positivity
  have h₁ : Tendsto (fun x : ℝ => Real.log x / x ^ r) atTop (𝓝 0) := by
    exact Asymptotics.IsLittleO.tendsto_div_nhds_zero (isLittleO_log_rpow_atTop hr)
  have h₂ : Tendsto (fun x : ℝ => (Real.log x / x ^ r) ^ n) atTop (𝓝 0) := by
    simpa [zero_pow hn] using h₁.pow n
  have hEq : (fun x : ℝ => (Real.log x) ^ n / Real.sqrt x) =ᶠ[atTop]
      fun x : ℝ => (Real.log x / x ^ r) ^ n := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_pow]
    congr 1
    have hx0 : 0 ≤ x := le_of_lt hx
    have hb : (x ^ r) ^ (n : ℝ) = x ^ (r * (n : ℝ)) := (Real.rpow_mul hx0 r (n : ℝ)).symm
    have hb' : (x ^ r) ^ n = x ^ (r * (n : ℝ)) := by
      rw [Real.rpow_natCast (x ^ r) n] at hb
      exact hb
    rw [hb']
    rw [show r * (n : ℝ) = 1 / 2 by
      dsimp [r]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp [hnR]]
    rw [← Real.sqrt_eq_rpow x]
  exact h₂.congr' hEq.symm

/-- Abstract "limsup" step: if `|b| ≤ a + φ X + ψ X` eventually along `X → ∞` and
`φ, ψ → 0`, then `|b| ≤ a`. -/
private lemma abs_le_of_eventually_le_add_tendsto_zero {b a : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : Tendsto φ atTop (𝓝 0)) (hψ : Tendsto ψ atTop (𝓝 0))
    (hbnd : ∀ᶠ X : ℝ in atTop, |b| ≤ a + φ X + ψ X) : |b| ≤ a := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hφε : ∀ᶠ X : ℝ in atTop, |φ X| < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp hφ) (ε / 2) hε2
    simpa [Real.dist_eq] using h
  have hψε : ∀ᶠ X : ℝ in atTop, |ψ X| < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp hψ) (ε / 2) hε2
    simpa [Real.dist_eq] using h
  have hall : ∀ᶠ X : ℝ in atTop,
      |b| ≤ a + φ X + ψ X ∧ |φ X| < ε / 2 ∧ |ψ X| < ε / 2 := by
    filter_upwards [hbnd, hφε, hψε] with X h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨X, hbX, hφX, hψX⟩ := Filter.Eventually.exists hall
  have hsum : a + φ X + ψ X < a + ε := by
    have hφle : φ X < ε / 2 := lt_of_le_of_lt (le_abs_self (φ X)) hφX
    have hψle : ψ X < ε / 2 := lt_of_le_of_lt (le_abs_self (ψ X)) hψX
    linarith
  have hlt : |b| < a + ε := lt_of_le_of_lt hbX hsum
  exact le_of_lt hlt

/-- `reErr B₁ t / (t·log²t)` interval-integrable on `[a,b]` when `2 ≤ a ≤ b`. -/
private lemma reErr_intervalIntegrable {B₁ a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => reErr B₁ t / (t * (Real.log t) ^ 2)) volume a b := by
  let f : ℝ → ℝ := fun t => logDiv t / (t * (Real.log t) ^ 2)
  let g : ℝ → ℝ := fun t => (Real.log t + B₁) / (t * (Real.log t) ^ 2)
  have hf : IntervalIntegrable f volume a b := by
    simpa [f] using intervalIntegrable_logDiv_div_id_log_sq_gen ha hab
  have hg : IntervalIntegrable g volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    intro z hz
    have hza : a ≤ z := by
      rw [Set.uIcc_of_le hab] at hz
      exact hz.1
    have hz2 : 2 ≤ z := le_trans ha hza
    have hz0 : z ≠ 0 := by linarith
    have hlogz : Real.log z ≠ 0 := by
      apply log_ne_zero_of_pos_of_ne_one <;> linarith
    unfold g
    fun_prop (disch := positivity)
  have hsub : IntervalIntegrable (fun t => f t - g t) volume a b := hf.sub hg
  refine hsub.congr_uIoo ?_
  intro t ht
  have hta : a < t := by
    rw [Set.uIoo_of_le hab] at ht
    exact ht.1
  have ht0 : t ≠ 0 := by linarith
  have hlogt : Real.log t ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith
  unfold f g reErr
  field_simp [ht0, hlogt]
  ring

/-- `C₁·(logt)^10/(t·√t)` interval integrable on `[x,X]`, `2 ≤ x ≤ X`. -/
private lemma maj_int {C₁ x X : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    IntervalIntegrable (fun t : ℝ => C₁ * ((Real.log t) ^ 10 / (t * Real.sqrt t))) volume x X := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  have hzx : x ≤ z := by
    rw [Set.uIcc_of_le hxX] at hz
    exact hz.1
  have hz2 : 2 ≤ z := le_trans hx hzx
  have hz0 : z ≠ 0 := by linarith
  have hsqrt : Real.sqrt z ≠ 0 := by
    have hzpos : 0 < z := by linarith
    exact ne_of_gt (Real.sqrt_pos.mpr hzpos)
  fun_prop (disch := positivity)

/-- pointwise: `|e t/(t log²t)| ≤ C₁·(logt)^10/(t·√t)` on `[x,X]` (with rate bounds). -/
private lemma reErr_pointwise {B₁ C₁ y₁ x t : ℝ}
    (hC₁ : 0 ≤ C₁)
    (hb : ∀ t : ℝ, y₁ ≤ t → |reErr B₁ t| ≤ C₁ * (Real.log t) ^ 10 / Real.sqrt t)
    (hxy₁ : y₁ ≤ x) (hx : 2 ≤ x) (hxe : Real.exp 1 ≤ x)
    (htx : x ≤ t) :
    |reErr B₁ t / (t * (Real.log t) ^ 2)| ≤ C₁ * ((Real.log t) ^ 10 / (t * Real.sqrt t)) := by
  have hty₁ : y₁ ≤ t := le_trans hxy₁ htx
  have htb := hb t hty₁
  have ht2 : 2 ≤ t := le_trans hx htx
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht2
  have hlogt1 : (1 : ℝ) ≤ Real.log t := by
    have hte : Real.exp 1 ≤ t := le_trans hxe htx
    have h := Real.log_le_log (Real.exp_pos 1) hte
    simpa using h
  have hlogtpos : 0 < Real.log t := lt_of_lt_of_le (by norm_num) hlogt1
  have hlogtne : Real.log t ≠ 0 := ne_of_gt hlogtpos
  have hpos1 : 0 < t * (Real.log t) ^ 2 := mul_pos htpos (pow_pos hlogtpos 2)
  have hsqrtpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  have hsqrtne : Real.sqrt t ≠ 0 := ne_of_gt hsqrtpos
  have hpos2 : 0 < t * Real.sqrt t := mul_pos htpos hsqrtpos
  rw [abs_div]
  rw [abs_of_pos hpos1]
  calc
    |reErr B₁ t| / (t * (Real.log t) ^ 2)
        ≤ (C₁ * (Real.log t) ^ 10 / Real.sqrt t) / (t * (Real.log t) ^ 2) := by
            exact div_le_div_of_nonneg_right htb (le_of_lt hpos1)
    _ = C₁ * ((Real.log t) ^ 8 / (t * Real.sqrt t)) := by
            field_simp [htpos.ne', hlogtne, hsqrtne]
    _ ≤ C₁ * ((Real.log t) ^ 10 / (t * Real.sqrt t)) := by
            have h8 : (Real.log t) ^ 8 ≤ (Real.log t) ^ 10 :=
              pow_le_pow_right₀ hlogt1 (by norm_num : (8 : ℕ) ≤ 10)
            have hA : (Real.log t) ^ 8 / (t * Real.sqrt t) ≤
                (Real.log t) ^ 10 / (t * Real.sqrt t) :=
              div_le_div_of_nonneg_right h8 (le_of_lt hpos2)
            exact mul_le_mul_of_nonneg_left hA hC₁

/-- Bound on `|f x − f X|` for `X ≥ x` from the two-point identity + rate bounds. -/
private lemma fdiff_le {B₁ C₁ y₁ x X K : ℝ} (hC₁ : 0 ≤ C₁)
    (hb : ∀ t : ℝ, y₁ ≤ t → |reErr B₁ t| ≤ C₁ * (Real.log t) ^ 10 / Real.sqrt t)
    (hxy₁ : y₁ ≤ x) (h2x : 2 ≤ x) (hxX : x ≤ X) (hxe : Real.exp 1 ≤ x)
    (hK : ∀ x : ℝ, Real.exp 1 ≤ x → ∀ X : ℝ, x ≤ X →
      (∫ t in x..X, (Real.log t) ^ 10 / (t * Real.sqrt t)) ≤ K * (Real.log x) ^ 10 / Real.sqrt x) :
    |reF x - reF X| ≤ C₁ * (Real.log x) ^ 9 / Real.sqrt x +
        C₁ * (Real.log X) ^ 9 / Real.sqrt X +
        C₁ * K * (Real.log x) ^ 10 / Real.sqrt x := by
  have h2X : (2 : ℝ) ≤ X := le_trans h2x hxX
  have hx1 : (1 : ℝ) < x := by linarith
  have hX1 : (1 : ℝ) < X := lt_of_lt_of_le hx1 hxX
  have hlogxpos : 0 < Real.log x := Real.log_pos hx1
  have hlogXpos : 0 < Real.log X := Real.log_pos hX1
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) h2x
  have hXpos : 0 < X := lt_of_lt_of_le hxpos hxX
  have hsqrtxpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hsqrtXpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hid := primeRecips_loglog_diff (x := x) (X := X) (B₁ := B₁) h2x hxX
  have hid' : reF X - reF x = (reErr B₁ X / Real.log X - reErr B₁ x / Real.log x) +
      (∫ t in x..X, reErr B₁ t / (t * (Real.log t) ^ 2)) := by
    simpa [reF, reErr] using hid
  have htri1 : |reF x - reF X| ≤
      |reErr B₁ X / Real.log X - reErr B₁ x / Real.log x| +
        |∫ t in x..X, reErr B₁ t / (t * (Real.log t) ^ 2)| := by
    rw [abs_sub_comm]
    rw [hid']
    exact abs_add_le _ _
  have htri2 : |reErr B₁ X / Real.log X - reErr B₁ x / Real.log x| ≤
      |reErr B₁ X| / Real.log X + |reErr B₁ x| / Real.log x := by
    have hsub : |reErr B₁ X / Real.log X - reErr B₁ x / Real.log x| ≤
        |reErr B₁ X / Real.log X| + |reErr B₁ x / Real.log x| := by
      rw [sub_eq_add_neg]
      simpa [abs_neg] using abs_add_le (reErr B₁ X / Real.log X) (-(reErr B₁ x / Real.log x))
    have hu : |reErr B₁ X / Real.log X| = |reErr B₁ X| / Real.log X := by
      rw [abs_div]
      rw [abs_of_pos hlogXpos]
    have hv : |reErr B₁ x / Real.log x| = |reErr B₁ x| / Real.log x := by
      rw [abs_div]
      rw [abs_of_pos hlogxpos]
    calc
      |reErr B₁ X / Real.log X - reErr B₁ x / Real.log x| ≤
          |reErr B₁ X / Real.log X| + |reErr B₁ x / Real.log x| := hsub
      _ = |reErr B₁ X| / Real.log X + |reErr B₁ x| / Real.log x := by rw [hu, hv]
  have htri3 : |∫ t in x..X, reErr B₁ t / (t * (Real.log t) ^ 2)| ≤
      ∫ t in x..X, |reErr B₁ t / (t * (Real.log t) ^ 2)| :=
    intervalIntegral.abs_integral_le_integral_abs hxX
  have hf1 : IntervalIntegrable (fun t : ℝ => reErr B₁ t / (t * (Real.log t) ^ 2)) volume x X :=
    reErr_intervalIntegrable h2x hxX
  have hf1abs : IntervalIntegrable (fun t : ℝ => |reErr B₁ t / (t * (Real.log t) ^ 2)|) volume x X :=
    hf1.abs
  have hg1 : IntervalIntegrable (fun t : ℝ => C₁ * ((Real.log t) ^ 10 / (t * Real.sqrt t))) volume x X :=
    maj_int h2x hxX
  have hmono : (∫ t in x..X, |reErr B₁ t / (t * (Real.log t) ^ 2)|) ≤
      ∫ t in x..X, C₁ * ((Real.log t) ^ 10 / (t * Real.sqrt t)) := by
    refine intervalIntegral.integral_mono_on hxX hf1abs hg1 ?_
    intro t ht
    exact reErr_pointwise (B₁ := B₁) (C₁ := C₁) (y₁ := y₁) (x := x) hC₁ hb hxy₁ h2x hxe ht.1
  have hconst : (∫ t in x..X, C₁ * ((Real.log t) ^ 10 / (t * Real.sqrt t))) =
      C₁ * (∫ t in x..X, (Real.log t) ^ 10 / (t * Real.sqrt t)) := by
    rw [intervalIntegral.integral_const_mul]
  have hKbnd : (∫ t in x..X, (Real.log t) ^ 10 / (t * Real.sqrt t)) ≤
      K * (Real.log x) ^ 10 / Real.sqrt x := hK x hxe X hxX
  have htail : |∫ t in x..X, reErr B₁ t / (t * (Real.log t) ^ 2)| ≤
      C₁ * K * (Real.log x) ^ 10 / Real.sqrt x := by
    calc
      |∫ t in x..X, reErr B₁ t / (t * (Real.log t) ^ 2)| ≤
          ∫ t in x..X, |reErr B₁ t / (t * (Real.log t) ^ 2)| := htri3
      _ ≤ ∫ t in x..X, C₁ * ((Real.log t) ^ 10 / (t * Real.sqrt t)) := hmono
      _ = C₁ * (∫ t in x..X, (Real.log t) ^ 10 / (t * Real.sqrt t)) := hconst
      _ ≤ C₁ * (K * (Real.log x) ^ 10 / Real.sqrt x) :=
            mul_le_mul_of_nonneg_left hKbnd hC₁
      _ = C₁ * K * (Real.log x) ^ 10 / Real.sqrt x := by
            field_simp [ne_of_gt hsqrtxpos]
  have hbX : |reErr B₁ X| / Real.log X ≤ C₁ * (Real.log X) ^ 9 / Real.sqrt X := by
    have hbX0 := hb X (le_trans hxy₁ hxX)
    calc
      |reErr B₁ X| / Real.log X ≤
          (C₁ * (Real.log X) ^ 10 / Real.sqrt X) / Real.log X := by
            exact div_le_div_of_nonneg_right hbX0 (le_of_lt hlogXpos)
      _ = C₁ * (Real.log X) ^ 9 / Real.sqrt X := by
            field_simp [ne_of_gt hlogXpos, ne_of_gt hsqrtXpos]
  have hbx : |reErr B₁ x| / Real.log x ≤ C₁ * (Real.log x) ^ 9 / Real.sqrt x := by
    have hbx0 := hb x hxy₁
    calc
      |reErr B₁ x| / Real.log x ≤
          (C₁ * (Real.log x) ^ 10 / Real.sqrt x) / Real.log x := by
            exact div_le_div_of_nonneg_right hbx0 (le_of_lt hlogxpos)
      _ = C₁ * (Real.log x) ^ 9 / Real.sqrt x := by
            field_simp [ne_of_gt hlogxpos, ne_of_gt hsqrtxpos]
  calc
    |reF x - reF X|
        ≤ |reErr B₁ X / Real.log X - reErr B₁ x / Real.log x| +
            |∫ t in x..X, reErr B₁ t / (t * (Real.log t) ^ 2)| := htri1
    _ ≤ (|reErr B₁ X| / Real.log X + |reErr B₁ x| / Real.log x) +
            |∫ t in x..X, reErr B₁ t / (t * (Real.log t) ^ 2)| := by
            exact add_le_add_left htri2 (|∫ t in x..X, reErr B₁ t / (t * (Real.log t) ^ 2)|)
    _ ≤ (|reErr B₁ X| / Real.log X + |reErr B₁ x| / Real.log x) +
            C₁ * K * (Real.log x) ^ 10 / Real.sqrt x := by
            exact add_le_add_right htail (|reErr B₁ X| / Real.log X + |reErr B₁ x| / Real.log x)
    _ ≤ (C₁ * (Real.log X) ^ 9 / Real.sqrt X + C₁ * (Real.log x) ^ 9 / Real.sqrt x) +
            C₁ * K * (Real.log x) ^ 10 / Real.sqrt x := by
            have hsum := add_le_add hbX hbx
            exact add_le_add_left hsum (C₁ * K * (Real.log x) ^ 10 / Real.sqrt x)
    _ = C₁ * (Real.log x) ^ 9 / Real.sqrt x +
            C₁ * (Real.log X) ^ 9 / Real.sqrt X +
            C₁ * K * (Real.log x) ^ 10 / Real.sqrt x := by
            ring

theorem primeRecips_limit_rate {B₁ C₁ y₁ : ℝ} (hC₁ : 0 ≤ C₁) (hY : 2 ≤ y₁)
    (hb : ∀ t : ℝ, y₁ ≤ t → |Commons.NumberTheory.Mertens.logDiv t - Real.log t - B₁| ≤
      C₁ * (Real.log t) ^ 10 / Real.sqrt t) {L : ℝ}
    (hL : Filter.Tendsto (fun x : ℝ => Commons.NumberTheory.Mertens.primeRecips x - Real.log (Real.log x))
      Filter.atTop (nhds L)) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ y₂ : ℝ, y₁ ≤ y₂ ∧ ∀ x : ℝ, y₂ ≤ x →
      |(Commons.NumberTheory.Mertens.primeRecips x - Real.log (Real.log x)) - L| ≤
        C₂ * (Real.log x) ^ 12 / Real.sqrt x := by
  rcases Commons.Analysis.Real.integral_finite_log10_sqrt_le with ⟨K, hKpos, hK⟩
  have hKnon : 0 ≤ K := le_of_lt hKpos
  refine ⟨C₁ * (1 + K) + 1, ?_, max y₁ (Real.exp 1), ?_, ?_⟩
  · have hnon : 0 ≤ C₁ * (1 + K) := by positivity
    linarith
  · exact le_max_left y₁ (Real.exp 1)
  · intro x hx
    have hxy₁ : y₁ ≤ x := le_trans (le_max_left y₁ (Real.exp 1)) hx
    have hxe : Real.exp 1 ≤ x := le_trans (le_max_right y₁ (Real.exp 1)) hx
    have h2x : (2 : ℝ) ≤ x := le_trans hY hxy₁
    have hx1 : (1 : ℝ) < x := by linarith
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) h2x
    have hsqrtxpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    have hsqrtxne : Real.sqrt x ≠ 0 := ne_of_gt hsqrtxpos
    have hxlog1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hxe
      simpa using h
    have hlogxpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hxlog1
    -- rate bound at x
    let A : ℝ := C₁ * (Real.log x) ^ 9 / Real.sqrt x +
        C₁ * K * (Real.log x) ^ 10 / Real.sqrt x
    have hb' : ∀ t : ℝ, y₁ ≤ t →
        |reErr B₁ t| ≤ C₁ * (Real.log t) ^ 10 / Real.sqrt t := by
      intro t ht
      simpa [reErr] using hb t ht
    have hfL : Tendsto (fun x : ℝ => reF x) atTop (𝓝 L) := by
      simpa [reF] using hL
    -- |f x − L| ≤ A
    have hbA : |reF x - L| ≤ A := by
      let φ : ℝ → ℝ := fun X => C₁ * (Real.log X) ^ 9 / Real.sqrt X
      let ψ : ℝ → ℝ := fun X => |reF X - L|
      have hφ0 : Tendsto φ atTop (𝓝 0) := by
        have h₁ := tendsto_log_pow_div_sqrt 9 (by norm_num : (9 : ℕ) ≠ 0)
        have h₂ : Tendsto (fun X : ℝ => C₁ * ((Real.log X) ^ 9 / Real.sqrt X)) atTop (𝓝 (C₁ * 0)) :=
          h₁.const_mul C₁
        have h₃ : Tendsto (fun X : ℝ => C₁ * ((Real.log X) ^ 9 / Real.sqrt X)) atTop (𝓝 0) := by
          simpa using h₂
        refine h₃.congr' ?_
        filter_upwards with X
        ring
      have hψ0 : Tendsto ψ atTop (𝓝 0) := by
        simpa [ψ, Real.norm_eq_abs] using (tendsto_iff_norm_sub_tendsto_zero.mp hfL)
      have hbnd : ∀ᶠ X : ℝ in atTop, |reF x - L| ≤ A + φ X + ψ X := by
        filter_upwards [eventually_ge_atTop x] with X hXx
        have htri : |reF x - L| ≤ |reF x - reF X| + |reF X - L| := by
          have h1 : reF x - L = (reF x - reF X) + (reF X - L) := by ring
          rw [h1]
          exact abs_add_le _ _
        have hfd := fdiff_le (B₁ := B₁) (C₁ := C₁) (y₁ := y₁) (x := x) (X := X) (K := K)
          hC₁ hb' hxy₁ h2x hXx hxe hK
        have hfdA : |reF x - reF X| ≤ A + φ X := by
          have hsum_eq : A + φ X = C₁ * (Real.log x) ^ 9 / Real.sqrt x +
                C₁ * (Real.log X) ^ 9 / Real.sqrt X +
                C₁ * K * (Real.log x) ^ 10 / Real.sqrt x := by
            dsimp [A, φ]
            ring
          rwa [hsum_eq]
        calc
          |reF x - L| ≤ |reF x - reF X| + |reF X - L| := htri
          _ ≤ (A + φ X) + |reF X - L| := by
                exact add_le_add_left hfdA (|reF X - L|)
          _ = A + φ X + ψ X := rfl
      exact abs_le_of_eventually_le_add_tendsto_zero (b := reF x - L) (a := A) hφ0 hψ0 hbnd
    -- |f x − L| ≤ C₁(logx)^9/√x + C₁K(logx)^10/√x (definitional)
    have hbA2 : |reF x - L| ≤ C₁ * (Real.log x) ^ 9 / Real.sqrt x +
        C₁ * K * (Real.log x) ^ 10 / Real.sqrt x := by
      simpa [A] using hbA
    -- raise to power 12
    have hL1 : C₁ * (Real.log x) ^ 9 / Real.sqrt x ≤ C₁ * (Real.log x) ^ 12 / Real.sqrt x := by
      have hpow : (Real.log x) ^ 9 ≤ (Real.log x) ^ 12 :=
        log_pow_le_log hxlog1 (by norm_num : (9 : ℕ) ≤ 12)
      have hnon : 0 ≤ C₁ / Real.sqrt x := div_nonneg hC₁ (le_of_lt hsqrtxpos)
      calc
        C₁ * (Real.log x) ^ 9 / Real.sqrt x = (C₁ / Real.sqrt x) * (Real.log x) ^ 9 := by
          field_simp [hsqrtxne]
        _ ≤ (C₁ / Real.sqrt x) * (Real.log x) ^ 12 := mul_le_mul_of_nonneg_left hpow hnon
        _ = C₁ * (Real.log x) ^ 12 / Real.sqrt x := by
          field_simp [hsqrtxne]
    have hL2 : C₁ * K * (Real.log x) ^ 10 / Real.sqrt x ≤
        C₁ * K * (Real.log x) ^ 12 / Real.sqrt x := by
      have hpow : (Real.log x) ^ 10 ≤ (Real.log x) ^ 12 :=
        log_pow_le_log hxlog1 (by norm_num : (10 : ℕ) ≤ 12)
      have hnon : 0 ≤ C₁ * K / Real.sqrt x := by
        positivity
      calc
        C₁ * K * (Real.log x) ^ 10 / Real.sqrt x = (C₁ * K / Real.sqrt x) * (Real.log x) ^ 10 := by
          field_simp [hsqrtxne]
        _ ≤ (C₁ * K / Real.sqrt x) * (Real.log x) ^ 12 := mul_le_mul_of_nonneg_left hpow hnon
        _ = C₁ * K * (Real.log x) ^ 12 / Real.sqrt x := by
          field_simp [hsqrtxne]
    have hsum12 : C₁ * (Real.log x) ^ 9 / Real.sqrt x +
          C₁ * K * (Real.log x) ^ 10 / Real.sqrt x ≤
        (C₁ * (1 + K)) * (Real.log x) ^ 12 / Real.sqrt x := by
      have hadd := add_le_add hL1 hL2
      calc
        C₁ * (Real.log x) ^ 9 / Real.sqrt x + C₁ * K * (Real.log x) ^ 10 / Real.sqrt x
            ≤ C₁ * (Real.log x) ^ 12 / Real.sqrt x + C₁ * K * (Real.log x) ^ 12 / Real.sqrt x := hadd
        _ = (C₁ + C₁ * K) * (Real.log x) ^ 12 / Real.sqrt x := by
            field_simp [hsqrtxne]
        _ = (C₁ * (1 + K)) * (Real.log x) ^ 12 / Real.sqrt x := by ring
    have hpow12 : 0 ≤ (Real.log x) ^ 12 := by
      exact pow_nonneg (le_trans zero_le_one hxlog1) 12
    have hnon12 : 0 ≤ (Real.log x) ^ 12 / Real.sqrt x :=
      div_nonneg hpow12 (le_of_lt hsqrtxpos)
    have hplus : (C₁ * (1 + K)) * (Real.log x) ^ 12 / Real.sqrt x ≤
        (C₁ * (1 + K) + 1) * (Real.log x) ^ 12 / Real.sqrt x := by
      have hone : C₁ * (1 + K) ≤ C₁ * (1 + K) + 1 := by linarith
      have hm := mul_le_mul_of_nonneg_right hone hnon12
      calc
        (C₁ * (1 + K)) * (Real.log x) ^ 12 / Real.sqrt x
            = (C₁ * (1 + K)) * ((Real.log x) ^ 12 / Real.sqrt x) := by ring
        _ ≤ (C₁ * (1 + K) + 1) * ((Real.log x) ^ 12 / Real.sqrt x) := hm
        _ = (C₁ * (1 + K) + 1) * (Real.log x) ^ 12 / Real.sqrt x := by ring
    change |reF x - L| ≤ (C₁ * (1 + K) + 1) * (Real.log x) ^ 12 / Real.sqrt x
    calc
      |reF x - L| ≤ C₁ * (Real.log x) ^ 9 / Real.sqrt x +
          C₁ * K * (Real.log x) ^ 10 / Real.sqrt x := hbA2
      _ ≤ (C₁ * (1 + K)) * (Real.log x) ^ 12 / Real.sqrt x := hsum12
      _ ≤ (C₁ * (1 + K) + 1) * (Real.log x) ^ 12 / Real.sqrt x := hplus

end

end Commons.NumberTheory.Mertens
