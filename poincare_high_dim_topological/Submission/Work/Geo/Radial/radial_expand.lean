import Mathlib

namespace Work.Geo.Radial

open Set Metric
open scoped Topology

/-!
# Radial expansion of `ℝⁿ` (blueprint G9, `Work.Geo.Radial.radial_expand`)

For `0 < ε < R` we build an explicit expanding radial self-homeomorphism of `ℝⁿ`: a strictly
increasing, piecewise-linear reparametrisation `ρ` of `[0,∞)` with `ρ 0 = 0`, `ρ t = t` for
`t ≥ R + 1`, and `ρ t ≥ R` for `t ≥ ε`.  The homeomorphism is `x ↦ (ρ ‖x‖ / ‖x‖) • x`, and its
inverse is the analogous map for the inverse reparametrisation `σ = ρ⁻¹`.

Concretely, the multiplier `sMul ε R t = ρ t / t` (with the limiting value at `t = 0`) is
`R / ε` for `t ≤ ε`, `(R + (t - ε)/(R + 1 - ε))/t` for `ε ≤ t ≤ R + 1`, and `1` for `t ≥ R + 1`;
the inverse multiplier `tMul` is built from the inverse reparametrisation `σ`.
-/

noncomputable section

/-- The "inner" part of the forward multiplier: constant `R/ε` up to `ε`, then the middle
piece of the (reparametrised) slope. -/
def sInner (ε R t : ℝ) : ℝ := if t ≤ ε then R / ε else (R + (t - ε) / (R + 1 - ε)) / t

/-- The forward multiplier `t ↦ ρ t / t` with its limiting value at `0`. -/
def sMul (ε R t : ℝ) : ℝ := if t ≤ R + 1 then sInner ε R t else 1

/-- The "inner" part of the inverse multiplier. -/
def tInner (ε R t : ℝ) : ℝ := if t ≤ R then ε / R else (ε + (t - R) * (R + 1 - ε)) / t

/-- The inverse multiplier `t ↦ σ t / t` with its limiting value at `0`. -/
def tMul (ε R t : ℝ) : ℝ := if t ≤ R + 1 then tInner ε R t else 1

/-! ## Continuity of the multipliers -/

lemma continuous_sInner {ε R : ℝ} (hε : 0 < ε) : Continuous (sInner ε R) := by
  unfold sInner
  refine continuous_if_le continuous_id continuous_const continuousOn_const ?_ ?_
  · apply ContinuousOn.div
    · fun_prop
    · exact continuous_id.continuousOn
    · intro x hx; exact ne_of_gt (lt_of_lt_of_le hε hx)
  · intro x hx; subst hx; simp

lemma continuous_tInner {ε R : ℝ} (hε : 0 < ε) (hR : ε < R) : Continuous (tInner ε R) := by
  unfold tInner
  refine continuous_if_le continuous_id continuous_const continuousOn_const ?_ ?_
  · apply ContinuousOn.div
    · fun_prop
    · exact continuous_id.continuousOn
    · intro x hx; exact ne_of_gt (lt_of_lt_of_le (by linarith : (0:ℝ) < R) hx)
  · intro x hx; subst hx; simp

lemma sInner_eq_one {ε R : ℝ} (hε : 0 < ε) (hR : ε < R) : sInner ε R (R + 1) = 1 := by
  unfold sInner
  rw [if_neg (by linarith : ¬ (R + 1 ≤ ε))]
  have h1 : (R + 1 - ε) ≠ 0 := by linarith
  have h2 : (R + 1 : ℝ) ≠ 0 := by linarith
  have h3 : R + (R + 1 - ε) / (R + 1 - ε) = R + 1 := by rw [div_self h1]
  rw [h3, div_self h2]

lemma tInner_eq_one {ε R : ℝ} (hε : 0 < ε) (hR : ε < R) : tInner ε R (R + 1) = 1 := by
  unfold tInner
  rw [if_neg (by linarith : ¬ (R + 1 ≤ R))]
  have h2 : (R + 1 : ℝ) ≠ 0 := by linarith
  have h3 : ε + (R + 1 - R) * (R + 1 - ε) = R + 1 := by ring
  rw [h3, div_self h2]

lemma continuous_sMul {ε R : ℝ} (hε : 0 < ε) (hR : ε < R) : Continuous (sMul ε R) := by
  unfold sMul
  refine continuous_if_le continuous_id continuous_const
    (continuous_sInner (R := R) hε).continuousOn continuousOn_const ?_
  · intro x hx; rw [hx]; exact sInner_eq_one hε hR

lemma continuous_tMul {ε R : ℝ} (hε : 0 < ε) (hR : ε < R) : Continuous (tMul ε R) := by
  unfold tMul
  refine continuous_if_le continuous_id continuous_const
    (continuous_tInner (R := R) hε hR).continuousOn continuousOn_const ?_
  · intro x hx; rw [hx]; exact tInner_eq_one hε hR

/-! ## The values of the multipliers -/

lemma sMul_of_le {ε R t : ℝ} (hR : ε < R) (h : t ≤ ε) : sMul ε R t = R / ε := by
  rw [sMul, if_pos (le_trans h (by linarith)), sInner, if_pos h]

lemma sMul_of_mem {ε R t : ℝ} (hε : 0 < ε) (hR : ε < R) (h1 : ε ≤ t) (h2 : t ≤ R + 1) :
    sMul ε R t = (R + (t - ε) / (R + 1 - ε)) / t := by
  rw [sMul, if_pos h2, sInner]
  by_cases h : t ≤ ε
  · have ht : t = ε := le_antisymm h h1
    rw [if_pos h, ht]; simp
  · rw [if_neg h]

lemma sMul_of_ge {ε R t : ℝ} (hε : 0 < ε) (hR : ε < R) (h : R + 1 ≤ t) : sMul ε R t = 1 := by
  by_cases h2 : t ≤ R + 1
  · have ht : t = R + 1 := le_antisymm h2 h
    rw [sMul, if_pos h2, ht]; exact sInner_eq_one hε hR
  · rw [sMul, if_neg h2]

lemma tMul_of_le {ε R t : ℝ} (hR : ε < R) (h : t ≤ R) : tMul ε R t = ε / R := by
  rw [tMul, if_pos (le_trans h (by linarith)), tInner, if_pos h]

lemma tMul_of_mem {ε R t : ℝ} (hε : 0 < ε) (hR : ε < R) (h1 : R ≤ t) (h2 : t ≤ R + 1) :
    tMul ε R t = (ε + (t - R) * (R + 1 - ε)) / t := by
  rw [tMul, if_pos h2, tInner]
  by_cases h : t ≤ R
  · have ht : t = R := le_antisymm h h1
    rw [if_pos h, ht]; ring_nf
  · rw [if_neg h]

lemma tMul_of_ge {ε R t : ℝ} (hε : 0 < ε) (hR : ε < R) (h : R + 1 ≤ t) : tMul ε R t = 1 := by
  by_cases h2 : t ≤ R + 1
  · have ht : t = R + 1 := le_antisymm h2 h
    rw [tMul, if_pos h2, ht]; exact tInner_eq_one hε hR
  · rw [tMul, if_neg h2]

lemma div_mul_div_one' {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : a / b * (b / a) = 1 := by
  rw [div_mul_div_comm, mul_comm b a, div_self (mul_ne_zero ha hb)]

/-! ## The two mutual-inverse multiplier identities -/

lemma tMul_sMul_mul {ε R t : ℝ} (hε : 0 < ε) (hR : ε < R) (ht : 0 ≤ t) :
    tMul ε R (sMul ε R t * t) * sMul ε R t = 1 := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hRne : R ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < R)
  by_cases h1 : t ≤ ε
  · rw [sMul_of_le hR h1]
    have hle : (R / ε) * t ≤ R := by
      calc (R / ε) * t ≤ (R / ε) * ε :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt (div_pos (by linarith) hε))
        _ = R := by rw [div_mul_cancel₀ R hεne]
    rw [tMul_of_le hR hle]
    exact div_mul_div_one' hεne hRne
  · have h1' : ε < t := lt_of_not_ge h1
    have htpos : 0 < t := lt_trans hε h1'
    have htne : t ≠ 0 := ne_of_gt htpos
    have hdne : (R + 1 - ε) ≠ 0 := by linarith
    by_cases h2 : t ≤ R + 1
    · rw [sMul_of_mem hε hR (le_of_lt h1') h2]
      have harg : (R + (t - ε) / (R + 1 - ε)) / t * t = R + (t - ε) / (R + 1 - ε) :=
        div_mul_cancel₀ _ htne
      rw [harg]
      have hRle : R ≤ R + (t - ε) / (R + 1 - ε) := by
        have : 0 ≤ (t - ε) / (R + 1 - ε) := div_nonneg (by linarith) (by linarith)
        linarith
      have hle' : R + (t - ε) / (R + 1 - ε) ≤ R + 1 := by
        have : (t - ε) / (R + 1 - ε) ≤ 1 := by
          rw [div_le_one (by linarith)]; linarith
        linarith
      rw [tMul_of_mem hε hR hRle hle']
      have hne : R + (t - ε) / (R + 1 - ε) ≠ 0 := by
        have hp : 0 < R + (t - ε) / (R + 1 - ε) := by
          have : 0 < (t - ε) / (R + 1 - ε) := div_pos (by linarith) (by linarith)
          linarith
        exact ne_of_gt hp
      have hdiff : (R + (t - ε) / (R + 1 - ε) - R) * (R + 1 - ε) = t - ε := by
        rw [show R + (t - ε) / (R + 1 - ε) - R = (t - ε) / (R + 1 - ε) by ring]
        exact div_mul_cancel₀ (t - ε) hdne
      rw [hdiff]
      have hnum : ε + (t - ε) = t := by ring
      rw [hnum, div_mul_div_comm, mul_comm (R + (t - ε) / (R + 1 - ε)) t]
      exact div_self (mul_ne_zero htne hne)
    · have h2' : R + 1 ≤ t := le_of_lt (lt_of_not_ge h2)
      rw [sMul_of_ge hε hR h2', one_mul, tMul_of_ge hε hR h2', one_mul]

lemma sMul_tMul_mul {ε R t : ℝ} (hε : 0 < ε) (hR : ε < R) (ht : 0 ≤ t) :
    sMul ε R (tMul ε R t * t) * tMul ε R t = 1 := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hRne : R ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < R)
  by_cases h1 : t ≤ R
  · rw [tMul_of_le hR h1]
    have hle : (ε / R) * t ≤ ε := by
      calc (ε / R) * t ≤ (ε / R) * R :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt (div_pos hε (by linarith)))
        _ = ε := by rw [div_mul_cancel₀ ε hRne]
    rw [sMul_of_le hR hle]
    exact div_mul_div_one' hRne hεne
  · have h1' : R < t := lt_of_not_ge h1
    have htpos : 0 < t := lt_trans (by linarith : (0:ℝ) < R) h1'
    have htne : t ≠ 0 := ne_of_gt htpos
    have hdne : (R + 1 - ε) ≠ 0 := by linarith
    by_cases h2 : t ≤ R + 1
    · rw [tMul_of_mem hε hR (le_of_lt h1') h2]
      have harg : (ε + (t - R) * (R + 1 - ε)) / t * t = ε + (t - R) * (R + 1 - ε) :=
        div_mul_cancel₀ _ htne
      rw [harg]
      have hεle : ε ≤ ε + (t - R) * (R + 1 - ε) := by
        have : 0 ≤ (t - R) * (R + 1 - ε) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hle' : ε + (t - R) * (R + 1 - ε) ≤ R + 1 := by
        have : (t - R) * (R + 1 - ε) ≤ R + 1 - ε := by
          have h := mul_le_mul_of_nonneg_right (show t - R ≤ 1 by linarith)
            (show (0:ℝ) ≤ R + 1 - ε by linarith)
          linarith
        linarith
      rw [sMul_of_mem hε hR hεle hle']
      have hne : ε + (t - R) * (R + 1 - ε) ≠ 0 := by
        have hp : 0 < ε + (t - R) * (R + 1 - ε) := by
          have : 0 ≤ (t - R) * (R + 1 - ε) := mul_nonneg (by linarith) (by linarith)
          linarith
        exact ne_of_gt hp
      have hfrac : (ε + (t - R) * (R + 1 - ε) - ε) / (R + 1 - ε) = t - R := by
        rw [show ε + (t - R) * (R + 1 - ε) - ε = (t - R) * (R + 1 - ε) by ring]
        exact mul_div_cancel_right₀ (t - R) hdne
      rw [hfrac]
      have hnum : R + (t - R) = t := by ring
      rw [hnum, div_mul_div_comm, mul_comm (ε + (t - R) * (R + 1 - ε)) t]
      exact div_self (mul_ne_zero htne hne)
    · have h2' : R + 1 ≤ t := le_of_lt (lt_of_not_ge h2)
      rw [tMul_of_ge hε hR h2', one_mul, sMul_of_ge hε hR h2', one_mul]

/-! ## Positivity and the lower bound -/

lemma sMul_pos {ε R t : ℝ} (hε : 0 < ε) (hR : ε < R) (ht : 0 ≤ t) : 0 < sMul ε R t := by
  by_cases h1 : t ≤ ε
  · rw [sMul_of_le hR h1]; exact div_pos (by linarith) hε
  · have h1' : ε < t := lt_of_not_ge h1
    by_cases h2 : t ≤ R + 1
    · rw [sMul_of_mem hε hR (le_of_lt h1') h2]
      apply div_pos
      · have : 0 ≤ (t - ε) / (R + 1 - ε) := div_nonneg (by linarith) (by linarith)
        linarith
      · linarith
    · rw [sMul_of_ge hε hR (le_of_lt (lt_of_not_ge h2))]; norm_num

lemma tMul_pos {ε R t : ℝ} (hε : 0 < ε) (hR : ε < R) (ht : 0 ≤ t) : 0 < tMul ε R t := by
  by_cases h1 : t ≤ R
  · rw [tMul_of_le hR h1]; exact div_pos hε (by linarith)
  · have h1' : R < t := lt_of_not_ge h1
    by_cases h2 : t ≤ R + 1
    · rw [tMul_of_mem hε hR (le_of_lt h1') h2]
      apply div_pos
      · have : 0 ≤ (t - R) * (R + 1 - ε) := mul_nonneg (by linarith) (by linarith)
        linarith
      · linarith
    · rw [tMul_of_ge hε hR (le_of_lt (lt_of_not_ge h2))]; norm_num

lemma le_sMul_mul_self {ε R t : ℝ} (hε : 0 < ε) (hR : ε < R) (ht : ε ≤ t) :
    R ≤ sMul ε R t * t := by
  by_cases h1 : t ≤ ε
  · have ht_eq : t = ε := le_antisymm h1 ht
    rw [sMul_of_le hR h1, ht_eq, div_mul_cancel₀ R (ne_of_gt hε)]
  · have h1' : ε < t := lt_of_not_ge h1
    by_cases h2 : t ≤ R + 1
    · rw [sMul_of_mem hε hR (le_of_lt h1') h2]
      rw [div_mul_cancel₀ _ (ne_of_gt (lt_trans hε h1'))]
      have : 0 ≤ (t - ε) / (R + 1 - ε) := div_nonneg (by linarith) (by linarith)
      linarith
    · have h2' : R + 1 ≤ t := le_of_lt (lt_of_not_ge h2)
      rw [sMul_of_ge hε hR h2', one_mul]; linarith

/-! ## The radial maps -/

lemma norm_real_smul {n : ℕ} {f : ℝ} (hf : 0 ≤ f) (z : EuclideanSpace ℝ (Fin n)) :
    ‖f • z‖ = f * ‖z‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hf]

/-- The forward radial map `x ↦ sMul ε R ‖x‖ • x`. -/
def gFun {n : ℕ} (ε R : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  sMul ε R ‖x‖ • x

/-- The inverse radial map `y ↦ tMul ε R ‖y‖ • y`. -/
def gInv {n : ℕ} (ε R : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  tMul ε R ‖x‖ • x

lemma continuous_gFun {n : ℕ} {ε R : ℝ} (hε : 0 < ε) (hR : ε < R) :
    Continuous (gFun (n := n) ε R) := by
  unfold gFun
  exact ((continuous_sMul hε hR).comp continuous_norm).smul continuous_id

lemma continuous_gInv {n : ℕ} {ε R : ℝ} (hε : 0 < ε) (hR : ε < R) :
    Continuous (gInv (n := n) ε R) := by
  unfold gInv
  exact ((continuous_tMul hε hR).comp continuous_norm).smul continuous_id

lemma gFun_gInv {n : ℕ} {ε R : ℝ} (hε : 0 < ε) (hR : ε < R)
    (x : EuclideanSpace ℝ (Fin n)) : gFun ε R (gInv ε R x) = x := by
  simp only [gFun, gInv]
  rw [norm_real_smul (le_of_lt (tMul_pos hε hR (norm_nonneg x))), smul_smul,
      sMul_tMul_mul hε hR (norm_nonneg x), one_smul]

lemma gInv_gFun {n : ℕ} {ε R : ℝ} (hε : 0 < ε) (hR : ε < R)
    (x : EuclideanSpace ℝ (Fin n)) : gInv ε R (gFun ε R x) = x := by
  simp only [gFun, gInv]
  rw [norm_real_smul (le_of_lt (sMul_pos hε hR (norm_nonneg x))), smul_smul,
      tMul_sMul_mul hε hR (norm_nonneg x), one_smul]

/-- The expanding radial self-homeomorphism of `ℝⁿ`. -/
def radialHom {n : ℕ} (ε R : ℝ) (hε : 0 < ε) (hR : ε < R) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  { toFun := gFun ε R
    invFun := gInv ε R
    left_inv := fun x => gInv_gFun hε hR x
    right_inv := fun x => gFun_gInv hε hR x
    continuous_toFun := continuous_gFun hε hR
    continuous_invFun := continuous_gInv hε hR }

/-- Blueprint G9 (`Work.Geo.Radial.radial_expand`): for `0 < ε < R` there is an expanding radial
self-homeomorphism of `ℝⁿ` fixing `0` and fixing everything at distance `≥ R + 1`, which pushes
every point at distance `≥ ε` to distance `≥ R`.

The intended fully-qualified name is `Work.Geo.Radial.radial_expand` (file
`Submission/Work/Geo/Radial/radial_expand.lean`). -/
theorem radial_expand {n : ℕ} (ε R : ℝ) (hε : 0 < ε) (hR : ε < R) :
    ∃ g : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n), g 0 = 0 ∧
      (∀ x, R + 1 ≤ ‖x‖ → g x = x) ∧ ∀ x, ε ≤ ‖x‖ → R ≤ ‖g x‖ := by
  refine ⟨radialHom ε R hε hR, ?_, ?_, ?_⟩
  · change gFun ε R (0 : EuclideanSpace ℝ (Fin n)) = 0
    simp [gFun]
  · intro x hx
    change gFun ε R x = x
    rw [gFun, sMul_of_ge hε hR hx, one_smul]
  · intro x hx
    change R ≤ ‖gFun ε R x‖
    rw [gFun, norm_real_smul (le_of_lt (sMul_pos hε hR (norm_nonneg x)))]
    exact le_sMul_mul_self hε hR hx

end

end Work.Geo.Radial
