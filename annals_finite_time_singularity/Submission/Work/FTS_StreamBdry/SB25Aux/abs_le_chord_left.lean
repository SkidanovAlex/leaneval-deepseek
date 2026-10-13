import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25Aux

open Set Filter

/-! Auxiliary facts: the derivative of the quadratic `(K/2)(y-a)(b-y)`, of its derivative,
and of the linear function `((y-a)/(b-a))*C`. -/

private lemma alcl_hasDerivAt_quad (K a b x : ℝ) :
    HasDerivAt (fun y : ℝ => (K/2)*(y - a)*(b - y)) ((K/2)*(a + b - 2*x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (K/2)*(y - a)) (K/2) x := by
    simpa using ((hasDerivAt_id x).sub_const a).const_mul (K/2)
  have h2 : HasDerivAt (fun y : ℝ => b - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub b
  refine (h1.mul h2).congr_deriv ?_
  ring

private lemma alcl_hasDerivAt_quad' (K a b x : ℝ) :
    HasDerivAt (fun y : ℝ => (K/2)*(a + b - 2*y)) (-K) x := by
  have h1 : HasDerivAt (fun y : ℝ => 2*y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2:ℝ)
  have h2 : HasDerivAt (fun y : ℝ => a + b - 2*y) (-2) x := by
    simpa using h1.const_sub (a + b)
  refine (h2.const_mul (K/2)).congr_deriv ?_
  ring

private lemma alcl_hasDerivAt_lin (C a b x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y - a)/(b - a)) * C) (C/(b - a)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y - a)/(b - a)) (1/(b - a)) x := by
    simpa using ((hasDerivAt_id x).sub_const a).div_const (b - a)
  refine (h1.mul_const C).congr_deriv ?_
  ring

/-- If `φ` tends to `0` at both endpoints of the open interval `(a,b)` and `φ'' ≥ 0` on
`(a,b)`, then `φ ≤ 0` on `(a,b)`.  (Two mean value theorems plus the monotonicity of `φ'`.) -/
private theorem alcl_chord_nonpos {φ φ' φ'' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hlima : Tendsto φ (nhdsWithin a (Ioi a)) (nhds 0))
    (hlimb : Tendsto φ (nhdsWithin b (Iio b)) (nhds 0))
    (hd1 : ∀ x ∈ Ioo a b, HasDerivAt φ (φ' x) x)
    (hd2 : ∀ x ∈ Ioo a b, HasDerivAt φ' (φ'' x) x)
    (h2 : ∀ x ∈ Ioo a b, 0 ≤ φ'' x) :
    ∀ θ ∈ Ioo a b, φ θ ≤ 0 := by
  intro θ hθ
  by_contra hcon
  rw [not_le] at hcon
  have hθa : a < θ := hθ.1
  have hθb : θ < b := hθ.2
  have hθt : Filter.Tendsto φ (nhdsWithin θ (Iio θ)) (nhds (φ θ)) :=
    ((hd1 θ hθ).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  -- Cauchy mean value theorem on `(a, θ)`: some `φ' c₁` is positive
  obtain ⟨c₁, hc₁, hc₁eq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope' φ φ' hθa id (fun _ => 1)
      (lfa := 0) (lga := a) (lfb := φ θ) (lgb := θ)
      (fun x hx => hd1 x ⟨hx.1, hx.2.trans hθb⟩)
      (fun x _ => hasDerivAt_id x)
      hlima
      ((continuousAt_id (x := a)).tendsto.mono_left nhdsWithin_le_nhds)
      hθt
      ((continuousAt_id (x := θ)).tendsto.mono_left nhdsWithin_le_nhds)
  simp only [sub_zero, mul_one] at hc₁eq
  have hc₁pos : 0 < φ' c₁ := by
    have : 0 < (θ - a) * φ' c₁ := by rw [hc₁eq]; exact hcon
    exact pos_of_mul_pos_left (by simpa [mul_comm] using this) (le_of_lt (sub_pos.mpr hθa))
  -- Cauchy mean value theorem on `(θ, b)`: some `φ' c₂` is negative
  obtain ⟨c₂, hc₂, hc₂eq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope' φ φ' hθb id (fun _ => 1)
      (lfa := φ θ) (lga := θ) (lfb := 0) (lgb := b)
      (fun x hx => hd1 x ⟨hθa.trans hx.1, hx.2⟩)
      (fun x _ => hasDerivAt_id x)
      ((hd1 θ hθ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((continuousAt_id (x := θ)).tendsto.mono_left nhdsWithin_le_nhds)
      hlimb
      ((continuousAt_id (x := b)).tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_sub, mul_one] at hc₂eq
  have hc₂neg : φ' c₂ < 0 := by
    have : (b - θ) * φ' c₂ < 0 := by rw [hc₂eq]; linarith
    exact neg_of_mul_neg_left (by simpa [mul_comm] using this) (le_of_lt (sub_pos.mpr hθb))
  have hc₁c₂ : c₁ < c₂ := hc₁.2.trans hc₂.1
  have hsub : Icc c₁ c₂ ⊆ Ioo a b := by
    intro x hx
    exact ⟨hc₁.1.trans_le hx.1, hx.2.trans_lt hc₂.2⟩
  -- `φ'` is monotone on `[c₁,c₂]` because `φ'' ≥ 0`
  have hmono : MonotoneOn φ' (Icc c₁ c₂) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc c₁ c₂) ?_ ?_ ?_
    · intro x hx
      exact ((hd2 x (hsub hx)).continuousAt).continuousWithinAt
    · rw [interior_Icc]
      intro x hx
      exact ((hd2 x (hsub ⟨hx.1.le, hx.2.le⟩)).differentiableAt).differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx' : x ∈ Ioo a b := hsub ⟨hx.1.le, hx.2.le⟩
      rw [(hd2 x hx').deriv]
      exact h2 x hx'
  have := hmono ⟨le_refl c₁, hc₁c₂.le⟩ ⟨hc₁c₂.le, le_refl c₂⟩ hc₁c₂.le
  linarith

/-- If `e` tends to `0` at both endpoints of `(a,b)` and `|e''| ≤ K` on `(a,b)`, then
`|e θ| ≤ (K/2)(θ-a)(b-θ)`.  Both estimates follow from `alcl_chord_nonpos` applied to
`e - H` and `-e - H`, where `H` is the parabola `(K/2)(y-a)(b-y)`. -/
private theorem alcl_chord_abs {e e' e'' : ℝ → ℝ} {a b K : ℝ} (hab : a < b)
    (hlima : Tendsto e (nhdsWithin a (Ioi a)) (nhds 0))
    (hlimb : Tendsto e (nhdsWithin b (Iio b)) (nhds 0))
    (hd1 : ∀ x ∈ Ioo a b, HasDerivAt e (e' x) x)
    (hd2 : ∀ x ∈ Ioo a b, HasDerivAt e' (e'' x) x)
    (hb : ∀ x ∈ Ioo a b, |e'' x| ≤ K) :
    ∀ θ ∈ Ioo a b, |e θ| ≤ (K/2)*(θ - a)*(b - θ) := by
  intro θ hθ
  have hHcont : Continuous (fun y : ℝ => (K/2)*(y - a)*(b - y)) := by fun_prop
  have hHa : K / 2 * (a - a) * (b - a) = 0 := by ring
  have hHb : K / 2 * (b - a) * (b - b) = 0 := by ring
  have hHca : ContinuousAt (fun y : ℝ => (K/2)*(y - a)*(b - y)) a := hHcont.continuousAt
  have hHcb : ContinuousAt (fun y : ℝ => (K/2)*(y - a)*(b - y)) b := hHcont.continuousAt
  have hHatend : Tendsto (fun y : ℝ => (K/2)*(y - a)*(b - y)) (nhdsWithin a (Ioi a)) (nhds 0) := by
    have := hHca.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi a))
    rwa [hHa] at this
  have hHbtend : Tendsto (fun y : ℝ => (K/2)*(y - a)*(b - y)) (nhdsWithin b (Iio b)) (nhds 0) := by
    have := hHcb.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio b))
    rwa [hHb] at this
  have hfirst : e θ - (K/2)*(θ - a)*(b - θ) ≤ 0 := by
    refine alcl_chord_nonpos (φ := fun y : ℝ => e y - (K/2)*(y - a)*(b - y))
      (φ' := fun y : ℝ => e' y - (K/2)*(a + b - 2*y)) (φ'' := fun y : ℝ => e'' y + K)
      hab ?_ ?_ ?_ ?_ ?_ θ hθ
    · have := hlima.sub hHatend; simpa using this
    · have := hlimb.sub hHbtend; simpa using this
    · intro x hx
      exact (hd1 x hx).sub (alcl_hasDerivAt_quad K a b x)
    · intro x hx
      refine ((hd2 x hx).sub (alcl_hasDerivAt_quad' K a b x)).congr_deriv ?_
      ring
    · intro x hx
      have := (abs_le.mp (hb x hx)).1
      linarith
  have hsecond : -e θ - (K/2)*(θ - a)*(b - θ) ≤ 0 := by
    refine alcl_chord_nonpos (φ := fun y : ℝ => -e y - (K/2)*(y - a)*(b - y))
      (φ' := fun y : ℝ => -e' y - (K/2)*(a + b - 2*y)) (φ'' := fun y : ℝ => -e'' y + K)
      hab ?_ ?_ ?_ ?_ ?_ θ hθ
    · have := hlima.neg.sub hHatend; simpa using this
    · have := hlimb.neg.sub hHbtend; simpa using this
    · intro x hx
      exact (hd1 x hx).neg.sub (alcl_hasDerivAt_quad K a b x)
    · intro x hx
      refine ((hd2 x hx).neg.sub (alcl_hasDerivAt_quad' K a b x)).congr_deriv ?_
      ring
    · intro x hx
      have := (abs_le.mp (hb x hx)).2
      linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_le_chord_left {F : ℝ → ℝ} {K a b : ℝ} (hab : a < b)
    (hlim : Filter.Tendsto F (nhdsWithin a (Set.Ioi a)) (nhds 0))
    (hcont : Filter.Tendsto F (nhdsWithin b (Set.Iio b)) (nhds (F b)))
    (hd1 : ∀ θ ∈ Set.Ioo a b, DifferentiableAt ℝ F θ)
    (hd2 : ∀ θ ∈ Set.Ioo a b, DifferentiableAt ℝ (deriv F) θ)
    (hb1 : ∀ θ ∈ Set.Ioo a b, |deriv F θ| ≤ K)
    (hb2 : ∀ θ ∈ Set.Ioo a b, |deriv (deriv F) θ| ≤ K) :
    ∀ θ ∈ Set.Ioo a b, |F θ| ≤ ((θ - a) / (b - a)) * |F b| + (K / 2) * (θ - a) * (b - θ) := by
  intro θ hθ
  -- the chord `L` joining `(a,0)` to `(b,F b)`
  have hLcont : Continuous (fun x : ℝ => ((x - a) / (b - a)) * F b) := by fun_prop
  have hLa : (a - a) / (b - a) * F b = 0 := by ring
  have hLb : (b - a) / (b - a) * F b = F b := by
    rw [div_self (ne_of_gt (sub_pos.mpr hab)), one_mul]
  have hLca : ContinuousAt (fun x : ℝ => ((x - a) / (b - a)) * F b) a := hLcont.continuousAt
  have hLcb : ContinuousAt (fun x : ℝ => ((x - a) / (b - a)) * F b) b := hLcont.continuousAt
  have hLtenda : Tendsto (fun x : ℝ => ((x - a) / (b - a)) * F b) (nhdsWithin a (Ioi a)) (nhds 0) := by
    have := hLca.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi a))
    rwa [hLa] at this
  have hLtendb : Tendsto (fun x : ℝ => ((x - a) / (b - a)) * F b) (nhdsWithin b (Iio b)) (nhds (F b)) := by
    have := hLcb.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio b))
    rwa [hLb] at this
  -- `e = F - L` vanishes at both ends
  have hlima : Tendsto (fun x : ℝ => F x - ((x - a) / (b - a)) * F b) (nhdsWithin a (Ioi a)) (nhds 0) := by
    have := hlim.sub hLtenda
    simpa using this
  have hlimb : Tendsto (fun x : ℝ => F x - ((x - a) / (b - a)) * F b) (nhdsWithin b (Iio b)) (nhds 0) := by
    have := hcont.sub hLtendb
    simpa using this
  have hder1 : ∀ x ∈ Ioo a b, HasDerivAt (fun y : ℝ => F y - ((y - a) / (b - a)) * F b)
      ((fun y : ℝ => deriv F y - F b / (b - a)) x) x := by
    intro x hx
    exact (hd1 x hx).hasDerivAt.sub (alcl_hasDerivAt_lin (F b) a b x)
  have hder2 : ∀ x ∈ Ioo a b, HasDerivAt (fun y : ℝ => deriv F y - F b / (b - a))
      ((fun y : ℝ => deriv (deriv F) y) x) x := by
    intro x hx
    exact (hd2 x hx).hasDerivAt.sub_const (F b / (b - a))
  have hb : ∀ x ∈ Ioo a b, |(fun y : ℝ => deriv (deriv F) y) x| ≤ K := by
    intro x hx
    exact hb2 x hx
  have hmain : |(fun y : ℝ => F y - ((y - a) / (b - a)) * F b) θ| ≤ (K/2)*(θ - a)*(b - θ) :=
    alcl_chord_abs hab hlima hlimb hder1 hder2 hb θ hθ
  have hLabs : |((θ - a) / (b - a)) * F b| = ((θ - a) / (b - a)) * |F b| := by
    rw [abs_mul, abs_div, abs_of_pos (sub_pos.mpr hθ.1), abs_of_pos (sub_pos.mpr hab)]
  have h1 : |F θ| ≤ |F θ - ((θ - a) / (b - a)) * F b| + |((θ - a) / (b - a)) * F b| := by
    have := abs_add_le (F θ - ((θ - a) / (b - a)) * F b) (((θ - a) / (b - a)) * F b)
    rwa [sub_add_cancel] at this
  calc |F θ| ≤ |F θ - ((θ - a) / (b - a)) * F b| + |((θ - a) / (b - a)) * F b| := h1
    _ ≤ (K/2)*(θ - a)*(b - θ) + ((θ - a) / (b - a)) * |F b| := add_le_add hmain (le_of_eq hLabs)
    _ = ((θ - a) / (b - a)) * |F b| + (K / 2) * (θ - a) * (b - θ) := by ring

end Work.FTS_StreamBdry.SB25Aux
