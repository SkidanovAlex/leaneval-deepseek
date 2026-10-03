import Mathlib

/-!
# The Koebe transform: from `|a₂| ≤ 2` to the one-quarter bound

For a univalent `f` on the unit disc with `f 0 = 0`, `deriv f 0 = 1`, and a value `w` omitted by
`f`, the *Koebe transform*

  `T z = w * f z / (w - f z)`

is again univalent on the disc with `T 0 = 0`, `deriv T 0 = 1`.  Its second coefficient is
`a₂ + 1/w`, so Bieberbach's inequality `|a₂| ≤ 2` (applied to both `f` and `T`) bounds `|1/w|`
by `4`, i.e. an omitted value has modulus at least `1/4`.  This is the classical derivation of
Koebe's one-quarter theorem from the second coefficient inequality.

This file isolates that derivation: it proves `Work.Repel.Koebe.omitted_norm_ge_quarter`, which
takes Bieberbach's inequality as an explicit hypothesis, and the necessary derivative
computations for the Koebe transform.
-/

namespace Work.Repel.Koebe

open Filter
open scoped Topology

/-- First derivative of the Koebe transform: `deriv (w * f / (w - f)) z = w^2 * f' z / (w - f z)^2`. -/
theorem koebe_transf_deriv {f : ℂ → ℂ} {w z : ℂ} (hf : AnalyticAt ℂ f z) (hne : w - f z ≠ 0) :
    deriv (fun y => w * f y / (w - f y)) z = w^2 * deriv f z / (w - f z)^2 := by
  have h1 : HasDerivAt f (deriv f z) z := hf.hasStrictDerivAt.hasDerivAt
  have h2 : HasDerivAt (fun y => w * f y) (w * deriv f z) z := h1.const_mul w
  have h3 : HasDerivAt (fun y => w - f y) (-(deriv f z)) z := h1.const_sub w
  have h4 := h2.div h3 hne
  have h4' : deriv (fun y => w * f y / (w - f y)) z
      = (w * deriv f z * (w - f z) - w * f z * -deriv f z) / (w - f z)^2 := h4.deriv
  rw [h4']
  field_simp
  ring

/-- Second derivative of the Koebe transform at the origin. -/
theorem koebe_transf_iteratedDeriv_two {f : ℂ → ℂ} {w : ℂ}
    (hf : ∀ᶠ z in nhds (0 : ℂ), AnalyticAt ℂ f z) (h0 : f 0 = 0) (hw : w ≠ 0) :
    iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0
      = deriv (deriv f) 0 + 2 * (deriv f 0)^2 / w := by
  have hf0 : AnalyticAt ℂ f 0 := hf.self_of_nhds
  have hcont : ContinuousAt (fun z => w - f z) 0 := continuousAt_const.sub hf0.continuousAt
  have hev : ∀ᶠ z in nhds (0 : ℂ), w - f z ≠ 0 :=
    hcont.eventually_ne (by rw [h0, sub_zero]; exact hw)
  have hT : (fun z => deriv (fun y => w * f y / (w - f y)) z)
      =ᶠ[nhds (0 : ℂ)] (fun z => w^2 * deriv f z / (w - f z)^2) := by
    filter_upwards [hf, hev] with z hz hz'
    exact koebe_transf_deriv hz hz'
  have hiter : iteratedDeriv 2 (fun z => w * f z / (w - f z))
      = deriv (deriv (fun z => w * f z / (w - f z))) := by
    rw [show (2:ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (fun z => deriv (fun y => w * f y / (w - f y)) z) 0
      = deriv (fun z => w^2 * deriv f z / (w - f z)^2) 0 := EventuallyEq.deriv_eq hT
  have hsq : deriv (fun z => (w - f z)^2) 0 = -2 * (w - f 0) * deriv f 0 := by
    have hd : DifferentiableAt ℂ (fun z => w - f z) 0 := hf0.differentiableAt.const_sub w
    have h := deriv_pow (f := fun z => w - f z) (x := 0) hd 2
    have h' : deriv (fun z => (w - f z)^2) 0
        = (2:ℂ) * (w - f 0)^(2-1) * deriv (fun z => w - f z) 0 := h
    rw [h', deriv_const_sub]
    ring
  have hdf : DifferentiableAt ℂ (deriv f) 0 := (hf0.deriv).differentiableAt
  rw [hiter, h1]
  change deriv ((fun z => w^2 * deriv f z) / (fun z => (w - f z)^2)) 0 = _
  rw [deriv_div]
  · rw [deriv_const_mul]
    · rw [hsq, h0]
      field_simp
      ring
    · exact hdf
  · exact hdf.const_mul (w^2)
  · exact (hf0.differentiableAt.const_sub w).pow 2
  · rw [h0]; simp [hw]

/-- The Koebe transform is injective wherever `f` is injective and avoids `w`. -/
theorem koebe_transf_injOn {f : ℂ → ℂ} {w : ℂ} {s : Set ℂ} (hinj : Set.InjOn f s) (hw : w ≠ 0)
    (hne : ∀ z ∈ s, f z ≠ w) : Set.InjOn (fun z => w * f z / (w - f z)) s := by
  intro z1 h1 z2 h2 heq
  have hne1 : w - f z1 ≠ 0 := sub_ne_zero.mpr (hne z1 h1).symm
  have hne2 : w - f z2 ≠ 0 := sub_ne_zero.mpr (hne z2 h2).symm
  rw [div_eq_div_iff hne1 hne2] at heq
  have hkey : w^2 * (f z1 - f z2) = 0 := by linear_combination heq
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h (pow_ne_zero 2 hw)
  · exact hinj h1 h2 (sub_eq_zero.mp h)

/-- **The Koebe transform step.**  If a bound `‖g''(0)‖ ≤ A` holds for every univalent
normalised `g` on the unit disc, then every value omitted by a univalent normalised `f` has
modulus at least `1/A`. -/
theorem omitted_norm_ge {A : ℝ} (hA : 0 < A) {f : ℂ → ℂ}
    (han : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z)
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1)
    (hb : ∀ g : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ g z) →
      Set.InjOn g (Metric.ball (0 : ℂ) 1) → g 0 = 0 → deriv g 0 = 1 →
      ‖iteratedDeriv 2 g 0‖ ≤ A)
    {w : ℂ} (hw : w ∉ f '' Metric.ball (0 : ℂ) 1) : 1/A ≤ ‖w‖ := by
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hw0 : w ≠ 0 := by
    intro h
    exact hw ⟨0, h0mem, by rw [h0, h]⟩
  have hTne : ∀ z ∈ Metric.ball (0 : ℂ) 1, w - f z ≠ 0 := by
    intro z hz hzw
    exact hw ⟨z, hz, (sub_eq_zero.mp hzw).symm⟩
  have hanT : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ (fun z => w * f z / (w - f z)) z := by
    intro z hz
    exact AnalyticAt.div
      (AnalyticAt.mul (analyticAt_const (v := w) (x := z)) (han z hz))
      (AnalyticAt.sub (analyticAt_const (v := w) (x := z)) (han z hz)) (hTne z hz)
  have hinjT : Set.InjOn (fun z => w * f z / (w - f z)) (Metric.ball (0 : ℂ) 1) :=
    koebe_transf_injOn hinj hw0 (fun z hz hfw => hTne z hz (by rw [hfw, sub_self]))
  have hT0 : (fun z => w * f z / (w - f z)) 0 = 0 := by
    simp [h0]
  have hT1 : deriv (fun z => w * f z / (w - f z)) 0 = 1 := by
    rw [koebe_transf_deriv (han 0 h0mem) (hTne 0 h0mem), h0, h1]
    simp only [mul_one, sub_zero]
    exact div_self (pow_ne_zero 2 hw0)
  have hBT : ‖iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0‖ ≤ A :=
    hb _ hanT hinjT hT0 hT1
  have hev_an : ∀ᶠ z in nhds (0 : ℂ), AnalyticAt ℂ f z :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds h0mem) han
  have hT2 : iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0 = deriv (deriv f) 0 + 2 / w := by
    rw [koebe_transf_iteratedDeriv_two hev_an h0 hw0, h1]
    ring
  have hf2 : ‖iteratedDeriv 2 f 0‖ ≤ A := hb f han hinj h0 h1
  rw [show iteratedDeriv 2 f 0 = deriv (deriv f) 0 from by
    rw [show (2:ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]] at hf2
  rw [hT2] at hBT
  have hsame : (deriv (deriv f) 0 + 2 / w) - deriv (deriv f) 0 = (2 : ℂ) / w := by ring
  have hfin : ‖(2 : ℂ) / w‖ ≤ 2 * A := by
    calc ‖(2 : ℂ) / w‖ = ‖(deriv (deriv f) 0 + 2 / w) - deriv (deriv f) 0‖ := by rw [hsame]
      _ ≤ ‖deriv (deriv f) 0 + 2 / w‖ + ‖deriv (deriv f) 0‖ := norm_sub_le _ _
      _ ≤ A + A := add_le_add hBT hf2
      _ = 2 * A := by ring
  rw [norm_div] at hfin
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo] at hfin
  rw [div_le_iff₀ (norm_pos_iff.mpr hw0)] at hfin
  rw [div_le_iff₀ hA]
  nlinarith [norm_nonneg w]

/-- Specialisation to Bieberbach's inequality: omitted values have modulus at least `1/4`. -/
theorem omitted_norm_ge_quarter {f : ℂ → ℂ}
    (han : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z)
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1)
    (hb : ∀ g : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ g z) →
      Set.InjOn g (Metric.ball (0 : ℂ) 1) → g 0 = 0 → deriv g 0 = 1 →
      ‖iteratedDeriv 2 g 0‖ ≤ 4)
    {w : ℂ} (hw : w ∉ f '' Metric.ball (0 : ℂ) 1) : 1/4 ≤ ‖w‖ := by
  have h := omitted_norm_ge (A := 4) (by norm_num) han hinj h0 h1 hb hw
  norm_num at h
  exact h

end Work.Repel.Koebe
