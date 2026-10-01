/-
# ZeroFreeTables — table10_93_cert

Region-form numerical certificates for the Table 10 rows with `λ₁ ≥ 0.36`, for
**HB Lemma 9.3**'s inequality

  `(k²+½)(F(−λ₁) − F(0)) − 2k F(λ₂−λ₁) + f(0)((k²+4k+3/2)(1/6+ε)) ≥ 0`

with the test function `tf72T λ` of HB Lemma 7.2 and `ε = 10⁻⁶`.

For each row `(a,b)` of `hbTable10` with `a ≥ 0.36` we exhibit rational `λ, k`
for which the left-hand side is **negative** on the whole region
`λ₁ ∈ [348/1000, a]`, `λ₂ ∈ [λ₁, b]`: the contradiction with HB Lemma 9.3 then
gives `λ₂ ≥ b`.

Everything is phrased in terms of `tf72Phi`, the `λ`-free form of the Laplace
transform (`F_λ z = tf72Phi (z/λ)`):

* `tf72Phi` is antitone, so `tf72Phi ((v−u)/λ) ≥ tf72Phi ((b−u)/λ)` for `v ≤ b`
  and the `v`-dependence is discharged;
* the `u`-dependence is handled by `tf72Phi_mono_step`, which compares the value
  at `u` with the value at the right endpoint `a` using the integral
  representation `tf72Phi (−x) = (1/30)∫₀² e^{xs}(2−s)³(4+6s+s²)ds` and a
  monotone-weight argument;
* the remaining scalar inequality at `u = a` is certified from the rational
  bounds `tf72PhiUB`, `tf72PhiLB`, `tf72PhiLBneg`, `tf72PhiUBpos` by `norm_num`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.tf72Phi_defs
import Submission.Work.ZeroFreeTables.tf72Phi_upper
import Submission.Work.ZeroFreeTables.tf72Phi_lower
import Submission.Work.ZeroFreeTables.tf72Phi_neg_lower
import Submission.Work.ZeroFreeTables.tf72Phi_pos_upper

namespace Work.ZeroFreeTables

noncomputable section

open scoped Real
open MeasureTheory

lemma continuous_tf72Body : Continuous tf72Body := by
  unfold tf72Body; fun_prop

lemma tf72Body_nonneg' (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 2) : 0 ≤ tf72Body s := by
  obtain ⟨hs0, hs2⟩ := hs
  rw [tf72Body]
  have h1 : 0 ≤ (2 - s) ^ 3 := by
    have : 0 ≤ 2 - s := by linarith
    positivity
  have h2 : 0 ≤ 4 + 6 * s + s ^ 2 := by nlinarith [sq_nonneg (s + 3)]
  positivity

/-- Monotone-weight comparison. -/
lemma integral_monotone_weight (φ ψ χ : ℝ → ℝ)
    (hφc : Continuous φ) (hφ0 : ∀ s ∈ Set.Icc (0:ℝ) 2, 0 ≤ φ s)
    (hψc : Continuous ψ) (hψm : MonotoneOn ψ (Set.Icc (0:ℝ) 2))
    (hψ0 : ∀ s ∈ Set.Icc (0:ℝ) 2, 0 ≤ ψ s)
    (hχc : Continuous χ) (hχm : MonotoneOn χ (Set.Icc (0:ℝ) 2))
    (hχ0 : χ 0 ≤ 0) (hχ2 : 0 ≤ χ 2)
    (hint : 0 ≤ ∫ s in (0:ℝ)..2, φ s * χ s) :
    0 ≤ ∫ s in (0:ℝ)..2, φ s * ψ s * χ s := by
  have h02 : (0:ℝ) ≤ 2 := by norm_num
  obtain ⟨s₀, hs₀, hs₀eq⟩ := (intermediate_value_Icc h02 hχc.continuousOn)
      (Set.mem_Icc.mpr ⟨hχ0, hχ2⟩)
  rw [Set.mem_Icc] at hs₀
  obtain ⟨hs₀0, hs₀2⟩ := hs₀
  have hψs₀ : 0 ≤ ψ s₀ := hψ0 s₀ (Set.mem_Icc.mpr ⟨hs₀0, hs₀2⟩)
  have hptL : ∀ s ∈ Set.Icc (0:ℝ) s₀, ψ s₀ * (φ s * χ s) ≤ φ s * ψ s * χ s := by
    intro s hs
    rw [Set.mem_Icc] at hs
    have hs' : s ∈ Set.Icc (0:ℝ) 2 := ⟨hs.1, le_trans hs.2 hs₀2⟩
    have hχs : χ s ≤ 0 := by
      have h := hχm hs' (Set.mem_Icc.mpr ⟨hs₀0, hs₀2⟩) hs.2
      rwa [hs₀eq] at h
    have hψs : ψ s ≤ ψ s₀ := hψm hs' (Set.mem_Icc.mpr ⟨hs₀0, hs₀2⟩) hs.2
    have hφs : 0 ≤ φ s := hφ0 s hs'
    have h1 : φ s * χ s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hφs hχs
    have h2 : ψ s - ψ s₀ ≤ 0 := by linarith
    have h3 : 0 ≤ (φ s * χ s) * (ψ s - ψ s₀) := mul_nonneg_of_nonpos_of_nonpos h1 h2
    nlinarith [h3]
  have hptR : ∀ s ∈ Set.Icc s₀ 2, ψ s₀ * (φ s * χ s) ≤ φ s * ψ s * χ s := by
    intro s hs
    rw [Set.mem_Icc] at hs
    have hs' : s ∈ Set.Icc (0:ℝ) 2 := ⟨le_trans hs₀0 hs.1, hs.2⟩
    have hχs : 0 ≤ χ s := by
      have h := hχm (Set.mem_Icc.mpr ⟨hs₀0, hs₀2⟩) hs' hs.1
      rwa [hs₀eq] at h
    have hψs : ψ s₀ ≤ ψ s := hψm (Set.mem_Icc.mpr ⟨hs₀0, hs₀2⟩) hs' hs.1
    have hφs : 0 ≤ φ s := hφ0 s hs'
    have h3 : 0 ≤ (φ s * χ s) * (ψ s - ψ s₀) :=
      mul_nonneg (mul_nonneg hφs hχs) (by linarith)
    nlinarith [h3]
  have hint1 : IntervalIntegrable (fun s : ℝ => ψ s₀ * (φ s * χ s)) volume (0:ℝ) s₀ :=
    (continuous_const.mul (hφc.mul hχc)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun s : ℝ => φ s * ψ s * χ s) volume (0:ℝ) s₀ :=
    ((hφc.mul hψc).mul hχc).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun s : ℝ => ψ s₀ * (φ s * χ s)) volume s₀ 2 :=
    (continuous_const.mul (hφc.mul hχc)).intervalIntegrable _ _
  have hint4 : IntervalIntegrable (fun s : ℝ => φ s * ψ s * χ s) volume s₀ 2 :=
    ((hφc.mul hψc).mul hχc).intervalIntegrable _ _
  have hint5 : IntervalIntegrable (fun s : ℝ => φ s * χ s) volume (0:ℝ) s₀ :=
    (hφc.mul hχc).intervalIntegrable _ _
  have hint6 : IntervalIntegrable (fun s : ℝ => φ s * χ s) volume s₀ 2 :=
    (hφc.mul hχc).intervalIntegrable _ _
  have hL := intervalIntegral.integral_mono_on hs₀0 hint1 hint2 hptL
  have hR := intervalIntegral.integral_mono_on hs₀2 hint3 hint4 hptR
  rw [intervalIntegral.integral_const_mul] at hL hR
  have hsum : ψ s₀ * (∫ s in (0:ℝ)..s₀, φ s * χ s) + ψ s₀ * (∫ s in s₀..2, φ s * χ s)
      = ψ s₀ * (∫ s in (0:ℝ)..2, φ s * χ s) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint5 hint6]
    ring
  have hfin : 0 ≤ ψ s₀ * (∫ s in (0:ℝ)..2, φ s * χ s) := mul_nonneg hψs₀ hint
  rw [← intervalIntegral.integral_add_adjacent_intervals hint2 hint4]
  linarith [hL, hR, hsum, hfin]

/-- Linearity of the interval integral for the four-term combination. -/
lemma integral_lin4 (c d : ℝ) (F₁ F₂ G₁ G₂ : ℝ → ℝ)
    (h1 : IntervalIntegrable F₁ volume (0:ℝ) 2) (h2 : IntervalIntegrable F₂ volume (0:ℝ) 2)
    (h3 : IntervalIntegrable G₁ volume (0:ℝ) 2) (h4 : IntervalIntegrable G₂ volume (0:ℝ) 2) :
    (∫ s in (0:ℝ)..2, (c * (F₁ s - F₂ s) - d * (G₁ s - G₂ s)))
      = c * ((∫ s in (0:ℝ)..2, F₁ s) - (∫ s in (0:ℝ)..2, F₂ s))
        - d * ((∫ s in (0:ℝ)..2, G₁ s) - (∫ s in (0:ℝ)..2, G₂ s)) := by
  rw [intervalIntegral.integral_sub ((h1.sub h2).const_mul c) ((h3.sub h4).const_mul d)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_sub h3 h4]

/-- Linearity for a two-term combination. -/
lemma integral_lin2 {c d : ℝ} (F G : ℝ → ℝ)
    (hF : IntervalIntegrable F volume (0:ℝ) 2) (hG : IntervalIntegrable G volume (0:ℝ) 2) :
    (∫ s in (0:ℝ)..2, (c * F s - d * G s)) = c * (∫ s in (0:ℝ)..2, F s) - d * (∫ s in (0:ℝ)..2, G s) := by
  rw [intervalIntegral.integral_sub (hF.const_mul c) (hG.const_mul d)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- The `χ` of the monotone-weight argument at `(a,b,λ,k)`. -/
def tf72Chi (a b lam k : ℝ) : ℝ → ℝ :=
  fun s => (k^2 + 1/2) * Real.exp (a*s/lam) - 2*k*Real.exp (-((b-a)*s/lam))

theorem tf72Phi_mono_step_aux (a b lam k u : ℝ) (hl : 0 < lam) (ha0 : 0 ≤ a) (hba : a ≤ b)
    (hua : u ≤ a) (hk : 0 ≤ k)
    (h1 : k^2 + 1/2 ≤ 2*k) (h2 : 2*k ≤ (k^2 + 1/2) * Real.exp (2*a/lam))
    (h3 : 2*k*tf72Phi ((b-a)/lam) ≤ (k^2 + 1/2)*tf72Phi (-(a/lam))) :
    (k^2 + 1/2)*tf72Phi (-(u/lam)) - 2*k*tf72Phi ((b-u)/lam)
      ≤ (k^2 + 1/2)*tf72Phi (-(a/lam)) - 2*k*tf72Phi ((b-a)/lam) := by
  -- integral representations
  have contF : ∀ c : ℝ, Continuous (fun s : ℝ => Real.exp (c*s/lam) * tf72Body s) := fun c =>
    (Real.continuous_exp.comp (by fun_prop)).mul continuous_tf72Body
  have contG : ∀ c : ℝ, Continuous (fun s : ℝ => Real.exp (-(c*s/lam)) * tf72Body s) := fun c =>
    (Real.continuous_exp.comp (by fun_prop)).mul continuous_tf72Body
  have hIa : tf72Phi (-(a/lam))
      = (1/30) * ∫ s in (0:ℝ)..2, Real.exp (a*s/lam) * tf72Body s := by
    rw [tf72Phi]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show -((-(a/lam)) * s) = a*s/lam by ring]
  have hIu : tf72Phi (-(u/lam))
      = (1/30) * ∫ s in (0:ℝ)..2, Real.exp (u*s/lam) * tf72Body s := by
    rw [tf72Phi]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show -((-(u/lam)) * s) = u*s/lam by ring]
  have hIba : tf72Phi ((b-a)/lam)
      = (1/30) * ∫ s in (0:ℝ)..2, Real.exp (-((b-a)*s/lam)) * tf72Body s := by
    rw [tf72Phi]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show -(((b-a)/lam) * s) = -((b-a)*s/lam) by ring]
  have hIbu : tf72Phi ((b-u)/lam)
      = (1/30) * ∫ s in (0:ℝ)..2, Real.exp (-((b-u)*s/lam)) * tf72Body s := by
    rw [tf72Phi]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show -(((b-u)/lam) * s) = -((b-u)*s/lam) by ring]
  -- the monotone-weight hypotheses
  have hχm : MonotoneOn (tf72Chi a b lam k) (Set.Icc (0:ℝ) 2) := by
    intro s₁ hs₁ s₂ hs₂ hs12
    have ha' : 0 ≤ a := ha0
    have hb' : 0 ≤ b - a := by linarith
    have h1' : Real.exp (a*s₁/lam) ≤ Real.exp (a*s₂/lam) := by
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs12 ha0) hl.le
    have h2' : Real.exp (-((b-a)*s₂/lam)) ≤ Real.exp (-((b-a)*s₁/lam)) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs12 hb') hl.le
    have hk2 : (0:ℝ) ≤ k^2+1/2 := by positivity
    have hn2 : -2*k ≤ 0 := by linarith
    have e1 := mul_le_mul_of_nonneg_left h1' hk2
    have e2 := mul_le_mul_of_nonpos_left h2' hn2
    simp only [tf72Chi]
    linarith [e1, e2]
  have hχ0 : tf72Chi a b lam k 0 ≤ 0 := by
    simp only [tf72Chi, mul_zero, zero_div, neg_zero, Real.exp_zero, mul_one]
    linarith
  have hχ2 : 0 ≤ tf72Chi a b lam k 2 := by
    simp only [tf72Chi]
    have hexp1 : Real.exp (-((b-a)*2/lam)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (b-a)*2/lam := div_nonneg (by nlinarith) hl.le
      linarith
    have hstep : 2*k*Real.exp (-((b-a)*2/lam)) ≤ 2*k := by
      calc 2*k*Real.exp (-((b-a)*2/lam)) ≤ 2*k*1 :=
            mul_le_mul_of_nonneg_left hexp1 (by linarith)
        _ = 2*k := by ring
    have harg : a*2/lam = 2*a/lam := by ring
    rw [harg]
    linarith [h2, hstep]
  have hint : 0 ≤ ∫ s in (0:ℝ)..2, tf72Body s * tf72Chi a b lam k s := by
    have hfun : (fun s : ℝ => tf72Body s * tf72Chi a b lam k s)
        = fun s : ℝ => ((k^2+1/2) * (Real.exp (a*s/lam)*tf72Body s)
            - 2*k * (Real.exp (-((b-a)*s/lam))*tf72Body s)) := by
      funext s; simp only [tf72Chi]; ring
    rw [hfun, integral_lin2 (F := fun s : ℝ => Real.exp (a*s/lam)*tf72Body s)
        (G := fun s : ℝ => Real.exp (-((b-a)*s/lam))*tf72Body s)
        ((contF a).intervalIntegrable 0 2) ((contG (b-a)).intervalIntegrable 0 2)]
    have h30 : (k^2+1/2) * (∫ s in (0:ℝ)..2, Real.exp (a*s/lam) * tf72Body s)
        = 30 * ((k^2+1/2) * tf72Phi (-(a/lam))) := by
      rw [hIa]; ring
    have h31 : 2*k * (∫ s in (0:ℝ)..2, Real.exp (-((b-a)*s/lam)) * tf72Body s)
        = 30 * (2*k * tf72Phi ((b-a)/lam)) := by
      rw [hIba]; ring
    linarith [h30, h31, h3]
  -- the pointwise identity linking the two sides
  have hpt : ∀ s : ℝ, tf72Body s * (1 - Real.exp (-((a-u)*s/lam))) * tf72Chi a b lam k s
      = ((k^2+1/2) * (Real.exp (a*s/lam)*tf72Body s - Real.exp (u*s/lam)*tf72Body s)
          - 2*k * (Real.exp (-((b-a)*s/lam))*tf72Body s - Real.exp (-((b-u)*s/lam))*tf72Body s)) := by
    intro s
    have hmu : Real.exp (u*s/lam) = Real.exp (a*s/lam) * Real.exp (-((a-u)*s/lam)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hga : Real.exp (-((b-u)*s/lam))
        = Real.exp (-((b-a)*s/lam)) * Real.exp (-((a-u)*s/lam)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hmu, hga]
    simp only [tf72Chi]
    ring
  -- conclusion
  have hw := integral_monotone_weight tf72Body (fun s : ℝ => 1 - Real.exp (-((a-u)*s/lam)))
      (tf72Chi a b lam k)
      continuous_tf72Body (fun s hs => tf72Body_nonneg' s hs)
      ((continuous_const.sub (Real.continuous_exp.comp (by fun_prop))))
      (by
        intro s₁ hs₁ s₂ hs₂ hs12
        show 1 - Real.exp (-((a-u)*s₁/lam)) ≤ 1 - Real.exp (-((a-u)*s₂/lam))
        have hc : 0 ≤ a-u := by linarith
        apply sub_le_sub_left
        apply Real.exp_le_exp.mpr
        have h1 : (a-u)*s₁ ≤ (a-u)*s₂ := mul_le_mul_of_nonneg_left hs12 hc
        have h2 : (a-u)*s₁/lam ≤ (a-u)*s₂/lam := div_le_div_of_nonneg_right h1 hl.le
        linarith)
      (by
        intro s hs
        show 0 ≤ 1 - Real.exp (-((a-u)*s/lam))
        rw [sub_nonneg]
        rw [Real.exp_le_one_iff]
        have : 0 ≤ (a-u)*s/lam := div_nonneg (mul_nonneg (by linarith) hs.1) hl.le
        linarith)
      ((continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).sub
        (continuous_const.mul (Real.continuous_exp.comp (by fun_prop))))
      hχm hχ0 hχ2 hint
  -- finish
  rw [hIa, hIu, hIba, hIbu]
  have hlin2 : (∫ s in (0:ℝ)..2, tf72Body s * (1 - Real.exp (-((a-u)*s/lam))) * tf72Chi a b lam k s)
      = ((k^2+1/2) * ((∫ s in (0:ℝ)..2, Real.exp (a*s/lam)*tf72Body s)
            - (∫ s in (0:ℝ)..2, Real.exp (u*s/lam)*tf72Body s))
        - 2*k * ((∫ s in (0:ℝ)..2, Real.exp (-((b-a)*s/lam))*tf72Body s)
            - (∫ s in (0:ℝ)..2, Real.exp (-((b-u)*s/lam))*tf72Body s))) := by
    rw [intervalIntegral.integral_congr (fun s _ => hpt s),
        integral_lin4 (k^2+1/2) (2*k)
          (F₁ := fun s : ℝ => Real.exp (a*s/lam)*tf72Body s)
          (F₂ := fun s : ℝ => Real.exp (u*s/lam)*tf72Body s)
          (G₁ := fun s : ℝ => Real.exp (-((b-a)*s/lam))*tf72Body s)
          (G₂ := fun s : ℝ => Real.exp (-((b-u)*s/lam))*tf72Body s)
          ((contF a).intervalIntegrable 0 2) ((contF u).intervalIntegrable 0 2)
          ((contG (b-a)).intervalIntegrable 0 2) ((contG (b-u)).intervalIntegrable 0 2)]
  linarith [hw, hlin2]


/-- The additive constant `f(0)((k²+4k+3/2)(1/6+ε))` of the Lemma 9.3 inequality,
with `f(0) = 16λ/15` and `ε = 10⁻⁶`. -/
def tf72C (lam k : ℝ) : ℝ :=
  (16*lam/15) * ((k^2 + 4*k + 3/2) * ((1:ℝ)/6 + 1/1000000))

/-- Region-form certificate for HB Lemma 9.3 in terms of `tf72Phi`.
`h1`, `h2`, `h3` are the hypotheses of `tf72Phi_mono_step` (with `h2` in the
rational form `2k ≤ (k²+½)(1+2a/λ)`), `h4` is the scalar value at the right
endpoint `u = a` certified by the rational bounds. -/
theorem rowcert_phi (a b lam k : ℝ) (hl : 0 < lam) (hk : 0 ≤ k)
    (ha0 : 0 ≤ a) (hba : a ≤ b) (hal : a/lam ≤ 2) (hbl : (b-a)/lam ≤ 2)
    (h1 : k^2 + 1/2 ≤ 2*k)
    (h2 : 2*k ≤ (k^2 + 1/2) * (1 + 2*a/lam))
    (h3 : 2*k*tf72PhiUBpos ((b-a)/lam) ≤ (k^2 + 1/2)*tf72PhiLBneg (a/lam))
    (h4 : (k^2 + 1/2) * (tf72PhiUB (a/lam) - 8/9) - 2*k*tf72PhiLB ((b-a)/lam)
        + tf72C lam k < 0) :
    ∀ u v : ℝ, (348:ℝ)/1000 ≤ u → u ≤ a → u ≤ v → v ≤ b →
      (k^2 + 1/2) * (tf72Phi (-(u/lam)) - 8/9) - 2*k*tf72Phi ((v-u)/lam)
        + tf72C lam k < 0 := by
  intro u v hu0 hua huv hvb
  have h2k : -2*k ≤ 0 := by linarith
  have hk2 : (0:ℝ) ≤ k^2 + 1/2 := by positivity
  -- the `v`-dependence
  have step_v : (k^2+1/2)*(tf72Phi (-(u/lam)) - 8/9) - 2*k*tf72Phi ((v-u)/lam)
      + tf72C lam k
      ≤ (k^2+1/2)*(tf72Phi (-(u/lam)) - 8/9) - 2*k*tf72Phi ((b-u)/lam)
        + tf72C lam k := by
    have hvu : (v - u)/lam ≤ (b - u)/lam :=
      div_le_div_of_nonneg_right (by linarith) hl.le
    have hv : tf72Phi ((b - u)/lam) ≤ tf72Phi ((v - u)/lam) := tf72Phi_antitone hvu
    have := mul_le_mul_of_nonpos_left hv h2k
    linarith [this]
  -- the `u`-dependence
  have h2e : 2*k ≤ (k^2 + 1/2) * Real.exp (2*a/lam) := by
    have hexp : 1 + 2*a/lam ≤ Real.exp (2*a/lam) := by
      have := Real.add_one_le_exp (2*a/lam)
      linarith
    have := mul_le_mul_of_nonneg_left hexp hk2
    linarith [this, h2]
  have h3' : 2*k*tf72Phi ((b-a)/lam) ≤ (k^2 + 1/2)*tf72Phi (-(a/lam)) := by
    have hL : tf72PhiLBneg (a/lam) ≤ tf72Phi (-(a/lam)) :=
      tf72Phi_neg_lower (a/lam) (by positivity) hal
    have hU : tf72Phi ((b-a)/lam) ≤ tf72PhiUBpos ((b-a)/lam) :=
      tf72Phi_pos_upper ((b-a)/lam) (by positivity) hbl
    have hA : 2*k*tf72Phi ((b-a)/lam) ≤ 2*k*tf72PhiUBpos ((b-a)/lam) :=
      mul_le_mul_of_nonneg_left hU (by linarith : (0:ℝ) ≤ 2*k)
    have hB : (k^2+1/2)*tf72PhiLBneg (a/lam) ≤ (k^2+1/2)*tf72Phi (-(a/lam)) :=
      mul_le_mul_of_nonneg_left hL hk2
    linarith [hA, hB, h3]
  have step_u : (k^2+1/2)*(tf72Phi (-(u/lam)) - 8/9) - 2*k*tf72Phi ((b-u)/lam)
      + tf72C lam k
      ≤ (k^2+1/2)*(tf72Phi (-(a/lam)) - 8/9) - 2*k*tf72Phi ((b-a)/lam)
        + tf72C lam k := by
    have mono := tf72Phi_mono_step_aux a b lam k u hl ha0 hba hua hk h1 h2e h3'
    linarith [mono]
  -- the scalar value at `u = a`
  have h4' : (k^2+1/2)*(tf72Phi (-(a/lam)) - 8/9) - 2*k*tf72Phi ((b-a)/lam)
      + tf72C lam k < 0 := by
    have hU2 : tf72Phi (-(a/lam)) ≤ tf72PhiUB (a/lam) :=
      tf72Phi_upper (a/lam) (by positivity) hal
    have hL2 : tf72PhiLB ((b-a)/lam) ≤ tf72Phi ((b-a)/lam) :=
      tf72Phi_lower ((b-a)/lam) (by positivity) hbl
    have hB1 : tf72Phi (-(a/lam)) - 8/9 ≤ tf72PhiUB (a/lam) - 8/9 := by linarith [hU2]
    have hB := mul_le_mul_of_nonneg_left hB1 hk2
    have hC : -2*k*tf72Phi ((b-a)/lam) ≤ -2*k*tf72PhiLB ((b-a)/lam) :=
      mul_le_mul_of_nonpos_left hL2 h2k
    linarith [hB, hC, h4]
  linarith [step_v, step_u, h4']

/-- Region-form certificate for HB Lemma 9.3, in the form used by the target
theorem (the left-hand side of the Lemma 9.3 inequality for the test function
`tf72T lam`). -/
theorem rowcert (a b lam k : ℝ) (hl : 0 < lam) (hk : 0 ≤ k)
    (ha0 : 0 ≤ a) (hba : a ≤ b) (hal : a/lam ≤ 2) (hbl : (b-a)/lam ≤ 2)
    (h1 : k^2 + 1/2 ≤ 2*k)
    (h2 : 2*k ≤ (k^2 + 1/2) * (1 + 2*a/lam))
    (h3 : 2*k*tf72PhiUBpos ((b-a)/lam) ≤ (k^2 + 1/2)*tf72PhiLBneg (a/lam))
    (h4 : (k^2 + 1/2) * (tf72PhiUB (a/lam) - 8/9) - 2*k*tf72PhiLB ((b-a)/lam)
        + tf72C lam k < 0) :
    ∀ u v : ℝ, (348:ℝ)/1000 ≤ u → u ≤ a → u ≤ v → v ≤ b →
      (k ^ 2 + 1 / 2) * ((tf72T lam hl).F (-u) - (tf72T lam hl).F 0)
        - 2 * k * (tf72T lam hl).F (v - u)
        + (tf72T lam hl).f 0 * ((k ^ 2 + 4 * k + 3 / 2) * ((1:ℝ)/6 + 1/1000000)) < 0 := by
  intro u v hu0 hua huv hvb
  have h := rowcert_phi a b lam k hl hk ha0 hba hal hbl h1 h2 h3 h4 u v hu0 hua huv hvb
  have hF1 : (tf72T lam hl).F (-u) = tf72Phi (-(u/lam)) := by
    rw [tf72F_eq_Phi lam hl (-u), neg_div]
  have h0 : (tf72T lam hl).F 0 = 8/9 := by
    rw [tf72F_eq_Phi lam hl 0, zero_div, tf72Phi_zero]
  have hF2 : (tf72T lam hl).F (v-u) = tf72Phi ((v-u)/lam) := tf72F_eq_Phi lam hl (v-u)
  have hf : (tf72T lam hl).f 0 = 16*lam/15 := tf72f_at_zero lam hl
  rw [hF1, h0, hF2, hf, tf72C] at *
  exact h



/-- Region-form numerical certificates for the Table 10 rows with `λ₁ ≥ 0.36`, for
**HB Lemma 9.3**'s inequality
`(k²+½)(F(−λ₁) − F(0)) − 2k F(λ₂−λ₁) + f(0)((k²+4k+3/2)(1/6+ε)) ≥ 0`:
for each row `p = (a,b)` of `hbTable10` with `a ≥ 0.36` there are `lam > 0`, `k ≥ 0` such that
on the whole region `λ₁ ∈ [348/1000, a]`, `λ₂ ∈ [λ₁, b]` the left-hand side is **negative**,
with the test function of HB Lemma 7.2 (`tf72T`). -/
theorem table10_93_cert :
    ∀ p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable10,
      (36/100 : ℝ) ≤ p.1 →
      ∃ (lam k : ℝ) (hl : 0 < lam), 0 ≤ k ∧
        ∀ u v : ℝ, 348/1000 ≤ u → u ≤ p.1 → u ≤ v → v ≤ p.2 →
          (k ^ 2 + 1 / 2) * ((Work.ZeroFreeTables.tf72T lam hl).F (-u)
              - (Work.ZeroFreeTables.tf72T lam hl).F 0)
            - 2 * k * (Work.ZeroFreeTables.tf72T lam hl).F (v - u)
            + (Work.ZeroFreeTables.tf72T lam hl).f 0 *
                ((k ^ 2 + 4 * k + 3 / 2) * ((1:ℝ)/6 + 1/1000000)) < 0 := by
  intro p hp h36
  simp only [tableR, hbTable10, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨q, hq, rfl⟩
  rcases hq with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · -- (34/100, 929/1000): excluded by the hypothesis `36/100 ≤ λ₁`
    subst h
    exact absurd h36 (by norm_num)
  · -- (36/100, 903/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨3/4, 91/100, by norm_num, by norm_num, ?_⟩
    refine rowcert ((36/100 : ℚ) : ℝ) ((903/1000 : ℚ) : ℝ) (3/4) (91/100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (38/100, 887/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨19/25, 91/100, by norm_num, by norm_num, ?_⟩
    refine rowcert ((38/100 : ℚ) : ℝ) ((887/1000 : ℚ) : ℝ) (19/25) (91/100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (40/100, 871/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨19/25, 9/10, by norm_num, by norm_num, ?_⟩
    refine rowcert ((40/100 : ℚ) : ℝ) ((871/1000 : ℚ) : ℝ) (19/25) (9/10)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (42/100, 856/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨77/100, 9/10, by norm_num, by norm_num, ?_⟩
    refine rowcert ((42/100 : ℚ) : ℝ) ((856/1000 : ℚ) : ℝ) (77/100) (9/10)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (44/100, 842/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨39/50, 9/10, by norm_num, by norm_num, ?_⟩
    refine rowcert ((44/100 : ℚ) : ℝ) ((842/1000 : ℚ) : ℝ) (39/50) (9/10)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (46/100, 829/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨79/100, 89/100, by norm_num, by norm_num, ?_⟩
    refine rowcert ((46/100 : ℚ) : ℝ) ((829/1000 : ℚ) : ℝ) (79/100) (89/100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (48/100, 816/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨4/5, 89/100, by norm_num, by norm_num, ?_⟩
    refine rowcert ((48/100 : ℚ) : ℝ) ((816/1000 : ℚ) : ℝ) (4/5) (89/100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (50/100, 803/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨81/100, 89/100, by norm_num, by norm_num, ?_⟩
    refine rowcert ((50/100 : ℚ) : ℝ) ((803/1000 : ℚ) : ℝ) (81/100) (89/100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (52/100, 791/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨81/100, 22/25, by norm_num, by norm_num, ?_⟩
    refine rowcert ((52/100 : ℚ) : ℝ) ((791/1000 : ℚ) : ℝ) (81/100) (22/25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (54/100, 780/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨41/50, 22/25, by norm_num, by norm_num, ?_⟩
    refine rowcert ((54/100 : ℚ) : ℝ) ((780/1000 : ℚ) : ℝ) (41/50) (22/25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (56/100, 769/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨83/100, 22/25, by norm_num, by norm_num, ?_⟩
    refine rowcert ((56/100 : ℚ) : ℝ) ((769/1000 : ℚ) : ℝ) (83/100) (22/25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (58/100, 759/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨21/25, 87/100, by norm_num, by norm_num, ?_⟩
    refine rowcert ((58/100 : ℚ) : ℝ) ((759/1000 : ℚ) : ℝ) (21/25) (87/100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (60/100, 749/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨21/25, 87/100, by norm_num, by norm_num, ?_⟩
    refine rowcert ((60/100 : ℚ) : ℝ) ((749/1000 : ℚ) : ℝ) (21/25) (87/100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (62/100, 739/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨17/20, 87/100, by norm_num, by norm_num, ?_⟩
    refine rowcert ((62/100 : ℚ) : ℝ) ((739/1000 : ℚ) : ℝ) (17/20) (87/100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (64/100, 730/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨43/50, 87/100, by norm_num, by norm_num, ?_⟩
    refine rowcert ((64/100 : ℚ) : ℝ) ((730/1000 : ℚ) : ℝ) (43/50) (87/100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (66/100, 721/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨43/50, 43/50, by norm_num, by norm_num, ?_⟩
    refine rowcert ((66/100 : ℚ) : ℝ) ((721/1000 : ℚ) : ℝ) (43/50) (43/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (68/100, 712/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨87/100, 43/50, by norm_num, by norm_num, ?_⟩
    refine rowcert ((68/100 : ℚ) : ℝ) ((712/1000 : ℚ) : ℝ) (87/100) (43/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (70/100, 704/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨22/25, 43/50, by norm_num, by norm_num, ?_⟩
    refine rowcert ((70/100 : ℚ) : ℝ) ((704/1000 : ℚ) : ℝ) (22/25) (43/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]
  · -- (702/1000, 702/1000)
    subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨22/25, 43/50, by norm_num, by norm_num, ?_⟩
    refine rowcert ((702/1000 : ℚ) : ℝ) ((702/1000 : ℚ) : ℝ) (22/25) (43/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · norm_num [tf72PhiUBpos, tf72PhiLBneg, tf72M, Finset.sum_range_succ, Nat.factorial]
    · norm_num [tf72PhiUB, tf72PhiLB, tf72M, tf72C, Finset.sum_range_succ, Nat.factorial]

end

end Work.ZeroFreeTables
