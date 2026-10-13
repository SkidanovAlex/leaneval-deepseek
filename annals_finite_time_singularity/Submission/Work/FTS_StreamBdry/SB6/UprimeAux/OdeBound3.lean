import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.Defs
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.Temps
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound1
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound3` — the final bound for the singular `θ`-ODE

Combining the two endpoint representations with the elementary integral bounds and the lower
bounds on `wfun` gives a bound on `|u'|` on `(0, π/2)` which is uniform in the parameter `z`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6.UprimeAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- The constant of the left half. -/
def Kleft (A C : ℝ) : ℝ := Real.pi ^ 2 / Real.sqrt 2 * (A / 4 + C * Real.pi / 12)

/-- The constant of the right half. -/
def Kright (A C : ℝ) : ℝ := Real.pi ^ 3 / 4 * (A / 6 + C * Real.pi / 8)

lemma Kleft_nonneg {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) : 0 ≤ Kleft A C := by
  rw [Kleft]
  have : 0 ≤ A / 4 + C * Real.pi / 12 := by positivity
  positivity

lemma Kright_nonneg {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) : 0 ≤ Kright A C := by
  rw [Kright]
  have : 0 ≤ A / 6 + C * Real.pi / 8 := by positivity
  positivity

lemma sqrt2_ne_zero : (Real.sqrt 2 : ℝ) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (by norm_num))

lemma Kleft_arith {A C θ w : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hθ : 0 < θ)
    (hθle : θ ≤ Real.pi / 4) (hw : Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2 ≤ w) :
    (A * (θ ^ 2 / 4) + C * (θ ^ 3 / 3)) / w ≤ Kleft A C := by
  have hwpos : 0 < w := lt_of_lt_of_le (by positivity) hw
  rw [div_le_iff₀ hwpos, Kleft]
  have hAB : A / 4 + C * θ / 3 ≤ A / 4 + C * Real.pi / 12 := by
    have h : θ / 3 ≤ Real.pi / 12 := by linarith [hθle, Real.pi_pos]
    nlinarith [hC, h]
  have hABnn : 0 ≤ A / 4 + C * Real.pi / 12 := by positivity
  have hcoef : 0 ≤ Real.pi ^ 2 / Real.sqrt 2 := by positivity
  have hrat : θ ^ 2 ≤ (Real.pi ^ 2 / Real.sqrt 2) * (Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2) := by
    have h2 : (Real.pi ^ 2 / Real.sqrt 2) * (Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2) = θ ^ 2 := by
      field_simp
      try ring
    linarith [h2]
  have hstep1 : θ ^ 2 * (A / 4 + C * Real.pi / 12)
      ≤ (Real.pi ^ 2 / Real.sqrt 2 * (A / 4 + C * Real.pi / 12))
        * (Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hrat hABnn
    calc θ ^ 2 * (A / 4 + C * Real.pi / 12)
        = (A / 4 + C * Real.pi / 12) * θ ^ 2 := by ring
      _ ≤ (A / 4 + C * Real.pi / 12)
            * ((Real.pi ^ 2 / Real.sqrt 2) * (Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2)) := h
      _ = (Real.pi ^ 2 / Real.sqrt 2 * (A / 4 + C * Real.pi / 12))
            * (Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2) := by ring
  calc A * (θ ^ 2 / 4) + C * (θ ^ 3 / 3)
      = θ ^ 2 * (A / 4 + C * θ / 3) := by ring
    _ ≤ θ ^ 2 * (A / 4 + C * Real.pi / 12) := mul_le_mul_of_nonneg_left hAB (sq_nonneg θ)
    _ ≤ (Real.pi ^ 2 / Real.sqrt 2 * (A / 4 + C * Real.pi / 12))
          * (Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2) := hstep1
    _ ≤ (Real.pi ^ 2 / Real.sqrt 2 * (A / 4 + C * Real.pi / 12)) * w :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hcoef hABnn)

lemma Kright_arith {A C θ w : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hδ : 0 < Real.pi / 2 - θ)
    (hδle : Real.pi / 2 - θ ≤ Real.pi / 2)
    (hw : 4 * (Real.pi / 2 - θ) ^ 3 / Real.pi ^ 3 ≤ w) :
    (A * ((Real.pi / 2 - θ) ^ 3 / 6) + C * ((Real.pi / 2 - θ) ^ 4 / 4)) / w
      ≤ Kright A C := by
  set δ := Real.pi / 2 - θ with hδdef
  have hδpos : 0 < δ := hδdef ▸ hδ
  have hwpos : 0 < w := lt_of_lt_of_le (by positivity) hw
  rw [div_le_iff₀ hwpos, Kright]
  have hAB : A / 6 + C * δ / 4 ≤ A / 6 + C * Real.pi / 8 := by
    have h : δ / 4 ≤ Real.pi / 8 := by rw [hδdef]; linarith [hδle]
    nlinarith [hC, h]
  have hABnn : 0 ≤ A / 6 + C * Real.pi / 8 := by positivity
  have hcoef : 0 ≤ Real.pi ^ 3 / 4 := by positivity
  have hrat : δ ^ 3 ≤ (Real.pi ^ 3 / 4) * (4 * δ ^ 3 / Real.pi ^ 3) := by
    have h2 : (Real.pi ^ 3 / 4) * (4 * δ ^ 3 / Real.pi ^ 3) = δ ^ 3 := by
      field_simp
      try ring
    linarith [h2]
  have hstep1 : δ ^ 3 * (A / 6 + C * Real.pi / 8)
      ≤ (Real.pi ^ 3 / 4 * (A / 6 + C * Real.pi / 8)) * (4 * δ ^ 3 / Real.pi ^ 3) := by
    have h := mul_le_mul_of_nonneg_left hrat hABnn
    calc δ ^ 3 * (A / 6 + C * Real.pi / 8)
        = (A / 6 + C * Real.pi / 8) * δ ^ 3 := by ring
      _ ≤ (A / 6 + C * Real.pi / 8)
            * ((Real.pi ^ 3 / 4) * (4 * δ ^ 3 / Real.pi ^ 3)) := h
      _ = (Real.pi ^ 3 / 4 * (A / 6 + C * Real.pi / 8)) * (4 * δ ^ 3 / Real.pi ^ 3) := by ring
  calc A * (δ ^ 3 / 6) + C * (δ ^ 4 / 4)
      = δ ^ 3 * (A / 6 + C * δ / 4) := by ring
    _ ≤ δ ^ 3 * (A / 6 + C * Real.pi / 8) :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
    _ ≤ (Real.pi ^ 3 / 4 * (A / 6 + C * Real.pi / 8)) * (4 * δ ^ 3 / Real.pi ^ 3) := hstep1
    _ ≤ (Real.pi ^ 3 / 4 * (A / 6 + C * Real.pi / 8)) * w :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hcoef hABnn)

/-- **The `z`-fixed bound**: the singular ODE forces `|u'| ≤ max Kleft Kright` on `(0, π/2)`. -/
lemma ode_z {u H : ℝ → ℝ → ℝ} {z A C C₁ : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hode : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (u1fun u z)
        (H z θ - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * u1fun u z θ) θ)
    (hH : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |H z θ| ≤ A / Real.sin (2 * θ) + C)
    (hcrude : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.sin (2 * θ) * u1fun u z θ| ≤ C₁) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u1fun u z θ| ≤ max (Kleft A C) (Kright A C) := by
  intro θ hθ
  have hwpos : 0 < wfun θ := Wpos hθ
  have hG : |wfun θ * u1fun u z θ| = wfun θ * |u1fun u z θ| := by
    rw [abs_mul, abs_of_pos hwpos]
  have hcont1 : Continuous (fun t : ℝ => wfun t / Real.sin (2 * t)) := by
    have h : (fun t : ℝ => wfun t / Real.sin (2 * t))
        = fun t => Real.sin t * Real.cos t ^ 2 / 2 := by
      funext t; exact wfun_div_s2_eq t
    rw [h]; fun_prop
  have hcont2 : Continuous wfun := by
    have h : wfun = fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3 := rfl
    rw [h]; fun_prop
  have hsplit : ∀ a b : ℝ, ∫ t in a..b, gwt A C t
      = A * (∫ t in a..b, wfun t / Real.sin (2 * t)) + C * (∫ t in a..b, wfun t) := by
    intro a b
    have h1 : (fun t => gwt A C t)
        = fun t => A * (wfun t / Real.sin (2 * t)) + C * wfun t := by
      funext t; rw [gwt_def]
    rw [h1, intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · exact (hcont1.const_mul A).intervalIntegrable a b
    · exact (hcont2.const_mul C).intervalIntegrable a b
  rcases le_total θ (Real.pi / 4) with hle | hle
  · have hrep := left_rep (u := u) (H := H) (z := z) hA hC hC₁ hode hH hcrude ⟨hθ.1, hle⟩
    have hb1 : ∫ t in (0 : ℝ)..θ, wfun t ≤ θ ^ 3 / 3 := Wint1 ⟨hθ.1.le, hθ.2.le⟩
    have hb2 : ∫ t in (0 : ℝ)..θ, wfun t / Real.sin (2 * t) ≤ θ ^ 2 / 4 :=
      Wint2 ⟨hθ.1.le, hθ.2.le⟩
    have hnum : ∫ t in (0 : ℝ)..θ, gwt A C t ≤ A * (θ ^ 2 / 4) + C * (θ ^ 3 / 3) := by
      rw [hsplit]
      have h2 := mul_le_mul_of_nonneg_left hb2 hA
      have h3 := mul_le_mul_of_nonneg_left hb1 hC
      linarith
    have hfin : |u1fun u z θ| ≤ (A * (θ ^ 2 / 4) + C * (θ ^ 3 / 3)) / wfun θ := by
      rw [le_div_iff₀ hwpos]
      calc |u1fun u z θ| * wfun θ = |wfun θ * u1fun u z θ| := by
            rw [abs_mul, abs_of_pos hwpos, mul_comm]
        _ ≤ ∫ t in (0 : ℝ)..θ, gwt A C t := hrep
        _ ≤ A * (θ ^ 2 / 4) + C * (θ ^ 3 / 3) := hnum
    exact le_trans hfin (le_trans (Kleft_arith hA hC hθ.1 hle (Wge_left ⟨hθ.1, hle⟩))
      (le_max_left _ _))
  · have hrep := right_rep (u := u) (H := H) (z := z) hA hC hC₁ hode hH hcrude ⟨hle, hθ.2⟩
    have hb3 : ∫ t in θ..(Real.pi / 2), wfun t ≤ (Real.pi / 2 - θ) ^ 4 / 4 := Wint3 hθ
    have hb4 : ∫ t in θ..(Real.pi / 2), wfun t / Real.sin (2 * t)
        ≤ (Real.pi / 2 - θ) ^ 3 / 6 := Wint4 hθ
    have hnum : ∫ t in θ..(Real.pi / 2), gwt A C t
        ≤ A * ((Real.pi / 2 - θ) ^ 3 / 6) + C * ((Real.pi / 2 - θ) ^ 4 / 4) := by
      rw [hsplit]
      have h2 := mul_le_mul_of_nonneg_left hb4 hA
      have h3 := mul_le_mul_of_nonneg_left hb3 hC
      linarith
    have hfin : |u1fun u z θ| ≤ (A * ((Real.pi / 2 - θ) ^ 3 / 6)
        + C * ((Real.pi / 2 - θ) ^ 4 / 4)) / wfun θ := by
      rw [le_div_iff₀ hwpos]
      calc |u1fun u z θ| * wfun θ = |wfun θ * u1fun u z θ| := by
            rw [abs_mul, abs_of_pos hwpos, mul_comm]
        _ ≤ ∫ t in θ..(Real.pi / 2), gwt A C t := hrep
        _ ≤ A * ((Real.pi / 2 - θ) ^ 3 / 6) + C * ((Real.pi / 2 - θ) ^ 4 / 4) := hnum
    exact le_trans hfin (le_trans
      (Kright_arith hA hC (by linarith [hθ.2]) (by linarith [hθ.1, Real.pi_pos])
        (Wge_right ⟨hle, hθ.2⟩))
      (le_max_right _ _))

set_option maxHeartbeats 2000000 in
/-- **The singular `θ`-ODE bound, uniformly in `z`.** -/
theorem ode_deriv_bound_fam {u H : ℝ → ℝ → ℝ} {A C C₁ : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hode : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (deriv (fun θ' => u z θ'))
        (H z θ - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ)
          * deriv (fun θ' => u z θ') θ) θ)
    (hH : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |H z θ| ≤ A / Real.sin (2 * θ) + C)
    (hcrude : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Real.sin (2 * θ) * deriv (fun θ' => u z θ') θ| ≤ C₁) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |deriv (fun θ' => u z θ') θ| ≤ K := by
  refine ⟨max (max (Kleft A C) (Kright A C)) 1, ?_, ?_⟩
  · exact le_max_of_le_left (le_max_of_le_left (Kleft_nonneg hA hC))
  · intro z θ hmem
    obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
    have h := ode_z (u := u) (H := H) (z := z) hA hC hC₁
      (fun θ hθ => hode z θ ⟨hz, hθ.1, hθ.2⟩)
      (fun θ hθ => hH z θ ⟨hz, hθ.1, hθ.2⟩)
      (fun θ hθ => hcrude z θ ⟨hz, hθ.1, hθ.2⟩)
      θ ⟨hθ1, hθ2⟩
    exact le_trans h (le_max_of_le_left le_rfl)

end Work.FTS_StreamBdry.SB6.UprimeAux
