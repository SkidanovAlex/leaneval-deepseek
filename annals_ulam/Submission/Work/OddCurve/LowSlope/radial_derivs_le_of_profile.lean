import Mathlib
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddCurve.LowSlope.radial_identity
import Submission.Work.OddCurve.LowSlope.Peano2
import Submission.Work.OddCurve.LowSlope.peano2_mul
import Submission.Work.OddCurve.LowSlope.peano2_comp
import Submission.Work.OddCurve.LowSlope.peano2_of_hasDerivAt_deriv
import Submission.Work.OddCurve.LowSlope.radial_core

/-!
# Bounds on the derivatives of the radial function

(The original statement and its docstring live in the challenge; this file proves it.)

`radial_derivs_le_of_profile`: if `ρ` is the radial function of a profile `f` in the
parametrisation `ρ v * √(1 - v²) = f (ρ v * v)` and `f` is `1/1000`-close to the semicircle in
first and second derivative at the point `ρ u * u`, then `|ρ' u| ≤ 3` and `|ρ'' u| ≤ 30`.

The proof goes through the (pointwise) Peano expansions `Peano2` of `ρ`, `f` and `s = √(1 - ·²)`
at the relevant points: comparing the coefficients of the two `Peano2` expansions of the common
function `v ↦ f (ρ v * v) = ρ v * √(1 - v²)` gives the two relations used by `radial_core`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open Filter Asymptotics
open scoped Topology

/-- `deriv (1 - t²) t = -2t`. -/
lemma radialAux_deriv_one_sub_sq (x : ℝ) : deriv (fun t : ℝ => 1 - t ^ 2) x = -2 * x := by
  rw [deriv_const_sub]
  change -deriv ((fun t : ℝ => t) ^ 2) x = -2 * x
  rw [deriv_pow (by fun_prop)]
  simp

/-- `deriv (√(1 - t²)) t = -t/√(1 - t²)` for `|t| < 1`. -/
lemma radialAux_deriv_sqrt {x : ℝ} (hx : |x| < 1) :
    deriv (fun t : ℝ => Real.sqrt (1 - t ^ 2)) x = -x / Real.sqrt (1 - x ^ 2) := by
  have harg : 0 < 1 - x ^ 2 := by nlinarith [abs_lt.mp hx |>.1, abs_lt.mp hx |>.2]
  rw [deriv_sqrt (f := fun t : ℝ => 1 - t ^ 2) (x := x) (by fun_prop) (by positivity)]
  rw [radialAux_deriv_one_sub_sq]
  field_simp [ne_of_gt harg]

/-- `HasDerivAt (√(1 - t²)) (-u/√(1 - u²)) u`. -/
lemma radialAux_hasDerivAt_sqrt {u : ℝ} (hu : |u| < 1) :
    HasDerivAt (fun v : ℝ => Real.sqrt (1 - v ^ 2)) (-u / Real.sqrt (1 - u ^ 2)) u := by
  have harg : 0 < 1 - u ^ 2 := by nlinarith [abs_lt.mp hu |>.1, abs_lt.mp hu |>.2]
  have hinner : HasDerivAt (fun v : ℝ => 1 - v ^ 2) (-(2 * u)) u := by
    have hh := (hasDerivAt_const (x := u) (c := (1 : ℝ))).sub ((hasDerivAt_id u).pow 2)
    have hfun : ((fun _ : ℝ => (1 : ℝ)) - id ^ 2) = fun v : ℝ => 1 - v ^ 2 := by
      funext v; simp
    rw [hfun] at hh
    refine hh.congr_deriv ?_
    rw [id_eq]
    norm_num
  have hsq := (Real.hasDerivAt_sqrt (x := 1 - u ^ 2) (ne_of_gt harg)).comp u hinner
  have hval : (1 / (2 * Real.sqrt (1 - u ^ 2))) * (-(2 * u)) = (-u) / Real.sqrt (1 - u ^ 2) := by
    field_simp [ne_of_gt harg]
  rwa [hval] at hsq

/-- `HasDerivAt (t ↦ -t/√(1 - t²)) (-1/√(1 - u²)³) u`. -/
lemma radialAux_hasDerivAt_neg_div_sqrt {u : ℝ} (hu : |u| < 1) :
    HasDerivAt (fun t : ℝ => -t / Real.sqrt (1 - t ^ 2))
      (-1 / (Real.sqrt (1 - u ^ 2)) ^ 3) u := by
  have harg : 0 < 1 - u ^ 2 := by nlinarith [abs_lt.mp hu |>.1, abs_lt.mp hu |>.2]
  have hS : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.2 harg
  have hnum : HasDerivAt (fun t : ℝ => -t) (-1) u := by
    have hh := (hasDerivAt_id u).neg
    have hfun : (-id : ℝ → ℝ) = fun t : ℝ => -t := by funext t; simp
    rw [hfun] at hh
    exact hh
  have hden := radialAux_hasDerivAt_sqrt hu
  have hdiv := hnum.div hden (ne_of_gt hS)
  have hfun : ((fun t : ℝ => -t) / fun t : ℝ => Real.sqrt (1 - t ^ 2))
      = fun t : ℝ => -t / Real.sqrt (1 - t ^ 2) := by funext t; simp
  rw [hfun] at hdiv
  refine hdiv.congr_deriv ?_
  have hS2 : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 := Real.sq_sqrt harg.le
  field_simp
  nlinarith [hS2, hS, sq_nonneg (Real.sqrt (1 - u ^ 2))]

/-- `deriv (deriv (√(1 - t²))) x = -1/√(1 - x²)³` for `|x| < 1`. -/
lemma radialAux_deriv_deriv_sqrt {x : ℝ} (hx : |x| < 1) :
    deriv (deriv (fun t : ℝ => Real.sqrt (1 - t ^ 2))) x =
      -1 / (Real.sqrt (1 - x ^ 2)) ^ 3 := by
  have heq : deriv (fun t : ℝ => Real.sqrt (1 - t ^ 2)) =ᶠ[𝓝 x]
      (fun t : ℝ => -t / Real.sqrt (1 - t ^ 2)) := by
    filter_upwards [Ioo_mem_nhds (abs_lt.mp hx).1 (abs_lt.mp hx).2] with t ht
    exact radialAux_deriv_sqrt (by rw [abs_lt]; exact ht)
  rw [Filter.EventuallyEq.deriv_eq heq]
  exact (radialAux_hasDerivAt_neg_div_sqrt hx).deriv

/-- `HasDerivAt (deriv (√(1 - t²))) (-1/√(1 - u²)³) u`. -/
lemma radialAux_hasDerivAt_deriv_sqrt {u : ℝ} (hu : |u| < 1) :
    HasDerivAt (deriv (fun t : ℝ => Real.sqrt (1 - t ^ 2)))
      (-1 / (Real.sqrt (1 - u ^ 2)) ^ 3) u := by
  have heq : deriv (fun t : ℝ => Real.sqrt (1 - t ^ 2)) =ᶠ[𝓝 u]
      (fun t : ℝ => -t / Real.sqrt (1 - t ^ 2)) := by
    filter_upwards [Ioo_mem_nhds (abs_lt.mp hu).1 (abs_lt.mp hu).2] with t ht
    exact radialAux_deriv_sqrt (by rw [abs_lt]; exact ht)
  exact (radialAux_hasDerivAt_neg_div_sqrt hu).congr_of_eventuallyEq heq


theorem radial_derivs_le_of_profile {f ρ : ℝ → ℝ} {u : ℝ}
    (hu : |u| < 1) (hu0 : 0 ≤ u) (hρpos : 0 < ρ u)
    (hgraph : ∀ v ∈ Set.Ioo (-1 : ℝ) 1,
      ρ v * Real.sqrt (1 - v ^ 2) = f (ρ v * v))
    (ht : |ρ u * u| < 1)
    (hρclose : |ρ u - 1| ≤ 1 / 1000)
    (h1 : |deriv f (ρ u * u) - deriv Work.OddEnvelope.semicircle (ρ u * u)| ≤ 1 / 1000)
    (h2 : |deriv (deriv f) (ρ u * u) - deriv (deriv Work.OddEnvelope.semicircle) (ρ u * u)|
      ≤ 1 / 1000)
    (hd1 : HasDerivAt f (deriv f (ρ u * u)) (ρ u * u))
    (hd2 : HasDerivAt (deriv f) (deriv (deriv f) (ρ u * u)) (ρ u * u))
    (hρd1 : HasDerivAt ρ (deriv ρ u) u)
    (hρd2 : HasDerivAt (deriv ρ) (deriv (deriv ρ) u) u)
    (hu2 : u ^ 2 ≤ 1 / 2) :
    |deriv ρ u| ≤ 3 ∧ |deriv (deriv ρ) u| ≤ 30 := by
  by_cases htriv : deriv ρ u = 0 ∧ deriv (deriv ρ) u = 0
  · rw [htriv.1, htriv.2]
    norm_num
  · have hne : deriv ρ u ≠ 0 ∨ deriv (deriv ρ) u ≠ 0 := by
      rcases eq_or_ne (deriv ρ u) 0 with h | h
      · exact Or.inr fun hq => htriv ⟨h, hq⟩
      · exact Or.inl h
    have huIoo : u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨(abs_lt.mp hu).1, (abs_lt.mp hu).2⟩
    -- the semicircle derivative facts
    have hsc1 : deriv Work.OddEnvelope.semicircle (ρ u * u)
        = -(ρ u * u) / Real.sqrt (1 - (ρ u * u) ^ 2) := by
      change deriv (fun t : ℝ => Real.sqrt (1 - t ^ 2)) (ρ u * u) = _
      exact radialAux_deriv_sqrt ht
    have hsc2 : deriv (deriv Work.OddEnvelope.semicircle) (ρ u * u)
        = -1 / (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3 := by
      change deriv (deriv (fun t : ℝ => Real.sqrt (1 - t ^ 2))) (ρ u * u) = _
      exact radialAux_deriv_deriv_sqrt ht
    have hS2 : (Real.sqrt (1 - u ^ 2)) ^ 2 = 1 - u ^ 2 := Real.sq_sqrt (by linarith)
    have hSp : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.2 (by linarith)
    have hsxp : 0 < Real.sqrt (1 - (ρ u * u) ^ 2) := by
      apply Real.sqrt_pos.2
      nlinarith [abs_lt.mp ht |>.1, abs_lt.mp ht |>.2]
    have hsx1 : Real.sqrt (1 - (ρ u * u) ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      nlinarith [sq_nonneg (ρ u * u)]
    have hb1b : |deriv f (ρ u * u) + (ρ u * u) / Real.sqrt (1 - (ρ u * u) ^ 2)| ≤ 1 / 1000 := by
      have h := h1
      rw [hsc1] at h
      convert h using 1
      ring
    have hb2b : |deriv (deriv f) (ρ u * u) + 1 / (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3|
        ≤ 1 / 1000 := by
      have h := h2
      rw [hsc2] at h
      convert h using 1
      ring
    have hb2ne : deriv (deriv f) (ρ u * u) ≠ 0 := by
      have hsx3p : 0 < (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3 := by positivity
      have hsx3le : (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3 ≤ 1 := by
        simpa using (pow_le_one₀ (n := 3) (le_of_lt hsxp) hsx1)
      have hge : 1 ≤ 1 / (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3 := one_le_one_div hsx3p hsx3le
      have hle : deriv (deriv f) (ρ u * u) ≤ -1 + 1 / 1000 := by
        have := (abs_le.mp hb2b).2
        linarith
      intro h0
      rw [h0] at hle
      norm_num at hle
    -- Peano expansions
    have hPf : Peano2 f (ρ u * u) (deriv f (ρ u * u)) (deriv (deriv f) (ρ u * u)) :=
      peano2_of_hasDerivAt_deriv hd1 hd2 (Or.inr hb2ne)
    have hPρ : Peano2 ρ u (deriv ρ u) (deriv (deriv ρ) u) :=
      peano2_of_hasDerivAt_deriv hρd1 hρd2 hne
    have hPid : Peano2 (fun v : ℝ => v) u 1 0 := by
      have h := peano2_id u
      unfold Peano2 at h ⊢
      simpa only [id_eq] using h
    have hX : Peano2 (fun v : ℝ => ρ v * v) u (deriv ρ u * u + ρ u)
        (deriv (deriv ρ) u * u + 2 * deriv ρ u) := by
      have h := peano2_mul hPρ hPid
      simpa only [mul_one, mul_zero, add_zero] using h
    have hPX : Peano2 (fun v : ℝ => f (ρ v * v)) u
        (deriv f (ρ u * u) * (deriv ρ u * u + ρ u))
        (deriv (deriv f) (ρ u * u) * (deriv ρ u * u + ρ u) ^ 2
          + deriv f (ρ u * u) * (deriv (deriv ρ) u * u + 2 * deriv ρ u)) :=
      peano2_comp hPf hX rfl
    have hPs : Peano2 (fun v : ℝ => Real.sqrt (1 - v ^ 2)) u
        (-u / Real.sqrt (1 - u ^ 2)) (-1 / (Real.sqrt (1 - u ^ 2)) ^ 3) :=
      peano2_of_hasDerivAt_deriv (radialAux_hasDerivAt_sqrt hu)
        (radialAux_hasDerivAt_deriv_sqrt hu) (Or.inr (by positivity))
    have hPY : Peano2 (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2)) u
        (deriv ρ u * Real.sqrt (1 - u ^ 2) + ρ u * (-u / Real.sqrt (1 - u ^ 2)))
        (deriv (deriv ρ) u * Real.sqrt (1 - u ^ 2)
          + 2 * deriv ρ u * (-u / Real.sqrt (1 - u ^ 2))
          + ρ u * (-1 / (Real.sqrt (1 - u ^ 2)) ^ 3)) :=
      peano2_mul hPρ hPs
    have heq : (fun v : ℝ => f (ρ v * v)) =ᶠ[𝓝 u]
        (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2)) := by
      filter_upwards [isOpen_Ioo.mem_nhds huIoo] with v hv
      exact (hgraph v hv).symm
    obtain ⟨hlin0, hquad0⟩ := peano2_unique (peano2_congr heq hPX) hPY
    -- first order relation
    have hlin : deriv ρ u * ((Real.sqrt (1 - u ^ 2)) ^ 2 - deriv f (ρ u * u) * u * Real.sqrt (1 - u ^ 2))
        = ρ u * (u + deriv f (ρ u * u) * Real.sqrt (1 - u ^ 2)) := by
      have hmul : deriv f (ρ u * u) * (deriv ρ u * u + ρ u) * Real.sqrt (1 - u ^ 2)
          = deriv ρ u * (Real.sqrt (1 - u ^ 2)) ^ 2 - ρ u * u := by
        have h := congrArg (fun t : ℝ => t * Real.sqrt (1 - u ^ 2)) hlin0
        rw [show (deriv ρ u * Real.sqrt (1 - u ^ 2) + ρ u * (-u / Real.sqrt (1 - u ^ 2)))
              * Real.sqrt (1 - u ^ 2)
            = deriv ρ u * (Real.sqrt (1 - u ^ 2)) ^ 2 - ρ u * u from by
          field_simp
          ring] at h
        linarith [h]
      ring_nf at hmul ⊢
      linarith [hmul]
    -- second order relation
    have hquad : deriv (deriv ρ) u * (Real.sqrt (1 - u ^ 2) - deriv f (ρ u * u) * u)
        = deriv (deriv f) (ρ u * u) * (deriv ρ u * u + ρ u) ^ 2
          + 2 * deriv f (ρ u * u) * deriv ρ u
          + 2 * deriv ρ u * u / Real.sqrt (1 - u ^ 2)
          + ρ u / (Real.sqrt (1 - u ^ 2)) ^ 3 := by
      have hq := hquad0
      rw [show 2 * deriv ρ u * (-u / Real.sqrt (1 - u ^ 2))
            = -(2 * deriv ρ u * u / Real.sqrt (1 - u ^ 2)) from by ring] at hq
      rw [show ρ u * (-1 / (Real.sqrt (1 - u ^ 2)) ^ 3)
            = -(ρ u / (Real.sqrt (1 - u ^ 2)) ^ 3) from by ring] at hq
      ring_nf at hq ⊢
      linarith [hq]
    exact radial_core hu0 hu2 hρpos hρclose hS2 hSp rfl hb1b hb2b hlin hquad


end

end Work.OddCurve.LowSlope
