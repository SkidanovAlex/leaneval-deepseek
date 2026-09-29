import Mathlib
import Submission.Work.A14.defs
import Submission.Work.C7.g_form
import Submission.Work.C7.trans
import Submission.Work.C7.J_ode
import Submission.Work.C17.Js_bound
import Submission.Work.C17.B5_pullback
import Submission.Work.C17I.hasSum_tsum_of_poly_growth
import Submission.Work.CPull.evp_aux
import Submission.Work.CPull.evp_sympPhi

namespace Work.A14D

open Complex Metric
open scoped BigOperators

/-! ## Helpers

The pullback statement `B₅∘y = (x/(x−1))·J` (`y = x²/(x−1)`) is the formal identity
`Work.C7.g4_form_c7`; the analytic content is that `evp` is multiplicative on the open unit
disc (`Work.CPull.evpMul`) together with the summability of the two coefficient series, which
follows from the polynomial growth of the coefficients of `Jps` (`Work.C17.Js_bound`, fed by
the ODE `Work.C7.J_ode`). -/

/-- `‖(q : ℂ)‖ = |(q : ℝ)|` for a rational `q`. -/
private lemma norm_ratCast (q : ℚ) : ‖(q : ℂ)‖ = |(q : ℝ)| := by simp

/-- `B₅∘ y = φ·J` as a formal power series, where `φ = x/(x−1)` and `y = x²/(x−1)`. -/
private lemma B5_subst_sympY :
    Submission.CDTPlan.B5.subst Submission.CDT.sympY
      = Submission.CDT.sympPhi * Work.C7.Jps := by
  have h := Work.C7.g4_form_c7
  rw [show Work.C7.g 4 = Submission.CDTPlan.B5.subst Submission.CDT.sympY by
        simp [Work.C7.g, Submission.CDTPlan.pureB, Fin.isValue]] at h
  simpa [Submission.CDT.sympPhi] using h

/-- The ODE satisfied by `Jps`, obtained by pulling back the differential relation of `B₅`. -/
private lemma Jps_ode :
    2 * PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Work.C7.Jps
      - PowerSeries.X * Work.C7.Jps = 2 * (1 - PowerSeries.X) * Work.C7.Lps :=
  Work.C7.J_ode Work.C7.g_form.1 Work.C7.g4_form_c7 Work.C17.B5_pullback

/-- The pullback of `B₅` along the symmetrisation coordinate `y = x²/(x−1)`, evaluated on the
open unit disc. -/
theorem pullback_B5_hasSum_aux (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (Submission.CDTPlan.B5.subst Submission.CDT.sympY) : ℚ) : ℂ) * z ^ n)
      ((z / (z - 1)) * (∑' n : ℕ, ((PowerSeries.coeff n Work.C7.Jps : ℚ) : ℂ) * z ^ n)) := by
  have hF := B5_subst_sympY
  -- Polynomial growth of the coefficients of `Jps`, hence summability on the unit disc.
  obtain ⟨C, k, hCk⟩ := Work.C17.Js_bound Jps_ode
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (by simpa using hCk 0)
  have hJbound : ∀ n : ℕ,
      ‖((PowerSeries.coeff n Work.C7.Jps : ℚ) : ℂ)‖ ≤ C * ((n : ℝ) + 1) ^ k := by
    intro n
    rw [norm_ratCast]
    exact hCk n
  have hJhas := Work.C17I.hasSum_tsum_of_poly_growth
    (c := fun n => ((PowerSeries.coeff n Work.C7.Jps : ℚ) : ℂ)) hC0 hJbound z hz
  have hsJ : Summable (fun n : ℕ => ((PowerSeries.coeff n Work.C7.Jps : ℚ) : ℂ) * z ^ n) :=
    hJhas.summable
  -- The coefficients of `φ = x/(x−1)` are `0` at `0` and `−1` afterwards: again summable.
  have hPhi_bound : ∀ n : ℕ,
      ‖((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ)‖
        ≤ (1 : ℝ) * ((n : ℝ) + 1) ^ 0 := by
    intro n
    rw [norm_ratCast, Work.CPull.coeff_sympPhi_eq n]
    split_ifs <;> norm_num
  have hPhihas := Work.C17I.hasSum_tsum_of_poly_growth
    (c := fun n => ((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ))
    (C := 1) (k := 0) (by norm_num) hPhi_bound z hz
  have hsPhi :
      Summable (fun n : ℕ => ((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ) * z ^ n) :=
    hPhihas.summable
  -- Cauchy product: `evp` is multiplicative, hence `evp (B₅∘y) z = (z/(z−1)) * evp J z`.
  obtain ⟨_, _, hsF, hevp⟩ :=
    Work.CPull.evpMul Submission.CDT.sympPhi Work.C7.Jps z hsPhi.norm hsJ.norm
  rw [← hF] at hsF hevp
  rw [(Work.CPull.evp_sympPhi z hz).1] at hevp
  have hevp' :
      (∑' n : ℕ,
          ((PowerSeries.coeff n (Submission.CDTPlan.B5.subst Submission.CDT.sympY) : ℚ) : ℂ)
            * z ^ n)
        = (z / (z - 1)) * (∑' n : ℕ, ((PowerSeries.coeff n Work.C7.Jps : ℚ) : ℂ) * z ^ n) :=
    hevp
  have hsum := hsF.hasSum
  rw [hevp'] at hsum
  exact hsum

theorem pullback_B5_hasSum (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (Submission.CDTPlan.B5.subst Submission.CDT.sympY) : ℚ) : ℂ) * z ^ n)
      ((z / (z - 1)) * (∑' n : ℕ, ((PowerSeries.coeff n Work.C7.Jps : ℚ) : ℂ) * z ^ n)) :=
  pullback_B5_hasSum_aux z hz

namespace Work.A14D

/-- The same statement under the doubled-namespace name `Work.A14D.Work.A14D.pullback_B5_hasSum`
(the name under which the seeded file originally declared it). -/
theorem pullback_B5_hasSum (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (Submission.CDTPlan.B5.subst Submission.CDT.sympY) : ℚ) : ℂ) * z ^ n)
      ((z / (z - 1)) * (∑' n : ℕ, ((PowerSeries.coeff n Work.C7.Jps : ℚ) : ℂ) * z ^ n)) :=
  pullback_B5_hasSum_aux z hz

end Work.A14D

end Work.A14D
