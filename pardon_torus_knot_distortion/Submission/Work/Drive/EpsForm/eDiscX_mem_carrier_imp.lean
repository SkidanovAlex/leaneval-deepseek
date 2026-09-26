import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDesign2
import Submission.Work.Drive.EpsForm.WaypointDiscDefs
import Submission.Work.Drive.EpsForm.profX_levels

namespace Work.Drive.EpsForm

/-- **The interior intersection of the corrected disc with the torus is the union of the
two chords.**  If `z` is in the *open* unit disc and `eDiscX z` lies on the standard torus,
then `arg z` is in the chord range and the radial parameter `‖z‖` is one of the two chord
levels `sig1 (arg z)`, `sig2 (arg z)`.

Route: writing `(u,v) = profX (arg z) ‖z‖`, the point `eDiscX z` has coordinates
`((2+u) cos (arg z), (2+u) sin (arg z), v)`.  If it equals `torusMap Θ Φ`, then comparing
squared radii gives `(2+u)² = (2+cos Φ)²`; since `2 + cos Φ > 0` and `u > -2` (because
`‖z‖ > 0`: `z = 0` would give the origin, which is not on the torus), this forces
`2 + u = 2 + cos Φ`, `u = cos Φ`, `v = sin Φ` and `arg z ≡ Θ (mod 2π)`.  Hence
`u² + v² = 1` and `profX_levels` (`Work.Drive.EpsForm.profX_levels`, imported) applies. -/
theorem eDiscX_mem_carrier_imp (z : Metric.closedBall (0 : ℂ) 1) (hz : ‖(z : ℂ)‖ < 1)
    (h : eDiscX z ∈ Work.CoreTopology.standard.carrier) :
    Complex.arg (z : ℂ) ∈ Set.Icc u0 v0 ∧
      (‖(z : ℂ)‖ = sig1 (Complex.arg (z : ℂ)) ∨
        ‖(z : ℂ)‖ = sig2 (Complex.arg (z : ℂ))) := by
  set t := Complex.arg (z : ℂ) with ht
  set s := ‖(z : ℂ)‖ with hs
  have hsle : s ≤ 1 := by
    have h1 : ‖(z : ℂ)‖ ≤ 1 := by
      have := z.2
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    rwa [hs]
  have hslt : s < 1 := by rwa [hs]
  have hsnn : 0 ≤ s := by rw [hs]; exact norm_nonneg _
  have htmem : t ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [ht]; exact Complex.arg_mem_Ioc _
  obtain ⟨Θ, Φ, hΘΦ⟩ :=
    (Work.CoreTopology.ParamTorus.mem_carrier_iff Work.CoreTopology.standard (eDiscX z)).mp h
  have hΘΦ' : Work.Core.torusMap Θ Φ = eDiscX z := by simpa using hΘΦ
  have hEq : Work.Core.torusMap Θ Φ = eFunX t s := by
    rw [hΘΦ']
    unfold eDiscX
    rw [← ht, ← hs]
  have h0 : (2 + Real.cos Φ) * Real.cos Θ = (2 + (profX t s).1) * Real.cos t := by
    have hh := congrArg (fun X => X (0 : Fin 3)) hEq
    simpa only [Work.Core.torusMap_apply_zero, eFunX_apply_zero] using hh
  have h1 : (2 + Real.cos Φ) * Real.sin Θ = (2 + (profX t s).1) * Real.sin t := by
    have hh := congrArg (fun X => X (1 : Fin 3)) hEq
    simpa only [Work.Core.torusMap_apply_one, eFunX_apply_one] using hh
  have h2 : Real.sin Φ = (profX t s).2 := by
    have hh := congrArg (fun X => X (2 : Fin 3)) hEq
    simpa only [Work.Core.torusMap_apply_two, eFunX_apply_two] using hh
  have hsq : (2 + (profX t s).1) ^ 2 = (2 + Real.cos Φ) ^ 2 := by
    have e0 := congrArg (fun x : ℝ => x ^ 2) h0
    have e1 := congrArg (fun x : ℝ => x ^ 2) h1
    nlinarith [e0, e1, Real.cos_sq_add_sin_sq t, Real.cos_sq_add_sin_sq Θ]
  have hspos : 0 < s := by
    rcases eq_or_lt_of_le hsnn with h0s | hlt
    · exfalso
      have hu : (profX t s).1 = -2 := by
        rw [← h0s, profX_zero]
        simp [W1]
      have hzero : (2 + Real.cos Φ) ^ 2 = 0 := by
        rw [← hsq, hu]; ring
      have hze : 2 + Real.cos Φ = 0 := sq_eq_zero_iff.mp hzero
      linarith [Real.neg_one_le_cos Φ]
    · exact hlt
  have hfst : -2 < (profX t s).1 := profX_fst_gt t s hspos hsle
  have hAB : 2 + (profX t s).1 = 2 + Real.cos Φ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hh | hh
    · exact hh
    · exfalso
      linarith [Real.neg_one_le_cos Φ]
  have hu : (profX t s).1 = Real.cos Φ := by linarith
  have hnorm : (profX t s).1 ^ 2 + (profX t s).2 ^ 2 = 1 := by
    rw [hu, ← h2]
    exact Real.cos_sq_add_sin_sq Φ
  have hlev := (profX_levels (t := t) (s := s) htmem.1 htmem.2).2 hspos hslt
  obtain ⟨hin, hsig⟩ := hlev.mp hnorm
  exact ⟨hin, hsig⟩

end Work.Drive.EpsForm
