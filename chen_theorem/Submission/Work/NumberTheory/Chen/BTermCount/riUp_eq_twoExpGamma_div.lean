/-
# `BTermCount.riUp_eq_twoExpGamma_div` — the closed form `F(s) = 2e^γ/s` on `[1,3]`

The Rosser–Iwaniec upper profile `riUp = F = 1 + riPhi` of the delay family `profC`
(`APSwitchUpper.prof`) is evaluated in closed form on the initial sifting range:

    `riUp s = 2·e^γ / s`   for `1 ≤ s ≤ 3`.

## Route

* The summed delay identity `ApSumTenth.riPhi_delay_system` gives, together with
  `ApSumTenth.riSys_integral_Ici_two_riPsi` (`∫_{Ici 2} riPsi = Ctot`),

      `s·riPhi s = (3 - s) + Ctot`   for `1 ≤ s ≤ 3`,

  hence `riUp s = (3 + Ctot)/s` on that range (`riUp_eq_add_Ctot_div`).

* The mass constant is exactly `3 + Ctot = 2·e^γ`: this is the classical Buchstab/Bernstein
  delay-limit lemma `ApSumTenth.buchstab_laplace_limit` applied to the test function
  `buchstabA s = 3 + Ctot` (`s ≤ 2`), `buchstabA s = s·(2 + riPhi s − riPsi s)` (`s ≥ 2`) of
  `ApSumTenth.TailAux`.  It satisfies the delay recurrence
  `buchstabA s = (3+Ctot) + ∫_1^{s-1} buchstabA v/v dv` for `s ≥ 2`, grows at most linearly,
  and `buchstabA s / s → 2`; the Buchstab lemma therefore returns
  `2 = (3 + Ctot)·e^{−γ}`, i.e. `3 + Ctot = 2e^γ`.

  (The same application, with the weaker conclusion `Ctot ≤ 2e^γ − 3`, is
  `ApSumTenth.mass_constant_of_buchstab`; here the *equality* `3 + Ctot = 2e^γ` is what the
  identity `riUp s = 2e^γ/s` needs, and it is recorded as `ct_add_Ctot_eq_twoExpGamma`.)
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.ApSumTenth.mass_constant_of_buchstab
import Submission.Work.NumberTheory.Chen.ApSumTenth.buchstab_laplace_limit
import Submission.Work.NumberTheory.Chen.ApSumTenth.eulerMascheroni_eq_integral
import Submission.Work.NumberTheory.Chen.ApSumTenth.eulerMascheroni_limit_form
import Submission.Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_system
import Submission.Work.NumberTheory.Chen.ApSumTenth.TailAux

namespace Work.NumberTheory.Chen.BTermCount

open Work.NumberTheory.Chen.APSwitchUpper
open Work.NumberTheory.Chen.ApSumTenth

/-- **The mass constant is exact:** `3 + Ctot = 2·e^γ`, where `Ctot = ∫_{Ici 2} riPsi` is the
total mass of the lower Rosser–Iwaniec profile.  This is the Buchstab/Bernstein delay-limit
lemma applied to `buchstabA`: the latter satisfies the Buchstab recurrence with initial value
`3 + Ctot` and has `buchstabA s / s → 2`, so `2 = (3 + Ctot)·e^{−γ}`. -/
theorem ct_add_Ctot_eq_twoExpGamma :
    3 + Ctot = 2 * Real.exp Real.eulerMascheroniConstant := by
  have hkey := buchstab_laplace_limit (eulerMascheroni_limit_form eulerMascheroni_eq_integral)
    buchstabA (3 + Ctot) 2 20
    (fun a b => intervalIntegrable_buchstabA a b)
    (fun s hs => buchstabA_of_le_two hs.2)
    (fun s hs => buchstabA_rec s hs)
    (fun s hs => buchstabA_bound s hs)
    tendsto_buchstabA_div
  have he : Real.exp (-Real.eulerMascheroniConstant) * Real.exp Real.eulerMascheroniConstant = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 : 2 * Real.exp Real.eulerMascheroniConstant = 3 + Ctot := by
    have h := congrArg (fun x : ℝ => x * Real.exp Real.eulerMascheroniConstant) hkey
    rw [mul_assoc (3 + Ctot), ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h
    exact h
  linarith [h2]

/-- **The summed delay identity on the initial range.**  For `1 ≤ s ≤ 3`,
`s·riPhi s = (3 - s) + Ctot`, hence `riUp s = (3 + Ctot)/s`. -/
theorem riUp_eq_add_Ctot_div {s : ℝ} (h1 : 1 ≤ s) (h3 : s ≤ 3) :
    riUp s = (3 + Ctot) / s := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hsys := riPhi_delay_system.1 s h1 h3
  rw [riSys_integral_Ici_two_riPsi] at hsys
  have hphi : riPhi s = ((3 - s) + Ctot) / s := by
    rw [eq_div_iff (ne_of_gt hs0)]
    linarith
  rw [riUp, hphi]
  field_simp
  ring

theorem riUp_eq_twoExpGamma_div (s : ℝ) (h1 : 1 ≤ s) (h3 : s ≤ 3) :
    Work.NumberTheory.Chen.APSwitchUpper.riUp s
      = 2 * Real.exp Real.eulerMascheroniConstant / s := by
  rw [riUp_eq_add_Ctot_div h1 h3, ct_add_Ctot_eq_twoExpGamma]

end Work.NumberTheory.Chen.BTermCount
