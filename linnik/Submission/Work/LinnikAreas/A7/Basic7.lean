/-
# Area 7 — small structural lemmas for the assembly

* `Phi_eq_Cf_add` : for `0 < z ≤ Λ`, `Φ(z) = C(Λ,z) + (Φ(Λ)/w(Λ))·w(z)` — the splitting of the
  per-character constant into the "credits" term `C` and the density-weight term.
* `Aref_expand` : the rewritten form of `Φ(p) - Aref c p` used when the second zero is outside the box.
* `InBox_star` : `InBox` is invariant under complex conjugation.
-/
import Mathlib
import Submission.Work.LinnikAreas.A7.Defs
import Submission.Work.A7.Wf_Cf_mono
import Submission.Work.A7.chi1_inv_api

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.A7

open Work.LinnikContract

/-- Splitting of `Φ` against the reference point `Λ`: for `0 < z ≤ Λ` the maximum in `C` is
attained, so `Φ(z) = C(Λ,z) + (Φ(Λ)/w(Λ))·w(z)`. -/
theorem Phi_eq_Cf_add {Λ z : ℝ} (hΛ : 0 < Λ) (hz : 0 < z) (hzΛ : z ≤ Λ) :
    Phi z = Cf Λ z + (Phi Λ / Wf Λ) * Wf z := by
  have hR : Phi Λ / Wf Λ ≤ Phi z / Wf z := Work.A7.PhiWf_antitone hz hzΛ
  have hWz : Wf z ≠ 0 := ne_of_gt (Work.A7.Wf_pos hz)
  have hWΛ : Wf Λ ≠ 0 := ne_of_gt (Work.A7.Wf_pos hΛ)
  have hA : 0 ≤ Wf z * (Phi z / Wf z - Phi Λ / Wf Λ) :=
    mul_nonneg (Work.A7.Wf_pos hz).le (by linarith)
  rw [Work.A7.Cf_eq_max hΛ hz, max_eq_right hA]
  field_simp
  ring

/-- The rewritten form of the refined χ-term when the second zero lies outside the box:
`Φ(p) - Aref c p = e^{-ac}B(p) + (e^{-ap} - e^{-ac})·(K⁻²F₂(p))`. -/
theorem Aref_expand {c p : ℝ} (hp : p ≠ 0) :
    Phi p - Aref c p = Real.exp (-(ac * c)) * Bfun Kc p
      + (Real.exp (-(ac * p)) - Real.exp (-(ac * c))) * (((1 - Real.exp (-(Kc * p))) / p) ^ 2 / K2) := by
  rw [Aref, Phi]
  ring

/-- `InBox` is invariant under complex conjugation. -/
theorem InBox_star {q : ℕ} {R : ℝ} {ρ : ℂ} :
    InBox q R ((starRingEnd ℂ) ρ) ↔ InBox q R ρ := by
  simp [InBox, Work.A7.lamOf_star, Work.A7.abs_im_star]

/-- Membership characterisation of `Aset`. -/
theorem mem_Aset {q : ℕ} [NeZero q] {R : ℝ} {χ : DirichletCharacter ℂ q} :
    χ ∈ Aset q R ↔ χ ≠ 1 ∧ ∃ ρ : ℂ, InBox q R ρ ∧ zeroMult χ ρ ≠ 0 := by
  simp [Aset, Finset.mem_filter, Finset.mem_erase]

/-- A non-principal character with a nonvanishing box sum lies in `Aset`. -/
theorem mem_Aset_of_boxSum_ne_zero {q : ℕ} [NeZero q] {R : ℝ} {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (h : boxSum q (11/2) (3/10) R χ ≠ 0) : χ ∈ Aset q R := by
  rw [mem_Aset]
  refine ⟨hχ, ?_⟩
  by_contra hcon
  push Not at hcon
  exact h (by
    rw [boxSum]
    refine finsum_eq_zero_of_forall_eq_zero (fun ρ => ?_)
    by_cases hb : InBox q R ρ
    · rw [if_pos hb, hcon ρ hb]
      simp
    · rw [if_neg hb])

end Work.LinnikAreas.A7
