import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mstG_spec

namespace Work.BourgainPlan.Maximal

open scoped BigOperators

/-- The exponential `e(x) = exp(2πi x)` at a real argument is conjugate-symmetric:
`star (e x) = e (-x)`. -/
lemma star_exp_two_pi_I (x : ℝ) :
    star (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I * ((-x : ℝ) : ℂ)) := by
  have hx : (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hy : (2 * Real.pi * Complex.I * ((-x : ℝ) : ℂ)) = ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hx, hy, Complex.star_def, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- `star ((Q : ℂ)⁻¹ * z) = (Q : ℂ)⁻¹ * star z`: the factor `Q⁻¹` for a natural `Q` is real. -/
lemma star_natCast_inv_mul (Q : ℕ) (z : ℂ) : star ((Q : ℂ)⁻¹ * z) = (Q : ℂ)⁻¹ * star z := by
  rw [star_mul, star_inv₀, star_natCast, mul_comm]

/-- **The complete sum is conjugate-antisymmetric in its numerator**: `polyWeight P Q (-b)` is the
conjugate of `polyWeight P Q b` (the exponential `e(bP(r)/Q)` is replaced by `e(-bP(r)/Q)`). -/
lemma polyWeight_neg (P : Polynomial ℤ) (Q : ℕ) (b : ℤ) :
    polyWeight P Q (-b) = star (polyWeight P Q b) := by
  unfold polyWeight
  rw [star_natCast_inv_mul, star_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [star_exp_two_pi_I]
  congr 1
  push_cast
  ring

/-- `mstG P β = 0` whenever `β` has no canonical representative `arcPt q a` (`0 < q`, `0 ≤ a < q`). -/
lemma mstG_eq_zero_of_not (P : Polynomial ℤ) {β : Work.BourgainPlan.IonescuWainger.Circle}
    (h : ¬ ∃ (q : ℕ) (a : ℤ), 0 < q ∧ 0 ≤ a ∧ a < q ∧
        Work.BourgainPlan.IonescuWainger.arcPt q a = β) :
    mstG P β = 0 := by
  classical
  unfold mstG
  rw [dif_neg h]

/-- **Negation preserves canonical representability.**  If `β` has a canonical representative
`arcPt q a` (`0 < q`, `0 ≤ a < q`) then so does `-β`: for `a = 0` one has `-β = β = arcPt q 0`,
and for `a > 0` the point `q - a` is again canonical and `arcPt q (q - a) = -β`. -/
lemma hasCanon_neg {β : Work.BourgainPlan.IonescuWainger.Circle}
    (h : ∃ (q : ℕ) (a : ℤ), 0 < q ∧ 0 ≤ a ∧ a < q ∧
        Work.BourgainPlan.IonescuWainger.arcPt q a = β) :
    ∃ (q : ℕ) (a : ℤ), 0 < q ∧ 0 ≤ a ∧ a < q ∧
        Work.BourgainPlan.IonescuWainger.arcPt q a = -β := by
  obtain ⟨q, a, hq, ha, haq, hβ⟩ := h
  rcases eq_or_lt_of_le ha with h0 | hpos
  · refine ⟨q, 0, hq, le_refl 0, by exact_mod_cast hq, ?_⟩
    have hβ0 : β = 0 := by rw [← hβ, ← h0, Work.BourgainPlan.IonescuWainger.arcPt_zero]
    rw [Work.BourgainPlan.IonescuWainger.arcPt_zero, hβ0, neg_zero]
  · refine ⟨q, q - a, hq, by omega, by omega, ?_⟩
    have hqq : Work.BourgainPlan.IonescuWainger.arcPt q (q : ℤ) = 0 :=
      (Work.BourgainPlan.IonescuWainger.arcPt_eq_zero_iff_dvd (by omega) (q : ℤ)).mpr
        (dvd_refl (q : ℤ))
    rw [show q - a = (q : ℤ) + (-a) by ring,
      ← Work.BourgainPlan.IonescuWainger.arcPt_add, hqq, zero_add,
      Work.BourgainPlan.IonescuWainger.arcPt_neg, hβ]

/-- **The complete-sum weight at the negated circle point.** The Gauss sum weight `mstG P` of
`mst_major_defs.lean` is conjugate-symmetric under `β ↦ -β`: for every circle point `β`,

  `mstG P (-β) = star (mstG P β)`.

On a canonical representative `β = arcPt q a` (`0 < q`, `0 ≤ a < q`) this is
`polyWeight P q (q - a) = star (polyWeight P q a)`, which is the statement that the complete sum
`q⁻¹ Σ_{r<q} e((q-a)P(r)/q)` is the conjugate of `q⁻¹ Σ_{r<q} e(aP(r)/q)` (the two sums differ by
the integer `P(r)` in the exponential). The case `a = 0` has `-β = β` and both sides equal `1`.
`mstG_spec` (`mstG_spec.lean`) computes `mstG` on a canonical representative and
`polyWeight_eq_of_arcPt_eq` there gives well-definedness; `arcPt_neg` (`ArcSep.lean`) gives
`-arcPt q a = arcPt q (-a) = arcPt q (q-a)`. -/
theorem mstG_neg (P : Polynomial ℤ) (β : Work.BourgainPlan.IonescuWainger.Circle) :
    Work.BourgainPlan.Maximal.mstG P (-β) = star (Work.BourgainPlan.Maximal.mstG P β) := by
  classical
  by_cases h : ∃ (q : ℕ) (a : ℤ), 0 < q ∧ 0 ≤ a ∧ a < q ∧
      Work.BourgainPlan.IonescuWainger.arcPt q a = β
  · obtain ⟨q, a, hq, ha, haq, hβ⟩ := h
    rcases eq_or_lt_of_le ha with h0 | hpos
    · -- `a = 0`: `β = 0` is fixed by negation and its weight is real (`= 1`).
      have ha0 : a = 0 := h0.symm
      have hβ0 : β = 0 := by rw [← hβ, ha0, Work.BourgainPlan.IonescuWainger.arcPt_zero]
      have hGβ : mstG P β = polyWeight P q 0 := by
        rw [← ha0]; exact mstG_spec P hq ha haq hβ
      have hstar0 : star (polyWeight P q 0) = polyWeight P q 0 := by
        simpa using (polyWeight_neg P q 0).symm
      calc mstG P (-β) = mstG P β := by rw [hβ0, neg_zero]
        _ = polyWeight P q 0 := hGβ
        _ = star (polyWeight P q 0) := hstar0.symm
        _ = star (mstG P β) := by rw [hGβ]
    · -- `0 < a`: `q - a` is a canonical representative of `-β`.
      have hb0 : 0 ≤ q - a := by omega
      have hbq : q - a < (q : ℤ) := by omega
      have hqq : Work.BourgainPlan.IonescuWainger.arcPt q (q : ℤ) = 0 :=
        (Work.BourgainPlan.IonescuWainger.arcPt_eq_zero_iff_dvd (by omega) (q : ℤ)).mpr
          (dvd_refl (q : ℤ))
      have hβneg : Work.BourgainPlan.IonescuWainger.arcPt q (q - a) = -β := by
        rw [show q - a = (q : ℤ) + (-a) by ring,
          ← Work.BourgainPlan.IonescuWainger.arcPt_add, hqq, zero_add,
          Work.BourgainPlan.IonescuWainger.arcPt_neg, hβ]
      have hGneg : mstG P (-β) = polyWeight P q (q - a) :=
        mstG_spec P hq hb0 hbq hβneg
      have hkey : polyWeight P q (q - a) = star (polyWeight P q a) := by
        rw [show q - a = -a + 1 * (q : ℤ) by ring,
          polyWeight_add_modulus_mul, polyWeight_neg]
      calc mstG P (-β) = polyWeight P q (q - a) := hGneg
        _ = star (polyWeight P q a) := hkey
        _ = star (mstG P β) := by rw [mstG_spec P hq ha haq hβ]
  · -- `β` has no canonical representative, and neither does `-β`.
    have hnegcanon : ¬ (∃ (q : ℕ) (a : ℤ), 0 < q ∧ 0 ≤ a ∧ a < q ∧
        Work.BourgainPlan.IonescuWainger.arcPt q a = -β) := by
      rintro hh
      exact h (by simpa only [neg_neg] using hasCanon_neg hh)
    rw [mstG_eq_zero_of_not P hnegcanon, mstG_eq_zero_of_not P h, star_zero]

end Work.BourgainPlan.Maximal
