import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.poly_weight_cap_block

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

/-- **Well-definedness of the complete-sum weight on a circle point.**  If `arcPt q a = arcPt q' a'`
with both representatives in canonical form (`0 < q`, `0 ≤ a < q`, `0 < q'`, `0 ≤ a' < q'`), then
the complete sums agree: `polyWeight P q a = polyWeight P q' a'`.

Both `a/q` and `a'/q'` lie in `[0,1)`, so equality in `𝕋 = ℝ/ℤ` gives equality in `ℝ`
(`AddCircle.coe_eq_coe_iff_of_mem_Ico`), hence `a * q' = a' * q`; the two sums are then both reduced
to the common modulus `q * q'` by the period reduction `polyWeight_eq_of_dvd`. -/
lemma polyWeight_eq_of_arcPt_eq (P : Polynomial ℤ) {q q' : ℕ} {a a' : ℤ}
    (hq : 0 < q) (ha : 0 ≤ a) (haq : a < q)
    (hq' : 0 < q') (ha' : 0 ≤ a') (ha'q : a' < q')
    (h : arcPt q a = arcPt q' a') :
    polyWeight P q a = polyWeight P q' a' := by
  -- A canonical representative `b/n` (`0 < n`, `0 ≤ b < n`) lies in `[0,1)`.
  have hmem : ∀ (n : ℕ) (b : ℤ), 0 < n → 0 ≤ b → b < n →
      (b : ℝ) / (n : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    intro n b hn hb hbn
    refine ⟨by positivity, ?_⟩
    rw [zero_add, div_lt_one (by exact_mod_cast hn : (0 : ℝ) < n)]
    exact_mod_cast hbn
  -- Equality in the circle, both entries in `[0,1)`, is equality in `ℝ`.
  have hreal : (a : ℝ) / (q : ℝ) = (a' : ℝ) / (q' : ℝ) :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem q a hq ha haq) (hmem q' a' hq' ha' ha'q)).mp h
  have hcross : a * (q' : ℤ) = a' * (q : ℤ) := by
    rw [div_eq_div_iff (by positivity) (by positivity)] at hreal
    exact_mod_cast hreal
  -- Reduce both sums to the common modulus `q * q'`.
  have hqpos' : 0 < q * q' := Nat.mul_pos hq hq'
  have h1 : polyWeight P (q * q') (a * (q' : ℤ)) = polyWeight P q a :=
    polyWeight_eq_of_dvd (P := P) (Q := q * q') (Q' := q) hqpos' hq (Nat.dvd_mul_right q q')
      (by push_cast; ring)
  have h2 : polyWeight P (q * q') (a' * (q : ℤ)) = polyWeight P q' a' :=
    polyWeight_eq_of_dvd (P := P) (Q := q * q') (Q' := q') hqpos' hq'
      ⟨q, by ring⟩ (by push_cast; ring)
  calc polyWeight P q a = polyWeight P (q * q') (a * (q' : ℤ)) := h1.symm
    _ = polyWeight P (q * q') (a' * (q : ℤ)) := by rw [hcross]
    _ = polyWeight P q' a' := h2

/-- The canonical complete-sum weight `mstG` on a given representative: for `0 < q` and `0 ≤ a < q`
the value `mstG P β` at `β = arcPt q a` is `polyWeight P q a`.

The proof establishes well-definedness: from `arcPt q a = arcPt q' a'` with `0 < q, 0 ≤ a < q,
0 < q', 0 ≤ a' < q'` the rationals `a/q` and `a'/q'` both lie in `[0,1)` and differ by an integer,
hence coincide, and then `polyWeight P q a = polyWeight P q' a'`.  The key ingredient is the
scale invariance `polyWeight P (m * q) (m * a) = polyWeight P q a`, which holds because
`r ↦ exp (2 * π * I * (a * P r) / q)` is `q`-periodic in `r`. -/
theorem mstG_spec (P : Polynomial ℤ) {β : Work.BourgainPlan.IonescuWainger.Circle} {q : ℕ} {a : ℤ}
    (hq : 0 < q) (ha : 0 ≤ a) (haq : a < q)
    (hβ : Work.BourgainPlan.IonescuWainger.arcPt q a = β) :
    Work.BourgainPlan.Maximal.mstG P β = Work.BourgainPlan.Maximal.polyWeight P q a := by
  classical
  -- The defining existential of `mstG` is satisfied by `(q, a)`.
  have hex : ∃ (q : ℕ) (a : ℤ), 0 < q ∧ 0 ≤ a ∧ a < q ∧ arcPt q a = β :=
    ⟨q, a, hq, ha, haq, hβ⟩
  unfold mstG
  rw [dif_pos hex]
  -- Name the chosen representative and expose its properties.
  set q₁ : ℕ := Classical.choose hex with hq₁def
  set a₁ : ℤ := Classical.choose (Classical.choose_spec hex) with ha₁def
  have hsp : 0 < q₁ ∧ 0 ≤ a₁ ∧ a₁ < (q₁ : ℤ) ∧ arcPt q₁ a₁ = β := by
    simpa only [← hq₁def, ← ha₁def] using Classical.choose_spec (Classical.choose_spec hex)
  exact polyWeight_eq_of_arcPt_eq P hsp.1 hsp.2.1 hsp.2.2.1 hq ha haq
    (hsp.2.2.2.trans hβ.symm)

end Work.BourgainPlan.Maximal
