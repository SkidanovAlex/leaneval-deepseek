import Mathlib
import Submission.Work.KMTAreas.A7.FiberGeneral
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- The `q`-torsion frequency set: the arithmetic frequencies `a/q`, `0 ≤ a < q`. -/
noncomputable def torsionSet (q : ℕ) : Finset Circ :=
  (Finset.range q).image (fun a : ℕ => (((a : ℝ) / (q : ℝ)) : Circ))

lemma torsionSet_def (q : ℕ) :
    torsionSet q = (Finset.range q).image (fun a : ℕ => (((a : ℝ) / (q : ℝ)) : Circ)) := rfl

/-- Membership in the `q`-torsion set: `q • α = 0`. -/
theorem mem_torsionSet {q : ℕ} (hq : 0 < q) {α : Circ} :
    α ∈ torsionSet q ↔ q • α = 0 := by
  rw [torsionSet, Finset.mem_image]
  constructor
  · rintro ⟨a, -, ha⟩
    rw [← ha]
    exact Work.Analysis.IonescuWainger.nsmul_div_eq_zero hq
  · intro hα
    exact Work.Analysis.IonescuWainger.eq_div_of_nsmul_eq_zero hq hα

/-- The intersection of two torsion sets is the torsion set of the gcd. -/
theorem torsionSet_inter (q₁ q₂ : ℕ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) :
    torsionSet q₁ ∩ torsionSet q₂ = torsionSet (Nat.gcd q₁ q₂) := by
  have hg : 0 < Nat.gcd q₁ q₂ := Nat.gcd_pos_of_pos_left q₂ h₁
  ext α
  rw [Finset.mem_inter, mem_torsionSet h₁, mem_torsionSet h₂, mem_torsionSet hg,
    ← addOrderOf_dvd_iff_nsmul_eq_zero, ← addOrderOf_dvd_iff_nsmul_eq_zero,
    ← addOrderOf_dvd_iff_nsmul_eq_zero, Nat.dvd_gcd_iff]

/-! ## Two elementary bridges -/

/-- A circle point of norm `≤ δ` lies in the `δ`-arc around `0` (the norm is attained). -/
lemma mem_arcSet_of_norm_le {δ : ℝ} {ξ : Circ} (h : ‖ξ‖ ≤ δ) :
    ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ := by
  set x : ℝ := ((AddCircle.equivIco (1:ℝ) 0 ξ : Set.Ico (0:ℝ) (0+1)) : ℝ) with hx
  have hxcoe : (x : Circ) = ξ := AddCircle.coe_equivIco
  have hx0 : 0 ≤ x := (AddCircle.equivIco (1:ℝ) 0 ξ).2.1
  have hx1 : x < 1 := by simpa using (AddCircle.equivIco (1:ℝ) 0 ξ).2.2
  by_cases hxc : x ≤ 1/2
  · have habs : |x| ≤ 1/2 := by rw [abs_of_nonneg hx0]; exact hxc
    have hnorm : (‖(x : Circ)‖) = |x| := by
      refine (AddCircle.norm_coe_eq_abs_iff 1 (x := x) one_ne_zero).mpr ?_
      rw [abs_one]; exact habs
    have hxnorm : |x| = ‖ξ‖ := hnorm.symm.trans (congrArg Norm.norm hxcoe)
    exact ⟨x, by rw [hxnorm]; exact h, by rw [zero_add]; exact hxcoe.symm⟩
  · have habs : |x - 1| ≤ 1/2 := by
      rw [abs_of_neg (by linarith : x - 1 < 0)]
      linarith
    have hcoe1 : ((1:ℝ) : Circ) = 0 := AddCircle.coe_period 1
    have hcoe : ((x - 1 : ℝ) : Circ) = ξ := by
      rw [sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg, hxcoe, hcoe1, neg_zero, add_zero]
    have hnorm : ‖((x - 1 : ℝ) : Circ)‖ = |x - 1| := by
      refine (AddCircle.norm_coe_eq_abs_iff 1 (x := x-1) one_ne_zero).mpr ?_
      rw [abs_one]; exact habs
    have hxnorm : |x - 1| = ‖ξ‖ := hnorm.symm.trans (congrArg Norm.norm hcoe)
    exact ⟨x - 1, by rw [hxnorm]; exact h, by rw [zero_add]; exact hcoe.symm⟩

/-- Outside the `δ`-arc around `0`, the circle norm exceeds `δ`. -/
lemma lt_norm_of_not_mem_arcSet {δ : ℝ} {ξ : Circ}
    (h : ξ ∉ Work.BourgainPlan.IonescuWainger.arcSet 0 δ) : δ < ‖ξ‖ :=
  lt_of_not_ge fun hle => h (mem_arcSet_of_norm_le hle)

/-- An absolutely summable sequence on `ℤ` is square summable. -/
lemma memlp_two_of_summable_norm {a : ℤ → ℂ} (h : Summable (fun j : ℤ => ‖a j‖)) :
    Memℓp a 2 := by
  set B : ℝ := ∑' j : ℤ, ‖a j‖ with hB
  have hle : ∀ j : ℤ, ‖a j‖ ≤ B := fun j => Summable.le_tsum h j (fun j _ => norm_nonneg _)
  have h2 : Summable (fun j : ℤ => ‖a j‖ ^ (2 : ℝ)) :=
    Summable.of_nonneg_of_le (fun j => Real.rpow_nonneg (norm_nonneg _) _)
      (fun j => by
        rw [Real.rpow_two, pow_two]
        exact mul_le_mul_of_nonneg_right (hle j) (norm_nonneg _))
      (h.mul_left B)
  rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
  convert h2 using 2
  rw [ENNReal.toReal_ofNat]


end Work.KMTAreas.A7Hi
