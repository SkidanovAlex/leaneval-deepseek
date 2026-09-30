import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.jsum_integrand_bound
import Submission.Work.BW.jsum_sum_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- BW §19 (27), residue-sum side: with `F(z) = ∏_{l' ∈ Z} β(z;l')^{T'+1}` and `f_m(l)` the Taylor coefficients of `f` at `l` (BW's (21)/(22) bound them by `‖f s‖ e^V`), the sum of residue integrals over the circles `C_l = {|z - l| = η}` is bounded by `|Z|(T'+1) η/(κ-η) e^{V+Y} ‖f s‖/‖F(s)‖`, using `|z - s| ≥ κ - η` on `C_l` (from `|s - l| ≥ κ`) and `‖F(s)‖ ≤ ‖F(z)‖ e^Y` on `C_l`. -/
lemma jsum_bound (f : ℂ → ℂ) (R η κ : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hκη : η < κ)
    (Z : Finset ℤ) (Tp : ℕ) (s : ℂ) (V Y : ℝ)
    (hsZ : ∀ l ∈ Z, κ ≤ ‖s - l‖)
    (hV : ∀ l ∈ Z, ∀ m ≤ Tp, ‖taylorC f m l‖ ≤ ‖f s‖ * Real.exp V)
    (hY : ∀ l ∈ Z, ∀ z : ℂ, ‖z - l‖ = η →
      ‖∏ l' ∈ Z, bfac R l' s ^ (Tp + 1)‖ ≤ ‖∏ l' ∈ Z, bfac R l' z ^ (Tp + 1)‖ * Real.exp Y)
    (hFs : (∏ l ∈ Z, bfac R l s ^ (Tp + 1)) ≠ 0) :
    ‖∑ l ∈ Z, ∑ m ∈ Finset.range (Tp + 1), taylorC f m l *
        ((2 * Real.pi * Complex.I)⁻¹ *
          ∮ z in C((l : ℂ), η), (z - l) ^ m / ((z - s) * ∏ l' ∈ Z, bfac R l' z ^ (Tp + 1)))‖
      ≤ ((Z.card : ℝ) * (Tp + 1) * (η / (κ - η)) * Real.exp (V + Y)) *
          (‖f s‖ / ‖(∏ l ∈ Z, bfac R l s ^ (Tp + 1))‖) := by
  have hterm : ∀ l ∈ Z, ∀ m ∈ Finset.range (Tp + 1),
      ‖taylorC f m l * ((2 * Real.pi * Complex.I)⁻¹ *
          ∮ z in C((l : ℂ), η), (z - l) ^ m / ((z - s) * ∏ l' ∈ Z, bfac R l' z ^ (Tp + 1)))‖
        ≤ η / (κ - η) * Real.exp (V + Y) * (‖f s‖ / ‖∏ l ∈ Z, bfac R l s ^ (Tp + 1)‖) := by
    intro l hl m hm
    have hmTp : m ≤ Tp := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have htv := hV l hl m hmTp
    have hcirc : ‖(2 * Real.pi * Complex.I)⁻¹ *
        ∮ z in C((l : ℂ), η), (z - l) ^ m / ((z - s) * ∏ l' ∈ Z, bfac R l' z ^ (Tp + 1))‖
        ≤ η * (Real.exp Y / ((κ - η) * ‖∏ l' ∈ Z, bfac R l' s ^ (Tp + 1)‖)) := by
      have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
        (f := fun z => (z - (l:ℂ)) ^ m / ((z - s) * ∏ l' ∈ Z, bfac R l' z ^ (Tp + 1)))
        (c := (l : ℂ)) (R := η)
        (C := Real.exp Y / ((κ - η) * ‖∏ l' ∈ Z, bfac R l' s ^ (Tp + 1)‖)) hη.le ?_
      · simpa only [smul_eq_mul] using h
      · intro z hz
        rw [mem_sphere_iff_norm] at hz
        exact jsum_integrand_bound (fun z => ∏ l' ∈ Z, bfac R l' z ^ (Tp + 1)) Y η κ hη hη1 hκη
          s z (l : ℂ) m hz (hsZ l hl) hFs (hY l hl z hz)
    calc ‖taylorC f m l * ((2 * Real.pi * Complex.I)⁻¹ *
          ∮ z in C((l : ℂ), η), (z - l) ^ m / ((z - s) * ∏ l' ∈ Z, bfac R l' z ^ (Tp + 1)))‖
        = ‖taylorC f m l‖ * ‖(2 * Real.pi * Complex.I)⁻¹ *
          ∮ z in C((l : ℂ), η), (z - l) ^ m / ((z - s) * ∏ l' ∈ Z, bfac R l' z ^ (Tp + 1))‖ :=
          norm_mul _ _
      _ ≤ (‖f s‖ * Real.exp V) *
            (η * (Real.exp Y / ((κ - η) * ‖∏ l' ∈ Z, bfac R l' s ^ (Tp + 1)‖))) :=
          mul_le_mul htv hcirc (norm_nonneg _) (by positivity)
      _ = η / (κ - η) * Real.exp (V + Y) * (‖f s‖ / ‖∏ l ∈ Z, bfac R l s ^ (Tp + 1)‖) := by
          rw [Real.exp_add]
          have hne : κ - η ≠ 0 := ne_of_gt (sub_pos.mpr hκη)
          have hFne : ‖∏ l ∈ Z, bfac R l s ^ (Tp + 1)‖ ≠ 0 :=
            ne_of_gt (norm_pos_iff.mpr hFs)
          field_simp
  have hsum := jsum_sum_bound Z Tp
      (fun l m => taylorC f m l * ((2 * Real.pi * Complex.I)⁻¹ *
          ∮ z in C((l : ℂ), η), (z - l) ^ m / ((z - s) * ∏ l' ∈ Z, bfac R l' z ^ (Tp + 1))))
      (η / (κ - η) * Real.exp (V + Y) * (‖f s‖ / ‖∏ l ∈ Z, bfac R l s ^ (Tp + 1)‖)) hterm
  refine hsum.trans (le_of_eq ?_)
  ring

end Work.BW
