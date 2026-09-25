import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

namespace Work.NN.Core

private lemma min_one_mul_le_rpow {M d α : ℝ} (hM : 0 ≤ M) (hd : 0 < d) (hα0 : 0 < α)
    (hα1 : α < 1) :
    min 1 (M * d) ≤ (1 + M) * d ^ α := by
  have hdα : 0 < d ^ α := Real.rpow_pos_of_pos hd α
  rcases le_or_gt d 1 with h1 | h1
  · have hle : d ≤ d ^ α := by
      have h := Real.rpow_le_rpow_of_exponent_ge hd h1 hα1.le
      rwa [Real.rpow_one] at h
    calc min 1 (M * d) ≤ M * d := min_le_right _ _
      _ ≤ M * d ^ α := mul_le_mul_of_nonneg_left hle hM
      _ ≤ (1 + M) * d ^ α := by nlinarith [hdα]
  · have h2 : 1 ≤ d ^ α := Real.one_le_rpow h1.le hα0.le
    calc min 1 (M * d) ≤ 1 := min_le_left _ _
      _ ≤ d ^ α := h2
      _ ≤ (1 + M) * d ^ α := by nlinarith [hdα, hM]

private lemma three_mul_nonneg {M ε D : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M) (hD : 0 ≤ D) :
    0 ≤ 3 * ε * (1 + M) * D :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε) (by linarith)) hD

private lemma norm_mul_reals {n : ℕ} (χ : Cn n → ℝ) (g : Cn n → ℂ) (z : Cn n) :
    ‖χ z * g z‖ = |χ z| * ‖g z‖ := by
  rw [show χ z * g z = (χ z : ℂ) * g z from rfl, norm_mul]
  congr 1
  simp only [Complex.norm_real, Real.norm_eq_abs]

private lemma norm_mul_reals_left {n : ℕ} (χ : Cn n → ℝ) (g : Cn n → ℂ) (x y : Cn n) :
    ‖(χ x : ℂ) * (g x - g y)‖ = |χ x| * ‖g x - g y‖ := by
  rw [norm_mul]
  congr 1
  simp only [Complex.norm_real, Real.norm_eq_abs]

private lemma norm_sub_reals {n : ℕ} (χ : Cn n → ℝ) (g : Cn n → ℂ) (x y : Cn n) :
    ‖((χ x : ℂ) - (χ y : ℂ)) * g y‖ = |χ x - χ y| * ‖g y‖ := by
  rw [norm_mul]
  congr 1
  rw [← Complex.ofReal_sub]
  simp only [Complex.norm_real, Real.norm_eq_abs]

theorem chiMulEntry {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {M : ℝ} (hM : 0 ≤ M) {χ : Cn n → ℝ} (hχ : ContDiff ℝ 1 χ) (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) (hχgrad : ∀ z, ‖fderiv ℝ χ z‖ ≤ M) (hχsupp : ∀ z, χ z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) {g : Cn n → ℂ} (hg : ContDiff ℝ 1 g) {ε : ℝ} (hε : 0 ≤ ε) (hgε : Work.CR.Flat.holderNorm 1 α g (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) : (∀ z, ‖χ z * g z‖ ≤ ε) ∧ (∀ x y, ‖χ x * g x - χ y * g y‖ ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α) := by
  have _ := hρ
  have _ := hg
  have hdiff : ∀ z : Cn n, DifferentiableAt ℝ χ z :=
    fun z => (hχ.differentiable (by norm_num)).differentiableAt
  have hlip : ∀ x y : Cn n, |χ x - χ y| ≤ M * ‖x - y‖ := fun x y => by
    have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := χ) (C := M) (s := Set.univ)
      (fun z _ => hdiff z) (fun z _ => hχgrad z) (Set.mem_univ x) (Set.mem_univ y)
    rw [Real.norm_eq_abs, abs_sub_comm, norm_sub_rev] at h
    exact h
  have hgΩ : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρ → ‖g z‖ ≤ ε := fun z hz =>
    (ENNReal.ofReal_le_ofReal_iff hε).mp
      (le_trans (Work.CR.Flat.norm_apply_le_holderNorm 1 α g _ hz) hgε)
  have hghold : ∀ x, x ∈ Work.CR.Flat.polydisc 0 ρ → ∀ y, y ∈ Work.CR.Flat.polydisc 0 ρ →
      x ≠ y → ‖g x - g y‖ ≤ ε * ‖x - y‖ ^ α := by
    intro x hx y hy hxy
    have hη : ‖iteratedFDerivWithin ℝ 0 g (Work.CR.Flat.polydisc 0 ρ) x
        - iteratedFDerivWithin ℝ 0 g (Work.CR.Flat.polydisc 0 ρ) y‖ = ‖g x - g y‖ := by
      rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]
    have hmain : ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) ≤ ENNReal.ofReal ε := by
      refine le_trans ?_ hgε
      have h := Work.CR.Flat.le_holderSeminorm 0 α g (Work.CR.Flat.polydisc 0 ρ) hx hy hxy
      rw [hη] at h
      exact le_trans h (Work.CR.Flat.holderSeminorm_le_holderNorm 1 α g
        (Work.CR.Flat.polydisc 0 ρ) (Nat.zero_le 1))
    have hle := (ENNReal.ofReal_le_ofReal_iff hε).mp hmain
    have hp : (0 : ℝ) < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    rwa [div_le_iff₀ hp] at hle
  refine ⟨?_, ?_⟩
  · intro z
    rcases eq_or_ne (χ z) 0 with hz0 | hz0
    · rw [hz0]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      exact hε
    · have hgz : ‖g z‖ ≤ ε := hgΩ z (hχsupp z hz0)
      have habs : |χ z| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ01 z).1], (hχ01 z).2⟩
      rw [norm_mul_reals χ g z]
      calc |χ z| * ‖g z‖ ≤ 1 * ε := mul_le_mul habs hgz (norm_nonneg _) (by norm_num)
        _ = ε := one_mul ε
  · intro x y
    by_cases hxy : x = y
    · rw [hxy]
      simp [sub_self, Real.zero_rpow (ne_of_gt hα0)]
    · have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hdα : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hd α
      have hmin0 : (0 : ℝ) ≤ min 1 (M * ‖x - y‖) :=
        le_min (by norm_num) (mul_nonneg hM (norm_nonneg _))
      have hmin_le : min 1 (M * ‖x - y‖) ≤ (1 + M) * ‖x - y‖ ^ α :=
        min_one_mul_le_rpow hM hd hα0 hα1
      have hfin : min 1 (M * ‖x - y‖) * ε ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α := by
        calc min 1 (M * ‖x - y‖) * ε ≤ ((1 + M) * ‖x - y‖ ^ α) * ε :=
              mul_le_mul_of_nonneg_right hmin_le hε
          _ ≤ 3 * (((1 + M) * ‖x - y‖ ^ α) * ε) := by
              have hx0 : (0 : ℝ) ≤ ((1 + M) * ‖x - y‖ ^ α) * ε :=
                mul_nonneg (mul_nonneg (by linarith) hdα.le) hε
              linarith
          _ = 3 * ε * (1 + M) * ‖x - y‖ ^ α := by ring
      by_cases hx0 : χ x = 0
      · have hL : ‖χ x * g x - χ y * g y‖ = ‖χ y * g y‖ := by rw [hx0]; simp
        rw [hL]
        by_cases hy0 : χ y = 0
        · rw [hy0]
          simp only [Complex.ofReal_zero, zero_mul, norm_zero]
          exact three_mul_nonneg hε hM hdα.le
        · have hyΩ : y ∈ Work.CR.Flat.polydisc 0 ρ := hχsupp y hy0
          have hgy : ‖g y‖ ≤ ε := hgΩ y hyΩ
          have habs1 : |χ y| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ01 y).1], (hχ01 y).2⟩
          have habs2 : |χ y| ≤ M * ‖x - y‖ := by
            have h := hlip y x
            have hx' : χ y - χ x = χ y := by rw [hx0, sub_zero]
            rw [hx', norm_sub_rev] at h
            exact h
          rw [norm_mul_reals χ g y]
          calc |χ y| * ‖g y‖ ≤ (min 1 (M * ‖x - y‖)) * ε :=
                mul_le_mul (le_min habs1 habs2) hgy (norm_nonneg _) hmin0
            _ ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α := hfin
      · by_cases hy0 : χ y = 0
        · have hL : ‖χ x * g x - χ y * g y‖ = ‖χ x * g x‖ := by rw [hy0]; simp
          rw [hL]
          have hxΩ : x ∈ Work.CR.Flat.polydisc 0 ρ := hχsupp x hx0
          have hgx : ‖g x‖ ≤ ε := hgΩ x hxΩ
          have habs1 : |χ x| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ01 x).1], (hχ01 x).2⟩
          have habs2 : |χ x| ≤ M * ‖x - y‖ := by
            have h := hlip x y
            have hy' : χ x - χ y = χ x := by rw [hy0, sub_zero]
            rwa [hy'] at h
          rw [norm_mul_reals χ g x]
          calc |χ x| * ‖g x‖ ≤ (min 1 (M * ‖x - y‖)) * ε :=
                mul_le_mul (le_min habs1 habs2) hgx (norm_nonneg _) hmin0
            _ ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α := hfin
        · have hxΩ : x ∈ Work.CR.Flat.polydisc 0 ρ := hχsupp x hx0
          have hyΩ : y ∈ Work.CR.Flat.polydisc 0 ρ := hχsupp y hy0
          have hgy : ‖g y‖ ≤ ε := hgΩ y hyΩ
          have hgh : ‖g x - g y‖ ≤ ε * ‖x - y‖ ^ α := hghold x hxΩ y hyΩ hxy
          have habsx : |χ x| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ01 x).1], (hχ01 x).2⟩
          have habs1 : |χ x - χ y| ≤ 1 :=
            abs_le.mpr ⟨by linarith [(hχ01 x).1, (hχ01 y).2],
              by linarith [(hχ01 x).2, (hχ01 y).1]⟩
          have hmin : |χ x - χ y| ≤ min 1 (M * ‖x - y‖) := le_min habs1 (hlip x y)
          have hdecomp : χ x * g x - χ y * g y
              = (χ x : ℂ) * (g x - g y) + ((χ x : ℂ) - (χ y : ℂ)) * g y := by ring
          rw [hdecomp]
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul_reals_left χ g x y, norm_sub_reals χ g x y]
          have hfin'' : min 1 (M * ‖x - y‖) * ε ≤ ((1 + M) * ‖x - y‖ ^ α) * ε :=
            mul_le_mul_of_nonneg_right hmin_le hε
          calc |χ x| * ‖g x - g y‖ + |χ x - χ y| * ‖g y‖
              ≤ 1 * (ε * ‖x - y‖ ^ α) + (min 1 (M * ‖x - y‖)) * ε :=
                add_le_add (mul_le_mul habsx hgh (norm_nonneg _) (by norm_num))
                  (mul_le_mul hmin hgy (norm_nonneg _) hmin0)
            _ ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α := by
                rw [one_mul]
                calc ε * ‖x - y‖ ^ α + (min 1 (M * ‖x - y‖)) * ε
                    ≤ ε * ‖x - y‖ ^ α + ((1 + M) * ‖x - y‖ ^ α) * ε :=
                      add_le_add le_rfl hfin''
                  _ = ε * ‖x - y‖ ^ α * (2 + M) := by ring
                  _ ≤ ε * ‖x - y‖ ^ α * (3 * (1 + M)) :=
                      mul_le_mul_of_nonneg_left (by linarith [hM]) (mul_nonneg hε hdα.le)
                  _ = 3 * ε * (1 + M) * ‖x - y‖ ^ α := by ring

end Work.NN.Core
