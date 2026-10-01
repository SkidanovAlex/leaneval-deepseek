/-
# `T13.Basic` — the analytic/numeric bridge lemmas for the `table13_cert` certificate
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.T13.Defs
import Submission.Work.LinnikAreas.Density4.t13_ft_laplace
import Submission.Work.LinnikAreas.Density4.t13_ft_zero
import Submission.Work.LinnikAreas.A7.ExpBounds

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4.T13

open Work.LinnikAreas.Density4

/-! ## The closed form in atom form -/

/-- `FT` in terms of the atoms `T = tan θ`, `cos²θ`, `sin 2θ`, `cos 2θ`, `exp (-(2γz))`. -/
theorem FTreal_spec (th lam z : ℝ) (hθ1 : Real.pi / 2 < th) (hθ2 : th < Real.pi)
    (hlam : 0 < lam) (hz : z ≠ 0) :
    FT th lam z = FTreal th lam z (Real.tan th) (Real.cos th ^ 2) (Real.sin (2 * th))
      (Real.cos (2 * th)) (Real.exp (-(2 * gammaT th lam * z))) := by
  rw [t13_ft_laplace th lam z hθ1 hθ2 hlam hz]
  have htan : Real.tan th ≠ 0 := ne_of_lt (tan_neg_of_half_pi_lt hθ1 hθ2)
  have hζ : -lam * Real.tan th ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hlam)) htan
  have hz2 : (0:ℝ) < z ^ 2 := by positivity
  have hW : z ^ 2 + (-lam * Real.tan th) ^ 2 ≠ 0 := by positivity
  simp only [FTreal, zetaT, gammaT]
  field_simp
  ring

/-! ## The interval enclosure of `FT` -/

theorem FT_mem (th lam z : ℝ) (Ti C2i S2i CC2i Ei : Iv)
    (hθ1 : Real.pi / 2 < th) (hθ2 : th < Real.pi) (hlam : 0 < lam) (hz : z ≠ 0)
    (hT : Ti.Mem (Real.tan th)) (hTi : Ti.hi < 0)
    (hC2 : C2i.Mem (Real.cos th ^ 2)) (hS2 : S2i.Mem (Real.sin (2 * th)))
    (hCC2 : CC2i.Mem (Real.cos (2 * th))) (hE : Ei.Mem (Real.exp (-(2 * gammaT th lam * z))))
    (hD : 0 < (Divv lam z Ti).lo) :
    (Iv.div (Miv th lam z Ti C2i S2i CC2i Ei) (Divv lam z Ti)).Mem (FT th lam z) := by
  rw [FTreal_spec th lam z hθ1 hθ2 hlam hz]
  have h1 := Miv_mem th lam z Ti C2i S2i CC2i Ei _ _ _ _ _ hT hC2 hS2 hCC2 hE
  have h2 := Divv_mem lam z Ti _ hT
  have hd := Iv.mem_div h1 h2 hD
  have hTne : Real.tan th ≠ 0 := ne_of_lt (tan_neg_of_half_pi_lt hθ1 hθ2)
  have hz2 : (0:ℝ) < z ^ 2 := by positivity
  have hWne : z ^ 2 + (lam * Real.tan th) ^ 2 ≠ 0 := by positivity
  rwa [← FTreal_eq th lam z _ _ _ _ _ hz (ne_of_gt hlam) hTne hWne] at hd

/-- Interval enclosure of `fT θ lam 0 / 6`. -/
theorem C_mem (th lam : ℝ) (Ti : Iv)
    (hθ1 : Real.pi / 2 < th) (hθ2 : th < Real.pi) (hlam : 0 < lam)
    (hT : Ti.Mem (Real.tan th)) (hD : 0 < (D0iv Ti).lo) :
    (Iv.div (M0iv th lam Ti) (D0iv Ti)).Mem (fT th lam 0 / 6) := by
  rw [t13_ft_zero th lam hθ1 hθ2 hlam]
  have hTne : Real.tan th ≠ 0 := ne_of_lt (tan_neg_of_half_pi_lt hθ1 hθ2)
  have h1 := M0mem th lam Ti _ hT
  have h2 := D0mem Ti _ hT
  have hd := Iv.mem_div h1 h2 hD
  have hM0 : lam * (1 + Real.tan th ^ 2) * (3 - th * Real.tan th - 3 * th / Real.tan th) / 6
      = M0real th lam (Real.tan th) / D0real (Real.tan th) := by
    rw [← M0_eq th lam (Real.tan th) hTne]
    simp only [f0real]
    ring
  rwa [hM0]

/-! ## Interval enclosure of `exp` of an interval -/

theorem exp_lower {x elo : ℝ} (n : ℕ) (h : |x| / ((n:ℝ) + 1) ≤ 1 / 2)
    (h2 : elo ≤ (∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℝ)) - |x| ^ n / (n.factorial : ℝ) * 2) :
    elo ≤ Real.exp x := by
  have hb := Work.LinnikAreas.A7.exp_rem_bound x n h
  have h1 := (abs_le.mp hb).1
  linarith

theorem exp_upper {x ehi : ℝ} (n : ℕ) (h : |x| / ((n:ℝ) + 1) ≤ 1 / 2)
    (h2 : (∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℝ)) + |x| ^ n / (n.factorial : ℝ) * 2 ≤ ehi) :
    Real.exp x ≤ ehi := by
  have hb := Work.LinnikAreas.A7.exp_rem_bound x n h
  have h1 := (abs_le.mp hb).2
  linarith

theorem exp_mem_of_iv {W : Iv} {w : ℝ} (hw : W.Mem w) {elo ehi : ℝ}
    (h1 : elo ≤ Real.exp W.lo) (h2 : Real.exp W.hi ≤ ehi) :
    (⟨elo, ehi⟩ : Iv).Mem (Real.exp w) :=
  ⟨le_trans h1 (Real.exp_le_exp.mpr hw.1), le_trans (Real.exp_le_exp.mpr hw.2) h2⟩

/-! ## The interval enclosure of the exp argument `-(2γz)` -/

/-- `-(2 γ z) = 2 θ z / (λ tan θ)`. -/
theorem neg_two_gammaT_mul_eq (th lam z : ℝ) (hlam : lam ≠ 0) (hT : Real.tan th ≠ 0) :
    -(2 * gammaT th lam * z) = 2 * th * z / (lam * Real.tan th) := by
  simp only [gammaT, zetaT]
  field_simp

def Wiv (th lam z : ℝ) (Ti : Iv) : Iv :=
  Iv.mul (Iv.ofReal (2 * th * z))
    (Iv.neg (Iv.inv (Iv.neg (Iv.mul (Iv.ofReal lam) Ti))))

theorem Wiv_mem {th lam z : ℝ} {Ti : Iv} (hT : Ti.Mem (Real.tan th)) (hTi : Ti.hi < 0)
    (hlam : 0 < lam) :
    (Wiv th lam z Ti).Mem (-(2 * gammaT th lam * z)) := by
  have h1 : 0 < (Iv.neg (Iv.mul (Iv.ofReal lam) Ti)).lo := by
    simp only [Iv.neg, Iv.mul, Iv.ofReal, max_self]
    rw [max_eq_right (by nlinarith [hlam, hT.1, hT.2] : lam * Ti.lo ≤ lam * Ti.hi)]
    nlinarith [hlam, hTi]
  have h := Iv.mem_mul (Iv.mem_ofReal (2 * th * z))
    (Iv.mem_neg (Iv.mem_inv (Iv.mem_neg (Iv.mem_mul (Iv.mem_ofReal lam) hT)) h1))
  have hT0 : Real.tan th ≠ 0 := ne_of_lt (lt_of_le_of_lt hT.2 hTi)
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  have heq : (2 * th * z) * (-( (-(lam * Real.tan th))⁻¹)) = -(2 * gammaT th lam * z) := by
    rw [neg_two_gammaT_mul_eq th lam z hlam0 hT0]
    field_simp
  rwa [heq] at h

/-! ## The rational ratio bound -/

theorem ratio_bound {A B c Alo Ahi Blo Bhi clo chi ub : ℝ}
    (hA1 : Alo ≤ A) (hA2 : A ≤ Ahi) (hB1 : Blo ≤ B) (hB2 : B ≤ Bhi)
    (hc1 : clo ≤ c) (hc2 : c ≤ chi)
    (hAlo0 : 0 ≤ Alo) (hclo0 : 0 ≤ clo) (hcAlo : chi ≤ Alo) (hcBlo : chi ≤ Blo)
    (hden : 0 < (Blo - chi) ^ 2 - Ahi * chi)
    (hub : Ahi * (Ahi - clo) / ((Blo - chi) ^ 2 - Ahi * chi) < ub) :
    A * (A - c) / ((B - c) ^ 2 - A * c) < ub := by
  have hA0 : 0 ≤ A := le_trans hAlo0 hA1
  have hAhi0 : 0 ≤ Ahi := le_trans hA0 hA2
  have hc0 : 0 ≤ c := le_trans hclo0 hc1
  have hAc : 0 ≤ A - c := by linarith
  have hAc' : A - c ≤ Ahi - clo := by linarith
  have hnum : A * (A - c) ≤ Ahi * (Ahi - clo) := mul_le_mul hA2 hAc' hAc hAhi0
  have hnum0 : 0 ≤ A * (A - c) := mul_nonneg hA0 hAc
  have hnumhi0 : 0 ≤ Ahi * (Ahi - clo) := le_trans hnum0 hnum
  have hden_ge : (Blo - chi) ^ 2 - Ahi * chi ≤ (B - c) ^ 2 - A * c := by
    have h1 : Blo - chi ≤ B - c := by linarith
    have h2 : 0 ≤ Blo - chi := by linarith
    have h3 : (Blo - chi) ^ 2 ≤ (B - c) ^ 2 := by nlinarith
    have h4 : A * c ≤ Ahi * chi := by
      have h5 : A * c ≤ Ahi * c := mul_le_mul_of_nonneg_right hA2 hc0
      have h6 : Ahi * c ≤ Ahi * chi := mul_le_mul_of_nonneg_left hc2 hAhi0
      linarith
    linarith
  have hdenpos : 0 < (B - c) ^ 2 - A * c := lt_of_lt_of_le hden hden_ge
  have hstep1 : A * (A - c) / ((B - c) ^ 2 - A * c) ≤ Ahi * (Ahi - clo) / ((B - c) ^ 2 - A * c) :=
    div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)
  have hstep2 : Ahi * (Ahi - clo) / ((B - c) ^ 2 - A * c)
      ≤ Ahi * (Ahi - clo) / ((Blo - chi) ^ 2 - Ahi * chi) :=
    div_le_div_of_nonneg_left hnumhi0 hden hden_ge
  linarith

end Work.LinnikAreas.Density4.T13
