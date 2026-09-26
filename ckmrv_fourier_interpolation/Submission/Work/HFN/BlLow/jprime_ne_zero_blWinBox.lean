/-
# `j' ≠ 0` on the compact box `blWinBox`

The kernel-window argument of `Work.Asymptotics.BlLow` needs `j' ≠ 0` on the closed box
`blWinBox = {|Re| ≤ 1/4, Im ∈ [1/3, 2/3]}`, because `j'` is the derivative of the local
coordinate `j` there (`Work.Asymptotics.Tile.tile_jDiff_linear_compact`).

By `Work.Residues.jprime_ne_zero_iff` and `j' = -2πi E₄²E₆/Δ` it suffices to keep both
`E₄` and `E₆` away from `0` on the box.

* `E₆ z = 0` forces `j z = 1728 = j(i)`, hence `z = γ • i` for some `γ ∈ SL(2,ℤ)`; the height
  formula `orbit_im_I` gives `Im z = 1/(c² + d²)` with `c = γ 1 0`, `d = γ 1 1`, so the box
  bounds pin `c² + d² ∈ [3/2, 3]`, while the real-part bound and the determinant `ad - bc = 1`
  together give `(a² + b²)(c² + d²) = 1`, impossible since `c² + d² ≥ 2`.
* `E₄ z = 0` forces `j z = 0 = j(ρ)`, hence `z = γ • ρ` with `ρ = e^{2πi/3}`; the height
  formula `orbit_im_rhoH` gives `Im z = (√3/2)/(c² - cd + d²)`, so the box bounds pin
  `c² - cd + d² = 2`, which has no integer solution since `c² - cd + d² ≡ (c+d)² (mod 3)`
  while `2` is not a square mod `3`.
-/
import Mathlib
import Submission.Work.HFN.BlLow.WinDefs
import Submission.Work.Asymptotics.HalfFunnel.tangPrincipalPart
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

namespace Work.HFN.BlLow
open Work.Asymptotics Work.Asymptotics.BlLow  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open UpperHalfPlane

/-- `E₆ ≠ 0` on `blWinBox`. -/
private lemma E6Fun_ne_zero_blWinBox {z : UpperHalfPlane}
    (hz : z ∈ blWinBox) : Work.Kernels.E6Fun z ≠ 0 := by
  intro h0
  obtain ⟨hre, hlo, hhi⟩ := hz
  have hjz : Work.Kernels.jInvariantFun z = 1728 :=
    Work.Asymptotics.HalfFunnel.jInvariantFun_eq_1728_of_E6Fun_eq_zero h0
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq (τ := z) (w := UpperHalfPlane.I)
    (by rw [hjz, Work.Asymptotics.HalfFunnel.jInvariantFun_I])
  have him := Work.Asymptotics.HalfFunnel.orbit_im_I γ
  rw [hγ, UpperHalfPlane.coe_im] at him
  have hreγ := Work.Asymptotics.HalfFunnel.orbit_re_I γ
  rw [hγ, UpperHalfPlane.coe_re] at hreγ
  have hQ : ((γ 1 0 : ℤ) : ℝ) ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2
      = (((γ 1 0) ^ 2 + (γ 1 1) ^ 2 : ℤ) : ℝ) := by push_cast; ring
  have hS : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) + ((γ 0 1 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ)
      = (((γ 0 0) * (γ 1 0) + (γ 0 1) * (γ 1 1) : ℤ) : ℝ) := by push_cast; ring
  rw [hQ] at him
  rw [hS, hQ] at hreγ
  have hdet : (γ 0 0) * (γ 1 1) - (γ 0 1) * (γ 1 0) = (1 : ℤ) := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    exact h
  have hQpos : (0:ℝ) < (((γ 1 0)^2 + (γ 1 1)^2 : ℤ) : ℝ) := by
    have h := Work.Asymptotics.HalfFunnel.bottom_row_ne γ
    have hz0 : (0:ℤ) < (γ 1 0)^2 + (γ 1 1)^2 := by
      rcases h with hc | hd
      · have := Work.Asymptotics.HalfFunnel.sq_ge_one _ hc
        nlinarith [sq_nonneg (γ 1 1)]
      · have := Work.Asymptotics.HalfFunnel.sq_ge_one _ hd
        nlinarith [sq_nonneg (γ 1 0)]
    exact_mod_cast hz0
  have hQle : (((γ 1 0)^2 + (γ 1 1)^2 : ℤ) : ℝ) ≤ 3 := by
    have h := hlo
    rw [him] at h
    rw [le_div_iff₀ hQpos] at h
    linarith
  have hQge : (3:ℝ)/2 ≤ (((γ 1 0)^2 + (γ 1 1)^2 : ℤ) : ℝ) := by
    have h := hhi
    rw [him] at h
    rw [div_le_iff₀ hQpos] at h
    linarith
  have hS0 : (γ 0 0) * (γ 1 0) + (γ 0 1) * (γ 1 1) = (0:ℤ) := by
    have h1 : |(((γ 0 0) * (γ 1 0) + (γ 0 1) * (γ 1 1) : ℤ) : ℝ)|
        / (((γ 1 0)^2 + (γ 1 1)^2 : ℤ) : ℝ) ≤ 1/4 := by
      have := hre
      rw [hreγ, abs_div, abs_of_pos hQpos] at this
      exact this
    have h2 : |(((γ 0 0) * (γ 1 0) + (γ 0 1) * (γ 1 1) : ℤ) : ℝ)| ≤ 3/4 := by
      have hm := mul_le_mul_of_nonneg_right h1 (le_of_lt hQpos)
      rw [div_mul_cancel₀ _ (ne_of_gt hQpos)] at hm
      nlinarith [hQle]
    have hlt1 : (((γ 0 0) * (γ 1 0) + (γ 0 1) * (γ 1 1) : ℤ) : ℝ) < 1 := by
      have := (abs_le.mp h2).2; linarith
    have hgt1 : -1 < (((γ 0 0) * (γ 1 0) + (γ 0 1) * (γ 1 1) : ℤ) : ℝ) := by
      have := (abs_le.mp h2).1; linarith
    have hlt1' : ((γ 0 0) * (γ 1 0) + (γ 0 1) * (γ 1 1) : ℤ) < 1 := by exact_mod_cast hlt1
    have hgt1' : -1 < ((γ 0 0) * (γ 1 0) + (γ 0 1) * (γ 1 1) : ℤ) := by exact_mod_cast hgt1
    omega
  have hAQ : ((γ 0 0)^2 + (γ 0 1)^2) * ((γ 1 0)^2 + (γ 1 1)^2) = 1 := by
    nlinarith [hS0, hdet]
  have htop : (γ 0 0) ≠ 0 ∨ (γ 0 1) ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1, h2] at hdet
    norm_num at hdet
  have hA1 : (1:ℤ) ≤ (γ 0 0)^2 + (γ 0 1)^2 := by
    rcases htop with h | h
    · have := Work.Asymptotics.HalfFunnel.sq_ge_one _ h; nlinarith [sq_nonneg (γ 0 1)]
    · have := Work.Asymptotics.HalfFunnel.sq_ge_one _ h; nlinarith [sq_nonneg (γ 0 0)]
  have hQ2 : (2:ℤ) ≤ (γ 1 0)^2 + (γ 1 1)^2 := by
    have h1 : (1:ℝ) < (((γ 1 0)^2 + (γ 1 1)^2 : ℤ) : ℝ) := by linarith [hQge]
    have h2 : (1:ℤ) < (γ 1 0)^2 + (γ 1 1)^2 := by exact_mod_cast h1
    omega
  nlinarith [hAQ, hA1, hQ2]

/-- `E₄ ≠ 0` on `blWinBox`. -/
private lemma E4Fun_ne_zero_blWinBox {z : UpperHalfPlane}
    (hz : z ∈ blWinBox) : Work.Kernels.E4Fun z ≠ 0 := by
  intro h0
  obtain ⟨hre, hlo, hhi⟩ := hz
  have hjz : Work.Kernels.jInvariantFun z = 0 := by
    have h : Work.Kernels.jInvariantFun z = Work.Kernels.E4Fun z ^ 3 / Work.Kernels.DeltaFun z := rfl
    rw [h, h0]; norm_num
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq (τ := z)
    (w := Work.Asymptotics.HalfFunnel.rhoH)
    (by rw [hjz, Work.Asymptotics.HalfFunnel.jInvariantFun_rhoH])
  have him := Work.Asymptotics.HalfFunnel.orbit_im_rhoH γ
  rw [hγ, UpperHalfPlane.coe_im] at him
  have hQ : ((γ 1 0 : ℤ) : ℝ) ^ 2 - ((γ 1 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ)
      + ((γ 1 1 : ℤ) : ℝ) ^ 2
      = (((γ 1 0) ^ 2 - (γ 1 0) * (γ 1 1) + (γ 1 1) ^ 2 : ℤ) : ℝ) := by push_cast; ring
  rw [hQ] at him
  have hQpos : (0:ℝ) < (((γ 1 0)^2 - (γ 1 0) * (γ 1 1) + (γ 1 1)^2 : ℤ) : ℝ) := by
    have h := Work.Asymptotics.HalfFunnel.bottom_row_ne γ
    have hz0 : (0:ℤ) < (γ 1 0)^2 - (γ 1 0) * (γ 1 1) + (γ 1 1)^2 := by
      have := Work.Asymptotics.HalfFunnel.form_ge_one (γ 1 0) (γ 1 1) h
      omega
    exact_mod_cast hz0
  have hQle : (((γ 1 0)^2 - (γ 1 0) * (γ 1 1) + (γ 1 1)^2 : ℤ) : ℝ) ≤ 3 * Real.sqrt 3 / 2 := by
    have h := hlo
    rw [him] at h
    rw [le_div_iff₀ hQpos] at h
    nlinarith [h]
  have hQge : 3 * Real.sqrt 3 / 4 ≤
      (((γ 1 0)^2 - (γ 1 0) * (γ 1 1) + (γ 1 1)^2 : ℤ) : ℝ) := by
    have h := hhi
    rw [him] at h
    rw [div_le_iff₀ hQpos] at h
    nlinarith [h]
  have hQeq : (γ 1 0)^2 - (γ 1 0) * (γ 1 1) + (γ 1 1)^2 = 2 := by
    have h1 : (1:ℝ) < (((γ 1 0)^2 - (γ 1 0) * (γ 1 1) + (γ 1 1)^2 : ℤ) : ℝ) := by
      nlinarith [hQge, Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    have h2 : (((γ 1 0)^2 - (γ 1 0) * (γ 1 1) + (γ 1 1)^2 : ℤ) : ℝ) < 3 := by
      nlinarith [hQle, Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    have h1' : (1:ℤ) < (γ 1 0)^2 - (γ 1 0) * (γ 1 1) + (γ 1 1)^2 := by exact_mod_cast h1
    have h2' : (γ 1 0)^2 - (γ 1 0) * (γ 1 1) + (γ 1 1)^2 < (3:ℤ) := by exact_mod_cast h2
    omega
  -- `c² - cd + d² = 2` is impossible: the form is a square modulo `3`.
  have hA : (((γ 1 0)^2 - (γ 1 0) * (γ 1 1) + (γ 1 1)^2 : ℤ) : ZMod 3) = (2 : ZMod 3) := by
    rw [hQeq]; norm_num
  have hB : (((γ 1 0) + (γ 1 1) : ℤ) : ZMod 3) ^ 2 = (2 : ZMod 3) := by
    rw [← hA]
    push_cast
    ring_nf
    rw [show (2 : ZMod 3) = -1 by decide]
    ring
  have hno : ∀ x : ZMod 3, x ^ 2 ≠ (2 : ZMod 3) := by decide
  exact hno _ hB

theorem jprime_ne_zero_blWinBox {z : UpperHalfPlane}
    (hz : z ∈ Work.HFN.BlLow.blWinBox) : Work.Residues.jprime z ≠ 0 := by
  rw [Work.Residues.jprime_ne_zero_iff]
  exact mul_ne_zero (E4Fun_ne_zero_blWinBox hz) (E6Fun_ne_zero_blWinBox hz)

end Work.HFN.BlLow
