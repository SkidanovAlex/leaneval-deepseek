import Mathlib

namespace Work.Potential

open scoped Interval
open MeasureTheory

theorem periodic_integral_deriv_deriv_exp
    {h : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε) (k : ℤ)
    (hh : ContDiffOn ℝ 2 h (Set.Icc (-ε) (2 * Real.pi + ε)))
    (h₀ : h 0 = h (2 * Real.pi)) (h₁ : deriv h 0 = deriv h (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        deriv (deriv h) θ * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
      = -((((k : ℝ) : ℂ)) ^ 2) *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          h θ * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) := by
  have hle : (0 : ℝ) ≤ 2 * Real.pi := le_of_lt Real.two_pi_pos
  let E : ℝ → ℂ := fun θ => Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))
  let C : ℂ := -(((k : ℝ) : ℂ) * Complex.I)
  have hsub : Set.Icc (0 : ℝ) (2 * Real.pi) ⊆ Set.Ioo (-ε) (2 * Real.pi + ε) := by
    intro x hx
    exact ⟨by linarith [hε, hx.1], by linarith [hx.2, hε]⟩
  have hmem : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      θ ∈ Set.Ioo (-ε) (2 * Real.pi + ε) := by
    intro θ hθ
    exact hsub (by rwa [Set.uIcc_of_le hle] at hθ)
  have hd1 : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt h (deriv h θ) θ := by
    intro θ hθ
    exact ((hh.contDiffAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds (hmem θ hθ))
      Set.Ioo_subset_Icc_self)).differentiableAt (by norm_num)).hasDerivAt
  have hderiv : ContDiffOn ℝ 1 (deriv h) (Set.Ioo (-ε) (2 * Real.pi + ε)) :=
    (hh.mono Set.Ioo_subset_Icc_self).deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2 : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt (deriv h) (deriv (deriv h) θ) θ := by
    intro θ hθ
    exact ((hderiv.contDiffAt (isOpen_Ioo.mem_nhds (hmem θ hθ))).differentiableAt
      (by norm_num)).hasDerivAt
  have hg_deriv : ∀ θ : ℝ, HasDerivAt E (E θ * C) θ := by
    intro θ
    change HasDerivAt (fun θ : ℝ => Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
      (Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)) * (-(((k : ℝ) : ℂ) * Complex.I))) θ
    have h1 : HasDerivAt (fun y : ℝ => (k : ℝ) * y) (k : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul ((k : ℝ))
    have h2 : HasDerivAt (fun y : ℝ => (((k : ℝ)) : ℂ) * ((y : ℝ) : ℂ))
        (((k : ℝ)) : ℂ) θ := by
      simpa only [Complex.ofReal_mul] using h1.ofReal_comp
    have h3 : HasDerivAt (fun y : ℝ => (((k : ℝ)) : ℂ) * ((y : ℝ) : ℂ) * Complex.I)
        ((((k : ℝ)) : ℂ) * Complex.I) θ := h2.mul_const Complex.I
    have h4 : HasDerivAt (fun y : ℝ => -(((((k : ℝ)) : ℂ) * ((y : ℝ) : ℂ)) * Complex.I))
        (-((((k : ℝ)) : ℂ) * Complex.I)) θ := h3.neg
    exact h4.cexp
  have hE_cont : Continuous E := by
    change Continuous (fun θ : ℝ => Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
    fun_prop
  have hcont_f : ContinuousOn (fun θ : ℝ => deriv h θ) (Set.uIcc (0 : ℝ) (2 * Real.pi)) :=
    ((hh.mono Set.Ioo_subset_Icc_self).continuousOn_deriv_of_isOpen isOpen_Ioo
      (by norm_num)).mono (by rw [Set.uIcc_of_le hle]; exact hsub)
  have hcont_f2 : ContinuousOn (fun θ : ℝ => deriv (deriv h) θ)
      (Set.uIcc (0 : ℝ) (2 * Real.pi)) :=
    (hderiv.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono
      (by rw [Set.uIcc_of_le hle]; exact hsub)
  have hInt_f : IntervalIntegrable (fun θ : ℝ => deriv h θ) volume (0 : ℝ) (2 * Real.pi) :=
    hcont_f.intervalIntegrable
  have hInt_f2 : IntervalIntegrable (fun θ : ℝ => deriv (deriv h) θ) volume
      (0 : ℝ) (2 * Real.pi) :=
    hcont_f2.intervalIntegrable
  have hInt_v' : IntervalIntegrable (fun θ : ℝ => E θ * C) volume (0 : ℝ) (2 * Real.pi) :=
    (hE_cont.mul continuous_const).intervalIntegrable _ _
  have hIBP1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (u := h) (u' := fun θ : ℝ => deriv h θ) (v := E) (v' := fun θ : ℝ => E θ * C)
    hd1 (fun x _ => hg_deriv x) hInt_f hInt_v'
  have hIBP2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (u := fun θ : ℝ => deriv h θ) (u' := fun θ : ℝ => deriv (deriv h) θ)
    (v := E) (v' := fun θ : ℝ => E θ * C)
    hd2 (fun x _ => hg_deriv x) hInt_f2 hInt_v'
  have hE2 : E (2 * Real.pi) = 1 := by
    dsimp only [E]
    rw [Complex.exp_eq_one_iff]
    exact ⟨-k, by push_cast; ring⟩
  have hE0 : E 0 = 1 := by
    dsimp only [E]
    simp
  have hb1 : h (2 * Real.pi) * E (2 * Real.pi) - h 0 * E 0 = 0 := by
    rw [hE2, hE0, mul_one, mul_one, sub_eq_zero]
    exact h₀.symm
  have hb2 : deriv h (2 * Real.pi) * E (2 * Real.pi) - deriv h 0 * E 0 = 0 := by
    rw [hE2, hE0, mul_one, mul_one, sub_eq_zero]
    exact h₁.symm
  have hA : (∫ θ in (0 : ℝ)..(2 * Real.pi), h θ * (E θ * C))
      = C * (∫ θ in (0 : ℝ)..(2 * Real.pi), h θ * E θ) := by
    have hfun : (fun θ : ℝ => h θ * (E θ * C)) = (fun θ : ℝ => C * (h θ * E θ)) := by
      funext θ; ring
    rw [hfun, intervalIntegral.integral_const_mul]
  have hB : (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv h θ * (E θ * C))
      = C * (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv h θ * E θ) := by
    have hfun : (fun θ : ℝ => deriv h θ * (E θ * C)) = (fun θ : ℝ => C * (deriv h θ * E θ)) := by
      funext θ; ring
    rw [hfun, intervalIntegral.integral_const_mul]
  have hstep1 : (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv h θ * E θ)
      = -(C * (∫ θ in (0 : ℝ)..(2 * Real.pi), h θ * E θ)) := by
    have hkey : (∫ θ in (0 : ℝ)..(2 * Real.pi), h θ * (E θ * C))
        = -(∫ θ in (0 : ℝ)..(2 * Real.pi), deriv h θ * E θ) := by
      rw [hIBP1, hb1, zero_sub]
    rw [hA] at hkey
    exact neg_eq_iff_eq_neg.mp hkey.symm
  have hstep2 : (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (deriv h) θ * E θ)
      = -(C * (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv h θ * E θ)) := by
    have hkey : (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv h θ * (E θ * C))
        = -(∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (deriv h) θ * E θ) := by
      rw [hIBP2, hb2, zero_sub]
    rw [hB] at hkey
    exact neg_eq_iff_eq_neg.mp hkey.symm
  have hC2 : C ^ 2 = -((((k : ℝ) : ℂ)) ^ 2) := by
    change (-(((k : ℝ) : ℂ) * Complex.I)) ^ 2 = -((((k : ℝ) : ℂ)) ^ 2)
    ring_nf
    rw [Complex.I_sq]
    ring
  have hfin : (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (deriv h) θ * E θ)
      = -((((k : ℝ) : ℂ)) ^ 2) * (∫ θ in (0 : ℝ)..(2 * Real.pi), h θ * E θ) := by
    rw [hstep2, hstep1]
    have hkey : -(C * -(C * (∫ θ in (0 : ℝ)..(2 * Real.pi), h θ * E θ)))
        = C ^ 2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), h θ * E θ) := by ring
    rw [hkey, hC2]
  exact hfin

end Work.Potential
