import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Bounds

open MulChar

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Commons.NumberTheory.Linnik

/-- For a Dirichlet character `χ` into `ℂ` and any `a`, `conj (χ a) = χ⁻¹ a`. -/
theorem star_apply_eq_inv {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a : ZMod n) :
    star (χ a) = χ⁻¹ a := by
  rw [MulChar.inv_apply]
  by_cases h : IsUnit a
  · have hnorm : ‖χ a‖ = 1 := by
      rw [← h.unit_spec]; exact DirichletCharacter.unit_norm_eq_one χ h.unit
    have hconj : star (χ a) = (χ a)⁻¹ := (Complex.inv_eq_conj hnorm).symm
    rw [hconj, ← h.unit_spec, Ring.inverse_unit]
    have hmul : χ (↑h.unit) * χ (↑(h.unit)⁻¹) = 1 := by
      rw [← map_mul, Units.mul_inv, MulChar.map_one]
    exact inv_eq_of_mul_eq_one_right hmul
  · have hzero : Ring.inverse a = 0 := dif_neg h
    rw [hzero, MulChar.map_nonunit χ h, star_zero]
    have h0 : ¬ IsUnit (0 : ZMod n) := by
      intro hunit
      have h01 : (0 : ZMod n) = 1 := isUnit_zero_iff.mp hunit
      refine h ?_
      have ha : a = 0 := by
        calc a = a * 1 := (mul_one a).symm
          _ = a * 0 := by rw [← h01]
          _ = 0 := mul_zero a
      rw [ha]; exact hunit
    exact (MulChar.map_nonunit χ h0).symm

/-- Split `(χ n / n^(β+w)).re` into the real factor `n^{-β}` and the shifted integrand. -/
theorem re_div_cpow_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 ≤ n)
    (β : ℝ) (w : ℂ) :
    (χ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + w)).re =
      (n : ℝ) ^ (-β) * (χ (n : ZMod q) * (n : ℂ) ^ (-w)).re := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hcn : (((n : ℝ) ^ (-β) : ℝ) : ℂ) = (n : ℂ) ^ (-(β : ℂ)) := by
    have h1 : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
    rw [h1, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hnpos.le (-β)]
  have hkey : (n : ℂ) ^ (-((β : ℂ) + w)) =
      (((n : ℝ) ^ (-β) : ℝ) : ℂ) * (n : ℂ) ^ (-w) := by
    have h2 : -((β : ℂ) + w) = (-(β : ℂ)) + (-w) := by ring
    rw [h2, Complex.cpow_add _ _ hnc, hcn]
  have hmain : χ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + w)
      = (((n : ℝ) ^ (-β) : ℝ) : ℂ) * (χ (n : ZMod q) * (n : ℂ) ^ (-w)) := by
    rw [div_eq_mul_inv, ← Complex.cpow_neg, hkey]; ring
  rw [hmain, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The elementary identity `ℜa₁ · ℜa₂ = ½ℜ(a₁a₂) + ½ℜ(a₁ā₂)`. -/
theorem mul_re_mul_re (a₁ a₂ : ℂ) :
    a₁.re * a₂.re = (1/2) * (a₁ * a₂).re + (1/2) * (a₁ * star a₂).re := by
  simp [Complex.mul_re, Complex.mul_im, star, Complex.conj_re, Complex.conj_im]
  ring

/-- `conj (n^{-iγ}) = n^{iγ}`. -/
theorem star_cpow_ofReal_neg {n : ℕ} (hn : 1 ≤ n) (γ : ℝ) :
    star ((n : ℂ) ^ (-((γ : ℂ) * Complex.I))) = (n : ℂ) ^ ((γ : ℂ) * Complex.I) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnorm : ‖(n : ℂ) ^ (-((γ : ℂ) * Complex.I))‖ = 1 := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simp
  have hconj : star ((n : ℂ) ^ (-((γ : ℂ) * Complex.I))) =
      (((n : ℂ) ^ (-((γ : ℂ) * Complex.I)))⁻¹) := (Complex.inv_eq_conj hnorm).symm
  rw [hconj, ← Complex.cpow_neg]
  congr 1
  ring

/-- **HB (6.3)/(6.4), pointwise.**  For `n ≥ 1` the five-term combination
`K`-summand is `Λ(n)·n^{-β}·(χ₀(n) + ℜ(χ₁(n)n^{-iγ₁}))(χ₀(n) + ℜ(χ₂(n)n^{-iγ₂}))·f(log n/L)`,
which is `≥ 0`. -/
theorem Ksum_pointwise {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) {L β γ₁ γ₂ : ℝ}
    (χ₁ χ₂ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
            * f (Real.log n / L)
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂⁻¹) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
            * f (Real.log n / L)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  set a₁ : ℂ := χ₁ (n : ZMod q) * (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) with ha₁
  set a₂ : ℂ := χ₂ (n : ZMod q) * (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I)) with ha₂
  set p : ℝ := ((1 : DirichletCharacter ℂ q) (n : ZMod q)).re with hp
  -- (1) the principal character takes only the values 0 and 1
  have hq01 : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 0 ∨
      ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 1 := by
    by_cases h : IsUnit (n : ZMod q)
    · right; rw [← h.unit_spec]; exact MulChar.one_apply h
    · left; exact MulChar.map_nonunit (1 : DirichletCharacter ℂ q) h
  have hp01 : p = 0 ∨ p = 1 := by
    rcases hq01 with h | h
    · left; rw [hp, h]; simp
    · right; rw [hp, h]; simp
  have hnu : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 0 → ¬ IsUnit (n : ZMod q) := by
    intro h hunit
    have h1 : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 1 := by
      rw [← hunit.unit_spec]; exact MulChar.one_apply hunit
    rw [h] at h1; exact zero_ne_one h1
  have hχ₁0 : p = 0 → a₁ = 0 := by
    intro h0
    have h0' : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 0 := by
      rcases hq01 with h | h
      · exact h
      · exfalso; rw [hp, h] at h0; norm_num at h0
    rw [ha₁, MulChar.map_nonunit χ₁ (hnu h0'), zero_mul]
  have hχ₂0 : p = 0 → a₂ = 0 := by
    intro h0
    have h0' : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 0 := by
      rcases hq01 with h | h
      · exact h
      · exfalso; rw [hp, h] at h0; norm_num at h0
    rw [ha₂, MulChar.map_nonunit χ₂ (hnu h0'), zero_mul]
  -- (2) rewriting the five summands
  have e1 : (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re
      = (n : ℝ) ^ (-β) * a₁.re := by
    rw [re_div_cpow_eq χ₁ hn β ((γ₁ : ℂ) * Complex.I), ha₁]
  have e2 : (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re
      = (n : ℝ) ^ (-β) * a₂.re := by
    rw [re_div_cpow_eq χ₂ hn β ((γ₂ : ℂ) * Complex.I), ha₂]
  have e0 : ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
      = (n : ℝ) ^ (-β) * p := by
    have h := re_div_cpow_eq (1 : DirichletCharacter ℂ q) hn β 0
    simp only [add_zero, neg_zero, Complex.cpow_zero, mul_one] at h
    rw [h, hp]
  have hsplit3 : (n : ℂ) ^ (-(((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I)) := by
    rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
  have hsplit4 : (n : ℂ) ^ (-(((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * (n : ℂ) ^ ((γ₂ : ℂ) * Complex.I) := by
    rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
  have hAA : (χ₁ * χ₂) (n : ZMod q) * (n : ℂ) ^ (-(((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I))
      = a₁ * a₂ := by
    rw [ha₁, ha₂, MulChar.mul_apply, hsplit3]; ring
  have hBB : (χ₁ * χ₂⁻¹) (n : ZMod q) * (n : ℂ) ^ (-(((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I))
      = a₁ * star a₂ := by
    rw [ha₁, ha₂, MulChar.mul_apply, star_mul, star_apply_eq_inv χ₂,
      star_cpow_ofReal_neg hn γ₂, hsplit4]
    ring
  have e3 : ((χ₁ * χ₂) (n : ZMod q) /
        (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * a₂).re := by
    rw [re_div_cpow_eq (χ₁ * χ₂) hn β (((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I), hAA]
  have e4 : ((χ₁ * χ₂⁻¹) (n : ZMod q) /
        (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * star a₂).re := by
    rw [re_div_cpow_eq (χ₁ * χ₂⁻¹) hn β (((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I), hBB]
  -- (3) the scalar identity
  have hpp : p * p = p := by rcases hp01 with h | h <;> rw [h] <;> norm_num
  have hp1 : p * a₁.re = a₁.re := by
    rcases hp01 with h | h
    · rw [h, zero_mul, hχ₁0 h]; simp
    · rw [h, one_mul]
  have hp2 : p * a₂.re = a₂.re := by
    rcases hp01 with h | h
    · rw [h, zero_mul, hχ₂0 h]; simp
    · rw [h, one_mul]
  have hp1b : a₁.re * p = a₁.re := by rw [mul_comm, hp1]
  have hp2b : a₂.re * p = a₂.re := by rw [mul_comm, hp2]
  have hid : (p + a₁.re) * (p + a₂.re)
      = p + a₁.re + a₂.re + (1/2) * (a₁ * a₂).re + (1/2) * (a₁ * star a₂).re := by
    have h4 := mul_re_mul_re a₁ a₂
    calc (p + a₁.re) * (p + a₂.re)
        = p * p + p * a₂.re + a₁.re * p + a₁.re * a₂.re := by ring
      _ = p + a₂.re + a₁.re + a₁.re * a₂.re := by rw [hpp, hp2, hp1b]
      _ = p + a₂.re + a₁.re + ((1/2) * (a₁ * a₂).re + (1/2) * (a₁ * star a₂).re) := by
            rw [← h4]
      _ = p + a₁.re + a₂.re + (1/2) * (a₁ * a₂).re + (1/2) * (a₁ * star a₂).re := by ring
  -- (4) non-negativity of each factor
  have hnorm₁ : ‖a₁‖ ≤ 1 := by
    rw [ha₁, norm_mul]
    refine mul_le_one₀ (DirichletCharacter.norm_le_one χ₁ _) (norm_nonneg _) ?_
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simp
  have hnorm₂ : ‖a₂‖ ≤ 1 := by
    rw [ha₂, norm_mul]
    refine mul_le_one₀ (DirichletCharacter.norm_le_one χ₂ _) (norm_nonneg _) ?_
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simp
  have hfac₁ : 0 ≤ p + a₁.re := by
    rcases hp01 with h | h
    · rw [h, hχ₁0 h]; simp
    · rw [h]
      have hle := Complex.abs_re_le_norm a₁
      rw [abs_le] at hle
      linarith [hle.1, hnorm₁]
  have hfac₂ : 0 ≤ p + a₂.re := by
    rcases hp01 with h | h
    · rw [h, hχ₂0 h]; simp
    · rw [h]
      have hle := Complex.abs_re_le_norm a₂
      rw [abs_le] at hle
      linarith [hle.1, hnorm₂]
  have hprod : 0 ≤ (p + a₁.re) * (p + a₂.re) := mul_nonneg hfac₁ hfac₂
  -- (5) assemble
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by positivity
  have hff : 0 ≤ f (Real.log n / L) := hf _
  have hnb : 0 ≤ (n : ℝ) ^ (-β) := Real.rpow_nonneg hnpos.le _
  have hmain : (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
            * f (Real.log n / L)
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂⁻¹) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      = (ArithmeticFunction.vonMangoldt n : ℝ) * f (Real.log n / L) * (n : ℝ) ^ (-β)
          * ((p + a₁.re) * (p + a₂.re)) := by
    rw [e1, e2, e0, e3, e4, hid]
    ring
  rw [hmain]
  exact mul_nonneg (mul_nonneg (mul_nonneg hΛ hff) hnb) hprod

end Commons.NumberTheory.Linnik

namespace Commons.NumberTheory.Linnik

/-- **HB (6.3)/(6.4).**  For a non-negative `f` supported in `[0,x₀]`,
`K(β,χ₀) + K(β+iγ₁,χ₁) + K(β+iγ₂,χ₂) + ½K(β+i(γ₁+γ₂),χ₁χ₂) + ½K(β+i(γ₁-γ₂),χ₁χ̄₂) ≥ 0`. -/
theorem Ksum_positivity {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t)
    {x₀ L β γ₁ γ₂ : ℝ} (hx₀ : 0 < x₀) (hL : 0 < L)
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) (χ₁ χ₂ : DirichletCharacter ℂ q) :
    0 ≤ (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re
            * f (Real.log n / L))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re
            * f (Real.log n / L))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
            * f (Real.log n / L))
      + (1/2) * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂⁻¹) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
            * f (Real.log n / L)) := by
  classical
  -- a bound beyond which every weight vanishes
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → x₀ ≤ Real.log n / L := by
    refine ⟨Nat.ceil (Real.exp (x₀ * L)) + 1, fun n hn => ?_⟩
    have h1 : Real.exp (x₀ * L) ≤ (n : ℝ) := by
      have : (Nat.ceil (Real.exp (x₀ * L)) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ _) hn)
      exact le_trans (Nat.le_ceil _) this
    have h2 : x₀ * L ≤ Real.log (n : ℝ) := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    rw [le_div_iff₀ hL]
    linarith
  have hvan : ∀ n : ℕ, N ≤ n → f (Real.log n / L) = 0 := fun n hn => hsupp _ (hN n hn)
  set s₁ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re * f (Real.log n / L)
    with hs₁
  set s₂ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re * f (Real.log n / L)
    with hs₂
  set s₀ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re * f (Real.log n / L)
    with hs₀
  set s₃ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₂) (n : ZMod q) /
        (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re * f (Real.log n / L)
    with hs₃
  set s₄ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₂⁻¹) (n : ZMod q) /
        (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re * f (Real.log n / L)
    with hs₄
  have hzero : ∀ n : ℕ, N ≤ n → s₁ n = 0 ∧ s₂ n = 0 ∧ s₀ n = 0 ∧ s₃ n = 0 ∧ s₄ n = 0 := by
    intro n hn
    have h := hvan n hn
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      · simp only [hs₁, hs₂, hs₀, hs₃, hs₄, h]
        ring
  have h1 : (∑' n : ℕ, s₁ n) = ∑ n ∈ Finset.range N, s₁ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).1)
  have h2 : (∑' n : ℕ, s₂ n) = ∑ n ∈ Finset.range N, s₂ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.1)
  have h0 : (∑' n : ℕ, s₀ n) = ∑ n ∈ Finset.range N, s₀ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.2.1)
  have h3 : (∑' n : ℕ, s₃ n) = ∑ n ∈ Finset.range N, s₃ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.2.2.1)
  have h4 : (∑' n : ℕ, s₄ n) = ∑ n ∈ Finset.range N, s₄ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.2.2.2)
  have hterm : ∀ n ∈ Finset.range N,
      0 ≤ s₁ n + s₂ n + s₀ n + (1/2) * s₃ n + (1/2) * s₄ n := by
    intro n hn
    rw [Finset.mem_range] at hn
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have h0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; exact not_isPrimePow_zero
      simp only [hs₁, hs₂, hs₀, hs₃, hs₄]
      rw [h0]
      norm_num
    · have := Ksum_pointwise (q := q) hf (L := L) (β := β) (γ₁ := γ₁) (γ₂ := γ₂) χ₁ χ₂ h
      simpa only [hs₁, hs₂, hs₀, hs₃, hs₄] using this
  have hcombine : ∑ n ∈ Finset.range N, (s₁ n + s₂ n + s₀ n + (1/2) * s₃ n + (1/2) * s₄ n)
      = (∑ n ∈ Finset.range N, s₁ n) + (∑ n ∈ Finset.range N, s₂ n)
        + (∑ n ∈ Finset.range N, s₀ n) + (1/2) * (∑ n ∈ Finset.range N, s₃ n)
        + (1/2) * (∑ n ∈ Finset.range N, s₄ n) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum : 0 ≤ ∑ n ∈ Finset.range N,
      (s₁ n + s₂ n + s₀ n + (1/2) * s₃ n + (1/2) * s₄ n) :=
    Finset.sum_nonneg hterm
  rw [h1, h2, h0, h3, h4]
  calc (0 : ℝ) ≤ ∑ n ∈ Finset.range N,
        (s₁ n + s₂ n + s₀ n + (1/2) * s₃ n + (1/2) * s₄ n) := hsum
    _ = _ := hcombine

end Commons.NumberTheory.Linnik