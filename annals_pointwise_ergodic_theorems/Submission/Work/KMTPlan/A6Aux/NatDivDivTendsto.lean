import Mathlib

namespace Work.KMTPlan.A6Aux

/-- For `0 < Q` the natural-number quotient `m / Q` differs from the real quotient
`m / Q` by at most `1`. -/
private lemma abs_cast_div_sub_div_le_one (m Q : ℕ) (hQ : 0 < Q) :
    |((m / Q : ℕ) : ℝ) - (m : ℝ) / (Q : ℝ)| ≤ 1 := by
  have hq : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ
  have h1 : (((m / Q : ℕ)) : ℝ) * (Q:ℝ) ≤ (m:ℝ) := by
    have := Nat.div_mul_le_self m Q
    exact_mod_cast this
  have h2 : (m:ℝ) < (((m / Q : ℕ) : ℝ) + 1) * (Q:ℝ) := by
    have h := Nat.lt_mul_div_succ m hQ
    have h' : (m:ℝ) < ((Q * (m / Q + 1) : ℕ) : ℝ) := by exact_mod_cast h
    have h'' : ((Q * (m / Q + 1) : ℕ) : ℝ) = (((m/Q:ℕ):ℝ) + 1) * (Q:ℝ) := by push_cast; ring
    linarith [h', h'']
  have hle : ((m / Q : ℕ) : ℝ) ≤ (m:ℝ)/(Q:ℝ) := (le_div_iff₀ hq).mpr h1
  have hlt : (m:ℝ)/(Q:ℝ) < ((m/Q:ℕ):ℝ) + 1 := (div_lt_iff₀ hq).mpr h2
  rw [abs_le]
  constructor <;> linarith

/-- `N - N / 2` is the "ceiling half" of `N`, off from `N / 2` by at most `1 / 2`. -/
private lemma abs_cast_half_sub (N : ℕ) :
    |((N - N / 2 : ℕ) : ℝ) - (N:ℝ)/2| ≤ 1/2 := by
  have h1 : N ≤ 2 * (N - N/2) := by omega
  have h2 : 2 * (N - N/2) ≤ N + 1 := by omega
  have h1' : (N:ℝ) ≤ 2 * ((N - N/2 : ℕ):ℝ) := by exact_mod_cast h1
  have h2' : 2 * ((N - N/2 : ℕ):ℝ) ≤ (N:ℝ) + 1 := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

theorem NatDivDivTendsto (Q : ℕ) (hQ : 1 ≤ Q) :
    Filter.Tendsto (fun N : ℕ => (((N - N / 2) / Q : ℕ) : ℂ) * (N : ℂ)⁻¹) Filter.atTop
      (nhds ((2 : ℂ)⁻¹ * (Q : ℂ)⁻¹)) := by
  have hQposR : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ
  have hQge1R : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hbound : ∀ N : ℕ, 1 ≤ N →
      |(((N - N / 2) / Q : ℕ) : ℝ) * (N : ℝ)⁻¹ - ((2:ℝ) * (Q:ℝ))⁻¹| ≤ (3/2) * (N:ℝ)⁻¹ := by
    intro N hN
    have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have hA : |(((N - N/2) / Q : ℕ) : ℝ) - ((N - N/2 : ℕ) : ℝ) / (Q:ℝ)| ≤ 1 :=
      abs_cast_div_sub_div_le_one (N - N/2) Q (by omega)
    have hB : |((N - N/2 : ℕ) : ℝ) - (N:ℝ)/2| ≤ 1/2 := abs_cast_half_sub N
    have h3 : |(((N - N/2 : ℕ):ℝ) - (N:ℝ)/2)/(Q:ℝ)| ≤ 1/2 := by
      rw [abs_div, abs_of_pos hQposR]
      have h4 : |((N - N/2 : ℕ):ℝ) - (N:ℝ)/2| / (Q:ℝ) ≤ (1/2)/(Q:ℝ) :=
        div_le_div_of_nonneg_right hB hQposR.le
      have h5 : (1/2)/(Q:ℝ) ≤ 1/2 := by rw [div_le_iff₀ hQposR]; linarith
      linarith
    have hmain : |(((N - N/2)/Q : ℕ) : ℝ) - (N:ℝ)/((2:ℝ)*(Q:ℝ))| ≤ 3/2 := by
      have hs : |(((N - N/2)/Q : ℕ) : ℝ) - (N:ℝ)/((2:ℝ)*(Q:ℝ))|
          ≤ |(((N - N/2)/Q : ℕ) : ℝ) - ((N - N/2 : ℕ):ℝ)/(Q:ℝ)|
            + |(((N - N/2 : ℕ):ℝ) - (N:ℝ)/2)/(Q:ℝ)| := by
        have hkey : (((N - N/2)/Q : ℕ) : ℝ) - (N:ℝ)/((2:ℝ)*(Q:ℝ))
            = ((((N - N/2)/Q : ℕ) : ℝ) - ((N - N/2 : ℕ):ℝ)/(Q:ℝ))
              + (((N - N/2 : ℕ):ℝ) - (N:ℝ)/2)/(Q:ℝ) := by
          field_simp
          ring
        rw [hkey]; exact abs_add_le _ _
      linarith [hA, h3, hs]
    have heq : (((N - N / 2) / Q : ℕ) : ℝ) * (N : ℝ)⁻¹ - ((2:ℝ) * (Q:ℝ))⁻¹
        = ((((N - N/2)/Q : ℕ) : ℝ) - (N:ℝ)/((2:ℝ)*(Q:ℝ))) * (N:ℝ)⁻¹ := by
      field_simp
    rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hNR)]
    exact mul_le_mul_of_nonneg_right hmain (le_of_lt (inv_pos.mpr hNR))
  have hlim : Filter.Tendsto (fun N : ℕ => (3/2:ℝ) * (N:ℝ)⁻¹) Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := (3/2:ℝ)) (f := Filter.atTop)).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [div_eq_mul_inv] using h
  have hreal : Filter.Tendsto (fun N : ℕ => (((N - N / 2) / Q : ℕ) : ℝ) * (N : ℝ)⁻¹) Filter.atTop
      (nhds ((2:ℝ) * (Q:ℝ))⁻¹) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun N : ℕ => ((2:ℝ) * (Q:ℝ))⁻¹ - (3/2) * (N:ℝ)⁻¹)
      (h := fun N : ℕ => ((2:ℝ) * (Q:ℝ))⁻¹ + (3/2) * (N:ℝ)⁻¹) ?_ ?_ ?_ ?_
    · have h := (tendsto_const_nhds (x := ((2:ℝ) * (Q:ℝ))⁻¹) (f := Filter.atTop)).sub hlim
      simpa using h
    · have h := (tendsto_const_nhds (x := ((2:ℝ) * (Q:ℝ))⁻¹) (f := Filter.atTop)).add hlim
      simpa using h
    · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have := hbound N hN
      linarith [(abs_le.mp this).1]
    · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have := hbound N hN
      linarith [(abs_le.mp this).2]
  have hcompl : Filter.Tendsto
      (Complex.ofReal ∘ (fun N : ℕ => (((N - N / 2) / Q : ℕ) : ℝ) * (N : ℝ)⁻¹)) Filter.atTop
      (nhds (Complex.ofReal ((2:ℝ) * (Q:ℝ))⁻¹)) :=
    (Complex.continuous_ofReal.tendsto ((2:ℝ) * (Q:ℝ))⁻¹).comp hreal
  have hfun : (fun N : ℕ => (((N - N / 2) / Q : ℕ) : ℂ) * (N : ℂ)⁻¹)
      = Complex.ofReal ∘ (fun N : ℕ => (((N - N / 2) / Q : ℕ) : ℝ) * (N : ℝ)⁻¹) := by
    funext N
    have h1 : (((N - N / 2) / Q : ℕ) : ℂ) = Complex.ofReal (((N - N/2)/Q : ℕ) : ℝ) :=
      (Complex.ofReal_natCast _).symm
    have h2 : (N : ℂ) = Complex.ofReal (N : ℝ) := (Complex.ofReal_natCast N).symm
    rw [Function.comp_apply, h1, h2, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  have hcC : Complex.ofReal ((2:ℝ) * (Q:ℝ))⁻¹ = (2:ℂ)⁻¹ * (Q:ℂ)⁻¹ := by
    rw [Complex.ofReal_inv, Complex.ofReal_mul, mul_inv, Complex.ofReal_ofNat,
      Complex.ofReal_natCast]
  rw [hfun, ← hcC]
  exact hcompl

end Work.KMTPlan.A6Aux
