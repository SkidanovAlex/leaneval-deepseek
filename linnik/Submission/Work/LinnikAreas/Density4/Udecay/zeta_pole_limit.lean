import Mathlib

namespace Work.LinnikAreas.Density4.Udecay

/-- Near the pole `s = 1`, `ζ` behaves like `1 / (s - 1)` with residue one, so
`(1/ζ(1+s)) / s → 1` as `s → 0⁺`. Taking real parts (which is legitimate since `s` is a
real variable, so `(1/ζ(1+s))/s` is a product of a real number and a complex number) gives
the stated real limit. -/
theorem zeta_pole_limit :
    Filter.Tendsto (fun s : ℝ => (1 / s) * ((riemannZeta ((1 + s : ℝ) : ℂ))⁻¹).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  -- `(1 + s : ℂ)` tends to `1` along the punctured neighbourhood `{1}ᶜ`.
  have hz : Filter.Tendsto (fun s : ℝ => ((1 + s : ℝ) : ℂ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (1 : ℂ) {1}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Continuous fun s : ℝ => ((1 + s : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp (continuous_const.add continuous_id)
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have h' : (1 + s : ℝ) = 1 := Complex.ofReal_inj.mp h
      have hs' : (0 : ℝ) < s := hs
      linarith
  -- Mathlib's residue-one statement, precomposed with `s ↦ 1 + s`.
  have hres : Filter.Tendsto
      (fun s : ℝ => (((1 + s : ℝ) : ℂ) - 1) * riemannZeta (((1 + s : ℝ) : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    riemannZeta_residue_one.comp hz
  -- Inverting, using that the limit `1` is nonzero.
  have hinv : Filter.Tendsto
      (fun s : ℝ => ((((1 + s : ℝ) : ℂ) - 1) * riemannZeta (((1 + s : ℝ) : ℂ)))⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using hres.inv₀ (one_ne_zero)
  -- Rewrite the inverted function in the form `(ζ (1+s))⁻¹ / s`.
  have heq : ∀ s : ℝ,
      ((((1 + s : ℝ) : ℂ) - 1) * riemannZeta (((1 + s : ℝ) : ℂ)))⁻¹
        = (riemannZeta ((1 + s : ℝ) : ℂ))⁻¹ / ((s : ℝ) : ℂ) := by
    intro s
    have h1 : ((1 + s : ℝ) : ℂ) - 1 = ((s : ℝ) : ℂ) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
      norm_num
    rw [h1, mul_inv, div_eq_mul_inv, mul_comm]
  have htendC : Filter.Tendsto
      (fun s : ℝ => (riemannZeta ((1 + s : ℝ) : ℂ))⁻¹ / ((s : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    hinv.congr' (Filter.Eventually.of_forall heq)
  -- Take real parts.
  have hre : Filter.Tendsto
      (fun s : ℝ => Complex.re ((riemannZeta ((1 + s : ℝ) : ℂ))⁻¹ / ((s : ℝ) : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp htendC
  -- Identify the real part with the expression in the statement.
  refine hre.congr' ?_
  filter_upwards with s
  rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.re_mul_ofReal, one_div]
  ring

end Work.LinnikAreas.Density4.Udecay
