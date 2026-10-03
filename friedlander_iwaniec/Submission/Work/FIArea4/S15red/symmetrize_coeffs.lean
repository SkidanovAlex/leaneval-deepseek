import Mathlib

namespace Work.FIArea4.S15red

open scoped BigOperators Topology

noncomputable section

/-- **Symmetrisation of the coefficient family of the log-sine Fourier expansion.**
Given an absolutely summable family `c : ℤ → ℂ`, the Hermitian symmetrisation
`ℓ ↦ (c ℓ + conj(c(-ℓ)))/2` is again absolutely summable, its `ℓ¹`-norm is no larger than that
of `c`, and its Fourier transform (with the real frequency `α`) is the *real part* of the Fourier
transform of `c`.  This is the step which replaces the coefficients of the log-sine expansion by
real-valued coefficients: writing `d ℓ = (c ℓ + conj (c (-ℓ)))/2`, one has `d (-ℓ) = conj (d ℓ)`,
so `∑_ℓ d ℓ e^{iℓα} = (1/2)(F + conj F) = Re F` with `F = ∑_ℓ c ℓ e^{iℓα}`. -/
theorem symmetrize_coeffs {c : ℤ → ℂ} (hn : Summable (fun ℓ : ℤ => ‖c ℓ‖)) :
    Summable (fun ℓ : ℤ => (c ℓ + star (c (-ℓ))) / 2) ∧
    Summable (fun ℓ : ℤ => ‖(c ℓ + star (c (-ℓ))) / 2‖) ∧
    (∑' ℓ : ℤ, ‖(c ℓ + star (c (-ℓ))) / 2‖) ≤ ∑' ℓ : ℤ, ‖c ℓ‖ ∧
    (∀ α : ℝ,
      (∑' ℓ : ℤ, ((c ℓ + star (c (-ℓ))) / 2) * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ)))
        = (((∑' ℓ : ℤ, c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))).re : ℂ))) := by
  classical
  -- Summability of the reflected family `ℓ ↦ ‖c (-ℓ)‖`.
  have hnneg : Summable (fun ℓ : ℤ => ‖c (-ℓ)‖) :=
    (Equiv.summable_iff (Equiv.neg ℤ)).mpr hn
  -- The pointwise norm bound for the symmetrised coefficients.
  have hn_bound : ∀ ℓ : ℤ, ‖(c ℓ + star (c (-ℓ))) / 2‖ ≤ (‖c ℓ‖ + ‖c (-ℓ)‖) / 2 := by
    intro ℓ
    rw [norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (norm_add_le _ _).trans_eq (by rw [norm_star])
  have hGsum : Summable (fun ℓ : ℤ => (‖c ℓ‖ + ‖c (-ℓ)‖) / 2) := (hn.add hnneg).div_const 2
  have hnormd : Summable (fun ℓ : ℤ => ‖(c ℓ + star (c (-ℓ))) / 2‖) :=
    Summable.of_nonneg_of_le (fun ℓ => norm_nonneg _) hn_bound hGsum
  have hdsum : Summable (fun ℓ : ℤ => (c ℓ + star (c (-ℓ))) / 2) := Summable.of_norm hnormd
  -- The `ℓ¹` inequality.
  have hle : (∑' ℓ : ℤ, ‖(c ℓ + star (c (-ℓ))) / 2‖) ≤ ∑' ℓ : ℤ, ‖c ℓ‖ := by
    have h1 : (∑' ℓ : ℤ, ‖(c ℓ + star (c (-ℓ))) / 2‖) ≤ ∑' ℓ : ℤ, (‖c ℓ‖ + ‖c (-ℓ)‖) / 2 :=
      hnormd.tsum_le_tsum hn_bound hGsum
    have hneg : (∑' ℓ : ℤ, ‖c (-ℓ)‖) = ∑' ℓ : ℤ, ‖c ℓ‖ := by
      simpa using (Equiv.tsum_eq (Equiv.neg ℤ) (fun ℓ : ℤ => ‖c ℓ‖))
    have hsplit : (∑' ℓ : ℤ, (‖c ℓ‖ + ‖c (-ℓ)‖) / 2) = ∑' ℓ : ℤ, ‖c ℓ‖ := by
      have h2 : (∑' ℓ : ℤ, (‖c ℓ‖ + ‖c (-ℓ)‖) / 2)
          = (1/2) * (∑' ℓ : ℤ, (‖c ℓ‖ + ‖c (-ℓ)‖)) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro ℓ
        ring
      rw [h2, hn.tsum_add hnneg, hneg]
      ring
    exact h1.trans (le_of_eq hsplit)
  refine ⟨hdsum, hnormd, hle, ?_⟩
  -- The Fourier transform identity.
  intro α
  -- `‖e^{i ℓ α}‖ = 1`.
  have he : ∀ ℓ : ℤ, ‖Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))‖ = 1 := by
    intro ℓ
    rw [Complex.norm_exp]
    have hre : (Complex.I * (ℓ : ℂ) * (α : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  -- `conj (e^{-i ℓ α}) = e^{i ℓ α}`.
  have hstare : ∀ ℓ : ℤ,
      star (Complex.exp (Complex.I * ((-ℓ : ℤ) : ℂ) * (α : ℂ)))
        = Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ)) := by
    intro ℓ
    rw [show star (Complex.exp (Complex.I * ((-ℓ : ℤ) : ℂ) * (α : ℂ)))
        = Complex.exp (star (Complex.I * ((-ℓ : ℤ) : ℂ) * (α : ℂ))) from (Complex.exp_conj _).symm]
    congr 1
    simp [Complex.conj_ofReal]
  -- Absolute summability of the twisted family `A ℓ = c ℓ * e^{i ℓ α}`.
  have hA_summ : Summable (fun ℓ : ℤ => c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))) := by
    apply Summable.of_norm
    have h : (fun ℓ : ℤ => ‖c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))‖)
        = (fun ℓ : ℤ => ‖c ℓ‖) := by
      funext ℓ; rw [norm_mul, he ℓ, mul_one]
    rw [h]; exact hn
  have hA_has : HasSum (fun ℓ : ℤ => c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ)))
      (∑' ℓ : ℤ, c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))) := hA_summ.hasSum
  -- The reflected-twisted family sums to `conj` of the twisted sum: reindex `ℓ ↦ -ℓ` and use
  -- `conj (e^{-i ℓ α}) = e^{i ℓ α}`.
  have hB'_has : HasSum
      (fun ℓ : ℤ => star (c (-ℓ) * Complex.exp (Complex.I * ((-ℓ : ℤ) : ℂ) * (α : ℂ))))
      (star (∑' ℓ : ℤ, c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ)))) :=
    (Equiv.hasSum_iff (Equiv.neg ℤ)).mpr hA_has.star
  have hB_has : HasSum (fun ℓ : ℤ => star (c (-ℓ)) * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ)))
      (star (∑' ℓ : ℤ, c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ)))) :=
    hB'_has.congr_fun (fun ℓ => by rw [star_mul, hstare ℓ, mul_comm])
  have hAB_has : HasSum
      (fun ℓ : ℤ => (c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))
        + star (c (-ℓ)) * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))) / 2)
      (((∑' ℓ : ℤ, c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ)))
        + star (∑' ℓ : ℤ, c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ)))) / 2) :=
    (hA_has.add hB_has).div_const 2
  have hmain : (∑' ℓ : ℤ, ((c ℓ + star (c (-ℓ))) / 2) * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ)))
      = (((∑' ℓ : ℤ, c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))).re : ℂ)) := by
    rw [show (∑' ℓ : ℤ, ((c ℓ + star (c (-ℓ))) / 2) * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ)))
        = (∑' ℓ : ℤ, (c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))
            + star (c (-ℓ)) * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))) / 2) by
      apply tsum_congr; intro ℓ; ring]
    rw [hAB_has.tsum_eq]
    apply Complex.ext <;> simp [Complex.add_re]
  exact hmain

end

end Work.FIArea4.S15red
