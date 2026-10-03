import Mathlib
import Submission.Work.FIArea2.CCountPoissonDefs
import Submission.Work.FIArea2.poisson_coset_2d

namespace Work.FIArea2

/-- **Absolute convergence of the coset Fourier sum of §6.**

For `Ψ : ℝ² → ℂ` of class `C³` with compact support, `m ≥ 1` and `γ ∈ ℤ²`, the family

  `h ↦ ft2coset Ψ m γ h = ∫_{ℝ²} Ψ(t) e(−h·(t−γ)/m) dt`

is summable over the lattice `ℤ²`.  This is the convergence that underlies the coset Poisson
summation `poisson_coset_2d`.

The argument is the change of variables `t = γ + m x` of `ft2_comp_affine`,

  `ft2coset Ψ m γ h = m² · ft2 (x ↦ Ψ(γ + m x)) h`,

together with the decay `summable_ft2` of the two-dimensional Fourier transform of a `C³`
compactly supported function: `x ↦ Ψ(γ + m x)` is again `C³` with compact support (it is the
composition of `Ψ` with the affine homeomorphism `x ↦ γ + m x` of `ℝ²`). -/
theorem summable_ft2coset (Ψ : ℝ × ℝ → ℂ) (hΨ : ContDiff ℝ 3 Ψ) (hcs : HasCompactSupport Ψ)
    (m : ℕ) (hm : 1 ≤ m) (γ : ℤ × ℤ) :
    Summable (fun h : ℤ × ℤ => Work.FIArea2.ft2coset Ψ m γ h) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  obtain ⟨e, he⟩ := exists_homeomorph_cosetPtR m hm γ
  have hcd : ContDiff ℝ 3 (fun x : ℝ × ℝ => Ψ (cosetPtR m γ x)) := by
    refine hΨ.comp ?_
    unfold cosetPtR
    fun_prop
  have hcs' : HasCompactSupport (fun x : ℝ × ℝ => Ψ (cosetPtR m γ x)) := by
    simpa only [he, Function.comp_def] using hcs.comp_homeomorph e
  have hsum := summable_ft2 (fun x : ℝ × ℝ => Ψ (cosetPtR m γ x)) hcd hcs'
  refine (hsum.mul_left (((m : ℝ) ^ 2) : ℂ)).congr (fun h => ?_)
  rw [ft2_comp_affine Ψ m hm γ h]
  rw [← mul_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (by positivity : ((m : ℝ) ^ 2) ≠ 0), Complex.ofReal_one, one_mul]

end Work.FIArea2
