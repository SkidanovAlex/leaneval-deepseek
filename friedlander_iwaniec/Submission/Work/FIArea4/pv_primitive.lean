import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.gaussSum_norm_sq_of_isPrimitive
import Submission.Commons.NumberTheory.DirichletCharacter.isPrimitive_inv
import Submission.Work.FIArea4.pv_exp_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

/-- **Pólya–Vinogradov for a primitive Dirichlet character** (Friedlander–Iwaniec (22.5)).
Proof plan: write `χ (n : ZMod q) = 𝓕⁻ (𝓕 χ) (n)` (`ZMod.dft`, `ZMod.invDFT_apply`,
`LinearEquiv.symm_apply_apply`), use
`DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum` to get
`𝓕 χ k = χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar`, and
`Commons.NumberTheory.DirichletCharacter.gaussSum_norm_sq_of_isPrimitive`
(`Submission/Commons/NumberTheory/DirichletCharacter/gaussSum_norm_sq_of_isPrimitive.lean`,
`‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = q`) for the size of the Gauss sum. Then `‖χ⁻¹ (-k)‖` is `0`
for `k = 0` (`2 ≤ q` makes `0` a non-unit, `MulChar.map_nonunit`) and at most `1` otherwise
(from `hbd`), and the exponential sums `∑_{n=1}^{X} stdAddChar (k * n)` are bounded by
`∑_{k ≠ 0} ‖∑_{n=1}^{X} stdAddChar (k * n)‖ ≤ q * (2 + Real.log q)` (prove this here as a helper
lemma, by the geometric series and the harmonic bound). This gives `√q * (2 + log q) ≤
4 * √q * (log q + 1)`. -/
theorem pv_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hpr : χ.IsPrimitive) (hq : 2 ≤ q) (hbd : ∀ a : ZMod q, ‖χ a‖ ≤ 1) (X : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 X, χ (n : ZMod q)‖ ≤ 4 * Real.sqrt q * (Real.log q + 1) := by
  classical
  -- `ZMod q` is nontrivial, so `χ 0 = 0`.
  have hnontriv : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
  -- Work with `χ⁻¹`, whose Fourier transform is `χ (-k) * τ` and whose partial sums have the
  -- same norm as those of `χ` (`χ⁻¹ = star ∘ χ`).
  have hpr' : (χ⁻¹).IsPrimitive :=
    Commons.NumberTheory.DirichletCharacter.isPrimitive_inv hpr
  set τ : ℂ := gaussSum χ⁻¹ (ZMod.stdAddChar (N := q)) with hτdef
  set T : ZMod q → ℂ :=
    fun k => ∑ n ∈ Finset.Icc 1 X, ZMod.stdAddChar (k * (n : ZMod q)) with hTdef
  -- The Gauss sum has modulus `√q` (`‖τ‖ ^ 2 = q`).
  have hτ2 : ‖τ‖ ^ 2 = (q : ℝ) := by
    rw [hτdef]
    exact Commons.NumberTheory.DirichletCharacter.gaussSum_norm_sq_of_isPrimitive χ⁻¹ hpr'
  have hτnorm : ‖τ‖ = Real.sqrt q := by
    rw [← hτ2, Real.sqrt_sq (norm_nonneg τ)]
  -- Fourier transform of a primitive character.
  have hdft : ∀ k : ZMod q, ZMod.dft (⇑χ⁻¹) k = χ (-k) * τ := by
    intro k
    rw [DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hpr', inv_inv,
      hτdef]
  -- Fourier inversion, pointwise.
  have hpoint : ∀ n : ZMod q,
      χ⁻¹ n = (q : ℂ)⁻¹ * ∑ k : ZMod q, ZMod.stdAddChar (k * n) * (χ (-k) * τ) := by
    intro n
    have hinv : ZMod.dft.symm (ZMod.dft (⇑χ⁻¹)) = ⇑χ⁻¹ :=
      LinearEquiv.symm_apply_apply (ZMod.dft (N := q) (E := ℂ)) _
    rw [← congr_fun hinv n, ZMod.invDFT_apply]
    simp only [smul_eq_mul, hdft]
  have hχ0 : χ (0 : ZMod q) = 0 := MulChar.map_zero χ
  -- Summing the inversion formula over `n ≤ X` and exchanging the two sums.
  have hsum1 : ∑ n ∈ Finset.Icc 1 X, χ⁻¹ (n : ZMod q)
      = (q : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 X, ∑ k : ZMod q,
          ZMod.stdAddChar (k * (n : ZMod q)) * (χ (-k) * τ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => hpoint (n : ZMod q)
  have hsum2 : ∑ n ∈ Finset.Icc 1 X, ∑ k : ZMod q,
        ZMod.stdAddChar (k * (n : ZMod q)) * (χ (-k) * τ)
      = ∑ k : ZMod q, T k * (χ (-k) * τ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, hTdef]
  have hsum : ∑ n ∈ Finset.Icc 1 X, χ⁻¹ (n : ZMod q)
      = (q : ℂ)⁻¹ * ∑ k : ZMod q, T k * (χ (-k) * τ) := by
    rw [hsum1, hsum2]
  -- The exponential sums, summed over the non-trivial characters.
  have hexp' : ∑ j ∈ Finset.univ.filter (fun j : ZMod q => j ≠ 0), ‖T j‖
      ≤ (q : ℝ) * (2 + Real.log q) := by
    simpa only [hTdef] using pv_exp_sum hq X
  -- `‖χ (-k)‖ ≤ 1` (and the `k = 0` term vanishes).
  have hfilter : ∑ k ∈ Finset.univ.filter (fun k : ZMod q => k ≠ 0), ‖T k‖ * ‖χ (-k)‖
      = ∑ k : ZMod q, ‖T k‖ * ‖χ (-k)‖ := by
    refine Finset.sum_filter_of_ne ?_
    intro x _ hx hx0
    exact hx (by rw [hx0]; simp [hχ0])
  have hkey : ∑ k : ZMod q, ‖T k‖ * ‖χ (-k)‖
      ≤ ∑ j ∈ Finset.univ.filter (fun j : ZMod q => j ≠ 0), ‖T j‖ := by
    rw [← hfilter]
    refine Finset.sum_le_sum fun k _ => ?_
    calc ‖T k‖ * ‖χ (-k)‖ ≤ ‖T k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hbd (-k)) (norm_nonneg _)
      _ = ‖T k‖ := mul_one _
  have hA : ‖∑ k : ZMod q, T k * (χ (-k) * τ)‖
      ≤ ‖τ‖ * ((q : ℝ) * (2 + Real.log q)) := by
    calc ‖∑ k : ZMod q, T k * (χ (-k) * τ)‖
        ≤ ∑ k : ZMod q, ‖T k * (χ (-k) * τ)‖ := norm_sum_le _ _
      _ = ∑ k : ZMod q, ‖T k‖ * ‖χ (-k)‖ * ‖τ‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_mul]
          ring
      _ = ‖τ‖ * ∑ k : ZMod q, ‖T k‖ * ‖χ (-k)‖ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ ‖τ‖ * ((q : ℝ) * (2 + Real.log q)) :=
          mul_le_mul_of_nonneg_left (le_trans hkey hexp') (norm_nonneg τ)
  -- `∑ χ⁻¹ = star (∑ χ)`, so the two sums have the same norm.
  have hstar : ∑ n ∈ Finset.Icc 1 X, χ⁻¹ (n : ZMod q)
      = star (∑ n ∈ Finset.Icc 1 X, χ (n : ZMod q)) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun n _ => (MulChar.star_apply' χ (n : ZMod q)).symm
  calc ‖∑ n ∈ Finset.Icc 1 X, χ (n : ZMod q)‖
      = ‖∑ n ∈ Finset.Icc 1 X, χ⁻¹ (n : ZMod q)‖ := by rw [hstar, norm_star]
    _ = ‖(q : ℂ)⁻¹ * ∑ k : ZMod q, T k * (χ (-k) * τ)‖ := by rw [hsum]
    _ ≤ (q : ℝ)⁻¹ * (‖τ‖ * ((q : ℝ) * (2 + Real.log q))) := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left hA (by positivity)
    _ = Real.sqrt q * (2 + Real.log q) := by
        rw [hτnorm]
        field_simp
    _ ≤ 4 * Real.sqrt q * (Real.log q + 1) := by
        have hlog : 0 ≤ Real.log q :=
          Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
        have h2 : (2 : ℝ) + Real.log q ≤ 4 * (Real.log q + 1) := by linarith
        calc Real.sqrt q * (2 + Real.log q) ≤ Real.sqrt q * (4 * (Real.log q + 1)) :=
              mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg q)
          _ = 4 * Real.sqrt q * (Real.log q + 1) := by ring

end Work.FIArea4
