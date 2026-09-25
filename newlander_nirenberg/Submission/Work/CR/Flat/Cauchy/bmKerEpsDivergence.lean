import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmKerEpsAux
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul
import Submission.Work.CR.Flat.Polydisc.dbarCoord_apply_conj_coord
import Submission.Work.CR.Flat.Polydisc.dbarCoord_add

namespace Work.CR.Flat.Cauchy

/-- **The divergence of the regularised Bochner–Martinelli kernel.**
For `ε > 0` and every `z : ℂⁿ`,
`Σ_k ∂̄_k (x ↦ \bar x_k / (nrmSq x + ε²)^n)(z) = n ε² / (nrmSq z + ε²)^{n+1}`,
where `nrmSq x = Σ_j ‖x_j‖²` and `∂̄_k = dbarCoord k` is the flat `∂̄`-operator of
`Submission.Work.CR.Flat.Polydisc`.  This is the pointwise identity behind the regularised
Bochner–Martinelli formula, obtained by integrating by parts.

Suggested route. Write `bmKerEps k ε x = star (x k) * F x` where `F x = (nrmSq x + ε²)^{-n}`
(`div_eq_mul_inv`); by the Leibniz rule `dbarCoord_mul` the sum splits as
`Σ_k ∂̄_k (star (x k)) z * F z + Σ_k star (z k) * ∂̄_k F z`; `dbarCoord_apply_conj_coord` gives
`∂̄_k (star (x k)) z = 1`, so the first sum is `n * F z`.  The second needs the radial chain rule:
for `Φ : ℝ → ℝ` differentiable at `nrmSq z`,
`∂̄_k (x ↦ (Φ (nrmSq x) : ℂ)) z = (Φ' (nrmSq z) : ℂ) * z k`, whose proof uses only that the real
Fréchet derivative of `nrmSq` in the two complex directions `Pi.single k 1` and
`Pi.single k Complex.I` is `2 * (z k).re` resp. `2 * (z k).im` (e.g. from `fderiv_norm_sq_apply`
applied to `ℂ`, or from `‖y‖^2 = Complex.normSq y = y.re * y.re + y.im * y.im` and
`Complex.reCLM`/`Complex.imCLM`), so that `∂̄_k (nrmSq as a ℂ-valued function) z = z k`; with
`Φ t = (t + ε²)^{-n}`, so that `Φ' t = -n (t + ε²)^{-n-1}`, the second sum becomes
`-n * nrmSq z * F z / (nrmSq z + ε²)`.  The final algebra is
`n (r + ε²)^{-n} - n r (r + ε²)^{-n-1} = n ε² (r + ε²)^{-n-1}` with `r = nrmSq z`. -/
theorem bmKerEpsDivergence {n : ℕ} {ε : ℝ} (hε : 0 < ε) (z : Fin n → ℂ) :
    ∑ k, dbarCoord k (bmKerEps k ε) z
      = (n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq z + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1) := by
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hCpos : (0 : ℝ) < nrmSq z + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (nrmSq_nonneg z) hε2
  -- The derivative of the radial weight `t ↦ (t + ε²)^{-n}` at `nrmSq z`.
  have h1m : HasDerivAt (fun t : ℝ => t + ε ^ 2) 1 (nrmSq z) := by
    simpa using (hasDerivAt_id (nrmSq z)).add_const (ε ^ 2)
  have hΦ' := (hasDerivAt_zpow (-(n : ℤ)) (nrmSq z + ε ^ 2) (Or.inl hCpos.ne')).comp
    (nrmSq z) h1m
  -- The `∂̄_k`-derivative of the radial weight via the radial chain rule.
  have hrad : ∀ k : Fin n,
      dbarCoord k (fun x : Fin n → ℂ => (((nrmSq x + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ)) z
        = ((((-(n : ℤ) : ℝ)) * (nrmSq z + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ) : ℂ) * z k := by
    intro k
    simpa only [Function.comp_apply, mul_one, Int.cast_neg, Int.cast_natCast]
      using dbarCoord_comp_nrmSq (z := z) k hΦ'
  -- The per-coordinate expansion of the divergence.
  have hterm : ∀ k : Fin n, dbarCoord k (bmKerEps k ε) z
      = (((nrmSq z + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ)
        + star (z k) * (((((-(n : ℤ) : ℝ)) * (nrmSq z + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ) : ℂ) * z k) := by
    intro k
    have hu : DifferentiableAt ℝ (fun x : Fin n → ℂ => star (x k)) z := by
      refine (Complex.conjCLE.differentiableAt.comp z
        ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt).congr_of_eventuallyEq ?_
      filter_upwards with x
      simp
    have hinner : DifferentiableAt ℝ (fun x : Fin n → ℂ => (nrmSq x + ε ^ 2) ^ (-(n : ℤ))) z := by
      refine (((differentiableAt_zpow (m := -(n : ℤ)) (x := nrmSq z + ε ^ 2)).mpr
        (Or.inl hCpos.ne')).comp z ((differentiableAt_nrmSq z).add_const (ε ^ 2))).congr_of_eventuallyEq ?_
      filter_upwards with x
      simp
    have hv : DifferentiableAt ℝ
        (fun x : Fin n → ℂ => (((nrmSq x + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ)) z := by
      refine (Complex.ofRealCLM.differentiableAt.comp z hinner).congr_of_eventuallyEq ?_
      filter_upwards with x
      simp [Function.comp_apply, Complex.ofRealCLM_apply]
    have hfun : bmKerEps k ε = fun x : Fin n → ℂ =>
        star (x k) * ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ)) := by
      funext x
      exact bmKerEps_eq_zpow k ε x
    rw [hfun,
      Work.CR.Flat.Polydisc.dbarCoord_mul k (fun x : Fin n → ℂ => star (x k))
        (fun x : Fin n → ℂ => (((nrmSq x + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ)) z hu hv,
      Work.CR.Flat.Polydisc.dbarCoord_apply_conj_coord k k z, ite_eq_left rfl, one_mul, hrad k]
  -- Sum over the coordinates.
  have hsum : ∑ k, dbarCoord k (bmKerEps k ε) z
      = (n : ℂ) * (((nrmSq z + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ)
        + (((((-(n : ℤ) : ℝ)) * (nrmSq z + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ) : ℂ)
            * ((nrmSq z : ℝ) : ℂ)) := by
    simp only [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hfac : ∀ H : ℂ, (∑ k : Fin n, star (z k) * (H * z k))
        = H * (∑ k, star (z k) * z k) := by
      intro H
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hfac, sum_conj_mul_self]
  rw [hsum]
  -- Turn the `zpow`-of-`ofReal` occurrences into `ofReal`-of-`zpow`.
  have hA : ((((nrmSq z + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ))
      = (((nrmSq z + ε ^ 2 : ℝ)) : ℂ) ^ (-(n : ℤ)) := Complex.ofReal_zpow _ _
  have hD : (((((-(n : ℤ) : ℝ)) * (nrmSq z + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ) : ℂ))
      = ((-(n : ℤ) : ℂ)) * ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ) ^ (-(n : ℤ) - 1)) := by
    rw [Complex.ofReal_mul, Complex.ofReal_zpow]
    push_cast
    ring
  rw [hA, hD]
  exact bmKerEps_algebra hε (nrmSq_nonneg z)

end Work.CR.Flat.Cauchy
