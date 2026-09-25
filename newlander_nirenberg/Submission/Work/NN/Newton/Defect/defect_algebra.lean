import Mathlib
import Submission.Work.NN.Newton.DefectDefs

/-!
# The algebraic identity `E = 2·X + TA` behind the quadratic `∂̄`-defect

`Eexpr A z l j k` is the `(0,2)`-form-level expansion of the integrability identity
`proj02 J (d ∂̄_J z_l) = 0`; `defectExpr A z l j k` is the flat `∂̄`-defect of the coordinate datum
`F^{(l)}_m = Lcoef A (·l) m`; `TA A z l j k` collects the ten quadratic terms of `Eexpr`.

The point of this file: **given the differentiated almost-complexity relation**

`hrel : (DA_z X)((Jstd + A) z Y) = -((Jstd + A) z ((DA_z X) Y))`

(pointwise derivative of `(Jstd + A)² = -1`), the expansion reduces to the *linear* identity

`Eexpr = 2 · defectExpr + TA`,

so on the locus `Eexpr = 0` the defect is exactly half the quadratic part:

`defectExpr = -(1/2) · TA`.

The proof is a finite computation.  Writing `m X Y = λ_l((DA_z X) Y)` and
`mA X Y = λ_l(A z ((DA_z X) Y))` (both additive in each argument), the four terms of `Eexpr`
that contain `(Jstd + A) z ·` in the *second* slot are rewritten with the scalar consequence of
`hrel`, and the remaining `(Jstd + A) z · = i·(·) + A z (·)` splits are pushed through by
linearity; the surviving combination is a sum of the two "bracket" expressions
`i·m X w + m X (i w) + m X (A z w) + mA X w`, for `(X,w) = (A z e_j, e_k)` and `(A z e_k, e_j)`,
each of which vanishes by the same scalar relation. -/

namespace Work.NN.Newton.Defect

open Work.NN.Newton

theorem defect_algebra {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l j k : Fin n)
    (hrel : ∀ X Y : Work.NN.Core.Cn n,
      (fderiv ℝ A z X) ((Work.NN.Core.JstdCn n + A) z Y)
        = -((Work.NN.Core.JstdCn n + A) z ((fderiv ℝ A z X) Y)))
    (hE : Work.NN.Newton.Eexpr A z l j k = 0) :
    Work.NN.Newton.defectExpr A z l j k = -(1 / 2) * Work.NN.Newton.TA A z l j k := by
  -- `(Jstd + A) z Y = i·Y + A z Y`
  have hS : ∀ Y : Work.NN.Core.Cn n,
      (Work.NN.Core.JstdCn n + A) z Y = Complex.I • Y + A z Y :=
    fun Y => by simp [Work.NN.Core.JstdCn_apply]
  -- `i·e_j = i e_j`, `i·e_k = i e_k`
  have hIej : Complex.I • evec j = ievec j := Work.NN.Core.smul_single_I j
  have hIek : Complex.I • evec k = ievec k := Work.NN.Core.smul_single_I k
  -- The scalar form of the differentiated almost-complexity relation.
  have hrel1 : ∀ X Y : Work.NN.Core.Cn n,
      lamC l ((fderiv ℝ A z X) ((Work.NN.Core.JstdCn n + A) z Y))
        = -Complex.I * lamC l ((fderiv ℝ A z X) Y)
          - lamC l (A z ((fderiv ℝ A z X) Y)) := by
    intro X Y
    have hSlam : ∀ W : Work.NN.Core.Cn n,
        lamC l ((Work.NN.Core.JstdCn n + A) z W)
          = Complex.I * lamC l W + lamC l (A z W) := by
      intro W
      rw [hS W, map_add]
      simp [lamC_apply, Pi.smul_apply, smul_eq_mul]
    have h := congrArg (lamC l) (hrel X Y)
    simp only [map_neg] at h
    rw [hSlam ((fderiv ℝ A z X) Y)] at h
    rw [hS Y] at h ⊢
    linear_combination h
  -- The "bracket" relation `i·m X w + m X (i w) + m X (A z w) + mA X w = 0`.
  have hrel2 : ∀ X w : Work.NN.Core.Cn n,
      Complex.I * lamC l ((fderiv ℝ A z X) w)
        + lamC l ((fderiv ℝ A z X) (Complex.I • w))
        + lamC l ((fderiv ℝ A z X) (A z w))
        + lamC l (A z ((fderiv ℝ A z X) w)) = 0 := by
    intro X w
    have h := hrel1 X w
    rw [hS w] at h
    have hsplit : lamC l ((fderiv ℝ A z X) (Complex.I • w + A z w))
        = lamC l ((fderiv ℝ A z X) (Complex.I • w))
          + lamC l ((fderiv ℝ A z X) (A z w)) := by
      simp only [map_add]
    rw [hsplit] at h
    linear_combination h
  -- The two surviving brackets vanish.
  have hqj : Complex.I * lamC l ((fderiv ℝ A z (A z (evec j))) (evec k))
      + lamC l (A z ((fderiv ℝ A z (A z (evec j))) (evec k)))
      + lamC l ((fderiv ℝ A z (A z (evec j))) (ievec k))
      + lamC l ((fderiv ℝ A z (A z (evec j))) (A z (evec k))) = 0 := by
    have h := hrel2 (A z (evec j)) (evec k)
    rw [hIek] at h
    linear_combination h
  have hqk : Complex.I * lamC l ((fderiv ℝ A z (A z (evec k))) (evec j))
      + lamC l (A z ((fderiv ℝ A z (A z (evec k))) (evec j)))
      + lamC l ((fderiv ℝ A z (A z (evec k))) (ievec j))
      + lamC l ((fderiv ℝ A z (A z (evec k))) (A z (evec j))) = 0 := by
    have h := hrel2 (A z (evec k)) (evec j)
    rw [hIej] at h
    linear_combination h
  -- The expansion `Eexpr = 2·defectExpr + TA + (bracket_j − bracket_k)`.
  have hmaster' : Eexpr A z l j k = 2 * defectExpr A z l j k + TA A z l j k
      + (Complex.I * lamC l ((fderiv ℝ A z (A z (evec j))) (evec k))
         + lamC l (A z ((fderiv ℝ A z (A z (evec j))) (evec k)))
         + lamC l ((fderiv ℝ A z (A z (evec j))) (ievec k))
         + lamC l ((fderiv ℝ A z (A z (evec j))) (A z (evec k)))
         - (Complex.I * lamC l ((fderiv ℝ A z (A z (evec k))) (evec j))
            + lamC l (A z ((fderiv ℝ A z (A z (evec k))) (evec j)))
            + lamC l ((fderiv ℝ A z (A z (evec k))) (ievec j))
            + lamC l ((fderiv ℝ A z (A z (evec k))) (A z (evec j))))) := by
    simp only [Eexpr, defectExpr, TA, LD, LDv]
    rw [hrel1 (evec k) (evec j), hrel1 (evec j) (evec k),
        hrel1 ((Work.NN.Core.JstdCn n + A) z (evec j)) (evec k),
        hrel1 ((Work.NN.Core.JstdCn n + A) z (evec k)) (evec j)]
    simp only [hS, hIej, hIek, map_add, add_apply]
    ring_nf
    simp only [pow_two, Complex.I_mul_I]
    ring
  -- Hence the linear algebra identity `Eexpr = 2·defectExpr + TA`.
  have hmaster : Eexpr A z l j k = 2 * defectExpr A z l j k + TA A z l j k := by
    rw [hmaster', hqj, hqk]
    ring
  -- `hE` says the left side vanishes, so the right side does.
  have h2 : 2 * defectExpr A z l j k + TA A z l j k = 0 := by
    rw [← hmaster]
    exact hE
  linear_combination (1 / 2 : ℂ) * h2

end Work.NN.Newton.Defect
