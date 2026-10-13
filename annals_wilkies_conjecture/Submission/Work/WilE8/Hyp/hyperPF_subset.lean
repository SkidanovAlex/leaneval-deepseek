import Mathlib
import Submission.Work.WilE8.Hyp.Basic

namespace Work.WilE8.Hyp

/-- The inverse relation for `psi` along a point of the unit circle: if
`y² + w² = 1` and `w > 0` then `psi (y / w) = y`, i.e. `y = x / √(1 + x²)` with
`x = y / w` (and `w = 1 / √(1 + x²)`). -/
theorem psi_div_of_sq_add_sq {y w : ℝ} (h : y ^ 2 + w ^ 2 = 1) (hw : 0 < w) :
    WilkiesDesign.E.psi (y / w) = y := by
  rw [WilkiesDesign.E.psi]
  have hwne : w ≠ 0 := ne_of_gt hw
  have h1 : 1 + (y / w) ^ 2 = (1 / w) ^ 2 := by
    rw [div_pow, div_eq_mul_inv, one_div, inv_pow]
    field_simp
    nlinarith [h]
  rw [h1, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity), div_div_eq_mul_div]
  field_simp
  try ring

theorem hyperPF_subset {n : ℕ} (Q : MvPolynomial (Fin n) ℝ) :
    WilkiesDesign.E.projFirst n n '' (Work.WilE8.Hyp.hyperPF Q).set ⊆
      WilkiesDesign.E.psiV '' {x : Fin n → ℝ | MvPolynomial.eval x Q = 0} := by
  rintro u ⟨z, hz, rfl⟩
  rw [Work.WilE8.Hyp.mem_hyperPF_set] at hz
  obtain ⟨hcube, hsq, hclr, hpos⟩ := hz
  -- The witnessing point of `{Q = 0}` is `x i = yᵢ / wᵢ`, where `y = projFirst n n z`
  -- and `w` is the last-`n`-coordinates block.
  refine ⟨fun i => z (Fin.castAdd n i) / z (Fin.natAdd n i), ?_, ?_⟩
  · -- `Q x = 0`: the cleared-denominator identity gives `∏ wᵢ^d * Q x = 0`.
    have hw : ∀ i : Fin n, z (Fin.natAdd n i) ≠ 0 := fun i => ne_of_gt (hpos i)
    have hce := Work.WilE8.Clear.clearDenom_eval Q (fun i => z (Fin.castAdd n i))
        (fun i => z (Fin.natAdd n i)) hw
    have hfun : (Sum.elim (fun i : Fin n => z (Fin.castAdd n i))
        (fun i : Fin n => z (Fin.natAdd n i)))
        = (fun v : Fin n ⊕ Fin n => z (finSumFinEquiv v)) := by
      funext v; cases v with
      | inl i => simp
      | inr i => simp
    have hclr' : MvPolynomial.eval (Sum.elim (fun i : Fin n => z (Fin.castAdd n i))
        (fun i : Fin n => z (Fin.natAdd n i))) (Work.WilE8.clearDenom Q) = 0 := by
      rw [hfun]; exact hclr
    have hprod : (∏ i : Fin n, z (Fin.natAdd n i) ^ Q.totalDegree) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hw i))
    have hzero : (∏ i : Fin n, z (Fin.natAdd n i) ^ Q.totalDegree) *
        MvPolynomial.eval (fun i => z (Fin.castAdd n i) / z (Fin.natAdd n i)) Q = 0 := by
      rw [hce, hclr']
    exact (mul_eq_zero.mp hzero).resolve_left hprod
  · -- `psiV x = projFirst n n z` coordinatewise, from `yᵢ² + wᵢ² = 1` and `wᵢ > 0`.
    funext i
    simp only [WilkiesDesign.E.psiV, WilkiesDesign.E.projFirst]
    exact psi_div_of_sq_add_sq (by linarith [hsq i]) (hpos i)

end Work.WilE8.Hyp
