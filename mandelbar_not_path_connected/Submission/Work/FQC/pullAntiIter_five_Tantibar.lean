import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.MRMT.Wirtinger.dzbar_comp
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-! ## The five-fold pull-back along an anti-holomorphic map

`pullAntiIter f 5 μ z` is the coefficient obtained by pulling `μ` back five times along the
*anti*-holomorphic map `f`.  When `f` is anti-holomorphic (`∂f ≡ 0`) this equals a single
pull-back of `μ` along the fifth iterate `f^[5]`:

`pullAntiIter f 5 μ z = star (μ (f^[5] z)) · (∂̄(f^[5]) z / conj (∂̄(f^[5]) z))`.

The proof expands `pullAntiIter f 5 μ` into an alternating product of the elementary ratios
`rho f w = ∂̄f w / conj (∂̄f w)` (via `star (rho f w) = (rho f w)⁻¹`) and computes `∂̄(f^[5])`
by four applications of the Wirtinger chain rules `dzbar_comp`, `dz_comp`.  The requested
statement is the specialisation `f = Tantibar c` (`∂̄` of an iterate of the antipolynomial). -/

/-- The elementary "ratio" of an anti-holomorphic derivative: `∂̄f w / conj (∂̄f w)`. -/
private def rho (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Work.MRMT.dzbar f z / star (Work.MRMT.dzbar f z)

/-- Conjugation inverts `rho`. -/
private theorem star_rho (f : ℂ → ℂ) (z : ℂ) : star (rho f z) = (rho f z)⁻¹ := by
  simp only [rho, star_div₀, star_star, inv_div]

/-- The inverse of the conjugate of `rho` is `rho` itself. -/
private theorem star_inv_rho (f : ℂ → ℂ) (z : ℂ) : star ((rho f z)⁻¹) = rho f z := by
  rw [← star_rho f z, star_star]

/-- The one-step recursion for `pullAntiIter`, in the `rho` vocabulary. -/
private theorem succ_apply (f μ : ℂ → ℂ) (n : ℕ) (w : ℂ) :
    pullAntiIter f (n + 1) μ w = star ((pullAntiIter f n μ) (f w)) * rho f w := by
  rw [pullAntiIter_succ]
  simp only [rho, pullAnti, div_eq_mul_inv]
  ring

private lemma iter2_apply (f : ℂ → ℂ) (z : ℂ) : (f^[2]) z = f (f z) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one]

private lemma iter3_apply (f : ℂ → ℂ) (z : ℂ) : (f^[3]) z = f (f (f z)) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply', iter2_apply]

private lemma iter4_apply (f : ℂ → ℂ) (z : ℂ) : (f^[4]) z = f (f (f (f z))) := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply', iter3_apply]

private lemma iter5_apply (f : ℂ → ℂ) (z : ℂ) : (f^[5]) z = f (f (f (f (f z)))) := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply', iter4_apply]

/-- **Five-fold pull-back along an anti-holomorphic map.**  For `f : ℂ → ℂ` that is real
differentiable everywhere and has `∂f ≡ 0`, the five-fold pulled-back coefficient is the
pull-back of `μ` along the iterate `f^[5]`. -/
private theorem pullAntiIter_five_eq (f μ : ℂ → ℂ) (hf : Differentiable ℝ f)
    (hdz : ∀ z, Work.MRMT.dz f z = 0) (z : ℂ) :
    pullAntiIter f 5 μ z = star (μ ((f^[5]) z)) *
      (Work.MRMT.dzbar (f^[5]) z / star (Work.MRMT.dzbar (f^[5]) z)) := by
  -- Step 1: expand the five folds into an alternating product of elementary ratios.
  have hP : pullAntiIter f 5 μ z = star (μ (f (f (f (f (f z)))))) *
      (rho f (f (f (f (f z)))) * (rho f (f (f (f z))))⁻¹ * rho f (f (f z))
        * (rho f (f z))⁻¹ * rho f z) := by
    simp only [show (5 : ℕ) = 4 + 1 from rfl, show (4 : ℕ) = 3 + 1 from rfl,
      show (3 : ℕ) = 2 + 1 from rfl, show (2 : ℕ) = 1 + 1 from rfl, succ_apply,
      pullAntiIter_zero, star_mul, star_rho, star_inv_rho, star_star]
    ring
  -- Step 2: the Wirtinger derivative of the fifth iterate, by the chain rules.
  have hA5 : Work.MRMT.dzbar (f^[5]) z =
      Work.MRMT.dzbar f (f (f (f (f z)))) * star (Work.MRMT.dzbar f (f (f (f z))))
        * Work.MRMT.dzbar f (f (f z)) * star (Work.MRMT.dzbar f (f z))
        * Work.MRMT.dzbar f z := by
    have hA2 : Work.MRMT.dzbar (f^[2]) z = 0 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ', Function.iterate_one]
      rw [Work.MRMT.Wirtinger.dzbar_comp (f := f) (g := f) (hf (f z)) (hf z)]
      rw [hdz (f z), hdz z]; simp
    have hB2 : Work.MRMT.dz (f^[2]) z =
        Work.MRMT.dzbar f (f z) * star (Work.MRMT.dzbar f z) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ', Function.iterate_one]
      rw [Work.MRMT.Wirtinger.dz_comp (f := f) (g := f) (hf (f z)) (hf z)]
      rw [hdz (f z), hdz z]; ring
    have hA3 : Work.MRMT.dzbar (f^[3]) z =
        Work.MRMT.dzbar f (f (f z)) * star (Work.MRMT.dzbar f (f z)) * Work.MRMT.dzbar f z := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ']
      rw [Work.MRMT.Wirtinger.dzbar_comp (f := f^[2]) (g := f) (hf ((f^[2]) z))
        ((hf.iterate 2) z)]
      rw [iter2_apply]
      rw [hdz (f (f z)), hB2]; simp only [star_mul, star_star]; ring
    have hB3 : Work.MRMT.dz (f^[3]) z = 0 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ']
      rw [Work.MRMT.Wirtinger.dz_comp (f := f^[2]) (g := f) (hf ((f^[2]) z))
        ((hf.iterate 2) z)]
      rw [hdz ((f^[2]) z), hA2]; simp
    have hA4 : Work.MRMT.dzbar (f^[4]) z = 0 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ']
      rw [Work.MRMT.Wirtinger.dzbar_comp (f := f^[3]) (g := f) (hf ((f^[3]) z))
        ((hf.iterate 3) z)]
      rw [hdz ((f^[3]) z), hB3]; simp
    have hB4 : Work.MRMT.dz (f^[4]) z =
        Work.MRMT.dzbar f (f (f (f z))) * star (Work.MRMT.dzbar f (f (f z)))
          * Work.MRMT.dzbar f (f z) * star (Work.MRMT.dzbar f z) := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ']
      rw [Work.MRMT.Wirtinger.dz_comp (f := f^[3]) (g := f) (hf ((f^[3]) z))
        ((hf.iterate 3) z)]
      rw [iter3_apply]
      rw [hdz (f (f (f z))), hA3]; simp only [star_mul, star_star]; ring
    rw [show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ']
    rw [Work.MRMT.Wirtinger.dzbar_comp (f := f^[4]) (g := f) (hf ((f^[4]) z))
      ((hf.iterate 4) z)]
    rw [iter4_apply]
    rw [hdz (f (f (f (f z)))), hB4]; simp only [star_mul, star_star]; ring
  -- Step 3: the alternating product of ratios is the ratio of the fifth iterate's derivative.
  have hprod : rho f (f (f (f (f z)))) * (rho f (f (f (f z))))⁻¹ * rho f (f (f z))
        * (rho f (f z))⁻¹ * rho f z
      = Work.MRMT.dzbar (f^[5]) z / star (Work.MRMT.dzbar (f^[5]) z) := by
    rw [hA5]
    simp only [rho, inv_div]
    simp only [star_mul, star_star]
    rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, div_mul_div_comm]
    ring
  rw [hP, iter5_apply, hprod]

/-! ## The antipolynomial `Tantibar c = z ↦ z̄² + c` -/

private theorem antistar_Tantibar (c : ℂ) :
    (star ∘ Tantibar c) = fun z : ℂ => z ^ 2 + star c := by
  funext z; simp [Tantibar, map_add, map_pow]

private theorem differentiable_Tantibar (c : ℂ) : Differentiable ℝ (Tantibar c) := by
  have hd : Differentiable ℂ (star ∘ Tantibar c) := by
    rw [antistar_Tantibar]; exact (differentiable_id.pow 2).add_const (star c)
  intro z
  exact Work.MRMT.Wirtinger.differentiableAt_of_antiholo (hd z)

private theorem dz_Tantibar (c : ℂ) (z : ℂ) : Work.MRMT.dz (Tantibar c) z = 0 := by
  apply Work.MRMT.Wirtinger.dz_of_antiholo
  rw [antistar_Tantibar]
  exact ((differentiable_id.pow 2).add_const (star c)).differentiableAt

/-- The `Tantibar c` specialisation: the five-fold pull-back along the antipolynomial. -/
theorem pullAntiIter_five_Tantibar (c : ℂ) (μ : ℂ → ℂ) (z : ℂ) :
    Work.FQC.pullAntiIter (LeanEval.ComplexAnalysis.Tantibar c) 5 μ z =
      star (μ ((LeanEval.ComplexAnalysis.Tantibar c)^[5] z)) *
        (Work.MRMT.dzbar ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z /
          star (Work.MRMT.dzbar ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z)) := by
  exact pullAntiIter_five_eq (Tantibar c) μ (differentiable_Tantibar c) (dz_Tantibar c) z

end

end Work.FQC
