/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The array/form dictionary: `∇(Arr α) = proj02 Jstd (dOne α) + ∇(Arr (Π₁ α))`

For a `1`-form `α` on `ℂⁿ` (a map `z ↦ (V ↦ α z V)` into the real-linear functionals) write
`Arr α` for its *array* of coefficients `m ↦ (z ↦ α z e_m)` (`e_m = Pi.single m 1`), so that the
array-level `∂̄₀` of `α` is the family of functions `z ↦ ∂̄_m(α · e_j)(z)` and

  `∇(Arr α)_{lm} := ∂̄_l (α · e_m) - ∂̄_m (α · e_l)`.

The *form*-level `∂̄₀` of `α` is `proj02 Jstd (dOne α)`.  The two do not agree for a general form,
because the array-level `∂̄₀` sees only the *values* `α z e_j` while the form-level operator sees the
whole jet of `α`.  The discrepancy is exactly the `∇` of the array of the `(1,0)`-part `Pi10 α`:

  `∇(Arr α)_{lm} = (∂̄₀ α)(z)(e_l, e_m) + ∇(Arr (Π₁ α))_{lm}`,

which is the form `Work.NN.Final.nabla_arr_Pi10` below.  Equivalently `Π₁` is precisely the
correction that makes the array-level `∂̄₀` of a `(1,0)`-form vanish (its array of coefficients is
`z ↦ α z e_j` and the `(1,0)`-part differentiates only through the `(1,0)`-directions, which the
array-level `∂̄₀` does not see); taking `α` itself as `Pi10`-part plus `(0,1)`-part splits the
identity into "form part" + "junk part", cf. `Work/NN/Final/NOTES_defect_step_CORRECTED.md` §3.

`Π₁ = Pi10` is *pointwise* in `α` (`Pi10 α z = (1/2)(α z - i·α z ∘ Jstd)`): it does **not**
differentiate the coefficients of `α`, which is why the junk term can be bounded by the values of
`α` alone.

The proof is purely algebraic: `dOne`, `dbarCoord` and `proj02` are all real-linear in the jet of
`ξ`, so after unfolding the definitions and applying the product/sum rule for `fderiv` to the
pointwise identity `Pi10 ξ z V = (1/2)(ξ z V - i·ξ z (i·V))`, both sides become the same
polynomial in the eight numbers `(∂_V ξ · W)(z)` (`V ∈ {e_l, ie_l}`, `W ∈ {e_m, ie_m}`).
-/
import Mathlib
import Submission.Work.NN.Final.defectFormIdentity
import Submission.Work.NN.Core.CnPert

namespace Work.NN.Final

open Work.NN.Core

/-- The pointwise identity `Pi10 ξ z W = (1/2)(ξ z W - i·ξ z (i•W))` propagates to the `fderiv`:
`fderiv` of `z' ↦ Pi10 ξ z' W` in direction `V` is `(1/2)((∂_V ξ·W) - i·(∂_V ξ·(i•W)))`.

This is the only place where differentiability of `ξ` (one derivative at `z`) is used. -/
lemma fderiv_Pi10_apply {n : ℕ} {ξ : Cn n → Cn n →L[ℝ] ℂ} {z : Cn n}
    (hξ : ∀ W : Cn n, DifferentiableAt ℝ (fun z' => ξ z' W) z) (V W : Cn n) :
    fderiv ℝ (fun z' => Pi10 ξ z' W) z V
      = (1 / 2 : ℂ) * (fderiv ℝ (fun z' => ξ z' W) z V
          - Complex.I * fderiv ℝ (fun z' => ξ z' (Complex.I • W)) z V) := by
  have ha : DifferentiableAt ℝ (fun z' => ξ z' W) z := hξ W
  have hb : DifferentiableAt ℝ (fun z' => ξ z' (Complex.I • W)) z := hξ (Complex.I • W)
  have hkey : (fun z' => Pi10 ξ z' W)
      = fun z' => (1 / 2 : ℂ) * (ξ z' W - Complex.I * ξ z' (Complex.I • W)) := by
    funext z'; rw [Pi10_apply]
  rw [hkey]
  have hsmul : (fun z' : Cn n => (1 / 2 : ℂ) * (ξ z' W - Complex.I * ξ z' (Complex.I • W)))
      = (1 / 2 : ℂ) • ((fun z' => ξ z' W)
          - Complex.I • (fun z' => ξ z' (Complex.I • W))) := by
    funext z'; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsmul]
  have hb' : DifferentiableAt ℝ ((fun z' => ξ z' W)
      - Complex.I • (fun z' => ξ z' (Complex.I • W))) z := ha.sub (hb.const_smul Complex.I)
  rw [fderiv_const_smul hb' (1 / 2 : ℂ), fderiv_sub ha (hb.const_smul Complex.I),
    fderiv_const_smul hb Complex.I]
  simp only [smul_apply, sub_apply, smul_eq_mul]

/-- **The array/form dictionary at component level.**

For a `C¹` `1`-form `ξ` on `ℂⁿ`, the array-level `∇` of its coefficient array agrees with the
form-level `(0,2)`-projection `∂̄₀ = proj02 Jstd (dOne ·)` of `ξ`, up to the array-level `∇` of the
`(1,0)`-part `Pi10 ξ`:

  `∇(Arr ξ)_{lm} = proj02 Jstd (dOne ξ)(z)(e_l, e_m) + ∇(Arr (Π₁ ξ))_{lm}`. -/
theorem nabla_arr_Pi10 {n : ℕ} {ξ : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ}
    (hξ : ContDiff ℝ 1 ξ) (l m : Fin n) (z : Work.NN.Core.Cn n) :
    Work.CR.Flat.dbarCoord l (fun z' => ξ z' (Pi.single m 1)) z
        - Work.CR.Flat.dbarCoord m (fun z' => ξ z' (Pi.single l 1)) z
      = Work.NN.Final.proj02 (Work.NN.Core.JstdCn n) (Work.NN.Final.dOne ξ) z
          (Pi.single l 1) (Pi.single m 1)
        + (Work.CR.Flat.dbarCoord l (fun z' => Work.NN.Final.Pi10 ξ z' (Pi.single m 1)) z
            - Work.CR.Flat.dbarCoord m (fun z' => Work.NN.Final.Pi10 ξ z' (Pi.single l 1)) z) := by
  have hξd : DifferentiableAt ℝ ξ z := hξ.contDiffAt.differentiableAt (by norm_num)
  have hdiff : ∀ W : Cn n, DifferentiableAt ℝ (fun z' => ξ z' W) z :=
    fun W => hξd.clm_apply (differentiableAt_const W)
  -- unfold the three operators and normalise the direction vectors
  simp only [Work.CR.Flat.dbarCoord, dOne, proj02, Work.NN.Core.JstdCn_apply]
  rw [← Work.NN.Core.smul_single_I l, ← Work.NN.Core.smul_single_I m]
  -- push `fderiv` through the pointwise definition of `Pi10`
  simp only [fderiv_Pi10_apply hdiff]
  -- what remains is the algebraic identity in the eight derivatives
  ring_nf
  rw [Complex.I_sq]
  ring

end Work.NN.Final
