import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.PB3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiMf_tsupport_subset`

The windowed mean-free part of a one-body state is supported in the corpus box:

    tsupport ((χ_ℓ x : ℂ) * mf ℓ f x) ⊆ boxL ℓ     (ℓ > 0),

where `χ_ℓ = Submission.BoseGases.chiScale ℓ` is the corpus bump `χ(x/ℓ)` (the `corpusBox`
localization function of `Work.BoseK15`) and `mf ℓ f = f − (ℓ³)⁻¹∫_{boxL ℓ} f` is the mean-free
part of `PB3Defs`.

This is *not* obvious from the definition of `mf` (the subtracted constant is nonzero for every
non-constant `f`); the point is that the product vanishes wherever `χ_ℓ` does, and `χ_ℓ` — being
the corpus bump scaled by `ℓ` — is supported in `ℓ • [-1/2,1/2]³ = boxL ℓ`, which is closed.  The
proof is therefore the support inclusion for `χ_ℓ` (`Work.BoseB4.BoxData.chiLam_supp`, read at
`B = Work.BoseK15.corpusBox`) transported through `tsupport ⊆ closure(support)`.
-/

open MeasureTheory

namespace Work.BoseBoxFock

/-- The corpus localization function of `Work.BoseK15.corpusBox` is `chiScale`: the coercion
`((χ_ℓ x : ℝ) : ℂ)` is the complexified `corpusBox.chiLam ℓ`. -/
theorem chiScale_complexify_eq_chiLam (ℓ : ℝ) :
    (fun x : EuclideanSpace ℝ (Fin 3) =>
        ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ))
      = fun x => ((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) :=
  rfl

/-- `χ_ℓ` vanishes off the corpus box: the support form of `chiLam_supp`. -/
theorem support_chiScale_subset {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Function.support (Submission.BoseGases.chiScale ℓ)
      ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  intro x hx
  exact Work.BoseB4.BoxData.chiLam_supp Work.BoseK15.corpusBox hℓ hx

/-- The `tsupport`-form: `χ_ℓ` is supported in the (closed) box `boxL ℓ`. -/
theorem tsupport_chiScale_subset {ℓ : ℝ} (hℓ : 0 < ℓ) :
    tsupport (Submission.BoseGases.chiScale ℓ) ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
  closure_minimal (support_chiScale_subset hℓ)
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).isClosed

/-- The target: the windowed mean-free part is supported in the corpus box. -/
theorem chiMf_tsupport_subset {ℓ : ℝ} (hℓ : 0 < ℓ) (f : EuclideanSpace ℝ (Fin 3) → ℂ) :
    tsupport (fun x : EuclideanSpace ℝ (Fin 3) =>
      ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * Work.BoseBoxFock.mf ℓ f x)
      ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  refine closure_minimal ?_ (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).isClosed
  intro x hx
  have hchi : Submission.BoseGases.chiScale ℓ x ≠ 0 := by
    intro h0
    exact hx (by simp [h0])
  exact support_chiScale_subset hℓ hchi

end Work.BoseBoxFock
