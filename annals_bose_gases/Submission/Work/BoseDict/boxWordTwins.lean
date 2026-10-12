import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.boxRealise_annOf
import Submission.Work.BoseDict.boxRealise_creOf_annOf
import Submission.Work.BoseDict.creOf_support_degree
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.boxWordTwins` — the box ↔ model dictionary for ladder *words*

The rows of `Work.BoseBoxFock.H2ndF` are words in the superposed box/model ladder operators
(`annOf`/`creOf` for the honest modes, `ann m 0`/`cre m 0` for the condensate).  The dictionary
identities on disk are one letter at a time (`Work.BoseDict.boxRealise_annOf`,
`Work.BoseDict.CreOfAnnAux.boxCreOf_boxRealise`, `Work.BoseDict.boxRealise_annOf_annOf`,
`Work.BoseDict.boxRealise_creOf_annOf`); this file assembles them into the **words actually
occurring in the rows**:

* `boxRealise_creOf_creOf` — two creations;
* `boxRealise_creOf_annOf_annOf` — creation + two annihilations (`a† a a`, the `Q̃₃`/`χ̂` rows);
* `boxRealise_creOf_creOf_annOf_annOf` — `a†a†aa` (the contact and pairing rows);
* `boxRealise_creOf_annOf_creOf_annOf` — the *interleaved* word `(cre ann)(cre ann)`
  (the `L0 ∘ a_k†a_k ∘ a_0` rows), i.e. a composition of two `dGamma`-type blocks.

**Convention** (the corpus's, cf. `Work.BoseDict.bomb_pair_row`): the degree parameter `d` is the
*lowest* degree occurring in the word, and every intermediate degree is written `d + j` with a
*numeral* `j` — never `n - 1`.  This is what makes the statements typecheck without casts (the
`Nat`-subtraction form `Xn n → Xn (n-1)` is *not* definitionally typed).

**No composite lemmas are needed beyond these**: a general word factors as a composition of
two-letter blocks (`cre∘ann` is `boxRealise_creOf_annOf`, `ann∘ann` is
`boxRealise_annOf_annOf`) and of the two one-letter peels
(`Work.BoseDict.CreOfAnnAux.boxCreOf_boxRealise`, `Work.BoseDict.boxRealise_annOf`), so the row
dictionary of a full `A_V` is a composition of the lemmas here and on disk.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option linter.unusedVariables false

/-- **Two creations.**  `boxRealise e (d+2) (creOf w₁ (creOf w₂ Ψ))` is the two-slot creation
applied to `boxRealise e d Ψ`.  (No degree hypothesis: `boxCreOf_boxRealise` is unconditional.) -/
theorem boxRealise_creOf_creOf {m d : ℕ} {e : Fin m → Sp → ℂ} (w₁ w₂ : Fin m → ℝ)
    (Ψ : Work.BoseB4.RealFock m) :
    boxRealise e (d + 2) (Work.BoseB4.creOf m w₁ (Work.BoseB4.creOf m w₂ Ψ))
      = boxCreOf e w₁ (d + 1) (boxCreOf e w₂ d (boxRealise e d Ψ)) := by
  have h1 : boxRealise e (d + 2) (Work.BoseB4.creOf m w₁ (Work.BoseB4.creOf m w₂ Ψ))
      = boxCreOf e w₁ (d + 1) (boxRealise e (d + 1) (Work.BoseB4.creOf m w₂ Ψ)) :=
    (CreOfAnnAux.boxCreOf_boxRealise (d := d + 1) e w₁ (Work.BoseB4.creOf m w₂ Ψ)).symm
  rw [h1]
  congr 1
  exact (CreOfAnnAux.boxCreOf_boxRealise (d := d) e w₂ Ψ).symm

/-- **Creation + two annihilations** (`a† a a`): for `deg Ψ = d + 2`,
`boxRealise e (d+1) (creOf w (annOf v₁ (annOf v₂ Ψ)))` is the two-slot annihilation followed by
the one-slot creation, applied to `boxRealise e (d+2) Ψ`. -/
theorem boxRealise_creOf_annOf_annOf {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v₁ v₂ : Fin m → ℝ) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 1)
        (Work.BoseB4.creOf m w (Work.BoseB4.annOf m v₁ (Work.BoseB4.annOf m v₂ Ψ)))
      = boxCreOf e w d
          (boxAnnOf e v₁ d (boxAnnOf e v₂ (d + 1) (boxRealise e (d + 2) Ψ))) := by
  have hX : ∀ β ∈ (Work.BoseB4.annOf m v₂ Ψ).support, β.sum (fun _ k => k) = d + 1 := by
    have h := annOf_support_degree (n := d + 2) v₂ Ψ hΨ
    intro β hβ
    have h' := h β hβ
    omega
  have h1 : boxRealise e (d + 1)
        (Work.BoseB4.creOf m w (Work.BoseB4.annOf m v₁ (Work.BoseB4.annOf m v₂ Ψ)))
      = boxCreOf e w d
          (boxRealise e d (Work.BoseB4.annOf m v₁ (Work.BoseB4.annOf m v₂ Ψ))) :=
    (CreOfAnnAux.boxCreOf_boxRealise (d := d) e w
      (Work.BoseB4.annOf m v₁ (Work.BoseB4.annOf m v₂ Ψ))).symm
  rw [h1]
  congr 1
  rw [boxRealise_annOf he hbdd hsupp v₁ (Work.BoseB4.annOf m v₂ Ψ) hX]
  congr 1
  exact boxRealise_annOf he hbdd hsupp v₂ Ψ hΨ

/-- **`a† a† a a`**: for `deg Ψ = d + 2`, the two-slot creation of the two-slot annihilation. -/
theorem boxRealise_creOf_creOf_annOf_annOf {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w₁ w₂ v₁ v₂ : Fin m → ℝ) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2)
        (Work.BoseB4.creOf m w₁
          (Work.BoseB4.creOf m w₂ (Work.BoseB4.annOf m v₁ (Work.BoseB4.annOf m v₂ Ψ))))
      = boxCreOf e w₁ (d + 1)
          (boxCreOf e w₂ d
            (boxAnnOf e v₁ d
              (boxAnnOf e v₂ (d + 1) (boxRealise e (d + 2) Ψ)))) := by
  have hX : ∀ β ∈ (Work.BoseB4.annOf m v₂ Ψ).support, β.sum (fun _ k => k) = d + 1 := by
    have h := annOf_support_degree (n := d + 2) v₂ Ψ hΨ
    intro β hβ
    have h' := h β hβ
    omega
  have hann : boxRealise e d (Work.BoseB4.annOf m v₁ (Work.BoseB4.annOf m v₂ Ψ))
      = boxAnnOf e v₁ d (boxAnnOf e v₂ (d + 1) (boxRealise e (d + 2) Ψ)) := by
    rw [boxRealise_annOf he hbdd hsupp v₁ (Work.BoseB4.annOf m v₂ Ψ) hX]
    congr 1
    exact boxRealise_annOf he hbdd hsupp v₂ Ψ hΨ
  have hc1 : boxRealise e (d + 2)
        (Work.BoseB4.creOf m w₁
          (Work.BoseB4.creOf m w₂ (Work.BoseB4.annOf m v₁ (Work.BoseB4.annOf m v₂ Ψ))))
      = boxCreOf e w₁ (d + 1)
          (boxRealise e (d + 1)
            (Work.BoseB4.creOf m w₂ (Work.BoseB4.annOf m v₁ (Work.BoseB4.annOf m v₂ Ψ)))) :=
    (CreOfAnnAux.boxCreOf_boxRealise (d := d + 1) e w₁
      (Work.BoseB4.creOf m w₂ (Work.BoseB4.annOf m v₁ (Work.BoseB4.annOf m v₂ Ψ)))).symm
  have hc2 : boxRealise e (d + 1)
        (Work.BoseB4.creOf m w₂ (Work.BoseB4.annOf m v₁ (Work.BoseB4.annOf m v₂ Ψ)))
      = boxCreOf e w₂ d
          (boxRealise e d (Work.BoseB4.annOf m v₁ (Work.BoseB4.annOf m v₂ Ψ))) :=
    (CreOfAnnAux.boxCreOf_boxRealise (d := d) e w₂
      (Work.BoseB4.annOf m v₁ (Work.BoseB4.annOf m v₂ Ψ))).symm
  rw [hc1]
  congr 1
  rw [hc2, hann]

/-- **The interleaved word `(cre ann)(cre ann)`** (i.e. two `dGamma`-type blocks composed): for
`deg Ψ = d + 2` the two creation/annihilation pairs read as a *degree-preserving* operator.  This
is the shape of the `L0 ∘ a_k†a_k ∘ a_0` rows of `H2ndF`.  The intermediate degree comes from
`Work.BoseDict.creOf_support_degree` (the superposed creation raises the degree by one). -/
theorem boxRealise_creOf_annOf_creOf_annOf {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w₁ w₂ v₁ v₂ : Fin m → ℝ) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2)
        (Work.BoseB4.creOf m w₁
          (Work.BoseB4.annOf m v₁
            (Work.BoseB4.creOf m w₂ (Work.BoseB4.annOf m v₂ Ψ))))
      = boxCreOf e w₁ (d + 1)
          (boxAnnOf e v₁ (d + 1)
            (boxCreOf e w₂ (d + 1)
              (boxAnnOf e v₂ (d + 1) (boxRealise e (d + 2) Ψ)))) := by
  have hdegX : ∀ β ∈ (Work.BoseB4.annOf m v₂ Ψ).support,
      β.sum (fun _ k => k) = d + 1 := by
    have h := annOf_support_degree (n := d + 2) v₂ Ψ hΨ
    intro β hβ
    have h' := h β hβ
    omega
  have hX : ∀ β ∈ (Work.BoseB4.creOf m w₂ (Work.BoseB4.annOf m v₂ Ψ)).support,
      β.sum (fun _ k => k) = d + 2 :=
    creOf_support_degree w₂ (Work.BoseB4.annOf m v₂ Ψ) hdegX
  -- the inner pair: `annOf v₂` then `creOf w₂`, both at degree `d+1`
  have hinner : boxRealise e (d + 2) (Work.BoseB4.creOf m w₂ (Work.BoseB4.annOf m v₂ Ψ))
      = boxCreOf e w₂ (d + 1) (boxAnnOf e v₂ (d + 1) (boxRealise e (d + 2) Ψ)) :=
    boxRealise_creOf_annOf he hbdd hsupp w₂ v₂ Ψ hΨ
  have h1 : boxRealise e (d + 2)
        (Work.BoseB4.creOf m w₁
          (Work.BoseB4.annOf m v₁
            (Work.BoseB4.creOf m w₂ (Work.BoseB4.annOf m v₂ Ψ))))
      = boxCreOf e w₁ (d + 1)
          (boxRealise e (d + 1)
            (Work.BoseB4.annOf m v₁
              (Work.BoseB4.creOf m w₂ (Work.BoseB4.annOf m v₂ Ψ)))) :=
    (CreOfAnnAux.boxCreOf_boxRealise (d := d + 1) e w₁
      (Work.BoseB4.annOf m v₁
        (Work.BoseB4.creOf m w₂ (Work.BoseB4.annOf m v₂ Ψ)))).symm
  rw [h1]
  congr 1
  rw [boxRealise_annOf he hbdd hsupp v₁
    (Work.BoseB4.creOf m w₂ (Work.BoseB4.annOf m v₂ Ψ)) hX]
  rw [hinner]

end Work.BoseDict
