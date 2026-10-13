/-
  WilC4/realize_bd_hyper : Łoś's theorem for *bounded* formulas in the hyperreal model `HR`.

  `HR = Germ (hyperfilter ℕ) ℝ` is the ultraproduct of `ℝ` along the (nonprincipal) ultrafilter
  `hyperfilter ℕ`, and `instLRcHR` is its `LRc`-structure, defined in `HyperRealSetup` as the
  *quotient* of the pointwise `LRc`-structure on `ℕ → ℝ`.

  Mathlib already provides Łoś's theorem for bounded formulas for its own ultraproduct
  structure `Ultraproduct.structure`.  The content here is the identification of the two
  structures: `instLRcHR` and `Ultraproduct.structure` have literally the same `funMap`
  (both evaluate the language functions pointwise on representatives) and their `RelMap`s agree
  because `LRc` has no relation symbols at all (`IsEmpty (LRc.Relations n)`).  In particular the
  two structures are *equal*, and Łoś's theorem transfers verbatim.
-/
import Mathlib
import Submission.Work.WilC4.HyperRealSetup

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC4

/-- `LRc` has no relation symbols: its relation types are built from `Empty` by `⊕`
(`Language.ring`, `rexpL` and `constantsOn ℝ` are all purely functional languages). -/
theorem isEmpty_rel (n : ℕ) : IsEmpty (WilkiesDesign.CG.LRc.Relations n) :=
  inferInstanceAs (IsEmpty ((FirstOrder.Language.ring.Relations n ⊕
      WilkiesDesign.CG.rexpL.Relations n) ⊕ (FirstOrder.Language.constantsOn ℝ).Relations n))

/-- The `LRc`-structure `instLRcHR` on the hyperreals agrees with the structure induced by
Mathlib's ultraproduct construction, `Ultraproduct.structure`.

The two `funMap`s are the same term (both interpret the language functions pointwise on
representatives), and the two `RelMap`s agree because `LRc` has no relation symbols, so both are
functions out of an empty type. -/
theorem instLRcHR_eq_ultraproduct :
    Work.WilC4.instLRcHR =
      Ultraproduct.structure (M := fun _ : ℕ => ℝ)
        (u := (Filter.hyperfilter ℕ : Ultrafilter ℕ)) (L := WilkiesDesign.CG.LRc) := by
  refine Structure.ext ?_ ?_
  · funext n f x
    rfl
  · funext n r x
    exact (isEmpty_rel n).elim r

/-- **Łoś's theorem for bounded formulas**: a bounded `LRc`-formula holds of germs in `HR`
if and only if it holds at almost every index. -/
theorem realize_bd_hyper {β : Type*} {n : ℕ} (φ : WilkiesDesign.CG.LRc.BoundedFormula β n)
    (x : β → ℕ → ℝ) (v : Fin n → ℕ → ℝ) :
    (@FirstOrder.Language.BoundedFormula.Realize WilkiesDesign.CG.LRc Work.WilC4.HR Work.WilC4.instLRcHR β n φ
        (fun i => (↑(x i) : Work.WilC4.HR)) (fun i => (↑(v i) : Work.WilC4.HR))) ↔
      ∀ᶠ a in (Filter.hyperfilter ℕ : Filter ℕ),
        @FirstOrder.Language.BoundedFormula.Realize WilkiesDesign.CG.LRc ℝ inferInstance β n φ
          (fun i => x i a) (fun i => v i a) := by
  rw [instLRcHR_eq_ultraproduct]
  exact Ultraproduct.boundedFormula_realize_cast (M := fun _ : ℕ => ℝ)
    (u := (Filter.hyperfilter ℕ : Ultrafilter ℕ)) (L := WilkiesDesign.CG.LRc) φ x v

end Work.WilC4
