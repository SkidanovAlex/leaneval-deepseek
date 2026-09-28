import Mathlib
import Submission.Work.Serre.OneCell.Prelim

/-!
# Transfer of the homology comparison along homeomorphisms

If two maps `g' : X → Y` and `g : X' → Y'` are conjugate by homeomorphisms `eX : X ≃ₜ X'` and
`eY : Y ≃ₜ Y'` (i.e. `eY ∘ g' = g ∘ eX`), then `g'` is a rational homology isomorphism in degree `k`
if and only if `g` is.  This is the tool that lets the sub-pair form `{x : ↥S | (x : Z) ∈ T}` of the
local model be replaced by the honest subspace `↥T`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

/-- **Transfer of the homology comparison along a commuting square of homeomorphisms.** -/
theorem isIso_ratHomologyMap_of_homeo_square {X Y X' Y' : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y'] (eX : X ≃ₜ X')
    (eY : Y ≃ₜ Y') (g' : C(X, Y)) (g : C(X', Y')) (h : ∀ x : X, eY (g' x) = g (eX x))
    (k : ℕ) (hg : IsIso (ratHomologyMap g k)) : IsIso (ratHomologyMap g' k) := by
  haveI hX : IsIso (ratHomologyMap (eX : C(X, X')) k) := isIso_ratHomologyMap_homeo eX k
  haveI hY : IsIso (ratHomologyMap (eY : C(Y, Y')) k) := isIso_ratHomologyMap_homeo eY k
  have hmaps : (eY : C(Y, Y')).comp g' = g.comp (eX : C(X, X')) :=
    ContinuousMap.ext fun x => h x
  have h1 : ratHomologyMap g' k ≫ ratHomologyMap (eY : C(Y, Y')) k
      = ratHomologyMap (eX : C(X, X')) k ≫ ratHomologyMap g k := by
    rw [← ratHomologyMap_comp g' (eY : C(Y, Y')),
      ← ratHomologyMap_comp (eX : C(X, X')) g, hmaps]
  have h2 := congrArg (fun t => t ≫ inv (ratHomologyMap (eY : C(Y, Y')) k)) h1
  have h3 : ratHomologyMap g' k
      = ratHomologyMap (eX : C(X, X')) k ≫ ratHomologyMap g k ≫
        inv (ratHomologyMap (eY : C(Y, Y')) k) := by
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, IsIso.inv_hom_id] using h2
  rw [h3]
  infer_instance

/-- Vanishing of rational homology in degree `k` transfers along an equality of subspaces. -/
theorem isZero_ratH_setCongr {X : Type} [TopologicalSpace X] {S T : Set X} (h : S = T) (k : ℕ)
    (hS : IsZero (ratH (TopCat.of ↥S) k)) : IsZero (ratH (TopCat.of ↥T) k) :=
  isZero_ratH_of_homeo (Homeomorph.setCongr h).symm k hS

end

end Work.Serre.OneCell
