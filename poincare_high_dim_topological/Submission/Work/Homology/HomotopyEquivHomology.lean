import Mathlib
import Submission.Work.Homology.Basic

/-!
# Homotopy invariance of singular homology: homotopy equivalences

Homotopic continuous maps induce the same map on singular homology, and hence a
homotopy equivalence induces an isomorphism on singular homology in every degree.

The key ingredient from Mathlib is
`TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`, which states that
a homotopy `H : TopCat.Homotopy f g` between maps `f g : X ⟶ Y` of topological
spaces yields equal maps on the homology of the singular chain complexes.
-/

open CategoryTheory AlgebraicTopology

namespace Work.Homology

/-- Homotopic maps induce equal maps on singular homology with coefficients in `R`. -/
lemma singHomologyMap_congr (R : ModuleCat ℤ) (k : ℕ) {X Y : TopCat} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) : singHomologyMap R k f = singHomologyMap R k g :=
  TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (C := ModuleCat ℤ) H R k

/-- A homotopy equivalence of topological spaces induces an isomorphism on singular
homology with coefficients in any `R : ModuleCat ℤ`, in every degree. -/
theorem HomotopyEquivHomology (R : ModuleCat ℤ) (k : ℕ) {X Y : TopCat} (f : X ⟶ Y)
    (hf : IsHomotopyEquivalence f) :
    Nonempty (singHomology R k X ≅ singHomology R k Y) := by
  obtain ⟨g, h1, h2⟩ := hf
  refine ⟨{ hom := singHomologyMap R k f
            inv := singHomologyMap R k g
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · rw [← singHomologyMap_comp R k f g, singHomologyMap_congr R k h1.some, singHomologyMap_id]
  · rw [← singHomologyMap_comp R k g f, singHomologyMap_congr R k h2.some, singHomologyMap_id]

end Work.Homology
