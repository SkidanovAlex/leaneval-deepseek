import Mathlib
import Submission.Work.Cohomology.CompatTrans.prodSphereDefs
import Submission.Work.Cohomology.CompatTrans.homotopyEquiv_A1set
import Submission.Work.Cohomology.homologyContractible

open CategoryTheory

set_option linter.style.haveILetI false

namespace Work.Cohomology

/-- If a continuous map `f : X ⟶ Sᵖ⁺¹` avoids the north pole `sphN p`, then it induces the zero
map on singular homology in positive degrees: the image of `f` lies in the punctured sphere
`{z | z ≠ sphN p}`, which is contractible, so `f` factors through a space with vanishing
positive-degree homology. -/
lemma homologyMap_eq_zero_of_avoiding_sphN (X : TopCat) (p n : ℕ) (hn : 1 ≤ n)
    (f : X ⟶ sphTop (p + 1)) (hf : ∀ x, f x ≠ sphN p) :
    HomologicalComplex.homologyMap (chainMap ℤ X (sphTop (p + 1)) f) n = 0 := by
  -- the punctured sphere, and the corestriction of `f` to it
  let Y : TopCat := TopCat.of {z : ↥(sphSet (p + 1)) // z ≠ sphN p}
  let g : X ⟶ Y :=
    TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, Continuous.subtype_mk f.hom.continuous _⟩
  let incl : Y ⟶ sphTop (p + 1) := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hfg : f = g ≫ incl := by
    apply TopCat.ext
    intro x
    rfl
  have hchain : chainMap ℤ X (sphTop (p + 1)) f
      = chainMap ℤ X Y g ≫ chainMap ℤ Y (sphTop (p + 1)) incl := by
    rw [hfg]
    simp only [chainMap]
    rw [CategoryTheory.Functor.map_comp]
  -- the punctured sphere is contractible, so `Hₙ` of it vanishes
  haveI : ContractibleSpace ↥Y := contractible_compl_sphN p
  have hY : CategoryTheory.Limits.IsZero ((singularChains ℤ Y).homology n) := homologyContractible n (by omega)
  have hincl : HomologicalComplex.homologyMap (chainMap ℤ Y (sphTop (p + 1)) incl) n = 0 :=
    hY.eq_zero_of_src _
  rw [hchain, HomologicalComplex.homologyMap_comp, hincl]
  simp

end Work.Cohomology
