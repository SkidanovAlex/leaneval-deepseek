import Mathlib
import Submission.Work.Pi6.MSS.E1B.Kit
import Submission.Work.SSSR.serreE2Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The duality of the `E_1` row: the comparison map

For the Serre cochain filtration `serreCF 𝕜 E B p` of a continuous map `p : E → B`, the first page
`E_1^{s,n}` is the `𝕜`-dual of `H_n` of the `s`-th graded piece of the Serre *chain* filtration.
The comparison map is built in `Work.Pi6.MSS.E1B.Kit` (`evZ`, `evS`); here we record the
canonical isomorphism `H_n(E) ≅ Z_n(E)/B_n(E)` (`homIsoH`) for an arbitrary chain complex of vector
spaces, and the resulting map `EV` from the first page to `Hom(H_n(gr_s),𝕜)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS.E1B

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B] {𝕜 : Type} [Field 𝕜]

/-- **The canonical isomorphism `H_n ≅ Z_n/B_n`** for a chain complex of vector spaces: the
composite of the identification of the homology with the homology of the short complex
`E_{n+1} → E_n → E_{n-1}` and the explicit description of that homology. -/
noncomputable def homIsoH (𝕜 : Type) [Field 𝕜] (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) :
    E.homology n ≅ ModuleCat.of 𝕜
      (↥(Work.StemsB.fdZ 𝕜 E n) ⧸ Work.StemsB.fdH 𝕜 E n) :=
  (E.homologyIsoSc' (n+1) n (n-1) (Work.Cohomology.down_prev n)
      (Work.Cohomology.down_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso (E.sc' (n+1) n (n-1))

/-- **The comparison map** `E_1^{s,n} → Hom_𝕜(H_n(gr_s), 𝕜)`: the evaluation of a class of the
first page on the cycles of the graded piece, transported along `homIsoH`. -/
noncomputable def EV (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n) :
    pEraw 𝕜 (Wc 𝕜 p) 1 s n →ₗ[𝕜] ((Kg 𝕜 p s).homology n →ₗ[𝕜] 𝕜) where
  toFun x := (evS 𝕜 p s n hann x).comp
    (ModuleCat.Hom.hom (homIsoH 𝕜 (Kg 𝕜 p s) n).hom)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp
  map_smul' a x := by
    apply LinearMap.ext
    intro z
    simp

@[simp] theorem EV_apply (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n)
    (x : pEraw 𝕜 (Wc 𝕜 p) 1 s n) (y : (Kg 𝕜 p s).homology n) :
    EV 𝕜 p s n hann x y = evS 𝕜 p s n hann x
      (ModuleCat.Hom.hom (homIsoH 𝕜 (Kg 𝕜 p s) n).hom y) := rfl

/-- `E1Complex` depends only on the underlying functor of the filtration. -/
theorem E1Complex_eq_of_F_eq {C : ChainComplex (ModuleCat 𝕜) ℕ}
    {ξ ξ' : Work.SSSR.Filtration 𝕜 C} (h : ξ.F = ξ'.F) (t : ℕ) :
    Work.SSSR.E1Complex 𝕜 ξ t = Work.SSSR.E1Complex 𝕜 ξ' t := by
  cases ξ with
  | mk F mono incl mono_incl compat sat =>
  cases ξ' with
  | mk F' mono' incl' mono_incl' compat' sat' =>
  change F = F' at h
  subst h
  rfl

end

end Work.Pi6.MSS.E1B
