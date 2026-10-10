import Submission.Work.CY3Stab.Prod.exDiv_prodMap_eq
import Submission.Work.CY3Stab.Prod.prodMap_symm
import Submission.Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv
import Submission.Work.CY3Stab.Prod.cInv_prodMap_of_exDiv_image_twoBases

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.ProdCoeff` — the coefficient comparison from the `exDiv`/residue-field data

With the `exDiv` analysis of the product map (`Work.CY3Stab.Prod.exDiv_prodMap_eq`), the
naturality of the inverse (`Work.CY3Stab.Prod.prodMap_symm`), the tensor transport at the cylinder
points (`Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv`) and the two-base counting
(`Work.CY3Stab.Prod.cInv_prodMap_of_exDiv_image_twoBases`), the *coefficient comparison* of the
stabilisation — the paper's `c(φ × Id_W) = [Z × ℙ¹ × W] − [Z' × ℙ¹ × W]` at the cylinder point,

`cInv 𝕜 (prodPt Z z k) (prodMap k φ) = cInv 𝕜 z φ` —

is a **theorem**, given the residue-field comparison at the cylinder points.  Its `⟸` direction is
*proved* (`Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv`, the tensor transport); its `⟹`
direction is the cylinder rigidity of the paper's Lemma `lem-stbirCY` — the residual input of the
whole stabilisation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3Stab

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- The cylinder point family is injective (the projection onto `X` recovers the point). -/
theorem prodPt_injective (k : ℕ) {X : Scheme.{0}} [X.Over (Spec (.of 𝕜))] (x x' : X)
    [IsDomain (cylTriplet (𝕜 := 𝕜) X x k).tensor]
    [IsDomain (cylTriplet (𝕜 := 𝕜) X x' k).tensor]
    (h : prodPt (𝕜 := 𝕜) X x k = prodPt (𝕜 := 𝕜) X x' k) : x = x' := by
  have h1 := congrArg (Work.K3.baseChangeAlongProj (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) X) h
  rwa [prodPt_snd, prodPt_snd] at h1

/-- **The coefficient comparison of the stabilisation**, from the `exDiv` analysis of the product
map, the tensor transport at the cylinder points, and the **cylinder rigidity** (`hR`, `hR'`: the
`⟹` direction of the residue-field comparison, i.e. the paper's Lemma `lem-stbirCY`). -/
theorem cInv_prodMap_eq (k : ℕ) {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (φ : X.BirationalMap Y) [φ.IsOver (Spec (.of 𝕜))]
    [Variety 𝕜 (WProd (𝕜 := 𝕜) X k)] [Variety 𝕜 (WProd (𝕜 := 𝕜) Y k)]
    [hDX : ∀ (x : X), IsDomain (cylTriplet (𝕜 := 𝕜) X x k).tensor]
    [hDY : ∀ (y : Y), IsDomain (cylTriplet (𝕜 := 𝕜) Y y k).tensor]
    [hSY : (φ.symm).IsOver (Spec (.of 𝕜))]
    (hR : ∀ (Z : Scheme.{0}) [Z.Over (Spec (.of 𝕜))] (z : Z)
      [IsDomain (cylTriplet (𝕜 := 𝕜) Z z k).tensor] (x : X),
      ResEquiv 𝕜 (prodPt (𝕜 := 𝕜) X x k) (prodPt (𝕜 := 𝕜) Z z k) ↔ ResEquiv 𝕜 x z)
    (hR' : ∀ (Z : Scheme.{0}) [Z.Over (Spec (.of 𝕜))] (z : Z)
      [IsDomain (cylTriplet (𝕜 := 𝕜) Z z k).tensor] (y : Y),
      ResEquiv 𝕜 (prodPt (𝕜 := 𝕜) Y y k) (prodPt (𝕜 := 𝕜) Z z k) ↔ ResEquiv 𝕜 y z)
    (Z : Scheme.{0}) [Z.Over (Spec (.of 𝕜))] (z : Z)
    [IsDomain (cylTriplet (𝕜 := 𝕜) Z z k).tensor] :
    cInv 𝕜 (prodPt (𝕜 := 𝕜) Z z k) (prodMap (𝕜 := 𝕜) k φ) = cInv 𝕜 z φ := by
  -- the `exDiv` analysis of the product map and of its inverse
  have hf : exDiv (prodMap (𝕜 := 𝕜) k φ) = (fun x => prodPt (𝕜 := 𝕜) X x k) '' exDiv φ :=
    Work.CY3Stab.Prod.exDiv_prodMap_eq 𝕜 k φ
  have hi : exDiv ((prodMap (𝕜 := 𝕜) k φ).symm) =
      (fun y => prodPt (𝕜 := 𝕜) Y y k) '' exDiv φ.symm := by
    rw [Work.CY3Stab.Prod.prodMap_symm 𝕜 k φ]
    exact Work.CY3Stab.Prod.exDiv_prodMap_eq 𝕜 k φ.symm
  -- injectivity of the two cylinder-point families
  have hp : Function.Injective (fun x => prodPt (𝕜 := 𝕜) X x k) := by
    intro x x' h
    exact prodPt_injective (𝕜 := 𝕜) k x x' h
  have hq : Function.Injective (fun y => prodPt (𝕜 := 𝕜) Y y k) := by
    intro y y' h
    have h1 := congrArg (Work.K3.baseChangeAlongProj (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) Y) h
    rwa [prodPt_snd, prodPt_snd] at h1
  -- the two-base counting, with the `⟸` direction supplied by the tensor transport
  exact Work.CY3Stab.Prod.cInv_prodMap_of_exDiv_image_twoBases 𝕜 k φ _ _ hf hi hp hq
    z (prodPt (𝕜 := 𝕜) Z z k)
    (fun x => hR Z z x) (fun y => hR' Z z y)

end

end Work.CY3Stab
