import Mathlib
import Submission.Work.CWIND.Basic
import Submission.Work.CWIND.GClass.MVDefs
import Submission.Work.CWIND.GClass.MVRows

namespace Work.CWIND.GClass

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

/-- **CWIND/T8 (the Mayer–Vietoris field of the CW induction).**  If `X` is Hausdorff and
`U, V ⊆ X` are open with `U ∪ V = X`, and the three spaces `U`, `V`, `U ∩ V` lie in `GOf b`, then
so does `X` — REFS/05 section 2.  There are three short exact rows of complexes:
`0 → C(U∩V) → C(U) ⊕ C(V) → C^{UV}(X) → 0` (whose last map is a quasi-isomorphism by the singular
Mayer–Vietoris input `SingMVProp`), the analogous row for `A` (exact degreewise because
`(U∩V)^{Δⁿ} = U^{Δⁿ} ∩ V^{Δⁿ}` inside `X^{Δⁿ}`), and `0 → ℤ[U∩V] → ℤ[U] ⊕ ℤ[V] → ℤ[X] → 0`
(`CondMVProp`).  The map `b` is a morphism from the first row to the second and `a` from the third
to the second; the two-out-of-three fields of `ToolkitProp` then show that `a^{UV}(X)` and
`b^{UV}(X)` are solid-equivalences, and naturality of `a` and `b` (together with the quasi-isomorphism
`C^{UV}(X) → C(X)`) identifies `b(X)` with `[A^{UV} → A] ∘ b^{UV}(X) ∘ [C^{UV} → C]⁻¹` in the derived
category.  The hypotheses record the solid-equivalences of `a` at Hausdorff spaces (from
`CWIND/AFun/aNat_solidEquiv`). -/
theorem G_mv (hTK : ToolkitProp) (hCondMV : CondMVProp) (hSingMV : SingMVProp)
    (a : freeLightCondAbOfTopFunctor ⋙ (CochainComplex.singleFunctor LightCondAb 0) ⟶ AFunctor)
    (hA : ∀ (Y : TopCat.{0}) [T2Space Y], SolidEquiv ((DerivedCategory.Q).map (a.app Y)))
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor)
    (X : TopCat.{0}) [T2Space X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ)
    (hGU : GOf b (TopCat.of U)) (hGV : GOf b (TopCat.of V)) (hGUV : GOf b (TopCat.of (U ∩ V : Set X))) :
    GOf b X :=
  GOf_mv hTK hCondMV hSingMV a hA b X U V hU hV hUV hGU hGV hGUV

end Work.CWIND.GClass
