import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.RhoData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.



namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry

universe u

open CategoryTheory Limits AlgebraicGeometry in
/-- **`appLE` against `⊤` on both sides is `appTop`.**  A general scheme-theoretic identity used
in `chartEval_chartConst`: pulling back a global section along `f` to the open `⊤` is pulling it
back to the global sections. -/
lemma appLE_top_top {X Y : Scheme} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have h : CategoryTheory.homOfLE e = 𝟙 (⊤ : X.Opens) := Subsingleton.elim _ _
  rw [h, CategoryTheory.op_id]
  simp

open CategoryTheory Limits AlgebraicGeometry in
/-- **The chart ring map `chartEval` sends the constant sections of `chartConst` to constants.**

Pulling back the invariant regular function `chartConst C n (chartOf C n hV) k` on the chart of
`Vⁿ` along the `n` points `y` gives the scalar `algebraMap K L k`: the map `chartConst` is the
structure map `K → Γ(Cⁿ,Vⁿ)^{S_n}` of the chart, and `evalAlg` is the pullback of regular
functions along the morphism `Π_m y_m : Spec L ⟶ Cⁿ`, which is a morphism of `K`-schemes. -/
theorem chartEval_chartConst {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {L : Type u} [Field L] [Algebra K L]
    {V : C.left.Opens} (hV : IsAffineOpen V)
    (y : Fin n → Work.SpecLin.CurveFPt C L)
    (h : ⊤ ≤ (Limits.Pi.lift y : Work.SpecLin.specOf (K := K) L ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n) (k : K) :
    Work.SymQuot.DivOf.Complete.chartEval C n y h
        (Work.SymQuot.DivOf.chartConst C n (Work.SymQuot.DivOf.Complete.chartOf C n hV) k) =
      algebraMap K L k := by
  have hE : Work.SymQuot.piOpen C.toOver V n ≤
      (Work.SymQuot.prod C.toOver n).hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens) := le_top
  -- The quotient structure morphism of `Symⁿ C` is `quotientMap ≫ Symⁿ.hom`.
  have hQuot : (Work.SymQuot.symData C n).quotientMap ≫ (Work.SymQuot.Sym C n).hom
      = (Work.SymQuot.prod C.toOver n).hom := by
    rw [Work.SymQuot.Sym.hom_def, Work.SymQuot.QuotientData.quotientMap_quotientHom]
  -- The chart map of `Vⁿ` followed by the quotient map is the inclusion of `Vⁿ`.
  have hKey0 : (Work.SymQuot.DivOf.Complete.chartOf C n hV).2.1.fromSpec
        ≫ (Work.SymQuot.symData C n).quotientMap
      = Spec.map (CommRingCat.ofHom (Subring.subtype (Work.SymQuot.chartInvariants (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V))))
        ≫ (Work.SymQuot.symData C n).chartι (Work.SymQuot.DivOf.Complete.chartOf C n hV) := by
    rw [IsAffineOpen.fromSpec]
    rw [Category.assoc, Work.SymQuot.QuotientData.quotientMap_chartι]
    rw [Work.SymQuot.GAction.chartMap]
    simp only [Category.assoc, IsAffineOpen.isoSpec_inv_toSpecΓ_assoc]
    rfl
  -- ... and composing with the structure morphism of `Symⁿ C` gives the structure map of `Vⁿ`.
  have key : (Work.SymQuot.DivOf.Complete.chartOf C n hV).2.1.fromSpec
        ≫ (Work.SymQuot.prod C.toOver n).hom
      = Spec.map (CommRingCat.ofHom (Subring.subtype (Work.SymQuot.chartInvariants (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V))))
        ≫ (Work.SymQuot.symData C n).chartι (Work.SymQuot.DivOf.Complete.chartOf C n hV) ≫ (Work.SymQuot.Sym C n).hom := by
    calc (Work.SymQuot.DivOf.Complete.chartOf C n hV).2.1.fromSpec ≫ (Work.SymQuot.prod C.toOver n).hom
        = (Work.SymQuot.DivOf.Complete.chartOf C n hV).2.1.fromSpec
            ≫ ((Work.SymQuot.symData C n).quotientMap ≫ (Work.SymQuot.Sym C n).hom) := by rw [hQuot]
      _ = ((Work.SymQuot.DivOf.Complete.chartOf C n hV).2.1.fromSpec ≫ (Work.SymQuot.symData C n).quotientMap)
            ≫ (Work.SymQuot.Sym C n).hom := by rw [Category.assoc]
      _ = (Spec.map (CommRingCat.ofHom (Subring.subtype (Work.SymQuot.chartInvariants (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V))))
            ≫ (Work.SymQuot.symData C n).chartι (Work.SymQuot.DivOf.Complete.chartOf C n hV)) ≫ (Work.SymQuot.Sym C n).hom := by
          rw [hKey0]
      _ = Spec.map (CommRingCat.ofHom (Subring.subtype (Work.SymQuot.chartInvariants (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V))))
            ≫ (Work.SymQuot.symData C n).chartι (Work.SymQuot.DivOf.Complete.chartOf C n hV) ≫ (Work.SymQuot.Sym C n).hom := by
          rw [Category.assoc]
  -- The ring map of the chart inclusion is the inclusion of the invariants in the sections.
  have hA : Spec.map (CommRingCat.ofHom ((Subring.subtype (Work.SymQuot.chartInvariants (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V))).comp (Work.SymQuot.DivOf.chartConst C n (Work.SymQuot.DivOf.Complete.chartOf C n hV))))
      = (Work.SymQuot.DivOf.Complete.chartOf C n hV).2.1.fromSpec ≫ (Work.SymQuot.prod C.toOver n).hom := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← Work.SymQuot.DivOf.Complete.chartIota_comp_hom]
    exact key.symm
  -- The `K`-structure of the chart ring, read on the level of schemes.
  have hB : Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv
        ≫ ((Work.SymQuot.prod C.toOver n).hom).appLE ⊤ (Work.SymQuot.piOpen C.toOver V n) hE)
      = (Work.SymQuot.DivOf.Complete.chartOf C n hV).2.1.fromSpec ≫ (Work.SymQuot.prod C.toOver n).hom := by
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
      ← IsAffineOpen.fromSpec_top (X := Spec (CommRingCat.of K)),
      IsAffineOpen.SpecMap_appLE_fromSpec]
  -- Hence the subtype inclusion of the constants is the "structure map" of the section ring.
  have hSub : (Subring.subtype (Work.SymQuot.chartInvariants (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V))).comp (Work.SymQuot.DivOf.chartConst C n (Work.SymQuot.DivOf.Complete.chartOf C n hV))
      = (((Scheme.ΓSpecIso (CommRingCat.of K)).inv
        ≫ ((Work.SymQuot.prod C.toOver n).hom).appLE ⊤ (Work.SymQuot.piOpen C.toOver V n) hE)).hom := by
    have h2 := Spec.map_inj.mp (hA.trans hB.symm)
    exact congrArg CommRingCat.Hom.hom h2
  have hs : (Subring.subtype (Work.SymQuot.chartInvariants (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V))) (Work.SymQuot.DivOf.chartConst C n (Work.SymQuot.DivOf.Complete.chartOf C n hV) k)
      = (((Work.SymQuot.prod C.toOver n).hom).appLE ⊤ (Work.SymQuot.piOpen C.toOver V n) hE).hom (((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom k) := by
    exact congrArg (fun (f : K →+* Γ((Work.SymQuot.prod C.toOver n).left, Work.SymQuot.piOpen C.toOver V n)) => f k) hSub
  -- The pullback along `Π_m y_m` of the structure map of `Cⁿ` is the structure map of `Spec L`.
  have hCompMor : (((Work.SymQuot.prod C.toOver n).hom).appLE ⊤ (Work.SymQuot.piOpen C.toOver V n) hE)
        ≫ ((Limits.Pi.lift y).left.appLE (Work.SymQuot.piOpen C.toOver V n) ⊤ h)
      = ((Limits.Pi.lift y).left ≫ (Work.SymQuot.prod C.toOver n).hom).appTop := by
    rw [Scheme.Hom.appLE_comp_appLE, appLE_top_top]
  have hW : (Limits.Pi.lift y).left ≫ (Work.SymQuot.prod C.toOver n).hom
      = (Work.SpecLin.specOf (K := K) L).hom := Over.w (Limits.Pi.lift y)
  have hgoal : Work.SymQuot.DivOf.Complete.chartEval C n y h
        (Work.SymQuot.DivOf.chartConst C n (Work.SymQuot.DivOf.Complete.chartOf C n hV) k)
      = (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom
          (((((Work.SymQuot.prod C.toOver n).hom).appLE ⊤ (Work.SymQuot.piOpen C.toOver V n) hE)
            ≫ ((Limits.Pi.lift y).left.appLE (Work.SymQuot.piOpen C.toOver V n) ⊤ h)).hom
            (((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom k)) := by
    simp only [Work.SymQuot.DivOf.Complete.chartEval, Work.SymQuot.DivOf.evalAlg, RingHom.comp_apply]
    rw [hs]
    rfl
  rw [hgoal, hCompMor, hW]
  have hcancel : (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom k) = k := by
    have h2 := congrArg (fun (f : (CommRingCat.of K) ⟶ (CommRingCat.of K)) => CommRingCat.Hom.hom f k)
      (Iso.inv_hom_id (Scheme.ΓSpecIso (CommRingCat.of K)))
    exact h2
  have hnat : (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom
        (((Work.SpecLin.specOf (K := K) L).hom).appTop.hom (((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom k))
      = algebraMap K L ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom k)) := by
    have h := congrArg (fun (f : Γ(Spec (CommRingCat.of K), ⊤) ⟶ CommRingCat.of L) => CommRingCat.Hom.hom f (((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom k))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap K L)))
    exact h
  rw [hnat, hcancel]

end Work.SymQuot.DivOf.Complete
