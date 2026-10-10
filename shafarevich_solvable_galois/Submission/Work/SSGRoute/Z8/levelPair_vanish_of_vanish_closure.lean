import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E7bZ8Step2Aux2
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.e6_util
import Submission.Work.SSGRoute.levelPair_comp_extHMap
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.Work.SSGRoute.localUnits_infl_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Z8

open SSGRoute.PTExt CategoryTheory

/-- **Vanishing of the local pairing at a level descends from a Galois closure.**

If the level pairing at the closure `Lc / k'` vanishes (for every compatible choice of level
data), then it vanishes at the intermediate level `L / k'`.  The proof identifies the level-`L`
pairing as the restriction of the level-`Lc` pairing along `Gal(Lc/k') ↠ Gal(L/k')` — the
pairing-inflation identity `levelPair_comp_extHMap` — and uses that the local inflation
`H²(D_{w'}, L_{w'}ˣ) → H²(D_{wc}, Lc_{wc}ˣ)` is injective (`localUnits_infl_injective`). -/
theorem levelPair_vanish_of_vanish_closure (k' K : Type) [Field k'] [NumberField k'] [Field K]
    [NumberField K] [Algebra k' K] [FiniteDimensional k' K] [IsGalois k' K]
    (w : NK.GlobalCFT.Place K) (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k'] K))
    (y : CategoryTheory.Abelian.Ext (Rep.res (SSGRoute.PTExt.decompK (k := k') w).subtype M)
      (SSGRoute.PTExt.localUnitsK (k := k') w) 1)
    (L : Type) [Field L] [NumberField L] [Algebra k' L] [Algebra K L] [IsScalarTower k' K L]
      [FiniteDimensional k' L] [IsGalois k' L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (Lc : Type) [Field Lc] [NumberField Lc] [Algebra k' Lc] [Algebra K Lc] [Algebra L Lc]
      [IsScalarTower k' K Lc] [IsScalarTower k' L Lc] [IsScalarTower K L Lc]
      [FiniteDimensional L Lc] [FiniteDimensional k' Lc] [IsGalois k' Lc]
    (wc : NK.GlobalCFT.Place Lc) (hwc : NK.GlobalCFT.Place.LiesOver wc w')
    (hwc' : NK.GlobalCFT.Place.LiesOver wc w) :
    (∀ (fc : MulAction.stabilizer (Lc ≃ₐ[k'] Lc) wc →* SSGRoute.PTExt.decompK (k := k') w)
      (hfc : ∀ σ, ((fc σ : SSGRoute.PTExt.decompK (k := k') w) : K ≃ₐ[k'] K)
        = SSGRoute.PTExt.galRes k' K Lc (σ : Lc ≃ₐ[k'] Lc))
      (ιc : Rep.res fc (SSGRoute.PTExt.localUnitsK (k := k') w)
        ⟶ NK.HassePrinciple.localUnitsRep k' Lc wc)
      (hιc : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ, ιc.hom (Additive.ofMul u)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits wc w hwc' u))
      (hc : SSGRoute.PTExt.extH (Rep.res fc
        (Rep.res (SSGRoute.PTExt.decompK (k := k') w).subtype M)) 1),
      SSGRoute.PTExt.levelPair fc ιc y hc = 0) →
    ∀ (f : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* SSGRoute.PTExt.decompK (k := k') w)
      (hf : ∀ σ, ((f σ : SSGRoute.PTExt.decompK (k := k') w) : K ≃ₐ[k'] K)
        = SSGRoute.PTExt.galRes k' K L (σ : L ≃ₐ[k'] L))
      (ι : Rep.res f (SSGRoute.PTExt.localUnitsK (k := k') w)
        ⟶ NK.HassePrinciple.localUnitsRep k' L w')
      (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ, ι.hom (Additive.ofMul u)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
      (h : SSGRoute.PTExt.extH (Rep.res f
        (Rep.res (SSGRoute.PTExt.decompK (k := k') w).subtype M)) 1),
      SSGRoute.PTExt.levelPair f ι y h = 0 := by
  intro hyp f hf ι hι h
  -- The restriction of Galois groups `Gal(Lc/k') →* Gal(L/k')`.
  obtain ⟨g, hg⟩ := Work.SSGRoute.decompK_restrict_exists (k := k') (K := L) (L := Lc)
    w' wc hwc
  -- The canonical local units map `L_{w'}ˣ → Lc_{wc}ˣ`.
  obtain ⟨ι₁, hι₁⟩ := Work.SSGRoute.localUnitsMap_exists (k := k') (K := L) (L := Lc)
    w' wc hwc g hg
  -- The composite group map `Gal(Lc/k') →* D_w`, which satisfies the top-level coherence.
  have hfc : ∀ σ : MulAction.stabilizer (Lc ≃ₐ[k'] Lc) wc,
      (((f.comp g) σ : SSGRoute.PTExt.decompK (k := k') w) : K ≃ₐ[k'] K)
        = SSGRoute.PTExt.galRes k' K Lc (σ : Lc ≃ₐ[k'] Lc) := by
    intro σ
    rw [MonoidHom.comp_apply, hf (g σ), hg σ]
    exact SSGRoute.PTExt.galRes_trans (k := k') (K := K) (L := L) (L' := Lc)
      (σ : Lc ≃ₐ[k'] Lc)
  -- The canonical coefficient map `K_wˣ → Lc_{wc}ˣ` at the top level.
  obtain ⟨ιc, hιc⟩ := Work.SSGRoute.localUnitsMap_exists (k := k') (K := K) (L := Lc)
    w wc hwc' (f.comp g) hfc
  -- It agrees with the composite `K_wˣ → L_{w'}ˣ → Lc_{wc}ˣ`.
  have hcomp : Rep.resMap g ι ≫ ι₁ = ιc :=
    Work.SSGRoute.localAlgebraMapUnits_comp_rep (k := k') (K := K) (L := L) (L' := Lc)
      w w' wc hw' hwc hwc' f g ι hι ι₁ hι₁ ιc hιc
  -- The pairing-inflation identity at the two levels.
  have hZ1 :=
    Work.SSGRoute.levelPair_comp_extHMap (G₁ := MulAction.stabilizer (L ≃ₐ[k'] L) w')
      (G := MulAction.stabilizer (Lc ≃ₐ[k'] Lc) wc)
      (D := SSGRoute.PTExt.decompK (k := k') w) f g
      (M := Rep.res (SSGRoute.PTExt.decompK (k := k') w).subtype M)
      (A := SSGRoute.PTExt.localUnitsK (k := k') w)
      (B₁ := SSGRoute.PTExt.localUnitsK (k := k') w')
      (B := NK.HassePrinciple.localUnitsRep k' Lc wc) ι ι₁ (r := 1) (s := 1) y h
  -- The vanishing hypothesis at the closure.
  have hzero : SSGRoute.PTExt.levelPair (f.comp g) ιc y
      (SSGRoute.PTExt.extHMap g (𝟙 _) h) = 0 :=
    hyp (f.comp g) hfc ιc hιc (SSGRoute.PTExt.extHMap g (𝟙 _) h)
  -- Hence the image of the level-`L` pairing under injective inflation is zero.
  have h2 : SSGRoute.PTExt.extHMap g ι₁ (SSGRoute.PTExt.levelPair f ι y h) = 0 := by
    rw [← hZ1, hcomp]
    exact hzero
  -- Injective inflation of local units classes.
  have hinj : Function.Injective
      (fun x : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k') w') 2 =>
        SSGRoute.PTExt.extHMap g ι₁ x) :=
    Work.SSGRoute.localUnits_infl_injective (k := k') (K := L) w' (L := Lc) (w' := wc)
      hwc g hg ι₁ hι₁
  exact hinj (h2.trans (Work.SSGRoute.E6Util.extHMap_zero g ι₁).symm)

end Work.SSGRoute.Z8
