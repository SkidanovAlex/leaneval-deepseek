import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Chart.quotientMap_fiber_orbit
import Submission.Work.GCBasics.Points
import Submission.Work.SymQuot.Invariants.fixedPoints_isInvariant
import Submission.Work.SymQuot.Sym.orbitAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.Sym

open CategoryTheory Limits AlgebraicGeometry


universe u

/-- The quotient map `Sym.quot C n` is invariant under the action of `S_n` on `Cⁿ`. -/
private theorem sym_quot_invariant {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ)
    (τ : Equiv.Perm (Fin n)) : (permIso C.toOver τ).hom ≫ Sym.quot C n = Sym.quot C n := by
  apply Over.OverMorphism.ext
  have h := QuotientData.quotientMap_isInvariant (symData C n) (ULift.up τ)
  rw [Sym.quot_left]
  simp only [Over.comp_left]
  exact h

/-- Precomposing the `n`-fold sum map with a permutation of the points only permutes the
summands. -/
private theorem powMap_comp_perm {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ)
    {F : Type u} [Field F] [Algebra K F] (x y : Fin n → Work.GCBasics.FPt C.toOver F)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ m, y m = x (σ m)) :
    Sym.powMap C n x = Sym.powMap C n y := by
  simp only [Sym.powMap]
  have hlift : Limits.Pi.lift y = Limits.Pi.lift x ≫ (permIso C.toOver σ⁻¹).hom := by
    apply Limits.Pi.hom_ext
    intro m
    rw [Category.assoc, Product.permIso_hom_proj, Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π]
    rw [hσ m, Equiv.Perm.inv_def, Equiv.symm_symm]
  rw [hlift, Category.assoc, sym_quot_invariant]

/-- The hom-level orbit statement in the fixed-subring form: two ring maps out of `B` which agree
on the fixed subring `B^G` of a finite group action differ by an element of `G`. -/
private theorem orbit_of_fixedPointsHoms {B : Type u} [CommRing B] (G : Type u) [Group G]
    [Finite G] [MulSemiringAction G B] {F : Type u} [Field F] (φ ψ : B →+* F)
    (h : ∀ a : FixedPoints.subring B G, φ a.1 = ψ a.1) :
    ∃ g : G, ∀ b : B, ψ b = φ (g • b) := by
  haveI : Algebra.IsInvariant (FixedPoints.subring B G) B G :=
    Work.SymQuot.Invariants.fixedPoints_isInvariant
  haveI : SMulCommClass G (FixedPoints.subring B G) B :=
    ⟨fun g a b => by
      change g • (a.1 * b) = a.1 * (g • b)
      rw [smul_mul', (Work.SymQuot.mem_fixedPoints_iff.mp a.2) g]⟩
  letI : Algebra (FixedPoints.subring B G) F :=
    (φ.comp (FixedPoints.subring B G).subtype).toAlgebra
  have hmap : (algebraMap (FixedPoints.subring B G) F)
      = (φ.comp (FixedPoints.subring B G).subtype) := by
    first
      | exact RingHom.algebraMap_toAlgebra (φ.comp (FixedPoints.subring B G).subtype)
      | rfl
  have key : ∀ a : FixedPoints.subring B G,
      (algebraMap (FixedPoints.subring B G) F) a = φ (a : B) :=
    fun a => congrFun (congrArg (fun f : FixedPoints.subring B G →+* F =>
      (f : FixedPoints.subring B G → F)) hmap) a
  have keyB : ∀ a : FixedPoints.subring B G,
      (algebraMap (FixedPoints.subring B G) B) a = (a : B) := fun a => rfl
  obtain ⟨g, hg⟩ := Work.SymQuot.Sym.orbitAux (A := FixedPoints.subring B G) G
    ({ toRingHom := φ, commutes' := fun a => (congrArg φ (keyB a)).trans (key a).symm } :
      B →ₐ[FixedPoints.subring B G] F)
    ({ toRingHom := ψ, commutes' := fun a =>
        (congrArg ψ (keyB a)).trans ((h a).symm.trans (key a).symm) } :
      B →ₐ[FixedPoints.subring B G] F)
  exact ⟨g, fun b => hg b⟩

theorem powMap_eq_iff_exists_perm {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) {F : Type u} [Field F] [Algebra K F] (x y : Fin n → Work.GCBasics.FPt C.toOver F) : Work.SymQuot.Sym.powMap C n x = Work.SymQuot.Sym.powMap C n y ↔ ∃ σ : Equiv.Perm (Fin n), ∀ m, y m = x (σ m) := by
  constructor
  · intro h
    set a : Work.GCBasics.FPt (prod C.toOver n) F := Limits.Pi.lift x with ha
    set b : Work.GCBasics.FPt (prod C.toOver n) F := Limits.Pi.lift y with hb
    have hq : a ≫ Sym.quot C n = b ≫ Sym.quot C n := by
      rw [ha, hb]
      simpa only [Sym.powMap] using h
    have hql : a.left ≫ (symData C n).quotientMap = b.left ≫ (symData C n).quotientMap := by
      have h1 := congrArg Over.Hom.left hq
      simpa only [Over.comp_left, Sym.quot_left] using h1
    have hpt : (symData C n).quotientMap (a.left (IsLocalRing.closedPoint F))
        = (symData C n).quotientMap (b.left (IsLocalRing.closedPoint F)) := by
      have h2 := congrArg (fun f : (Work.GCBasics.specOf K F).left ⟶ (symData C n).Quotient =>
        f (IsLocalRing.closedPoint F)) hql
      simpa only [Scheme.Hom.comp_apply] using h2
    obtain ⟨g, hg⟩ := (Work.SymQuot.GAction.mem_orbit_iff (symData C n).action).mp
      (Work.SymQuot.Chart.quotientMap_fiber_orbit (symData C n) hpt)
    obtain ⟨U, hUaff, hUinv, hxU⟩ := (symData C n).covers (a.left (IsLocalRing.closedPoint F))
    have hyU : b.left (IsLocalRing.closedPoint F) ∈ U := by
      rw [← hg]
      exact hUinv.smul_mem hxU g
    obtain ⟨a', ha', _⟩ := Work.GCBasics.FPt.factor_of_landsIn U a hxU
    obtain ⟨b', hb', _⟩ := Work.GCBasics.FPt.factor_of_landsIn U b hyU
    have ha_left : a.left = a'.left ≫ U.ι := by
      have h1 : (a' ≫ Work.GCBasics.Opens.ιOver U).left = a.left := congrArg Over.Hom.left ha'
      simpa only [Over.comp_left, Work.GCBasics.Opens.ιOver_left] using h1.symm
    have hb_left : b.left = b'.left ≫ U.ι := by
      have h1 : (b' ≫ Work.GCBasics.Opens.ιOver U).left = b.left := congrArg Over.Hom.left hb'
      simpa only [Over.comp_left, Work.GCBasics.Opens.ιOver_left] using h1.symm
    have hchart : a'.left ≫ (symData C n).action.chartMap U hUinv
        = b'.left ≫ (symData C n).action.chartMap U hUinv := by
      have key : (a'.left ≫ (symData C n).action.chartMap U hUinv)
            ≫ (symData C n).chartι ⟨U, hUaff, hUinv⟩
          = (b'.left ≫ (symData C n).action.chartMap U hUinv)
            ≫ (symData C n).chartι ⟨U, hUaff, hUinv⟩ := by
        have h1 : (a'.left ≫ U.ι) ≫ (symData C n).quotientMap
            = (b'.left ≫ U.ι) ≫ (symData C n).quotientMap := by
          rw [← ha_left, ← hb_left]
          exact hql
        rw [Category.assoc, Category.assoc,
          QuotientData.quotientMap_chartι (symData C n) ⟨U, hUaff, hUinv⟩] at h1
        rw [← Category.assoc, ← Category.assoc] at h1
        exact h1
      exact (cancel_mono ((symData C n).chartι ⟨U, hUaff, hUinv⟩)).mp key
    -- ring maps attached to a' and b'
    letI : MulSemiringAction (ULift.{u} (Equiv.Perm (Fin n))) Γ((prod C.toOver n).left, U) :=
      (symData C n).action.sectionMulSemiringAction U hUinv
    let A : Subring Γ((prod C.toOver n).left, U) :=
      FixedPoints.subring Γ((prod C.toOver n).left, U) (ULift.{u} (Equiv.Perm (Fin n)))
    let ca : (Work.GCBasics.specOf K F).left ⟶ Spec Γ((prod C.toOver n).left, U) :=
      a'.left ≫ hUaff.isoSpec.hom
    let cb : (Work.GCBasics.specOf K F).left ⟶ Spec Γ((prod C.toOver n).left, U) :=
      b'.left ≫ hUaff.isoSpec.hom
    let φ : Γ((prod C.toOver n).left, U) →+* F := (Spec.preimage ca).hom
    let ψ : Γ((prod C.toOver n).left, U) →+* F := (Spec.preimage cb).hom
    have hchart' : ca ≫ Spec.map (CommRingCat.ofHom (Subring.subtype A))
        = cb ≫ Spec.map (CommRingCat.ofHom (Subring.subtype A)) := by
      have hh := hchart
      simp only [Work.SymQuot.GAction.chartMap, IsAffineOpen.isoSpec_hom,
        Work.SymQuot.GAction.invariants, ca, cb, Category.assoc] at hh
      exact hh
    have hpre : CommRingCat.ofHom (Subring.subtype A) ≫ Spec.preimage ca
        = CommRingCat.ofHom (Subring.subtype A) ≫ Spec.preimage cb := by
      have h1 := congrArg Spec.preimage hchart'
      rwa [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map] at h1
    have hφψ : ∀ a : A, φ a.1 = ψ a.1 := by
      intro a
      have h3 := congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of F => f a) hpre
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h3
      simpa only [φ, ψ, CommRingCat.hom_ofHom, Subring.subtype_apply] using h3
    obtain ⟨g', hg'⟩ := orbit_of_fixedPointsHoms (ULift.{u} (Equiv.Perm (Fin n))) φ ψ hφψ
    -- conclude
    have hg'' : ∀ b : Γ((prod C.toOver n).left, U),
        ψ b = φ (Work.SymQuot.GAction.sectionHom (symData C n).action U hUinv g'⁻¹ b) := by
      intro b
      have hb : g' • b = Work.SymQuot.GAction.sectionHom (symData C n).action U hUinv g'⁻¹ b :=
        rfl
      exact (hg' b).trans (congrArg φ hb)
    have hψφ : ψ = φ.comp (Work.SymQuot.GAction.sectionHom (symData C n).action U hUinv g'⁻¹) :=
      RingHom.ext (fun b => hg'' b)
    have hcb : cb = ca ≫ Spec.map (CommRingCat.ofHom
        (Work.SymQuot.GAction.sectionHom (symData C n).action U hUinv g'⁻¹)) := by
      apply Spec.preimage_injective
      rw [Spec.preimage_comp, Spec.preimage_map]
      rw [show Spec.preimage cb = CommRingCat.ofHom ψ from rfl,
        show Spec.preimage ca = CommRingCat.ofHom φ from rfl, ← CommRingCat.ofHom_comp]
      exact congrArg CommRingCat.ofHom hψφ
    have hnatural : hUaff.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
          (Work.SymQuot.GAction.sectionHom (symData C n).action U hUinv g'⁻¹))
        = ((symData C n).action.hom g'⁻¹).resLE U U (le_of_eq (hUinv g'⁻¹).symm)
            ≫ hUaff.isoSpec.hom := by
      rw [IsAffineOpen.isoSpec_hom]
      exact Scheme.Opens.toSpecΓ_SpecMap_appLE ((symData C n).action.hom g'⁻¹) U U
        (le_of_eq (hUinv g'⁻¹).symm)
    have hb'left : b'.left = a'.left ≫ ((symData C n).action.hom g'⁻¹).resLE U U
        (le_of_eq (hUinv g'⁻¹).symm) := by
      have h1 : b'.left ≫ hUaff.isoSpec.hom = (a'.left ≫ hUaff.isoSpec.hom) ≫ Spec.map
          (CommRingCat.ofHom (Work.SymQuot.GAction.sectionHom (symData C n).action U hUinv g'⁻¹)) :=
        hcb
      have h2 : (a'.left ≫ hUaff.isoSpec.hom) ≫ Spec.map (CommRingCat.ofHom
            (Work.SymQuot.GAction.sectionHom (symData C n).action U hUinv g'⁻¹))
          = (a'.left ≫ ((symData C n).action.hom g'⁻¹).resLE U U
              (le_of_eq (hUinv g'⁻¹).symm)) ≫ hUaff.isoSpec.hom := by
        rw [Category.assoc, hnatural, Category.assoc]
      have h3 : b'.left ≫ hUaff.isoSpec.hom
          = (a'.left ≫ ((symData C n).action.hom g'⁻¹).resLE U U
              (le_of_eq (hUinv g'⁻¹).symm)) ≫ hUaff.isoSpec.hom := h1.trans h2
      first
        | exact (cancel_epi hUaff.isoSpec.hom).mp h3
        | exact (cancel_mono hUaff.isoSpec.hom).mp h3
        | (have h4 := congrArg (fun f => f ≫ hUaff.isoSpec.inv) h3
           rw [Category.assoc, Category.assoc, hUaff.isoSpec.hom_inv_id, Category.comp_id] at h4
           exact h4)
    have hbl : b.left = a.left ≫ (permIso C.toOver ((g'⁻¹).down)).hom.left := by
      rw [hb_left, ha_left, hb'left, Category.assoc, Category.assoc]
      rw [Scheme.Hom.resLE_comp_ι]
      rfl
    refine ⟨((g'⁻¹).down).symm, fun m => ?_⟩
    have hylift : Limits.Pi.lift y = Limits.Pi.lift x ≫ (permIso C.toOver ((g'⁻¹).down)).hom := by
      rw [← ha, ← hb]
      apply Over.OverMorphism.ext
      exact hbl
    calc y m = Limits.Pi.lift y ≫ (proj C.toOver n m) := (Limits.Pi.lift_comp_π y m).symm
      _ = (Limits.Pi.lift x ≫ (permIso C.toOver ((g'⁻¹).down)).hom) ≫ (proj C.toOver n m) := by
            rw [hylift]
      _ = Limits.Pi.lift x ≫ ((permIso C.toOver ((g'⁻¹).down)).hom ≫ (proj C.toOver n m)) := by
            rw [Category.assoc]
      _ = Limits.Pi.lift x ≫ (proj C.toOver n (((g'⁻¹).down).symm m)) := by
            rw [Product.permIso_hom_proj]
      _ = x (((g'⁻¹).down).symm m) := Limits.Pi.lift_comp_π x (((g'⁻¹).down).symm m)
  · rintro ⟨σ, hσ⟩
    exact powMap_comp_perm C n x y σ hσ

end Work.SymQuot.Sym
