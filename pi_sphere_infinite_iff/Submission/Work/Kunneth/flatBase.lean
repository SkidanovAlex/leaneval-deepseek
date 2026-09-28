import Mathlib
import Submission.Work.Kunneth.FlatDefs

/-!
# Flat base change for the `(p,q)`-summand of the homological Künneth computation

For a chain complex `C` of `ℤ`-modules and a family `M` of *flat* `ℤ`-modules, the `(p,q)`-summand
of the homological Künneth computation is

`ker (∂_p ⊗ 1) ⧸ im (∂_{p+1} ⊗ 1) ≅ H_p(C) ⊗_ℤ M q`,

compatibly with the generators: the class of `iCycles u ⊗ m` (for a cycle `u` of `C` and
`m ∈ M q`) corresponds to `[u] ⊗ m` (`Work.Kunneth.flatBase`).

The proof is the classical flat base change in two steps.

* Flatness of `M q` makes tensoring with `M q` preserve the exact sequence `0 → Z_p → C_p → C_{p-1}`
  (`Z_p` the cycles): the kernel of `∂_p ⊗ 1` is the image of `Z_p ⊗ M q`
  (`Work.Kunneth.range_rTensor_cycKer_subtype`), and, by injectivity of `Z_p ⊗ M q → C_p ⊗ M q`
  (`Work.Kunneth.injective_rTensor_cycKer_subtype`), the comparison `Work.Kunneth.fbBase` is
  `Z_p ⊗ M q ≅ ker (∂_p ⊗ 1)`.  The image of `∂_{p+1} ⊗ 1` corresponds to the image of
  `B_p ⊗ M q` for the boundaries `B_p` (`Work.Kunneth.range_hDOut_eq`,
  `Work.Kunneth.mem_fbKout_iff`), which yields `Work.Kunneth.fbQuotEquiv`.
* Right exactness of the tensor product gives
  `(Z_p ⊗ M q) ⧸ im (B_p ⊗ M q) ≅ (Z_p ⧸ B_p) ⊗ M q` (`Work.Kunneth.fbQuotCycEquiv`), and
  `Z_p ⧸ B_p ≅ H_p(C)` is `Work.Kunneth.homQuotIso`, packaged as the linear equivalence
  `Work.Kunneth.fbHomQuotEquiv` (`Work.Kunneth.fbHomQuotEquiv_apply_mk`).

The main theorem `Work.Kunneth.flatBase` assembles these (`Work.Kunneth.fbIsoLin`,
`Work.Kunneth.fbIsoLin_hQuotOf`) and computes the value of the resulting isomorphism on the
generators `hQuotOf C M p q u m h ↦ hHTensOf C M p q u m`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

abbrev fbKin (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ) (p q : ℕ) :
    Submodule ℤ ↥(C.X p ⊗ (sumShift M).X q) :=
  LinearMap.ker (hDIn C M p q)

abbrev fbKout (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ) (p q : ℕ) :
    Submodule ℤ ↥(C.X p ⊗ (sumShift M).X q) :=
  LinearMap.range (hDOut C M p q)

abbrev fbK1 (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ) (p q : ℕ) :
    Submodule ℤ ↥(fbKin C M p q) :=
  (fbKout C M p q).comap (fbKin C M p q).subtype

abbrev fbCycT (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ) (p q : ℕ) : Type :=
  ↥(cycKer C p) ⊗[ℤ] ↥((sumShift M).X q)

abbrev fbQ (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ) (p q : ℕ) :
    Submodule ℤ (fbCycT C M p q) :=
  LinearMap.range (LinearMap.rTensor ↥((sumShift M).X q) (homBnd C p).subtype)

abbrev fbKinQ (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ) (p q : ℕ) : Type :=
  ↥(fbKin C M p q) ⧸ fbK1 C M p q

abbrev fbCycQ (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ) (p q : ℕ) : Type :=
  fbCycT C M p q ⧸ fbQ C M p q

theorem range_rTensor_cycKer_subtype (C : ChainComplex (ModuleCat ℤ) ℕ)
    (M : ℕ → ModuleCat ℤ) (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ) :
    (LinearMap.rTensor ↥((sumShift M).X q) (Submodule.subtype (cycKer C p))).range
      = fbKin C M p q := by
  haveI : Module.Flat ℤ ↥((sumShift M).X q) := hT
  have hfg : Function.Exact ⇑(Submodule.subtype (cycKer C p)) ⇑((C.d p (p - 1)).hom) := by
    refine LinearMap.exact_iff.mpr ?_
    rw [Submodule.range_subtype]
    rfl
  have hex := Module.Flat.rTensor_exact (R := ℤ) (M := ↥((sumShift M).X q)) hfg
  rw [LinearMap.exact_iff] at hex
  exact hex.symm

theorem injective_rTensor_cycKer_subtype (C : ChainComplex (ModuleCat ℤ) ℕ)
    (M : ℕ → ModuleCat ℤ) (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ) :
    Function.Injective
      (LinearMap.rTensor ↥((sumShift M).X q) (Submodule.subtype (cycKer C p))) := by
  haveI : Module.Flat ℤ ↥((sumShift M).X q) := hT
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

def fbBase (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ) :
    fbCycT C M p q ≃ₗ[ℤ] ↥(fbKin C M p q) :=
  LinearEquiv.ofBijective
    ((LinearMap.rTensor ↥((sumShift M).X q) (Submodule.subtype (cycKer C p))).codRestrict
        (fbKin C M p q)
        (fun y => by
          rw [← range_rTensor_cycKer_subtype C M q hT p]
          exact ⟨y, rfl⟩))
    ⟨fun x y hxy =>
        injective_rTensor_cycKer_subtype C M q hT p (Subtype.ext_iff.mp hxy),
     fun y => by
        obtain ⟨x, hx⟩ := (LinearMap.mem_range.mp (show y.1 ∈
          (LinearMap.rTensor ↥((sumShift M).X q) (Submodule.subtype (cycKer C p))).range from by
            rw [range_rTensor_cycKer_subtype C M q hT p]
            exact y.2))
        exact ⟨x, Subtype.ext hx⟩⟩

theorem fbBase_apply_val (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ) (y : fbCycT C M p q) :
    ((fbBase C M q hT p y : ↥(fbKin C M p q)) : ↥(C.X p ⊗ (sumShift M).X q))
      = LinearMap.rTensor ↥((sumShift M).X q) (Submodule.subtype (cycKer C p)) y := by
  rw [fbBase, LinearEquiv.ofBijective_apply, LinearMap.codRestrict_apply]
  rfl

/-- The inverse of `fbBase` composed with it is the identity (in the `LinearMap` spelling
used when composing below). -/
theorem fbBase_symm_apply_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ) (v : fbCycT C M p q) :
    ((fbBase C M q hT p).symm : ↥(fbKin C M p q) →ₗ[ℤ] fbCycT C M p q)
      ((fbBase C M q hT p) v) = v := by
  rw [show ((fbBase C M q hT p).symm : ↥(fbKin C M p q) →ₗ[ℤ] fbCycT C M p q)
        ((fbBase C M q hT p) v)
      = (fbBase C M q hT p).symm ((fbBase C M q hT p) v) from rfl,
    LinearEquiv.symm_apply_apply]

/-- **The inverse of `fbBase` on a generator.** -/
theorem fbBase_symm_apply_tmul (C : ChainComplex (ModuleCat ℤ) ℕ)
    (M : ℕ → ModuleCat ℤ) (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ)
    (a : ↥(C.X p)) (ha : a ∈ cycKer C p) (t : ↥((sumShift M).X q))
    (hh : a ⊗ₜ[ℤ] t ∈ fbKin C M p q) :
    ((fbBase C M q hT p).symm : ↥(fbKin C M p q) →ₗ[ℤ] fbCycT C M p q)
        ⟨a ⊗ₜ[ℤ] t, hh⟩ = ⟨a, ha⟩ ⊗ₜ[ℤ] t := by
  rw [show ((fbBase C M q hT p).symm : ↥(fbKin C M p q) →ₗ[ℤ] fbCycT C M p q)
        ⟨a ⊗ₜ[ℤ] t, hh⟩
      = (fbBase C M q hT p).symm ⟨a ⊗ₜ[ℤ] t, hh⟩ from rfl]
  apply (fbBase C M q hT p).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [fbBase_apply_val, LinearMap.rTensor_tmul]
  rfl

theorem range_hDOut_eq (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ) (p q : ℕ) :
    fbKout C M p q
      = (LinearMap.rTensor ↥((sumShift M).X q)
          ((Submodule.subtype (cycKer C p)).comp (homBnd C p).subtype)).range := by
  have hz : ∀ x : ↥(C.X (p + 1)), (C.d p (p - 1)).hom ((C.d (p + 1) p) x) = 0 := by
    intro x
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d C (p + 1) p (p - 1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x
  let f : ↥(C.X (p + 1)) →ₗ[ℤ] ↥(cycKer C p) :=
    ((C.d (p + 1) p).hom).codRestrict (cycKer C p) hz
  let dc : ↥(C.X (p + 1)) →ₗ[ℤ] ↥(homBnd C p) :=
    f.codRestrict (homBnd C p) (fun x => (mem_homBnd_iff C p (f x)).mpr ⟨x, rfl⟩)
  have hcomp : ((Submodule.subtype (cycKer C p)).comp (homBnd C p).subtype).comp dc
      = (C.d (p + 1) p).hom := by
    ext x
    rfl
  have hdc : Function.Surjective ⇑dc := by
    intro b
    obtain ⟨w, hw⟩ := (mem_homBnd_iff C p b).mp b.2
    exact ⟨w, Subtype.ext (Subtype.ext hw)⟩
  show (LinearMap.rTensor ↥((sumShift M).X q) ((C.d (p + 1) p).hom)).range = _
  rw [← hcomp, LinearMap.rTensor_comp,
    LinearMap.range_comp (LinearMap.rTensor ↥((sumShift M).X q) dc)
      (LinearMap.rTensor ↥((sumShift M).X q)
        ((Submodule.subtype (cycKer C p)).comp (homBnd C p).subtype)),
    LinearMap.range_eq_top.mpr (LinearMap.rTensor_surjective _ hdc), Submodule.map_top]

theorem mem_fbKout_iff (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ)
    (y : ↥(fbKin C M p q)) :
    (y : ↥(C.X p ⊗ (sumShift M).X q)) ∈ fbKout C M p q
      ↔ (fbBase C M q hT p).symm y ∈ fbQ C M p q := by
  have h1 : ∀ y : ↥(fbKin C M p q),
      (y : ↥(C.X p ⊗ (sumShift M).X q))
        = LinearMap.rTensor ↥((sumShift M).X q) (Submodule.subtype (cycKer C p))
            ((fbBase C M q hT p).symm y) := by
    intro y
    rw [← fbBase_apply_val C M q hT p ((fbBase C M q hT p).symm y),
      LinearEquiv.apply_symm_apply]
  have hβ : LinearMap.rTensor ↥((sumShift M).X q)
        ((Submodule.subtype (cycKer C p)).comp (homBnd C p).subtype)
      = (LinearMap.rTensor ↥((sumShift M).X q) (Submodule.subtype (cycKer C p))).comp
          (LinearMap.rTensor ↥((sumShift M).X q) (homBnd C p).subtype) :=
    LinearMap.rTensor_comp _ _ _
  show (y : ↥(C.X p ⊗ (sumShift M).X q)) ∈ fbKout C M p q
      ↔ (fbBase C M q hT p).symm y
          ∈ (LinearMap.rTensor ↥((sumShift M).X q) (homBnd C p).subtype).range
  rw [range_hDOut_eq C M p q]
  constructor
  · intro hy
    obtain ⟨w, hw⟩ := hy
    refine ⟨w, ?_⟩
    have hw' : LinearMap.rTensor ↥((sumShift M).X q)
          ((Submodule.subtype (cycKer C p)).comp (homBnd C p).subtype) w
        = LinearMap.rTensor ↥((sumShift M).X q) (Submodule.subtype (cycKer C p))
            (LinearMap.rTensor ↥((sumShift M).X q) (homBnd C p).subtype w) := by
      rw [hβ]
      rfl
    refine injective_rTensor_cycKer_subtype C M q hT p ?_
    rw [← hw', hw, h1 y]
  · intro hy
    obtain ⟨w, hw⟩ := hy
    refine ⟨w, ?_⟩
    have hw' : LinearMap.rTensor ↥((sumShift M).X q)
          ((Submodule.subtype (cycKer C p)).comp (homBnd C p).subtype) w
        = LinearMap.rTensor ↥((sumShift M).X q) (Submodule.subtype (cycKer C p))
            (LinearMap.rTensor ↥((sumShift M).X q) (homBnd C p).subtype w) := by
      rw [hβ]
      rfl
    rw [hw', hw, h1 y]

def fbQuotMap (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ) :
    fbKinQ C M p q →ₗ[ℤ] fbCycQ C M p q :=
  Submodule.liftQ (fbK1 C M p q)
    ((Submodule.mkQ (fbQ C M p q)).comp
      ((fbBase C M q hT p).symm : ↥(fbKin C M p q) →ₗ[ℤ] fbCycT C M p q))
    (fun z hz => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact (mem_fbKout_iff C M q hT p z).mp (Submodule.mem_comap.mp hz))

theorem fbQuotMap_apply_mk (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ) (z : ↥(fbKin C M p q)) :
    fbQuotMap C M q hT p (Submodule.Quotient.mk z)
      = Submodule.Quotient.mk
          (((fbBase C M q hT p).symm : ↥(fbKin C M p q) →ₗ[ℤ] fbCycT C M p q) z) := by
  simp only [fbQuotMap, Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply]

def fbQuotEquiv (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ) :
    fbKinQ C M p q ≃ₗ[ℤ] fbCycQ C M p q := by
  refine LinearEquiv.ofBijective (fbQuotMap C M q hT p) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker] at ha
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (fbK1 C M p q) a
    rw [Submodule.mkQ_apply] at ha
    rw [fbQuotMap_apply_mk, Submodule.Quotient.mk_eq_zero] at ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_comap.mpr ((mem_fbKout_iff C M q hT p z).mpr ha)
  · intro w
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (fbQ C M p q) w
    refine ⟨Submodule.Quotient.mk ((fbBase C M q hT p) v), ?_⟩
    rw [fbQuotMap_apply_mk, fbBase_symm_apply_apply]
    rfl

theorem fbQuotEquiv_apply_mk (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ) (z : ↥(fbKin C M p q)) :
    fbQuotEquiv C M q hT p (Submodule.Quotient.mk z)
      = Submodule.Quotient.mk
          (((fbBase C M q hT p).symm : ↥(fbKin C M p q) →ₗ[ℤ] fbCycT C M p q) z) := by
  rw [fbQuotEquiv, LinearEquiv.ofBijective_apply, fbQuotMap_apply_mk]

def fbQuotCycEquiv (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ) (p q : ℕ) :
    fbCycQ C M p q ≃ₗ[ℤ]
      (↥(cycKer C p) ⧸ homBnd C p) ⊗[ℤ] ↥((sumShift M).X q) :=
  rTensor.equiv (R := ℤ) (Q := ↥((sumShift M).X q)) (f := (homBnd C p).subtype)
    (g := (homBnd C p).mkQ) (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)

theorem fbQuotCycEquiv_apply_mk (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (p q : ℕ) (y : fbCycT C M p q) :
    fbQuotCycEquiv C M p q (Submodule.Quotient.mk y)
      = LinearMap.rTensor ↥((sumShift M).X q) (homBnd C p).mkQ y := by
  show Submodule.liftQ _ _ _ (Submodule.Quotient.mk y) = _
  rw [Submodule.liftQ_apply]

def fbHomQuotEquiv (C : ChainComplex (ModuleCat ℤ) ℕ) (p : ℕ) :
    (↥(cycKer C p) ⧸ homBnd C p) ≃ₗ[ℤ] ↥(C.homology p) :=
  LinearEquiv.ofBijective (homQuotIso C p).inv.hom
    ⟨fun x y hxy => by
        have h := congrArg (homQuotIso C p).hom.hom hxy
        rwa [homIso_hom_apply, homIso_hom_apply] at h,
     fun y => ⟨(homQuotIso C p).hom.hom y, homIso_inv_apply (homQuotIso C p) y⟩⟩

theorem fbHomQuotEquiv_apply_mk (C : ChainComplex (ModuleCat ℤ) ℕ) (p : ℕ)
    (u : ↥(C.cycles p)) :
    fbHomQuotEquiv C p ((homBnd C p).mkQ ((cycIso C p).hom u)) = (C.homologyπ p).hom u := by
  rw [fbHomQuotEquiv, LinearEquiv.ofBijective_apply, ← homQuotIso_apply C p u]
  exact homIso_inv_apply (homQuotIso C p) ((C.homologyπ p).hom u)

def fbIsoLin (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ) :
    fbKinQ C M p q ≃ₗ[ℤ]
      ↥(C.homology p) ⊗[ℤ] ↥((sumShift M).X q) :=
  (fbQuotEquiv C M q hT p).trans
    ((fbQuotCycEquiv C M p q).trans
      ((fbHomQuotEquiv C p).rTensor ↥((sumShift M).X q)))

theorem fbIsoLin_hQuotOf (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥((sumShift M).X q)) (p : ℕ) (u : ↥(C.cycles p))
    (m : ↥((sumShift M).X q)) (h : hDIn C M p q ((C.iCycles p).hom u ⊗ₜ[ℤ] m) = 0) :
    fbIsoLin C M q hT p (hQuotOf C M p q u m h) = hHTensOf C M p q u m := by
  show (fbHomQuotEquiv C p).rTensor ↥((sumShift M).X q)
      (fbQuotCycEquiv C M p q (fbQuotEquiv C M q hT p
        (hQuotOf C M p q u m h))) = hHTensOf C M p q u m
  have hmem : (C.iCycles p).hom u ⊗ₜ[ℤ] m ∈ fbKin C M p q := LinearMap.mem_ker.mpr h
  have hval : hQuotOf C M p q u m h
      = Submodule.Quotient.mk (p := fbK1 C M p q)
          ⟨(C.iCycles p).hom u ⊗ₜ[ℤ] m, hmem⟩ := rfl
  have hz : (C.iCycles p).hom u ∈ cycKer C p := by
    rw [← cycIso_hom_val C p u]
    exact ((cycIso C p).hom u).2
  have hsymm : ((fbBase C M q hT p).symm : ↥(fbKin C M p q) →ₗ[ℤ] fbCycT C M p q)
      ⟨(C.iCycles p).hom u ⊗ₜ[ℤ] m, hmem⟩ = (cycIso C p).hom u ⊗ₜ[ℤ] m := by
    rw [fbBase_symm_apply_tmul C M q hT p ((C.iCycles p).hom u) hz m hmem]
    exact congrArg (fun w : ↥(cycKer C p) => w ⊗ₜ[ℤ] m)
      (Subtype.ext (cycIso_hom_val C p u).symm)
  rw [hval, fbQuotEquiv_apply_mk, hsymm, fbQuotCycEquiv_apply_mk, LinearMap.rTensor_tmul,
    LinearEquiv.rTensor_tmul, fbHomQuotEquiv_apply_mk]
  rfl

theorem flatBase (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (hM : ∀ q, Module.Flat ℤ ↥(M q)) (p q : ℕ) :
    ∃ θ : Work.Kunneth.hQuot C M p q ≅ Work.Kunneth.hHTens C M p q,
      ∀ (u : ↥(C.cycles p)) (m : ↥((Work.Kunneth.sumShift M).X q))
        (h : Work.Kunneth.hDIn C M p q ((C.iCycles p).hom u ⊗ₜ[ℤ] m) = 0),
        θ.hom.hom (Work.Kunneth.hQuotOf C M p q u m h) = Work.Kunneth.hHTensOf C M p q u m := by
  have hT : Module.Flat ℤ ↥((sumShift M).X q) := hM q
  refine ⟨LinearEquiv.toModuleIso (fbIsoLin C M q hT p), ?_⟩
  intro u m h
  show fbIsoLin C M q hT p (hQuotOf C M p q u m h) = hHTensOf C M p q u m
  exact fbIsoLin_hQuotOf C M q hT p u m h

end

end Work.Kunneth
