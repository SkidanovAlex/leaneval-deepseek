import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.Kunneth.CohKunneth.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The value rule of the Künneth isomorphism `Hⁿ(ctens A T) ≅ ∏_{p+q=n} Hᵖ(A) ⊗ T q`

`Submission/Work/Kunneth/homology_ctens.lean` proves the *existence* of an isomorphism
`Hⁿ(ctens A T) ≅ ∏_{p+q=n} Hᵖ(A) ⊗ T q` for a family `T` of flat `ℤ`-modules.  This file
produces one that is *transparent on the classes of cycles*: if a cycle `x` of `ctens A T` has
`pq`-component `iCycles z ⊗ t`, then the class of `x` is mapped to `[z] ⊗ t` in the `pq`-component.

The proof follows the pattern of `Submission/Work/Kunneth/flatKunneth_exists.lean` (the
homological Künneth theorem in cross-product form, which carries the same kind of value rule).
It is the cohomological companion of `flatBase.lean`/`HomQuot.lean` (chain complexes) and
consists of three independent blocks:

* **A.** the cochain analogue of `HomQuot.lean`: `Hⁿ(C) ≅ ker dⁿ ⧸ im dⁿ⁻¹` (`kcHomQuotIso`),
  transparently on the class of a cycle (`kcHomQuotIso_apply`);
* **B.** the cochain analogue of `flatBase.lean`: for `T q` flat, the concrete
  `ker (∂ ⊗ 1) ⧸ im (∂ ⊗ 1)` of the coefficient complex `A^• ⊗ T q` in degree `p` is
  `Hᵖ(A) ⊗ T q`, transparendly on the generators (`kcIsoLin_value`, packaged as
  `kcSummandValue` for the `cycQuot` spelling of `homology_ctens.lean`);
* **C.** the assembly: the component projections `kcProj`/`kcToProd` of `ctens A T` (the cochain
  analogue of `cycToProd`, but on the `(ctens A T).d`-spelling of the cycles), and the value rule.

As everywhere in this chapter the generic `AddCommGroup.toIntModule` instance is removed, so that
the `ℤ`-module structures occurring in the tensor products are those of the `ModuleCat` objects at
hand.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.checkUnivs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## A. `Hⁿ` of a cochain complex as `ker dⁿ ⧸ im dⁿ⁻¹`, on the class of a cycle -/

/-- The concrete `n`-cycles of a cochain complex: the kernel of the differential `dⁿ`. -/
def kcCycKer (C : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (n : ℕ) : Submodule ℤ ↥(C.X n) :=
  LinearMap.ker (C.d n (n+1)).hom

/-- The concrete `n`-boundaries *inside the cycles*: the image of `dⁿ⁻¹`. -/
def kcBnd (C : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (n : ℕ) : Submodule ℤ ↥(kcCycKer C n) :=
  LinearMap.range (((C.d (n-1) n).hom).codRestrict (kcCycKer C n) (fun x => by
    show (C.d n (n+1)).hom ((C.d (n-1) n).hom x) = 0
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d C (n-1) n (n+1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x))

/-- The boundaries inside the cycles are the range of the concrete map `Zⁿ⁻¹ → Zⁿ`. -/
theorem kcBnd_eq_range (C : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (n : ℕ) :
    kcBnd C n = LinearMap.range (ShortComplex.moduleCatToCycles (C.sc' (n-1) n (n+1))) := rfl

/-- The boundaries inside the cycles, as the preimage of the boundaries. -/
theorem kcBnd_eq_comap (C : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (n : ℕ) :
    kcBnd C n = (LinearMap.range (C.d (n-1) n).hom).comap (kcCycKer C n).subtype := by
  rw [kcBnd, LinearMap.range_codRestrict]

/-- Membership in `kcBnd`: the element of `Zⁿ` is the differential of something. -/
theorem mem_kcBnd_iff (C : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (n : ℕ) (x : ↥(kcCycKer C n)) :
    x ∈ kcBnd C n ↔ ∃ w : ↥(C.X (n-1)), (C.d (n-1) n).hom w = (x : ↥(C.X n)) := by
  rw [show kcBnd C n = (LinearMap.range (C.d (n-1) n).hom).comap (kcCycKer C n).subtype from
      kcBnd_eq_comap C n, Submodule.mem_comap, LinearMap.mem_range]
  exact Iff.rfl

/-- **The cycles as the concrete kernel of the differential.** -/
noncomputable def kcCycIso (C : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (n : ℕ) :
    C.cycles n ≅ ModuleCat.of ℤ ↥(kcCycKer C n) :=
  (C.cyclesIsoSc' (n-1) n (n+1) (FlatKerQuot.prev_up n) (FlatKerQuot.next_up n)) ≪≫
    ShortComplex.moduleCatCyclesIso (C.sc' (n-1) n (n+1))

theorem kcCycIso_hom_i (C : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (n : ℕ) :
    (kcCycIso C n).hom ≫
        (ShortComplex.moduleCatLeftHomologyData (C.sc' (n-1) n (n+1))).i
      = C.iCycles n := by
  rw [kcCycIso, Iso.trans_hom, Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- `kcCycIso` does not change the underlying element. -/
theorem kcCycIso_hom_val (C : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (n : ℕ) (c : ↥(C.cycles n)) :
    ((kcCycIso C n).hom c : ↥(C.X n)) = (C.iCycles n).hom c := by
  have h := congrArg (fun (m : C.cycles n ⟶ C.X n) => ModuleCat.Hom.hom m c) (kcCycIso_hom_i C n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- **The homology as the concrete quotient `Zⁿ ⧸ Bⁿ`.** -/
noncomputable def kcHomQuotIso (C : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (n : ℕ) :
    C.homology n ≅ ModuleCat.of ℤ (↥(kcCycKer C n) ⧸ kcBnd C n) :=
  (C.homologyIsoSc' (n-1) n (n+1) (FlatKerQuot.prev_up n) (FlatKerQuot.next_up n)) ≪≫
    ShortComplex.moduleCatHomologyIso (C.sc' (n-1) n (n+1))

/-- The projection onto the left homology data of the degree-`n` short complex is the quotient
map `Zⁿ → Zⁿ ⧸ Bⁿ`. -/
theorem kcLHD_pi_eq (C : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (n : ℕ) :
    (ShortComplex.moduleCatLeftHomologyData (C.sc' (n-1) n (n+1))).π
      = ModuleCat.ofHom (kcBnd C n).mkQ := by
  rw [ModuleCat.hom_ext_iff, ShortComplex.moduleCatLeftHomologyData_π_hom]
  rfl

theorem kcHomQuotIso_comp (C : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (n : ℕ) :
    (C.homologyπ n) ≫ (kcHomQuotIso C n).hom
      = (kcCycIso C n).hom ≫ ModuleCat.ofHom (kcBnd C n).mkQ := by
  simp only [kcHomQuotIso, Iso.trans_hom, Category.assoc, kcCycIso,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.π_moduleCatCyclesIso_hom]
  rw [kcLHD_pi_eq C n]

/-- **The computation rule for `kcHomQuotIso`**: the class of a cycle is the class of the same
element of `Zⁿ ⧸ Bⁿ`. -/
theorem kcHomQuotIso_apply (C : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (n : ℕ) (c : ↥(C.cycles n)) :
    (kcHomQuotIso C n).hom.hom ((C.homologyπ n).hom c)
      = (kcBnd C n).mkQ ((kcCycIso C n).hom c) := by
  have h := congrArg (fun (m : C.cycles n ⟶ ModuleCat.of ℤ (↥(kcCycKer C n) ⧸ kcBnd C n)) =>
    ModuleCat.Hom.hom m c) (kcHomQuotIso_comp C n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] using h

/-! ## B. The `(p,q)`-summand: the cochain analogue of `flatBase.lean` -/

/-- The cycles of the coefficient complex `A^• ⊗ T q` in degree `p`. -/
abbrev kcKin (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ) (p q : ℕ) :
    Submodule ℤ ↥(A.X p ⊗ T q) := LinearMap.ker (dTensOut A T p q)

/-- The boundaries of the coefficient complex `A^• ⊗ T q` in degree `p`. -/
abbrev kcKout (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ) (p q : ℕ) :
    Submodule ℤ ↥(A.X p ⊗ T q) := LinearMap.range (dTensIn A T p q)

/-- The boundaries inside the cycles of the coefficient complex in degree `p`. -/
abbrev kcK1 (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ) (p q : ℕ) :
    Submodule ℤ ↥(kcKin A T p q) := (kcKout A T p q).comap (kcKin A T p q).subtype

/-- The cycles of `A` in degree `p`, tensored with `T q`. -/
abbrev kcCycT (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (p q : ℕ) : Type := ↥(kcCycKer A p) ⊗[ℤ] ↥(T q)

/-- The image of the boundaries of `A` inside `kcCycT`. -/
abbrev kcQ (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ) (p q : ℕ) :
    Submodule ℤ (kcCycT A T p q) :=
  LinearMap.range (LinearMap.rTensor ↥(T q) (kcBnd A p).subtype)

/-- `ker (∂ ⊗ 1) ⧸ im (∂ ⊗ 1)` in degree `p` of the coefficient complex. -/
abbrev kcKinQ (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ) (p q : ℕ) :
    Type := ↥(kcKin A T p q) ⧸ kcK1 A T p q

/-- The same quotient, with the boundaries of `A` taken out first. -/
abbrev kcCycQ (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ) (p q : ℕ) :
    Type := kcCycT A T p q ⧸ kcQ A T p q

/-- Flatness of `T q` makes tensoring preserve the exact sequence
`0 → Z^p → A^p → A^{p+1}`, so that the kernel of `∂ ⊗ 1` is `Z^p ⊗ T q`. -/
theorem range_rTensor_kcCycKer_subtype (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ)
    (T : ℕ → ModuleCat.{0,0} ℤ) (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ) :
    (LinearMap.rTensor ↥(T q) (Submodule.subtype (kcCycKer A p))).range = kcKin A T p q := by
  haveI : Module.Flat ℤ ↥(T q) := hT
  have hfg : Function.Exact ⇑(Submodule.subtype (kcCycKer A p)) ⇑((A.d p (p+1)).hom) := by
    refine LinearMap.exact_iff.mpr ?_
    rw [Submodule.range_subtype]
    rfl
  have hex := Module.Flat.rTensor_exact (R := ℤ) (M := ↥(T q)) hfg
  rw [LinearMap.exact_iff] at hex
  exact hex.symm

theorem injective_rTensor_kcCycKer_subtype (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ)
    (T : ℕ → ModuleCat.{0,0} ℤ) (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ) :
    Function.Injective (LinearMap.rTensor ↥(T q) (Submodule.subtype (kcCycKer A p))) := by
  haveI : Module.Flat ℤ ↥(T q) := hT
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

/-- **Flat base change**: `Z^p ⊗ T q ≅ ker (∂ ⊗ 1)`, by flatness of `T q`. -/
def kcBase (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ) : kcCycT A T p q ≃ₗ[ℤ] ↥(kcKin A T p q) :=
  LinearEquiv.ofBijective
    ((LinearMap.rTensor ↥(T q) (Submodule.subtype (kcCycKer A p))).codRestrict
        (kcKin A T p q)
        (fun y => by
          rw [← range_rTensor_kcCycKer_subtype A T q hT p]
          exact ⟨y, rfl⟩))
    ⟨fun x y hxy =>
        injective_rTensor_kcCycKer_subtype A T q hT p (Subtype.ext_iff.mp hxy),
     fun y => by
        obtain ⟨x, hx⟩ := (LinearMap.mem_range.mp (show y.1 ∈
          (LinearMap.rTensor ↥(T q) (Submodule.subtype (kcCycKer A p))).range from by
            rw [range_rTensor_kcCycKer_subtype A T q hT p]
            exact y.2))
        exact ⟨x, Subtype.ext hx⟩⟩

theorem kcBase_apply_val (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ) (y : kcCycT A T p q) :
    ((kcBase A T q hT p y : ↥(kcKin A T p q)) : ↥(A.X p ⊗ T q))
      = LinearMap.rTensor ↥(T q) (Submodule.subtype (kcCycKer A p)) y := by
  rw [kcBase, LinearEquiv.ofBijective_apply, LinearMap.codRestrict_apply]
  rfl

theorem kcBase_symm_apply_apply (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ)
    (T : ℕ → ModuleCat.{0,0} ℤ) (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ)
    (v : kcCycT A T p q) :
    ((kcBase A T q hT p).symm : ↥(kcKin A T p q) →ₗ[ℤ] kcCycT A T p q)
      ((kcBase A T q hT p) v) = v := by
  rw [show ((kcBase A T q hT p).symm : ↥(kcKin A T p q) →ₗ[ℤ] kcCycT A T p q)
        ((kcBase A T q hT p) v)
      = (kcBase A T q hT p).symm ((kcBase A T q hT p) v) from rfl,
    LinearEquiv.symm_apply_apply]

/-- **The inverse of `kcBase` on a generator.** -/
theorem kcBase_symm_apply_tmul (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ)
    (T : ℕ → ModuleCat.{0,0} ℤ) (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ)
    (a : ↥(A.X p)) (ha : a ∈ kcCycKer A p) (t : ↥(T q))
    (hh : a ⊗ₜ[ℤ] t ∈ kcKin A T p q) :
    ((kcBase A T q hT p).symm : ↥(kcKin A T p q) →ₗ[ℤ] kcCycT A T p q)
        ⟨a ⊗ₜ[ℤ] t, hh⟩ = ⟨a, ha⟩ ⊗ₜ[ℤ] t := by
  rw [show ((kcBase A T q hT p).symm : ↥(kcKin A T p q) →ₗ[ℤ] kcCycT A T p q)
        ⟨a ⊗ₜ[ℤ] t, hh⟩
      = (kcBase A T q hT p).symm ⟨a ⊗ₜ[ℤ] t, hh⟩ from rfl]
  apply (kcBase A T q hT p).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [kcBase_apply_val, LinearMap.rTensor_tmul]
  rfl

/-- The image of the incoming differential is the image of the boundaries of `A`. -/
theorem range_dTensIn_eq (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (p q : ℕ) :
    kcKout A T p q
      = (LinearMap.rTensor ↥(T q)
          ((Submodule.subtype (kcCycKer A p)).comp (kcBnd A p).subtype)).range := by
  have hz : ∀ x : ↥(A.X (p-1)), (A.d p (p+1)).hom ((A.d (p-1) p).hom x) = 0 := by
    intro x
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d A (p-1) p (p+1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x
  let f : ↥(A.X (p-1)) →ₗ[ℤ] ↥(kcCycKer A p) :=
    ((A.d (p-1) p).hom).codRestrict (kcCycKer A p) hz
  let dc : ↥(A.X (p-1)) →ₗ[ℤ] ↥(kcBnd A p) :=
    f.codRestrict (kcBnd A p) (fun x => (mem_kcBnd_iff A p (f x)).mpr ⟨x, rfl⟩)
  have hcomp : ((Submodule.subtype (kcCycKer A p)).comp (kcBnd A p).subtype).comp dc
      = (A.d (p-1) p).hom := by
    ext x
    rfl
  have hdc : Function.Surjective ⇑dc := by
    intro b
    obtain ⟨w, hw⟩ := (mem_kcBnd_iff A p b).mp b.2
    exact ⟨w, Subtype.ext (Subtype.ext hw)⟩
  show (LinearMap.rTensor ↥(T q) ((A.d (p-1) p).hom)).range = _
  rw [← hcomp, LinearMap.rTensor_comp,
    LinearMap.range_comp (LinearMap.rTensor ↥(T q) dc)
      (LinearMap.rTensor ↥(T q)
        ((Submodule.subtype (kcCycKer A p)).comp (kcBnd A p).subtype)),
    LinearMap.range_eq_top.mpr (LinearMap.rTensor_surjective _ hdc), Submodule.map_top]

/-- The boundaries of `A^• ⊗ T q` inside the cycles correspond to the boundaries of `A` inside
`Z^p ⊗ T q`, under `kcBase`. -/
theorem mem_kcKout_iff (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ) (y : ↥(kcKin A T p q)) :
    (y : ↥(A.X p ⊗ T q)) ∈ kcKout A T p q
      ↔ (kcBase A T q hT p).symm y ∈ kcQ A T p q := by
  have h1 : ∀ y : ↥(kcKin A T p q),
      (y : ↥(A.X p ⊗ T q))
        = LinearMap.rTensor ↥(T q) (Submodule.subtype (kcCycKer A p))
            ((kcBase A T q hT p).symm y) := by
    intro y
    rw [← kcBase_apply_val A T q hT p ((kcBase A T q hT p).symm y),
      LinearEquiv.apply_symm_apply]
  have hβ : LinearMap.rTensor ↥(T q)
        ((Submodule.subtype (kcCycKer A p)).comp (kcBnd A p).subtype)
      = (LinearMap.rTensor ↥(T q) (Submodule.subtype (kcCycKer A p))).comp
          (LinearMap.rTensor ↥(T q) (kcBnd A p).subtype) :=
    LinearMap.rTensor_comp _ _ _
  show (y : ↥(A.X p ⊗ T q)) ∈ kcKout A T p q
      ↔ (kcBase A T q hT p).symm y
          ∈ (LinearMap.rTensor ↥(T q) (kcBnd A p).subtype).range
  rw [range_dTensIn_eq A T p q]
  constructor
  · intro hy
    obtain ⟨w, hw⟩ := hy
    refine ⟨w, ?_⟩
    have hw' : LinearMap.rTensor ↥(T q)
          ((Submodule.subtype (kcCycKer A p)).comp (kcBnd A p).subtype) w
        = LinearMap.rTensor ↥(T q) (Submodule.subtype (kcCycKer A p))
            (LinearMap.rTensor ↥(T q) (kcBnd A p).subtype w) := by
      rw [hβ]; rfl
    refine injective_rTensor_kcCycKer_subtype A T q hT p ?_
    rw [← hw', hw, h1 y]
  · intro hy
    obtain ⟨w, hw⟩ := hy
    refine ⟨w, ?_⟩
    have hw' : LinearMap.rTensor ↥(T q)
          ((Submodule.subtype (kcCycKer A p)).comp (kcBnd A p).subtype) w
        = LinearMap.rTensor ↥(T q) (Submodule.subtype (kcCycKer A p))
            (LinearMap.rTensor ↥(T q) (kcBnd A p).subtype w) := by
      rw [hβ]; rfl
    rw [hw', hw, h1 y]

/-- `ker (∂ ⊗ 1) ⧸ im (∂ ⊗ 1)` computed as a quotient of `Z^p ⊗ T q`. -/
def kcQuotMap (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ) :
    kcKinQ A T p q →ₗ[ℤ] kcCycQ A T p q :=
  Submodule.liftQ (kcK1 A T p q)
    ((Submodule.mkQ (kcQ A T p q)).comp
      ((kcBase A T q hT p).symm : ↥(kcKin A T p q) →ₗ[ℤ] kcCycT A T p q))
    (fun z hz => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact (mem_kcKout_iff A T q hT p z).mp (Submodule.mem_comap.mp hz))

theorem kcQuotMap_apply_mk (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ)
    (T : ℕ → ModuleCat.{0,0} ℤ) (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ)
    (z : ↥(kcKin A T p q)) :
    kcQuotMap A T q hT p (Submodule.Quotient.mk z)
      = Submodule.Quotient.mk
          (((kcBase A T q hT p).symm : ↥(kcKin A T p q) →ₗ[ℤ] kcCycT A T p q) z) := by
  simp only [kcQuotMap, Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply]

def kcQuotEquiv (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ) : kcKinQ A T p q ≃ₗ[ℤ] kcCycQ A T p q := by
  refine LinearEquiv.ofBijective (kcQuotMap A T q hT p) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker] at ha
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (kcK1 A T p q) a
    rw [Submodule.mkQ_apply] at ha
    rw [kcQuotMap_apply_mk, Submodule.Quotient.mk_eq_zero] at ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_comap.mpr ((mem_kcKout_iff A T q hT p z).mpr ha)
  · intro w
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (kcQ A T p q) w
    refine ⟨Submodule.Quotient.mk ((kcBase A T q hT p) v), ?_⟩
    rw [kcQuotMap_apply_mk, kcBase_symm_apply_apply]
    rfl

theorem kcQuotEquiv_apply_mk (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ)
    (T : ℕ → ModuleCat.{0,0} ℤ) (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ)
    (z : ↥(kcKin A T p q)) :
    kcQuotEquiv A T q hT p (Submodule.Quotient.mk z)
      = Submodule.Quotient.mk
          (((kcBase A T q hT p).symm : ↥(kcKin A T p q) →ₗ[ℤ] kcCycT A T p q) z) := by
  rw [kcQuotEquiv, LinearEquiv.ofBijective_apply, kcQuotMap_apply_mk]

/-- Right exactness of the tensor product: `(Z^p ⧸ B^p) ⊗ T q ≅ (Z^p ⊗ T q) ⧸ (B^p ⊗ T q)`. -/
def kcQuotCycEquiv (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (p q : ℕ) :
    kcCycQ A T p q ≃ₗ[ℤ] (↥(kcCycKer A p) ⧸ kcBnd A p) ⊗[ℤ] ↥(T q) :=
  rTensor.equiv (R := ℤ) (Q := ↥(T q)) (f := (kcBnd A p).subtype) (g := (kcBnd A p).mkQ)
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)

theorem kcQuotCycEquiv_apply_mk (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ)
    (T : ℕ → ModuleCat.{0,0} ℤ) (p q : ℕ) (y : kcCycT A T p q) :
    kcQuotCycEquiv A T p q (Submodule.Quotient.mk y)
      = LinearMap.rTensor ↥(T q) (kcBnd A p).mkQ y := by
  show Submodule.liftQ _ _ _ (Submodule.Quotient.mk y) = _
  rw [Submodule.liftQ_apply]

/-- `Z^p ⧸ B^p ≅ Hᵖ(A)`, on the class of a cycle. -/
def kcHomQuotEquiv (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (p : ℕ) :
    (↥(kcCycKer A p) ⧸ kcBnd A p) ≃ₗ[ℤ] ↥(A.homology p) :=
  LinearEquiv.ofBijective (kcHomQuotIso A p).inv.hom
    ⟨fun x y hxy => by
        have h := congrArg (kcHomQuotIso A p).hom.hom hxy
        rwa [homIso_hom_apply, homIso_hom_apply] at h,
     fun y => ⟨(kcHomQuotIso A p).hom.hom y, homIso_inv_apply (kcHomQuotIso A p) y⟩⟩

theorem kcHomQuotEquiv_apply_mk (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (p : ℕ)
    (u : ↥(A.cycles p)) :
    kcHomQuotEquiv A p ((kcBnd A p).mkQ ((kcCycIso A p).hom u)) = (A.homologyπ p).hom u := by
  rw [kcHomQuotEquiv, LinearEquiv.ofBijective_apply, ← kcHomQuotIso_apply A p u]
  exact homIso_inv_apply (kcHomQuotIso A p) ((A.homologyπ p).hom u)

/-- **The `(p,q)`-Künneth summand with flat coefficients, transparently on the generators:**
`ker (∂ ⊗ 1) ⧸ im (∂ ⊗ 1) ≅ Hᵖ(A) ⊗ T q`. -/
def kcIsoLin (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ) :
    kcKinQ A T p q ≃ₗ[ℤ] ↥(A.homology p) ⊗[ℤ] ↥(T q) :=
  (kcQuotEquiv A T q hT p).trans
    ((kcQuotCycEquiv A T p q).trans ((kcHomQuotEquiv A p).rTensor ↥(T q)))

/-- **The value rule of the summand**: the class of `iCycles z ⊗ t` is mapped to `[z] ⊗ t`. -/
theorem kcIsoLin_value (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (q : ℕ) (hT : Module.Flat ℤ ↥(T q)) (p : ℕ) (z : ↥(A.cycles p)) (t : ↥(T q))
    (h : dTensOut A T p q ((A.iCycles p).hom z ⊗ₜ[ℤ] t) = 0) :
    kcIsoLin A T q hT p (Submodule.Quotient.mk (p := kcK1 A T p q)
        ⟨(A.iCycles p).hom z ⊗ₜ[ℤ] t, h⟩) = (A.homologyπ p).hom z ⊗ₜ[ℤ] t := by
  show (kcHomQuotEquiv A p).rTensor ↥(T q) (kcQuotCycEquiv A T p q (kcQuotEquiv A T q hT p
        (Submodule.Quotient.mk (p := kcK1 A T p q) ⟨(A.iCycles p).hom z ⊗ₜ[ℤ] t, h⟩)))
      = (A.homologyπ p).hom z ⊗ₜ[ℤ] t
  have hmem : (A.iCycles p).hom z ⊗ₜ[ℤ] t ∈ kcKin A T p q := LinearMap.mem_ker.mpr h
  have hval : (Submodule.Quotient.mk (p := kcK1 A T p q) ⟨(A.iCycles p).hom z ⊗ₜ[ℤ] t, h⟩)
      = Submodule.Quotient.mk (p := kcK1 A T p q)
          ⟨(A.iCycles p).hom z ⊗ₜ[ℤ] t, hmem⟩ := rfl
  have hz : (A.iCycles p).hom z ∈ kcCycKer A p := by
    rw [← kcCycIso_hom_val A p z]
    exact ((kcCycIso A p).hom z).2
  have hsymm : ((kcBase A T q hT p).symm : ↥(kcKin A T p q) →ₗ[ℤ] kcCycT A T p q)
      ⟨(A.iCycles p).hom z ⊗ₜ[ℤ] t, hmem⟩ = (kcCycIso A p).hom z ⊗ₜ[ℤ] t := by
    rw [kcBase_symm_apply_tmul A T q hT p ((A.iCycles p).hom z) hz t hmem]
    exact congrArg (fun w : ↥(kcCycKer A p) => w ⊗ₜ[ℤ] t)
      (Subtype.ext (kcCycIso_hom_val A p z).symm)
  rw [hval, kcQuotEquiv_apply_mk, hsymm, kcQuotCycEquiv_apply_mk, LinearMap.rTensor_tmul,
    LinearEquiv.rTensor_tmul, kcHomQuotEquiv_apply_mk]

/-- `dTensOut` kills `iCycles z ⊗ t`, so that the generators of the summand are cycles. -/
theorem dTensOut_iCycles_tmul (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ)
    (T : ℕ → ModuleCat.{0,0} ℤ) (p q : ℕ) (z : ↥(A.cycles p)) (t : ↥(T q)) :
    dTensOut A T p q ((A.iCycles p).hom z ⊗ₜ[ℤ] t) = 0 := by
  show LinearMap.rTensor ↥(T q) (A.d p (p+1)).hom ((A.iCycles p).hom z ⊗ₜ[ℤ] t) = 0
  rw [LinearMap.rTensor_tmul]
  have h : (A.d p (p+1)).hom ((A.iCycles p).hom z) = 0 := by
    have hh := congrArg (fun (m : A.cycles p ⟶ A.X (p+1)) => ModuleCat.Hom.hom m z)
      (HomologicalComplex.iCycles_d A p (p+1))
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
      LinearMap.zero_apply] using hh
  rw [h, TensorProduct.zero_tmul]

/-! ## C. The value rule for `Hⁿ(ctens A T)` -/

/-- The projection of the cycles of `ctens A T` onto the cycles of one summand, on the
`(ctens A T).d`-spelling of the cycles. -/
def kcProj (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ) (n : ℕ)
    (pq : tpIdx n) :
    ↥(kcCycKer (ctens A T) n) →ₗ[ℤ] ↥(LinearMap.ker (dTensOut A T pq.1.1 pq.1.2)) where
  toFun x := ⟨(show ctensX A T n from (x : ↥((ctens A T).X n))) pq, by
    rw [LinearMap.mem_ker, ← ctensD_apply_step A T n (show ctensX A T n from
      (x : ↥((ctens A T).X n))) pq]
    have h : ctensD A T n (show ctensX A T n from (x : ↥((ctens A T).X n))) = 0 := by
      have h2 : ModuleCat.Hom.hom ((ctens A T).d n (n+1)) (x : ↥((ctens A T).X n)) = 0 := x.2
      rw [ctens_d] at h2
      exact h2
    rw [h]
    simp⟩
  map_add' x y := by
    apply Subtype.ext
    show (show ctensX A T n from ((x + y : ↥(kcCycKer (ctens A T) n)) : ↥((ctens A T).X n))) pq
      = (show ctensX A T n from (x : ↥((ctens A T).X n))) pq
        + (show ctensX A T n from (y : ↥((ctens A T).X n))) pq
    rw [show ((x + y : ↥(kcCycKer (ctens A T) n)) : ↥((ctens A T).X n))
        = (x : ↥((ctens A T).X n)) + (y : ↥((ctens A T).X n)) from rfl]
    exact DirectSum.add_apply _ _ pq
  map_smul' c x := by
    apply Subtype.ext
    exact DirectSum.smul_apply c (show ctensX A T n from (x : ↥((ctens A T).X n))) pq

/-- The value of `kcProj`: the underlying element is the corresponding component. -/
theorem kcProj_val (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (n : ℕ) (pq : tpIdx n) (x : ↥(kcCycKer (ctens A T) n)) :
    ((kcProj A T n pq x : ↥(LinearMap.ker (dTensOut A T pq.1.1 pq.1.2)))
        : ctensSummand A T pq.1.1 pq.1.2)
      = (show ctensX A T n from (x : ↥((ctens A T).X n))) pq := rfl

/-- The projection of the cycles of `ctens A T` onto the product of the summands' quotients. -/
def kcToProd (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ) (n : ℕ) :
    ↥(kcCycKer (ctens A T) n) →ₗ[ℤ] (∀ pq : tpIdx n, cycQuot A T n pq) :=
  LinearMap.pi (fun pq => (Submodule.mkQ (cycBnd A T n pq)).comp (kcProj A T n pq))

theorem kcToProd_apply (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (n : ℕ) (x : ↥(kcCycKer (ctens A T) n)) (pq : tpIdx n) :
    kcToProd A T n x pq = (Submodule.mkQ (cycBnd A T n pq)) (kcProj A T n pq x) :=
  LinearMap.pi_apply _ _ _

/-- The range of `dⁿ⁻¹` of the complex `ctens A T`, in the spelling of `ctensDIn`. -/
theorem range_ctens_d_eq (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (n : ℕ) :
    (LinearMap.range ((ctens A T).d (n-1) n).hom) = (ctensDIn A T n).range := by
  rw [ctens_d_in]
  rfl

/-- The kernel of `kcToProd` is the submodule of boundaries. -/
theorem kcToProd_ker (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (n : ℕ) : (kcToProd A T n).ker = kcBnd (ctens A T) n := by
  ext x
  rw [LinearMap.mem_ker, funext_iff, kcBnd_eq_comap, Submodule.mem_comap, range_ctens_d_eq,
    range_ctensDIn, mem_ctensProdSub]
  constructor
  · intro h pq
    have h' := h pq
    rw [kcToProd_apply] at h'
    simp only [Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, cycBnd,
      Submodule.mem_comap, kcProj_val] at h'
    exact h'
  · intro hx pq
    rw [kcToProd_apply]
    simp only [Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, cycBnd,
      Submodule.mem_comap, kcProj_val]
    exact hx pq

/-- `kcToProd` is surjective. -/
theorem kcToProd_surjective (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ)
    (T : ℕ → ModuleCat.{0,0} ℤ) (n : ℕ) : Function.Surjective (kcToProd A T n) := by
  intro f
  choose g hg using fun pq => Submodule.mkQ_surjective (cycBnd A T n pq) (f pq)
  have hzmem : (ctensMk A T n fun pq => (g pq : ctensSummand A T pq.1.1 pq.1.2))
      ∈ (ctensD A T n).ker := by
    rw [mem_ker_ctensD_iff]
    intro pq
    rw [ctensMk_apply]
    exact (g pq).2
  have hz : ctensD A T n (ctensMk A T n fun pq => (g pq : ctensSummand A T pq.1.1 pq.1.2))
      = 0 := hzmem
  have hmem : (ctensMk A T n fun pq => (g pq : ctensSummand A T pq.1.1 pq.1.2))
      ∈ kcCycKer (ctens A T) n := by
    rw [kcCycKer, LinearMap.mem_ker, ctens_d]
    exact hz
  refine ⟨⟨ctensMk A T n (fun pq => (g pq : ctensSummand A T pq.1.1 pq.1.2)), hmem⟩, ?_⟩
  funext pq
  show kcToProd A T n ⟨ctensMk A T n fun pq => (g pq : ctensSummand A T pq.1.1 pq.1.2),
    hmem⟩ pq = f pq
  rw [kcToProd_apply]
  have hproj : kcProj A T n pq ⟨ctensMk A T n fun pq => (g pq : ctensSummand A T pq.1.1 pq.1.2),
      hmem⟩ = g pq := by
    apply Subtype.ext
    rw [kcProj_val, ctensMk_apply]
  rw [hproj]
  exact hg pq

/-- **The `(p,q)`-summand of the cohomological Künneth computation, with its value rule**, in the
spelling of `Submission/Work/Kunneth/homology_ctens.lean`. -/
theorem kcSummandValue (A : CochainComplex (ModuleCat.{0,0} ℤ) ℕ) (T : ℕ → ModuleCat.{0,0} ℤ)
    (n : ℕ) (pq : tpIdx n) (hT : Module.Flat ℤ ↥(T pq.1.2)) :
    ∃ θ : ModuleCat.of ℤ (cycQuot A T n pq) ≅ homologyTensor A T pq.1.1 pq.1.2,
      ∀ (z : ↥(A.cycles pq.1.1)) (t : ↥(T pq.1.2))
        (h : dTensOut A T pq.1.1 pq.1.2 ((A.iCycles pq.1.1).hom z ⊗ₜ[ℤ] t) = 0),
        θ.hom.hom (Submodule.Quotient.mk (p := cycBnd A T n pq)
            ⟨(A.iCycles pq.1.1).hom z ⊗ₜ[ℤ] t, h⟩)
          = (A.homologyπ pq.1.1).hom z ⊗ₜ[ℤ] t :=
  ⟨LinearEquiv.toModuleIso (kcIsoLin A T pq.1.2 hT pq.1.1),
    fun z t h => kcIsoLin_value A T pq.1.2 hT pq.1.1 z t h⟩

/-- **The value rule of the cohomological Künneth isomorphism.** -/
theorem ctensHomologyValue (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ)
    (hT : ∀ q, Module.Flat ℤ ↥(T q)) (n : ℕ) :
    ∃ e : (ctens A T).homology n ≅ ctensH A T n,
      ∀ (x : ↥((ctens A T).cycles n)) (pq : tpIdx n) (z : ↥(A.cycles pq.1.1))
        (t : ↥(T pq.1.2)),
        (show ctensX A T n from ((ctens A T).iCycles n).hom x) pq
          = (A.iCycles pq.1.1).hom z ⊗ₜ[ℤ] t →
        (e.hom.hom ((ctens A T).homologyπ n x)) pq
          = (A.homologyπ pq.1.1).hom z ⊗ₜ[ℤ] t := by
  set e2Lin : (↥(kcCycKer (ctens A T) n) ⧸ kcBnd (ctens A T) n) ≃ₗ[ℤ]
      (∀ pq : tpIdx n, cycQuot A T n pq) :=
    (Submodule.quotEquivOfEq (kcBnd (ctens A T) n) (kcToProd A T n).ker
        (kcToProd_ker A T n).symm).trans
      (LinearMap.quotKerEquivOfSurjective (kcToProd A T n) (kcToProd_surjective A T n))
      with he2def
  have he2 : ∀ z : ↥(kcCycKer (ctens A T) n),
      e2Lin ((kcBnd (ctens A T) n).mkQ z) = kcToProd A T n z := by
    intro z
    rw [he2def, LinearEquiv.trans_apply, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective]
    simp [LinearMap.quotKerEquivRange_apply_mk]
  set e3Lin : (∀ pq : tpIdx n, cycQuot A T n pq) ≃ₗ[ℤ]
      (∀ pq : tpIdx n, ↥(homologyTensor A T pq.1.1 pq.1.2)) :=
    LinearEquiv.piCongrRight (fun pq =>
      hIsoToLinearEquiv ((kcSummandValue A T n pq (hT pq.1.2)).choose)) with he3def
  have he3 : ∀ (g : ∀ pq : tpIdx n, cycQuot A T n pq) (pq : tpIdx n),
      e3Lin g pq = ((kcSummandValue A T n pq (hT pq.1.2)).choose).hom.hom (g pq) := by
    intro g pq
    rw [he3def, LinearEquiv.piCongrRight_apply]
    rfl
  set Elin : ↥((ctens A T).homology n) ≃ₗ[ℤ]
      (∀ pq : tpIdx n, ↥(homologyTensor A T pq.1.1 pq.1.2)) :=
    (hIsoToLinearEquiv (kcHomQuotIso (ctens A T) n)).trans (e2Lin.trans e3Lin) with hEdef
  refine ⟨LinearEquiv.toModuleIso Elin, ?_⟩
  intro x pq z t hx
  show Elin ((ctens A T).homologyπ n x) pq = (A.homologyπ pq.1.1).hom z ⊗ₜ[ℤ] t
  show e3Lin (e2Lin ((hIsoToLinearEquiv (kcHomQuotIso (ctens A T) n))
      ((ctens A T).homologyπ n x))) pq = (A.homologyπ pq.1.1).hom z ⊗ₜ[ℤ] t
  rw [show (hIsoToLinearEquiv (kcHomQuotIso (ctens A T) n)) ((ctens A T).homologyπ n x)
      = (kcBnd (ctens A T) n).mkQ ((kcCycIso (ctens A T) n).hom x) from
        kcHomQuotIso_apply (ctens A T) n x]
  rw [he2 ((kcCycIso (ctens A T) n).hom x), he3 (kcToProd A T n ((kcCycIso (ctens A T) n).hom x)),
    kcToProd_apply]
  have hproj : kcProj A T n pq ((kcCycIso (ctens A T) n).hom x)
      = ⟨(A.iCycles pq.1.1).hom z ⊗ₜ[ℤ] t,
          dTensOut_iCycles_tmul A T pq.1.1 pq.1.2 z t⟩ := by
    apply Subtype.ext
    rw [kcProj_val, kcCycIso_hom_val]
    exact hx
  rw [Submodule.mkQ_apply, hproj]
  exact (kcSummandValue A T n pq (hT pq.1.2)).choose_spec z t _

end

end Work.Kunneth
