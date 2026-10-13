import Mathlib
import Submission.Work.DSMX0U.Cell

namespace Work.DSMX0U

open CategoryTheory AlgebraicGeometry

universe a

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace Fallback

section Aux

variable {A : Type a} [CommRing A]

/-! ## Two cycles are cohomologous iff they differ by a boundary

For a short complex `S` of `A`-modules, two cycles have the same class in `S.homology` if and
only if their difference lies in the image of `S.f`.  This is the concrete statement that
`S.homology` is the quotient of the cycles by the image of `S.f`, combined with the identity
`S.homologyπ ≫ S.homologyι = S.iCycles ≫ S.pOpcycles`.
-/

lemma sc_homologyπ_eq_iff (S : ShortComplex (ModuleCat.{a} A)) (x y : ↥S.cycles) :
    (S.homologyπ).hom x = (S.homologyπ).hom y ↔
      (S.iCycles).hom x - (S.iCycles).hom y ∈ LinearMap.range (S.f.hom) := by
  have key : ∀ z : ↥S.cycles,
      (S.homologyι).hom ((S.homologyπ).hom z) = (S.pOpcycles).hom ((S.iCycles).hom z) := by
    intro z
    have h := congrArg (fun (f : S.cycles ⟶ S.opcycles) => f.hom z) S.homology_π_ι
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  constructor
  · intro h
    apply (S.moduleCat_pOpcycles_eq_iff _ _).mp
    have h2 : (S.homologyι).hom ((S.homologyπ).hom x)
        = (S.homologyι).hom ((S.homologyπ).hom y) := by rw [h]
    rwa [key x, key y] at h2
  · intro h
    have h1 := (S.moduleCat_pOpcycles_eq_iff _ _).mpr h
    have h2 : (S.homologyι).hom ((S.homologyπ).hom x)
        = (S.homologyι).hom ((S.homologyπ).hom y) := by rwa [key x, key y]
    exact (ModuleCat.mono_iff_injective _).mp inferInstance h2

/-- The same statement for a cochain complex: two cycles of `C` in degree `d` have the same
class in `H^{d}(C)` if and only if their difference is in the image of `d : C^{d-1} ⟶ C^{d}`. -/
lemma homologyπ_eq_iff {C : CochainComplex (ModuleCat.{a} A) ℤ} {d : ℤ}
    (x y : ↥(C.cycles d)) :
    (C.homologyπ d).hom x = (C.homologyπ d).hom y ↔
      (C.iCycles d).hom x - (C.iCycles d).hom y ∈ LinearMap.range (C.d (d-1) d).hom := by
  have hi : (ComplexShape.up ℤ).prev d = d - 1 :=
    ComplexShape.prev_eq' _ (ComplexShape.up_mk (d-1) d (by ring))
  have hk : (ComplexShape.up ℤ).next d = d + 1 :=
    ComplexShape.next_eq' _ (ComplexShape.up_mk d (d+1) rfl)
  have hxa : ∀ z : ↥(C.cycles d),
      (C.iCycles d).hom z = ((C.sc' (d-1) d (d+1)).iCycles).hom
        (((C.cyclesIsoSc' (d-1) d (d+1) hi hk).hom).hom z) := by
    intro z
    have h := congrArg (fun (f : C.cycles d ⟶ C.X d) => f.hom z)
      (C.cyclesIsoSc'_hom_iCycles (d-1) d (d+1) hi hk)
    rw [ConcreteCategory.comp_apply] at h
    exact h.symm
  have hxb : ∀ z : ↥(C.cycles d),
      ((C.homologyIsoSc' (d-1) d (d+1) hi hk).hom).hom ((C.homologyπ d).hom z)
        = ((C.sc' (d-1) d (d+1)).homologyπ).hom
            (((C.cyclesIsoSc' (d-1) d (d+1) hi hk).hom).hom z) := by
    intro z
    have h := congrArg (fun (f : C.cycles d ⟶ (C.sc' (d-1) d (d+1)).homology) => f.hom z)
      (C.π_homologyIsoSc'_hom (d-1) d (d+1) hi hk)
    rw [ConcreteCategory.comp_apply] at h
    exact h
  have hinj : Function.Injective
      (fun z : ↥(C.homology d) => ((C.homologyIsoSc' (d-1) d (d+1) hi hk).hom).hom z) := by
    haveI : Mono (C.homologyIsoSc' (d-1) d (d+1) hi hk).hom := inferInstance
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  rw [← hinj.eq_iff, hxb x, hxb y, sc_homologyπ_eq_iff]
  have hf : (C.sc' (d-1) d (d+1)).f.hom = (C.d (d-1) d).hom := rfl
  rw [hf, ← hxa x, ← hxa y]

/-! ## A finite free module surjecting onto the cohomology in degree `d` -/

lemma exists_surj_homologyπ {C : CochainComplex (ModuleCat.{a} A) ℤ} {d : ℤ}
    (hfg : Module.Finite A (C.homology d)) :
    ∃ (n : ℕ) (σ : ModuleCat.of A (Fin n → A) ⟶ C.cycles d),
      Function.Surjective (fun x => (C.homologyπ d).hom (σ.hom x)) := by
  haveI := hfg
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A ↥(C.homology d)
  have hsurj : Function.Surjective (C.homologyπ d).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (C.homologyπ d).hom p hsurj
  refine ⟨n, ModuleCat.ofHom σ, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hp y
  refine ⟨x, ?_⟩
  rw [← hx]
  simpa only [ModuleCat.hom_ofHom, LinearMap.comp_apply] using congrArg (fun f => f x) hσ

/-! ## The coaugmentation cycle

If `d = 0`, the element `c₀ 1` is a cycle of `C` in degree `d` (after transporting it along the
equality), so it has a preimage under `iCycles d`. -/

variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

/-- The `A`-linear map `A ⟶ C^{d}` given by `c₀`, transported to degree `d` along `h : d = 0`. -/
noncomputable def coaugHom {d : ℤ} (h : d = 0) : ModuleCat.of A A ⟶ C.X d :=
  c₀ ≫ (C.XIsoOfEq h.symm).hom

lemma coaugHom_comp_d {d : ℤ} (hc₀ : ∀ j : ℤ, c₀ ≫ C.d 0 j = 0) (h : d = 0) :
    coaugHom (C := C) (c₀ := c₀) h ≫ C.d d (d+1) = 0 := by
  have h1 : d + 1 = 1 := by rw [h]; norm_num
  show (c₀ ≫ (C.XIsoOfEq h.symm).hom) ≫ C.d d (d+1) = 0
  rw [Category.assoc]
  rw [HomologicalComplex.XIsoOfEq_hom_comp_d C h.symm (d+1)]
  rw [← HomologicalComplex.d_comp_XIsoOfEq_hom C h1.symm 0]
  rw [← Category.assoc, hc₀ 1]
  simp

/-- The cycle `c₀ 1` of `C` in degree `d`, when `d = 0`. -/
noncomputable def coaugCycle {d : ℤ} (hc₀ : ∀ j : ℤ, c₀ ≫ C.d 0 j = 0) (h : d = 0) :
    ↥(C.cycles d) :=
  (C.liftCycles (coaugHom (C := C) (c₀ := c₀) h) (d+1)
    (ComplexShape.next_eq' _ (ComplexShape.up_mk d (d+1) rfl))
    (coaugHom_comp_d hc₀ h)).hom 1

set_option backward.isDefEq.respectTransparency false in
lemma iCycles_coaugCycle {d : ℤ} (hc₀ : ∀ j : ℤ, c₀ ≫ C.d 0 j = 0) (h : d = 0) :
    (C.iCycles d).hom (coaugCycle (C := C) (c₀ := c₀) hc₀ h) = coaugElem A c₀ d h := by
  unfold coaugCycle
  have h2 := congrArg (fun (f : ModuleCat.of A A ⟶ C.X d) => f.hom 1)
    (C.liftCycles_i (coaugHom (C := C) (c₀ := c₀) h) (d+1)
      (ComplexShape.next_eq' _ (ComplexShape.up_mk d (d+1) rfl)) (coaugHom_comp_d hc₀ h))
  rw [ConcreteCategory.comp_apply] at h2
  rw [h2]
  show (coaugHom (C := C) (c₀ := c₀) h).hom 1 = coaugElem A c₀ d h
  show (c₀ ≫ (C.XIsoOfEq h.symm).hom).hom 1 = coaugElem A c₀ d h
  rw [ConcreteCategory.comp_apply]
  rfl

/-! ## An element of the cycles with prescribed underlying element -/

lemma exists_cycle_eq {d : ℤ} (z : ↥(C.X d)) (hz : (C.d d (d+1)).hom z = 0) :
    ∃ zc : ↥(C.cycles d), (C.iCycles d).hom zc = z := by
  let φ : ModuleCat.of A A ⟶ C.X d :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton A ↥(C.X d) z)
  have hφ : φ ≫ C.d d (d+1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simpa [φ, ModuleCat.hom_comp, LinearMap.toSpanSingleton_apply] using hz
  refine ⟨(C.liftCycles φ (d+1)
    (ComplexShape.next_eq' _ (ComplexShape.up_mk d (d+1) rfl)) hφ).hom 1, ?_⟩
  have h := congrArg (fun (f : ModuleCat.of A A ⟶ C.X d) => f.hom 1)
    (C.liftCycles_i φ (d+1) (ComplexShape.next_eq' _ (ComplexShape.up_mk d (d+1) rfl)) hφ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  simp [φ, LinearMap.toSpanSingleton_apply]

end Aux


/-- Fallback for `Work.DSMX0U.exists_gen_sigma` (self-contained copy, no import of the child). -/
theorem step_gen_sigma_aux {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0} {d : ℤ}
    (hc₀ : ∀ j : ℤ, c₀ ≫ C.d 0 j = 0)
    (hfg : Module.Finite A (C.homology d)) :
    ∃ (gen : ModuleCat.{a} A) (instFree : Module.Free A gen) (instFin : Module.Finite A gen)
      (σ : gen ⟶ C.cycles d),
      (∀ z : ↥(C.X d), (C.d d (d + 1)).hom z = 0 →
        ∃ g : ↥gen, (C.iCycles d).hom (σ.hom g) - z ∈
          LinearMap.range (C.d (d - 1) d).hom) ∧
      (∀ (h : d = 0), ∃ g : ↥gen,
        (C.iCycles d).hom (σ.hom g) = coaugElem A c₀ d h) := by
  obtain ⟨n, σF, hσF⟩ := exists_surj_homologyπ (C := C) (d := d) hfg
  let η : ↥(C.cycles d) :=
    if h : d = 0 then coaugCycle (C := C) (c₀ := c₀) hc₀ h else 0
  let gen : ModuleCat.{a} A := pairMod A (ModuleCat.of A (Fin n → A)) (ModuleCat.of A A)
  let σHom : ↥gen →ₗ[A] ↥(C.cycles d) :=
    LinearMap.coprod (σF.hom)
      (LinearMap.toSpanSingleton A ↥(C.cycles d) η :
        ↥(ModuleCat.of A A) →ₗ[A] ↥(C.cycles d))
  let σ : gen ⟶ C.cycles d := ModuleCat.ofHom σHom
  refine ⟨gen, inferInstance, inferInstance, σ, ?_, ?_⟩
  · intro z hz
    obtain ⟨zc, hzc⟩ := exists_cycle_eq (C := C) z hz
    obtain ⟨x, hx⟩ := hσF ((C.homologyπ d).hom zc)
    refine ⟨(x, (0:A)), ?_⟩
    have hσx : σ.hom (x, (0:A)) = σF.hom x := by
      change (LinearMap.coprod (σF.hom)
          (LinearMap.toSpanSingleton A ↥(C.cycles d) η :
            ↥(ModuleCat.of A A) →ₗ[A] ↥(C.cycles d)))
          (x, (0:↥(ModuleCat.of A A))) = σF.hom x
      simp [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]
    rw [hσx, ← hzc]
    exact (homologyπ_eq_iff (C := C) (d := d) (σF.hom x) zc).mp hx
  · intro h
    refine ⟨((0:Fin n → A), (1:A)), ?_⟩
    have hσ0 : σ.hom ((0:Fin n → A), (1:A)) = η := by
      change (LinearMap.coprod (σF.hom)
          (LinearMap.toSpanSingleton A ↥(C.cycles d) η :
            ↥(ModuleCat.of A A) →ₗ[A] ↥(C.cycles d)))
          ((0:↥(ModuleCat.of A (Fin n → A))), (1:↥(ModuleCat.of A A))) = η
      simp [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]
    rw [hσ0]
    have hη : η = coaugCycle (C := C) (c₀ := c₀) hc₀ h := by
      show (if h' : d = 0 then coaugCycle (C := C) (c₀ := c₀) hc₀ h' else 0) = _
      rw [dite_eq_left h]
    rw [hη]
    exact iCycles_coaugCycle (C := C) (c₀ := c₀) hc₀ h

end Fallback

end Work.DSMX0U
