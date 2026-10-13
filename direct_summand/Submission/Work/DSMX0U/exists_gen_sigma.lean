import Mathlib
import Submission.Work.DSMX0U.Cell

open CategoryTheory Limits

/-!
# DSMX0U — generators of the cohomology in one degree and the coaugmentation class

This file proves `Work.DSMX0U.exists_gen_sigma`: for a cochain complex `C` of `A`-modules whose
`d`-th cohomology is finitely generated, and a coaugmentation cocycle `c₀ : A ⟶ C⁰`, there are a
finitely generated free module `gen` and a map `σ : gen ⟶ C.cycles d` such that

* `σ` hits every cycle of `C` in degree `d` modulo boundaries (i.e. `gen → H^d(C)` is onto), and
* when `d = 0`, some generator of `gen` maps exactly onto the coaugmentation element `c₀ 1`.

The construction is the first half of the "pseudo-coherence" step of the area `MX0U`
(see `Submission/Work/DSMX0U/DESIGN.md`): it is the input that `Work.DSMX0U.StepData` consumes
(generators of `H^d` plus the coaugmentation generator).

## Structure of the proof

* `genSigma_exists_free_surj_of_span` — a finite free module surjects onto a module with a chosen
  finite spanning set, with one prescribed basis vector sent to a prescribed element.
* `genSigma_exists_lift_of_basis` — a surjection onto a free module can be lifted along its basis
  with one prescribed value on a basis vector.
* `genSigma_pOpcycles_eq_iff` — two elements of `C.X d` have equal image in `C.opcycles d` iff
  their difference is in the range of `C.d (d-1) d` (i.e. is a boundary); this is the concrete
  description of the quotient `C.X d ⧸ boundaries` that the statement is phrased with.
* `genSigma_pOpcycles_iCycles` — the compatibility of `pOpcycles` with `iCycles`, `homologyπ` and
  `homologyι` (the `ShortComplex.homology_π_ι` identity, elementwise).
* `genSigma_exists_cycle_lift` — every cycle of `C.X d` is `iCycles` of some element of
  `C.cycles d`.
* `genSigma_aux` — the main construction, given a finite spanning set of `H^d(C)` and a prescribed
  cycle `w₀` (the coaugmentation cycle when `d = 0`).
-/

namespace Work.DSMX0U

set_option linter.style.haveILetI false

universe a

variable {A : Type a} [CommRing A]

section Helpers

/-- **A free cover of a module with a prescribed value at one basis vector.**  If `S` is a finite
spanning set of `M` and `m₀ : M`, there is a surjective linear map from the free module on
`Option S` onto `M` sending the basis vector at `none` to `m₀`.  The extra `none` generator is
what makes both conditions compatible. -/
lemma genSigma_exists_free_surj_of_span {M : Type a} [AddCommGroup M] [Module A M]
    {S : Set M} [Fintype S] (hSspan : Submodule.span A S = ⊤) (m₀ : M) :
    ∃ f : (Option S → A) →ₗ[A] M,
      Function.Surjective f ∧ f ((Pi.basisFun A (Option S)) none) = m₀ := by
  classical
  let b := Pi.basisFun A (Option S)
  refine ⟨b.constr A (fun o => o.elim m₀ (fun i => (i : M))), ?_, ?_⟩
  · rw [← LinearMap.range_eq_top, Module.Basis.constr_range]
    have hsub : Set.range (Subtype.val : S → M) ⊆
        Set.range (fun o : Option S => o.elim m₀ (fun i => (i : M))) := by
      rintro x ⟨i, rfl⟩
      exact ⟨some i, rfl⟩
    have h2 : Submodule.span A (Set.range (Subtype.val : S → M)) = Submodule.span A S :=
      congrArg (Submodule.span A) (Subtype.range_val (s := S))
    have h1 : Submodule.span A S ≤ Submodule.span A
        (Set.range (fun o : Option S => o.elim m₀ (fun i => (i : M)))) := by
      rw [← h2]
      exact Submodule.span_mono hsub
    exact top_le_iff.mp (by rw [← hSspan]; exact h1)
  · rw [Module.Basis.constr_basis]
    exact rfl

/-- **A surjection onto a free module lifts along its basis, with a prescribed value.**  Given
`π : X →ₗ[A] Y` surjective, a linear map `f` from the free module on `ι`, and `w₀ : X` with
`f (b i₀) = π w₀`, there is a lift `σ` of `f` along `π` with `σ (b i₀) = w₀`. -/
lemma genSigma_exists_lift_of_basis {ι : Type a} [Fintype ι] [DecidableEq ι]
    {X : Type a} {Y : Type a} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (π : X →ₗ[A] Y) (hπ : Function.Surjective π) (i₀ : ι) (w₀ : X)
    (f : (ι → A) →ₗ[A] Y) (hf₀ : f ((Pi.basisFun A ι) i₀) = π w₀) :
    ∃ σ : (ι → A) →ₗ[A] X, π.comp σ = f ∧ σ ((Pi.basisFun A ι) i₀) = w₀ := by
  classical
  let b := Pi.basisFun A ι
  let ζ : ι → X := fun i => if i = i₀ then w₀ else Classical.choose (hπ (f (b i)))
  refine ⟨b.constr A ζ, ?_, ?_⟩
  · apply Module.Basis.ext
    intro i
    rw [LinearMap.comp_apply, Module.Basis.constr_basis]
    by_cases hi : i = i₀
    · subst hi
      have hζ : ζ i = w₀ := by simp [ζ]
      rw [hζ]
      exact hf₀.symm
    · have hζ : ζ i = Classical.choose (hπ (f (b i))) := by simp [ζ, hi]
      rw [hζ]
      exact Classical.choose_spec (hπ (f (b i)))
  · rw [Module.Basis.constr_basis]
    simp only [ζ, ↓reduceIte]

end Helpers

section Complex

variable {C : CochainComplex (ModuleCat.{a} A) ℤ}

/-- **The concrete description of `C.opcycles d`.**  Two elements of `C.X d` have the same image
in `C.opcycles d` (the cokernel of `C.d (d-1) d`) if and only if their difference is a boundary.
This is `ShortComplex.moduleCat_pOpcycles_eq_iff` transported across `opcyclesIsoSc'`, so that
the middle term is the same object `C.X d`. -/
lemma genSigma_pOpcycles_eq_iff (d : ℤ) (x y : ↥(C.X d)) :
    (C.pOpcycles d).hom x = (C.pOpcycles d).hom y ↔
      x - y ∈ LinearMap.range (C.d (d-1) d).hom := by
  have hi : (ComplexShape.up ℤ).prev d = d - 1 :=
    ComplexShape.prev_eq' (ComplexShape.up ℤ) (ComplexShape.up_mk (d-1) d (by ring))
  have hk : (ComplexShape.up ℤ).next d = d + 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℤ) (ComplexShape.up_mk d (d+1) (by ring))
  have hkeyEq := C.pOpcycles_opcyclesIsoSc'_hom (d-1) d (d+1) hi hk
  have hkey : ∀ z : ↥(C.X d),
      (C.sc' (d-1) d (d+1)).pOpcycles.hom z =
        ModuleCat.Hom.hom (C.opcyclesIsoSc' (d-1) d (d+1) hi hk).hom
          ((C.pOpcycles d).hom z) := by
    intro z
    have h := congrArg ModuleCat.Hom.hom hkeyEq
    simp only [ModuleCat.hom_comp] at h
    exact (LinearMap.congr_fun h z).symm
  have hinj : Function.Injective
      (ModuleCat.Hom.hom (C.opcyclesIsoSc' (d-1) d (d+1) hi hk).hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  constructor
  · intro h
    have h2 : (C.sc' (d-1) d (d+1)).pOpcycles.hom x =
        (C.sc' (d-1) d (d+1)).pOpcycles.hom y := by rw [hkey x, hkey y, h]
    exact (C.sc' (d-1) d (d+1)).moduleCat_pOpcycles_eq_iff x y |>.mp h2
  · intro h
    have h3 : (C.sc' (d-1) d (d+1)).pOpcycles.hom x =
        (C.sc' (d-1) d (d+1)).pOpcycles.hom y :=
      (C.sc' (d-1) d (d+1)).moduleCat_pOpcycles_eq_iff x y |>.mpr h
    rw [hkey x, hkey y] at h3
    exact hinj h3

/-- The `ShortComplex.homology_π_ι` identity, elementwise: passing from a cycle to its class in
cohomology and then back to `opcycles` is the same as passing to `opcycles` directly. -/
lemma genSigma_pOpcycles_iCycles (d : ℤ) (x : ↥(C.cycles d)) :
    (C.pOpcycles d).hom ((C.iCycles d).hom x) =
      (C.homologyι d).hom ((C.homologyπ d).hom x) := by
  have h := congrArg ModuleCat.Hom.hom (C.homology_π_ι d)
  simp only [ModuleCat.hom_comp] at h
  exact (LinearMap.congr_fun h x).symm

/-- **Every cycle is the inclusion of an element of the cycles.**  For a cycle `z` of `C` in
degree `d` there is an element `w` of `C.cycles d` with `iCycles d w = z`. -/
lemma genSigma_exists_cycle_lift (d : ℤ) (z : ↥(C.X d))
    (hz : (C.d d (d+1)).hom z = 0) :
    ∃ w : ↥(C.cycles d), (C.iCycles d).hom w = z := by
  have hk : (ComplexShape.up ℤ).next d = d + 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℤ) (ComplexShape.up_mk d (d+1) (by ring))
  let ℓ : ModuleCat.of A A ⟶ C.X d :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton A ↥(C.X d) z)
  have hℓ : ℓ.hom 1 = z := by
    rw [show ModuleCat.Hom.hom ℓ = LinearMap.toSpanSingleton A ↥(C.X d) z from rfl,
      LinearMap.toSpanSingleton_apply, one_smul]
  have h0 : ℓ ≫ C.d d (d+1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro u
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply, map_smul, hz, smul_zero]
    rfl
  refine ⟨(C.liftCycles ℓ (d+1) hk h0).hom 1, ?_⟩
  have h2 := congrArg ModuleCat.Hom.hom (C.liftCycles_i ℓ (d+1) hk h0)
  simp only [ModuleCat.hom_comp] at h2
  exact (LinearMap.congr_fun h2 1).trans hℓ

/-- The coaugmentation element in degree `0` is the image of `1` under the coaugmentation. -/
lemma genSigma_coaugElem_zero {c₀ : ModuleCat.of A A ⟶ C.X 0} (h : (0 : ℤ) = 0) :
    coaugElem A c₀ 0 h = c₀.hom 1 := by
  cases h
  simp [coaugElem]

end Complex

section Aux

variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {d : ℤ}

/-- **The main construction.**  Given a finite spanning set `S` of `H^d(C)` and a prescribed cycle
`w₀` of `C`, there are a finitely generated free module `gen`, a map `σ : gen ⟶ C.cycles d`
whose composite with `homologyπ d` is surjective, and a distinguished generator `g₀` of `gen`
whose image under `σ` is `w₀`. -/
lemma genSigma_aux (S : Set ↥(C.homology d)) (hSfin : S.Finite)
    (hSspan : Submodule.span A S = ⊤) (w₀ : ↥(C.cycles d)) :
    ∃ (gen : ModuleCat.{a} A) (_ : Module.Free A gen) (_ : Module.Finite A gen)
      (σ : gen ⟶ C.cycles d) (g₀ : ↥gen),
      (∀ z : ↥(C.X d), (C.d d (d+1)).hom z = 0 →
        ∃ g : ↥gen, (C.iCycles d).hom (σ.hom g) - z ∈
          LinearMap.range (C.d (d-1) d).hom) ∧
      (C.iCycles d).hom (σ.hom g₀) = (C.iCycles d).hom w₀ := by
  classical
  have hSft : Fintype S := hSfin.fintype
  haveI := hSft
  have hsurj : Function.Surjective (C.homologyπ d).hom :=
    (ModuleCat.epi_iff_surjective (C.homologyπ d)).mp inferInstance
  obtain ⟨f, hfsurj, hf₀⟩ :=
    genSigma_exists_free_surj_of_span (A := A) (S := S) hSspan ((C.homologyπ d).hom w₀)
  obtain ⟨σl, hcomp, hσ₀⟩ :=
    genSigma_exists_lift_of_basis (A := A) (ι := Option S) (π := (C.homologyπ d).hom)
      hsurj none w₀ f hf₀
  refine ⟨ModuleCat.of A (Option S → A), inferInstance, inferInstance, ModuleCat.ofHom σl,
    (Pi.basisFun A (Option S)) none, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw⟩ := genSigma_exists_cycle_lift (C := C) d z hz
    obtain ⟨g, hg⟩ := hfsurj ((C.homologyπ d).hom w)
    refine ⟨g, ?_⟩
    change (C.iCycles d).hom (σl g) - z ∈ LinearMap.range (C.d (d-1) d).hom
    rw [← genSigma_pOpcycles_eq_iff (C := C) d]
    rw [← hw]
    rw [genSigma_pOpcycles_iCycles, genSigma_pOpcycles_iCycles]
    rw [show (C.homologyπ d).hom (σl g) = (C.homologyπ d).hom w from
      (LinearMap.congr_fun hcomp g).trans hg]
  · change (C.iCycles d).hom (σl ((Pi.basisFun A (Option S)) none)) = (C.iCycles d).hom w₀
    rw [hσ₀]

end Aux

/-- **Generators of the cohomology in one degree, including the coaugmentation class.** -/
theorem exists_gen_sigma {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0} {d : ℤ}
    (hc₀ : ∀ j : ℤ, CategoryTheory.CategoryStruct.comp c₀ (C.d 0 j) = 0)
    (hfg : Module.Finite A (C.homology d)) :
    ∃ (gen : ModuleCat.{a} A) (instFree : Module.Free A gen) (instFin : Module.Finite A gen)
      (σ : gen ⟶ C.cycles d),
      (∀ z : ↥(C.X d), (C.d d (d + 1)).hom z = 0 →
        ∃ g : ↥gen, (C.iCycles d).hom (σ.hom g) - z ∈
          LinearMap.range (C.d (d - 1) d).hom) ∧
      (∀ (h : d = 0), ∃ g : ↥gen,
        (C.iCycles d).hom (σ.hom g) = Work.DSMX0U.coaugElem A c₀ d h) := by
  classical
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp hfg.fg_top
  have hSft : Fintype S := hSfin.fintype
  haveI := hSft
  by_cases hd : d = 0
  · subst hd
    have hz : (C.d 0 (0+1)).hom (c₀.hom 1) = 0 := by
      have h := congrArg ModuleCat.Hom.hom (hc₀ 1)
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      exact LinearMap.congr_fun h 1
    obtain ⟨w₀, hw₀⟩ := genSigma_exists_cycle_lift (C := C) 0 (c₀.hom 1) hz
    obtain ⟨gen, hfree, hfin, σ, g₀, hconj1, hconj2⟩ :=
      genSigma_aux (C := C) (d := 0) S hSfin hSspan w₀
    refine ⟨gen, hfree, hfin, σ, hconj1, ?_⟩
    intro h
    exact ⟨g₀, by rw [hconj2, genSigma_coaugElem_zero (C := C) (c₀ := c₀) h, hw₀]⟩
  · obtain ⟨gen, hfree, hfin, σ, _, hconj1, _⟩ :=
      genSigma_aux (C := C) (d := d) S hSfin hSspan 0
    exact ⟨gen, hfree, hfin, σ, hconj1, fun h => absurd h hd⟩

end Work.DSMX0U
