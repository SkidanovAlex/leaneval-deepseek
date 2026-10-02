import Mathlib
import Submission.Work.Cohomology.Crux.vkOvlDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two chart restrictions of the pair `(Vk(-2), Mk(-2))`

`Vk(-2)` is covered by the two chart images `vkU` and `vkV`, with overlap `vkOvl = U ∩ V` and
`Mk(-2) = vkPairA` the unit sphere bundle.  This file collects the relative cochain complexes and
the restriction maps between them which the restriction

  `H⁴(Vk(-2), Mk(-2)) ⟶ H⁴(U∩V, (U∩V)∩Mk(-2))`

is built from:

* `USpace`, `VSpace`, `WSpace` — the three subspaces as `TopCat`s;
* `AU`, `AV` — the trace of the sphere bundle on each chart;
* `rUmap`, `rVmap` — the restrictions of the pair `(Vk,Mk)` to the two chart pairs;
* `rhoUmap`, `rhoVmap` — the restrictions of the two chart pairs to the overlap;
* `rhoMap` — the restriction of `(Vk,Mk)` to the overlap (the map of the target theorem);
* the factorisations `rhoMap = rUmap ≫ rhoUmap` and `rhoMap = rVmap ≫ rhoVmap`.

Everything is written with the implicit space arguments of `relComplexMap` passed explicitly: at the
default transparency the unifier otherwise diverges when it has to unfold `↥(U ∩ V)` (see
`Submission/Work/Cohomology/Endgame/NOTES.md` §33).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology.Ovl

noncomputable section

/-- The first chart of `Vk(-2)`, as a space. -/
abbrev USpace : TopCat := TopCat.of ↥(Crux.vkU)

/-- The trace of the sphere bundle on the first chart. -/
abbrev AU : Set ↥(Crux.vkU) := {y | (y : vkPairX) ∈ vkPairA}

/-- The second chart of `Vk(-2)`, as a space. -/
abbrev VSpace : TopCat := TopCat.of ↥(Crux.vkV)

/-- The trace of the sphere bundle on the second chart. -/
abbrev AV : Set ↥(Crux.vkV) := {y | (y : vkPairX) ∈ vkPairA}

/-- The overlap of the two charts, as a space. -/
abbrev WSpace : TopCat := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)

/-- The inclusion of the overlap into the first chart. -/
def inclWU : WSpace ⟶ USpace :=
  TopCat.ofHom ⟨fun z => (⟨(z : vkPairX), z.2.1⟩ : ↥(Crux.vkU)),
    Continuous.subtype_mk continuous_subtype_val (fun z => z.2.1)⟩

/-- The inclusion of the overlap into the second chart. -/
def inclWV : WSpace ⟶ VSpace :=
  TopCat.ofHom ⟨fun z => (⟨(z : vkPairX), z.2.2⟩ : ↥(Crux.vkV)),
    Continuous.subtype_mk continuous_subtype_val (fun z => z.2.2)⟩

/-- **Contravariant functoriality of `relComplexMap`** (local copy, so that this module does not
depend on a module that clashes with `Work.Cohomology.cappedPairDefs`). -/
theorem relComplexMap_comp_ovl {X₁ X₂ X₃ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (A₃ : Set X₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h₁ : ∀ x ∈ A₁, (ConcreteCategory.hom f) x ∈ A₂)
    (h₂ : ∀ y ∈ A₂, (ConcreteCategory.hom g) y ∈ A₃) :
    relComplexMap ℤ A₁ A₃ (f ≫ g) (fun x hx => h₂ (f x) (h₁ x hx))
      = relComplexMap ℤ A₂ A₃ g h₂ ≫ relComplexMap ℤ A₁ A₂ f h₁ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  show ((relMapLM ℤ A₁ A₃ (f ≫ g) (fun x hx => h₂ (f x) (h₁ x hx)) n) x).1
      = ((relMapLM ℤ A₁ A₂ f h₁ n) ((relMapLM ℤ A₂ A₃ g h₂ n) x)).1
  simp only [relComplexMap_f, dualChainMap_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_ofHom, relMapLM_coe]

/-- **Proof irrelevance of the compatibility hypothesis of `relComplexMap`.** -/
theorem relComplexMap_hcongr {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h h' : ∀ x ∈ A₁, (ConcreteCategory.hom f) x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h = relComplexMap ℤ A₁ A₂ f h' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The restriction of the pair `(Vk(-2), Mk(-2))` to the first chart. -/
def rUmap : relComplex ℤ vkPairX vkPairA ⟶ relComplex ℤ USpace AU :=
  relComplexMap (X₁ := USpace) (X₂ := vkPairX) ℤ AU vkPairA
    (subtypeIncl vkPairX Crux.vkU) (fun x hx => hx)

/-- The restriction of the pair `(Vk(-2), Mk(-2))` to the second chart. -/
def rVmap : relComplex ℤ vkPairX vkPairA ⟶ relComplex ℤ VSpace AV :=
  relComplexMap (X₁ := VSpace) (X₂ := vkPairX) ℤ AV vkPairA
    (subtypeIncl vkPairX Crux.vkV) (fun x hx => hx)

/-- The restriction of the pair `(U, U ∩ A)` to the overlap. -/
def rhoUmap : relComplex ℤ USpace AU ⟶ relComplex ℤ WSpace Crux.vkOvlA :=
  relComplexMap (X₁ := WSpace) (X₂ := USpace) ℤ Crux.vkOvlA AU inclWU
    (fun x hx => hx)

/-- The restriction of the pair `(V, V ∩ A)` to the overlap. -/
def rhoVmap : relComplex ℤ VSpace AV ⟶ relComplex ℤ WSpace Crux.vkOvlA :=
  relComplexMap (X₁ := WSpace) (X₂ := VSpace) ℤ Crux.vkOvlA AV inclWV
    (fun x hx => hx)

/-- The restriction of the pair `(Vk(-2), Mk(-2))` to the overlap: the map of the target theorem. -/
def rhoMap : relComplex ℤ vkPairX vkPairA ⟶ relComplex ℤ WSpace Crux.vkOvlA :=
  relComplexMap (X₁ := WSpace) (X₂ := vkPairX) ℤ Crux.vkOvlA vkPairA
    (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) (fun x hx => hx)

/-- The composite of the inclusion of the overlap into the first chart with the inclusion of the
first chart into `Vk(-2)` is the inclusion of the overlap into `Vk(-2)`. -/
theorem inclWU_comp :
    inclWU ≫ subtypeIncl vkPairX Crux.vkU = subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV) := by
  apply TopCat.hom_ext
  ext z
  rfl

/-- The same for the second chart. -/
theorem inclWV_comp :
    inclWV ≫ subtypeIncl vkPairX Crux.vkV = subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV) := by
  apply TopCat.hom_ext
  ext z
  rfl

/-- **Congruence of `relComplexMap` in the map of pairs.** -/
theorem relComplexMap_congr_map {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) {f f' : X₁ ⟶ X₂}
    (hf : f = f') (h : ∀ x ∈ A₁, (ConcreteCategory.hom f) x ∈ A₂)
    (h' : ∀ x ∈ A₁, (ConcreteCategory.hom f') x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h = relComplexMap ℤ A₁ A₂ f' h' := by
  subst hf
  exact relComplexMap_hcongr A₁ A₂ f h h'

/-- **The restriction to the overlap factors through the first chart.** -/
theorem rhoMap_eq_rUmap_comp : rhoMap = rUmap ≫ rhoUmap := by
  have h := relComplexMap_comp_ovl (A₁ := Crux.vkOvlA) (A₂ := AU) (A₃ := vkPairA)
    (f := inclWU) (g := subtypeIncl vkPairX Crux.vkU)
    (h₁ := fun x hx => hx) (h₂ := fun x hx => hx)
  rw [rhoMap, rUmap, rhoUmap, ← h]
  exact (relComplexMap_congr_map (X₁ := WSpace) (X₂ := vkPairX) Crux.vkOvlA vkPairA
    (f := inclWU ≫ subtypeIncl vkPairX Crux.vkU)
    (f' := subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) inclWU_comp
    (fun x hx => hx) (fun x hx => hx)).symm

/-- **The restriction to the overlap factors through the second chart.** -/
theorem rhoMap_eq_rVmap_comp : rhoMap = rVmap ≫ rhoVmap := by
  have h := relComplexMap_comp_ovl (A₁ := Crux.vkOvlA) (A₂ := AV) (A₃ := vkPairA)
    (f := inclWV) (g := subtypeIncl vkPairX Crux.vkV)
    (h₁ := fun x hx => hx) (h₂ := fun x hx => hx)
  rw [rhoMap, rVmap, rhoVmap, ← h]
  exact (relComplexMap_congr_map (X₁ := WSpace) (X₂ := vkPairX) Crux.vkOvlA vkPairA
    (f := inclWV ≫ subtypeIncl vkPairX Crux.vkV)
    (f' := subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) inclWV_comp
    (fun x hx => hx) (fun x hx => hx)).symm


/-- **The chart-model ("retraction square") lemma.**

Let `(W,AW)`, `(U,AU)`, `(F,AF)`, `(S,AS)` be pairs of spaces and let
`i : W ⟶ U`, `rU : U ⟶ F`, `rW : W ⟶ S`, `g : S ⟶ F`, `j' : F ⟶ S`, `k : S ⟶ W` be maps of pairs
satisfying the *on-the-nose* identity `rU ∘ i = g ∘ rW` (i.e. `i ≫ rU = rW ≫ g`), together with the
two *cohomological* identities
`j'* ≫ g* = 𝟙` and `k* ≫ rW* = 𝟙`
on the relative cochain complexes.  Then the pullback `i* : C^•(U,AU) → C^•(W,AW)` induces a
surjective map on relative cohomology in every degree.

The two cohomological identities are what one obtains from the *homotopies* `j' ∘ g ≃ id_S` and
`k ∘ rW ≃ id_W` of maps of pairs (relative homotopy invariance), which hold in the chart models of
`U ≅ ℝ⁴×ℍ` and `W ≅ {x ≠ 0}×ℍ` with `S = {‖x‖ = 1}` and `F = {basePt}×ℍ`. -/
theorem surjective_of_retraction_square {U W F S : TopCat}
    (AU : Set ↥U) (AW : Set ↥W) (AF : Set ↥F) (AS : Set ↥S)
    (i : W ⟶ U) (hi : ∀ x ∈ AW, (ConcreteCategory.hom i) x ∈ AU)
    (rU : U ⟶ F) (hrU : ∀ x ∈ AU, (ConcreteCategory.hom rU) x ∈ AF)
    (rW : W ⟶ S) (hrW : ∀ x ∈ AW, (ConcreteCategory.hom rW) x ∈ AS)
    (g : S ⟶ F) (hg : ∀ x ∈ AS, (ConcreteCategory.hom g) x ∈ AF)
    (j' : F ⟶ S) (hj' : ∀ x ∈ AF, (ConcreteCategory.hom j') x ∈ AS)
    (k : S ⟶ W) (hk : ∀ x ∈ AS, (ConcreteCategory.hom k) x ∈ AW)
    (hA : i ≫ rU = rW ≫ g)
    (hB : relComplexMap ℤ AF AS j' hj' ≫ relComplexMap ℤ AS AF g hg = 𝟙 (relComplex ℤ S AS))
    (hC : relComplexMap ℤ AS AW k hk ≫ relComplexMap ℤ AW AS rW hrW = 𝟙 (relComplex ℤ W AW))
    (n : ℕ) :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap ℤ AW AU i hi) n)) := by
  -- the contravariant form of the commuting square
  have hα : (relComplexMap ℤ AU AF rU hrU) ≫ (relComplexMap ℤ AW AU i hi)
      = (relComplexMap ℤ AS AF g hg) ≫ (relComplexMap ℤ AW AS rW hrW) := by
    rw [← relComplexMap_comp_ovl (A₁ := AW) (A₂ := AU) (A₃ := AF) i rU hi hrU,
      ← relComplexMap_comp_ovl (A₁ := AW) (A₂ := AS) (A₃ := AF) rW g hrW hg]
    exact relComplexMap_congr_map (A₁ := AW) (A₂ := AF) hA _ _
  -- the composite `k* ≫ j'* ≫ rU*` is a right inverse of `i*`
  have hkey : ((relComplexMap ℤ AS AW k hk) ≫ (relComplexMap ℤ AF AS j' hj')
      ≫ (relComplexMap ℤ AU AF rU hrU)) ≫ (relComplexMap ℤ AW AU i hi)
      = 𝟙 (relComplex ℤ W AW) := by
    have e1 : ((relComplexMap ℤ AS AW k hk) ≫ (relComplexMap ℤ AF AS j' hj')
          ≫ (relComplexMap ℤ AU AF rU hrU)) ≫ (relComplexMap ℤ AW AU i hi)
        = (relComplexMap ℤ AS AW k hk) ≫ ((relComplexMap ℤ AF AS j' hj')
          ≫ ((relComplexMap ℤ AU AF rU hrU) ≫ (relComplexMap ℤ AW AU i hi))) := by
      simp only [Category.assoc]
    have e2 : (relComplexMap ℤ AS AW k hk) ≫ ((relComplexMap ℤ AF AS j' hj')
          ≫ ((relComplexMap ℤ AU AF rU hrU) ≫ (relComplexMap ℤ AW AU i hi)))
        = (relComplexMap ℤ AS AW k hk) ≫ ((relComplexMap ℤ AF AS j' hj')
          ≫ ((relComplexMap ℤ AS AF g hg) ≫ (relComplexMap ℤ AW AS rW hrW))) := by
      rw [hα]
    have e3 : (relComplexMap ℤ AS AW k hk) ≫ ((relComplexMap ℤ AF AS j' hj')
          ≫ ((relComplexMap ℤ AS AF g hg) ≫ (relComplexMap ℤ AW AS rW hrW)))
        = (relComplexMap ℤ AS AW k hk)
          ≫ (((relComplexMap ℤ AF AS j' hj') ≫ (relComplexMap ℤ AS AF g hg))
            ≫ (relComplexMap ℤ AW AS rW hrW)) := by
      simp only [Category.assoc]
    have e4 : (relComplexMap ℤ AS AW k hk)
          ≫ (((relComplexMap ℤ AF AS j' hj') ≫ (relComplexMap ℤ AS AF g hg))
            ≫ (relComplexMap ℤ AW AS rW hrW))
        = (relComplexMap ℤ AS AW k hk) ≫ (𝟙 (relComplex ℤ S AS)
            ≫ (relComplexMap ℤ AW AS rW hrW)) := by
      rw [hB]
    have e5 : (relComplexMap ℤ AS AW k hk) ≫ (𝟙 (relComplex ℤ S AS)
          ≫ (relComplexMap ℤ AW AS rW hrW))
        = (relComplexMap ℤ AS AW k hk) ≫ (relComplexMap ℤ AW AS rW hrW) := by
      rw [Category.id_comp]
    exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans hC))))
  -- conclude
  intro y
  refine ⟨(ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      ((relComplexMap ℤ AS AW k hk) ≫ (relComplexMap ℤ AF AS j' hj')
        ≫ (relComplexMap ℤ AU AF rU hrU)) n)) y, ?_⟩
  have h4 : HomologicalComplex.homologyMap
        ((relComplexMap ℤ AS AW k hk) ≫ (relComplexMap ℤ AF AS j' hj')
          ≫ (relComplexMap ℤ AU AF rU hrU)) n
      ≫ HomologicalComplex.homologyMap (relComplexMap ℤ AW AU i hi) n
      = 𝟙 ((relComplex ℤ W AW).homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, hkey, HomologicalComplex.homologyMap_id]
  have h5 := congrArg (fun (φ : (relComplex ℤ W AW).homology n
      ⟶ (relComplex ℤ W AW).homology n) => (ModuleCat.Hom.hom φ) y) h4
  simpa [ModuleCat.hom_comp] using h5

end

end Work.Cohomology.Ovl
