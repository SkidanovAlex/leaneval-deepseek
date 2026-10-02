import Submission.Work.StemsB.FibrewiseTrivIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibrewise triviality on *pairs* (the map `ε` of the pentagon)

`FibrewiseTrivial p W d₀` trivialises the fibration over `W` with fibre `p⁻¹d₀`, with homotopies
that preserve the base coordinate.  This file draws the **relative** consequence: for every subset
`A ⊆ W`, the induced map of pairs

  `(p⁻¹W, p⁻¹A) ⟶ (W × F, A × F)`,  `F = p⁻¹(d₀)`

induces a quasi-isomorphism of relative chain complexes.  The important point is that the two
homotopies of the triviality are *fibrewise* (base coordinate preserved), so they restrict to the
preimages of `A`; the conclusion is then the five lemma
(`Work.Cohomology.relChainsMapOf_homologyMap_isIso`).

This is the map called `ε` in `Submission/Work/StemsB/SERRE_PLAN.md` §2.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Work.StemsB

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
variable (p : C(E, B)) (W : Set B) (d₀ : ↥W) (A : Set B)

/-- `p⁻¹A` as a subset of `↥(p⁻¹W)`: the relative part on the total space of the two pairs. -/
abbrev relA : Set ↥(p ⁻¹' W) := {x | (x : E) ∈ p ⁻¹' A}

/-- `A × F` as a subset of `↥W × F`: the relative part of the trivialised pair. -/
abbrev relB : Set (↥W × ↥(p ⁻¹' {d₀.1})) := {y | (y.1 : B) ∈ A}

/-- The trivialisation restricted to the pair, on the total spaces. -/
def relΦA (hT : FibrewiseTrivial p W d₀) :
    TopCat.of (relA p W A) ⟶ TopCat.of (relB p W d₀ A) :=
  TopCat.ofHom
    ⟨fun x => ⟨fibTrivΦ p W d₀ hT x.1, by
        show ((fibTrivΦ p W d₀ hT x.1).1 : B) ∈ A
        rw [fibTrivΦ_fst p W d₀ hT]
        exact x.2⟩,
     Continuous.subtype_mk (f := fun x : ↥(relA p W A) => fibTrivΦ p W d₀ hT x.1)
       ((fibTrivΦ p W d₀ hT).continuous.comp continuous_subtype_val)
       (fun x => by
         show ((fibTrivΦ p W d₀ hT x.1).1 : B) ∈ A
         rw [fibTrivΦ_fst p W d₀ hT]
         exact x.2)⟩

/-- The inverse trivialisation restricted to the pair. -/
def relΨA (hT : FibrewiseTrivial p W d₀) :
    TopCat.of (relB p W d₀ A) ⟶ TopCat.of (relA p W A) :=
  TopCat.ofHom
    ⟨fun y => ⟨fibTrivΨ p W d₀ hT y.1, by
        show ((fibTrivΨ p W d₀ hT y.1) : E) ∈ p ⁻¹' A
        rw [Set.mem_preimage, fibTrivΨ_fst p W d₀ hT]
        exact y.2⟩,
     Continuous.subtype_mk (f := fun y : ↥(relB p W d₀ A) => fibTrivΨ p W d₀ hT y.1)
       ((fibTrivΨ p W d₀ hT).continuous.comp continuous_subtype_val)
       (fun y => by
         show ((fibTrivΨ p W d₀ hT y.1) : E) ∈ p ⁻¹' A
         rw [Set.mem_preimage, fibTrivΨ_fst p W d₀ hT]
         exact y.2)⟩

/-- The first homotopy, restricted to the preimage of `A`. -/
def relH (hT : FibrewiseTrivial p W d₀) :
    C(↥(relA p W A) × unitInterval, ↥(relA p W A)) :=
  ⟨fun z => ⟨fibTrivH p W d₀ hT (z.1.1, z.2), by
      show ((fibTrivH p W d₀ hT (z.1.1, z.2)) : E) ∈ p ⁻¹' A
      rw [Set.mem_preimage, fibTrivH_base p W d₀ hT]
      exact z.1.2⟩,
   Continuous.subtype_mk
     (f := fun z : ↥(relA p W A) × unitInterval => fibTrivH p W d₀ hT (z.1.1, z.2))
     ((fibTrivH p W d₀ hT).continuous.comp
       (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd))
     (fun z => by
       show ((fibTrivH p W d₀ hT (z.1.1, z.2)) : E) ∈ p ⁻¹' A
       rw [Set.mem_preimage, fibTrivH_base p W d₀ hT]
       exact z.1.2)⟩

/-- The second homotopy, restricted to `A × F` (the base coordinate is preserved). -/
def relK (hT : FibrewiseTrivial p W d₀) :
    C(↥(relB p W d₀ A) × unitInterval, ↥(relB p W d₀ A)) :=
  ⟨fun z => ⟨fibTrivK p W d₀ hT (z.1.1, z.2), by
      show ((fibTrivK p W d₀ hT (z.1.1, z.2)).1 : B) ∈ A
      rw [fibTrivK_fst p W d₀ hT]
      exact z.1.2⟩,
   Continuous.subtype_mk
     (f := fun z : ↥(relB p W d₀ A) × unitInterval => fibTrivK p W d₀ hT (z.1.1, z.2))
     ((fibTrivK p W d₀ hT).continuous.comp
       (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd))
     (fun z => by
       show ((fibTrivK p W d₀ hT (z.1.1, z.2)).1 : B) ∈ A
       rw [fibTrivK_fst p W d₀ hT]
       exact z.1.2)⟩

theorem relH_zero (hT : FibrewiseTrivial p W d₀) (x : ↥(relA p W A)) :
    relH p W d₀ A hT (x, 0) = x := by
  apply Subtype.ext
  exact fibTrivH_zero p W d₀ hT x.1

theorem relH_one (hT : FibrewiseTrivial p W d₀) (x : ↥(relA p W A)) :
    relH p W d₀ A hT (x, 1) = relΨA p W d₀ A hT (relΦA p W d₀ A hT x) := by
  apply Subtype.ext
  exact fibTrivH_one p W d₀ hT x.1

theorem relK_zero (hT : FibrewiseTrivial p W d₀) (y : ↥(relB p W d₀ A)) :
    relK p W d₀ A hT (y, 0) = y := by
  apply Subtype.ext
  exact fibTrivK_zero p W d₀ hT y.1

theorem relK_one (hT : FibrewiseTrivial p W d₀) (y : ↥(relB p W d₀ A)) :
    relK p W d₀ A hT (y, 1) = relΦA p W d₀ A hT (relΨA p W d₀ A hT y) := by
  apply Subtype.ext
  exact fibTrivK_one p W d₀ hT y.1

/-- The compatibility of the restricted trivialisation with the inclusions of the pairs. -/
theorem relΦA_subtypeIncl (hT : FibrewiseTrivial p W d₀) :
    Work.Cohomology.subtypeIncl (TopCat.of ↥(p ⁻¹' W)) (relA p W A)
        ≫ TopCat.ofHom (fibTrivΦ p W d₀ hT)
      = relΦA p W d₀ A hT
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (↥W × ↥(p ⁻¹' {d₀.1})))
            (relB p W d₀ A) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

/-- The two restricted homotopies, packaged as homotopies of `TopCat` morphisms. -/
def relHomotopyΦΨ (hT : FibrewiseTrivial p W d₀) :
    TopCat.Homotopy (relΦA p W d₀ A hT ≫ relΨA p W d₀ A hT)
      (𝟙 (TopCat.of (relA p W A))) :=
  topCatHomotopyOf (X := TopCat.of (relA p W A)) (Y := TopCat.of (relB p W d₀ A))
    (f := relΦA p W d₀ A hT) (g := relΨA p W d₀ A hT) (relH p W d₀ A hT)
    (fun x => relH_zero p W d₀ A hT x) (fun x => relH_one p W d₀ A hT x)

def relHomotopyΨΦ (hT : FibrewiseTrivial p W d₀) :
    TopCat.Homotopy (relΨA p W d₀ A hT ≫ relΦA p W d₀ A hT)
      (𝟙 (TopCat.of (relB p W d₀ A))) :=
  topCatHomotopyOf (X := TopCat.of (relB p W d₀ A)) (Y := TopCat.of (relA p W A))
    (f := relΨA p W d₀ A hT) (g := relΦA p W d₀ A hT) (relK p W d₀ A hT)
    (fun y => relK_zero p W d₀ A hT y) (fun y => relK_one p W d₀ A hT y)

/-- The chain map of relative complexes induced by the restricted trivialisation. -/
def relMap (hT : FibrewiseTrivial p W d₀) :
    Work.Cohomology.relChains (TopCat.of ↥(p ⁻¹' W)) (relA p W A) ⟶
      Work.Cohomology.relChains (TopCat.of (↥W × ↥(p ⁻¹' {d₀.1}))) (relB p W d₀ A) :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(p ⁻¹' W)) (TopCat.of (↥W × ↥(p ⁻¹' {d₀.1})))
    (relA p W A) (relB p W d₀ A) (TopCat.ofHom (fibTrivΦ p W d₀ hT)) (relΦA p W d₀ A hT)
    (relΦA_subtypeIncl p W d₀ A hT)

/-- **The map `ε` of the pentagon is a quasi-isomorphism.**  For every `A ⊆ W` the trivialisation
induces a quasi-isomorphism `C_*(p⁻¹W, p⁻¹A) ⟶ C_*(W × F, A × F)`. -/
theorem isIso_relMap (hT : FibrewiseTrivial p W d₀) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (relMap p W d₀ A hT) q) := by
  unfold relMap
  refine Work.Cohomology.relChainsMapOf_homologyMap_isIso (X := TopCat.of ↥(p ⁻¹' W))
    (Y := TopCat.of (↥W × ↥(p ⁻¹' {d₀.1}))) (relA p W A) (relB p W d₀ A)
    (TopCat.ofHom (fibTrivΦ p W d₀ hT)) (relΦA p W d₀ A hT)
    (relΦA_subtypeIncl p W d₀ A hT) q ?_ ?_
  · intro k
    exact isIso_fibTrivΦHomology hT k
  · intro k
    exact Work.Cohomology.homologyEquiv ℤ (TopCat.of (relA p W A)) (TopCat.of (relB p W d₀ A))
      (relΦA p W d₀ A hT) (relΨA p W d₀ A hT) (relHomotopyΦΨ p W d₀ A hT)
      (relHomotopyΨΦ p W d₀ A hT) k

end

end Work.StemsB
