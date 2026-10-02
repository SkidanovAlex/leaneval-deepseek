import Mathlib
import Submission.Work.StemsB.FibrewiseTrivIso
import Submission.Work.StemsB.FibreTrivial
import Submission.Work.StemsB.WangSphereHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The comparison ("clutching") maps of the two trivialisations over the collar

`Work.StemsB.FibrewiseTrivial p W d₀` is a structure of maps **over the base**
(`fibTrivΦ_fst`, `fibTrivΨ_fst`: the first component of `fibTrivΦ x` is `p x`, and
`p (fibTrivΨ y).1 = y.1`).  Consequently, on the collar `C = sphLoopCollar b = O ∩ G` the two
trivialisations can be composed *genuinely* (no `Classical.choice` of a `Nonempty`):

* `collarClutchG : C × F_G → O × F_O`, `q ↦ Φ_O (Ψ_G q)`, where `F_G = p⁻¹{d_G.1}` and
  `F_O = p⁻¹{dOuter b} = p⁻¹{∞}` (the fibre of `WangCohFsp`);
* `collarClutchO : C × F_O → G × F_G`, `q ↦ Φ_G (Ψ_O q)`.

Both are **continuous maps over the base** (`collarClutchG_fst`, `collarClutchO_fst`), so the
induced maps on cohomology are **ring maps** (`collarClutchGCoh`, `collarClutchOCoh`).

The second component of `collarClutchG` is the *clutching map* `λ_G : C × F_G → F_O` of the two
trivialisations, and that of `collarClutchO` is the inverse comparison `λ_O : C × F_O → F_G`;
these are the maps whose induced maps on cohomology intertwine the transgression with the
suspension class (`D2_PLAN.md` §2, `D2_STATUS_LEMMA_AGENT.md` §4octies).
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- A class of `p ⁻¹' {d₀.1}`-shaped point: if the base point of a point of `↥W × p⁻¹{d₀.1}` lies
in `S`, then the corresponding point of the total space lies over `S`. -/
theorem fibTrivΨ_mem {B : Type} [TopologicalSpace B] {p : C(E, B)} (W : Set B) (d₀ : ↥W)
    (hT : FibrewiseTrivial p W d₀) (y : ↥W × ↥(p ⁻¹' {d₀.1})) (S : Set B)
    (h : (y.1 : B) ∈ S) : (fibTrivΨ p W d₀ hT y : E) ∈ p ⁻¹' S := by
  rw [Set.mem_preimage, fibTrivΨ_fst p W d₀ hT y]
  exact h

/-- The collar cut out by `sphLoopCollar b` inside `↥(sphLoopOuter b) × Y` (the mirror of
`sphLoopCollarProd`, which cuts it out inside `↥(sphLoopBig b) × Y`). -/
def sphLoopCollarProdOuter (b : ℕ) (Y : Type) : Set (↥(sphLoopOuter b) × Y) :=
  {x | (x.1 : SphModel b) ∈ sphLoopCollar b}

/-- **The comparison map `C × F_G → O × F_O`**: `q ↦ Φ_O (Ψ_G q)`.  (`Ψ_G q` lies over `q.1.1 ∈ C`,
hence in `p⁻¹C ⊆ p⁻¹O`.) -/
def collarClutchG (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    C(↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})),
      ↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})) :=
  ⟨fun q => fibTrivΦ p (sphLoopOuter b) (dOuter b) hT_O
      ⟨(fibTrivΨ p (sphLoopBig b) d_G hT_G q.1).1,
        fibTrivΨ_mem (sphLoopBig b) d_G hT_G q.1 (sphLoopOuter b) q.2.1⟩, by fun_prop⟩

/-- **The comparison map `C × F_O → G × F_G`**: `q ↦ Φ_G (Ψ_O q)`. -/
def collarClutchO (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    C(↥(sphLoopCollarProdOuter b ↥(p ⁻¹' {(dOuter b).1})),
      ↥(sphLoopBig b) × ↥(p ⁻¹' {d_G.1})) :=
  ⟨fun q => fibTrivΦ p (sphLoopBig b) d_G hT_G
      ⟨(fibTrivΨ p (sphLoopOuter b) (dOuter b) hT_O q.1).1,
        fibTrivΨ_mem (sphLoopOuter b) (dOuter b) hT_O q.1 (sphLoopBig b) q.2.2⟩, by fun_prop⟩

/-- **The comparison map `collarClutchG` lies over the base**: its first component is `p` of the
underlying point. -/
theorem collarClutchG_fst (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (q : ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1}))) :
    (collarClutchG b p d_G hT_G hT_O q).1
      = ⟨p (fibTrivΨ p (sphLoopBig b) d_G hT_G q.1).1,
          fibTrivΨ_mem (sphLoopBig b) d_G hT_G q.1 (sphLoopOuter b) q.2.1⟩ :=
  fibTrivΦ_fst p (sphLoopOuter b) (dOuter b) hT_O
    ⟨(fibTrivΨ p (sphLoopBig b) d_G hT_G q.1).1,
      fibTrivΨ_mem (sphLoopBig b) d_G hT_G q.1 (sphLoopOuter b) q.2.1⟩

/-- The corresponding statement for `collarClutchO`. -/
theorem collarClutchO_fst (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (q : ↥(sphLoopCollarProdOuter b ↥(p ⁻¹' {(dOuter b).1}))) :
    (collarClutchO b p d_G hT_G hT_O q).1
      = ⟨p (fibTrivΨ p (sphLoopOuter b) (dOuter b) hT_O q.1).1,
          fibTrivΨ_mem (sphLoopOuter b) (dOuter b) hT_O q.1 (sphLoopBig b) q.2.2⟩ :=
  fibTrivΦ_fst p (sphLoopBig b) d_G hT_G
    ⟨(fibTrivΨ p (sphLoopOuter b) (dOuter b) hT_O q.1).1,
      fibTrivΨ_mem (sphLoopOuter b) (dOuter b) hT_O q.1 (sphLoopBig b) q.2.2⟩

/-- The **clutching map** `λ_G : C × F_G ⟶ F_O`, the second component of `collarClutchG`.  Its
target is the fibre `p⁻¹{∞}` of `WangCohFsp`. -/
def collarLambdaG (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    C(↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})), ↥(p ⁻¹' {(dOuter b).1})) :=
  ⟨fun q => (collarClutchG b p d_G hT_G hT_O q).2, by fun_prop⟩

/-- The **inverse clutching map** `λ_O : C × F_O ⟶ F_G`, the second component of `collarClutchO`. -/
def collarLambdaO (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    C(↥(sphLoopCollarProdOuter b ↥(p ⁻¹' {(dOuter b).1})), ↥(p ⁻¹' {d_G.1})) :=
  ⟨fun q => (collarClutchO b p d_G hT_G hT_O q).2, by fun_prop⟩

/-- The **ring map on cohomology** induced by `collarClutchG`:
`H^*(↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})) ⟶ H^*(↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})))`. -/
noncomputable def collarClutchGCoh (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (n : ℕ) :
    Work.Cohomology.singularCohomology ℤ n
        (TopCat.of (↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1}))) ⟶
      Work.Cohomology.singularCohomology ℤ n
        (TopCat.of ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1}))) :=
  Work.Cohomology.singularCohomologyMap ℤ
    (TopCat.of ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})))
    (TopCat.of (↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})))
    (TopCat.ofHom (collarClutchG b p d_G hT_G hT_O)) n

/-- The **ring map on cohomology** induced by `collarClutchO`. -/
noncomputable def collarClutchOCoh (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (n : ℕ) :
    Work.Cohomology.singularCohomology ℤ n
        (TopCat.of (↥(sphLoopBig b) × ↥(p ⁻¹' {d_G.1}))) ⟶
      Work.Cohomology.singularCohomology ℤ n
        (TopCat.of ↥(sphLoopCollarProdOuter b ↥(p ⁻¹' {(dOuter b).1}))) :=
  Work.Cohomology.singularCohomologyMap ℤ
    (TopCat.of ↥(sphLoopCollarProdOuter b ↥(p ⁻¹' {(dOuter b).1})))
    (TopCat.of (↥(sphLoopBig b) × ↥(p ⁻¹' {d_G.1})))
    (TopCat.ofHom (collarClutchO b p d_G hT_G hT_O)) n

/-- The **pullback along the clutching map** `λ_G^* : H^*(F_O) ⟶ H^*(C × F_G)`: the ring map
`Work.Cohomology.singularCohomologyMap` of `collarLambdaG`.  This is the map `u` of the collar
computation (`D2_STATUS_LEMMA_AGENT.md` §4octies). -/
noncomputable def collarLambdaGCoh (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (n : ℕ) :
    Work.Cohomology.singularCohomology ℤ n (TopCat.of ↥(p ⁻¹' {(dOuter b).1})) ⟶
      Work.Cohomology.singularCohomology ℤ n
        (TopCat.of ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1}))) :=
  Work.Cohomology.singularCohomologyMap ℤ
    (TopCat.of ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})))
    (TopCat.of ↥(p ⁻¹' {(dOuter b).1}))
    (TopCat.ofHom (collarLambdaG b p d_G hT_G hT_O)) n

end

end Work.StemsB
