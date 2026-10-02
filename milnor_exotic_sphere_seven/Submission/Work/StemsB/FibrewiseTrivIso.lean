import Submission.Work.StemsB.CollarModel
import Submission.Work.StemsB.SerreSphereDefs
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.StemsB.SerreSphereStep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibrewise triviality input (T) of the pentagon

The second missing input of the pentagon of `Submission/Work/StemsB/SERRE_PLAN.md` §2 is the
**fibrewise triviality** of the fibration over the inner piece `W`.  This file draws its homological
consequence: if `FibrewiseTrivial p W d₀` holds (`SerreSphereDefs.lean`), then for every `A ⊆ W` the
map of relative chain complexes

  `C_*(p⁻¹W, p⁻¹A) ⟶ C_*(W × F, A × F)`,  `F = p⁻¹(d₀)`,

induced by the trivialisation `x ↦ (p x, Φ₀ x)`, is a **quasi-isomorphism**: the trivialisation is a
homotopy equivalence (with inverse `Ψ`), and — this is the point of the *fibrewise* form of the
hypothesis — both homotopies preserve the base coordinate, so they restrict to the preimages of `A`,
making the map on the relative parts a homotopy equivalence as well.  The conclusion then follows
from `Work.Cohomology.relChainsMapOf_isIso` (five lemma).

The trivialisation and its data are extracted from the hypothesis with `Classical.choose`
(`fibTrivΦ`, `fibTrivΨ`, `fibTrivH`, `fibTrivK`), so that the statement can name them.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Work.StemsB

variable {R : Type} [CommRing R]

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

section Data

variable (p : C(E, B)) (W : Set B) (d₀ : ↥W)

/-- The trivialisation map of a fibrewise triviality. -/
def fibTrivΦ (hT : FibrewiseTrivial p W d₀) :
    C(↥(p ⁻¹' W), ↥W × ↥(p ⁻¹' {d₀.1})) :=
  Classical.choose hT

/-- Its inverse. -/
def fibTrivΨ (hT : FibrewiseTrivial p W d₀) :
    C(↥W × ↥(p ⁻¹' {d₀.1}), ↥(p ⁻¹' W)) :=
  Classical.choose (Classical.choose_spec hT)

theorem fibTrivΦ_fst (hT : FibrewiseTrivial p W d₀) (x : ↥(p ⁻¹' W)) :
    (fibTrivΦ p W d₀ hT x).1 = ⟨p x.1, x.2⟩ :=
  (Classical.choose_spec (Classical.choose_spec hT)).1 x

theorem fibTrivΨ_fst (hT : FibrewiseTrivial p W d₀) (y : ↥W × ↥(p ⁻¹' {d₀.1})) :
    p (fibTrivΨ p W d₀ hT y).1 = (y.1 : B) :=
  (Classical.choose_spec (Classical.choose_spec hT)).2.1 y

/-- The fibrewise homotopy `id ≃ Ψ ∘ Φ`. -/
def fibTrivH (hT : FibrewiseTrivial p W d₀) :
    C(↥(p ⁻¹' W) × unitInterval, ↥(p ⁻¹' W)) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec hT)).2.2.1

theorem fibTrivH_zero (hT : FibrewiseTrivial p W d₀) (x : ↥(p ⁻¹' W)) :
    fibTrivH p W d₀ hT (x, 0) = x :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hT)).2.2.1).1 x

theorem fibTrivH_one (hT : FibrewiseTrivial p W d₀) (x : ↥(p ⁻¹' W)) :
    fibTrivH p W d₀ hT (x, 1) = fibTrivΨ p W d₀ hT (fibTrivΦ p W d₀ hT x) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hT)).2.2.1).2.1 x

theorem fibTrivH_base (hT : FibrewiseTrivial p W d₀) (x : ↥(p ⁻¹' W)) (t : unitInterval) :
    p (fibTrivH p W d₀ hT (x, t)).1 = p x.1 :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hT)).2.2.1).2.2 x t

/-- The fibrewise homotopy `id ≃ Φ ∘ Ψ`. -/
def fibTrivK (hT : FibrewiseTrivial p W d₀) :
    C((↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval, ↥W × ↥(p ⁻¹' {d₀.1})) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec hT)).2.2.2

theorem fibTrivK_zero (hT : FibrewiseTrivial p W d₀) (y : ↥W × ↥(p ⁻¹' {d₀.1})) :
    fibTrivK p W d₀ hT (y, 0) = y :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hT)).2.2.2).1 y

theorem fibTrivK_one (hT : FibrewiseTrivial p W d₀) (y : ↥W × ↥(p ⁻¹' {d₀.1})) :
    fibTrivK p W d₀ hT (y, 1) = fibTrivΦ p W d₀ hT (fibTrivΨ p W d₀ hT y) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hT)).2.2.2).2.1 y

theorem fibTrivK_fst (hT : FibrewiseTrivial p W d₀) (y : ↥W × ↥(p ⁻¹' {d₀.1}))
    (t : unitInterval) : (fibTrivK p W d₀ hT (y, t)).1 = y.1 :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hT)).2.2.2).2.2 y t

end Data

variable {p : C(E, B)} {W : Set B} {d₀ : ↥W}

/-! ## The total space -/

theorem isIso_fibTrivΦHomology (hT : FibrewiseTrivial p W d₀) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap R
      (TopCat.of ↥(p ⁻¹' W)) (TopCat.of (↥W × ↥(p ⁻¹' {d₀.1})))
      (TopCat.ofHom (fibTrivΦ p W d₀ hT))) k) := by
  have h1 : TopCat.Homotopy (TopCat.ofHom (fibTrivΦ p W d₀ hT)
      ≫ TopCat.ofHom (fibTrivΨ p W d₀ hT)) (𝟙 (TopCat.of ↥(p ⁻¹' W))) :=
    topCatHomotopyOf (X := TopCat.of ↥(p ⁻¹' W)) (Y := TopCat.of (↥W × ↥(p ⁻¹' {d₀.1})))
      (f := TopCat.ofHom (fibTrivΦ p W d₀ hT)) (g := TopCat.ofHom (fibTrivΨ p W d₀ hT))
      (fibTrivH p W d₀ hT)
      (fun x => fibTrivH_zero p W d₀ hT x)
      (fun x => fibTrivH_one p W d₀ hT x)
  have h2 : TopCat.Homotopy (TopCat.ofHom (fibTrivΨ p W d₀ hT)
      ≫ TopCat.ofHom (fibTrivΦ p W d₀ hT)) (𝟙 (TopCat.of (↥W × ↥(p ⁻¹' {d₀.1})))) :=
    topCatHomotopyOf (X := TopCat.of (↥W × ↥(p ⁻¹' {d₀.1}))) (Y := TopCat.of ↥(p ⁻¹' W))
      (f := TopCat.ofHom (fibTrivΨ p W d₀ hT)) (g := TopCat.ofHom (fibTrivΦ p W d₀ hT))
      (fibTrivK p W d₀ hT)
      (fun y => fibTrivK_zero p W d₀ hT y)
      (fun y => fibTrivK_one p W d₀ hT y)
  exact Work.Cohomology.homologyEquiv R _ _ _ _ h1 h2 k

end

end Work.StemsB
