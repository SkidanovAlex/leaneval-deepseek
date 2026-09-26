import Submission.Work.InnermostDisk.Clean

/-!
# The classical input of Pardon's Lemma as a single predicate

Pardon's Lemma 4.2 is proved from two geometric steps (`Work.InnermostDisk.Reduction`):

* `InnermostDiscInput P S` — among the essential curves of `S ∩ F` there is one innermost in `S`
  (the disc it bounds inside `S` contains only inessential curves of `F`);
* `CleansDiscs P` — an innermost disc can be cleaned up so that its interior misses `F`.

Both are classical topological facts about a PL embedded sphere in `ℝ³`.  This file packages
them, once as the pair

* `PardonInnermostInput P := (∀ S, IsEmbeddedSphere S → InnermostDiscInput P S) ∧ CleansDiscs P`

and once in the *combined* form in which the lemma is most naturally quoted,

* `PardonSphereInput P := ∀ S, IsEmbeddedSphere S → CleansInSphere P S`,

i.e. "a sphere meeting `F` along an essential loop contains a *simple* essential loop bounding a
disc in the complement of `F`" — which is exactly what Pardon's innermost argument establishes:
if `S ∩ F` contains an essential curve, then there is a curve of `S ∩ F` bounding a PL embedded
disc whose interior is disjoint from `F`.  The main theorems of the chapter are then stated from
the single hypothesis `PardonSphereInput P` (plus the fact that the sphere at hand is an embedded
sphere, in the sense of `Work.InnermostDisk.IsEmbeddedSphere`).

A caller who does not want to prove `IsEmbeddedSphere S` can instead use the input
`InnermostDiscInput P S` directly for the sphere at hand
(`Work.InnermostDisk.Reduction.mustbeinessential_of_inputs`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section

/-- **The two innermost-disc inputs, globally.**  Every embedded sphere in `ℝ³` admits innermost
discs, and innermost discs can be cleaned. -/
def PardonInnermostInput (P : ParamTorus) : Prop :=
  (∀ S : Set R3, IsEmbeddedSphere S → InnermostDiscInput P S) ∧ CleansDiscs P

/-- **Pardon's innermost-disc argument as a single classical statement about embedded spheres.**
Every embedded sphere in `ℝ³` which meets `F` along an essential loop contains a *simple*
essential loop of `F` bounding an embedded disc whose interior is disjoint from `F` (Pardon's
set `U`). -/
def PardonSphereInput (P : ParamTorus) : Prop :=
  ∀ S : Set R3, IsEmbeddedSphere S → CleansInSphere P S

/-- The two separate inputs imply the combined sphere input. -/
theorem pardonSphereInput_of_inputs {P : ParamTorus} (h : PardonInnermostInput P) :
    PardonSphereInput P :=
  fun S hS => cleansInSphere_of_inputs (h.1 S hS) h.2

/-! ## Pardon's Lemma from the packaged inputs -/

/-- **Pardon's Lemma 4.2 from the single sphere-conditioned classical input.** -/
theorem mustbeinessential_of_pardonSphereInput (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hS : IsEmbeddedSphere S) (h : PardonSphereInput P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_of_cleansInSphere P β S (h S hS) hSβ

/-- The contrapositive (Pardon's Lemma in the form in which it is applied to a sphere family): an
essential loop inside an embedded sphere forces at least `I(F, β)` intersections with `β`. -/
theorem le_pardonsI_of_pardonSphereInput (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hS : IsEmbeddedSphere S) (h : PardonSphereInput P) (α : ClosedCurve P)
    (hαS : ∀ t : ℝ, α.γ t ∈ S) (hα : IsEssential P α) :
    pardonsI P β ≤ Set.encard (Set.range β.γ ∩ S) :=
  le_pardonsI_of_cleansInSphere P β S (h S hS) α hαS hα

/-- **Pardon's Lemma 4.2 from the two innermost-disc inputs, packaged.** -/
theorem mustbeinessential_of_pardonInnermostInput (P : ParamTorus) (β : ClosedCurve P)
    (S : Set R3) (hS : IsEmbeddedSphere S) (h : PardonInnermostInput P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_of_inputs P β S (h.1 S hS) h.2 hSβ

/-- **Pardon's Lemma 4.2 with abstract `I`, from the single sphere-conditioned classical
input.** -/
theorem mustbeinessential_core_of_pardonSphereInput (P : ParamTorus) (β : ClosedCurve P)
    (S : Set R3) (I : ℕ∞) (hS : IsEmbeddedSphere S) (h : PardonSphereInput P)
    (hI : ∀ α : ClosedCurve P, IsSimple P α → IsEssential P α → BoundsDiskInComplement P α →
      I ≤ Set.encard (Set.range α.γ ∩ Set.range β.γ))
    (hSβ : Set.encard (Set.range β.γ ∩ S) < I) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_core_of_cleansInSphere P β S I hI (h S hS) hSβ

end

end Work.InnermostDisk
