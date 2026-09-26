import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.BoxShrink.PinchOff.exists_outerDiscRegion
import Submission.Work.PinchLemma3.ClosedDiscA.wall_core
import Submission.Work.InnermostDisk.not_isEssential_iff_homotopic_const
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq

/-!
# Infrastructure for `Work.Drive.EpsForm.regionEquivalent_of_discAttach`

The target `Work.Drive.EpsForm.regionEquivalent_of_discAttach` says: if `B ⊆ D.carrier` is open
in the carrier `F = P.carrier` of a parametrised torus, every point of the frontier of `B` lies
in `A`, and any two frontier points are joined inside `A ∩ D.carrier`, then every closed curve of
`F` inside `A ∪ B` is matched, at the level of winding vectors, by a closed curve inside `A`.

The proof (see `NOTES_discAttach.md` §1 for the intended one, and §2 the repair of its gap at
accumulation points of the excursion set) replaces the excursions of a loop `γ` into `B` by paths
in `A ∩ D.carrier`.  The mathematical content of each replacement is that *both* the excursion
(because `B ⊆ D.carrier`) and the replacement path (because `hconn` supplies it in `A ∩
D.carrier`) are paths in the disc `D.carrier`, where any two paths with the same endpoints are
homotopic rel endpoints; hence the winding vector is unchanged.

This file collects the elementary facts the construction needs, all of them unconditionally
provable:

* `closure_subset_surface`: `closure B ⊆ P.carrier` when `B ⊆ D.carrier`;
* `frontier_subset_A`: the frontier of `B` lies in `A`;
* `exists_thickening`: an embedded disc `D₂` with `D.carrier ⊆ D₂.interior` (so that the
  accumulation points of the excursion set have a *contractible* neighbourhood, which is what
  makes the "cluster" replacement legitimate at accumulation points);
* `homotopic_const_of_subset_discRegion`: every closed curve of `F` inside `D.carrier` is
  null-homotopic;
* `off_B_subset_A`: the points of a curve in `A ∪ B` which are not in `B` lie in `A`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.EpsForm

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The closure of `B` lies in the surface**, when `B ⊆ D.carrier`: the carrier of an embedded
disc is closed in `ℝ³` (`Work.PinchLemma3.ClosedDiscA.isClosed_carrier_of_discRegion`), so the
closure of `B` is contained in `D.carrier ⊆ P.carrier`. -/
theorem closure_subset_surface (D : Work.SurgeryInvariance.DiscRegion P) {B : Set R3}
    (hB : B ⊆ D.carrier) : closure B ⊆ P.carrier :=
  (closure_minimal hB (Work.PinchLemma3.ClosedDiscA.isClosed_carrier_of_discRegion D)).trans
    D.carrier_subset_surface

/-- **Every frontier point of `B` lies in `A`.**  This is `hcl`, with the hypothesis `x ∈
P.carrier` discharged by `closure_subset_surface`. -/
theorem frontier_subset_A {A B : Set R3} (D : Work.SurgeryInvariance.DiscRegion P)
    (hB : B ⊆ D.carrier)
    (hcl : ∀ x : R3, x ∈ P.carrier → x ∈ closure B → x ∉ B → x ∈ A) :
    ∀ x : R3, x ∈ closure B → x ∉ B → x ∈ A :=
  fun x hx1 hx2 => hcl x (closure_subset_surface D hB hx1) hx1 hx2

/-- **Every frontier point of `B` lies in `A ∩ D.carrier`**: the frontier of `B` is contained in
`closure B ⊆ D.carrier`, and in `A` by `hcl`. -/
theorem frontier_subset_A_inter {A B : Set R3} (D : Work.SurgeryInvariance.DiscRegion P)
    (hB : B ⊆ D.carrier)
    (hcl : ∀ x : R3, x ∈ P.carrier → x ∈ closure B → x ∉ B → x ∈ A) :
    ∀ x : R3, x ∈ closure B → x ∉ B → x ∈ A ∩ D.carrier := fun x hx1 hx2 =>
  ⟨frontier_subset_A D hB hcl x hx1 hx2,
    closure_minimal hB (Work.PinchLemma3.ClosedDiscA.isClosed_carrier_of_discRegion D) hx1⟩

/-- **A thickening of an embedded disc**: there is an embedded disc `D₂` of the surface whose
*interior* contains the closed disc `D.carrier`.  In particular a point of `D.carrier` has a
neighbourhood lying in `D₂.interior`, which is a disc, hence simply connected: this is the fact
that makes the replacement of an accumulating family of excursions by a single path legitimate.

The proof is `Work.BoxShrink.PinchOff.exists_outerDiscRegion` applied to the whole carrier. -/
theorem exists_thickening (D : Work.SurgeryInvariance.DiscRegion P) :
    ∃ D₂ : Work.SurgeryInvariance.DiscRegion P, D.carrier ⊆ D₂.interior := by
  obtain ⟨D₂, h1, -⟩ := Work.BoxShrink.PinchOff.exists_outerDiscRegion D
    (Work.SurgeryInvariance.isOpenInCarrier_univ P) (fun _ _ => trivial)
  exact ⟨D₂, h1⟩

/-- **A closed curve of the surface lying in an embedded disc is null-homotopic.**  It is
inessential (`Work.SurgeryInvariance.DiscRegion.not_isEssential`, the disc being contractible),
and for closed curves of the torus inessentiality is equivalent to being homotopic to a constant
(`Work.InnermostDisk.not_isEssential_iff_homotopic_const`). -/
theorem homotopic_const_of_subset_discRegion (D : Work.SurgeryInvariance.DiscRegion P)
    {γ : Work.CoreTopology.ClosedCurve P} (hγ : ∀ t : ℝ, γ t ∈ D.carrier) :
    ∃ x : R3, ∃ hx : x ∈ P.carrier,
      Work.CoreTopology.Homotopic P γ (Work.InnermostDisk.constCurve P x hx) :=
  (Work.InnermostDisk.not_isEssential_iff_homotopic_const P γ).mp
    (Work.SurgeryInvariance.DiscRegion.not_isEssential D γ hγ)


/-- **An ambient open set for a compact piece of `γ` inside a carrier-open set.**  If `K ⊆ ℝ` is
compact and `γ` maps `K` into a set `V` which is open in the carrier, then there is an open subset
`W ⊆ ℝ³` containing `γ '' K` whose trace on the surface is contained in `V`.  This is what lets
`Work.Drive.EpsForm.cluster_cover` (which is stated with an open subset of `ℝ³`) be applied with
`V = D₂.interior`, the output clusters then having `γ`-image inside `D₂.interior`. -/
theorem exists_open_ambient {V : Set R3} (hV : Work.SurgeryInvariance.IsOpenInCarrier P V) :
    ∃ W : Set R3, IsOpen W ∧ W ∩ P.carrier = V ∩ P.carrier := by
  classical
  rw [Work.SurgeryInvariance.IsOpenInCarrier] at hV
  obtain ⟨W, hWopen, hW⟩ := hV
  refine ⟨W, hWopen, ?_⟩
  ext y
  constructor
  · rintro ⟨hyW, hyC⟩
    have : (⟨y, hyC⟩ : P.carrier) ∈ Subtype.val ⁻¹' W := hyW
    rw [hW] at this
    exact ⟨this, hyC⟩
  · rintro ⟨hyV, hyC⟩
    have : (⟨y, hyC⟩ : P.carrier) ∈ Subtype.val ⁻¹' V := hyV
    rw [← hW] at this
    exact ⟨this, hyC⟩

/-- A point of a curve with values in `A ∪ B` which does not lie in `B` lies in `A`. -/
theorem off_B_subset_A {A B : Set R3} (γ : Work.CoreTopology.ClosedCurve P)
    (hγ : ∀ t : ℝ, γ t ∈ A ∪ B) :
    ∀ t : ℝ, γ t ∉ B → γ t ∈ A := by
  intro t ht
  rcases hγ t with h | h
  · exact h
  · exact absurd h ht

/-- A closed curve with values in `A` is *a fortiori* a curve with values in `A ∪ B`. -/
theorem subset_union_right_curve {A B : Set R3} (γ : Work.CoreTopology.ClosedCurve P)
    (hγ : ∀ t : ℝ, γ t ∈ A) : ∀ t : ℝ, γ t ∈ A ∪ B := fun t => Or.inl (hγ t)

end

end Work.Drive.EpsForm
