import Mathlib
import Submission.Work.Drive.Mono.Split
import Submission.Work.EpsW.localEuclidean_range_of_periodic_injOn
import Submission.Work.InnermostDisk.not_isEssential_of_range_subset_covered

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-! ## A finite disjoint union of closed locally Euclidean pieces

These are the two elementary topological lemmas which turn clause 1 of the trace data into the
local structure of the trace; they are stated for arbitrary subsets of `ℝ³` (no surface involved),
since that is all the argument uses. -/

/-- **Local Euclidean structure from an open cover by locally Euclidean pieces.**  If every point
of `Z` has a neighbourhood `U` *open in `ℝ³`* with `U ∩ Z` locally Euclidean of dimension one,
then so is `Z`.  This is `Work.Smooth.OneManifold.isLocallyEuclidean_of_forall_exists` with the
surface hypothesis dropped: an open set of `ℝ³` is a fortiori open in any subset. -/
theorem isLocallyEuclidean_of_forall_exists_isOpen {Z : Set R3}
    (H : ∀ x : Z, ∃ U : Set R3, IsOpen U ∧ (x : R3) ∈ U ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean (U ∩ Z)) :
    Work.Smooth.OneManifold.IsLocallyEuclidean Z := by
  classical
  choose U hUopen hxU hUloc using H
  refine Work.Smooth.OneManifold.isLocallyArc_of_isOpen_cover (ι := ↥Z) (X := ↥Z)
    (U := fun x => Subtype.val ⁻¹' (U x)) ?_ ?_ ?_
  · intro x
    exact (hUopen x).preimage continuous_subtype_val
  · intro x
    exact ⟨x, hxU x⟩
  · intro x
    have h1 : Work.Smooth.SphereJordan.IsLocallyArc
        ↥{y : ↥Z | (y : R3) ∈ U x ∩ Z} :=
      Work.Smooth.OneManifold.isLocallyArc_of_homeomorph
        (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph
          (show U x ∩ Z ⊆ Z from inter_subset_right)) (hUloc x)
    exact Work.Smooth.OneManifold.isLocallyArc_of_eq (by
      ext y
      exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩) h1

/-- **A finite family of pairwise disjoint closed locally Euclidean subsets of `ℝ³` has a locally
Euclidean union.**

At a point `x` of the piece `F i`, the union of the *other* pieces is closed and does not contain
`x`, so its complement `U` is an open neighbourhood of `x` with `U ∩ ⋃ j, F j = F i`; the local
structure of the union at `x` is thus that of `F i`. -/
theorem isLocallyEuclidean_iUnion_of_isClosed_pairwise_disjoint {ι : Type*} [Fintype ι]
    {F : ι → Set R3}
    (hclosed : ∀ i, IsClosed (F i))
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (F i) (F j))
    (hloc : ∀ i, Work.Smooth.OneManifold.IsLocallyEuclidean (F i)) :
    Work.Smooth.OneManifold.IsLocallyEuclidean (⋃ i, F i) := by
  classical
  refine isLocallyEuclidean_of_forall_exists_isOpen (Z := ⋃ i, F i) ?_
  rintro ⟨x, hx⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  refine ⟨(⋃ j : {j : ι // j ≠ i}, F j.1)ᶜ, ?_, ?_, ?_⟩
  · exact (isClosed_iUnion_of_finite (fun j : {j : ι // j ≠ i} => hclosed j.1)).isOpen_compl
  · intro hxU
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxU
    exact (Set.disjoint_left.mp (hdisj i j.1 (Ne.symm j.2)) hxi) hxj
  · have heq : F i = (⋃ j : {j : ι // j ≠ i}, F j.1)ᶜ ∩ (⋃ k, F k) := by
      ext y
      constructor
      · intro hyi
        refine ⟨?_, Set.mem_iUnion.mpr ⟨i, hyi⟩⟩
        intro hyU
        obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hyU
        exact (Set.disjoint_left.mp (hdisj i j.1 (Ne.symm j.2)) hyi) hyj
      · rintro ⟨hyU, hyZ⟩
        obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hyZ
        by_cases hji : j = i
        · rwa [hji] at hyj
        · exact absurd (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩) hyU
    exact Work.Smooth.OneManifold.isLocallyEuclidean_of_eq heq (hloc i)

/-- **Clause 1 of the trace data makes the trace a topological `1`-manifold.**  If the frontier of the
level's removed set meets the surface in a finite union of pairwise disjoint simple curves
(`Work.Drive.Mono.TraceCurvesAt`), then the trace `carrier ∩ frontier (tiltedLevelRemoved …)` is
locally Euclidean of dimension one.  Hence *any* point of the trace at which the trace is not locally
Euclidean — for instance the "T" of the junction analysis
(`Submission/Work/Drive/Mono/NOTES_H381_s8_graze.md` §2, `NOTES_H381_s11_forced_slab.md` §2) — is an
obstruction to clause 1, and this is the missing link between the local structure of the trace and
the failure of the trace data at a level. -/
theorem LocalEuclideanTrace_of_traceCurves {P : Work.CoreTopology.ParamTorus} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ}
    (htrace : Work.Drive.Mono.TraceCurvesAt P s c σ u v h ℓ lam) :
    Work.Smooth.OneManifold.IsLocallyEuclidean
      (P.carrier ∩ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
  obtain ⟨n, cs, hsimple, _hess, hdisj, hunion⟩ := htrace
  rw [← hunion]
  exact isLocallyEuclidean_iUnion_of_isClosed_pairwise_disjoint
    (F := fun i : Fin n => Set.range (cs i).γ)
    (fun i => Work.InnermostDisk.isClosed_range_closedCurve (cs i))
    (fun i j hij => hdisj i j hij)
    (fun i => Work.EpsW.localEuclidean_range_of_periodic_injOn
      (cs i).cont (cs i).periodic (hsimple i))

end

end Work.Drive.Mono
