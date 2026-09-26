import Mathlib
import Submission.Work.EpsW.arcsWallFamily
import Submission.Work.EpsW.arcsWallFamily_aux
import Submission.Work.EpsW.localModel_endpoint

/-!
# `ArcsWallFamily`: the arcs case of the wall, via the classification of compact `1`-manifolds

The trace `W = F ∩ halfBoxWall s c σ u` of the upper half-box wall on the surface `F = P.carrier`
is, at an arcs configuration, a compact subset of `F` which is locally Euclidean of dimension one:
the local models are checked at the three kinds of points of `W` in
`Submission/Work/EpsW/arcsWallFamily_aux.lean` (a point of the slice, a point of the sphere trace
above the level `u`, and an equator point, `Work.EpsW.localModel_endpoint`).  The classification of
compact `1`-manifolds (`Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean`) then produces
the required family of pairwise disjoint simple closed curves.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.Smooth.OneManifold

namespace Work.EpsW

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- Local Euclidean structure from pointwise local models. -/
theorem isLocallyEuclidean_of_forall_local {Z : Set R3}
    (H : ∀ x : ↥Z, ∃ O : Set R3, IsOpen O ∧ (x : R3) ∈ O ∧ IsLocallyEuclidean (O ∩ Z)) :
    IsLocallyEuclidean Z := by
  classical
  choose O hOopen hxO hOloc using H
  refine isLocallyArc_of_isOpen_cover (ι := ↥Z) (X := ↥Z)
    (U := fun x => Subtype.val ⁻¹' O x) ?_ ?_ ?_
  · intro x
    exact (hOopen x).preimage continuous_subtype_val
  · intro x
    exact ⟨x, hxO x⟩
  · intro x
    have h1 : Work.Smooth.SphereJordan.IsLocallyArc ↥{y : ↥Z | (y : R3) ∈ O x ∩ Z} :=
      isLocallyArc_of_homeomorph (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph
        (show O x ∩ Z ⊆ Z from inter_subset_right)) (hOloc x)
    exact isLocallyArc_of_eq (by
      ext y
      exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩) h1

/-- **The wall trace is locally Euclidean of dimension one.**  The three local models are supplied
by `Work.EpsW.localModel_slice`, `Work.EpsW.localModel_trace` and `Work.EpsW.localModel_endpoint`;
the wall trace is the union of the slice (below the box sphere), of the part of the sphere trace
above the level, and of the equator points. -/
theorem isLocallyEuclidean_Wset
    (Sl : Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s))
    (hcross : ∀ (i : Sl.ι) (t : ℝ), (Sl.c i).γ t (σ 2) = c (σ 2) + u →
      (∀ ε : ℝ, 0 < ε → ∃ t' : ℝ, |t' - t| < ε ∧ c (σ 2) + u < (Sl.c i).γ t' (σ 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ t' : ℝ, |t' - t| < ε ∧ (Sl.c i).γ t' (σ 2) < c (σ 2) + u))
    {n : ℕ} (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3))
    (hinj : ∀ j : Fin n, Function.Injective (a j))
    (ha : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ closure (Sigset P s c σ u))
    (hdisj : Pairwise fun j j' : Fin n => Disjoint (Set.range (a j)) (Set.range (a j')))
    (hcover : closure (Sigset P s c σ u) ⊆ ⋃ j, Set.range (a j))
    (hint : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ Work.BoxShrink.Core.sphereSet c σ s → ((x : ℝ) = 0 ∨ (x : ℝ) = 1))
    (hhend : ∀ j : Fin n, arcEnd0 a j ∈ Work.BoxShrink.Core.sphereSet c σ s ∧
      arcEnd1 a j ∈ Work.BoxShrink.Core.sphereSet c σ s)
    (heq : ∀ q ∈ P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s ∩
        Work.BoxShrink.Core.cutPlane c σ u,
      ∃ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
        ((x : ℝ) = 0 ∨ (x : ℝ) = 1) ∧ a j x = q) :
    IsLocallyEuclidean (Wset P s c σ u) := by
  classical
  have hboxopen : IsOpen {z : R3 | Submission.boxNorm c σ z < s} :=
    isOpen_lt (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const
  have hupperopen : IsOpen {z : R3 | c (σ 2) + u < lvl σ z} :=
    isOpen_lt continuous_const (Work.Topology.SphereSlicing.continuous_coordR3 (σ 2))
  refine isLocallyEuclidean_of_forall_local fun y => ?_
  by_cases hyE : (y : R3) ∈ Set.range (endpt a)
  · obtain ⟨p, hp⟩ := hyE
    obtain ⟨O, hOopen, hmem, hOloc⟩ :=
      localModel_endpoint Sl hcross a hinj ha hdisj hcover hint hhend heq p
    exact ⟨O, hOopen, by rw [← hp]; exact hmem, hOloc⟩
  · by_cases hyS : (y : R3) ∈ Sigset P s c σ u
    · obtain ⟨O, hOopen, hmem, hOloc⟩ :=
        localModel_slice hinj ha hdisj hcover hint hhend hyS
      have hybox : (y : R3) ∈ {z : R3 | Submission.boxNorm c σ z < s} :=
        (Submission.mem_PBox_iff s c σ (y : R3)).mp (mem_Sigset.mp hyS).2.1
      refine ⟨O ∩ {z : R3 | Submission.boxNorm c σ z < s}, hOopen.inter hboxopen,
        ⟨hmem, hybox⟩, ?_⟩
      have hEq : (O ∩ {z : R3 | Submission.boxNorm c σ z < s}) ∩ Wset P s c σ u =
          {z : R3 | Submission.boxNorm c σ z < s} ∩ (O ∩ Sigset P s c σ u) := by
        apply Set.Subset.antisymm
        · rintro z ⟨⟨hzO, hzb⟩, hzW⟩
          have hzun : z ∈ (Gset P s c σ ∩ {z : R3 | c (σ 2) + u ≤ lvl σ z}) ∪
              Sigset P s c σ u := by
            rw [← Wset_eq]; exact hzW
          rcases hzun with hz | hz
          · exact absurd ((Work.BoxShrink.Core.mem_sphereSet).mp hz.1.2) (ne_of_lt hzb)
          · exact ⟨hzb, hzO, hz⟩
        · rintro z ⟨hzb, hzO, hzSig⟩
          refine ⟨⟨hzO, hzb⟩, ?_⟩
          rw [Wset_eq]
          exact Or.inr hzSig
      rw [hEq]
      exact IsLocallyEuclidean.inter_isOpen hOloc hboxopen
    · have hyW : (y : R3) ∈ Wset P s c σ u := y.2
      have hyG : (y : R3) ∈ Gset P s c σ ∩ {z : R3 | c (σ 2) + u ≤ lvl σ z} := by
        rcases (show (y : R3) ∈ (Gset P s c σ ∩ {z : R3 | c (σ 2) + u ≤ lvl σ z}) ∪
            Sigset P s c σ u from by rw [← Wset_eq]; exact hyW) with h | h
        · exact h
        · exact absurd h hyS
      have hyu : c (σ 2) + u < lvl σ (y : R3) := by
        refine lt_of_le_of_ne hyG.2 (Ne.symm ?_)
        intro hlu
        refine hyE ?_
        rw [range_endpt_eq_equator ha hhend heq]
        exact ⟨hyG.1, hlu⟩
      obtain ⟨O, hOopen, hmem, hOloc⟩ := localModel_trace Sl hyG.1 hyu
      refine ⟨O ∩ {z : R3 | c (σ 2) + u < lvl σ z}, hOopen.inter hupperopen,
        ⟨hmem, hyu⟩, ?_⟩
      have hEq : (O ∩ {z : R3 | c (σ 2) + u < lvl σ z}) ∩ Wset P s c σ u =
          {z : R3 | c (σ 2) + u < lvl σ z} ∩
            (O ∩ (Gset P s c σ ∩ {z : R3 | c (σ 2) + u < lvl σ z})) := by
        apply Set.Subset.antisymm
        · rintro z ⟨⟨hzO, hzu⟩, hzW⟩
          have hzun : z ∈ (Gset P s c σ ∩ {z : R3 | c (σ 2) + u ≤ lvl σ z}) ∪
              Sigset P s c σ u := by
            rw [← Wset_eq]; exact hzW
          rcases hzun with hz | hz
          · refine ⟨?_, ?_, ?_, ?_⟩
            · show c (σ 2) + u < lvl σ z
              exact hzu
            · exact hzO
            · exact hz.1
            · show c (σ 2) + u < lvl σ z
              exact hzu
          · exfalso
            have h1 : lvl σ z = c (σ 2) + u := (mem_Sigset.mp hz).2.2
            have h2 : c (σ 2) + u < lvl σ z := hzu
            linarith
        · rintro z ⟨hzu, hzO, hzG, hzu'⟩
          refine ⟨⟨hzO, hzu⟩, ?_⟩
          rw [Wset_eq]
          exact Or.inl ⟨hzG, by
            show c (σ 2) + u ≤ lvl σ z
            exact le_of_lt hzu'⟩
      rw [hEq]
      exact IsLocallyEuclidean.inter_isOpen hOloc hupperopen

theorem arcsWallFamily_holds : Work.EpsW.ArcsWallFamily := by
  intro P s c σ u Sl hcross n a hinj ha hdisj hcover hint hhend heq
  obtain ⟨m, γ, hsimple, hdisjγ, hcoverγ⟩ :=
    exists_family_of_isCompact_of_isLocallyEuclidean (P := P) (Z := Wset P s c σ u)
      (fun _ hy => hy.1) (isCompact_Wset (P := P) (s := s) (c := c) (σ := σ) (u := u))
      (isLocallyEuclidean_Wset Sl hcross a hinj ha hdisj hcover hint hhend heq)
  exact ⟨m, γ, hsimple, hdisjγ, hcoverγ.symm⟩

end

end Work.EpsW
