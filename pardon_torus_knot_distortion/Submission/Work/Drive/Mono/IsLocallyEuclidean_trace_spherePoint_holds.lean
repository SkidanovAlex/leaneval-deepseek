import Mathlib
import Submission.Work.Drive.Mono.Residual
import Submission.Work.EpsW.arcsWallFamily_aux
import Submission.Work.EpsW.localEuclidean_range_of_periodic_injOn
import Submission.Work.Drive.Mono.SlicedSphere_covers
import Submission.Work.Topology.SphereSlicing.frontier_PBox

/-!
# Local Euclidean structure of the trace of a level of the tilted sweep at the box sphere

This module proves `Work.Drive.Mono.IsLocallyEuclidean_trace_spherePoint_holds`: at a point `z` of
the surface `P.carrier` which lies on the *box sphere* `sphereSet c σ s` (and hence on exactly one
face of the box, by the hypothesis `hface`), away from the level wall (`ℓ z ≠ lam`) and away from
the two faces of the tilted slab (`|⟪v,z⟫ - (⟪v,c⟫+u)| ≠ h`), the trace
`P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)` of the level is locally Euclidean of
dimension one.

The proof rests on three observations.

* **The removed set is locally the box or locally empty.**  The removed set is
  `f = PBox \ (S ∩ {ℓ < lam})` with `S` the closed tilted slab.  Since `z` is not on the boundary
  `|⟪v,·⟫ - (⟪v,c⟫+u)| = h` of the slab and not on the wall `ℓ = lam`, one of the following two
  open sets is a neighbourhood of `z` on which the removed set is the box, resp. empty:

  - `|⟪v,z⟫ - (⟪v,c⟫+u)| > h` (outside the closed slab): `f = PBox` near `z`;
  - `|⟪v,z⟫ - (⟪v,c⟫+u)| < h` and `ℓ z > lam` (inside the slab, above the wall): `f = PBox` near
    `z` (the box is entirely removed, the slab condition being irrelevant);
  - `|⟪v,z⟫ - (⟪v,c⟫+u)| < h` and `ℓ z < lam` (inside the slab, below the wall): `f = ∅` near `z`.

  Hence on a neighbourhood of `z` the frontier of `f` is either the box sphere (the frontier of the
  box, `Work.Topology.SphereSlicing.frontier_PBox`) or empty.

* **The surface's part of the box sphere is a single slicing curve near a point.**  A
  `SphereSlicing` of the box sphere has pairwise disjoint simple curves whose ranges cover
  `P.carrier ∩ sphereSet` (`Work.InnermostDisk.carrier_inter_subset_iUnion_range_of_sphereSlicing`);
  the curve through `z` is compact, the other curves are compact and disjoint from it, so a small
  ball around `z` meets only that one curve
  (`exists_ball_inter_eq_range_of_sphereSlicing`).

* **The range of a simple closed curve is a one-manifold**
  (`Work.EpsW.localEuclidean_range_of_periodic_injOn`).

The hypothesis `hface` (and `hs`) enter only through `frontier_PBox`; the counting or transversality
input is entirely contained in the existence of the slicing `hslice`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.Mono

noncomputable section

/-- The range of a closed curve is the image of the fundamental interval `[0, 2π]` (in particular it
is compact). -/
theorem closedCurve_range_eq_image_Icc {P : Work.CoreTopology.ParamTorus}
    (γ : Work.CoreTopology.ClosedCurve P) :
    Set.range γ.γ = γ.γ '' Set.Icc 0 (2 * Real.pi) := by
  rw [Work.CoreTopology.ClosedCurve.range_eq_image]
  refine Set.Subset.antisymm (Set.image_mono Set.Ico_subset_Icc_self) ?_
  rintro _ ⟨t, ht, rfl⟩
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact ⟨t, ⟨ht.1, hlt⟩, rfl⟩
  · refine ⟨0, ⟨le_refl 0, by positivity⟩, ?_⟩
    rw [heq]
    simpa using (γ.periodic 0).symm

/-- **A slicing of a sphere, near a point of the surface on the sphere, is a single one of its
curves.**  If `z` lies on the surface and on the sphere sliced, then some curve `h.c i` of the
slicing passes through `z` and, on a small ball around `z`, the surface's part of the sphere is
exactly that curve: the ranges of the other curves are compact and disjoint from `z`, hence at
positive distance from it. -/
theorem exists_ball_inter_eq_range_of_sphereSlicing {P : Work.CoreTopology.ParamTorus}
    {S : Set R3} (h : Work.InnermostDisk.SphereSlicing P S) {z : R3}
    (hz : z ∈ P.carrier ∩ S) :
    ∃ (i : h.ι) (ρ : ℝ), 0 < ρ ∧
      Metric.ball z ρ ∩ (P.carrier ∩ S) = Metric.ball z ρ ∩ Set.range (h.c i).γ := by
  classical
  have hcover : P.carrier ∩ S ⊆ ⋃ i, Set.range (h.c i).γ :=
    Work.InnermostDisk.carrier_inter_subset_iUnion_range_of_sphereSlicing h
  have hrange_sub : ∀ i : h.ι, Set.range (h.c i).γ ⊆ P.carrier ∩ S := by
    intro i y hy
    exact ⟨(h.c i).range_subset_carrier hy,
      by obtain ⟨t, rfl⟩ := hy; exact h.mem i t⟩
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp (hcover hz)
  set K : Set R3 := ⋃ i ∈ ({i₀}ᶜ : Set h.ι), Set.range (h.c i).γ with hKdef
  have hKclosed : IsClosed K := by
    rw [hKdef]
    exact (Set.Finite.isCompact_biUnion (Set.toFinite _) (fun i _ => by
      rw [closedCurve_range_eq_image_Icc]
      exact isCompact_Icc.image (h.c i).cont)).isClosed
  have hzK : z ∉ K := by
    rw [hKdef]
    rintro hzK'
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hzK'
    have hne : i ≠ i₀ := by simpa using hi
    exact Set.disjoint_left.mp (h.disjoint hne) hzi hi₀
  have hρ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : R3, y ∈ Metric.ball z ρ →
      y ∈ P.carrier ∩ S → y ∈ Set.range (h.c i₀).γ := by
    by_cases hne : K.Nonempty
    · refine ⟨Metric.infDist z K, (hKclosed.notMem_iff_infDist_pos hne).mp hzK, ?_⟩
      intro y hy hyS
      by_contra hyR
      have hyK : y ∈ K := by
        rw [hKdef]
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hyS)
        refine Set.mem_iUnion₂.mpr ⟨i, ?_, hi⟩
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hii
        exact hyR (hii ▸ hi)
      rw [Metric.mem_ball] at hy
      have h1 : Metric.infDist z K ≤ dist z y := Metric.infDist_le_dist_of_mem hyK
      linarith [h1, dist_comm y z]
    · refine ⟨1, one_pos, ?_⟩
      intro y _ hyS
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hyS)
      have hii : i = i₀ := by
        by_contra hne'
        refine hne ⟨y, ?_⟩
        rw [hKdef]
        exact Set.mem_iUnion₂.mpr ⟨i, by simpa using hne', hi⟩
      simpa [hii] using hi
  obtain ⟨ρ, hρpos, hρ'⟩ := hρ
  exact ⟨i₀, ρ, hρpos, by
    ext y
    exact ⟨fun hy => ⟨hy.1, hρ' y hy.1 hy.2⟩, fun hy => ⟨hy.1, hrange_sub i₀ hy.2⟩⟩⟩

/-- If the removed set of a level coincides with the box on an open set, then on that set the
frontier of the removed set is the box sphere. -/
theorem frontier_tiltedLevelRemoved_inter_of_eq_PBox {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {O : Set R3}
    (hs : 0 < s) (hO : IsOpen O)
    (heq : tiltedLevelRemoved s c σ u v h ℓ lam ∩ O = Submission.PBox s c σ ∩ O) :
    frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ∩ O =
      Work.BoxShrink.Core.sphereSet c σ s ∩ O := by
  have h1 := frontier_inter_open_inter (s := tiltedLevelRemoved s c σ u v h ℓ lam) (t := O) hO
  have h2 := frontier_inter_open_inter (s := Submission.PBox s c σ) (t := O) hO
  rw [heq] at h1
  rw [← h1, h2, Work.Topology.SphereSlicing.frontier_PBox hs c σ,
    ← Work.BoxShrink.Core.sphereSet_eq_BoxSphere]

/-- If the removed set of a level is empty on an open set, then the frontier of the removed set is
empty there. -/
theorem frontier_tiltedLevelRemoved_inter_of_eq_empty {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {O : Set R3}
    (hO : IsOpen O) (heq : tiltedLevelRemoved s c σ u v h ℓ lam ∩ O = ∅) :
    frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ∩ O = ∅ := by
  have h1 := frontier_inter_open_inter (s := tiltedLevelRemoved s c σ u v h ℓ lam) (t := O) hO
  rw [heq, frontier_empty, Set.empty_inter] at h1
  exact h1.symm

/-- **The trace of a level of the tilted sweep is locally Euclidean at a point of the box sphere.**
At a point `z` of the surface on the box sphere `sphereSet c σ s`, away from the wall (`ℓ z ≠ lam`)
and from the two slab faces (`|⟪v,z⟫ - (⟪v,c⟫+u)| ≠ h`), the trace
`P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)` is locally Euclidean of dimension one:
near `z` the frontier of the removed set is either the box sphere — whose intersection with the
surface is one of the simple curves of the slicing `hslice` near `z`, hence a one-manifold — or
empty. -/
theorem IsLocallyEuclidean_trace_spherePoint_holds
    {P : Work.CoreTopology.ParamTorus} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ}
    {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s)))
    (hz : z ∈ P.carrier) (hzS : z ∈ Work.BoxShrink.Core.sphereSet c σ s)
    (hface : ∃ i : Fin 3, |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
      ∀ j : Fin 3, j ≠ i → |z (σ j) - c (σ j)| < Submission.boxSide j * s)
    (hznotwall : ℓ z ≠ lam)
    (hznotface : |inner ℝ v z - (inner ℝ v c + u)| ≠ h) :
    ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ (P.carrier ∩ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  classical
  set f : Set R3 := Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam with hfdef
  have hfmem : ∀ y : R3, y ∈ f ↔ y ∈ Submission.PBox s c σ ∧
      ¬ (|inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y < lam) := by
    intro y
    rw [hfdef]
    simp only [Work.Drive.Mono.tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Work.Drive.EpsForm.tiltedSlabClosed]
  -- **Step 1**: a neighbourhood of `z` on which `f` is the box or is empty
  have key : ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧ (f ∩ O = Submission.PBox s c σ ∩ O ∨ f ∩ O = ∅) := by
    rcases lt_or_gt_of_ne hznotface with hlt | hgt
    · rcases lt_or_gt_of_ne hznotwall with hlt2 | hgt2
      · -- inside the slab, below the wall: `f` is empty near `z`
        refine ⟨{y : R3 | |inner ℝ v y - (inner ℝ v c + u)| < h} ∩ {y : R3 | ℓ y < lam},
          ?_, ⟨hlt, hlt2⟩, Or.inr ?_⟩
        · exact (isOpen_lt (continuous_abs.comp
            ((continuous_const.inner continuous_id).sub continuous_const)) continuous_const).inter
            (isOpen_lt ℓ.continuous continuous_const)
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro y ⟨hyf, hyO⟩
          rw [hfmem y] at hyf
          exact hyf.2 ⟨le_of_lt hyO.1, hyO.2⟩
      · -- inside the slab, above the wall: the slab is irrelevant, `f` is the box near `z`
        refine ⟨{y : R3 | |inner ℝ v y - (inner ℝ v c + u)| < h} ∩ {y : R3 | lam < ℓ y},
          ?_, ⟨hlt, hgt2⟩, Or.inl ?_⟩
        · exact (isOpen_lt (continuous_abs.comp
            ((continuous_const.inner continuous_id).sub continuous_const)) continuous_const).inter
            (isOpen_lt continuous_const ℓ.continuous)
        · ext y
          constructor
          · rintro ⟨hyf, hyO⟩
            rw [hfmem y] at hyf
            exact ⟨hyf.1, hyO⟩
          · rintro ⟨hyP, hyO⟩
            refine ⟨?_, hyO⟩
            rw [hfmem y]
            exact ⟨hyP, fun hcon => absurd hcon.2 (not_lt.mpr (le_of_lt hyO.2))⟩
    · -- outside the closed slab: `f` is the box near `z`
      refine ⟨{y : R3 | h < |inner ℝ v y - (inner ℝ v c + u)|}, ?_, hgt, Or.inl ?_⟩
      · exact isOpen_lt continuous_const (continuous_abs.comp
          ((continuous_const.inner continuous_id).sub continuous_const))
      · ext y
        constructor
        · rintro ⟨hyf, hyO⟩
          rw [hfmem y] at hyf
          exact ⟨hyf.1, hyO⟩
        · rintro ⟨hyP, hyO⟩
          refine ⟨?_, hyO⟩
          rw [hfmem y]
          exact ⟨hyP, fun hcon => absurd hcon.1 (not_le.mpr hyO)⟩
  obtain ⟨O, hOopen, hzO, hcase⟩ := key
  rcases hcase with hbox | hemp
  · -- the frontier of `f` is the box sphere near `z`
    obtain ⟨Sl⟩ := hslice
    obtain ⟨i₀, ρ, hρpos, hball⟩ :=
      exists_ball_inter_eq_range_of_sphereSlicing Sl ⟨hz, hzS⟩
    have hfr : frontier f ∩ (O ∩ Metric.ball z ρ) =
        Work.BoxShrink.Core.sphereSet c σ s ∩ (O ∩ Metric.ball z ρ) := by
      have hmain := frontier_tiltedLevelRemoved_inter_of_eq_PBox (s := s) (u := u) (c := c)
        (σ := σ) (v := v) (h := h) (ℓ := ℓ) (lam := lam) hs hOopen (by rw [← hfdef]; exact hbox)
      calc frontier f ∩ (O ∩ Metric.ball z ρ)
          = (frontier f ∩ O) ∩ Metric.ball z ρ := by rw [Set.inter_assoc]
        _ = (Work.BoxShrink.Core.sphereSet c σ s ∩ O) ∩ Metric.ball z ρ := by rw [hmain]
        _ = Work.BoxShrink.Core.sphereSet c σ s ∩ (O ∩ Metric.ball z ρ) := by rw [Set.inter_assoc]
    have hSeq : P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s =
        ⋃ i, Set.range (Sl.c i).γ := by
      apply Set.Subset.antisymm
      · intro y hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
          (Work.InnermostDisk.carrier_inter_subset_iUnion_range_of_sphereSlicing Sl hy)
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      · intro y hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
        exact ⟨(Sl.c i).range_subset_carrier hi,
          by obtain ⟨t, rfl⟩ := hi; exact Sl.mem i t⟩
    have hdisj_ball : ∀ i : Sl.ι, i ≠ i₀ →
        Metric.ball z ρ ∩ Set.range (Sl.c i).γ = ∅ := by
      intro i hi
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hyb, hyi⟩
      have hy2 : y ∈ Metric.ball z ρ ∩ (P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s) :=
        ⟨hyb, (Sl.c i).range_subset_carrier hyi,
          by obtain ⟨t, rfl⟩ := hyi; exact Sl.mem i t⟩
      rw [hball] at hy2
      exact Set.disjoint_left.mp (Sl.disjoint hi) hyi hy2.2
    have hEqS : (O ∩ Metric.ball z ρ) ∩ (P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s) =
        (O ∩ Metric.ball z ρ) ∩ (P.carrier ∩ Set.range (Sl.c i₀).γ) := by
      rw [show (O ∩ Metric.ball z ρ) ∩ (P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s)
            = O ∩ (Metric.ball z ρ ∩ (P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s)) from by
              ext x; simp only [Set.mem_inter_iff]; tauto,
        hball,
        show O ∩ (Metric.ball z ρ ∩ Set.range (Sl.c i₀).γ)
            = (O ∩ Metric.ball z ρ) ∩ (P.carrier ∩ Set.range (Sl.c i₀).γ) from by
              ext x
              simp only [Set.mem_inter_iff]
              constructor
              · rintro ⟨hxO, hxb, hxr⟩
                exact ⟨⟨hxO, hxb⟩, (Sl.c i₀).range_subset_carrier hxr, hxr⟩
              · rintro ⟨⟨hxO, hxb⟩, -, hxr⟩
                exact ⟨hxO, hxb, hxr⟩]
    have htrace : (O ∩ Metric.ball z ρ) ∩ (P.carrier ∩ frontier f) =
        (O ∩ Metric.ball z ρ) ∩ (P.carrier ∩ Set.range (Sl.c i₀).γ) := by
      calc (O ∩ Metric.ball z ρ) ∩ (P.carrier ∩ frontier f)
          = P.carrier ∩ (frontier f ∩ (O ∩ Metric.ball z ρ)) := by
            ext x; simp only [Set.mem_inter_iff]; tauto
        _ = P.carrier ∩ (Work.BoxShrink.Core.sphereSet c σ s ∩ (O ∩ Metric.ball z ρ)) := by
            rw [hfr]
        _ = (O ∩ Metric.ball z ρ) ∩ (P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s) := by
            ext x; simp only [Set.mem_inter_iff]; tauto
        _ = (O ∩ Metric.ball z ρ) ∩ (P.carrier ∩ Set.range (Sl.c i₀).γ) := hEqS
    refine ⟨O ∩ Metric.ball z ρ, hOopen.inter Metric.isOpen_ball,
      ⟨hzO, Metric.mem_ball_self hρpos⟩, ?_⟩
    rw [htrace]
    have hloc : Work.Smooth.OneManifold.IsLocallyEuclidean (Set.range (Sl.c i₀).γ) :=
      Work.EpsW.localEuclidean_range_of_periodic_injOn (Sl.c i₀).cont (Sl.c i₀).periodic
        (Sl.simple i₀)
    refine Work.Smooth.OneManifold.IsLocallyEuclidean.of_isOpenIn ?_ ?_ hloc
    · intro x hx
      exact hx.2.2
    · show IsOpen ((Subtype.val ⁻¹' ((O ∩ Metric.ball z ρ) ∩
          (P.carrier ∩ Set.range (Sl.c i₀).γ))) : Set ↥(Set.range (Sl.c i₀).γ))
      have hVe : ((Subtype.val ⁻¹' ((O ∩ Metric.ball z ρ) ∩
            (P.carrier ∩ Set.range (Sl.c i₀).γ))) : Set ↥(Set.range (Sl.c i₀).γ)) =
          (Subtype.val ⁻¹' (O ∩ Metric.ball z ρ) : Set ↥(Set.range (Sl.c i₀).γ)) := by
        ext x
        constructor
        · intro hx
          exact hx.1
        · intro hx
          exact ⟨hx, (Sl.c i₀).range_subset_carrier x.2, x.2⟩
      rw [hVe]
      exact (hOopen.inter Metric.isOpen_ball).preimage continuous_subtype_val
  · -- the frontier of `f` is empty near `z`
    refine ⟨O, hOopen, hzO, ?_⟩
    have hfr : frontier f ∩ O = ∅ :=
      frontier_tiltedLevelRemoved_inter_of_eq_empty (s := s) (u := u) (c := c) (σ := σ) (v := v)
        (h := h) (ℓ := ℓ) (lam := lam) hOopen (by rw [← hfdef]; exact hemp)
    have hzeq : O ∩ (P.carrier ∩ frontier f) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hyO, -, hyfr⟩
      exact (show y ∉ frontier f ∩ O from by rw [hfr]; exact Set.notMem_empty y) ⟨hyfr, hyO⟩
    rw [hzeq]
    exact fun x => x.2.elim

end

end Work.Drive.Mono
