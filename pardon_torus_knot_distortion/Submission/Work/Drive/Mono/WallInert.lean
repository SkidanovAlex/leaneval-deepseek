import Mathlib
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.Topology.SphereSlicing.frontier_PBox
import Submission.Work.Drive.Mono.IsLocallyEuclidean_trace_spherePoint_holds

/-!
# The wall-inert cases of the trace of a level: the graze repair

The local models of the trace of the tilted sweep (`Work.Drive.Mono.trace_localModels_of_junctionGenC`
and the modules it rests on) all take as a *data* condition that the box sphere, the slab faces and
the level wall cut the surface *transversally*.  At a configuration where the surface is **tangent**
to the box sphere (a *graze*), the corresponding clause is unsatisfiable, and the local analysis of
the trace has to be redone: near a graze point the surface sits on *both* sides of its tangency curve
`C`, so the strict-inequality arguments that make the junctions at the box sphere "V"-shaped may fail.

This module isolates the two cases of a graze point at which the level **wall is inert** on the box,
i.e. the box near the point is entirely below (resp. above) the level.  In these cases the trace has
a completely elementary local structure, *independent of any transversality*:

* if the box near `z` is strictly **below** the level (`WallInertBelow`) and `z` lies strictly inside
  the closed slab, then `z` is **not** in the trace at all: the removed set near `z` is
  `PBox ∩ slabClosedᶜ`, and the frontier of that set is empty near `z` because a whole ball around
  `z` is contained in the slab (`frontier_sdiff_tiltedSlabClosed_inter_ball_eq_empty`).  This is the
  case of the concrete graze configuration: the wall is the tangency plane of the surface, the box
  lies below it, and the trace of that level misses the tangency curve;
* if the box near `z` is strictly **above** the level (`WallInertAbove`), then the removed set near
  `z` *is* the box, so the trace near `z` is the box-sphere trace, i.e. one of the curves of the
  slicing of the box sphere (`localModel_of_wallInertAbove`): locally Euclidean of dimension one, with
  no transversality hypothesis.

These two lemmas are what make the graze repairs of the junction bundles (`JunctionGenE`) usable at a
graze: they show that a graze point at which the wall is inert is harmless — either it is not a trace
point, or its trace is the box sphere's slicing curve.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Filter
open scoped Topology

namespace Work.Drive.Mono

noncomputable section

/-- **The wall is below the box near `z`**: on a neighbourhood of `z` inside the box, the sweep
height is strictly below the level.  At a graze point `z` of the box sphere at the level `lam`, this
says that `z` is a local maximum of `ℓ` on the box: the wall *hugs* the surface there and the removed
set near `z` is a box minus a slab. -/
def WallInertBelow (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ)
    (z : R3) : Prop :=
  ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧ ∀ y ∈ O ∩ Submission.PBox s c σ, ℓ y < lam

/-- **The wall is above the box near `z`**: on a neighbourhood of `z` inside the box, the sweep
height is strictly above the level.  At a graze point this is the mirror case: the removed set near
`z` is the box itself, so the trace is the box sphere. -/
def WallInertAbove (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ)
    (z : R3) : Prop :=
  ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧ ∀ y ∈ O ∩ Submission.PBox s c σ, lam < ℓ y

/-! ## The ball around a point strictly inside the closed slab -/

/-- **A point strictly inside the closed tilted slab has a ball around it contained in the slab.** -/
theorem exists_ball_subset_tiltedSlabClosed (a : ℝ) (v : R3) {h : ℝ} {z : R3}
    (hz : |inner ℝ v z - a| < h) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball z ε ⊆ Work.Drive.EpsForm.tiltedSlabClosed a v h := by
  set δ : ℝ := h - |inner ℝ v z - a| with hδdef
  have hδ : 0 < δ := sub_pos.mpr hz
  have hv : 0 ≤ ‖v‖ := norm_nonneg v
  refine ⟨δ / (2 * (‖v‖ + 1)), by positivity, ?_⟩
  intro y hy
  rw [Metric.mem_ball] at hy
  have h1 : |inner ℝ v y - a| ≤ |inner ℝ v z - a| + ‖v‖ * ‖y - z‖ := by
    have h2 : inner ℝ v y - a = (inner ℝ v z - a) + inner ℝ v (y - z) := by
      rw [inner_sub_right]; ring
    rw [h2]
    refine (abs_add_le _ _).trans ?_
    exact add_le_add le_rfl (abs_real_inner_le_norm _ _)
  have hε' : ‖y - z‖ < δ / (2 * (‖v‖ + 1)) := by
    rwa [dist_eq_norm] at hy
  have h3 : ‖v‖ * ‖y - z‖ ≤ δ / 2 := by
    calc ‖v‖ * ‖y - z‖ ≤ ‖v‖ * (δ / (2 * (‖v‖ + 1))) :=
          mul_le_mul_of_nonneg_left (le_of_lt hε') hv
      _ ≤ δ / 2 := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0:ℝ) < 2 * (‖v‖ + 1))]
          nlinarith [hδ.le, hv]
  rw [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq]
  linarith [h1, h3]

/-- **The frontier of `PBox \ slabClosed` is empty near a point strictly inside the slab**: a whole
ball around the point is contained in the slab, so the difference is empty there. -/
theorem frontier_sdiff_tiltedSlabClosed_inter_ball_eq_empty {A : Set R3} {a h : ℝ} {v z : R3}
    (hz : |inner ℝ v z - a| < h) :
    ∃ ε : ℝ, 0 < ε ∧
      frontier (A \ Work.Drive.EpsForm.tiltedSlabClosed a v h) ∩ Metric.ball z ε = ∅ := by
  obtain ⟨ε, hε, hsub⟩ := exists_ball_subset_tiltedSlabClosed a v hz
  refine ⟨ε, hε, ?_⟩
  set S : Set R3 := Work.Drive.EpsForm.tiltedSlabClosed a v h with hSdef
  have h2 : Metric.ball z ε ⊆ (A \ S)ᶜ := by
    intro w hw hcon
    exact hcon.2 (hsub hw)
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨hyfr, hyb⟩
  have hcl : y ∈ closure (A \ S) := hyfr.1
  have hnb : (A \ S)ᶜ ∈ 𝓝 y :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hyb) h2
  obtain ⟨y', hy'c, hy's⟩ := mem_closure_iff_nhds.mp hcl _ hnb
  exact hy'c hy's

/-! ## The set-theoretic form of the removed set when the wall is inert -/

/-- **A wall strictly below the box near `z`**: the removed set near `z` is the box minus the closed
slab (the wall condition is invisible there). -/
theorem eq_sdiff_of_wallInertBelow {s u h lam : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} {z : R3} (hW : WallInertBelow s c σ ℓ lam z) :
    ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      tiltedLevelRemoved s c σ u v h ℓ lam ∩ O =
        (Submission.PBox s c σ \
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ∩ O := by
  obtain ⟨O, hOopen, hzO, hOb⟩ := hW
  refine ⟨O, hOopen, hzO, ?_⟩
  ext y
  constructor
  · rintro ⟨hyf, hyO⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff] at hyf
    refine ⟨⟨hyf.1, ?_⟩, hyO⟩
    intro hle
    exact hyf.2 ⟨hle, hOb y ⟨hyO, hyf.1⟩⟩
  · rintro ⟨⟨hyP, hyS⟩, hyO⟩
    refine ⟨?_, hyO⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff]
    exact ⟨hyP, fun hc => hyS hc.1⟩

/-- **A wall strictly above the box near `z`**: the removed set near `z` is the box itself. -/
theorem eq_PBox_of_wallInertAbove {s u h lam : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} {z : R3} (hW : WallInertAbove s c σ ℓ lam z) :
    ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      tiltedLevelRemoved s c σ u v h ℓ lam ∩ O = Submission.PBox s c σ ∩ O := by
  obtain ⟨O, hOopen, hzO, hOb⟩ := hW
  refine ⟨O, hOopen, hzO, ?_⟩
  ext y
  constructor
  · rintro ⟨hyf, hyO⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff] at hyf
    exact ⟨hyf.1, hyO⟩
  · rintro ⟨hyP, hyO⟩
    refine ⟨?_, hyO⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff]
    refine ⟨hyP, fun hc => ?_⟩
    exact absurd (hOb y ⟨hyO, hyP⟩) (not_lt.mpr (le_of_lt hc.2))

/-! ## The graze lemmas -/

/-- **A wall-inert point strictly inside the slab is not a trace point at its own level.**  The
removed set near `z` is `PBox ∩ slabClosedᶜ` (`eq_sdiff_of_wallInertBelow`), and a whole ball around
`z` is contained in the slab, so the frontier of the removed set misses a neighbourhood of `z`.  This
is the mechanism by which the graze points of a configuration with an inert wall are harmless: they
are simply not in the trace. -/
theorem notMem_frontier_tiltedLevelRemoved_of_wallInertBelow {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {z : R3}
    (hslab : |inner ℝ v z - (inner ℝ v c + u)| < h)
    (hW : WallInertBelow s c σ ℓ lam z) :
    z ∉ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) := by
  obtain ⟨O, hOopen, hzO, heq⟩ :=
    eq_sdiff_of_wallInertBelow (u := u) (v := v) (h := h) (lam := lam) hW
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.isOpen_iff.mp hOopen z hzO
  obtain ⟨ε₂, hε₂pos, hε₂sub⟩ := exists_ball_subset_tiltedSlabClosed (inner ℝ v c + u) v hslab
  obtain ⟨ε₃, hε₃pos, hε₃emp⟩ :=
    frontier_sdiff_tiltedSlabClosed_inter_ball_eq_empty (A := Submission.PBox s c σ) hslab
  set ρ : ℝ := min ε₁ (min ε₂ ε₃) with hρdef
  have hρpos : 0 < ρ := lt_min hε₁pos (lt_min hε₂pos hε₃pos)
  have hρ₂ : ρ ≤ ε₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ₃ : ρ ≤ ε₃ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hb₁ : Metric.ball z ρ ⊆ O := (Metric.ball_subset_ball (min_le_left _ _)).trans hε₁
  have hb₂ : Metric.ball z ρ ⊆
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h :=
    (Metric.ball_subset_ball hρ₂).trans hε₂sub
  have hball : frontier (Submission.PBox s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ∩ Metric.ball z ρ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem] at hε₃emp ⊢
    rintro y ⟨hyfr, hyb⟩
    exact hε₃emp y ⟨hyfr, Metric.ball_subset_ball hρ₃ hyb⟩
  have hfr : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ∩ Metric.ball z ρ = ∅ := by
    have h1 := frontier_inter_open_inter (s := tiltedLevelRemoved s c σ u v h ℓ lam)
      (t := Metric.ball z ρ) Metric.isOpen_ball
    rw [← h1]
    have h2 : tiltedLevelRemoved s c σ u v h ℓ lam ∩ Metric.ball z ρ =
        (Submission.PBox s c σ \
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ∩ Metric.ball z ρ := by
      calc tiltedLevelRemoved s c σ u v h ℓ lam ∩ Metric.ball z ρ
          = (tiltedLevelRemoved s c σ u v h ℓ lam ∩ O) ∩ Metric.ball z ρ := by
            rw [Set.inter_assoc, Set.inter_eq_right.mpr hb₁]
        _ = ((Submission.PBox s c σ \
              Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ∩ O) ∩
              Metric.ball z ρ := by rw [heq]
        _ = (Submission.PBox s c σ \
              Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ∩ Metric.ball z ρ := by
            rw [Set.inter_assoc, Set.inter_eq_right.mpr hb₁]
    rw [h2, frontier_inter_open_inter (s := Submission.PBox s c σ \
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) (t := Metric.ball z ρ)
        Metric.isOpen_ball, hball]
  intro hcon
  have hzmem : z ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ∩ Metric.ball z ρ :=
    ⟨hcon, Metric.mem_ball_self hρpos⟩
  rw [hfr] at hzmem
  exact hzmem

/-- **The local model at a box-sphere point at which the removed set coincides with the box**: if
the removed set agrees with the box on an open set `O` containing `z`, and `z` lies on the surface and
on the box sphere, then the trace near `z` is the box-sphere trace, i.e. the curve of the slicing of
the box sphere through `z`.  No transversality of the surface with the box sphere is used: the
argument is purely about the frontier of the removed set near `z`. -/
theorem localModel_of_eq_PBox_on {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3} {O : Set R3}
    (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.sphereSet c σ s)))
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : z ∈ Work.BoxShrink.Core.sphereSet c σ s)
    (hOopen : IsOpen O) (hzO : z ∈ O)
    (heq : tiltedLevelRemoved s c σ u v h ℓ lam ∩ O = Submission.PBox s c σ ∩ O) :
    ∃ O' : Set R3, IsOpen O' ∧ z ∈ O' ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O' ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  classical
  set P : Work.CoreTopology.ParamTorus := Work.Drive.EpsSphere.torusOf ψ with hP
  have hfr : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ∩ O =
      Work.BoxShrink.Core.sphereSet c σ s ∩ O :=
    frontier_tiltedLevelRemoved_inter_of_eq_PBox hs hOopen heq
  obtain ⟨Sl⟩ := hslice
  obtain ⟨i₀, ρ, hρpos, hball⟩ := exists_ball_inter_eq_range_of_sphereSlicing Sl ⟨hz, hzS⟩
  have hmain : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ∩ (O ∩ Metric.ball z ρ) =
      Work.BoxShrink.Core.sphereSet c σ s ∩ (O ∩ Metric.ball z ρ) := by
    calc frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ∩ (O ∩ Metric.ball z ρ)
        = (frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ∩ O) ∩ Metric.ball z ρ := by
          rw [Set.inter_assoc]
      _ = (Work.BoxShrink.Core.sphereSet c σ s ∩ O) ∩ Metric.ball z ρ := by rw [hfr]
      _ = Work.BoxShrink.Core.sphereSet c σ s ∩ (O ∩ Metric.ball z ρ) := by rw [Set.inter_assoc]
  have hSeq : P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s = ⋃ i, Set.range (Sl.c i).γ := by
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
  have htrace : (O ∩ Metric.ball z ρ) ∩ (P.carrier ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) =
      (O ∩ Metric.ball z ρ) ∩ (P.carrier ∩ Set.range (Sl.c i₀).γ) := by
    calc (O ∩ Metric.ball z ρ) ∩ (P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam))
        = P.carrier ∩ (frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ∩
            (O ∩ Metric.ball z ρ)) := by
          ext x; simp only [Set.mem_inter_iff]; tauto
      _ = P.carrier ∩ (Work.BoxShrink.Core.sphereSet c σ s ∩ (O ∩ Metric.ball z ρ)) := by
          rw [hmain]
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

/-- **The trace at a box-sphere point above whose box the wall is inert is the box sphere.** -/
theorem localModel_of_wallInertAbove {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3}
    (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.sphereSet c σ s)))
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : z ∈ Work.BoxShrink.Core.sphereSet c σ s)
    (hW : WallInertAbove s c σ ℓ lam z) :
    ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  obtain ⟨O, hOopen, hzO, heq⟩ :=
    eq_PBox_of_wallInertAbove (u := u) (v := v) (h := h) (lam := lam) hW
  exact localModel_of_eq_PBox_on hs hslice hz hzS hOopen hzO heq

/-- **The trace at a box-sphere point strictly above the level is the box sphere.**  Note that no
transversality of the surface with the box sphere is assumed: this is the local model which remains
valid at a *graze* at which the level is above the point. -/
theorem wallInert_localModel_spherePoint_of_lt_level {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3}
    (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.sphereSet c σ s)))
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : z ∈ Work.BoxShrink.Core.sphereSet c σ s)
    (hzl : lam < ℓ z) :
    ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  refine localModel_of_eq_PBox_on hs hslice hz hzS
    (isOpen_lt continuous_const ℓ.continuous) (by simpa using hzl) ?_
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hyf, hyO⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff,
      Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq] at hyf
    exact ⟨hyf.1, hyO⟩
  · rintro ⟨hyP, hyO⟩
    refine ⟨?_, hyO⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff,
      Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq]
    exact ⟨hyP, fun hc => absurd hc.2 (not_lt.mpr (le_of_lt hyO))⟩

/-- **The trace at a box-sphere point strictly outside the closed slab is the box sphere.** -/
theorem localModel_spherePoint_of_off_slab {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3}
    (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.sphereSet c σ s)))
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : z ∈ Work.BoxShrink.Core.sphereSet c σ s)
    (hzout : h < |inner ℝ v z - (inner ℝ v c + u)|) :
    ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  refine localModel_of_eq_PBox_on hs hslice hz hzS
    (isOpen_lt continuous_const (continuous_abs.comp
      ((continuous_const.inner continuous_id).sub continuous_const)))
    (by simpa using hzout) ?_
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hyf, hyO⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff,
      Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq] at hyf
    exact ⟨hyf.1, hyO⟩
  · rintro ⟨hyP, hyO⟩
    refine ⟨?_, hyO⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff,
      Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq]
    exact ⟨hyP, fun hc => absurd hyO (not_lt.mpr hc.1)⟩

/-- **A point strictly inside the slab and strictly below the level is not in the closure of the
removed set.**  This is the pointwise form of the strict-distance argument: the removed set is empty
on the open set `{|⟪v,·⟫-a| < h} ∩ {ℓ < lam}`, which contains `z`. -/
theorem wallInert_notMem_closure_tiltedLevelRemoved_of_slab_below {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {z : R3}
    (hslab : |inner ℝ v z - (inner ℝ v c + u)| < h) (hzl : ℓ z < lam) :
    z ∉ closure (tiltedLevelRemoved s c σ u v h ℓ lam) := by
  set O : Set R3 := {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| < h} ∩ {y : R3 | ℓ y < lam}
    with hOdef
  have hOopen : IsOpen O :=
    (isOpen_lt (continuous_abs.comp
      ((continuous_const.inner continuous_id).sub continuous_const)) continuous_const).inter
      (isOpen_lt ℓ.continuous continuous_const)
  have hzO : z ∈ O := ⟨hslab, hzl⟩
  have hemp : tiltedLevelRemoved s c σ u v h ℓ lam ∩ O = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyf, hyO⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff] at hyf
    refine hyf.2 ⟨?_, hyO.2⟩
    rw [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq]
    exact le_of_lt hyO.1
  intro hcl
  have hnb : O ∈ 𝓝 z := hOopen.mem_nhds hzO
  obtain ⟨y, hyO, hyf⟩ := mem_closure_iff_nhds.mp hcl O hnb
  have : y ∈ tiltedLevelRemoved s c σ u v h ℓ lam ∩ O := ⟨hyf, hyO⟩
  rw [hemp] at this
  exact this


end

end Work.Drive.Mono
