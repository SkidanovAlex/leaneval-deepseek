import Mathlib
import Submission.Work.Drive.Mono.IsLocallyEuclidean_trace_spherePoint_holds
import Submission.Work.Drive.Mono.TiltedTraceData

/-!
# The trace of a level of the tilted sweep at a box-sphere point *outside the slab*

`Work.Drive.Mono.IsLocallyEuclidean_trace_spherePoint_holds` proves the local Euclidean structure of
the trace `P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)` at a point `z` of the box
sphere, under the two extra hypotheses that `z` is off the level wall (`ℓ z ≠ lam`) and off the two
faces of the tilted slab (`|⟪v,z⟫ - (⟪v,c⟫+u)| ≠ h`).

The present lemma is the case in which `z` lies **outside the closed slab**
(`h < |⟪v,z⟫ - (⟪v,c⟫+u)|`) — the case that arises when the trace is analysed at the points of the
slab boundary.  Then the second factor of the removed set
`tiltedLevelRemoved = PBox \ (slabClosed ∩ {ℓ < lam})` is *empty* on an open neighbourhood of `z`
(namely the open outside-slab region), so the removed set is the box there and its frontier is the
box sphere **regardless of the wall**, and the wall hypothesis `ℓ z ≠ lam` of the `_holds` version is
unnecessary.  The proof is the corresponding branch of the proof of the `_holds` version.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.Mono

noncomputable section

theorem isLocallyEuclidean_trace_spherePoint_outsideSlab {P : Work.CoreTopology.ParamTorus} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ}
    {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s)))
    (hz : z ∈ P.carrier) (hzS : z ∈ Work.BoxShrink.Core.sphereSet c σ s)
    (hface : ∃ i : Fin 3, |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
      ∀ j : Fin 3, j ≠ i → |z (σ j) - c (σ j)| < Submission.boxSide j * s)
    (hzout : h < |inner ℝ v z - (inner ℝ v c + u)|) :
    ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ (P.carrier ∩ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  classical
  set f : Set R3 := Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam with hfdef
  -- the *open* outside-slab region: on it the removed set is the box
  set O : Set R3 := {y : R3 | h < |inner ℝ v y - (inner ℝ v c + u)|} with hOdef
  have hfmem : ∀ y : R3, y ∈ f ↔ y ∈ Submission.PBox s c σ ∧
      ¬ (|inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y < lam) := by
    intro y
    rw [hfdef]
    simp only [Work.Drive.Mono.tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Work.Drive.EpsForm.tiltedSlabClosed]
  have hOmem : ∀ y : R3, y ∈ O ↔ h < |inner ℝ v y - (inner ℝ v c + u)| := by
    intro y; rw [hOdef]; exact Iff.rfl
  have hOopen : IsOpen O := by
    rw [hOdef]
    exact isOpen_lt continuous_const (continuous_abs.comp
      ((continuous_const.inner continuous_id).sub continuous_const))
  have hzO : z ∈ O := (hOmem z).mpr hzout
  have hbox : f ∩ O = Submission.PBox s c σ ∩ O := by
    ext y
    constructor
    · rintro ⟨hyf, hyO⟩
      rw [hfmem y] at hyf
      exact ⟨hyf.1, hyO⟩
    · rintro ⟨hyP, hyO⟩
      refine ⟨?_, hyO⟩
      rw [hfmem y]
      exact ⟨hyP, fun hcon => absurd hcon.1 (not_le.mpr ((hOmem y).mp hyO))⟩
  -- the frontier of `f` is the box sphere on `O`
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

end

end Work.Drive.Mono
