import Mathlib
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.Topology.SphereSlicing.isOpen_PBox

namespace Work.Drive.Mono

open Set
open LeanEval.KnotTheory.PardonDistortion

/-- **The trace of the tilted sweep near a wall point.**
At a point `z` of the box which lies in the *open* tilted slab, the frontier of the level's removed
set coincides, near `z`, with the level set `{ℓ = lam}` intersected with the surface.

The removed set is `f = PBox ∖ (S ∩ L)` where `S` is the closed tilted slab and `L = {ℓ < lam}` is
the open half-space behind the wall.  Because `z` is strictly inside the slab, the open box `O` is
a neighbourhood of `z` on which one has, for every `y ∈ O`:

* `ℓ y < lam`  ⟹  `y ∈ S ∩ L` with room to spare, hence `y ∈ interior (fᶜ)`: it is not even in
  `closure f`;
* `lam < ℓ y`  ⟹  a whole neighbourhood of `y` is contained in `f`: `y ∈ interior f`;
* `ℓ y = lam`  ⟹  `y ∈ f ⊆ closure f`, while every neighbourhood of `y` meets `S ∩ L` (move
  slightly towards smaller `ℓ`, using `ℓ ≠ 0`): `y ∉ interior f`.

Hence on `O`, `frontier f` is exactly `{ℓ = lam}`. -/
theorem Trace_eq_levelSet_near_wallPoint_holds
    {P : Work.CoreTopology.ParamTorus} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ} {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    {lam : ℝ}
    {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hℓne : ℓ ≠ 0)
    (hz : z ∈ P.carrier) (hzb : z ∈ Submission.PBox s c σ)
    (hzslab : |inner ℝ v z - (inner ℝ v c + u)| < h) (hzl : ℓ z = lam) :
    ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
      O ∩ (P.carrier ∩ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))
        = O ∩ P.carrier ∩ {y : LeanEval.KnotTheory.PardonDistortion.R3 | ℓ y = lam} := by
  classical
  set Slab : Set R3 := Work.Drive.EpsForm.tiltedSlab (inner ℝ v c + u) v h with hSlabdef
  set S : Set R3 := Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h with hSdef
  set L : Set R3 := {y : R3 | ℓ y < lam} with hLdef
  set f : Set R3 := Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam with hfdef
  have hf_exp : f = Submission.PBox s c σ \ (S ∩ L) := by
    simp only [hfdef, hSdef, hLdef, Work.Drive.Mono.tiltedLevelRemoved]
  have hSlab_open : IsOpen Slab := by
    rw [hSlabdef, Work.Drive.EpsForm.tiltedSlab]
    exact isOpen_lt (by fun_prop) continuous_const
  have hSlab_sub : Slab ⊆ S := by
    rw [hSlabdef, hSdef]
    exact Work.Drive.EpsForm.tiltedSlab_subset_tiltedSlabClosed _ _ _
  have hL_open : IsOpen L := by
    rw [hLdef]
    exact isOpen_lt ℓ.continuous continuous_const
  have hLmem : ∀ y : R3, (y ∈ L ↔ ℓ y < lam) := fun y => Iff.rfl
  have hfmem : ∀ y : R3, (y ∈ f ↔ y ∈ Submission.PBox s c σ ∧ ¬ (y ∈ S ∧ y ∈ L)) := by
    intro y; rw [hf_exp, Set.mem_sdiff, Set.mem_inter_iff]
  have hfront_mem : ∀ y : R3, (y ∈ frontier f ↔ y ∈ closure f ∧ y ∉ interior f) := by
    intro y; rw [frontier, Set.mem_sdiff]
  refine ⟨Submission.PBox s c σ ∩ Slab,
    (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter hSlab_open, ⟨hzb, ?_⟩, ?_⟩
  · rw [hSlabdef, Work.Drive.EpsForm.tiltedSlab]; exact hzslab
  · have key : ∀ y : R3, y ∈ Submission.PBox s c σ ∩ Slab →
        (y ∈ frontier f ↔ ℓ y = lam) := by
      intro y hyO
      have hyR : y ∈ Submission.PBox s c σ := hyO.1
      have hySlab : y ∈ Slab := hyO.2
      constructor
      · intro hyfr
        obtain ⟨-, hyint⟩ := (hfront_mem y).mp hyfr
        rcases lt_trichotomy (ℓ y) lam with hlt | heq | hgt
        · exfalso
          have hsub : Slab ∩ L ⊆ fᶜ := by
            rintro t ⟨htSlab, htL⟩
            rw [Set.mem_compl_iff]
            intro htf
            exact ((hfmem t).mp htf).2 ⟨hSlab_sub htSlab, htL⟩
          have hyint' : y ∈ interior fᶜ :=
            interior_maximal hsub (hSlab_open.inter hL_open) ⟨hySlab, (hLmem y).mpr hlt⟩
          rw [interior_compl] at hyint'
          exact hyint' (frontier_subset_closure hyfr)
        · exact heq
        · exfalso
          have hsub2 : (Submission.PBox s c σ ∩ Slab) ∩ {t : R3 | lam < ℓ t} ⊆ f := by
            rintro t ⟨⟨htR, -⟩, htgt⟩
            rw [hfmem]
            refine ⟨htR, ?_⟩
            intro htm
            exact absurd ((hLmem t).mp htm.2) (not_lt.mpr (le_of_lt htgt))
          have hOpen2 : IsOpen ((Submission.PBox s c σ ∩ Slab) ∩ {t : R3 | lam < ℓ t}) :=
            ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter hSlab_open).inter
              (isOpen_lt continuous_const ℓ.continuous)
          have hyint2 : y ∈ interior f := interior_maximal hsub2 hOpen2 ⟨hyO, hgt⟩
          exact hyint hyint2
      · intro hylam
        refine (hfront_mem y).mpr ⟨?_, ?_⟩
        · apply subset_closure
          rw [hfmem]
          refine ⟨hyR, ?_⟩
          rintro ⟨-, hL⟩
          have hlt : ℓ y < lam := (hLmem y).mp hL
          rw [hylam] at hlt
          exact absurd hlt (lt_irrefl lam)
        · intro hyint
          obtain ⟨w, hwpos⟩ : ∃ w : R3, 0 < ℓ w := by
            obtain ⟨w, hw⟩ : ∃ w : R3, ℓ w ≠ 0 := by
              by_contra hc
              simp only [not_exists, not_ne_iff] at hc
              exact hℓne (ContinuousLinearMap.ext hc)
            rcases lt_or_gt_of_ne hw with hneg | hpos
            · exact ⟨-w, by simpa using neg_pos.mpr hneg⟩
            · exact ⟨w, hpos⟩
          have hwne : w ≠ 0 := by
            rintro rfl
            rw [map_zero] at hwpos
            exact (lt_irrefl (0 : ℝ)) hwpos
          have hnormpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
          obtain ⟨ε, hεpos, hεsub⟩ :=
            Metric.isOpen_iff.mp (hSlab_open.inter isOpen_interior) y ⟨hySlab, hyint⟩
          set t : ℝ := ε / (2 * (‖w‖ + 1)) with htdef
          have htpos : 0 < t := by
            rw [htdef]; positivity
          have htw : t * (‖w‖ + 1) = ε / 2 := by
            rw [htdef, div_mul_eq_mul_div]
            exact mul_div_mul_right ε 2 (by positivity)
          have hball : y - t • w ∈ Slab ∩ interior f := by
            apply hεsub
            rw [Metric.mem_ball, dist_eq_norm]
            have h1 : y - t • w - y = -(t • w) := by abel
            rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
            have hle : t * ‖w‖ ≤ t * (‖w‖ + 1) := by
              have : ‖w‖ ≤ ‖w‖ + 1 := by linarith [norm_nonneg w]
              exact mul_le_mul_of_nonneg_left this (le_of_lt htpos)
            rw [htw] at hle
            linarith
          have hy'S : y - t • w ∈ S := hSlab_sub hball.1
          have hy'L : y - t • w ∈ L := by
            refine (hLmem _).mpr ?_
            have hval : ℓ (y - t • w) = lam - t * ℓ w := by
              rw [map_sub, map_smul, hylam]; simp [smul_eq_mul]
            rw [hval]
            have : 0 < t * ℓ w := mul_pos htpos hwpos
            linarith
          exact ((hfmem (y - t • w)).mp (interior_subset hball.2)).2 ⟨hy'S, hy'L⟩
    have hOeq : (Submission.PBox s c σ ∩ Slab) ∩ frontier f
        = (Submission.PBox s c σ ∩ Slab) ∩ {y : R3 | ℓ y = lam} := by
      ext y
      rw [Set.mem_inter_iff]
      constructor
      · rintro ⟨hyO, hyfr⟩
        exact ⟨hyO, (key y hyO).mp hyfr⟩
      · rintro ⟨hyO, hyℓ⟩
        exact ⟨hyO, (key y hyO).mpr hyℓ⟩
    calc (Submission.PBox s c σ ∩ Slab) ∩ (P.carrier ∩ frontier f)
        = ((Submission.PBox s c σ ∩ Slab) ∩ frontier f) ∩ P.carrier := by
          ext y; simp only [Set.mem_inter_iff]; tauto
      _ = ((Submission.PBox s c σ ∩ Slab) ∩ {y : R3 | ℓ y = lam}) ∩ P.carrier := by rw [hOeq]
      _ = (Submission.PBox s c σ ∩ Slab) ∩ P.carrier ∩ {y : R3 | ℓ y = lam} := by
          ext y; simp only [Set.mem_inter_iff]; tauto

end Work.Drive.Mono
