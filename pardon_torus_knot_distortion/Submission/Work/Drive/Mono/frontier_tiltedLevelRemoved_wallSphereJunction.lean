import Mathlib
import Submission.Work.Drive.EpsFormSphere.frontier_tiltedSweptBall_eq
import Submission.Work.Drive.Mono.Trace_eq_levelSet_near_wallPoint_holds
import Submission.Work.Topology.SphereSlicing.isOpen_PBox
import Submission.Work.Topology.SphereSlicing.boxNorm_continuous
import Submission.Work.Topology.SphereSlicing.boxNorm_homogeneous

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- A point lies in the frontier of a set iff it lies in the closure of the set and not in its
interior. -/
private theorem mem_frontier_iff_wsj {X : Type*} [TopologicalSpace X] {s : Set X} {x : X} :
    x ∈ frontier s ↔ x ∈ closure s ∧ x ∉ interior s := by
  rw [← closure_sdiff_interior s, Set.mem_sdiff]

/-- The closure of Pardon's box is contained in the closed sublevel set `{boxNorm ≤ s}`. -/
private theorem closure_PBox_subset_le_wsj (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    closure (Submission.PBox s c σ) ⊆ {y : R3 | Submission.boxNorm c σ y ≤ s} :=
  closure_minimal (fun _ hy => le_of_lt ((Submission.mem_PBox_iff s c σ _).mp hy))
    (isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const)

theorem frontier_tiltedLevelRemoved_wallSphereJunction
    {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ}
    {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hs : 0 < s) (hℓne : ℓ ≠ 0) (hz : Submission.boxNorm c σ z = s)
    (hzslab : |inner ℝ v z - (inner ℝ v c + u)| < h) (hzl : ℓ z = lam)
    (hdir : ∃ δ : ℝ, 0 < δ ∧ ∀ y : LeanEval.KnotTheory.PardonDistortion.R3, dist y z < δ →
      Submission.boxNorm c σ y = s → ℓ y = lam → ∀ ε : ℝ, 0 < ε →
      ∃ y' : LeanEval.KnotTheory.PardonDistortion.R3, dist y' y < ε ∧
        Submission.boxNorm c σ y' < s ∧ ℓ y' ≥ lam) :
    ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
      ∀ y ∈ O, (y ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) ↔
        Submission.boxNorm c σ y ≤ s ∧ ℓ y ≥ lam ∧
          (Submission.boxNorm c σ y = s ∨ ℓ y = lam)) := by
  classical
  obtain ⟨δ, hδpos, hδ⟩ := hdir
  set a : ℝ := inner ℝ v c + u with ha
  set R : Set R3 := Submission.PBox s c σ with hRdef
  set SlabI : Set R3 := Work.Drive.EpsForm.tiltedSlab a v h with hSlabIdef
  set S : Set R3 := Work.Drive.EpsForm.tiltedSlabClosed a v h with hSdef
  set f : Set R3 := Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam with hfdef
  have hf_eq : f = R \ (S ∩ {y : R3 | ℓ y < lam}) := by
    rw [hfdef, hRdef, hSdef, ha, Work.Drive.Mono.tiltedLevelRemoved]
  have hRopen : IsOpen R := by
    rw [hRdef]; exact Work.Topology.SphereSlicing.isOpen_PBox s c σ
  have hSlabIopen : IsOpen SlabI := by
    rw [hSlabIdef, Work.Drive.EpsForm.tiltedSlab]
    exact isOpen_lt
      (continuous_abs.comp ((continuous_const.inner continuous_id).sub continuous_const))
      continuous_const
  have hzSlabI : z ∈ SlabI := by
    rw [hSlabIdef, Work.Drive.EpsForm.tiltedSlab, ha]; exact hzslab
  -- local description of `f` on the interior of the slab
  have hfloc : ∀ w : R3, w ∈ SlabI → (w ∈ f ↔ w ∈ R ∧ ℓ w ≥ lam) := by
    intro w hw
    have hwS : w ∈ S := by
      rw [hSdef, Work.Drive.EpsForm.tiltedSlabClosed]
      exact le_of_lt (by simpa [hSlabIdef, Work.Drive.EpsForm.tiltedSlab] using hw)
    rw [hf_eq, Set.mem_sdiff, Set.mem_inter_iff]
    constructor
    · rintro ⟨hwR, hnot⟩
      refine ⟨hwR, ?_⟩
      by_contra hcon
      exact hnot ⟨hwS, not_le.mp hcon⟩
    · rintro ⟨hwR, hge⟩
      refine ⟨hwR, ?_⟩
      rintro ⟨-, hlt⟩
      exact absurd (show ℓ w < lam from hlt) (not_lt.mpr hge)
  have hsub_fR : f ⊆ R := by intro w hw; rw [hf_eq] at hw; exact hw.1
  have hclosR : closure f ⊆ {w : R3 | Submission.boxNorm c σ w ≤ s} := by
    have h1 : closure f ⊆ closure (Submission.PBox s c σ) := by
      have h2 := closure_mono hsub_fR
      rwa [hRdef] at h2
    exact h1.trans (closure_PBox_subset_le_wsj s c σ)
  -- closure of `f` at a point of the box sphere strictly above the level
  have hclos_gt : ∀ w : R3, Submission.boxNorm c σ w = s → ℓ w > lam → w ∈ closure f := by
    intro w hwb hwl
    have hwc : w - c ≠ 0 := by
      intro he
      have hwce : w = c := sub_eq_zero.mp he
      rw [hwce] at hwb
      have h0 : Submission.boxNorm c σ c = 0 := by simp [Submission.boxNorm]
      rw [h0] at hwb
      exact absurd hwb (ne_of_lt hs)
    rw [Metric.mem_closure_iff]
    intro ε hε
    set η : ℝ := min (min (1 / 2) (ε / (2 * (‖w - c‖ + 1))))
      ((ℓ w - lam) / (2 * (|ℓ w - ℓ c| + 1))) with hηdef
    have hηpos : 0 < η := by
      rw [hηdef]
      exact lt_min (lt_min (by norm_num) (div_pos hε (by positivity)))
        (div_pos (by linarith) (by positivity))
    have hηhalf : η ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hηε : η * ‖w - c‖ < ε := by
      have h1 : η ≤ ε / (2 * (‖w - c‖ + 1)) :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      calc η * ‖w - c‖ ≤ (ε / (2 * (‖w - c‖ + 1))) * ‖w - c‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖w - c‖ + 1))]
            nlinarith [norm_nonneg (w - c), hε]
    have hηl : η * (ℓ w - ℓ c) < ℓ w - lam := by
      have h2 : η ≤ (ℓ w - lam) / (2 * (|ℓ w - ℓ c| + 1)) := min_le_right _ _
      calc η * (ℓ w - ℓ c) ≤ η * |ℓ w - ℓ c| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (le_of_lt hηpos)
        _ ≤ ((ℓ w - lam) / (2 * (|ℓ w - ℓ c| + 1))) * |ℓ w - ℓ c| :=
            mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ < ℓ w - lam := by
            rw [div_mul_eq_mul_div,
              div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (|ℓ w - ℓ c| + 1))]
            nlinarith [abs_nonneg (ℓ w - ℓ c), hwl]
    have h1half : 0 < 1 - η := by linarith
    refine ⟨c + (1 - η) • (w - c), ?_, ?_⟩
    · rw [hf_eq, Set.mem_sdiff, Set.mem_inter_iff]
      refine ⟨?_, ?_⟩
      · have hb' : Submission.boxNorm c σ (c + (1 - η) • (w - c)) < s := by
          rw [Work.Topology.SphereSlicing.boxNorm_homogeneous c σ (1 - η) w, hwb,
            abs_of_pos h1half]
          nlinarith [hs, hηpos]
        rw [hRdef]
        exact (Submission.mem_PBox_iff s c σ _).mpr hb'
      · rintro ⟨-, hlt⟩
        have hval : ℓ (c + (1 - η) • (w - c)) = ℓ w - η * (ℓ w - ℓ c) := by
          rw [map_add, map_smul, map_sub, smul_eq_mul]; ring
        have hlt' : ℓ (c + (1 - η) • (w - c)) < lam := hlt
        rw [hval] at hlt'
        linarith
    · have hvec : c + (1 - η) • (w - c) - w = -η • (w - c) := by module
      rw [dist_comm, dist_eq_norm, hvec, norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_pos hηpos]
      exact hηε
  -- closure of `f` at the junction, using the prescribed direction
  have hclos_lvl : ∀ w : R3, dist w z < δ → Submission.boxNorm c σ w = s → ℓ w = lam →
      w ∈ closure f := by
    intro w hwδ hwb hwl
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨w', hw'd, hw'b, hw'l⟩ := hδ w hwδ hwb hwl ε hε
    refine ⟨w', ?_, ?_⟩
    · rw [hf_eq, Set.mem_sdiff, Set.mem_inter_iff]
      exact ⟨(Submission.mem_PBox_iff s c σ w').mpr hw'b,
        fun h => absurd (show ℓ w' < lam from h.2) (not_lt.mpr hw'l)⟩
    · rw [dist_comm]; exact hw'd
  -- interior of `f` in the open box strictly above the level
  have hint : ∀ w : R3, w ∈ R → ℓ w > lam → w ∈ interior f := by
    intro w hwR hwl
    refine interior_maximal ?_ (hRopen.inter (isOpen_lt continuous_const ℓ.continuous))
      ⟨hwR, hwl⟩
    rintro t ⟨htR, htl⟩
    rw [hf_eq, Set.mem_sdiff, Set.mem_inter_iff]
    exact ⟨htR, fun h => absurd (show ℓ t < lam from h.2) (not_lt.mpr (le_of_lt htl))⟩
  obtain ⟨ρ1, hρ1pos, hρ1sub⟩ := Metric.isOpen_iff.mp hSlabIopen z hzSlabI
  set O : Set R3 := Metric.ball z (min ρ1 δ) with hOdef
  have hOopen : IsOpen O := by rw [hOdef]; exact Metric.isOpen_ball
  have hzO : z ∈ O := by
    rw [hOdef, Metric.mem_ball, dist_self]; exact lt_min hρ1pos hδpos
  have hOsubSlab : O ⊆ SlabI := by
    intro y hy
    rw [hOdef] at hy
    exact hρ1sub (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _)))
  -- a point of `O` strictly below the level is not in the closure of `f`
  have hnotclos_lt : ∀ w : R3, w ∈ O → ℓ w < lam → w ∉ closure f := by
    intro w hwO hwl hwcl
    have hwSlabI : w ∈ SlabI := hOsubSlab hwO
    obtain ⟨r1, hr1pos, hr1sub⟩ := Metric.isOpen_iff.mp hSlabIopen w hwSlabI
    obtain ⟨r2, hr2pos, hr2sub⟩ :=
      Metric.isOpen_iff.mp (isOpen_lt ℓ.continuous continuous_const) w hwl
    obtain ⟨t, htf, htd⟩ := (Metric.mem_closure_iff.mp hwcl) (min r1 r2)
      (lt_min hr1pos hr2pos)
    have htd' : dist t w < min r1 r2 := by rwa [dist_comm]
    have htSlabI : t ∈ SlabI :=
      hr1sub (Metric.mem_ball.mpr (lt_of_lt_of_le htd' (min_le_left _ _)))
    have htlt : ℓ t < lam :=
      hr2sub (Metric.mem_ball.mpr (lt_of_lt_of_le htd' (min_le_right _ _)))
    exact absurd htlt (not_lt.mpr ((hfloc t htSlabI).mp htf).2)
  -- a point of `O` inside the box at the level is not in the interior of `f`
  have hnotint_lvl : ∀ w : R3, w ∈ O → Submission.boxNorm c σ w < s → ℓ w = lam →
      w ∉ interior f := by
    intro w hwO hwb hwl hwint
    have hwSlabI : w ∈ SlabI := hOsubSlab hwO
    obtain ⟨r1, hr1pos, hr1sub⟩ := Metric.isOpen_iff.mp hSlabIopen w hwSlabI
    obtain ⟨r2, hr2pos, hr2sub0⟩ := Metric.isOpen_iff.mp isOpen_interior w hwint
    have hr2sub : Metric.ball w r2 ⊆ f := fun x hx => interior_subset (hr2sub0 hx)
    obtain ⟨g, hgneg⟩ : ∃ g : R3, ℓ g < 0 := by
      obtain ⟨g0, hg0⟩ := Work.Drive.EpsFormSphere.exists_apply_ne_zero hℓne
      rcases lt_or_gt_of_ne hg0 with h | h
      · exact ⟨g0, h⟩
      · exact ⟨-g0, by rw [map_neg]; exact neg_lt_zero.mpr h⟩
    set t : ℝ := min r1 r2 / (2 * (‖g‖ + 1)) with htdef
    have htpos : 0 < t := by
      rw [htdef]; exact div_pos (lt_min hr1pos hr2pos) (by positivity)
    have htmin : t * ‖g‖ < min r1 r2 := by
      rw [htdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖g‖ + 1))]
      nlinarith [norm_nonneg g, lt_min hr1pos hr2pos]
    have hwt1 : w + t • g ∈ Metric.ball w r1 := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos htpos]
      exact lt_of_lt_of_le htmin (min_le_left _ _)
    have hwt2 : w + t • g ∈ Metric.ball w r2 := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos htpos]
      exact lt_of_lt_of_le htmin (min_le_right _ _)
    have hmemf : w + t • g ∈ f := hr2sub hwt2
    have hmemSlabI : w + t • g ∈ SlabI := hr1sub hwt1
    have hlt' : ℓ (w + t • g) < lam := by
      rw [map_add, map_smul, smul_eq_mul, hwl]
      have hgt : t * ℓ g < 0 := mul_neg_of_pos_of_neg htpos hgneg
      linarith
    exact absurd hlt' (not_lt.mpr ((hfloc (w + t • g) hmemSlabI).mp hmemf).2)
  refine ⟨O, hOopen, hzO, ?_⟩
  intro y hyO
  have hyball : y ∈ Metric.ball z (min ρ1 δ) := hOdef ▸ hyO
  have hyδ : dist y z < δ :=
    lt_of_lt_of_le (Metric.mem_ball.mp hyball) (min_le_right _ _)
  have hySlabI : y ∈ SlabI := hOsubSlab hyO
  constructor
  · intro hyfront
    have hycl : y ∈ closure f := by
      have h := hyfront; rw [mem_frontier_iff_wsj] at h; exact h.1
    have hyint : y ∉ interior f := by
      have h := hyfront; rw [mem_frontier_iff_wsj] at h; exact h.2
    have hyclO : y ∈ closure (O ∩ f) := by
      rw [Metric.mem_closure_iff] at hycl ⊢
      intro ε hε
      obtain ⟨r, hrpos, hrsub⟩ := Metric.isOpen_iff.mp hOopen y hyO
      obtain ⟨t, htf, htd⟩ := hycl (min ε r) (lt_min hε hrpos)
      have htd' : dist t y < min ε r := by rwa [dist_comm]
      refine ⟨t, ⟨?_, htf⟩, ?_⟩
      · exact hrsub (Metric.mem_ball.mpr (lt_of_lt_of_le htd' (min_le_right _ _)))
      · exact lt_of_lt_of_le htd (min_le_left _ _)
    have hsub : O ∩ f ⊆ {w : R3 | Submission.boxNorm c σ w ≤ s ∧ ℓ w ≥ lam} := by
      rintro w ⟨hwO, hwf⟩
      exact ⟨hclosR (subset_closure hwf), ((hfloc w (hOsubSlab hwO)).mp hwf).2⟩
    have hclosed : IsClosed {w : R3 | Submission.boxNorm c σ w ≤ s ∧ ℓ w ≥ lam} :=
      (isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const).inter
        (isClosed_le continuous_const ℓ.continuous)
    obtain ⟨hble, hge⟩ := closure_minimal hsub hclosed hyclO
    refine ⟨hble, hge, ?_⟩
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hne1, hne2⟩ := hcon
    have hlt : Submission.boxNorm c σ y < s := lt_of_le_of_ne hble hne1
    have hgt : ℓ y > lam := lt_of_le_of_ne hge (Ne.symm hne2)
    have hyR : y ∈ R := by rw [hRdef]; exact (Submission.mem_PBox_iff s c σ y).mpr hlt
    exact hyint (hint y hyR hgt)
  · intro hRHS
    obtain ⟨hble, hge, hcase⟩ := hRHS
    have hycl : y ∈ closure f := by
      rcases hcase with hbeq | hleq
      · rcases lt_or_eq_of_le hge with hlt | heq
        · exact hclos_gt y hbeq hlt
        · exact hclos_lvl y hyδ hbeq heq.symm
      · by_cases hbeq : Submission.boxNorm c σ y = s
        · exact hclos_lvl y hyδ hbeq hleq
        · have hblt : Submission.boxNorm c σ y < s := lt_of_le_of_ne hble hbeq
          have hyf : y ∈ f := by
            rw [hf_eq, Set.mem_sdiff, Set.mem_inter_iff]
            refine ⟨?_, ?_⟩
            · rw [hRdef]; exact (Submission.mem_PBox_iff s c σ y).mpr hblt
            · rintro ⟨-, hlt⟩
              have hlt' : ℓ y < lam := hlt
              rw [hleq] at hlt'
              exact absurd hlt' (lt_irrefl lam)
          exact subset_closure hyf
    have hyint : y ∉ interior f := by
      intro hyi
      by_cases hbeq : Submission.boxNorm c σ y = s
      · have hyR : y ∉ R := by
          rw [hRdef, Submission.mem_PBox_iff]
          intro hlt
          exact absurd hbeq (ne_of_lt hlt)
        exact hyR (hsub_fR (interior_subset hyi))
      · have hblt : Submission.boxNorm c σ y < s := lt_of_le_of_ne hble hbeq
        have hleq : ℓ y = lam := hcase.resolve_left hbeq
        exact hnotint_lvl y hyO hblt hleq hyi
    rw [mem_frontier_iff_wsj]
    exact ⟨hycl, hyint⟩

end

end Work.Drive.Mono
