import Mathlib
import Submission.Work.Drive.Mono.SphereFaceDefs

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-!
# The frontier of a level of the tilted sweep at a box-sphere/face-plane junction

This module proves `Work.Drive.Mono.frontier_tiltedLevelRemoved_sphereFace`: at a point `z` of the
surface which lies simultaneously on the box sphere (`boxNorm c σ z = s`) and on the *upper face of
the tilted slab* (`⟪v,z⟫ = ⟪v,c⟫ + u + h`), and strictly behind the level wall (`ℓ z < lam`), the
frontier of the removed set `R = PBox \ (slab ∩ {ℓ < lam})` is, near `z`, the "corner"

  `{boxNorm ≤ s ∧ a + h ≤ ⟪v,·⟫ ∧ (boxNorm = s ∨ ⟪v,·⟫ = a + h)}`  (`a := ⟪v,c⟫ + u`).

Away from `z` the only way for a point of the surface to satisfy the two equalities
`boxNorm = s` and `⟪v,·⟫ = a + h` is to be in the *closure* of `PBox ∩ {⟪v,·⟫ > a + h}`, which can
fail exactly when `v` is parallel to the active face normal of the box at that point; this is what
the hypothesis `hhsep` excludes (and `hcl` supplies at `z` itself).

The proof is elementary point-set topology of `ℝ³`:

* pick a ball around `z` on which `ℓ < lam` and `⟪v,·⟫ > a - h`; there the removed set agrees with
  `PBox ∩ {⟪v,·⟫ > a + h}` (the lower half `{⟪v,·⟫ < a - h}` of the complement of the slab is
  disjoint from the ball, and `ℓ < lam` makes the wall condition vacuous);
* `frontier` commutes with restriction to the (open) ball, `frontier_inter_open_inter`;
* the inclusion `frontier (PBox ∩ {⟪v,·⟫ > a + h}) ⊆ {boxNorm ≤ s ∧ a + h ≤ ⟪v,·⟫ ∧ …}` is the
  closure of an open set minus itself: `closure` of an intersection is contained in the intersection
  of the closures, and a point of `PBox ∩ {⟪v,·⟫ > a + h}` is interior;
* conversely, a point of the corner set with `boxNorm = s` and `⟪v,·⟫ > a + h` is a limit of points
  of `PBox ∩ {⟪v,·⟫ > a + h}` rayed towards the centre (`v ≠ 0` is used in the other mixed case,
  where the perturbation is along `v`).
-/

/-- A point of the closed box is a limit of points of the open box. -/
theorem mem_closure_PBox_of_boxNorm_le {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    {y : R3} (hy : Submission.boxNorm c σ y ≤ s) : y ∈ closure (Submission.PBox s c σ) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t : ℝ := min (1 / 2) (ε / (2 * (‖y - c‖ + 1))) with htdef
  have htpos : 0 < t := by
    rw [htdef]; exact lt_min (by norm_num) (div_pos hε (by positivity))
  have ht1 : t ≤ 1 / 2 := by rw [htdef]; exact min_le_left _ _
  refine ⟨c + (1 - t) • (y - c), ?_, ?_⟩
  · rw [Submission.mem_PBox_iff, Work.Topology.SphereSlicing.frontier_PBox_boxNorm_homogeneous,
      abs_of_pos (by linarith : (0:ℝ) < 1 - t)]
    nlinarith [hs, ht1, htpos, hy, Submission.boxNorm_nonneg c σ y]
  · rw [dist_eq_norm]
    have hsub : y - (c + (1 - t) • (y - c)) = t • (y - c) := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hnc : (0:ℝ) ≤ ‖y - c‖ := norm_nonneg _
    have h3 : ε / (2 * (‖y - c‖ + 1)) * ‖y - c‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (‖y - c‖ + 1))]
      nlinarith [hnc, hε]
    have h2 : t * ‖y - c‖ ≤ ε / (2 * (‖y - c‖ + 1)) * ‖y - c‖ :=
      mul_le_mul_of_nonneg_right (by rw [htdef]; exact min_le_right _ _) hnc
    linarith

/-- A point with `A ≤ ⟪v,·⟫` is a limit of points with `A < ⟪v,·⟫`, for `v ≠ 0`. -/
theorem mem_closure_gt_of_le {A : ℝ} {v : R3} (hv : v ≠ 0) {y : R3}
    (h : A ≤ inner ℝ v y) : y ∈ closure {y : R3 | A < inner ℝ v y} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set t : ℝ := ε / (2 * (‖v‖ + 1)) with htdef
  have htpos : 0 < t := by rw [htdef]; exact div_pos hε (by positivity)
  refine ⟨y + t • v, ?_, ?_⟩
  · show A < inner ℝ v (y + t • v)
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have : 0 < t * ‖v‖ ^ 2 := by positivity
    linarith
  · rw [dist_eq_norm]
    have hsub : y - (y + t • v) = -(t • v) := by module
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    rw [htdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (‖v‖ + 1))]
    nlinarith [hvnorm, hε]

/-- The frontier of the half-box `PBox ∩ {A < ⟪v,·⟫}` is contained in the corner set
`{boxNorm ≤ s ∧ A ≤ ⟪v,·⟫ ∧ (boxNorm = s ∨ ⟪v,·⟫ = A)}`. -/
theorem frontier_PBox_inter_gt_subset {s A : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v y : R3} :
    y ∈ frontier (Submission.PBox s c σ ∩ {y : R3 | A < inner ℝ v y}) →
    Submission.boxNorm c σ y ≤ s ∧ A ≤ inner ℝ v y ∧
      (Submission.boxNorm c σ y = s ∨ inner ℝ v y = A) := by
  intro hy
  rw [frontier] at hy
  have hclos : y ∈ closure (Submission.PBox s c σ ∩ {y : R3 | A < inner ℝ v y}) := hy.1
  have hnotint : y ∉ interior (Submission.PBox s c σ ∩ {y : R3 | A < inner ℝ v y}) := hy.2
  have hclos_box : y ∈ closure (Submission.PBox s c σ) :=
    closure_mono (Set.inter_subset_left :
      Submission.PBox s c σ ∩ {y : R3 | A < inner ℝ v y} ⊆ Submission.PBox s c σ) hclos
  have hclos_U : y ∈ closure {y : R3 | A < inner ℝ v y} :=
    closure_mono (Set.inter_subset_right :
      Submission.PBox s c σ ∩ {y : R3 | A < inner ℝ v y} ⊆ {y : R3 | A < inner ℝ v y}) hclos
  have hbox : Submission.boxNorm c σ y ≤ s :=
    closure_minimal (fun w hw => le_of_lt ((Submission.mem_PBox_iff s c σ w).mp hw))
      (isClosed_le (Work.Topology.SphereSlicing.frontier_PBox_boxNorm_continuous c σ)
        continuous_const) hclos_box
  have hA : A ≤ inner ℝ v y :=
    closure_lt_subset_le continuous_const (continuous_const.inner continuous_id) hclos_U
  refine ⟨hbox, hA, ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hbne, hAne⟩ := hcon
  have hblt : Submission.boxNorm c σ y < s := lt_of_le_of_ne hbox hbne
  have hAlt : A < inner ℝ v y := lt_of_le_of_ne hA (Ne.symm hAne)
  have hopen : IsOpen (Submission.PBox s c σ ∩ {y : R3 | A < inner ℝ v y}) :=
    (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter
      (isOpen_lt continuous_const (continuous_const.inner continuous_id))
  have hmem : y ∈ Submission.PBox s c σ ∩ {y : R3 | A < inner ℝ v y} :=
    ⟨(Submission.mem_PBox_iff s c σ y).mpr hblt, hAlt⟩
  exact hnotint (by rwa [hopen.interior_eq])

/-- NB: the two hypotheses `hcl` and `hhsep` are NOT redundant, despite their apparent content:
`cl (PBox ∩ {⟪v,·⟫ > a+h})` is strictly smaller than `cl PBox ∩ cl {⟪v,·⟫ > a+h}` at points where
`v` is parallel to the active face normal, so the double-equality case `boxNorm = s ∧ ⟪v,·⟫ = a+h`
(which lies in the right-hand set) has to be excluded by `hhsep`, with `z` itself handled by `hcl`. -/
theorem frontier_tiltedLevelRemoved_sphereFace (ψ : Submission.Diffeo) {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3}
    (hs : 0 < s) (hv : v ≠ 0) (hh : 0 < h)
    (hzsphere : Submission.boxNorm c σ z = s)
    (hzface : inner ℝ v z = inner ℝ v c + u + h) (hzl : ℓ z < lam)
    (hcl : z ∈ closure (Submission.PBox s c σ ∩ {y : R3 | inner ℝ v c + u + h < inner ℝ v y}))
    (hhsep : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ y : R3, y ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        dist y z < ρ₀ → Submission.boxNorm c σ y = s →
        inner ℝ v y = inner ℝ v c + u + h → y = z) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball z ρ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) =
        Metric.ball z ρ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          {y : R3 | Submission.boxNorm c σ y ≤ s ∧ inner ℝ v c + u + h ≤ inner ℝ v y ∧
            (Submission.boxNorm c σ y = s ∨ inner ℝ v y = inner ℝ v c + u + h)}) := by
  obtain ⟨ρ₀, hρ₀pos, hsep⟩ := hhsep
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ y : R3, dist y z < δ₁ → ℓ y < lam := by
    obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp
      (isOpen_lt ℓ.continuous continuous_const) z hzl
    exact ⟨δ, hδpos, fun y hy => hδ hy⟩
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ : ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ y : R3, dist y z < δ₂ →
      inner ℝ v c + u - h < inner ℝ v y := by
    have hz_gt : inner ℝ v c + u - h < inner ℝ v z := by rw [hzface]; linarith
    have hopen : IsOpen {y : R3 | inner ℝ v c + u - h < inner ℝ v y} :=
      isOpen_lt continuous_const (continuous_const.inner continuous_id)
    obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hopen z hz_gt
    exact ⟨δ, hδpos, fun y hy => hδ hy⟩
  set ρ : ℝ := min (min δ₁ δ₂) ρ₀ with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min (lt_min hδ₁pos hδ₂pos) hρ₀pos
  have hρδ₁ : ρ ≤ δ₁ := by rw [hρdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρδ₂ : ρ ≤ δ₂ := by rw [hρdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρρ₀ : ρ ≤ ρ₀ := by rw [hρdef]; exact min_le_right _ _
  have hℓball : ∀ y : R3, y ∈ Metric.ball z ρ → ℓ y < lam :=
    fun y hy => hδ₁ y (lt_of_lt_of_le hy hρδ₁)
  have hAball : ∀ y : R3, y ∈ Metric.ball z ρ → inner ℝ v c + u - h < inner ℝ v y :=
    fun y hy => hδ₂ y (lt_of_lt_of_le hy hρδ₂)
  -- On the ball the removed set is the upper half of the box.
  have hloc_pt : ∀ y : R3, y ∈ Metric.ball z ρ →
      (y ∈ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam ↔
        y ∈ Submission.PBox s c σ ∧ inner ℝ v c + u + h < inner ℝ v y) := by
    intro y hyb
    have hyℓ : ℓ y < lam := hℓball y hyb
    have hygt : inner ℝ v c + u - h < inner ℝ v y := hAball y hyb
    constructor
    · intro hy
      rw [Work.Drive.Mono.tiltedLevelRemoved, Set.mem_sdiff] at hy
      obtain ⟨hyP, hynot⟩ := hy
      refine ⟨hyP, ?_⟩
      have hnot : ¬ (|inner ℝ v y - (inner ℝ v c + u)| ≤ h) := by
        intro hle
        exact hynot ⟨hle, hyℓ⟩
      rcases lt_abs.mp (not_le.mp hnot) with hlt | hlt
      · linarith
      · exfalso; linarith
    · intro hy'
      rw [Work.Drive.Mono.tiltedLevelRemoved, Set.mem_sdiff]
      refine ⟨hy'.1, ?_⟩
      rintro ⟨hle, _⟩
      have hle' : |inner ℝ v y - (inner ℝ v c + u)| ≤ h := hle
      have h1 : inner ℝ v y - (inner ℝ v c + u) ≤ |inner ℝ v y - (inner ℝ v c + u)| :=
        le_abs_self _
      linarith
  have hloc : Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam ∩ Metric.ball z ρ =
      (Submission.PBox s c σ ∩ {y : R3 | inner ℝ v c + u + h < inner ℝ v y}) ∩
        Metric.ball z ρ := by
    ext y
    constructor
    · rintro ⟨hyR, hyb⟩; exact ⟨(hloc_pt y hyb).mp hyR, hyb⟩
    · rintro ⟨hyPU, hyb⟩; exact ⟨(hloc_pt y hyb).mpr hyPU, hyb⟩
  have hfr : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) ∩ Metric.ball z ρ =
      frontier (Submission.PBox s c σ ∩ {y : R3 | inner ℝ v c + u + h < inner ℝ v y}) ∩
        Metric.ball z ρ :=
    calc frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) ∩ Metric.ball z ρ
        = frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam ∩ Metric.ball z ρ)
            ∩ Metric.ball z ρ := (frontier_inter_open_inter Metric.isOpen_ball).symm
      _ = frontier ((Submission.PBox s c σ ∩ {y : R3 | inner ℝ v c + u + h < inner ℝ v y})
            ∩ Metric.ball z ρ) ∩ Metric.ball z ρ := by rw [hloc]
      _ = frontier (Submission.PBox s c σ ∩ {y : R3 | inner ℝ v c + u + h < inner ℝ v y})
            ∩ Metric.ball z ρ := frontier_inter_open_inter Metric.isOpen_ball
  have hkey : ∀ y : R3, y ∈ Metric.ball z ρ → y ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      (y ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) ↔
       y ∈ {y : R3 | Submission.boxNorm c σ y ≤ s ∧ inner ℝ v c + u + h ≤ inner ℝ v y ∧
          (Submission.boxNorm c σ y = s ∨ inner ℝ v y = inner ℝ v c + u + h)}) := by
    intro y hyb hyc
    have hfr_pt : y ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) ↔
        y ∈ frontier (Submission.PBox s c σ ∩
          {y : R3 | inner ℝ v c + u + h < inner ℝ v y}) := by
      have h := Set.ext_iff.mp hfr y
      exact ⟨fun h1 => (h.mp ⟨h1, hyb⟩).1, fun h2 => (h.mpr ⟨h2, hyb⟩).1⟩
    rw [hfr_pt]
    constructor
    · intro hyf
      exact frontier_PBox_inter_gt_subset hyf
    · intro hyC
      obtain ⟨hboxle, hAge, hdisj⟩ := hyC
      have hdist : dist y z < ρ₀ := lt_of_lt_of_le hyb hρρ₀
      -- the corner point is not interior: it satisfies at least one of the two equalities.
      have hnotint : y ∉ interior (Submission.PBox s c σ ∩
          {y : R3 | inner ℝ v c + u + h < inner ℝ v y}) := by
        intro hint
        have hopen : IsOpen (Submission.PBox s c σ ∩
            {y : R3 | inner ℝ v c + u + h < inner ℝ v y}) :=
          (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter
            (isOpen_lt continuous_const (continuous_const.inner continuous_id))
        have hmem : y ∈ Submission.PBox s c σ ∩
            {y : R3 | inner ℝ v c + u + h < inner ℝ v y} := by
          rwa [hopen.interior_eq] at hint
        obtain ⟨hm1, hm2⟩ := (Set.mem_inter_iff y (Submission.PBox s c σ)
          {y : R3 | inner ℝ v c + u + h < inner ℝ v y}).mp hmem
        have hbL : Submission.boxNorm c σ y < s := (Submission.mem_PBox_iff s c σ y).mp hm1
        rcases hdisj with hb | hi
        · rw [hb] at hbL; exact lt_irrefl s hbL
        · have hm2' : inner ℝ v c + u + h < inner ℝ v y := hm2
          rw [hi] at hm2'
          exact lt_irrefl (inner ℝ v c + u + h) hm2'
      have hclos : y ∈ closure (Submission.PBox s c σ ∩
          {y : R3 | inner ℝ v c + u + h < inner ℝ v y}) := by
        by_cases hdouble : Submission.boxNorm c σ y = s ∧ inner ℝ v y = inner ℝ v c + u + h
        · -- the double-equality case: `y = z`, handled by `hcl`
          obtain ⟨hb, hi⟩ := hdouble
          have hyz : y = z := hsep y hyc hdist hb hi
          rw [hyz]; exact hcl
        · have hbne : Submission.boxNorm c σ y ≠ s ∨
              inner ℝ v y ≠ inner ℝ v c + u + h := by
            rwa [not_and_or] at hdouble
          rcases hdisj with hb | hi
          · -- `boxNorm = s` and `⟪v,·⟫ > a + h`: ray towards the centre
            have hAgt : inner ℝ v c + u + h < inner ℝ v y := by
              rcases hbne with hbn | hin
              · exact absurd hb hbn
              · exact lt_of_le_of_ne hAge (Ne.symm hin)
            have hclbox : y ∈ closure (Submission.PBox s c σ) :=
              mem_closure_PBox_of_boxNorm_le hs c σ (le_of_eq hb)
            exact (isOpen_lt continuous_const (continuous_const.inner continuous_id)).closure_inter
              ⟨hclbox, hAgt⟩
          · -- `⟪v,·⟫ = a + h` and `boxNorm < s`: perturb along `v`
            have hblt : Submission.boxNorm c σ y < s := by
              rcases hbne with hbn | hin
              · exact lt_of_le_of_ne hboxle hbn
              · exact absurd hi hin
            have hyP : y ∈ Submission.PBox s c σ := (Submission.mem_PBox_iff s c σ y).mpr hblt
            have hyUcl : y ∈ closure {y : R3 | inner ℝ v c + u + h < inner ℝ v y} :=
              mem_closure_gt_of_le hv (le_of_eq hi.symm)
            exact (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter_closure ⟨hyP, hyUcl⟩
      rw [frontier, Set.mem_sdiff]
      exact ⟨hclos, hnotint⟩
  refine ⟨ρ, hρpos, ?_⟩
  ext y
  constructor
  · rintro ⟨hyb, hyc, hyf⟩
    exact ⟨hyb, hyc, (hkey y hyb hyc).mp hyf⟩
  · rintro ⟨hyb, hyc, hyC⟩
    exact ⟨hyb, hyc, (hkey y hyb hyc).mpr hyC⟩

end

end Work.Drive.Mono
