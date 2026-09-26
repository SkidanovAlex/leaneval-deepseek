import Mathlib
import Submission.Work.Drive.Final.tls_pieces

/-!
# The frontier of a level of the tilted sweep outside the one-sphere window

`Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam` is Pardon's open box with the closed tilted
slab `{|⟪v,·⟫ - (⟪v,c⟫ + u)| ≤ h}` cut away on the side `{ℓ < lam}`.  This file proves that its
frontier is a finite disjoint union of embedded spheres, under the single hypothesis that the
configuration does **not** lie in the one-sphere window `Work.Drive.Final.OneSphereWindow` (the
regime handled by `Work.Drive.Final.tls_twoDiscs_crux`).

Write, as in `Work.Drive.Final.tls_pieces`,

* `X = tlsUpCap s c σ u h v` (the part of the box strictly beyond the upper slab face),
* `Y = tlsDnCap s c σ u h v` (the part strictly beyond the lower slab face),
* `Z = tlsWallClosed s c σ ℓ lam` (the part weakly above the wall) and
* `Zw = tlsWallOpen s c σ ℓ lam` (the part strictly above the wall).

The removed set is `X ∪ Y ∪ Z` (`tiltedLevelRemoved_eq_three`), the three pieces are convex and
`cl X ∩ cl Y = ∅`.  The window is exactly `X ∩ Zw ≠ ∅ ∧ Y ∩ Zw ≠ ∅` (`oneSphereWindow_iff`), so
outside it one of `X ∩ Zw`, `Y ∩ Zw` is empty.  The content of the proof is then

* **the separation lemma** (`closure_tlsUpCap_disjoint_tlsWallClosed` and its mirror for `Y`): if
  `X ∩ Zw = ∅` and `Z ≠ ∅`, then `cl X ∩ cl Z = ∅`.  The proof is by the maximiser `ŷ` of `ℓ` on
  the compact convex body `cl PBox ∩ {⟪v,·⟫ ≥ ⟪v,c⟫+u+h}`: if `ℓ ŷ > lam` one produces a point of the
  open box with `⟪v,·⟫ > ⟪v,c⟫+u+h` and `ℓ > lam`, i.e. a point of `X ∩ Zw`, using either the
  density of the box in its closure (when `⟪v,ŷ⟫ > ⟪v,c⟫+u+h`) or the segment from a point of `X`
  to `ŷ` (when `⟪v,ŷ⟫ = ⟪v,c⟫+u+h`); and if `ℓ ŷ = lam` then either `ŷ` is a global maximiser of `ℓ`
  on the closed box (when `⟪v,ŷ⟫` is strictly beyond the face), which forces `ℓ = 0` on the
  interior point of `Z` and hence is impossible, or `hseam` applies at `ŷ` and produces a point of
  `X ∩ Zw` as well;
* the point-set case analysis, in which the frontier is a disjoint union of the frontiers of the
  pieces (`frontier_union_of_disjoint_closure`, `sphere_decomposition_of_two/three`), each of which
  is an embedded sphere because it is the frontier of a convex body of `ℝ³` or a union of two
  convex bodies with nonempty intersection (`frontier_tlsUpCap_sphere`,
  `frontier_tlsWallOpen_sphere`, `frontier_union_dnCap_wallClosed_sphere`).
-/

namespace Work.Drive.Final

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set

noncomputable section

variable {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u h lam : ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ}

/-- The **one-sphere window** of a level of the tilted sweep: the box pokes out of both slab faces
(so the slab cuts the box) and, on both sides of the slab, strictly above the wall (so the wall
meets both caps).  This is the regime in which the frontier of the level is a single embedded
sphere (`Work.Drive.Final.tls_twoDiscs_crux`); it is a disjoint union of spheres outside it
(`Work.Drive.Final.tls_rest_crux`). -/
def OneSphereWindow (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Prop :=
  (∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y) ∧
  (∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y) ∧
  (∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y) ∧
  (∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h)

theorem oneSphereWindow_iff (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) :
    OneSphereWindow s c σ u h lam v ℓ ↔
      (tlsUpCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty ∧
      (tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty := by
  constructor
  · rintro ⟨h1, h2, -, -⟩
    rcases h1 with ⟨y, hy, hfy, hly⟩
    rcases h2 with ⟨y', hy', hfy', hly'⟩
    exact ⟨⟨y, ⟨hy, hfy⟩, ⟨hy, hly⟩⟩, ⟨y', ⟨hy', hfy'⟩, ⟨hy', hly'⟩⟩⟩
  · rintro ⟨h1, h2⟩
    rcases h1 with ⟨y, hyU, hyW⟩
    rcases h2 with ⟨y', hyD, hyW'⟩
    exact ⟨⟨y, hyU.1, hyU.2, hyW.2⟩, ⟨y', hyD.1, hyD.2, hyW'.2⟩, ⟨y, hyU.1, hyU.2⟩,
      ⟨y', hyD.1, hyD.2⟩⟩

theorem continuous_inner_fst (v : R3) : Continuous fun y : R3 => inner ℝ v y :=
  (continuous_const : Continuous fun _ : R3 => v).inner continuous_id

/-- A point of the closure of a set, at which a continuous function is strictly above a constant, is
a limit of points of the set which are still above the constant. -/
theorem exists_mem_of_mem_closure_of_lt {X : Set R3} {φ : R3 → ℝ} (hcont : Continuous φ)
    {y : R3} (hy : y ∈ closure X) {a : ℝ} (ha : a < φ y) : ∃ z ∈ X, a < φ z := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ((isOpen_lt continuous_const hcont).mem_nhds ha)
  obtain ⟨z, hzX, hzd⟩ := Metric.mem_closure_iff.mp hy ε hε
  exact ⟨z, hzX, hball (Metric.mem_ball.mpr (by rw [dist_comm]; exact hzd))⟩

/-- The same for two functions. -/
theorem exists_mem_of_mem_closure_of_lt₂ {X : Set R3} {φ ψ : R3 → ℝ}
    (hcontφ : Continuous φ) (hcontψ : Continuous ψ) {y : R3} (hy : y ∈ closure X)
    {a b : ℝ} (ha : a < φ y) (hb : b < ψ y) : ∃ z ∈ X, a < φ z ∧ b < ψ z := by
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.mem_nhds_iff.mp ((isOpen_lt continuous_const hcontφ).mem_nhds ha)
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.mem_nhds_iff.mp ((isOpen_lt continuous_const hcontψ).mem_nhds hb)
  obtain ⟨z, hzX, hzd⟩ := Metric.mem_closure_iff.mp hy (min ε₁ ε₂) (lt_min hε₁ hε₂)
  exact ⟨z, hzX,
    h₁ (Metric.ball_subset_ball (min_le_left _ _) (Metric.mem_ball.mpr (by rw [dist_comm]; exact hzd))),
    h₂ (Metric.ball_subset_ball (min_le_right _ _) (Metric.mem_ball.mpr (by rw [dist_comm]; exact hzd)))⟩

/-- The dual of `exists_mem_of_mem_closure_of_lt₂`: strict upper bounds. -/
theorem exists_mem_of_mem_closure_of_gt₂ {X : Set R3} {φ ψ : R3 → ℝ}
    (hcontφ : Continuous φ) (hcontψ : Continuous ψ) {y : R3} (hy : y ∈ closure X)
    {a b : ℝ} (ha : φ y < a) (hb : b < ψ y) : ∃ z ∈ X, φ z < a ∧ b < ψ z := by
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.mem_nhds_iff.mp ((isOpen_lt hcontφ continuous_const).mem_nhds ha)
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.mem_nhds_iff.mp ((isOpen_lt continuous_const hcontψ).mem_nhds hb)
  obtain ⟨z, hzX, hzd⟩ := Metric.mem_closure_iff.mp hy (min ε₁ ε₂) (lt_min hε₁ hε₂)
  exact ⟨z, hzX,
    h₁ (Metric.ball_subset_ball (min_le_left _ _) (Metric.mem_ball.mpr (by rw [dist_comm]; exact hzd))),
    h₂ (Metric.ball_subset_ball (min_le_right _ _) (Metric.mem_ball.mpr (by rw [dist_comm]; exact hzd)))⟩

/-! ## The separation lemmas -/

/-- **The upper cap is separated from the wall region.**  If the box does not poke strictly above
the wall beyond the upper slab face (`tlsUpCap ∩ tlsWallOpen = ∅`) and the wall region is nonempty,
then the closures of `tlsUpCap` and `tlsWallClosed` are disjoint. -/
theorem closure_tlsUpCap_disjoint_tlsWallClosed (hs : 0 < s) (hh : 0 < h) (hv : v ≠ 0)
    (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hseamP : (∃ y ∈ closure (Submission.PBox s c σ),
        inner ℝ v y = inner ℝ v c + u + h ∧ ℓ y = lam) →
      (∃ z ∈ Submission.PBox s c σ,
        inner ℝ v z = inner ℝ v c + u + h ∧ lam < ℓ z))
    (hZne : (tlsWallClosed s c σ ℓ lam).Nonempty)
    (hXne : (tlsUpCap s c σ u h v).Nonempty)
    (hno : tlsUpCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam = ∅) :
    Disjoint (closure (tlsUpCap s c σ u h v)) (closure (tlsWallClosed s c σ ℓ lam)) := by
  rw [Set.disjoint_left]
  intro y hyX hyZ
  obtain ⟨hKy, hfy⟩ := closure_tlsUpCap_subset hyX
  have hgy : lam ≤ ℓ y := (closure_tlsWallClosed_subset hyZ).2
  set C : Set R3 := tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y} with hC
  have hCcompact : IsCompact C := by
    rw [hC]
    exact (tlsBoxCl_isCompact hs).inter_right
      (isClosed_le continuous_const (continuous_inner_fst v))
  have hCne : C.Nonempty := ⟨y, hKy, hfy⟩
  obtain ⟨ŷ, hŷC, hŷmax⟩ := hCcompact.exists_isMaxOn hCne ℓ.continuous.continuousOn
  have hŷf : inner ℝ v c + u + h ≤ inner ℝ v ŷ := hŷC.2
  have hŷK : ŷ ∈ tlsBoxCl s c σ := hŷC.1
  have hLge : lam ≤ ℓ ŷ := le_trans hgy (hŷmax ⟨hKy, hfy⟩)
  have hno' : ¬ (tlsUpCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty :=
    Set.not_nonempty_iff_eq_empty.mpr hno
  rcases lt_or_eq_of_le hLge with hLgt | hLeq
  · -- `ℓ ŷ > lam`: produce a point of `X ∩ Zw`
    refine hno' ?_
    rcases lt_or_eq_of_le hŷf with hfgt | hfeq
    · by_cases hŷP : ŷ ∈ Submission.PBox s c σ
      · exact ⟨ŷ, ⟨⟨hŷP, hfgt⟩, ⟨hŷP, hLgt⟩⟩⟩
      · obtain ⟨z, hzP, hzf, hzl⟩ :=
          exists_mem_of_mem_closure_of_lt₂ (continuous_inner_fst v) ℓ.continuous hŷK hfgt hLgt
        exact ⟨z, ⟨⟨hzP, hzf⟩, ⟨hzP, hzl⟩⟩⟩
    · -- `⟪v,ŷ⟫ = ⟪v,c⟫+u+h`: use the segment from a point of `X` to `ŷ`
      obtain ⟨ξ, hξX⟩ := hXne
      have hξP : ξ ∈ Submission.PBox s c σ := hξX.1
      have hξf : inner ℝ v c + u + h < inner ℝ v ξ := hξX.2
      set t : ℝ := min (1 / 2) ((ℓ ŷ - lam) / (2 * (|ℓ ξ - ℓ ŷ| + 1))) with ht
      have htpos : 0 < t := by rw [ht]; exact lt_min (by norm_num) (by positivity)
      have htle : t ≤ 1 / 2 := by rw [ht]; exact min_le_left _ _
      have hD : 0 < ℓ ŷ - lam := by linarith
      have htbound : t * |ℓ ξ - ℓ ŷ| < (ℓ ŷ - lam) / 2 := by
        have h1 : t ≤ (ℓ ŷ - lam) / (2 * (|ℓ ξ - ℓ ŷ| + 1)) := by
          rw [ht]; exact min_le_right _ _
        have h3 : (ℓ ŷ - lam) / (2 * (|ℓ ξ - ℓ ŷ| + 1)) * |ℓ ξ - ℓ ŷ| < (ℓ ŷ - lam) / 2 := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (|ℓ ξ - ℓ ŷ| + 1))]
          have h4 : (ℓ ŷ - lam) / 2 * (2 * (|ℓ ξ - ℓ ŷ| + 1)) = (ℓ ŷ - lam) * (|ℓ ξ - ℓ ŷ| + 1) := by
            field_simp
          rw [h4]
          exact mul_lt_mul_of_pos_left (by linarith : |ℓ ξ - ℓ ŷ| < |ℓ ξ - ℓ ŷ| + 1) hD
        nlinarith [mul_le_mul_of_nonneg_right h1 (abs_nonneg (ℓ ξ - ℓ ŷ))]
      have hmemP : (1 - t) • ŷ + t • ξ ∈ Submission.PBox s c σ := by
        have h2 := (Work.Topology.SphereSlicing.convex_PBox s c σ).combo_closure_interior_mem_interior
          (x := ŷ) (y := ξ) (a := 1 - t) (b := t) hŷK
          (by rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]; exact hξP)
          (by linarith) htpos (by ring)
        rwa [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq] at h2
      have hmemf : inner ℝ v c + u + h < inner ℝ v ((1 - t) • ŷ + t • ξ) := by
        rw [inner_add_right, inner_smul_right, inner_smul_right, hfeq]
        nlinarith [hξf, htpos, htle]
      have hmeml : lam < ℓ ((1 - t) • ŷ + t • ξ) := by
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        have h3 : ℓ ξ - ℓ ŷ ≤ |ℓ ξ - ℓ ŷ| := le_abs_self _
        have h4 : -(ℓ ξ - ℓ ŷ) ≤ |ℓ ξ - ℓ ŷ| := neg_le_abs _
        nlinarith [htbound, h3, h4, htpos, htle, hD]
      exact ⟨_, ⟨⟨hmemP, hmemf⟩, ⟨hmemP, hmeml⟩⟩⟩
  · -- `ℓ ŷ = lam`
    rcases lt_or_eq_of_le hŷf with hfgt | hfeq
    · -- `ŷ` is a global maximiser of `ℓ` on the closed box, hence `Z = ∅`
      exfalso
      have hmax : ∀ p ∈ tlsBoxCl s c σ, ℓ p ≤ ℓ ŷ := by
        intro p hp
        by_contra hcon
        push_neg at hcon
        obtain ⟨p', hp'P, hp'l⟩ := exists_mem_of_mem_closure_of_lt ℓ.continuous hp
          (show (ℓ p + ℓ ŷ) / 2 < ℓ p by linarith)
        set t : ℝ := min (1 / 2) ((inner ℝ v ŷ - (inner ℝ v c + u + h)) /
          (2 * (|inner ℝ v p' - inner ℝ v ŷ| + 1))) with ht
        have htpos : 0 < t := by rw [ht]; exact lt_min (by norm_num) (by positivity)
        have htle : t ≤ 1 / 2 := by rw [ht]; exact min_le_left _ _
        have hD : 0 < inner ℝ v ŷ - (inner ℝ v c + u + h) := by linarith
        have htbound : t * |inner ℝ v p' - inner ℝ v ŷ| <
            (inner ℝ v ŷ - (inner ℝ v c + u + h)) / 2 := by
          have h1 : t ≤ (inner ℝ v ŷ - (inner ℝ v c + u + h)) /
              (2 * (|inner ℝ v p' - inner ℝ v ŷ| + 1)) := by
            rw [ht]; exact min_le_right _ _
          have h3 : (inner ℝ v ŷ - (inner ℝ v c + u + h)) /
              (2 * (|inner ℝ v p' - inner ℝ v ŷ| + 1)) * |inner ℝ v p' - inner ℝ v ŷ| <
              (inner ℝ v ŷ - (inner ℝ v c + u + h)) / 2 := by
            rw [div_mul_eq_mul_div,
              div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (|inner ℝ v p' - inner ℝ v ŷ| + 1))]
            have h4 : (inner ℝ v ŷ - (inner ℝ v c + u + h)) / 2 *
                (2 * (|inner ℝ v p' - inner ℝ v ŷ| + 1)) =
                (inner ℝ v ŷ - (inner ℝ v c + u + h)) *
                  (|inner ℝ v p' - inner ℝ v ŷ| + 1) := by
              field_simp
            rw [h4]
            exact mul_lt_mul_of_pos_left
              (by linarith : |inner ℝ v p' - inner ℝ v ŷ| < |inner ℝ v p' - inner ℝ v ŷ| + 1) hD
          nlinarith [mul_le_mul_of_nonneg_right h1 (abs_nonneg (inner ℝ v p' - inner ℝ v ŷ))]
        have hmemP : (1 - t) • ŷ + t • p' ∈ Submission.PBox s c σ := by
          have h2 := (Work.Topology.SphereSlicing.convex_PBox s c σ).combo_closure_interior_mem_interior
            (x := ŷ) (y := p') (a := 1 - t) (b := t) hŷK
            (by rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]; exact hp'P)
            (by linarith) htpos (by ring)
          rwa [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq] at h2
        have hmemf : inner ℝ v c + u + h < inner ℝ v ((1 - t) • ŷ + t • p') := by
          rw [inner_add_right, inner_smul_right, inner_smul_right]
          have h3 : inner ℝ v p' - inner ℝ v ŷ ≤ |inner ℝ v p' - inner ℝ v ŷ| := le_abs_self _
          have h4 : -(inner ℝ v p' - inner ℝ v ŷ) ≤ |inner ℝ v p' - inner ℝ v ŷ| := neg_le_abs _
          nlinarith [htbound, h3, h4, htpos, htle, hD]
        have hle := hŷmax ⟨subset_closure hmemP, le_of_lt hmemf⟩
        have hle' : ℓ ((1 - t) • ŷ + t • p') ≤ ℓ ŷ := hle
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hle'
        nlinarith [htpos, hle', hp'l]
      obtain ⟨z, hzP, hzl⟩ := hZne
      have h1 : ℓ z ≤ ℓ ŷ := hmax z (subset_closure hzP)
      have h2 : ℓ ŷ ≤ ℓ z := hLeq ▸ hzl
      have hzeq : ℓ z = ℓ ŷ := le_antisymm h1 h2
      have hzero : ∀ w : R3, ℓ w = 0 := by
        intro w
        obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
          ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hzP)
        set t : ℝ := min (δ / (2 * (‖w‖ + 1))) (1 / 2) with ht
        have htpos : 0 < t := by rw [ht]; exact lt_min (by positivity) (by norm_num)
        have htd : t * ‖w‖ < δ := by
          have h1 : t ≤ δ / (2 * (‖w‖ + 1)) := by rw [ht]; exact min_le_left _ _
          have h3 : δ / (2 * (‖w‖ + 1)) * ‖w‖ < δ := by
            have hden : 0 < 2 * (‖w‖ + 1) := by positivity
            rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
            nlinarith [norm_nonneg w, hδ]
          nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg w)]
        have hmem1 : z + t • w ∈ Submission.PBox s c σ := hball (by
          rw [Metric.mem_ball, dist_eq_norm]
          have hsub : z + t • w - z = t • w := by module
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
          exact htd)
        have hmem2 : z - t • w ∈ Submission.PBox s c σ := hball (by
          rw [Metric.mem_ball, dist_eq_norm]
          have hsub : z - t • w - z = -(t • w) := by module
          rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
          exact htd)
        have hle1 : ℓ (z + t • w) ≤ ℓ ŷ := hmax _ (subset_closure hmem1)
        have hle2 : ℓ (z - t • w) ≤ ℓ ŷ := hmax _ (subset_closure hmem2)
        rw [map_add, map_smul, smul_eq_mul] at hle1
        rw [map_sub, map_smul, smul_eq_mul] at hle2
        have htw : t * ℓ w = 0 := by linarith [hle1, hle2, hzeq]
        rcases mul_eq_zero.mp htw with hw0 | hw0
        · exact absurd hw0 (ne_of_gt htpos)
        · exact hw0
      exact hℓne (ContinuousLinearMap.ext hzero)
    · -- `hseam` at `ŷ` produces a point of `X ∩ Zw`
      obtain ⟨z, hzP, hzf, hzl⟩ := hseamP ⟨ŷ, hŷK, hfeq.symm, hLeq.symm⟩
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
        ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hzP)
      set t : ℝ := δ / (2 * (‖v‖ + 1)) with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have hd : t * ‖v‖ < δ := by
        have h1 : t ≤ δ / (2 * (‖v‖ + 1)) := le_of_eq ht
        have h2 : δ / (2 * (‖v‖ + 1)) * ‖v‖ < δ := by
          have hden : 0 < 2 * (‖v‖ + 1) := by positivity
          rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
          nlinarith [norm_nonneg v, hδ]
        nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg v)]
      have hmemP : z + t • v ∈ Submission.PBox s c σ := hball (by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : z + t • v - z = t • v := by module
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        exact hd)
      refine hno' ⟨z + t • v, ⟨⟨hmemP, ?_⟩, ⟨hmemP, ?_⟩⟩⟩
      · show inner ℝ v c + u + h < inner ℝ v (z + t • v)
        rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
        have hvv : 0 < ‖v‖ ^ 2 := by positivity
        nlinarith [mul_pos htpos hvv]
      · show lam < ℓ (z + t • v)
        rw [map_add, map_smul, smul_eq_mul, hℓv, mul_zero, add_zero]
        exact hzl


/-! ## The mirror separation lemma for the lower cap -/

/-- **The lower cap is separated from the wall region** (the mirror of
`closure_tlsUpCap_disjoint_tlsWallClosed`). -/
theorem closure_tlsDnCap_disjoint_tlsWallClosed (hs : 0 < s) (hh : 0 < h) (hv : v ≠ 0)
    (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hseamM : (∃ y ∈ closure (Submission.PBox s c σ),
        inner ℝ v y = inner ℝ v c + u - h ∧ ℓ y = lam) →
      (∃ z ∈ Submission.PBox s c σ,
        inner ℝ v z = inner ℝ v c + u - h ∧ lam < ℓ z))
    (hZne : (tlsWallClosed s c σ ℓ lam).Nonempty)
    (hYne : (tlsDnCap s c σ u h v).Nonempty)
    (hno : tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam = ∅) :
    Disjoint (closure (tlsDnCap s c σ u h v)) (closure (tlsWallClosed s c σ ℓ lam)) := by
  rw [Set.disjoint_left]
  intro y hyY hyZ
  obtain ⟨hKy, hfy⟩ := closure_tlsDnCap_subset hyY
  have hgy : lam ≤ ℓ y := (closure_tlsWallClosed_subset hyZ).2
  set C : Set R3 := tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h} with hC
  have hCcompact : IsCompact C := by
    rw [hC]
    exact (tlsBoxCl_isCompact hs).inter_right
      (isClosed_le (continuous_inner_fst v) continuous_const)
  have hCne : C.Nonempty := ⟨y, hKy, hfy⟩
  obtain ⟨ŷ, hŷC, hŷmax⟩ := hCcompact.exists_isMaxOn hCne ℓ.continuous.continuousOn
  have hŷf : inner ℝ v ŷ ≤ inner ℝ v c + u - h := hŷC.2
  have hŷK : ŷ ∈ tlsBoxCl s c σ := hŷC.1
  have hLge : lam ≤ ℓ ŷ := le_trans hgy (hŷmax ⟨hKy, hfy⟩)
  have hno' : ¬ (tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty :=
    Set.not_nonempty_iff_eq_empty.mpr hno
  rcases lt_or_eq_of_le hLge with hLgt | hLeq
  · -- `ℓ ŷ > lam`: produce a point of `Y ∩ Zw`
    refine hno' ?_
    rcases lt_or_eq_of_le hŷf with hflt | hfeq
    · by_cases hŷP : ŷ ∈ Submission.PBox s c σ
      · exact ⟨ŷ, ⟨⟨hŷP, hflt⟩, ⟨hŷP, hLgt⟩⟩⟩
      · obtain ⟨z, hzP, hzf, hzl⟩ :=
          exists_mem_of_mem_closure_of_gt₂ (continuous_inner_fst v) ℓ.continuous hŷK hflt hLgt
        exact ⟨z, ⟨⟨hzP, hzf⟩, ⟨hzP, hzl⟩⟩⟩
    · -- `⟪v,ŷ⟫ = ⟪v,c⟫+u-h`: use the segment from a point of `Y` to `ŷ`
      obtain ⟨ξ, hξY⟩ := hYne
      have hξP : ξ ∈ Submission.PBox s c σ := hξY.1
      have hξf : inner ℝ v ξ < inner ℝ v c + u - h := hξY.2
      set t : ℝ := min (1 / 2) ((ℓ ŷ - lam) / (2 * (|ℓ ξ - ℓ ŷ| + 1))) with ht
      have htpos : 0 < t := by rw [ht]; exact lt_min (by norm_num) (by positivity)
      have htle : t ≤ 1 / 2 := by rw [ht]; exact min_le_left _ _
      have hD : 0 < ℓ ŷ - lam := by linarith
      have htbound : t * |ℓ ξ - ℓ ŷ| < (ℓ ŷ - lam) / 2 := by
        have h1 : t ≤ (ℓ ŷ - lam) / (2 * (|ℓ ξ - ℓ ŷ| + 1)) := by
          rw [ht]; exact min_le_right _ _
        have h3 : (ℓ ŷ - lam) / (2 * (|ℓ ξ - ℓ ŷ| + 1)) * |ℓ ξ - ℓ ŷ| < (ℓ ŷ - lam) / 2 := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (|ℓ ξ - ℓ ŷ| + 1))]
          have h4 : (ℓ ŷ - lam) / 2 * (2 * (|ℓ ξ - ℓ ŷ| + 1)) = (ℓ ŷ - lam) * (|ℓ ξ - ℓ ŷ| + 1) := by
            field_simp
          rw [h4]
          exact mul_lt_mul_of_pos_left (by linarith : |ℓ ξ - ℓ ŷ| < |ℓ ξ - ℓ ŷ| + 1) hD
        nlinarith [mul_le_mul_of_nonneg_right h1 (abs_nonneg (ℓ ξ - ℓ ŷ))]
      have hmemP : (1 - t) • ŷ + t • ξ ∈ Submission.PBox s c σ := by
        have h2 := (Work.Topology.SphereSlicing.convex_PBox s c σ).combo_closure_interior_mem_interior
          (x := ŷ) (y := ξ) (a := 1 - t) (b := t) hŷK
          (by rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]; exact hξP)
          (by linarith) htpos (by ring)
        rwa [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq] at h2
      have hmemf : inner ℝ v ((1 - t) • ŷ + t • ξ) < inner ℝ v c + u - h := by
        rw [inner_add_right, inner_smul_right, inner_smul_right, hfeq]
        nlinarith [hξf, htpos, htle]
      have hmeml : lam < ℓ ((1 - t) • ŷ + t • ξ) := by
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        have h3 : ℓ ξ - ℓ ŷ ≤ |ℓ ξ - ℓ ŷ| := le_abs_self _
        have h4 : -(ℓ ξ - ℓ ŷ) ≤ |ℓ ξ - ℓ ŷ| := neg_le_abs _
        nlinarith [htbound, h3, h4, htpos, htle, hD]
      exact ⟨_, ⟨⟨hmemP, hmemf⟩, ⟨hmemP, hmeml⟩⟩⟩
  · -- `ℓ ŷ = lam`
    rcases lt_or_eq_of_le hŷf with hflt | hfeq
    · -- `ŷ` is a global maximiser of `ℓ` on the closed box
      exfalso
      have hmax : ∀ p ∈ tlsBoxCl s c σ, ℓ p ≤ ℓ ŷ := by
        intro p hp
        by_contra hcon
        push_neg at hcon
        obtain ⟨p', hp'P, hp'l⟩ := exists_mem_of_mem_closure_of_lt ℓ.continuous hp
          (show (ℓ p + ℓ ŷ) / 2 < ℓ p by linarith)
        have hD : 0 < inner ℝ v c + u - h - inner ℝ v ŷ := by linarith
        set t : ℝ := min (1 / 2) ((inner ℝ v c + u - h - inner ℝ v ŷ) /
          (2 * (|inner ℝ v p' - inner ℝ v ŷ| + 1))) with ht
        have htpos : 0 < t := by rw [ht]; exact lt_min (by norm_num) (by positivity)
        have htle : t ≤ 1 / 2 := by rw [ht]; exact min_le_left _ _
        have htbound : t * |inner ℝ v p' - inner ℝ v ŷ| <
            (inner ℝ v c + u - h - inner ℝ v ŷ) / 2 := by
          have h1 : t ≤ (inner ℝ v c + u - h - inner ℝ v ŷ) /
              (2 * (|inner ℝ v p' - inner ℝ v ŷ| + 1)) := by
            rw [ht]; exact min_le_right _ _
          have h3 : (inner ℝ v c + u - h - inner ℝ v ŷ) /
              (2 * (|inner ℝ v p' - inner ℝ v ŷ| + 1)) * |inner ℝ v p' - inner ℝ v ŷ| <
              (inner ℝ v c + u - h - inner ℝ v ŷ) / 2 := by
            rw [div_mul_eq_mul_div,
              div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (|inner ℝ v p' - inner ℝ v ŷ| + 1))]
            have h4 : (inner ℝ v c + u - h - inner ℝ v ŷ) / 2 *
                (2 * (|inner ℝ v p' - inner ℝ v ŷ| + 1)) =
                (inner ℝ v c + u - h - inner ℝ v ŷ) *
                  (|inner ℝ v p' - inner ℝ v ŷ| + 1) := by
              field_simp
            rw [h4]
            exact mul_lt_mul_of_pos_left
              (by linarith : |inner ℝ v p' - inner ℝ v ŷ| < |inner ℝ v p' - inner ℝ v ŷ| + 1) hD
          nlinarith [mul_le_mul_of_nonneg_right h1 (abs_nonneg (inner ℝ v p' - inner ℝ v ŷ))]
        have hmemP : (1 - t) • ŷ + t • p' ∈ Submission.PBox s c σ := by
          have h2 := (Work.Topology.SphereSlicing.convex_PBox s c σ).combo_closure_interior_mem_interior
            (x := ŷ) (y := p') (a := 1 - t) (b := t) hŷK
            (by rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]; exact hp'P)
            (by linarith) htpos (by ring)
          rwa [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq] at h2
        have hmemf : inner ℝ v ((1 - t) • ŷ + t • p') < inner ℝ v c + u - h := by
          rw [inner_add_right, inner_smul_right, inner_smul_right]
          have h3 : inner ℝ v p' - inner ℝ v ŷ ≤ |inner ℝ v p' - inner ℝ v ŷ| := le_abs_self _
          have h4 : -(inner ℝ v p' - inner ℝ v ŷ) ≤ |inner ℝ v p' - inner ℝ v ŷ| := neg_le_abs _
          nlinarith [htbound, h3, h4, htpos, htle, hD]
        have hle := hŷmax ⟨subset_closure hmemP, le_of_lt hmemf⟩
        have hle' : ℓ ((1 - t) • ŷ + t • p') ≤ ℓ ŷ := hle
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hle'
        nlinarith [htpos, hle', hp'l]
      obtain ⟨z, hzP, hzl⟩ := hZne
      have h1 : ℓ z ≤ ℓ ŷ := hmax z (subset_closure hzP)
      have h2 : ℓ ŷ ≤ ℓ z := hLeq ▸ hzl
      have hzeq : ℓ z = ℓ ŷ := le_antisymm h1 h2
      have hzero : ∀ w : R3, ℓ w = 0 := by
        intro w
        obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
          ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hzP)
        set t : ℝ := min (δ / (2 * (‖w‖ + 1))) (1 / 2) with ht
        have htpos : 0 < t := by rw [ht]; exact lt_min (by positivity) (by norm_num)
        have htd : t * ‖w‖ < δ := by
          have h1 : t ≤ δ / (2 * (‖w‖ + 1)) := by rw [ht]; exact min_le_left _ _
          have h3 : δ / (2 * (‖w‖ + 1)) * ‖w‖ < δ := by
            have hden : 0 < 2 * (‖w‖ + 1) := by positivity
            rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
            nlinarith [norm_nonneg w, hδ]
          nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg w)]
        have hmem1 : z + t • w ∈ Submission.PBox s c σ := hball (by
          rw [Metric.mem_ball, dist_eq_norm]
          have hsub : z + t • w - z = t • w := by module
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
          exact htd)
        have hmem2 : z - t • w ∈ Submission.PBox s c σ := hball (by
          rw [Metric.mem_ball, dist_eq_norm]
          have hsub : z - t • w - z = -(t • w) := by module
          rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
          exact htd)
        have hle1 : ℓ (z + t • w) ≤ ℓ ŷ := hmax _ (subset_closure hmem1)
        have hle2 : ℓ (z - t • w) ≤ ℓ ŷ := hmax _ (subset_closure hmem2)
        rw [map_add, map_smul, smul_eq_mul] at hle1
        rw [map_sub, map_smul, smul_eq_mul] at hle2
        have htw : t * ℓ w = 0 := by linarith [hle1, hle2, hzeq]
        rcases mul_eq_zero.mp htw with hw0 | hw0
        · exact absurd hw0 (ne_of_gt htpos)
        · exact hw0
      exact hℓne (ContinuousLinearMap.ext hzero)
    · -- `hseam` at `ŷ` produces a point of `Y ∩ Zw`
      obtain ⟨z, hzP, hzf, hzl⟩ := hseamM ⟨ŷ, hŷK, hfeq, hLeq.symm⟩
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
        ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hzP)
      set t : ℝ := δ / (2 * (‖v‖ + 1)) with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have hd : t * ‖v‖ < δ := by
        have h1 : t ≤ δ / (2 * (‖v‖ + 1)) := le_of_eq ht
        have h2 : δ / (2 * (‖v‖ + 1)) * ‖v‖ < δ := by
          have hden : 0 < 2 * (‖v‖ + 1) := by positivity
          rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
          nlinarith [norm_nonneg v, hδ]
        nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg v)]
      have hmemP : z - t • v ∈ Submission.PBox s c σ := hball (by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : z - t • v - z = -(t • v) := by module
        rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        exact hd)
      refine hno' ⟨z - t • v, ⟨⟨hmemP, ?_⟩, ⟨hmemP, ?_⟩⟩⟩
      · show inner ℝ v (z - t • v) < inner ℝ v c + u - h
        rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
        have hvv : 0 < ‖v‖ ^ 2 := by positivity
        nlinarith [mul_pos htpos hvv]
      · show lam < ℓ (z - t • v)
        rw [map_sub, map_smul, smul_eq_mul, hℓv, mul_zero, sub_zero]
        exact hzl

/-! ## The frontier of the removed set -/

/-- The two caps have disjoint closures. -/
theorem closure_tlsUpCap_disjoint_tlsDnCap (hh : 0 < h) :
    Disjoint (closure (tlsUpCap s c σ u h v)) (closure (tlsDnCap s c σ u h v)) := by
  rw [Set.disjoint_left]
  intro y hyX hyY
  have h1 : inner ℝ v c + u + h ≤ inner ℝ v y := (closure_tlsUpCap_subset hyX).2
  have h2 : inner ℝ v y ≤ inner ℝ v c + u - h := (closure_tlsDnCap_subset hyY).2
  linarith


/-! ## The main theorem -/

theorem tls_rest_crux (s : ℝ) (hs : 0 < s)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ)
    (v : LeanEval.KnotTheory.PardonDistortion.R3)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ)
    (hv : v ≠ 0) (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hedge : ∀ (i : Fin 3) (ε : Fin 3 → Bool),
      lam = ℓ (WithLp.toLp 2 (fun k : Fin 3 => c k +
        (if k = σ i then (0 : ℝ) else
          (if ε (σ.symm k) then 1 else -1) * Submission.boxSide (σ.symm k) * s))) →
      ℓ (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0)
    (hvertex : ∀ ε : Fin 3 → Bool,
      lam ≠ ℓ (WithLp.toLp 2 (fun j : Fin 3 => c j +
        (if ε (σ.symm j) then 1 else -1) * Submission.boxSide (σ.symm j) * s)))
    (hseam : ((∃ y ∈ closure (Submission.PBox s c σ),
          inner ℝ v y = inner ℝ v c + u + h ∧ ℓ y = lam) →
        (∃ z ∈ Submission.PBox s c σ,
          inner ℝ v z = inner ℝ v c + u + h ∧ lam < ℓ z)) ∧
      ((∃ y ∈ closure (Submission.PBox s c σ),
          inner ℝ v y = inner ℝ v c + u - h ∧ ℓ y = lam) →
        (∃ z ∈ Submission.PBox s c σ,
          inner ℝ v z = inner ℝ v c + u - h ∧ lam < ℓ z)) ∧
      ((∃ y ∈ closure (Submission.PBox s c σ),
          |inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y = lam) →
        (∃ z ∈ Submission.PBox s c σ,
          |inner ℝ v z - (inner ℝ v c + u)| ≤ h ∧ lam < ℓ z)))
    (hnotwin : ¬ Work.Drive.Final.OneSphereWindow s c σ u h lam v ℓ) :
    ∃ (n : ℕ) (S : Fin n → Set LeanEval.KnotTheory.PardonDistortion.R3),
      (∀ i, Work.InnermostDisk.IsEmbeddedSphere (S i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (S i) (S j)) ∧
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) = ⋃ i, S i := by
  classical
  set X : Set R3 := tlsUpCap s c σ u h v with hXdef
  set Y : Set R3 := tlsDnCap s c σ u h v with hYdef
  set Z : Set R3 := tlsWallClosed s c σ ℓ lam with hZdef
  set Zw : Set R3 := tlsWallOpen s c σ ℓ lam with hZwdef
  have hR : Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam = X ∪ Y ∪ Z :=
    tiltedLevelRemoved_eq_three s u h lam c v σ ℓ
  have hXYc : Disjoint (closure X) (closure Y) := closure_tlsUpCap_disjoint_tlsDnCap hh
  have hXYf : Disjoint (frontier X) (frontier Y) :=
    hXYc.mono frontier_subset_closure frontier_subset_closure
  have hXp : frontier X = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere (frontier X) := by
    by_cases hne : X.Nonempty
    · exact Or.inr (frontier_tlsUpCap_sphere hs hv hne)
    · exact Or.inl (by rw [Set.not_nonempty_iff_eq_empty.mp hne, frontier_empty])
  have hYp : frontier Y = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere (frontier Y) := by
    by_cases hne : Y.Nonempty
    · exact Or.inr (frontier_tlsDnCap_sphere hs hv hne)
    · exact Or.inl (by rw [Set.not_nonempty_iff_eq_empty.mp hne, frontier_empty])
  by_cases hZne : Z.Nonempty
  · have hZp : frontier Z = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere (frontier Z) := by
      by_cases hne : Z.Nonempty
      · refine Or.inr ?_
        rw [frontier_tlsWallClosed_eq hℓne]
        exact frontier_tlsWallOpen_sphere hs hℓne (tlsWallOpen_nonempty_of_closed hℓne hne)
      · exact Or.inl (by rw [Set.not_nonempty_iff_eq_empty.mp hne, frontier_empty])
    by_cases hXZ : (X ∩ Zw).Nonempty
    · by_cases hYZ : (Y ∩ Zw).Nonempty
      · exact absurd ((oneSphereWindow_iff s c σ u h lam v ℓ).mpr ⟨hXZ, hYZ⟩) hnotwin
      · -- `Y ∩ Zw = ∅`: the frontier is `∂Y ⊔ ∂(X ∪ Z)`, a disjoint union of two spheres
        have hnoY : tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hYZ
        have hYZc : Disjoint (closure Y) (closure Z) := by
          by_cases hYne : Y.Nonempty
          · exact closure_tlsDnCap_disjoint_tlsWallClosed hs hh hv hℓv hℓne hseam.2.1 hZne hYne hnoY
          · rw [Set.not_nonempty_iff_eq_empty.mp hYne, closure_empty]
            exact disjoint_bot_left
        have hdisj : Disjoint (closure (X ∪ Z)) (closure Y) := by
          rw [closure_union, Set.disjoint_iff_inter_eq_empty, Set.union_inter_distrib_right,
            hXYc.inter_eq, hYZc.symm.inter_eq, Set.union_empty]
        have hfr : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) =
            frontier Y ∪ frontier (X ∪ Z) := by
          have h1 : X ∪ Y ∪ Z = (X ∪ Z) ∪ Y := by
            ext x; simp only [Set.mem_union]; tauto
          rw [hR, h1, frontier_union_of_disjoint_closure hdisj, Set.union_comm]
        have hsphere : Work.InnermostDisk.IsEmbeddedSphere (frontier (X ∪ Z)) :=
          frontier_union_upCap_wallClosed_sphere hs hv hℓne hℓv hXZ
        obtain ⟨n, S, hS, hdisjS, hunion⟩ :=
          sphere_decomposition_of_two (frontier Y) (frontier (X ∪ Z)) hYp (Or.inr hsphere)
            (hdisj.symm.mono frontier_subset_closure frontier_subset_closure)
        exact ⟨n, S, hS, hdisjS, by rw [hfr, hunion]⟩
    · -- `X ∩ Zw = ∅`
      have hnoX : tlsUpCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hXZ
      have hXZc : Disjoint (closure X) (closure Z) := by
        by_cases hXne : X.Nonempty
        · exact closure_tlsUpCap_disjoint_tlsWallClosed hs hh hv hℓv hℓne hseam.1 hZne hXne hnoX
        · rw [Set.not_nonempty_iff_eq_empty.mp hXne, closure_empty]
          exact disjoint_bot_left
      by_cases hYZ : (Y ∩ Zw).Nonempty
      · -- `X ∩ Zw = ∅`, `Y ∩ Zw ≠ ∅`: the frontier is `∂X ⊔ ∂(Y ∪ Z)`
        have hdisj : Disjoint (closure X) (closure (Y ∪ Z)) := by
          rw [closure_union, Set.disjoint_iff_inter_eq_empty, Set.inter_union_distrib_left,
            hXYc.inter_eq, hXZc.inter_eq, Set.empty_union]
        have hfr : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) =
            frontier X ∪ frontier (Y ∪ Z) := by
          have h1 : X ∪ Y ∪ Z = X ∪ (Y ∪ Z) := by
            ext x; simp only [Set.mem_union]; tauto
          rw [hR, h1, frontier_union_of_disjoint_closure hdisj]
        have hsphere : Work.InnermostDisk.IsEmbeddedSphere (frontier (Y ∪ Z)) :=
          frontier_union_dnCap_wallClosed_sphere hs hv hℓne hℓv hYZ
        obtain ⟨n, S, hS, hdisjS, hunion⟩ :=
          sphere_decomposition_of_two (frontier X) (frontier (Y ∪ Z)) hXp (Or.inr hsphere)
            (hdisj.mono frontier_subset_closure frontier_subset_closure)
        exact ⟨n, S, hS, hdisjS, by rw [hfr, hunion]⟩
      · -- `X ∩ Zw = Y ∩ Zw = ∅`: the frontier is `∂X ⊔ ∂Y ⊔ ∂Z`
        have hnoY : tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hYZ
        have hYZc : Disjoint (closure Y) (closure Z) := by
          by_cases hYne : Y.Nonempty
          · exact closure_tlsDnCap_disjoint_tlsWallClosed hs hh hv hℓv hℓne hseam.2.1 hZne hYne hnoY
          · rw [Set.not_nonempty_iff_eq_empty.mp hYne, closure_empty]
            exact disjoint_bot_left
        obtain ⟨n, S, hS, hdisjS, hunion⟩ :=
          sphere_decomposition_of_three (frontier X) (frontier Y) (frontier Z) hXp hYp hZp
            hXYf (hXZc.mono frontier_subset_closure frontier_subset_closure)
            (hYZc.mono frontier_subset_closure frontier_subset_closure)
        refine ⟨n, S, hS, hdisjS, ?_⟩
        rw [hR, frontier_union_three_of_disjoint_closure hXYc hXZc hYZc, hunion]
  · -- `Z = ∅`: the frontier is `∂X ⊔ ∂Y`
    have hfr : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) =
        frontier X ∪ frontier Y := by
      rw [hR, Set.not_nonempty_iff_eq_empty.mp hZne, Set.union_empty,
        frontier_union_of_disjoint_closure hXYc]
    obtain ⟨n, S, hS, hdisjS, hunion⟩ :=
      sphere_decomposition_of_two (frontier X) (frontier Y) hXp hYp hXYf
    exact ⟨n, S, hS, hdisjS, by rw [hfr, hunion]⟩

end

end Work.Drive.Final
