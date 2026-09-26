import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.isEmbeddedSphere_frontier_union_convex
import Submission.Work.Drive.Mono.isEmbeddedSphere_frontier_slabCaps

/-!
# The three pieces of the frontier of a level of the tilted sweep

`Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam` is Pardon's open box with the closed tilted
slab `{|⟪v,·⟫ - (⟪v,c⟫ + u)| ≤ h}` cut away on the side `{ℓ < lam}`.  This file writes the removed
set as the union of

* the **upper cap** `tlsUpCap = PBox ∩ {⟪v,·⟫ > ⟪v,c⟫ + u + h}`,
* the **lower cap** `tlsDnCap = PBox ∩ {⟪v,·⟫ < ⟪v,c⟫ + u - h}`,
* the **wall region** `tlsWallClosed = PBox ∩ {lam ≤ ℓ}`,

(`tiltedLevelRemoved_eq_three`) and collects the point-set facts about those three open convex
pieces which the decomposition of the frontier uses: their closures, their interiors, and the
embeddness of their frontiers (each is the frontier of a convex body of `ℝ³`, and the frontier of a
union of two of them — with disjoint closures, or with nonempty intersection — is an embedded
sphere as well).

The frontier of the removed set is *not* the union of the frontiers of the three pieces in general
(the wall disc outside the slab belongs to the removed set, so it is not on the frontier); the
separation lemmas which make the union disjoint are in `Submission.Work.Drive.Final.tls_rest_crux`,
where the decomposition is assembled.
-/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set

noncomputable section

/-! ## The three pieces -/

/-- The upper cap of Pardon's box cut by the tilted slab. -/
def tlsUpCap (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h : ℝ) (v : R3) : Set R3 :=
  Submission.PBox s c σ ∩ {y : R3 | inner ℝ v c + u + h < inner ℝ v y}

/-- The lower cap of Pardon's box cut by the tilted slab. -/
def tlsDnCap (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h : ℝ) (v : R3) : Set R3 :=
  Submission.PBox s c σ ∩ {y : R3 | inner ℝ v y < inner ℝ v c + u - h}

/-- The part of the box strictly above the wall. -/
def tlsWallOpen (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) :
    Set R3 :=
  Submission.PBox s c σ ∩ {y : R3 | lam < ℓ y}

/-- The closure of the wall region: the part of the box weakly above the wall. -/
def tlsWallClosed (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) :
    Set R3 :=
  Submission.PBox s c σ ∩ {y : R3 | lam ≤ ℓ y}

/-- The closure of Pardon's box. -/
def tlsBoxCl (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  closure (Submission.PBox s c σ)

/-! ## Elementary convexity, openness and boundedness -/

variable {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u h lam : ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ}

theorem tlsUpCap_subset_PBox : tlsUpCap s c σ u h v ⊆ Submission.PBox s c σ :=
  Set.inter_subset_left

theorem tlsDnCap_subset_PBox : tlsDnCap s c σ u h v ⊆ Submission.PBox s c σ :=
  Set.inter_subset_left

theorem tlsWallOpen_subset_PBox : tlsWallOpen s c σ ℓ lam ⊆ Submission.PBox s c σ :=
  Set.inter_subset_left

theorem tlsWallClosed_subset_PBox : tlsWallClosed s c σ ℓ lam ⊆ Submission.PBox s c σ :=
  Set.inter_subset_left

theorem tlsUpCap_isOpen :
    IsOpen (tlsUpCap s c σ u h v) :=
  (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter
    (isOpen_lt continuous_const
      ((continuous_const : Continuous fun _ : R3 => v).inner continuous_id))

theorem tlsDnCap_isOpen :
    IsOpen (tlsDnCap s c σ u h v) :=
  (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter
    (isOpen_lt ((continuous_const : Continuous fun _ : R3 => v).inner continuous_id)
      continuous_const)

theorem tlsWallOpen_isOpen : IsOpen (tlsWallOpen s c σ ℓ lam) :=
  (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter
    (isOpen_lt continuous_const ℓ.continuous)

theorem convex_setOf_clm_lt (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Convex ℝ {y : R3 | ℓ y < lam} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hlin : ℓ (a • x + b • y) = a * ℓ x + b * ℓ y := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hlin]
  calc a * ℓ x + b * ℓ y < a * lam + b * lam :=
        add_lt_add (mul_lt_mul_of_pos_left hx ha) (mul_lt_mul_of_pos_left hy hb)
    _ = lam := by rw [← add_mul, hab, one_mul]

theorem convex_setOf_clm_gt (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Convex ℝ {y : R3 | lam < ℓ y} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hlin : ℓ (a • x + b • y) = a * ℓ x + b * ℓ y := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hlin]
  calc lam = a * lam + b * lam := by rw [← add_mul, hab, one_mul]
    _ < a * ℓ x + b * ℓ y :=
        add_lt_add (mul_lt_mul_of_pos_left hx ha) (mul_lt_mul_of_pos_left hy hb)

theorem convex_setOf_clm_le (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Convex ℝ {y : R3 | lam ≤ ℓ y} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hlin : ℓ (a • x + b • y) = a * ℓ x + b * ℓ y := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hlin]
  calc lam = a * lam + b * lam := by rw [← add_mul, hab, one_mul]
    _ ≤ a * ℓ x + b * ℓ y :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha.le) (mul_le_mul_of_nonneg_left hy hb.le)

theorem convex_setOf_gt_inner (v : R3) (A : ℝ) : Convex ℝ {y : R3 | A < inner ℝ v y} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hlin : inner ℝ v (a • x + b • y) = a * inner ℝ v x + b * inner ℝ v y := by
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  rw [hlin]
  calc A = a * A + b * A := by rw [← add_mul, hab, one_mul]
    _ < a * inner ℝ v x + b * inner ℝ v y :=
        add_lt_add (mul_lt_mul_of_pos_left hx ha) (mul_lt_mul_of_pos_left hy hb)

theorem convex_setOf_inner_le (v : R3) (A : ℝ) : Convex ℝ {y : R3 | inner ℝ v y ≤ A} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hlin : inner ℝ v (a • x + b • y) = a * inner ℝ v x + b * inner ℝ v y := by
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  rw [hlin]
  calc a * inner ℝ v x + b * inner ℝ v y ≤ a * A + b * A :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha.le) (mul_le_mul_of_nonneg_left hy hb.le)
    _ = A := by rw [← add_mul, hab, one_mul]

theorem convex_setOf_lt_inner (v : R3) (A : ℝ) : Convex ℝ {y : R3 | inner ℝ v y < A} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hlin : inner ℝ v (a • x + b • y) = a * inner ℝ v x + b * inner ℝ v y := by
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  rw [hlin]
  calc a * inner ℝ v x + b * inner ℝ v y < a * A + b * A :=
        add_lt_add (mul_lt_mul_of_pos_left hx ha) (mul_lt_mul_of_pos_left hy hb)
    _ = A := by rw [← add_mul, hab, one_mul]

theorem tlsUpCap_convex : Convex ℝ (tlsUpCap s c σ u h v) :=
  (Work.Topology.SphereSlicing.convex_PBox s c σ).inter (convex_setOf_gt_inner v _)

theorem tlsDnCap_convex : Convex ℝ (tlsDnCap s c σ u h v) :=
  (Work.Topology.SphereSlicing.convex_PBox s c σ).inter (convex_setOf_lt_inner v _)

theorem tlsWallOpen_convex : Convex ℝ (tlsWallOpen s c σ ℓ lam) :=
  (Work.Topology.SphereSlicing.convex_PBox s c σ).inter (convex_setOf_clm_gt ℓ lam)

theorem tlsBound (hs : 0 < s) : Bornology.IsBounded (Submission.PBox s c σ) :=
  (Metric.isBounded_ball).subset (Submission.PBox_subset_ball s hs.le c σ)

theorem tlsUpCap_isBounded (hs : 0 < s) : Bornology.IsBounded (tlsUpCap s c σ u h v) :=
  (tlsBound hs).subset tlsUpCap_subset_PBox

theorem tlsDnCap_isBounded (hs : 0 < s) : Bornology.IsBounded (tlsDnCap s c σ u h v) :=
  (tlsBound hs).subset tlsDnCap_subset_PBox

theorem tlsWallOpen_isBounded (hs : 0 < s) : Bornology.IsBounded (tlsWallOpen s c σ ℓ lam) :=
  (tlsBound hs).subset tlsWallOpen_subset_PBox

theorem tlsWallClosed_isBounded (hs : 0 < s) : Bornology.IsBounded (tlsWallClosed s c σ ℓ lam) :=
  (tlsBound hs).subset tlsWallClosed_subset_PBox

theorem tlsBoxCl_convex : Convex ℝ (tlsBoxCl s c σ) :=
  (Work.Topology.SphereSlicing.convex_PBox s c σ).closure

theorem tlsBoxCl_isClosed : IsClosed (tlsBoxCl s c σ) := isClosed_closure

theorem tlsBoxCl_isBounded (hs : 0 < s) : Bornology.IsBounded (tlsBoxCl s c σ) := by
  have h : Submission.PBox s c σ ⊆ Metric.closedBall c (5 / 2 * s) :=
    (Submission.PBox_subset_ball s hs.le c σ).trans Metric.ball_subset_closedBall
  exact (Metric.isBounded_closedBall).subset ((closure_minimal h Metric.isClosed_closedBall))

theorem tlsBoxCl_isCompact (hs : 0 < s) : IsCompact (tlsBoxCl s c σ) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨tlsBoxCl_isClosed, tlsBoxCl_isBounded hs⟩

theorem interior_tlsBoxCl (hs : 0 < s) : interior (tlsBoxCl s c σ) = Submission.PBox s c σ := by
  have hc : c ∈ Submission.PBox s c σ := by
    rw [Submission.mem_PBox]
    intro i
    rw [sub_self, abs_zero]
    exact mul_pos (Submission.boxSide_pos i) hs
  rw [tlsBoxCl,
    (Work.Topology.SphereSlicing.convex_PBox s c σ).interior_closure_eq_interior_of_nonempty_interior
      ⟨c, by rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]; exact hc⟩,
    (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]

/-! ## The removal identity -/

theorem tiltedLevelRemoved_eq_three (s u h lam : ℝ) (c v : R3) (σ : Equiv.Perm (Fin 3))
    (ℓ : R3 →L[ℝ] ℝ) :
    Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam =
      tlsUpCap s c σ u h v ∪ tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam := by
  ext y
  simp only [Work.Drive.Mono.tiltedLevelRemoved, Work.Drive.EpsForm.tiltedSlabClosed, tlsUpCap,
    tlsDnCap, tlsWallClosed, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hy, hnot⟩
    rcases not_and_or.mp hnot with h1 | h2
    · have hc' : h < |inner ℝ v y - (inner ℝ v c + u)| := not_le.mp h1
      rcases (lt_abs.mp hc') with hlt | hlt
      · exact Or.inl (Or.inl ⟨hy, by linarith⟩)
      · exact Or.inl (Or.inr ⟨hy, by linarith⟩)
    · exact Or.inr ⟨hy, le_of_not_gt h2⟩
  · intro hmem
    rcases hmem with h' | ⟨hy, hle⟩
    · rcases h' with ⟨hy, hlt⟩ | ⟨hy, hlt⟩
      · refine ⟨hy, fun hc => ?_⟩
        have hx : h < |inner ℝ v y - (inner ℝ v c + u)| := by
          rw [lt_abs]; exact Or.inl (by linarith)
        linarith [hc.1]
      · refine ⟨hy, fun hc => ?_⟩
        have hx : h < |inner ℝ v y - (inner ℝ v c + u)| := by
          rw [lt_abs]; exact Or.inr (by linarith)
        linarith [hc.1]
    · exact ⟨hy, fun hc => absurd hc.2 (not_lt.mpr hle)⟩


/-! ## A direction of positive level, orthogonal to `v` -/

theorem exists_pos_of_clm_ne {ℓ : R3 →L[ℝ] ℝ} (h : ℓ ≠ 0) : ∃ u : R3, 0 < ℓ u := by
  by_contra hc
  have hc' : ∀ u : R3, ℓ u ≤ 0 := fun u => le_of_not_gt (fun hlt => hc ⟨u, hlt⟩)
  refine h (ContinuousLinearMap.ext fun u => ?_)
  have h1 : ℓ u ≤ 0 := hc' u
  have h2 : -ℓ u ≤ 0 := by
    have h := hc' (-u)
    rwa [map_neg] at h
  show ℓ u = 0
  linarith

/-- If `ℓ v = 0` and `ℓ ≠ 0`, `v ≠ 0` there is a direction `w` with `ℓ w > 0` and `⟪v,w⟫ = 0`. -/
theorem exists_dir_perp_pos {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓne : ℓ ≠ 0)
    (hℓv : ℓ v = 0) : ∃ w : R3, 0 < ℓ w ∧ inner ℝ v w = 0 := by
  obtain ⟨u, hu⟩ := exists_pos_of_clm_ne hℓne
  refine ⟨u - (inner ℝ v u / ‖v‖ ^ 2) • v, ?_, ?_⟩
  · rw [map_sub, map_smul, hℓv, smul_zero, sub_zero]; exact hu
  · rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have h2 : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
    rw [div_mul_cancel₀ _ (ne_of_gt h2), sub_self]

/-! ## The interiors of the wall regions -/

theorem interior_clm_ge (ψ : R3 →L[ℝ] ℝ) {w : R3} (hw : 0 < ψ w) (lam : ℝ) :
    interior {y : R3 | lam ≤ ψ y} = {y : R3 | lam < ψ y} := by
  refine Set.Subset.antisymm ?_
    (interior_maximal (fun y hy => show lam ≤ ψ y from le_of_lt (show lam < ψ y from hy))
      (isOpen_lt continuous_const ψ.continuous))
  intro y hy
  simp only [Set.mem_ofPred_eq]
  by_contra hcon
  rw [not_lt] at hcon
  have hyle : lam ≤ ψ y := by
    have h := interior_subset (s := {y : R3 | lam ≤ ψ y}) hy
    simpa only [Set.mem_ofPred_eq] using h
  have hyeq : ψ y = lam := le_antisymm hcon hyle
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hy)
  set t : ℝ := ε / (2 * (‖w‖ + 1)) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have htw : t * ‖w‖ < ε := by
    have h1 : t ≤ ε / (2 * (‖w‖ + 1)) := le_of_eq ht
    have h2 : ε / (2 * (‖w‖ + 1)) * ‖w‖ < ε := by
      have hden : 0 < 2 * (‖w‖ + 1) := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [norm_nonneg w, hε]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg w)]
  have hmem : y - t • w ∈ interior {y : R3 | lam ≤ ψ y} := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have hyw : y - t • w - y = -(t • w) := by module
    rw [hyw, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact htw
  have hval : ψ (y - t • w) = lam - t * ψ w := by
    rw [map_sub, map_smul, smul_eq_mul, hyeq]
  have hsub := interior_subset (s := {y : R3 | lam ≤ ψ y}) hmem
  simp only [Set.mem_ofPred_eq] at hsub
  rw [hval] at hsub
  have hpos : 0 < t * ψ w := mul_pos htpos hw
  linarith [hsub]

theorem interior_inner_ge {v : R3} (hv : v ≠ 0) (A : ℝ) :
    interior {y : R3 | A ≤ inner ℝ v y} = {y : R3 | A < inner ℝ v y} := by
  refine Set.Subset.antisymm ?_
    (interior_maximal (fun y hy => show A ≤ inner ℝ v y from le_of_lt (show A < inner ℝ v y from hy))
      (isOpen_lt continuous_const
        ((continuous_const : Continuous fun _ : R3 => v).inner continuous_id)))
  intro y hy
  simp only [Set.mem_ofPred_eq]
  by_contra hcon
  rw [not_lt] at hcon
  have hyle : A ≤ inner ℝ v y := by
    have h := interior_subset (s := {y : R3 | A ≤ inner ℝ v y}) hy
    simpa only [Set.mem_ofPred_eq] using h
  have hyeq : inner ℝ v y = A := le_antisymm hcon hyle
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hy)
  set t : ℝ := ε / (2 * (‖v‖ + 1)) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have htv : t * ‖v‖ < ε := by
    have h1 : t ≤ ε / (2 * (‖v‖ + 1)) := le_of_eq ht
    have h2 : ε / (2 * (‖v‖ + 1)) * ‖v‖ < ε := by
      have hden : 0 < 2 * (‖v‖ + 1) := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [norm_nonneg v, hε]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg v)]
  have hmem : y - t • v ∈ interior {y : R3 | A ≤ inner ℝ v y} := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have hyw : y - t • v - y = -(t • v) := by module
    rw [hyw, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact htv
  have hval : inner ℝ v (y - t • v) = A - t * inner ℝ v v := by
    rw [inner_sub_right, inner_smul_right, hyeq]
  have hsub := interior_subset (s := {y : R3 | A ≤ inner ℝ v y}) hmem
  simp only [Set.mem_ofPred_eq] at hsub
  rw [hval] at hsub
  have hpos : 0 < t * inner ℝ v v := mul_pos htpos (real_inner_self_pos.mpr hv)
  linarith [hsub]

theorem interior_inner_le {v : R3} (hv : v ≠ 0) (A : ℝ) :
    interior {y : R3 | inner ℝ v y ≤ A} = {y : R3 | inner ℝ v y < A} := by
  have h : {y : R3 | inner ℝ v y ≤ A} = {y : R3 | -A ≤ inner ℝ (-v) y} := by
    ext y
    simp only [Set.mem_ofPred_eq, inner_neg_left]
    constructor <;> intro h <;> linarith
  rw [h, interior_inner_ge (neg_ne_zero.mpr hv) (-A)]
  ext y
  simp only [Set.mem_ofPred_eq, inner_neg_left]
  constructor <;> intro h <;> linarith

/-! ## The interiors of the closed convex bodies and the caps -/

theorem interior_boxCl_inter_ge (hs : 0 < s) (hv : v ≠ 0) :
    interior (tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y}) =
      tlsUpCap s c σ u h v := by
  rw [tlsUpCap, interior_inter, interior_tlsBoxCl hs, interior_inner_ge hv]

theorem interior_boxCl_inter_le (hs : 0 < s) (hv : v ≠ 0) :
    interior (tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h}) =
      tlsDnCap s c σ u h v := by
  rw [tlsDnCap, interior_inter, interior_tlsBoxCl hs, interior_inner_le hv]

theorem interior_boxCl_inter_wall (hs : 0 < s) (hℓne : ℓ ≠ 0) :
    interior (tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y}) = tlsWallOpen s c σ ℓ lam := by
  obtain ⟨w, hw⟩ := exists_pos_of_clm_ne hℓne
  rw [tlsWallOpen, interior_inter, interior_tlsBoxCl hs, interior_clm_ge ℓ hw]

theorem interior_tlsWallClosed (hℓne : ℓ ≠ 0) :
    interior (tlsWallClosed s c σ ℓ lam) = tlsWallOpen s c σ ℓ lam := by
  obtain ⟨w, hw⟩ := exists_pos_of_clm_ne hℓne
  rw [tlsWallClosed, tlsWallOpen, interior_inter,
    (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq, interior_clm_ge ℓ hw]

/-! ## The closures of the pieces -/

theorem closure_tlsUpCap_subset :
    closure (tlsUpCap s c σ u h v) ⊆
      tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y} := by
  have hclosed : IsClosed (tlsBoxCl s c σ ∩
      {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y}) :=
    tlsBoxCl_isClosed.inter (isClosed_le continuous_const
      ((continuous_const : Continuous fun _ : R3 => v).inner continuous_id))
  refine (closure_mono ?_).trans (le_of_eq hclosed.closure_eq)
  intro y hy
  exact ⟨subset_closure hy.1,
    show inner ℝ v c + u + h ≤ inner ℝ v y from
      le_of_lt (show inner ℝ v c + u + h < inner ℝ v y from hy.2)⟩

theorem closure_tlsDnCap_subset :
    closure (tlsDnCap s c σ u h v) ⊆
      tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h} := by
  have hclosed : IsClosed (tlsBoxCl s c σ ∩
      {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h}) :=
    tlsBoxCl_isClosed.inter (isClosed_le
      ((continuous_const : Continuous fun _ : R3 => v).inner continuous_id) continuous_const)
  refine (closure_mono ?_).trans (le_of_eq hclosed.closure_eq)
  intro y hy
  exact ⟨subset_closure hy.1,
    show inner ℝ v y ≤ inner ℝ v c + u - h from
      le_of_lt (show inner ℝ v y < inner ℝ v c + u - h from hy.2)⟩

theorem closure_tlsWallClosed_subset :
    closure (tlsWallClosed s c σ ℓ lam) ⊆ tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y} := by
  have hclosed : IsClosed (tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y}) :=
    tlsBoxCl_isClosed.inter (isClosed_le continuous_const ℓ.continuous)
  refine (closure_mono ?_).trans (le_of_eq hclosed.closure_eq)
  intro y hy
  exact ⟨subset_closure hy.1, show lam ≤ ℓ y from hy.2⟩

theorem closure_tlsWallOpen_subset :
    closure (tlsWallOpen s c σ ℓ lam) ⊆ tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y} := by
  have hclosed : IsClosed (tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y}) :=
    tlsBoxCl_isClosed.inter (isClosed_le continuous_const ℓ.continuous)
  refine (closure_mono ?_).trans (le_of_eq hclosed.closure_eq)
  intro y hy
  exact ⟨subset_closure hy.1,
    show lam ≤ ℓ y from le_of_lt (show lam < ℓ y from hy.2)⟩

/-! ## The closures of the open pieces -/

theorem closure_tlsUpCap_eq (hne : (tlsUpCap s c σ u h v).Nonempty) :
    closure (tlsUpCap s c σ u h v) =
      tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y} := by
  refine Set.Subset.antisymm closure_tlsUpCap_subset ?_
  intro y hy
  obtain ⟨y₁, hy₁⟩ := hne
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hconv := Work.Topology.SphereSlicing.convex_PBox s c σ
  have hopen := Work.Topology.SphereSlicing.isOpen_PBox s c σ
  set t : ℝ := min (1 / 2) (ε / (2 * (‖y₁ - y‖ + 1))) with ht
  have htpos : 0 < t := by
    rw [ht]; exact lt_min (by norm_num) (by positivity)
  have htle : t ≤ 1 / 2 := by rw [ht]; exact min_le_left _ _
  have htdist : t * ‖y₁ - y‖ < ε := by
    have h1 : t ≤ ε / (2 * (‖y₁ - y‖ + 1)) := by rw [ht]; exact min_le_right _ _
    have h2 : ε / (2 * (‖y₁ - y‖ + 1)) * ‖y₁ - y‖ < ε := by
      have hden : 0 < 2 * (‖y₁ - y‖ + 1) := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [norm_nonneg (y₁ - y), hε]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg (y₁ - y))]
  have hmemP : (1 - t) • y + t • y₁ ∈ Submission.PBox s c σ := by
    have h2 := hconv.combo_closure_interior_mem_interior (x := y) (y := y₁)
      (a := 1 - t) (b := t) hy.1
      (by rw [hopen.interior_eq]; exact hy₁.1) (by linarith) htpos (by ring)
    rwa [hopen.interior_eq] at h2
  have hmemf : inner ℝ v c + u + h < inner ℝ v ((1 - t) • y + t • y₁) := by
    have h1 : inner ℝ v c + u + h < inner ℝ v y₁ := hy₁.2
    have h2 : inner ℝ v c + u + h ≤ inner ℝ v y := hy.2
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    nlinarith [h1, h2, htpos, htle]
  refine ⟨(1 - t) • y + t • y₁, ⟨hmemP, hmemf⟩, ?_⟩
  rw [dist_comm, dist_eq_norm]
  have hsub : (1 - t) • y + t • y₁ - y = t • (y₁ - y) := by module
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  exact htdist

theorem closure_tlsDnCap_eq (hne : (tlsDnCap s c σ u h v).Nonempty) :
    closure (tlsDnCap s c σ u h v) =
      tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h} := by
  refine Set.Subset.antisymm closure_tlsDnCap_subset ?_
  intro y hy
  obtain ⟨y₁, hy₁⟩ := hne
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hconv := Work.Topology.SphereSlicing.convex_PBox s c σ
  have hopen := Work.Topology.SphereSlicing.isOpen_PBox s c σ
  set t : ℝ := min (1 / 2) (ε / (2 * (‖y₁ - y‖ + 1))) with ht
  have htpos : 0 < t := by
    rw [ht]; exact lt_min (by norm_num) (by positivity)
  have htle : t ≤ 1 / 2 := by rw [ht]; exact min_le_left _ _
  have htdist : t * ‖y₁ - y‖ < ε := by
    have h1 : t ≤ ε / (2 * (‖y₁ - y‖ + 1)) := by rw [ht]; exact min_le_right _ _
    have h2 : ε / (2 * (‖y₁ - y‖ + 1)) * ‖y₁ - y‖ < ε := by
      have hden : 0 < 2 * (‖y₁ - y‖ + 1) := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [norm_nonneg (y₁ - y), hε]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg (y₁ - y))]
  have hmemP : (1 - t) • y + t • y₁ ∈ Submission.PBox s c σ := by
    have h2 := hconv.combo_closure_interior_mem_interior (x := y) (y := y₁)
      (a := 1 - t) (b := t) hy.1
      (by rw [hopen.interior_eq]; exact hy₁.1) (by linarith) htpos (by ring)
    rwa [hopen.interior_eq] at h2
  have hmemf : inner ℝ v ((1 - t) • y + t • y₁) < inner ℝ v c + u - h := by
    have h1 : inner ℝ v y₁ < inner ℝ v c + u - h := hy₁.2
    have h2 : inner ℝ v y ≤ inner ℝ v c + u - h := hy.2
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    nlinarith [h1, h2, htpos, htle]
  refine ⟨(1 - t) • y + t • y₁, ⟨hmemP, hmemf⟩, ?_⟩
  rw [dist_comm, dist_eq_norm]
  have hsub : (1 - t) • y + t • y₁ - y = t • (y₁ - y) := by module
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  exact htdist

theorem closure_tlsWallOpen_eq (hne : (tlsWallOpen s c σ ℓ lam).Nonempty) :
    closure (tlsWallOpen s c σ ℓ lam) = tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y} := by
  refine Set.Subset.antisymm closure_tlsWallOpen_subset ?_
  intro y hy
  obtain ⟨y₁, hy₁⟩ := hne
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hconv := Work.Topology.SphereSlicing.convex_PBox s c σ
  have hopen := Work.Topology.SphereSlicing.isOpen_PBox s c σ
  set t : ℝ := min (1 / 2) (ε / (2 * (‖y₁ - y‖ + 1))) with ht
  have htpos : 0 < t := by
    rw [ht]; exact lt_min (by norm_num) (by positivity)
  have htle : t ≤ 1 / 2 := by rw [ht]; exact min_le_left _ _
  have htdist : t * ‖y₁ - y‖ < ε := by
    have h1 : t ≤ ε / (2 * (‖y₁ - y‖ + 1)) := by rw [ht]; exact min_le_right _ _
    have h2 : ε / (2 * (‖y₁ - y‖ + 1)) * ‖y₁ - y‖ < ε := by
      have hden : 0 < 2 * (‖y₁ - y‖ + 1) := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [norm_nonneg (y₁ - y), hε]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg (y₁ - y))]
  have hmemP : (1 - t) • y + t • y₁ ∈ Submission.PBox s c σ := by
    have h2 := hconv.combo_closure_interior_mem_interior (x := y) (y := y₁)
      (a := 1 - t) (b := t) hy.1
      (by rw [hopen.interior_eq]; exact hy₁.1) (by linarith) htpos (by ring)
    rwa [hopen.interior_eq] at h2
  have hmemf : lam < ℓ ((1 - t) • y + t • y₁) := by
    have h1 : lam < ℓ y₁ := hy₁.2
    have h2 : lam ≤ ℓ y := hy.2
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    nlinarith [h1, h2, htpos, htle]
  refine ⟨(1 - t) • y + t • y₁, ⟨hmemP, hmemf⟩, ?_⟩
  rw [dist_comm, dist_eq_norm]
  have hsub : (1 - t) • y + t • y₁ - y = t • (y₁ - y) := by module
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  exact htdist

/-! ## The wall region is nonempty when its closure-region is -/

theorem tlsWallOpen_nonempty_of_closed (hℓne : ℓ ≠ 0)
    (hne : (tlsWallClosed s c σ ℓ lam).Nonempty) :
    (tlsWallOpen s c σ ℓ lam).Nonempty := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨w, hw⟩ := exists_pos_of_clm_ne hℓne
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hy.1)
  set t : ℝ := δ / (2 * (‖w‖ + 1)) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have htw : t * ‖w‖ < δ := by
    have h1 : t ≤ δ / (2 * (‖w‖ + 1)) := le_of_eq ht
    have h2 : δ / (2 * (‖w‖ + 1)) * ‖w‖ < δ := by
      have hden : 0 < 2 * (‖w‖ + 1) := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [norm_nonneg w, hδ]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg w)]
  refine ⟨y + t • w, ?_, ?_⟩
  · refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : y + t • w - y = t • w := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact htw
  · show lam < ℓ (y + t • w)
    have h2 : lam ≤ ℓ y := hy.2
    rw [map_add, map_smul, smul_eq_mul]
    have hpos : 0 < t * ℓ w := mul_pos htpos hw
    linarith [h2]


/-! ## The frontiers are spheres -/

theorem frontier_eq_of_closure_eq_interior_eq {a b : Set R3}
    (h1 : closure a = closure b) (h2 : interior a = interior b) : frontier a = frontier b := by
  rw [(closure_sdiff_interior a).symm, (closure_sdiff_interior b).symm, h1, h2]

theorem frontier_tlsUpCap_sphere (hs : 0 < s) (hv : v ≠ 0)
    (hne : (tlsUpCap s c σ u h v).Nonempty) :
    Work.InnermostDisk.IsEmbeddedSphere (frontier (tlsUpCap s c σ u h v)) := by
  have hCconv : Convex ℝ
      (tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y}) :=
    (tlsBoxCl_convex).inter (Work.Drive.Mono.convex_setOf_le_inner v _)
  have hCbdd : Bornology.IsBounded
      (tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y}) :=
    (tlsBoxCl_isBounded hs).subset Set.inter_subset_left
  have hCne : (interior (tlsBoxCl s c σ ∩
      {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y})).Nonempty := by
    rw [interior_boxCl_inter_ge hs hv]; exact hne
  have hsphere := Work.Drive.Mono.isEmbeddedSphere_frontier_of_convex hCconv hCne hCbdd
  have hCclosed : IsClosed (tlsBoxCl s c σ ∩
      {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y}) :=
    tlsBoxCl_isClosed.inter (isClosed_le continuous_const
      ((continuous_const : Continuous fun _ : R3 => v).inner continuous_id))
  have h1 : frontier (tlsUpCap s c σ u h v) =
      (tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y}) \
        tlsUpCap s c σ u h v := by
    rw [(closure_sdiff_interior (tlsUpCap s c σ u h v)).symm, closure_tlsUpCap_eq hne,
      tlsUpCap_isOpen.interior_eq]
  have h2 : frontier (tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y}) =
      (tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y}) \
        tlsUpCap s c σ u h v := by
    rw [(closure_sdiff_interior (tlsBoxCl s c σ ∩
        {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y})).symm, hCclosed.closure_eq,
      interior_boxCl_inter_ge hs hv]
  rw [h1, ← h2]
  exact hsphere

theorem frontier_tlsDnCap_sphere (hs : 0 < s) (hv : v ≠ 0)
    (hne : (tlsDnCap s c σ u h v).Nonempty) :
    Work.InnermostDisk.IsEmbeddedSphere (frontier (tlsDnCap s c σ u h v)) := by
  have hCconv : Convex ℝ
      (tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h}) :=
    (tlsBoxCl_convex).inter (convex_setOf_inner_le v (inner ℝ v c + u - h))
  have hCbdd : Bornology.IsBounded
      (tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h}) :=
    (tlsBoxCl_isBounded hs).subset Set.inter_subset_left
  have hCne : (interior (tlsBoxCl s c σ ∩
      {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h})).Nonempty := by
    rw [interior_boxCl_inter_le hs hv]; exact hne
  have hsphere := Work.Drive.Mono.isEmbeddedSphere_frontier_of_convex hCconv hCne hCbdd
  have hCclosed : IsClosed (tlsBoxCl s c σ ∩
      {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h}) :=
    tlsBoxCl_isClosed.inter (isClosed_le
      ((continuous_const : Continuous fun _ : R3 => v).inner continuous_id) continuous_const)
  have h1 : frontier (tlsDnCap s c σ u h v) =
      (tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h}) \
        tlsDnCap s c σ u h v := by
    rw [(closure_sdiff_interior (tlsDnCap s c σ u h v)).symm, closure_tlsDnCap_eq hne,
      tlsDnCap_isOpen.interior_eq]
  have h2 : frontier (tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h}) =
      (tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h}) \
        tlsDnCap s c σ u h v := by
    rw [(closure_sdiff_interior (tlsBoxCl s c σ ∩
        {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h})).symm, hCclosed.closure_eq,
      interior_boxCl_inter_le hs hv]
  rw [h1, ← h2]
  exact hsphere

theorem frontier_tlsWallOpen_sphere (hs : 0 < s) (hℓne : ℓ ≠ 0)
    (hne : (tlsWallOpen s c σ ℓ lam).Nonempty) :
    Work.InnermostDisk.IsEmbeddedSphere (frontier (tlsWallOpen s c σ ℓ lam)) := by
  have hCconv : Convex ℝ (tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y}) :=
    (tlsBoxCl_convex).inter (convex_setOf_clm_le ℓ lam)
  have hCbdd : Bornology.IsBounded (tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y}) :=
    (tlsBoxCl_isBounded hs).subset Set.inter_subset_left
  have hCne : (interior (tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y})).Nonempty := by
    rw [interior_boxCl_inter_wall hs hℓne]; exact hne
  have hsphere := Work.Drive.Mono.isEmbeddedSphere_frontier_of_convex hCconv hCne hCbdd
  have hCclosed : IsClosed (tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y}) :=
    tlsBoxCl_isClosed.inter (isClosed_le continuous_const ℓ.continuous)
  have h1 : frontier (tlsWallOpen s c σ ℓ lam) =
      (tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y}) \ tlsWallOpen s c σ ℓ lam := by
    rw [(closure_sdiff_interior (tlsWallOpen s c σ ℓ lam)).symm, closure_tlsWallOpen_eq hne,
      tlsWallOpen_isOpen.interior_eq]
  have h2 : frontier (tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y}) =
      (tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y}) \ tlsWallOpen s c σ ℓ lam := by
    rw [(closure_sdiff_interior (tlsBoxCl s c σ ∩ {y : R3 | lam ≤ ℓ y})).symm,
      hCclosed.closure_eq, interior_boxCl_inter_wall hs hℓne]
  rw [h1, ← h2]
  exact hsphere

/-! ## The closure of the wall region as a set -/

theorem tlsWallOpen_mem_closure (hℓne : ℓ ≠ 0) {z : R3}
    (hzP : z ∈ Submission.PBox s c σ) (hzl : lam ≤ ℓ z) :
    z ∈ closure (tlsWallOpen s c σ ℓ lam) := by
  obtain ⟨w, hw⟩ := exists_pos_of_clm_ne hℓne
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hzP)
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t : ℝ := min (δ / (2 * (‖w‖ + 1))) (ε / (2 * (‖w‖ + 1))) with ht
  have htpos : 0 < t := by rw [ht]; exact lt_min (by positivity) (by positivity)
  have htwδ : t * ‖w‖ < δ := by
    have h1 : t ≤ δ / (2 * (‖w‖ + 1)) := by rw [ht]; exact min_le_left _ _
    have h2 : δ / (2 * (‖w‖ + 1)) * ‖w‖ < δ := by
      have hden : 0 < 2 * (‖w‖ + 1) := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [norm_nonneg w, hδ]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg w)]
  have htwε : t * ‖w‖ < ε := by
    have h1 : t ≤ ε / (2 * (‖w‖ + 1)) := by rw [ht]; exact min_le_right _ _
    have h2 : ε / (2 * (‖w‖ + 1)) * ‖w‖ < ε := by
      have hden : 0 < 2 * (‖w‖ + 1) := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [norm_nonneg w, hε]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg w)]
  refine ⟨z + t • w, ⟨hball ?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have hsub : z + t • w - z = t • w := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact htwδ
  · show lam < ℓ (z + t • w)
    rw [map_add, map_smul, smul_eq_mul]
    have hpos : 0 < t * ℓ w := mul_pos htpos hw
    linarith
  · rw [dist_comm, dist_eq_norm]
    have hsub : z + t • w - z = t • w := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact htwε

theorem closure_tlsWallClosed_eq_closure_open (hℓne : ℓ ≠ 0) :
    closure (tlsWallClosed s c σ ℓ lam) = closure (tlsWallOpen s c σ ℓ lam) := by
  refine Set.Subset.antisymm ?_
    (closure_mono (fun z hz => ⟨hz.1, show lam ≤ ℓ z from le_of_lt hz.2⟩))
  refine closure_minimal ?_ isClosed_closure
  intro z hz
  rcases hz with ⟨hzP, hzl⟩
  by_cases hlt : lam < ℓ z
  · exact subset_closure ⟨hzP, hlt⟩
  · exact tlsWallOpen_mem_closure hℓne hzP hzl

theorem frontier_tlsWallClosed_eq (hℓne : ℓ ≠ 0) :
    frontier (tlsWallClosed s c σ ℓ lam) = frontier (tlsWallOpen s c σ ℓ lam) := by
  refine frontier_eq_of_closure_eq_interior_eq (closure_tlsWallClosed_eq_closure_open hℓne) ?_
  rw [interior_tlsWallClosed hℓne, tlsWallOpen_isOpen.interior_eq]

/-! ## The union of a cap with the wall region -/

theorem interior_union_dnCap_wallClosed (hv : v ≠ 0) (hℓne : ℓ ≠ 0) (hℓv : ℓ v = 0) :
    interior (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) =
      tlsDnCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    by_cases h1 : z ∈ tlsDnCap s c σ u h v
    · exact Or.inl h1
    by_cases h2 : z ∈ tlsWallOpen s c σ ℓ lam
    · exact Or.inr h2
    exfalso
    have hzu : z ∈ tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam :=
      interior_subset (s := tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) hz
    rcases hzu with hw' | hw'
    · exact h1 hw'
    · have hzP : z ∈ Submission.PBox s c σ := hw'.1
      have hzl : ℓ z = lam :=
        le_antisymm (le_of_not_gt (fun hlt => h2 ⟨hzP, hlt⟩)) hw'.2
      have hzf : inner ℝ v c + u - h ≤ inner ℝ v z := by
        by_contra hcon
        exact h1 ⟨hzP, lt_of_not_ge hcon⟩
      obtain ⟨w, hw, hvw⟩ := exists_dir_perp_pos hv hℓne hℓv
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz)
      set t : ℝ := ε / (2 * (‖w‖ + 1)) with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have htw : t * ‖w‖ < ε := by
        have h1' : t ≤ ε / (2 * (‖w‖ + 1)) := le_of_eq ht
        have h2' : ε / (2 * (‖w‖ + 1)) * ‖w‖ < ε := by
          have hden : 0 < 2 * (‖w‖ + 1) := by positivity
          rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
          nlinarith [norm_nonneg w, hε]
        nlinarith [mul_le_mul_of_nonneg_right h1' (norm_nonneg w)]
      have hmem : z - t • w ∈ interior
          (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) := by
        refine hball ?_
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : z - t • w - z = -(t • w) := by module
        rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        exact htw
      have hnotin : z - t • w ∉
          tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam := by
        intro hc
        rcases hc with hc | hc
        · have hlt : inner ℝ v (z - t • w) < inner ℝ v c + u - h := hc.2
          rw [inner_sub_right, inner_smul_right, hvw, mul_zero, sub_zero] at hlt
          linarith
        · have hlt : lam ≤ ℓ (z - t • w) := hc.2
          rw [map_sub, map_smul, smul_eq_mul] at hlt
          have hpos : 0 < t * ℓ w := mul_pos htpos hw
          linarith
      exact hnotin (interior_subset
        (s := tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) hmem)
  · intro z hz
    rcases hz with h | h
    · exact interior_maximal (Set.subset_union_left) tlsDnCap_isOpen h
    · exact interior_maximal
        (fun w hw => Or.inr ⟨hw.1, show lam ≤ ℓ w from le_of_lt hw.2⟩) tlsWallOpen_isOpen h

theorem interior_union_upCap_wallClosed (hv : v ≠ 0) (hℓne : ℓ ≠ 0) (hℓv : ℓ v = 0) :
    interior (tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) =
      tlsUpCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    by_cases h1 : z ∈ tlsUpCap s c σ u h v
    · exact Or.inl h1
    by_cases h2 : z ∈ tlsWallOpen s c σ ℓ lam
    · exact Or.inr h2
    exfalso
    have hzu : z ∈ tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam :=
      interior_subset (s := tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) hz
    rcases hzu with hw' | hw'
    · exact h1 hw'
    · have hzP : z ∈ Submission.PBox s c σ := hw'.1
      have hzl : ℓ z = lam :=
        le_antisymm (le_of_not_gt (fun hlt => h2 ⟨hzP, hlt⟩)) hw'.2
      have hzf : inner ℝ v z ≤ inner ℝ v c + u + h := by
        by_contra hcon
        exact h1 ⟨hzP, lt_of_not_ge hcon⟩
      obtain ⟨w, hw, hvw⟩ := exists_dir_perp_pos hv hℓne hℓv
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz)
      set t : ℝ := ε / (2 * (‖w‖ + 1)) with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have htw : t * ‖w‖ < ε := by
        have h1' : t ≤ ε / (2 * (‖w‖ + 1)) := le_of_eq ht
        have h2' : ε / (2 * (‖w‖ + 1)) * ‖w‖ < ε := by
          have hden : 0 < 2 * (‖w‖ + 1) := by positivity
          rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
          nlinarith [norm_nonneg w, hε]
        nlinarith [mul_le_mul_of_nonneg_right h1' (norm_nonneg w)]
      have hmem : z - t • w ∈ interior
          (tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) := by
        refine hball ?_
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : z - t • w - z = -(t • w) := by module
        rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        exact htw
      have hnotin : z - t • w ∉
          tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam := by
        intro hc
        rcases hc with hc | hc
        · have hlt : inner ℝ v c + u + h < inner ℝ v (z - t • w) := hc.2
          rw [inner_sub_right, inner_smul_right, hvw, mul_zero, sub_zero] at hlt
          linarith
        · have hlt : lam ≤ ℓ (z - t • w) := hc.2
          rw [map_sub, map_smul, smul_eq_mul] at hlt
          have hpos : 0 < t * ℓ w := mul_pos htpos hw
          linarith
      exact hnotin (interior_subset
        (s := tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) hmem)
  · intro z hz
    rcases hz with h | h
    · exact interior_maximal (Set.subset_union_left) tlsUpCap_isOpen h
    · exact interior_maximal
        (fun w hw => Or.inr ⟨hw.1, show lam ≤ ℓ w from le_of_lt hw.2⟩) tlsWallOpen_isOpen h

theorem closure_union_dnCap_wallClosed (hℓne : ℓ ≠ 0) :
    closure (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) =
      closure (tlsDnCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam) := by
  refine Set.Subset.antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · intro z hz
    rcases hz with hz' | hz'
    · exact subset_closure (s := tlsDnCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam) (Or.inl hz')
    · by_cases hlt : lam < ℓ z
      · exact subset_closure (s := tlsDnCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam)
          (Or.inr ⟨hz'.1, hlt⟩)
      · exact closure_mono Set.subset_union_right
          (tlsWallOpen_mem_closure hℓne hz'.1 hz'.2)
  · intro z hz
    rcases hz with hz' | hz'
    · exact Or.inl hz'
    · exact Or.inr ⟨hz'.1, show lam ≤ ℓ z from le_of_lt hz'.2⟩

theorem closure_union_upCap_wallClosed (hℓne : ℓ ≠ 0) :
    closure (tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) =
      closure (tlsUpCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam) := by
  refine Set.Subset.antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · intro z hz
    rcases hz with hz' | hz'
    · exact subset_closure (s := tlsUpCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam) (Or.inl hz')
    · by_cases hlt : lam < ℓ z
      · exact subset_closure (s := tlsUpCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam)
          (Or.inr ⟨hz'.1, hlt⟩)
      · exact closure_mono Set.subset_union_right
          (tlsWallOpen_mem_closure hℓne hz'.1 hz'.2)
  · intro z hz
    rcases hz with hz' | hz'
    · exact Or.inl hz'
    · exact Or.inr ⟨hz'.1, show lam ≤ ℓ z from le_of_lt hz'.2⟩

theorem frontier_union_dnCap_wallClosed_sphere (hs : 0 < s) (hv : v ≠ 0) (hℓne : ℓ ≠ 0)
    (hℓv : ℓ v = 0)
    (hne : (tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam)) := by
  have hsphere : Work.InnermostDisk.IsEmbeddedSphere
      (frontier (tlsDnCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam)) :=
    Work.Drive.Mono.isEmbeddedSphere_frontier_union_convex tlsDnCap_isOpen
      tlsWallOpen_isOpen (tlsDnCap_convex) (tlsWallOpen_convex)
      (tlsDnCap_isBounded hs) (tlsWallOpen_isBounded hs) hne
  have hint : interior (tlsDnCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam) =
      tlsDnCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam :=
    (tlsDnCap_isOpen.union tlsWallOpen_isOpen).interior_eq
  rw [show frontier (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) =
      frontier (tlsDnCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam) from
    frontier_eq_of_closure_eq_interior_eq (closure_union_dnCap_wallClosed hℓne)
      (by rw [interior_union_dnCap_wallClosed hv hℓne hℓv, hint])]
  exact hsphere

theorem frontier_union_upCap_wallClosed_sphere (hs : 0 < s) (hv : v ≠ 0) (hℓne : ℓ ≠ 0)
    (hℓv : ℓ v = 0)
    (hne : (tlsUpCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier (tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam)) := by
  have hsphere : Work.InnermostDisk.IsEmbeddedSphere
      (frontier (tlsUpCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam)) :=
    Work.Drive.Mono.isEmbeddedSphere_frontier_union_convex tlsUpCap_isOpen
      tlsWallOpen_isOpen (tlsUpCap_convex) (tlsWallOpen_convex)
      (tlsUpCap_isBounded hs) (tlsWallOpen_isBounded hs) hne
  have hint : interior (tlsUpCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam) =
      tlsUpCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam :=
    (tlsUpCap_isOpen.union tlsWallOpen_isOpen).interior_eq
  rw [show frontier (tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) =
      frontier (tlsUpCap s c σ u h v ∪ tlsWallOpen s c σ ℓ lam) from
    frontier_eq_of_closure_eq_interior_eq (closure_union_upCap_wallClosed hℓne)
      (by rw [interior_union_upCap_wallClosed hv hℓne hℓv, hint])]
  exact hsphere

/-! ## The frontier of a union of two sets with disjoint closures -/

theorem interior_union_subset_closure (A B : Set R3) :
    interior (A ∪ B) ⊆ interior A ∪ closure B := by
  intro x hx
  by_cases hxi : x ∈ interior A
  · exact Or.inl hxi
  · right
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
    have hδ' : 0 < min δ ε := lt_min hδ hε
    by_contra hcon
    push_neg at hcon
    have hsub : Metric.ball x (min δ ε) ⊆ A := by
      intro u hu
      have hu' : u ∈ interior (A ∪ B) := hball (Metric.ball_subset_ball (min_le_left _ _) hu)
      rcases interior_subset hu' with h | h
      · exact h
      · exact absurd (hcon u h)
          (not_le.mpr (lt_of_lt_of_le (by rw [dist_comm]; exact Metric.mem_ball.mp hu)
            (min_le_right _ _)))
    exact hxi (interior_maximal hsub Metric.isOpen_ball (Metric.mem_ball_self hδ'))

theorem interior_union_subset_closure' (A B : Set R3) :
    interior (A ∪ B) ⊆ closure A ∪ interior B := by
  intro x hx
  have h := interior_union_subset_closure B A (by rwa [Set.union_comm] at hx)
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem frontier_union_of_disjoint_closure {A B : Set R3}
    (h : Disjoint (closure A) (closure B)) : frontier (A ∪ B) = frontier A ∪ frontier B := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [(closure_sdiff_interior (A ∪ B)).symm, closure_union] at hx
    rcases hx with ⟨hxA | hxB, hxnot⟩
    · by_cases hxi : x ∈ interior A
      · exact absurd (interior_mono Set.subset_union_left hxi) hxnot
      · exact Or.inl ⟨hxA, hxi⟩
    · by_cases hxi : x ∈ interior B
      · exact absurd (interior_mono Set.subset_union_right hxi) hxnot
      · exact Or.inr ⟨hxB, hxi⟩
  · intro x hx
    rw [(closure_sdiff_interior (A ∪ B)).symm, closure_union]
    rcases hx with hx | hx
    · refine ⟨Or.inl hx.1, fun hc => ?_⟩
      have hxB : x ∈ closure B := by
        rcases interior_union_subset_closure A B hc with h' | h'
        · exact absurd h' hx.2
        · exact h'
      exact (Set.disjoint_left.mp h hx.1) hxB
    · refine ⟨Or.inr hx.1, fun hc => ?_⟩
      have hxA : x ∈ closure A := by
        rcases interior_union_subset_closure' A B hc with h' | h'
        · exact h'
        · exact absurd h' hx.2
      exact (Set.disjoint_left.mp h hxA) hx.1

theorem frontier_union_three_of_disjoint_closure {A B C : Set R3}
    (hAB : Disjoint (closure A) (closure B))
    (hAC : Disjoint (closure A) (closure C))
    (hBC : Disjoint (closure B) (closure C)) :
    frontier (A ∪ B ∪ C) = frontier A ∪ frontier B ∪ frontier C := by
  have h1 : Disjoint (closure (A ∪ B)) (closure C) := by
    rw [closure_union, Set.disjoint_iff_inter_eq_empty, Set.union_inter_distrib_right,
      hAC.inter_eq, hBC.inter_eq, Set.union_empty]
  rw [frontier_union_of_disjoint_closure h1, frontier_union_of_disjoint_closure hAB,
    Set.union_assoc]


/-! ## Assembling a disjoint union of spheres from "empty or sphere" pieces -/

theorem sphere_decomposition_of_two (A B : Set R3)
    (hA : A = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere A)
    (hB : B = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere B) (hd : Disjoint A B) :
    ∃ (n : ℕ) (S : Fin n → Set R3),
      (∀ i, Work.InnermostDisk.IsEmbeddedSphere (S i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (S i) (S j)) ∧ A ∪ B = ⋃ i, S i := by
  rcases hA with rfl | hA
  · rcases hB with rfl | hB
    · exact ⟨0, Fin.elim0, by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i, by simp⟩
    · rw [Set.empty_union]
      exact ⟨1, fun _ => B, by intro i; exact hB,
        by intro i j hij; exact absurd (Subsingleton.elim i j) hij, (Set.iUnion_const B).symm⟩
  · rcases hB with rfl | hB
    · rw [Set.union_empty]
      exact ⟨1, fun _ => A, by intro i; exact hA,
        by intro i j hij; exact absurd (Subsingleton.elim i j) hij, (Set.iUnion_const A).symm⟩
    · refine ⟨2, ![A, B], ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · simpa using hA
        · simpa using hB
      · intro i j hij
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact hd
        · exact hd.symm
        · exact absurd rfl hij
      · ext x
        constructor
        · rintro (h | h)
          · exact Set.mem_iUnion.mpr ⟨0, by simpa using h⟩
          · exact Set.mem_iUnion.mpr ⟨1, by simpa using h⟩
        · intro h
          rcases Set.mem_iUnion.mp h with ⟨i, hi⟩
          fin_cases i
          · exact Or.inl (by simpa using hi)
          · exact Or.inr (by simpa using hi)

theorem sphere_decomposition_of_three (A B C : Set R3)
    (hA : A = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere A)
    (hB : B = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere B)
    (hC : C = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    ∃ (n : ℕ) (S : Fin n → Set R3),
      (∀ i, Work.InnermostDisk.IsEmbeddedSphere (S i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (S i) (S j)) ∧ A ∪ B ∪ C = ⋃ i, S i := by
  rcases hA with rfl | hA
  · rw [Set.empty_union]
    exact sphere_decomposition_of_two B C hB hC hBC
  rcases hB with rfl | hB
  · rw [Set.union_empty]
    exact sphere_decomposition_of_two A C (Or.inr hA) hC hAC
  rcases hC with rfl | hC
  · rw [Set.union_empty]
    exact sphere_decomposition_of_two A B (Or.inr hA) (Or.inr hB) hAB
  refine ⟨3, ![A, B, C], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using hA
    · simpa using hB
    · simpa using hC
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hAB
    · exact hAC
    · exact hAB.symm
    · exact absurd rfl hij
    · exact hBC
    · exact hAC.symm
    · exact hBC.symm
    · exact absurd rfl hij
  · ext x
    constructor
    · rintro ((h | h) | h)
      · exact Set.mem_iUnion.mpr ⟨0, by simpa using h⟩
      · exact Set.mem_iUnion.mpr ⟨1, by simpa using h⟩
      · exact Set.mem_iUnion.mpr ⟨2, by simpa using h⟩
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl (by simpa using hi))
      · exact Or.inl (Or.inr (by simpa using hi))
      · exact Or.inr (by simpa using hi)

end

end Work.Drive.Final
