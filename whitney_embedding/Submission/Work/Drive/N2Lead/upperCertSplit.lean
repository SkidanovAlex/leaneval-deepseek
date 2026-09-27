import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.saddleScaled
import Submission.Work.Drive.N2.footMapDefs
import Submission.Work.Drive.N2Lead.saddlePacket
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_starRegions
import Submission.Work.Drive.N2Lead.saddleLowerCertifiedFleet
import Submission.Work.Drive.N2Lead.upperRegionRate
import Submission.Work.Drive.N2Lead.upperRegionRateNeg
import Submission.Work.Drive.N2Lead.upperRegionMem
import Submission.Work.Drive.N2Lead.modelArcCross_absLe
import Submission.Work.Drive.N2Lead.polarBridgeRate
import Submission.Work.Drive.N2Lead.polarArc_eq_sqrt
import Submission.Work.Drive.N2Lead.saddleArcs
import Submission.Work.Drive.N2Lead.modelArcRayFree
import Submission.Work.Drive.N2Lead.polarRayHit
import Submission.Work.Drive.N2Lead.arcRangeOrBridgeZone
import Submission.Work.Drive.N2Lead.saddleWindow_of_packet_band_off
import Submission.Work.Compat.MFDerivCongrV433

set_option maxHeartbeats 1000000

open scoped Manifold ContDiff

/-!
# §4.3: the **upper** certificate of the saddle window (H8, session S27)

The lower certificate of the saddle packet (`Work.Drive.N2Lead.saddleLowerCertifiedFleet`) certifies
the *anchor* level `c - lam η`.  This file certifies the *upper* level `c + lam η` for the two-piece
drawing produced by the engine `Work.Drive.N2Lead.saddleWindow_of_packet_band_off`:

`W x = if x ∈ saddleRegion U Z c₀ then cE3 (saddlePsi η δ (Z x)) else A (foot x)`.

The design is `N2Lead/NOTES_LEAD_saddlePacket.md` §4.3; the interface is recorded in
`N2Lead/NOTES_H8_upperCert_S27.md`.

## The point classes of the upper level `u⁺ = c + lam η` and their rows

* `y ∈ saddleRegion` (the *model*): `W y = cE3 (Ψ (Z y))` with `(Z y)² = η + i w`, `|w| < c₀`; the
  rows come from `upperRegionMem` / `upperRegionRate` / `upperRegionRateNeg`.
* `y ∉ saddleRegion`: `foot y` lies on the anchor level (`f (foot y) = c - lam η`), `foot y = L.γ j t₀`
  for a level component `j`, and `W y = A (foot y)`:
  * `j ≠ i`: the parked circle `farCurve n j t₀` (region `ball (proj2 (farPos n j)) 2`);
  * `j = i`: the marked polar curve `t ↦ cE3 (r (Θ t) exp (i Θ t))`, split by the coverage row
    `arcRangeOrBridgeZone` into the two **pinned** arcs (`A (L.γ i (τU w)) = cE3 (arcZ η w)` resp.
    its negative, rate `modelArcCross_absLe`) and the **bridge** (`|Θ t - kπ| ≤ φE`, rate
    `polarBridgeRate` and its odd mirror).

Everything is fed to the star-regions engine `isCertifiedAt_of_starRegions`, whose regions here are
`Ω_R = {Re > 0} ∩ ball 0 5` (centre `1`), `Ω_L` its mirror (centre `-1`) and the far discs.
-/

namespace Work.Drive.N2Lead.UpCS

open scoped Topology
open Set Filter

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## The two-piece drawing of the engine -/

/-- **The two-piece drawing of the saddle engine**: the model picture `cE3 ∘ Ψ ∘ Z` inside the model
region `|Im (Z ·)²| < c₀` and the transported anchor picture `A ∘ foot` outside it.  This is the
function produced by `Work.Drive.N2Lead.saddleWindow_of_packet_band_off` (with `a = c - lam η`). -/
def saddleWindowDrawing (η δ c₀ : ℝ) (U : Set M) (Z : M → ℂ)
    (A : M → EuclideanSpace ℝ (Fin 3)) (foot : M → M) : M → EuclideanSpace ℝ (Fin 3) := by
  classical
  exact fun x => if x ∈ Work.Drive.N2.saddleRegion U Z c₀
    then Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z x)) else A (foot x)

lemma saddleWindowDrawing_of_mem {η δ c₀ : ℝ} {U : Set M} {Z : M → ℂ}
    {A : M → EuclideanSpace ℝ (Fin 3)} {foot : M → M} {x : M}
    (hx : x ∈ Work.Drive.N2.saddleRegion U Z c₀) :
    saddleWindowDrawing η δ c₀ U Z A foot x
      = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z x)) := by
  rw [saddleWindowDrawing]; exact if_pos hx

lemma saddleWindowDrawing_of_notMem {η δ c₀ : ℝ} {U : Set M} {Z : M → ℂ}
    {A : M → EuclideanSpace ℝ (Fin 3)} {foot : M → M} {x : M}
    (hx : x ∉ Work.Drive.N2.saddleRegion U Z c₀) :
    saddleWindowDrawing η δ c₀ U Z A foot x = A (foot x) := by
  rw [saddleWindowDrawing]; exact if_neg hx

/-! ## The region family of the upper certificate -/

/-- The right region of the upper certificate: `{Re > 0} ∩ ball 0 5`, centre `1`. -/
def upperRight : Set ℂ := {z : ℂ | 0 < z.re ∧ ‖z‖ < 5}

/-- The left region: the mirror of `upperRight`, centre `-1`. -/
def upperLeft : Set ℂ := {z : ℂ | z.re < 0 ∧ ‖z‖ < 5}

/-- **The regions of the upper certificate**: the left region, the right region (both for the marked
component's polar curve, cut by the sign of the real part) and one disc per parked circle. -/
def upperRegions (n : ℕ) (i : Fin n) : Fin (n + 1) → Set ℂ :=
  Fin.cases upperLeft
    (fun j => if j = i then upperRight else Metric.ball (proj2 (farPos n j)) 2)

/-- The centres of the regions: `-1`, `1` and the parking spots' projections. -/
def upperCentres (n : ℕ) (i : Fin n) : Fin (n + 1) → ℂ :=
  Fin.cases (-1) (fun j => if j = i then 1 else proj2 (farPos n j))

@[simp] lemma upperRegions_zero (n : ℕ) (i : Fin n) : upperRegions n i 0 = upperLeft := rfl

@[simp] lemma upperRegions_succ (n : ℕ) (i j : Fin n) :
    upperRegions n i j.succ = if j = i then upperRight else Metric.ball (proj2 (farPos n j)) 2 := rfl

@[simp] lemma upperCentres_zero (n : ℕ) (i : Fin n) : upperCentres n i 0 = -1 := rfl

@[simp] lemma upperCentres_succ (n : ℕ) (i j : Fin n) :
    upperCentres n i j.succ = if j = i then 1 else proj2 (farPos n j) := rfl

lemma upperCentres_succ_self (n : ℕ) (i : Fin n) : upperCentres n i i.succ = 1 := by
  rw [upperCentres_succ, if_pos rfl]

lemma upperCentres_succ_of_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) :
    upperCentres n i j.succ = proj2 (farPos n j) := by
  rw [upperCentres_succ, if_neg h]

lemma upperRegions_succ_self (n : ℕ) (i : Fin n) : upperRegions n i i.succ = upperRight := by
  rw [upperRegions_succ, if_pos rfl]

lemma upperRegions_succ_of_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) :
    upperRegions n i j.succ = Metric.ball (proj2 (farPos n j)) 2 := by
  rw [upperRegions_succ, if_neg h]

/-! ## The elementary geometry of the region family -/

lemma mem_upperLeft {z : ℂ} : z ∈ upperLeft ↔ z.re < 0 ∧ ‖z‖ < 5 := Iff.rfl

lemma mem_upperRight {z : ℂ} : z ∈ upperRight ↔ 0 < z.re ∧ ‖z‖ < 5 := Iff.rfl

lemma upperLeft_eq_inter : upperLeft = {z : ℂ | z.re < 0} ∩ {z : ℂ | ‖z‖ < 5} := rfl

lemma upperRight_eq_inter : upperRight = {z : ℂ | 0 < z.re} ∩ {z : ℂ | ‖z‖ < 5} := rfl

lemma mem_upperLeft_ball {z : ℂ} (h1 : z.re < 0) (h2 : ‖z‖ < 5) : z ∈ upperLeft := ⟨h1, h2⟩

lemma mem_upperRight_ball {z : ℂ} (h1 : 0 < z.re) (h2 : ‖z‖ < 5) : z ∈ upperRight := ⟨h1, h2⟩

lemma isOpen_upperLeft : IsOpen upperLeft := by
  have h1 : IsOpen {z : ℂ | z.re < 0} := isOpen_lt Complex.continuous_re continuous_const
  have h2 : IsOpen {z : ℂ | ‖z‖ < 5} := by
    rw [show {z : ℂ | ‖z‖ < 5} = Metric.ball 0 5 by
      ext z; simp [Metric.mem_ball, dist_eq_norm]]
    exact Metric.isOpen_ball
  rw [upperLeft_eq_inter]
  exact h1.inter h2

lemma isOpen_upperRight : IsOpen upperRight := by
  have h1 : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {z : ℂ | ‖z‖ < 5} := by
    rw [show {z : ℂ | ‖z‖ < 5} = Metric.ball 0 5 by
      ext z; simp [Metric.mem_ball, dist_eq_norm]]
    exact Metric.isOpen_ball
  rw [upperRight_eq_inter]
  exact h1.inter h2

lemma convex_re_lt_zero : Convex ℝ {z : ℂ | z.re < 0} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have h1 : (a • x + b • y).re = a * x.re + b * y.re := by simp
  rw [h1]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by linarith
    rw [← ha0, zero_mul, zero_add, hb1, one_mul]
    exact hy
  · have h3 : a * x.re < 0 := mul_neg_of_pos_of_neg ha0 hx
    have h4 : b * y.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hy.le
    linarith

lemma convex_re_gt_zero : Convex ℝ {z : ℂ | 0 < z.re} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have h1 : (a • x + b • y).re = a * x.re + b * y.re := by simp
  rw [h1]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by linarith
    rw [← ha0, zero_mul, zero_add, hb1, one_mul]
    exact hy
  · have h3 : 0 < a * x.re := mul_pos ha0 hx
    have h4 : 0 ≤ b * y.re := mul_nonneg hb hy.le
    linarith

lemma convex_upperLeft : Convex ℝ upperLeft := by
  rw [upperLeft_eq_inter]
  refine Convex.inter convex_re_lt_zero ?_
  rw [show {z : ℂ | ‖z‖ < 5} = Metric.ball 0 5 by
      ext z; simp [Metric.mem_ball, dist_eq_norm]]
  exact convex_ball 0 5

lemma convex_upperRight : Convex ℝ upperRight := by
  rw [upperRight_eq_inter]
  refine Convex.inter convex_re_gt_zero ?_
  rw [show {z : ℂ | ‖z‖ < 5} = Metric.ball 0 5 by
      ext z; simp [Metric.mem_ball, dist_eq_norm]]
  exact convex_ball 0 5

lemma closedBall_subset_upperLeft : Metric.closedBall (-1 : ℂ) (1 / 2) ⊆ upperLeft := by
  intro z hz
  have h1 : ‖z + 1‖ ≤ 1 / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] using hz
  show z.re < 0 ∧ ‖z‖ < 5
  constructor
  · have h3 : z.re + 1 ≤ ‖z + 1‖ := by
      have := Complex.abs_re_le_norm (z + 1)
      have h4 := (abs_le.mp this).2
      simpa using h4
    linarith
  · have h2 : ‖z‖ ≤ ‖z + 1‖ + 1 := by
      calc ‖z‖ = ‖(z + 1) - 1‖ := by ring_nf
        _ ≤ ‖z + 1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖z + 1‖ + 1 := by simp
    linarith

lemma closedBall_subset_upperRight : Metric.closedBall (1 : ℂ) (1 / 2) ⊆ upperRight := by
  intro z hz
  have h1 : ‖z - 1‖ ≤ 1 / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  show 0 < z.re ∧ ‖z‖ < 5
  constructor
  · have h3 : -‖z - 1‖ ≤ z.re - 1 := by
      have := Complex.abs_re_le_norm (z - 1)
      have h4 := (abs_le.mp this).1
      simpa using h4
    linarith
  · have h2 : ‖z‖ ≤ ‖z - 1‖ + 1 := by
      calc ‖z‖ = ‖(z - 1) + 1‖ := by ring_nf
        _ ≤ ‖z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖z - 1‖ + 1 := by simp
    linarith

lemma norm_proj2_farPos_ge_17 (n : ℕ) (j : Fin n) : 17 ≤ ‖proj2 (farPos n j)‖ := by
  have h := norm_proj2_farPos_ge n j
  linarith

lemma isOpen_convex_upperRegions (n : ℕ) (i : Fin n) :
    ∀ k : Fin (n + 1), IsOpen (upperRegions n i k) ∧ Convex ℝ (upperRegions n i k) := by
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact ⟨isOpen_upperLeft, convex_upperLeft⟩
  · by_cases hj : j = i
    · rw [upperRegions_succ, if_pos hj]
      exact ⟨isOpen_upperRight, convex_upperRight⟩
    · rw [upperRegions_succ, if_neg hj]
      exact ⟨Metric.isOpen_ball, convex_ball _ _⟩

lemma closedBall_subset_upperRegions (n : ℕ) (i : Fin n) :
    ∀ k : Fin (n + 1), Metric.closedBall (upperCentres n i k) (1 / 2) ⊆ upperRegions n i k := by
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · rw [upperCentres_zero, upperRegions_zero]
    exact closedBall_subset_upperLeft
  · by_cases hj : j = i
    · rw [upperCentres_succ, upperRegions_succ, if_pos hj, if_pos hj]
      exact closedBall_subset_upperRight
    · rw [upperCentres_succ, upperRegions_succ, if_neg hj, if_neg hj]
      intro z hz
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by norm_num)

/-! ### The three pairwise disjointnesses of the pieces -/

lemma disjoint_upperLeft_upperRight : Disjoint upperLeft upperRight := by
  rw [Set.disjoint_left]
  intro z hzL hzR
  rw [mem_upperLeft] at hzL
  rw [mem_upperRight] at hzR
  exact absurd hzL.1 (not_lt.mpr hzR.1.le)

lemma disjoint_upperLeft_far (n : ℕ) (j : Fin n) :
    Disjoint upperLeft (Metric.ball (proj2 (farPos n j)) 2) := by
  rw [Set.disjoint_left]
  intro z hzL hzF
  rw [Metric.mem_ball, dist_eq_norm] at hzF
  have htri : ‖proj2 (farPos n j)‖ - ‖z‖ ≤ ‖proj2 (farPos n j) - z‖ := by
    have h := norm_add_le (proj2 (farPos n j) - z) z
    rw [sub_add_cancel] at h
    linarith
  have h1 : ‖proj2 (farPos n j) - z‖ = ‖z - proj2 (farPos n j)‖ := norm_sub_rev _ _
  rw [h1] at htri
  have h2 := norm_proj2_farPos_ge_17 n j
  rw [mem_upperLeft] at hzL
  linarith [hzL.2]

lemma disjoint_upperRight_far (n : ℕ) (j : Fin n) :
    Disjoint upperRight (Metric.ball (proj2 (farPos n j)) 2) := by
  rw [Set.disjoint_left]
  intro z hzL hzF
  rw [Metric.mem_ball, dist_eq_norm] at hzF
  have htri : ‖proj2 (farPos n j)‖ - ‖z‖ ≤ ‖proj2 (farPos n j) - z‖ := by
    have h := norm_add_le (proj2 (farPos n j) - z) z
    rw [sub_add_cancel] at h
    linarith
  have h1 : ‖proj2 (farPos n j) - z‖ = ‖z - proj2 (farPos n j)‖ := norm_sub_rev _ _
  rw [h1] at htri
  have h2 := norm_proj2_farPos_ge_17 n j
  rw [mem_upperRight] at hzL
  linarith [hzL.2]

lemma disjoint_far_far {n : ℕ} {j k : Fin n} (h : j ≠ k) :
    Disjoint (Metric.ball (proj2 (farPos n j)) 2) (Metric.ball (proj2 (farPos n k)) 2) := by
  rw [Set.disjoint_left]
  intro z hzj hzk
  rw [Metric.mem_ball, dist_eq_norm] at hzj hzk
  have h4 : dist (proj2 (farPos n j)) (proj2 (farPos n k))
      ≤ ‖z - proj2 (farPos n j)‖ + ‖z - proj2 (farPos n k)‖ := by
    rw [dist_eq_norm]
    calc ‖proj2 (farPos n j) - proj2 (farPos n k)‖
        = ‖(proj2 (farPos n j) - z) + (z - proj2 (farPos n k))‖ := by ring_nf
      _ ≤ ‖proj2 (farPos n j) - z‖ + ‖z - proj2 (farPos n k)‖ := norm_add_le _ _
      _ = ‖z - proj2 (farPos n j)‖ + ‖z - proj2 (farPos n k)‖ := by rw [norm_sub_rev]
  have h5 := dist_proj2_farPos_ge (n := n) (j := j) (k := k) h
  linarith

/-- **The classification of the region family.**  A point of `upperRegions n i k` is either in the
left region (and then `k = 0`), or in the right region `upperRight` of the marked component (then
`k = i.succ`), or in the far disc of a component `j ≠ i` (then `k = j.succ`). -/
lemma mem_upperRegions_classify {n : ℕ} {i : Fin n} {k : Fin (n + 1)} {z : ℂ}
    (hz : z ∈ upperRegions n i k) :
    (k = 0 ∧ z ∈ upperLeft) ∨
      ∃ j : Fin n, k = j.succ ∧
        ((j = i ∧ z ∈ upperRight) ∨ (j ≠ i ∧ z ∈ Metric.ball (proj2 (farPos n j)) 2)) := by
  rcases Fin.eq_zero_or_eq_succ k with hk | ⟨j, rfl⟩
  · subst hk
    exact Or.inl ⟨rfl, hz⟩
  · by_cases hj : j = i
    · rw [upperRegions_succ, if_pos hj] at hz
      exact Or.inr ⟨j, rfl, Or.inl ⟨hj, hz⟩⟩
    · rw [upperRegions_succ, if_neg hj] at hz
      exact Or.inr ⟨j, rfl, Or.inr ⟨hj, hz⟩⟩

lemma pairwiseDisjoint_upperRegions (n : ℕ) (i : Fin n) :
    Pairwise fun k l : Fin (n + 1) => Disjoint (upperRegions n i k) (upperRegions n i l) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro z hzk hzl
  have hLR : ∀ {z : ℂ}, z ∈ upperLeft → z ∈ upperRight → False :=
    fun {z} h1 h2 => Set.disjoint_left.mp disjoint_upperLeft_upperRight h1 h2
  have hLF : ∀ (j : Fin n) {z : ℂ}, z ∈ upperLeft →
      z ∈ Metric.ball (proj2 (farPos n j)) 2 → False :=
    fun j {z} h1 h2 => Set.disjoint_left.mp (disjoint_upperLeft_far n j) h1 h2
  have hRF : ∀ (j : Fin n) {z : ℂ}, z ∈ upperRight →
      z ∈ Metric.ball (proj2 (farPos n j)) 2 → False :=
    fun j {z} h1 h2 => Set.disjoint_left.mp (disjoint_upperRight_far n j) h1 h2
  have hFF : ∀ {j j' : Fin n}, j ≠ j' → ∀ {z : ℂ},
      z ∈ Metric.ball (proj2 (farPos n j)) 2 →
      z ∈ Metric.ball (proj2 (farPos n j')) 2 → False :=
    fun {j j'} hjj {z} h1 h2 => Set.disjoint_left.mp (disjoint_far_far hjj) h1 h2
  rcases mem_upperRegions_classify hzk with ⟨hk0, hzL⟩ | ⟨j, hkj, hzj⟩
  · rcases mem_upperRegions_classify hzl with ⟨hl0, hzlL⟩ | ⟨j', hlj', hzj'⟩
    · exact absurd (hk0.trans hl0.symm) hkl
    · rcases hzj' with ⟨-, hzR⟩ | ⟨-, hzF⟩
      · exact hLR hzL hzR
      · exact hLF j' hzL hzF
  · rcases hzj with ⟨hji, hzR⟩ | ⟨hji, hzF⟩
    · rcases mem_upperRegions_classify hzl with ⟨hl0, hzlL⟩ | ⟨j', hlj', hzj'⟩
      · exact hLR hzlL hzR
      · rcases hzj' with ⟨hj'i, hzR'⟩ | ⟨hj'i, hzF'⟩
        · exact absurd (hkj.trans (by rw [hlj', hji, hj'i])) hkl
        · exact hRF j' hzR hzF'
    · rcases mem_upperRegions_classify hzl with ⟨hl0, hzlL⟩ | ⟨j', hlj', hzj'⟩
      · exact hLF j hzlL hzF
      · rcases hzj' with ⟨hj'i, hzR'⟩ | ⟨hj'i, hzF'⟩
        · exact hRF j hzR' hzF
        · exact hFF (fun hjj => hkl (by rw [hkj, hlj', hjj])) hzF hzF'


/-! ## The main theorem: the upper certificate

The statement is long because it carries (a) the *engine* rows of
`Work.Drive.N2Lead.saddleWindow_of_packet_band_off` (which the caller has anyway), (b) the *packet*
rows of `Work.Drive.N2Lead.saddlePacketRowsOfArcs` in the form the certificate consumes them, and
(c) the analytic rows of the profile `r`. -/


/-! ## The polar curve and the model arc: the analytic bricks of the certificate -/

/-- The marked polar curve `t ↦ cE3 (r (Θ t) · exp (i Θ t))` of the packet. -/
def polarCurve (r Θ : ℝ → ℝ) : ℝ → EuclideanSpace ℝ (Fin 3) :=
  fun t => Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))

@[simp] lemma polarCurve_apply (r Θ : ℝ → ℝ) (t : ℝ) :
    polarCurve r Θ t
      = Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) := rfl

lemma proj2_polarCurve (r Θ : ℝ → ℝ) (t : ℝ) :
    proj2 (polarCurve r Θ t) = (r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) := by
  rw [polarCurve_apply, proj2_cE3]

lemma norm_proj2_polarCurve {r Θ : ℝ → ℝ} (hrpos : ∀ φ : ℝ, 0 < r φ) (t : ℝ) :
    ‖proj2 (polarCurve r Θ t)‖ = r (Θ t) := by
  rw [proj2_polarCurve, norm_mul, Complex.norm_exp]
  simp [abs_of_pos (hrpos (Θ t))]

lemma polarCurve_periodic {r Θ : ℝ → ℝ} (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ)
    (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi) (t : ℝ) :
    polarCurve r Θ (t + 1) = polarCurve r Θ t := by
  rw [polarCurve_apply, polarCurve_apply, hΘper t, hrper (Θ t)]
  congr 1
  have h1 : ((Θ t + 2 * Real.pi : ℝ) : ℂ) * Complex.I
      = ((Θ t : ℝ) : ℂ) * Complex.I + (2 * Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [h1, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma polarCurve_add_int {r Θ : ℝ → ℝ} (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ)
    (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi) (k : ℤ) (t : ℝ) :
    polarCurve r Θ (t + k) = polarCurve r Θ t := by
  have hper : Function.Periodic (polarCurve r Θ) 1 := polarCurve_periodic hrper hΘper
  have := hper.int_mul k
  simpa using this t

lemma contDiff_polarCurve {r Θ : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polarCurve r Θ) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => (r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) := by
    refine ContDiff.mul ?_ ?_
    · exact Complex.ofRealCLM.contDiff.comp (hr.comp hΘ)
    · refine Complex.contDiff_exp.comp ?_
      exact (Complex.ofRealCLM.contDiff.comp hΘ).mul contDiff_const
  have h2 : polarCurve r Θ
      = fun t : ℝ => Work.Drive.N2.cE3 ((r (Θ t) : ℂ)
          * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) := rfl
  rw [h2]
  exact Work.Drive.N2.cE3.contDiff.comp h1

/-! ### The model arc `arcZ` against the model root `mobiusRho` -/

lemma sq_eq_sq_iff_eq_or_eq_neg_c (a b : ℂ) : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    have h2 : (a - b) * (a + b) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Or.inl (sub_eq_zero.mp h3)
    · exact Or.inr (by linear_combination h3)
  · rintro (rfl | rfl) <;> ring

lemma mobiusRho_sq_of_neg {η δ w : ℝ} (hδ : 0 < δ)
    (h2 : (0 : ℝ) < 2 - 4 * δ) :
    (Work.Drive.N2Lead.mobiusRho η δ (-η) w) ^ 2 = -(η : ℂ) + (w : ℂ) * Complex.I := by
  rw [Work.Drive.N2Lead.mobiusRho, complex_sqrt_sq']
  rw [Work.Drive.N2.saddleSigma_apply]
  have h3 : (-η + Work.Drive.N2.saddleM δ w * (-η - -η) : ℝ) = -η := by ring
  rw [h3]
  push_cast
  ring

lemma arcZ_eq_or_eq_neg_mobiusRho {η δ w : ℝ} (hδ : 0 < δ) (h2 : (0 : ℝ) < 2 - 4 * δ) :
    arcZ η w = Work.Drive.N2Lead.mobiusRho η δ (-η) w ∨
      arcZ η w = -Work.Drive.N2Lead.mobiusRho η δ (-η) w := by
  have h1 : arcZ η w ^ 2 = (Work.Drive.N2Lead.mobiusRho η δ (-η) w) ^ 2 := by
    rw [arcZ_sq, mobiusRho_sq_of_neg hδ h2]
  exact (sq_eq_sq_iff_eq_or_eq_neg_c _ _).mp h1

lemma re_mobiusRho_pos {η δ w : ℝ} (hδ : 0 < δ) (h2 : (0 : ℝ) < 2 - 4 * δ) (hw : w ≠ 0) :
    0 < (Work.Drive.N2Lead.mobiusRho η δ (-η) w).re := by
  have hsq := mobiusRho_sq_of_neg (η := η) hδ h2 (w := w)
  have him : (Work.Drive.N2Lead.mobiusRho η δ (-η) w ^ 2).im = w := by
    rw [hsq]; simp
  have hne : (Work.Drive.N2Lead.mobiusRho η δ (-η) w) ^ 2 ≠ 0 := by
    intro h0
    have h1 : w = 0 := by rw [← him, h0]; simp
    exact hw h1
  have hre : (Work.Drive.N2Lead.mobiusRho η δ (-η) w).re ≠ 0 := by
    intro h0
    have h1 : (Work.Drive.N2Lead.mobiusRho η δ (-η) w ^ 2).im = 0 := by
      rw [pow_two, Complex.mul_im, h0]
      ring
    rw [him] at h1
    exact hw h1
  have hnn : 0 ≤ (Work.Drive.N2Lead.mobiusRho η δ (-η) w).re := by
    have := Work.Drive.N2Lead.sqrt_re_nonneg'
      (Work.Drive.N2Lead.modelZeta η δ (-η) w)
    rw [Work.Drive.N2Lead.mobiusRho]; exact this
  exact lt_of_le_of_ne' hnn hre

lemma im_sqrt_neg_of_im_neg {z : ℂ} (hz : z.im < 0) : (Complex.sqrt z).im < 0 := by
  have hre : 0 < (Complex.sqrt z).re := by
    refine Work.Drive.N2Lead.upperMem_sqrt_re_pos (Or.inl ?_)
    exact ne_of_lt hz
  have hsq : Complex.sqrt z ^ 2 = z := complex_sqrt_sq' z
  have him : (Complex.sqrt z ^ 2).im = 2 * (Complex.sqrt z).re * (Complex.sqrt z).im := by
    rw [pow_two, Complex.mul_im]; ring
  rw [hsq] at him
  have h2 : 0 < 2 * (Complex.sqrt z).re := by linarith
  by_contra hcon
  push_neg at hcon
  have : 0 ≤ 2 * (Complex.sqrt z).re * (Complex.sqrt z).im :=
    mul_nonneg (le_of_lt h2) hcon
  linarith [him.symm ▸ hz]

lemma re_arcZ_pos_of_pos {η : ℝ} (hη : 0 < η) {w : ℝ} (hw : 0 < w) : 0 < (arcZ η w).re := by
  have hz : (η - (w : ℂ) * Complex.I).im < 0 := by
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one]
    linarith
  have h := im_sqrt_neg_of_im_neg hz
  rw [arcZ, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp only [zero_mul, one_mul]
  linarith

lemma re_arcZ_neg_of_neg {η : ℝ} (hη : 0 < η) {w : ℝ} (hw : w < 0) : (arcZ η w).re < 0 := by
  have hz : 0 < (η - (w : ℂ) * Complex.I).im := by
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one]
    linarith
  have hpos : 0 < (Complex.sqrt (η - (w : ℂ) * Complex.I)).im := by
    have hre : 0 < (Complex.sqrt (η - (w : ℂ) * Complex.I)).re := by
      refine Work.Drive.N2Lead.upperMem_sqrt_re_pos (Or.inl ?_)
      exact ne_of_gt hz
    have hsq : Complex.sqrt (η - (w : ℂ) * Complex.I) ^ 2 = η - (w : ℂ) * Complex.I :=
      complex_sqrt_sq' _
    have him : (Complex.sqrt (η - (w : ℂ) * Complex.I) ^ 2).im
        = 2 * (Complex.sqrt (η - (w : ℂ) * Complex.I)).re
          * (Complex.sqrt (η - (w : ℂ) * Complex.I)).im := by
      rw [pow_two, Complex.mul_im]; ring
    rw [hsq] at him
    have h2 : 0 < 2 * (Complex.sqrt (η - (w : ℂ) * Complex.I)).re := by linarith
    by_contra hcon
    push_neg at hcon
    have : 2 * (Complex.sqrt (η - (w : ℂ) * Complex.I)).re
        * (Complex.sqrt (η - (w : ℂ) * Complex.I)).im ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt h2) hcon
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one] at him
    linarith
  rw [arcZ, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp only [zero_mul, one_mul]
  linarith

lemma arcZ_eq_mobiusRho_of_pos {η δ w : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (h2 : (0 : ℝ) < 2 - 4 * δ) (hw : 0 < w) :
    arcZ η w = Work.Drive.N2Lead.mobiusRho η δ (-η) w := by
  rcases arcZ_eq_or_eq_neg_mobiusRho (η := η) hδ h2 (w := w) with h | h
  · exact h
  · exfalso
    have h1 := re_arcZ_pos_of_pos hη hw
    have h2' := re_mobiusRho_pos (η := η) hδ h2 (ne_of_gt hw)
    rw [h, Complex.neg_re] at h1
    linarith

lemma arcZ_eq_neg_mobiusRho_of_neg {η δ w : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (h2 : (0 : ℝ) < 2 - 4 * δ) (hw : w < 0) :
    arcZ η w = -Work.Drive.N2Lead.mobiusRho η δ (-η) w := by
  rcases arcZ_eq_or_eq_neg_mobiusRho (η := η) hδ h2 (w := w) with h | h
  · exfalso
    have h1 := re_arcZ_neg_of_neg hη hw
    have h2' := re_mobiusRho_pos (η := η) hδ h2 (ne_of_lt hw)
    rw [h] at h1
    linarith
  · exact h

lemma re_arcZ_zero {η : ℝ} (hη : 0 ≤ η) : (arcZ η 0).re = 0 := by
  rw [arcZ]
  have h1 : (((η : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * Complex.I) = ((η : ℝ) : ℂ) := by simp
  rw [h1, Complex.sqrt_of_nonneg (by exact_mod_cast hη), Complex.mul_re, Complex.I_re,
    Complex.I_im]
  simp

lemma arcZ_ne_zero_of_ne {η w : ℝ} (hw : w ≠ 0) : arcZ η w ≠ 0 := by
  intro h
  have h1 := arcZ_sq_im η w
  rw [h] at h1
  simp at h1
  exact hw h1.symm

lemma re_arcZ_ne_zero_iff {η : ℝ} {w : ℝ} (hw : w ≠ 0) : (arcZ η w).re ≠ 0 := by
  intro h0
  have him : ((arcZ η w) ^ 2).im = 2 * (arcZ η w).re * (arcZ η w).im := by
    rw [pow_two, Complex.mul_im]; ring
  rw [arcZ_sq_im η w, h0] at him
  simp at him
  exact hw him

lemma normSq_arcZ_le {η m w : ℝ} (hw : |w| ≤ m) :
    Complex.normSq (arcZ η w) ≤ Real.sqrt (η ^ 2 + m ^ 2) := by
  rw [normSq_arcZ]
  exact Real.sqrt_le_sqrt (by nlinarith [abs_le.mp hw, sq_abs w, sq_nonneg w])

/-- `deriv` of a pointwise negation. -/
lemma deriv_neg_fun (g : ℝ → ℂ) (w : ℝ) : deriv (fun u => -g u) w = -deriv g w := by
  by_cases hd : DifferentiableAt ℝ g w
  · exact (hd.hasDerivAt.neg).deriv
  · have h1 : ¬ DifferentiableAt ℝ (fun u : ℝ => -g u) w := by
      intro hcon
      refine hd ?_
      have := hcon.neg
      simpa using this
    rw [deriv_zero_of_not_differentiableAt h1, deriv_zero_of_not_differentiableAt hd, neg_zero]

/-- **The rate of the model arc about `1`** (the points of the right branch): for `0 < w` the
velocity of the model arc is never a real multiple of `z - 1`, where `z = arcZ η w`. -/
lemma arcZ_cross_one_ne_zero {η δ C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η)
    (hη' : η < 1 / 10) (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀)
    (hsmall : 8 * C₀ * η ≤ δ) {w : ℝ} (hw : w ∈ Set.Icc (-2) 2) (hw0 : 0 < w) :
    (star (arcZ η w - 1) * deriv (fun u : ℝ => arcZ η u) w).im ≠ 0 := by
  have h2 : (0 : ℝ) < 2 - 4 * δ := by linarith
  have he : (fun u : ℝ => arcZ η u)
      =ᶠ[𝓝 w] (fun u : ℝ => Work.Drive.N2Lead.mobiusRho η δ (-η) u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw0] with u hu
    exact arcZ_eq_mobiusRho_of_pos hη hδ h2 hu
  have hder := he.deriv_eq
  have hval := arcZ_eq_mobiusRho_of_pos (η := η) (δ := δ) (w := w) hη hδ h2 hw0
  rw [hval, hder]
  intro hzero
  have h := Work.Drive.N2Lead.modelArcCross_absLe (η := η) (δ := δ) (s := -η) (C₀ := C₀)
    hδ hδ' hη hη' ⟨by linarith, by linarith⟩ hC₀ hsmall w hw (ne_of_gt hw0)
  rw [hzero] at h
  simpa using h

/-- **The rate of the model arc about `-1`** (the points of the left branch): for `w < 0` the
velocity of the model arc is never a real multiple of `z + 1`, where `z = arcZ η w`. -/
lemma arcZ_cross_neg_one_ne_zero {η δ C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η)
    (hη' : η < 1 / 10) (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀)
    (hsmall : 8 * C₀ * η ≤ δ) {w : ℝ} (hw : w ∈ Set.Icc (-2) 2) (hw0 : w < 0) :
    (star (arcZ η w + 1) * deriv (fun u : ℝ => arcZ η u) w).im ≠ 0 := by
  have h2 : (0 : ℝ) < 2 - 4 * δ := by linarith
  have he : (fun u : ℝ => arcZ η u)
      =ᶠ[𝓝 w] (fun u : ℝ => -Work.Drive.N2Lead.mobiusRho η δ (-η) u) := by
    filter_upwards [isOpen_Iio.mem_nhds hw0] with u hu
    exact arcZ_eq_neg_mobiusRho_of_neg hη hδ h2 hu
  have hder := he.deriv_eq
  have hval := arcZ_eq_neg_mobiusRho_of_neg (η := η) (δ := δ) (w := w) hη hδ h2 hw0
  rw [hval, hder]
  have hder' : deriv (fun u : ℝ => -Work.Drive.N2Lead.mobiusRho η δ (-η) u) w
      = -deriv (fun u : ℝ => Work.Drive.N2Lead.mobiusRho η δ (-η) u) w :=
    deriv_neg_fun _ w
  rw [hder']
  intro hzero
  have h := Work.Drive.N2Lead.modelArcCross_absLe (η := η) (δ := δ) (s := -η) (C₀ := C₀)
    hδ hδ' hη hη' ⟨by linarith, by linarith⟩ hC₀ hsmall w hw (ne_of_lt hw0)
  have hEq : (star (-Work.Drive.N2Lead.mobiusRho η δ (-η) w + 1)
      * -deriv (fun u : ℝ => Work.Drive.N2Lead.mobiusRho η δ (-η) u) w).im
      = (star (Work.Drive.N2Lead.mobiusRho η δ (-η) w - 1)
        * deriv (fun u : ℝ => Work.Drive.N2Lead.mobiusRho η δ (-η) u) w).im := by
    have h1 : star (-Work.Drive.N2Lead.mobiusRho η δ (-η) w + 1)
        = -star (Work.Drive.N2Lead.mobiusRho η δ (-η) w - 1) := by
      rw [show -Work.Drive.N2Lead.mobiusRho η δ (-η) w + 1
          = -(Work.Drive.N2Lead.mobiusRho η δ (-η) w - 1) by ring, star_neg]
    rw [h1]
    congr 1
    ring
  rw [hEq] at hzero
  rw [hzero] at h
  simpa using h

/-- **The bridge rate of the marked polar curve, odd zone.**  The companion of
`Work.Drive.N2Lead.polarBridgeRate` for the points whose angle is within `φE` of an **odd** multiple
of `π` (drawn in the left region about the centre `-1`), obtained from `π`-periodicity of the
profile. -/
lemma polarBridgeRate_odd {η m : ℝ} (hη : 0 < η) (hm : 1 < m)
    {r : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrpi : ∀ φ : ℝ, r (φ + Real.pi) = r φ) (hrev : ∀ φ : ℝ, r (-φ) = r φ)
    (hlo : ∀ φ ∈ Set.Icc (0 : ℝ) (Work.Drive.N2Lead.mobiusPhiE η m),
      Real.sqrt (η ^ 2 + m ^ 2) ≤ r φ ^ 2)
    (hmono : ∀ φ ∈ Set.Icc (0 : ℝ) (Work.Drive.N2Lead.mobiusPhiE η m), deriv r φ ≤ 0)
    {φ : ℝ} (hφ : |φ| ≤ Work.Drive.N2Lead.mobiusPhiE η m) :
    0 < (star ((r (φ + Real.pi) : ℂ) * Complex.exp (((φ + Real.pi : ℝ) : ℂ) * Complex.I) + 1)
          * deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
              (φ + Real.pi)).im := by
  set G : ℝ → ℂ := fun x => (r x : ℂ) * Complex.exp ((x : ℂ) * Complex.I) with hG
  have hA : ∀ x : ℝ, G (x + Real.pi) = -G x := by
    intro x
    show (r (x + Real.pi) : ℂ) * Complex.exp (((x + Real.pi : ℝ) : ℂ) * Complex.I)
      = -((r x : ℂ) * Complex.exp ((x : ℂ) * Complex.I))
    have h1 : r (x + Real.pi) = r x := hrpi x
    have h2 : (((x + Real.pi : ℝ)) : ℂ) * Complex.I
        = ((x : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [h1, h2, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hder : deriv G (φ + Real.pi) = -deriv G φ := by
    have heq : G = fun x : ℝ => -G (x + Real.pi) := by
      funext x
      rw [hA x, neg_neg]
    have step : deriv G φ = deriv (fun x : ℝ => -G (x + Real.pi)) φ :=
      congrArg (fun F : ℝ → ℂ => deriv F φ) heq
    rw [deriv_neg_fun, deriv_comp_add_const] at step
    rw [step]
    ring
  show 0 < (star (G (φ + Real.pi) + 1) * deriv G (φ + Real.pi)).im
  rw [hder, hA φ]
  have hstar : star (-G φ + 1) = -star (G φ - 1) := by
    rw [show -G φ + 1 = -(G φ - 1) by ring, star_neg]
  rw [hstar, neg_mul_neg]
  have h := Work.Drive.N2Lead.polarBridgeRate (η := η) (m := m) hη hm hr hrpos hrev hlo hmono hφ
  simpa [hG] using h

/-- **The bridge rate of the polar curve, in the bridge zone.**  For `φ` whose class mod `π` is
within `φE = mobiusPhiE η m` of `0`, the polar curve `ψ ↦ r ψ · exp (i ψ)` has a non-vanishing
angular rate about the centre `1` (resp. `-1`) according to the sign of its real part.  This is
`Work.Drive.N2Lead.polarBridgeRate` plus the `π`-periodicity bookkeeping that carries the claim from
the interval `[-φE, φE]` to the whole bridge zone. -/
lemma polarBridge_rate_zone {η m : ℝ} (hη : 0 < η) (hm : 1 < m)
    {r : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ)
    (hrpi : ∀ φ : ℝ, r (φ + Real.pi) = r φ) (hrev : ∀ φ : ℝ, r (-φ) = r φ)
    (hlo : ∀ φ ∈ Set.Icc (0 : ℝ) (Work.Drive.N2Lead.mobiusPhiE η m),
      Real.sqrt (η ^ 2 + m ^ 2) ≤ r φ ^ 2)
    (hmono : ∀ φ ∈ Set.Icc (0 : ℝ) (Work.Drive.N2Lead.mobiusPhiE η m), deriv r φ ≤ 0)
    {φ : ℝ} (hφ : ∃ k : ℤ, |φ - (k : ℝ) * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE η m) :
    (0 < ((r φ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)).re →
        0 < (star ((r φ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) - 1)
            * deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) φ).im) ∧
    (((r φ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)).re < 0 →
        0 < (star ((r φ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) + 1)
            * deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) φ).im) := by
  obtain ⟨k, hk⟩ := hφ
  set θ₀ : ℝ := φ - (k : ℝ) * Real.pi with hθ₀def
  have hθ₀mem : |θ₀| ≤ Work.Drive.N2Lead.mobiusPhiE η m := by
    rw [hθ₀def]; exact hk
  have hφElt : Work.Drive.N2Lead.mobiusPhiE η m < Real.pi / 2 :=
    (leadProfile_phiE hη (by linarith : 0 < m)).2.2
  set F : ℝ → ℂ := fun ψ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) with hF
  have hFval : ∀ ψ : ℝ, F ψ = (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) := fun ψ => rfl
  have hper2 : Function.Periodic F (2 * Real.pi) := by
    intro ψ
    rw [hFval ψ, hFval (ψ + 2 * Real.pi)]
    have h1 : r (ψ + 2 * Real.pi) = r ψ := hrper ψ
    have h2 : (((ψ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
        = ((ψ : ℂ) * Complex.I) + (((2 : ℝ) : ℂ) * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [h1, h2, Complex.exp_add]
    have h3 : Complex.exp (((2 : ℝ) : ℂ) * (Real.pi : ℂ) * Complex.I) = 1 := by
      simpa using Complex.exp_two_pi_mul_I
    rw [h3, mul_one]
  have hπanti : ∀ ψ : ℝ, F (ψ + Real.pi) = -F ψ := by
    intro ψ
    rw [hFval ψ, hFval (ψ + Real.pi)]
    have h1 : r (ψ + Real.pi) = r ψ := hrpi ψ
    have h2 : (((ψ + Real.pi : ℝ)) : ℂ) * Complex.I
        = ((ψ : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [h1, h2, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hval_2π' : ∀ j : ℤ, ∀ ψ : ℝ, F (ψ + (j : ℝ) * (2 * Real.pi)) = F ψ := by
    intro j ψ
    exact hper2.int_mul j ψ
  have hval_2π : ∀ j : ℤ, F (θ₀ + (j : ℝ) * (2 * Real.pi)) = F θ₀ := fun j => hval_2π' j θ₀
  have hval_odd : ∀ j : ℤ, F (θ₀ + (2 * (j : ℝ) * Real.pi + Real.pi)) = -F θ₀ := by
    intro j
    rw [show θ₀ + (2 * (j : ℝ) * Real.pi + Real.pi)
        = (θ₀ + (j : ℝ) * (2 * Real.pi)) + Real.pi by ring, hπanti, hval_2π j]
  have hder_2π : ∀ j : ℤ, deriv F (θ₀ + (j : ℝ) * (2 * Real.pi)) = deriv F θ₀ := by
    intro j
    have heq : F = fun ψ : ℝ => F (ψ + (j : ℝ) * (2 * Real.pi)) := by
      funext ψ
      rw [hval_2π' j ψ]
    have h : deriv F θ₀ = deriv (fun ψ : ℝ => F (ψ + (j : ℝ) * (2 * Real.pi))) θ₀ :=
      congrArg (fun G : ℝ → ℂ => deriv G θ₀) heq
    rw [deriv_comp_add_const] at h
    exact h.symm
  have hπder : ∀ x : ℝ, deriv F x = -deriv F (x - Real.pi) := by
    intro x
    have hπfun : F = fun ψ : ℝ => -F (ψ - Real.pi) := by
      funext ψ
      have h := hπanti (ψ - Real.pi)
      rw [show ψ - Real.pi + Real.pi = ψ by ring] at h
      exact h
    have h : deriv F x = deriv (fun ψ : ℝ => -F (ψ - Real.pi)) x :=
      congrArg (fun G : ℝ → ℂ => deriv G x) hπfun
    rw [deriv_neg_fun, deriv_comp_sub_const] at h
    exact h
  have hder_odd : ∀ j : ℤ, deriv F (θ₀ + (2 * (j : ℝ) * Real.pi + Real.pi)) = -deriv F θ₀ := by
    intro j
    rw [show θ₀ + (2 * (j : ℝ) * Real.pi + Real.pi)
        = (θ₀ + (j : ℝ) * (2 * Real.pi)) + Real.pi by ring]
    rw [hπder (θ₀ + (j : ℝ) * (2 * Real.pi) + Real.pi)]
    rw [show θ₀ + (j : ℝ) * (2 * Real.pi) + Real.pi - Real.pi
        = θ₀ + (j : ℝ) * (2 * Real.pi) by ring]
    rw [hder_2π j]
  have hrew : 0 < (F θ₀).re := by
    rw [hFval θ₀, Complex.mul_re]
    have hcos : 0 < Real.cos θ₀ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_le.mp hθ₀mem, hφElt],
        by linarith [abs_le.mp hθ₀mem, hφElt]⟩
    have hre : (Complex.exp ((θ₀ : ℂ) * Complex.I)).re = Real.cos θ₀ := by
      rw [Complex.exp_ofReal_mul_I]; simp [Complex.cos_ofReal_re]
    have him : (Complex.exp ((θ₀ : ℂ) * Complex.I)).im = Real.sin θ₀ := by
      rw [Complex.exp_ofReal_mul_I]; simp [Complex.sin_ofReal_re]
    rw [hre, him]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (hrpos θ₀) hcos
  have hbr := Work.Drive.N2Lead.polarBridgeRate (η := η) (m := m) hη hm hr hrpos hrev hlo
    hmono (φ := θ₀) hθ₀mem
  rcases Int.even_or_odd k with hk2 | hk2
  · -- `k` even
    obtain ⟨j, hj⟩ := hk2
    have hk_eq : k = 2 * j := by omega
    have hφeq : φ = θ₀ + (j : ℝ) * (2 * Real.pi) := by rw [hθ₀def, hk_eq]; push_cast; ring
    have hval : F φ = F θ₀ := by rw [hφeq]; exact hval_2π j
    have hder : deriv F φ = deriv F θ₀ := by rw [hφeq]; exact hder_2π j
    constructor
    · intro _
      have hExp : star (F φ - 1) * deriv F φ = star (F θ₀ - 1) * deriv F θ₀ := by rw [hval, hder]
      rw [hExp]
      exact hbr
    · intro hneg
      exfalso
      have h1 : (F φ).re = (F θ₀).re := by rw [hval]
      rw [h1] at hneg
      linarith
  · -- `k` odd
    obtain ⟨j, hj⟩ := hk2
    have hφeq : φ = θ₀ + (2 * (j : ℝ) * Real.pi + Real.pi) := by
      rw [hθ₀def, hj]; push_cast; ring
    have hval : F φ = -F θ₀ := by rw [hφeq]; exact hval_odd j
    have hder : deriv F φ = -deriv F θ₀ := by rw [hφeq]; exact hder_odd j
    constructor
    · intro hpos
      exfalso
      have h1 : (F φ).re = -(F θ₀).re := by rw [hval, Complex.neg_re]
      rw [h1] at hpos
      linarith
    · intro _
      have hExp : star (F φ + 1) * deriv F φ = star (F θ₀ - 1) * deriv F θ₀ := by
        rw [hval, hder]
        rw [show -F θ₀ + 1 = -(F θ₀ - 1) by ring, star_neg, neg_mul_neg]
      rw [hExp]
      exact hbr

open scoped Manifold ContDiff Topology in
/-- **The chain rule for a complex-valued function of a real variable.** -/
lemma deriv_comp_real_complex (F : ℝ → ℂ) (g : ℝ → ℝ) (w : ℝ)
    (hF : DifferentiableAt ℝ F (g w)) (hg : DifferentiableAt ℝ g w) :
    deriv (fun u : ℝ => F (g u)) w = deriv F (g w) * ((deriv g w : ℝ) : ℂ) := by
  have h1 := (hF.hasFDerivAt).comp_hasDerivAt w hg.hasDerivAt
  have h2 : deriv (fun u : ℝ => F (g u)) w = (fderiv ℝ F (g w)) (deriv g w) := h1.deriv
  rw [h2]
  rw [show deriv g w = (deriv g w) • (1 : ℝ) by simp, ContinuousLinearMap.map_smul,
    fderiv_apply_one_eq_deriv, Complex.real_smul]
  ring

/-- The planar polar curve as a complex-valued function. -/
lemma contDiff_polarF {r : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) :=
  (Complex.ofRealCLM.contDiff.comp hr).mul
    (Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp contDiff_id).mul contDiff_const))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The chain rule through `foot` for the planar picture `proj2 ∘ A`.** -/
lemma mfderiv_proj2A_comp_foot {y : M} {foot : M → M} {A : M → EuclideanSpace ℝ (Fin 3)}
    (hfoot : ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) foot y)
    (hA : ∀ z : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A z)
    (v : TangentSpace (𝓡 2) y) :
    mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ) (fun z : M => proj2 (A (foot z))) y v
      = mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ) (fun z : M => proj2 (A z)) (foot y)
          (mfderiv (𝓡 2) (𝓡 2) foot y v) :=
  mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ))
    (f := foot) (g := fun z : M => proj2 (A z)) (x := y)
    ((Work.Drive.N2Lead.proj2CLM.mdifferentiableAt).comp (foot y)
      ((hA (foot y)).mdifferentiableAt (by simp)))
    (hfoot.mdifferentiableAt (by simp)) v

/-- **The chain rule through `foot` for a real-valued function.** -/
lemma mfderiv_f_comp_foot {y : M} {foot : M → M} {f : M → ℝ}
    (hfoot : ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) foot y)
    (hf : ContMDiffAt (𝓡 2) 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f (foot y))
    (v : TangentSpace (𝓡 2) y) :
    mfderiv (𝓡 2) 𝓘(ℝ,ℝ) (fun z : M => f (foot z)) y v
      = mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (foot y) (mfderiv (𝓡 2) (𝓡 2) foot y v) :=
  mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓘(ℝ,ℝ))
    (f := foot) (g := f) (x := y) (hf.mdifferentiableAt (by simp))
    (hfoot.mdifferentiableAt (by simp)) v

/-- **The rate obstruction, in the form the `ker df`-bricks provide it.**  If `D = l • d` with
`l ≠ 0` and `Im (conj (z - o) · d) ≠ 0`, then `D` is not a real multiple of `z - o`. -/
lemma not_smul_of_im_ne {D z o d : ℂ} {l : ℝ} (hl : l ≠ 0)
    (hD : D = (l : ℂ) * d) (h : (star (z - o) * d).im ≠ 0) :
    ¬ ∃ t : ℝ, D = t • (z - o) := by
  rintro ⟨t, ht⟩
  have h1 : (star (z - o) * D).im = l * (star (z - o) * d).im := by
    rw [hD, show star (z - o) * ((l : ℂ) * d) = (l : ℂ) * (star (z - o) * d) by ring,
      Complex.mul_im]
    simp
  have h2 : (star (z - o) * (t • (z - o))).im = 0 := by
    have hw : ((z - o) * star (z - o)).im = 0 := by
      simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    rw [Complex.real_smul,
      show star (z - o) * ((t : ℂ) * (z - o)) = (t : ℂ) * ((z - o) * star (z - o)) by ring,
      Complex.mul_im, hw]
    simp
  rw [ht, h2] at h1
  exact h (mul_eq_zero.mp h1.symm |>.resolve_left hl)

/-- The same obstruction from a non-radiality statement about `d` itself. -/
lemma not_smul_of_not_smul {D z o d : ℂ} {l : ℝ} (hl : l ≠ 0) (hD : D = (l : ℂ) * d)
    (h : ¬ ∃ t : ℝ, d = t • (z - o)) : ¬ ∃ t : ℝ, D = t • (z - o) := by
  rintro ⟨t, ht⟩
  have h1 : d = ((t : ℂ) * (z - o)) / (l : ℂ) := by
    rw [eq_div_iff (Complex.ofReal_ne_zero.mpr hl), mul_comm d]
    rw [hD] at ht
    exact ht
  refine h ⟨t / l, ?_⟩
  rw [h1, Complex.real_smul, Complex.ofReal_div]
  ring

/-- A value with `Re > 0` and norm `< 17` in the region family must lie in the *right* region of the
marked component. -/
lemma eq_succ_of_mem_of_re_pos {n : ℕ} {i : Fin n} {k : Fin (n + 1)} {z : ℂ}
    (hk : z ∈ upperRegions n i k) (hnorm : ‖z‖ ≤ 15) (h1 : 0 < z.re) : k = i.succ := by
  rcases mem_upperRegions_classify hk with ⟨hk0, hmemL⟩ | ⟨j, hkj, hmemj⟩
  · subst hk0
    rw [mem_upperLeft] at hmemL
    linarith [hmemL.1]
  · rcases hmemj with ⟨hji, hmemR⟩ | ⟨hji, hmemF⟩
    · rw [hkj, hji]
    · rw [Metric.mem_ball, dist_eq_norm] at hmemF
      have h3 : ‖proj2 (farPos n j)‖ - ‖z‖ ≤ ‖proj2 (farPos n j) - z‖ := by
        have h := norm_add_le (proj2 (farPos n j) - z) z
        rw [sub_add_cancel] at h
        linarith
      rw [norm_sub_rev] at h3
      have h4 := norm_proj2_farPos_ge_17 n j
      linarith

/-- A value with `Re < 0` and norm `< 17` in the region family must lie in the *left* region. -/
lemma eq_zero_of_mem_of_re_neg {n : ℕ} {i : Fin n} {k : Fin (n + 1)} {z : ℂ}
    (hk : z ∈ upperRegions n i k) (hnorm : ‖z‖ ≤ 15) (h1 : z.re < 0) : k = 0 := by
  rcases mem_upperRegions_classify hk with ⟨hk0, _⟩ | ⟨j, hkj, hmemj⟩
  · exact hk0
  · rcases hmemj with ⟨hji, hmemR⟩ | ⟨hji, hmemF⟩
    · rw [mem_upperRight] at hmemR
      linarith [hmemR.1]
    · rw [Metric.mem_ball, dist_eq_norm] at hmemF
      have h3 : ‖proj2 (farPos n j)‖ - ‖z‖ ≤ ‖proj2 (farPos n j) - z‖ := by
        have h := norm_add_le (proj2 (farPos n j) - z) z
        rw [sub_add_cancel] at h
        linarith
      rw [norm_sub_rev] at h3
      have h4 := norm_proj2_farPos_ge_17 n j
      linarith

/-- A value in the far disc of the component `j ≠ i` occupies the region of index `j.succ`. -/
lemma eq_succ_of_mem_farDisc {n : ℕ} {i : Fin n} {j : Fin n} {k : Fin (n + 1)} {z : ℂ}
    (hji : j ≠ i) (hk : z ∈ upperRegions n i k)
    (hmem : z ∈ Metric.ball (proj2 (farPos n j)) 2) : k = j.succ := by
  rcases mem_upperRegions_classify hk with ⟨hk0, hmemL⟩ | ⟨j', hkj', hmemj'⟩
  · subst hk0
    rw [mem_upperLeft] at hmemL
    rw [Metric.mem_ball, dist_eq_norm] at hmem
    have h3 : ‖proj2 (farPos n j)‖ - ‖z‖ ≤ ‖proj2 (farPos n j) - z‖ := by
      have h := norm_add_le (proj2 (farPos n j) - z) z
      rw [sub_add_cancel] at h
      linarith
    rw [norm_sub_rev] at h3
    have h4 := norm_proj2_farPos_ge_17 n j
    linarith
  · rcases hmemj' with ⟨hj'i, hmemR⟩ | ⟨hj'i, hmemF⟩
    · rw [mem_upperRight] at hmemR
      rw [Metric.mem_ball, dist_eq_norm] at hmem
      have h3 : ‖proj2 (farPos n j)‖ - ‖z‖ ≤ ‖proj2 (farPos n j) - z‖ := by
        have h := norm_add_le (proj2 (farPos n j) - z) z
        rw [sub_add_cancel] at h
        linarith
      rw [norm_sub_rev] at h3
      have h4 := norm_proj2_farPos_ge_17 n j
      linarith
    · -- two far discs
      refine hkj'.trans ?_
      congr 1
      by_contra hne
      have hd := disjoint_far_far (n := n) hne
      rw [Set.disjoint_left] at hd
      exact hd hmemF hmem

/-- Shifts of a `LevelCurves` parametrisation by an integer. -/
lemma levelCurves_shift {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f b n)
    (i : Fin n) (k : ℤ) (x : ℝ) : L.γ i (x + k) = L.γ i x := by
  have hper : Function.Periodic (L.γ i) 1 := L.per i
  have := hper.int_mul k
  simpa using this x

/-- The norm of the model arc is `< 5` on `|w| ≤ m ≤ 2`, `η < 1/10`. -/
lemma norm_arcZ_lt_five {η m w : ℝ} (hη0 : 0 < η) (hη : η < 1 / 10) (hm1 : 1 < m)
    (hm2 : m ≤ 2) (hw : |w| ≤ m) :
    ‖arcZ η w‖ < 5 := by
  have h1 : ‖arcZ η w‖ ^ 2 = Real.sqrt (η ^ 2 + w ^ 2) := by
    rw [Complex.sq_norm, normSq_arcZ]
  have h2 : Real.sqrt (η ^ 2 + w ^ 2) ≤ Real.sqrt (η ^ 2 + m ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [abs_le.mp hw, sq_abs w, sq_nonneg w]
  have h3 : Real.sqrt (η ^ 2 + m ^ 2) < 25 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 25)]
    nlinarith [sq_nonneg η, sq_nonneg m, hη, hη0, hm1, hm2]
  nlinarith [norm_nonneg (arcZ η w), h1, h2, h3]

/-- The imaginary part of a (`cE3`-)image is the second coordinate, which vanishes. -/
lemma cE3_apply_two_eq_zero (z : ℂ) : (Work.Drive.N2.cE3 z) 2 = 0 :=
  Work.Drive.N2.cE3_apply_two z

/-- The model arc never equals `1` (for `η > 0`). -/
lemma arcZ_ne_one {η : ℝ} (hη : 0 < η) (w : ℝ) : arcZ η w ≠ 1 := by
  intro h
  have h2 : -(η : ℂ) + (w : ℂ) * Complex.I = 1 := by
    rw [← Work.Drive.N2Lead.arcZ_sq, h]
    norm_num
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp at him hre
  linarith

/-- The model arc never equals `-1` (for `η > 0`). -/
lemma arcZ_ne_neg_one {η : ℝ} (hη : 0 < η) (w : ℝ) : arcZ η w ≠ -1 := by
  intro h
  have h2 : -(η : ℂ) + (w : ℂ) * Complex.I = 1 := by
    rw [← Work.Drive.N2Lead.arcZ_sq, h]
    norm_num
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp at him hre
  linarith

/-- Integer shifts of a `π`-periodic function. -/
lemma r_pi_int {r : ℝ → ℝ} (hrpi : ∀ φ : ℝ, r (φ + Real.pi) = r φ) (φ : ℝ) (k : ℤ) :
    r (φ + (k : ℝ) * Real.pi) = r φ := by
  have hnat : ∀ (n : ℕ) (y : ℝ), r (y + (n : ℝ) * Real.pi) = r y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      have h1 : y + ((m + 1 : ℕ) : ℝ) * Real.pi
          = (y + (m : ℝ) * Real.pi) + Real.pi := by push_cast; ring
      rw [h1, hrpi, ih]
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
  · subst hn; simpa using hnat n φ
  · subst hn
    have h1 := hnat n (φ + -(n : ℝ) * Real.pi)
    have h2 : φ + -(n : ℝ) * Real.pi + (n : ℝ) * Real.pi = φ := by ring
    rw [h2] at h1
    have h3 : r φ = r (φ + -(n : ℝ) * Real.pi) := h1
    rw [h3]
    congr 1
    push_cast
    ring

/-- Two indices of `Fin n` with `|5 (j - j₀)| ≤ 1` are equal (the parking spots are `5` apart). -/
lemma fin_eq_of_abs_five_le {n : ℕ} {j j₀ : Fin n}
    (h : |(5 : ℝ) * (((j : ℕ) : ℝ) - ((j₀ : ℕ) : ℝ))| ≤ 1) : j = j₀ := by
  apply Fin.ext
  have h1 : |((j : ℤ) : ℝ) - ((j₀ : ℤ) : ℝ)| ≤ 1 / 5 := by
    have h2 : |((j : ℤ) : ℝ) - ((j₀ : ℤ) : ℝ)|
        = |(5 : ℝ) * (((j : ℕ) : ℝ) - ((j₀ : ℕ) : ℝ))| / 5 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
      field_simp
      push_cast
      ring
    rw [h2, div_le_iff₀ (by norm_num : (0 : ℝ) < 5)]
    linarith
  have h3 : (j : ℤ) = (j₀ : ℤ) := by
    by_contra hne
    have h5 : (1 : ℤ) ≤ |(j : ℤ) - (j₀ : ℤ)| :=
      Int.one_le_abs (sub_ne_zero.mpr hne)
    have h6 : (1 : ℝ) ≤ ((|(j : ℤ) - (j₀ : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h5
    have h7 : ((|(j : ℤ) - (j₀ : ℤ)| : ℤ) : ℝ)
        = |((j : ℤ) : ℝ) - ((j₀ : ℤ) : ℝ)| := by
      rw [Int.cast_abs]
      push_cast
      ring
    rw [h7] at h6
    linarith
  exact_mod_cast h3

end
open scoped Manifold ContDiff Topology in
/-- **§4.3: the upper certificate of the saddle window.**  The two-piece drawing
`saddleWindowDrawing η δ c₀ U Z A foot` (the engine's `W`) is certified at the upper level
`c + lam * η`.

The proof decomposes every level-`u⁺` point:

* `y ∈ saddleRegion U Z c₀`: the model rows (`upperRegionMem`, `upperRegionRate{,Neg}`);
* `y ∉ saddleRegion`: `W y = A (foot y)` with `foot y` on the anchor level `c - lam η`; `foot y` is
  a parked circle (region `ball (proj2 (farPos n j)) 2`) or, on the marked component, is split by
  `arcRangeOrBridgeZone` into the pinned arcs (`A (L.γ i (τU w)) = cE3 (arcZ η w)`, rate
  `modelArcCross_absLe`) and the bridge (`polarBridgeRate` and its odd mirror). -/
theorem isCertifiedAt_upper_saddleWindow {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {c η δ c₀ lam ηb m R C₀ : ℝ} {U : Set M} {Z : M → ℂ}
    {foot : M → M} {A : M → EuclideanSpace ℝ (Fin 3)} {θ : M → ℝ}
    {n : ℕ} {L : Work.Drive.N2C.LevelCurves f (c - lam * η) n} {i : Fin n}
    {r Θ τU τL : ℝ → ℝ}
    (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hlam : 0 < lam)
    (hc₀ : 2 - 2 * δ < c₀) (hc₀' : c₀ < 2) (hηb : η < ηb)
    (hU : IsOpen U)
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z U)
    (hZimm : ∀ x ∈ U, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x))
    (hlev : ∀ x ∈ U, f x = c + lam * ((Z x) ^ 2).re)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c + lam * η → ¬ Work.Drive.Morse.IsCritical f x)
    (hfoot : ∀ x : M, ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) foot x)
    (hfootinj : ∀ x y : M, f x = f y → foot x = foot y → x = y)
    (hfootimm : ∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 2) foot x v = 0 → v = 0)
    (hfootval : ∀ y : M, y ∉ Work.Drive.N2.saddleRegion U Z c₀ →
      f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → f (foot y) = c - lam * η)
    (hlandFr : ∀ x : M, x ∈ frontier (Work.Drive.N2.saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → ∀ᶠ y in 𝓝 x, f (foot y) = c - lam * η)
    (hfront : ∀ x : M, x ∈ frontier (Work.Drive.N2.saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      (fun y : M => Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z y))) =ᶠ[𝓝 x]
        (fun y : M => A (foot y)))
    (hbig : ∀ x : M, x ∉ Work.Drive.N2.saddleRegion U Z c₀ →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → θ (foot x) = 1 →
      c₀ ≤ |((Z (foot x)) ^ 2).im|)
    (hθ01 : ∀ x : M, 0 ≤ θ x ∧ θ x ≤ 1)
    (hAsm : ∀ x : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A x)
    (hAoff : ∀ x : M, f x = c - lam * η → θ x < 1 →
      (A x) 2 ≠ 0 ∨ c₀ + 2 * η < ‖A x‖ ^ 2)
    (hAcurve : ∀ (j : Fin n) (t : ℝ), A (L.γ j t) =
      if j = i then polarCurve r Θ t else farCurve n j t)
    (hZu : ∀ w ∈ Set.Icc (-m) m, Z (L.γ i (τU w)) = arcZ η w)
    (hZd : ∀ w ∈ Set.Icc (-m) m, Z (L.γ i (τL w)) = -arcZ η w)
    (hau : ∀ w ∈ Set.Icc (-m) m, A (L.γ i (τU w)) = Work.Drive.N2.cE3 (arcZ η w))
    (hal : ∀ w ∈ Set.Icc (-m) m, A (L.γ i (τL w)) = Work.Drive.N2.cE3 (-arcZ η w))
    (hΘu : ∀ w ∈ Set.Icc (-m) m, Θ (τU w) = Real.pi / 2 - (1 / 2) * Real.arctan (w / η))
    (hΘl : ∀ w ∈ Set.Icc (-m) m, Θ (τL w) = -(Real.pi / 2) - (1 / 2) * Real.arctan (w / η))
    (hτu : ∀ w ∈ Set.Ioo (-m) m, DifferentiableAt ℝ τU w ∧ deriv τU w ≠ 0)
    (hτl : ∀ w ∈ Set.Ioo (-m) m, DifferentiableAt ℝ τL w ∧ deriv τL w ≠ 0)
    (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ)
    (hrpi : ∀ φ : ℝ, r (φ + Real.pi) = r φ) (hrev : ∀ φ : ℝ, r (-φ) = r φ)
    (hlo : ∀ φ ∈ Set.Icc (0 : ℝ) (mobiusPhiE η m), Real.sqrt (η ^ 2 + m ^ 2) ≤ r φ ^ 2)
    (hmono : ∀ φ ∈ Set.Icc (0 : ℝ) (mobiusPhiE η m), deriv r φ ≤ 0)
    (hbR : ∀ φ : ℝ, (∃ k : ℤ, |φ - k * Real.pi| ≤ mobiusPhiE η m) → r φ ≤ R)
    (hR : R < 5) (hm : 1 < m) (hm2 : m ≤ 2)
    (hnum : c₀ + 2 * η < Real.sqrt (η ^ 2 + m ^ 2))
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (hΘmono : StrictMono Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0) (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 8 * C₀ * η ≤ δ)
    (hW : Work.Drive.N2.GoodDrawingOn f (Set.Ioo (c - lam * ηb) (c + lam * ηb))
      (saddleWindowDrawing η δ c₀ U Z A foot)) :
    Work.Drive.N2C.IsCertifiedAt f (c + lam * η) (saddleWindowDrawing η δ c₀ U Z A foot) := by
  classical
  have hδ₂ : δ < 1 / 2 := by linarith
  have hc₀₂ : c₀ ≤ 2 := le_of_lt hc₀'
  have hφElt : Work.Drive.N2Lead.mobiusPhiE η m < Real.pi / 2 :=
    (leadProfile_phiE hη (by linarith : 0 < m)).2.2
  set D : Set M := Work.Drive.N2.saddleRegion U Z c₀ with hDdef
  set W : M → EuclideanSpace ℝ (Fin 3) := saddleWindowDrawing η δ c₀ U Z A foot with hWdef
  have hDopen : IsOpen D := by rw [hDdef]; exact Work.Drive.N2.isOpen_saddleRegion hU hZsm
  have hηb' : c + lam * η ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) :=
    ⟨by nlinarith [hη, hηb], by nlinarith [hη, hηb]⟩
  -- the level isotopy of the constant family
  have hiso : Work.Drive.N2C.IsLevelIsotopy f (c + lam * η) (fun _ : ℝ => W) := by
    refine ⟨?_, ?_, ?_⟩
    · intro s z hz
      have hcomp : (fun p : ℝ × M => W p.2) = W ∘ Prod.snd := rfl
      rw [hcomp]
      exact ContMDiffAt.comp (s, z) (hW.1 z (by rw [hz]; exact hηb')) contMDiffAt_snd
    · intro s x y hx hy
      exact hW.2.2 x y (by rw [hx]; exact hηb') (by rw [hy]; exact hηb') (by rw [hx, hy])
    · intro s z hz v hv
      exact hW.2.1 z (by rw [hz]; exact hηb') v hv
  have hbrlo : ∀ φ : ℝ, (∃ kk : ℤ, |φ - (kk : ℝ) * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE η m) →
      Real.sqrt (η ^ 2 + m ^ 2) ≤ r φ ^ 2 := by
    intro φ hφ
    obtain ⟨kk, hk⟩ := hφ
    have hval : r φ = r (φ - (kk : ℝ) * Real.pi) := by
      have h1 : r (φ - (kk : ℝ) * Real.pi + (kk : ℝ) * Real.pi)
          = r (φ - (kk : ℝ) * Real.pi) :=
        r_pi_int hrpi (φ - (kk : ℝ) * Real.pi) kk
      have h2 : φ - (kk : ℝ) * Real.pi + (kk : ℝ) * Real.pi = φ := by ring
      rwa [h2] at h1
    rw [hval]
    rcases abs_le.mp hk with ⟨hlo', hhi'⟩
    by_cases hpos : 0 ≤ φ - (kk : ℝ) * Real.pi
    · exact hlo _ ⟨hpos, hhi'⟩
    · rw [← hrev (φ - (kk : ℝ) * Real.pi)]
      exact hlo _ ⟨by linarith, by linarith⟩
  refine Work.Drive.N2Lead.isCertifiedAt_of_starRegions hf hreg hiso (upperRegions n i)
    (upperCentres n i) (fun _ => 1 / 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k
    exact isOpen_convex_upperRegions n i k
  · intro k
    norm_num
  · intro k
    exact closedBall_subset_upperRegions n i k
  · exact pairwiseDisjoint_upperRegions n i
  · -- ## `hin`
    intro y hy
    by_cases hyD : y ∈ D
    · have hmem := Work.Drive.N2Lead.upperRegionMem (η := η) (δ := δ) (c := c) (c₀ := c₀)
        (lam := lam) (U := U) (Z := Z) (y := y) hlev (ne_of_gt hlam) hη hη' hδ hδ₂ hc₀₂
        hyD.1 hyD.2 hy
      obtain ⟨hsign, hnorm⟩ := hmem
      have hWy : proj2 (W y) = Work.Drive.N2.saddlePsi η δ (Z y) := by
        rw [hWdef, saddleWindowDrawing_of_mem hyD, proj2_cE3]
      rw [hWy]
      rcases hsign with hpos | hneg
      · exact ⟨i.succ, by rw [upperRegions_succ_self]; exact ⟨hpos, hnorm⟩⟩
      · exact ⟨0, by rw [upperRegions_zero]; exact ⟨hneg, hnorm⟩⟩
    · have hyb : f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) := by
        rw [hy]; exact hηb'
      have hland : f (foot y) = c - lam * η := hfootval y hyD hyb
      obtain ⟨j, t, hjt⟩ := L.cover (foot y) hland
      have hWy : W y = A (foot y) := by rw [hWdef, saddleWindowDrawing_of_notMem hyD]
      rw [hWy, hjt, hAcurve j t]
      by_cases hji : j = i
      · rw [if_pos hji]
        rcases arcRangeOrBridgeZone hη hm hΘmono hΘper hΘu hΘl t with
          ⟨w, hw, k', hkt⟩ | ⟨w, hw, k', hkt⟩ | ⟨k', hkr⟩
        · -- upper pinned arc
          have hfoot' : foot y = L.γ i (τU w + k') := by rw [hjt, hkt, hji]
          have hwIcc : w ∈ Set.Icc (-m) m := Set.Ioo_subset_Icc_self hw
          rw [hkt]
          have hwne : w ≠ 0 := by
            intro hw0
            have hZeq : Z (foot y) = arcZ η w := by
              rw [hfoot', levelCurves_shift L i k' (τU w), hZu w hwIcc]
            have him0 : ((Z (foot y)) ^ 2).im = 0 := by rw [hZeq, arcZ_sq_im, hw0]
            by_cases hθ : θ (foot y) = 1
            · have h1 := hbig y hyD hyb hθ
              rw [him0] at h1
              simp at h1
              linarith [hc₀, hδ]
            · have hθlt : θ (foot y) < 1 := lt_of_le_of_ne (hθ01 (foot y)).2 hθ
              have h2 := hAoff (foot y) hland hθlt
              have hAval : A (foot y) = Work.Drive.N2.cE3 (arcZ η w) := by
                rw [hfoot', levelCurves_shift L i k' (τU w), hau w hwIcc]
              rcases h2 with h2 | h2
              · rw [hAval, cE3_apply_two_eq_zero] at h2
                exact absurd rfl h2
              · have hnorm2 : ‖A (foot y)‖ ^ 2 = Real.sqrt (η ^ 2 + w ^ 2) := by
                  rw [hAval, norm_cE3_eq, Complex.sq_norm, normSq_arcZ]
                rw [hw0] at hnorm2
                rw [hnorm2] at h2
                have h3 : Real.sqrt (η ^ 2 + (0:ℝ) ^ 2) = η := by
                  rw [show η ^ 2 + (0:ℝ) ^ 2 = η ^ 2 by ring, Real.sqrt_sq_eq_abs,
                    abs_of_pos hη]
                rw [h3] at h2
                linarith [hc₀, hδ]
          have hAc : A (L.γ i (τU w)) = polarCurve r Θ (τU w) := by
            rw [hAcurve i (τU w), if_pos rfl]
          have hpolval : proj2 (polarCurve r Θ (τU w + k')) = arcZ η w := by
            rw [polarCurve_add_int hrper hΘper k' (τU w), ← hAc, hau w hwIcc, proj2_cE3]
          rw [hpolval]
          have hre : (arcZ η w).re ≠ 0 := re_arcZ_ne_zero_iff hwne
          have hn5 : ‖arcZ η w‖ < 5 :=
            norm_arcZ_lt_five hη hη' hm hm2 (le_of_lt (abs_lt.mpr ⟨hw.1, hw.2⟩))
          rcases lt_or_gt_of_ne hre with hneg | hpos
          · exact ⟨0, by rw [upperRegions_zero]; exact ⟨hneg, hn5⟩⟩
          · exact ⟨i.succ, by rw [upperRegions_succ_self]; exact ⟨hpos, hn5⟩⟩
        · -- lower pinned arc
          have hfoot' : foot y = L.γ i (τL w + k') := by rw [hjt, hkt, hji]
          have hwIcc : w ∈ Set.Icc (-m) m := Set.Ioo_subset_Icc_self hw
          rw [hkt]
          have hwne : w ≠ 0 := by
            intro hw0
            have hZeq : Z (foot y) = -arcZ η w := by
              rw [hfoot', levelCurves_shift L i k' (τL w), hZd w hwIcc]
            have him0 : ((Z (foot y)) ^ 2).im = 0 := by
              rw [hZeq, show (-arcZ η w) ^ 2 = (arcZ η w) ^ 2 by ring, arcZ_sq_im, hw0]
            by_cases hθ : θ (foot y) = 1
            · have h1 := hbig y hyD hyb hθ
              rw [him0] at h1
              simp at h1
              linarith [hc₀, hδ]
            · have hθlt : θ (foot y) < 1 := lt_of_le_of_ne (hθ01 (foot y)).2 hθ
              have h2 := hAoff (foot y) hland hθlt
              have hAval : A (foot y) = Work.Drive.N2.cE3 (-arcZ η w) := by
                rw [hfoot', levelCurves_shift L i k' (τL w), hal w hwIcc]
              rcases h2 with h2 | h2
              · rw [hAval, cE3_apply_two_eq_zero] at h2
                exact absurd rfl h2
              · have hnorm2 : ‖A (foot y)‖ ^ 2 = Real.sqrt (η ^ 2 + w ^ 2) := by
                  rw [hAval, norm_cE3_eq, Complex.sq_norm, Complex.normSq_neg, normSq_arcZ]
                rw [hw0] at hnorm2
                rw [hnorm2] at h2
                have h3 : Real.sqrt (η ^ 2 + (0:ℝ) ^ 2) = η := by
                  rw [show η ^ 2 + (0:ℝ) ^ 2 = η ^ 2 by ring, Real.sqrt_sq_eq_abs,
                    abs_of_pos hη]
                rw [h3] at h2
                linarith [hc₀, hδ]
          have hAc : A (L.γ i (τL w)) = polarCurve r Θ (τL w) := by
            rw [hAcurve i (τL w), if_pos rfl]
          have hpolval : proj2 (polarCurve r Θ (τL w + k')) = -arcZ η w := by
            rw [polarCurve_add_int hrper hΘper k' (τL w), ← hAc, hal w hwIcc, proj2_cE3]
          rw [hpolval]
          have hre : (arcZ η w).re ≠ 0 := re_arcZ_ne_zero_iff hwne
          have hn5 : ‖arcZ η w‖ < 5 :=
            norm_arcZ_lt_five hη hη' hm hm2 (le_of_lt (abs_lt.mpr ⟨hw.1, hw.2⟩))
          rcases lt_or_gt_of_ne hre with hneg | hpos
          · refine ⟨i.succ, ?_⟩
            rw [upperRegions_succ_self]
            exact ⟨by rw [Complex.neg_re]; linarith, by simpa using hn5⟩
          · refine ⟨0, ?_⟩
            rw [upperRegions_zero]
            exact ⟨by rw [Complex.neg_re]; linarith, by simpa using hn5⟩
        · -- bridge zone
          have hval : proj2 (polarCurve r Θ t) = (r (Θ t) : ℂ)
              * Complex.exp ((Θ t : ℂ) * Complex.I) := proj2_polarCurve r Θ t
          rw [hval]
          set z : ℂ := (r (Θ t) : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I) with hzdef
          have hzre : z.re = r (Θ t) * Real.cos (Θ t) := by
            rw [hzdef, Complex.mul_re]
            have hre : (Complex.exp ((Θ t : ℂ) * Complex.I)).re = Real.cos (Θ t) := by
              rw [Complex.exp_ofReal_mul_I]; simp [Complex.cos_ofReal_re]
            rw [hre]
            simp
          have hzre_ne : z.re ≠ 0 := by
            rw [hzre]
            refine mul_ne_zero (ne_of_gt (hrpos (Θ t))) ?_
            intro h0
            obtain ⟨k2, hk2⟩ := Real.cos_eq_zero_iff.mp h0
            have h2 : Θ t = (2 * (k2 : ℝ) + 1) * Real.pi / 2 := hk2
            have h3 : Θ t - (k' : ℝ) * Real.pi
                = (2 * ((k2 : ℝ) - k') + 1) * (Real.pi / 2) := by
              rw [h2]; ring
            have h4 : (2 * ((k2 : ℝ) - k') + 1) ≠ 0 := by
              intro hh
              have h2z : ((2 * (k2 - k') + 1 : ℤ) : ℝ) = 0 := by
                push_cast
                linarith
              have h3z : (2 * (k2 - k') + 1 : ℤ) = 0 := by exact_mod_cast h2z
              omega
            have h5 : (1 : ℝ) ≤ |(2 * ((k2 : ℝ) - k') + 1)| := by
              have hcast : ((2 * (k2 - k') + 1 : ℤ) : ℝ) = 2 * ((k2 : ℝ) - k') + 1 := by
                push_cast; ring
              rw [← hcast]
              exact_mod_cast Int.one_le_abs (by omega : (2 * (k2 - k') + 1 : ℤ) ≠ 0)
            have hk1 : |Θ t - (k' : ℝ) * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE η m := hkr
            rw [h3, abs_mul, abs_of_pos (by positivity : (0:ℝ) < Real.pi / 2)] at hk1
            have h7 : Real.pi / 2 ≤ |(2 * ((k2 : ℝ) - k') + 1)| * (Real.pi / 2) := by
              nlinarith [Real.pi_pos]
            linarith [hφElt]
          have hznorm : ‖z‖ ≤ R := by
            have h1 : ((Θ t : ℂ) * Complex.I).re = 0 := by simp
            have h2 : ‖(r (Θ t) : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I)‖ = r (Θ t) := by
              rw [norm_mul, Complex.norm_exp, h1, Real.exp_zero, mul_one]
              simp [abs_of_pos (hrpos (Θ t))]
            rw [hzdef, h2]
            exact hbR (Θ t) ⟨k', hkr⟩
          have hn5 : ‖z‖ < 5 := lt_of_le_of_lt hznorm hR
          rcases lt_or_gt_of_ne hzre_ne with hneg | hpos
          · exact ⟨0, by rw [upperRegions_zero]; exact ⟨hneg, hn5⟩⟩
          · exact ⟨i.succ, by rw [upperRegions_succ_self]; exact ⟨hpos, hn5⟩⟩
      · -- another component: a parked circle
        rw [if_neg hji]
        have hval : proj2 (farCurve n j t) = proj2 (farPos n j) + proj2 (Work.Drive.N2.ang t) :=
          proj2_farCurve n j t
        rw [hval]
        refine ⟨j.succ, ?_⟩
        rw [upperRegions_succ_of_ne hji, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        rw [norm_proj2_ang]
        norm_num
  · -- ## `hrate`
    intro y k hy hmem
    by_cases hyD : y ∈ D
    · -- ### the model region
      obtain ⟨hsign, hnorm5⟩ := Work.Drive.N2Lead.upperRegionMem (η := η) (δ := δ) (c := c)
        (c₀ := c₀) (lam := lam) (U := U) (Z := Z) (y := y) hlev (ne_of_gt hlam) hη hη'
        hδ hδ₂ hc₀₂ hyD.1 hyD.2 hy
      have hWy : proj2 (W y) = Work.Drive.N2.saddlePsi η δ (Z y) := by
        rw [hWdef, saddleWindowDrawing_of_mem hyD, proj2_cE3]
      have hev : (fun z : M => proj2 (W z))
          =ᶠ[𝓝 y] (fun z : M => (Work.Drive.N2.saddlePsi η δ (Z z) : ℂ)) := by
        filter_upwards [IsOpen.mem_nhds hDopen hyD] with z hz
        rw [hWdef, saddleWindowDrawing_of_mem hz, proj2_cE3]
      rw [hWy] at hmem ⊢
      have hsq_ne : (Work.Drive.N2.saddlePsi η δ (Z y)) ^ 2 ≠ 1 := by
        intro h1
        have hδh : (0 : ℝ) < 2 - 4 * δ := by linarith
        have h2 : Work.Drive.N2.saddlePhi η δ ((Z y) ^ 2) = 1 := by
          rw [← Work.Drive.N2.saddlePsi_sq hδ hδh.le (Z y), h1]
        have h3 : ((Z y) ^ 2).im = 0 := by
          have h := congrArg Complex.im h2
          rw [Work.Drive.N2.saddlePhi_im] at h
          simpa using h
        have h4 : ((Z y) ^ 2).re = η := by
          have h := hlev y hyD.1
          rw [hy] at h
          exact mul_left_cancel₀ (ne_of_gt hlam) (by linarith)
        have hm0 : Work.Drive.N2.saddleM δ (0 : ℝ) = 0 :=
          Work.Drive.N2Lead.saddleM_zero_of_lt_half hδ hδ₂
        have h5 : (Work.Drive.N2.saddlePhi η δ ((Z y) ^ 2)).re = η := by
          rw [Work.Drive.N2.saddlePhi_re, Work.Drive.N2.saddleSigma_apply, h3, h4, hm0]
          ring
        have h6 := congrArg Complex.re h2
        rw [h5] at h6
        have h7 : η = 1 := by simpa using h6
        linarith [hη']
      rcases mem_upperRegions_classify hmem with ⟨hk0, hmemL⟩ | ⟨j, hkj, hmemj⟩
      · -- left region, centre `-1`
        have hneg : (Work.Drive.N2.saddlePsi η δ (Z y)).re < 0 := hmemL.1
        refine ⟨?_, ?_⟩
        · rw [hk0, upperCentres_zero]
          exact fun hcon => hsq_ne (by rw [hcon]; norm_num)
        · intro v hv hvne hEx
          obtain ⟨s, hs⟩ := hEx
          have hrow := Work.Drive.N2Lead.upperRegionRateNeg (v := v) (hU := hU) (hZsm := hZsm)
            (hZimm := hZimm) (hlev := hlev) (hlam := ne_of_gt hlam) hη hη' hδ hδ' hc₀₂ hC₀
            hsmall hyD.1 hyD.2 hy hneg hv hvne
          refine hrow.2 ⟨s, ?_⟩
          have hmf : mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => proj2 (W z)) y
              = mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
                  (fun z : M => (Work.Drive.N2.saddlePsi η δ (Z z) : ℂ)) y := hev.mfderiv_eq_v433
          rw [hmf, hk0, upperCentres_zero] at hs
          exact hs
      · rcases hmemj with ⟨hj2i, hmemR⟩ | ⟨hj2i, hmemF⟩
        · -- right region, centre `1`
          have hpos : 0 < (Work.Drive.N2.saddlePsi η δ (Z y)).re := hmemR.1
          refine ⟨?_, ?_⟩
          · rw [hkj, hj2i, upperCentres_succ_self]
            exact fun hcon => hsq_ne (by rw [hcon]; norm_num)
          · intro v hv hvne hEx
            obtain ⟨s, hs⟩ := hEx
            have hrow := Work.Drive.N2Lead.upperRegionRate (v := v) (hU := hU) (hZsm := hZsm)
              (hZimm := hZimm) (hlev := hlev) (hlam := ne_of_gt hlam) hη hη' hδ hδ' hc₀₂ hC₀
              hsmall hyD.1 hyD.2 hy hpos hv hvne
            refine hrow.2 ⟨s, ?_⟩
            have hmf : mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => proj2 (W z)) y
                = mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
                    (fun z : M => (Work.Drive.N2.saddlePsi η δ (Z z) : ℂ)) y := hev.mfderiv_eq_v433
            rw [hmf, hkj, hj2i, upperCentres_succ_self] at hs
            exact hs
        · -- a model value of norm `< 2` cannot lie in a far disc
          exfalso
          rw [Metric.mem_ball, dist_eq_norm] at hmemF
          have h3 : ‖proj2 (farPos n j)‖ - ‖Work.Drive.N2.saddlePsi η δ (Z y)‖
              ≤ ‖proj2 (farPos n j) - Work.Drive.N2.saddlePsi η δ (Z y)‖ := by
            have h := norm_add_le (proj2 (farPos n j) - Work.Drive.N2.saddlePsi η δ (Z y))
              (Work.Drive.N2.saddlePsi η δ (Z y))
            rw [sub_add_cancel] at h
            linarith
          rw [norm_sub_rev] at h3
          have h4 := norm_proj2_farPos_ge_17 n j
          linarith [hnorm5]
    · -- ### off the model region: the drawing is `A ∘ foot`
      have hyb : f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) := by rw [hy]; exact hηb'
      have hland : f (foot y) = c - lam * η := hfootval y hyD hyb
      obtain ⟨j, t, hjt⟩ := L.cover (foot y) hland
      have hWy : W y = A (foot y) := by rw [hWdef, saddleWindowDrawing_of_notMem hyD]
      have hycl_or_fr : y ∈ frontier D ∨ y ∉ closure D := by
        by_cases hfr : y ∈ frontier D
        · exact Or.inl hfr
        · refine Or.inr fun hcl => hfr ?_
          rw [frontier_eq_closure_inter_closure]
          refine ⟨hcl, ?_⟩
          rw [IsClosed.closure_eq (isClosed_compl_iff.mpr hDopen)]
          exact hyD
      have hevland : (fun z : M => f (foot z)) =ᶠ[𝓝 y] (fun _ : M => c - lam * η) := by
        rcases hycl_or_fr with hfr | hcl
        · exact hlandFr y hfr hyb
        · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl,
            hf.continuous.continuousAt (isOpen_Ioo.mem_nhds hyb)] with z hzcl hzf
          exact hfootval z (fun hzD => hzcl (subset_closure hzD)) hzf
      have hWev : (fun z : M => W z) =ᶠ[𝓝 y] (fun z : M => A (foot z)) := by
        rcases hycl_or_fr with hfr | hcl
        · filter_upwards [hfront y hfr hyb] with z hzf
          by_cases hzD : z ∈ D
          · rw [hWdef, saddleWindowDrawing_of_mem hzD]
            exact hzf
          · rw [hWdef, saddleWindowDrawing_of_notMem hzD]
        · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl] with z hzcl
          rw [hWdef, saddleWindowDrawing_of_notMem (fun hzD => hzcl (subset_closure hzD))]
      have hWmj : ∀ v : TangentSpace (𝓡 2) y,
          mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ) (fun z : M => proj2 (W z)) y v
            = mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ)
                (fun z : M => proj2 (A (foot z))) y v := by
        intro v
        have h1 : (fun z : M => proj2 (W z)) =ᶠ[𝓝 y] (fun z : M => proj2 (A (foot z))) := by
          filter_upwards [hWev] with z hz
          rw [hz]
        exact DFunLike.congr_fun h1.mfderiv_eq_v433 v
      have hAchain : ∀ v : TangentSpace (𝓡 2) y,
          mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ) (fun z : M => proj2 (A (foot z))) y v
            = mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ) (fun z : M => proj2 (A z)) (foot y)
                (mfderiv (𝓡 2) (𝓡 2) foot y v) :=
        fun v => mfderiv_proj2A_comp_foot (hfoot y) hAsm v
      have hfootker : ∀ v : TangentSpace (𝓡 2) y, mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f y v = 0 →
          mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (foot y) (mfderiv (𝓡 2) (𝓡 2) foot y v) = 0 := by
        intro v _
        have h0 : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) (fun z : M => f (foot z)) y v = 0 := by
          have hc : (fun z : M => f (foot z)) =ᶠ[𝓝 y] (fun _ : M => f (foot y)) := by
            filter_upwards [hevland] with z hz
            rw [hz, hland]
          rw [hc.mfderiv_eq_v433, mfderiv_const]
          simp
        rw [mfderiv_f_comp_foot (hfoot y) (hf.contMDiffAt) v] at h0
        exact h0
      -- the value of `A (foot y)` and its component
      rw [hWy, hjt, hAcurve j t] at hmem ⊢
      -- the component parameter of the tangent vector, from `L.ker`
      have hkomp : ∀ v : TangentSpace (𝓡 2) y, mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f y v = 0 →
          ∃ s₀ : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ j) t s₀ = mfderiv (𝓡 2) (𝓡 2) foot y v :=
        fun v hv => L.ker j t (mfderiv (𝓡 2) (𝓡 2) foot y v)
          (by rw [← hjt]; exact hfootker v hv)
      -- the derivative of `proj2 ∘ W` along a level-component
      have hder : ∀ (v : TangentSpace (𝓡 2) y) (s₀ : ℝ),
          mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f y v = 0 →
          mfderiv (𝓡 2) (𝓡 2) foot y v = mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ j) t s₀ →
          mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => proj2 (W z)) y v
            = deriv (fun u : ℝ => proj2 (A (L.γ j u))) t * (s₀ : ℂ) := by
        intro v s₀ hv hs₀
        rw [hWmj v, hAchain v]
        have h1 : mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ) (fun z : M => proj2 (A z))
            (foot y) (mfderiv (𝓡 2) (𝓡 2) foot y v)
            = mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ) (fun z : M => proj2 (A z))
                (L.γ j t) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ j) t s₀) := by
          rw [hs₀, hjt]
        rw [h1]
        exact Work.Drive.N2Lead.mfderiv_levelCurve_eq_deriv L
          (fun z _ => hAsm z) (fun j' u' => rfl) j t s₀
      -- the tangent over the component is nonzero
      have hsne : ∀ (v : TangentSpace (𝓡 2) y) (s₀ : ℝ),
          mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f y v = 0 → v ≠ 0 →
          mfderiv (𝓡 2) (𝓡 2) foot y v = mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ j) t s₀ → s₀ ≠ 0 := by
        intro v s₀ hv hvne hs₀ h0
        refine hvne (hfootimm y v hv ?_)
        rw [hs₀, h0]
        exact map_zero _
      by_cases hji : j = i
      · -- ### the marked component
        rw [if_pos hji] at hmem ⊢
        have hAA : (fun u : ℝ => proj2 (A (L.γ i u))) = fun u : ℝ => proj2 (polarCurve r Θ u) := by
          funext u
          rw [hAcurve i u, if_pos rfl]
        rcases arcRangeOrBridgeZone hη hm hΘmono hΘper hΘu hΘl t with
          ⟨w, hw, k', hkt⟩ | ⟨w, hw, k', hkt⟩ | ⟨k', hkr⟩
        · -- ## pinned, upper arc: the value is `arcZ η w`
          have hwIcc : w ∈ Set.Icc (-m) m := Set.Ioo_subset_Icc_self hw
          have hfoot' : foot y = L.γ i (τU w + k') := by rw [hjt, hkt, hji]
          rw [hkt] at hmem ⊢
          have hAc : A (L.γ i (τU w)) = polarCurve r Θ (τU w) := by
            rw [hAcurve i (τU w), if_pos rfl]
          have hval : proj2 (polarCurve r Θ (τU w + k')) = arcZ η w := by
            rw [polarCurve_add_int hrper hΘper k' (τU w), ← hAc, hau w hwIcc, proj2_cE3]
          rw [hval] at hmem ⊢
          have hwne : w ≠ 0 := by
            intro hw0
            have hZeq : Z (foot y) = arcZ η w := by
              rw [hfoot', levelCurves_shift L i k' (τU w), hZu w hwIcc]
            have him0 : ((Z (foot y)) ^ 2).im = 0 := by rw [hZeq, arcZ_sq_im, hw0]
            by_cases hθ : θ (foot y) = 1
            · have h1 := hbig y hyD hyb hθ
              rw [him0] at h1
              simp at h1
              linarith [hc₀, hδ]
            · have hθlt : θ (foot y) < 1 := lt_of_le_of_ne (hθ01 (foot y)).2 hθ
              have h2 := hAoff (foot y) hland hθlt
              have hAval : A (foot y) = Work.Drive.N2.cE3 (arcZ η w) := by
                rw [hfoot', levelCurves_shift L i k' (τU w), hau w hwIcc]
              rcases h2 with h2 | h2
              · rw [hAval, cE3_apply_two_eq_zero] at h2
                exact absurd rfl h2
              · have hnorm2 : ‖A (foot y)‖ ^ 2 = Real.sqrt (η ^ 2 + w ^ 2) := by
                  rw [hAval, norm_cE3_eq, Complex.sq_norm, normSq_arcZ]
                rw [hw0] at hnorm2
                rw [hnorm2] at h2
                have h3 : Real.sqrt (η ^ 2 + (0:ℝ) ^ 2) = η := by
                  rw [show η ^ 2 + (0:ℝ) ^ 2 = η ^ 2 by ring, Real.sqrt_sq_eq_abs,
                    abs_of_pos hη]
                rw [h3] at h2
                linarith [hc₀, hδ]
          have hn5 : ‖arcZ η w‖ < 5 :=
            norm_arcZ_lt_five hη hη' hm hm2 (le_of_lt (abs_lt.mpr ⟨hw.1, hw.2⟩))
          have hre : (arcZ η w).re ≠ 0 := re_arcZ_ne_zero_iff hwne
          have hcomp_eq : (fun u : ℝ => proj2 (polarCurve r Θ (τU u)))
              =ᶠ[𝓝 w] (fun u : ℝ => arcZ η u) := by
            filter_upwards [isOpen_Ioo.mem_nhds hw] with u hu
            have h1 : A (L.γ i (τU u)) = polarCurve r Θ (τU u) := by
              rw [hAcurve i (τU u), if_pos rfl]
            have h2 : A (L.γ i (τU u)) = Work.Drive.N2.cE3 (arcZ η u) :=
              hau u (Set.Ioo_subset_Icc_self hu)
            rw [← h1, h2, proj2_cE3]
          have hdercomp : deriv (fun u : ℝ => proj2 (polarCurve r Θ (τU u))) w
              = deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) (τU w)
                  * ((deriv τU w : ℝ) : ℂ) := by
            have hGdiff : DifferentiableAt ℝ (fun u : ℝ => proj2 (polarCurve r Θ u)) (τU w) :=
              ((Work.Drive.N2Lead.proj2CLM.contDiff.comp (contDiff_polarCurve hr hΘ)).differentiable
                (by simp)).differentiableAt
            exact deriv_comp_real_complex _ τU w hGdiff ((hτu w hw).1)
          have hderpolar : deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) (τU w)
              = deriv (fun u : ℝ => arcZ η u) w / ((deriv τU w : ℝ) : ℂ) := by
            have h1 : deriv (fun u : ℝ => proj2 (polarCurve r Θ (τU u))) w
                = deriv (fun u : ℝ => arcZ η u) w := hcomp_eq.deriv_eq
            rw [h1] at hdercomp
            have hne : ((deriv τU w : ℝ) : ℂ) ≠ 0 :=
              Complex.ofReal_ne_zero.mpr (hτu w hw).2
            rw [eq_div_iff hne, ← hdercomp]
          have hderper : deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) (τU w + (k' : ℝ))
              = deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) (τU w) := by
            have hshift : ∀ u : ℝ, proj2 (polarCurve r Θ (u + (k' : ℝ)))
                = proj2 (polarCurve r Θ u) := fun u =>
              congrArg proj2 (polarCurve_add_int hrper hΘper k' u)
            have hfun : (fun u : ℝ => proj2 (polarCurve r Θ u))
                = fun u : ℝ => proj2 (polarCurve r Θ (u + (k' : ℝ))) := by
              funext u; exact (hshift u).symm
            have hcomm : deriv (fun u : ℝ => proj2 (polarCurve r Θ (u + (k' : ℝ)))) (τU w)
                = deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) (τU w + (k' : ℝ)) :=
              deriv_comp_add_const (fun u : ℝ => proj2 (polarCurve r Θ u)) (k' : ℝ) (τU w)
            have h2 : deriv (fun u : ℝ => proj2 (polarCurve r Θ (u + (k' : ℝ)))) (τU w)
                = deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) (τU w) := by
              rw [hfun]
            rw [← hcomm]
            exact h2
          rcases lt_or_gt_of_ne hre with hreneg | hrepos
          · -- ## centre `-1`
            have hk0 : k = 0 :=
              eq_zero_of_mem_of_re_neg hmem (by linarith [hn5, norm_nonneg (arcZ η w)]) hreneg
            rw [hk0, upperCentres_zero]
            have hwneg : w < 0 := by
              by_contra hcon
              push_neg at hcon
              rcases lt_or_eq_of_le hcon with hpos | h0
              · rw [arcZ_eq_mobiusRho_of_pos hη hδ (by linarith) hpos] at hreneg
                exact absurd hreneg (not_lt.mpr (le_of_lt (re_mobiusRho_pos hδ (by linarith)
                  (ne_of_gt hpos))))
              · rw [← h0] at hreneg
                rw [re_arcZ_zero hη.le] at hreneg
                exact absurd hreneg (by norm_num)
            refine ⟨arcZ_ne_neg_one hη w, ?_⟩
            intro v hv hvne
            obtain ⟨s₀, hs₀⟩ := hkomp v hv
            have hs₀ne : s₀ ≠ 0 := hsne v s₀ hv hvne hs₀.symm
            have hl : s₀ / deriv τU w ≠ 0 := div_ne_zero hs₀ne (hτu w hw).2
            have hder' : mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ)
                  (fun z : M => proj2 (W z)) y v
                = (((s₀ / deriv τU w : ℝ)) : ℂ) * deriv (fun u : ℝ => arcZ η u) w := by
              rw [hder v s₀ hv hs₀.symm, hji, hAA, hkt, hderper, hderpolar]
              push_cast
              field_simp
              try ring
            refine not_smul_of_im_ne (l := s₀ / deriv τU w)
              (d := deriv (fun u : ℝ => arcZ η u) w) hl hder' ?_
            simpa using arcZ_cross_neg_one_ne_zero hδ hδ' hη hη' hC₀ hsmall
              ⟨by linarith [hw.1], by linarith [hw.2]⟩ hwneg
          · -- ## centre `1`
            have hk1 : k = i.succ :=
              eq_succ_of_mem_of_re_pos hmem (by linarith [hn5, norm_nonneg (arcZ η w)]) hrepos
            rw [hk1, upperCentres_succ_self]
            have hwpos : 0 < w := by
              by_contra hcon
              push_neg at hcon
              rcases lt_or_eq_of_le hcon with hneg | h0
              · have h1 : (arcZ η w).re = -(Work.Drive.N2Lead.mobiusRho η δ (-η) w).re := by
                  rw [arcZ_eq_neg_mobiusRho_of_neg hη hδ (by linarith) hneg, Complex.neg_re]
                rw [h1] at hrepos
                have h2 := re_mobiusRho_pos (η := η) hδ (by linarith) (ne_of_lt hneg)
                linarith
              · rw [h0] at hrepos
                rw [re_arcZ_zero hη.le] at hrepos
                exact absurd hrepos (by norm_num)
            refine ⟨arcZ_ne_one hη w, ?_⟩
            intro v hv hvne
            obtain ⟨s₀, hs₀⟩ := hkomp v hv
            have hs₀ne : s₀ ≠ 0 := hsne v s₀ hv hvne hs₀.symm
            have hl : s₀ / deriv τU w ≠ 0 := div_ne_zero hs₀ne (hτu w hw).2
            have hder' : mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ)
                  (fun z : M => proj2 (W z)) y v
                = (((s₀ / deriv τU w : ℝ)) : ℂ) * deriv (fun u : ℝ => arcZ η u) w := by
              rw [hder v s₀ hv hs₀.symm, hji, hAA, hkt, hderper, hderpolar]
              push_cast
              field_simp
              try ring
            refine not_smul_of_im_ne (l := s₀ / deriv τU w)
              (d := deriv (fun u : ℝ => arcZ η u) w) hl hder' ?_
            simpa using arcZ_cross_one_ne_zero hδ hδ' hη hη' hC₀ hsmall
              ⟨by linarith [hw.1], by linarith [hw.2]⟩ hwpos
        · -- ## pinned, lower arc: the value is `-arcZ η w`
          have hwIcc : w ∈ Set.Icc (-m) m := Set.Ioo_subset_Icc_self hw
          have hfoot' : foot y = L.γ i (τL w + k') := by rw [hjt, hkt, hji]
          rw [hkt] at hmem ⊢
          have hAc : A (L.γ i (τL w)) = polarCurve r Θ (τL w) := by
            rw [hAcurve i (τL w), if_pos rfl]
          have hval : proj2 (polarCurve r Θ (τL w + k')) = -arcZ η w := by
            rw [polarCurve_add_int hrper hΘper k' (τL w), ← hAc, hal w hwIcc, proj2_cE3]
          rw [hval] at hmem ⊢
          have hwne : w ≠ 0 := by
            intro hw0
            have hZeq : Z (foot y) = -arcZ η w := by
              rw [hfoot', levelCurves_shift L i k' (τL w), hZd w hwIcc]
            have him0 : ((Z (foot y)) ^ 2).im = 0 := by
              rw [hZeq, show (-arcZ η w) ^ 2 = (arcZ η w) ^ 2 by ring, arcZ_sq_im, hw0]
            by_cases hθ : θ (foot y) = 1
            · have h1 := hbig y hyD hyb hθ
              rw [him0] at h1
              simp at h1
              linarith [hc₀, hδ]
            · have hθlt : θ (foot y) < 1 := lt_of_le_of_ne (hθ01 (foot y)).2 hθ
              have h2 := hAoff (foot y) hland hθlt
              have hAval : A (foot y) = Work.Drive.N2.cE3 (-arcZ η w) := by
                rw [hfoot', levelCurves_shift L i k' (τL w), hal w hwIcc]
              rcases h2 with h2 | h2
              · rw [hAval, cE3_apply_two_eq_zero] at h2
                exact absurd rfl h2
              · have hnorm2 : ‖A (foot y)‖ ^ 2 = Real.sqrt (η ^ 2 + w ^ 2) := by
                  rw [hAval, norm_cE3_eq, Complex.sq_norm, Complex.normSq_neg, normSq_arcZ]
                rw [hw0] at hnorm2
                rw [hnorm2] at h2
                have h3 : Real.sqrt (η ^ 2 + (0:ℝ) ^ 2) = η := by
                  rw [show η ^ 2 + (0:ℝ) ^ 2 = η ^ 2 by ring, Real.sqrt_sq_eq_abs,
                    abs_of_pos hη]
                rw [h3] at h2
                linarith [hc₀, hδ]
          have hn5 : ‖-arcZ η w‖ < 5 := by
            rw [norm_neg]
            exact norm_arcZ_lt_five hη hη' hm hm2 (le_of_lt (abs_lt.mpr ⟨hw.1, hw.2⟩))
          have hre : (-arcZ η w).re ≠ 0 := by
            rw [Complex.neg_re]
            exact neg_ne_zero.mpr (re_arcZ_ne_zero_iff hwne)
          have hcomp_eq : (fun u : ℝ => proj2 (polarCurve r Θ (τL u)))
              =ᶠ[𝓝 w] (fun u : ℝ => -arcZ η u) := by
            filter_upwards [isOpen_Ioo.mem_nhds hw] with u hu
            have h1 : A (L.γ i (τL u)) = polarCurve r Θ (τL u) := by
              rw [hAcurve i (τL u), if_pos rfl]
            have h2 : A (L.γ i (τL u)) = Work.Drive.N2.cE3 (-arcZ η u) :=
              hal u (Set.Ioo_subset_Icc_self hu)
            rw [← h1, h2, proj2_cE3]
          have hdercomp : deriv (fun u : ℝ => proj2 (polarCurve r Θ (τL u))) w
              = deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) (τL w)
                  * ((deriv τL w : ℝ) : ℂ) := by
            have hGdiff : DifferentiableAt ℝ (fun u : ℝ => proj2 (polarCurve r Θ u)) (τL w) :=
              ((Work.Drive.N2Lead.proj2CLM.contDiff.comp (contDiff_polarCurve hr hΘ)).differentiable
                (by simp)).differentiableAt
            exact deriv_comp_real_complex _ τL w hGdiff ((hτl w hw).1)
          have hderpolar : deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) (τL w)
              = -(deriv (fun u : ℝ => arcZ η u) w) / ((deriv τL w : ℝ) : ℂ) := by
            have h1 : deriv (fun u : ℝ => proj2 (polarCurve r Θ (τL u))) w
                = deriv (fun u : ℝ => -arcZ η u) w := hcomp_eq.deriv_eq
            have h1' : deriv (fun u : ℝ => -arcZ η u) w
                = -(deriv (fun u : ℝ => arcZ η u) w) := deriv_neg_fun _ w
            rw [h1, h1'] at hdercomp
            have hne : ((deriv τL w : ℝ) : ℂ) ≠ 0 :=
              Complex.ofReal_ne_zero.mpr (hτl w hw).2
            rw [eq_div_iff hne]
            exact hdercomp.symm
          have hderper : deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) (τL w + (k' : ℝ))
              = deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) (τL w) := by
            have hshift : ∀ u : ℝ, proj2 (polarCurve r Θ (u + (k' : ℝ)))
                = proj2 (polarCurve r Θ u) := fun u =>
              congrArg proj2 (polarCurve_add_int hrper hΘper k' u)
            have hfun : (fun u : ℝ => proj2 (polarCurve r Θ u))
                = fun u : ℝ => proj2 (polarCurve r Θ (u + (k' : ℝ))) := by
              funext u; exact (hshift u).symm
            have hcomm : deriv (fun u : ℝ => proj2 (polarCurve r Θ (u + (k' : ℝ)))) (τL w)
                = deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) (τL w + (k' : ℝ)) :=
              deriv_comp_add_const (fun u : ℝ => proj2 (polarCurve r Θ u)) (k' : ℝ) (τL w)
            have h2 : deriv (fun u : ℝ => proj2 (polarCurve r Θ (u + (k' : ℝ)))) (τL w)
                = deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) (τL w) := by
              rw [hfun]
            rw [← hcomm]
            exact h2
          rcases lt_or_gt_of_ne hre with hreneg | hrepos
          · -- ## centre `-1`: the value `-arcZ η w = -1` is impossible
            have hk0 : k = 0 := eq_zero_of_mem_of_re_neg hmem
              (by linarith [hn5, norm_nonneg (-arcZ η w)]) hreneg
            rw [hk0, upperCentres_zero]
            have hwpos : 0 < w := by
              by_contra hcon
              push_neg at hcon
              rcases lt_or_eq_of_le hcon with hneg' | h0
              · have h1 : (-arcZ η w).re = (Work.Drive.N2Lead.mobiusRho η δ (-η) w).re := by
                  rw [arcZ_eq_neg_mobiusRho_of_neg hη hδ (by linarith) hneg', neg_neg]
                rw [h1] at hreneg
                have h2 := re_mobiusRho_pos (η := η) hδ (by linarith) (ne_of_lt hneg')
                linarith
              · rw [h0] at hreneg
                have h2 : (-arcZ η 0).re = 0 := by rw [Complex.neg_re, re_arcZ_zero hη.le]; ring
                rw [h2] at hreneg
                exact absurd hreneg (by norm_num)
            refine ⟨?_, ?_⟩
            · intro hcon
              exact arcZ_ne_one hη w (neg_inj.mp hcon)
            · intro v hv hvne
              obtain ⟨s₀, hs₀⟩ := hkomp v hv
              have hs₀ne : s₀ ≠ 0 := hsne v s₀ hv hvne hs₀.symm
              have hl : -s₀ / deriv τL w ≠ 0 :=
                div_ne_zero (neg_ne_zero.mpr hs₀ne) (hτl w hw).2
              have hder' : mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ)
                    (fun z : M => proj2 (W z)) y v
                  = (((-s₀ / deriv τL w : ℝ)) : ℂ) * deriv (fun u : ℝ => arcZ η u) w := by
                rw [hder v s₀ hv hs₀.symm, hji, hAA, hkt, hderper, hderpolar]
                push_cast
                field_simp
                try ring
              refine not_smul_of_im_ne (l := -s₀ / deriv τL w)
                (d := deriv (fun u : ℝ => arcZ η u) w) hl hder' ?_
              have hC := arcZ_cross_one_ne_zero hδ hδ' hη hη' hC₀ hsmall
                ⟨by linarith [hw.1], by linarith [hw.2]⟩ hwpos
              rw [show -arcZ η w - (-1) = -(arcZ η w - 1) by ring, star_neg, neg_mul,
                Complex.neg_im, neg_ne_zero]
              exact hC
          · -- ## centre `1`
            have hk1 : k = i.succ := eq_succ_of_mem_of_re_pos hmem
              (by linarith [hn5, norm_nonneg (-arcZ η w)]) hrepos
            rw [hk1, upperCentres_succ_self]
            have hwneg : w < 0 := by
              by_contra hcon
              push_neg at hcon
              rcases lt_or_eq_of_le hcon with hpos' | h0
              · have h1 : (-arcZ η w).re = -(Work.Drive.N2Lead.mobiusRho η δ (-η) w).re := by
                  rw [arcZ_eq_mobiusRho_of_pos hη hδ (by linarith) hpos', Complex.neg_re]
                rw [h1] at hrepos
                have h2 := re_mobiusRho_pos (η := η) hδ (by linarith) (ne_of_gt hpos')
                linarith
              · rw [← h0] at hrepos
                have h2 : (-arcZ η 0).re = 0 := by rw [Complex.neg_re, re_arcZ_zero hη.le]; ring
                rw [h2] at hrepos
                exact absurd hrepos (by norm_num)
            refine ⟨?_, ?_⟩
            · intro hcon
              exact arcZ_ne_neg_one hη w (neg_eq_iff_eq_neg.mp hcon)
            · intro v hv hvne
              obtain ⟨s₀, hs₀⟩ := hkomp v hv
              have hs₀ne : s₀ ≠ 0 := hsne v s₀ hv hvne hs₀.symm
              have hl : -s₀ / deriv τL w ≠ 0 :=
                div_ne_zero (neg_ne_zero.mpr hs₀ne) (hτl w hw).2
              have hder' : mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ)
                    (fun z : M => proj2 (W z)) y v
                  = (((-s₀ / deriv τL w : ℝ)) : ℂ) * deriv (fun u : ℝ => arcZ η u) w := by
                rw [hder v s₀ hv hs₀.symm, hji, hAA, hkt, hderper, hderpolar]
                push_cast
                field_simp
                try ring
              refine not_smul_of_im_ne (l := -s₀ / deriv τL w)
                (d := deriv (fun u : ℝ => arcZ η u) w) hl hder' ?_
              have hC := arcZ_cross_neg_one_ne_zero hδ hδ' hη hη' hC₀ hsmall
                ⟨by linarith [hw.1], by linarith [hw.2]⟩ hwneg
              rw [show -arcZ η w - 1 = -(arcZ η w + 1) by ring, star_neg, neg_mul,
                Complex.neg_im, neg_ne_zero]
              exact hC
        · -- ## bridge zone
          have hval : proj2 (polarCurve r Θ t) = (r (Θ t) : ℂ)
              * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) := proj2_polarCurve r Θ t
          rw [hval] at hmem ⊢
          have hzre : ((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)).re
              = r (Θ t) * Real.cos (Θ t) := by
            rw [Complex.mul_re]
            have hre : (Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)).re = Real.cos (Θ t) := by
              rw [Complex.exp_ofReal_mul_I]; simp [Complex.cos_ofReal_re]
            rw [hre]
            simp
          have hznorm : ‖(r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)‖ = r (Θ t) := by
            have h1 : (((Θ t : ℝ) : ℂ) * Complex.I).re = 0 := by simp
            rw [norm_mul, Complex.norm_exp, h1, Real.exp_zero, mul_one]
            simp [abs_of_pos (hrpos (Θ t))]
          have hzre_ne : ((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)).re ≠ 0 := by
            rw [hzre]
            refine mul_ne_zero (ne_of_gt (hrpos (Θ t))) ?_
            intro h0
            obtain ⟨k2, hk2⟩ := Real.cos_eq_zero_iff.mp h0
            have h3 : Θ t - (k' : ℝ) * Real.pi
                = (2 * ((k2 : ℝ) - k') + 1) * (Real.pi / 2) := by
              rw [hk2]; ring
            have h4 : (2 * ((k2 : ℝ) - k') + 1) ≠ 0 := by
              intro hh
              have h2z : ((2 * (k2 - k') + 1 : ℤ) : ℝ) = 0 := by
                push_cast
                linarith
              have h3z : (2 * (k2 - k') + 1 : ℤ) = 0 := by exact_mod_cast h2z
              omega
            have h5 : (1 : ℝ) ≤ |(2 * ((k2 : ℝ) - k') + 1)| := by
              have hcast : ((2 * (k2 - k') + 1 : ℤ) : ℝ) = 2 * ((k2 : ℝ) - k') + 1 := by
                push_cast; ring
              rw [← hcast]
              exact_mod_cast Int.one_le_abs (by omega : (2 * (k2 - k') + 1 : ℤ) ≠ 0)
            have hk1 : |Θ t - (k' : ℝ) * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE η m := hkr
            rw [h3, abs_mul, abs_of_pos (by positivity : (0:ℝ) < Real.pi / 2)] at hk1
            have h7 : Real.pi / 2 ≤ |(2 * ((k2 : ℝ) - k') + 1)| * (Real.pi / 2) := by
              nlinarith [Real.pi_pos]
            linarith [hφElt]
          have hnorm15 : ‖(r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)‖ ≤ 15 := by
            rw [hznorm]
            linarith [hbR (Θ t) ⟨k', hkr⟩, hR]
          have hr1 : 1 < r (Θ t) := by
            have h1 : (1 : ℝ) < Real.sqrt (η ^ 2 + m ^ 2) := by
              have h2 : (1 : ℝ) < c₀ + 2 * η := by linarith [hc₀, hδ, hη]
              linarith [hnum]
            have h3 : Real.sqrt (η ^ 2 + m ^ 2) ≤ r (Θ t) ^ 2 := hbrlo (Θ t) ⟨k', hkr⟩
            nlinarith [hrpos (Θ t), h3, h1]
          rcases lt_or_gt_of_ne hzre_ne with hneg | hpos
          · -- ## centre `-1`
            have hk0 : k = 0 := eq_zero_of_mem_of_re_neg hmem hnorm15 hneg
            rw [hk0, upperCentres_zero]
            refine ⟨?_, ?_⟩
            · intro hcon
              have h2 : r (Θ t) = 1 := by
                have h3 := congrArg norm hcon
                rw [hznorm] at h3
                simpa using h3
              linarith
            · intro v hv hvne
              obtain ⟨s₀, hs₀⟩ := hkomp v hv
              have hs₀ne : s₀ ≠ 0 := hsne v s₀ hv hvne hs₀.symm
              have hl : deriv Θ t * s₀ ≠ 0 := mul_ne_zero (hΘderiv t) hs₀ne
              have hder' : mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ)
                    (fun z : M => proj2 (W z)) y v
                  = (((deriv Θ t * s₀ : ℝ)) : ℂ)
                    * deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) (Θ t) := by
                have hcomp2 : deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) t
                    = deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) (Θ t)
                      * ((deriv Θ t : ℝ) : ℂ) := by
                  have hGdiff : DifferentiableAt ℝ
                      (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) (Θ t) :=
                    ((contDiff_polarF hr).differentiable (by simp)).differentiableAt
                  exact deriv_comp_real_complex _ Θ t hGdiff
                    ((hΘ.differentiable (by simp)).differentiableAt)
                have hgoal : deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) t * (s₀ : ℂ)
                    = (((deriv Θ t * s₀ : ℝ)) : ℂ)
                      * deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) (Θ t) := by
                  rw [hcomp2]
                  push_cast
                  ring
                rw [hder v s₀ hv hs₀.symm, hji, hAA]
                exact hgoal
              refine not_smul_of_im_ne (l := deriv Θ t * s₀)
                (d := deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) (Θ t))
                hl hder' ?_
              have h := (polarBridge_rate_zone hη hm hr hrpos hrper hrpi hrev hlo hmono
                ⟨k', hkr⟩).2 hneg
              rw [sub_neg_eq_add]
              exact ne_of_gt h
          · -- ## centre `1`
            have hk1 : k = i.succ := eq_succ_of_mem_of_re_pos hmem hnorm15 hpos
            rw [hk1, upperCentres_succ_self]
            refine ⟨?_, ?_⟩
            · intro hcon
              have h2 : r (Θ t) = 1 := by
                have h3 := congrArg norm hcon
                rw [hznorm] at h3
                simpa using h3
              linarith
            · intro v hv hvne
              obtain ⟨s₀, hs₀⟩ := hkomp v hv
              have hs₀ne : s₀ ≠ 0 := hsne v s₀ hv hvne hs₀.symm
              have hl : deriv Θ t * s₀ ≠ 0 := mul_ne_zero (hΘderiv t) hs₀ne
              have hder' : mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ)
                    (fun z : M => proj2 (W z)) y v
                  = (((deriv Θ t * s₀ : ℝ)) : ℂ)
                    * deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) (Θ t) := by
                have hcomp2 : deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) t
                    = deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) (Θ t)
                      * ((deriv Θ t : ℝ) : ℂ) := by
                  have hGdiff : DifferentiableAt ℝ
                      (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) (Θ t) :=
                    ((contDiff_polarF hr).differentiable (by simp)).differentiableAt
                  exact deriv_comp_real_complex _ Θ t hGdiff
                    ((hΘ.differentiable (by simp)).differentiableAt)
                have hgoal : deriv (fun u : ℝ => proj2 (polarCurve r Θ u)) t * (s₀ : ℂ)
                    = (((deriv Θ t * s₀ : ℝ)) : ℂ)
                      * deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) (Θ t) := by
                  rw [hcomp2]
                  push_cast
                  ring
                rw [hder v s₀ hv hs₀.symm, hji, hAA]
                exact hgoal
              refine not_smul_of_im_ne (l := deriv Θ t * s₀)
                (d := deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) (Θ t))
                hl hder' ?_
              have h := (polarBridge_rate_zone hη hm hr hrpos hrper hrpi hrev hlo hmono
                ⟨k', hkr⟩).1 hpos
              exact ne_of_gt h
      · -- ### a parked circle (`j ≠ i`)
        rw [if_neg hji] at hmem ⊢
        have hvalF : proj2 (farCurve n j t) ∈ Metric.ball (proj2 (farPos n j)) 2 := by
          rw [proj2_farCurve, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_proj2_ang]
          norm_num
        have hk := eq_succ_of_mem_farDisc hji hmem hvalF
        subst hk
        rw [upperCentres_succ_of_ne hji]
        refine ⟨?_, ?_⟩
        · intro h0
          have h2 : proj2 (Work.Drive.N2.ang t) = 0 := by
            have h3 : proj2 (farPos n j) + proj2 (Work.Drive.N2.ang t) - proj2 (farPos n j) = 0 := by
              rw [proj2_farCurve] at h0
              rw [h0, sub_self]
            rwa [add_sub_cancel_left] at h3
          have h4 := norm_proj2_ang t
          rw [h2] at h4
          norm_num at h4
        · intro v hv hvne
          obtain ⟨s₀, hs₀⟩ := hkomp v hv
          have hs₀ne : s₀ ≠ 0 := hsne v s₀ hv hvne hs₀.symm
          have hder' : mfderiv (𝓡 2) (𝓘(ℝ,ℂ) : ModelWithCorners ℝ ℂ ℂ)
                (fun z : M => proj2 (W z)) y v
              = ((s₀ : ℝ) : ℂ) * deriv (fun u : ℝ => proj2 (farCurve n j u)) t := by
            have hgoal : deriv (fun u : ℝ => proj2 (A (L.γ j u))) t * (s₀ : ℂ)
                = ((s₀ : ℝ) : ℂ) * deriv (fun u : ℝ => proj2 (farCurve n j u)) t := by
              have hfun : (fun u : ℝ => proj2 (A (L.γ j u)))
                  = fun u : ℝ => proj2 (farCurve n j u) := by
                funext u
                rw [hAcurve j u, if_neg hji]
              rw [hfun]
              ring
            rw [hder v s₀ hv hs₀.symm]
            exact hgoal
          refine not_smul_of_not_smul (l := s₀)
            (d := deriv (fun u : ℝ => proj2 (farCurve n j u)) t) hs₀ne hder' ?_
          intro h
          obtain ⟨s', hs'⟩ := h
          refine farCurve_deriv_not_radial n j t ⟨s', ?_⟩
          have h2 : proj2 (Work.Drive.N2.ang t)
              = proj2 (farCurve n j t) - proj2 (farPos n j) := by
            rw [proj2_farCurve, add_sub_cancel_left]
          simpa [h2] using hs'
  · -- ## `hhit`: one ray per region
    intro k
    -- the model value of a level-`u⁺` point can only be real with absolute real part `√η`
    have hmodel : ∀ z : M, f z = c + lam * η → z ∈ D → (proj2 (W z)).im = 0 →
        |(proj2 (W z)).re| = Real.sqrt η := by
      intro z hz hzD him
      have hWz : W z = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z z)) := by
        rw [hWdef, saddleWindowDrawing_of_mem hzD]
      rw [hWz, proj2_cE3] at him ⊢
      have hδh : (0 : ℝ) < 2 - 4 * δ := by linarith
      have hsq : (Work.Drive.N2.saddlePsi η δ (Z z)) ^ 2
          = Work.Drive.N2.saddlePhi η δ ((Z z) ^ 2) :=
        Work.Drive.N2.saddlePsi_sq hδ hδh.le (Z z)
      have him2 : ((Z z) ^ 2).im = 0 := by
        have h1 : (Work.Drive.N2.saddlePhi η δ ((Z z) ^ 2)).im = ((Z z) ^ 2).im :=
          Work.Drive.N2.saddlePhi_im η δ ((Z z) ^ 2)
        rw [← h1, ← hsq, pow_two, Complex.mul_im, him]
        ring
      have hre2 : ((Z z) ^ 2).re = η := by
        have h1 := hlev z hzD.1
        rw [hz] at h1
        exact mul_left_cancel₀ (ne_of_gt hlam) (by linarith)
      have hzsq : (Z z) ^ 2 = ((η : ℝ) : ℂ) := by
        apply Complex.ext
        · simpa using hre2
        · simpa using him2
      have hphi : Work.Drive.N2.saddlePhi η δ ((η : ℝ) : ℂ) = ((η : ℝ) : ℂ) := by
        apply Complex.ext
        · rw [Work.Drive.N2.saddlePhi_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im]
          rw [Work.Drive.N2.saddleSigma_apply,
            Work.Drive.N2Lead.saddleM_zero_of_lt_half hδ hδ₂]
          try ring
        · rw [Work.Drive.N2.saddlePhi_im]
      have hPsq : (Work.Drive.N2.saddlePsi η δ (Z z)) ^ 2 = ((η : ℝ) : ℂ) := by
        rw [hsq, hzsq, hphi]
      have hsqre : ((Work.Drive.N2.saddlePsi η δ (Z z)).re) ^ 2 = η := by
        have h1 : ((Work.Drive.N2.saddlePsi η δ (Z z)) ^ 2).re = η := by
          rw [hPsq]; simp
        rw [pow_two, Complex.mul_re, him] at h1
        simp at h1
        simpa [pow_two] using h1
      rw [← Real.sqrt_sq_eq_abs, hsqre]
    have hsqrt1 : Real.sqrt η < 1 :=
      (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by linarith [hη'])
    -- the left ray `(-∞, -1)`: only the polar bridge can meet it
    have hleft : ∀ z : M, f z = c + lam * η →
        (∃ s : ℝ, 0 < s ∧ proj2 (W z) = (-1 : ℂ) + s • (-1 : ℂ)) →
        ∃ (t : ℝ) (mm : ℤ), foot z = L.γ i t ∧ Θ t = Real.pi + 2 * Real.pi * (mm : ℝ) := by
      intro z hz hray
      obtain ⟨s, hs, hsz⟩ := hray
      have hsz' : proj2 (W z) = -(((1 + s : ℝ)) : ℂ) := by
        rw [hsz, Complex.real_smul]
        push_cast
        ring
      have him : (proj2 (W z)).im = 0 := by rw [hsz']; simp
      have hre : (proj2 (W z)).re = -(1 + s) := by rw [hsz']; simp
      by_cases hzD : z ∈ D
      · exfalso
        have habs := hmodel z hz hzD him
        rw [hre, abs_neg, abs_of_pos (by linarith : (0:ℝ) < 1 + s)] at habs
        linarith
      · have hzb : f z ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) := by rw [hz]; exact hηb'
        have hland : f (foot z) = c - lam * η := hfootval z hzD hzb
        obtain ⟨j, t, hjt⟩ := L.cover (foot z) hland
        have hWz : W z = A (foot z) := by rw [hWdef, saddleWindowDrawing_of_notMem hzD]
        have hval : proj2 (W z) = proj2 (A (L.γ j t)) := by rw [hWz, hjt]
        by_cases hji : j = i
        · rw [hji] at hval hjt
          have hray' : proj2 (polarCurve r Θ t) = -(((1 + s : ℝ)) : ℂ) := by
            rw [hval, hAcurve i t, if_pos rfl] at hsz'
            exact hsz'
          rcases arcRangeOrBridgeZone hη hm hΘmono hΘper hΘu hΘl t with
            ⟨w, hw, k', hkt⟩ | ⟨w, hw, k', hkt⟩ | ⟨k', hkr⟩
          · -- upper arc
            exfalso
            have hwIcc : w ∈ Set.Icc (-m) m := Set.Ioo_subset_Icc_self hw
            have hAc : A (L.γ i (τU w)) = polarCurve r Θ (τU w) := by
              rw [hAcurve i (τU w), if_pos rfl]
            have harc : proj2 (polarCurve r Θ t) = arcZ η w := by
              rw [hkt, polarCurve_add_int hrper hΘper k' (τU w), ← hAc, hau w hwIcc, proj2_cE3]
            rw [harc] at hray'
            rcases lt_trichotomy w 0 with hwlt | hweq | hwgt
            · rw [arcZ_eq_neg_mobiusRho_of_neg hη hδ (by linarith) hwlt, neg_inj] at hray'
              exact Work.Drive.N2Lead.modelArc_not_mem_ray (η := η) (δ := δ) (s := -η) (w := w)
                hδ (by linarith) (by linarith) (by linarith [hη']) ⟨s, hs, hray'⟩
            · have h1 := congrArg Complex.re hray'
              rw [hweq, re_arcZ_zero hη.le] at h1
              simp at h1
              linarith [hs]
            · rw [arcZ_eq_mobiusRho_of_pos hη hδ (by linarith) hwgt] at hray'
              exact Work.Drive.N2Lead.modelArc_not_mem_ray_neg (η := η) (δ := δ) (s := -η) (w := w)
                hδ (by linarith) (by linarith) (by linarith [hη']) ⟨s, hs, hray'⟩
          · -- lower arc
            exfalso
            have hwIcc : w ∈ Set.Icc (-m) m := Set.Ioo_subset_Icc_self hw
            have hAc : A (L.γ i (τL w)) = polarCurve r Θ (τL w) := by
              rw [hAcurve i (τL w), if_pos rfl]
            have harc : proj2 (polarCurve r Θ t) = -arcZ η w := by
              rw [hkt, polarCurve_add_int hrper hΘper k' (τL w), ← hAc, hal w hwIcc, proj2_cE3]
            rw [harc] at hray'
            rcases lt_trichotomy w 0 with hwlt | hweq | hwgt
            · rw [arcZ_eq_neg_mobiusRho_of_neg hη hδ (by linarith) hwlt, neg_neg] at hray'
              exact Work.Drive.N2Lead.modelArc_not_mem_ray_neg (η := η) (δ := δ) (s := -η) (w := w)
                hδ (by linarith) (by linarith) (by linarith [hη']) ⟨s, hs, hray'⟩
            · have h1 := congrArg Complex.re hray'
              rw [hweq, Complex.neg_re, Complex.neg_re, re_arcZ_zero hη.le] at h1
              simp at h1
              linarith [hs]
            · rw [arcZ_eq_mobiusRho_of_pos hη hδ (by linarith) hwgt, neg_inj] at hray'
              exact Work.Drive.N2Lead.modelArc_not_mem_ray (η := η) (δ := δ) (s := -η) (w := w)
                hδ (by linarith) (by linarith) (by linarith [hη']) ⟨s, hs, hray'⟩
          · -- bridge zone: the angle is an odd multiple of `π`
            have hray2 : (r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)
                = -(((1 + s : ℝ)) : ℂ) := by
              rw [← proj2_polarCurve r Θ t]
              exact hray'
            have hbridge : (r (Θ t + Real.pi) : ℂ)
                * Complex.exp (((Θ t + Real.pi : ℝ) : ℂ) * Complex.I) = (((1 + s : ℝ)) : ℂ) := by
              have h2 : (((Θ t + Real.pi : ℝ)) : ℂ) * Complex.I
                  = ((Θ t : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by push_cast; ring
              rw [hrpi (Θ t), h2, Complex.exp_add, Complex.exp_pi_mul_I]
              rw [show (r (Θ t) : ℂ) * (Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) * (-1))
                  = -((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) by ring]
              rw [hray2]
              ring
            obtain ⟨mm, hmm⟩ := Work.Drive.N2Lead.polarRay_angle (r := r)
              (Θ := fun u : ℝ => Θ u + Real.pi) (t := t) (σ := s) hs hrpos hbridge
            refine ⟨t, mm - 1, hjt, ?_⟩
            have h3 : Θ t + Real.pi = 2 * Real.pi * (mm : ℝ) := hmm
            push_cast
            linarith
        · -- a parked circle: the ray is real, the circle is not
          exfalso
          have hray2 : proj2 (farCurve n j t) = -(((1 + s : ℝ)) : ℂ) := by
            rw [hval, hAcurve j t, if_neg hji] at hsz'
            exact hsz'
          have h1 : (proj2 (Work.Drive.N2.ang t)).im = -(20 + 5 * ((j : ℕ) : ℝ)) := by
            have h5 := congrArg Complex.im hray2
            rw [proj2_farCurve, proj2_farPos] at h5
            simp only [Complex.add_im, Complex.ofReal_im, Complex.neg_im, Complex.zero_im] at h5
            linarith [h5]
          have h3 : -1 ≤ (proj2 (Work.Drive.N2.ang t)).im := by
            have h2 := (abs_le.mp (Complex.abs_im_le_norm (proj2 (Work.Drive.N2.ang t)))).1
            rwa [norm_proj2_ang] at h2
          have h4 : (0:ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
    -- the right ray `(1, ∞)`: only the polar bridge can meet it
    have hright : ∀ z : M, f z = c + lam * η →
        (∃ s : ℝ, 0 < s ∧ proj2 (W z) = (1 : ℂ) + s • (1 : ℂ)) →
        ∃ (t : ℝ) (mm : ℤ), foot z = L.γ i t ∧ Θ t = 2 * Real.pi * (mm : ℝ) := by
      intro z hz hray
      obtain ⟨s, hs, hsz⟩ := hray
      have hsz' : proj2 (W z) = (((1 + s : ℝ)) : ℂ) := by
        rw [hsz, Complex.real_smul]
        push_cast
        ring
      have him : (proj2 (W z)).im = 0 := by rw [hsz']; simp
      have hre : (proj2 (W z)).re = 1 + s := by rw [hsz']; simp
      by_cases hzD : z ∈ D
      · exfalso
        have habs := hmodel z hz hzD him
        rw [hre, abs_of_pos (by linarith : (0:ℝ) < 1 + s)] at habs
        linarith
      · have hzb : f z ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) := by rw [hz]; exact hηb'
        have hland : f (foot z) = c - lam * η := hfootval z hzD hzb
        obtain ⟨j, t, hjt⟩ := L.cover (foot z) hland
        have hWz : W z = A (foot z) := by rw [hWdef, saddleWindowDrawing_of_notMem hzD]
        have hval : proj2 (W z) = proj2 (A (L.γ j t)) := by rw [hWz, hjt]
        by_cases hji : j = i
        · rw [hji] at hval hjt
          have hray' : proj2 (polarCurve r Θ t) = (((1 + s : ℝ)) : ℂ) := by
            rw [hval, hAcurve i t, if_pos rfl] at hsz'
            exact hsz'
          rcases arcRangeOrBridgeZone hη hm hΘmono hΘper hΘu hΘl t with
            ⟨w, hw, k', hkt⟩ | ⟨w, hw, k', hkt⟩ | ⟨k', hkr⟩
          · -- upper arc
            exfalso
            have hwIcc : w ∈ Set.Icc (-m) m := Set.Ioo_subset_Icc_self hw
            have hAc : A (L.γ i (τU w)) = polarCurve r Θ (τU w) := by
              rw [hAcurve i (τU w), if_pos rfl]
            have harc : proj2 (polarCurve r Θ t) = arcZ η w := by
              rw [hkt, polarCurve_add_int hrper hΘper k' (τU w), ← hAc, hau w hwIcc, proj2_cE3]
            rw [harc] at hray'
            rcases lt_trichotomy w 0 with hwlt | hweq | hwgt
            · rw [arcZ_eq_neg_mobiusRho_of_neg hη hδ (by linarith) hwlt,
                neg_eq_iff_eq_neg] at hray'
              exact Work.Drive.N2Lead.modelArc_not_mem_ray_neg (η := η) (δ := δ) (s := -η) (w := w)
                hδ (by linarith) (by linarith) (by linarith [hη']) ⟨s, hs, hray'⟩
            · have h1 := congrArg Complex.re hray'
              rw [hweq, re_arcZ_zero hη.le] at h1
              simp at h1
              linarith [hs]
            · rw [arcZ_eq_mobiusRho_of_pos hη hδ (by linarith) hwgt] at hray'
              exact Work.Drive.N2Lead.modelArc_not_mem_ray (η := η) (δ := δ) (s := -η) (w := w)
                hδ (by linarith) (by linarith) (by linarith [hη']) ⟨s, hs, hray'⟩
          · -- lower arc
            exfalso
            have hwIcc : w ∈ Set.Icc (-m) m := Set.Ioo_subset_Icc_self hw
            have hAc : A (L.γ i (τL w)) = polarCurve r Θ (τL w) := by
              rw [hAcurve i (τL w), if_pos rfl]
            have harc : proj2 (polarCurve r Θ t) = -arcZ η w := by
              rw [hkt, polarCurve_add_int hrper hΘper k' (τL w), ← hAc, hal w hwIcc, proj2_cE3]
            rw [harc] at hray'
            rcases lt_trichotomy w 0 with hwlt | hweq | hwgt
            · rw [arcZ_eq_neg_mobiusRho_of_neg hη hδ (by linarith) hwlt, neg_neg] at hray'
              exact Work.Drive.N2Lead.modelArc_not_mem_ray (η := η) (δ := δ) (s := -η) (w := w)
                hδ (by linarith) (by linarith) (by linarith [hη']) ⟨s, hs, hray'⟩
            · have h1 := congrArg Complex.re hray'
              rw [hweq, Complex.neg_re, re_arcZ_zero hη.le] at h1
              simp at h1
              linarith [hs]
            · rw [arcZ_eq_mobiusRho_of_pos hη hδ (by linarith) hwgt,
                neg_eq_iff_eq_neg] at hray'
              exact Work.Drive.N2Lead.modelArc_not_mem_ray_neg (η := η) (δ := δ) (s := -η) (w := w)
                hδ (by linarith) (by linarith) (by linarith [hη']) ⟨s, hs, hray'⟩
          · -- bridge zone
            have hray2 : (r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)
                = (((1 + s : ℝ)) : ℂ) := by
              rw [← proj2_polarCurve r Θ t]
              exact hray'
            obtain ⟨mm, hmm⟩ := Work.Drive.N2Lead.polarRay_angle (r := r) (Θ := Θ)
              (t := t) (σ := s) hs hrpos hray2
            exact ⟨t, mm, hjt, hmm⟩
        · -- a parked circle: the ray is real, the circle is not
          exfalso
          have hray2 : proj2 (farCurve n j t) = (((1 + s : ℝ)) : ℂ) := by
            rw [hval, hAcurve j t, if_neg hji] at hsz'
            exact hsz'
          have h1 : (proj2 (Work.Drive.N2.ang t)).im = -(20 + 5 * ((j : ℕ) : ℝ)) := by
            have h5 := congrArg Complex.im hray2
            rw [proj2_farCurve, proj2_farPos] at h5
            simp only [Complex.add_im, Complex.ofReal_im, Complex.zero_im] at h5
            linarith [h5]
          have h3 : -1 ≤ (proj2 (Work.Drive.N2.ang t)).im := by
            have h2 := (abs_le.mp (Complex.abs_im_le_norm (proj2 (Work.Drive.N2.ang t)))).1
            rwa [norm_proj2_ang] at h2
          have h4 : (0:ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
    -- the far ray: only the circle of `j₀` itself can meet it
    have hfar : ∀ z : M, f z = c + lam * η → ∀ (j₀ : Fin n), j₀ ≠ i →
        (∃ s : ℝ, 0 < s ∧ proj2 (W z) = proj2 (farPos n j₀) + s • (-1 : ℂ)) →
        ∃ (t : ℝ) (mm : ℤ), foot z = L.γ j₀ t ∧ t = 1 / 2 + (mm : ℝ) := by
      intro z hz j₀ hj₀ hray
      obtain ⟨s, hs, hsz⟩ := hray
      have hsz' : proj2 (W z) = proj2 (farPos n j₀) - ((s : ℝ) : ℂ) := by
        rw [hsz, Complex.real_smul]
        ring
      by_cases hzD : z ∈ D
      · exfalso
        obtain ⟨-, hnorm⟩ := Work.Drive.N2Lead.upperRegionMem (η := η) (δ := δ) (c := c)
          (c₀ := c₀) (lam := lam) (U := U) (Z := Z) (y := z) hlev (ne_of_gt hlam) hη hη' hδ
          hδ₂ hc₀₂ hzD.1 hzD.2 hz
        have hWz : W z = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z z)) := by
          rw [hWdef, saddleWindowDrawing_of_mem hzD]
        have hlt : |(Work.Drive.N2.saddlePsi η δ (Z z)).im| < 5 :=
          lt_of_le_of_lt (Complex.abs_im_le_norm _) hnorm
        have hh : (Work.Drive.N2.saddlePsi η δ (Z z)).im = 20 + 5 * ((j₀ : ℕ) : ℝ) := by
          have h1 := congrArg Complex.im hsz'
          rw [hWz, proj2_cE3, proj2_farPos] at h1
          simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, sub_zero] at h1
          linarith [h1]
        rw [hh, abs_of_nonneg (by positivity : (0:ℝ) ≤ 20 + 5 * ((j₀ : ℕ) : ℝ))] at hlt
        have hj0 : (0:ℝ) ≤ ((j₀ : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      · have hzb : f z ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) := by rw [hz]; exact hηb'
        have hland : f (foot z) = c - lam * η := hfootval z hzD hzb
        obtain ⟨j, t, hjt⟩ := L.cover (foot z) hland
        have hWz : W z = A (foot z) := by rw [hWdef, saddleWindowDrawing_of_notMem hzD]
        have hval : proj2 (W z) = proj2 (A (L.γ j t)) := by rw [hWz, hjt]
        by_cases hji : j = i
        · -- the marked component: arc or bridge
          rw [hji] at hval hjt
          have hray' : proj2 (polarCurve r Θ t) = proj2 (farPos n j₀) - ((s : ℝ) : ℂ) := by
            rw [hval, hAcurve i t, if_pos rfl] at hsz'
            exact hsz'
          rcases arcRangeOrBridgeZone hη hm hΘmono hΘper hΘu hΘl t with
            ⟨w, hw, k', hkt⟩ | ⟨w, hw, k', hkt⟩ | ⟨k', hkr⟩
          · -- upper arc
            exfalso
            have hwIcc : w ∈ Set.Icc (-m) m := Set.Ioo_subset_Icc_self hw
            have hAc : A (L.γ i (τU w)) = polarCurve r Θ (τU w) := by
              rw [hAcurve i (τU w), if_pos rfl]
            have harc : proj2 (polarCurve r Θ t) = arcZ η w := by
              rw [hkt, polarCurve_add_int hrper hΘper k' (τU w), ← hAc, hau w hwIcc, proj2_cE3]
            rw [harc] at hray'
            have hlt : |(arcZ η w).im| < 5 :=
              lt_of_le_of_lt (Complex.abs_im_le_norm _)
                (norm_arcZ_lt_five hη hη' hm hm2 (le_of_lt (abs_lt.mpr ⟨hw.1, hw.2⟩)))
            have hh : (arcZ η w).im = 20 + 5 * ((j₀ : ℕ) : ℝ) := by
              have h1 := congrArg Complex.im hray'
              rw [proj2_farPos] at h1
              simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, sub_zero] at h1
              linarith [h1]
            rw [hh, abs_of_nonneg (by positivity : (0:ℝ) ≤ 20 + 5 * ((j₀ : ℕ) : ℝ))] at hlt
            have hj0 : (0:ℝ) ≤ ((j₀ : ℕ) : ℝ) := Nat.cast_nonneg _
            linarith
          · -- lower arc
            exfalso
            have hwIcc : w ∈ Set.Icc (-m) m := Set.Ioo_subset_Icc_self hw
            have hAc : A (L.γ i (τL w)) = polarCurve r Θ (τL w) := by
              rw [hAcurve i (τL w), if_pos rfl]
            have harc : proj2 (polarCurve r Θ t) = -arcZ η w := by
              rw [hkt, polarCurve_add_int hrper hΘper k' (τL w), ← hAc, hal w hwIcc, proj2_cE3]
            rw [harc] at hray'
            have hlt : |(arcZ η w).im| < 5 :=
              lt_of_le_of_lt (Complex.abs_im_le_norm _)
                (norm_arcZ_lt_five hη hη' hm hm2 (le_of_lt (abs_lt.mpr ⟨hw.1, hw.2⟩)))
            have hh : (arcZ η w).im = -(20 + 5 * ((j₀ : ℕ) : ℝ)) := by
              have h1 := congrArg Complex.im hray'
              rw [Complex.neg_im, proj2_farPos] at h1
              simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, sub_zero] at h1
              linarith [h1]
            rw [hh, abs_neg,
              abs_of_nonneg (by positivity : (0:ℝ) ≤ 20 + 5 * ((j₀ : ℕ) : ℝ))] at hlt
            have hj0 : (0:ℝ) ≤ ((j₀ : ℕ) : ℝ) := Nat.cast_nonneg _
            linarith
          · -- bridge zone
            exfalso
            have hlt : |((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)).im| < 5 := by
              have h1 : (((Θ t : ℝ) : ℂ) * Complex.I).re = 0 := by simp
              have h2 : ‖(r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)‖ = r (Θ t) := by
                rw [norm_mul, Complex.norm_exp, h1, Real.exp_zero, mul_one]
                simp [abs_of_pos (hrpos (Θ t))]
              refine lt_of_le_of_lt (Complex.abs_im_le_norm _) ?_
              rw [h2]
              linarith [hbR (Θ t) ⟨k', hkr⟩, hR]
            have hh : ((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)).im
                = 20 + 5 * ((j₀ : ℕ) : ℝ) := by
              have h1 := congrArg Complex.im hray'
              rw [proj2_polarCurve, proj2_farPos] at h1
              simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, sub_zero] at h1
              linarith [h1]
            rw [hh, abs_of_nonneg (by positivity : (0:ℝ) ≤ 20 + 5 * ((j₀ : ℕ) : ℝ))] at hlt
            have hj0 : (0:ℝ) ≤ ((j₀ : ℕ) : ℝ) := Nat.cast_nonneg _
            linarith
        · -- a parked circle: the imaginary parts force `j = j₀`
          have hray' : proj2 (farCurve n j t) = proj2 (farPos n j₀) - ((s : ℝ) : ℂ) := by
            rw [hval, hAcurve j t, if_neg hji] at hsz'
            exact hsz'
          have h6 : (proj2 (Work.Drive.N2.ang t)).im
              = (((j₀ : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * 5 := by
            have h7 := congrArg Complex.im hray'
            rw [proj2_farCurve, proj2_farPos, proj2_farPos] at h7
            simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.neg_im,
              Complex.zero_im] at h7
            linarith [h7]
          have h7 : |(proj2 (Work.Drive.N2.ang t)).im| ≤ 1 := by
            have h8 := Complex.abs_im_le_norm (proj2 (Work.Drive.N2.ang t))
            rwa [norm_proj2_ang] at h8
          have h8 : |(5 : ℝ) * (((j : ℕ) : ℝ) - ((j₀ : ℕ) : ℝ))| ≤ 1 := by
            have h9 : |(((j₀ : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * 5| ≤ 1 := by rwa [h6] at h7
            rwa [show (((j₀ : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * 5
              = -(5 * (((j : ℕ) : ℝ) - ((j₀ : ℕ) : ℝ))) by ring, abs_neg] at h9
          have hjj : j = j₀ := fin_eq_of_abs_five_le h8
          rw [hjj] at hray' hjt hval
          -- the point of the circle on the ray is the one at distance `1` to the left
          have hang : proj2 (Work.Drive.N2.ang t) = -(((s : ℝ)) : ℂ) := by
            have h9 := hray'
            rw [proj2_farCurve, sub_eq_add_neg] at h9
            have h10 : proj2 (farPos n j₀) + proj2 (Work.Drive.N2.ang t)
                = proj2 (farPos n j₀) + (-(((s : ℝ)) : ℂ)) := h9
            exact add_left_cancel h10
          have hexp : Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
              = -(((s : ℝ)) : ℂ) := by
            rw [← proj2_ang t]
            exact hang
          have hs1 : s = 1 := by
            have h1 := congrArg norm hexp
            have h2 : (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I).re = 0 := by simp
            rw [Complex.norm_exp, h2, Real.exp_zero] at h1
            have h3 : ‖-(((s : ℝ)) : ℂ)‖ = s := by
              rw [norm_neg]
              simp [abs_of_pos hs]
            rw [h3] at h1
            linarith
          have hexp1 : Complex.exp (((2 * Real.pi * t - Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
            have h2 : (((2 * Real.pi * t - Real.pi : ℝ)) : ℂ) * Complex.I
                = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I - (Real.pi : ℂ) * Complex.I := by
              push_cast; ring
            rw [h2, Complex.exp_sub, hexp, hs1, Complex.exp_pi_mul_I]
            norm_num
          obtain ⟨mm, hmm⟩ := Complex.exp_eq_one_iff.mp hexp1
          refine ⟨t, mm, hjt, ?_⟩
          have him2 : 2 * Real.pi * t - Real.pi = 2 * Real.pi * (mm : ℝ) := by
            have h' : (((2 * Real.pi * t - Real.pi : ℝ)) : ℂ) * Complex.I
                = (((mm : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
              rw [hmm]
              push_cast
              ring
            have h'' : (((2 * Real.pi * t - Real.pi : ℝ)) : ℂ)
                = (((mm : ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
              mul_right_cancel₀ Complex.I_ne_zero h'
            have h3 : 2 * Real.pi * t - Real.pi = (mm : ℝ) * (2 * Real.pi) := by
              exact_mod_cast h''
            linarith [h3]
          have h4 : 2 * Real.pi * t = 2 * Real.pi * ((mm : ℝ) + 1 / 2) := by linarith
          have h5 : t = (mm : ℝ) + 1 / 2 :=
            mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0) h4
          linarith
    rcases Fin.eq_zero_or_eq_succ k with hk | ⟨j₀, rfl⟩
    · -- `k = 0`: the left ray `(-∞, -1)`
      rw [hk, upperCentres_zero]
      refine ⟨-1, by norm_num, ?_⟩
      intro x y hx hy hxr hyr
      obtain ⟨tx, mx, hxf, hxθ⟩ := hleft x hx hxr
      obtain ⟨ty, my, hyf, hyθ⟩ := hleft y hy hyr
      have hΘeq : Θ tx = Θ (ty + ((mx : ℝ) - (my : ℝ))) := by
        have h := Work.Drive.N2Lead.thetaAddInt hΘper ty (mx - my)
        push_cast at h
        rw [h, hyθ, hxθ]
        ring
      have ht : tx = ty + ((mx : ℝ) - (my : ℝ)) := hΘmono.injective hΘeq
      have hfe : foot x = foot y := by
        have h := levelCurves_shift L i (mx - my) ty
        push_cast at h
        rw [hxf, hyf, ht, h]
      exact hfootinj x y (hx.trans hy.symm) hfe
    · by_cases hj₀ : j₀ = i
      · -- `k = i.succ`: the right ray `(1, ∞)`
        rw [hj₀, upperCentres_succ_self]
        refine ⟨1, one_ne_zero, ?_⟩
        intro x y hx hy hxr hyr
        have hxr' : ∃ s : ℝ, 0 < s ∧ proj2 (W x) = (1 : ℂ) + s • (1 : ℂ) := by
          obtain ⟨s, hs, hsx⟩ := hxr
          exact ⟨s, hs, by simp [hsx, Complex.real_smul]⟩
        have hyr' : ∃ s : ℝ, 0 < s ∧ proj2 (W y) = (1 : ℂ) + s • (1 : ℂ) := by
          obtain ⟨s, hs, hsy⟩ := hyr
          exact ⟨s, hs, by simp [hsy, Complex.real_smul]⟩
        obtain ⟨tx, mx, hxf, hxθ⟩ := hright x hx hxr'
        obtain ⟨ty, my, hyf, hyθ⟩ := hright y hy hyr'
        have hΘeq : Θ tx = Θ (ty + ((mx : ℝ) - (my : ℝ))) := by
          have h := Work.Drive.N2Lead.thetaAddInt hΘper ty (mx - my)
          push_cast at h
          rw [h, hyθ, hxθ]
          ring
        have ht : tx = ty + ((mx : ℝ) - (my : ℝ)) := hΘmono.injective hΘeq
        have hfe : foot x = foot y := by
          have h := levelCurves_shift L i (mx - my) ty
          push_cast at h
          rw [hxf, hyf, ht, h]
        exact hfootinj x y (hx.trans hy.symm) hfe
      · -- `k = j₀.succ` with `j₀ ≠ i`: the far ray
        rw [upperCentres_succ_of_ne hj₀]
        refine ⟨-1, by norm_num, ?_⟩
        intro x y hx hy hxr hyr
        obtain ⟨tx, mx, hxf, hxθ⟩ := hfar x hx j₀ hj₀ hxr
        obtain ⟨ty, my, hyf, hyθ⟩ := hfar y hy j₀ hj₀ hyr
        have ht : tx = ty + ((mx : ℝ) - (my : ℝ)) := by
          rw [hxθ, hyθ]
          push_cast
          ring
        have hfe : foot x = foot y := by
          have h := levelCurves_shift L j₀ (mx - my) ty
          push_cast at h
          rw [hxf, hyf, ht, h]
        exact hfootinj x y (hx.trans hy.symm) hfe

end Work.Drive.N2Lead.UpCS
