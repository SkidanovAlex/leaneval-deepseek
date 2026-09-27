import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2Lead.mobiusPacketDefs
import Submission.Work.Drive.N2C.mobiusShape
import Submission.Work.Drive.N2Lead.mobiusUpperDefs
import Submission.Work.Drive.N2Lead.mobiusUpperFootKit
import Submission.Work.Drive.N2Lead.mobiusUpperModelNorm
import Submission.Work.Drive.N2C.mfrFarPiece
import Submission.Work.Drive.N2C.lowerCert
import Submission.Work.Drive.N2Lead.mobiusGoodDrawing
import Submission.Work.Drive.N2Lead.twistToolkit

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter


/-! ## The region family of the star rows

The regions are one disc about the origin for the marked component (the model arcs and the
transported polar picture, all within `Dp + 3` of `0`) and one disc of radius `2` about each shifted
parking spot.  The centres of the marked component and of `farPos` are far apart, which is what makes
the family pairwise disjoint. -/

/-- The centres of the star regions: the origin for the marked component of the anchor level, and the
shifted parking spots `proj2 (farPos n k) + Dp i` for the parked circles. -/
noncomputable def mfrO (n : ℕ) (i : Fin n) (Dp : ℝ) : Fin n → ℂ :=
  fun k => if k = i then 0 else proj2 (farPos n k) + (Dp : ℂ) * Complex.I

/-- The star regions of the twisted Möbius upper picture. -/
noncomputable def mfrOm (n : ℕ) (i : Fin n) (Dp : ℝ) : Fin n → Set ℂ :=
  fun k => if k = i then Metric.ball 0 (Dp + 5) else Metric.ball (mfrO n i Dp k) 2

/-- The ray of each star region: the positive real axis for the marked region and the negative real
direction for the parked circles. -/
noncomputable def mfrE (n : ℕ) (i : Fin n) : Fin n → ℂ :=
  fun k => if k = i then 1 else -1

@[simp] lemma mfrO_self (n : ℕ) (i : Fin n) (Dp : ℝ) : mfrO n i Dp i = 0 := by
  simp [mfrO]

lemma mfrO_of_ne (n : ℕ) (i : Fin n) (Dp : ℝ) {k : Fin n} (hk : k ≠ i) :
    mfrO n i Dp k = proj2 (farPos n k) + (Dp : ℂ) * Complex.I := by
  simp [mfrO, hk]

@[simp] lemma mfrOm_self (n : ℕ) (i : Fin n) (Dp : ℝ) : mfrOm n i Dp i = Metric.ball 0 (Dp + 5) := by
  simp [mfrOm]

lemma mfrOm_of_ne (n : ℕ) (i : Fin n) (Dp : ℝ) {k : Fin n} (hk : k ≠ i) :
    mfrOm n i Dp k = Metric.ball (mfrO n i Dp k) 2 := by
  simp [mfrOm, hk]

@[simp] lemma mfrE_self (n : ℕ) (i : Fin n) : mfrE n i i = 1 := by simp [mfrE]

@[simp] lemma mfrE_of_ne (n : ℕ) (i : Fin n) {k : Fin n} (hk : k ≠ i) : mfrE n i k = -1 := by
  simp [mfrE, hk]

/-! ### The elementary geometry of the region family -/

lemma im_mfrO (n : ℕ) (i : Fin n) (Dp : ℝ) {k : Fin n} (hk : k ≠ i) :
    (mfrO n i Dp k).im = 20 + 5 * ((k : ℕ) : ℝ) + Dp := by
  rw [mfrO_of_ne n i Dp hk, Complex.add_im, Work.Drive.N2C.proj2_farPos]
  simp [Complex.mul_im]

lemma re_mfrO (n : ℕ) (i : Fin n) (Dp : ℝ) {k : Fin n} (hk : k ≠ i) :
    (mfrO n i Dp k).re = -20 := by
  rw [mfrO_of_ne n i Dp hk, Complex.add_re, Work.Drive.N2C.proj2_farPos]
  simp [Complex.mul_re]

lemma im_mfrO_add_smul_neg (n : ℕ) (i : Fin n) (Dp : ℝ) {k : Fin n} (hk : k ≠ i) (s : ℝ) :
    (mfrO n i Dp k + s • (-1 : ℂ)).im = 20 + 5 * ((k : ℕ) : ℝ) + Dp := by
  rw [Complex.add_im, im_mfrO n i Dp hk]
  simp

lemma re_mfrO_add_smul_neg (n : ℕ) (i : Fin n) (Dp : ℝ) {k : Fin n} (hk : k ≠ i) (s : ℝ) :
    (mfrO n i Dp k + s • (-1 : ℂ)).re = -20 - s := by
  rw [Complex.add_re, re_mfrO n i Dp hk]
  simp
  ring

lemma im_far_add (n : ℕ) (j : Fin n) (Dp : ℝ) (t : ℝ) :
    (proj2 (farPos n j) + (Dp : ℂ) * Complex.I + proj2 (Work.Drive.N2.ang t)).im
      = 20 + 5 * ((j : ℕ) : ℝ) + Dp + Real.sin (2 * Real.pi * t) := by
  rw [Complex.add_im, Complex.add_im, Work.Drive.N2C.proj2_farPos, Work.Drive.N2C.im_proj2_ang]
  simp [Complex.mul_im]

lemma re_far_add (n : ℕ) (j : Fin n) (Dp : ℝ) (t : ℝ) :
    (proj2 (farPos n j) + (Dp : ℂ) * Complex.I + proj2 (Work.Drive.N2.ang t)).re
      = -20 + Real.cos (2 * Real.pi * t) := by
  rw [Complex.add_re, Complex.add_re, Work.Drive.N2C.proj2_farPos, Work.Drive.N2C.re_proj2_ang]
  simp [Complex.mul_re]

/-- A shifted parking spot is at distance at least `Dp + 20` from the origin. -/
lemma mfrO_norm_ge (n : ℕ) (i : Fin n) {Dp : ℝ} (hDp : 0 ≤ Dp) {k : Fin n} (hk : k ≠ i) :
    Dp + 20 ≤ ‖mfrO n i Dp k‖ := by
  have h1 := Complex.abs_im_le_norm (mfrO n i Dp k)
  rw [im_mfrO n i Dp hk] at h1
  have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg (by linarith)] at h1
  linarith

/-- Two distinct shifted parking spots are at distance at least `5`. -/
lemma mfrO_dist_ge (n : ℕ) (i : Fin n) (Dp : ℝ) {k l : Fin n}
    (hk : k ≠ i) (hl : l ≠ i) (hkl : k ≠ l) :
    5 ≤ ‖mfrO n i Dp k - mfrO n i Dp l‖ := by
  have him : (mfrO n i Dp k - mfrO n i Dp l).im
      = 5 * (((k : ℕ) : ℝ) - ((l : ℕ) : ℝ)) := by
    rw [Complex.sub_im, im_mfrO n i Dp hk, im_mfrO n i Dp hl]
    ring
  have h2 := Complex.abs_im_le_norm (mfrO n i Dp k - mfrO n i Dp l)
  rw [him] at h2
  have hne : ((k : ℕ) : ℝ) - ((l : ℕ) : ℝ) ≠ 0 := by
    have h : ((k : ℕ) : ℝ) ≠ ((l : ℕ) : ℝ) := by
      intro hc
      exact hkl (Fin.ext (by exact_mod_cast hc))
    exact sub_ne_zero.mpr h
  have h1 : (1 : ℝ) ≤ |((k : ℕ) : ℝ) - ((l : ℕ) : ℝ)| := by
    obtain ⟨m, hm⟩ : ∃ m : ℤ, ((k : ℕ) : ℝ) - ((l : ℕ) : ℝ) = (m : ℝ) :=
      ⟨((k : ℕ) : ℤ) - ((l : ℕ) : ℤ), by push_cast; ring⟩
    have hm0 : m ≠ 0 := by
      intro h0
      exact hne (by rw [hm, h0]; norm_num)
    have hle := Int.one_le_abs hm0
    rw [hm]
    exact_mod_cast hle
  calc (5 : ℝ) = 5 * 1 := by ring
    _ ≤ 5 * |((k : ℕ) : ℝ) - ((l : ℕ) : ℝ)| := by linarith
    _ = |5 * (((k : ℕ) : ℝ) - ((l : ℕ) : ℝ))| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
    _ ≤ ‖mfrO n i Dp k - mfrO n i Dp l‖ := h2

/-- The regions are open and convex. -/
theorem mfr_isOpen_convex (n : ℕ) (i : Fin n) (Dp : ℝ) (k : Fin n) :
    IsOpen (mfrOm n i Dp k) ∧ Convex ℝ (mfrOm n i Dp k) := by
  unfold mfrOm
  split
  · exact ⟨Metric.isOpen_ball, convex_ball _ _⟩
  · exact ⟨Metric.isOpen_ball, convex_ball _ _⟩

/-- Each region contains the closed ball of radius `1/2` about its centre. -/
theorem mfr_closedBall_subset (n : ℕ) (i : Fin n) {Dp : ℝ} (hDp : 0 ≤ Dp) (k : Fin n) :
    Metric.closedBall (mfrO n i Dp k) (1 / 2) ⊆ mfrOm n i Dp k := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  by_cases hk : k = i
  · rw [mfrOm, if_pos hk, Metric.mem_ball, dist_zero_right]
    rw [mfrO, if_pos hk] at hz
    simp only [sub_zero] at hz
    linarith
  · rw [mfrOm, if_neg hk, Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt hz (by norm_num)

/-- The regions are pairwise disjoint (for `Dp ≥ 0`). -/
theorem mfr_pairwiseDisjoint (n : ℕ) (i : Fin n) {Dp : ℝ} (hDp : 0 ≤ Dp) :
    Pairwise fun k l : Fin n => Disjoint (mfrOm n i Dp k) (mfrOm n i Dp l) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro z hzk hzl
  by_cases hk : k = i
  · have hl : l ≠ i := fun h => hkl (hk.trans h.symm)
    rw [mfrOm, if_pos hk, Metric.mem_ball, dist_zero_right] at hzk
    rw [mfrOm, if_neg hl, Metric.mem_ball, dist_eq_norm] at hzl
    have hge := mfrO_norm_ge n i hDp hl
    have h3 : ‖mfrO n i Dp l‖ ≤ ‖z - mfrO n i Dp l‖ + ‖z‖ := by
      have h := norm_add_le (mfrO n i Dp l - z) z
      rw [sub_add_cancel] at h
      rw [norm_sub_rev] at h
      exact h
    linarith
  · by_cases hl : l = i
    · rw [mfrOm, if_neg hk, Metric.mem_ball, dist_eq_norm] at hzk
      rw [mfrOm, if_pos hl, Metric.mem_ball, dist_zero_right] at hzl
      have hge := mfrO_norm_ge n i hDp hk
      have h3 : ‖mfrO n i Dp k‖ ≤ ‖z - mfrO n i Dp k‖ + ‖z‖ := by
        have h := norm_add_le (mfrO n i Dp k - z) z
        rw [sub_add_cancel] at h
        rw [norm_sub_rev] at h
        exact h
      linarith
    · rw [mfrOm, if_neg hk, Metric.mem_ball, dist_eq_norm] at hzk
      rw [mfrOm, if_neg hl, Metric.mem_ball, dist_eq_norm] at hzl
      have h5 := mfrO_dist_ge n i Dp hk hl hkl
      have h4 : ‖mfrO n i Dp k - mfrO n i Dp l‖
          ≤ ‖z - mfrO n i Dp l‖ + ‖z - mfrO n i Dp k‖ := by
        rw [show mfrO n i Dp k - mfrO n i Dp l
            = (z - mfrO n i Dp l) - (z - mfrO n i Dp k) by ring]
        exact norm_sub_le _ _
      linarith

/-- The planar projection does not increase the norm. -/
lemma norm_proj2_le (v : E3) : ‖proj2 v‖ ≤ ‖v‖ := by
  have h1 : ‖proj2 v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [proj2]
    ring
  have h2 : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three]
  nlinarith [norm_nonneg (proj2 v), norm_nonneg v, sq_nonneg (v 2)]

/-- **The classification of a level point whose picture lies in a far region.**  Such a point is
outside the model region and its foot is on the parked component of index `k`. -/
theorem mfr_far_classify {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (S : Work.Drive.N2Lead.MobiusPacket D η)
    {ε εp Dp : ℝ} (hε : 0 < ε) (hε19 : ε ≤ 19) (hεp : 0 < εp) (hεp19 : εp ≤ 19) (hDp : 0 ≤ Dp)
    {k : Fin S.n} (hk : k ≠ S.i) {y : M} (hy : f y = f p + 3 * η / 2)
    (hz : dist (proj2 (mobiusTwisted D η S ε εp Dp y)) (mfrO S.n S.i Dp k) < 2) :
    y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20) ∧
      ∃ t : ℝ, Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ k t := by
  have hband : f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) := by
    rw [hy]; constructor <;> linarith
  have hOnorm : Dp + 20 ≤ ‖mfrO S.n S.i Dp k‖ := mfrO_norm_ge S.n S.i hDp hk
  have htri : ∀ z : ℂ, ‖mfrO S.n S.i Dp k‖ ≤ ‖mfrO S.n S.i Dp k - z‖ + ‖z‖ := by
    intro z
    have h := norm_add_le (mfrO S.n S.i Dp k - z) z
    rwa [sub_add_cancel] at h
  have hdist : ‖mfrO S.n S.i Dp k - proj2 (mobiusTwisted D η S ε εp Dp y)‖ < 2 := by
    rw [dist_eq_norm] at hz
    rwa [norm_sub_rev] at hz
  have hnotmem : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
      S.Z (39 / 20) := by
    intro hmem
    have h1 : ‖mobiusTwisted D η S ε εp Dp y‖ ≤ Dp + 2 :=
      mobiusUpperModelNorm (D := D) hη hsmall S (ε := ε) (εp := εp) hDp y hy hmem
    have h2 : ‖proj2 (mobiusTwisted D η S ε εp Dp y)‖
        ≤ ‖mobiusTwisted D η S ε εp Dp y‖ := norm_proj2_le _
    have h3 := htri (proj2 (mobiusTwisted D η S ε εp Dp y))
    linarith
  refine ⟨hnotmem, ?_⟩
  have hfl := S.hfootval y hnotmem hband
  obtain ⟨j, t, hjt⟩ := S.L.cover _ hfl
  by_cases hji : j = S.i
  · exfalso
    have h1 : ‖mobiusTwisted D η S ε εp Dp y‖ ≤ Dp + 3 :=
      mobiusTwisted_norm_le_marked (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp) hDp
        (y := y) (t := t) hnotmem (by rw [hji] at hjt; exact hjt)
    have h2 : ‖proj2 (mobiusTwisted D η S ε εp Dp y)‖
        ≤ ‖mobiusTwisted D η S ε εp Dp y‖ := norm_proj2_le _
    have h3 := htri (proj2 (mobiusTwisted D η S ε εp Dp y))
    linarith
  · by_cases hjk : j = k
    · exact ⟨t, by rw [hjk] at hjt; exact hjt⟩
    · exfalso
      have hval := mobiusTwisted_far_proj (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp)
        hε hε19 hεp hεp19 (j := j) hji (y := y) (t := t) hnotmem hjt
      have hd1 : ‖proj2 (mobiusTwisted D η S ε εp Dp y) - mfrO S.n S.i Dp j‖ = 1 := by
        rw [hval, mfrO_of_ne S.n S.i Dp hji, add_sub_cancel_left, Work.Drive.N2C.norm_proj2_ang]
      have h5 : 5 ≤ ‖mfrO S.n S.i Dp k - mfrO S.n S.i Dp j‖ :=
        mfrO_dist_ge S.n S.i Dp hk hji (fun h => hjk h.symm)
      have h6 : ‖mfrO S.n S.i Dp k - mfrO S.n S.i Dp j‖
          ≤ ‖mfrO S.n S.i Dp k - proj2 (mobiusTwisted D η S ε εp Dp y)‖
            + ‖proj2 (mobiusTwisted D η S ε εp Dp y) - mfrO S.n S.i Dp j‖ := by
        have h := norm_add_le
          (mfrO S.n S.i Dp k - proj2 (mobiusTwisted D η S ε εp Dp y))
          (proj2 (mobiusTwisted D η S ε εp Dp y) - mfrO S.n S.i Dp j)
        rwa [sub_add_sub_cancel] at h
      rw [hd1] at *
      linarith

/-- **The classification of a level point on the negative ray of a far region.**  If the picture lies
on the ray `o k - s` (`s > 0`, `k ≠ i`), then the point is outside the model region and its foot is
the point `γ k (1/2)` of the parked component `k`. -/
theorem mfr_ray_foot {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (S : Work.Drive.N2Lead.MobiusPacket D η)
    {ε εp Dp : ℝ} (hε : 0 < ε) (hε19 : ε ≤ 19) (hεp : 0 < εp) (hεp19 : εp ≤ 19) (hDp : 0 ≤ Dp)
    {k : Fin S.n} (hk : k ≠ S.i) {y : M} (hy : f y = f p + 3 * η / 2)
    (hs : ∃ s : ℝ, 0 < s ∧ proj2 (mobiusTwisted D η S ε εp Dp y)
        = mfrO S.n S.i Dp k + s • (-1 : ℂ)) :
    y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20) ∧
      Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ k (1 / 2) := by
  obtain ⟨s, hs0, hsz⟩ := hs
  have hband : f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) := by
    rw [hy]; constructor <;> linarith
  have him : (proj2 (mobiusTwisted D η S ε εp Dp y)).im = 20 + 5 * ((k : ℕ) : ℝ) + Dp := by
    rw [hsz]
    exact im_mfrO_add_smul_neg S.n S.i Dp hk s
  have hznorm : Dp + 20 ≤ ‖proj2 (mobiusTwisted D η S ε εp Dp y)‖ := by
    have h1 := Complex.abs_im_le_norm (proj2 (mobiusTwisted D η S ε εp Dp y))
    rw [him] at h1
    have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_of_nonneg (by linarith)] at h1
    linarith
  have hnotmem : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
      S.Z (39 / 20) := by
    intro hmem
    have h1 : ‖mobiusTwisted D η S ε εp Dp y‖ ≤ Dp + 2 :=
      mobiusUpperModelNorm (D := D) hη hsmall S (ε := ε) (εp := εp) hDp y hy hmem
    have h2 : ‖proj2 (mobiusTwisted D η S ε εp Dp y)‖
        ≤ ‖mobiusTwisted D η S ε εp Dp y‖ := norm_proj2_le _
    linarith
  have hfl := S.hfootval y hnotmem hband
  obtain ⟨j, t, hjt⟩ := S.L.cover _ hfl
  by_cases hji : j = S.i
  · exfalso
    have h1 : ‖mobiusTwisted D η S ε εp Dp y‖ ≤ Dp + 3 :=
      mobiusTwisted_norm_le_marked (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp) hDp
        (y := y) (t := t) hnotmem (by rw [hji] at hjt; exact hjt)
    have h2 : ‖proj2 (mobiusTwisted D η S ε εp Dp y)‖
        ≤ ‖mobiusTwisted D η S ε εp Dp y‖ := norm_proj2_le _
    linarith
  · have hval := mobiusTwisted_far_proj (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp)
      hε hε19 hεp hεp19 (j := j) hji (y := y) (t := t) hnotmem hjt
    have him2 : (proj2 (mobiusTwisted D η S ε εp Dp y)).im
        = 20 + 5 * ((j : ℕ) : ℝ) + Dp + Real.sin (2 * Real.pi * t) := by
      rw [hval]
      exact im_far_add S.n j Dp t
    have hre2 : (proj2 (mobiusTwisted D η S ε εp Dp y)).re = -20 + Real.cos (2 * Real.pi * t) := by
      rw [hval]
      exact re_far_add S.n j Dp t
    have hre1 : (proj2 (mobiusTwisted D η S ε εp Dp y)).re = -20 - s := by
      rw [hsz]
      exact re_mfrO_add_smul_neg S.n S.i Dp hk s
    have hsin : Real.sin (2 * Real.pi * t) = 5 * (((k : ℕ) : ℝ) - ((j : ℕ) : ℝ)) := by linarith
    have hcos : Real.cos (2 * Real.pi * t) = -s := by linarith
    have hc : |((k : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ 1 / 5 := by
      have h1 : |5 * (((k : ℕ) : ℝ) - ((j : ℕ) : ℝ))| ≤ 1 := by
        rw [← hsin]; exact Real.abs_sin_le_one _
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)] at h1
      linarith
    have hkj : ((k : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
      refine le_antisymm ?_ ?_
      · by_contra h
        have hlt : (j : ℕ) < (k : ℕ) := by
          have : ((j : ℕ) : ℝ) < ((k : ℕ) : ℝ) := lt_of_not_ge h
          exact_mod_cast this
        have h1 : ((j : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by
          have : (j : ℕ) + 1 ≤ (k : ℕ) := by omega
          exact_mod_cast this
        have h2 : 0 ≤ ((k : ℕ) : ℝ) - ((j : ℕ) : ℝ) := by linarith
        rw [abs_of_nonneg h2] at hc
        linarith
      · by_contra h
        have hlt : (k : ℕ) < (j : ℕ) := by
          have : ((k : ℕ) : ℝ) < ((j : ℕ) : ℝ) := lt_of_not_ge h
          exact_mod_cast this
        have h1 : ((k : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
          have : (k : ℕ) + 1 ≤ (j : ℕ) := by omega
          exact_mod_cast this
        have h2 : ((k : ℕ) : ℝ) - ((j : ℕ) : ℝ) ≤ 0 := by linarith
        rw [abs_of_nonpos h2] at hc
        linarith
    have hjeq : j = k := Fin.ext (by exact_mod_cast hkj.symm)
    have hsin0 : Real.sin (2 * Real.pi * t) = 0 := by
      rw [hsin, hkj]; ring
    have hs1 : s = 1 := by
      have hsq := Real.cos_sq_add_sin_sq (2 * Real.pi * t)
      rw [hcos, hsin0] at hsq
      have hs2 : s ^ 2 = 1 := by nlinarith [hsq]
      rcases sq_eq_one_iff.mp hs2 with h | h
      · exact h
      · linarith
    have hcos1 : Real.cos (2 * Real.pi * t) = -1 := by rw [hcos, hs1]
    obtain ⟨m2, hm2⟩ := Real.cos_eq_neg_one_iff.mp hcos1
    have ht : t = 1 / 2 + (m2 : ℝ) := by
      have h2 : 2 * Real.pi * t = 2 * Real.pi * (1 / 2 + (m2 : ℝ)) := by
        rw [← hm2]; ring
      exact mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) h2
    have hgamma : S.L.γ k t = S.L.γ k (1 / 2) := by
      have hper : Function.Periodic (S.L.γ k) 1 := fun x => S.L.per k x
      rw [ht]
      simpa using (hper.int_mul m2) (1 / 2)
    refine ⟨hnotmem, ?_⟩
    rw [hjeq] at hjt
    exact hjt.trans hgamma



/-- **The star rows of the twisted Möbius upper picture, at a fixed triple, from the marked rows.**

`G := mobiusTwisted D η S ε εp Dp` is the twisted Möbius window drawing at the level
`u⁺ = f p + 3η/2`; its planar picture is `proj2 (G y)` and `Work.Drive.N2Lead.proj2` is the
`(x,y)`-projection `E3 → ℂ`.

Take `K := S.n`,
`Ω k := if k = S.i then Metric.ball 0 (Dp + 5) else Metric.ball (proj2 (farPos S.n k) + (Dp:ℂ)*I) 2`,
`o k := if k = S.i then 0 else proj2 (farPos S.n k) + (Dp:ℂ)*I`, `ρ := fun _ => 1/2`,
`e k := if k = S.i then 1 else -1`.

The statement says that these regions satisfy the whole star-regions interface at the *same* triple
`(ε, εp, Dp)`, given only `ε ≤ 19`, `εp ≤ 19`, `Dp ≥ 0` and the three *marked* rows (`hne`, `hrate`,
`hray` for the single region `ball 0 (Dp+5)` with centre `0`).

Hints (all the cited lemmas are proved and `sorry`-free):

* `proj2_farPos` in `Submission.Work.Drive.N2C.lowerCert` gives `proj2 (farPos S.n k) =
  ⟨-20, 20 + 5 * k⟩`, so `‖o k‖ ≥ 20 + 5k + Dp ≥ Dp + 20` for `k ≠ S.i`, while `‖o S.i‖ = 0` and
  `‖o k - o l‖ ≥ 5` for `k ≠ l`, both `≠ S.i`.  This gives `closedBall (o k) (1/2) ⊆ Ω k` and the
  pairwise disjointness (`ball 0 (Dp+5)` is disjoint from `ball (o k) 2` because `Dp + 20 > Dp + 7`).
* COVER: for `f y = u⁺`, either `y ∈ saddleRegion … (39/20)` (then
  `mobiusUpperModelNorm` gives `‖G y‖ ≤ Dp + 2`), or `y ∉ saddleRegion`; in the latter case
  `S.hfootval y hy hband` writes the foot as `S.L.γ j t`.  For `j = S.i`
  `mobiusTwisted_norm_le_marked` gives `‖G y‖ ≤ Dp + 3`, and for `j ≠ S.i`
  `mobiusTwisted_far_proj` (needs `ε ≤ 19`, `εp ≤ 19`) gives
  `proj2 (G y) = o j + proj2 (ang t)` with `‖proj2 (ang t)‖ = 1` (`norm_proj2_ang`), so
  `proj2 (G y) ∈ Ω j` with radius `1 < 2`.
* RATE for `k ≠ S.i`: membership in `Ω k` forces `y ∉ saddleRegion` with foot on the far component
  `j = k`: if `y` were a model point or had foot on `S.i`, then `‖proj2 (G y)‖ ≤ Dp + 3`, whereas
  `dist (z, o k) ≥ ‖o k‖ - ‖z‖ ≥ (Dp + 20) - (Dp + 3) = 17 > 2`; and if the far foot were on
  `j ≠ k`, then `dist (proj2 (G y), o j) = 1` so `dist (proj2 (G y), o k) ≥ ‖o j - o k‖ - 1 ≥ 4 > 2`.
  Then `mfrFarPiece` gives exactly the required row (non-radiality about `o k`) and
  `proj2 (G y) ≠ o k` since `dist (proj2 (G y), o k) = 1`.
* RAY for `k ≠ S.i` (`e k = -1`): if `proj2 (G x) = o k - s` (`s > 0`), then
  `Im (proj2 (G x)) = 20 + 5k + Dp ≥ Dp + 20`, which rules out `x` being a model point or having a
  marked foot (`‖proj2 (G x)‖ ≤ Dp + 3` there), so `x` has a far foot on some `j ≠ S.i`; writing it
  as `S.L.γ j t` and using `proj2 (G x) = o j + proj2 (ang t)` with `proj2_ang t = exp (i 2πt)` and
  `proj2_farPos` gives `sin (2πt) = 5 (k - j)` (hence `j = k` and `sin (2πt) = 0`) and
  `cos (2πt) = -s < 0` (hence `t ≡ 1/2 (mod 1)`); so `S.L.γ k t = S.L.γ k (1/2)`, and since `y`
  satisfies the same, `foot x = foot y`, hence `G x = G y` by `mobiusTwisted_foot`, and `x = y` by
  injectivity of `G` on the level (`mobiusGoodDrawing` plus
  `pushY_injective`/`twistX_injective`/`twistY_injective` from
  `Submission.Work.Drive.N2Lead.twistToolkit`).
* RATE about `o S.i = 0` and RAY `e S.i = 1` are the hypotheses `hrate`/`hray` verbatim (note
  `‖proj2 (G y)‖ < Dp + 5` on the open ball gives `≤ Dp + 5`).-/
theorem mfrStarRowsOfMarkedRows {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S)
    {ε εp Dp : ℝ} (hε : 0 < ε) (hε19 : ε ≤ 19) (hεp : 0 < εp) (hεp19 : εp ≤ 19) (hDp : 0 ≤ Dp)
    (hne : ∀ y : M, f y = f p + 3 * η / 2 →
      Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) ≠ 0)
    (hrate : ∀ (y : M), f y = f p + 3 * η / 2 →
      ‖Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)‖ ≤ Dp + 5 →
      ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y,
        mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ ℝ) f y v = 0 → v ≠ 0 →
        ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ ℂ)
            (fun z : M => Work.Drive.N2Lead.proj2
              (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
          = t • Work.Drive.N2Lead.proj2
              (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)))
    (hray : ∀ x y : M, f x = f p + 3 * η / 2 → f y = f p + 3 * η / 2 →
      (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
          (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp x) = ((s : ℝ) : ℂ)) →
      (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
          (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) = ((s : ℝ) : ℂ)) →
      x = y) :
    ∃ (K : ℕ) (Ω : Fin K → Set ℂ) (o : Fin K → ℂ) (ρ : Fin K → ℝ) (e : Fin K → ℂ),
      (∀ k, IsOpen (Ω k) ∧ Convex ℝ (Ω k)) ∧ (∀ k, 0 < ρ k) ∧
      (∀ k, Metric.closedBall (o k) (ρ k) ⊆ Ω k) ∧ (Pairwise fun k l => Disjoint (Ω k) (Ω l)) ∧
      (∀ y : M, f y = f p + 3 * η / 2 → ∃ k, Work.Drive.N2Lead.proj2
        (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) ∈ Ω k) ∧
      (∀ (y : M) (k : Fin K), f y = f p + 3 * η / 2 → Work.Drive.N2Lead.proj2
          (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) ∈ Ω k →
        Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) ≠ o k ∧
        ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y,
          mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ ℝ) f y v = 0 → v ≠ 0 →
          ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
              (modelWithCornersSelf ℝ ℂ) (fun z : M => Work.Drive.N2Lead.proj2
                (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
            = t • (Work.Drive.N2Lead.proj2
                (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) - o k))) ∧
      (∀ k : Fin K, e k ≠ 0 ∧ ∀ x y : M, f x = f p + 3 * η / 2 → f y = f p + 3 * η / 2 →
        (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
            (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp x) = o k + s • e k) →
        (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
            (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) = o k + s • e k) → x = y) := by
  have hband : f p + 3 * η / 2 ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) := by
    constructor <;> linarith
  have hcov : ∀ y : M, f y = f p + 3 * η / 2 → ∃ k : Fin S.n,
      proj2 (mobiusTwisted D η S ε εp Dp y) ∈ mfrOm S.n S.i Dp k := by
    intro y hy
    by_cases hreg : y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
        S.Z (39 / 20)
    · refine ⟨S.i, ?_⟩
      rw [mfrOm_self, Metric.mem_ball, dist_zero_right]
      have h1 := mobiusUpperModelNorm (D := D) hη hsmall S (ε := ε) (εp := εp) hDp y hy hreg
      have h2 := norm_proj2_le (mobiusTwisted D η S ε εp Dp y)
      linarith
    · have hfl := S.hfootval y hreg (by rw [hy]; exact hband)
      obtain ⟨j, t, hjt⟩ := S.L.cover _ hfl
      by_cases hji : j = S.i
      · refine ⟨S.i, ?_⟩
        rw [mfrOm_self, Metric.mem_ball, dist_zero_right]
        have h1 := mobiusTwisted_norm_le_marked (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp)
          hDp (y := y) (t := t) hreg (by rw [hji] at hjt; exact hjt)
        have h2 := norm_proj2_le (mobiusTwisted D η S ε εp Dp y)
        linarith
      · refine ⟨j, ?_⟩
        rw [mfrOm_of_ne S.n S.i Dp hji, Metric.mem_ball, dist_eq_norm]
        have hval := mobiusTwisted_far_proj (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp)
          hε hε19 hεp hεp19 (j := j) hji (y := y) (t := t) hreg hjt
        rw [hval, mfrO_of_ne S.n S.i Dp hji, add_sub_cancel_left, Work.Drive.N2C.norm_proj2_ang]
        norm_num
  have hrate' : ∀ (y : M) (k : Fin S.n), f y = f p + 3 * η / 2 →
      proj2 (mobiusTwisted D η S ε εp Dp y) ∈ mfrOm S.n S.i Dp k →
      proj2 (mobiusTwisted D η S ε εp Dp y) ≠ mfrO S.n S.i Dp k ∧
      ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y,
        mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ ℝ) f y v = 0 → v ≠ 0 →
        ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ ℂ)
            (fun z : M => proj2 (mobiusTwisted D η S ε εp Dp z)) y v
          = t • (proj2 (mobiusTwisted D η S ε εp Dp y) - mfrO S.n S.i Dp k)) := by
    intro y k hy hz
    by_cases hk : k = S.i
    · subst hk
      rw [mfrOm_self, Metric.mem_ball, dist_zero_right] at hz
      rw [mfrO_self]
      refine ⟨hne y hy, ?_⟩
      intro v hv hvne h
      obtain ⟨t, ht⟩ := h
      exact hrate y hy (le_of_lt hz) v hv hvne ⟨t, by simpa using ht⟩
    · have hz2 : dist (proj2 (mobiusTwisted D η S ε εp Dp y)) (mfrO S.n S.i Dp k) < 2 := by
        rw [mfrOm_of_ne S.n S.i Dp hk, Metric.mem_ball] at hz
        exact hz
      obtain ⟨hnotmem, t, hjt⟩ := mfr_far_classify (D := D) hη hsmall S hε hε19 hεp hεp19 hDp
        hk hy hz2
      have hfp := Work.Drive.N2C.mfrFarPiece (D := D) hη hsmall hf S hε hε19 hεp hεp19 hDp hk hy hnotmem hjt
      obtain ⟨-, hneF, hrateF⟩ := hfp
      rw [mfrO_of_ne S.n S.i Dp hk]
      exact ⟨hneF, fun v hv hvne h => by
        obtain ⟨t', ht'⟩ := h
        exact hrateF v hv hvne ⟨t', ht'⟩⟩
  have hray' : ∀ k : Fin S.n, mfrE S.n S.i k ≠ 0 ∧
      ∀ x y : M, f x = f p + 3 * η / 2 → f y = f p + 3 * η / 2 →
        (∃ s : ℝ, 0 < s ∧ proj2 (mobiusTwisted D η S ε εp Dp x)
            = mfrO S.n S.i Dp k + s • mfrE S.n S.i k) →
        (∃ s : ℝ, 0 < s ∧ proj2 (mobiusTwisted D η S ε εp Dp y)
            = mfrO S.n S.i Dp k + s • mfrE S.n S.i k) → x = y := by
    intro k
    by_cases hk : k = S.i
    · subst hk
      refine ⟨by rw [mfrE_self]; norm_num, ?_⟩
      intro x y hx hy hxs hys
      refine hray x y hx hy ?_ ?_
      · obtain ⟨s, hs0, hs⟩ := hxs
        rw [mfrO_self, mfrE_self] at hs
        exact ⟨s, hs0, by simpa using hs⟩
      · obtain ⟨s, hs0, hs⟩ := hys
        rw [mfrO_self, mfrE_self] at hs
        exact ⟨s, hs0, by simpa using hs⟩
    · refine ⟨by rw [mfrE_of_ne S.n S.i hk]; norm_num, ?_⟩
      intro x y hx hy hxs hys
      have hxs' : ∃ s : ℝ, 0 < s ∧ proj2 (mobiusTwisted D η S ε εp Dp x)
          = mfrO S.n S.i Dp k + s • (-1 : ℂ) := by
        obtain ⟨s, hs0, hs⟩ := hxs
        rw [mfrE_of_ne S.n S.i hk] at hs
        exact ⟨s, hs0, hs⟩
      have hys' : ∃ s : ℝ, 0 < s ∧ proj2 (mobiusTwisted D η S ε εp Dp y)
          = mfrO S.n S.i Dp k + s • (-1 : ℂ) := by
        obtain ⟨s, hs0, hs⟩ := hys
        rw [mfrE_of_ne S.n S.i hk] at hs
        exact ⟨s, hs0, hs⟩
      obtain ⟨hxnot, hxfoot⟩ := mfr_ray_foot (D := D) hη hsmall S hε hε19 hεp hεp19 hDp hk hx hxs'
      obtain ⟨hynot, hyfoot⟩ := mfr_ray_foot (D := D) hη hsmall S hε hε19 hεp hεp19 hDp hk hy hys'
      have hfooteq : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) x
          = Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y := hxfoot.trans hyfoot.symm
      have hG : mobiusTwisted D η S ε εp Dp x = mobiusTwisted D η S ε εp Dp y := by
        rw [mobiusTwisted_foot (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp) (y := x) hxnot,
          mobiusTwisted_foot (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp) (y := y) hynot,
          hfooteq]
      exact Work.Drive.N2C.mfr_injOn_level (D := D) hη hsmall hf S hεp hDp hx hy hG
  exact ⟨S.n, mfrOm S.n S.i Dp, mfrO S.n S.i Dp, fun _ => (1 / 2 : ℝ), mfrE S.n S.i,
    fun k => mfr_isOpen_convex S.n S.i Dp k, fun k => by norm_num,
    fun k => mfr_closedBall_subset S.n S.i hDp k, mfr_pairwiseDisjoint S.n S.i hDp,
    hcov, hrate', hray'⟩


end Work.Drive.N2Lead
