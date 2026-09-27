import Mathlib
import Submission.Work.Drive.diskHomotopyParam
import Submission.Work.Drive.sqDisk_foldBox_existsUnique

namespace Work.Drive

open scoped Topology

noncomputable section

/-!
## Helpers

The extra parameter `q.2` of the perturbed lift enters only through the disk point
`sqDisk (foldBox q.2)`, which always lies in the **closed unit disk**; so both the unperturbed lift and
the perturbation factor through the *compact* parameter space

> `(s, z) ∈ ℝ × ℂ`,  `s = q.1`,  `z = sqDisk (foldBox q.2)`,  `‖z‖ ≤ 1`.

On the compact set `[1/4, 3/4] × D̄` the unperturbed lift is bounded below by a positive constant
(continuity + nonvanishing), while the perturbation is `O ‖t‖` (the weights `X i` are bounded on the
closed disk and `|smoothPhi s| ≤ 1`).
-/

/-- The **unperturbed** lift, written on the compact parameter space `ℝ × ℂ`. -/
def diskHomotopyBase (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3) (s : ℝ) (z : ℂ) : Eucl 3 :=
  (1 - smoothSigma s) • V z + smoothSigma s • W z + (smoothPhi s * χ z) • p

/-- The **perturbation** of the parameter-rich lift, on the same compact parameter space. -/
def diskHomotopyPert {N : ℕ} (X : Fin N → ℂ → ℝ) (E : Fin N → Eucl 3) (t : Fin N → ℝ)
    (s : ℝ) (z : ℂ) : Eucl 3 :=
  ∑ i, (smoothPhi s * t i * X i z) • E i

/-- The norm of the unperturbed lift, as a real-valued function (kept behind a definition so that the
compactness argument below never has to unfold the norm of `Eucl 3`). -/
def diskHomotopyBaseNorm (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3) : ℝ × ℂ → ℝ :=
  fun q => ‖diskHomotopyBase V W χ p q.1 q.2‖

/-- The unperturbed lift is `diskHomotopyBase` evaluated at the disk point `sqDisk (foldBox q.2)`. -/
lemma diskHomotopyLift_eq_base (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (q : ℝ × EuclideanSpace ℝ (Fin 2)) :
    diskHomotopyLift V W χ p q = diskHomotopyBase V W χ p q.1 (sqDisk (foldBox q.2)) := rfl

/-- The perturbed lift is the unperturbed one plus `diskHomotopyPert`, at the same disk point. -/
lemma diskHomotopyLiftParam_eq_base_add {N : ℕ} (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (X : Fin N → ℂ → ℝ) (E : Fin N → Eucl 3) (t : Fin N → ℝ)
    (q : ℝ × EuclideanSpace ℝ (Fin 2)) :
    diskHomotopyLiftParam V W χ p X E t q
      = diskHomotopyBase V W χ p q.1 (sqDisk (foldBox q.2))
        + diskHomotopyPert X E t q.1 (sqDisk (foldBox q.2)) := rfl

/-- Continuity of the unperturbed lift on the compact parameter space. -/
lemma continuous_diskHomotopyBase (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (hV : Continuous V) (hW : Continuous W) (hχ : Continuous χ) :
    Continuous (fun q : ℝ × ℂ => diskHomotopyBase V W χ p q.1 q.2) := by
  have h1 : Continuous (fun q : ℝ × ℂ => (1 - smoothSigma q.1) • V q.2) :=
    ((continuous_const (y := (1 : ℝ))).sub
      (contDiff_smoothSigma.continuous.comp continuous_fst)).smul (hV.comp continuous_snd)
  have h2 : Continuous (fun q : ℝ × ℂ => smoothSigma q.1 • W q.2) :=
    (contDiff_smoothSigma.continuous.comp continuous_fst).smul (hW.comp continuous_snd)
  have h3 : Continuous (fun q : ℝ × ℂ => (smoothPhi q.1 * χ q.2) • p) :=
    ((contDiff_smoothPhi.continuous.comp continuous_fst).mul (hχ.comp continuous_snd)).smul
      continuous_const
  have h : Continuous (fun q : ℝ × ℂ =>
      (1 - smoothSigma q.1) • V q.2 + smoothSigma q.1 • W q.2 + (smoothPhi q.1 * χ q.2) • p) :=
    (h1.add h2).add h3
  simpa [diskHomotopyBase] using h

/-- Continuity of the norm of the unperturbed lift. -/
lemma continuous_diskHomotopyBaseNorm (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (hV : Continuous V) (hW : Continuous W) (hχ : Continuous χ) :
    Continuous (diskHomotopyBaseNorm V W χ p) := by
  change Continuous (fun q : ℝ × ℂ => ‖diskHomotopyBase V W χ p q.1 q.2‖)
  exact (continuous_diskHomotopyBase V W χ p hV hW hχ).norm

/-- **The unperturbed lift is nonvanishing on the compact parameter space**: on the closed disk it is
one of the three nonvanishing families of `DiskGood` (by the case analysis on `smoothSigma`). -/
lemma diskHomotopyBase_ne_zero (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (hnz : DiskGood V W χ p) :
    ∀ s : ℝ, ∀ z : ℂ, ‖z‖ ≤ 1 → diskHomotopyBase V W χ p s z ≠ 0 := by
  intro s z hz
  obtain ⟨y, hy, -⟩ := sqDisk_foldBox_existsUnique z hz
  have h := diskHomotopyLift_ne_zero V W χ p hnz (s, y)
  rwa [diskHomotopyLift_eq_base, hy.2] at h

/-- **The unperturbed lift is bounded below by a positive constant on `[1/4, 3/4] × D̄`**: it is
continuous and nowhere zero on that compact set. -/
lemma exists_diskHomotopyBase_lower_bound (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (hnz : ∀ s : ℝ, ∀ z : ℂ, ‖z‖ ≤ 1 → diskHomotopyBase V W χ p s z ≠ 0)
    (hcont : Continuous (diskHomotopyBaseNorm V W χ p)) :
    ∃ m : ℝ, 0 < m ∧ ∀ s ∈ Set.Icc (1 / 4 : ℝ) (3 / 4), ∀ z : ℂ, ‖z‖ ≤ 1 →
      m ≤ ‖diskHomotopyBase V W χ p s z‖ := by
  have hK : IsCompact (Set.Icc (1 / 4 : ℝ) (3 / 4) ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    isCompact_Icc.prod (isCompact_closedBall 0 1)
  have hne : (Set.Icc (1 / 4 : ℝ) (3 / 4) ×ˢ Metric.closedBall (0 : ℂ) 1).Nonempty :=
    ⟨(1 / 2, 0), ⟨by norm_num, by simp [Metric.mem_closedBall]⟩⟩
  obtain ⟨x, hxK, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  refine ⟨diskHomotopyBaseNorm V W χ p x, ?_, ?_⟩
  · simpa only [diskHomotopyBaseNorm] using
      norm_pos_iff.mpr (hnz x.1 x.2 (by simpa [Metric.mem_closedBall] using hxK.2))
  · intro s hs z hz
    simpa only [diskHomotopyBaseNorm, Set.mem_ofPred_eq] using
      hmin (Set.mk_mem_prod hs (by simpa [Metric.mem_closedBall] using hz))

/-- **The perturbation is `O ‖t‖`**: the weights `X i` are bounded on the closed disk, `|smoothPhi| ≤ 1`
everywhere and `|t i| ≤ ‖t‖`. -/
lemma norm_diskHomotopyPert_le {N : ℕ} (X : Fin N → ℂ → ℝ) (E : Fin N → Eucl 3) (M : Fin N → ℝ)
    (hM : ∀ i z, ‖z‖ ≤ 1 → |X i z| ≤ M i) (t : Fin N → ℝ) (s : ℝ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖diskHomotopyPert X E t s z‖ ≤ ‖t‖ * ∑ i, M i * ‖E i‖ := by
  have hφ : |smoothPhi s| ≤ 1 := by
    rw [abs_of_nonneg (smoothPhi_mem s).1]; exact (smoothPhi_mem s).2
  have hterm : ∀ i : Fin N,
      ‖(smoothPhi s * t i * X i z) • E i‖ ≤ ‖t‖ * (M i * ‖E i‖) := by
    intro i
    have hti : |t i| ≤ ‖t‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm t i
    have hMi : 0 ≤ M i := le_trans (abs_nonneg _) (hM i 0 (by simp))
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 : |smoothPhi s| * |t i| ≤ 1 * ‖t‖ :=
      mul_le_mul hφ hti (abs_nonneg _) (by norm_num)
    have h2 : (|smoothPhi s| * |t i|) * |X i z| ≤ (1 * ‖t‖) * M i :=
      mul_le_mul h1 (hM i z hz) (abs_nonneg _) (by positivity)
    have h3 : ((|smoothPhi s| * |t i|) * |X i z|) * ‖E i‖ ≤ ((1 * ‖t‖) * M i) * ‖E i‖ :=
      mul_le_mul h2 le_rfl (norm_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) hMi)
    calc ((|smoothPhi s| * |t i|) * |X i z|) * ‖E i‖ ≤ ((1 * ‖t‖) * M i) * ‖E i‖ := h3
      _ = ‖t‖ * (M i * ‖E i‖) := by ring
  have hsum : ‖∑ i, (smoothPhi s * t i * X i z) • E i‖ ≤ ∑ i, ‖t‖ * (M i * ‖E i‖) :=
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => hterm i))
  rw [diskHomotopyPert]
  calc ‖∑ i, (smoothPhi s * t i * X i z) • E i‖ ≤ ∑ i, ‖t‖ * (M i * ‖E i‖) := hsum
    _ = ‖t‖ * ∑ i, M i * ‖E i‖ := by rw [Finset.mul_sum]

/-- A uniform bound for the weights `X i` on the closed unit disk. -/
lemma exists_bound_of_smooth_X {N : ℕ} (X : Fin N → ℂ → ℝ) (hX : ∀ i, Continuous (X i)) :
    ∃ M : Fin N → ℝ, ∀ i z, ‖z‖ ≤ 1 → |X i z| ≤ M i := by
  have h : ∀ i : Fin N, ∃ M : ℝ, ∀ z : ℂ, ‖z‖ ≤ 1 → |X i z| ≤ M := by
    intro i
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn (hX i).continuousOn
    exact ⟨C, fun z hz => by
      simpa [Real.norm_eq_abs, Metric.mem_closedBall] using hC z (by simpa [Metric.mem_closedBall] using hz)⟩
  choose M hM using h
  exact ⟨M, hM⟩

/-- **The perturbation is small for small parameters.**  If the unperturbed disk-homotopy data is
nonvanishing (`Work.Drive.DiskGood V W χ p`) then there is `δ > 0` such that for every parameter `t`
with `‖t‖ < δ` the perturbed lift `Work.Drive.diskHomotopyLiftParam V W χ p X E t` is nonvanishing
everywhere.  (The perturbed lift is the unperturbed one plus
`∑ i, (smoothPhi q.1 * t i * X i (sqDisk (foldBox q.2))) • E i`; the perturbation vanishes outside
`[1/4, 3/4]` in the first coordinate, and on the compact set `[1/4, 3/4] × □` the unperturbed lift is
bounded below by a positive constant while the perturbation is `O ‖t‖`.) -/
theorem exists_small_diskHomotopyLiftParam_ne_zero {N : ℕ} (V W : ℂ → Eucl 3) (χ : ℂ → ℝ)
    (p : Eucl 3) (X : Fin N → ℂ → ℝ) (E : Fin N → Eucl 3)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hX : ∀ i : Fin N, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (X i))
    (hVne : ∀ z : ℂ, V z ≠ 0) (hWne : ∀ z : ℂ, W z ≠ 0)
    (hnz : Work.Drive.DiskGood V W χ p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : Fin N → ℝ, ‖t‖ < δ →
      ∀ q : ℝ × EuclideanSpace ℝ (Fin 2),
        Work.Drive.diskHomotopyLiftParam V W χ p X E t q ≠ 0 := by
  -- the disk point of a parameter `q`, always in the closed unit disk
  have hdisk : ∀ q : ℝ × EuclideanSpace ℝ (Fin 2),
      ‖sqDisk (foldBox q.2)‖ ≤ 1 :=
    fun q => norm_sqDisk_le_one _ (foldBox_mem_unitBox q.2)
  -- the unperturbed lift is nonvanishing on `ℝ × D̄`
  have hbase : ∀ s : ℝ, ∀ z : ℂ, ‖z‖ ≤ 1 → diskHomotopyBase V W χ p s z ≠ 0 :=
    diskHomotopyBase_ne_zero V W χ p hnz
  -- a positive lower bound on `[1/4, 3/4] × D̄`
  obtain ⟨m, hmpos, hm⟩ := exists_diskHomotopyBase_lower_bound V W χ p hbase
    (continuous_diskHomotopyBaseNorm V W χ p hV.continuous hW.continuous hχ.continuous)
  -- a bound for the weights on the closed disk
  obtain ⟨M, hM⟩ := exists_bound_of_smooth_X X (fun i => (hX i).continuous)
  have hMi : ∀ i : Fin N, 0 ≤ M i := fun i => le_trans (abs_nonneg _) (hM i 0 (by simp))
  set C : ℝ := ∑ i, M i * ‖E i‖ with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hMi i) (norm_nonneg _))
  have hCpos : 0 < C + 1 := by linarith
  refine ⟨m / (2 * (C + 1)), div_pos hmpos (by linarith), ?_⟩
  intro t ht q
  have htC : ‖t‖ * (C + 1) < m / 2 := by
    have h2 : (0 : ℝ) < 2 * (C + 1) := by linarith
    have h3 := (lt_div_iff₀ h2).mp ht
    linarith
  have hpert : ‖diskHomotopyPert X E t q.1 (sqDisk (foldBox q.2))‖ ≤ ‖t‖ * C := by
    have h := norm_diskHomotopyPert_le X E M hM t q.1 (sqDisk (foldBox q.2)) (hdisk q)
    rwa [← hCdef] at h
  by_cases hq : q.1 ∈ Set.Icc (1 / 4 : ℝ) (3 / 4)
  · -- inside `[1/4, 3/4]` the unperturbed lift dominates the perturbation
    have hlow : m ≤ ‖diskHomotopyBase V W χ p q.1 (sqDisk (foldBox q.2))‖ :=
      hm q.1 hq _ (hdisk q)
    intro hzero
    rw [diskHomotopyLiftParam_eq_base_add] at hzero
    have hz0 : ‖diskHomotopyBase V W χ p q.1 (sqDisk (foldBox q.2))
        + diskHomotopyPert X E t q.1 (sqDisk (foldBox q.2))‖ = 0 := by
      rw [hzero, norm_zero]
    have hstep : m ≤ ‖diskHomotopyPert X E t q.1 (sqDisk (foldBox q.2))‖ := by
      calc m ≤ ‖diskHomotopyBase V W χ p q.1 (sqDisk (foldBox q.2))‖ := hlow
        _ = ‖(diskHomotopyBase V W χ p q.1 (sqDisk (foldBox q.2))
              + diskHomotopyPert X E t q.1 (sqDisk (foldBox q.2)))
              - diskHomotopyPert X E t q.1 (sqDisk (foldBox q.2))‖ := by
              rw [add_sub_cancel_right]
        _ ≤ ‖diskHomotopyBase V W χ p q.1 (sqDisk (foldBox q.2))
              + diskHomotopyPert X E t q.1 (sqDisk (foldBox q.2))‖
            + ‖diskHomotopyPert X E t q.1 (sqDisk (foldBox q.2))‖ := norm_sub_le _ _
        _ = ‖diskHomotopyPert X E t q.1 (sqDisk (foldBox q.2))‖ := by rw [hz0, zero_add]
    have hle : m ≤ ‖t‖ * (C + 1) :=
      le_trans hstep (le_trans hpert (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg t)))
    linarith
  · -- outside `[1/4, 3/4]` the perturbation vanishes identically
    have hφ0 : smoothPhi q.1 = 0 := by
      rcases (show q.1 < 1 / 4 ∨ 3 / 4 < q.1 by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hq) with h | h
      · exact smoothPhi_eq_zero_of_lt h
      · exact smoothPhi_eq_zero_of_gt h
    have hpert0 : diskHomotopyPert X E t q.1 (sqDisk (foldBox q.2)) = 0 := by
      rw [diskHomotopyPert]
      simp [hφ0]
    rw [diskHomotopyLiftParam_eq_base_add, hpert0, add_zero]
    exact hbase q.1 _ (hdisk q)

end

end Work.Drive
