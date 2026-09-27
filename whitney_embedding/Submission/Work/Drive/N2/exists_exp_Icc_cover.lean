import Mathlib

/-!
# A closed connected subset of the circle with nonempty interior is an arc

`Work.Drive.N2.exists_exp_Icc_cover`: a closed connected subset `A` of the unit circle with
nonempty interior is the image of a closed interval of length at most `2π` under `Circle.exp`.

The proof cuts the circle at a point `c ∉ A`: the *argument chart*
`expChart θ₀ c z = θ₀ + arg (z * (-c)⁻¹)` is continuous at every point of `A` (its only
discontinuity is at `c`), satisfies `Circle.exp (expChart θ₀ c z) = z` whenever `Circle.exp θ₀ = -c`,
and maps `A` into an open interval of length `2π`.  Its image of `A` is therefore a compact
preconnected subset of `ℝ`, i.e. a closed interval `Icc a b`, and `A = Circle.exp '' Icc a b`.
-/

namespace Work.Drive.N2

open Set Function Metric Filter
open scoped Topology

/-- The argument chart of the circle cut at the point `c`: for `Circle.exp θ = -c` it is a
continuous (at every point `≠ c`) real logarithm of the identity, `Circle.exp (expChart θ c z) = z`. -/
noncomputable def expChart (θ : ℝ) (c z : Circle) : ℝ := θ + (↑(z * (-c)⁻¹) : ℂ).arg

/-- A point of the circle different from `-1` lies in the slit plane, where `Complex.arg` is
continuous. -/
lemma mem_slitPlane_of_ne_neg_one {w : Circle} (hw : w ≠ -1) : (↑w : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  obtain ⟨hre, him⟩ := h
  have hsq : (↑w : ℂ).re ^ 2 + (↑w : ℂ).im ^ 2 = 1 := by
    have h2 : Complex.normSq (↑w : ℂ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]; norm_num
    rw [Complex.normSq_apply] at h2
    nlinarith [h2]
  have hre' : (↑w : ℂ).re = -1 := by nlinarith
  apply hw
  refine Subtype.ext ?_
  rw [show (↑(-1 : Circle) : ℂ) = -1 by simp]
  exact Complex.ext hre' (by simpa using him)

/-- The argument chart is continuous away from its cut point. -/
lemma expChart_continuousAt (θ : ℝ) {c z : Circle} (hz : z ≠ c) :
    ContinuousAt (expChart θ c) z := by
  have hzc : z * (-c)⁻¹ ≠ -1 := by
    intro h
    apply hz
    have h2 := congrArg (fun w : Circle => w * (-c)) h
    simpa using h2
  have h1 : ContinuousAt (fun w : Circle => (↑w : ℂ).arg) (z * (-c)⁻¹) :=
    (Complex.continuousAt_arg (mem_slitPlane_of_ne_neg_one hzc)).comp
      continuous_subtype_val.continuousAt
  have h2 : ContinuousAt (fun w : Circle => w * (-c)⁻¹) z :=
    (continuous_id.mul continuous_const).continuousAt
  have h3 : ContinuousAt (fun w : Circle => θ + (↑(w * (-c)⁻¹) : ℂ).arg) z :=
    (h1.comp (f := fun w : Circle => w * (-c)⁻¹) h2).const_add θ
  exact h3

/-- The argument chart is a logarithm: `exp (expChart θ c z) = z` as soon as `exp θ = -c`. -/
lemma expChart_exp (θ : ℝ) {c : Circle} (hθ : Circle.exp θ = -c) (z : Circle) :
    Circle.exp (expChart θ c z) = z := by
  simp only [expChart, Circle.exp_add, hθ, Circle.exp_arg]
  rw [← mul_assoc, mul_comm (-c) z, mul_inv_cancel_right]

/-- The argument chart with cut at `c` takes its values in an interval of length `2π`. -/
lemma expChart_mem_Ioc (θ : ℝ) (c z : Circle) :
    expChart θ c z ∈ Ioc (θ - Real.pi) (θ + Real.pi) := by
  constructor
  · simp only [expChart]; linarith [Complex.neg_pi_lt_arg (↑(z * (-c)⁻¹) : ℂ)]
  · simp only [expChart]; linarith [Complex.arg_le_pi (↑(z * (-c)⁻¹) : ℂ)]

/-- A set with nonempty interior in the circle has at least two points. -/
lemma exists_two_points_of_interior_nonempty {A : Set Circle} (h : ∃ z, z ∈ interior A) :
    ∃ z ∈ A, ∃ w ∈ A, z ≠ w := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz)
  have hcont : ContinuousAt (fun s : ℝ => z * Circle.exp s) 0 :=
    (continuous_const.mul Circle.exp.continuous).continuousAt
  have hmem : (fun s : ℝ => z * Circle.exp s) ⁻¹' Metric.ball z ε ∈ 𝓝 (0 : ℝ) := by
    have h : Metric.ball z ε ∈ 𝓝 (z * Circle.exp 0) := by simpa using Metric.ball_mem_nhds z hε
    exact hcont.preimage_mem_nhds h
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hmem
  set t : ℝ := min δ 1 / 2 with ht
  have hmin : 0 < min δ 1 := lt_min hδ zero_lt_one
  have htpos : 0 < t := by rw [ht]; linarith
  have htlt : t < δ := by rw [ht]; linarith [min_le_left δ 1, hδ]
  have ht2 : t < 2 * Real.pi := by
    rw [ht]; nlinarith [min_le_right δ 1, Real.pi_gt_three]
  refine ⟨z, interior_subset hz, z * Circle.exp t, interior_subset (hball (hδsub ?_)), ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]; exact htlt
  · intro heq
    have h1 : Circle.exp t = 1 := by
      have h := congrArg (fun w : Circle => z⁻¹ * w) heq
      simpa using h.symm
    have hinj : InjOn Circle.exp (Set.Ico 0 (2 * Real.pi)) :=
      Circle.exp_injOn_Ico (by linarith)
    have htI : t ∈ Set.Ico 0 (2 * Real.pi) := ⟨htpos.le, ht2⟩
    have h0I : (0 : ℝ) ∈ Set.Ico 0 (2 * Real.pi) := ⟨le_refl 0, Real.two_pi_pos⟩
    have := hinj htI h0I (by rw [h1, Circle.exp_zero])
    linarith

theorem exists_exp_Icc_cover {A : Set Circle} (hclosed : IsClosed A) (hconn : IsConnected A)
    (hint : ∃ z, z ∈ interior A) :
    ∃ α β : ℝ, α < β ∧ β - α ≤ 2 * Real.pi ∧ A = Circle.exp '' Set.Icc α β := by
  classical
  by_cases huniv : A = univ
  · refine ⟨0, 2 * Real.pi, by positivity, by linarith, ?_⟩
    rw [huniv, ← Circle.exp_surjective.range_eq]
    simpa only [zero_add] using (Circle.periodic_exp.image_Icc Real.two_pi_pos (0 : ℝ)).symm
  · -- cut the circle at a point `c` outside `A`
    obtain ⟨c, hc⟩ : ∃ c, c ∉ A := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact huniv (Set.eq_univ_iff_forall.mpr h)
    obtain ⟨θ₀, hθ₀⟩ := Circle.exp_surjective (-c)
    set B : Set ℝ := expChart θ₀ c '' A with hBdef
    have hcont : ContinuousOn (expChart θ₀ c) A :=
      fun z hz => (expChart_continuousAt θ₀ (fun h => hc (by rw [← h]; exact hz))).continuousWithinAt
    have hpc : IsPreconnected B := hconn.isPreconnected.image _ hcont
    have hcomp : IsCompact B := hclosed.isCompact.image_of_continuousOn hcont
    have hBcl : IsClosed B := hcomp.isClosed
    have hBne : B.Nonempty := hconn.nonempty.image _
    have hBsub : B ⊆ Set.Ioc (θ₀ - Real.pi) (θ₀ + Real.pi) := by
      rintro t ⟨z, hz, rfl⟩
      exact expChart_mem_Ioc θ₀ c z
    have hbd : BddBelow B := ⟨θ₀ - Real.pi, fun t ht => (hBsub ht).1.le⟩
    have hbu : BddAbove B := ⟨θ₀ + Real.pi, fun t ht => (hBsub ht).2⟩
    have haB : sInf B ∈ B := hBcl.csInf_mem hBne hbd
    have hbB : sSup B ∈ B := hBcl.csSup_mem hBne hbu
    have hBIcc : B = Set.Icc (sInf B) (sSup B) := by
      refine Subset.antisymm (fun t ht => subset_Icc_csInf_csSup hbd hbu ht) (fun t ht => ?_)
      exact (isPreconnected_iff_ordConnected.mp hpc).out haB hbB ht
    have hBIcc' : Set.Icc (sInf B) (sSup B) = B := hBIcc.symm
    have hlt : sInf B < sSup B := by
      obtain ⟨z, hz, w, hw, hzw⟩ := exists_two_points_of_interior_nonempty hint
      have h1 : expChart θ₀ c z ∈ B := ⟨z, hz, rfl⟩
      have h2 : expChart θ₀ c w ∈ B := ⟨w, hw, rfl⟩
      have hne : expChart θ₀ c z ≠ expChart θ₀ c w := by
        intro heq
        refine hzw ?_
        rw [← expChart_exp θ₀ hθ₀ z, ← expChart_exp θ₀ hθ₀ w, heq]
      by_contra hcon
      push Not at hcon
      have hall : ∀ t ∈ B, t = sInf B := by
        intro t ht
        have ht' : t ∈ Set.Icc (sInf B) (sSup B) := by rw [← hBIcc]; exact ht
        exact le_antisymm (le_trans ht'.2 hcon) ht'.1
      exact hne (by rw [hall _ h1, hall _ h2])
    refine ⟨sInf B, sSup B, hlt, ?_, ?_⟩
    · have ha : θ₀ - Real.pi ≤ sInf B := (hBsub haB).1.le
      have hb : sSup B ≤ θ₀ + Real.pi := (hBsub hbB).2
      linarith
    · refine Subset.antisymm (fun z hz => ?_) ?_
      · refine ⟨expChart θ₀ c z, ?_, expChart_exp θ₀ hθ₀ z⟩
        rw [hBIcc']
        exact ⟨z, hz, rfl⟩
      · rintro y ⟨t, ht, rfl⟩
        obtain ⟨z, hz, hzt⟩ := (show t ∈ B from by rw [← hBIcc']; exact ht)
        rw [← hzt, expChart_exp θ₀ hθ₀ z]
        exact hz

end Work.Drive.N2
