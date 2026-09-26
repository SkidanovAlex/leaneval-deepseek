import Mathlib
import Submission.Work.Drive.Mono.Band.thinSlabBand_core
import Submission.Work.Drive.Mono.Band.bandData_core_exists
import Submission.Work.Drive.Mono.Band.heightGood_exists_in
import Submission.Work.Drive.Mono.Band.exists_slab_direction
import Submission.Work.Drive.Mono.Band.exists_adapted_basis
import Submission.Work.Drive.Mono.Band.badPoint_chart
import Submission.Work.Drive.Mono.Band.fundamentalDomain_reduction
import Submission.Work.Drive.Mono.Band.clauseTwo_exists
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.Final.sweep_mono
import Submission.Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic

/-!
# Tilt data for an arbitrarily thin slab

`Work.Drive.Mono.exists_smallSlab_tiltData` asks for the thin-slab tilt data
(`Work.Drive.Final.TiltedGenericity`, the two size conditions and the cutting condition) at a
half-width `h` which is *arbitrarily small*: `h < η` for a prescribed `η > 0`.

The proved `Work.Drive.Mono.Band.bandData_core_exists` produces the same data at a half-width
`h ∈ (‖v - shiftVσ σ 1‖ * (5/2 * s), boxWidth s σ v - |u|)`, and its proof uses the lower end of
that window only for the positivity of `h`: the whole analytic content (the a.e. finiteness of the
bad face values, the Morse property, the finiteness of the critical values) is obtained for any `h`
in the window, by `Work.Drive.Mono.Band.exists_window_avoiding` applied to a null set of chart
values and a null set of levels.  Hence the *upper* end of the window is free, and the data exist at
every half-width below `η`, **provided the slab direction `v` is close enough to `shiftVσ σ 1`**:
the size condition forces `‖v - shiftVσ σ 1‖ * (5/2 * s) < h < η`, so the slack
`η - ‖v - shiftVσ σ 1‖ * (5/2 * s)` has to be positive.

The one new ingredient is therefore that the *good* height directions (`HeightGood`, i.e. Morse with
injectively valued critical points) are dense *at the equator* `e^⊥`, not merely in a fixed belt
around it: `Work.Drive.Mono.Band.heightGood_exists_in` gives a good direction in *any* non-empty
open set, and the belt `{|⟪e,n⟫| < δ ‖n‖}` is non-empty for every `δ > 0` (it contains a unit vector
orthogonal to `e`).  That gives the good unit direction `n` with `|⟪e,n⟫|` as small as we wish, and
the slab direction `v` of `Work.Drive.Mono.Band.exists_slab_direction` built from it satisfies
`‖v - e‖ ≤ b/8` for a `b` of our choosing.

The rest of the proof is `Work.Drive.Mono.Band.bandData_core_exists` verbatim, with the window of
admissible half-widths changed from
`(‖v - e‖ * (5/2 * s), boxWidth s σ v - |u|)` to
`(‖v - e‖ * (5/2 * s), min η (boxWidth s σ v - |u|))`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology
open scoped RealInnerProductSpace
open Work.Drive.Mono.Band

noncomputable section

/-! ## 1. Good height directions arbitrarily close to the equator -/

/-- **A good height direction with an arbitrarily small component along `e`.**  For every `δ > 0`
there is a unit `n` with `HeightGood ψ n` and `|⟪e, n⟫| < δ`.  (The belt `{|⟪e,n⟫| < δ‖n‖}` is a
non-empty open set, and `Work.Drive.Mono.Band.heightGood_exists_in` finds a good direction in it.) -/
theorem exists_heightGood_unit_close (ψ : Submission.Diffeo) {e : R3} (he : ‖e‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : R3, ‖n‖ = 1 ∧ HeightGood ψ n ∧ |inner ℝ e n| < δ := by
  set U : Set R3 := {n : R3 | |inner ℝ e n| < δ * ‖n‖ ∧ n ≠ 0} with hU
  have hUopen : IsOpen U := by
    have h1 : IsOpen {n : R3 | |inner ℝ e n| < δ * ‖n‖} :=
      isOpen_lt (by fun_prop) (by fun_prop)
    have h3 : U = {n : R3 | |inner ℝ e n| < δ * ‖n‖} ∩ {n : R3 | n ≠ 0} := by
      rw [hU]
      exact Set.ext fun n => Iff.rfl
    rw [h3]
    exact h1.inter isOpen_ne
  have hUne : U.Nonempty := by
    obtain ⟨n₀, hn₀1, hn₀e⟩ := Work.Drive.EpsForm.exists_unit_orthogonal (e := e) (by
      intro h0; rw [h0, norm_zero] at he; exact one_ne_zero he.symm)
    refine ⟨n₀, ?_, ?_⟩
    · show |inner ℝ e n₀| < δ * ‖n₀‖
      rw [real_inner_comm, hn₀e, abs_zero, hn₀1, mul_one]
      exact hδ
    · intro h0; rw [h0, norm_zero] at hn₀1; exact one_ne_zero hn₀1.symm
  obtain ⟨n₁, hn₁U, hgood₁⟩ := heightGood_exists_in ψ hUopen hUne
  obtain ⟨hbelt₁, hn₁ne⟩ := hn₁U
  have hn₁p : 0 < ‖n₁‖ := norm_pos_iff.mpr hn₁ne
  refine ⟨(‖n₁‖)⁻¹ • n₁, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg n₁),
      inv_mul_cancel₀ (ne_of_gt hn₁p)]
  · exact (heightGood_smul_iff ψ (inv_ne_zero (ne_of_gt hn₁p)) n₁).mpr hgood₁
  · rw [real_inner_smul_right, abs_mul, abs_inv, abs_of_nonneg (norm_nonneg n₁)]
    calc ‖n₁‖⁻¹ * |inner ℝ e n₁| < ‖n₁‖⁻¹ * (δ * ‖n₁‖) :=
          mul_lt_mul_of_pos_left hbelt₁ (inv_pos.mpr hn₁p)
      _ = δ := by rw [mul_comm δ, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hn₁p), one_mul]

/-! ## 2. The slab direction, with a quantitative bound -/

/-- **The slab direction, quantitatively.**  The unit vector `v` in the direction of the orthogonal
projection of `e` onto `n^⊥` satisfies `‖v - e‖ ≤ b/8` whenever `16 * |⟪e,n⟫| < b`.  This is
`Work.Drive.Mono.Band.exists_slab_direction` with the numerical bound kept. -/
theorem exists_slab_direction_close {e n : R3} (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) (hb : 16 * |inner ℝ e n| < b) :
    ∃ v : R3, ‖v‖ = 1 ∧ inner ℝ v n = 0 ∧ ‖v - e‖ ≤ b / 8 := by
  set c : ℝ := inner ℝ e n with hcdef
  have hcabs : |c| < b / 16 := by rw [hcdef]; nlinarith
  have hc2 : c ^ 2 < (b / 16) ^ 2 := by
    have h := abs_lt.mp hcabs
    nlinarith [h.1, h.2]
  set w : R3 := e - c • n with hwdef
  have hwn : inner ℝ w n = 0 := by
    rw [hwdef, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hn, ← hcdef]
    ring
  have hwe : inner ℝ w e = 1 - c ^ 2 := by
    rw [hwdef, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he,
      ← real_inner_comm n e, ← hcdef]
    ring
  have hinner_sub : ∀ x : R3, inner ℝ x w = inner ℝ x e - c * inner ℝ x n := by
    intro x
    rw [hwdef, inner_sub_right, real_inner_smul_right]
  have hww : inner ℝ w w = 1 - c ^ 2 := by
    rw [hinner_sub w, hwe, hwn, mul_zero, sub_zero]
  have hwnorm : ‖w‖ ^ 2 = 1 - c ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]; exact hww
  have hwpos : 0 < ‖w‖ := by
    have h : 0 < ‖w‖ ^ 2 := by rw [hwnorm]; nlinarith [hc2, hb1, hb0]
    exact lt_of_le_of_ne (norm_nonneg w) (Ne.symm (sq_pos_iff.mp h))
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hwpos)
  have hvnorm : ‖(‖w‖)⁻¹ • w‖ = 1 := norm_smul_inv_norm hw0
  have hvinv : ‖(‖w‖)⁻¹ • w - e‖ ^ 2 = 2 * (1 - ‖w‖) := by
    have hve_inner : inner ℝ ((‖w‖)⁻¹ • w) e = ‖w‖ := by
      rw [real_inner_smul_left, hwe, ← hwnorm]
      field_simp
    rw [norm_sub_sq_real, hve_inner, he, hvnorm]
    ring
  have hle : ‖(‖w‖)⁻¹ • w - e‖ ^ 2 ≤ 2 * c ^ 2 := by
    rw [hvinv]
    have hwle1 : ‖w‖ ≤ 1 := by
      have h : ‖w‖ ^ 2 ≤ 1 := by rw [hwnorm]; nlinarith [sq_nonneg c]
      nlinarith [norm_nonneg w]
    have hb' : 1 - ‖w‖ ≤ c ^ 2 := by
      have h2 : ‖w‖ ^ 2 ≤ ‖w‖ := by nlinarith [hwle1, norm_nonneg w]
      nlinarith [hwnorm]
    linarith
  refine ⟨(‖w‖)⁻¹ • w, hvnorm, ?_, ?_⟩
  · rw [real_inner_smul_left, hwn, mul_zero]
  · have hfin : ‖(‖w‖)⁻¹ • w - e‖ ^ 2 ≤ (b / 8) ^ 2 := by
      nlinarith [hle, hc2, hb0, hb1]
    have h := sq_le_sq.mp hfin
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by linarith : (0 : ℝ) ≤ b / 8)] at h

/-! ## 3. The direction data -/

/-- **The slab direction and the wall normal for an arbitrarily thin slab.**  Given `η > 0` there
are orthonormal `v ⊥ n` with `n` a good height direction and `‖v - shiftVσ σ 1‖ * (5/2 * s) < η`, so
that the admissible window of half-widths has room below `η`. -/
theorem exists_dirData_close (ψ : Submission.Diffeo) (s : ℝ) (σ : Equiv.Perm (Fin 3)) (η : ℝ)
    (hs : 0 < s) (hη : 0 < η) :
    ∃ v n : R3, ‖v‖ = 1 ∧ ‖n‖ = 1 ∧ inner ℝ v n = 0 ∧ HeightGood ψ n ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 8 ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < η := by
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with he
  have he1 : ‖e‖ = 1 := Work.Drive.EpsForm.norm_shiftVσ_one σ
  set b : ℝ := min 1 (η / (10 * s)) with hbdef
  have hb0 : 0 < b := lt_min one_pos (div_pos hη (by linarith))
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbη : b ≤ η / (10 * s) := min_le_right _ _
  obtain ⟨n, hn1, hgood, hbelt⟩ := exists_heightGood_unit_close ψ he1 (δ := b / 16) (by linarith)
  have hbelt' : 16 * |inner ℝ e n| < b := by
    have h : |inner ℝ e n| < b / 16 := hbelt
    linarith
  obtain ⟨v, hv1, hvn, hve⟩ := exists_slab_direction_close he1 hn1 hb0 hb1 hbelt'
  refine ⟨v, n, hv1, hn1, hvn, hgood, ?_, ?_⟩
  · have : b / 8 ≤ 1 / 8 := by linarith
    linarith
  · have hs' : (0 : ℝ) < 5 / 2 * s := by linarith
    have h1 : ‖v - e‖ * (5 / 2 * s) ≤ (b / 8) * (5 / 2 * s) :=
      mul_le_mul_of_nonneg_right hve hs'.le
    have h2 : (b / 8) * (5 / 2 * s) ≤ η / 32 := by
      have h3 : b / 8 ≤ (η / (10 * s)) / 8 := by linarith
      have h4 := mul_le_mul_of_nonneg_right h3 hs'.le
      have h5 : (η / (10 * s) / 8) * (5 / 2 * s) = η / 32 := by
        field_simp
        ring
      linarith [h4, h5.le, h5.ge]
    linarith

/-! ## 4. The analytic core at a prescribed direction, with a free upper bound on the half-width -/

/-- **The analytic core of the thin-slab band data, with a free upper bound `η` on the half-width.**
At a prescribed orthonormal pair `v ⊥ n` (`n` a good height direction, `v` within `1/8` of
`shiftVσ σ 1`, and `‖v - shiftVσ σ 1‖ * (5/2 * s) < η`) there are a half-width `h < η` and a finite
exceptional set with the full tilt genericity, the size condition and the cutting condition.

This is `Work.Drive.Mono.Band.bandData_core_exists` with the window of half-widths
`(‖v - e‖ * (5/2 * s), min η (boxWidth s σ v - |u|))`; every step below is that proof verbatim. -/
theorem exists_tiltData_small_of_dir
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u r η : ℝ)
    (v n : R3)
    (hr : 0 < r) (hrs : r < s) (hu : |u| < Submission.eps * r) (hη : 0 < η)
    (hv1 : ‖v‖ = 1) (hn1 : ‖n‖ = 1) (hvn : inner ℝ v n = 0)
    (hgood : HeightGood ψ n)
    (hve : ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 8)
    (hvη : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < η) :
    ∃ (h : ℝ) (nn : R3) (exc : Finset ℝ), 0 < h ∧ h < η ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < h ∧
      h + |u| < boxWidth s σ v ∧
      ‖nn‖ = 1 ∧ inner ℝ v nn = 0 ∧
      Work.Drive.Final.TiltedGenericity ψ s c σ u v h ((innerSL ℝ) nn) exc := by
  classical
  have hs0 : 0 < s := lt_trans hr hrs
  -- ## 1. the adapted orthonormal basis of `v^⊥`: `n` has projective coordinate `1` in it
  obtain ⟨a₀, b₀, ha, hb, hab, hva, hvb, hnb⟩ := exists_adapted_basis hv1 hn1 hvn
  -- ## 2. an interval of good parameters `τ` around `1`
  have hgood1 : HeightGood ψ (dirOf 1 a₀ b₀) := by
    rw [dirOf_one ha hb hab hnb]; exact hgood
  obtain ⟨ρ, hρ0, hρgood⟩ := heightGood_open ψ hgood1
  have hdene : ∀ τ : ℝ, ‖τ • a₀ + b₀‖ ≠ 0 := by
    intro τ
    have h1 : inner ℝ b₀ (τ • a₀ + b₀) = 1 := inner_b₀_add_dirOf ha hb hab τ
    intro h0
    rw [norm_eq_zero] at h0
    rw [h0, inner_zero_right] at h1
    exact one_ne_zero h1.symm
  have hcont : Continuous fun τ : ℝ => dirOf τ a₀ b₀ := by
    unfold dirOf
    exact ((continuous_norm.comp (by fun_prop)).inv₀ hdene).smul (by fun_prop)
  have hmem_nhds : {τ : ℝ | HeightGood ψ (dirOf τ a₀ b₀)} ∈ nhds (1 : ℝ) := by
    have hev : ∀ᶠ τ in nhds (1 : ℝ), ‖dirOf τ a₀ b₀ - dirOf 1 a₀ b₀‖ < ρ :=
      hcont.continuousAt.eventually (Metric.ball_mem_nhds (dirOf 1 a₀ b₀) hρ0)
    filter_upwards [hev] with τ hτ
    exact hρgood _ hτ
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp hmem_nhds
  have hgoodτ : ∀ τ : ℝ, |τ - 1| < δ → HeightGood ψ (dirOf τ a₀ b₀) := by
    intro τ hτ
    exact hδ (Metric.mem_ball.mpr (by rwa [Real.dist_eq]))
  -- ## 3. the window of half-widths, with the free upper bound `η`
  have hwin0 : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < boxWidth s σ v - |u| :=
    window_nondegenerate s hs0 σ hve hrs hu
  have hwin : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) <
      min η (boxWidth s σ v - |u|) := lt_min hvη hwin0
  have hwpos : (0 : ℝ) ≤ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) := by positivity
  -- ## 4. the fundamental compact set and the null set of chart values
  set Kc : Set (ℝ × ℝ) := (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) ∩
    {p : ℝ × ℝ | Work.BoxShrink.Pinch.par ψ p ∈ closure (Submission.PBox s c σ)} with hKcdef
  have hKc : IsCompact Kc := by
    rw [hKcdef]
    exact (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_closure.preimage (Work.BoxShrink.Pinch.par_continuous ψ))
  have hKN : ∀ N : ℕ, IsCompact (Kc ∩ {p : ℝ × ℝ | ((N : ℝ) + 1)⁻¹ ≤ |betaV ψ v b₀ p|}) := by
    intro N
    refine hKc.inter_right ?_
    exact isClosed_le continuous_const (continuous_abs.comp (contDiff_betaV ψ v b₀).continuous)
  have hNull : ∀ N : ℕ, MeasureTheory.volume {y : ℝ × ℝ |
      (((bandChart ψ v a₀ b₀) ⁻¹' {y}) ∩
        (Kc ∩ {p : ℝ × ℝ | ((N : ℝ) + 1)⁻¹ ≤ |betaV ψ v b₀ p|})).Infinite} = 0 := by
    intro N
    refine chartSard_null ψ v a₀ b₀ (hKN N) ?_
    intro p hp
    have h1 : (0 : ℝ) < ((N : ℝ) + 1)⁻¹ := by positivity
    exact abs_pos.mp (lt_of_lt_of_le h1 hp.2)
  set Nbad : Set (ℝ × ℝ) := ⋃ N : ℕ, {y : ℝ × ℝ |
      (((bandChart ψ v a₀ b₀) ⁻¹' {y}) ∩
        (Kc ∩ {p : ℝ × ℝ | ((N : ℝ) + 1)⁻¹ ≤ |betaV ψ v b₀ p|})).Infinite} with hNbaddef
  have hNbad0 : MeasureTheory.volume Nbad = 0 := by
    rw [hNbaddef]
    exact MeasureTheory.measure_iUnion_null hNull
  -- ## 5. the critical values of the height in the direction `v`
  set CV : Set ℝ := {y : ℝ | ∃ p : ℝ × ℝ, heightV ψ v p = y ∧ fderiv ℝ (heightV ψ v) p = 0}
    with hCVdef
  have hCV0 : MeasureTheory.volume CV = 0 := by
    rw [hCVdef]
    refine Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic
      (contDiff_heightV ψ v) ?_ ?_
    · intro p
      show heightV ψ v (p.1 + 2 * Real.pi, p.2) = heightV ψ v p
      simp only [heightV]
      rw [par_add_two_pi_left ψ p]
    · intro p
      show heightV ψ v (p.1, p.2 + 2 * Real.pi) = heightV ψ v p
      simp only [heightV]
      rw [par_add_two_pi_right ψ p]
  -- ## 6. the avoidance
  obtain ⟨h, τ, hh1, hh2, hτ1, hτ2, hnoA, hnoB, hnoF1, hnoF2⟩ :=
    exists_window_avoiding hNbad0 hCV0 (a := inner ℝ v c + u) (tmin := 1 - δ) (tmax := 1 + δ)
      hwin (by linarith)
  -- ## 7. the final direction
  set nf : R3 := dirOf τ a₀ b₀ with hnfdef
  have hnf1 : ‖nf‖ = 1 := norm_dirOf ha hb hab τ
  have hvnf : inner ℝ v nf = 0 := inner_v_dirOf hva hvb τ
  have hgoodf : HeightGood ψ nf := hgoodτ τ (by rw [abs_lt]; exact ⟨by linarith, by linarith⟩)
  -- ## 8. regularity at the two face levels
  have hregA : ∀ p : ℝ × ℝ, p ∈ Kc → heightV ψ v p = inner ℝ v c + u + h →
      fderiv ℝ (heightV ψ v) p ≠ 0 := by
    intro p _ hval hd
    exact hnoA ⟨p, hval, hd⟩
  have hregB : ∀ p : ℝ × ℝ, p ∈ Kc → heightV ψ v p = inner ℝ v c + u - h →
      fderiv ℝ (heightV ψ v) p ≠ 0 := by
    intro p _ hval hd
    exact hnoB ⟨p, hval, hd⟩
  -- ## 9. the finiteness of the bad values
  have hfib1 := chartFibre_finite ψ v a₀ b₀ hv1 ha hb hab hva hvb hKc
    (y := (inner ℝ v c + u + h, τ)) hnoF1 hregA
  have hfib2 := chartFibre_finite ψ v a₀ b₀ hv1 ha hb hab hva hvb hKc
    (y := (inner ℝ v c + u - h, τ)) hnoF2 hregB
  have hbadfin : ({y : ℝ | ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ ∧
      |heightV ψ v p - (inner ℝ v c + u)| = h ∧
      inner ℝ (Work.Drive.Generic.crossE v nf)
        (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 ∧
      heightIn ψ nf p = y}).Finite := by
    refine Set.Finite.subset ((hfib1.image (heightIn ψ nf)).union (hfib2.image (heightIn ψ nf))) ?_
    rintro y ⟨p, hpbox, hface, hcross, rfl⟩
    -- the fundamental representative of `p`
    obtain ⟨p₀, hp₀box, hp₀par, hp₀fd⟩ := fundamentalDomain_reduction ψ p
    have hp₀K : p₀ ∈ Kc := by
      rw [hKcdef]
      refine ⟨hp₀box, ?_⟩
      show Work.BoxShrink.Pinch.par ψ p₀ ∈ closure (Submission.PBox s c σ)
      rw [hp₀par]
      exact subset_closure hpbox
    have hnorm : Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p₀
        = Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p := by
      simp only [Work.Drive.Generic.normal, Work.Drive.Generic.d1, Work.Drive.Generic.d2]
      rw [hp₀fd]
    have hα : alphaV ψ v a₀ p₀ = alphaV ψ v a₀ p := by
      simp only [alphaV, projVv, projV, hnorm, hp₀fd]
    have hβ : betaV ψ v b₀ p₀ = betaV ψ v b₀ p := by
      simp only [betaV, projVv, projV, hnorm, hp₀fd]
    have hf0 : heightV ψ v p₀ = heightV ψ v p := by simp only [heightV, hp₀par]
    -- the projective coordinate is `τ`
    have hproj : projV (Work.BoxShrink.Pinch.par ψ) v p ≠ 0 := by
      intro h0
      have hd : fderiv ℝ (heightV ψ v) p = 0 := by
        have h := (fderiv_par_height_eq_zero_iff_projV ψ (v := v) hv1 p).mpr h0
        change fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p = 0
        exact h
      have habs : heightV ψ v p = inner ℝ v c + u + h ∨
          heightV ψ v p = inner ℝ v c + u - h := by
        have hlt : 0 < h := lt_of_le_of_lt hwpos hh1
        have := hface
        rw [abs_eq hlt.le] at this
        rcases this with h' | h'
        · left; linarith [h']
        · right; linarith [h']
      rcases habs with h' | h'
      · exact hnoA ⟨p, h'.symm ▸ rfl, hd⟩
      · exact hnoB ⟨p, h'.symm ▸ rfl, hd⟩
    have hbad := badPoint_chart ψ hv1 ha hb hab hva hvb (τ := τ) (p := p)
      (by simpa only [← hnfdef] using hcross) hproj
    have hratio : alphaV ψ v a₀ p / betaV ψ v b₀ p = τ := hbad.1
    have hb0' : betaV ψ v b₀ p ≠ 0 := hbad.2
    have hstep : ∀ z : ℝ, heightV ψ v p = z →
        bandChart ψ v a₀ b₀ p₀ = (z, τ) := by
      intro z hz
      show (heightV ψ v p₀, alphaV ψ v a₀ p₀ / betaV ψ v b₀ p₀) = (z, τ)
      rw [Prod.ext_iff]
      exact ⟨by rw [hf0, hz], by rw [hα, hβ, hratio]⟩
    have habs : heightV ψ v p = inner ℝ v c + u + h ∨
        heightV ψ v p = inner ℝ v c + u - h := by
      have hlt : 0 < h := lt_of_le_of_lt hwpos hh1
      have := hface
      rw [abs_eq hlt.le] at this
      rcases this with h' | h'
      · left; linarith [h']
      · right; linarith [h']
    rcases habs with h' | h'
    · refine Set.mem_union_left _ ?_
      have hmem : p₀ ∈ ((bandChart ψ v a₀ b₀) ⁻¹' {(inner ℝ v c + u + h, τ)}) ∩ Kc
          ∩ chartDomain ψ v b₀ := ⟨⟨hstep _ h', hp₀K⟩, by
            show betaV ψ v b₀ p₀ ≠ 0
            rw [hβ]; exact hb0'⟩
      rw [show heightIn ψ nf p = heightIn ψ nf p₀ from by
        show inner ℝ nf (Work.BoxShrink.Pinch.par ψ p)
          = inner ℝ nf (Work.BoxShrink.Pinch.par ψ p₀)
        rw [hp₀par]]
      exact Set.mem_image_of_mem _ hmem
    · refine Set.mem_union_right _ ?_
      have hmem : p₀ ∈ ((bandChart ψ v a₀ b₀) ⁻¹' {(inner ℝ v c + u - h, τ)}) ∩ Kc
          ∩ chartDomain ψ v b₀ := ⟨⟨hstep _ h', hp₀K⟩, by
            show betaV ψ v b₀ p₀ ≠ 0
            rw [hβ]; exact hb0'⟩
      rw [show heightIn ψ nf p = heightIn ψ nf p₀ from by
        show inner ℝ nf (Work.BoxShrink.Pinch.par ψ p)
          = inner ℝ nf (Work.BoxShrink.Pinch.par ψ p₀)
        rw [hp₀par]]
      exact Set.mem_image_of_mem _ hmem
  -- ## 10. the exceptional set
  have hcritfin : ({p : ℝ × ℝ | fderiv ℝ (heightIn ψ nf) p = 0} ∩
      (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi))).Finite :=
    Work.Drive.EpsForm.finite_critSet_box (heightIn_contDiff_two ψ nf) hgoodf.1
  -- ## 11. the four data conditions
  have hMorse : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p = 0 →
      Function.Injective
        (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf))) p) := by
    intro p _ hcrit
    have hcrit' : fderiv ℝ (heightIn ψ nf) p = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit
    have h := hgoodf.1 p hcrit'
    rwa [Work.Drive.EpsForm.sweepHeight_innerSL]
  have hdistinct : ∀ p p' : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p' ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p = 0 →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p' = 0 →
      (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p
        = (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p' →
      Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p' := by
    intro p p' _ _ hcrit hcrit' hval
    have h1 : fderiv ℝ (heightIn ψ nf) p = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit
    have h2 : fderiv ℝ (heightIn ψ nf) p' = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit'
    have h3 : heightIn ψ nf p = heightIn ψ nf p' := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hval
    exact hgoodf.2 p p' h1 h2 h3
  have hcritMem : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p = 0 →
      (innerSL ℝ) nf (Work.BoxShrink.Pinch.par ψ p) ∈
        hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset := by
    intro p hpbox hcrit
    have hcrit' : fderiv ℝ (heightIn ψ nf) p = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit
    obtain ⟨p₀, hp₀box, hp₀crit, hp₀par⟩ :=
      Work.Drive.EpsForm.exists_fundamental_of_crit ψ (innerSL ℝ nf) hcrit
    have hp₀crit' : fderiv ℝ (heightIn ψ nf) p₀ = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hp₀crit
    have hmem : p₀ ∈ hcritfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨hp₀crit', hp₀box⟩
    have hval : heightIn ψ nf p₀ ∈ hcritfin.toFinset.image (heightIn ψ nf) :=
      Finset.mem_image.mpr ⟨p₀, hmem, rfl⟩
    exact Finset.mem_union_left _ (by simpa only [innerSL_apply_apply, ← hp₀par] using hval)
  have hface : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h →
      inner ℝ (Work.Drive.Generic.crossE v nf)
        (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 →
      (innerSL ℝ) nf (Work.BoxShrink.Pinch.par ψ p) ∈
        hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset := by
    intro p hpbox hfacept hcross
    refine Finset.mem_union_right _ ?_
    rw [hbadfin.mem_toFinset]
    exact ⟨p, hpbox, hfacept, hcross, rfl⟩
  refine ⟨h, nf, hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset,
    lt_of_le_of_lt hwpos hh1, ?_, hh1, ?_, hnf1, hvnf, ?_⟩
  · exact lt_of_lt_of_le hh2 (min_le_left _ _)
  · have h3 : h < boxWidth s σ v - |u| := lt_of_lt_of_le hh2 (min_le_right _ _)
    linarith
  · exact Work.Drive.Mono.Band.tiltedGenericity_of_data ψ s c σ u v nf h
      (hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset)
      hv1 hnf1 hvnf hMorse hdistinct hcritMem hface

/-! ## 5. The requested lemma -/

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem exists_smallSlab_tiltData
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u r η : ℝ)
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hu : |u| < Submission.eps * r) (hη : 0 < η) :
    ∃ (v n : R3) (h : ℝ) (exc : Finset ℝ),
      ‖v‖ = 1 ∧ ‖n‖ = 1 ∧ inner ℝ v n = 0 ∧ 0 < h ∧ h < η ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < h ∧
      h + |u| < Work.Drive.Mono.boxWidth s σ v ∧
      Work.Drive.Final.TiltedGenericity ψ s c σ u v h ((innerSL ℝ) n) exc := by
  have hs0 : 0 < s := lt_trans hr hrs
  obtain ⟨v, n, hv1, hn1, hvn, hgood, hve, hvη⟩ := exists_dirData_close ψ s σ η hs0 hη
  obtain ⟨h, nn, exc, hh0, hhη, hsize, hcut, hnn1, hvnn, hgen⟩ :=
    exists_tiltData_small_of_dir ψ s c σ u r η v n hr hrs hu hη hv1 hn1 hvn hgood hve hvη
  exact ⟨v, nn, h, exc, hv1, hnn1, hvnn, hh0, hhη, hsize, hcut, hgen⟩

end

end Work.Drive.Mono
