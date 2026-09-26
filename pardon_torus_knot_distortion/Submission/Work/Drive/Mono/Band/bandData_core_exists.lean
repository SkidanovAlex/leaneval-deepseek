import Mathlib
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.Mono.Band.BadFaceDefs
import Submission.Work.Drive.Mono.Band.BandChartDefs
import Submission.Work.Drive.Mono.Band.HeightGoodDefs
import Submission.Work.Drive.Mono.Band.noTangency_data
import Submission.Work.Drive.Mono.Band.ae_finite_preimage
import Submission.Work.Drive.Mono.Band.ae_finite_preimage_open
import Submission.Work.Drive.Mono.Band.badPoint_projNormal
import Submission.Work.Drive.Mono.Band.exists_param_avoiding
import Submission.Work.Drive.Mono.Band.fundamentalDomain_reduction
import Submission.Work.Drive.Mono.Band.clauseTwo_exists
import Submission.Work.Drive.Mono.ThinWidth.exists_window_regular
import Submission.Work.Drive.EpsForm.critTrackExists
import Submission.Work.Drive.EpsForm.goodHeight_exists
import Submission.Work.Drive.Generic.ae_height_morse
import Submission.Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic
import Submission.Work.Drive.Mono.Band.heightGood_exists_in
import Submission.Work.Drive.Mono.Band.heightGood_open
import Submission.Work.Drive.Mono.Band.exists_slab_direction
import Submission.Work.Drive.Mono.Band.exists_adapted_basis
import Submission.Work.Drive.Mono.Band.badPoint_chart
import Submission.Work.Drive.Mono.Band.exists_betaBound_of_compact

/-!
# The analytic core of the thin-slab band data

(see the docstring of the statement at the end of this file)
-/

namespace Work.Drive.Mono.Band

open LeanEval.KnotTheory.PardonDistortion
open scoped RealInnerProductSpace
open MeasureTheory
open Filter
open scoped Topology

noncomputable section

/-! ## 0. Elementary cancellations of scaled continuous linear maps -/

private theorem smul_clm_eq_iff {c : ℝ} (hc : c ≠ 0) {x y : (ℝ × ℝ) →L[ℝ] ℝ} :
    c • x = c • y ↔ x = y := by
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun w => ?_
    have h2 : c * (x w) = c * (y w) := by
      have h3 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L w) h
      simpa only [smul_apply, smul_eq_mul] using h3
    exact mul_left_cancel₀ hc h2
  · intro h; rw [h]

private theorem smul_clm_eq_zero_iff {c : ℝ} (hc : c ≠ 0) {x : (ℝ × ℝ) →L[ℝ] ℝ} :
    c • x = 0 ↔ x = 0 := by
  have h : c • x = c • (0 : (ℝ × ℝ) →L[ℝ] ℝ) ↔ x = 0 := smul_clm_eq_iff hc
  rwa [smul_zero] at h

private theorem smul_clm_injective_iff {c : ℝ} (hc : c ≠ 0)
    {H : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)} :
    Function.Injective (c • H) ↔ Function.Injective H := by
  have key : ∀ a b : ℝ × ℝ, H a = H b → (c • H) a = (c • H) b := by
    intro a b hab
    show c • (H a) = c • (H b)
    exact (smul_clm_eq_iff hc).mpr hab
  have key2 : ∀ a b : ℝ × ℝ, (c • H) a = (c • H) b → H a = H b := by
    intro a b hab
    have h2 : c • (H a) = c • (H b) := hab
    exact (smul_clm_eq_iff hc).mp h2
  constructor
  · intro h a b hab
    exact h (key a b hab)
  · intro h a b hab
    exact h (key2 a b hab)

/-- The height of the scaled direction is the scaled height. -/
theorem heightIn_smul (ψ : Submission.Diffeo) (c : ℝ) (n : R3) :
    heightIn ψ (c • n) = fun q => c • heightIn ψ n q := by
  funext q
  simp only [heightIn, real_inner_smul_left, smul_eq_mul]

/-- The derivative of the scaled height is the scaled derivative. -/
theorem fderiv_heightIn_smul (ψ : Submission.Diffeo) (c : ℝ) (n : R3) (p : ℝ × ℝ) :
    fderiv ℝ (heightIn ψ (c • n)) p = c • fderiv ℝ (heightIn ψ n) p := by
  have hd : DifferentiableAt ℝ (heightIn ψ n) p :=
    ((heightIn_contDiff ψ n).differentiable (by simp)).differentiableAt
  rw [heightIn_smul]
  exact fderiv_const_smul hd c

/-- The second derivative of the scaled height is the scaled second derivative. -/
theorem fderiv_fderiv_heightIn_smul (ψ : Submission.Diffeo) (c : ℝ) (n : R3) (p : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (heightIn ψ (c • n))) p
      = c • fderiv ℝ (fderiv ℝ (heightIn ψ n)) p := by
  have hcd : ContDiff ℝ 1 (fun p => fderiv ℝ (heightIn ψ n) p) :=
    (heightIn_contDiff_two ψ n).fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fun p => fderiv ℝ (heightIn ψ n) p) p :=
    (hcd.differentiable (by norm_num)).differentiableAt
  rw [show fderiv ℝ (heightIn ψ (c • n)) = fun q => c • fderiv ℝ (heightIn ψ n) q from
    funext (fderiv_heightIn_smul ψ c n)]
  exact fderiv_const_smul hd c

/-- **The good property only depends on the direction.** -/
theorem heightGood_smul_iff (ψ : Submission.Diffeo) {c : ℝ} (hc : c ≠ 0) (n : R3) :
    HeightGood ψ (c • n) ↔ HeightGood ψ n := by
  have hcrit : ∀ p, fderiv ℝ (heightIn ψ (c • n)) p = 0 ↔ fderiv ℝ (heightIn ψ n) p = 0 :=
    fun p => by rw [fderiv_heightIn_smul ψ c n p]; exact smul_clm_eq_zero_iff hc
  have hval : ∀ q, heightIn ψ (c • n) q = c * heightIn ψ n q := fun q => by
    rw [heightIn_smul]; rfl
  constructor
  · intro h
    refine ⟨fun p hp => ?_, fun p p' hp hp' hvv => ?_⟩
    · have h1 := h.1 p ((hcrit p).mpr hp)
      rw [fderiv_fderiv_heightIn_smul ψ c n p] at h1
      exact (smul_clm_injective_iff hc).mp h1
    · refine h.2 p p' ((hcrit p).mpr hp) ((hcrit p').mpr hp') ?_
      rw [hval p, hval p']
      exact congrArg (fun x => c * x) hvv
  · intro h
    refine ⟨fun p hp => ?_, fun p p' hp hp' hvv => ?_⟩
    · have h1 := h.1 p ((hcrit p).mp hp)
      rw [fderiv_fderiv_heightIn_smul ψ c n p]
      exact (smul_clm_injective_iff hc).mpr h1
    · refine h.2 p p' ((hcrit p).mp hp) ((hcrit p').mp hp') ?_
      exact mul_left_cancel₀ hc (by rw [← hval p, ← hval p']; exact hvv)



/-! ## 1. A good unit direction with a small component along `e` -/

/-- There is a unit direction `n` whose height is good and which is nearly orthogonal to the unit
vector `e`: `16 * |⟪e, n⟫| < 1`.  The set of such directions is the open "belt" around `e^⊥`. -/
theorem exists_heightGood_unit (ψ : Submission.Diffeo) {e : R3} (he : ‖e‖ = 1) :
    ∃ n : R3, ‖n‖ = 1 ∧ HeightGood ψ n ∧ 16 * |inner ℝ e n| < 1 := by
  set U : Set R3 := {n : R3 | 16 * |inner ℝ e n| < ‖n‖ ∧ n ≠ 0} with hU
  have hUopen : IsOpen U := by
    have h1 : IsOpen {n : R3 | 16 * |inner ℝ e n| < ‖n‖} :=
      isOpen_lt (by fun_prop) (by fun_prop)
    have h3 : U = {n : R3 | 16 * |inner ℝ e n| < ‖n‖} ∩ {n : R3 | n ≠ 0} := by
      rw [hU]
      exact Set.ext fun n => Iff.rfl
    rw [h3]
    exact h1.inter isOpen_ne
  have hUne : U.Nonempty := by
    obtain ⟨n₀, hn₀1, hn₀e⟩ := Work.Drive.EpsForm.exists_unit_orthogonal (e := e) (by
      intro h0; rw [h0, norm_zero] at he; exact one_ne_zero he.symm)
    refine ⟨n₀, ?_, ?_⟩
    · show 16 * |inner ℝ e n₀| < ‖n₀‖
      rw [real_inner_comm n₀ e, hn₀e, abs_zero, mul_zero, hn₀1]
      norm_num
    · intro h0; rw [h0, norm_zero] at hn₀1; exact one_ne_zero hn₀1.symm
  obtain ⟨n₁, hn₁U, hgood₁⟩ := heightGood_exists_in ψ hUopen hUne
  obtain ⟨hbelt₁, hn₁ne⟩ := hn₁U
  have hn₁p : 0 < ‖n₁‖ := norm_pos_iff.mpr hn₁ne
  refine ⟨(‖n₁‖)⁻¹ • n₁, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg n₁),
      inv_mul_cancel₀ (ne_of_gt hn₁p)]
  · exact (heightGood_smul_iff ψ (inv_ne_zero (ne_of_gt hn₁p)) n₁).mpr hgood₁
  · show 16 * |inner ℝ e ((‖n₁‖)⁻¹ • n₁)| < 1
    rw [real_inner_smul_right, abs_mul, abs_inv, abs_of_nonneg (norm_nonneg n₁)]
    have h16 : 16 * (‖n₁‖⁻¹ * |inner ℝ e n₁|) = ‖n₁‖⁻¹ * (16 * |inner ℝ e n₁|) := by ring
    rw [h16]
    calc ‖n₁‖⁻¹ * (16 * |inner ℝ e n₁|) < ‖n₁‖⁻¹ * ‖n₁‖ :=
          mul_lt_mul_of_pos_left hbelt₁ (inv_pos.mpr hn₁p)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hn₁p)

/-! ## 4. The window of half-widths is non-degenerate -/

/-- For `‖v - e‖ ≤ 1/8` and `|u| < ε * r < ε * s`, the interval
`(‖v - e‖ * (5/2 * s), boxWidth s σ v - |u|)` of admissible half-widths is non-empty. -/
theorem window_nondegenerate (s : ℝ) (hs : 0 < s) (σ : Equiv.Perm (Fin 3)) {v : R3}
    (hve : ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 8) {u r : ℝ} (hrs : r < s)
    (hu : |u| < Submission.eps * r) :
    ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < boxWidth s σ v - |u| := by
  have hbox : 7 / 8 * s ≤ boxWidth s σ v := boxWidth_ge s hs σ hve
  have heps : Submission.eps = 2 / 13 := rfl
  have heps0 : 0 < Submission.eps := by rw [heps]; norm_num
  have h1 : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) ≤ 1 / 8 * (5 / 2 * s) :=
    mul_le_mul_of_nonneg_right hve (by linarith)
  have h2 : |u| < 2 / 13 * s := by
    have h3 : Submission.eps * r < Submission.eps * s :=
      mul_lt_mul_of_pos_left hrs heps0
    have h4 : Submission.eps * s = 2 / 13 * s := by rw [heps]
    linarith [hu, h3, h4.le, h4.ge]
  linarith

/-! ## 5. Sard for the projective chart (on compact pieces) -/

theorem chartSard_null (ψ : Submission.Diffeo) (v a₀ b₀ : R3)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKβ : ∀ p ∈ K, betaV ψ v b₀ p ≠ 0) :
    MeasureTheory.volume {y : ℝ × ℝ |
      (((bandChart ψ v a₀ b₀) ⁻¹' {y}) ∩ K).Infinite} = 0 :=
  ae_finite_preimage_open (chartDomain_isOpen ψ v b₀) (contDiffOn_bandChart ψ v a₀ b₀) hK
    (fun p hp => hKβ p hp)

/-! ## 6. Avoiding a null set of chart values and a null set of levels simultaneously -/

/-- The two-moving-points step of the band proof: given a null set `S` of chart values, a null set
`N` of levels, and two non-degenerate intervals, there are `h` and `τ` in them with the four points
`(a + h, τ)`, `(a - h, τ)`, `a + h`, `a - h` all outside the respective bad sets. -/
theorem exists_window_avoiding {S : Set (ℝ × ℝ)} (hS : MeasureTheory.volume S = 0)
    {N : Set ℝ} (hN : MeasureTheory.volume N = 0) {a tmin tmax hmin hmax : ℝ}
    (hlt : hmin < hmax) (hlt' : tmin < tmax) :
    ∃ h τ : ℝ, hmin < h ∧ h < hmax ∧ tmin < τ ∧ τ < tmax ∧
      a + h ∉ N ∧ a - h ∉ N ∧ (a + h, τ) ∉ S ∧ (a - h, τ) ∉ S := by
  have h1 : MeasureTheory.volume ((fun p : ℝ × ℝ => (a + p.1, p.2)) ⁻¹' S) = 0 := by
    have h : (fun p : ℝ × ℝ => (a + p.1, p.2)) = (fun p => (a, 0) + p) := by
      funext p; simp [Prod.add_def]
    rw [h]
    exact (MeasureTheory.measure_preimage_add (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      (a, 0) S).trans hS
  have h2 : MeasureTheory.volume ((fun p : ℝ × ℝ => (a - p.1, p.2)) ⁻¹' S) = 0 := by
    have hlog : Measure.map (fun x : ℝ => x) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        = MeasureTheory.volume := Measure.map_id
    have hmap : Measure.map (fun p : ℝ × ℝ => (-p.1, p.2))
        (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) = MeasureTheory.volume := by
      have h := MeasureTheory.Measure.map_prod_map
        (μa := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (μc := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (f := fun x : ℝ => -x) (g := fun x : ℝ => x) measurable_neg measurable_id
      rw [MeasureTheory.Measure.map_neg_eq_self, hlog, ← MeasureTheory.Measure.volume_eq_prod] at h
      have hfun : (fun p : ℝ × ℝ => (-p.1, p.2)) = Prod.map Neg.neg id := by
        funext p; simp [Prod.map]
      rw [hfun]
      exact h.symm
    have hcomp : (fun p : ℝ × ℝ => (a - p.1, p.2))
        = (fun p : ℝ × ℝ => (a + p.1, p.2)) ∘ (fun p : ℝ × ℝ => (-p.1, p.2)) := by
      funext p; simp [sub_eq_add_neg]
    rw [hcomp, Set.preimage_comp]
    have hle := MeasureTheory.Measure.le_map_apply
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)))
      (f := fun p : ℝ × ℝ => (-p.1, p.2)) (by fun_prop)
      ((fun p : ℝ × ℝ => (a + p.1, p.2)) ⁻¹' S)
    rw [hmap, h1] at hle
    exact le_antisymm hle bot_le
  have h3 : MeasureTheory.volume ({u : ℝ | a + u ∈ N} ×ˢ (Set.univ : Set ℝ)) = 0 := by
    have h3set : MeasureTheory.volume ({u : ℝ | a + u ∈ N}) = 0 :=
      (MeasureTheory.measure_preimage_add (MeasureTheory.volume : MeasureTheory.Measure ℝ) a N).trans hN
    rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod, h3set, zero_mul]
  have h4 : MeasureTheory.volume ({u : ℝ | a - u ∈ N} ×ˢ (Set.univ : Set ℝ)) = 0 := by
    have h4set : MeasureTheory.volume ({u : ℝ | a - u ∈ N}) = 0 := by
      have hmap : Measure.map (fun u : ℝ => a - u) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
          = MeasureTheory.volume := MeasureTheory.Measure.map_sub_left_eq_self MeasureTheory.volume a
      have hle := MeasureTheory.Measure.le_map_apply
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (f := fun u : ℝ => a - u) (measurable_const.sub measurable_id).aemeasurable N
      rw [hmap, hN] at hle
      exact le_antisymm hle bot_le
    rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod, h4set, zero_mul]
  set B : Set (ℝ × ℝ) :=
      ((fun p : ℝ × ℝ => (a + p.1, p.2)) ⁻¹' S ∪ (fun p : ℝ × ℝ => (a - p.1, p.2)) ⁻¹' S)
      ∪ {u : ℝ | a + u ∈ N} ×ˢ (Set.univ : Set ℝ)
      ∪ {u : ℝ | a - u ∈ N} ×ˢ (Set.univ : Set ℝ) with hB
  have hBnull : MeasureTheory.volume B = 0 := by
    rw [hB]
    exact MeasureTheory.measure_union_null
      (MeasureTheory.measure_union_null (MeasureTheory.measure_union_null h1 h2) h3) h4
  have hstrip : MeasureTheory.volume ((Set.Ioo hmin hmax) ×ˢ (Set.Ioo tmin tmax)) ≠ 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (by linarith))
      (ENNReal.ofReal_ne_zero_iff.mpr (by linarith))
  have hnotsub : ¬ ((Set.Ioo hmin hmax) ×ˢ (Set.Ioo tmin tmax) ⊆ B) := by
    intro hsub
    have hle : MeasureTheory.volume ((Set.Ioo hmin hmax) ×ˢ (Set.Ioo tmin tmax))
        ≤ MeasureTheory.volume B := MeasureTheory.measure_mono hsub
    rw [hBnull] at hle
    exact hstrip (le_antisymm hle bot_le)
  obtain ⟨p, hpmem, hpnot⟩ := Set.not_subset.mp hnotsub
  obtain ⟨h, τ⟩ := p
  rw [Set.mem_prod] at hpmem
  obtain ⟨hhmem, hτmem⟩ := hpmem
  rw [Set.mem_Ioo] at hhmem hτmem
  rw [hB, Set.mem_union, Set.mem_union, Set.mem_union, not_or, not_or, not_or] at hpnot
  obtain ⟨⟨⟨hp1, hp2⟩, hp3⟩, hp4⟩ := hpnot
  exact ⟨h, τ, hhmem.1, hhmem.2, hτmem.1, hτmem.2, fun hc => hp3 ⟨hc, trivial⟩,
    fun hc => hp4 ⟨hc, trivial⟩, fun hc => hp1 hc, fun hc => hp2 hc⟩

/-! ## 8. The chart fibre is finite -/

/-- **The chart fibre over a value without infinite fibres is finite.**  If `y` is not one of the
values with an infinite fibre on any of the compact pieces `K ∩ {|betaV| ≥ 1/N}`, and the height is
regular on `K` at the level `y.1`, then the fibre of the chart over `y` inside `K ∩ {betaV ≠ 0}` is
finite.

Route: the level set `S = {heightV = y.1, alphaV = y.2 * betaV} ∩ K` is compact; it misses
`{betaV = 0}` (at such a point `projV = alphaV • a₀ + betaV • b₀ = 0` by `projV_coord_eq_zero`,
hence `fderiv (heightV) = 0`, contradicting the regularity hypothesis), so
`Work.Drive.Mono.Band.exists_betaBound_of_compact` bounds `|betaV|` below on `S` by `1/N` with
`N ≥ 1`, and the fibre is inside the (finite by hypothesis) set
`bandChart ⁻¹' {y} ∩ (K ∩ {|betaV| ≥ 1/N})`. -/
theorem chartFibre_finite (ψ : Submission.Diffeo) (v a₀ b₀ : R3)
    (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {y : ℝ × ℝ}
    (hy : y ∉ ⋃ N : ℕ, {y' : ℝ × ℝ | (((bandChart ψ v a₀ b₀) ⁻¹' {y'}) ∩
      (K ∩ {p : ℝ × ℝ | ((N : ℝ) + 1)⁻¹ ≤ |betaV ψ v b₀ p|})).Infinite})
    (hreg : ∀ p : ℝ × ℝ, p ∈ K → heightV ψ v p = y.1 → fderiv ℝ (heightV ψ v) p ≠ 0) :
    (((bandChart ψ v a₀ b₀) ⁻¹' {y}) ∩ K ∩ chartDomain ψ v b₀).Finite := by
  have hCdom : ({p : ℝ × ℝ | heightV ψ v p = y.1 ∧
      alphaV ψ v a₀ p = y.2 * betaV ψ v b₀ p} ∩ K) ⊆ chartDomain ψ v b₀ := by
    rintro p ⟨⟨h1, h2⟩, hpK⟩
    intro hb0
    have ha0 : alphaV ψ v a₀ p = 0 := by rw [h2, hb0, mul_zero]
    have hXv : inner ℝ v (projV (Work.BoxShrink.Pinch.par ψ) v p) = 0 := by
      rw [← real_inner_comm v (projV (Work.BoxShrink.Pinch.par ψ) v p)]
      exact inner_projV_v hv p
    have hproj : projVv ψ v p = 0 :=
      projV_coord_eq_zero hv ha hb hab hva hvb hXv ha0 hb0
    have hfd : fderiv ℝ (heightV ψ v) p = 0 := by
      have h := (fderiv_par_height_eq_zero_iff_projV ψ (v := v) hv p).mpr hproj
      unfold heightV
      exact h
    exact hreg p hpK h1 hfd
  obtain ⟨N, hN1, hNsub⟩ := exists_betaBound_of_compact ψ v a₀ b₀ hK hCdom
  have hNcast : (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) := by
    have h1 : (1 : ℕ) ≤ N := hN1
    have h2 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub h1]; norm_num
    rw [h2]; ring
  have hfin : (((bandChart ψ v a₀ b₀) ⁻¹' {y}) ∩
      (K ∩ {p : ℝ × ℝ | (((N - 1 : ℕ) : ℝ) + 1)⁻¹ ≤ |betaV ψ v b₀ p|})).Finite := by
    by_contra h
    exact hy (Set.mem_iUnion.mpr ⟨N - 1, h⟩)
  refine Set.Finite.subset hfin ?_
  rintro p ⟨⟨hpy, hpK⟩, hpdom⟩
  have h1 : heightV ψ v p = y.1 := by
    have := congrArg Prod.fst hpy
    simpa [bandChart] using this
  have h2 : alphaV ψ v a₀ p / betaV ψ v b₀ p = y.2 := by
    have := congrArg Prod.snd hpy
    simpa [bandChart] using this
  have h3 : alphaV ψ v a₀ p = y.2 * betaV ψ v b₀ p := by
    rw [div_eq_iff hpdom] at h2
    exact h2
  have hNp : (((N - 1 : ℕ) : ℝ) + 1)⁻¹ ≤ |betaV ψ v b₀ p| := by
    rw [hNcast]
    exact hNsub ⟨⟨h1, h3⟩, hpK⟩
  exact ⟨hpy, hpK, hNp⟩

/-! ## 9. The band data -/

theorem bandData_core_exists
    (ψ : Submission.Diffeo) (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u r : ℝ)
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hu : |u| < Submission.eps * r) :
    ∃ (v n : LeanEval.KnotTheory.PardonDistortion.R3) (h : ℝ) (exc : Finset ℝ),
      ‖v‖ = 1 ∧ ‖n‖ = 1 ∧ inner ℝ v n = 0 ∧ 0 < h ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < h ∧
      h + |u| < boxWidth s σ v ∧
      (∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p = 0 →
        Function.Injective
          (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n))) p)) ∧
      (∀ p p' : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
        Work.BoxShrink.Pinch.par ψ p' ∈ Submission.PBox s c σ →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p = 0 →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p' = 0 →
        (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p
          = (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p' →
        Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p') ∧
      (∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p = 0 →
        (innerSL ℝ) n (Work.BoxShrink.Pinch.par ψ p) ∈ exc) ∧
      (∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
        |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h →
        inner ℝ (Work.Drive.Generic.crossE v n)
          (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 →
        (innerSL ℝ) n (Work.BoxShrink.Pinch.par ψ p) ∈ exc) := by
  classical
  have hs0 : 0 < s := lt_trans hr hrs
  have he1 : ‖Work.BoxShrink.shiftVσ σ 1‖ = 1 := Work.Drive.EpsForm.norm_shiftVσ_one σ
  -- ## 1. a good unit direction nearly orthogonal to the shift direction
  obtain ⟨n, hn1, hgood, hbelt⟩ := exists_heightGood_unit ψ he1
  -- ## 2. the slab direction
  obtain ⟨v, hv1, hvn, hve⟩ := exists_slab_direction he1 hn1 hbelt
  -- ## 3. the adapted orthonormal basis of `v^⊥`
  obtain ⟨a₀, b₀, ha, hb, hab, hva, hvb, hnb⟩ := exists_adapted_basis hv1 hn1 hvn
  -- ## 4. an interval of good parameters `τ` around `1`
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
  -- ## 5. the window of half-widths
  have hwin : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < boxWidth s σ v - |u| :=
    window_nondegenerate s hs0 σ hve hrs hu
  have hwpos : (0 : ℝ) ≤ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) := by positivity
  -- ## 6. the fundamental compact set and the null set of chart values
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
  -- ## 7. the critical values of the height in the direction `v`
  set CV : Set ℝ := {y : ℝ | ∃ p : ℝ × ℝ, heightV ψ v p = y ∧ fderiv ℝ (heightV ψ v) p = 0}
    with hCVdef
  have hCV0 : MeasureTheory.volume CV = 0 := by
    rw [hCVdef]
    refine Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic
      (contDiff_heightV ψ v) ?_ ?_
    · intro p
      show heightV ψ v (p.1 + 2 * Real.pi, p.2) = heightV ψ v p
      simp only [heightV]
      rw [Work.Drive.Mono.Band.par_add_two_pi_left ψ p]
    · intro p
      show heightV ψ v (p.1, p.2 + 2 * Real.pi) = heightV ψ v p
      simp only [heightV]
      rw [Work.Drive.Mono.Band.par_add_two_pi_right ψ p]
  -- ## 8. the avoidance
  obtain ⟨h, τ, hh1, hh2, hτ1, hτ2, hnoA, hnoB, hnoF1, hnoF2⟩ :=
    exists_window_avoiding hNbad0 hCV0 (a := inner ℝ v c + u) (tmin := 1 - δ) (tmax := 1 + δ)
      hwin (by linarith)
  -- ## 9. the final direction
  set nf : R3 := dirOf τ a₀ b₀ with hnfdef
  have hnf1 : ‖nf‖ = 1 := norm_dirOf ha hb hab τ
  have hvnf : inner ℝ v nf = 0 := inner_v_dirOf hva hvb τ
  have hgoodf : HeightGood ψ nf := hgoodτ τ (by rw [abs_lt]; exact ⟨by linarith, by linarith⟩)
  -- ## 10. regularity at the two face levels
  have hregA : ∀ p : ℝ × ℝ, p ∈ Kc → heightV ψ v p = inner ℝ v c + u + h →
      fderiv ℝ (heightV ψ v) p ≠ 0 := by
    intro p _ hval hd
    exact hnoA ⟨p, hval, hd⟩
  have hregB : ∀ p : ℝ × ℝ, p ∈ Kc → heightV ψ v p = inner ℝ v c + u - h →
      fderiv ℝ (heightV ψ v) p ≠ 0 := by
    intro p _ hval hd
    exact hnoB ⟨p, hval, hd⟩
  -- ## 11. the finiteness of the bad values
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
    have hb0 : betaV ψ v b₀ p ≠ 0 := hbad.2
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
            rw [hβ]; exact hb0⟩
      rw [show heightIn ψ nf p = heightIn ψ nf p₀ from by
        show inner ℝ nf (Work.BoxShrink.Pinch.par ψ p)
          = inner ℝ nf (Work.BoxShrink.Pinch.par ψ p₀)
        rw [hp₀par]]
      exact Set.mem_image_of_mem _ hmem
    · refine Set.mem_union_right _ ?_
      have hmem : p₀ ∈ ((bandChart ψ v a₀ b₀) ⁻¹' {(inner ℝ v c + u - h, τ)}) ∩ Kc
          ∩ chartDomain ψ v b₀ := ⟨⟨hstep _ h', hp₀K⟩, by
            show betaV ψ v b₀ p₀ ≠ 0
            rw [hβ]; exact hb0⟩
      rw [show heightIn ψ nf p = heightIn ψ nf p₀ from by
        show inner ℝ nf (Work.BoxShrink.Pinch.par ψ p)
          = inner ℝ nf (Work.BoxShrink.Pinch.par ψ p₀)
        rw [hp₀par]]
      exact Set.mem_image_of_mem _ hmem
  -- ## 12. the exceptional set
  have hcritfin : ({p : ℝ × ℝ | fderiv ℝ (heightIn ψ nf) p = 0} ∩
      (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi))).Finite :=
    Work.Drive.EpsForm.finite_critSet_box (heightIn_contDiff_two ψ nf) hgoodf.1
  refine ⟨v, nf, h, hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset,
    hv1, hnf1, hvnf, ?_, hh1, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt hwpos hh1
  · -- the cutting condition
    linarith
  · -- (i) the Hessian is nondegenerate at the critical points of the box-region
    intro p _ hcrit
    have hcrit' : fderiv ℝ (heightIn ψ nf) p = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit
    have h := hgoodf.1 p hcrit'
    rwa [Work.Drive.EpsForm.sweepHeight_innerSL]
  · -- (ii) the critical values with equal value have equal image
    intro p p' _ _ hcrit hcrit' hval
    have h1 : fderiv ℝ (heightIn ψ nf) p = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit
    have h2 : fderiv ℝ (heightIn ψ nf) p' = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit'
    have h3 : heightIn ψ nf p = heightIn ψ nf p' := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hval
    exact hgoodf.2 p p' h1 h2 h3
  · -- (iii) the critical values in the box are in the exceptional set
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
  · -- (iv) the bad face points have their values in the exceptional set
    intro p hpbox hface hcross
    refine Finset.mem_union_right _ ?_
    rw [hbadfin.mem_toFinset]
    exact ⟨p, hpbox, hface, by simpa only [← hnfdef] using hcross, rfl⟩

end

end Work.Drive.Mono.Band
