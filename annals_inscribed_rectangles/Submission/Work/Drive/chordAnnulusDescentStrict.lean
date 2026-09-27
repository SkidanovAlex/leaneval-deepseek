import Mathlib
import Submission.Work.Drive.bandData
import Submission.Work.Drive.seeleyDescent_ext

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff
open Set Filter

noncomputable section

/-- **The chord data descended across the seam, with the STRICT band estimate on the annulus
`1/2 ≤ ‖x‖ ≤ 2`.**

Strict strengthening of the band clause of `Work.Drive.chordAnnulusDescent` (which gives
`‖M (x,τ)‖² ≥ 2 * |τ| * ‖W (x,τ)‖²`): here

> `2 * |τ| * ‖W (x,τ)‖² < ‖M (x,τ)‖²`  for `1/2 ≤ ‖x‖ ≤ 2`, `-c ≤ τ < 0`,

and in addition `W` does not vanish on the diagonal `1/2 ≤ ‖x‖ ≤ 1`, `τ = 0` (the sibling only had
the non-vanishing clause for `M` there).

The construction is the one of `Work.Drive.bandMidData` / `Work.Drive.bandWData` (the `bandMu`-blend
of the chord data with a constant, which is globally `C^∞` and even in the opening), descended to the
`τ = s²` variable by `Work.Drive.seeleyDescent_ext`.  On the unit circle the blend is inactive
(`Work.Drive.bandMu_circle`) so the descent reproduces the honest data.  The only difference with the
sibling is in the propagation step: on the compact diagonal `S = {1/2 ≤ ‖x‖ ≤ 2, τ = 0}` one has
`0 < ‖M p‖² - 2 * |p.2| * ‖W p‖²` (the term `2 * |p.2| * ‖W p‖²` *vanishes* on `S`, and
`M (x,0) = dataMid γ x 0 = curvePtAt γ x 0 ≠ 0` because `γ x ≠ 0`) *and* `W p ≠ 0`; the set where
both strict conditions hold is *open* and a thickening of the compact `S` lies inside it, so on that
collar the inequality is *strict* — which is exactly the strict band clause. -/
theorem chordAnnulusDescentStrict (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) :
    ∃ M W : ℂ × ℝ → ℂ, ∃ c : ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧
      0 < c ∧
      (∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
        M (x, τ) = Work.Drive.Neutral.dataMid γ x (Real.sqrt τ)) ∧
      (∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
        W (x, τ) = Work.Drive.Neutral.dchW γ (x, Real.sqrt τ)) ∧
      (∀ x : ℂ, ∀ τ : ℝ, 1 / 2 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
        2 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2) ∧
      (∀ x : ℂ, ∀ τ : ℝ, 1 / 2 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0) ∧
      (∀ x : ℂ, 1 / 2 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0) ∧
      (∀ x : ℂ, 1 / 2 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0) := by
  -- ## The blended, globally smooth and even data
  obtain ⟨M, hMsm, hMval⟩ := seeleyDescent_ext (X := ℂ) (E := ℂ) (F := bandMidData γ 1)
    (contDiff_bandMidData γ hγ 1) (fun x t => bandMidData_even γ 1 (x, t))
  obtain ⟨W, hWsm, hWval⟩ := seeleyDescent_ext (X := ℂ) (E := ℂ) (F := bandWData γ 1)
    (contDiff_bandWData γ hγ 1) (fun x t => bandWData_even γ 1 (x, t))
  -- ## The values on the unit circle: the blend is inactive there
  have hMid0 : ∀ x : ℂ, 1 / 4 ≤ Complex.normSq x → ∀ s : ℝ,
      bandMidData γ 1 (x, s) = Neutral.dataMid γ x s := by
    intro x hx s
    simp only [bandMidData, bandMu_eq_one hx]
    simp
  have hW0 : ∀ x : ℂ, 1 / 4 ≤ Complex.normSq x → ∀ s : ℝ,
      bandWData γ 1 (x, s) = Neutral.dchW γ (x, s) := by
    intro x hx s
    simp only [bandWData, bandMu_eq_one hx]
    simp
  have hns : ∀ x : ℂ, ‖x‖ = 1 → 1 / 4 ≤ Complex.normSq x := by
    intro x hx
    rw [Complex.normSq_eq_norm_sq, hx]; norm_num
  -- the chord midpoint on the diagonal is non-zero
  have hmid_ne : ∀ x : ℂ, 1 / 2 ≤ ‖x‖ → Neutral.dataMid γ x 0 ≠ 0 := by
    intro x hx h
    have hx0 : x ≠ 0 := by intro hz; rw [hz, norm_zero] at hx; norm_num at hx
    have hpt : Neutral.dataMid γ x 0 = Neutral.curvePtAt γ x 0 := by
      simp only [Neutral.dataMid, Neutral.endPlus, Neutral.endMinus, neg_zero,
        add_self_div_two]
    rw [hpt] at h
    have hθ : (Circle.exp (Complex.arg x) : ℂ) = x / (‖x‖ : ℂ) := by
      rw [← Neutral.toCirc_eq_exp_arg x hx0, Neutral.toCirc_coe]
    rw [Neutral.curvePtAt_eq_exp γ x hx0 hθ 0] at h
    have hsc : Neutral.sClamp (0 : ℝ) = 0 :=
      Neutral.sClamp_eq_self (by rw [abs_zero]; positivity)
    rw [hsc, add_zero] at h
    exact hγne (Circle.exp (Complex.arg x)) (Neutral.symmC_eq_zero_iff.mp h)
  have hW_ne : ∀ x : ℂ, x ≠ 0 → Neutral.dchW γ (x, 0) ≠ 0 :=
    fun x hx => (Neutral.stripDiskChordNe γ hγ).2 x hx 0
  -- ## The compact set `S` and the open condition
  set S : Set (ℂ × ℝ) :=
    {p : ℂ × ℝ | 1 / 2 ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ 2 ∧ p.2 = 0} with hSdef
  have hScompact : IsCompact S := by
    have hsub : S ⊆ Metric.closedBall (0 : ℂ × ℝ) 3 := by
      intro q hq
      rw [hSdef] at hq
      obtain ⟨h1, h2, h3⟩ := hq
      rw [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def]
      simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, norm_zero, max_le_iff]
      exact ⟨by simpa only [Real.norm_eq_abs] using (show ‖q.1‖ ≤ 3 by linarith),
        by rw [h3]; norm_num⟩
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ × ℝ) 3) ?_ hsub
    exact (isClosed_le continuous_const (continuous_norm.comp continuous_fst)).inter
      ((isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
        (isClosed_eq continuous_snd continuous_const))
  have hcont : Continuous fun p : ℂ × ℝ =>
      ‖M p‖ ^ 2 - 2 * |p.2| * ‖W p‖ ^ 2 :=
    (hMsm.continuous.norm.pow 2).sub
      ((continuous_const.mul continuous_snd.abs).mul (hWsm.continuous.norm.pow 2))
  have hSopen : IsOpen {p : ℂ × ℝ | 0 < ‖M p‖ ^ 2 - 2 * |p.2| * ‖W p‖ ^ 2 ∧ W p ≠ 0} :=
    (isOpen_lt continuous_const hcont).inter (isOpen_ne.preimage hWsm.continuous)
  have hSsub : S ⊆ {p : ℂ × ℝ | 0 < ‖M p‖ ^ 2 - 2 * |p.2| * ‖W p‖ ^ 2 ∧ W p ≠ 0} := by
    intro q hq
    rw [hSdef] at hq
    obtain ⟨x, τ⟩ := q
    obtain ⟨h1, h2, h3⟩ := hq
    subst h3
    have hx0 : x ≠ 0 := by intro hz; rw [hz, norm_zero] at h1; norm_num at h1
    have h1' : 1 / 4 ≤ Complex.normSq x := by rw [Complex.normSq_eq_norm_sq]; nlinarith
    have hMx : M (x, 0) = Neutral.dataMid γ x 0 := by
      rw [hMval x 0 le_rfl, Real.sqrt_zero, hMid0 x h1' 0]
    have hWx : W (x, 0) = Neutral.dchW γ (x, 0) := by
      rw [hWval x 0 le_rfl, Real.sqrt_zero, hW0 x h1' 0]
    constructor
    · rw [hMx, hWx]
      simp only [abs_zero]
      nlinarith [pow_pos (norm_pos_iff.mpr (hmid_ne x h1)) 2,
        sq_nonneg ‖Neutral.dchW γ (x, 0)‖]
    · rw [hWx]
      exact hW_ne x hx0
  obtain ⟨δ, hδpos, hδ⟩ := hScompact.exists_thickening_subset_open hSopen hSsub
  have hdist : ∀ (x : ℂ) (τ : ℝ), dist ((x, τ) : ℂ × ℝ) (x, (0 : ℝ)) = |τ| := by
    intro x τ
    rw [dist_eq_norm, Prod.norm_def]
    simp
  refine ⟨M, W, δ / 2, hMsm, hWsm, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x τ hτ hx
    rw [hMval x τ hτ, hMid0 x (hns x hx) (Real.sqrt τ)]
  · intro x τ hτ hx
    rw [hWval x τ hτ, hW0 x (hns x hx) (Real.sqrt τ)]
  · intro x τ h1 h2 h3 h4
    have hmem : (x, τ) ∈ Metric.thickening δ S :=
      Metric.mem_thickening_iff.mpr ⟨(x, 0), ⟨h1, h2, rfl⟩, by
        rw [hdist]; rw [abs_of_neg h4]; linarith⟩
    have hpos : 0 < ‖M (x, τ)‖ ^ 2 - 2 * |τ| * ‖W (x, τ)‖ ^ 2 := (hδ hmem).1
    linarith
  · intro x τ h1 h2 h3 h4
    refine (hδ ?_).2
    exact Metric.mem_thickening_iff.mpr ⟨(x, 0), ⟨h1, h2, rfl⟩, by
      rw [hdist]; rw [abs_of_neg h4]; linarith⟩
  · intro x h1 h2
    have hx0 : x ≠ 0 := by intro hz; rw [hz, norm_zero] at h1; norm_num at h1
    have h1' : 1 / 4 ≤ Complex.normSq x := by rw [Complex.normSq_eq_norm_sq]; nlinarith
    rw [hMval x 0 le_rfl, Real.sqrt_zero, hMid0 x h1' 0]
    exact hmid_ne x h1
  · intro x h1 h2
    have hx0 : x ≠ 0 := by intro hz; rw [hz, norm_zero] at h1; norm_num at h1
    have h1' : 1 / 4 ≤ Complex.normSq x := by rw [Complex.normSq_eq_norm_sq]; nlinarith
    rw [hWval x 0 le_rfl, Real.sqrt_zero, hW0 x h1' 0]
    exact hW_ne x hx0

end

end Work.Drive
