import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.H2.T1Q.Cutoff
import Submission.Work.H2.T1Q.HardBoundQ
import Submission.Work.FTS.StrongPersist.N6Trans.HardSlotAux.IbpCutoffAnyQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `IbpSliceBound` — the cutoff-free angular integration-by-parts bound

The angular integration by parts of `Work.H2.T1Q.IbpCutoff` is localised away from the two
ends `θ = 0`, `θ = π/2` of the quadrant by a cutoff `χ`; here we remove the cutoff, at the
price of weakening the *identity* to an *inequality*:

  `|∫_θ sin(2θ)^{-q}·F·(sin(2θ)·V')·V| ≤ (3/2)·Kf·∫_θ V²·sin(2θ)^{-q}`

with the exponent range `|1 - q| ≤ 1` (i.e. `q ∈ [0,2]`, the range of the slots `η`, `γ`).

The proof uses the cutoff family `χ ζ` of `Work.H2.T1Q.Cutoff` at the scale `ζ`: for every `ζ`
the localised bound `Work.H2.T1Q.slotBound_cutoff` gives

  `|∫_θ χ_ζ·F·D_θV·V·sin(2θ)^{-q}| ≤ (3/2)Kf·∫_θ V²sin(2θ)^{-q}
      + (Kf·B/2)·(∫_{(0,2ζ)}V²sin(2θ)^{-q} + ∫_{(π/2-2ζ,π/2)}V²sin(2θ)^{-q})`,

with a *uniform* constant `B` (the uniform weighted derivative bound `|sin(2θ)·χ_ζ'| ≤ B` of
`Cutoff`).  Along the sequence `ζ_n = 1/(2(n+4))` the error terms vanish by
`Work.H2.T1Q.ShrinkInt`, the cutoffs converge to `1` almost everywhere, and
`Work.H2.T1Q.SliceLimit` passes to the limit, provided `θ ↦ sin(2θ)^{-q}F(sin(2θ)V')V` is
integrable; when it is not, the integral is `0` by definition and the estimate is trivial.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.HardSlotAux

set_option maxHeartbeats 800000

theorem IbpSliceBound :
    ∃ B : ℝ, 0 < B ∧ ∀ (q Kf : ℝ) (F V : ℝ → ℝ),
      0 ≤ Kf → |1 - q| ≤ 1 →
      ContDiffOn ℝ 1 F (Set.Ioo 0 (π / 2)) →
      ContDiffOn ℝ 1 V (Set.Ioo 0 (π / 2)) →
      (∀ θ ∈ Set.Ioo 0 (π / 2), |F θ| ≤ Kf) →
      (∀ θ ∈ Set.Ioo 0 (π / 2), |Real.sin (2 * θ) * deriv F θ| ≤ Kf) →
      MeasureTheory.IntegrableOn (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ →
      |∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-q) * F θ * (Real.sin (2 * θ) * deriv V θ) * V θ|
        ≤ (3 / 2 + B / 2) * Kf * ∫ θ in Work.Spaces.Iθ,
            (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := by
  obtain ⟨chi, B, hBpos, hchism, hchinn, hchile, hchione, hchiz0l, hchiz0r, hchid0l, hchid0r,
    hchibd, hchilim⟩ := Work.H2.T1Q.Cutoff
  refine ⟨B, hBpos, ?_⟩
  intro q Kf F V hKf0 hqabs hF1 hV1 hFb hFd hVint
  set g : ℝ → ℝ := fun θ =>
    (Real.sin (2 * θ)) ^ (-q) * F θ * (Real.sin (2 * θ) * deriv V θ) * V θ with hg
  set psi : ℝ → ℝ := fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) with hpsi
  -- nonnegativity of `psi`
  have hpsi_mem : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ psi θ := by
    intro θ hθ
    rw [hpsi]
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)
  have hpsi_nonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ, psi θ :=
    MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpsi_mem)
  have hpsi_int : MeasureTheory.IntegrableOn psi Work.Spaces.Iθ := by
    rw [hpsi]; exact hVint
  -- the pointwise bound on the `W`-factor of the localised integration by parts
  have hWb : ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(1 / 2) * (Real.sin (2 * θ) * deriv F θ) + (1 - q) * Real.cos (2 * θ) * F θ|
        ≤ (3 / 2) * Kf :=
    fun θ hθ => Work.H2.T1Q.Wq_bound hKf0 (hFd θ hθ) (hFb θ hθ) hqabs
  -- the support-weighted derivative bound of the cutoff at scale `ζ`
  have hsd : ∀ ζ : ℝ, 0 < ζ → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Real.sin (2 * θ) * deriv (chi ζ) θ|
        ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
            + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) := by
    intro ζ hζ θ hθ
    have hindnn : 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
        + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
      have ha : 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ := by
        by_cases hm : θ ∈ Set.Ioc 0 (2 * ζ)
        · simp [Set.indicator_of_mem hm]
        · simp [Set.indicator_of_notMem hm]
      have hb : 0 ≤ (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
        by_cases hm : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2)
        · simp [Set.indicator_of_mem hm]
        · simp [Set.indicator_of_notMem hm]
      linarith
    -- the derivative vanishes on the middle interval, where the cutoff is `1`
    have hmid : ∀ θ' ∈ Set.Ioo ζ (π / 2 - ζ), deriv (chi ζ) θ' = 0 := by
      intro θ' hθ'
      have hev : chi ζ =ᶠ[𝓝 θ'] (fun _ => (1 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ'] with t ht
        exact hchione ζ t hζ (le_of_lt ht.1) (le_of_lt ht.2)
      exact Work.H2.T1Q.deriv_eq_zero_of_eventuallyEq_one hev
    by_cases h1 : θ < ζ / 2
    · rw [hchid0l ζ θ hζ h1, mul_zero, abs_zero]
      exact mul_nonneg hBpos.le hindnn
    by_cases h2 : π / 2 - ζ / 2 < θ
    · rw [hchid0r ζ θ hζ h2, mul_zero, abs_zero]
      exact mul_nonneg hBpos.le hindnn
    by_cases h3 : θ ≤ 2 * ζ
    · have hA : θ ∈ Set.Ioc 0 (2 * ζ) := ⟨by linarith [hθ.1], h3⟩
      have hind : 1 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
        have ha : (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ = 1 :=
          Set.indicator_of_mem hA _
        have hb : 0 ≤ (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
          by_cases hm : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2)
          · simp [Set.indicator_of_mem hm]
          · simp [Set.indicator_of_notMem hm]
        rw [ha]; linarith
      calc |Real.sin (2 * θ) * deriv (chi ζ) θ| ≤ B := hchibd ζ hζ θ
        _ = B * 1 := by ring
        _ ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) :=
            mul_le_mul_of_nonneg_left hind hBpos.le
    · have h3' : 2 * ζ < θ := not_le.mp h3
      by_cases h4 : π / 2 - 2 * ζ < θ
      · have hB' : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2) :=
          ⟨h4, by linarith [not_lt.mp h2, Real.pi_pos]⟩
        have hind : 1 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
            + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
          have hb : (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ = 1 :=
            Set.indicator_of_mem hB' _
          have ha : 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ := by
            by_cases hm : θ ∈ Set.Ioc 0 (2 * ζ)
            · simp [Set.indicator_of_mem hm]
            · simp [Set.indicator_of_notMem hm]
          rw [hb]; linarith
        calc |Real.sin (2 * θ) * deriv (chi ζ) θ| ≤ B := hchibd ζ hζ θ
          _ = B * 1 := by ring
          _ ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
                + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) :=
              mul_le_mul_of_nonneg_left hind hBpos.le
      · have hmidz : deriv (chi ζ) θ = 0 :=
          hmid θ ⟨by linarith, by linarith [not_lt.mp h4]⟩
        rw [hmidz, mul_zero, abs_zero]
        exact mul_nonneg hBpos.le hindnn
  -- the localised integration by parts, in `IbpG`/`IbpK` form
  have hibp : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 / 4 →
      MeasureTheory.IntegrableOn (Work.H2.T1Q.IbpG q (chi ζ) F V) Work.Spaces.Iθ
      ∧ ∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpG q (chi ζ) F V θ
        = -∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpK q (chi ζ) F V θ := by
    intro ζ hζ hζ4
    have hδ : 0 < ζ / 2 := by linarith
    have hδ4 : ζ / 2 ≤ π / 4 := by linarith [Real.pi_gt_three]
    exact IbpCutoffAnyQ (q := q) (χ := chi ζ) (hf := F) (hv := V) (hchism ζ) hδ hδ4
      (fun θ hθ => hchiz0l ζ θ hζ hθ) (fun θ hθ => hchiz0r ζ θ hζ hθ) hF1 hV1
  -- the cutoff scales tend to `0⁺`
  have hζseq : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 4))) Filter.atTop
      (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hshift : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 4)) Filter.atTop Filter.atTop := by
        have h2 := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 4)
        simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h2
      have hmul : Filter.Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 4)) Filter.atTop Filter.atTop :=
        hshift.const_mul_atTop (by norm_num)
      have hinv : Filter.Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 4))⁻¹) Filter.atTop (nhds 0) :=
        hmul.inv_tendsto_atTop
      simpa [one_div] using hinv
    · refine Filter.Eventually.of_forall (fun n => ?_)
      show (0 : ℝ) < 1 / (2 * ((n : ℝ) + 4))
      positivity
  -- the shrinking error term
  set err : ℕ → ℝ := fun n => (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (1 / ((n : ℝ) + 4)), psi θ)
      + ∫ θ in Set.Ioc (π / 2 - 1 / ((n : ℝ) + 4)) (π / 2), psi θ) with herrdef
  have herr : Filter.Tendsto err Filter.atTop (nhds 0) := by
    rw [herrdef]
    have h := (Work.H2.T1Q.ShrinkInt (h := psi) hpsi_int).const_mul (Kf * B / 2)
    simpa only [mul_zero] using h
  -- the localised bound at scale `ζ_n`
  have hbd : ∀ n : ℕ, |∫ θ in Work.Spaces.Iθ, chi (1 / (2 * ((n : ℝ) + 4))) θ * g θ|
      ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, psi θ) + err n := by
    intro n
    set ζ : ℝ := 1 / (2 * ((n : ℝ) + 4)) with hζdef
    have hn4 : (0 : ℝ) < (n : ℝ) + 4 := by
      have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hζ0 : 0 < ζ := by rw [hζdef]; positivity
    have hζ4 : ζ ≤ 1 / 4 := by
      rw [hζdef]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h1 : (2 : ℝ) * 4 ≤ 2 * ((n : ℝ) + 4) := by linarith
      calc 1 / (2 * ((n : ℝ) + 4)) ≤ 1 / (2 * 4) := one_div_le_one_div_of_le (by norm_num) h1
        _ ≤ 1 / 4 := by norm_num
    have hζ2 : 2 * ζ ≤ π / 2 := by linarith [hζ4, Real.pi_gt_three]
    obtain ⟨hAint, hIBP⟩ := hibp ζ hζ0 hζ4
    have hb := Work.H2.T1Q.slotBound_cutoff (q := q) (Kf := Kf) (B := B) (ζ := ζ)
      (χ := chi ζ) (F := F) (V := V) hKf0 hBpos.le hζ0 hζ2 (fun θ => hchinn ζ θ)
      (fun θ => hchile ζ θ) (hsd ζ hζ0) hFb hWb hVint hAint hIBP
    have hLfun : (∫ θ in Work.Spaces.Iθ,
          chi ζ θ * (F θ * (Real.sin (2 * θ) * deriv V θ) * V θ * (Real.sin (2 * θ)) ^ (-q)))
        = ∫ θ in Work.Spaces.Iθ, chi ζ θ * g θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [hg]; ring
    rw [hLfun] at hb
    have h2ζ : 2 * ζ = 1 / ((n : ℝ) + 4) := by
      rw [hζdef]
      field_simp
    rw [h2ζ] at hb
    simpa only [herrdef, hζdef] using hb
  by_cases hLint : MeasureTheory.IntegrableOn g Work.Spaces.Iθ
  · -- the genuine case: pass to the limit in `ζ`
    have hlim : |∫ θ in Work.Spaces.Iθ, g θ| ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, psi θ) :=
      Work.H2.T1Q.SliceLimit (φ := g) (chi := fun n : ℕ => chi (1 / (2 * ((n : ℝ) + 4))))
        (M := (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, psi θ)) (err := err) herr hLint
        (fun n => ((hchism _).continuous).aestronglyMeasurable)
        (fun n θ => by rw [abs_of_nonneg (hchinn _ θ)]; exact hchile _ θ)
        (by
          filter_upwards [Work.H2.T1Q.ae_Iθ_mem_Ioo] with θ hθ
          exact (hchilim θ hθ.1 hθ.2).comp hζseq)
        hbd
    refine le_trans hlim ?_
    have h1 : 0 ≤ (B / 2) * Kf * (∫ θ in Work.Spaces.Iθ, psi θ) :=
      mul_nonneg (mul_nonneg (by linarith [hBpos]) hKf0) hpsi_nonneg
    nlinarith [h1]
  · -- the degenerate case: not integrable, so the integral is `0` by definition
    have hzero : (∫ θ in Work.Spaces.Iθ, g θ) = 0 := MeasureTheory.integral_undef hLint
    rw [hzero, abs_zero]
    exact mul_nonneg (mul_nonneg (by linarith [hBpos]) hKf0) hpsi_nonneg

end Work.FTS.StrongPersist.N6Trans.HardSlotAux
