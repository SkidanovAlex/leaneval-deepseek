/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `(v'')²σ` coercivity bound on a `θ`-slice

With `v = u / cos θ` and `σ = sin(2θ)^{2-γ}`, `1 ≤ γ ≤ 3/2`, this module proves
`∫_{Iθ} (v'')² σ` is finite and bounded by `C (∫(g')²σ + ∫(u'')²sEta + ∫(u')² + ∫u²)`,
for `u` of class `C³` on `(0, π/2)` solving `Lzero1 u = g`.

The estimate is an assembly of the weighted interval integration-by-parts identity
(`slice_ibp_w`) on `[π/4, b]`, the pointwise boundary bound (`slice_bd_ptwise`), the
`(v')²σ` bound (`slice_Y2_le`), the `∫g²σ` bound (`slice_G2_le_fts`), the Hardy-type bound
(`slice_u_div_cos_sq_le`) for `(u/cos)²σ` and the left-half bound (`slice_left_le`); all of
these are collected in `slice_v2_interval`, which gives the interval estimate
`∫_{π/4}^{b} (v'')²σ ≤ CI · R` for every `b ∈ (π/4, π/2)`.  Here we

* push that interval estimate to the open interval `(π/4, π/2)` with
  `interval_integral_mono_limit` (which needs only continuity of the integrand and
  integrability on each `(π/4, b)`);
* add the left half `[0, π/4]` (`slice_left_le`);
* split `Iθ = [0, π/2]` at `π/4` (the point `π/4` and the endpoints are null)
  and read off the constant `C = CL + CI + 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.slice_left_le
import Submission.Work.FTS.EllipticEst.remov.slice_v2_interval
import Submission.Work.FTS.EllipticEst.remov.sliceLeftUniform
import Submission.Work.FTS.EllipticEst.remov.sliceV2IntervalUniform
import Submission.Work.FTS.EllipticEst.remov.interval_integral_mono_limit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The `(v'')²σ`-coercivity bound, `v = u/cos θ`, `σ = sin(2θ)^{2-γ}`, `1 ≤ γ ≤ 3/2`. -/
theorem sliceV2Uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), 1 ≤ γ → γ ≤ 3 / 2 →
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      (MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
              + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))) := by
  -- the two halves: the interval estimate on `(π/4, b)` and the bound on `[0, π/4]`
  obtain ⟨CI, hCIpos, hCI⟩ := sliceV2IntervalUniform
  obtain ⟨CL, hCLpos, hCL⟩ := sliceLeftUniform
  refine ⟨CL + CI + 1, by linarith, ?_⟩
  intro γ u g hγ1 hγ2 hu huc hu0 hupi hg hint2 hint1 hint0 hintg
  -- notational abbreviations (all `let`-definitions, hence definitionally equal to their bodies)
  let F : ℝ → ℝ := fun θ => (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 - γ)
  let D : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
  let B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  let C1 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2
  let C0 : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2
  let R : ℝ := D + B + C1 + C0
  change MeasureTheory.IntegrableOn F Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, F θ) ≤ (CL + CI + 1) * R
  -- nonnegativity of the four data integrals
  have hDnn : 0 ≤ D := by
    change 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
    rw [Work.Spaces.Iθ]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    rw [Set.mem_Icc] at hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩) _)
  have hBnn : 0 ≤ B := by
    change 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [Work.Spaces.Iθ]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    rw [Set.mem_Icc] at hθ
    refine mul_nonneg (sq_nonneg _) ?_
    rw [Work.FTS.EllipticEst.sEta]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩) _
  have hC1nn : 0 ≤ C1 := by
    change 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hC0nn : 0 ≤ C0 := by
    change 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hRnn : 0 ≤ R := by
    change 0 ≤ D + B + C1 + C0
    linarith
  -- the interval estimate, transported to `F`
  have hintv2 : ∀ b ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (∫ θ in (Real.pi / 4)..b, F θ) ≤ CI * R := by
    intro b hb
    exact hCI γ u g hγ1 hγ2 hu huc hu0 hupi hg hint2 hint1 hint0 hintg b hb
  -- `F` is continuous on the whole open interval
  have hcos_ne : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), Real.cos x ≠ 0 := by
    intro x hx
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  have hv2c : ContinuousOn (fun θ => deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hv : ContDiffOn ℝ 3 (fun s => u s / Real.cos s) (Set.Ioo 0 (Real.pi / 2)) :=
      hu.div ((Real.contDiff_cos (n := 3)).contDiffOn) hcos_ne
    have h1 : ContDiffOn ℝ 2 (deriv (fun s => u s / Real.cos s)) (Set.Ioo 0 (Real.pi / 2)) :=
      hv.deriv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)
    have h2 : ContDiffOn ℝ 1 (deriv (deriv (fun s => u s / Real.cos s)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    exact h2.continuousOn
  have hσcont : Continuous (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
    (Real.continuous_rpow_const (q := 2 - γ) (by linarith)).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hcontBig : ContinuousOn F (Set.Ioo 0 (Real.pi / 2)) := by
    change ContinuousOn (fun θ => (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Ioo 0 (Real.pi / 2))
    exact (hv2c.pow 2).mul hσcont.continuousOn
  have hnnF : ∀ x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), 0 ≤ F x := by
    intro x hx
    change 0 ≤ (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) (2 - γ)
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩) _)
  have hcont : ContinuousOn F (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    hcontBig.mono (Set.Ioo_subset_Ioo (by linarith [Real.pi_pos]) le_rfl)
  have hintF : ∀ b ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      MeasureTheory.IntegrableOn F (Set.Ioo (Real.pi / 4) b) := by
    intro b hb
    have hsub : Set.Icc (Real.pi / 4) b ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro x hx
      rw [Set.mem_Icc] at hx
      exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hb.2]⟩
    exact ((hcontBig.mono hsub).integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  -- pass to the open interval `(π/4, π/2)`
  obtain ⟨hintIoo, hbdIoo⟩ :=
    interval_integral_mono_limit (a := Real.pi / 4) (β := Real.pi / 2) (f := F) (K := CI * R)
      (by linarith [Real.pi_pos]) hcont hnnF hintF (fun b hb => hintv2 b hb)
  -- the left half
  obtain ⟨hLint, hLbd⟩ := hCL γ u g hγ1 hγ2 hu huc hu0 hupi hg hint2 hint1 hint0
  have hleftInt : MeasureTheory.IntegrableOn F (Set.Icc 0 (Real.pi / 4)) := hLint
  have hleftBd : (∫ θ in Set.Icc 0 (Real.pi / 4), F θ) ≤ CL * R := by
    have h : (∫ θ in Set.Icc 0 (Real.pi / 4), F θ) ≤ CL * (B + C1 + C0) := hLbd
    calc (∫ θ in Set.Icc 0 (Real.pi / 4), F θ) ≤ CL * (B + C1 + C0) := h
      _ ≤ CL * R := by
          change CL * (B + C1 + C0) ≤ CL * (D + B + C1 + C0)
          exact mul_le_mul_of_nonneg_left (by linarith) hCLpos.le
  -- split `Iθ` at `π/4`
  have hDisj : Disjoint (Set.Icc 0 (Real.pi / 4)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt_of_ge hx1.2))
  have hSsub : (Set.Icc 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2)) ⊆
      Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    rcases (Set.mem_union x _ _).mp hx with hx | hx
    · rw [Set.mem_Icc] at hx
      exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    · rw [Set.mem_Ioo] at hx
      exact ⟨by linarith [hx.1, Real.pi_pos], le_of_lt hx.2⟩
  have hsub1 : Work.Spaces.Iθ \
        (Set.Icc 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2)) ⊆
      ({Real.pi / 2} : Set ℝ) := by
    intro x hx
    rw [Set.mem_sdiff] at hx
    obtain ⟨hxIθ, hxS⟩ := hx
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hxIθ
    simp only [Set.mem_singleton_iff]
    by_contra hne
    have hxq : Real.pi / 4 < x := by
      rcases le_or_gt x (Real.pi / 4) with h | h
      · exact absurd ((Set.mem_union x (Set.Icc 0 (Real.pi / 4))
          (Set.Ioo (Real.pi / 4) (Real.pi / 2))).mpr (Or.inl ⟨hxIθ.1, h⟩)) hxS
      · exact h
    exact hxS ((Set.mem_union x (Set.Icc 0 (Real.pi / 4))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2))).mpr
        (Or.inr ⟨hxq, lt_of_le_of_ne hxIθ.2 hne⟩))
  have hSae : (Set.Icc 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2))
      =ᵐ[volume] Work.Spaces.Iθ := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, MeasureTheory.measure_mono_null hsub1 Real.volume_singleton⟩
    rw [Set.sdiff_eq_empty.mpr hSsub]
    exact MeasureTheory.measure_empty
  refine ⟨(hleftInt.union hintIoo).congr_set_ae hSae.symm, ?_⟩
  calc (∫ θ in Work.Spaces.Iθ, F θ)
      = ∫ θ in (Set.Icc 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2)), F θ :=
          (MeasureTheory.setIntegral_congr_set hSae).symm
    _ = (∫ θ in Set.Icc 0 (Real.pi / 4), F θ)
          + (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ) :=
          MeasureTheory.setIntegral_union hDisj measurableSet_Ioo hleftInt hintIoo
    _ ≤ CL * R + CI * R := add_le_add hleftBd hbdIoo
    _ ≤ (CL + CI + 1) * R := by nlinarith [hCLpos, hCIpos, hRnn]

end Work.FTS.EllipticEst.remov
