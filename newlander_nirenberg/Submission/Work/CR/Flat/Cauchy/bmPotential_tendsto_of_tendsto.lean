import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmSetup

noncomputable section

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter Metric

namespace Work.CR.Flat.Cauchy

/-- Pointwise bound for the Bochner–Martinelli kernel by the inverse power of the Euclidean norm.
For `n ≥ 1` the singular factor `‖x‖ ^ (1 - 2n)` is integrable in the `2n` real dimensions of
`ℂⁿ`, which is what makes the kernel locally integrable. -/
private lemma norm_bmKernel_le {n : ℕ} (j : Fin n) (w : Fin n → ℂ) :
    ‖bmKernel j w‖ ≤ ‖w‖ ^ (1 - 2 * (n : ℝ)) := by
  rw [bmKernel, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (eucNorm_nonneg w), Complex.norm_conj]
  by_cases hw : w = 0
  · subst hw
    simp only [Pi.zero_apply, norm_zero, eucNorm_zero, zero_div]
    exact Real.rpow_nonneg le_rfl _
  · have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have h1 : ‖w j‖ ≤ ‖w‖ := norm_le_pi_norm w j
    have h2 : ‖w‖ ^ (2 * n) ≤ eucNorm w ^ (2 * n) :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_eucNorm w) _
    have key : ‖w‖ ^ (1 - 2 * (n : ℝ)) = ‖w‖ / ‖w‖ ^ (2 * n) := by
      rw [Real.rpow_sub hwn (1:ℝ) (2*(n:ℝ)), Real.rpow_one,
        show (2*(n:ℝ)) = ((2*n : ℕ) : ℝ) from by push_cast; ring,
        Real.rpow_natCast]
    calc ‖w j‖ / eucNorm w ^ (2 * n)
        ≤ ‖w‖ / eucNorm w ^ (2 * n) :=
          div_le_div_of_nonneg_right h1 (pow_nonneg (eucNorm_nonneg w) _)
      _ ≤ ‖w‖ / ‖w‖ ^ (2 * n) :=
          div_le_div_of_nonneg_left hwn.le (pow_pos hwn _) h2
      _ = ‖w‖ ^ (1 - 2 * (n : ℝ)) := key.symm

private lemma measurable_bmKernel {n : ℕ} (j : Fin n) :
    Measurable (fun w : Fin n → ℂ => bmKernel j w) := by
  rw [show (fun w : Fin n → ℂ => bmKernel j w)
      = fun w => starRingEnd ℂ (w j) / (eucNorm w : ℂ) ^ (2 * n) from rfl]
  refine Measurable.div ((continuous_star.comp (continuous_apply j)).measurable) ?_
  exact ((Complex.continuous_ofReal.comp continuous_eucNorm).pow (2*n)).measurable

/-- The Bochner–Martinelli kernel is locally integrable on `ℂⁿ` for `n ≥ 1`. -/
private lemma locallyIntegrable_bmKernel {n : ℕ} (hn : 0 < n) (j : Fin n) :
    LocallyIntegrable (fun w : Fin n → ℂ => bmKernel j w) volume := by
  have hfr : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Complex.finrank_real_complex, smul_eq_mul]
    ring
  have hd : 1 ≤ Module.finrank ℝ (Fin n → ℂ) := by rw [hfr]; omega
  have hα : (2*(n:ℝ) - 1) < (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by
    rw [hfr]; push_cast; linarith
  refine locallyIntegrable_of_norm_le_rpow (C := 1) hd hα ?_ (measurable_bmKernel j).aestronglyMeasurable
  filter_upwards with w
  rw [one_mul]
  simpa [show -(2*(n:ℝ) - 1) = 1 - 2*(n:ℝ) from by ring] using norm_bmKernel_le j w

/-- A continuous compactly supported cutoff equal to `1` on a polydisc. -/
private lemma exists_cutoff_polydisc {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {s : Fin n → ℝ}
    (hs : ∀ j, 0 < s j) :
    ∃ η : (Fin n → ℂ) → ℝ, Continuous η ∧ HasCompactSupport η ∧ ∀ z ∈ polydisc c s, η z = 1 := by
  set ρ : ℝ := ∑ i, s i with hρdef
  have hsρ : ∀ i, s i ≤ ρ := fun i => by
    rw [hρdef]; exact Finset.single_le_sum (fun j _ => (hs j).le) (Finset.mem_univ i)
  obtain ⟨i0⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hρnn : 0 ≤ ρ := le_trans (hs i0).le (hsρ i0)
  obtain ⟨η, hη1, -, hηcs, -⟩ :=
    exists_continuous_one_zero_of_isCompact (X := Fin n → ℂ)
      (s := Metric.closedBall c ρ) (t := ∅) (isCompact_closedBall c ρ) isClosed_empty
      (by simp)
  refine ⟨η, η.continuous, hηcs, ?_⟩
  intro z hz
  apply hη1
  rw [Metric.mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hρnn]
  intro i
  exact le_trans (hz i).le (hsρ i)

/-- **Convergence of the Bochner–Martinelli potential under pointwise convergence.**

If a sequence `m ↦ F m` of families of continuous functions, uniformly bounded by `R` and
supported in the fixed polydisc `polydisc c s`, converges pointwise to `f`, then the
Bochner–Martinelli potentials converge pointwise to the potential of `f`. This is the dominated
convergence theorem, the dominating function being `‖bmKernel j (· - z)‖` times a compactly
supported cutoff; the singular kernel is locally integrable precisely because its singularity
`‖x‖ ^ (1-2n)` is integrable in the `2n` real dimensions of `ℂⁿ`. -/
theorem bmPotential_tendsto_of_tendsto {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {s : Fin n → ℝ}
    (hs : ∀ j, 0 < s j) {R : ℝ} (hR : 0 ≤ R)
    {F : ℕ → Fin n → (Fin n → ℂ) → ℂ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hFcont : ∀ m j, Continuous (F m j)) (hfcont : ∀ j, Continuous (f j))
    (hFbound : ∀ m j z, ‖F m j z‖ ≤ R) (hfbound : ∀ j z, ‖f j z‖ ≤ R)
    (hFsupp : ∀ m j z, (∃ i, s i ≤ ‖z i - c i‖) → F m j z = 0)
    (hfsupp : ∀ j z, (∃ i, s i ≤ ‖z i - c i‖) → f j z = 0)
    (hconv : ∀ j z, Filter.Tendsto (fun m => F m j z) Filter.atTop (nhds (f j z))) :
    ∀ z, Filter.Tendsto (fun m => Work.CR.Flat.Cauchy.bmPotential (F m) z) Filter.atTop
      (nhds (Work.CR.Flat.Cauchy.bmPotential f z)) := by
  obtain ⟨η, hηcont, hηcs, hηP⟩ := exists_cutoff_polydisc (c := c) hn hs
  set Gfun : ℝ → ℂ := fun r => (R : ℂ) * ((r : ℝ) : ℂ) with hGfundef
  have hGfuncont : Continuous Gfun := by
    rw [hGfundef]; exact continuous_const.mul Complex.continuous_ofReal
  have hGfun0 : Gfun 0 = 0 := by rw [hGfundef]; simp
  set g : (Fin n → ℂ) → ℂ := Gfun ∘ η with hgdef
  have hgcont : Continuous g := by
    rw [hgdef]; exact hGfuncont.comp hηcont
  have hgcs : HasCompactSupport g := by
    rw [hgdef]; exact hηcs.comp_left hGfun0
  intro z
  -- per-component dominated convergence
  have key : ∀ j, Filter.Tendsto (fun m => ∫ ζ, bmKernel j (ζ - z) * F m j ζ) Filter.atTop
      (nhds (∫ ζ, bmKernel j (ζ - z) * f j ζ)) := by
    intro j
    set Gζ : (Fin n → ℂ) → ℂ := fun ζ => bmKernel j (ζ - z) * g ζ with hGζdef
    set Gw : (Fin n → ℂ) → ℂ := fun w => bmKernel j w * g (w + z) with hGwdef
    have hcomp : Gζ = Gw ∘ (fun ζ : Fin n → ℂ => ζ - z) := by
      funext ζ
      simp only [Function.comp_apply, hGζdef, hGwdef, sub_add_cancel]
    have hGwcont : Continuous (fun w : Fin n → ℂ => g (w + z)) :=
      hgcont.comp (continuous_id.add continuous_const)
    have hGwcs : HasCompactSupport (fun w : Fin n → ℂ => g (w + z)) :=
      hgcs.comp_homeomorph (Homeomorph.addRight z)
    have hGwint : Integrable Gw volume := by
      have := (locallyIntegrable_bmKernel hn j).integrable_smul_right_of_hasCompactSupport
        hGwcont hGwcs
      simpa [hGwdef, smul_eq_mul] using this
    have hGwmeas : AEStronglyMeasurable Gw volume := by
      rw [hGwdef]
      exact ((measurable_bmKernel j).mul hGwcont.measurable).aestronglyMeasurable
    have hmp : MeasurePreserving (fun ζ : Fin n → ℂ => ζ - z) volume volume :=
      measurePreserving_sub_right volume z
    have hGζint : Integrable Gζ volume := by
      rw [hcomp]
      exact (hmp.integrable_comp hGwmeas).mpr hGwint
    -- dominated convergence theorem
    have hbound_int : Integrable (fun ζ => ‖Gζ ζ‖) volume := hGζint.norm
    have hF_meas : ∀ m, AEStronglyMeasurable (fun ζ => bmKernel j (ζ - z) * F m j ζ) volume := by
      intro m
      exact (((measurable_bmKernel j).comp
        (continuous_id.sub continuous_const).measurable).mul
        (hFcont m j).measurable).aestronglyMeasurable
    have h_bound : ∀ m, ∀ᵐ ζ ∂volume,
        ‖bmKernel j (ζ - z) * F m j ζ‖ ≤ ‖Gζ ζ‖ := by
      intro m
      filter_upwards with ζ
      have hle' : ‖F m j ζ‖ ≤ ‖g ζ‖ := by
        by_cases hζ : ζ ∈ polydisc c s
        · have h1 : η ζ = 1 := hηP ζ hζ
          have h2 : g ζ = (R : ℂ) := by
            rw [hgdef, Function.comp_apply, hGfundef, h1]; simp
          rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
          exact hFbound m j ζ
        · rw [polydisc, Set.mem_ofPred_eq] at hζ
          push_neg at hζ
          obtain ⟨i, hi⟩ := hζ
          rw [hFsupp m j ζ ⟨i, hi⟩, norm_zero]
          exact norm_nonneg _
      rw [norm_mul, show ‖Gζ ζ‖ = ‖bmKernel j (ζ - z)‖ * ‖g ζ‖ from by
        rw [hGζdef]; exact norm_mul _ _]
      exact mul_le_mul_of_nonneg_left hle' (norm_nonneg _)
    have h_lim : ∀ᵐ ζ ∂volume, Filter.Tendsto (fun m => bmKernel j (ζ - z) * F m j ζ) Filter.atTop
        (nhds (bmKernel j (ζ - z) * f j ζ)) := by
      filter_upwards with ζ
      exact (hconv j ζ).const_mul _
    exact tendsto_integral_of_dominated_convergence (fun ζ => ‖Gζ ζ‖)
      hF_meas hbound_int h_bound h_lim
  simp only [bmPotential]
  exact tendsto_finsetSum _ (fun j _ => key j)

end Work.CR.Flat.Cauchy
