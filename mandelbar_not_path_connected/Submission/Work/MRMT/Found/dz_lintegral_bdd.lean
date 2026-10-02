/-
`Work.MRMT.Found.dz_lintegral_bdd` — uniform bound on the `∂`-energy of the approximants
`F n` of the principal solution, measured on an arbitrary compact set.

The key input is the area bound `dzSq_integral_le_area`: since `F n` is an injective `C¹` map
whose complex dilatation is bounded by `d.k < 1`, the `L²` norm of `∂(F n)` over a ball is
controlled by the area of the image of that ball.  The images `(F n) '' B(0,R)` all lie in one
fixed ball because the sequence `F n` converges locally uniformly to `φ`, hence is uniformly
bounded on the compact `cl B(0,R)`.  Finally the `lintegral` over an arbitrary compact `K` is
bounded by the `lintegral` over a ball containing `K`, and for a *continuous* integrand the
`lintegral` of `ENNReal.ofReal` is the `ENNReal.ofReal` of the Bochner integral.

Note this does **not** need `μ` to be admissible: the only property of `μ` used is that the
approximants `μn n` are bounded by `d.k < 1` (`PrincipalData.norm_μn`), which is part of the
record.  This is why the statement has no `Admissible μ` hypothesis.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.dzSq_integral_le_area

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function Bornology
open scoped Topology ENNReal

set_option linter.unusedVariables false

namespace Work.MRMT.Found

/-- A sequence of continuous functions on `ℂ` converging locally uniformly to a continuous
limit is *uniformly* bounded on every compact set: on the compact set the convergence is
uniform, which bounds all but finitely many terms at once, and the finitely many remaining
terms are bounded because each of them is continuous on a compact set.

(This is a copy of the private lemma of the same name in `uniform_dz_bound.lean`, made
available here because it is `private` there.) -/
private lemma exists_forall_norm_le_of_tendstoLocallyUniformly {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : TendstoLocallyUniformly F f atTop) (hf : Continuous f) (hFc : ∀ n, Continuous (F n))
    {K : Set ℂ} (hK : IsCompact K) : ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖F n z‖ ≤ M := by
  have hunif : TendstoUniformlyOn F f atTop K :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hF) K hK
  have hev : ∀ᶠ n in atTop, ∀ x ∈ K, dist (f x) (F n x) < 1 :=
    (Metric.tendstoUniformlyOn_iff.mp hunif) 1 one_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨Mf, hMf⟩ := (hK.image hf).isBounded.exists_norm_le
  have hbdd : ∀ n, ∃ Mn : ℝ, ∀ z ∈ K, ‖F n z‖ ≤ Mn := by
    intro n
    obtain ⟨Mn, hMn⟩ := ((hK.image (hFc n)).isBounded).exists_norm_le
    exact ⟨Mn, fun z hz => hMn (F n z) ⟨z, hz, rfl⟩⟩
  choose M hM using hbdd
  refine ⟨max (Mf + 1)
      (Finset.sup' (Finset.range (N + 1))
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ M), ?_⟩
  intro n z hz
  by_cases hn : N ≤ n
  · have hd : dist (f z) (F n z) < 1 := hN n hn z hz
    have hd' : ‖F n z - f z‖ < 1 := by
      rw [dist_eq_norm] at hd
      simpa [norm_sub_rev] using hd
    have h1 : ‖F n z‖ ≤ ‖f z‖ + 1 := by
      calc ‖F n z‖ = ‖f z + (F n z - f z)‖ := by
            congr 1
            ring
        _ ≤ ‖f z‖ + ‖F n z - f z‖ := norm_add_le _ _
        _ ≤ ‖f z‖ + 1 := by linarith
    calc ‖F n z‖ ≤ ‖f z‖ + 1 := h1
      _ ≤ Mf + 1 := by linarith [hMf (f z) ⟨z, hz, rfl⟩]
      _ ≤ max (Mf + 1) _ := le_max_left _ _
  · have hn' : n < N := not_le.mp hn
    have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    calc ‖F n z‖ ≤ M n := hM n z hz
      _ ≤ Finset.sup' (Finset.range (N + 1))
            ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ M := Finset.le_sup' M hmem
      _ ≤ max (Mf + 1) _ := le_max_right _ _

/-- **Uniform bound on the `∂`-energy of the approximants over a ball.**

For principal data `d` for `μ`, the sequence `n ↦ ∫_{B(0,R)} ‖∂(F n)‖²` is bounded uniformly
in `n`.  (No admissibility of `μ` is needed: only the dilatation bound `d.k < 1` on the smooth
approximants `d.μn n` is used.) -/
theorem dzSq_ball_integral_le {μ : ℂ → ℂ} (d : PrincipalData μ) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∫ z in Metric.ball 0 R, ‖dz ((d.Fn n) : ℂ → ℂ) z‖ ^ 2 ≤ C := by
  have hk0 : 0 ≤ d.k := le_trans (norm_nonneg (d.μn 0 0)) (d.norm_μn 0 0)
  have hk2 : 0 < 1 - d.k ^ 2 := by nlinarith [d.hk]
  have hR0 : 0 ≤ R := le_of_lt hR
  obtain ⟨M, hM⟩ := exists_forall_norm_le_of_tendstoLocallyUniformly d.tendsto_Fn
    d.φ.continuous (fun n => (d.Fn n).continuous) (isCompact_closedBall (0 : ℂ) R)
  refine ⟨(1 - d.k ^ 2)⁻¹ * ((volume : Measure ℂ) (Metric.closedBall 0 M)).toReal, ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.mpr hk2.le) ENNReal.toReal_nonneg
  · intro n
    have hb := dzSq_integral_le_area hk0 d.hk (d.contDiff_Fn n) (d.Fn n).injective
      (fun z => by
        rw [d.beltrami_Fn n z, norm_mul]
        exact mul_le_mul_of_nonneg_right (d.norm_μn n z) (norm_nonneg _)) (0 : ℂ) hR0
    refine le_trans hb (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hk2.le))
    have hsub : ((d.Fn n : ℂ → ℂ) '' Metric.ball 0 R) ⊆ Metric.closedBall 0 M := by
      rintro y ⟨z, hz, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hM n z (Metric.ball_subset_closedBall hz)
    exact ENNReal.toReal_mono ((isCompact_closedBall (0 : ℂ) M).measure_lt_top.ne)
      (measure_mono hsub)

/-- **Uniform bound on the `∂`-energy of the approximants over a compact set.**

For principal data `d` for `μ` and any compact `K ⊆ ℂ`, the quantities
`∫⁻_K ‖∂(F n)‖²` are bounded uniformly in `n`.  The compact set is contained in a ball, where
the area bound `dzSq_ball_integral_le` gives a uniform bound; the `lintegral` over `K` of the
(continuous) integrand is the `ENNReal.ofReal` of the Bochner integral, so it inherits the
bound. -/
theorem dz_lintegral_bdd {μ : ℂ → ℂ} (d : Work.MRMT.Found.PrincipalData μ) {K : Set ℂ}
    (hK : IsCompact K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ,
      ∫⁻ z in K, ENNReal.ofReal ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖ ^ 2 ≤ ENNReal.ofReal D := by
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  have hRpos : 0 < max M 0 + 1 := by have : 0 ≤ max M 0 := le_max_right _ _; linarith
  obtain ⟨C, hC0, hC⟩ := dzSq_ball_integral_le d (R := max M 0 + 1) hRpos
  have hKR : K ⊆ Metric.ball 0 (max M 0 + 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : M ≤ max M 0 := le_max_left _ _
    linarith [hM z hz]
  refine ⟨C, hC0, ?_⟩
  intro n
  have hdzc : Continuous (fun z : ℂ => dz ((d.Fn n) : ℂ → ℂ) z) := by
    have hfd : Continuous (fderiv ℝ (((d.Fn n) : ℂ → ℂ))) :=
      (d.contDiff_Fn n).continuous_fderiv (by norm_num)
    simp only [dz]
    exact ((hfd.clm_apply continuous_const).sub
      (continuous_const.mul (hfd.clm_apply continuous_const))).div_const 2
  have hcont : Continuous (fun z : ℂ => ‖dz ((d.Fn n) : ℂ → ℂ) z‖ ^ 2) := (hdzc.norm).pow 2
  have hintK : Integrable (fun z : ℂ => ‖dz ((d.Fn n) : ℂ → ℂ) z‖ ^ 2) (volume.restrict K) :=
    ContinuousOn.integrableOn_compact hK hcont.continuousOn
  have hintB : Integrable (fun z : ℂ => ‖dz ((d.Fn n) : ℂ → ℂ) z‖ ^ 2)
      (volume.restrict (Metric.ball 0 (max M 0 + 1))) :=
    IntegrableOn.mono_set
      (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 (max M 0 + 1)) hcont.continuousOn)
      Metric.ball_subset_closedBall
  have e1 : ∫⁻ z in K, ENNReal.ofReal ‖dz ((d.Fn n) : ℂ → ℂ) z‖ ^ 2
      = ∫⁻ z in K, ENNReal.ofReal (‖dz ((d.Fn n) : ℂ → ℂ) z‖ ^ 2) :=
    lintegral_congr (fun z => (ENNReal.ofReal_pow (norm_nonneg (dz ((d.Fn n) : ℂ → ℂ) z)) 2).symm)
  rw [e1, ← ofReal_integral_eq_lintegral_ofReal hintK (Eventually.of_forall fun z => sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hmono : ∫ z in K, ‖dz ((d.Fn n) : ℂ → ℂ) z‖ ^ 2
      ≤ ∫ z in Metric.ball 0 (max M 0 + 1), ‖dz ((d.Fn n) : ℂ → ℂ) z‖ ^ 2 :=
    setIntegral_mono_set hintB (Eventually.of_forall fun z => sq_nonneg _)
      (Eventually.of_forall fun z hz => hKR hz)
  linarith [hC n]

end Work.MRMT.Found
