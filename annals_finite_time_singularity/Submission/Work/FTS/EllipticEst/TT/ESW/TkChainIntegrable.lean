/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ESW.TkChainIntegrable`

The `m`-th plain angular slot of a datum `v ∈ ℋ^K` (`1 ≤ m ≤ K`), with its sharp weight
`sin(2θ)^{2m-γ}`, is integrable on the angular interval `Iθ = [0,π/2]` for every `z ∈ Iz`, and
its angular integral `z ↦ w(z)² ∫_θ (∂_θ^m v)² · sin(2θ)^{2m-γ}` is integrable on `Iz = [0,∞)`.

The mathematics is the weighted `D_θ`-chain of the `ℋ^K`-norm: `D_θ^m = Σ_{r ≤ m} a_{m,r}(θ) ∂_θ^r`
is triangular with respect to the plain angular derivatives, with diagonal coefficient
`a_{m,m} = sin(2θ)^m`, so that

  `w(z)² · (∂_θ^m v)² · sin(2θ)^{2m-γ} ≤ C · HkIntegrand α K v`    (a.e. in `θ`)

(`slot_pointwise_HkIntegrand_allAlpha`, the form of the chain of
`remov.high_chain_sum_self` in which the positivity of `α` is *not* needed — the chain itself is
`α`-free, only the weight identity uses `sin(2θ) > 0`), with a constant depending on `m` only.
Since `HkIntegrand α K v` is integrable on `Iθ` for every `z ∈ Iz` and on `Iz` — the two
conjuncts of `HkMem α K v` — both statements follow by `Integrable.mono'`: the a.e. strong
measurability of the angular slice comes from the joint continuity of the integrand on the open
quadrant, and that of the `z`-integral from `SrcBnd.SlotAESM` (plus the unconditional identity
`∫_θ w(z)² F = w(z)² ∫_θ F` bringing it into the stated shape).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SrcBnd.SlotAESM

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT.ESW

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary facts about the angular weight -/

/-- `sin(2θ) > 0` on the open quadrant. -/
private theorem sin_two_pos_Q0 {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.sin (2 * p.2) := by
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- `θ ↦ sin(2θ)^c` is continuous on the open quadrant. -/
private theorem continuousOn_sin_rpow_Q0 (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.EllipticEst.Q0 :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Q0 hp)))

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- A pointwise statement on `Iθ` is an a.e. statement for `volume.restrict Iθ`. -/
private theorem ae_Iθ_of_forall {p : ℝ → Prop} (h : ∀ θ ∈ Work.Spaces.Iθ, p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p θ :=
  MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc h

/-! ## The pointwise `D_θ`-chain, with no positivity hypothesis on `α`

This is the statement of `remov.selfdth.slot_pointwise_HkIntegrand` with the (vestigial)
hypothesis `0 < α` removed; the proof is the same, since neither the chain of `dthChain_core`
nor the weight identity `slot_sq_eq_Wt_sq` (whose only hypothesis is `sin(2θ) > 0`) refers to
the sign of `α`. -/
theorem slot_pointwise_HkIntegrand_allAlpha (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (v : ℝ → ℝ → ℝ) (K : ℕ), m ≤ K →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m v z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))
          ≤ C * Work.Spaces.HkIntegrand α K v z θ := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.EllipticEst.remov.selfdth.dthChain_core m hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine ⟨C0 * m, mul_pos hC0pos hmpos, ?_⟩
  intro α v K hmK hsm z hz
  have hz0 : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz0 with hzeq | hzpos
  · -- `z = 0`: the radial weight vanishes, and the right-hand side is nonnegative.
    have hw0 : (Work.Spaces.w z) ^ 2 = 0 := by rw [hzeq.symm]; norm_num [Work.Spaces.w]
    refine Eventually.of_forall (fun θ => ?_)
    rw [hw0, zero_mul]
    exact mul_nonneg (mul_pos hC0pos hmpos).le
      (Work.Spaces.HkIntegrand_nonneg α K v z θ)
  · -- `z > 0`: the genuine pointwise chain.
    refine Work.FTS.EllipticEst.remov.selfdth.ae_mem_Ioo_of_Iθ.mono (fun θ hθ => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    have hcd : ∀ k : ℕ, ContDiffAt ℝ k (Function.uncurry v) (z, θ) := fun k =>
      (hsm k).contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hzpos, hθ⟩)
    rw [Work.FTS.EllipticEst.remov.selfdth.slot_sq_eq_Wt_sq m α z θ v hs]
    have hsum : (∑ r ∈ Finset.Icc 1 m,
          (Work.Spaces.DthIter r v z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2)
        ≤ (m : ℝ) * Work.Spaces.HkIntegrand α K v z θ := by
      have hbd : ∀ r ∈ Finset.Icc 1 m,
          (Work.Spaces.DthIter r v z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α K v z θ := by
        intro r hr
        obtain ⟨hr1, _⟩ := Finset.mem_Icc.mp hr
        simpa only [Work.Spaces.mixed_zero_left, mul_pow] using
          (Work.Spaces.sq_le_HkIntegrand_mixed α K v z θ r 0 hr1 (by omega))
      calc (∑ r ∈ Finset.Icc 1 m,
            (Work.Spaces.DthIter r v z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2)
          ≤ ∑ _r ∈ Finset.Icc 1 m, Work.Spaces.HkIntegrand α K v z θ :=
            Finset.sum_le_sum hbd
        _ = (m : ℝ) * Work.Spaces.HkIntegrand α K v z θ := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    calc ((Real.sin (2 * θ)) ^ m * Work.Spaces.pthIter m v z θ) ^ 2
            * (Work.Spaces.Wt α z θ) ^ 2
        ≤ (C0 * ∑ r ∈ Finset.Icc 1 m, (Work.Spaces.DthIter r v z θ) ^ 2)
            * (Work.Spaces.Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (hC0 v z θ hθ hcd) (sq_nonneg _)
      _ = C0 * ((∑ r ∈ Finset.Icc 1 m, (Work.Spaces.DthIter r v z θ) ^ 2)
            * (Work.Spaces.Wt α z θ) ^ 2) := by ring
      _ = C0 * ∑ r ∈ Finset.Icc 1 m,
            (Work.Spaces.DthIter r v z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by
          rw [Finset.sum_mul]
      _ ≤ C0 * ((m : ℝ) * Work.Spaces.HkIntegrand α K v z θ) :=
          mul_le_mul_of_nonneg_left hsum hC0pos.le
      _ = (C0 * m) * Work.Spaces.HkIntegrand α K v z θ := by ring

/-! ## The target -/

theorem TkChainIntegrable {α : ℝ} {K : ℕ} {v : ℝ → ℝ → ℝ} {m : ℕ} (hm : 1 ≤ m) (hmK : m ≤ K)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α K v) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
        Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
        Work.Spaces.Iz := by
  classical
  obtain ⟨C, hCpos, hC⟩ := slot_pointwise_HkIntegrand_allAlpha m hm
  -- the two intervals are measurable
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  -- the a.e. strong measurability of the slice integrand and of its `z`-integral
  have hv : Work.FTS.EllipticEst.SmoothOpen v := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hσc : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 * (m : ℝ) - Work.Spaces.gam α))
      Work.FTS.EllipticEst.Q0 := continuousOn_sin_rpow_Q0 _
  obtain ⟨hAESM_slice, hAESM_int⟩ := Work.FTS.EllipticEst.SrcBnd.SlotAESM (n := m)
    (σ := fun θ => (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) hv hσc
  -- the same, in the shape of the statement (the constant `w z ^ 2` pulled out of the integral)
  have hAESM_int' : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hAESM_int.congr (Filter.Eventually.of_forall (fun z =>
      MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        ((Work.Spaces.w z) ^ 2)
        (fun θ => (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))))
  -- nonnegativity of a single angular integrand, on `Iθ`
  have hslot_nn : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      0 ≤ (Work.Spaces.pthIter m v z θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α) :=
    fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
  constructor
  · -- first conjunct: the angular slot is integrable on `Iθ` for every `z ∈ Iz`
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
    · -- `z = 0`: the integrand vanishes identically
      subst h0
      have hzero : (fun θ : ℝ => (Work.Spaces.w 0) ^ 2 * ((Work.Spaces.pthIter m v 0 θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
            = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        simp [Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · -- `z > 0`: dominate by the integrable `HkIntegrand`
      refine ((hmem.1 z hz).const_mul C).mono' (hAESM_slice z hz) ?_
      filter_upwards [hC α v K hmK hsm z hz, MeasureTheory.ae_restrict_mem hIθ] with θ hθ hθmem
      have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)) :=
        mul_nonneg (sq_nonneg _) (hslot_nn z θ hθmem)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hθ
  · -- second conjunct: the angular integral is integrable on `Iz`
    have hmaj : MeasureTheory.IntegrableOn
        (fun z => C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α K v z θ)
        Work.Spaces.Iz := hmem.2.const_mul C
    refine hmaj.mono' hAESM_int' ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIz] with z hzmem
    -- the pointwise (in `z`) bound, by monotonicity of the angular integral
    have hkey : (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α K v z θ) := by
      rw [(MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
            ((Work.Spaces.w z) ^ 2)
            (fun θ => (Work.Spaces.pthIter m v z θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))).symm,
        (MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) C
            (fun θ => Work.Spaces.HkIntegrand α K v z θ)).symm]
      exact MeasureTheory.integral_mono_of_nonneg
        (ae_Iθ_of_forall (fun θ hθ => mul_nonneg (sq_nonneg _) (hslot_nn z θ hθ)))
        ((hmem.1 z hzmem).const_mul C)
        (hC α v K hmK hsm z hzmem)
    have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
        (ae_Iθ_of_forall (fun θ hθ => hslot_nn z θ hθ)))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hkey

end

end Work.FTS.EllipticEst.TT.ESW
