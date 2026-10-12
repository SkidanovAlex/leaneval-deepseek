import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Filter Metric
open scoped Topology ENNReal Real FourierTransform BigOperators

namespace Work.BoseFixB1S.kineticCrux

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- Norm of the multiplier `fourierPowSMulRight` on a single direction: for a complex number
`z`, a real `x` and `N : ℕ`,
`‖(-(2πI))^N • (x^N) • z‖ = (2π)^N |x|^N ‖z‖`. -/
private lemma norm_neg_two_pi_I_pow_smul (z : ℂ) (x : ℝ) (N : ℕ) :
    ‖(-(2 * (Real.pi : ℂ) * Complex.I)) ^ N • (x ^ N : ℝ) • z‖
      = (2 * Real.pi) ^ N * |x| ^ N * ‖z‖ := by
  have ha : ‖(-(2 * (Real.pi : ℂ) * Complex.I))‖ = 2 * Real.pi := by
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_of_nonneg Real.pi_nonneg, Complex.norm_ofNat]
  rw [norm_smul, norm_smul, norm_pow, ha, Real.norm_eq_abs, abs_pow]
  ring

/-- **Fourier transform of a directional iterated derivative.**  For `u : ℝ³ → ℂ` smooth and
compactly supported, `N : ℕ`, and any `v p : ℝ³`,

`‖kinFT (fun x ↦ (iteratedFDeriv ℝ N u x) (fun _ ↦ v)) p‖ = |⟪v,p⟫|^N ‖kinFT u p‖`.

(So the `N`-fold derivative of `u` in a direction `v` transforms into multiplication by
`⟪v,p⟫^N`.) -/
lemma kinFT_iteratedFDeriv_dir (u : E3 → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcs : HasCompactSupport u) (N : ℕ) (v p : E3) :
    ‖Submission.BoseGases.kinFT (fun x => (iteratedFDeriv ℝ N u x) (fun _ : Fin N => v)) p‖
      = |inner ℝ v p| ^ N * ‖Submission.BoseGases.kinFT u p‖ := by
  have hInt : ∀ n : ℕ, (n : ℕ∞) ≤ ⊤ → Integrable (iteratedFDeriv ℝ n u) := by
    intro n _
    exact (hu.continuous_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport (hcs.iteratedFDeriv n)
  have hfour := Real.fourier_iteratedFDeriv (N := (⊤ : ℕ∞)) (f := u) hu hInt (n := N) le_top
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier,
    Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  set w : E3 := (2 * Real.pi)⁻¹ • p with hw
  have heval :
      (𝓕 (fun x => (iteratedFDeriv ℝ N u x) (fun _ : Fin N => v))) w
        = ((𝓕 (iteratedFDeriv ℝ N u)) w) (fun _ : Fin N => v) := by
    rw [Real.fourier_eq, Real.fourier_eq]
    have hI' : Integrable (fun x : E3 => 𝐞 (-inner ℝ x w) • (iteratedFDeriv ℝ N u x)) volume :=
      (Real.fourierIntegral_convergent_iff (μ := volume) (f := iteratedFDeriv ℝ N u) w).mpr
        (hInt N le_top)
    rw [ContinuousMultilinearMap.integral_apply hI']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rfl
  rw [heval, hfour, VectorFourier.fourierPowSMulRight_apply]
  have hinner : ∀ i : Fin N, ((-innerSL ℝ) w) v = -(inner ℝ w v) := by
    intro i
    rw [show ((-innerSL ℝ) w) v = -(((innerSL ℝ) w) v) from rfl, innerSL_apply_apply]
  have hprod : (∏ i : Fin N, ((-innerSL ℝ) w) v) = (-(inner ℝ w v)) ^ N := by
    rw [Finset.prod_congr rfl (fun i _ => hinner i), Finset.prod_const]
    simp
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have harith : ∀ x : ℝ, (2 * Real.pi) ^ N * |(2 * Real.pi)⁻¹ * x| ^ N = |x| ^ N := by
    intro x
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr h2pi.le), ← mul_pow]
    congr 1
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h2pi), one_mul]
  have hwv : inner ℝ w v = (2 * Real.pi)⁻¹ * inner ℝ v p := by
    rw [hw, real_inner_smul_left, real_inner_comm v p]
  rw [hprod, norm_neg_two_pi_I_pow_smul, hwv, abs_neg, harith]

/-- **Pointwise Fourier decay.**  For `u : ℝ³ → ℂ` smooth with compact support and all `p`,

`‖p‖^N ‖kinFT u p‖ ≤ ∫ x, ‖iteratedFDeriv ℝ N u x‖`. -/
lemma kinFT_decay_core (N : ℕ) (u : E3 → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcs : HasCompactSupport u) (p : E3) :
    ‖p‖ ^ N * ‖Submission.BoseGases.kinFT u p‖ ≤ ∫ x, ‖iteratedFDeriv ℝ N u x‖ := by
  by_cases hp : p = 0
  · subst hp
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have h0 : Submission.BoseGases.kinFT u 0 = ∫ y, u y := by
        rw [Submission.BoseGases.kinFT]
        apply integral_congr_ae
        filter_upwards with y
        simp
      rw [pow_zero, one_mul, h0]
      calc ‖∫ y, u y‖ ≤ ∫ y, ‖u y‖ := norm_integral_le_integral_norm _
        _ = ∫ y, ‖iteratedFDeriv ℝ 0 u y‖ := by simp
    · rw [norm_zero, zero_pow (ne_of_gt hN), zero_mul]
      exact integral_nonneg (fun x => norm_nonneg _)
  · have hpnorm : 0 < ‖p‖ := norm_pos_iff.mpr hp
    set v : E3 := ‖p‖⁻¹ • p with hv
    have hvnorm : ‖v‖ = 1 := by
      rw [hv, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),
        inv_mul_cancel₀ (ne_of_gt hpnorm)]
    have hvp : inner ℝ v p = ‖p‖ := by
      rw [hv, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    have hkey := kinFT_iteratedFDeriv_dir u hu hcs N v p
    have hnorm1 : ‖p‖ ^ N * ‖Submission.BoseGases.kinFT u p‖
        = ‖Submission.BoseGases.kinFT
            (fun x => (iteratedFDeriv ℝ N u x) (fun _ : Fin N => v)) p‖ := by
      rw [hkey, hvp, abs_of_nonneg (norm_nonneg p)]
    rw [hnorm1]
    have hInt : Integrable (fun x => ‖iteratedFDeriv ℝ N u x‖) :=
      ((hu.continuous_iteratedFDeriv
        (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport
          (hcs.iteratedFDeriv N)).norm
    have hstep1 : ‖Submission.BoseGases.kinFT
          (fun x => (iteratedFDeriv ℝ N u x) (fun _ : Fin N => v)) p‖
        ≤ ∫ x, ‖(iteratedFDeriv ℝ N u x) (fun _ : Fin N => v)‖ := by
      rw [Submission.BoseGases.kinFT]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      apply integral_congr_ae
      filter_upwards with x
      have hre : (-(Complex.I * (inner ℝ p x : ℂ))).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, one_mul]
    have hstep2 : ∫ x, ‖(iteratedFDeriv ℝ N u x) (fun _ : Fin N => v)‖
        ≤ ∫ x, ‖iteratedFDeriv ℝ N u x‖ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
        hInt (Filter.Eventually.of_forall fun x => ?_)
      calc ‖(iteratedFDeriv ℝ N u x) (fun _ : Fin N => v)‖
          ≤ ‖iteratedFDeriv ℝ N u x‖ * ∏ _ : Fin N, ‖v‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖iteratedFDeriv ℝ N u x‖ := by rw [hvnorm]; simp
    exact hstep1.trans hstep2

/-- **The `L¹` bound for the `N`-th derivative.**  If `ψ` is compactly supported with
`tsupport ψ ⊆ closedBall x₀ A` and `‖iteratedFDeriv ℝ N ψ x‖ ≤ B / A^N` everywhere, then

`∫ x, ‖iteratedFDeriv ℝ N ψ x‖ ≤ (4π/3) A³ (B/A^N)`. -/
lemma kinFTDerivIntegral (N : ℕ) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    {x₀ : E3} {ψ : E3 → ℂ} (hcs : HasCompactSupport ψ)
    (hsupp : ∀ x ∈ tsupport ψ, ‖x - x₀‖ ≤ A)
    (hderiv : ∀ x : E3, ‖iteratedFDeriv ℝ N ψ x‖ ≤ B / A ^ N) :
    ∫ x : E3, ‖iteratedFDeriv ℝ N ψ x‖ ≤ 4 * Real.pi / 3 * A ^ 3 * (B / A ^ N) := by
  set S : Set E3 := Metric.closedBall x₀ A with hS
  have hsub : Function.support (iteratedFDeriv ℝ N ψ) ⊆ S := by
    refine (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := ψ) N).trans ?_
    intro x hx
    rw [hS, Metric.mem_closedBall, dist_eq_norm]
    exact hsupp x hx
  have hzero : ∀ x ∉ S, ‖iteratedFDeriv ℝ N ψ x‖ = 0 := by
    intro x hx
    have hx' : x ∉ Function.support (iteratedFDeriv ℝ N ψ) := fun h => hx (hsub h)
    simp only [Function.mem_support, not_not] at hx'
    rw [hx', norm_zero]
  have hvol : volume.real S = 4 * Real.pi / 3 * A ^ 3 := by
    rw [hS, Measure.real_def, EuclideanSpace.volume_closedBall_fin_three,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hA.le,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi * 4 / 3)]
    ring
  have hfin : volume S < ⊤ := (isCompact_closedBall x₀ A).measure_lt_top
  have h1 : ‖∫ x in S, ‖iteratedFDeriv ℝ N ψ x‖‖ ≤ (B / A ^ N) * volume.real S :=
    norm_setIntegral_le_of_norm_le_const hfin (fun x _ => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hderiv x)
  have hnn : 0 ≤ ∫ x in S, ‖iteratedFDeriv ℝ N ψ x‖ :=
    setIntegral_nonneg measurableSet_closedBall (fun x _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hnn] at h1
  rw [hvol] at h1
  calc ∫ x : E3, ‖iteratedFDeriv ℝ N ψ x‖
      = ∫ x in S, ‖iteratedFDeriv ℝ N ψ x‖ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ ≤ (B / A ^ N) * (4 * Real.pi / 3 * A ^ 3) := h1
    _ = 4 * Real.pi / 3 * A ^ 3 * (B / A ^ N) := by ring

/-- **The radial tail integral.** For `N > 5` and `c > 0`,

`∫_{‖p‖ ≥ c} ‖p‖^{2-N} dp = 4π / ((N-5) c^{N-5})`. -/
lemma kinFTRadialTail (N : ℕ) (hN : 5 < N) {c : ℝ} (hc : 0 < c) :
    ∫ p in {p : E3 | c ≤ ‖p‖}, ‖p‖ ^ ((2 : ℝ) - (N : ℝ))
      = 4 * Real.pi / (((N : ℝ) - 5) * c ^ (N - 5)) := by
  have hN5' : (5 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set S : Set E3 := {p : E3 | c ≤ ‖p‖} with hS
  set g : ℝ → ℝ := fun y => if c ≤ y then y ^ ((2 : ℝ) - (N : ℝ)) else 0 with hg
  have hmes : MeasurableSet S := measurableSet_le measurable_const continuous_norm.measurable
  have hind : S.indicator (fun p : E3 => ‖p‖ ^ ((2 : ℝ) - (N : ℝ))) = fun p : E3 => g ‖p‖ := by
    funext p
    by_cases hp : c ≤ ‖p‖
    · rw [Set.indicator_of_mem (show p ∈ S from hp), hg]
      simp [hp]
    · rw [Set.indicator_of_notMem (show p ∉ S from hp), hg]
      simp [hp]
  rw [← MeasureTheory.integral_indicator hmes (f := fun p : E3 => ‖p‖ ^ ((2 : ℝ) - (N : ℝ))),
    hind]
  rw [MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure E3)) (f := g)]
  rw [finrank_euclideanSpace_fin]
  have h1d : ∫ y in Set.Ioi (0 : ℝ), y ^ (3 - 1) • g y
      = c ^ ((5 : ℝ) - (N : ℝ)) / ((N : ℝ) - 5) := by
    have hcongr : (fun y : ℝ => y ^ (3 - 1) • g y)
        = (Set.Ici c).indicator (fun y : ℝ => y ^ (3 - 1) * y ^ ((2 : ℝ) - (N : ℝ))) := by
      funext y
      rw [hg]
      by_cases hy : c ≤ y
      · simp [hy, Set.indicator_of_mem, smul_eq_mul]
      · simp [hy, Set.indicator_of_notMem, smul_eq_mul]
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ici c = Set.Ici c := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      exact ⟨fun h => h.2, fun h => ⟨hc.trans_le h, h⟩⟩
    have hpow : ∀ y ∈ Set.Ioi c, y ^ (3 - 1) * y ^ ((2 : ℝ) - (N : ℝ))
        = y ^ ((4 : ℝ) - (N : ℝ)) := by
      intro y hy
      have hy0 : 0 < y := hc.trans hy
      rw [← Real.rpow_natCast y (3 - 1), show ((3 - 1 : ℕ) : ℝ) = 2 by norm_num,
        ← Real.rpow_add hy0,
        show (2 : ℝ) + ((2 : ℝ) - (N : ℝ)) = (4 : ℝ) - (N : ℝ) by ring]
    rw [hcongr, MeasureTheory.setIntegral_indicator measurableSet_Ici, hset,
      integral_Ici_eq_integral_Ioi,
      setIntegral_congr_fun measurableSet_Ioi hpow,
      integral_Ioi_rpow_of_lt (a := (4 : ℝ) - (N : ℝ)) (c := c) (by linarith) hc,
      show (4 : ℝ) - (N : ℝ) + 1 = -(((N : ℝ) - 5)) by ring, neg_div_neg_eq,
      show -(((N : ℝ) - 5)) = (5 : ℝ) - (N : ℝ) by ring]
  rw [h1d]
  have hvol : (volume : Measure E3).real (Metric.ball 0 1) = Real.pi * 4 / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num),
      ENNReal.toReal_ofReal (by positivity)]
    norm_num
  rw [hvol]
  have hN5 : ((N : ℝ) - 5) ≠ 0 := by linarith
  have hcpow : c ^ ((5 : ℝ) - (N : ℝ)) = (c ^ (N - 5))⁻¹ := by
    rw [show (5 : ℝ) - (N : ℝ) = -(((N : ℝ) - 5)) by ring, Real.rpow_neg hc.le,
      show ((N : ℝ) - 5) = ((N - 5 : ℕ) : ℝ) by
        rw [Nat.cast_sub (by omega : 5 ≤ N)]; norm_num, Real.rpow_natCast]
  rw [hcpow, nsmul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- **Tail decay of `kinFT` at scale `A`.**  A compactly supported smooth `ψ` whose
derivatives up to order `N` are bounded by `B / A^j` (with support within `A` of `x₀`)
has Fourier transform decaying so that

`∫_{‖p‖ ≥ c} ‖p‖² ‖kinFT ψ p‖ ≤ C B / A² / (A c)^{N-5}` for all `c ≥ 1/A`. -/
theorem kinFT_decay_scale (N : ℕ) (hN : 5 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A B : ℝ}, 0 < A → 0 ≤ B → ∀ {x₀ : EuclideanSpace ℝ (Fin 3)}
      {ψ : EuclideanSpace ℝ (Fin 3) → ℂ},
      ContDiff ℝ (⊤ : ENat) ψ → HasCompactSupport ψ →
      (∀ x ∈ tsupport ψ, ‖x - x₀‖ ≤ A) →
      (∀ (j : ℕ), j ≤ N → ∀ x : EuclideanSpace ℝ (Fin 3),
        ‖iteratedFDeriv ℝ j ψ x‖ ≤ B / A ^ j) →
      ∀ c : ℝ, 1 / A ≤ c →
        ∫ p in {p : EuclideanSpace ℝ (Fin 3) | c ≤ ‖p‖},
            ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ p‖
          ≤ C * B / A ^ 2 / (A * c) ^ (N - 5) := by
  have hN5pos : (0 : ℝ) < (N : ℝ) - 5 := by
    have : (5 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  refine ⟨16 * Real.pi ^ 2 / (3 * ((N : ℝ) - 5)), by positivity, ?_⟩
  intro A B hA hB x₀ ψ hψd hψs hsupp hderiv c hc
  have hcpos : 0 < c := lt_of_lt_of_le (one_div_pos.mpr hA) hc
  set S : Set E3 := {p : E3 | c ≤ ‖p‖} with hS
  set K : ℝ := ∫ x : E3, ‖iteratedFDeriv ℝ N ψ x‖ with hK
  have hKbound : K ≤ 4 * Real.pi / 3 * A ^ 3 * (B / A ^ N) := by
    rw [hK]
    exact kinFTDerivIntegral N hA hB hψs hsupp (fun x => hderiv N le_rfl x)
  -- pointwise decay on the shell
  have hpoint : ∀ p ∈ S, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ p‖
      ≤ K * ‖p‖ ^ ((2 : ℝ) - (N : ℝ)) := by
    intro p hp
    have hpnorm : 0 < ‖p‖ := hcpos.trans_le hp
    have hcore : ‖p‖ ^ N * ‖Submission.BoseGases.kinFT ψ p‖ ≤ K := by
      rw [hK]
      exact kinFT_decay_core N ψ hψd hψs p
    have hpowpos : 0 < ‖p‖ ^ N := pow_pos hpnorm N
    have h1 : ‖Submission.BoseGases.kinFT ψ p‖ ≤ K / ‖p‖ ^ N := by
      rw [le_div_iff₀ hpowpos, mul_comm]
      exact hcore
    calc ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ p‖
        ≤ ‖p‖ ^ 2 * (K / ‖p‖ ^ N) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K * ‖p‖ ^ ((2 : ℝ) - (N : ℝ)) := by
          have h2 : ‖p‖ ^ ((2 : ℝ) - (N : ℝ)) = ‖p‖ ^ 2 / ‖p‖ ^ N := by
            rw [Real.rpow_sub hpnorm, Real.rpow_ofNat (n := 2), Real.rpow_natCast]
          rw [h2]
          generalize hb : ‖p‖ ^ N = b
          ring
  -- integrability of the majorant, from the computed value of its integral
  have hSint : IntegrableOn (fun p : E3 => ‖p‖ ^ ((2 : ℝ) - (N : ℝ))) S := by
    by_contra hcon
    have h0 : ∫ p in S, ‖p‖ ^ ((2 : ℝ) - (N : ℝ)) = 0 := integral_undef hcon
    rw [hS, kinFTRadialTail N hN hcpos] at h0
    have hpos : 0 < 4 * Real.pi / (((N : ℝ) - 5) * c ^ (N - 5)) := by positivity
    linarith
  have hmajint : IntegrableOn (fun p : E3 => K * ‖p‖ ^ ((2 : ℝ) - (N : ℝ))) S :=
    hSint.const_mul K
  have hmono : ∫ p in S, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ p‖
      ≤ ∫ p in S, K * ‖p‖ ^ ((2 : ℝ) - (N : ℝ)) :=
    setIntegral_mono_of_nonneg (fun p _ => by positivity) (fun p hp => hpoint p hp) hmajint
  have hval : ∫ p in S, K * ‖p‖ ^ ((2 : ℝ) - (N : ℝ))
      = K * (4 * Real.pi / (((N : ℝ) - 5) * c ^ (N - 5))) := by
    rw [MeasureTheory.integral_const_mul, hS, kinFTRadialTail N hN hcpos]
  calc ∫ p in S, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ p‖
      ≤ ∫ p in S, K * ‖p‖ ^ ((2 : ℝ) - (N : ℝ)) := hmono
    _ = K * (4 * Real.pi / (((N : ℝ) - 5) * c ^ (N - 5))) := hval
    _ ≤ (4 * Real.pi / 3 * A ^ 3 * (B / A ^ N)) *
          (4 * Real.pi / (((N : ℝ) - 5) * c ^ (N - 5))) :=
        mul_le_mul_of_nonneg_right hKbound (by positivity)
    _ = 16 * Real.pi ^ 2 / (3 * ((N : ℝ) - 5)) * B / A ^ 2 / (A * c) ^ (N - 5) := by
        have hA' : A ^ N = A ^ (N - 5) * A ^ 5 := by
          rw [← pow_add, Nat.sub_add_cancel (by omega : 5 ≤ N)]
        have hN5 : ((N : ℝ) - 5) ≠ 0 := by linarith
        have hcN : c ^ (N - 5) ≠ 0 := by positivity
        have hAN : A ^ (N - 5) ≠ 0 := by positivity
        rw [show (A * c) ^ (N - 5) = A ^ (N - 5) * c ^ (N - 5) by rw [mul_pow], hA']
        field_simp
        ring

end Work.BoseFixB1S.kineticCrux
