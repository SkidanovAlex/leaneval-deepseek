import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PressureOn.OffPlanes.offPlanes_ibp
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.PressureOn.weakCurl.weyl_cross
import Submission.Work.FTS.PressureOn.weakDiv_timeDeriv
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.logW_fderiv_integral_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumZ0
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.SP6.EH6
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_BSIdentP.Slim.TendstoSliceQuotient
import Submission.Work.FTS_LocDatum3a.Assembly
import Submission.Work.FTS_LocDatum3a.Basic
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.Spaces.pz_mixed_mul_le_4
-- ===== merged: Submission.Work.FTS.EpsEngine.HkSq_JepsPz_le8 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The target.**  `J_ε` maps the weighted space `X` of the `ε`-scheme into the projected
`ℋᵏ`-space for every `k ≤ 8`, at a cost of one factor `C/ε` per derivative.

It is the order-`8` slot estimate `EpsSqIter_mixed_Jeps_le_gen ρ hρ 8` (`EpsSqIter_mixed_Jeps_le6`
was the `k ≤ 6` case) fed into the assembly `HkSq_JepsPz_le8_of_slot`, which is the proof of
`EpsSqTools.HkSq_JepsPz_le` with the order-`8` bump bound `exists_HkNorm_bump_le8` and the
cardinal constants `9`, `81`, `90`, `180` replacing `7`, `49`, `56`, `112`. -/
theorem HkSq_JepsPz_le8 (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ k : ℕ, k ≤ 8 → ∀ f : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.StrongEps.EpsMem α f →
        Work.Spaces.HkSq α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
          ≤ C * (C / ε) ^ (2 * (k : ℕ)) * Work.FTS.StrongEps.EpsSq α f := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := EpsSqIter_mixed_Jeps_le_gen ρ hρ 8
  exact Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le8_of_slot ρ hρ hC₀pos hC₀

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.Data =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

noncomputable section

/-- The slice of a clamped field at time `s` is the slice of the original at the clamped time. -/
theorem extendTime_slice (v : R3 → ℝ → R3) (S : ℝ) (s : ℝ) :
    (extendTime v S · s) = fun x => v x (clampt S s) := rfl

/-- The clamped slice inherits the regularity of the strip. -/
theorem contDiff_extendTime_slice {α : NNReal} {v : R3 → ℝ → R3} {S : ℝ} (hS : 0 ≤ S)
    (hstrip : IsContDiffHolderOn ℝ α v.uncurry (Set.univ ×ˢ Set.Icc 0 S)) (s : ℝ) :
    ContDiff ℝ 1 (extendTime v S · s) := by
  have h := contDiff_slice_of_isContDiffHolderOn (τ := clampt S s) hstrip (clampt_mem_Icc hS s)
  show ContDiff ℝ 1 fun x => v x (clampt S s)
  exact h

/-- The clamped time lies in `[0,T)` as soon as `S < T`. -/
theorem clampt_mem_Ico_of_lt {S T s : ℝ} (hS : S < T) (h0 : 0 ≤ S) :
    clampt S s ∈ Set.Ico (0 : ℝ) T :=
  ⟨clampt_nonneg S s, lt_of_le_of_lt (clampt_mem_Icc h0 s).2 hS⟩

/-- **The clamped vorticity is the curl of the clamped velocity.** -/
theorem vorticity_extendTime {u ω : R3 → ℝ → R3} {S T : ℝ} (hS : S ∈ Set.Ioo 0 T)
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x, FiniteTimeSingularity.vorticity (u · s) x = ω x s) (s : ℝ) :
    FiniteTimeSingularity.vorticity (extendTime u S · s) = (extendTime ω S · s) := by
  funext x
  rw [extendTime_slice, extendTime_apply]
  exact hcurl (clampt S s) (clampt_mem_Ico_of_lt hS.2 hS.1.le) x

/-- **The clamped velocity is divergence-free.** -/
theorem div_extendTime {u : R3 → ℝ → R3} {S T : ℝ} (hS : S ∈ Set.Ioo 0 T)
    (hdiv : ∀ s ∈ Set.Ico 0 T, FiniteTimeSingularity.div (u · s) = 0) (s : ℝ) :
    FiniteTimeSingularity.div (extendTime u S · s) = 0 := by
  rw [extendTime_slice]
  exact hdiv (clampt S s) (clampt_mem_Ico_of_lt hS.2 hS.1.le)


/-- **The right derivative of a clamped field at an interior time.** -/
theorem hasDerivWithinAt_extendTime {v : R3 → ℝ → R3} {S t : ℝ} (ht : t ∈ Set.Ioo 0 S)
    (h : ∀ x, HasDerivWithinAt (v x) (FiniteTimeSingularity.timeDeriv v x t) (Set.Ici t) t)
    (x : R3) :
    HasDerivWithinAt (extendTime v S x) (FiniteTimeSingularity.timeDeriv (extendTime v S) x t)
      (Set.Ici t) t := by
  rw [timeDeriv_extendTime ht x]
  exact (h x).congr_of_eventuallyEq_of_mem (eventuallyEq_extendTime_Ici ht x) (le_refl t)

/-- A Lipschitz constant for a bound holding on all of `[0,S]` against an interior point is
nonnegative (for `t < S` the bound is applied at a point `s ≠ t`). -/
theorem nonneg_of_lipschitz {v : R3 → ℝ → R3} {t S C : ℝ} (ht0 : 0 ≤ t) (htS : t < S)
    (h : ∀ x, ∀ s ∈ Set.Icc 0 S, ‖v x s - v x t‖ ≤ C * |s - t|) : 0 ≤ C := by
  by_contra hC
  push_neg at hC
  have hpos : 0 < (S - t) / 2 := by linarith
  have hs : t + (S - t) / 2 ∈ Set.Icc (0 : ℝ) S := by constructor <;> linarith
  have habs : |t + (S - t) / 2 - t| = (S - t) / 2 := by
    rw [add_sub_cancel_left, abs_of_pos hpos]
  have hle := h 0 (t + (S - t) / 2) hs
  rw [habs] at hle
  nlinarith [norm_nonneg (v 0 (t + (S - t) / 2) - v 0 t)]

/-- **The vorticity slice is continuous**, being the curl of the `C¹` velocity slice. -/
theorem continuous_vorticity_slice {α : NNReal} {ω : R3 → ℝ → R3} {T S t : ℝ} (hST : S < T)
    (ht : t ∈ Set.Icc 0 S)
    (hstrip : IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry
      (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s) :
    Continuous (fun x => ω x t) := by
  have htT : t ∈ Set.Ico 0 T := ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
  have hcv : ContDiff ℝ 1 (Work.FTS.Physical.physVel ω · t) :=
    contDiff_slice_of_isContDiffHolderOn hstrip ht
  have hfun : (fun x => ω x t)
      = FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z t) :=
    funext fun x => (hcurl t htT x).symm
  rw [hfun]
  exact Work.FTS.BSSwirl.continuous_vorticity hcv

/-- The Lamb vector vanishes wherever the vorticity does. -/
theorem lamb_eq_zero_of_right_eq_zero {u ω : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : ω x t = 0) : Work.FTS.PressureOn.lamb u ω x t = 0 := by
  have h1 : ‖Work.FTS.PressureOn.lamb u ω x t‖ ≤ ‖u x t‖ * ‖ω x t‖ :=
    vorticityCross_norm_crossVec_le (u x t) (ω x t)
  rw [h, norm_zero, mul_zero] at h1
  exact norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _))

/-- **The Lamb-vector slice is compactly supported** as soon as the vorticity slice is. -/
theorem hasCompactSupport_lamb_slice {u ω : R3 → ℝ → R3} {R t : ℝ}
    (hsupp : ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R) :
    HasCompactSupport (fun x => Work.FTS.PressureOn.lamb u ω x t) :=
  hasCompactSupport_of_norm_bound (fun x hx =>
    hsupp x (fun h => hx (lamb_eq_zero_of_right_eq_zero h)))

end

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.weakCurl_pair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


/-!
# `weakCurl_pair`

See the module docstring of `Defs.lean` for the role of this lemma in the pressure reconstruction:
it is the statement that `∂_t curl u = curl ∂_t u` **weakly**, i.e. that the pairings of `∂_t u` and
of `u × ω` against a curl `A` agree.

## Route

* `BSSwirl.integral_vorticity_eq` (the curl is self-adjoint on `ℝ³`) gives, for every `s` near `t`,
  `∫ ⟪u(·,s), curl A⟫ = ∫ ⟪curl u(·,s), A⟫ = ∫ ⟪ω(·,s), A⟫`;
* differentiating in `s` at `t` (`tendsto_integral_slope_self`) gives
  `∫ ⟪∂_t u(·,t), curl A⟫ = ∫ ⟪∂_t ω(·,t), A⟫`;
* the pointwise vorticity equation (`hvort`, valid a.e.) rewrites the right-hand side as
  `X := ∫ ⟪(ω·∇)u, A⟫ - ∫ ⟪(u·∇)ω, A⟫`;
* `vorticity_cross_eq` gives `curl (u × ω) = (div ω) • u + (ω·∇)u - (u·∇)ω` (using `div u = 0`), so
  `∫ ⟪curl (u×ω), A⟫ = T1 + X` with `T1 := ∫ div ω · ⟪u,A⟫`;
* the pointwise Weyl identity `BSSwirl.inner_vorticity_sub_eq_div` turns
  `∫ ⟪curl (u × ω), A⟫` into `∫ ⟪u × ω, curl A⟫ + ∫ div((u×ω) × A)`, and the last integral
  vanishes (it is `∫ div(ω⟪u,A⟫) - ∫ div(u⟪ω,A⟫) = 0`, the first term by the off-plane integration
  by parts `OffPlanes.offPlanes_ibp` together with `CurlGrad.vorticity_gradient_integral_eq_zero`,
  the second by `div u = 0`);
* finally `T1 = 0`, again by the off-plane integration by parts and
  `CurlGrad.vorticity_gradient_integral_eq_zero`.

Hence `∫ ⟪u × ω, curl A⟫ = T1 + X = X = ∫ ⟪∂_t u, curl A⟫`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

open MeasureTheory Filter Set Topology
open FiniteTimeSingularity

namespace Work.FTS.PressureOn

/-! ## Nullity of the complement of `Uax` -/

/-- **Every coordinate hyperplane of `ℝ³` is Lebesgue-null.** -/
lemma volume_coord_eq_zero_R3 (i : Fin 3) (c : ℝ) :
    volume {x : R3 | x i = c} = 0 := by
  have hmap : Measure.map (WithLp.toLp 2 : (Fin 3 → ℝ) → R3) volume = volume :=
    (PiLp.volume_preserving_toLp (Fin 3)).map_eq
  rw [← hmap, MeasureTheory.Measure.map_apply (by fun_prop) (by measurability)]
  have h : (WithLp.toLp 2 : (Fin 3 → ℝ) → R3) ⁻¹' {x : R3 | x i = c}
      = {v : Fin 3 → ℝ | v i = c} := by
    ext v; simp
  rw [h, MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) i c

lemma volume_Uax_compl_eq_zero : volume (Uaxᶜ : Set R3) = 0 := by
  have hsub : (Uaxᶜ : Set R3) ⊆ {x : R3 | x 2 = 0} ∪ {x : R3 | x 0 = 0} := by
    intro x hx
    by_cases h1 : x 2 = 0
    · exact Or.inl h1
    · right
      have h2 : x 0 ^ 2 + x 1 ^ 2 = 0 := not_not.mp (fun hc => hx ⟨h1, hc⟩)
      have hA : x 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x 1)]
      simpa using (sq_eq_zero_iff.mp hA)
  exact measure_mono_null hsub
    (measure_union_null (volume_coord_eq_zero_R3 2 0) (volume_coord_eq_zero_R3 0 0))

lemma ae_mem_Uax : ∀ᵐ x ∂(volume : Measure R3), x ∈ Uax := by
  rw [MeasureTheory.ae_iff]
  exact volume_Uax_compl_eq_zero

/-! ## A compact-support integrability helper -/



/-! ## The main theorem -/

theorem weakCurl_pair {u ω : R3 → ℝ → R3} {t : ℝ} {A : R3 → R3}
    (hA : ∀ n : ℕ, ContDiff ℝ n A) (hAcs : HasCompactSupport A)
    (hR : ∃ R : ℝ, 0 ≤ R ∧ ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hsnbhd : ∀ s ∈ Set.Ioo (t - 1) (t + 1), ContDiff ℝ 1 (u · s))
    (hcurl : ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x,
      FiniteTimeSingularity.vorticity (fun y => u y s) x = ω x s)
    (hdivu : ∀ s ∈ Set.Ioo (t - 1) (t + 1), FiniteTimeSingularity.div (u · s) = 0)
    (hωcont : Continuous (fun x => ω x t))
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt (fun x => ω x t) (fderiv ℝ (ω · t) x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ (ω · t) x))
    (huderiv : ∀ x, HasDerivWithinAt (u x) (FiniteTimeSingularity.timeDeriv u x t) (Set.Ici t) t)
    (hωderiv : ∀ x, HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x t) (Set.Ici t) t)
    (hulip : ∃ C, ∀ x, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖u x s - u x t‖ ≤ C * |s - t|)
    (hωlip : ∃ C, ∀ x, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖ω x s - ω x t‖ ≤ C * |s - t|)
    (hvort : ∀ x ∈ Uax, FiniteTimeSingularity.timeDeriv ω x t
        + FiniteTimeSingularity.directionalDeriv ω u x t
          = FiniteTimeSingularity.directionalDeriv u ω x t) :
    ∫ x, inner ℝ (FiniteTimeSingularity.timeDeriv u x t) (FiniteTimeSingularity.vorticity A x)
      = ∫ x, inner ℝ (crossVec (u x t) (ω x t)) (FiniteTimeSingularity.vorticity A x) := by
  have hBcs : HasCompactSupport (fun x => vorticity A x) :=
    (BSSwirl.contDiff_vorticity_and_support hA hAcs).2
  have hBcont : Continuous (fun x => vorticity A x) :=
    ((BSSwirl.contDiff_vorticity_and_support hA hAcs).1 0).continuous
  -- ## Step 1: for every `s` near `t`, the two pairings agree
  have hident : ∀ s ∈ Ioo (t - 1) (t + 1),
      ∫ x, inner ℝ (u x s) (vorticity A x) = ∫ x, inner ℝ (ω x s) (A x) := by
    intro s hs
    have h := BSSwirl.integral_vorticity_eq (V := fun x => u x s) (Ψ := A) (hsnbhd s hs) hA hAcs
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [hcurl s hs x]
  -- ## Step 2: differentiate the identity in `s` at `t`
  have hucont : ∀ᶠ s in nhdsWithin t (Ioi t), Continuous (fun x => u x s) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, one_pos, ?_⟩
    rintro s ⟨hs, -⟩
    simp only [Set.mem_setOf_eq]
    rw [Metric.mem_ball, Real.dist_eq] at hs
    exact (hsnbhd s ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩).continuous
  have hwcont : ∀ᶠ s in nhdsWithin t (Ioi t), Continuous (fun x => ω x s) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, one_pos, ?_⟩
    rintro s ⟨hs, -⟩
    simp only [Set.mem_setOf_eq]
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hsI : s ∈ Ioo (t - 1) (t + 1) :=
      ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
    rw [show (fun x => ω x s) = fun x => vorticity (fun y => u y s) x from
      funext (fun x => (hcurl s hsI x).symm)]
    exact BSSwirl.continuous_vorticity (hsnbhd s hsI)
  have hlim_u := tendsto_integral_slope_self (u := u) (t := t) (w := fun x => vorticity A x)
    hBcont hBcs hucont huderiv hulip
  have hlim_w := tendsto_integral_slope_self (u := ω) (t := t) (w := A)
    (hA 0).continuous hAcs hwcont hωderiv hωlip
  -- the slope integrals are the difference quotients of the two pairings
  have hquot_u : ∀ᶠ s in nhdsWithin t (Ioi t),
      (∫ x, inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (vorticity A x))
        = ((∫ x, inner ℝ (u x s) (vorticity A x))
            - (∫ x, inner ℝ (u x t) (vorticity A x))) / (s - t) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, one_pos, ?_⟩
    rintro s ⟨hs, -⟩
    simp only [Set.mem_setOf_eq]
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hsI : s ∈ Ioo (t - 1) (t + 1) :=
      ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
    have htI : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
    have hcs : ContDiff ℝ 1 (fun x => u x s) := hsnbhd s hsI
    have hct : ContDiff ℝ 1 (fun x => u x t) := hsnbhd t htI
    have hIs : Integrable (fun x => inner ℝ (u x s) (vorticity A x)) :=
      (hcs.continuous.inner hBcont).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact hBcs (by
          intro x hx
          rw [Function.mem_support] at hx
          exact subset_tsupport _ (by
            rw [Function.mem_support]
            intro h0
            exact hx (by simp [h0]))))
    have hIt : Integrable (fun x => inner ℝ (u x t) (vorticity A x)) :=
      (hct.continuous.inner hBcont).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact hBcs (by
          intro x hx
          rw [Function.mem_support] at hx
          exact subset_tsupport _ (by
            rw [Function.mem_support]
            intro h0
            exact hx (by simp [h0]))))
    have hsub : (∫ x, inner ℝ (u x s - u x t) (vorticity A x))
        = (∫ x, inner ℝ (u x s) (vorticity A x))
          - (∫ x, inner ℝ (u x t) (vorticity A x)) := by
      rw [← integral_sub hIs hIt]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [inner_sub_left]
    have hsmul : (∫ x, inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (vorticity A x))
        = (s - t)⁻¹ * (∫ x, inner ℝ (u x s - u x t) (vorticity A x)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [real_inner_smul_left]
    rw [hsmul, hsub, div_eq_inv_mul]
  have hquot_w : ∀ᶠ s in nhdsWithin t (Ioi t),
      (∫ x, inner ℝ ((s - t)⁻¹ • (ω x s - ω x t)) (A x))
        = ((∫ x, inner ℝ (ω x s) (A x))
            - (∫ x, inner ℝ (ω x t) (A x))) / (s - t) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, one_pos, ?_⟩
    rintro s ⟨hs, -⟩
    simp only [Set.mem_setOf_eq]
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hsI : s ∈ Ioo (t - 1) (t + 1) :=
      ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
    have hcs : Continuous (fun x => ω x s) := by
      rw [show (fun x => ω x s) = fun x => vorticity (fun y => u y s) x from
        funext (fun x => (hcurl s hsI x).symm)]
      exact BSSwirl.continuous_vorticity (hsnbhd s hsI)
    have hct : Continuous (fun x => ω x t) := hωcont
    have hIs : Integrable (fun x => inner ℝ (ω x s) (A x)) :=
      (hcs.inner (hA 0).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact hAcs (by
          intro x hx
          rw [Function.mem_support] at hx
          exact subset_tsupport _ (by
            rw [Function.mem_support]
            intro h0
            exact hx (by simp [h0]))))
    have hIt : Integrable (fun x => inner ℝ (ω x t) (A x)) :=
      (hct.inner (hA 0).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact hAcs (by
          intro x hx
          rw [Function.mem_support] at hx
          exact subset_tsupport _ (by
            rw [Function.mem_support]
            intro h0
            exact hx (by simp [h0]))))
    have hsub : (∫ x, inner ℝ (ω x s - ω x t) (A x))
        = (∫ x, inner ℝ (ω x s) (A x)) - (∫ x, inner ℝ (ω x t) (A x)) := by
      rw [← integral_sub hIs hIt]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [inner_sub_left]
    have hsmul : (∫ x, inner ℝ ((s - t)⁻¹ • (ω x s - ω x t)) (A x))
        = (s - t)⁻¹ * (∫ x, inner ℝ (ω x s - ω x t) (A x)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [real_inner_smul_left]
    rw [hsmul, hsub, div_eq_inv_mul]
  have hEq : ∀ᶠ s in nhdsWithin t (Ioi t),
      (∫ x, inner ℝ (u x s) (vorticity A x)) = ∫ x, inner ℝ (ω x s) (A x) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, one_pos, ?_⟩
    rintro s ⟨hs, -⟩
    simp only [Set.mem_setOf_eq]
    rw [Metric.mem_ball, Real.dist_eq] at hs
    exact hident s ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
  have hEq_t : (∫ x, inner ℝ (u x t) (vorticity A x)) = ∫ x, inner ℝ (ω x t) (A x) :=
    hident t ⟨by linarith, by linarith⟩
  have hQeq : (fun s => ∫ x, inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (vorticity A x))
      =ᶠ[nhdsWithin t (Ioi t)]
      (fun s => ∫ x, inner ℝ ((s - t)⁻¹ • (ω x s - ω x t)) (A x)) := by
    filter_upwards [hquot_u, hquot_w, hEq] with s h1 h2 h3
    rw [h1, h2, h3, hEq_t]
  -- ## the conclusion of Step 2
  have hLHS_eq : (∫ x, inner ℝ (timeDeriv u x t) (vorticity A x))
      = ∫ x, inner ℝ (timeDeriv ω x t) (A x) :=
    tendsto_nhds_unique hlim_u (hlim_w.congr' hQeq.symm)
  -- ## Step 3: the pointwise vorticity equation
  have hLHS_eq2 : (∫ x, inner ℝ (timeDeriv ω x t) (A x))
      = ∫ x, inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
          - fderiv ℝ (fun y => ω y t) x (u x t)) (A x) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Uax] with x hx
    have h := hvort x hx
    simp only [FiniteTimeSingularity.directionalDeriv] at h
    have h' : timeDeriv ω x t
        = fderiv ℝ (fun y => u y t) x (ω x t) - fderiv ℝ (fun y => ω y t) x (u x t) := by
      rw [eq_sub_iff_add_eq]
      exact h
    rw [h']
  rw [hLHS_eq, hLHS_eq2]
  -- ## Step 4: the pointwise curl of `u × ω` and the three remaining integrals
  obtain ⟨R, hR0, hRbd⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ s ∈ Ioo (t - 1) (t + 1), ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R := hR
  have htI : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hu_t : ContDiff ℝ 1 (fun y => u y t) := hsnbhd t htI
  have hdu_t : ∀ x, HasFDerivAt (fun y => u y t) (fderiv ℝ (fun y => u y t) x) x := fun x =>
    (hu_t.differentiable_one x).hasFDerivAt
  have hωcs_t : HasCompactSupport (fun y => ω y t) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R3) R) ?_
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hRbd t htI x hx
  have hae_diff : ∀ᵐ x ∂(volume : Measure R3), x 0 ≠ 0 ∧ x 2 ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have h : {x : R3 | ¬(x 0 ≠ 0 ∧ x 2 ≠ 0)} = {x : R3 | x 0 = 0} ∪ {x : R3 | x 2 = 0} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or, not_ne_iff]
    rw [h]
    exact measure_union_null (volume_coord_eq_zero_R3 0 0) (volume_coord_eq_zero_R3 2 0)
  have hdivω_eq : ∀ x, div (fun y => ω y t) x
      = ∑ j : Fin 3, fderiv ℝ (fun y => ω y t) x (FiniteTimeSingularity.e j) j := fun x =>
    vorticityCross_div_eq_sum_diag _ _
  -- the pointwise identity for `curl (u × ω)`
  have hptcurl : ∀ᵐ x ∂(volume : Measure R3),
      inner ℝ (vorticity (fun y => crossVec (u y t) (ω y t)) x) (A x)
        = div (fun y => ω y t) x * inner ℝ (u x t) (A x)
          + inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
              - fderiv ℝ (fun y => ω y t) x (u x t)) (A x) := by
    filter_upwards [hae_diff] with x hx
    have hvc := vorticity_cross_eq (u := fun y => u y t) (ω := fun y => ω y t)
      (hdu_t x) (hωdiff x hx.1 hx.2)
    have hdiv0 : div (fun y => u y t) x = 0 := congrFun (hdivu t htI) x
    rw [hvc, hdiv0, zero_smul, sub_zero, inner_sub_left, inner_add_left, real_inner_smul_left,
      inner_sub_left]
    ring
  -- the compact set on which everything lives
  have hK : IsCompact (tsupport (fun y => ω y t)) := hωcs_t.isCompact
  have hKω : ∀ x, x ∉ tsupport (fun y => ω y t) → ω x t = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (f := fun y => ω y t) hx
  have hKfd : ∀ x, x ∉ tsupport (fun y => ω y t) →
      fderiv ℝ (fun y => ω y t) x = 0 := fun x hx =>
    fderiv_eq_zero_of_notMem_tsupport (G := fun y => ω y t) hx
  -- integrability of the two summands
  have hw : ContDiff ℝ 1 (fun p : R3 × R3 => inner ℝ p.1 p.2) :=
    isBoundedBilinearMap_inner.contDiff
  have hψh : ContDiff ℝ 1 (fun x => inner ℝ (u x t) (A x)) :=
    hw.comp (hu_t.prodMk (hA 1))
  have hψhcs : HasCompactSupport (fun x => inner ℝ (u x t) (A x)) := by
    refine hAcs.mono' ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport _ (by
      rw [Function.mem_support]
      intro hAx
      exact hx (by rw [hAx, inner_zero_right]))
  have hInt1 : Integrable (fun x => div (fun y => ω y t) x * inner ℝ (u x t) (A x)) := by
    have h := integrable_mul_div (ω := fun y => ω y t) hωint hψh hψhcs
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    exact mul_comm _ _
  have hInt2 : Integrable (fun x => inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
      - fderiv ℝ (fun y => ω y t) x (u x t)) (A x)) :=
    weakCurl.int2_integrable hA hAcs ⟨R, hR0, hRbd⟩ hsnbhd hωcont hωdiff hωint
  -- (A)
  have hA1 : (∫ x, inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
          - fderiv ℝ (fun y => ω y t) x (u x t)) (A x))
      = (∫ x, inner ℝ (vorticity (fun y => crossVec (u y t) (ω y t)) x) (A x))
        - ∫ x, div (fun y => ω y t) x * inner ℝ (u x t) (A x) := by
    have h := integral_congr_ae hptcurl
    rw [integral_add hInt1 hInt2] at h
    linarith
  -- (C): the divergence term vanishes
  have hT1 : (∫ x, div (fun y => ω y t) x * inner ℝ (u x t) (A x)) = 0 :=
    div_vorticity_mul_eq_zero hu_t (fun x => hcurl t htI x) hωcont
      ⟨R, fun x hx => hRbd t htI x hx⟩ hωdiff hωint hψh hψhcs
  -- (B): the Weyl identity
  have hB1 : (∫ x, inner ℝ (crossVec (u x t) (ω x t)) (vorticity A x))
      = ∫ x, inner ℝ (vorticity (fun y => crossVec (u y t) (ω y t)) x) (A x) :=
    weakCurl.weyl_cross hA hAcs ⟨R, hR0, hRbd⟩ hsnbhd hcurl hdivu hωcont hωdiff hωint
  rw [hB1, hA1, hT1, sub_zero]

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Rec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/IP4Rec.lean` — the recursion of the transfer defect

With `Def n b a` the transfer defect of the `n`-th pairing of the recursion at the slot `(a,b)`,
`HkIPStep` gives `Def (n+1) b a = Def n b a + c₁ Def n b (a+1) + c₂ Def n (b+1) a`; every slot
order stays below four (first argument) and five (second argument), so the level-zero bound is
uniform and the recursion multiplies the constant by `1 + |c₁| + |c₂|` at each step.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The recursion of the pairings -/

/-- The coefficient pairs of the three steps of `Assembly.IP4`. -/
def stepC (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) : ℕ → ℝ × ℝ
  | 0 => (c₁, c₂)
  | 1 => (c₁', c₂')
  | _ => (c₁'', c₂'')

@[simp] theorem stepC_zero (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    stepC c₁ c₂ c₁' c₂' c₁'' c₂'' 0 = (c₁, c₂) := rfl

@[simp] theorem stepC_one (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    stepC c₁ c₂ c₁' c₂' c₁'' c₂'' 1 = (c₁', c₂') := rfl


/-- The coercive recursion `HkIPStep`, iterated from `H1IP α` with free coefficient pairs. -/
noncomputable def QP (α : ℝ) (c : ℕ → ℝ × ℝ) : ℕ → Fn → Fn → ℝ
  | 0 => Work.Coercivity.H1IP α
  | n + 1 => Work.Coercivity.HkIPStep (c n).1 (c n).2 (QP α c n)






/-- The constant of the recursion: the product of the `1 + |c₁| + |c₂|` of the steps. -/
def KCB (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n *
      (1 + |(stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).1| + |(stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).2|)

@[simp] theorem KCB_zero (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    KCB c₁ c₂ c₁' c₂' c₁'' c₂'' 0 = 1 := rfl

@[simp] theorem KCB_succ (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (n : ℕ) :
    KCB c₁ c₂ c₁' c₂' c₁'' c₂'' (n + 1) = KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n *
      (1 + |(stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).1|
        + |(stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).2|) := rfl



/-- The transfer defect of the level-`n` pairing at the slot `(a,b)`. -/
noncomputable def Def (α : ℝ) (c : ℕ → ℝ × ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f h : Fn)
    (n b a : ℕ) : ℝ :=
  QP α c n (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a f)) (Work.Spaces.mixed b a h)
    - QP α c n (Work.Spaces.mixed b a f)
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a h))



end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.HkMem_E1_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two inputs of the frozen assembly, in the open class -/

/-- **Block continuity of `E1 α f` on the open class.**  `E1 α f = B(θ)·R(z)` is a separated
product with `B = sin 2θ·Γ'(θ)` of class `C³` on `(0,π/2)` and `R = radA α f` of class `C⁴`
(hence `C³`) on `(0,∞)`; `BlocksCont_mul_factor` gives the blocks of order `≤ 3`, and
`blocksCont_mono` the order `≤ n ≤ 3`. -/
theorem E1_blocks_open_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3) {f : Fn}
    (hf : CoerAdmO α f) :
    Work.FTS.CoercivityFix.Assembly.BlocksCont n (Work.FTS.CoercivityFix.Transfer.E1 α f) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.1.2.1
  have hR : ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) :=
    ((Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four hα hα1 hsm hmem5).1).of_le
      (by norm_num)
  have hb : ContDiffOn ℝ 3
      (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      (Set.Ioo 0 (π / 2)) :=
    Work.FTS.CoercivityFix.Transfer.sinGam_contDiffOn_Ioo α
  have h3 : Work.FTS.CoercivityFix.Assembly.BlocksCont 3
      (fun z θ : ℝ => (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
        * Work.FTS.CoercivityFix.Transfer.radA α f z) :=
    Work.FTS.CoercivityFix.Transfer.BlocksCont_mul_factor _ _ hb hR
  exact Work.FTS.CoercivityFix.Transfer.blocksCont_mono hn h3

/-- **The level-three radial slot sum of `radA α f` is integrable** on `Iz` for the open class:
`EpsE4Thr.radA_slotSum_le` at `n = 3`. -/
private theorem radA_slot_sum_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : CoerAdmO α f) :
    IntegrableOn (fun z : ℝ => ∑ c ∈ Finset.range 4,
      (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
  (Work.FTS.StrongEps.EpsE4Thr.radA_slotSum_le.choose_spec.2 α hα hα1 f hf 3 (by norm_num)).1

/-- **A single radial slot is integrable, given the integrability of the slot sum.**  The
summand `(D_z^j A)²w²` is nonnegative and bounded by the (integrable) sum; its a.e. strong
measurability on `Iz` comes from its continuity on `(0,∞)`, i.e. from the continuity of the
`Zop`-iterate `Zop^[j] A = D_z^j A` (`DzdIter_eq_Zop_iter`) and of the weight `w`, the endpoint
`z = 0` being a null set. -/
private theorem integrableOn_slot_of_sum {A : ℝ → ℝ}
    (hA : ContDiffOn ℝ 4 A (Set.Ioi (0 : ℝ)))
    (hsum : IntegrableOn (fun z : ℝ => ∑ c ∈ Finset.range 4,
      (Work.Elliptic.DzdIter c A z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz)
    {j : ℕ} (hj : j ≤ 3) :
    IntegrableOn (fun z : ℝ => (Work.Elliptic.DzdIter j A z) ^ 2
      * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  refine MeasureTheory.Integrable.mono' hsum ?_ ?_
  · -- continuity on `(0,∞)`, hence a.e. strong measurability on `Iz = [0,∞)`
    have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
      have hEq : (fun z : ℝ => Work.Spaces.w z) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
      rw [hEq]
      exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
    have hZ : ContinuousOn (Work.Spaces.Zop^[j] A) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.continuousOn_Zop_iter_of_contDiffOn
        (b := j) (n := 0) (by
          have h4 : ((j : ℕ) : WithTop ℕ∞) ≤ 4 := by
            exact_mod_cast (show j ≤ 4 by omega)
          simpa using hA.of_le h4)
    have hfun : (fun z : ℝ => (Work.Elliptic.DzdIter j A z) ^ 2 * (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => (Work.Spaces.Zop^[j] A z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
      funext z
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
    rw [hfun, Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
    exact ((hZ.pow 2).mul (hw.pow 2)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards with z
    have hnn : 0 ≤ (Work.Elliptic.DzdIter j A z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    exact Finset.single_le_sum
      (f := fun c => (Work.Elliptic.DzdIter c A z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun c _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Finset.mem_range.mpr (by omega))

/-! ## The target -/

/-- **`E1 α f ∈ ℋⁿ` for `f` in the open coercivity class.**  This is the `SmoothOpen`-twin of
`E1Parts.HkMem_E1_of`: the angular majorant `Γ²sin(2θ)^{-η} + Γ²sin(2θ)^{-γ}` (`AngGam`) is
integrable and the radial majorant is the level-three slot sum of `radA α f`, whose
integrability is `radA_slotSum_le` (open class); the individual slots are extracted from that
sum by `integrableOn_slot_of_sum`. -/
theorem HkMem_E1_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f) (n : ℕ) (hn : n ≤ 3) :
    Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Transfer.E1 α f) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.1.2.1
  have hrad4 : ContDiffOn ℝ 4 (Work.FTS.CoercivityFix.Transfer.radA α f)
      (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four hα hα1 hsm hmem5).1
  have hblocks := E1_blocks_open_O α hα hα1 n hn hf
  have hsum := radA_slot_sum_integrable hα hα1 hf
  exact Work.FTS.CoercivityFix.Transfer.E1Parts.HkMem_E1_of α hα hα1 n hn hblocks
    (fun j hj => integrableOn_slot_of_sum hrad4 hsum hj)

end Work.FTS.StrongEps.EpsE4Thr.TransO
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfileFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.EpsRLX.ProfileFacts`

**The profile facts of one admissible datum of the projected `ε`-scheme.**

Given the datum `ProfileData α C₀ B ε ρ u` (open-quadrant smoothness of `u`, honest `ℋ⁶`-membership
with size `≤ B`, and `ClassC` plus the small-ball bound `Xn ≤ C₀α²` for the projected-mollified
profile `Wp ρ ε u = Pz (Jeps ρ ε u)`), the datum and its projected-mollified profile satisfy the
eight boundedness facts needed downstream, with one constant `C` — independent of `α ∈ (0,1]`,
of `ε ∈ (0,1]`, of `C₀`, `B`, `u` and of the kernel `ρ` (it only depends on `ρ` through the two
constants of `EpsMemOfClassCJeps` and `HkSq_JepsPz_le`).

The four ingredients are, in order of appearance,

* `EpsLocalPStar.EpsMemOfClassCJeps` — the datum itself is in the weighted space `X`, with the
  sharp `1/(γ-1)²`-degradation (`γ = 1 + α/10`), using the vanishing of the endpoint traces forced
  by `ClassC α (Pz (Jeps ρ ε u))` (conjuncts 1, 2);
* `EpsSqTools.HkSq_JepsPz_le` at `k = 6` — the mollified-projected profile is in `ℋ⁶`, at the cost
  of one factor `C/ε` per derivative (conjunct 3);
* `EpsSqTools.EpsSq_le_HkSq_ClassC` — the `X`-norm of a class element is bounded by its `ℋ⁴`-norm
  times `C/(γ-1)⁸`, and `ℋ⁴ ≤ ℋ⁶` (conjuncts 4, 5);
* the class fields `tr`, `mem` (conjuncts 6, 7), and the mixed slots (conjunct 8), which are the
  `KMath` content of this file's siblings:
  * for `1 ≤ a`, `EpsSq α (mixed b a Wp) ≤ HkSq α 6 Wp` because `(mixed b a Wp · W)²` is literally
    one summand of `HkIntegrand α 6 Wp` (`EpsRLX.ProfileMixedSlot.EpsSq_mixed_le_HkSq`);
  * for `a = 0` (so `mixed b 0 Wp = D_z^b Wp`, `b ≤ 4`), the weighted angular Hardy inequality
    (`EpsLocalPStar.EpsSliceLe`, constant `1/(γ-1)²`) applied to the `θ`-slice of `D_z^b Wp` turns
    `sin^{-γ}(D_z^b Wp)²` into the `(b,1)`-slot `(mixed b 1 Wp · W)²` of `ℋ⁶`
    (`EpsRLX.ProfileDzSlot.EpsSq_dzIter_le_HkSq`); the traces required by the Hardy inequality are
    exactly the `(a,b) = (0,b)` clause of the class's `BdryTraces α 6 Wp`.

Since `(γ-1)² ≥ (γ-1)⁸` for `γ - 1 = α/10 ≤ 1/10`, all the exponents `2` above are absorbed into
the exponent `8`, and since `1 ≤ C/(γ-1)⁸` the slot bounds may be inflated freely.
-/

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

theorem ProfileFacts (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ ε ∈ Set.Ioc 0 1, ∀ {C₀ B : ℝ}, ∀ {u : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.EpsRLX.ProfileData α C₀ B ε ρ u →
      Work.FTS.StrongEps.EpsMem α u ∧
      Work.FTS.StrongEps.EpsSq α u ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 u ∧
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
        ≤ C * (C / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α u ∧
      Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ∧
      Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
        ≤ C / (Work.Spaces.gam α - 1) ^ 8
            * Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ∧
      Work.FTS.Nonlin.BdryTraces α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ∧
      Work.Spaces.HkMem α 7 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ∧
      (∀ b a : ℕ, a + b ≤ 4 →
        Work.FTS.StrongEps.EpsMem α (Work.Spaces.mixed b a (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)) ∧
        Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed b a (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))
          ≤ C / (Work.Spaces.gam α - 1) ^ 8
              * Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps ρ hρ
  obtain ⟨C₃, hC₃pos, hC₃⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  obtain ⟨C₅, hC₅pos, hC₅⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC
  obtain ⟨C₈, hC₈pos, hC₈⟩ := Work.FTS.StrongEps.EpsRLX.ProfileDzSlot.EpsSq_dzIter_le_HkSq
  refine ⟨max 1 (C₁ + C₃ + C₅ + C₈), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α hα ε hε C₀ B u hd
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  set C : ℝ := max 1 (C₁ + C₃ + C₅ + C₈) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hCnn : 0 ≤ C := hCpos.le
  have hs : C₁ + C₃ + C₅ + C₈ ≤ C := le_max_right _ _
  have hC₁le : C₁ ≤ C := by linarith [hs, hC₃pos, hC₅pos, hC₈pos]
  have hC₃le : C₃ ≤ C := by linarith [hs, hC₁pos, hC₅pos, hC₈pos]
  have hC₅le : C₅ ≤ C := by linarith [hs, hC₁pos, hC₃pos, hC₈pos]
  have hC₈le : C₈ ≤ C := by linarith [hs, hC₁pos, hC₃pos, hC₅pos]
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα0
    linarith
  have hγle : Work.Spaces.gam α - 1 ≤ 1 := by rw [Work.Spaces.gam]; linarith
  -- (1) and (2): the datum `u` itself
  obtain ⟨hmem_u, hsq_u⟩ := hC₁ α hα ε hε0 hε1 u hd.smo hd.hkmem hd.cls
  have hB : Work.FTS.StrongEps.EpsSq α u
      ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 u := by
    have hcoef : C₁ / (Work.Spaces.gam α - 1) ^ 2 ≤ C / (Work.Spaces.gam α - 1) ^ 2 :=
      div_le_div_of_nonneg_right hC₁le (pow_pos hγpos 2).le
    exact le_trans hsq_u (mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 1 u))
  -- (3): the `ℋ⁶`-size of the projected-mollified profile
  have h3 : Work.Spaces.HkSq α 6 (Wp ρ ε u)
      ≤ C * (C / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α u := by
    have h := hC₃ α hα ε hε0 hε1 6 (by norm_num) u hd.smo hmem_u
    have hE : 0 ≤ Work.FTS.StrongEps.EpsSq α u := Work.FTS.StrongEps.EpsSq_nonneg α u
    have hbase : C₃ / ε ≤ C / ε := div_le_div_of_nonneg_right hC₃le hε0.le
    have hpow : (C₃ / ε) ^ 12 ≤ (C / ε) ^ 12 :=
      pow_le_pow_left₀ (div_nonneg hC₃pos.le hε0.le) hbase 12
    have hCY : C₃ * (C₃ / ε) ^ 12 ≤ C * (C / ε) ^ 12 :=
      mul_le_mul hC₃le hpow (pow_nonneg (div_nonneg hC₃pos.le hε0.le) 12) hCnn
    refine le_trans h ?_
    simpa only [show 2 * 6 = 12 by norm_num] using mul_le_mul_of_nonneg_right hCY hE
  -- (4) and (5): the projected-mollified profile
  obtain ⟨hmem_W, hsq_W⟩ := hC₅ α hα (Wp ρ ε u) hd.cls
  have hmem6W : Work.Spaces.HkMem α 6 (Wp ρ ε u) :=
    Work.FTS.OpenPkg.HkMem_mono_open hd.cls.reg 6 (by norm_num) hd.cls.mem8
  have hE5 : Work.FTS.StrongEps.EpsSq α (Wp ρ ε u)
      ≤ C / (Work.Spaces.gam α - 1) ^ 8 * Work.Spaces.HkSq α 6 (Wp ρ ε u) := by
    have hmono : Work.Spaces.HkSq α 4 (Wp ρ ε u) ≤ Work.Spaces.HkSq α 6 (Wp ρ ε u) :=
      Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem6W
    have hcoef : C₅ / (Work.Spaces.gam α - 1) ^ 8 ≤ C / (Work.Spaces.gam α - 1) ^ 8 :=
      div_le_div_of_nonneg_right hC₅le (pow_pos hγpos 8).le
    exact le_trans hsq_W
      (mul_le_mul hcoef hmono (Work.Spaces.HkSq_nonneg α 4 (Wp ρ ε u))
        (div_nonneg hCnn (pow_pos hγpos 8).le))
  -- (8): the mixed slots of the projected-mollified profile
  have h8 : ∀ b a : ℕ, a + b ≤ 4 →
      Work.FTS.StrongEps.EpsMem α (Work.Spaces.mixed b a (Wp ρ ε u)) ∧
      Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed b a (Wp ρ ε u))
        ≤ C / (Work.Spaces.gam α - 1) ^ 8 * Work.Spaces.HkSq α 6 (Wp ρ ε u) := by
    intro b a hab
    have hbig : (1 : ℝ) ≤ C / (Work.Spaces.gam α - 1) ^ 8 := by
      have hx : (Work.Spaces.gam α - 1) ^ 8 ≤ 1 := pow_le_one₀ hγpos.le hγle
      have hinv : (1 : ℝ) ≤ ((Work.Spaces.gam α - 1) ^ 8)⁻¹ :=
        (one_le_inv₀ (pow_pos hγpos 8)).mpr hx
      rw [div_eq_mul_inv]
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ C * ((Work.Spaces.gam α - 1) ^ 8)⁻¹ := mul_le_mul hC1 hinv zero_le_one hCnn
    by_cases ha : a = 0
    · subst ha
      obtain ⟨hmem8, hsq8⟩ := hC₈ α hα (f := Wp ρ ε u) hd.cls.reg hmem6W hd.cls.tr b (by omega)
      have hcoef : C₈ / (Work.Spaces.gam α - 1) ^ 2 ≤ C / (Work.Spaces.gam α - 1) ^ 8 :=
        div_le_div₀ hCnn hC₈le (pow_pos hγpos 8)
          (pow_le_pow_of_le_one hγpos.le hγle (by norm_num))
      refine ⟨?_, ?_⟩
      · simpa only [Work.Spaces.mixed_zero_right] using hmem8
      · calc Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed b 0 (Wp ρ ε u))
            = Work.FTS.StrongEps.EpsSq α (Work.Spaces.DzIter b (Wp ρ ε u)) := by
              rw [Work.Spaces.mixed_zero_right]
          _ ≤ C₈ / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 6 (Wp ρ ε u) := hsq8
          _ ≤ C / (Work.Spaces.gam α - 1) ^ 8 * Work.Spaces.HkSq α 6 (Wp ρ ε u) :=
              mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 6 (Wp ρ ε u))
    · have ha1 : 1 ≤ a := by omega
      obtain ⟨hmemM, hsqM⟩ :=
        Work.FTS.StrongEps.EpsRLX.ProfileMixedSlot.EpsSq_mixed_le_HkSq hd.cls.reg hmem6W
          (j := b) (i := a) ha1 (by omega)
      exact ⟨hmemM, le_trans hsqM (by
        calc Work.Spaces.HkSq α 6 (Wp ρ ε u)
            = 1 * Work.Spaces.HkSq α 6 (Wp ρ ε u) := by ring
          _ ≤ C / (Work.Spaces.gam α - 1) ^ 8 * Work.Spaces.HkSq α 6 (Wp ρ ε u) :=
              mul_le_mul_of_nonneg_right hbig (Work.Spaces.HkSq_nonneg α 6 (Wp ρ ε u)))⟩
  exact ⟨hmem_u, hB, h3, hmem_W, hE5, hd.cls.tr, hd.cls.mem, h8⟩

end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.TendstoPhiOddPi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

open Filter Set
open scoped Topology

/-!
# The boundary value `Φ̂/cos` at `θ = π/2`

Near `θ = π/2` the stream function `Φ` vanishes (`Φ w (π/2) τ = 0`), so the quotient
`Φ̂(w,θ,τ)/cos θ` has a finite limit there, namely `-∂_θ Φ(w₀,π/2,τ)`: indeed, writing
`θ = π/2 - δ` with `δ → 0⁺`, `cos θ = sin δ` and `Φ(w,θ) = -δ ∂_θΦ(w,π/2) + o(δ)`.

The proof is the product rule for limits applied to the two factors
`Φ(w,θ)/(θ - π/2) → ∂_θΦ(w₀,π/2)` (the slice difference quotient, `tendsto_slice_quotient`)
and `(θ - π/2)/cos θ → 1/∂_θ(cos)(π/2) = -1`, combined with `Φ̂ = Φ` on the sector
`{p.2 > 0}`.
-/

/-- Near `(w₀, π/2)`, the sector `{0 < p.1 ∧ 0 < p.2 ∧ p.2 < π/2}` is contained in the box
`{|p.1 - w₀| < δ} ∩ {|p.2 - π/2| < δ}` (and there `p.2 ≠ π/2`).  This is the filter transfer
that lets the slice-quotient lemmas be applied on the sector. -/
private lemma sector_le_box (w₀ δ : ℝ) (hδ : 0 < δ) :
    𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2) ≤
      𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - Real.pi / 2| < δ ∧ p.2 ≠ Real.pi / 2}]
        (w₀, Real.pi / 2) := by
  set T : Set (ℝ × ℝ) := {p | |p.1 - w₀| < δ ∧ |p.2 - Real.pi / 2| < δ} with hT
  have hTmem : T ∈ 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}]
      (w₀, Real.pi / 2) :=
    nhdsWithin_le_nhds (Filter.mem_of_superset (Metric.ball_mem_nhds (w₀, Real.pi / 2) hδ)
      (by
        intro p hp
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hp
        exact hp))
  calc 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2)
      = 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2} ∩ T] (w₀, Real.pi / 2) :=
        (nhdsWithin_inter_of_mem' hTmem).symm
    _ ≤ 𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - Real.pi / 2| < δ ∧ p.2 ≠ Real.pi / 2}]
          (w₀, Real.pi / 2) :=
        nhdsWithin_mono _ fun p hp => ⟨hp.2.1, hp.2.2, ne_of_lt hp.1.2.2⟩

theorem tendsto_PhiOdd_div_cos_at_pi_div_two {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0)
    {w₀ : ℝ} (hw₀ : 0 < w₀) :
    Filter.Tendsto (fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (-(deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2)))) := by
  -- a positive radius, small enough that the box stays in `w > -1` and in `w > 0`
  obtain ⟨δ, hδpos, hδ1, hδw⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ w₀ :=
    ⟨min 1 w₀, lt_min one_pos hw₀, min_le_left _ _, min_le_right _ _⟩
  -- the `C²` hypothesis and the vanishing, on the box of half-width `δ`
  have hsm' : ∀ w θ : ℝ, |w - w₀| < δ → |θ - Real.pi / 2| < δ →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ) := by
    intro w θ hw hθ
    rw [abs_lt] at hw hθ
    exact hsm w θ (by linarith [hw.1, hδw])
      (by linarith [hθ.1, hδ1, Real.pi_pos]) (by linarith [hθ.2, hδ1])
  have hz' : ∀ w : ℝ, |w - w₀| < δ → Φ w (Real.pi / 2) τ = 0 := by
    intro w hw
    rw [abs_lt] at hw
    exact hπ w (by linarith [hw.1, hδw])
  -- (1) the `θ`-difference quotient of `Φ` tends to `∂_θΦ (w₀, π/2)`
  have hslope : Filter.Tendsto (fun p : ℝ × ℝ => Φ p.1 p.2 τ / (p.2 - Real.pi / 2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2))) :=
    (tendsto_slice_quotient (f := fun w θ : ℝ => Φ w θ τ) (w₀ := w₀) (θ₀ := Real.pi / 2)
      (δ := δ) hδpos hsm' hz').mono_left (sector_le_box w₀ δ hδpos)
  -- (2) the quotient `(θ - π/2) / cos θ` tends to `-1`
  have hcosq : Filter.Tendsto (fun p : ℝ × ℝ => (p.2 - Real.pi / 2) / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (-1)) := by
    have hsmc : ∀ w θ : ℝ, |w - w₀| < Real.pi / 2 + 1 → |θ - Real.pi / 2| < Real.pi / 2 + 1 →
        ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.cos p.2) (w, θ) :=
      fun _ _ _ _ => ContDiffAt.cos contDiffAt_snd
    have hzc : ∀ w : ℝ, |w - w₀| < Real.pi / 2 + 1 → Real.cos (Real.pi / 2) = 0 :=
      fun _ _ => Real.cos_pi_div_two
    have h1 : Filter.Tendsto (fun p : ℝ × ℝ => Real.cos p.2 / (p.2 - Real.pi / 2))
        (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
        (𝓝 (-1)) := by
      have h0 := (tendsto_slice_quotient (f := fun _ θ : ℝ => Real.cos θ) (w₀ := w₀)
        (θ₀ := Real.pi / 2) (δ := Real.pi / 2 + 1) (by linarith [Real.pi_pos]) hsmc
        hzc).mono_left (sector_le_box w₀ (Real.pi / 2 + 1) (by linarith [Real.pi_pos]))
      simpa [Real.deriv_cos, Real.sin_pi_div_two] using h0
    have h2 : Filter.Tendsto (fun p : ℝ × ℝ => (Real.cos p.2 / (p.2 - Real.pi / 2))⁻¹)
        (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
        (𝓝 (-1)) := by
      have h0 := h1.inv₀ (by norm_num : (-1 : ℝ) ≠ 0)
      simpa using h0
    exact h2.congr' (Eventually.of_forall fun p => inv_div _ _)
  -- (3) the product is the quotient of the statement
  have hprod : Filter.Tendsto
      (fun p : ℝ × ℝ =>
        (Φ p.1 p.2 τ / (p.2 - Real.pi / 2)) * ((p.2 - Real.pi / 2) / Real.cos p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2) * (-1))) :=
    hslope.mul hcosq
  have key : Filter.Tendsto
      (fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2) * (-1))) :=
    hprod.congr' (by
      filter_upwards [self_mem_nhdsWithin] with p hp
      rw [Work.FTS.BSIdent.PhiOdd_of_nonneg (Φ := Φ) (z := p.1) (θ := p.2) (τ := τ)
        (le_of_lt hp.2.1)]
      have h1 : p.2 - Real.pi / 2 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hp.2.2)
      have h2 : Real.cos p.2 ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hp.2.2⟩)
      have h3 : p.2 * 2 - Real.pi ≠ 0 := fun hcon => h1 (by linarith)
      field_simp)
  simpa [mul_neg, mul_one] using key

end Work.FTS.BSIdentP.Levels
end
