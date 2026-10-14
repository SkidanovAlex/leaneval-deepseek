import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_val
import Submission.Work.FTS.StrongEps.EpsSlotLipP
import Submission.Work.FTS.StrongEps.EpsSqTools.Shift
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EpsEngine.abs_mixed_Jeps_le_sup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `abs_mixed_Jeps_le_sup`

The mixed-slot sup bound for the mollified profile: for a compact `K` inside the open quadrant
`Q0 = (0,∞) × (0,π/2)` there is a compact `K' ⊆ Q0` containing `K` such that every mixed slot
`D_z^j D_θ^i (J_ε F)` on `K` is bounded by a constant (depending on `ρ`, `ε`, `j`, `i` only)
times the sup of `F` on `K'`.

The mathematics is entirely contained in the already-proved value bound
`Work.FTS.StrongEps.abs_mixed_Jeps_le_val`: every derivative falling on the mollified profile
`J_ε F` can be *routed onto the mollifier kernel* (by
`mixed_Jeps_kernel_partial` at `j' = i' = 0`), and the routed kernel `Kd (Jker ρ ε) j i` is
supported in the ball of radius `ε`, so only the values of `F` at the shifted points
`(z e^{-p₁}, arctan(tan θ · e^{-p₂}))`, `|p_k| ≤ ε`, enter — with the kernel's `L¹`-mass
`Kmass ρ ε j i` as the constant.

The only geometric work here is the construction of `K'`: exactly as in
`Work.FTS.StrongEps.Jeps_absCompactBound`, compactness of `K ⊆ Q0` supplies a box
`[z₀,z₁] × [θ₀,θ₁]` with `z₀ > 0` and `0 < θ₀ ≤ θ₁ < π/2`, and the enlarged box
`[z₀e^{-ε}, z₁e^{ε}] × [arctan(tan θ₀ · e^{-ε}), arctan(tan θ₁ · e^{ε})]`
is compact, still inside `Q0` (because `arctan < π/2`), contains `K`, and contains every shifted
point.
-/

namespace Work.FTS.EpsEngine

open scoped Real Topology
open Set

noncomputable section

theorem abs_mixed_Jeps_le_sup {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (j i : ℕ) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Work.FTS.Galerkin.Fn),
          Work.FTS.EllipticEst.SmoothOpen F → ∀ (B : ℝ), 0 ≤ B →
            (∀ p ∈ K', |F p.1 p.2| ≤ B) → ∀ p ∈ K,
              |Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε F) p.1 p.2| ≤ C * B := by
  intro K hK hKQ
  rcases Set.eq_empty_or_nonempty K with hE | hne
  · subst hE
    exact ⟨∅, isCompact_empty, empty_subset _, empty_subset _,
      (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i,
      mul_nonneg (by positivity) (Work.FTS.StrongEps.Kmass_nonneg ρ ε j i),
      fun F _ B _ _ p hp => absurd hp (by simp)⟩
  · -- the coordinate bounds of `K` and of the four tangents
    obtain ⟨pz0, hpz0K, hz0min⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨pz1, hpz1K, hz1max⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
    obtain ⟨pt0, hpt0K, ht0min⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
    obtain ⟨pt1, hpt1K, ht1max⟩ := hK.exists_isMaxOn hne continuous_snd.continuousOn
    have hz0Q := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hpz0K)
    have hz1Q := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hpz1K)
    have ht0Q := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hpt0K)
    have ht1Q := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hpt1K)
    have hz_le : ∀ p ∈ K, pz0.1 ≤ p.1 := fun p hp => hz0min hp
    have hz_ge : ∀ p ∈ K, p.1 ≤ pz1.1 := fun p hp => hz1max hp
    have ht_le : ∀ p ∈ K, pt0.2 ≤ p.2 := fun p hp => ht0min hp
    have ht_ge : ∀ p ∈ K, p.2 ≤ pt1.2 := fun p hp => ht1max hp
    have htan0pos : 0 < Real.tan pt0.2 :=
      Real.tan_pos_of_pos_of_lt_pi_div_two ht0Q.2.1 ht0Q.2.2
    have htan1pos : 0 < Real.tan pt1.2 :=
      Real.tan_pos_of_pos_of_lt_pi_div_two ht1Q.2.1 ht1Q.2.2
    have hmem0 : pt0.2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
      ⟨by linarith [ht0Q.2.1, Real.pi_pos], ht0Q.2.2⟩
    have hmem1 : pt1.2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
      ⟨by linarith [ht1Q.2.1, Real.pi_pos], ht1Q.2.2⟩
    have hexp1 : Real.exp (-ε) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (show -ε ≤ 0 by linarith)
      rwa [Real.exp_zero] at h
    have hexp2 : 1 ≤ Real.exp ε := Real.one_le_exp hε.le
    -- the enlarged box
    set a : ℝ := pz0.1 * Real.exp (-ε) with ha
    set b : ℝ := pz1.1 * Real.exp ε with hb
    set c : ℝ := Real.arctan (Real.tan pt0.2 * Real.exp (-ε)) with hc
    set d : ℝ := Real.arctan (Real.tan pt1.2 * Real.exp ε) with hd
    have hapos : 0 < a := by rw [ha]; exact mul_pos hz0Q.1 (Real.exp_pos _)
    have hcpos : 0 < c := by
      rw [hc]; exact Real.arctan_pos.mpr (mul_pos htan0pos (Real.exp_pos _))
    have hdpi : d < π / 2 := by rw [hd]; exact Real.arctan_lt_pi_div_two _
    refine ⟨Set.Icc a b ×ˢ Set.Icc c d, isCompact_Icc.prod isCompact_Icc, ?_, ?_,
      (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i,
      mul_nonneg (by positivity) (Work.FTS.StrongEps.Kmass_nonneg ρ ε j i), ?_⟩
    · -- the box lies in the open quadrant
      rintro ⟨z, θ⟩ hy
      exact Work.FTS.EllipticEst.mem_Q0.mpr
        ⟨lt_of_lt_of_le hapos hy.1.1, lt_of_lt_of_le hcpos hy.2.1, lt_of_le_of_lt hy.2.2 hdpi⟩
    · -- `K` is contained in the box
      rintro ⟨z, θ⟩ hp
      have hpQ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
      have hθmem : θ ∈ Set.Ioo (-(π / 2)) (π / 2) :=
        ⟨by linarith [hpQ.2.1, Real.pi_pos], hpQ.2.2⟩
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · exact le_trans (mul_le_of_le_one_right hz0Q.1.le hexp1) (hz_le (z, θ) hp)
      · exact le_trans (hz_ge (z, θ) hp) (le_mul_of_one_le_right hz1Q.1.le hexp2)
      · calc c = Real.arctan (Real.tan pt0.2 * Real.exp (-ε)) := hc
          _ ≤ Real.arctan (Real.tan θ) := Real.arctan_strictMono.monotone
              (le_trans (mul_le_of_le_one_right htan0pos.le hexp1)
                (Real.strictMonoOn_tan.monotoneOn hmem0 hθmem (ht_le (z, θ) hp)))
          _ = θ := Real.arctan_tan (by linarith [Real.pi_pos]) hpQ.2.2
      · calc θ = Real.arctan (Real.tan θ) :=
              (Real.arctan_tan (by linarith [Real.pi_pos]) hpQ.2.2).symm
          _ ≤ Real.arctan (Real.tan pt1.2 * Real.exp ε) := Real.arctan_strictMono.monotone
              (le_trans (Real.strictMonoOn_tan.monotoneOn hθmem hmem1 (ht_ge (z, θ) hp))
                (le_mul_of_one_le_right htan1pos.le hexp2))
          _ = d := hd.symm
    · -- the bound: route every derivative onto the mollifier kernel and read off the values
      intro F hFsm B hB hFB
      rintro ⟨z, θ⟩ hp
      have hpQ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
      have hθmem : θ ∈ Set.Ioo (-(π / 2)) (π / 2) :=
        ⟨by linarith [hpQ.2.1, Real.pi_pos], hpQ.2.2⟩
      have htanθpos : 0 < Real.tan θ :=
        Real.tan_pos_of_pos_of_lt_pi_div_two hpQ.2.1 hpQ.2.2
      have ht0le : Real.tan pt0.2 ≤ Real.tan θ :=
        Real.strictMonoOn_tan.monotoneOn hmem0 hθmem (ht_le (z, θ) hp)
      have htθ1 : Real.tan θ ≤ Real.tan pt1.2 :=
        Real.strictMonoOn_tan.monotoneOn hθmem hmem1 (ht_ge (z, θ) hp)
      have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Work.FTS.StrongEps.Quad :=
        fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hFsm n
      -- the value bound of `F` transfers to the shifted points inside the kernel's ball
      have hval : ∀ q : ℝ × ℝ, |q.1| ≤ ε → |q.2| ≤ ε →
          |F (Work.FTS.StrongEps.zShift z q.1) (Work.FTS.StrongEps.thShift θ q.2)| ≤ B := by
        intro q hq1 hq2
        have hq1a : -ε ≤ q.1 := (abs_le.mp hq1).1
        have hq1b : q.1 ≤ ε := (abs_le.mp hq1).2
        have hq2a : -ε ≤ q.2 := (abs_le.mp hq2).1
        have hq2b : q.2 ≤ ε := (abs_le.mp hq2).2
        refine hFB (Work.FTS.StrongEps.zShift z q.1, Work.FTS.StrongEps.thShift θ q.2)
          ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · -- `a ≤ z e^{-q₁}`
          rw [ha]
          exact mul_le_mul (hz_le (z, θ) hp) (Real.exp_le_exp.mpr (by linarith))
            (Real.exp_pos _).le hpQ.1.le
        · -- `z e^{-q₁} ≤ b`
          rw [hb]
          exact mul_le_mul (hz_ge (z, θ) hp) (Real.exp_le_exp.mpr (by linarith))
            (Real.exp_pos _).le (le_of_lt hz1Q.1)
        · -- `c ≤ arctan (tan θ e^{-q₂})`
          rw [hc]
          exact Real.arctan_strictMono.monotone
            (mul_le_mul ht0le (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
              htanθpos.le)
        · -- `arctan (tan θ e^{-q₂}) ≤ d`
          rw [hd]
          exact Real.arctan_strictMono.monotone
            (mul_le_mul htθ1 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
              htan1pos.le)
      exact Work.FTS.StrongEps.abs_mixed_Jeps_le_val (ρ := ρ) hρ hε hsm hpQ.1
        ⟨hpQ.2.1, hpQ.2.2⟩ hval j i

end

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.PhiStar.RouteB.psiSeries_sub_eqOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

set_option autoImplicit false

namespace Work.FTS.PhiStar.RouteB

/-! ## Locality and additivity of the mode coefficients

The mode coefficient `cmode m F z` is the `e_m`-coefficient of the slice `F z ·` in the weight
`cos θ dθ`, hence is *linear* in the source (this is `DiffGreen.cmode_sub`), and the radial
Green function `radGreen` only sees its source on the open half-line `(0,∞)` (its two defining
integrals range over `(0,z)` and `(z,∞)`).  Composing the two gives the additivity of `acoeff`. -/

/-- `radGreen` only sees the values of its source on the open half-line `(0,∞)`: for `z > 0`
both integrals range over positive arguments only. -/
private lemma radGreen_congr_Ioi {α : ℝ} (m : ℕ) {f g : ℝ → ℝ}
    (h : ∀ t : ℝ, 0 < t → f t = g t) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Radial.radGreen α m f z
      = Work.FTS.PhiStar.Radial.radGreen α m g z := by
  have h1 : (∫ t in (0 : ℝ)..z, f t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = (∫ t in (0 : ℝ)..z, g t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) := by
    rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => by rw [h t ht.1])
  have h2 : (∫ t in Set.Ioi z, f t * t ^ (-(2 * (m : ℝ) / α) - 1))
      = (∫ t in Set.Ioi z, g t * t ^ (-(2 * (m : ℝ) / α) - 1)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => by rw [h t (lt_trans hz ht)])
  simp only [Work.FTS.PhiStar.Radial.radGreen, h1, h2]

/-- **The mode-`m` radial coefficient is additive in the source** (at `z > 0`): both the mode
coefficient `cmode m · z` (linearity of the slice integral, `DiffGreen.cmode_sub`) and the
radial Green operator (locality on `z > 0`) are additive, and the `L²`-integrability of the two
sources is exactly what `cmode_sq_integrable` provides. -/
private lemma acoeff_sub {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {X Y : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X)
    (hY : Work.FTS.EllipticEst.SmoothOpen Y)
    (hXm : Work.Spaces.HkMem α 0 X) (hYm : Work.Spaces.HkMem α 0 Y)
    (m : ℕ) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Series.acoeff α m (fun z θ => X z θ - Y z θ) z
      = Work.FTS.PhiStar.Series.acoeff α m X z
        - Work.FTS.PhiStar.Series.acoeff α m Y z := by
  have hsl := Work.FTS.PhiStar.Honesty.DiffGreen.radGreen_sub (α := α) hα hα4 m
    (Work.EllipticEst.ModalSolution.aesm_cmode hY m)
    (Work.EllipticEst.ModalSolution.aesm_cmode hX m)
    (Work.FTS.PhiStar.Honesty.cmode_sq_integrable hY hYm m)
    (Work.FTS.PhiStar.Honesty.cmode_sq_integrable hX hXm m) hz
  have hcg := radGreen_congr_Ioi (α := α) m
    (f := fun t => Work.FTS.PhiStar.Series.cmode m (fun z θ => X z θ - Y z θ) t)
    (g := fun t => Work.FTS.PhiStar.Series.cmode m X t
      - Work.FTS.PhiStar.Series.cmode m Y t)
    (fun t ht => Work.FTS.PhiStar.Honesty.DiffGreen.cmode_sub hX hY hXm hYm m ht) hz
  simp only [Work.FTS.PhiStar.Series.acoeff]
  rw [hcg]
  exact hsl

/-! ## The truncations are additive in the source -/

private lemma psiTrunc_sub_eq {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {X Y : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X)
    (hY : Work.FTS.EllipticEst.SmoothOpen Y)
    (hXm : Work.Spaces.HkMem α 0 X) (hYm : Work.Spaces.HkMem α 0 Y)
    (N : ℕ) {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    Work.FTS.PhiStar.Series.psiTrunc α X N z θ
        - Work.FTS.PhiStar.Series.psiTrunc α Y N z θ
      = Work.FTS.PhiStar.Series.psiTrunc α (fun z θ => X z θ - Y z θ) N z θ := by
  simp only [Work.FTS.PhiStar.Series.psiTrunc]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun m _ => by
    rw [acoeff_sub hα hα4 hX hY hXm hYm m hz]
    ring)

/-- `psiSeries` is additive in the source on the open quadrant: `psiSeries α X - psiSeries α Y = psiSeries α (X - Y)`.
Suggested route (avoids any `Summable` bookkeeping): the truncations satisfy
`psiTrunc α X N z θ - psiTrunc α Y N z θ = psiTrunc α (X - Y) N z θ` for every `N`, because
`acoeff α m (X - Y) z = acoeff α m X z - acoeff α m Y z` (from `cmode_sub` + `radGreen_sub`);
each of the three truncation families converges (`psiTrunc_tendsto_psiSeries`) and the limit of a
difference is the difference of the limits, so `tendsto_nhds_unique` closes it. -/
theorem psiSeries_sub_eqOn {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {X Y : ℝ → ℝ → ℝ}
    (hXsm : Work.FTS.EllipticEst.SmoothOpen X) (hYsm : Work.FTS.EllipticEst.SmoothOpen Y)
    (hXm0 : Work.Spaces.HkMem α 0 X) (hYm0 : Work.Spaces.HkMem α 0 Y)
    (hXm1 : Work.Spaces.HkMem α 1 X) (hYm1 : Work.Spaces.HkMem α 1 Y)
    (hXor : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar X z = 0)
    (hYor : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar Y z = 0)
    (hXL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => X p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    (hYL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Y p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    (hZsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => X z θ - Y z θ))
    (hZor : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (fun z θ => X z θ - Y z θ) z = 0)
    (hZL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (X p.1 p.2 - Y p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.FTS.PhiStar.Series.psiSeries α X z θ - Work.FTS.PhiStar.Series.psiSeries α Y z θ
        = Work.FTS.PhiStar.Series.psiSeries α (fun z θ => X z θ - Y z θ) z θ := by
  intro z hz θ hθ0 hθ2
  have hα1 : α ≤ 1 := by linarith
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ2⟩
  -- the three truncation families converge to their series
  have hXlim := Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries (α := α) hα hα1
    hXor hXsm hXL2 hz hθI
  have hYlim := Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries (α := α) hα hα1
    hYor hYsm hYL2 hz hθI
  have hZlim := Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries (α := α) hα hα1
    hZor hZsm hZL2 hz hθI
  -- the difference of the first two is again a convergent family, with the limit `· - ·`
  have hsub := hXlim.sub hYlim
  -- and it is *pointwise equal* to the third family
  have hfun : (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α X N z θ
        - Work.FTS.PhiStar.Series.psiTrunc α Y N z θ)
      = fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α (fun z θ => X z θ - Y z θ) N z θ :=
    funext fun N => psiTrunc_sub_eq hα hα4 hXsm hYsm hXm0 hYm0 N hz θ
  rw [hfun] at hsub
  exact tendsto_nhds_unique hsub hZlim

end Work.FTS.PhiStar.RouteB
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.c1_of_locUnif_slots_lip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Slice derivatives of a differentiable two-variable function -/

/-- The `z`-slice of a differentiable two-variable function has derivative `∂_z`. -/
theorem hasDerivAt_uncurry_slice_z {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry f) (z, θ)) :
    HasDerivAt (fun s : ℝ => f s θ) (Work.Spaces.pz f z θ) z := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  have hd := h.hasFDerivAt.comp_hasDerivAt z hcurve
  rw [Work.Spaces.pz_eq_fderiv h]
  exact hd

/-- The `θ`-slice of a differentiable two-variable function has derivative `∂_θ`. -/
theorem hasDerivAt_uncurry_slice_th {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry f) (z, θ)) :
    HasDerivAt (fun t : ℝ => f z t) (Work.Spaces.pth f z θ) θ := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  have hd := h.hasFDerivAt.comp_hasDerivAt θ hcurve
  rw [Work.Spaces.pth_eq_fderiv h]
  exact hd

/-- `toSpanSingleton` is the scalar multiple of the identity: this is the bridge between the
`HasDerivAt`-form (whose Fréchet derivative is a `toSpanSingleton`) and `clmPair`. -/
theorem toSpanSingleton_eq_smul_one (b : ℝ) :
    ContinuousLinearMap.toSpanSingleton ℝ b = (b • (1 : ℝ →L[ℝ] ℝ)) := by
  refine ContinuousLinearMap.ext fun c => ?_
  rw [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smul_apply]
  simp [smul_eq_mul, mul_comm]

/-- `clmHead` in the one-dimensional second slot is `clmPair`. -/
theorem clmHead_smul_one (a b : ℝ) :
    clmHead ℝ a ((b • (1 : ℝ →L[ℝ] ℝ)) : ℝ →L[ℝ] ℝ) = clmPair (a, b) :=
  clmHead_eq_clmPair a b


/-! ## The theorem -/

theorem c1_of_locUnif_slots_lip {G : ℕ → Work.FTS.Galerkin.Fam} {F : ℝ → Work.FTS.Galerkin.Fn}
    {W : ℝ → Work.FTS.Galerkin.Fn} {α B T : ℝ}
    (hT : 0 < T)
    (hconv : ∀ τ ∈ Set.Icc 0 T,
      Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) τ) (F τ))
    (hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 1 → ∀ p ∈ K,
        ∀ τ ∈ Set.Icc 0 T, ∀ τ' ∈ Set.Icc 0 T,
          |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ) p.1 p.2
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ') p.1 p.2|
            ≤ C * |τ - τ'|)
    (hW : ∀ τ ∈ Set.Icc 0 T, ∀ p ∈ Work.Construction.Qd,
      HasDerivWithinAt (fun s => F s p.1 p.2) (W τ p.1 p.2) (Set.Icc 0 T) τ)
    (hWc : ContinuousOn (fun p : ℝ × ℝ × ℝ => W p.2.2 p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 T)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => F p.2.2 p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 T) := by
  set U : Set (ℝ × ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T with hU
  set A : ℝ × ℝ × ℝ → ℝ := (fun p : ℝ × ℝ × ℝ => F p.2.2 p.1 p.2.1) with hA
  have hUopen : IsOpen U := by
    rw [hU]
    exact isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioo)
  have hmemU : ∀ q : ℝ × ℝ × ℝ, q ∈ U →
      0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi / 2 ∧ 0 < q.2.2 ∧ q.2.2 < T := by
    intro q hq
    rw [hU] at hq
    exact ⟨hq.1, hq.2.1.1, hq.2.1.2, hq.2.2.1, hq.2.2.2⟩
  have hQ0 : ∀ q : ℝ × ℝ × ℝ, q ∈ U → (q.1, q.2.1) ∈ Work.FTS.EllipticEst.Q0 := by
    intro q hq
    have h := hmemU q hq
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨h.1, h.2.1, h.2.2.1⟩
  have hUsub : U ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 T := by
    intro q hq
    have h := hmemU q hq
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
    exact ⟨h.1, ⟨⟨h.2.1, h.2.2.1⟩, le_of_lt h.2.2.2.1, le_of_lt h.2.2.2.2⟩⟩
  -- (1) the slices are `C⁴`
  have hsm : ∀ τ ∈ Set.Icc 0 T,
      ContDiffOn ℝ 4 (Function.uncurry (F τ)) Work.FTS.EllipticEst.Q0 :=
    fun τ hτ => (hconv τ hτ).2.1
  -- (2) the limit slots are Lipschitz in `τ`
  have hlipF := slot_lip_limit (G := G) (F := F) (α := α) (B := B) (T := T) hconv hlip
  -- (3) joint continuity of the slots of the limit
  have hslot := slot_joint_cont (F := F) (T := T) hsm hlipF
  -- (4) continuity of the partial derivatives on `U`
  have hmix10 : ∀ q : ℝ × ℝ × ℝ, Work.Spaces.mixed 1 0 (F q.2.2) q.1 q.2.1
      = q.1 * Work.Spaces.pz (F q.2.2) q.1 q.2.1 := fun q => rfl
  have hmix01 : ∀ q : ℝ × ℝ × ℝ, Work.Spaces.mixed 0 1 (F q.2.2) q.1 q.2.1
      = Real.sin (2 * q.2.1) * Work.Spaces.pth (F q.2.2) q.1 q.2.1 := fun q => rfl
  have hz0 : ∀ q ∈ U, q.1 ≠ 0 := fun q hq => ne_of_gt (hmemU q hq).1
  have hs0 : ∀ q ∈ U, Real.sin (2 * q.2.1) ≠ 0 := by
    intro q hq
    have h := hmemU q hq
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hpz_cont : ContinuousOn (fun q : ℝ × ℝ × ℝ => Work.Spaces.pz (F q.2.2) q.1 q.2.1) U := by
    have h10 : ContinuousOn (fun q : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed 1 0 (F q.2.2) q.1 q.2.1) U :=
      (hslot 1 0 (by norm_num)).mono hUsub
    have hz : ContinuousOn (fun q : ℝ × ℝ × ℝ => q.1) U := continuous_fst.continuousOn
    refine (h10.div hz hz0).congr fun q hq => ?_
    change Work.Spaces.pz (F q.2.2) q.1 q.2.1
      = Work.Spaces.mixed 1 0 (F q.2.2) q.1 q.2.1 / q.1
    rw [hmix10 q, mul_div_cancel_left₀ _ (hz0 q hq)]
  have hpth_cont : ContinuousOn (fun q : ℝ × ℝ × ℝ => Work.Spaces.pth (F q.2.2) q.1 q.2.1) U := by
    have h01 : ContinuousOn (fun q : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed 0 1 (F q.2.2) q.1 q.2.1) U :=
      (hslot 0 1 (by norm_num)).mono hUsub
    have hs : ContinuousOn (fun q : ℝ × ℝ × ℝ => Real.sin (2 * q.2.1)) U :=
      (Real.continuous_sin.comp (continuous_const.mul
        (continuous_fst.comp continuous_snd))).continuousOn
    refine (h01.div hs hs0).congr fun q hq => ?_
    change Work.Spaces.pth (F q.2.2) q.1 q.2.1
      = Work.Spaces.mixed 0 1 (F q.2.2) q.1 q.2.1 / Real.sin (2 * q.2.1)
    rw [hmix01 q, mul_div_cancel_left₀ _ (hs0 q hq)]
  have hW_cont : ContinuousOn (fun q : ℝ × ℝ × ℝ => W q.2.2 q.1 q.2.1) U := hWc
  -- (5) slice derivatives
  have hsliceθ : ∀ τ ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun t : ℝ => F τ z t) (Work.Spaces.pth (F τ) z θ) θ := by
    intro τ hτ z θ hQ
    have hd : DifferentiableAt ℝ (Function.uncurry (F τ)) (z, θ) :=
      ((hsm τ hτ).differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ)
    exact hasDerivAt_uncurry_slice_th hd
  have hslicez : ∀ τ ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun s : ℝ => F τ s θ) (Work.Spaces.pz (F τ) z θ) z := by
    intro τ hτ z θ hQ
    have hd : DifferentiableAt ℝ (Function.uncurry (F τ)) (z, θ) :=
      ((hsm τ hτ).differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ)
    exact hasDerivAt_uncurry_slice_z hd
  have hsliceτ : ∀ τ ∈ Set.Ioo 0 T, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s : ℝ => F s z θ) (W τ z θ) τ := by
    intro τ hτ z θ hQ
    exact (hW τ ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩ (z, θ) hQ).hasDerivAt
      (Icc_mem_nhds hτ.1 hτ.2)
  -- (6) the inner Fréchet derivative: differentiation in `(θ, τ)` at fixed `z`
  have hinner : ∀ (z θ τ : ℝ), 0 < z →
      (θ, τ) ∈ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T →
      HasFDerivAt (fun y : ℝ × ℝ => F y.2 z y.1)
        (clmPair (Work.Spaces.pth (F τ) z θ, W τ z θ)) (θ, τ) := by
    intro z θ τ hz hmem
    have hV : IsOpen (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T) :=
      isOpen_Ioo.prod isOpen_Ioo
    have hp : (θ, τ) ∈ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T := hmem
    have h₁ : ∀ q ∈ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T,
        HasDerivAt (fun x : ℝ => F q.2 z x) (Work.Spaces.pth (F q.2) z q.1) q.1 := by
      intro q hq
      exact hsliceθ q.2 ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩ z q.1
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hq.1.1, hq.1.2⟩)
    have h₂ : ∀ q ∈ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T,
        HasFDerivAt (fun y : ℝ => F y z q.1) ((W q.2 z q.1) • (1 : ℝ →L[ℝ] ℝ)) q.2 := by
      intro q hq
      have hd := hsliceτ q.2 hq.2 z q.1 ⟨hz, hq.1.1, hq.1.2⟩
      rw [← toSpanSingleton_eq_smul_one]
      exact hd.hasFDerivAt
    have hmap : Set.MapsTo (fun q : ℝ × ℝ => (z, q.1, q.2))
        (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T) U := by
      intro q hq
      have h1 : 0 < q.1 := hq.1.1
      have h2 : q.1 < Real.pi / 2 := hq.1.2
      have h3 : 0 < q.2 := hq.2.1
      have h4 : q.2 < T := hq.2.2
      rw [hU]
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      tauto
    have hcont2 : Continuous (fun q : ℝ × ℝ => (z, q.1, q.2)) :=
      (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))
    have hc₁ : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.pth (F q.2) z q.1)
        (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T) :=
      hpth_cont.comp hcont2.continuousOn hmap
    have hc₂ : ContinuousOn (fun q : ℝ × ℝ => (W q.2 z q.1) • (1 : ℝ →L[ℝ] ℝ))
        (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T) :=
      (hW_cont.comp hcont2.continuousOn hmap).smul continuousOn_const
    have hmain : HasFDerivAt (fun y : ℝ × ℝ => F y.2 z y.1)
        (clmHead ℝ (Work.Spaces.pth (F τ) z θ)
          ((W τ z θ) • (1 : ℝ →L[ℝ] ℝ))) (θ, τ) :=
      hasFDerivAt_of_fst_snd (E := ℝ)
        (f := fun q : ℝ × ℝ => F q.2 z q.1)
        (g₁ := fun q : ℝ × ℝ => Work.Spaces.pth (F q.2) z q.1)
        (g₂ := fun q : ℝ × ℝ => (W q.2 z q.1) • (1 : ℝ →L[ℝ] ℝ))
        hV hp h₁ h₂ hc₁ hc₂
    rw [clmHead_smul_one] at hmain
    exact hmain
  -- (7) the outer Fréchet derivative
  have hderiv : ∀ p ∈ U, HasFDerivAt A (clmHead (ℝ × ℝ)
      (Work.Spaces.pz (F p.2.2) p.1 p.2.1)
      (clmPair (Work.Spaces.pth (F p.2.2) p.1 p.2.1, W p.2.2 p.1 p.2.1))) p := by
    intro p hp
    refine hasFDerivAt_of_fst_snd (E := ℝ × ℝ) (f := A)
      (g₁ := fun q : ℝ × ℝ × ℝ => Work.Spaces.pz (F q.2.2) q.1 q.2.1)
      (g₂ := fun q : ℝ × ℝ × ℝ =>
        clmPair (Work.Spaces.pth (F q.2.2) q.1 q.2.1, W q.2.2 q.1 q.2.1))
      hUopen hp ?_ ?_ hpz_cont ?_
    · intro q hq
      have h := hmemU q hq
      exact hslicez q.2.2 ⟨le_of_lt h.2.2.2.1, le_of_lt h.2.2.2.2⟩ q.1 q.2.1
        (hQ0 q hq)
    · intro q hq
      have h := hmemU q hq
      refine hinner q.1 q.2.1 q.2.2 h.1 ?_
      simp only [Set.mem_prod, Set.mem_Ioo]
      exact ⟨⟨h.2.1, h.2.2.1⟩, ⟨h.2.2.2.1, h.2.2.2.2⟩⟩
    · have hpair : ContinuousOn (fun q : ℝ × ℝ × ℝ =>
          (Work.Spaces.pth (F q.2.2) q.1 q.2.1, W q.2.2 q.1 q.2.1)) U :=
        hpth_cont.prodMk hW_cont
      exact clmPair.continuous.comp_continuousOn hpair
  -- (8) assemble `C¹`
  have hdiff : DifferentiableOn ℝ A U := fun p hp =>
    (hderiv p hp).differentiableAt.differentiableWithinAt
  have hfdc : ContinuousOn (fun p : ℝ × ℝ × ℝ => fderiv ℝ A p) U := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        (Work.Spaces.pz (F p.2.2) p.1 p.2.1,
          clmPair (Work.Spaces.pth (F p.2.2) p.1 p.2.1, W p.2.2 p.1 p.2.1))) U :=
      hpz_cont.prodMk (clmPair.continuous.comp_continuousOn (hpth_cont.prodMk hW_cont))
    have h2 := (clmHeadL (ℝ × ℝ)).continuous.comp_continuousOn h1
    refine h2.congr fun p hp => ?_
    rw [(hderiv p hp).fderiv]
    rfl
  have key : ContDiffOn ℝ (1 : ℕ∞ω) A U := by
    rw [show (1 : ℕ∞ω) = (0 : ℕ∞ω) + 1 from by norm_num]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen hUopen).mpr ⟨hdiff, ?_, ?_⟩
    · intro h
      exact absurd h (by norm_num)
    · rw [contDiffOn_zero]
      exact hfdc
  exact key

end Work.FTS.StrongEps.E5Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.EpsRHSP_slotSup_val5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

/-! ## A uniform pointwise bound for the mixed derivatives of the correction profile

`bump` is `C^∞` on the open quadrant (`smoothOpen_bump`), so each `D_z^jD_θ^i bump` is `C^∞`
on `Q0` (`SmoothOpen.mixed`), hence in particular continuous on the compact `K ⊆ Q0`; the sum of
the absolute values of the finitely many slots of order `≤ 5` is a continuous function on `K`,
and its supremum bounds every single slot. -/

theorem exists_bound_mixed_bump5 (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (j i : ℕ), j + i ≤ 5 → ∀ p ∈ K,
      |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| ≤ Cb := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ∑ j ∈ Finset.range 6, ∑ i ∈ Finset.range 6,
      |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|) K := by
    refine continuousOn_finsetSum _ (fun j _ => continuousOn_finsetSum _ (fun i _ => ?_))
    exact ((Work.FTS.StrongEps.smoothOpen_bump.mixed j i).continuousOn.mono hKQ).abs
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro j i hji p hp
  have hj : j ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have hi : i ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have h1 : |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
      ≤ ∑ i' ∈ Finset.range 6,
          |Work.Spaces.mixed j i' Work.FTS.StrongEps.bump p.1 p.2| :=
    Finset.single_le_sum
      (f := fun i' => |Work.Spaces.mixed j i' Work.FTS.StrongEps.bump p.1 p.2|)
      (fun i' _ => abs_nonneg _) hi
  have h2 : (∑ i' ∈ Finset.range 6,
        |Work.Spaces.mixed j i' Work.FTS.StrongEps.bump p.1 p.2|)
      ≤ ∑ j' ∈ Finset.range 6, ∑ i' ∈ Finset.range 6,
          |Work.Spaces.mixed j' i' Work.FTS.StrongEps.bump p.1 p.2| :=
    Finset.single_le_sum
      (f := fun j' => ∑ i' ∈ Finset.range 6,
        |Work.Spaces.mixed j' i' Work.FTS.StrongEps.bump p.1 p.2|)
      (fun j' _ => Finset.sum_nonneg (fun i' _ => abs_nonneg _)) hj
  have h3 : (∑ j' ∈ Finset.range 6, ∑ i' ∈ Finset.range 6,
        |Work.Spaces.mixed j' i' Work.FTS.StrongEps.bump p.1 p.2|) ≤ M := by
    have hMp := hM p hp
    rw [Real.norm_eq_abs] at hMp
    exact le_trans (le_abs_self _) hMp
  linarith [le_max_left M 0]

/-! ## The mass of the routed kernels over the slots of order `≤ 5` -/

/-- The total mass over the twenty-one slots of order `≤ 5`, which dominates every single one of
them (together with the factor `2 ^ i` coming from the `θ`-routing).  This is
`Work.FTS.StrongEps.KmassTot` with the ranges enlarged from `5` to `6`. -/
noncomputable def KmassTot5 (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, ∑ i ∈ Finset.range 6, (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i

theorem KmassTot5_nonneg (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : 0 ≤ KmassTot5 ρ ε := by
  unfold KmassTot5
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
    mul_nonneg (by positivity) (Work.FTS.StrongEps.Kmass_nonneg ρ ε j i)

/-- Every slot of order `≤ 5` is dominated by the total mass. -/
theorem two_pow_mul_Kmass_le_KmassTot5 (ρ : ℝ × ℝ → ℝ) (ε : ℝ) {j i : ℕ}
    (hji : j + i ≤ 5) : (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i ≤ KmassTot5 ρ ε := by
  have hj : j ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have hi : i ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have hinner : ∀ i' ∈ Finset.range 6,
      (0 : ℝ) ≤ (2 : ℝ) ^ i' * Work.FTS.StrongEps.Kmass ρ ε j i' :=
    fun i' _ => mul_nonneg (by positivity) (Work.FTS.StrongEps.Kmass_nonneg ρ ε j i')
  calc (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i
      ≤ ∑ i' ∈ Finset.range 6, (2 : ℝ) ^ i' * Work.FTS.StrongEps.Kmass ρ ε j i' :=
        Finset.single_le_sum
          (f := fun i' => (2 : ℝ) ^ i' * Work.FTS.StrongEps.Kmass ρ ε j i') hinner hi
    _ ≤ KmassTot5 ρ ε := by
        unfold KmassTot5
        refine Finset.single_le_sum
          (f := fun j' => ∑ i' ∈ Finset.range 6, (2 : ℝ) ^ i' * Work.FTS.StrongEps.Kmass ρ ε j' i')
          (fun j' _ => ?_) hj
        exact Finset.sum_nonneg fun i' _ =>
          mul_nonneg (by positivity) (Work.FTS.StrongEps.Kmass_nonneg ρ ε j' i')

/-! ## The target -/

theorem EpsRHSP_slotSup_val5 {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hreg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hwin : ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
      (∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ 1 → |q.2| ≤ 1 →
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2) ∈ K') ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K',
        |Work.FTS.StrongEps.epsWP α ρ ε Φs E g s p.1 p.2| ≤ B)
    (hnorm : ∃ KW : ℝ, 0 ≤ KW ∧ ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ≤ KW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 5 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∀ p ∈ K, |Work.Spaces.mixed j i
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C := by
  obtain ⟨K', hK'c, hK'Q, hKK', hshift, B, hB, hbdd⟩ := hwin
  obtain ⟨KW, hKW, hnorm'⟩ := hnorm
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump5 K hK hKQ
  obtain ⟨CL, hCL0, hCL⟩ := Work.FTS.StrongEps.abs_L12_Jeps_le (ρ := ρ) hρ
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  refine ⟨B * KmassTot5 ρ ε + (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hB (KmassTot5_nonneg ρ ε))
      (mul_nonneg (div_nonneg (mul_nonneg hCL0 hKW) hpzpos.le) hCb0)
  · intro j i hji s hs p hp
    obtain ⟨hmems, hnormbs⟩ := hnorm' s hs
    have hpQ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
    have hz : 0 < p.1 := hpQ.1
    have hθ : p.2 ∈ Set.Ioo 0 (π / 2) := ⟨hpQ.2.1, hpQ.2.2⟩
    have hsm : ∀ n : ℕ, ContDiffOn ℝ n
        (Function.uncurry (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))
        Work.FTS.StrongEps.Quad := (hreg s hs).forall
    -- the *value* bound of `epsWP` transfers to the shifted points inside the kernel's ball
    have hF : ∀ q : ℝ × ℝ, |q.1| ≤ ε → |q.2| ≤ ε →
        |Work.FTS.StrongEps.epsWP α ρ ε Φs E g s
            (Work.FTS.StrongEps.zShift p.1 q.1) (Work.FTS.StrongEps.thShift p.2 q.2)| ≤ B :=
      fun q hq1 hq2 => hbdd s hs
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2)
        (hshift p hp q (le_trans hq1 hε.2) (le_trans hq2 hε.2))
    have hmain : |Work.Spaces.mixed j i
        (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2|
        ≤ B * KmassTot5 ρ ε := by
      refine le_trans
        (Work.FTS.StrongEps.abs_mixed_Jeps_le_val (ρ := ρ) hρ hε.1 hsm hz hθ hF j i) ?_
      calc (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i * B
          = ((2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i) * B := by ring
        _ ≤ KmassTot5 ρ ε * B :=
            mul_le_mul_of_nonneg_right (two_pow_mul_Kmass_le_KmassTot5 ρ ε hji) hB
        _ = B * KmassTot5 ρ ε := by ring
    have hcorr : |(Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
            / Work.FTS.StrongEps.pzNorm) * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
        ≤ (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb := by
      rw [abs_mul]
      have hL : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0|
          ≤ CL * KW := hCL hα hε.1 hε.2 hKW hsm hmems hnormbs
      have hal : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
            / Work.FTS.StrongEps.pzNorm| ≤ CL * KW / Work.FTS.StrongEps.pzNorm := by
        rw [abs_div, abs_of_pos hpzpos]
        exact div_le_div_of_nonneg_right hL hpzpos.le
      have hb : |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| ≤ Cb :=
        hbump j i hji p hp
      exact mul_le_mul hal hb (abs_nonneg _)
        (div_nonneg (mul_nonneg hCL0 hKW) hpzpos.le)
    have hsplit : Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2
        = Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2 := by
      rw [Work.FTS.StrongEps.epsRHSP_eq_Pz_Jeps_epsWP,
        Work.FTS.StrongEps.PZeroAux.mixed_Pz
          (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε.1 hsm) hz hθ j i]
    rw [hsplit]
    calc |Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
        ≤ |Work.Spaces.mixed j i
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2|
          + |(Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| := by
          have h := abs_add_le (Work.Spaces.mixed j i
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2)
            (-((Work.Construction.L12
                (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                  / Work.FTS.StrongEps.pzNorm)
                * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2))
          simpa only [sub_eq_add_neg, abs_neg] using h
      _ ≤ B * KmassTot5 ρ ε + (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb :=
          add_le_add hmain hcorr

end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.slice_lip_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

/-! ## Elementary helper lemmas -/

/-- For a nonnegative function, `ENNReal.ofReal` of its Bochner integral is at most the
`lintegral` of `ENNReal.ofReal ∘ f`.  (No measurability or integrability is needed: this is the
`enorm` form of the elementary `‖∫ f‖ ≤ ∫ ‖f‖`.) -/
theorem slice_lip_ofReal_integral_le_lintegral {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have h1 : ENNReal.ofReal (∫ x, f x ∂μ) = ‖∫ x, f x ∂μ‖ₑ :=
    (Real.enorm_eq_ofReal (integral_nonneg hf)).symm
  rw [h1]
  refine (enorm_integral_le_lintegral_enorm f).trans ?_
  refine lintegral_mono fun x => ?_
  rw [Real.enorm_eq_ofReal (hf x)]

/-- `HkSq` is the square of `HkNorm`, so a bound on the norm bounds the square. -/
theorem slice_lip_HkSq_le_sq {α B : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkNorm α k f ≤ B) : Work.Spaces.HkSq α k f ≤ B ^ 2 := by
  have h2 : Work.Spaces.HkSq α k f = (Work.Spaces.HkNorm α k f) ^ 2 :=
    (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f)).symm
  rw [h2]
  exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α k f) h 2

/-! ## The pointwise slot identity for the fake-time integral -/

/-- The mixed slots of the fake-time integral of the right-hand side:
`D_z^jD_θ^i (∫ s in σ'..σ, epsRHSP s) = ∫ s in σ'..σ, D_z^jD_θ^i (epsRHSP s)` at every point of
the open quadrant, for `j + i ≤ 4`. -/
theorem slice_lip_slot_eq {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) (Set.Icc (0 : ℝ) T))
    (hsmR : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hslotb : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ 4 → ∀ p : ℝ × ℝ, p ∈ K →
        |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C)
    {σ σ' : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) T) (hσ' : σ' ∈ Set.Icc (0 : ℝ) T) (hle : σ' ≤ σ)
    {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) {j i : ℕ} (hji : j + i ≤ 4) :
    Work.Spaces.mixed j i
        (fun z θ => ∫ s in σ'..σ, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) p.1 p.2
      = ∫ s in σ'..σ, Work.Spaces.mixed j i
          (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2 := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  -- a closed box around `p` inside the open quadrant
  set z₁ : ℝ := p.1 / 2 with hz₁
  set z₂ : ℝ := p.1 + 1 with hz₂
  set θ₁ : ℝ := p.2 / 2 with hθ₁
  set θ₂ : ℝ := (p.2 + Real.pi / 2) / 2 with hθ₂
  have hz1lt : z₁ < p.1 := by rw [hz₁]; linarith
  have hz2gt : p.1 < z₂ := by rw [hz₂]; linarith
  have hθ1lt : θ₁ < p.2 := by rw [hθ₁]; linarith
  have hθ2gt : p.2 < θ₂ := by rw [hθ₂]; linarith
  have hz1pos : 0 < z₁ := by rw [hz₁]; linarith
  have hθ1pos : 0 < θ₁ := by rw [hθ₁]; linarith
  have hθ2lt : θ₂ < Real.pi / 2 := by rw [hθ₂]; linarith
  have hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro q ⟨hq1, hq2⟩
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le hz1pos hq1.1, lt_of_lt_of_le hθ1pos hq2.1, lt_of_le_of_lt hq2.2 hθ2lt⟩
  have hbox_compact : IsCompact (Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hslotb _ hbox_compact hboxQ
  have hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ →
        |Work.Spaces.mixed k l (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) q.1 q.2| ≤ max C 0 :=
    fun s hs k l hkl q hq => le_trans (hC s hs k l hkl q hq) (le_max_left _ _)
  exact Work.FTS.StrongEps.mixed_intervalIntegral_eq (H := fun s z θ =>
      Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) hσ' hσ hle (le_max_right _ _) hsmR
    (Work.FTS.StrongEps.aemeasurable_mixed_family hsmR hcont) hbdd hboxQ hji p.1 p.2
    ⟨⟨hz1lt, hz2gt⟩, ⟨hθ1lt, hθ2gt⟩⟩

/-! ## The slice difference is the fake-time integral on the open quadrant -/

/-- `slice g σ - slice g σ'` agrees with `∫ s in σ'..σ, epsRHSP s` on the open quadrant. -/
theorem slice_lip_diff_eq_integral {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) (Set.Icc (0 : ℝ) T))
    {σ σ' : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) T) (hσ' : σ' ∈ Set.Icc (0 : ℝ) T) (hle : σ' ≤ σ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.FTS.Galerkin.slice g σ z θ - Work.FTS.Galerkin.slice g σ' z θ
        = ∫ s in σ'..σ, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ := by
  intro z θ hzθ
  have h1 := Work.FTS.StrongEps.epsSol_eq_integralP hsol hcont z θ σ hzθ hσ
  have h2 := Work.FTS.StrongEps.epsSol_eq_integralP hsol hcont z θ σ' hzθ hσ'
  have hcontF : ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ)
      (Set.Icc (0 : ℝ) T) := hcont z θ hzθ
  have hi1 : IntervalIntegrable (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ)
      volume 0 σ' :=
    ContinuousOn.intervalIntegrable_of_Icc hσ'.1
      (hcontF.mono (Set.Icc_subset_Icc le_rfl hσ'.2))
  have hi2 : IntervalIntegrable (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ)
      volume σ' σ :=
    ContinuousOn.intervalIntegrable_of_Icc hle
      (hcontF.mono (Set.Icc_subset_Icc hσ'.1 hσ.2))
  have hadj := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  show g z θ σ - g z θ σ' = _
  rw [h1, h2]
  linarith

/-! ## The per-`s` Tonelli identity -/

/-- For a fixed slice `f` of class `HkMem α k` whose `HkIntegrand` is jointly measurable, the
`lintegral` of `ofReal ∘ HkIntegrand` over `Iz × Iθ` is `ofReal (HkSq α k f)`. -/
theorem slice_lip_ofReal_HkSq_eq_lintegral {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k f)
    (hmeas : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    (∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = ENNReal.ofReal (Work.Spaces.HkSq α k f) := by
  have hmeas' : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hmeas
  rw [Work.Spaces.HkSq,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)]
  have hlin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      = ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f p.1 p.2)
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.lintegral_lintegral
      (f := fun z θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ)) hmeas'
  rw [← hlin]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)).symm


/-! ## Auxiliary lemmas for the main chain -/

/-- The interval `uIoc σ' σ` is contained in `Icc 0 T`. -/
lemma slice_lip_uIoc_subset {T σ σ' : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) T)
    (hσ' : σ' ∈ Set.Icc (0 : ℝ) T) (hle : σ' ≤ σ) : Set.uIoc σ' σ ⊆ Set.Icc (0 : ℝ) T := by
  intro s hs
  have h1 : s ∈ Set.Icc σ' σ := by
    have h2 := Set.uIoc_subset_uIcc hs
    rwa [Set.uIcc_of_le hle] at h2
  exact ⟨le_trans hσ'.1 h1.1, le_trans h1.2 hσ.2⟩

/-- The interval integral over `σ'..σ` is the set integral over `uIoc σ' σ`. -/
lemma slice_lip_intervalIntegral_eq_set {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x in a..b, f x) = ∫ x in Set.uIoc a b, f x := by
  rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]

/-- **Tonelli swap for the fake-time integral of the `HkIntegrand`.**
For a family `H` of `SmoothOpen` profiles whose `HkIntegrand` is jointly measurable, the iterated
`lintegral` over `(z,θ)` of the fake-time `lintegral` over `s` equals the iterated `lintegral` over
`s` of the `(z,θ)`-one. -/
theorem slice_lip_tonelli {α : ℝ} {k : ℕ} {T σ σ' : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hσ : σ ∈ Set.Icc (0 : ℝ) T) (hσ' : σ' ∈ Set.Icc (0 : ℝ) T) (hle : σ' ≤ σ)
    (hmeas : AEMeasurable
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.HkIntegrand α k (H q.1) q.2.1 q.2.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ))
      = ∫⁻ s in Set.uIoc σ' σ, ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ) := by
  have hsub : Set.uIoc σ' σ ⊆ Set.Icc (0 : ℝ) T := slice_lip_uIoc_subset hσ hσ' hle
  have hle' : (volume.restrict (Set.uIoc σ' σ) : Measure ℝ) ≤ volume.restrict (Set.Icc (0 : ℝ) T) :=
    Measure.restrict_mono hsub le_rfl
  have hle'' : (volume.restrict (Set.uIoc σ' σ) : Measure ℝ).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      ≤ (volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Measure.prod_mono hle' le_rfl
  -- measurability of the `ofReal`-family with the `s`-measure restricted to the interval
  have hf : AEMeasurable
      (fun q : ℝ × (ℝ × ℝ) => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H q.1) q.2.1 q.2.2))
      ((volume.restrict (Set.uIoc σ' σ)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hmeas.mono_measure hle'')
  -- measurability of the partial `s`-integral over `(z,θ)`
  have hf'' : AEMeasurable
      (fun p : ℝ × ℝ => ∫⁻ s in Set.uIoc σ' σ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    AEMeasurable.lintegral_prod_left'
      (f := fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H q.1) q.2.1 q.2.2)) hf
  -- single-slice measurability, from continuity on the open quadrant
  have hsingle : ∀ s ∈ Set.uIoc σ' σ, AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    intro s hs
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact (Work.Spaces.aesm_of_continuousOn_Qd _
      ((hsm s (hsub hs)).continuousOn_HkIntegrand α k)).aemeasurable
  have h1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ))
      = ∫⁻ p, (∫⁻ s in Set.uIoc σ' σ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2))
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.lintegral_prod
      (f := fun p : ℝ × ℝ => ∫⁻ s in Set.uIoc σ' σ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2)) hf'').symm
  have h2 : (∫⁻ p, (∫⁻ s in Set.uIoc σ' σ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2))
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = ∫⁻ s in Set.uIoc σ' σ, ∫⁻ p,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2)
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.lintegral_prod_symm
        (f := fun q : ℝ × (ℝ × ℝ) =>
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H q.1) q.2.1 q.2.2)) hf).symm.trans
      (MeasureTheory.lintegral_prod
        (f := fun q : ℝ × (ℝ × ℝ) =>
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H q.1) q.2.1 q.2.2)) hf)
  have h3 : (∫⁻ s in Set.uIoc σ' σ, ∫⁻ p,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = ∫⁻ s in Set.uIoc σ' σ, ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    exact MeasureTheory.lintegral_prod
      (f := fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2))
      (hsingle s hs)
  exact h1.trans (h2.trans h3)
end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsProfileLip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem EpsProfileLip {α T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam}
    (hsol : ∀ n : ℕ, Work.FTS.StrongEps.IsEpsSolP α ρ (ε n) T Φs E g₀ (G n))
    (hcont : ∀ n : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
        (Set.Icc (0 : ℝ) T))
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K,
        |Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) T,
        ∀ τ' ∈ Set.Icc (0 : ℝ) T,
          |Work.FTS.Galerkin.slice (G n) τ p.1 p.2 - Work.FTS.Galerkin.slice (G n) τ' p.1 p.2|
            ≤ C * |τ - τ'| := by
  intro K hK hKQ
  obtain ⟨C₀, hC₀nn, hC₀⟩ := hbdd K hK hKQ
  refine ⟨C₀, hC₀nn, ?_⟩
  intro n p hp τ hτ τ' hτ'
  have hQ : (p.1, p.2) ∈ Work.FTS.EllipticEst.Q0 := hKQ hp
  have hFcont : ContinuousOn
      (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
      (Set.Icc (0 : ℝ) T) := hcont n p hQ
  have hFbd : ∀ s ∈ Set.Icc (0 : ℝ) T,
      |Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C₀ :=
    fun s hs => hC₀ n s hs p hp
  -- the integral form of the two slices and the resulting difference identity
  have key : ∀ σ σ' : ℝ, σ ∈ Set.Icc (0 : ℝ) T → σ' ∈ Set.Icc (0 : ℝ) T → σ' ≤ σ →
      |Work.FTS.Galerkin.slice (G n) σ p.1 p.2 - Work.FTS.Galerkin.slice (G n) σ' p.1 p.2|
        ≤ C₀ * |σ - σ'| := by
    intro σ σ' hσ hσ' hle
    have h1 := Work.FTS.StrongEps.epsSol_eq_integralP (hsol n)
      (fun z θ hzθ => hcont n (z, θ) hzθ) p.1 p.2 σ hQ hσ
    have h2 := Work.FTS.StrongEps.epsSol_eq_integralP (hsol n)
      (fun z θ hzθ => hcont n (z, θ) hzθ) p.1 p.2 σ' hQ hσ'
    have hi1 : IntervalIntegrable
        (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
        MeasureTheory.volume (0 : ℝ) σ' :=
      ContinuousOn.intervalIntegrable_of_Icc hσ'.1
        (hFcont.mono (Set.Icc_subset_Icc le_rfl hσ'.2))
    have hi2 : IntervalIntegrable
        (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
        MeasureTheory.volume σ' σ :=
      ContinuousOn.intervalIntegrable_of_Icc hle (hFcont.mono (Set.Icc_subset_Icc hσ'.1 hσ.2))
    have hadj := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hdiff : Work.FTS.Galerkin.slice (G n) σ p.1 p.2
          - Work.FTS.Galerkin.slice (G n) σ' p.1 p.2
        = ∫ s in σ'..σ, Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2 := by
      show (G n) p.1 p.2 σ - (G n) p.1 p.2 σ' = _
      rw [h1, h2]
      linarith
    rw [hdiff]
    have hnorm : ‖∫ s in σ'..σ,
          Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2‖
        ≤ C₀ * |σ - σ'| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      rw [Set.uIoc_of_le hle] at hx
      rw [Real.norm_eq_abs]
      exact hFbd x ⟨le_trans hσ'.1 hx.1.le, le_trans hx.2 hσ.2⟩
    simpa only [Real.norm_eq_abs] using hnorm
  rcases le_total τ' τ with hle | hle
  · exact key τ τ' hτ hτ' hle
  · have h := key τ' τ hτ' hτ hle
    rw [abs_sub_comm (Work.FTS.Galerkin.slice (G n) τ p.1 p.2)
          (Work.FTS.Galerkin.slice (G n) τ' p.1 p.2), abs_sub_comm τ τ']
    exact h

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_sub_smul_bump_res =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The weight `epsW` on the open quadrant -/

/-- The weighted profile `bump · epsW α` is a.e. strongly measurable for the measure of
`EpsMem`. -/
theorem aesm_bump_mul_epsW (α : ℝ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
      Work.FTS.StrongEps.Quad :=
    (Work.FTS.StrongEps.contDiff_bump 0).continuous.continuousOn.mul (continuousOn_epsW_quad α)
  have h1 := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  rwa [Measure.prod_restrict] at h1

/-- The a.e. strong measurability of the weighted profile `h · epsW α` follows from the
`C^∞`-on-the-open-quadrant regularity class `SmoothOpen h` of the chapter. -/
theorem aesm_mul_epsW_of_smoothOpen {α : ℝ} {h : ℝ → ℝ → ℝ}
    (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) Work.FTS.StrongEps.Quad :=
    ((hh.forall 0).continuousOn).mul (continuousOn_epsW_quad α)
  have h1 := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  rwa [Measure.prod_restrict] at h1

/-! ## The corrected statement -/

/-- **The corrected `EpsSq_sub_smul_bump`** (the requested statement is false: see the module
docstring).  The extra hypothesis is exactly the a.e. strong measurability of the weighted profile
`h · epsW α`, which `EpsMem α h` does *not* imply (it controls only its square). -/
theorem EpsSq_sub_smul_bump_of_aesm : ∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ (h : Work.FTS.Galerkin.Fn) (c : ℝ), Work.FTS.StrongEps.EpsMem α h →
      AEStronglyMeasurable (fun p : ℝ × ℝ => h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
        ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) →
      Work.FTS.StrongEps.EpsMem α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ)
        ≤ 2 * Work.FTS.StrongEps.EpsSq α h + B * c ^ 2 := by
  obtain ⟨K, hKpos, hB⟩ := BumpEpsSqBound
  refine ⟨2 * K, by linarith, ?_⟩
  intro α hα h c hh hAESM
  obtain ⟨hbumpmem, hbumpSq⟩ := hB α hα
  have hFint : Integrable (fun p : ℝ × ℝ => (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hh
  have hGint : Integrable (fun p : ℝ × ℝ =>
      (Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hbumpmem
  have hDle : ∀ p : ℝ × ℝ,
      ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2) * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
        ≤ 2 * (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
          + 2 * c ^ 2 * (Work.FTS.StrongEps.bump p.1 p.2
              * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 := by
    intro p
    nlinarith [sq_nonneg ((h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
        + c * (Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2))]
  have hBigint : Integrable (fun p : ℝ × ℝ =>
      2 * (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
        + 2 * c ^ 2 * (Work.FTS.StrongEps.bump p.1 p.2
            * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    (hFint.const_mul 2).add (hGint.const_mul (2 * c ^ 2))
  have hGE : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    aesm_bump_mul_epsW α
  have hDaesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2) * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    have h1 : (fun p : ℝ × ℝ => ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2)
        * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        = fun p : ℝ × ℝ => (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2
            - c * (Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)) ^ 2 := by
      funext p; ring
    rw [h1]
    exact (hAESM.sub (hGE.const_mul c)).pow 2
  have hDint : Integrable (fun p : ℝ × ℝ =>
      ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2) * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    Integrable.mono' hBigint hDaesm (Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hDle p))
  have hEsq : ∀ {f : ℝ → ℝ → ℝ}, Work.FTS.StrongEps.EpsMem α f →
      Work.FTS.StrongEps.EpsSq α f
        = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
            (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 := by
    intro f hf
    rw [Work.FTS.StrongEps.EpsSq]
    exact (MeasureTheory.setIntegral_prod _ hf).symm
  refine ⟨hDint, ?_⟩
  have hmono := MeasureTheory.integral_mono hDint hBigint hDle
  have h2 : (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        2 * (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
          + 2 * c ^ 2 * (Work.FTS.StrongEps.bump p.1 p.2
              * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      = 2 * Work.FTS.StrongEps.EpsSq α h
        + 2 * c ^ 2 * Work.FTS.StrongEps.EpsSq α Work.FTS.StrongEps.bump := by
    rw [MeasureTheory.integral_add (hFint.const_mul 2) (hGint.const_mul (2 * c ^ 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      ← hEsq hh, ← hEsq hbumpmem]
  calc Work.FTS.StrongEps.EpsSq α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ)
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2)
            * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 := hEsq hDint
    _ ≤ _ := hmono
    _ = 2 * Work.FTS.StrongEps.EpsSq α h
        + 2 * c ^ 2 * Work.FTS.StrongEps.EpsSq α Work.FTS.StrongEps.bump := h2
    _ ≤ 2 * Work.FTS.StrongEps.EpsSq α h + (2 * K) * c ^ 2 := by
        have h3 := mul_le_mul_of_nonneg_left hbumpSq (by positivity : (0 : ℝ) ≤ 2 * c ^ 2)
        linarith

/-- **The corrected `EpsSq_sub_smul_bump`, in the regularity class of the chapter**: for
`SmoothOpen h` (which is the case in every intended application, e.g. `h = f - g` with `f`, `g`
`SmoothOpen`) the a.e. measurability hypothesis is automatic. -/
theorem EpsSq_sub_smul_bump_of_smoothOpen : ∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ (h : Work.FTS.Galerkin.Fn) (c : ℝ), Work.FTS.EllipticEst.SmoothOpen h →
      Work.FTS.StrongEps.EpsMem α h →
      Work.FTS.StrongEps.EpsMem α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ)
        ≤ 2 * Work.FTS.StrongEps.EpsSq α h + B * c ^ 2 := by
  obtain ⟨B, hBpos, hB⟩ := EpsSq_sub_smul_bump_of_aesm
  exact ⟨B, hBpos, fun α hα h c hsm hmem =>
    hB α hα h c hmem (aesm_mul_epsW_of_smoothOpen hsm)⟩



/-! ## The formal refutation of the requested statement -/


end Work.FTS.StrongEps.EpsSqTools
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## The product-measure form of the memberships -/

/-- The product of the two restricted measures is the restriction of the volume to the domain. -/
theorem prodRestrict_eq (s t : Set ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (s ×ˢ t)
      = (volume.restrict s).prod (volume.restrict t) := by
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]

/-- `EpsMem` as integrability for the product measure on the domain. -/
theorem EpsMem_iff_integrable {α : ℝ} {f : ℝ → ℝ → ℝ} :
    EpsMem α f ↔ MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  rw [EpsMem, MeasureTheory.IntegrableOn, prodRestrict_eq Work.Spaces.Iz Work.Spaces.Iθ]

/-- Almost-everywhere strong measurability of the weighted profile on the domain. -/
abbrev AK (α : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 * epsW α p.1 p.2)
    ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))

theorem AK_add {α : ℝ} {f g : ℝ → ℝ → ℝ} (hf : AK α f) (hg : AK α g) :
    AK α (fun z θ => f z θ + g z θ) := by
  have h : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 * epsW α p.1 p.2
      + g p.1 p.2 * epsW α p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    AEStronglyMeasurable.add hf hg
  refine h.congr ?_
  filter_upwards with p
  ring

theorem AK_neg {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : AK α f) : AK α (fun z θ => -f z θ) := by
  have h : AEStronglyMeasurable (fun p : ℝ × ℝ => -(f p.1 p.2 * epsW α p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    AEStronglyMeasurable.neg hf
  refine h.congr ?_
  filter_upwards with p
  ring





/-! ## Membership under domination -/


theorem EpsMem_ext {α : ℝ} {f g : ℝ → ℝ → ℝ} (h : ∀ z θ, f z θ = g z θ)
    (hf : EpsMem α f) : EpsMem α g := by
  rw [EpsMem] at hf ⊢
  refine hf.congr ?_
  filter_upwards with p
  rw [h p.1 p.2]


theorem EpsMem_neg {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : EpsMem α f) :
    EpsMem α (fun z θ => -f z θ) := by
  rw [EpsMem] at hf ⊢
  refine hf.congr ?_
  filter_upwards with p
  ring

theorem EpsMem_add {α : ℝ} {f g : ℝ → ℝ → ℝ} (hakf : AK α f) (hakg : AK α g)
    (hf : EpsMem α f) (hg : EpsMem α g) :
    EpsMem α (fun z θ => f z θ + g z θ) := by
  refine (EpsMem_iff_integrable (α := α)).mpr ?_
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ((f p.1 p.2 + g p.1 p.2) * epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    AEStronglyMeasurable.pow (AK_add hakf hakg) 2
  have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      2 * (f p.1 p.2 * epsW α p.1 p.2) ^ 2 + 2 * (g p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (((EpsMem_iff_integrable (α := α)).mp hf).const_mul 2).add
      (((EpsMem_iff_integrable (α := α)).mp hg).const_mul 2)
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  · filter_upwards with p
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h : ((f p.1 p.2 + g p.1 p.2) * epsW α p.1 p.2) ^ 2
        = (f p.1 p.2 * epsW α p.1 p.2 + g p.1 p.2 * epsW α p.1 p.2) ^ 2 := by ring
    rw [h]
    nlinarith [sq_nonneg (f p.1 p.2 * epsW α p.1 p.2),
      sq_nonneg (g p.1 p.2 * epsW α p.1 p.2),
      sq_nonneg (f p.1 p.2 * epsW α p.1 p.2 + g p.1 p.2 * epsW α p.1 p.2),
      sq_nonneg (f p.1 p.2 * epsW α p.1 p.2 - g p.1 p.2 * epsW α p.1 p.2)]

theorem EpsMem_sub {α : ℝ} {f g : ℝ → ℝ → ℝ} (hakf : AK α f) (hakg : AK α g)
    (hf : EpsMem α f) (hg : EpsMem α g) :
    EpsMem α (fun z θ => f z θ - g z θ) :=
  EpsMem_ext (fun _ _ => (sub_eq_add_neg _ _).symm)
    (EpsMem_add hakf (AK_neg hakg) hf (EpsMem_neg hg))




theorem EpsSq_add_le_of_mem {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : EpsMem α f) (hg : EpsMem α g) :
    EpsSq α (fun z θ => f z θ + g z θ) ≤ 2 * EpsSq α f + 2 * EpsSq α g := by
  have hfp := (EpsMem_iff_integrable (α := α)).mp hf
  have hgp := (EpsMem_iff_integrable (α := α)).mp hg
  have hslicef := hfp.prod_right_ae
  have hsliceg := hgp.prod_right_ae
  have hBf : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    refine (hfp.integral_prod_left).congr ?_
    filter_upwards with z
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with θ
    rfl
  have hBg : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    refine (hgp.integral_prod_left).congr ?_
    filter_upwards with z
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with θ
    rfl
  have hsum : MeasureTheory.Integrable
      (fun z => 2 * (∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2)
        + 2 * (∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2))
      (volume.restrict Work.Spaces.Iz) :=
    (hBf.const_mul 2).add (hBg.const_mul 2)
  have hae : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, ((f z θ + g z θ) * epsW α z θ) ^ 2)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2)
          + 2 * (∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2) := by
    filter_upwards [hslicef, hsliceg] with z hzf hzg
    have hmaj : MeasureTheory.Integrable
        (fun θ => 2 * (f z θ * epsW α z θ) ^ 2 + 2 * (g z θ * epsW α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (hzf.const_mul 2).add (hzg.const_mul 2)
    have h1 : (∫ θ in Work.Spaces.Iθ, ((f z θ + g z θ) * epsW α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ,
            (2 * (f z θ * epsW α z θ) ^ 2 + 2 * (g z θ * epsW α z θ) ^ 2) := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => sq_nonneg _) hmaj ?_
      filter_upwards with θ
      nlinarith [sq_nonneg (f z θ * epsW α z θ), sq_nonneg (g z θ * epsW α z θ),
        sq_nonneg (f z θ * epsW α z θ + g z θ * epsW α z θ),
        sq_nonneg (f z θ * epsW α z θ - g z θ * epsW α z θ)]
    rw [MeasureTheory.integral_add (hzf.const_mul 2) (hzg.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at h1
    exact h1
  calc EpsSq α (fun z θ => f z θ + g z θ)
      = ∫ z in Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ, ((f z θ + g z θ) * epsW α z θ) ^ 2) := rfl
    _ ≤ ∫ z in Work.Spaces.Iz,
          (2 * (∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2)
            + 2 * (∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2)) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z =>
            MeasureTheory.integral_nonneg fun θ => sq_nonneg _) hsum hae
    _ = 2 * EpsSq α f + 2 * EpsSq α g := by
        rw [MeasureTheory.integral_add (hBf.const_mul 2) (hBg.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
        rfl

/-! ## The master domination lemma -/


/-! ## The angular profile times a radial function -/


/-! ## Versions restricted to the domain `Iz × Iθ` -/


theorem AK_of_uncurry {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    AK α f := by
  have he : AEStronglyMeasurable (fun p : ℝ × ℝ => epsW α p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (by simpa only [Work.FTS.StrongEps.Quad] using continuousOn_epsW_quad α)
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 * epsW α p.1 p.2) _ :=
    AEStronglyMeasurable.mul h he
  exact h2








end

end Work.FTS.StrongEps.EpsSqTools
end
