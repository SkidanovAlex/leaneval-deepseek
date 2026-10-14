import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.PkgK5.tracesK5
import Submission.Work.FTS.EllipticEst.HkNorm_Dz_le_open
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.bump_mixed_EpsSq_le
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyRight
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS.StrongPersist.SupOpenH2Z
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.slotAbsBound
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXB.l12dens_weighted_bound
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.uopSlotAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- `SmoothOpen` of a radial function `(z,θ) ↦ Λ z`, for a profile smooth on `(0,∞)`. -/
theorem smoothOpen_radial_slot {Λ : ℝ → ℝ}
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Λ z) := by
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllExist.sep_mul_open (g := Λ) (χ := fun _ : ℝ => (1 : ℝ)) hΛ
      contDiff_const) fun z θ _ _ _ => by ring

end Work.FTS.EllSol.EllPkgAux
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.uopTransferK5c_of_wall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Local helpers -/

/-- `SmoothOpen` of a radial function `(z,θ) ↦ Λ z`, for a profile smooth on `(0,∞)`. -/
theorem smoothOpen_radial_fts {Λ : ℝ → ℝ}
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Λ z) := by
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllExist.sep_mul_open (g := Λ) (χ := fun _ : ℝ => (1 : ℝ)) hΛ
      contDiff_const) fun z θ _ _ _ => by ring

/-- `SmoothOpen` is closed under multiplication by `z²`. -/
theorem smoothOpen_zsq_mul_fts {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * f z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 ^ 2) Work.FTS.EllipticEst.Q0 :=
    (contDiff_fst.pow 2).contDiffOn
  have h1 : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hf.forall n
  have h3 := h2.mul h1
  have hfun : (fun p : ℝ × ℝ => p.1 ^ 2 * Function.uncurry f p)
      = Function.uncurry (fun z θ => z ^ 2 * f z θ) := by
    funext p
    rfl
  rw [hfun] at h3
  exact h3

/-! ## The target -/


end Work.FTS.EllSol.PkgK5
end
-- ===== merged: Submission.Work.FTS.EpsEngine.EpsSq_iter_limFam_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps.EpsLocalPStar (iter limFam)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem EpsSq_iter_limFam_le {α q δ : ℝ} {F : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hconv : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ z θ)
        Filter.atTop (nhds (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) τ z θ)))
    (hBK : ∀ M K : ℕ, 1 ≤ K → K ≤ M → ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ M) τ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ K) τ z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ M) τ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ K) τ z θ)
        ≤ q ^ (K + 1)) :
    ∀ N : ℕ, 1 ≤ N → ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) τ z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) τ z θ)
        ≤ q ^ N := by
  intro N hN τ hτ
  -- The Fatou step: the differences `slice (iter (m+N)) − slice (iter N)` converge a.e. to
  -- `slice (limFam) − slice (iter N)`, and all of them have `EpsSq ≤ q ^ (N+1)`.
  obtain ⟨hmemL, hsqL⟩ := EpsMem_and_EpsSq_le_of_ae_tendsto_mem (B := q ^ (N + 1))
    (pow_nonneg hq0 (N + 1))
    (A := fun m z θ => slice (iter F h₀ (m + N)) τ z θ - slice (iter F h₀ N) τ z θ)
    (Alim := fun z θ => slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ)
    (fun m => (hBK (m + N) N hN (Nat.le_add_left N m) τ hτ).1)
    (fun m => (hBK (m + N) N hN (Nat.le_add_left N m) τ hτ).2)
    (Work.FTS.StrongEps.EpsLocalPStar.ae_of_forall_open (fun z hz θ hθ0 hθ1 =>
      ((hconv τ hτ z θ hz hθ0 hθ1).comp (tendsto_add_atTop_nat N)).sub tendsto_const_nhds))
  -- `q ^ (N+1) ≤ q ^ N` for `0 ≤ q ≤ 1`.
  have hpow : q ^ (N + 1) ≤ q ^ N :=
    mul_le_of_le_one_right (pow_nonneg hq0 N) hq1.le
  refine ⟨?_, ?_⟩
  · -- `EpsMem` is invariant under negation, and the two differences are negatives of each other.
    refine Work.FTS.StrongEps.EpsLocalPStar.EpsMem_congr_ae
      (f := fun z θ => -(slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ)) ?_
      (Work.FTS.StrongEps.EpsLocalPStar.EpsMem_neg2 hmemL)
    filter_upwards with p
    ring
  · -- `EpsSq` is invariant under swapping the two entries of a difference.
    rw [Work.FTS.StrongEps.EpsLocalPStar.EpsSq_sub_comm]
    exact le_trans hsqL hpow

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.EpsEngine.VolterraV4Iter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsLocalPStar

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The a priori bounds for the Picard iterates (iterate-indexed hypotheses) -/

/-- A difference of two Picard iterates is the parametric integral of the difference of the
right-hand sides. -/
theorem diff_eq_integral_v4 {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} {δ : ℝ}
    (hP : ∀ n τ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ))
    (hcontIter : ∀ n : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s => F (slice (iter F h₀ n) s) z θ) (Set.Icc 0 δ))
    {N₁ N₂ : ℕ} {τ z θ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) (h1 : 1 ≤ N₁) (h2 : 1 ≤ N₂)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    slice (iter F h₀ N₁) τ z θ - slice (iter F h₀ N₂) τ z θ
      = ∫ s in (0 : ℝ)..τ,
          (F (slice (iter F h₀ (N₁ - 1)) s) z θ - F (slice (iter F h₀ (N₂ - 1)) s) z θ) := by
  have hint : ∀ k : ℕ, IntervalIntegrable (fun s => F (slice (iter F h₀ k) s) z θ) volume 0 τ :=
    fun k => ContinuousOn.intervalIntegrable_of_Icc hτ.1
      ((hcontIter k z θ hz hθ0 hθ1).mono
        (Set.Icc_subset_Icc_right hτ.2))
  obtain ⟨N₁', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N₁ ≠ 0)
  obtain ⟨N₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N₂ ≠ 0)
  rw [show N₁' + 1 - 1 = N₁' from by omega, show N₂' + 1 - 1 = N₂' from by omega]
  rw [iter_succ F h₀ N₁', iter_succ F h₀ N₂']
  simp only [Work.FTS.Galerkin.slice_apply]
  rw [intervalIntegral.integral_sub (hint N₁') (hint N₂')]
  ring

/-- The a priori bounds of the Picard iteration of the Volterra map: `P` is preserved, the
increments (`wseq`) and the differences of iterates are bounded in `EpsSq` by the geometric
sequence `q ^ (n+1)`, and they are bounded pointwise. -/
theorem iter_bounds_v4 {α : ℝ} {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} {Cpt L δ q r : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hδL : δ * Real.sqrt L < 1)
    (hq : q = δ ^ 2 * L) (hr : r = Real.sqrt q) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr0 : 0 ≤ r) (hrpow : ∀ n : ℕ, Real.sqrt (q ^ n) = r ^ n)
    (hCpt : 0 ≤ Cpt) (hP₀ : P h₀)
    (hbd : ∀ u : Fn, P u → EpsMem α (F u) ∧ EpsSq α (F u) ≤ L)
    (hlip : ∀ u v : Fn, P u → P v → EpsMem α (fun z θ => u z θ - v z θ) →
      EpsSq α (fun z θ => F u z θ - F v z θ) ≤ L * EpsSq α (fun z θ => u z θ - v z θ))
    (hpt : ∀ u v : Fn, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ| ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ)))
    (hcontP : ∀ u : Fn, P u → ContinuousOn (fun q : ℝ × ℝ => F u q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzeroP : ∀ u : Fn, P u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → F u q.1 q.2 = 0)
    (hkeepIter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      P (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ)) :
    (∀ n τ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ)) ∧
    (∀ M τ, τ ∈ Set.Icc 0 δ → 1 ≤ M →
      EpsMem α (fun z θ => slice (iter F h₀ M) τ z θ - h₀ z θ) ∧
      EpsSq α (fun z θ => slice (iter F h₀ M) τ z θ - h₀ z θ) ≤ q) ∧
    (∀ M K, 1 ≤ K → K ≤ M → ∀ τ ∈ Set.Icc 0 δ,
      EpsMem α (fun z θ => slice (iter F h₀ M) τ z θ - slice (iter F h₀ K) τ z θ) ∧
      EpsSq α (fun z θ => slice (iter F h₀ M) τ z θ - slice (iter F h₀ K) τ z θ)
        ≤ q ^ (K + 1)) ∧
    (∀ n τ, τ ∈ Set.Icc 0 δ → EpsSq α (wseq F h₀ n τ) ≤ q ^ (n + 1)) ∧
    (∀ n τ, τ ∈ Set.Icc 0 δ → 1 ≤ n → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |wseq F h₀ n τ z θ| ≤ δ * Cpt * r ^ n) := by
  have hδ0 : 0 ≤ δ := hδ.le
  have hL0 : 0 ≤ L := hL.le
  have hqdef : q = δ ^ 2 * L := hq
  -- ## 1. `P` is preserved along the iteration (the iterate-indexed hypothesis `hkeepIter`)
  have hP : ∀ n τ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ) := by
    intro n
    induction n with
    | zero =>
      intro τ _
      exact hP₀
    | succ m ih =>
      intro τ hτ
      exact hkeepIter m τ hτ
  -- ## 1'. continuity in the fake time and joint measurability of the Picard curves, *derived*
  -- from the class data (`IterContMeas.iter_cont_meas`)
  obtain ⟨hcontIter, hmeasIter⟩ :=
    iter_cont_meas (α := α) (Cpt := Cpt) (L := L) (δ := δ) (F := F) (h₀ := h₀) (P := P)
      hδ hL0 hCpt hP hcontP hzeroP hbd hpt
  have hrestr : ∀ τ ∈ Set.Icc 0 δ,
      (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) ≤
        (MeasureTheory.volume.restrict (Set.Icc 0 δ)) :=
    fun τ hτ => restrict_uIoc_le_Icc hτ
  -- ## 2. a.e. sections of jointly measurable families are `AK2`
  have hAKsec : ∀ n : ℕ, ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc 0 δ)),
      AK2 α (F (slice (iter F h₀ n) s)) :=
    fun n => AK2_sections_restrict (hmeasIter n)
  -- ## 3. a difference of two iterates is a parametric integral of the `F`-difference
  have hdiff_eq : ∀ (N₁ N₂ : ℕ) (τ z θ : ℝ), τ ∈ Set.Icc 0 δ → 1 ≤ N₁ → 1 ≤ N₂ →
      0 < z → 0 < θ → θ < Real.pi / 2 →
      slice (iter F h₀ N₁) τ z θ - slice (iter F h₀ N₂) τ z θ
        = ∫ s in (0 : ℝ)..τ,
            (F (slice (iter F h₀ (N₁ - 1)) s) z θ - F (slice (iter F h₀ (N₂ - 1)) s) z θ) := by
    intro N₁ N₂ τ z θ hτ h1 h2 hz hθ0 hθ1
    have hint : ∀ k : ℕ, IntervalIntegrable (fun s => F (slice (iter F h₀ k) s) z θ) volume 0 τ :=
      fun k => ContinuousOn.intervalIntegrable_of_Icc hτ.1
        ((hcontIter k z θ hz hθ0 hθ1).mono
          (Set.Icc_subset_Icc_right hτ.2))
    obtain ⟨N₁', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N₁ ≠ 0)
    obtain ⟨N₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N₂ ≠ 0)
    rw [show N₁' + 1 - 1 = N₁' from by omega, show N₂' + 1 - 1 = N₂' from by omega]
    rw [iter_succ F h₀ N₁', iter_succ F h₀ N₂']
    simp only [Work.FTS.Galerkin.slice_apply]
    rw [intervalIntegral.integral_sub (hint N₁') (hint N₂')]
    ring
  -- ## 4. a priori bounds for the iterates
  have hBmain : ∀ M : ℕ,
      (∀ τ ∈ Set.Icc 0 δ, 1 ≤ M →
        EpsMem α (fun z θ => slice (iter F h₀ M) τ z θ - h₀ z θ) ∧
        EpsSq α (fun z θ => slice (iter F h₀ M) τ z θ - h₀ z θ) ≤ q) ∧
      (∀ K : ℕ, 1 ≤ K → K ≤ M → ∀ τ ∈ Set.Icc 0 δ,
        EpsMem α (fun z θ => slice (iter F h₀ M) τ z θ - slice (iter F h₀ K) τ z θ) ∧
        EpsSq α (fun z θ => slice (iter F h₀ M) τ z θ - slice (iter F h₀ K) τ z θ)
          ≤ q ^ (K + 1)) := by
    intro M
    induction M with
    | zero =>
      exact ⟨fun τ hτ h1 => absurd h1 (by omega),
        fun K hK hKM τ hτ => absurd hKM (by omega)⟩
    | succ M ih =>
      obtain ⟨ih0, ihK⟩ := ih
      refine ⟨?_, ?_⟩
      · -- (i) the `h₀`-difference
        intro τ hτ _
        have hdiff : (fun z θ => slice (iter F h₀ (M + 1)) τ z θ - h₀ z θ)
            = fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ M) s) z θ := by
          funext z θ
          show h₀ z θ + (∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ M) s) z θ) - h₀ z θ
            = ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ M) s) z θ
          ring
        rw [hdiff]
        have hm : MeasureTheory.AEStronglyMeasurable
            (fun p : ℝ × ℝ × ℝ =>
              F (slice (iter F h₀ M) p.1) p.2.1 p.2.2 * epsW α p.2.1 p.2.2)
            ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod DomM) :=
          aesm_weighted_uIoc_of_restrict (α := α) (Φ := fun s => F (slice (iter F h₀ M) s)) hτ (hmeasIter M)
        have hmono : (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) ≤
            (MeasureTheory.volume.restrict (Set.Icc 0 τ)) := by
          refine MeasureTheory.Measure.restrict_mono (s := Set.uIoc 0 τ)
            (s' := Set.Icc 0 τ) ?_ le_rfl
          rw [Set.uIoc_of_le hτ.1]
          exact Set.Ioc_subset_Icc_self
        have hb : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)),
            epsL2 α (F (slice (iter F h₀ M) s)) ≤ ENNReal.ofReal L := by
          refine (ae_mono hmono) ?_
          refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc ?_
          intro s hs
          exact epsL2_le_ofReal_of_mem (hbd _ (hP M s ⟨hs.1, le_trans hs.2 hτ.2⟩)).1
            (hbd _ (hP M s ⟨hs.1, le_trans hs.2 hτ.2⟩)).2
        obtain ⟨hmem, hbd'⟩ :=
          Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le (α := α) (τ := τ) (B := L)
            hτ.1 hL0 hm hb
        exact ⟨hmem, le_trans hbd' (by
          rw [hqdef]
          have h1 : τ * τ ≤ δ ^ 2 := by nlinarith [hτ.1, hτ.2]
          have h2 : τ * (τ * L) = τ * τ * L := by ring
          rw [h2]
          exact mul_le_mul_of_nonneg_right h1 hL0)⟩
      · -- (ii) the differences of two iterates
        intro K hK hKM τ hτ
        rcases eq_or_lt_of_le hKM with hEq | hLt
        · -- K = M+1: the difference vanishes
          subst hEq
          have hz : (fun z θ => slice (iter F h₀ (M + 1)) τ z θ - slice (iter F h₀ (M + 1)) τ z θ)
              = fun _ _ => (0 : ℝ) := by funext z θ; ring
          rw [hz]
          exact ⟨EpsMem_zero2 α, by rw [EpsSq_zero]; exact pow_nonneg hq0 _⟩
        · have hKM' : K ≤ M := Nat.lt_succ_iff.mp hLt
          have heq : ∀ᵐ p ∂DomM,
              (slice (iter F h₀ (M + 1)) τ p.1 p.2 - slice (iter F h₀ K) τ p.1 p.2)
              = ∫ s in (0 : ℝ)..τ,
                  (F (slice (iter F h₀ M) s) p.1 p.2
                    - F (slice (iter F h₀ (K - 1)) s) p.1 p.2) :=
            ae_of_forall_open (fun z hz θ hθ0 hθ1 =>
              hdiff_eq (M + 1) K τ z θ hτ (by omega) hK hz hθ0 hθ1)
          have hm : MeasureTheory.AEStronglyMeasurable
              (fun p : ℝ × ℝ × ℝ =>
                (F (slice (iter F h₀ M) p.1) p.2.1 p.2.2
                  - F (slice (iter F h₀ (K - 1)) p.1) p.2.1 p.2.2) * epsW α p.2.1 p.2.2)
              ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod DomM) := by
            have h1 := aesm_weighted_uIoc_of_restrict (α := α) (Φ := fun s => F (slice (iter F h₀ M) s)) hτ (hmeasIter M)
            have h2 := aesm_weighted_uIoc_of_restrict (α := α) (Φ := fun s => F (slice (iter F h₀ (K - 1)) s)) hτ (hmeasIter (K - 1))
            exact (h1.sub h2).congr (by filter_upwards with p; simp only [Pi.sub_apply]; ring)
          have hb : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)),
              epsL2 α (fun z θ => F (slice (iter F h₀ M) s) z θ
                - F (slice (iter F h₀ (K - 1)) s) z θ) ≤ ENNReal.ofReal (L * q ^ K) := by
            have hsec : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)),
                AK2 α (F (slice (iter F h₀ M) s)) ∧ AK2 α (F (slice (iter F h₀ (K - 1)) s)) :=
              (ae_mono (hrestr τ hτ)) ((hAKsec M).and (hAKsec (K - 1)))
            filter_upwards [hsec, MeasureTheory.ae_restrict_mem measurableSet_uIoc]
              with s hAKs hs
            have hsIcc : s ∈ Set.Icc 0 δ := by
              rw [Set.uIoc_of_le hτ.1] at hs
              exact ⟨le_of_lt hs.1, le_trans hs.2 hτ.2⟩
            have hmemD : EpsMem α (fun z θ => slice (iter F h₀ M) s z θ
                - slice (iter F h₀ (K - 1)) s z θ) := by
              rcases eq_or_lt_of_le hK with hK1 | hK2
              · subst hK1
                have := (ih0 s hsIcc (by omega : 1 ≤ M)).1
                simpa using this
              · exact (ihK (K - 1) (by omega) (by omega) s hsIcc).1
            have hsqD : EpsSq α (fun z θ => slice (iter F h₀ M) s z θ
                - slice (iter F h₀ (K - 1)) s z θ) ≤ q ^ K := by
              rcases eq_or_lt_of_le hK with hK1 | hK2
              · subst hK1
                have := (ih0 s hsIcc (by omega : 1 ≤ M)).2
                simpa using this
              · have h := (ihK (K - 1) (by omega) (by omega) s hsIcc).2
                rwa [Nat.sub_add_cancel hK] at h
            have hmemG : EpsMem α (fun z θ => F (slice (iter F h₀ M) s) z θ
                - F (slice (iter F h₀ (K - 1)) s) z θ) :=
              EpsMem_sub2 hAKs.1 hAKs.2 (hbd _ (hP M s hsIcc)).1 (hbd _ (hP (K - 1) s hsIcc)).1
            have hsqG : EpsSq α (fun z θ => F (slice (iter F h₀ M) s) z θ
                - F (slice (iter F h₀ (K - 1)) s) z θ) ≤ L * q ^ K :=
              le_trans (hlip _ _ (hP M s hsIcc) (hP (K - 1) s hsIcc) hmemD)
                (mul_le_mul_of_nonneg_left hsqD hL0)
            exact epsL2_le_ofReal_of_mem hmemG hsqG
          obtain ⟨hmemI, hbdI⟩ :=
            Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le (α := α) (τ := τ) (B := L * q ^ K)
              hτ.1 (mul_nonneg hL0 (pow_nonneg hq0 K)) hm hb
          refine ⟨EpsMem_congr_ae (heq.mono fun p hp => hp.symm) hmemI, ?_⟩
          have hEps : EpsSq α (fun z θ => slice (iter F h₀ (M + 1)) τ z θ - slice (iter F h₀ K) τ z θ)
              = EpsSq α (fun z θ => ∫ s in (0 : ℝ)..τ,
                  (F (slice (iter F h₀ M) s) z θ - F (slice (iter F h₀ (K - 1)) s) z θ)) :=
            EpsSq_congr_ae heq
          rw [hEps]
          refine le_trans hbdI ?_
          calc τ * (τ * (L * q ^ K)) = τ * τ * (L * q ^ K) := by ring
            _ ≤ δ ^ 2 * (L * q ^ K) :=
                mul_le_mul_of_nonneg_right (by nlinarith [hτ.1, hτ.2])
                  (mul_nonneg hL0 (pow_nonneg hq0 K))
            _ = q ^ (K + 1) := by
                rw [show δ ^ 2 * (L * q ^ K) = q * q ^ K by rw [hqdef]; ring, pow_succ']
  -- ## 5. the increments are bounded
  have hwsq : ∀ n τ, τ ∈ Set.Icc 0 δ → EpsSq α (wseq F h₀ n τ) ≤ q ^ (n + 1) := by
    intro n τ hτ
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h := (hBmain 1).1 τ hτ (le_refl 1)
      show EpsSq α (fun z θ => slice (iter F h₀ 1) τ z θ - h₀ z θ) ≤ q ^ (0 + 1)
      rw [pow_one]
      exact h.2
    · have h := (hBmain (n + 1)).2 n hn (by omega) τ hτ
      show EpsSq α (fun z θ => slice (iter F h₀ (n + 1)) τ z θ - slice (iter F h₀ n) τ z θ)
        ≤ q ^ (n + 1)
      exact h.2
  have hwpt : ∀ n τ, τ ∈ Set.Icc 0 δ → 1 ≤ n → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |wseq F h₀ n τ z θ| ≤ δ * Cpt * r ^ n := by
    intro n τ hτ hn z θ hz hθ0 hθ1
    have hint : ∀ k : ℕ,
        IntervalIntegrable (fun s => F (slice (iter F h₀ k) s) z θ) volume 0 τ :=
      fun k => ContinuousOn.intervalIntegrable_of_Icc hτ.1
        ((hcontIter k z θ hz hθ0 hθ1).mono
          (Set.Icc_subset_Icc_right hτ.2))
    have hiter : wseq F h₀ n τ z θ
        = ∫ s in (0 : ℝ)..τ,
            (F (slice (iter F h₀ n) s) z θ - F (slice (iter F h₀ (n - 1)) s) z θ) := by
      obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have h1 : slice (iter F h₀ (n' + 1 + 1)) τ z θ
          = h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ (n' + 1)) s) z θ := by
        rw [iter_succ F h₀ (n' + 1)]
        simp only [Work.FTS.Galerkin.slice_apply]
      have h2 : slice (iter F h₀ (n' + 1)) τ z θ
          = h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n') s) z θ := by
        rw [iter_succ F h₀ n']
        simp only [Work.FTS.Galerkin.slice_apply]
      have h3 : n' + 1 - 1 = n' := by omega
      show slice (iter F h₀ (n' + 1 + 1)) τ z θ - slice (iter F h₀ (n' + 1)) τ z θ = _
      rw [h3, h1, h2]
      rw [intervalIntegral.integral_sub (hint (n' + 1)) (hint n')]
      ring
    rw [hiter, ← Real.norm_eq_abs]
    have h2 : ∀ s ∈ Set.uIoc (0 : ℝ) τ,
        ‖F (slice (iter F h₀ n) s) z θ - F (slice (iter F h₀ (n - 1)) s) z θ‖ ≤ Cpt * r ^ n := by
      intro s hs
      rw [Real.norm_eq_abs]
      have hsIcc : s ∈ Set.Icc 0 δ := by
        rw [Set.uIoc_of_le hτ.1] at hs
        exact ⟨le_of_lt hs.1, le_trans hs.2 hτ.2⟩
      have hwseq : wseq F h₀ (n - 1) s
          = fun z θ => slice (iter F h₀ n) s z θ - slice (iter F h₀ (n - 1)) s z θ := by
        funext z θ
        simp only [wseq, Nat.sub_add_cancel hn]
      have hsq : EpsSq α (fun z θ => slice (iter F h₀ n) s z θ
          - slice (iter F h₀ (n - 1)) s z θ) ≤ q ^ n := by
        have h := hwsq (n - 1) s hsIcc
        rw [Nat.sub_add_cancel hn] at h
        rwa [hwseq] at h
      calc |F (slice (iter F h₀ n) s) z θ - F (slice (iter F h₀ (n - 1)) s) z θ|
          ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => slice (iter F h₀ n) s z θ
              - slice (iter F h₀ (n - 1)) s z θ)) :=
            hpt _ _ (hP n s hsIcc) (hP (n - 1) s hsIcc) z θ hz hθ0 hθ1
        _ ≤ Cpt * r ^ n := by
            rw [← hrpow n]
            exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) hCpt
    have h3 := intervalIntegral.norm_integral_le_of_norm_le_const (C := Cpt * r ^ n)
      (a := (0 : ℝ)) (b := τ) h2
    rw [sub_zero, abs_of_nonneg hτ.1] at h3
    refine h3.trans ?_
    nlinarith [hτ.1, hτ.2, mul_nonneg hCpt (pow_nonneg hr0 n)]
  exact ⟨hP, (fun M τ hτ hM => (hBmain M).1 τ hτ hM),
    (fun M K hK hKM τ hτ => (hBmain M).2 K hK hKM τ hτ), hwsq, hwpt⟩

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.tendsto_slice_iter_limFam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open Filter

set_option autoImplicit false

/-- The Picard iterates converge pointwise to the limit family, as soon as the increments
`wseq F h₀ n` (`n ≥ 1`) are dominated by a geometric sequence.  The proof is the telescoping
of the increments: the partial sums `∑_{n<N} wseq F h₀ (n+1)` are the tail of the sum whose
total is the (absolutely convergent) series defining `limFam`. -/
theorem tendsto_slice_iter_limFam {F : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn} {δ Cpt r : ℝ}
    (hCpt : 0 ≤ Cpt) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hwpt : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → 1 ≤ n → ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ n τ z θ| ≤ δ * Cpt * r ^ n) :
    ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ z θ)
        Filter.atTop (nhds (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) τ z θ)) := by
  intro τ hτ z θ hz hθ0 hθ1
  -- the geometric majorant is nonnegative: take `max (δ*Cpt) 0` in place of `δ*Cpt`
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hgeo : Summable (fun n : ℕ => max (δ * Cpt) 0 * r ^ (n + 1)) := by
    have h := (summable_geometric_of_norm_lt_one hrnorm).mul_left (max (δ * Cpt) 0 * r)
    refine h.congr (fun n => ?_)
    rw [pow_succ']; ring
  have hbnd : ∀ n : ℕ, |Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ (n + 1) τ z θ|
      ≤ max (δ * Cpt) 0 * r ^ (n + 1) := by
    intro n
    refine le_trans (hwpt (n + 1) τ hτ (by omega) z θ hz hθ0 hθ1) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr0 _)
  have hsumm : Summable
      (fun n : ℕ => Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ (n + 1) τ z θ) :=
    Summable.of_norm_bounded hgeo fun n => by rw [Real.norm_eq_abs]; exact hbnd n
  have htsum : HasSum (fun n : ℕ => Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ (n + 1) τ z θ)
      (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ
        - (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ)) := by
    have h2 : Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ
        - (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ)
        = ∑' n, Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ (n + 1) τ z θ := by
      simp only [Work.FTS.StrongEps.EpsLocalPStar.limFam]
      ring
    rw [h2]
    exact hsumm.hasSum
  have h1 := htsum.tendsto_sum_nat
  have h3 : Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.range N,
          Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ (n + 1) τ z θ)
        + (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ))
      Filter.atTop (nhds (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ)) := by
    have h := h1.add_const (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ)
    have h4 : (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ
        - (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ))
        + (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ)
        = Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ := by ring
    rw [h4] at h
    exact h
  have heq : (fun N : ℕ => (∑ n ∈ Finset.range N,
        Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ (n + 1) τ z θ)
      + (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ))
      =ᶠ[Filter.atTop] (fun N : ℕ => Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (N + 1)) τ z θ) := by
    filter_upwards with N
    rw [Work.FTS.StrongEps.EpsLocalPStar.sum_wseq_shift]
    ring
  have htend : Filter.Tendsto (fun N : ℕ => Work.FTS.Galerkin.slice
      (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (N + 1)) τ z θ) Filter.atTop
      (nhds (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ)) :=
    (Filter.tendsto_congr' heq).mp h3
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp htend

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.Open3.Defs3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Open3

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.VocabO2
open Work.FTS.Galerkin (Fn Fam slice galFun galField IsGalFam ConvLocUnif IsDynWeakOn
  IsDynEqOn RegPkg galFam gdot dynLin dynRHS Slab)

set_option autoImplicit false

/-! ## The elliptic law for the corrected boundary conditions -/

/-- `IsBslSolPos α F Ψ`: the elliptic equation `bslOp α Ψ = F` on the **open** quadrant and the
boundary conditions only for `z ≥ 0`.  This is the (corrected) elliptic law `Law` of the chain:
`Work.Elliptic.IsBslSol` asks `Ψ z 0 = 0` for all real `z`, which the modulated solution on the
closed quadrant does not satisfy. -/
def IsBslSolPos (α : ℝ) (F Ψ : Fn) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
    (∀ z, 0 ≤ z → Ψ z 0 = 0) ∧ (∀ z, 0 ≤ z → Ψ z (π / 2) = 0) ∧
    (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0))

/-! ## The extra regularity of the two sides of the equation -/


/-! ## The corrected hypotheses of the limit passage -/




/-! ## The corrected field conditions, on the Euclidean ball -/

/-- The **Euclidean ball** of radius `r` in `Fin n → ℝ`: `EBall n r = {c | ∑ cₖ² ≤ r²}`.  This is
the ball that the a-priori estimate `hCoeffBound` controls; the sup-norm ball of the same radius
(`Metric.closedBall 0 r`) contains it strictly and is the wrong hypothesis for the projected
field (design §4). -/
def EBall (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) := {c | ∑ k, c k ^ 2 ≤ r ^ 2}

/-- **`hField_lip'`**: the projected field is Lipschitz on the Euclidean ball `EBall n (2R)` with
constant `K n`. -/
def hField_lip' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
    LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ) (EBall n (2 * R))

/-- **`hField_bound'`**: the projected field is bounded on the Euclidean ball `EBall n (2R)`. -/
def hField_bound' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) (L : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (τ : ℝ) (c : Fin n → ℝ), 0 ≤ τ → c ∈ EBall n (2 * R) →
    ‖galField α (IP α) φ n (PsiCan Φs EllSol) τ c‖ ≤ L n

/-- **`hField_cont'`**: the projected field is continuous in the fake time on the Euclidean ball
`EBall n (2R)`. -/
def hField_cont' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℝ), c ∈ EBall n (2 * R) →
    ContinuousOn (fun τ => galField α (IP α) φ n (PsiCan Φs EllSol) τ c) (Set.Ici 0)

/-! ## The corrected bilinearity class of the pairing -/



/-! ## The density classes of the corrected Galerkin basis -/



/-! ## The corrected determination of the equation by its weak form -/


end Work.FTS.Open3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsConvRat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false
open Work.FTS.Galerkin (Fn Fam slice)

/-- Uniform convergence survives reindexing by a map tending to infinity. -/
theorem tendstoUniformlyOn_comp_index {X β : Type*} [UniformSpace β] {F : ℕ → X → β}
    {f : X → β} {s : Set X} (h : TendstoUniformlyOn F f atTop s) {A : ℕ → ℕ}
    (hA : Tendsto A atTop atTop) : TendstoUniformlyOn (F ∘ A) f atTop s :=
  fun u hu => hA.eventually (h u hu)


/-- The convergence package `ConvLocUnifH6` survives reindexing by a map tending to infinity. -/
theorem ConvLocUnifH6.comp_index {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLocUnifH6 α B G f)
    {A : ℕ → ℕ} (hA : Tendsto A atTop atTop) : ConvLocUnifH6 α B (G ∘ A) f :=
  ⟨fun K hK hKQ j i hji => tendstoUniformlyOn_comp_index (h.1 K hK hKQ j i hji) hA, h.2⟩

/-- The convergence package `ConvLocUnifH6` survives an eventual change of the sequence of
profiles. -/
theorem ConvLocUnifH6.congr_ae {α B : ℝ} {G G' : ℕ → Fn} {f : Fn} (h : ConvLocUnifH6 α B G f)
    (hGG : G =ᶠ[atTop] G') : ConvLocUnifH6 α B G' f :=
  ⟨fun K hK hKQ j i hji => (h.1 K hK hKQ j i hji).congr
      (hGG.mono (fun n hn => by intro p hp; simp only [hn])), h.2⟩

/-- **The diagonal extraction over the fake times.**  From a sequence of families `G n` with a
uniform `ℋ⁶`-bound at every `τ ∈ [0,T]` (and `C^∞`-regularity of every slice on the open quadrant)
there is a single strictly increasing `φ` and, at every *rational* `τ ∈ [0,T]`, a limit `f τ`
carrying the convergence package `ConvLocUnifH6` along `φ`. -/
theorem EpsConvRat {α B T : ℝ} (hα : 0 < α) {G : ℕ → Work.FTS.Galerkin.Fam}
    (hsm : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice (G n) τ))
    (hb : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice (G n) τ) ≤ B) :
    ∃ (φ : ℕ → ℕ) (f : ℝ → Work.FTS.Galerkin.Fn), StrictMono φ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T ∩ Set.range (fun q : ℚ => (q : ℝ)),
        Work.FTS.StrongEps.ConvLocUnifH6 α B
          (fun n => Work.FTS.Galerkin.slice (G (φ n)) τ) (f τ) := by
  classical
  -- an enumeration of the rationals
  obtain ⟨e, he⟩ := exists_surjective_nat ℚ
  -- the extraction at level `k`, with its two components bundled
  let hw : ∀ (k : ℕ) (ψ : ℕ → ℕ), ((e k : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T →
      ∃ (p : (ℕ → ℕ) × Fn), StrictMono p.1 ∧
        ConvLocUnifH6 α B (fun n => slice (G (ψ (p.1 n))) ((e k : ℚ) : ℝ)) p.2 := by
    intro k ψ h
    obtain ⟨φ0, f0, hφ0, hc0⟩ := EpsConvSubseq (α := α) (B := B) hα
      (G := fun n => slice (G (ψ n)) ((e k : ℚ) : ℝ))
      (fun n l => hsm (ψ n) ((e k : ℚ) : ℝ) h l)
      (fun n => hmem (ψ n) ((e k : ℚ) : ℝ) h)
      (fun n => hb (ψ n) ((e k : ℚ) : ℝ) h)
    exact ⟨(φ0, f0), hφ0, hc0⟩
  let step : ℕ → (ℕ → ℕ) → (ℕ → ℕ) × Fn := fun k ψ =>
    if h : ((e k : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T then Classical.choose (hw k ψ h) else (id, 0)
  let S : ℕ → (ℕ → ℕ) → (ℕ → ℕ) := fun k ψ => (step k ψ).1
  let L : ℕ → (ℕ → ℕ) → Fn := fun k ψ => (step k ψ).2
  have hStep : ∀ k ψ (h : ((e k : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T),
      StrictMono (S k ψ) ∧
      ConvLocUnifH6 α B (fun n => slice (G (ψ (S k ψ n))) ((e k : ℚ) : ℝ)) (L k ψ) := by
    intro k ψ h
    have heq : step k ψ = Classical.choose (hw k ψ h) := by
      simp only [step]; rw [dite_eq_left h]
    simp only [show S k ψ = (step k ψ).1 from rfl, show L k ψ = (step k ψ).2 from rfl, heq]
    exact Classical.choose_spec (hw k ψ h)
  have hSmono : ∀ k ψ, StrictMono (S k ψ) := by
    intro k ψ
    by_cases h : ((e k : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T
    · exact (hStep k ψ h).1
    · have heq : step k ψ = (id, (0 : Fn)) := by simp only [step]; rw [dite_eq_right h]
      rw [show S k ψ = (step k ψ).1 from rfl, heq]
      exact strictMono_id
  -- the composite subsequence at level `k` and the diagonal
  let W : ℕ → (ℕ → ℕ) := Nat.rec id (fun k Wk => Wk ∘ S k Wk)
  have hWsucc : ∀ k, W (k + 1) = W k ∘ S k (W k) := fun k => rfl
  have hWapply : ∀ k n, W (k + 1) n = W k (S k (W k) n) := fun k n => congrFun (hWsucc k) n
  have hWmono : ∀ k, StrictMono (W k) := by
    intro k
    induction k with
    | zero => exact strictMono_id
    | succ k ih => rw [hWsucc k]; exact ih.comp (hSmono k (W k))
  -- the `n`-th iterate of the steps from level `k` on
  let E : ℕ → ℕ → (ℕ → ℕ) := fun k =>
    Nat.rec id (fun n En => if n + 1 ≤ k then id else En ∘ S n (W n))
  have hEsucc : ∀ k n, E k (n + 1) = if n + 1 ≤ k then id else E k n ∘ S n (W n) :=
    fun k n => rfl
  have hEself : ∀ k, E k k = id := by
    intro k
    cases k with
    | zero => rfl
    | succ m => rw [hEsucc (m + 1) m, ite_eq_left (le_refl (m + 1))]
  have hWmult : ∀ k n, k ≤ n → W n = W k ∘ E k n := by
    intro k
    refine Nat.le_induction ?_ ?_
    · rw [hEself k, Function.comp_id]
    · intro n hkn ih
      rw [hWsucc n, hEsucc k n, ite_eq_right (by omega), ← Function.comp_assoc, ih]
  have hEge : ∀ k n m, m ≤ E k n m := by
    intro k n
    induction n with
    | zero => intro m; rw [show E k 0 = id from rfl]; exact le_rfl
    | succ n ih =>
      intro m
      rw [hEsucc]
      by_cases h : n + 1 ≤ k
      · rw [ite_eq_left h]; exact le_rfl
      · rw [ite_eq_right h, Function.comp_apply]
        exact le_trans ((hSmono n (W n)).id_le m) (ih (S n (W n) m))
  have hdiag : ∀ k n, k + 1 ≤ n → W n n = W (k + 1) (E (k + 1) n n) := by
    intro k n hn
    exact congrFun (hWmult (k + 1) n hn) n
  let φ : ℕ → ℕ := fun n => W n n
  have hφmono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ (fun n => ?_)
    show W (n + 1) (n + 1) > W n n
    rw [hWapply n (n + 1)]
    exact (hWmono n).lt_iff_lt.mpr
      (lt_of_lt_of_le (Nat.lt_succ_self n) ((hSmono n (W n)).id_le (n + 1)))
  -- the level-`k` convergence, re-indexed to `W (k+1)`
  have hconvW : ∀ k, ((e k : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T →
      ConvLocUnifH6 α B (fun m => slice (G (W (k + 1) m)) ((e k : ℚ) : ℝ)) (L k (W k)) := by
    intro k hk
    have h := (hStep k (W k) hk).2
    refine ⟨fun K hK hKQ j i hji => ?_, h.2.1, h.2.2⟩
    exact (h.1 K hK hKQ j i hji).congr (Filter.Eventually.of_forall (fun n => by
      intro p hp
      show Work.Spaces.mixed j i (slice (G (W k (S k (W k) n))) ((e k : ℚ) : ℝ)) p.1 p.2
        = Work.Spaces.mixed j i (slice (G (W (k + 1) n)) ((e k : ℚ) : ℝ)) p.1 p.2
      rw [hWapply k n]))
  -- the diagonal step: the tail of `φ` is a subsequence of the level-`k` extraction
  have hfinal : ∀ k, ((e k : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T →
      ConvLocUnifH6 α B (fun n => slice (G (W n n)) ((e k : ℚ) : ℝ)) (L k (W k)) := by
    intro k hk
    have hlevel := hconvW k hk
    have hA : Tendsto (fun n => E (k + 1) n n) atTop atTop :=
      tendsto_atTop_mono (fun n => hEge (k + 1) n n) tendsto_id
    have hcomp := hlevel.comp_index hA
    refine hcomp.congr_ae ?_
    filter_upwards [Filter.eventually_ge_atTop (k + 1)] with n hn
    simp only [Function.comp_apply]
    show slice (G (W (k + 1) (E (k + 1) n n))) ((e k : ℚ) : ℝ)
      = slice (G (W n n)) ((e k : ℚ) : ℝ)
    rw [hdiag k n hn]
  -- the limit at a real time: pick the rational `τ` and its index in the enumeration
  let kIdx : ℝ → ℕ := fun τ =>
    if h : ∃ k : ℕ, ((e k : ℚ) : ℝ) = τ then Classical.choose h else 0
  have hkIdx : ∀ τ, τ ∈ Set.range (fun q : ℚ => (q : ℝ)) → ((e (kIdx τ) : ℚ) : ℝ) = τ := by
    intro τ hτ
    obtain ⟨q, hq⟩ := hτ
    have hex : ∃ k : ℕ, ((e k : ℚ) : ℝ) = τ :=
      ⟨Classical.choose (he q), by rw [Classical.choose_spec (he q)]; exact hq⟩
    simp only [kIdx]
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  refine ⟨φ, fun τ => L (kIdx τ) (W (kIdx τ)), hφmono, ?_⟩
  intro τ hτ
  obtain ⟨hτI, hτQ⟩ := hτ
  have hk := hkIdx τ hτQ
  have hk' : ((e (kIdx τ) : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T := by rw [hk]; exact hτI
  have hres := hfinal (kIdx τ) hk'
  convert hres using 2
  rw [hk]

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.RegFromVolterraD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsE4Thr/RegFromVolterraD.lean` — OPEN LEAF-D `regFromVolterra'` (+ the `RegDataD` bundle)

curric-46 install 2026-10-12 (`cbc/fts_regularity_interface.md` §2 last bullet, §4.3; REVIEW (d),
F2).  TRUE.  The tree's `EpsE4Thr.RegFromVolterra` (PROVED) takes `hG`: `C¹` IN THE FAKE TIME of
`σ ↦ F (w_σ)`, which is NOT available for `F = Feps` with `E` unconstrained.  Its proof uses `hG`
only to obtain `hA`'s continuity and `hB` (via `RegSlab.continuousOn_sliceFderiv_slab`); so adapt
it: `∂_τ w = A` is continuous by `hAc`; `∂_y w = ∂_y h₀ + ∫ ∂_y A`, with local boundedness from `hB`
on the closed-`τ` slab (`RegSlab.hasFDerivAt_intervalIntegral_slab`,
`continuousOn_intervalIntegral_slab_normed`, `RXT0.slabC1Flat`).

`RegDataD F h₀ δ` bundles the three hypotheses (joint continuity of the integrand, per-slice `C¹`
in space, joint continuity of the spatial `fderiv`); its producer for `F = Feps` along the limit
family is LEAF-D2 `regData_of_xball` (`EpsE4Thr/RegDataOfXBall.lean`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R5

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false


/-- the weaker regularity data of the right-hand side along the limit curve (the three hypotheses
of `regFromVolterra'`). -/
def RegDataD (F : Fn → Fn) (h₀ : Fn) (δ : ℝ) : Prop :=
  ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) p.2.2) p.1 p.2.1)
    (Ioi 0 ×ˢ Ioo 0 (Real.pi / 2) ×ˢ Icc 0 δ) ∧
  (∀ σ ∈ Icc 0 δ, ContDiffOn ℝ 1 (Function.uncurry
      (F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) σ))) Work.FTS.EllipticEst.Q0) ∧
  ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      fderiv ℝ (Function.uncurry
        (F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) p.2.2))) (p.1, p.2.1))
    (Ioi 0 ×ˢ Ioo 0 (Real.pi / 2) ×ˢ Icc 0 δ)


end Work.FTS.StrongEps.EpsE4Thr.E4R5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.continuousOn_slice_fam_reorder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr


end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.BumpSlotFour =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open Work.FTS.StrongEps.EpsSqTools.LinAux

/-! ## The slotwise constants -/





/-! ## The target -/


end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS.TransportS.t2SlotGuarded =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS


end Work.FTS.TransportS
end
