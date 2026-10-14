import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassC.A2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The angular slices of a `ClassC` profile decay at `z → ∞`.**

`BdryTraces α 6 g` at `(a,b) = (0,0)` is `z·(g(z,θ)·w z)² → 0` at `+∞` for every `θ ∈ (0,π/2)`;
since `w z = (1+z)²/z² ≥ 1` and `z ≥ 1` on a neighbourhood of `+∞`, this forces `g(z,θ) → 0`.
At the two endpoints `θ = 0, π/2` the class field `norm` forces `g z θ = 0` identically. -/
theorem classC_tendsto_atTop {α : ℝ} {g : Fn} (h : ClassC α g) :
    ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => g z θ) atTop (𝓝 0) := by
  intro θ hθ
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h2 | h2
    · -- `θ` interior: the `BdryTraces` radial vanishing
      have hθI : θ ∈ Set.Ioo 0 (π / 2) := ⟨h0, h2⟩
      have hlimF : Tendsto (fun z => z * (g z θ * Work.Spaces.w z) ^ 2) atTop (𝓝 0) := by
        have h1 := (h.tr 0 0 (by norm_num)).1 θ hθI
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h1.2
      have hlimG : Tendsto (fun z => (g z θ) ^ 2) atTop (𝓝 0) := by
        refine squeeze_zero' ?_ ?_ hlimF
        · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
          exact sq_nonneg _
        · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
          have hw1 : 1 ≤ Work.Spaces.w z := by
            rw [Work.Spaces.w, one_le_div (by positivity)]
            nlinarith
          have hgnn : 0 ≤ (g z θ) ^ 2 := sq_nonneg _
          have h1 : (g z θ) ^ 2 ≤ (g z θ * Work.Spaces.w z) ^ 2 := by
            rw [mul_pow]
            calc (g z θ) ^ 2 = (g z θ) ^ 2 * 1 := by ring
              _ ≤ (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
                  mul_le_mul_of_nonneg_left (one_le_pow₀ hw1) hgnn
          have h2 : (g z θ * Work.Spaces.w z) ^ 2 ≤ z * (g z θ * Work.Spaces.w z) ^ 2 := by
            have := mul_le_mul_of_nonneg_right hz (sq_nonneg (g z θ * Work.Spaces.w z))
            simpa using this
          linarith
      have habs : Tendsto (fun z => |g z θ|) atTop (𝓝 0) := by
        have hsqrt : Tendsto (fun z => Real.sqrt ((g z θ) ^ 2)) atTop (𝓝 0) := by
          have hc := (Real.continuous_sqrt.tendsto 0).comp hlimG
          rw [Function.comp_def] at hc
          simpa using hc
        simpa only [Real.sqrt_sq_eq_abs] using hsqrt
      exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa using habs)
    · -- `θ = π/2`: `g` vanishes there by the class field `norm`
      subst h2
      have hz : ∀ z : ℝ, g z (π / 2) = 0 := by
        intro z
        have hthis := congr_fun (congr_fun h.norm z) (π / 2)
        rw [normTh_apply_of_not_mem
          (show (π / 2) ∉ Set.Ioo 0 (π / 2) from fun hc => absurd hc.2 (lt_irrefl _))] at hthis
        exact hthis.symm
      have : (fun z => g z (π / 2)) = fun _ : ℝ => (0 : ℝ) := funext hz
      rw [this]
      exact tendsto_const_nhds
  · -- `θ = 0`: `g` vanishes there by the class field `norm`
    subst h0
    have hz : ∀ z : ℝ, g z 0 = 0 := by
      intro z
      have hthis := congr_fun (congr_fun h.norm z) 0
      rw [normTh_apply_of_not_mem
        (show (0 : ℝ) ∉ Set.Ioo 0 (π / 2) from fun hc => absurd hc.1 (lt_irrefl _))] at hthis
      exact hthis.symm
    have : (fun z => g z 0) = fun _ : ℝ => (0 : ℝ) := funext hz
    rw [this]
    exact tendsto_const_nhds

/-- **The two first inputs of the repaired existence node** (smoothness of the orthogonalised
source, and its honesty at level `10 = 8 + 2`, the input level of
`EllExist.ellClassOk_exists_of_inputs_pp 8`), from the class fields (`mem10`, lead install
2026-10-11). -/
theorem classC_orthSource_inputs {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) (h : ClassC α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) ∧
    Work.Spaces.HkMem α 10 (Work.Elliptic.orthSource g) :=
  ⟨Work.FTS.EllExist.smoothOpen_orthSource_of_Fstar_smooth h.reg h.fsm,
    Work.FTS.EllExist.hkMem_orthSource_of_Fstar_smooth hα hα1 h.reg h.mem10 h.fsm⟩

/-- **The full elliptic input package of a `ClassC` profile, at level `8`.**

Assembles the five hypotheses of the level-`8` existence node from the class fields and the
auxiliary decay lemmas of the area. -/
theorem classC_ellInputs_full {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) (h : ClassC α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) ∧
    Work.Spaces.HkMem α 10 (Work.Elliptic.orthSource g) ∧
    (∀ θ ∈ Work.Spaces.Iθ,
      Tendsto (fun z => Work.Elliptic.orthSource g z θ) atTop (𝓝 0)) ∧
    (∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0)) ∧
    MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r) (Set.Ioi 0) := by
  have hFdec : Tendsto (fun z => Work.Elliptic.Fstar g z) atTop (𝓝 0) :=
    fstar_tendsto_atTop_zero_of_classC hα hα1 h.reg h.mem (classC_tendsto_atTop h)
  exact ⟨(classC_orthSource_inputs hα hα1 h).1, (classC_orthSource_inputs hα hα1 h).2,
    Work.FTS.EllExist.tendsto_orthSource_atTop_of (classC_tendsto_atTop h) hFdec,
    h.fsm,
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 8 g h.reg h.mem8⟩

/-- **A2: the level-`8` existence node on `ClassC`.**

Every profile of the linear class `C` has an elliptic stream function in `EllClassOk 8`.  The
level-`4` slots consume it through `ellClassOk_mono` (see `A4`/`Main`).

Lead install 2026-10-11: the node is the repaired `ellClassOk_exists_of_inputs_pp 8`
(input `HkMem α 10` of the orthogonalised source, from the class field `mem10`); the original
`ellClassOk_exists_of_inputs 8` rested on the false `PhiStar.bslOp_sol_exists 8`.

Lead install R6 2026-10-11 (`cbc/fts_ellnode_ruling.md` §4.4): the node is now
`ellClassOk_exists_of_inputs_tr` (`PhiStar.EllNode8tr_holds`), fed the θ-traces of the
orthogonalised source by `PhiStar.thetaTraces_orthSource` from the class field `thTr`;
`bslOp_sol_exists_pp` is no longer on the path. -/
theorem ellClassOk_exists_of_classC :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ g : Fn, ClassC α g →
      ∃ Ψ : Fn, Work.FTS.EllExist.EllClassOk 8 α g Ψ := by
  obtain ⟨α₁, hα₁pos, hmain⟩ := Work.FTS.EllExist.ellClassOk_exists_of_inputs_tr
  refine ⟨min α₁ (1 / 4), lt_min hα₁pos (by norm_num), ?_⟩
  intro α hα hαm g hg
  have hα₁ : α ≤ α₁ := le_trans hαm (min_le_left _ _)
  have hα4 : α ≤ 1 / 4 := le_trans hαm (min_le_right _ _)
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨hSm, hHk, hDec, hFsm, hFint⟩ := classC_ellInputs_full hα hα1 hg
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g hFsm hFint
  obtain ⟨hGsm, hGode⟩ :=
    Work.FTS.EllipticEst.Gsing_contDiffOn_ode_of_Fstar_facts α g hα hFsm hFint hL12
  exact hmain α hα hα₁ g hSm hHk
    (Work.FTS.PhiStar.thetaTraces_orthSource hα hα1 hg.reg hg.fsm hg.thTr) hDec hGsm hGode
    (gsing_tendsto_atTop_zero_of_classC hα hg.reg hg.mem)

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.ellClassOk_add_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## A3 at an arbitrary level -/

/-- **A3 at an arbitrary level `K`**: `EllClassOk K` is closed under
`(g, Ψ) ↦ (g + c • g', Ψ + c • Ψ')` over the linear class `ClassC`. -/
theorem ellClassOk_add_gen (K : ℕ) {α : ℝ} (hα : 0 < α) {g g' Ψ Ψ' : Work.FTS.Galerkin.Fn}
    (c : ℝ)
    (hg : Work.FTS.ClassC.ClassC α g) (hg' : Work.FTS.ClassC.ClassC α g')
    (h : Work.FTS.EllExist.EllClassOk K α g Ψ)
    (h' : Work.FTS.EllExist.EllClassOk K α g' Ψ') :
    Work.FTS.EllExist.EllClassOk K α (g + c • g') (Ψ + c • Ψ') := by
  have hgadd : (g + c • g') = fun z θ => g z θ + c * g' z θ := by
    funext z θ; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hΨadd : (Ψ + c • Ψ') = fun z θ => Ψ z θ + c * Ψ' z θ := by
    funext z θ; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hcΨ' : (fun z θ => c * Ψ' z θ) = c • Ψ' := by
    funext z θ; simp only [Pi.smul_apply, smul_eq_mul]
  rw [hgadd, hΨadd]
  -- the two pieces of weak-class data
  have hshift : Work.FTS.EllipticEst.TT.EllWeakPos α K
      (Work.Elliptic.orthSource g)
      (fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) := h.2.2
  have hshift' : Work.FTS.EllipticEst.TT.EllWeakPos α K
      (Work.Elliptic.orthSource g')
      (fun z θ => Ψ' z θ + Work.Elliptic.Gsing α g' z * Real.sin (2 * θ)) := h'.2.2
  -- the two sources are smooth on the open quadrant: they are `bslOp` of the shifted unknowns
  have hsoF : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) := by
    have hSso : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.smoothOpen_of_forall hshift.smooth
    exact (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hSso).congr
      (fun z θ hz h0 h1 => hshift.eq z hz θ h0 h1)
  have hsoF' : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g') := by
    have hSso : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Ψ' z θ + Work.Elliptic.Gsing α g' z * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.smoothOpen_of_forall hshift'.smooth
    exact (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hSso).congr
      (fun z θ hz h0 h1 => hshift'.eq z hz θ h0 h1)
  have hmemF0 : Work.Spaces.HkMem α 0 (Work.Elliptic.orthSource g) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := K) (Nat.zero_le K)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsoF) hshift.memF
  have hmemF0' : Work.Spaces.HkMem α 0 (Work.Elliptic.orthSource g') :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := K) (Nat.zero_le K)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsoF') hshift'.memF
  -- the solvability condition of the combined source
  have horth : ∀ z, 0 < z → Work.Elliptic.Fstar
      (fun z θ => Work.Elliptic.orthSource g z θ + c * Work.Elliptic.orthSource g' z θ) z
      = 0 := by
    intro z hz
    rw [Work.FTS.EllSol.Fstar_add_mul
      (Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hsoF.continuousOn
        hmemF0 hz)
      (Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hsoF'.continuousOn
        hmemF0' hz),
      Work.FTS.EllExist.Fstar_orthSource_zero, Work.FTS.EllExist.Fstar_orthSource_zero]
    ring
  have hcl := Work.FTS.EllSol.EllWeakPos_add_mul hsoF hsoF' horth hshift hshift'
  -- congruence with the combination
  have hFcongr : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      (fun z θ => Work.Elliptic.orthSource g z θ + c * Work.Elliptic.orthSource g' z θ) z θ
        = Work.Elliptic.orthSource (fun z θ => g z θ + c * g' z θ) z θ := by
    intro z θ hz h0 h1
    exact (Work.FTS.EllSol.orthSource_add_mul_apply
      (Work.FTS.EllSol.Fstar_add_mul
        (slice_sinCos2_integrable hg.reg (classC_hkMem_zero hg) hz)
        (slice_sinCos2_integrable hg'.reg (classC_hkMem_zero hg') hz))).symm
  have hScongr : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      (fun z θ => (fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) z θ
          + c * (fun z θ => Ψ' z θ + Work.Elliptic.Gsing α g' z * Real.sin (2 * θ)) z θ) z θ
        = (fun z θ => (fun z θ => Ψ z θ + c * Ψ' z θ) z θ
            + Work.Elliptic.Gsing α (fun z θ => g z θ + c * g' z θ) z
              * Real.sin (2 * θ)) z θ := by
    intro z θ hz h0 h1
    show Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)
        + c * (Ψ' z θ + Work.Elliptic.Gsing α g' z * Real.sin (2 * θ))
      = Ψ z θ + c * Ψ' z θ
        + Work.Elliptic.Gsing α (fun z θ => g z θ + c * g' z θ) z * Real.sin (2 * θ)
    have hG := Gsing_add_mul_open hα c hz hg.reg (classC_hkMem_four hg) hg'.reg
      (classC_hkMem_four hg')
    rw [hG]
    ring
  have h0' : ∀ z, (fun z θ => (fun z θ => Ψ z θ + c * Ψ' z θ) z θ
      + Work.Elliptic.Gsing α (fun z θ => g z θ + c * g' z θ) z * Real.sin (2 * θ)) z 0 = 0 := by
    intro z
    show Ψ z 0 + c * Ψ' z 0
      + Work.Elliptic.Gsing α (fun z θ => g z θ + c * g' z θ) z * Real.sin (2 * 0) = 0
    rw [show (2 : ℝ) * 0 = 0 from by norm_num, Real.sin_zero,
      h.1.2.1 z, h'.1.2.1 z]
    ring
  have hpi' : ∀ z, (fun z θ => (fun z θ => Ψ z θ + c * Ψ' z θ) z θ
      + Work.Elliptic.Gsing α (fun z θ => g z θ + c * g' z θ) z
        * Real.sin (2 * θ)) z (π / 2) = 0 := by
    intro z
    show Ψ z (π / 2) + c * Ψ' z (π / 2)
      + Work.Elliptic.Gsing α (fun z θ => g z θ + c * g' z θ) z * Real.sin (2 * (π / 2)) = 0
    rw [show (2 : ℝ) * (π / 2) = π from by ring, Real.sin_pi,
      h.1.2.2.1 z, h'.1.2.2.1 z]
    ring
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_,
    Work.FTS.EllSol.EllWeakPos_congr_Q0 hcl hFcongr hScongr h0' hpi'⟩
  · -- the equation of the combined unknown
    intro z hz θ h0 h1
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
    have hb1 : Work.Elliptic.bslOp α (fun z θ => Ψ z θ + c * Ψ' z θ) z θ
        = Work.Elliptic.bslOp α Ψ z θ
          + Work.Elliptic.bslOp α (fun z θ => c * Ψ' z θ) z θ :=
      Work.Elliptic.bslOp_add α Ψ (fun z θ => c * Ψ' z θ) z θ hcos
        (Work.FTS.EllSol.smoothOpen_contDiffAt_two h.2.1 hz h0 h1)
        (Work.FTS.EllSol.smoothOpen_contDiffAt_two (h'.2.1.const_mul' c) hz h0 h1)
    have hb2 : Work.Elliptic.bslOp α (fun z θ => c * Ψ' z θ) z θ
        = c * Work.Elliptic.bslOp α Ψ' z θ := by
      have hs := Work.FTS.EllipticEst.LevelOneFts.CF.bslOp_smul α c Ψ' z θ
      rw [← hcΨ'] at hs
      exact hs
    rw [hb1, hb2, h.1.1 z hz θ h0 h1, h'.1.1 z hz θ h0 h1]
  · -- the Dirichlet value at `θ = 0`
    intro z
    show Ψ z 0 + c * Ψ' z 0 = 0
    rw [h.1.2.1 z, h'.1.2.1 z]
    ring
  · -- the Dirichlet value at `θ = π/2`
    intro z
    show Ψ z (π / 2) + c * Ψ' z (π / 2) = 0
    rw [h.1.2.2.1 z, h'.1.2.2.1 z]
    ring
  · -- the decay at `z → ∞`
    intro θ hθ
    have h1 := (h.1.2.2.2 θ hθ).add ((h'.1.2.2.2 θ hθ).const_mul c)
    simpa using h1
  · -- smoothness of the combined unknown
    exact Work.FTS.EllipticEst.smoothOpen_add h.2.1 (h'.2.1.const_mul' c)

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.pth_Vop_EllResid_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The pointwise identity `∂_θ(Vop α Ξ) = -orthSource g - α²z²∂_z²Ψ̂ - α(5+α)z∂_zΨ̂ - 6Ξ`

For a datum `g` of the linear class `C` (`Work.FTS.ClassC.ClassC α g`) and a stream function
`Ψ` in the elliptic class at level `7` (`Work.FTS.EllExist.EllClassOk 7 α g Ψ`), write

* `Ψ̂ := shiftSing α g Ψ = Ψ + Gsing α g · sin 2θ` — the *straight* unknown, the one whose
  equation is `bslOp α Ψ̂ = orthSource g` on the open quadrant (`EllWeakPos.eq`, a field of
  `EllClassOk`), and
* `Ξ := EllResid α g Ψ = Ψ - (1/(4α))·sin 2θ·L₁₂(g) = Ψ̂ - Ḡ(α,g)·sin 2θ` — the residual.

Then, on the open quadrant,

`∂_θ(Vop α Ξ) = -(L₀Ξ + 6Ξ) = -(L₀Ψ̂ + 6Ξ)`, since `L₀(Ḡ·sin 2θ) = 0` (`Lzero_sin_two_mul`)
and `L₀` is additive on the open quadrant; and the equation for `Ψ̂` turns `L₀Ψ̂` into
`orthSource g + α²z²∂_z²Ψ̂ + α(5+α)z∂_zΨ̂`.  This is the `ClassC`/`EllClassOk`-`shiftSing`
instance of `Work.FTS.EllSol.pth_Vop_PhiTil_eq`, the `V`-slot companion of Theorem
`RemovingL12`: the singular terms cancel and **no `α^{-1}` survives**.

The only smoothness input not already a field of the two classes is the `C^∞`-regularity of the
layer `Ḡ(α,g)·sin 2θ` on the open quadrant, obtained from the all-order smoothness of the
angular moment `F_*(g)` (`ClassC.fsm`) and the honesty `HkMem α 7 g`. -/

/-- **`Ḡ(α,g)·sin 2θ` is `C^∞` on the open quadrant** for a datum of the class `C` (no
restriction on `α` beyond `0 < α`): `Ḡ(α,g) ∈ C^∞((0,∞))` because `Gsing` is smooth on `(0,∞)`
and `L₁₂(g)` is (its derivative is `-3F_*(g)(z)/z`, which is smooth on `(0,∞)`). -/
theorem smoothOpen_GbarSin_classC {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hreg : Work.FTS.EllipticEst.SmoothOpen g) (hfsm : ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar g) (Set.Ioi 0)) (hmem : Work.Spaces.HkMem α 7 g) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) := by
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hreg hmem
  have hGbsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α g) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.Gbar_contDiffOn_Ioi α g hα hfsm hFint
  exact Work.FTS.EllipticEst.SmoothOpen.sep_mul hGbsm (by fun_prop)


end Work.FTS.ClassC
end
