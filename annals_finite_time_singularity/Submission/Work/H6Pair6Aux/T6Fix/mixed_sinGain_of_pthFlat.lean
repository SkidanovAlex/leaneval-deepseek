import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.AeI1Fts.psiDeriv_setup
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired
import Submission.Work.FTS.PhiStar.Psi0Est.exists_ZClass
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.L6Aux.ZslotSupBound6
import Submission.Work.FTS.StrongPersist.N6.Exc6
import Submission.Work.FTS.StrongPersist.N6.ProdAssembly6
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.ZcutSmoothCompact
-- ===== merged: Submission.Work.FTS.ClassC.Fstar_chain_pz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The moment chain for `∂_z`

The angular moment `F_*(g)(z) = ∫_θ g(z,θ) sinθcos²θ dθ` of the plain radial derivative
`∂_z f` is an antiderivative of `F_* f`:

  `F_* f (z) - F_* f (s) = ∫_{s}^{z} F_*(∂_z f)(r) dr`  (`0 < s ≤ z`).

This is the `j = 0` case of the paper's chain rule for `F_*` along the radial operators
(the `D_z`-chain of `Work.FTS.EllipticEst.FstarDzIter_chain_open`), stated at the *minimal*
honesty level `HkMem α 1 f`:  only the first `D_z`-slot of the `ℋ¹`-integrand is needed,
because on the radial box `(s,z]` one has `∂_z f = D_z f / r` with `r ≥ s > 0`, so the plain
`z`-derivative is controlled by the first weighted `D_z`-slot
(`PzSinCos2Box`, via `pzSqSeta_le_Dz1_mul`).

The analytic content is Fubini on the box `[s,z] × Iθ` together with the fundamental theorem
of calculus along the radial slices
(`Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz`); the three integrability hypotheses of that
theorem are supplied from `HkMem α 1 f`:
`Cores.integrableOn_slice_mul_sinCos2` (via the descent `HkMem α 1 f → HkMem α 0 f`) for the two
endpoint slices, and `PzSinCos2Box` for the box integrand. -/

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.removingL12_classC_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.removingL12_classC_aux` — helpers for `removingL12_classC`

The bookkeeping of the `ClassC` / `EllClassOk 7` instance of Elgindi's Theorem `RemovingL12`
(tex 1034), kept in a separate module so that the target file stays inside the build guard's
size limit:

* `hkNorm_congr_classC` — `HkNorm` only sees the open quadrant;
* `smoothOpen_pthIter_classC` — `∂_θ`-iterates preserve open-quadrant smoothness;
* `scCoeff` and its norm bound ingredients — the coefficient of the radial removal;
* `ellWeakPos_descend` — the weak class `TT.EllWeakPos` descends in the level;
* `orthSource_HkNorm_le_classC` — `|orthSource g|_{ℋ^k} ≤ C|g|_{ℋ^k}` on `ClassC`;
* `gsing_certs_classC` — the classical certificates of the singular term on `ClassC`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-! ## Elementary closure facts -/


/-- `∂_θ`-iterates of a function `C^∞` on the open quadrant are `C^∞` there. -/
theorem smoothOpen_pthIter_classC {F : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using h
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth




/-! ## Descent of the weak class in the level -/

/-- **`TT.EllWeakPos` descends in the level**: the four `HkMem` fields descend by
`TT.HkMem_descend_open` (the open-quadrant smoothness of the four functions is available from the
smoothness of `F` and `Ψ`), and the remaining fields are level-free. -/
theorem ellWeakPos_descend {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {k l : ℕ} (hkl : k ≤ l)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α l F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ := by
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.zsq_mul (hΨ.pzIter 2)
  have hB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    smoothOpen_pthIter_classC hΨ 2
  have hZ : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) := hB.Dz
  exact ⟨h.eq, h.zero, h.pi_half, (fun z hz => h.orthF z hz), (fun z hz => h.orthPsi z hz),
    h.smooth,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl hF.forall h.memF,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl hA.forall h.memA,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl hB.forall h.memB,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl hZ.forall h.memZPth2⟩

/-! ## The source comparison on `ClassC` -/


/-! ## The classical certificates of the singular term on `ClassC` -/

/-- **The certificates of `Gsing α g` for `ClassC`-data.**  The angular moment `F_*(g)`, the
singular term `Gsing α g` and its lower part `Ḡ α g` are `C^∞` on `(0,∞)`, and `G = Gsing α g`
satisfies the two ODE relations behind the removal identities. -/
theorem gsing_certs_classC {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : Fn} (hg : ClassC α g) :
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0)) ∧
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α g) (Set.Ioi 0)) ∧
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α g) (Set.Ioi 0)) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      α * z * deriv (Work.Elliptic.Gsing α g) z = -5 * Work.Elliptic.Gbar α g z) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z
      = (15 / 4) * Work.Elliptic.Fstar g z) := by
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0) := hg.fsm
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hg.reg hg.mem
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g hFsm hFint
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar g) (deriv (Work.Elliptic.Fstar g) z) z := by
    intro z hz
    exact (((hFsm 1).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z',
          s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z :=
    Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar α g hFsm hFint hα hα1
  exact ⟨hFsm,
    (Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts α g hα hFsm hFint hL12).1,
    Work.FTS.EllipticEst.Cert.Gbar_contDiffOn_Ioi α g hα hFsm hFint,
    Work.FTS.EllipticEst.Gsing_deriv_rel α g hα hL12 hFc hJ,
    Work.Elliptic.Gsing_ode α g hα hL12 hFc hJ⟩

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.CoreDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The hypotheses of one additivity step of the transfer.**  The three arguments are
`C^n` on the open quadrant and lie in `ℋⁿ`; the smoothness is what makes `D_θ`/`D_z`
additive, the membership is what makes the `wip`-splittings legitimate. -/
def AddOKSm (α : ℝ) (n : ℕ) (f₁ f₂ g : Fn) : Prop :=
  Q0Sm n f₁ ∧ Q0Sm n f₂ ∧ Q0Sm n g ∧
    Work.Spaces.HkMem α n f₁ ∧ Work.Spaces.HkMem α n f₂ ∧ Work.Spaces.HkMem α n g

/-- **The algebraic inputs of the transfer at level `n`.**  The congruence needs no
regularity (the derivative is local and the quadrant is co-null); additivity needs
`AddOKSm`; the two commutator identities of `𝓛̂` are pointwise statements on `Qd` for a
`SmoothQuad` datum. -/
structure CommSm (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) : Prop where
  /-- congruence in the first argument on the open quadrant, with no membership -/
  congr : ∀ f f' g : Fn,
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g
  /-- additivity in the first argument, from `C^n`-smoothness and `ℋⁿ`-membership -/
  add : ∀ f₁ f₂ g : Fn, AddOKSm α n f₁ f₂ g → IP (f₁ + f₂) g = IP f₁ g + IP f₂ g
  /-- `D_θ` commutes with `Lhat` exactly -/
  dthC : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ
  /-- the `D_z` commutator of `Lhat` is the explicit defect `Ê₂` -/
  dzC : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ

/-- **Cauchy–Schwarz at level `n`** for `C^n` arguments in `ℋⁿ`.  This is the form in which
the two error pairings `IP (E1 α f) (D_θf)` and `IP (E2 α f) (D_zf)` are consumed: the two
defects are `C³` on the open quadrant (`Transfer/E1Parts/ContE1.lean`, `Transfer/E2_blocks.lean`)
and lie in `ℋⁿ` for `n ≤ 3`, but they are *not* `RegQ`, so the delivered `RegQ`-based
Cauchy–Schwarz bound does not apply. -/
def CSQ (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (CC : ℝ) : Prop :=
  ∀ X Y : Fn, Q0Sm n X → Q0Sm n Y → Work.Spaces.HkMem α n X → Work.Spaces.HkMem α n Y →
    |IP X Y| ≤ CC * Work.Spaces.HkNorm α n X * Work.Spaces.HkNorm α n Y

end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.C0_sq_le_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

set_option autoImplicit false

/-! ## The pointwise comparison `(A W)² ≤ (A (W / s^{η/2}))²` -/

/-- For `0 < s ≤ 1` and reals `A`, `W`: `(A·W)² ≤ (A·(W/s^{η/2}))²`.  In the application
`s = sin(2θ)`, so that `A·(W/s^{η/2})` is the `i = 0` summand of the `ℋⁿ`-integrand. -/
private lemma sq_le_sq_div_sin (A W s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    (A * W) ^ 2 ≤ (A * (W / s ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have heta : s ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs) hs1 (by norm_num [Work.Spaces.eta])
  have hpos : 0 < s ^ Work.Spaces.eta := Real.rpow_pos_of_pos hs _
  have h1 : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ Work.Spaces.eta := by
    rw [← Real.rpow_natCast (s ^ (Work.Spaces.eta / 2)) 2]
    rw [← Real.rpow_mul (le_of_lt hs)]
    norm_num [Work.Spaces.eta]
  simp only [mul_pow, div_pow, h1]
  rw [← mul_div_assoc, le_div_iff₀ hpos]
  exact mul_le_of_le_one_right (by positivity) heta

/-! ## `Ef ≤ HkSq α n` -/

/-- The level-`0` energy is dominated by the `ℋⁿ`-norm for every `n`: the `i = 0` summand of
the integrand of `HkSq α n f` is `(f · w / sin(2θ)^{η/2})²`, which dominates `(f · w)²`
because `sin(2θ)^{η} ≤ 1` on `(0,π/2)` — and the two endpoints of `Iθ` are null. -/
theorem Ef_le_HkSq (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α n f) :
    Work.Coercivity.Ef f ≤ Work.Spaces.HkSq α n f := by
  rw [Work.Coercivity.Ef, Work.Spaces.L2Sq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hmem.2 ?_
  show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz => ?_
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hz) ?_
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  calc (f z θ * Work.Spaces.w z) ^ 2
      ≤ (f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
        sq_le_sq_div_sin _ _ _ hsin (Real.sin_le_one _)
    _ = (Work.Spaces.DzIter 0 f z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        simp
    _ ≤ Work.Spaces.HkIntegrand α n f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α n f z θ 0 (Nat.zero_le n)

/-! ## The target -/


end Work.FTS.CoercivityFix.Transfer.E1Norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.ContE1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false




end Work.FTS.CoercivityFix.Transfer.E1Parts
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadABnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1600000





end Work.FTS.CoercivityFix.Transfer.E1Parts
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.mixIntS_zmoll_le_indicator =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set Filter
open scoped Real Topology

local notation "Iθ" => Work.Spaces.Iθ
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-! ## The kernel bound and the weight comparison on the logarithmic window -/


/-- The weight `w (e^s)² = (1+e^s)^4 e^{-3s}` compared at the two ends of the logarithmic
window `|log z - t| ≤ δ ≤ 1/2`: `w z ² ≤ 10 · w (e^t)²`. -/
theorem w_window_cmp {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) {z t : ℝ} (hz : 0 < z)
    (ht : |Real.log z - t| ≤ δ) :
    (Work.Spaces.w z) ^ 2 ≤ 10 * (Work.Spaces.w (Real.exp t)) ^ 2 := by
  have hlog : Real.exp (Real.log z) = z := Real.exp_log hz
  have h1 : |Real.log z - t| ≤ 1 / 2 := le_trans ht (le_trans hδ1 (by norm_num))
  have h2 := Work.FTS.EllSol.EllPkgAux.wExpCmp (Real.log z) t h1
  rw [hlog] at h2
  have hEt : Real.exp t ≤ 2 * z := by
    have hle : t - Real.log z ≤ 1 / 2 := by
      have h := (abs_le.mp h1).1
      linarith
    have hexp1 : Real.exp (t - Real.log z) ≤ 2 := by
      refine le_trans (Real.exp_le_exp.mpr hle) ?_
      have hsq : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
        rw [sq, ← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 / 2), hsq, Real.exp_one_lt_d9]
    calc Real.exp t = Real.exp (Real.log z + (t - Real.log z)) := by ring_nf
      _ = z * Real.exp (t - Real.log z) := by rw [Real.exp_add, hlog]
      _ ≤ z * 2 := by nlinarith [hexp1, hz.le]
      _ = 2 * z := by ring
  have h3 : (Work.Spaces.w z) ^ 2 * z
      ≤ 5 * ((Work.Spaces.w (Real.exp t)) ^ 2 * (2 * z)) := by
    nlinarith [h2, hEt, hz, sq_nonneg (Work.Spaces.w (Real.exp t))]
  have h4 : (Work.Spaces.w z) ^ 2 * z ≤ (10 * (Work.Spaces.w (Real.exp t)) ^ 2) * z := by
    calc (Work.Spaces.w z) ^ 2 * z ≤ 5 * ((Work.Spaces.w (Real.exp t)) ^ 2 * (2 * z)) := h3
      _ = (10 * (Work.Spaces.w (Real.exp t)) ^ 2) * z := by ring
  exact (mul_le_mul_iff_of_pos_right hz).mp h4

/-! ## Dropping the angular weight `σ_η ≥ 1` -/

/-- `σ_η = sin(2θ)^{-η} ≥ 1` on the open angular interval. -/
private theorem one_le_thEta_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ σθ θ := by
  rw [Work.FTS.EllipticEst.thEta]
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h := Real.rpow_le_rpow_of_nonpos (z := -(Work.Spaces.eta)) hsin
    (Real.sin_le_one (2 * θ)) (by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h

/-- `σ_η = sin(2θ)^{-η} ≥ 1` almost everywhere on `Iθ = [0, π/2]`. -/
private theorem ae_one_le_thEta :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict Iθ), 1 ≤ σθ s := by
  have hEq : MeasureTheory.volume.restrict Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [hEq]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => one_le_thEta_Ioo hθ)

/-- Dropping the angular weight `σ_η ≥ 1` costs nothing: for a nonnegative `f` whose
`σ_η`-weighted version is integrable on `Iθ`, `∫_{Iθ} f ≤ ∫_{Iθ} f σ_η`. -/
private theorem integral_le_integral_mul_thEta {f : ℝ → ℝ} (hf : ∀ s : ℝ, 0 ≤ f s)
    (hint : MeasureTheory.Integrable (fun s : ℝ => f s * σθ s)
      (MeasureTheory.volume.restrict Iθ)) :
    (∫ s in Iθ, f s) ≤ ∫ s in Iθ, f s * σθ s := by
  have h := MeasureTheory.integral_mono_of_nonneg
    (μ := MeasureTheory.volume.restrict Iθ)
    (f := fun s : ℝ => f s) (g := fun s : ℝ => f s * σθ s)
    (Filter.Eventually.of_forall hf) hint ?_
  · exact h
  · filter_upwards [ae_one_le_thEta] with s hs
    exact le_mul_of_one_le_right (hf s) hs

/-! ## The main estimate -/

theorem mixIntS_zmoll_le_indicator (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
      Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z
        ≤ C * ∫ t : ℝ,
            (if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0) := by
  have hP0 : Work.FTS.EllSol.EllPkgAux.Params δ ε := hP
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP0
  obtain ⟨KJc, hKJc0, hKJc⟩ := Work.FTS.EllSol.EllPkgAux.kernelJensen
  obtain ⟨C1, hC10, hC1⟩ := zSchur_pth_window_unif G hT hF δ hδ0 hδ1
  obtain ⟨C2, hC20, hC2⟩ := window_E_le_F G hT hF δ hδ0
  refine ⟨KJc * C1 * C2 * 10, by positivity, fun z hz => ?_⟩
  set A : ℝ → ℝ := fun s => zSchur δ (fun w => Work.Spaces.pth G w s) z with hAdef
  have hintA : MeasureTheory.IntegrableOn (fun s : ℝ => (A s) ^ 2 * σθ s) Iθ := by
    rw [hAdef]
    exact (hC1 z hz).1
  have hKJ := hKJc A hintA ε hε0 hε1
  have hid := zmoll_mixed_conv G hT hF δ ε hP z hz
  -- Step 1: insert the convolution identity and apply the angular Jensen/Schur estimate
  have heq : (∫ θ in Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ) ^ 2
          * σθ θ)
      = (∫ θ in Iθ, σθ θ
          * (∫ s in Iθ,
              (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s)
                + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * A s) ^ 2) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    simp only [hAdef]
    rw [hid θ hθ]
    simp only [Work.FTS.EllSol.EllPkgAux.KJ]
    ring
  have h1 : (∫ θ in Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ) ^ 2
          * σθ θ)
      ≤ KJc * (∫ s in Iθ, (A s) ^ 2 * σθ s) := by
    rw [heq]
    exact hKJ
  -- Step 2: the logarithmic-Schur window bound for the angular derivative
  have h2 : (∫ s in Iθ, (A s) ^ 2 * σθ s)
      ≤ C1 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
          (∫ s in Iθ, σθ s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0)) := by
    have h := (hC1 z hz).2
    refine le_of_eq_of_le ?_ h
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    simp only [hAdef]
    ring
  -- Step 3: the weighted Poincaré estimate on the logarithmic window
  have h3 : (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
        (∫ s in Iθ, σθ s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0))
      ≤ C2 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
        (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0)) :=
    (hC2 z hz).2
  -- Step 4: the radial weight comparison on the window
  have hAngint : ∀ t : ℝ, MeasureTheory.Integrable
      (fun s : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s)
      (MeasureTheory.volume.restrict Iθ) := by
    intro t
    have h0 := hT.2.2.2.2.2.2.2.1 (Real.exp t) (Real.exp_pos t)
    have hwne : (Work.Spaces.w (Real.exp t)) ^ 2 ≠ 0 := by
      have h1 : 0 < Work.Spaces.w (Real.exp t) := by rw [Work.Spaces.w]; positivity
      positivity
    refine (h0.const_mul (((Work.Spaces.w (Real.exp t)) ^ 2)⁻¹)).congr
      (Filter.Eventually.of_forall (fun s => ?_))
    calc ((Work.Spaces.w (Real.exp t)) ^ 2)⁻¹
          * ((Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2
              * (Work.Spaces.w (Real.exp t)) ^ 2 * σθ s)
        = ((Work.Spaces.w (Real.exp t)) ^ 2)⁻¹ * (Work.Spaces.w (Real.exp t)) ^ 2
            * ((Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s) := by ring
      _ = (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s := by
            rw [inv_mul_cancel₀ hwne, one_mul]
  have hmain : ∀ t : ℝ, (Work.Spaces.w z) ^ 2 * (if |Real.log z - t| ≤ δ then
        (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0)
      ≤ 10 * (if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0) := by
    intro t
    by_cases ht : |Real.log z - t| ≤ δ
    · rw [if_pos ht, if_pos ht]
      have hAB := integral_le_integral_mul_thEta (f := fun s : ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2)
        (fun s => sq_nonneg _) (hAngint t)
      have hBnn : 0 ≤ ∫ s in Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s :=
        MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun s hs => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hs))
      have hwcmp := w_window_cmp hδ0 hδ1 hz ht
      have hTdef : Work.EllipticEst.Core.ttIntS G (Real.exp t)
          = (Work.Spaces.w (Real.exp t)) ^ 2 * (∫ s in Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s) := rfl
      rw [hTdef]
      calc (Work.Spaces.w z) ^ 2 * (∫ s in Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2)
          ≤ (Work.Spaces.w z) ^ 2 * (∫ s in Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s) :=
            mul_le_mul_of_nonneg_left hAB (sq_nonneg _)
        _ ≤ (10 * (Work.Spaces.w (Real.exp t)) ^ 2) * (∫ s in Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s) :=
            mul_le_mul_of_nonneg_right hwcmp hBnn
        _ = 10 * ((Work.Spaces.w (Real.exp t)) ^ 2 * (∫ s in Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s)) := by ring
    · rw [if_neg ht, if_neg ht]
      simp
  have h4 : (Work.Spaces.w z) ^ 2 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
        (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0))
      ≤ 10 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
          Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0)) := by
    have hIntT : MeasureTheory.Integrable (fun t : ℝ => 10 * (if |Real.log z - t| ≤ δ then
        Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0)) MeasureTheory.volume :=
      ((window_ttIntS_integrable G hT hF δ z hδ0 hz).1).const_mul 10
    have hleft_nn : 0 ≤ᵐ[MeasureTheory.volume] (fun t : ℝ => (Work.Spaces.w z) ^ 2 *
        (if |Real.log z - t| ≤ δ then
          (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0)) := by
      filter_upwards with t
      by_cases ht : |Real.log z - t| ≤ δ
      · rw [if_pos ht]
        exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun s _ => sq_nonneg _))
      · rw [if_neg ht]
        simp
    have hmono := MeasureTheory.integral_mono_of_nonneg hleft_nn hIntT
      (Filter.Eventually.of_forall hmain)
    calc (Work.Spaces.w z) ^ 2 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0))
        = ∫ t : ℝ, (Work.Spaces.w z) ^ 2 * (if |Real.log z - t| ≤ δ then
            (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ ∫ t : ℝ, 10 * (if |Real.log z - t| ≤ δ then
            Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0) := hmono
      _ = 10 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0)) := by
          rw [MeasureTheory.integral_const_mul]
  calc Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ,
          (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ) ^ 2
            * σθ θ) := rfl
    _ ≤ (Work.Spaces.w z) ^ 2 * (KJc * (∫ s in Iθ, (A s) ^ 2 * σθ s)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = KJc * ((Work.Spaces.w z) ^ 2 * (∫ s in Iθ, (A s) ^ 2 * σθ s)) := by ring
    _ ≤ KJc * ((Work.Spaces.w z) ^ 2 * (C1 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Iθ, σθ s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hKJc0.le
        exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = KJc * C1 * ((Work.Spaces.w z) ^ 2 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Iθ, σθ s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0))) := by ring
    _ ≤ KJc * C1 * ((Work.Spaces.w z) ^ 2 * (C2 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    _ = KJc * C1 * C2 * ((Work.Spaces.w z) ^ 2 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0))) := by ring
    _ ≤ KJc * C1 * C2 * (10 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact h4
    _ = (KJc * C1 * C2 * 10) * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0)) := by ring

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.VthAux.mixedSlot_sup_le_hk_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VthAux

/-- Elgindi's Corollary `SecondDerivativesBounded` in the honest open class
(`SmoothOpen` + `HkMem α 4`): every mixed derivative `D_z^b D_θ^a f` of total order `a + b ≤ 2`
is bounded pointwise on the open quadrant by `C / √(γ-1) · |f|_{ℋ⁴}`, with a universal constant
`C`.

The two halves are already available in the workspace:

* `a = 0` (pure radial slots `D_z^b f`, `b ≤ 2`): `Work.FTS.TransportS.sup_dz_le_hk`, whose
  constant already has the shape `C/√(γ-1)`;
* `a ≥ 1` (the genuinely mixed slots):`Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn`, an
  `α`-uniform pointwise bound `|D_z^bD_θ^af| ≤ C·|f|_{ℋ⁴}` (`i + j ≤ 2`, `i ≥ 1`).  Since
  `γ - 1 = α/10 ≤ 1` gives `1 ≤ 1/√(γ-1)`, that bound is also of the required shape
  `C/√(γ-1) · |f|_{ℋ⁴}`.

With `C := Cs + Cm` the two cases assemble to the stated bound. -/
theorem mixedSlot_sup_le_hk_open : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → a + b ≤ 2 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a f z θ|
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
  obtain ⟨Cs, hCs0, hsupdz⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨Cm, hCm0, hmix⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  refine ⟨Cs + Cm, by linarith, ?_⟩
  intro α f b a hα hα1 hab hF hmem z θ hz hθ hθ1
  -- the two elementary facts about `γ - 1 = α/10 ∈ (0, 1]`
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hγ1le : Work.Spaces.gam α - 1 ≤ 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hspos : 0 < Real.sqrt (Work.Spaces.gam α - 1) := Real.sqrt_pos.mpr hγ1
  have hsinv : (1 : ℝ) ≤ 1 / Real.sqrt (Work.Spaces.gam α - 1) := by
    rw [one_le_div hspos]
    exact Real.sqrt_le_one.mpr hγ1le
  have hHk : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
  rcases Nat.eq_zero_or_pos a with ha | ha
  · -- `a = 0`: the pure radial slot `D_z^b f`
    have hb : b ≤ 2 := by omega
    have hbound := hsupdz α f hα hα1 hF hmem b hb z θ hz hθ hθ1
    rw [ha, Work.Spaces.mixed_zero_right] at *
    refine hbound.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hHk
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · -- `a ≥ 1`: the genuinely mixed slot
    have ha1 : 1 ≤ a := ha
    have hbound := hmix α f hα hα1 hF hmem b a ha1 hab z θ hz hθ hθ1
    refine hbound.trans ?_
    calc Cm * Work.Spaces.HkNorm α 4 f
        ≤ (Cm / Real.sqrt (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f := by
          refine mul_le_mul_of_nonneg_right ?_ hHk
          have hmul : Cm * 1 ≤ Cm * (1 / Real.sqrt (Work.Spaces.gam α - 1)) :=
            mul_le_mul_of_nonneg_left hsinv hCm0.le
          rw [div_eq_mul_inv]
          simpa using hmul
      _ ≤ ((Cs + Cm) / Real.sqrt (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f := by
          refine mul_le_mul_of_nonneg_right ?_ hHk
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Work.FTS.EllSol.VthAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_P_integrable_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000


end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.psiDeriv_layer_prep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/psiDeriv_layer_prep` — the ingredients of the angular layer bound

The `θ`-analysis of the boundary term `∫_θ σ θ (χ_ε)' θ (U·V)` of `psiDeriv_tendsto_zero`:

`|∫_{(0,π/2)} σ (χ_ε)' Uloc Vloc| ≤ 2 S₁ √(2·(2^η/(1+η))·(π/4)^η) √A
    √(∫_{(0,ε)} σ Vloc² + ∫_{(π/2-ε,π/2)} σ Vloc²)`,

for `0 < ε ≤ π/4`, given the two endpoint bounds `Uloc θ² ≤ (2^η/(1+η)) A θ^{1+η}` and
`Uloc θ² ≤ (2^η/(1+η)) A (π/2-θ)^{1+η}` for the slice `Uloc` and the `σ`-integrability of
`Uloc²`, `Vloc²`.

## Route

* `(χ_ε)'` vanishes on `(ε, π/2-ε)` (`deriv_cut_support`) and `|(χ_ε)'| ≤ 2S₁/ε` everywhere
  (`SliceMixedAux.abs_deriv_cut_le`); hence the integrand vanishes a.e. off the two layers and
  the integral splits as `∫_L + ∫_R` (`setIntegral_eq_of_subset_of_ae_sdiff_eq_zero`), each part
  being bounded by `(2S₁/ε)` times the layer integral of `σ|Uloc||Vloc|`.
* Cauchy–Schwarz (`Work.Spaces.cs_integral`) on `L ∪ R`: `∫ σ|Uloc||Vloc| ≤ √(∫σUloc²)√(∫σVloc²)`.
* On `L = (0,ε)`: `σ θ ≤ (π/4)^η θ^{-η}` (Jordan) and `Uloc θ² ≤ C A θ^{1+η}` give
  `σUloc² ≤ C A (π/4)^η ε`, so `∫_L σUloc² ≤ C A (π/4)^η ε²`; on `R = (π/2-ε,π/2)` the reflected
  inequalities give the same (with `θ ↦ π/2-θ`), so `∫_{L∪R} σUloc² ≤ 2 C A (π/4)^η ε²`.
* The `1/ε` cancels against the `ε` of the square root.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)







end Work.FTS.EllipticEst.AeI1Fts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.cascadeSourceless =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `WeakPureAux/cascadeSourceless` — the source term of the cascade is *provably* dead

`WeakPureAux/cascadeBalance.lean` proves the amplitude balance of the cascade at `θ = π/2`:

  `(1 - N²)·B = α²z²·B₂ + α(5+α)z·B₁`   for `N ≥ 2`,                     (⋆)

*provided* the source has no component of order `N+2`.  `NOTES_weakPhiPoleBound.md` §U records
that this proviso is what blocks the closure: the descent's "the source is to blame" branch could
not be ruled out because `HkMem α 0 G` was believed to control only the *weighted `L²(sEta)`*
size of the source's slice, which is compatible with a *pointwise* failure (`t^{-3.5}` spikes).

**The point of this module**: at the level of the *amplitudes* — which is the level at which the
cascade recursion (⋆) and §K's factorial count live — the source term is **exactly zero**, with no
extra hypothesis:

```
theorem sourceAmp_vanishes (hSOG, hmem, hz, hN : 2 ≤ N, hlim : (π/2-θ)^{N+2}·G z θ → c) : c = 0
```

Reason: if the limit were `c ≠ 0`, the slice would satisfy `|G z θ| ≥ (|c|/2)(π/2-θ)^{-(N+2)}`
near `π/2` with `N ≥ 2`, and the *proved* `SliceA.not_integrableOn_sinCos2_of_tendsto` then
makes `sinθcos²θ·|G z ·|` non-integrable — contradicting
`endpt_slice_mul_sinCos2_integrable_of_HkMem` (which makes that quantity integrable on `Iθ` for
**every** `z > 0`).  Note the argument is *per-fiber and per-`z`*: it uses only `HkMem α 0 G`, and
it does not need any continuity of the source, so the spike construction recorded in
`NOTES_cascadeBalance.md` §3 (which defeats the *pointwise* route) is irrelevant here: spikes do
not have an amplitude.

Consequently `cascadeBalance_sourceless` below is (⋆) with the source hypothesis discharged from
`HkMem`; it is the *homogeneous* recursion which the factorial-growth analysis of
`cascadeAmplitude.lean` / §K applies to.  What that analysis still needs is the *decay half*
(the amplitudes of an actual slice must decay) together with the same statement at the shifted
levels `m ≥ 1` (`D_z^m G`), i.e. the z-differentiation/limit-interchange lemma
`lim t^M D_z^m G = ∂_z^m (lim t^M G)`, which would turn `sourceAmp_vanishes` into the vanishing
of *all* the source amplitudes (the amplitude function of the source is identically zero, so all
its z-derivatives are).
-/

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

local notation "Lθ" => nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))






end Work.FTS.EllipticEst.H2W.WeakPureAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.I1Ae.RIFCollar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut

open Work.FTS.EllipticEst.AeI1Fts (U V Hh AA BB sigE sig1 sig2 II nuQ Fp Fd)

section Collar



end Collar

end Work.FTS.EllipticEst.I1Ae
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row22 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option linter.unusedVariables false

/-! ## Row 22 of the design table of `Submission/Work/FTS/Nonlinear/NOTES_N4.md`

The piece is `N₄^{∗g} = -(1/2)·FK(F_*)·D_θ g` (row 22 of `Defs.lean`), i.e. the slot of the
transport estimate in which the coefficient `-(1/2)·FK(F_*)` is a function of `z` alone and the
derivative `D_θ g = sin(2θ)·∂_θ g` falls on the test function.  The relevant clause of the
`IP`-interface is `N4Extra.t4`,

  `|IP α (f · D_θ g) g| ≤ Ct·α^{-1/2}·|f|_{𝒲^{4,∞}}·X²`,

so everything reduces to the `𝒲^{4,∞}`-norm of the radial coefficient.

The two facts needed about the coefficient:

* `FK (F_*(α)) z = α·(2z/(1+z)²) = α·2·hKer z` (`FstarPkg.FK_Fstar`), so that the coefficient
  is `-α·hKer`;
* for any constant `c`, the function `(z,θ) ↦ c·hKer z` lies in `𝒲^{4,∞}` with norm at most
  `200·|c|`.

The second fact is the radial (angular-factor-free) companion of `Work.Spaces.Gamma_WlInf`
(which bounds `Γ(θ)·hKer z` uniformly in `α`): here the angular variable does not occur at all,
so every positive `D_θ`-iterate vanishes identically and only the five radial summands of the
norm survive, each bounded by `|c|·k!·(k+1)` (`Work.Spaces.pzIter_hKer_bound`).  Since
`∑_{k≤4} k!(k+1) = 153 < 200` the norm is at most `200|c|`. -/

/-- **The `𝒲^{4,∞}`-norm of a constant multiple of the radial profile `hKer(z) = z/(1+z)²`.**

`(z,θ) ↦ c·hKer z` is `θ`-independent, so all its positive `D_θ`-iterates vanish
(`Work.Spaces.DthIter` of a function of `z` alone), and the `𝒲^{4,∞}`-norm is just the sum of
the five radial summands `sup |(z+1)^k h^{(k)}|`, each `≤ |c|·k!·(k+1)`. -/
theorem hKerConstWlInf (α c : ℝ) :
    Work.Spaces.WlInfMem α 4 (fun z θ => c * Work.Spaces.hKer z) ∧
    Work.Spaces.WlInf α 4 (fun z θ => c * Work.Spaces.hKer z) ≤ 200 * |c| := by
  -- every positive `D_θ`-iterate of a `θ`-independent function vanishes
  have hDth : ∀ j : ℕ, Work.Spaces.DthIter (j + 1) (fun z θ => c * Work.Spaces.hKer z)
      = fun _ _ => (0 : ℝ) := by
    intro j
    induction j with
    | zero => funext z θ; simp [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    | succ j ih =>
        rw [show j + 1 + 1 = (j + 1) + 1 from rfl, Work.Spaces.DthIter_succ, ih]
        funext z θ
        simp [Work.Spaces.Dth, Work.Spaces.pth]
  have hpzIter0 : ∀ k : ℕ, Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Work.Spaces.pzIter_succ, ih]; funext z θ; simp [Work.Spaces.pz]
  -- the pointwise bounds of the radial summands
  have hrad : ∀ k : ℕ, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * Work.Spaces.hKer z) z θ|
        ≤ |c| * ((k.factorial : ℝ) * (k + 1)) := by
    intro k z hz θ hθ
    rw [Work.Spaces.pzIter_decomp k (fun _ : ℝ => c) Work.Spaces.hKer z θ]
    rw [show (z + 1) ^ k * (c * deriv^[k] Work.Spaces.hKer z)
        = c * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z) by ring]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Work.Spaces.pzIter_hKer_bound k z hz) (abs_nonneg c)
  have hmem : Work.Spaces.WlInfMem α 4 (fun z θ => c * Work.Spaces.hKer z) := by
    constructor
    · intro k hk
      exact ⟨|c| * ((k.factorial : ℝ) * (k + 1)), fun y hy => by
        rcases hy with ⟨z, hz, θ, hθ, rfl⟩
        exact hrad k z hz θ hθ⟩
    · intro j hj k hk hj1 hjk
      have hDj : Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z) = fun _ _ => (0 : ℝ) := by
        rw [← Nat.sub_add_cancel hj1]
        exact hDth (j - 1)
      refine ⟨0, fun y hy => ?_⟩
      rcases hy with ⟨z, hz', θ, hθ, rfl⟩
      simp only []
      rw [hDj]
      have h0 : Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
        congrFun (congrFun (hpzIter0 k) z) θ
      rw [h0, mul_zero, zero_mul, zero_div, abs_zero]
  refine ⟨hmem, ?_⟩
  rw [Work.Spaces.WlInf]
  have h1 : (∑ k ∈ Finset.range 5, Work.Spaces.supAbs
      (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * Work.Spaces.hKer z) z θ))
      ≤ ∑ k ∈ Finset.range 5, (|c| * ((k.factorial : ℝ) * (k + 1))) :=
    Finset.sum_le_sum fun k _ => Work.Spaces.supAbs_le (hrad k)
  have h2 : (∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
      if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.supAbs
        (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      else 0) ≤ 0 := by
    refine Finset.sum_nonpos (fun j _ => Finset.sum_nonpos (fun k _ => ?_))
    by_cases hc : 1 ≤ j ∧ k + j ≤ 4
    · rw [if_pos hc]
      refine Work.Spaces.supAbs_le (fun z hz' θ hθ => ?_)
      have hDj : Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z) = fun _ _ => (0 : ℝ) := by
        rw [← Nat.sub_add_cancel hc.1]
        exact hDth (j - 1)
      rw [hDj]
      have h0 : Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
        congrFun (congrFun (hpzIter0 k) z) θ
      rw [h0, mul_zero, zero_mul, zero_div, abs_zero]
    · rw [if_neg hc]
  calc (∑ k ∈ Finset.range 5, Work.Spaces.supAbs
          (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * Work.Spaces.hKer z) z θ))
        + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
            (if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.supAbs
              (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
                  (Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z)) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)
      ≤ (∑ k ∈ Finset.range 5, (|c| * ((k.factorial : ℝ) * (k + 1)))) + 0 := add_le_add h1 h2
    _ = |c| * (∑ k ∈ Finset.range 5, ((k.factorial : ℝ) * (k + 1))) := by
        rw [Finset.mul_sum, add_zero]
    _ ≤ |c| * 200 := mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg c)
    _ = 200 * |c| := by ring


end Work.FTS.Nonlinear.Pieces.RNP
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row26 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# Row 26 of the per-piece table of `Work/FTS/Nonlinear`: `|N₅^{ss}|_{ℋ⁴} ≤ Kα²`

Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
Euler equations on `ℝ³`*, Annals 194 (3) 2021, §8: the `ss`-piece of the quadratic term `N₅`
of the modulated self-similar equation, `N₅^{ss} = -sin²θ·(F_*,K)_{L²_θ}·F_*` (the design's
`Work.FTS.Nonlin.N5ss`), has `ℋ⁴`-norm at most `Kα²`, uniformly for `0 < α ≤ min(α₂,1)`.

The estimate is *unconditional* (it involves only the fundamental model `F_*`, not the
perturbation `g` or the stream functions `Φs`, `Φg`; `N4Norm` is carried only to fix the
context of the design table).  The proof is a direct computation in the weighted `ℋ⁴`-norm,
reducing everything to `HkSq_sep_le` and to the angular core
`Work.FTS.Nonlinear.Pieces.RNP26.psiB_Lop_bound`; see the docstrings below.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The angular profile `θ ↦ sin²θ·Γ(θ)` of `N₅^{ss} = -sin²θ·FK(F_*)·F_*`. -/
def psiB (α : ℝ) (θ : ℝ) : ℝ := Real.sin θ ^ 2 * Work.Spaces.Gam α θ

theorem psiB_abs_le_one {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    |psiB α θ| ≤ 1 := by
  have hΓ : |Work.Spaces.Gam α θ| ≤ 1 := by
    rw [abs_of_nonneg (Work.Construction.Gam_nonneg_of_Iθ hα hθ)]
    exact Work.Construction.Gam_le_one_of_Iθ hα hθ
  have hs : Real.sin θ ^ 2 ≤ 1 := by
    rw [← sq_abs (Real.sin θ)]
    nlinarith [Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ)]
  have hsabs : |Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]; exact hs
  rw [psiB, abs_mul]
  calc |Real.sin θ ^ 2| * |Work.Spaces.Gam α θ| ≤ 1 * 1 :=
        mul_le_mul hsabs hΓ (abs_nonneg _) (by norm_num)
    _ = 1 := by ring



end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.ConvLev0Defs =====
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

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The level-`0` limit package.**  The profiles `G n` converge to `f` locally uniformly on the
open quadrant `Q0`, `f` is `C⁴` there, and `HkNorm α 6 f ≤ B`.

This is `ConvLocUnifH6` with the slot clause weakened to the `(0,0)`-slot; it is the package that
the coherent limit *family* of `E5` is built from (the remaining slots are recovered at each fake
time separately, by a fresh extraction). -/
def ConvLev0H6 (α B : ℝ) (G : ℕ → Fn) (f : Fn) : Prop :=
  (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
    TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G n p.1 p.2) (fun p => f p.1 p.2) Filter.atTop K) ∧
  ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 ∧
  Work.Spaces.HkNorm α 6 f ≤ B

/-- The level-`0` convergence clause, unbundled. -/
theorem ConvLev0H6.conv {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLev0H6 α B G f) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G n p.1 p.2) (fun p => f p.1 p.2)
        Filter.atTop K := h.1

/-- The `C⁴`-clause of `ConvLev0H6`. -/
theorem ConvLev0H6.contDiffOn {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLev0H6 α B G f) :
    ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := h.2.1

/-- The `ℋ⁶`-bound of `ConvLev0H6`. -/
theorem ConvLev0H6.hkNorm_le {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLev0H6 α B G f) :
    Work.Spaces.HkNorm α 6 f ≤ B := h.2.2

/-- `ConvLocUnifH6` is stronger: it implies `ConvLev0H6` (its slot clause at `(0,0)` is the
level-`0` convergence). -/
theorem ConvLocUnifH6.toLev0 {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLocUnifH6 α B G f) :
    ConvLev0H6 α B G f :=
  ⟨fun K hK hKQ => h.1 K hK hKQ 0 0 (by norm_num), h.2.1, h.2.2⟩

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity of the leaf weights of the `IP4`-unfolding on the open quadrant

`Work.FTS.TransportS.IsLeafW α a ρ` says that `ρ` is one of the three *leaf weights*

* `leafEta     = w(z)² · sin(2θ)^{-η}`,
* `leafOne     = w(z)²`,
* `leafGam α   = w(z)² · sin(2θ)^{-γ(α)}` (only for slots with `a ≥ 1`),

with `w z = (1+z)²/z²`.  On the **open** quadrant `Q0 = (0,∞) × (0,π/2)` every one of them is
continuous: `w` is continuous off `z = 0` (its pole) and `sin(2θ) > 0` on the open quadrant, so
`Real.rpow` is continuous in the base there.

This is the regularity hypothesis the transfer estimates of `JepsTransfer` consume (e.g. the
convolution identities relating `logPair` to the pairings `slotPairing`).
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3

/-- The radial factor `z ↦ w z = (1+z)²/z²` of the leaf weights is continuous on the open
quadrant (the pole at `z = 0` is outside `Q0`). -/
private theorem continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- The angular factor `θ ↦ sin(2θ)^q` is continuous on the open quadrant for every real
exponent `q` (the base is positive there, so no junk value of `Real.rpow` occurs). -/
private theorem continuousOn_sinpow_Q0 (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ q) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => ?_)
  exact Or.inl (ne_of_gt (hsinpos p hp))

/-- **Every leaf weight of the `IP4`-unfolding is continuous on the open quadrant.** -/
theorem continuousOn_leafW {α : ℝ} {a : ℕ} {w : ℝ → ℝ → ℝ}
    (h : Work.FTS.TransportS.IsLeafW α a w) :
    ContinuousOn (Function.uncurry w) Work.FTS.EllipticEst.Q0 := by
  rcases h with rfl | rfl | ⟨_, rfl⟩
  · have he : Function.uncurry Work.FTS.TransportS.leafEta = fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := rfl
    rw [he]
    exact (continuousOn_w_Q0.pow 2).mul (continuousOn_sinpow_Q0 (-(Work.Spaces.eta)))
  · have he : Function.uncurry Work.FTS.TransportS.leafOne = fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 := rfl
    rw [he]
    exact continuousOn_w_Q0.pow 2
  · have he : Function.uncurry (Work.FTS.TransportS.leafGam α) = fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) := rfl
    rw [he]
    exact (continuousOn_w_Q0.pow 2).mul (continuousOn_sinpow_Q0 (-(Work.Spaces.gam α)))

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.slot_lip_limit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux

/-- **The slot Lipschitz bound passes to the locally uniform limit.**

If every slot `D_z^j D_θ^i` (`j + i ≤ 1`) of the profile family `τ ↦ slice (G n) τ` is
Lipschitz in `τ` with a constant `C` that is uniform in `n` on each compact subset `K` of the
quadrant `Q0`, and if for every `τ ∈ [0,T]` the slots of order `≤ 4` of `slice (G n) τ` converge
to those of `F τ` locally uniformly (the `ConvLocUnifH6` package), then the same slots of the
limit family `F` are Lipschitz in `τ` on `K` with the same constant.

The proof is the standard one: fix the two times `τ, τ'` and the point `p`, apply the uniform
bound to the `n`-th member and pass to the limit `n → ∞` using `le_of_tendsto_of_tendsto'`,
the pointwise convergence at `p` being `TendstoUniformlyOn.tendsto_at` (at the two times
separately). -/
theorem slot_lip_limit {G : ℕ → Work.FTS.Galerkin.Fam} {F : ℝ → Work.FTS.Galerkin.Fn}
    {α B T : ℝ}
    (hconv : ∀ τ ∈ Set.Icc 0 T,
      Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) τ) (F τ))
    (hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 1 → ∀ p ∈ K,
        ∀ τ ∈ Set.Icc 0 T, ∀ τ' ∈ Set.Icc 0 T,
          |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ) p.1 p.2
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ') p.1 p.2|
            ≤ C * |τ - τ'|) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 1 → ∀ p ∈ K,
        ∀ τ ∈ Set.Icc 0 T, ∀ τ' ∈ Set.Icc 0 T,
          |Work.Spaces.mixed j i (F τ) p.1 p.2
            - Work.Spaces.mixed j i (F τ') p.1 p.2| ≤ C * |τ - τ'| := by
  intro K hK hKQ0
  obtain ⟨C, hC0, hClip⟩ := hlip K hK hKQ0
  refine ⟨C, hC0, ?_⟩
  intro j i hji p hp τ hτ τ' hτ'
  -- the slots of order `≤ 1` are among the slots of order `≤ 4` covered by `hconv`
  have hji4 : j + i ≤ 4 := by omega
  have huτ := Work.FTS.StrongEps.ConvLocUnifH6.conv (hconv τ hτ) K hK hKQ0 j i hji4
  have huτ' := Work.FTS.StrongEps.ConvLocUnifH6.conv (hconv τ' hτ') K hK hKQ0 j i hji4
  -- pointwise convergence of the two slots at the fixed point `p`
  have h1 := huτ.tendsto_at hp
  have h2 := huτ'.tendsto_at hp
  -- pass to the limit in the modulus of the increment
  have h3 : Filter.Tendsto
      (fun n : ℕ => |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ) p.1 p.2
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ') p.1 p.2|)
      Filter.atTop
      (nhds |Work.Spaces.mixed j i (F τ) p.1 p.2
          - Work.Spaces.mixed j i (F τ') p.1 p.2|) := (h1.sub h2).abs
  exact le_of_tendsto_of_tendsto' h3 tendsto_const_nhds
    (fun n => hClip n j i hji p hp τ hτ τ' hτ')

end Work.FTS.StrongEps.E5Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.HkIntegrand_three_perz_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Integrability of a finite sum of integrable functions -/

private lemma integrable_finsetSum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ} (h : ∀ i ∈ s, MeasureTheory.Integrable (g i) μ) :
    MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MeasureTheory.integrable_zero ℝ ℝ μ
  | insert a s ha ih =>
      have h1 : MeasureTheory.Integrable (g a) μ := h a (Finset.mem_insert_self a s)
      have h2 : MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      rw [show (fun x : ℝ => ∑ i ∈ insert a s, g i x)
          = fun x : ℝ => g a x + ∑ i ∈ s, g i x from by
        funext x; rw [Finset.sum_insert ha]]
      exact h1.add h2

/-! ## The integrand at `z = 0` -/

private theorem HkIntegrand_three_zero (α : ℝ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α 3 f 0 θ = 0 := by
  have hw : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
  have h1 : ∀ i : ℕ, (Work.Spaces.DzIter i f 0 θ
      * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
    intro i; rw [hw, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have h2 : ∀ i j : ℕ, (Work.Spaces.mixed j i f 0 θ * Work.Spaces.Wt α 0 θ) ^ 2 = 0 := by
    intro i j
    rw [Work.Spaces.Wt, hw, zero_mul, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [Work.Spaces.HkIntegrand]
  simp only [h1, h2, ite_self, Finset.sum_const_zero, add_zero]

/-! ## The per-`z` bound for a single `z`-slot, against the level-`4` norm -/

private theorem zslot_perz_le_four (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {i : ℕ} (hi : i ≤ 3) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 3 * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f := by
  obtain ⟨hswap, hGint, hGslice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hF hmem
  set R₀ : ℝ := max z 2 with hR₀
  have hzR : z ≤ R₀ := le_max_left z 2
  have h2R : (2 : ℝ) ≤ R₀ := le_max_right z 2
  have hRpos : 0 < R₀ := lt_of_lt_of_le (by norm_num) h2R
  have hcoef : (Work.Spaces.w z) ^ 2 * (2 + 2 / R₀) ≤ 3 * (Work.Spaces.w z) ^ 2 := by
    have h1 : 2 / R₀ ≤ 1 := by
      rw [div_le_one hRpos]
      linarith
    nlinarith [sq_nonneg (Work.Spaces.w z)]
  have hle : (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun σ : ℝ => (3 * (Work.Spaces.w z) ^ 2)
        * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)) := by
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ, hGslice] with σ hσ hσint
    have hwin :=
      Work.FTS.StrongEps.E5Aux.zslot_window_perz α hF 4 i (by omega) hz hzR hσ hσint
    have hI : 0 ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ :=
      integral_nonneg fun s => Work.Spaces.HkIntegrand_nonneg α 4 f s σ
    calc (Work.Spaces.DzIter i f z σ
            * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / R₀)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) := hwin
      _ = ((Work.Spaces.w z) ^ 2 * (2 + 2 / R₀))
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) := by ring
      _ ≤ (3 * (Work.Spaces.w z) ^ 2)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) :=
          mul_le_mul_of_nonneg_right hcoef hI
  have hLI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
      * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.integrableOn_zSummand α 4 hF hmem i (by omega)
      (Set.mem_Ici.mpr hz.le)
  have hRI : MeasureTheory.Integrable (fun σ : ℝ => (3 * (Work.Spaces.w z) ^ 2)
      * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hGint.const_mul _
  have hmain := MeasureTheory.integral_mono_ae hLI hRI hle
  rw [MeasureTheory.integral_const_mul, hswap] at hmain
  exact hmain

/-! ## The per-`z` bound for a single mixed slot, against the level-`4` norm -/

/-- The uniform angular slice bound `Work.FTS.OpenPkg.ProdOpen.sliceAng_le`, as a predicate
in its constant, so that it can be passed around. -/
private def SliceAngBd (C : ℝ) : Prop :=
  ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f → 1 ≤ a → a + b ≤ 3 →
    ∀ z : ℝ, 0 < z →
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ C * Work.Spaces.HkSq α 4 f

private theorem mixed_perz_le_four {C : ℝ} (hC : SliceAngBd C) {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 3) {z : ℝ}
    (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ (C * (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 4 f := by
  have hcongr : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    rw [← MeasureTheory.integral_const_mul]
    refine Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo (fun θ hθ => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hs]
    ring
  rw [hcongr]
  have hb := hC α f j i hα0 hα1 hF hmem hi hij z hz
  calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (Work.Spaces.w z) ^ 2 * (C * Work.Spaces.HkSq α 4 f) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = (C * (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 4 f := by ring

/-! ## Integrability of a mixed slot of the level-`3` integrand -/

private lemma integrableOn_if_mixed_three (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (i j : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 3
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      Work.Spaces.Iθ := by
  by_cases h : 1 ≤ i ∧ i + j ≤ 3
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 3
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 from by
      funext θ; rw [if_pos h]]
    refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le))
      (Work.FTS.GalBasis.cc.aesm_slice_mixed_Wt_sq hF α j i hz) ?_
    rw [MeasureTheory.ae_restrict_iff'
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    exact Filter.Eventually.of_forall fun θ _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j h.1 (by omega)
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 3
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun _ : ℝ => (0 : ℝ) from by funext θ; rw [if_neg h]]
    exact MeasureTheory.integrableOn_zero

/-! ## The target -/

theorem HkIntegrand_three_perz_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
      α ∈ Set.Ioc 0 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3 f z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α 4 f) ^ 2 := by
  obtain ⟨Cang, hCangpos, hCang⟩ := Work.FTS.OpenPkg.ProdOpen.sliceAng_le
  have hSAB : SliceAngBd Cang := hCang
  refine ⟨12 + 16 * Cang, by linarith, ?_⟩
  intro α f hα hF hmem z hz
  obtain ⟨hα0, hα1⟩ := hα
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- ### the degenerate case `z = 0`
    subst hz0
    have hzero : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3 f 0 θ) = 0 := by
      rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α 3 f 0 θ) = fun _ : ℝ => (0 : ℝ)
        from funext (fun θ => HkIntegrand_three_zero α f θ)]
      simp
    rw [hzero]
    have hCpos : 0 < 12 + 16 * Cang := by linarith
    have hw : (0 : ℝ) ≤ 1 + (Work.Spaces.w 0) ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg hCpos.le hw) (sq_nonneg _)
  · -- ### the main case `z > 0`
    have hPint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range 4, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum _ (fun i hi =>
        Work.FTS.EllipticEst.integrableOn_zSummand α 4 hF hmem i
          (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))
    have hMint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
          (if 1 ≤ i ∧ i + j ≤ 3
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j _ => integrableOn_if_mixed_three α hF hmem i j hzpos))
    have hdec : (fun θ : ℝ => Work.Spaces.HkIntegrand α 3 f z θ)
        = fun θ : ℝ => (∑ i ∈ Finset.range 4, (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
              (if 1 ≤ i ∧ i + j ≤ 3
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      funext θ
      rw [Work.Spaces.HkIntegrand]
    have hPb : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 4, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 12 * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range 4) (hf := fun i hi =>
        Work.FTS.EllipticEst.integrableOn_zSummand α 4 hF hmem i
          (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))]
      calc ∑ i ∈ Finset.range 4, (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range 4,
              (3 * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f) :=
            Finset.sum_le_sum fun i hi => zslot_perz_le_four α hF hmem
              (by rw [Finset.mem_range] at hi; omega) hzpos
        _ = 12 * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
            ring
    have hMb : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
          (if 1 ≤ i ∧ i + j ≤ 3
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ 16 * (Cang * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range 4) (hf := fun i _ =>
        integrable_finsetSum _ (fun j _ => integrableOn_if_mixed_three α hF hmem i j hzpos))]
      calc ∑ i ∈ Finset.range 4, (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range 4,
              (if 1 ≤ i ∧ i + j ≤ 3
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range 4,
              (4 * (Cang * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [MeasureTheory.integral_finsetSum (s := Finset.range 4) (hf := fun j _ =>
              integrableOn_if_mixed_three α hF hmem i j hzpos)]
            calc ∑ j ∈ Finset.range 4, (∫ θ in Work.Spaces.Iθ,
                    (if 1 ≤ i ∧ i + j ≤ 3
                      then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
                ≤ ∑ _j ∈ Finset.range 4,
                    (Cang * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f) := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  by_cases hij : 1 ≤ i ∧ i + j ≤ 3
                  · simp only [if_pos hij]
                    exact mixed_perz_le_four hSAB hα0 hα1 hF hmem hij.1 (by omega) hzpos
                  · simp only [if_neg hij]
                    have h1 : 0 ≤ Cang * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f :=
                      mul_nonneg (mul_nonneg hCangpos.le (sq_nonneg _))
                        (Work.Spaces.HkSq_nonneg α 4 f)
                    simpa using h1
              _ = 4 * (Cang * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                  norm_num
        _ = 16 * (Cang * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    rw [hdec, MeasureTheory.integral_add hPint hMint]
    refine le_trans (add_le_add hPb hMb) ?_
    have hXnn : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
    have hNnn : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
    have hXle : Work.Spaces.HkSq α 4 f ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 2 := by
      have hsq : Work.Spaces.HkSq α 4 f = (Work.Spaces.HkNorm α 4 f) ^ 2 := by
        rw [Work.Spaces.HkNorm, Real.sq_sqrt hXnn]
      nlinarith [hsq, hNnn, hXnn]
    have hWnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hWle : (Work.Spaces.w z) ^ 2 ≤ 1 + (Work.Spaces.w z) ^ 2 := by linarith
    have h1 : (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f
        ≤ (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α 4 f) ^ 2 :=
      mul_le_mul hWle hXle hXnn (by linarith)
    have h2 : (12 + 16 * Cang)
          * ((Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f)
        ≤ (12 + 16 * Cang)
          * ((1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α 4 f) ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith [h2]

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroLayerSetBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SlotsZeroLayerSetBound` — the layer integral in product-measure form

The boundary-layer estimate of the zero-mode comparison argument is needed in two shapes:

* `layer_slice_le` / `layer_integral_le` (in `SlotsZeroModeIbp`) give, for a *fixed* `z > 0`,
  `∫_θ |Φ z θ|·1_{layer_n}(θ) ≤ 2C√(sliceEnergy Φ z)·(2δ_n)^((3+η)/2)`, and the corresponding
  `z`-integrated form over `[a,b]`;
* the surrounding development (`SlotsZeroModeKey2`, `SlotsZeroModeKey3`) consumes the layer
  density in the **product-measure** form
  `∫_{Q0} |Φ p.1 p.2|·1_{[a,b]}(p.1)·1_{layer_n}(p.2)`.

This file bridges the two: `setIntegral_absPhi_layer` is the Fubini identity identifying the
product-measure integral over the quadrant `Q0 = (0,∞) × (0,π/2)` with the iterated integral over
`z ∈ (0,∞)` and `θ ∈ Iθ = [0,π/2]`, and `SlotsZeroLayerSetBound` is the resulting bound.
-/

namespace Work.FTS.StrongEps.EComparison

open scoped Real Topology
open MeasureTheory Set Filter

/-- `Iθ = [0, π/2]` is measurable. -/
theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  show MeasurableSet (Set.Icc (0 : ℝ) (Real.pi / 2))
  exact measurableSet_Icc

/-- The layer `(0, 2δ_n) ∪ (π/2 - 2δ_n, π/2)` is measurable. -/
theorem layer_measurable (n : ℕ) : MeasurableSet (layer n) := by
  rw [layer_eq_union]
  exact measurableSet_Ioo.union measurableSet_Ioo

/-- The restricted measure of the quadrant is the product of the radial half-line with the
angular interval `Iθ`. -/
theorem restrict_Q0_eq_prod_Iθ :
    (volume.restrict Work.FTS.EllipticEst.Q0 : Measure (ℝ × ℝ))
      = ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
  rw [restrict_Q0_eq_prod, restrict_Ioo_eq_Iθ]

/-- **Fubini for the layer density.**  The product-measure integral over the quadrant of
`|Φ|·1_{[a,b]}(z)·1_{layer n}(θ)` equals the iterated integral over `z ∈ (0,∞)` and `θ ∈ Iθ`. -/
theorem setIntegral_absPhi_layer {Φ : ℝ → ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hEint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
      (Set.Icc a b)) :
    (∫ p in Work.FTS.EllipticEst.Q0,
        |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
      = ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
          |Φ z θ| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z * layerInd n θ := by
  classical
  have hcont : ContinuousOn (fun p : ℝ × ℝ => |Φ p.1 p.2|) Work.FTS.EllipticEst.Q0 :=
    continuousOn_absPhi_mode hsm
  have hind : Measurable (fun p : ℝ × ℝ =>
      (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) :=
    (measurable_const.indicator measurableSet_Icc).comp measurable_fst
  have hlay : Measurable (fun p : ℝ × ℝ => layerInd n p.2) :=
    (measurable_const.indicator (layer_measurable n)).comp measurable_snd
  have hK : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1)
      Work.FTS.EllipticEst.Q0 := integrableOn_absPhi_box hsm hΦint hEint
  have hG : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
      Work.FTS.EllipticEst.Q0 := by
    refine Integrable.mono' hK ?_ ?_
    · exact ((hcont.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet).mul
        hind.aestronglyMeasurable).mul hlay.aestronglyMeasurable
    · filter_upwards with p
      simp only [Real.norm_eq_abs, abs_mul, abs_abs, layerInd]
      rw [abs_of_nonneg (indicator_one_nonneg (A := Set.Icc a b) p.1),
        abs_of_nonneg (indicator_one_nonneg (A := layer n) p.2)]
      simpa using mul_le_mul_of_nonneg_left (indicator_one_le_one (A := layer n) p.2)
        (mul_nonneg (abs_nonneg (Φ p.1 p.2)) (indicator_one_nonneg (A := Set.Icc a b) p.1))
  have hQ0 : (volume.restrict Work.FTS.EllipticEst.Q0 : Measure (ℝ × ℝ))
      = ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := restrict_Q0_eq_prod_Iθ
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
    rw [← hQ0]
    exact hG
  have hfub := MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
      |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2) hint
  rw [show (∫ p in Work.FTS.EllipticEst.Q0,
        |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
      = ∫ p, |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2
          ∂(((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
            ((volume : Measure ℝ).restrict Work.Spaces.Iθ)) from by rw [hQ0]]
  exact hfub

/-- The boundary-layer bound in product-measure form: the `[a,b] × layer_n` part of `|Φ|` is
controlled by `2C·(2δ_n)^((3+η)/2)·∫_{[a,b]} √(sliceEnergy Φ)`. -/
theorem SlotsZeroLayerSetBound {Φ : ℝ → ℝ → ℝ} {C a b : ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hC : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
      (∫ θ in Set.Ioo 0 δ, |Φ z θ|)
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)
              * δ ^ ((3 + Work.Spaces.eta) / 2) ∧
      (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), |Φ z θ|)
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)
              * δ ^ ((3 + Work.Spaces.eta) / 2))
    (hEint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
      (Set.Icc a b))
    (hEsqrt : MeasureTheory.IntegrableOn
      (fun z => Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)) (Set.Icc a b))
    (ha : 0 < a)
    {n : ℕ} (hn0 : 0 < 2 * Work.FTS.StrongEps.EComparison.delta n)
    (hn1 : 2 * Work.FTS.StrongEps.EComparison.delta n ≤ Real.pi / 4) :
    (∫ p in Work.FTS.EllipticEst.Q0,
        |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
          * Work.FTS.StrongEps.EComparison.layerInd n p.2)
      ≤ 2 * C * (2 * Work.FTS.StrongEps.EComparison.delta n) ^ ((3 + Work.Spaces.eta) / 2)
          * (∫ z in Set.Icc a b,
              Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)) := by
  classical
  have haIcc : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hInd : ∀ z : ℝ, 0 ≤ (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z :=
    fun z => indicator_one_nonneg z
  rw [setIntegral_absPhi_layer hsm hΦint hEint]
  have hstep : (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        |Φ z θ| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z * layerInd n θ)
      ≤ ∫ z in Set.Ioi (0 : ℝ), (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
          * (2 * C * Real.sqrt (sliceEnergy Φ z)
              * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with z
      exact MeasureTheory.integral_nonneg fun θ =>
        mul_nonneg (mul_nonneg (abs_nonneg (Φ z θ)) (hInd z)) (indicator_one_nonneg θ)
    · -- integrability of the dominating slice expression
      have h1 : MeasureTheory.Integrable
          ((Set.Icc a b).indicator (fun z : ℝ => Real.sqrt (sliceEnergy Φ z))) volume :=
        hEsqrt.integrable_indicator measurableSet_Icc
      have h2 : MeasureTheory.Integrable
          ((Set.Icc a b).indicator (fun z : ℝ => Real.sqrt (sliceEnergy Φ z)))
          (volume.restrict (Set.Ioi (0 : ℝ))) :=
        h1.mono_measure MeasureTheory.Measure.restrict_le_self
      have h3 : MeasureTheory.Integrable (fun z => (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
          * Real.sqrt (sliceEnergy Φ z)) (volume.restrict (Set.Ioi (0 : ℝ))) := by
        refine h2.congr (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ Set.Icc a b
        · simp only [Set.indicator_of_mem hz, one_mul]
        · simp only [Set.indicator_of_notMem hz, zero_mul]
      refine (h3.const_mul (2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2))).congr
        (Eventually.of_forall fun z => ?_)
      ring
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => ?_
      show (∫ θ in Work.Spaces.Iθ, |Φ z θ| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
            * layerInd n θ)
          ≤ (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
              * (2 * C * Real.sqrt (sliceEnergy Φ z)
                  * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2))
      have hc : (∫ θ in Work.Spaces.Iθ, |Φ z θ| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
            * layerInd n θ)
          = (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
              * ∫ θ in Work.Spaces.Iθ, |Φ z θ| * layerInd n θ := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ _ => ?_)
        ring
      rw [hc]
      exact mul_le_mul_of_nonneg_left (layer_slice_le hΦint hC hz hn0 hn1) (hInd z)
  refine hstep.trans ?_
  rw [show (fun z : ℝ => (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
        * (2 * C * Real.sqrt (sliceEnergy Φ z)
            * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)))
      = fun z => (2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2))
          * ((Set.Icc a b).indicator (fun _ => (1 : ℝ)) z * Real.sqrt (sliceEnergy Φ z)) from by
    funext z; ring]
  rw [MeasureTheory.integral_const_mul]
  rw [show (∫ z in Set.Ioi (0 : ℝ), (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
        * Real.sqrt (sliceEnergy Φ z))
      = ∫ z in Set.Ioi (0 : ℝ), Real.sqrt (sliceEnergy Φ z)
          * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z from by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
  rw [setIntegral_mul_indicator measurableSet_Icc haIcc]

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeKey2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The cut-off identity in product-measure form -/

/-- The `bslOp_ibp` identity for the cut-off test function, product-measure form. -/
theorem perN_zero_set {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsol : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Φ z θ = 0)
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) (hρc : HasCompactSupport ρ) (hρs : tsupport ρ ⊆ Set.Ioi 0)
    (hCut : CutFacts m) (n : ℕ) :
    (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
      * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p) = 0 := by
  classical
  have hφ := modeTest_contDiff (m := m) (n := n) hρ hCut
  have hφc := modeTest_hasCompactSupport (m := m) (n := n) hρc hCut
  have hφs := modeTest_tsupport_subset_Q0 (m := m) (n := n) hρs hCut
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc hp.2.1,
      lt_of_le_of_lt hp.2.2 hd⟩
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen Φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mpr (fun k => hsm k)
  have htestsm : Work.FTS.EllipticEst.SmoothOpen (modeTest m ρ n) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun k => (hφ k).contDiffOn)
  have h1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Φ p.1 p.2
      * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) Work.FTS.EllipticEst.Q0 := by
    refine integrableOn_Q0_of_box ha hab.le hc hcd.le hd (fun p hp => ?_) ?_
    · rw [Work.FTS.H2.ModalSolR.bslOp_eq_zero_off_box (α := α) hbox hp]
      ring
    · exact ((hΦsm.continuousOn.mono hKsub).mul
        ((continuousOn_bslOp_of_smoothOpen htestsm).mono hKsub)).mul
          ((continuousOn_weight α).mono hKsub)
  have h2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Elliptic.bslOp α Φ p.1 p.2) * (modeTest m ρ n) p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) Work.FTS.EllipticEst.Q0 := by
    refine (integrableOn_zero (s := Work.FTS.EllipticEst.Q0)).congr_fun
      (fun p hp => ?_) Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    change (0 : ℝ) = (Work.Elliptic.bslOp α Φ p.1 p.2) * (modeTest m ρ n) p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
    rw [hsol p.1 hz p.2 hθ0 hθ1]
    ring
  have hibp := Work.EllipticEst.ModalSolution.bslOp_ibp α (u := Φ) (φ := modeTest m ρ n)
    hsm hφ hφc hφs h1 h2
  have hR : (∫ p in Work.FTS.EllipticEst.Q0, (Work.Elliptic.bslOp α Φ p.1 p.2)
      * (modeTest m ρ n) p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) = 0 := by
    have hcongr := MeasureTheory.setIntegral_congr_fun (μ := volume)
      (f := fun p : ℝ × ℝ => (Work.Elliptic.bslOp α Φ p.1 p.2) * (modeTest m ρ n) p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) (g := fun _ => (0 : ℝ))
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet (fun p hp => by
        obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        show (Work.Elliptic.bslOp α Φ p.1 p.2) * (modeTest m ρ n) p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2) = 0
        rw [hsol p.1 hz p.2 hθ0 hθ1]
        ring)
    rw [hcongr]
    simp
  change (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
      * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) = 0
  rw [hibp, hR]

/-! ## The pointwise difference bound -/


end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroPairingFubini =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.StrongEps.EComparison

theorem SlotsZeroPairingFubini {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ} {a b : ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) (ha : 0 < a)
    (hsub : tsupport ρ ⊆ Set.Icc a b)
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hEint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
      (Set.Icc a b)) :
    (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            p.1 p.2
        * Work.FTS.StrongEps.EComparison.bslWeight α p)
      = ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Φ z θ
          * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              z θ
          * (z ^ ((5 - α) / α) * Real.cos θ) := by
  -- The integrand of the left-hand side is product-measure integrable on the quadrant
  -- (`integrableOn_modeIntegrand`, fed by the box integrability of `|Φ|`).
  have hFint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Φ p.1 p.2
      * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
      * Work.FTS.StrongEps.EComparison.bslWeight α p)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict (Set.Ioo 0 (Real.pi / 2)))) := by
    rw [← Work.FTS.StrongEps.EComparison.restrict_Q0_eq_prod]
    exact Work.FTS.StrongEps.EComparison.integrableOn_modeIntegrand (α := α) (m := m)
      hsm hρ ha hsub (Work.FTS.StrongEps.EComparison.integrableOn_absPhi_box hsm hΦint hEint)
  -- Rewrite the set integral over `Q0 = (0,∞) × (0,π/2)` as an integral against the
  -- product of the two restricted measures.
  rw [show (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
        * Work.FTS.StrongEps.EComparison.bslWeight α p)
      = ∫ p, (Φ p.1 p.2
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
        * Work.FTS.StrongEps.EComparison.bslWeight α p)
        ∂(((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
          ((volume : Measure ℝ).restrict (Set.Ioo 0 (Real.pi / 2)))) from by
    rw [Work.FTS.StrongEps.EComparison.restrict_Q0_eq_prod]]
  -- Fubini.
  rw [MeasureTheory.integral_prod _ hFint]
  -- Replace the angular interval `(0,π/2)` by `Iθ = [0,π/2]` (same restricted measure),
  -- and unfold the pairing weight `bslWeight α (z,θ) = z^((5-α)/α)·cos θ`.
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  rw [Work.FTS.StrongEps.EComparison.restrict_Ioo_eq_Iθ]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  simp [Work.FTS.StrongEps.EComparison.bslWeight]

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.mixed_fam_continuous_Icc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1000000

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.JepsJoint

/-! ## An open-set version of `mixed_fam_continuous`

The sibling's proof only uses that its domain is open (through `contDiffOn_mixedJ`), so it works
verbatim on any open subset of `ℝ × (ℝ × ℝ)`.  This form is what the pull-back argument below
needs. -/


/-! ## The closed slab with nonnegative horizon -/








/-! ## The requested statement -/


end Work.FTS.StrongEps.EpsE4Thr.JepsJoint
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.integrableOn_Pz_div_pow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.L12Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The angular interval `Iθ = [0, π/2]` is measurable. -/
private lemma measurableSet_Iθ_fts : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

/-- **A.e. strong measurability of the `z`-slice integral.**

The uncurried integrand
`(z,θ) ↦ (D_z^k x (z,θ))² · sin(2θ)^{-η} / z⁴` is continuous on the open quadrant
(`SmoothOpen x` keeps `D_z^k x` continuous there, and the two weights are continuous on the
open quadrant because `sin(2θ) > 0` and `z ≠ 0` there), so
`Work.Spaces.aesm_of_continuousOn_Qd` together with
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` gives the a.e. strong measurability
of its angular integral. -/
private lemma aesm_integral_Pzsplit (x : Work.FTS.Galerkin.Fn) (k : ℕ)
    (hreg : Work.FTS.EllipticEst.SmoothOpen x) :
    AEStronglyMeasurable (fun z : ℝ => ∫ θ : ℝ,
        ((Work.Spaces.DzIter k x z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          / z ^ 4) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.DzIter k x p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))
        / p.1 ^ 4) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).mono
        (subset_univ _)
    have hsinpow : ContinuousOn (fun p : ℝ × ℝ =>
        (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      refine hsin.rpow_const (fun p hp => Or.inl ?_)
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos]))
    exact ContinuousOn.div (ContinuousOn.mul ((hreg.DzIter k).continuousOn.pow 2) hsinpow)
      (continuousOn_fst.pow 4) (fun p hp => pow_ne_zero 4 (ne_of_gt hp.1))
  exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'

/-- **A.e. strong measurability of `z ↦ Pz x k z / z⁴` on `(0,1)`.**

For `z > 0` one may pull the factor `z^{-4}` inside the angular integral
(`MeasureTheory.integral_div`), which identifies the function with the slice integral of the
previous lemma; restricting the measure to `(0,1)` gives the claim. -/
private lemma aesm_Pz_div_pow {α : ℝ} {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) (k : ℕ) :
    AEStronglyMeasurable (fun z : ℝ => Pz x k z / z ^ 4)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Work.Spaces.Iz := fun z hz => le_of_lt hz.1
  have hA : AEStronglyMeasurable (fun z : ℝ => ∫ θ : ℝ,
      ((Work.Spaces.DzIter k x z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        / z ^ 4) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    have h1 := (aesm_integral_Pzsplit x k hx.reg).restrict (s := Set.Ioo (0 : ℝ) 1)
    rwa [MeasureTheory.Measure.restrict_restrict_of_subset hsub] at h1
  refine hA.congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ?_)
  show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter k x z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 4) = Pz x k z / z ^ 4
  rw [MeasureTheory.integral_div, Pz]

/-- **The pointwise bound `Pz x k z / z⁴ ≤ ∫_θ HkIntegrand α 10 x z θ` for `z > 0`.**

`(D_z^k x · w / sin(2θ)^{η/2})²` is a summand of `HkIntegrand α 10 x` (`k ≤ 10`), and by the
weight identity `summand_sq_eq` it equals `(D_z^k x)² · sin(2θ)^{-η} · w²`.  Integrating in `θ`
and pulling `w(z)²` out of the integral gives `w(z)² · Pz x k z ≤ ∫_θ HkIntegrand α 10 x z θ`;
on the other hand `Pz x k z / z⁴ · (1+z)⁴ = Pz x k z · w(z)²` and `(1+z)⁴ ≥ 1`. -/
private lemma Pz_div_pow_le_integral_HkIntegrand {α : ℝ} {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {k : ℕ} (hk : k ≤ 10) {z : ℝ} (hz : 0 < z) :
    Pz x k z / z ^ 4 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 10 x z θ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 10 x z θ)
      Work.Spaces.Iθ := hx.mem10.1 z hzI
  -- the pointwise bound on the angular interval
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, (Work.Spaces.DzIter k x z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 10 x z θ := by
    intro θ hθ
    rw [← summand_sq_eq x k hθ]
    exact Work.Spaces.sq_le_HkIntegrand_z α 10 x z θ k hk
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ : ℝ => (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter k x z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ_fts
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _)))
  have hle : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter k x z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => Work.Spaces.HkIntegrand α 10 x z θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ_fts (fun θ hθ => by
      have h := hpt θ hθ
      show (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter k x z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ Work.Spaces.HkIntegrand α 10 x z θ
      rw [show (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter k x z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          = (Work.Spaces.DzIter k x z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.w z) ^ 2 from by ring]
      exact h)
  have hmono : (Work.Spaces.w z) ^ 2 * Pz x k z
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 10 x z θ := by
    have hstep : (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter k x z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.DzIter k x z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
      (MeasureTheory.integral_const_mul _ _).symm
    rw [Pz, hstep]
    exact MeasureTheory.integral_mono_of_nonneg hnn hInt hle
  -- `Pz / z⁴ ≤ w² · Pz`
  have hkey : Pz x k z * (Work.Spaces.w z) ^ 2 = Pz x k z / z ^ 4 * (1 + z) ^ 4 := by
    rw [Work.Spaces.w]
    field_simp
  have hchain : Pz x k z / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 * Pz x k z := by
    have hnn2 : 0 ≤ Pz x k z / z ^ 4 :=
      div_nonneg (Pz_nonneg x k z) (pow_nonneg hz.le 4)
    have h1 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith)
    calc Pz x k z / z ^ 4 ≤ Pz x k z / z ^ 4 * (1 + z) ^ 4 :=
          le_mul_of_one_le_right hnn2 h1
      _ = Pz x k z * (Work.Spaces.w z) ^ 2 := hkey.symm
      _ = (Work.Spaces.w z) ^ 2 * Pz x k z := by ring
  exact le_trans hchain hmono

/-- **`Pz x k · z^{-4}` is integrable on `(0,1)` for a `ClassC` profile.**

Here `Pz x k z = ∫_{Iθ} (D_z^k x (z,θ))² · sin(2θ)^{-η} dθ` (`η = 99/100`,
`D_z = z ∂_z`, `Iθ = [0,π/2]`; see `Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs`).

Proof route: `ClassC α x` carries `reg : SmoothOpen x` and `mem10 : HkMem α 10 x`.  For
`z ∈ Iz` the slot `(D_z^k x z θ * (w z / sin(2θ)^{η/2}))²` is a summand of
`HkIntegrand α 10 x z θ` (`Work.Spaces.sq_le_HkIntegrand_z`, `k ≤ 4 ≤ 10`), and by
`L12Aux.summand_sq_eq` (proved in `Defs`) it equals
`(D_z^k x z θ)² * sin(2θ)^{-η} * (w z)²`.  Hence, with
`F z := ∫ θ in Iθ, (DzIter k x z θ * (w z / sin(2θ)^{η/2}))²`, one has the pointwise bound
`Pz x k z / z^4 ≤ F z` for `z ∈ (0,1)` (because `(w z)² z^4 = (1+z)^4 ≥ 1`), and
`F` is integrable on `Iz` (dominated by `z ↦ ∫ θ, HkIntegrand α 10 x z θ`, which is integrable
by `mem10.2`); see `Work.Spaces.L2Sq_DzIter_le_HkSq` and, for the measurability of `F`,
`Work.Spaces.aesm_of_continuousOn_Qd` together with
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` and
`Work.FTS.EllipticEst.SmoothOpen.continuousOn_summand`.  Restricting to `(0,1)` and applying
`MeasureTheory.Integrable.mono'` gives the claim. -/
theorem integrableOn_Pz_div_pow {α : ℝ} {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {k : ℕ} (hk : k ≤ 4) :
    MeasureTheory.IntegrableOn (fun z => Pz x k z / z ^ 4) (Set.Ioo (0 : ℝ) 1) := by
  have hk10 : k ≤ 10 := by omega
  have hmajI : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 10 x z θ)
      Work.Spaces.Iz := hx.mem10.2
  have hmaj : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 10 x z θ)
      (Set.Ioo (0 : ℝ) 1) :=
    hmajI.mono_set (fun z hz => le_of_lt hz.1)
  refine MeasureTheory.Integrable.mono' hmaj (aesm_Pz_div_pow hx k) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ?_)
  have hle := Pz_div_pow_le_integral_HkIntegrand hx hk10 hz.1
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Pz_nonneg x k z) (pow_nonneg hz.1.le 4))]
  exact hle

end Work.FTS.StrongEps.EpsE4Thr.L12Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSinPow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The iterated angular derivative of `sin²θ`

`D_θ f = sin(2θ) ∂_θ f`, and `D_θ (sin²θ) = sin(2θ)²`.  Since `D_θ = sin(2θ) · ∂_θ` is a
derivation, every iterate of `sin²` is of the form

`D_θ^r (sin²) (θ) = sin(2θ)² · P_r(cos 2θ)`      (`r ≥ 1`),

where `P_r` is the polynomial produced by the recursion

`P_1 = 1`,   `P_{r+1} = 4 X P_r - 2 (1 - X²) P_r'`.

Indeed, for `G_p(θ) = sin(2θ)² · p(cos 2θ)` one computes
`Lop (G_p) = G_{4Xp - 2(1-X²)p'}` (`Lop u θ = sin(2θ) u'(θ)` is the one-variable action of
`D_θ`), so the identity follows by induction.  The bound `|P_r(c)| ≤ ∑ |coeff|` for
`|c| ≤ 1` converts this into the uniform estimate
`|D_θ^r (sin²) (θ)| ≤ Ksin r · sin(2θ)²` for every `θ`, which is what the transport
estimates of `IP4` need. -/

noncomputable section

/-- The auxiliary function `θ ↦ sin(2θ)² · p(cos 2θ)` attached to a polynomial `p`. -/
private def Gfun (p : Polynomial ℝ) : ℝ → ℝ :=
  fun θ => (Real.sin (2 * θ)) ^ 2 * p.eval (Real.cos (2 * θ))







/-- `Lop (sin²) = Gfun 1 = sin(2θ)²`. -/
private lemma Lop_sin_sq : Work.Spaces.Lop (fun θ : ℝ => Real.sin θ ^ 2) = Gfun 1 := by
  funext θ
  change Real.sin (2 * θ) * deriv (fun θ : ℝ => Real.sin θ ^ 2) θ
    = (Real.sin (2 * θ)) ^ 2 * (1 : Polynomial ℝ).eval (Real.cos (2 * θ))
  have hd : deriv (fun θ : ℝ => Real.sin θ ^ 2) θ = Real.sin (2 * θ) := by
    have h := (Real.hasDerivAt_sin θ).pow 2
    have h2 : ((2 : ℕ) : ℝ) * Real.sin θ ^ (2 - 1) * Real.cos θ = Real.sin (2 * θ) := by
      rw [Real.sin_two_mul]
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [h2] at h
    convert h.deriv using 1
  rw [hd, Polynomial.eval_one, mul_one]
  ring








end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.slotEnergyLeHkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-! ## The two endpoints are null for the angular measure -/

/-- For `volume.restrict Iθ` the two endpoints `0`, `π/2` are null, so `θ` lies in the open
interval almost everywhere.  (`Icc 0 (π/2)` and `Ioo 0 (π/2)` agree a.e.) -/
private theorem ae_mem_Ioo_Iθ_prv :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## Nonnegativity of the leaf weights on the closed quadrant -/

/-- Every leaf weight of `IP6` is nonnegative on `Iz × Iθ`. -/
private theorem leaf_nonneg_prv {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ := by
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · intro z hz θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
  · intro z hz θ hθ
    exact sq_nonneg _
  · intro z hz θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-! ## The pointwise domination of a leaf weight -/

/-- The *two* leaf weights of a `D_z`-only slot (`a = 0`) — `leafEta` and `leafOne` — are
dominated by the square of the block weight `Whz`.

(`leafGam` is deliberately excluded: at `a = 0` it is not a leaf weight
(`Work.FTS.TransportS.IsLeafW` requires `1 ≤ a` for `leafGam`), and indeed
`w²σ^{-γ} ≤ w²σ^{-η}` is *false* on the open quadrant since `σ^{-γ} ≥ σ^{-η}`.) -/
private theorem leaf_le_Whz_sq_prv {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (ha : a = 0) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
  subst ha
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨ha1, _⟩
  · rw [Work.FTS.TransportS.leafEta, Work.FTS.H2.hbi_Whz_sq z θ hs]
  · rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Whz_sq z θ hs]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
  · exfalso; omega

/-- Every leaf weight is dominated by the square of the block weight `Wm`. -/
private theorem leaf_le_Wm_sq_prv {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ ≤ (Work.FTS.H2.Wm α z θ) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · rw [Work.FTS.TransportS.leafEta, Work.FTS.H2.hbi_Wm_sq α z θ hs]
    exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα hθI) (sq_nonneg _)
  · rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Wm_sq α z θ hs]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (Work.FTS.TransportS.one_le_rpow_neg (le_of_lt (Work.Spaces.gam_pos hα)) hθ)
  · rw [Work.FTS.TransportS.leafGam, Work.FTS.H2.hbi_Wm_sq α z θ hs]

/-- **The pointwise slot domination.**  For a leaf weight `ρ` of the slot `a` and any slot
`(a,b)` of order `≤ N`, the weighted slot of any datum `h` is dominated by the
`ℋ^N`-integrand of `h` on the open quadrant. -/
private theorem leaf_dom_gen_prv {α : ℝ} (hα : 0 < α) {N a b : ℕ} (hab : a + b ≤ N)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {h : ℝ → ℝ → ℝ}
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ * (Work.Spaces.mixed b a h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α N h z θ := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    rw [Work.Spaces.mixed_zero_right]
    have hb : b ≤ N := by omega
    calc ρ z θ * (Work.Spaces.DzIter b h z θ) ^ 2
        ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter b h z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (leaf_le_Whz_sq_prv hρ rfl hθ) (sq_nonneg _)
      _ = (Work.Spaces.DzIter b h z θ * Work.FTS.H2.Whz z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α N h z θ :=
          Work.Spaces.sq_le_HkIntegrand_z α N h z θ b hb
  · have h1 : 1 ≤ a := hpos
    calc ρ z θ * (Work.Spaces.mixed b a h z θ) ^ 2
        ≤ (Work.FTS.H2.Wm α z θ) ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (leaf_le_Wm_sq_prv hα hρ hθ) (sq_nonneg _)
      _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          simp only [Work.FTS.H2.Wm]; ring
      _ ≤ Work.Spaces.HkIntegrand α N h z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α N h z θ a b h1 hab

/-! ## The requested single-slot energy bound -/


end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbSub.slotWeightBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbSub

/-! ## Elementary nonnegativity -/

/-- `w z ≥ 0` (for every `z`). -/
private theorem w_nonneg_l (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- `Whz z θ ≥ 0` on the closed quadrant. -/
private theorem Whz_nonneg_l {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.H2.Whz z θ := by
  rw [Work.FTS.H2.Whz_eq]
  exact div_nonneg (w_nonneg_l z)
    (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-- `Wm α z θ ≥ 0` on the closed quadrant. -/
private theorem Wm_nonneg_l (α : ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.H2.Wm α z θ := by
  rw [Work.FTS.H2.Wm_eq, Work.Spaces.Wt, Work.Spaces.wTheta]
  exact mul_nonneg (w_nonneg_l z)
    (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-! ## Single slots are dominated by `HkIntegrand α 6 g` -/

/-- **Every slot of level `≤ 6`, weighted by `Whz`, is dominated by `HkIntegrand α 6 g`.**
If the slot carries a `θ`-derivative (`i ≥ 1`) this is a mixed summand, compared against
the `γ`-weight via `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}`; if `i = 0` it is the pure `D_z`-summand
`i = j ≤ 6`. -/
private theorem slot_whz_sq_le {α : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hα : 0 < α) (_hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {i j : ℕ} (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i g z θ * Work.FTS.H2.Whz z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  rcases eq_or_ne i 0 with hi | hi
  · subst hi
    simpa only [Work.Spaces.mixed_zero_right, Work.FTS.H2.Whz_eq] using
      Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ j (by omega)
  · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi
    have hW := Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ i j hi1 hij
    rw [← Work.FTS.H2.Wm_eq] at hW
    have hsq := Work.FTS.H2.Whz_Wm_sq α hα z θ hθI
    have hle : (Work.FTS.H2.Whz z θ) ^ 2 ≤ (Work.FTS.H2.Wm α z θ) ^ 2 := by
      rw [hsq.1, hsq.2]
      exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα hθI) (sq_nonneg _)
    have h2 : (Work.Spaces.mixed j i g z θ * Work.FTS.H2.Whz z θ) ^ 2
        ≤ (Work.Spaces.mixed j i g z θ * Work.FTS.H2.Wm α z θ) ^ 2 := by
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    exact le_trans h2 hW

/-- **Every slot of level `≤ 6` carrying a `θ`-derivative is dominated by
`HkIntegrand α 6 g` when weighted by `Wm`.** -/
private theorem slot_wm_sq_le {α : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    {i j : ℕ} (hi1 : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i g z θ * Work.FTS.H2.Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  have h := Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ i j hi1 hij
  rwa [← Work.FTS.H2.Wm_eq] at h

/-! ## The AM–GM step -/

/-- **AM–GM for two slots sharing the weight `W`**: if the two weighted slots are each
dominated by `H` then so is the product of the two slots times `W²`. -/
private theorem amgm_mul_le {X Y W H : ℝ} (hW : 0 ≤ W)
    (hX : (X * W) ^ 2 ≤ H) (hY : (Y * W) ^ 2 ≤ H) :
    |X| * |Y| * W ^ 2 ≤ H := by
  have h1 : |X| * |Y| * W ^ 2 = |X * W| * |Y * W| := by
    simp only [abs_mul, abs_of_nonneg hW]
    ring
  rw [h1]
  nlinarith [sq_nonneg (|X * W| - |Y * W|), sq_abs (X * W), sq_abs (Y * W), hX, hY]

/-! ## The target -/

theorem slotWeightBound {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} (a b u v : ℕ)
    (hab : a + b ≤ 6) (hu : 1 ≤ u) (huv : u + v ≤ 6) {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * |Work.Spaces.mixed v u g z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hρle : ρ z θ ≤ Work.FTS.TransportS.slotW α a z θ :=
    (Work.FTS.TransportS.IsLeafW_le α hα hρ).2 z θ hz hθ0 hθ1
  rcases eq_or_ne a 0 with ha | ha
  · -- the slot `(a,b)` is a pure `D_z`-slot: the leaf weight is dominated by `(Whz)²`
    subst ha
    have hρW : ρ z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
      simpa using hρle
    have hW : 0 ≤ Work.FTS.H2.Whz z θ := Whz_nonneg_l hθI
    have hX : (Work.Spaces.mixed v u g z θ * Work.FTS.H2.Whz z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      slot_whz_sq_le hα hz hθ0 hθ1 (i := u) (j := v) huv
    have hY : (Work.Spaces.mixed b 0 g z θ * Work.FTS.H2.Whz z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      slot_whz_sq_le hα hz hθ0 hθ1 (i := 0) (j := b) hab
    calc ρ z θ * |Work.Spaces.mixed v u g z θ| * |Work.Spaces.mixed b 0 g z θ|
        ≤ (Work.FTS.H2.Whz z θ) ^ 2 * |Work.Spaces.mixed v u g z θ|
            * |Work.Spaces.mixed b 0 g z θ| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hρW (abs_nonneg _)) (abs_nonneg _)
      _ = |Work.Spaces.mixed v u g z θ| * |Work.Spaces.mixed b 0 g z θ|
            * (Work.FTS.H2.Whz z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 6 g z θ := amgm_mul_le hW hX hY
  · -- the slot `(a,b)` carries a `θ`-derivative: the leaf weight is dominated by `(Wm)²`
    have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    have hρW : ρ z θ ≤ (Work.FTS.H2.Wm α z θ) ^ 2 := by
      have h := hρle
      rw [Work.FTS.TransportS.slotW_of_pos' α ha1] at h
      exact h
    have hW : 0 ≤ Work.FTS.H2.Wm α z θ := Wm_nonneg_l α hθI
    have hX : (Work.Spaces.mixed v u g z θ * Work.FTS.H2.Wm α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      slot_wm_sq_le (i := u) (j := v) hu huv
    have hY : (Work.Spaces.mixed b a g z θ * Work.FTS.H2.Wm α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      slot_wm_sq_le (i := a) (j := b) ha1 hab
    calc ρ z θ * |Work.Spaces.mixed v u g z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ (Work.FTS.H2.Wm α z θ) ^ 2 * |Work.Spaces.mixed v u g z θ|
            * |Work.Spaces.mixed b a g z θ| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hρW (abs_nonneg _)) (abs_nonneg _)
      _ = |Work.Spaces.mixed v u g z θ| * |Work.Spaces.mixed b a g z θ|
            * (Work.FTS.H2.Wm α z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 6 g z θ := amgm_mul_le hW hX hY

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbSub
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux

theorem leibniz_rad_mixed_cd6 {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ}
    (hr : ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => r z)) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ) := by
  intro z θ hz hθ0 hθ1
  -- The general finite-order Leibniz rule for `D_z^j D_θ^i` applied to `(z,θ) ↦ r z · g z θ`.
  have h := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixedMul_cd6
    (f := fun z (_ : ℝ) => r z) (g := g) hr hg j i (by omega) z θ hz hθ0 hθ1
  rw [h]
  -- Every angular derivative of a function of `z` alone vanishes, so only the `b = 0` slot of
  -- the inner (angular) sum survives.
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single 0 ?_ ?_]
  · rw [Nat.choose_zero_right, Nat.sub_zero, Work.Spaces.mixed_zero_right,
      Work.Elliptic.DzIter_rad r a z θ]
    ring
  · intro b _ hb
    rw [show Work.Spaces.mixed a b (fun z _ => r z) z θ = 0 from
      congrFun (congrFun (Work.Elliptic.mixed_rad_eq_zero r (by omega)) z) θ]
    ring
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDthAux.MslotPt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The mixed slots.**  For `1 ≤ i`, `i + j ≤ 3` the `(j,i)`-slot of the `ℋ³`-integrand of
`h·D_θ f` is dominated by `|h|²_𝒲 · HkIntegrand α 4 f`. -/
theorem mslot_le_pt : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ i j : ℕ, 1 ≤ i → i + j ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.mixed j i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          ≤ C * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro α h f hα hα1 hh hhm hf _hfm i j hi hij z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 4 h := Work.Spaces.WlInf_nonneg α 4 h hhm
  have hHInn : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hjk : j ≤ 3 := by omega
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i h (Work.Spaces.Dth f) hh hf.Dth
    z θ hz hθ0 hθ1
  have hexp : Work.Spaces.mixed j i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a h z θ
              * Work.Spaces.mixed (j - b) (i - a + 1) f z θ) := by
    rw [heq]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mixed_Dth_shift]
  have hsplit : (Work.Spaces.mixed j i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a h z θ
              * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ))) ^ 2 := by
    rw [hexp, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hsplit]
  have hterm : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      (((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a h z θ
              * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ))) ^ 2
        ≤ 2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
            * Work.Spaces.HkIntegrand α 4 f z θ) := by
    intro a ha b hb
    have hai : a ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hch1 : ((i.choose a : ℝ)) ^ 2 ≤ 256 := Work.Spaces.choose_sq_le_256 i a hai (by omega)
    have hch2 : ((j.choose b : ℝ)) ^ 2 ≤ 256 := Work.Spaces.choose_sq_le_256 j b hbj (by omega)
    have hab4 : a + b ≤ 4 := by omega
    have hDh : |Work.Spaces.mixed b a h z θ| ≤ 200 * Work.Spaces.WlInf α 4 h :=
      Work.FTS.TransportS.abs_mixed_le_WlInf_open hα hα1 hh hhm hab4 hz hθ
    have hx : (Work.Spaces.mixed b a h z θ) ^ 2
        ≤ (200 * Work.Spaces.WlInf α 4 h) ^ 2 := by
      have hB : (0 : ℝ) ≤ 200 * Work.Spaces.WlInf α 4 h := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDh).1
      have h2 := (abs_le.mp hDh).2
      nlinarith [hB, h1, h2]
    have hmix : (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ (i - a + 1) (j - b) (by omega) (by omega)
    calc (((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a h z θ
            * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ))) ^ 2
        = ((i.choose a : ℝ)) ^ 2 * ((j.choose b : ℝ)) ^ 2
            * (Work.Spaces.mixed b a h z θ) ^ 2
            * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          ring
      _ ≤ 256 * 256 * (200 * Work.Spaces.WlInf α 4 h) ^ 2
            * Work.Spaces.HkIntegrand α 4 f z θ := by
          gcongr
      _ = 2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
            * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
  have hinner : ∀ a ∈ Finset.range (i + 1),
      (∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a h z θ
              * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ
                * Work.Spaces.Wt α z θ))) ^ 2
        ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1),
            (((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a h z θ
                * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ
                  * Work.Spaces.Wt α z θ))) ^ 2 := by
    intro a _
    have hs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
      (f := fun b => ((i.choose a : ℝ) * (j.choose b : ℝ))
        * (Work.Spaces.mixed b a h z θ
          * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ)))
    have hc : (((Finset.range (j + 1)).card : ℕ) : ℝ) = (j : ℝ) + 1 := by
      rw [Finset.card_range]; push_cast; ring
    rwa [hc] at hs
  have hbnd : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a h z θ
            * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ))) ^ 2
      ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
          * (2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ)) := by
    calc ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a h z θ
              * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ))) ^ 2
        ≤ ∑ _a ∈ Finset.range (i + 1), ∑ _b ∈ Finset.range (j + 1),
            (2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ)) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
      _ = ((i : ℝ) + 1) * ((j : ℝ) + 1)
            * (2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
                * Work.Spaces.HkIntegrand α 4 f z θ)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
  calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a h z θ
              * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ))) ^ 2
      ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
          (∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a h z θ
                * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ
                  * Work.Spaces.Wt α z θ))) ^ 2 := by
        have hs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
          (f := fun a => ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a h z θ
                * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ
                  * Work.Spaces.Wt α z θ)))
        have hc : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
          rw [Finset.card_range]; push_cast; ring
        rwa [hc] at hs
    _ ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
          (((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1),
            (((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a h z θ
                * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ
                  * Work.Spaces.Wt α z θ))) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha => hinner a ha)
          (by positivity)
    _ = ((i : ℝ) + 1) * ((j : ℝ) + 1)
          * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a h z θ
                * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ
                  * Work.Spaces.Wt α z θ))) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
          * (((i : ℝ) + 1) * ((j : ℝ) + 1)
              * (2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
                  * Work.Spaces.HkIntegrand α 4 f z θ))) :=
        mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ ≤ 10 ^ 12 * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
        have htarget : (10 : ℝ) ^ 12 * (Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ
            = 10 ^ 12 * ((Work.Spaces.WlInf α 4 h) ^ 2
                * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
        rw [htarget]
        have hxnn : (0 : ℝ) ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1) := by positivity
        have h16 : ((i : ℝ) + 1) * ((j : ℝ) + 1) ≤ 16 := by
          have h1 : i + 1 ≤ 4 := by omega
          have h2 : j + 1 ≤ 4 := by omega
          have hnat : (i + 1) * (j + 1) ≤ 16 :=
            calc (i + 1) * (j + 1) ≤ 4 * 4 := Nat.mul_le_mul h1 h2
              _ = 16 := by norm_num
          have hcast : (((i + 1) * (j + 1) : ℕ) : ℝ) ≤ 16 := by exact_mod_cast hnat
          have h := hcast
          push_cast at h
          exact h
        have hsq256 : (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2 ≤ 256 := by
          have h := pow_le_pow_left₀ hxnn h16 2
          norm_num at h
          exact h
        have hbase : 0 ≤ (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
          mul_nonneg (sq_nonneg _) hHInn
        have hkey : ((i : ℝ) + 1) * ((j : ℝ) + 1)
              * (((i : ℝ) + 1) * ((j : ℝ) + 1)
                * (2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
                    * Work.Spaces.HkIntegrand α 4 f z θ)))
            = (2621440000 * (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2)
              * ((Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
        rw [hkey]
        refine mul_le_mul_of_nonneg_right ?_ hbase
        calc 2621440000 * (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2
            ≤ 2621440000 * 256 := mul_le_mul_of_nonneg_left hsq256 (by norm_num)
          _ ≤ 10 ^ 12 := by norm_num

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.HKerRadialMul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## A pointwise domination transfers to `HkSq` -/

/-- A pointwise domination of the `ℋᵏ`-integrand on the closed quadrant, with the integrand of
`f` integrable, transfers to `HkSq` (both sides being iterated integrals). -/
private theorem hkSq_le_of_integrand_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (C : ℝ)
    (hmf : Work.Spaces.HkMem α k f)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k g z θ ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkSq α k g ≤ C * Work.Spaces.HkSq α k f := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k f z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => Work.Spaces.HkIntegrand α k g z θ)
        (g := fun θ => C * Work.Spaces.HkIntegrand α k f z θ)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
        ((hmf.1 z hz).const_mul C)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt z hz θ hθ)
    rwa [MeasureTheory.integral_const_mul] at h1
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ)
      ≤ ∫ z in Work.Spaces.Iz, C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      (g := fun z => C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ))
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
      (hmf.2.const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  rwa [MeasureTheory.integral_const_mul] at h2

/-! ## The profile `h(z) = z/(1+z)²` -/

/-- `hKer = (1/2)·(2z/(1+z)²)`. -/
private theorem hKer_eq_half_two_z_div :
    Work.Spaces.hKer = fun z => (1 / 2 : ℝ) * (2 * z / (1 + z) ^ 2) := by
  funext w
  rw [Work.Spaces.hKer_apply]
  ring

/-- `hKer` is `C⁴` on `(0,∞)`. -/
private theorem hKer_contDiffOn_four : ContDiffOn ℝ 4 Work.Spaces.hKer (Set.Ioi 0) := by
  rw [hKer_eq_half_two_z_div]
  have h : ContDiffOn ℝ 4 (fun z : ℝ => (1 / 2 : ℝ) * (2 * z / (1 + z) ^ 2))
      (Set.Ioi 0) := by
    refine ((contDiffOn_const.mul Work.FTS.StrongPersist.L3Aux.contDiffOn_two_z_div).mono
      ?_).of_le le_top
    intro z hz
    have hz' : (-1 : ℝ) < z := by have := Set.mem_Ioi.mp hz; linarith
    exact Set.mem_Ioi.mpr hz'
  exact h

/-- **The `D_z`-iterates of `hKer` are bounded on `(0,∞)` by `24000`.**  This is the profile
bound `Work.FTS.StrongPersist.L3Aux.zslot_supBound` for `2z/(1+z)²`, divided by the factor
`2` (`Zop_iter_const_mul`). -/
private theorem zop_hKer_bound :
    ∀ b ≤ 4, ∀ z : ℝ, 0 < z → |Work.Spaces.Zop^[b] Work.Spaces.hKer z| ≤ 24000 := by
  intro b hb z hz
  rw [hKer_eq_half_two_z_div,
    Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul b (1 / 2 : ℝ)
      (fun z => 2 * z / (1 + z) ^ 2),
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b
      (fun z => 2 * z / (1 + z) ^ 2)]
  have h1 := Work.FTS.StrongPersist.L3Aux.zslot_supBound b hb z (le_of_lt hz) (π / 4)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  rw [Work.Elliptic.DzIter_rad] at h1
  linarith

/-! ## Continuity of the iterates of `r · h` -/

/-- **Every `D_z`-iterate of `r·hKer` (of order `≤ 4`) is continuous on `(0,∞)`**, for `r` of
class `C⁴` on `(0,∞)`: the uncurried product is `C⁴` on the open quadrant, so all its mixed
blocks are continuous there (`blocksCont_of_contDiffOn`), and the `θ`-slices of the pure
`D_z`-blocks give the one-dimensional statement at `θ = π/4`. -/
private theorem dzdIter_mul_hKer_continuousOn {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ 4 r (Set.Ioi 0)) :
    ∀ b ≤ 4, ContinuousOn
      (fun z : ℝ => Work.Elliptic.DzdIter b (fun z : ℝ => r z * Work.Spaces.hKer z) z)
      (Set.Ioi 0) := by
  intro b hb
  have h1 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => r p.1) Work.Construction.Qd :=
    hr.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have h2 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Work.Spaces.hKer p.1) Work.Construction.Qd :=
    hKer_contDiffOn_four.comp contDiffOn_fst
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hFsm : ContDiffOn ℝ 4
      (Function.uncurry (fun z θ : ℝ => r z * Work.Spaces.hKer z)) Work.Construction.Qd :=
    h1.mul h2
  have hBc := Work.FTS.CoercivityFix.Transfer.E2pkg.blocksCont_of_contDiffOn hFsm
  have h0b : 0 + b ≤ 4 := by simpa using hb
  have hb0 : ContinuousOn
      (Function.uncurry (Work.Spaces.DzIter b (fun z θ : ℝ => r z * Work.Spaces.hKer z)))
      Work.Construction.Qd := by
    have h := hBc 0 b h0b
    rwa [Work.Spaces.mixed_zero_right] at h
  have hcomp : ContinuousOn
      (fun z : ℝ => Work.Spaces.DzIter b (fun z θ : ℝ => r z * Work.Spaces.hKer z) z (π / 4))
      (Set.Ioi 0) := by
    have hmap : ContinuousOn (fun z : ℝ => ((z, π / 4) : ℝ × ℝ)) (Set.Ioi 0) :=
      continuousOn_id.prodMk continuousOn_const
    have hmem : ∀ z ∈ Set.Ioi (0 : ℝ), ((z, π / 4) : ℝ × ℝ) ∈ Work.Construction.Qd :=
      fun z hz => ⟨hz, ⟨by positivity, by linarith [Real.pi_pos]⟩⟩
    refine (hb0.comp hmap hmem).congr (fun z _ => ?_)
    rfl
  refine hcomp.congr (fun z _ => ?_)
  exact (Work.Elliptic.DzIter_rad (fun z => r z * Work.Spaces.hKer z) b z (π / 4)).symm

/-! ## The main statement -/

theorem HKerRadialMul : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ r : ℝ → ℝ,
    ContDiffOn ℝ 4 r (Set.Ioi 0) →
    Work.Spaces.HkMem α 4 (fun z _ => r z) →
    (∀ b : ℕ, b ≤ 4 → ContinuousOn
      (fun z : ℝ => Work.Elliptic.DzdIter b (fun z : ℝ => r z * Work.Spaces.hKer z) z)
      (Set.Ioi 0)) ∧
    Work.Spaces.HkMem α 4 (fun z _ => r z * Work.Spaces.hKer z) ∧
    Work.Spaces.HkSq α 4 (fun z _ => r z * Work.Spaces.hKer z)
      ≤ K * Work.Spaces.HkSq α 4 (fun z _ => r z) := by
  refine ⟨Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2,
    mul_pos (Work.FTS.StrongPersist.L3Aux.zmulConst_pos 4) (by norm_num), ?_⟩
  intro α hα hα1 r hr hrmem
  -- the two shapes of the product
  have hfun : (fun z θ : ℝ => Work.Spaces.hKer z * r z)
      = fun z (_ : ℝ) => r z * Work.Spaces.hKer z := by
    funext z θ
    exact mul_comm _ _
  have hCnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2 :=
    (mul_pos (Work.FTS.StrongPersist.L3Aux.zmulConst_pos 4) (by norm_num)).le
  -- the pointwise domination on the open quadrant
  have hpt_open : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ,
      Work.Spaces.HkIntegrand α 4 (fun z θ : ℝ => Work.Spaces.hKer z * r z) z θ
        ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2)
          * Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ := by
    intro z hz θ
    refine Work.FTS.StrongPersist.L3Aux.zmul_pt α 4 Work.Spaces.hKer (fun z (_ : ℝ) => r z)
      (by norm_num) (fun b hb => zop_hKer_bound b hb z hz) ?_ ?_
    · intro i hi
      exact Work.FTS.FinalClock.DzIter_mul_of_contDiffOn i Work.Spaces.hKer
        (fun z (_ : ℝ) => r z) isOpen_Ioi
        (hKer_contDiffOn_four.of_le (Nat.cast_le.mpr hi))
        (hr.of_le (Nat.cast_le.mpr hi)) z hz
    · intro j i hi hij
      exact Work.FTS.FinalClock.mixed_mul_of_contDiffOn j i Work.Spaces.hKer
        (fun z (_ : ℝ) => r z) isOpen_Ioi
        (hKer_contDiffOn_four.of_le (Nat.cast_le.mpr (by omega : j ≤ 4)))
        (by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
          rw [Work.Elliptic.DthIter_rad_succ]
          exact contDiffOn_const) z hz
  -- and on the closed quadrant
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ : ℝ => Work.Spaces.hKer z * r z) z θ
        ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2)
          * Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
    · subst h0
      rw [Work.FTS.LocData.HkIntegrand_zero_fst]
      exact mul_nonneg hCnn (Work.Spaces.HkIntegrand_nonneg α 4 _ 0 θ)
    · exact hpt_open z hzpos θ
  -- continuity of the integrand of the product on the open quadrant
  have hFsm : ContDiffOn ℝ 4
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.hKer z * r z)) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => r p.1) Work.FTS.EllipticEst.Q0 :=
      hr.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    have h2 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Work.Spaces.hKer p.1)
        Work.FTS.EllipticEst.Q0 :=
      hKer_contDiffOn_four.comp contDiffOn_fst
        (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    exact h2.mul h1
  have hBc := Work.FTS.CoercivityFix.Transfer.E2pkg.blocksCont_of_contDiffOn hFsm
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
      (fun z θ : ℝ => Work.Spaces.hKer z * r z) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.continuousOn_HkIntegrand_of_blocksCont hBc α
  -- honesty of the product
  have hmemProd : Work.Spaces.HkMem α 4 (fun z θ : ℝ => Work.Spaces.hKer z * r z) := by
    refine Work.FTS.LocData.HkMem_of_majorant α 4 hcont ?_ ?_ hpt
    · intro z hz
      exact (hrmem.1 z hz).const_mul _
    · have h2 := (hrmem.2).const_mul
          (Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2)
      have heq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            (Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2)
              * Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ)
          = fun z : ℝ =>
              (Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2)
                * ∫ θ in Work.Spaces.Iθ,
                    Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ := by
        funext z
        rw [MeasureTheory.integral_const_mul]
      rw [heq]
      exact h2
  -- the `HkSq` estimate
  have hsq := hkSq_le_of_integrand_le α 4
    (Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2) hrmem hpt
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    exact dzdIter_mul_hKer_continuousOn hr b hb
  · rw [← hfun]
    exact hmemProd
  · rw [← hfun]
    exact hsq

end Work.FTS.StrongPersist.L3Rhs.NfkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.VfsTriglJetBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

set_option maxHeartbeats 800000

-- `VfsTriglJetBounds`: uniform bounds for the `dthU`-jets of order `≤ 4` of the two angular
-- profiles `sin 2θ` and `c₂(θ) = cos 2θ − sin²θ` on `Iθ = [0,π/2]`.
-- Intended namespace `Work.FTS.StrongPersist.L3Rhs`
-- (file `Submission/Work/FTS/StrongPersist/L3Rhs/VfsTriglJetBounds.lean`).
-- Route: `Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired` supplies a single
-- `b : ℕ → ℝ` with `|dthU^[j] (sin 2·) θ| ≤ b j · sin 2θ`, `|dthU^[j] (sin²) θ| ≤ b j · sin²θ`,
-- `|dthU^[j] (cos 2·) θ| ≤ b j` for `j ≤ 7` on `Iθ`; take `B := 2 * Σ_{j<5} b j + 1` and use
-- `c₂ = cos 2· − sin²` together with the linearity of the iterates
-- (`Work.FTS.PhiStar.Psi0Est.dthU_iter_sub_eqOn` on `Set.univ`, or a direct induction).
theorem VfsTriglJetBounds : ∃ B : ℝ, 0 < B ∧
    (∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin (2 * t)) θ| ≤ B * Real.sin (2 * θ)) ∧
    (∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ B) := by
  obtain ⟨b, hb0, hbsin, hbsinsq, _hbcossq, hbcos2⟩ :=
    Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired
  set S : ℝ := ∑ i ∈ Finset.range 5, b i with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef]; exact Finset.sum_nonneg (fun i _ => hb0 i)
  refine ⟨2 * S + 1, by linarith, ?_, ?_⟩
  · -- the `sin 2θ`-profile: `b j ≤ S ≤ 2S+1`, and `sin 2θ ≥ 0` on `Iθ`
    intro j hj θ hθ
    have hbj : b j ≤ S := by
      rw [hSdef]
      exact Finset.single_le_sum (fun i _ => hb0 i) (Finset.mem_range.mpr (by omega))
    have hbB : b j ≤ 2 * S + 1 := by linarith
    have hsin2 : 0 ≤ Real.sin (2 * θ) := by
      apply Real.sin_nonneg_of_mem_Icc
      constructor
      · linarith [hθ.1]
      · linarith [hθ.2, Real.pi_pos]
    calc |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin (2 * t)) θ|
        ≤ b j * Real.sin (2 * θ) := hbsin j (by omega) θ hθ
      _ ≤ (2 * S + 1) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_right hbB hsin2
  · -- `c₂ = cos 2· − sin²`: linearity of the iterates plus the `cos 2·`- and `sin²`-bounds
    intro j hj θ hθ
    have hbj : b j ≤ S := by
      rw [hSdef]
      exact Finset.single_le_sum (fun i _ => hb0 i) (Finset.mem_range.mpr (by omega))
    have hbB : b j ≤ 2 * S + 1 := by linarith
    have hb0j : 0 ≤ b j := hb0 j
    have hc2m : Work.Construction.c2m = fun x : ℝ => Real.cos (2 * x) - Real.sin x ^ 2 := rfl
    have hlin := Work.FTS.PhiStar.Psi0Est.dthU_iter_sub_eqOn
      (f := fun t : ℝ => Real.cos (2 * t)) (g := fun t : ℝ => Real.sin t ^ 2)
      (U := Set.univ) isOpen_univ (by fun_prop) (by fun_prop) j
    have hlin' : Work.Spaces.dthU^[j] (fun x : ℝ => Real.cos (2 * x) - Real.sin x ^ 2) θ
        = Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ
          - Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ := hlin (Set.mem_univ θ)
    have hcos := hbcos2 j (by omega) θ hθ
    have hsinsq := hbsinsq j (by omega) θ hθ
    have hsin_sq_le : Real.sin θ ^ 2 ≤ 1 := by
      rw [Real.sin_sq]; linarith [sq_nonneg (Real.cos θ)]
    have habs : |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ
          - Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
        ≤ |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ|
          + |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ| := by
      calc |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ
              - Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
          = |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ
              + (-(Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ))| := by ring_nf
        _ ≤ |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ|
              + |-(Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ)| := abs_add_le _ _
        _ = |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ|
              + |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ| := by rw [abs_neg]
    calc |Work.Spaces.dthU^[j] Work.Construction.c2m θ|
        = |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ
          - Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ| := by rw [hc2m, hlin']
      _ ≤ |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ|
          + |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ| := habs
      _ ≤ b j + b j * Real.sin θ ^ 2 := add_le_add hcos hsinsq
      _ ≤ b j + b j * 1 := by
            have := mul_le_mul_of_nonneg_left hsin_sq_le hb0j
            linarith
      _ = 2 * b j := by ring
      _ ≤ 2 * S + 1 := by linarith

end Work.FTS.StrongPersist.L3Rhs
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6.Prod6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter


namespace Work.FTS.StrongPersist.N6


end Work.FTS.StrongPersist.N6
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T2SliceAux.easyM_sq_int =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2SliceAux

set_option autoImplicit false

/-! ## Elementary helpers

Nothing here is specific to the problem: `esq_integrableOn_of_bound` is the standard
"dominated by an integrable function on the open interval, continuous there" criterion for
`IntegrableOn · Iθ` (the endpoints `{0, π/2}` are null), and the two closure lemmas for
`IntegrableOn` package the `const_mul` / finite-sum operations. -/






/-! ## The AM–GM step: one bounded factor against one weighted `L²` slot -/



/-! ## The expanded mixed block of `Heasy` -/








end Work.FTS.TransportS.T2SliceAux
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.HkSq_le_of_JConv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Fatou for the `ℋ^k`-energy along pointwise-convergent sequences

`Work.FTS_EllLimOK.HkSq_le_of_JConv`: if every `Ψn n` lies in `ℋ^k` (`HkMem`), the energies
`HkSq α k (Ψn n)` are uniformly bounded by `B`, and all mixed slots `D_z^j D_θ^i (Ψn n)` with
`j + i ≤ k` converge pointwise on the open quadrant `Qd` to the corresponding slot of `Ψ`, then
`HkSq α k Ψ ≤ B`.

The proof is Fatou's lemma, applied once in `θ` and once in `z`:

* **the integrands converge**, and in fact at every point of `Iz × Iθ`: on `Qd` this is the
  hypothesis on the slots (the weights only depend on the point), while at `z = 0` the weight
  `w 0 = (1+0)²/0² = 0` kills the integrand, and at `sin (2θ) = 0` every summand carries a
  factor `sin (2θ)` or `1/sin(2θ)^{η/2}` and vanishes.  Hence no exceptional set at all;
* **the slices of the limit integrand are a.e. measurable** (`AEMeasurable.liminf`: a pointwise --
  hence a.e. -- limit of a.e. measurable functions is a.e. measurable);
* **Fatou in `θ`** (`MeasureTheory.lintegral_liminf_le'`) gives, for each `z ∈ Iz`, the `ℝ≥0∞`
  inequality `∫⁻_θ ofReal (HkIntegrand α k Ψ z ·) ≤ liminf_n ∫⁻_θ ofReal (HkIntegrand α k (Ψn n) z ·)`;
  converting on both sides with `integral_eq_lintegral_of_nonneg_ae` and `ofReal_toReal_le` turns
  this into the real inequality `ofReal (∫_θ HkIntegrand α k Ψ z ·) ≤ liminf_n ofReal (∫_θ HkIntegrand α k (Ψn n) z ·)`;
* **Fatou in `z`** does the same at the outer level, the sequence of `z`-functions being
  integrable (the second half of `HkMem`) and nonnegative, and the `z`-integrals of the sequence
  being exactly the `HkSq α k (Ψn n)`, bounded by `B`.  This gives
  `∫⁻_z ofReal (∫_θ HkIntegrand α k Ψ z ·) ≤ ofReal B`;
* **conclusion**: either `z ↦ ∫_θ HkIntegrand α k Ψ z ·` is integrable, in which case
  `HkSq α k Ψ = (∫⁻_z ...).toReal ≤ B`; or it is not, in which case Lean's Bochner integral is
  `0` (`MeasureTheory.integral_undef`), so `HkSq α k Ψ = 0 ≤ B`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Vanishing of the `ℋ^k`-integrand on the boundary of the domain -/

/-- The `ℋ^k`-integrand vanishes at `z = 0`: the radial weight `w 0 = (1+0)²/0² = 0` kills both
blocks of the defining sum. -/
theorem HkIntegrand_fst_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  have hw : Work.Spaces.w (0 : ℝ) = 0 := by norm_num [Work.Spaces.w]
  have hW : Work.Spaces.Wt α 0 θ = 0 := by rw [Work.Spaces.Wt, hw, zero_mul]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f 0 θ *
        (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hw, zero_div, mul_zero, sq, mul_zero]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i f 0 θ * Work.Spaces.Wt α 0 θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left hc, hW, mul_zero, sq, mul_zero]
    · rw [ite_eq_right hc]
  rw [Work.Spaces.HkIntegrand, h1, h2, add_zero]

/-- At an angle where `sin (2θ) = 0`, every `D_θ`-iterate `D_θ^i u` with `i ≥ 1` vanishes: the
outermost `D_θ` is `sin (2θ) · ∂_θ`. -/
lemma DthIter_eq_zero_of_sin_eq_zero (u : ℝ → ℝ → ℝ) (i : ℕ) (hi : 1 ≤ i) (θ : ℝ)
    (h : Real.sin (2 * θ) = 0) (z : ℝ) : Work.Spaces.DthIter i u z θ = 0 := by
  cases i with
  | zero => omega
  | succ m => simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, h, zero_mul]

/-- If `g (·) θ` vanishes identically, then so does every `D_z`-iterate `D_z^j g (·) θ`. -/
lemma DzIter_eq_zero_of_forall_eq_zero (g : ℝ → ℝ → ℝ) (θ : ℝ) (hg : ∀ z, g z θ = 0)
    (j : ℕ) (z : ℝ) : Work.Spaces.DzIter j g z θ = 0 := by
  induction j generalizing z with
  | zero => simpa using hg z
  | succ m ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have hfun : (fun z' => Work.Spaces.DzIter m g z' θ) = fun _ => (0 : ℝ) :=
      funext fun z' => ih z'
    simp only [Work.Spaces.pz, hfun, deriv_const, mul_zero]

/-- At an angle where `sin (2θ) = 0`, every mixed derivative `D_z^j D_θ^i u` with `i ≥ 1`
vanishes. -/
lemma mixed_eq_zero_of_sin_eq_zero (u : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (θ : ℝ)
    (h : Real.sin (2 * θ) = 0) (z : ℝ) : Work.Spaces.mixed j i u z θ = 0 := by
  rw [Work.Spaces.mixed]
  exact DzIter_eq_zero_of_forall_eq_zero (Work.Spaces.DthIter i u) θ
    (fun z' => DthIter_eq_zero_of_sin_eq_zero u i hi θ h z') j z

/-- The `ℋ^k`-integrand vanishes at any angle `θ` with `sin (2θ) = 0`. -/
theorem HkIntegrand_eq_zero_of_sin_eq_zero (α : ℝ) (k : ℕ) (u : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k u z θ = 0 := by
  have hden : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [h, Real.zero_rpow (by norm_num [Work.Spaces.eta]), div_zero]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i u z θ *
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hden, mul_zero, sq, mul_zero]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i u z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left hc, mixed_eq_zero_of_sin_eq_zero u j i hc.1 θ h z, zero_mul, sq, mul_zero]
    · rw [ite_eq_right hc]
  rw [Work.Spaces.HkIntegrand, h1, h2, add_zero]

/-! ## Convergence of the integrand from convergence of the slots -/

/-- The `ℋ^k`-integrand is a finite sum of squares of terms `slot · weight`, where the weight
depends only on the point: hence convergence of the slots at a point gives convergence of the
integrand there. -/
theorem tendsto_HkIntegrand_of_tendsto_mixed {α : ℝ} {k : ℕ} {fn : ℕ → ℝ → ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (h : ∀ j i : ℕ, j + i ≤ k →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (fn n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2))) :
    Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α k (fn n) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.HkIntegrand α k f p.1 p.2)) := by
  have key : ∀ (c : ℝ) (j i : ℕ), j + i ≤ k →
      Filter.Tendsto (fun n => (Work.Spaces.mixed j i (fn n) p.1 p.2 * c) ^ 2) Filter.atTop
        (nhds ((Work.Spaces.mixed j i f p.1 p.2 * c) ^ 2)) :=
    fun c j i hji => ((h j i hji).mul_const c).pow 2
  simp only [Work.Spaces.HkIntegrand]
  refine Tendsto.add ?_ ?_
  · refine tendsto_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    exact key _ i 0 (by have := Finset.mem_range.mp hi; omega)
  · refine tendsto_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    refine tendsto_finsetSum (Finset.range (k + 1)) (fun j hj => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [ite_eq_left hc]
      exact key _ j i (by omega)
    · simp only [ite_eq_right hc]
      exact tendsto_const_nhds

/-! ## The main theorem -/

theorem HkSq_le_of_JConv {α : ℝ} {k : ℕ} {Ψn : ℕ → Work.FTS.Galerkin.Fn}
    {Ψ : Work.FTS.Galerkin.Fn} {B : ℝ}
    (hMem : ∀ n, Work.Spaces.HkMem α k (Ψn n))
    (hB : ∀ n, Work.Spaces.HkSq α k (Ψn n) ≤ B)
    (h : ∀ j i : ℕ, j + i ≤ k → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (Ψn n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Ψ z θ))) :
    Work.Spaces.HkSq α k Ψ ≤ B := by
  classical
  have hB0 : 0 ≤ B := le_trans (Work.Spaces.HkSq_nonneg α k (Ψn 0)) (hB 0)
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici

  -- (i) the integrands converge, at every point of `Iz × Iθ`
  have hconv : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α k (Ψn n) z θ) Filter.atTop
        (nhds (Work.Spaces.HkIntegrand α k Ψ z θ)) := by
    intro z hz θ hθ
    by_cases hz0 : z = 0
    · subst hz0
      have h1 : ∀ n, Work.Spaces.HkIntegrand α k (Ψn n) 0 θ = 0 :=
        fun n => HkIntegrand_fst_zero α k (Ψn n) θ
      have h2 : Work.Spaces.HkIntegrand α k Ψ 0 θ = 0 := HkIntegrand_fst_zero α k Ψ θ
      rw [show (fun n => Work.Spaces.HkIntegrand α k (Ψn n) 0 θ) = fun _ => (0 : ℝ) from
        funext h1, h2]
      exact tendsto_const_nhds
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      by_cases hsin : Real.sin (2 * θ) = 0
      · have h1 : ∀ n, Work.Spaces.HkIntegrand α k (Ψn n) z θ = 0 :=
          fun n => HkIntegrand_eq_zero_of_sin_eq_zero α k (Ψn n) z θ hsin
        have h2 : Work.Spaces.HkIntegrand α k Ψ z θ = 0 :=
          HkIntegrand_eq_zero_of_sin_eq_zero α k Ψ z θ hsin
        rw [show (fun n => Work.Spaces.HkIntegrand α k (Ψn n) z θ) = fun _ => (0 : ℝ) from
          funext h1, h2]
        exact tendsto_const_nhds
      · have hθ0 : 0 < θ := by
          rcases lt_or_eq_of_le hθ.1 with h' | h'
          · exact h'
          · exact absurd (by rw [← h']; simp) hsin
        have hθpi : θ < π / 2 := by
          rcases lt_or_eq_of_le hθ.2 with h' | h'
          · exact h'
          · exact absurd (by rw [h', show 2 * (π / 2) = π by ring]; exact Real.sin_pi) hsin
        exact tendsto_HkIntegrand_of_tendsto_mixed (α := α) (k := k) (fn := Ψn) (f := Ψ)
          (p := (z, θ))
          (fun j i hji => h j i hji z θ (by
            rw [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
            exact ⟨hzpos, hθ0, hθpi⟩))

  -- (ii) the slices of the limit integrand are a.e. strongly measurable
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ => Work.Spaces.HkIntegrand α k Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have hlim : AEMeasurable
        (fun θ => Filter.liminf
          (fun n => Work.Spaces.HkIntegrand α k (Ψn n) z θ) Filter.atTop)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      AEMeasurable.liminf (fun n => ((hMem n).1 z hz).aestronglyMeasurable.aemeasurable)
    have hEq : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Filter.liminf (fun n => Work.Spaces.HkIntegrand α k (Ψn n) z θ) Filter.atTop
          = Work.Spaces.HkIntegrand α k Ψ z θ := by
      rw [MeasureTheory.ae_restrict_iff' hIθ]
      exact Filter.Eventually.of_forall fun θ hθ => (hconv z hz θ hθ).liminf_eq
    exact hlim.congr hEq

  -- (iii) Fatou in `θ`, for each fixed `z`
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ Filter.liminf (fun n => ∫⁻ θ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Ψn n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) Filter.atTop := by
    intro z hz
    have hfat := MeasureTheory.lintegral_liminf_le'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) (u := Filter.atTop)
      (f := fun n θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Ψn n) z θ))
      (fun n => ((hMem n).1 z hz).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    have hEq : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ)
          = Filter.liminf
              (fun n => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Ψn n) z θ))
                Filter.atTop := by
      rw [MeasureTheory.ae_restrict_iff' hIθ]
      exact Filter.Eventually.of_forall fun θ hθ =>
        ((ENNReal.continuous_ofReal.tendsto (Work.Spaces.HkIntegrand α k Ψ z θ)).comp
          (hconv z hz θ hθ)).liminf_eq.symm
    rw [MeasureTheory.lintegral_congr_ae hEq]
    exact hfat

  -- (iv) the same statement for the real `θ`-integrals
  have hGle : ∀ z ∈ Work.Spaces.Iz,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
        ≤ Filter.liminf (fun n => ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Ψn n) z θ)) Filter.atTop := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
        = (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k Ψ z θ)
        ((hslice z hz).aestronglyMeasurable)
    calc ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
        = ENNReal.ofReal ((∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)).toReal) := by rw [h1]
      _ ≤ (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := ENNReal.ofReal_toReal_le
      _ ≤ Filter.liminf (fun n => ∫⁻ θ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Ψn n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) Filter.atTop := hinner z hz
      _ = Filter.liminf (fun n => ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Ψn n) z θ)) Filter.atTop := by
          refine Filter.liminf_congr (Filter.Eventually.of_forall fun n => ?_)
          exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hMem n).1 z hz)
            (Filter.Eventually.of_forall fun θ =>
              Work.Spaces.HkIntegrand_nonneg α k (Ψn n) z θ)).symm

  -- (v) Fatou in `z`
  have hFatouZ := MeasureTheory.lintegral_liminf_le'
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) (u := Filter.atTop)
    (f := fun n z => ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Ψn n) z θ))
    (fun n => ((hMem n).2).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hchain : (∫⁻ z, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) ≤ ENNReal.ofReal B := by
    refine le_trans (MeasureTheory.lintegral_mono_ae ?_) (le_trans hFatouZ ?_)
    · have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
            ≤ Filter.liminf (fun n => ENNReal.ofReal
                (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Ψn n) z θ))
                  Filter.atTop := by
        rw [MeasureTheory.ae_restrict_iff' hIz]
        exact Filter.Eventually.of_forall fun z hz => hGle z hz
      exact hle
    · have hrew : Filter.liminf (fun n => ∫⁻ z, ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Ψn n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) Filter.atTop
          = Filter.liminf (fun n => ENNReal.ofReal (Work.Spaces.HkSq α k (Ψn n)))
              Filter.atTop := by
        refine Filter.liminf_congr (Filter.Eventually.of_forall fun n => ?_)
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hMem n).2)
          (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg
            (fun θ => Work.Spaces.HkIntegrand_nonneg α k (Ψn n) z θ))).symm
      rw [hrew, Filter.liminf_eq_iSup_iInf_of_nat]
      refine iSup_le fun n =>
        (iInf_le _ n).trans ((iInf_le _ le_rfl).trans (ENNReal.ofReal_le_ofReal (hB n)))

  -- (vi) conclusion
  by_cases hInt : MeasureTheory.Integrable
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
  · have h4 : Work.Spaces.HkSq α k Ψ
        = (∫⁻ z, ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)).toReal := by
      rw [show Work.Spaces.HkSq α k Ψ
          = (∫ z in Work.Spaces.Iz,
              ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ) from rfl]
      exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg
          (fun θ => Work.Spaces.HkIntegrand_nonneg α k Ψ z θ))
        hInt.aestronglyMeasurable
    rw [h4]
    exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain)
      (by rw [ENNReal.toReal_ofReal hB0])
  · have h0 : Work.Spaces.HkSq α k Ψ = 0 := by
      rw [show Work.Spaces.HkSq α k Ψ
          = (∫ z in Work.Spaces.Iz,
              ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ) from rfl]
      exact MeasureTheory.integral_undef hInt
    rw [h0]
    exact hB0

end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Locality =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Congruence of the iterated operators on an open set -/

/-- Two functions that agree on an open set have the same `D_θ`-iterates there. -/
theorem DthIter_congr_eqOn {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i u))
      (Function.uncurry (Work.Spaces.DthIter i v)) V := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro p hp
      show Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter n u) p.1 p.2
        = Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter n v) p.1 p.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hp]

/-- Two functions that agree on an open set have the same `D_z`-iterates there. -/
theorem DzIter_congr_eqOn {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter i u))
      (Function.uncurry (Work.Spaces.DzIter i v)) V := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro p hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter n u) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter n v) p.1 p.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

/-- **Locality of `mixed`**: agreement on a neighbourhood of `(z,θ)` gives equality of every
mixed derivative there. -/
theorem mixed_congr_of_eventuallyEq {f g : ℝ → ℝ → ℝ} {z θ : ℝ} (a b : ℕ)
    (h : Function.uncurry f =ᶠ[𝓝 (z, θ)] Function.uncurry g) :
    Work.Spaces.mixed a b f z θ = Work.Spaces.mixed a b g z θ := by
  obtain ⟨s, hs, hssub⟩ := Filter.Eventually.exists_mem h
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hs
  have heqW : Set.EqOn (Function.uncurry f) (Function.uncurry g) W := fun p hp => hssub p (hWsub hp)
  have hDth := DthIter_congr_eqOn hWopen heqW b
  have hfin := DzIter_congr_eqOn hWopen hDth a hWmem
  simpa only [Function.uncurry, Work.Spaces.mixed] using hfin

/-- The `EqOn`-form of the locality of `mixed` (on an open set). -/
theorem mixed_congr_of_eqOn_isOpen {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {z θ : ℝ} (hz : (z, θ) ∈ V)
    (a b : ℕ) : Work.Spaces.mixed a b f z θ = Work.Spaces.mixed a b g z θ :=
  mixed_congr_of_eventuallyEq a b (h.eventuallyEq_of_mem (hV.mem_nhds hz))

/-! ## The consequences for `QdZero` -/



/-- A `QdZero` direction is `C^∞` on `Qd` (it vanishes on a neighbourhood of `Qd`). -/
theorem QdZero.contDiffOn {γ : Fn} (h : QdZero γ) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry γ) Work.Construction.Qd := by
  obtain ⟨V, hVopen, hQd, hzero⟩ := h
  refine ContDiffOn.congr
    (contDiffOn_const (c := (0 : ℝ)) (s := Work.Construction.Qd)) ?_
  intro p hp
  show Function.uncurry γ p = (0 : ℝ)
  have hγ0 : γ p.1 p.2 = 0 := hzero p.1 p.2 (hQd hp)
  simpa only [Function.uncurry] using hγ0



end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.L12_classC_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

/-!
# The four analytic facts about `L₁₂` on the linear elliptic class `ClassC`

`L₁₂(g)(z) = ∫_z^∞ ∫_θ K(θ) g(s,θ)/s dθ ds` is the radial `L₁₂`-transform of the
fundamental model, and `L12dens g s = ∫_θ K(θ) g(s,θ)/s dθ` is its angular density.  For a
datum `g` of the linear elliptic class `Work.FTS.ClassC.ClassC α` the present lemma collects
the four analytic facts every consumer of the `PkgJets` chapter needs:

* `L12dens g ∈ L¹((0,∞))`,
* `∂_z L₁₂(g)(z) = -L12dens g z` for every `z > 0`,
* `L₁₂(g)` is continuous on `[0,1]`,
* `L₁₂(g)(z) → 0` as `z → ∞`.

The proof is an assembly of three facts already in the tree:

1. `ClassC` supplies *continuity* of the datum on the open quadrant `Q0` (`hg.reg`, open-quadrant
   `C^∞`) and `ℋ⁴`-honesty (`hg.mem`, `ℋ⁷`, restricted by the pointwise monotonicity
   `HkMem_mono_le` of the `ℋ`-integrand).  Those are exactly the two hypotheses of
   `L12dens_integrableOn_of_continuousOn`, which gives the first conjunct.  No smoothness
   (let alone analyticity) of `g` is used here — only continuity on `Q0`.
2. The derivative conjunct is `HasDerivAt_L12_of_Fstar_facts`, applied to the all-order
   smoothness of the angular moment `F_*(g)` on `(0,∞)` (`hg.fsm`, one of the new fields of
   `ClassC`, and the reason `ClassC` was introduced: the old `GalClass` lacked it).  Its second
   hypothesis, the integrability of `r ↦ F_*(g)(r)/r`, is *not* independent: `L12dens` is
   `3·F_*/·` (`L12dens_eq_three_Fstar_div`), so it is a consequence of the first conjunct.
3. The value `L₁₂(g)(0) = 0`, together with the first conjunct, is all that
   `Work.Elliptic.L12_values` needs to produce the last two conjuncts: the tail integral of an
   `L¹`-function is continuous on `[0,1]` and tends to `0` at `+∞`.  The vanishing of the
   `L₁₂`-mode at `z = 0` is the class field `hg.l12`.

`Work.Construction.L12`/`Work.Construction.L12dens` are definitionally `Work.Elliptic.L12`/
`Work.Elliptic.L12dens` (they are `Work.FM.L12 Spaces.K`/`Work.FM.L12dens Spaces.K`, and
`Spaces.K = Elliptic.Ktheta = 3 sinθ cos²θ`), so all three facts transfer by `rfl`-level
definitional unfolding; the only things that are *not* definitional are the two scalar
identities `L12dens = 3·F_*/·` and `3·F_*/· = L12dens`, which are closed by `ring`.
-/

theorem L12_classC_facts {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.ClassC.ClassC α g) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens g) (Set.Ioi 0) ∧
    (∀ z : ℝ, 0 < z → HasDerivAt (fun z => Work.Construction.L12 g z)
      (-(Work.Construction.L12dens g z)) z) ∧
    ContinuousOn (fun z => Work.Construction.L12 g z) (Set.Icc 0 1) ∧
    Filter.Tendsto (fun z => Work.Construction.L12 g z) Filter.atTop (nhds 0) := by
  -- `ClassC` gives continuity on the open quadrant and `ℋ⁴`-honesty
  have hcont : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0 := hg.reg.continuousOn
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS_EllLimOK.PkgJets.HkMem_mono_le hg.reg (by norm_num) hg.mem
  -- (1) the density is `L¹` on `(0,∞)`
  have hint : MeasureTheory.IntegrableOn (Work.Construction.L12dens g) (Set.Ioi 0) :=
    Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn hcont hmem4
  have hintE : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) := hint
  -- `F_*/·` is integrable: it is `L12dens/3` (`L12dens = 3·F_*/·`), off the null point `0`
  have hFint : MeasureTheory.IntegrableOn (fun r => Work.Elliptic.Fstar g r / r) (Set.Ioi 0) := by
    have h3 : MeasureTheory.IntegrableOn (fun r => Work.Elliptic.L12dens g r / 3) (Set.Ioi 0) :=
      hintE.div_const 3
    refine MeasureTheory.IntegrableOn.congr_fun_ae h3 ?_
    filter_upwards with r
    rw [Work.Elliptic.L12dens_eq_three_Fstar_div g r]
    ring
  -- (2) the derivative, from the fundamental theorem of calculus for the tail integral
  have hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (fun z => Work.Construction.L12 g z)
      (-(Work.Construction.L12dens g z)) z := by
    intro z hz
    have h := Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g (fun m => hg.fsm m) hFint z hz
    have hval : 3 * Work.Elliptic.Fstar g z / z = Work.Construction.L12dens g z := by
      have h1 : Work.Construction.L12dens g z = 3 * (Work.Elliptic.Fstar g z / z) :=
        Work.Elliptic.L12dens_eq_three_Fstar_div g z
      rw [h1]; ring
    exact h.congr_deriv (by rw [hval])
  -- (3)+(4) continuity on `[0,1]` and decay at `+∞`, from `L₁₂(g)(0) = 0` and `L¹`-ness
  have h0 : Work.Elliptic.L12 g 0 = 0 := hg.l12
  obtain ⟨-, htend, hcontIcc⟩ := Work.Elliptic.L12_values g hintE h0
  exact ⟨hint, hderiv, hcontIcc, htend⟩

end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.oneSubChi_jet_le8 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `D_z`-jets of the localising factor `1 - χ(z/L)`, up to order `8`

This is the order-`8` instance of the chain
`Work.FTS.LocData.ZFBase.DzIter_oneSubChi_bound_uniform` (order `4`),
`Work.FTS.LocDataExt.oneSubChi_jet_le5` (order `5`) and
`Work.FTS.LocData6.oneSubChi_jet_le6` (order `6`), and the proof is the same one:
the Stirling expansion `D_z^c = ∑_k S(c,k) z^k ∂_z^k` reduces the jet `D_z^c` of the
dilated factor `1 - χ(z/L)` to the weighted derivatives `(z/L)^k ∂^k(1-χ)(z/L)`, whose
uniform bound in `L ≥ 1` is `OneSubChi_deriv_bound8`; the total coefficient mass is the
Bell number `bell c ≤ 5000` for `c ≤ 8`. -/

/-- The Bell number of row `c` is below `5000`, for `c ≤ 8`.  (`bell 8 = 4140`; the rows
`0..8` are `1, 1, 2, 5, 15, 52, 203, 877, 4140`.) -/
theorem bell_le_5000_of_le_eight {c : ℕ} (hc : c ≤ 8) : (Work.Spaces.bell c : ℝ) ≤ 5000 := by
  have h : Work.Spaces.bell c ≤ 5000 := by interval_cases c <;> decide
  exact_mod_cast h

theorem oneSubChi_jet_le8 :
    ∃ Cu : ℝ, 1 ≤ Cu ∧ ∀ L : ℝ, 1 ≤ L → ∀ c : ℕ, c ≤ 8 →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Cu := by
  obtain ⟨M, hM0, hMb⟩ := OneSubChi_deriv_bound8
  -- `M ≥ 1`, by evaluating the bound at `k = 0`, `x = 2`
  have hM1 : 1 ≤ M := by
    have h := hMb 0 (by norm_num) (2 : ℝ)
    have h2 : iteratedDeriv 0 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (2 : ℝ) = 1 := by
      rw [iteratedDeriv_zero, Work.Stability.chi_eq_zero (by norm_num)]
      norm_num
    simpa [h2] using h
  refine ⟨5000 * M, by linarith, fun L hL c hc z hz θ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  -- smoothness of the two cut-off factors
  have hsmg : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  have hsmL : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) :=
    hsmg.comp (contDiff_id.div_const L)
  -- 1. the `θ`-independent function is a `z`-only multiplier
  have h1 : Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ
      = Work.Coercivity.CommutZ.DzIterZ c
          (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z := by
    have h := congrFun (congrFun (Work.Coercivity.CommutZ.DzIter_mulZ c
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L))) z) θ
    have hfun : Work.Coercivity.CommutZ.mulZ (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L))
        = (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) := rfl
    rw [hfun] at h
    simpa only [Work.Coercivity.CommutZ.mulZ_apply] using h
  rw [h1]
  -- 2. the Stirling expansion
  have h2 : Work.Coercivity.CommutZ.DzIterZ c
        (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z
      = ∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
          (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) := by
    simpa only [] using congrFun (Work.FTS.LocData.DzIterZ_eq_sum_scoef
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) hsmL c) z
  rw [h2]
  -- 3. each summand is bounded by `M`, uniformly in `L`
  have hb : ∀ k ≤ c, |z ^ k * iteratedDeriv k
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z| ≤ M := by
    intro k hk
    have hk8 : k ≤ 8 := le_trans hk hc
    have hrew : iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z
        = (L⁻¹) ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L) :=
      Work.FTS.LocData.IteratedDeriv_comp_div
        (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) hsmg hLne k z
    have hzL : z ^ k * ((L⁻¹) ^ k *
          iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L))
        = (z / L) ^ k * iteratedDeriv k
            (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L) := by
      have hdiv : z / L = z * L⁻¹ := by rw [div_eq_mul_inv]
      rw [hdiv, mul_pow]
      ring
    rw [hrew, hzL]
    exact hMb k hk8 (z / L)
  have hsum := Work.Spaces.abs_sum_scoef_mul_le c M
    (fun k => z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) hb
  have hbell : (Work.Spaces.bell c : ℝ) ≤ 5000 := bell_le_5000_of_le_eight hc
  calc |∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
        (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z)|
      ≤ (Work.Spaces.bell c : ℝ) * M := hsum
    _ ≤ 5000 * M := mul_le_mul_of_nonneg_right hbell hM0

end Work.FTS_LocDatum3a
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_mul_le2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys.GdotAux

/-- **The Leibniz rule for `D_z^j D_θ^i` on the open quadrant, at total order `j + i ≤ 2`.**

`D_z f = z ∂_z f` and `D_θ f = sin(2θ) ∂_θ f` are derivations for the pointwise product, so,
writing `Work.Spaces.mixed j i f = D_z^j D_θ^i f`, the iterated Leibniz rule

`D_z^j D_θ^i (f·h) = ∑_{a ≤ i} ∑_{b ≤ j} C(i,a) C(j,b) (D_z^b D_θ^a f)(D_z^{j-b} D_θ^{i-a} h)`

holds as soon as `f` and `h` are `C^{j+i}` at the point.  This is the `C²` instance needed by
the finite-order calculus of the `g`-system: it is the low-order specialisation of the general
finite-order statement `mixedMulFinLocal` (in
`...Sys.GdotAux.mixed_mul_fin_local`), which covers two functions of class `C^{j+i}` on an
arbitrary *open* set `V`.  (Indeed neither `Work.Spaces.mixed_mul_eq` — stated for
analytic/`C^∞` functions on the strip — nor any of the `SmoothNbhd`/`SmoothOpen` Leibniz rules
applies to a merely `C²` datum.) -/
theorem mixed_mul_le2 {f h : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hh : ContDiffOn ℝ 2 (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ 2) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.mixed j i (fun z θ => f z θ * h z θ) z θ
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) h z θ) := by
  have hle : ((j + i : ℕ) : WithTop ℕ∞) ≤ ((2 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hji
  exact mixedMulFinLocal (V := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
    (hf.of_le hle) (hh.of_le hle) z θ
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)

end Work.FTS_RegExport.RXT.Sys.GdotAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.mixed_mul_fin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys.JetCalc

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The Leibniz rule for `D_z^j D_θ^i` at finite order on an open set

`Work.Spaces.mixed j i f = D_z^j D_θ^i f` where `D_z f = z ∂_z f` and
`D_θ f = sin(2θ) ∂_θ f`; both are derivations for the pointwise product, so the iterated
Leibniz rule

`D_z^j D_θ^i (f·g) = ∑_{a ≤ i} ∑_{b ≤ j} C(i,a) C(j,b) (D_z^b D_θ^a f)(D_z^{j-b} D_θ^{i-a} g)`

holds.  Here it is proved for `f`, `g` that are jointly `C^{j+i}` on an *arbitrary open*
set `V ⊂ ℝ²`, at a point of `V`.

The proof is the direct induction on the pair `(a,b)` (as in
`Work.FTS.GalBasis.ApproxCC.mixedMul`, which does the same for globally `C^9` functions):
`D_z^a D_θ^b = D_z (D_z^{a-1} D_θ^b)` resp. `D_θ (D_z^a D_θ^{b-1})`, one application of the
product rule for `D_z` resp. `D_θ`, and the Pascal identity `Work.Spaces.leibniz_step` to
recombine the two shifted binomial sums.  The differentiability side conditions are
discharged from the local `C^{a+b}` hypothesis through
`Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le` (every mixed block costs
its total order in regularity), and the induction hypothesis, which holds only on `V`, is
transported across `D_z`/`D_θ` by the locality of the derivative on the open set `V`.
-/

/-! ## Pointwise product rules and linearity for `D_z` and `D_θ` -/


private lemma Dz_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun z' => u z' θ) z)
    (hv : DifferentiableAt ℝ (fun z' => v z' θ) z) :
    Work.Spaces.Dz (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dz u z θ * v z θ + u z θ * Work.Spaces.Dz v z θ) := by
  show z * deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
      = cc * (z * deriv (fun z' : ℝ => u z' θ) z * v z θ
        + u z θ * (z * deriv (fun z' : ℝ => v z' θ) z))
  rw [show deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
        = deriv (fun y => cc * ((fun z' : ℝ => u z' θ) * (fun z' : ℝ => v z' θ)) y) z
        from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma Dz_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => A i z' θ) z) :
    Work.Spaces.Dz (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dz (A i) z θ := by
  have hfun : (fun z' : ℝ => ∑ i ∈ s, A i z' θ) = (∑ i ∈ s, fun z' : ℝ => A i z' θ) := by
    funext z'
    rw [Finset.sum_apply]
  show z * deriv (fun z' : ℝ => ∑ i ∈ s, A i z' θ) z
      = ∑ i ∈ s, z * deriv (fun z' : ℝ => A i z' θ) z
  rw [hfun, deriv_sum h, Finset.mul_sum]


private lemma Dth_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun θ' => u z θ') θ)
    (hv : DifferentiableAt ℝ (fun θ' => v z θ') θ) :
    Work.Spaces.Dth (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dth u z θ * v z θ + u z θ * Work.Spaces.Dth v z θ) := by
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
      = cc * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => u z θ') θ * v z θ
        + u z θ * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => v z θ') θ))
  rw [show deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
        = deriv (fun y => cc * ((fun θ' : ℝ => u z θ') * (fun θ' : ℝ => v z θ')) y) θ
        from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma Dth_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun θ' => A i z θ') θ) :
    Work.Spaces.Dth (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dth (A i) z θ := by
  have hfun : (fun θ' : ℝ => ∑ i ∈ s, A i z θ') = (∑ i ∈ s, fun θ' : ℝ => A i z θ') := by
    funext θ'
    rw [Finset.sum_apply]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => ∑ i ∈ s, A i z θ') θ
      = ∑ i ∈ s, Real.sin (2 * θ) * deriv (fun θ' : ℝ => A i z θ') θ
  rw [hfun, deriv_sum h, Finset.mul_sum]

private lemma differentiableAt_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {z : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) z) :
    DifferentiableAt ℝ (fun z' => ∑ i ∈ s, A i z') z := by
  have hfun : (fun z' => ∑ i ∈ s, A i z') = (∑ i ∈ s, A i) := by
    funext z'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

private lemma differentiableAt_sum_θ {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {θ : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) θ) :
    DifferentiableAt ℝ (fun θ' => ∑ i ∈ s, A i θ') θ := by
  have hfun : (fun θ' => ∑ i ∈ s, A i θ') = (∑ i ∈ s, A i) := by
    funext θ'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

/-! ## Locality of `D_z` and `D_θ` on an open set -/

private lemma Dz_congr_of_eqOn {V : Set (ℝ × ℝ)} {f g : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ∀ p ∈ V, f p.1 p.2 = g p.1 p.2) :
    ∀ p ∈ V, Work.Spaces.Dz f p.1 p.2 = Work.Spaces.Dz g p.1 p.2 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have htend : Tendsto (fun z' : ℝ => ((z', θ) : ℝ × ℝ)) (𝓝 z) (𝓝 (z, θ)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  have hmem : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => g z' θ) := by
    filter_upwards [htend.eventually (hV.mem_nhds hp)] with z' hz'
    exact h (z', θ) hz'
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hmem.deriv_eq]

private lemma Dth_congr_of_eqOn {V : Set (ℝ × ℝ)} {f g : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ∀ p ∈ V, f p.1 p.2 = g p.1 p.2) :
    ∀ p ∈ V, Work.Spaces.Dth f p.1 p.2 = Work.Spaces.Dth g p.1 p.2 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have htend : Tendsto (fun θ' : ℝ => ((z, θ') : ℝ × ℝ)) (𝓝 θ) (𝓝 (z, θ)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hmem : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') := by
    filter_upwards [htend.eventually (hV.mem_nhds hp)] with θ' hθ'
    exact h (z, θ') hθ'
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hmem.deriv_eq]

/-! ## Differentiability of the mixed blocks at a point of `V` -/

private lemma diffAt_mixed_z {N : ℕ} {F : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ N (Function.uncurry F) V) {i j : ℕ} (hij : i + j + 1 ≤ N)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j F z' θ) z := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed i j F)) V :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le hV j i 1 (by omega) hF
  have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed i j F)) (z, θ) :=
    (h1.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hz)
  exact Work.Spaces.differentiableAt_slice_fst hd

private lemma diffAt_mixed_θ {N : ℕ} {F : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ N (Function.uncurry F) V) {i j : ℕ} (hij : i + j + 1 ≤ N)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j F z θ') θ := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed i j F)) V :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le hV j i 1 (by omega) hF
  have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed i j F)) (z, θ) :=
    (h1.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hz)
  exact Work.Spaces.differentiableAt_slice_snd hd

/-! ## The finite-order Leibniz rule -/

theorem mixed_mul_fin_aux {N : ℕ} {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ N (Function.uncurry f) V)
    (hg : ContDiffOn ℝ N (Function.uncurry g) V) :
    ∀ a b : ℕ, a + b ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.mixed a b (fun z θ => f z θ * g z θ) z θ
        = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ))
              * (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a - i) (b - j) g z θ) := by
  have hfz : ∀ i j : ℕ, i + j + 1 ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j f z' θ) z :=
    fun i j hij z θ hz => diffAt_mixed_z hV hf hij hz
  have hgz : ∀ i j : ℕ, i + j + 1 ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j g z' θ) z :=
    fun i j hij z θ hz => diffAt_mixed_z hV hg hij hz
  have hfθ : ∀ i j : ℕ, i + j + 1 ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j f z θ') θ :=
    fun i j hij z θ hz => diffAt_mixed_θ hV hf hij hz
  have hgθ : ∀ i j : ℕ, i + j + 1 ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j g z θ') θ :=
    fun i j hij z θ hz => diffAt_mixed_θ hV hg hij hz
  have key : ∀ n : ℕ, ∀ a b : ℕ, a + b ≤ n → a + b ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.mixed a b (fun z θ => f z θ * g z θ) z θ
        = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ))
              * (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a - i) (b - j) g z θ) := by
    intro n
    induction n with
    | zero =>
        intro a b hsum hN z θ hz
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha
        subst hb
        simp [Work.Spaces.mixed]
    | succ n ih =>
        intro a b hsum hN z θ hz
        rcases Nat.eq_zero_or_pos a with ha | ha
        · subst ha
          rcases Nat.eq_zero_or_pos b with hb | hb
          · subst hb
            simp [Work.Spaces.mixed]
          · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
            have hs : 0 + b' ≤ n := by omega
            have hN' : 0 + b' ≤ N := by omega
            have hEqOn : ∀ p ∈ V,
                Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ) p.1 p.2
                  = (fun z θ => ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                      (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ)) p.1 p.2 :=
              fun p hp => ih 0 b' hs hN' p.1 p.2 hp
            have hL : Work.Spaces.mixed 0 (b' + 1) (fun z θ => f z θ * g z θ) z θ
                = Work.Spaces.Dth
                    (Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ)) z θ := by
              simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DzIter_zero]
            have hcong := Dth_congr_of_eqOn
              (f := Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ))
              (g := fun z θ => ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
              hV hEqOn (z, θ) hz
            rw [hL, hcong]
            have hstep1 : Work.Spaces.Dth (fun z θ => ∑ i ∈ Finset.range (0 + 1),
                  ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (0 - i) (b' - j) g z θ)) z θ
                = ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i (j + 1) f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ) := by
              rw [Dth_sum (Finset.range (0 + 1))
                    (fun i z θ => ∑ j ∈ Finset.range (b' + 1),
                      (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ
                    (fun i hi => differentiableAt_sum_θ (Finset.range (b' + 1))
                      (fun j θ' => (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ'
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ'))
                      (fun j hj => ((hfθ i j (by
                            have := Finset.mem_range.mp hi
                            have := Finset.mem_range.mp hj
                            omega) z θ hz).mul
                        (hgθ (0 - i) (b' - j) (by
                            have := Finset.mem_range.mp hi
                            have := Finset.mem_range.mp hj
                            omega) z θ hz)).const_mul _))]
              refine Finset.sum_congr rfl fun i hi => ?_
              rw [Dth_sum (Finset.range (b' + 1))
                    (fun j z θ => (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ
                    (fun j hj => ((hfθ i j (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hz).mul
                      (hgθ (0 - i) (b' - j) (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hz)).const_mul _)]
              refine Finset.sum_congr rfl fun j hj => ?_
              have hi0 : i = 0 := by have := Finset.mem_range.mp hi; omega
              rw [Dth_cmul (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ))
                    (hfθ i j (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hz)
                    (hgθ (0 - i) (b' - j) (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hz)]
              rw [show Work.Spaces.Dth (Work.Spaces.mixed i j f) z θ
                    = Work.Spaces.mixed i (j + 1) f z θ from by
                    rw [show i = 0 from hi0]
                    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ,
                      Work.Spaces.DzIter_zero],
                  show Work.Spaces.Dth (Work.Spaces.mixed (0 - i) (b' - j) g) z θ
                    = Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ from by
                    rw [show i = 0 from hi0]
                    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ,
                      Work.Spaces.DzIter_zero, Nat.sub_zero]]
            have hstep2 : (∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                    (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ))
                = ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1 + 1),
                    (((0 : ℕ).choose i : ℝ) * ((b' + 1).choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ) := by
              refine Finset.sum_congr rfl fun i hi => ?_
              have h1 : (∑ j ∈ Finset.range (b' + 1),
                    (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ))
                  = ((0 : ℕ).choose i : ℝ) * (∑ j ∈ Finset.range (b' + 1),
                      (b'.choose j : ℝ) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ)) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
              rw [h1, Work.Spaces.leibniz_step b' (fun j => Work.Spaces.mixed i j f z θ)
                    (fun m => Work.Spaces.mixed (0 - i) m g z θ)]
              have h2 : ((0 : ℕ).choose i : ℝ) * (∑ j ∈ Finset.range (b' + 1 + 1),
                    ((b' + 1).choose j : ℝ) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ))
                  = ∑ j ∈ Finset.range (b' + 1 + 1),
                      (((0 : ℕ).choose i : ℝ) * ((b' + 1).choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
              exact h2
            rw [hstep1, hstep2]
        · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          have hs : a' + b ≤ n := by omega
          have hN' : a' + b ≤ N := by omega
          have hEqOn : ∀ p ∈ V,
              Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ) p.1 p.2
                = (fun z θ => ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                    ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ)) p.1 p.2 :=
            fun p hp => ih a' b hs hN' p.1 p.2 hp
          have hL : Work.Spaces.mixed (a' + 1) b (fun z θ => f z θ * g z θ) z θ
              = Work.Spaces.Dz
                  (Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ)) z θ := by
            simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]
          have hcong := Dz_congr_of_eqOn
            (f := Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ))
            (g := fun z θ => ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed i j f z θ
                    * Work.Spaces.mixed (a' - i) (b - j) g z θ))
            hV hEqOn (z, θ) hz
          rw [hL, hcong]
          have hstep1 : Work.Spaces.Dz (fun z θ => ∑ i ∈ Finset.range (a' + 1),
                ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed i j f z θ
                    * Work.Spaces.mixed (a' - i) (b - j) g z θ)) z θ
              = ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed (i + 1) j f z θ
                      * Work.Spaces.mixed (a' - i) (b - j) g z θ
                    + Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ) := by
            rw [Dz_sum (Finset.range (a' + 1))
                  (fun i z θ => ∑ j ∈ Finset.range (b + 1),
                    ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ
                  (fun i hi => differentiableAt_sum (Finset.range (b + 1))
                    (fun j z' => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z' θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z' θ))
                    (fun j hj => ((hfz i j (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hz).mul
                      (hgz (a' - i) (b - j) (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hz)).const_mul _))]
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [Dz_sum (Finset.range (b + 1))
                  (fun j z θ => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ
                  (fun j hj => ((hfz i j (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hz).mul
                    (hgz (a' - i) (b - j) (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hz)).const_mul _)]
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Dz_cmul ((a'.choose i : ℝ) * (b.choose j : ℝ))
                  (hfz i j (by
                      have := Finset.mem_range.mp hi
                      have := Finset.mem_range.mp hj
                      omega) z θ hz)
                  (hgz (a' - i) (b - j) (by
                      have := Finset.mem_range.mp hi
                      have := Finset.mem_range.mp hj
                      omega) z θ hz)]
            rw [show Work.Spaces.Dz (Work.Spaces.mixed i j f) z θ
                  = Work.Spaces.mixed (i + 1) j f z θ from by
                  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ],
                show Work.Spaces.Dz (Work.Spaces.mixed (a' - i) (b - j) g) z θ
                  = Work.Spaces.mixed (a' - i + 1) (b - j) g z θ from by
                  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]]
          have hstep2 : (∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                  ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
              = ∑ i ∈ Finset.range (a' + 1 + 1), ∑ j ∈ Finset.range (b + 1),
                  ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ) := by
            have hkey1 := Finset.sum_comm (s := Finset.range (a' + 1))
              (t := Finset.range (b + 1))
              (f := fun i j => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                (Work.Spaces.mixed (i + 1) j f z θ
                    * Work.Spaces.mixed (a' - i) (b - j) g z θ
                  + Work.Spaces.mixed i j f z θ
                    * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
            have hkey2 := Finset.sum_comm (s := Finset.range (a' + 1 + 1))
              (t := Finset.range (b + 1))
              (f := fun i j => ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                (Work.Spaces.mixed i j f z θ
                  * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ))
            rw [hkey1, hkey2]
            refine Finset.sum_congr rfl fun j hj => ?_
            have h1 : (∑ i ∈ Finset.range (a' + 1),
                  ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
                = (b.choose j : ℝ) * (∑ i ∈ Finset.range (a' + 1), (a'.choose i : ℝ) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ)) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [h1, Work.Spaces.leibniz_step a' (fun i => Work.Spaces.mixed i j f z θ)
                  (fun m => Work.Spaces.mixed m (b - j) g z θ)]
            have h2 : (b.choose j : ℝ) * (∑ i ∈ Finset.range (a' + 1 + 1),
                  ((a' + 1).choose i : ℝ) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ))
                = ∑ i ∈ Finset.range (a' + 1 + 1),
                    ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            exact h2
          rw [hstep1, hstep2]
  intro a b hab z θ hz
  exact key (a + b) a b le_rfl hab z θ hz

/-! ## The requested statement -/

theorem mixed_mul_fin {j i : ℕ} {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V)
    (hf : ContDiffOn ℝ (j + i) (Function.uncurry f) V)
    (hg : ContDiffOn ℝ (j + i) (Function.uncurry g) V) :
    ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ) := by
  intro z θ hz
  have h := mixed_mul_fin_aux (N := j + i) hV hf hg j i le_rfl z θ hz
  rw [h]
  have h2 : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ))
      = ∑ b ∈ Finset.range (j + 1), ∑ a ∈ Finset.range (i + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ) :=
    Finset.sum_comm
  rw [h2]
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => ?_
  ring

end Work.FTS_RegExport.RXT.Sys.JetCalc
end
end
-- ===== merged: Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H6Pair6Aux.T6Fix

open scoped Real Topology

set_option maxHeartbeats 800000

/-!
## The `sin(2θ)`-gain for angular derivatives, from a flat `∂_θ`-datum

This file proves

`|D_z^b D_θ^a A| ≤ C · K_f · sin(2θ)`  (`1 ≤ a`, `a + b ≤ 2`)

for a source `A` that is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, where `K_f` bounds
only the *first-order* mixed derivatives of `∂_θA = pth A` (`b + i ≤ 1`).

The mechanism is completely elementary: `D_θ` carries the factor `sin(2θ)` and `D_z` does
not differentiate in `θ`, so

* `D_z^b D_θ A = sin(2θ) · D_z^b (∂_θA)` (`mixed_one_eq`), controlled by `mixed b 0 (pth A)`;
* `D_θ² A = sin(2θ) · ∂_θ(D_θA)`, and the product rule for `D_θ A = sin(2θ)·∂_θA` gives
  `∂_θ(D_θA) = 2cos(2θ)·∂_θA + D_θ(∂_θA)` (`pth_Dth_eq`), controlled by `mixed 0 0 (pth A)`
  and `mixed 0 1 (pth A)`.

No boundedness of `A` itself, and no `z`-differentiability, is needed in the second factor.
-/

/-! ## Pulling a `z`-independent factor through the radial operators -/

/-- A factor which does not depend on `z` passes through `∂_z`. -/
theorem pz_const_mul (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pz K z θ :=
  deriv_const_mul_field (c θ)

/-- A factor which does not depend on `z` passes through `D_z^j`. -/
theorem dzIter_const_mul (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => c θ * K z θ) z θ
      = c θ * Work.Spaces.DzIter j K z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have heq : Work.Spaces.DzIter j (fun z θ => c θ * K z θ)
        = fun z θ => c θ * Work.Spaces.DzIter j K z θ :=
      funext fun z => funext fun θ => ih z θ
    rw [heq, pz_const_mul]
    ring

/-! ## The explicit `sin(2θ)` factor in the mixed derivatives -/

/-- `D_z^j D_θ A = sin(2θ) · D_z^j(∂_θA)`. -/
theorem mixed_one_eq (g : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j 1 g z θ
      = Real.sin (2 * θ) * Work.Spaces.DzIter j (Work.Spaces.pth g) z θ := by
  have h : Work.Spaces.mixed j 1 g = Work.Spaces.DzIter j (Work.Spaces.Dth g) := rfl
  rw [h]
  exact dzIter_const_mul (fun θ => Real.sin (2 * θ)) (Work.Spaces.pth g) j z θ

/-- `D_z^j D_θ² A = sin(2θ) · D_z^j(∂_θ(D_θA))`. -/
theorem mixed_two_eq (g : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j 2 g z θ
      = Real.sin (2 * θ)
        * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.Dth g)) z θ := by
  have h : Work.Spaces.mixed j 2 g
      = Work.Spaces.DzIter j (Work.Spaces.Dth (Work.Spaces.Dth g)) := rfl
  rw [h]
  exact dzIter_const_mul (fun θ => Real.sin (2 * θ))
    (Work.Spaces.pth (Work.Spaces.Dth g)) j z θ

/-- The `j = 0` instance: `D_θ A = sin(2θ) · ∂_θA`. -/
theorem mixed_zero_one_eq (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 1 g z θ = Real.sin (2 * θ) * Work.Spaces.pth g z θ := by
  have h := mixed_one_eq g 0 z θ
  simpa only [Work.Spaces.DzIter_zero] using h

/-- The `j = 0` instance: `D_θ² A = sin(2θ) · ∂_θ(D_θA)`. -/
theorem mixed_zero_two_eq (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 2 g z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.Dth g) z θ := by
  have h := mixed_two_eq g 0 z θ
  simpa only [Work.Spaces.DzIter_zero] using h

/-! ## The `θ`-slice derivative and the product rule for `D_θ` -/

/-- The `θ`-slice of a function `C^∞` on the open quadrant, differentiated. -/
theorem hasDerivAt_slice_theta {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ := by
  have hne : Work.Stability.smoothOrder ≠ 0 := by decide
  have hd : DifferentiableOn ℝ (fun θ' : ℝ => F z θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hF.curry_θ hz).differentiableOn hne
  exact (hd.differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt

/-- The product rule for `D_θ = sin(2θ)∂_θ`: on the open quadrant,
`∂_θ(D_θA) = 2cos(2θ)·∂_θA + D_θ(∂_θA)`. -/
theorem pth_Dth_eq {A : ℝ → ℝ → ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.pth (Work.Spaces.Dth A) z θ
      = 2 * Real.cos (2 * θ) * Work.Spaces.pth A z θ
        + Work.Spaces.Dth (Work.Spaces.pth A) z θ := by
  have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) θ).const_mul (2 : ℝ)
    have h2 := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    have h3 : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
    rw [h3] at h2
    exact h2
  have h2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth A z θ')
      (Work.Spaces.pth (Work.Spaces.pth A) z θ) θ :=
    hasDerivAt_slice_theta hA.pth hz hmem
  have hprod := hsin.mul h2
  have hpth : Work.Spaces.pth (Work.Spaces.Dth A) z θ
      = 2 * Real.cos (2 * θ) * Work.Spaces.pth A z θ
        + Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.pth A) z θ :=
    hprod.deriv
  rw [hpth]
  rfl

/-! ## The main statement -/

theorem mixed_sinGain_of_pthFlat : ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ → ℝ → ℝ) (Kf : ℝ),
    0 ≤ Kf → Work.FTS.EllipticEst.SmoothOpen A →
    (∀ b i : ℕ, b + i ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b i (Work.Spaces.pth A) z θ| ≤ Kf) →
    ∀ (a b₁ : ℕ), 1 ≤ a → a + b₁ ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b₁ a A z θ| ≤ C * Kf * Real.sin (2 * θ) := by
  refine ⟨4, by norm_num, ?_⟩
  intro A Kf hKf hA hB a b₁ ha hab z θ hz hθ hθ2
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  -- the two available point bounds on the `∂_θ`-datum
  have hb0 : |Work.Spaces.pth A z θ| ≤ Kf := hB 0 0 (by norm_num) z θ hz hθ hθ2
  have hb01 : |Work.Spaces.Dth (Work.Spaces.pth A) z θ| ≤ Kf :=
    hB 0 1 (by norm_num) z θ hz hθ hθ2
  have ha_cases : a = 1 ∨ a = 2 := by omega
  rcases ha_cases with rfl | rfl
  · -- `a = 1`: `D_z^b₁ D_θ A = sin(2θ)·D_z^b₁(∂_θA)`
    have hb1 : b₁ = 0 ∨ b₁ = 1 := by omega
    rcases hb1 with rfl | rfl
    · rw [mixed_zero_one_eq, abs_mul, abs_of_pos hsin]
      nlinarith [hb0, hKf, hsin]
    · have hD : |Work.Spaces.DzIter 1 (Work.Spaces.pth A) z θ| ≤ Kf :=
        hB 1 0 (by norm_num) z θ hz hθ hθ2
      rw [mixed_one_eq, abs_mul, abs_of_pos hsin]
      nlinarith [hD, hKf, hsin]
  · -- `a = 2` and hence `b₁ = 0`: `D_θ² A = sin(2θ)·∂_θ(D_θA)`
    have hb1 : b₁ = 0 := by omega
    subst b₁
    rw [mixed_zero_two_eq, abs_mul, abs_of_pos hsin]
    have hpd := pth_Dth_eq hA hz hθ hθ2
    have h3 : |Work.Spaces.pth (Work.Spaces.Dth A) z θ| ≤ 3 * Kf := by
      rw [hpd]
      have h1 : |2 * Real.cos (2 * θ) * Work.Spaces.pth A z θ|
          = |2 * Real.cos (2 * θ)| * |Work.Spaces.pth A z θ| := by rw [abs_mul]
      have hc : |2 * Real.cos (2 * θ)| ≤ 2 := by
        rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        linarith [Real.abs_cos_le_one (2 * θ)]
      have hAB : |2 * Real.cos (2 * θ)| * |Work.Spaces.pth A z θ| ≤ 2 * Kf :=
        mul_le_mul hc hb0 (abs_nonneg _) (by norm_num)
      calc |2 * Real.cos (2 * θ) * Work.Spaces.pth A z θ
              + Work.Spaces.Dth (Work.Spaces.pth A) z θ|
          ≤ |2 * Real.cos (2 * θ) * Work.Spaces.pth A z θ|
              + |Work.Spaces.Dth (Work.Spaces.pth A) z θ| := abs_add_le _ _
        _ = |2 * Real.cos (2 * θ)| * |Work.Spaces.pth A z θ|
              + |Work.Spaces.Dth (Work.Spaces.pth A) z θ| := by rw [h1]
        _ ≤ 2 * Kf + Kf := add_le_add hAB hb01
        _ = 3 * Kf := by ring
    nlinarith [h3, hKf, hsin]

end Work.H6Pair6Aux.T6Fix
end
