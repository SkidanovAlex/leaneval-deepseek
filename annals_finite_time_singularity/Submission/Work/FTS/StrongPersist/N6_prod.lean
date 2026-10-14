import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.ExcPairBranches
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.radial_alt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/radial_alt` — the radial `z`-integration by parts of the chain, assembled

This is the assembly of the identity

  `IP (AA u)(BB u) + IP (cw·U)(BB u) = ∫_z w²∫_θ V²σ - 2η·∫_z w²∫_θ U·V·cos(2θ)·σ₁`

out of

* the *truncated* identity `trunc_identity` (both integrations by parts against the two
  cut-offs `χ_k = cut k` and `ψ_k = SliceMixedAux.cut (1/(k+1))`, proved), and
* the four `k → ∞` limits collected in `tendsto_terms_cut` together with the vanishing of the
  boundary term `tendsto_term_psi_cut`, and
* the representation `IP_add_repr` of the two pairings on the left.

Route of the limit passage (the cut-offs are sent to `1` simultaneously): the `z`-cut-off term
vanishes because `|∫_θ σ ψ (U·BB)| ≤ √(∫_θ σU²)·√(∫_θ σB²)·w²` and the extra factor `z·χ_k'`
is uniformly bounded with support escaping to `0` and `∞` (`cut_deriv_tendsto_zero`); the
`ψ`-cut-off term vanishes by the endpoint rate of `U` (`slice_rate`); the three remaining terms
pass to their limits by dominated convergence (`HkMem` of `AA`, `BB`, `V` and the `N`-bound of
`N_bound`, which controls `w²U²cos²(2θ)σ₂`).
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)


end

end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkMem_JepsSub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The slot of the difference

The one place where the hypothesis `hlin` of the statement is used: on the open quadrant each mixed
slot of `J_ε f - f` is the difference of the corresponding slots of `J_ε f` and of `f`.  The second
equality is the `C^∞`-commutation `mixed_Jeps` of `E1`; the first is the hypothesis itself. -/




/-! ## The main theorem -/


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDthW.hardTermWlInf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDthW

set_option autoImplicit false
set_option maxHeartbeats 1600000


end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDthW
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.assembly_core =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `SmoothOpen`-closure of the elementary combinations -/

/-- The negation of an open-quadrant-smooth datum. -/
theorem smoothOpen_neg' {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -g z θ) := by
  have hfun : Function.uncurry (fun z θ => -g z θ) = -(Function.uncurry g) := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact hg.neg

/-- The sum of two open-quadrant-smooth data. -/
theorem smoothOpen_add' {f g : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  have hfun : Function.uncurry (fun z θ => f z θ + g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact hf.add hg

/-- The difference of two open-quadrant-smooth data. -/
theorem smoothOpen_sub' {f g : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h : Function.uncurry (fun z θ => f z θ - g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p - Function.uncurry g p := rfl
  rw [h]
  exact (hf.forall n).sub (hg.forall n)

/-! ## The pointwise additivity of the weighted integrand -/

/-- **Pointwise additivity of `HkIntegrand`** on the closed domain, for data smooth on the open
quadrant: this is `EllipticEst.HkIntegrand_add_le_of_contDiffOn` (whose smoothness set is
`Q0`). -/
theorem HkIntegrand_add_le' (α : ℝ) (k : ℕ) {f g : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ :=
  Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn α k hf hg

/-- **Pointwise subadditivity of `HkIntegrand`**: the integrand of a difference is dominated by
`2` (integrand of each factor).  Immediate from the additivity applied to `f` and `-g` and the
negation-invariance `EllipticEst.HkIntegrand_neg`. -/
theorem HkIntegrand_sub_le' (α : ℝ) (k : ℕ) {f g : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ - g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ hθ
  have hneg : Work.Spaces.HkIntegrand α k (fun z θ => -g z θ)
      = Work.Spaces.HkIntegrand α k g := by
    have h := Work.FTS.EllipticEst.HkIntegrand_neg α k g
    rwa [show (-g : Fn) = fun z θ => -g z θ from rfl] at h
  have he : (fun z θ => f z θ - g z θ) = fun z θ => f z θ + (fun z θ => -g z θ) z θ := by
    funext z θ
    exact sub_eq_add_neg (f z θ) (g z θ)
  rw [he]
  have h := HkIntegrand_add_le' α k hf (smoothOpen_neg' hg) z hz θ hθ
  rw [hneg] at h
  exact h

/-! ## The `HkMem`-closure of the elementary combinations -/

/-- **`HkMem` of a sum**: from the memberships of the two summands and their open-quadrant
smoothness. -/
theorem HkMem_add_of_HkMem (α : ℝ) (k : ℕ) {f g : Fn}
    (hf_sm : Work.FTS.EllipticEst.SmoothOpen f) (hg_sm : Work.FTS.EllipticEst.SmoothOpen g)
    (hf : Work.Spaces.HkMem α k f) (hg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) :=
  Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open α k
    (smoothOpen_add' hf_sm hg_sm) hf hg
    (fun z hz => ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => HkIntegrand_add_le' α k hf_sm hg_sm z hz θ hθ))

/-- **`HkMem` of a difference**: from the memberships of the two summands and their
open-quadrant smoothness. -/
theorem HkMem_sub_of_HkMem (α : ℝ) (k : ℕ) {f g : Fn}
    (hf_sm : Work.FTS.EllipticEst.SmoothOpen f) (hg_sm : Work.FTS.EllipticEst.SmoothOpen g)
    (hf : Work.Spaces.HkMem α k f) (hg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) :=
  Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open α k
    (smoothOpen_sub' hf_sm hg_sm) hf hg
    (fun z hz => ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => HkIntegrand_sub_le' α k hf_sm hg_sm z hz θ hθ))

/-! ## The four-fold splitting of the pairing -/


end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.IP6_cs_coeffs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Descent of the honest class along the two recursion slots -/

/-- The honest `ℋⁿ`-class is preserved by `D_θ` when the level drops by one. -/
theorem hqo_dth {α : ℝ} {n : ℕ} {u : Fn} (hα : -(1 / 10 : ℝ) ≤ α)
    (hu : Work.FTS.VocabO.HQo α (n + 1) u) : Work.FTS.VocabO.HQo α n (Work.Spaces.Dth u) :=
  ⟨hu.1.Dth, Work.FTS.IPGen.HkMem_Dth_le hα hu.1 hu.2⟩

/-- The honest `ℋⁿ`-class is preserved by `D_z` when the level drops by one. -/
theorem hqo_dz {α : ℝ} {n : ℕ} {u : Fn} (hu : Work.FTS.VocabO.HQo α (n + 1) u) :
    Work.FTS.VocabO.HQo α n (Work.Spaces.Dz u) :=
  ⟨hu.1.Dz, Work.FTS.IPGen.HkMem_Dz_le hu.1 hu.2⟩

/-- The honest `ℋˡ`-class for `l ≤ k` is contained in the honest `ℋᵏ`-class. -/
theorem hqo_mono {α : ℝ} {k l : ℕ} {u : Fn} (hkl : l ≤ k) (hu : Work.FTS.VocabO.HQo α k u) :
    Work.FTS.VocabO.HQo α l u :=
  ⟨hu.1, Work.FTS.IPGen.HkMem_mono_le hu.1 l hkl hu.2⟩

/-! ## The three norm comparisons of the recursion step -/

/-- The `ℋⁿ`-norm of `u` is dominated by its `ℋ^{n+1}`-norm. -/
theorem hkNorm_mono {α : ℝ} {n : ℕ} {u : Fn} (hu : Work.Spaces.HkMem α (n + 1) u) :
    Work.Spaces.HkNorm α n u ≤ Work.Spaces.HkNorm α (n + 1) u :=
  Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hu)

/-- The `ℋⁿ`-norm of `D_θ u` is dominated by the `ℋ^{n+1}`-norm of `u`
(`CoercivityFix.Assembly.HkSq_Dth_le_ge` in square-root form). -/
theorem hkNorm_dth {α : ℝ} {n : ℕ} {u : Fn} (hα : 0 < α)
    (hu : Work.Spaces.HkMem α (n + 1) u) :
    Work.Spaces.HkNorm α n (Work.Spaces.Dth u) ≤ Work.Spaces.HkNorm α (n + 1) u :=
  Real.sqrt_le_sqrt (Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge α (by linarith) n hu)

/-- **The `D_z`-index shift for the squared `ℋ`-norm, in the open class**: for a profile
which is `C^∞` on the open quadrant and honest in `ℋ^{n+1}`, the squared `ℋⁿ`-norm of
`D_z u` is dominated by the squared `ℋ^{n+1}`-norm of `u`.  This is
`CoercivityStep.Norm.HkSq_Dz_le` with the analytic hypothesis `SmoothNbhd` weakened to
`SmoothOpen` (the pointwise domination of the integrands is the same,
`EllipticEst.UopHk.HkIntegrand_Dz_le_succ`). -/
theorem hkSq_dz_le_open (α : ℝ) (n : ℕ) {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hm : Work.Spaces.HkMem α (n + 1) u) :
    Work.Spaces.HkSq α n (Work.Spaces.Dz u) ≤ Work.Spaces.HkSq α (n + 1) u := by
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz u) z θ) hm.2 ?_
  show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (Work.Spaces.Dz u) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (n + 1) u z θ
  exact MeasureTheory.ae_restrict_of_forall_mem hmesz fun z hz =>
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz u) z θ)
      (hm.1 z hz)
      (MeasureTheory.ae_restrict_of_forall_mem hmesθ fun θ hθ =>
        Work.FTS.EllipticEst.UopHk.HkIntegrand_Dz_le_succ α n hu z θ hz hθ)

/-- The `ℋⁿ`-norm of `D_z u` is dominated by the `ℋ^{n+1}`-norm of `u`, in the open class. -/
theorem hkNorm_dz {α : ℝ} {n : ℕ} {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hm : Work.Spaces.HkMem α (n + 1) u) :
    Work.Spaces.HkNorm α n (Work.Spaces.Dz u) ≤ Work.Spaces.HkNorm α (n + 1) u :=
  Real.sqrt_le_sqrt (hkSq_dz_le_open α n hu hm)

/-! ## The arithmetic of the triple product -/

/-- `CC * A * B ≤ CC * A' * B'` for nonnegative `CC`, `A`, `B` and `A ≤ A'`, `B ≤ B'`. -/
theorem mul_three_le {CC A A' B B' : ℝ} (hCC : 0 ≤ CC) (hA : A ≤ A') (hB : B ≤ B')
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) : CC * A * B ≤ CC * A' * B' := by
  have h1 : CC * A ≤ CC * A' := mul_le_mul_of_nonneg_left hA hCC
  have h2 : CC * A * B ≤ CC * A' * B := mul_le_mul_of_nonneg_right h1 hB0
  have h3 : CC * A' * B ≤ CC * A' * B' :=
    mul_le_mul_of_nonneg_left hB (mul_nonneg hCC (le_trans hA0 hA))
  linarith

/-! ## One step of the recursion -/

/-- **One step of the Cauchy–Schwarz recursion.**  If `IP` satisfies a Cauchy–Schwarz bound
against the `ℋⁿ`-norm with constant `CC`, then `HkIPStep c₁ c₂ IP` satisfies one against the
`ℋ^{n+1}`-norm with constant `(1 + |c₁| + |c₂|) · CC`: the three slots `u`, `D_θu`, `D_zu`
of `HkIPStep` all sit inside the `(n+1)`-ball (`hkNorm_mono`, `hkNorm_dth`, `hkNorm_dz`),
and the triangle inequality is taken with `|c₁|`, `|c₂|`.  No positivity of the coefficients
is needed. -/
theorem abs_HkIPStep_le {α : ℝ} (hα : 0 < α) {n : ℕ} {IP : Fn → Fn → ℝ} {CC c₁ c₂ : ℝ}
    (hCC : 0 ≤ CC)
    (hcs : ∀ u v : Fn, Work.FTS.VocabO.HQo α n u → Work.FTS.VocabO.HQo α n v →
      |IP u v| ≤ CC * Work.Spaces.HkNorm α n u * Work.Spaces.HkNorm α n v) :
    ∀ u v : Fn, Work.FTS.VocabO.HQo α (n + 1) u → Work.FTS.VocabO.HQo α (n + 1) v →
      |Work.Coercivity.HkIPStep c₁ c₂ IP u v|
        ≤ (1 + |c₁| + |c₂|) * CC * Work.Spaces.HkNorm α (n + 1) u
            * Work.Spaces.HkNorm α (n + 1) v := by
  have hα' : -(1 / 10 : ℝ) ≤ α := by linarith
  intro u v hu hv
  -- the six slots of the step, and their norm comparisons
  have hun : Work.FTS.VocabO.HQo α n u := hqo_mono (Nat.le_succ n) hu
  have hvn : Work.FTS.VocabO.HQo α n v := hqo_mono (Nat.le_succ n) hv
  have huth : Work.FTS.VocabO.HQo α n (Work.Spaces.Dth u) := hqo_dth hα' hu
  have hvth : Work.FTS.VocabO.HQo α n (Work.Spaces.Dth v) := hqo_dth hα' hv
  have huz : Work.FTS.VocabO.HQo α n (Work.Spaces.Dz u) := hqo_dz hu
  have hvz : Work.FTS.VocabO.HQo α n (Work.Spaces.Dz v) := hqo_dz hv
  have e0u : Work.Spaces.HkNorm α n u ≤ Work.Spaces.HkNorm α (n + 1) u := hkNorm_mono hu.2
  have e0v : Work.Spaces.HkNorm α n v ≤ Work.Spaces.HkNorm α (n + 1) v := hkNorm_mono hv.2
  have e1u : Work.Spaces.HkNorm α n (Work.Spaces.Dth u) ≤ Work.Spaces.HkNorm α (n + 1) u :=
    hkNorm_dth hα hu.2
  have e1v : Work.Spaces.HkNorm α n (Work.Spaces.Dth v) ≤ Work.Spaces.HkNorm α (n + 1) v :=
    hkNorm_dth hα hv.2
  have e2u : Work.Spaces.HkNorm α n (Work.Spaces.Dz u) ≤ Work.Spaces.HkNorm α (n + 1) u :=
    hkNorm_dz hu.1 hu.2
  have e2v : Work.Spaces.HkNorm α n (Work.Spaces.Dz v) ≤ Work.Spaces.HkNorm α (n + 1) v :=
    hkNorm_dz hv.1 hv.2
  -- the three terms of the step
  have hA : |IP u v| ≤ CC * Work.Spaces.HkNorm α (n + 1) u
      * Work.Spaces.HkNorm α (n + 1) v :=
    le_trans (hcs u v hun hvn)
      (mul_three_le hCC e0u e0v (Work.Spaces.HkNorm_nonneg α n u)
        (Work.Spaces.HkNorm_nonneg α n v))
  have hB : |IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) u * Work.Spaces.HkNorm α (n + 1) v :=
    le_trans (hcs _ _ huth hvth)
      (mul_three_le hCC e1u e1v (Work.Spaces.HkNorm_nonneg α n (Work.Spaces.Dth u))
        (Work.Spaces.HkNorm_nonneg α n (Work.Spaces.Dth v)))
  have hC : |IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) u * Work.Spaces.HkNorm α (n + 1) v :=
    le_trans (hcs _ _ huz hvz)
      (mul_three_le hCC e2u e2v (Work.Spaces.HkNorm_nonneg α n (Work.Spaces.Dz u))
        (Work.Spaces.HkNorm_nonneg α n (Work.Spaces.Dz v)))
  set Z : ℝ := CC * Work.Spaces.HkNorm α (n + 1) u * Work.Spaces.HkNorm α (n + 1) v with hZ
  have htri : |IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)
      + c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
      ≤ Z + |c₁| * Z + |c₂| * Z := by
    have h1 : |IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
        ≤ |IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
          + |c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)| := abs_add_le _ _
    have h2 : |IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
        ≤ |IP u v| + |c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)| := abs_add_le _ _
    have h3 : |c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
        = |c₁| * |IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)| := abs_mul _ _
    have h4 : |c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
        = |c₂| * |IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)| := abs_mul _ _
    have h5 : |c₁| * |IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)| ≤ |c₁| * Z :=
      mul_le_mul_of_nonneg_left hB (abs_nonneg c₁)
    have h6 : |c₂| * |IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)| ≤ |c₂| * Z :=
      mul_le_mul_of_nonneg_left hC (abs_nonneg c₂)
    linarith
  have hstep : Work.Coercivity.HkIPStep c₁ c₂ IP u v
      = IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v) := rfl
  rw [hstep]
  calc |IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
      ≤ Z + |c₁| * Z + |c₂| * Z := htri
    _ = (1 + |c₁| + |c₂|) * CC * Work.Spaces.HkNorm α (n + 1) u
          * Work.Spaces.HkNorm α (n + 1) v := by
        rw [hZ]; ring

/-! ## The level-six Cauchy–Schwarz bound -/

/-- **Cauchy–Schwarz for the level-six pairing `IP6`**, for arbitrary coefficients: there is
a constant `CC > 0`, depending only on the ten step coefficients, such that
`|IP6 … α f g| ≤ CC |f|_{ℋ⁶} |g|_{ℋ⁶}` for every `α ∈ (0, α₂]` and every pair of honest
`ℋ⁶` profiles. -/
theorem IP6_cs_coeffs (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α₂ : ℝ) (hα₂ : 0 < α₂) :
    ∃ CC : ℝ, 0 < CC ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 6 f → Work.FTS.VocabO.HQo α 6 g →
      |Work.FTS.StrongPersist.IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
        ≤ CC * Work.FTS.StrongPersist.Xn6 α f * Work.FTS.StrongPersist.Xn6 α g := by
  -- the constant: five lifts, each multiplying by `1 + |c₁| + |c₂|`
  let C0 : ℝ := 10 ^ 22
  let C1 : ℝ := (1 + |c₁| + |c₂|) * C0
  let C2 : ℝ := (1 + |c₁'| + |c₂'|) * C1
  let C3 : ℝ := (1 + |c₁''| + |c₂''|) * C2
  let C4 : ℝ := (1 + |f₁| + |f₂|) * C3
  let C5 : ℝ := (1 + |e₁| + |e₂|) * C4
  have hC0 : 0 < C0 := by norm_num
  have h1 : (0 : ℝ) < 1 + |c₁| + |c₂| := by
    have a := abs_nonneg c₁; have b := abs_nonneg c₂; linarith
  have h2 : (0 : ℝ) < 1 + |c₁'| + |c₂'| := by
    have a := abs_nonneg c₁'; have b := abs_nonneg c₂'; linarith
  have h3 : (0 : ℝ) < 1 + |c₁''| + |c₂''| := by
    have a := abs_nonneg c₁''; have b := abs_nonneg c₂''; linarith
  have h4 : (0 : ℝ) < 1 + |f₁| + |f₂| := by
    have a := abs_nonneg f₁; have b := abs_nonneg f₂; linarith
  have h5 : (0 : ℝ) < 1 + |e₁| + |e₂| := by
    have a := abs_nonneg e₁; have b := abs_nonneg e₂; linarith
  have hC1 : 0 < C1 := mul_pos h1 hC0
  have hC2 : 0 < C2 := mul_pos h2 hC1
  have hC3 : 0 < C3 := mul_pos h3 hC2
  have hC4 : 0 < C4 := mul_pos h4 hC3
  have hC5 : 0 < C5 := mul_pos h5 hC4
  refine ⟨C5, hC5, ?_⟩
  intro α hα f g hf hg
  have hα0 : 0 < α := hα.1
  -- the base: `H1IP` against the `ℋ¹`-norm on the honest class
  have cs0 : ∀ u v : Fn, Work.FTS.VocabO.HQo α 1 u → Work.FTS.VocabO.HQo α 1 v →
      |Work.Coercivity.H1IP α u v| ≤ C0 * Work.Spaces.HkNorm α 1 u * Work.Spaces.HkNorm α 1 v :=
    fun u v hu hv => Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem α hα0 u v hu.2 hv.2
  -- the five lifts
  have cs1 := abs_HkIPStep_le hα0 (c₁ := c₁) (c₂ := c₂) (le_of_lt hC0) cs0
  have cs2 := abs_HkIPStep_le hα0 (c₁ := c₁') (c₂ := c₂') (le_of_lt hC1) cs1
  have cs3 := abs_HkIPStep_le hα0 (c₁ := c₁'') (c₂ := c₂'') (le_of_lt hC2) cs2
  have cs4 := abs_HkIPStep_le hα0 (c₁ := f₁) (c₂ := f₂) (le_of_lt hC3) cs3
  have cs5 := abs_HkIPStep_le hα0 (c₁ := e₁) (c₂ := e₂) (le_of_lt hC4) cs4
  -- identify the composite with `IP6`
  have hIP4 : Work.Coercivity.HkIPStep c₁'' c₂''
        (Work.Coercivity.HkIPStep c₁' c₂'
          (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)))
      = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α := by
    simpa only [Work.FTS.IPGen.IPnG_succ, Work.FTS.IPGen.IPnG_zero] using
      Work.FTS.IPGen.IPnG_eq_IP4 (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
        (c₁'' := c₁'') (c₂'' := c₂'') (α := α)
  have hIP6 : Work.FTS.StrongPersist.IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α
      = Work.Coercivity.HkIPStep e₁ e₂ (Work.Coercivity.HkIPStep f₁ f₂
          (Work.Coercivity.HkIPStep c₁'' c₂'' (Work.Coercivity.HkIPStep c₁' c₂'
            (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α))))) := by
    rw [Work.FTS.StrongPersist.IP6, hIP4]
  rw [hIP6]
  exact cs5 f g hf hg

end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3_lin_mem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The raw forms of the two separated coefficients -/

/-- The nonlocal coefficient `(2z/(1+z)²)·(Γ(θ)/c(α))`, in the form in which the delegated
piece estimates state it. -/
def AcR (α : ℝ) : Fn :=
  fun z θ => (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ / Work.Spaces.c α)

/-- The projector coefficient `(Γ(θ)/c(α))·(2z²/(1+z)³)`, in the raw form. -/
def BcR (α : ℝ) : Fn :=
  fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)

/-- The nonlocal coefficient of `𝓛_Γ` is the separated one. -/
theorem Acoef_eq_AcR (α : ℝ) (z θ : ℝ) : Acoef α z θ = AcR α z θ := by
  rw [Acoef_eq_mul]
  rfl


/-- **`linPart` in the raw form of the three pieces.** -/
theorem linPart_eq_raw (α : ℝ) (f : Fn) :
    linPart α f
      = fun z θ => locOp f z θ + AcR α z θ * Mf f z θ - BcR α z θ * K0f f := by
  rw [linPart_eq]
  funext z θ
  rw [Acoef_eq_AcR, show Bcoef α z θ = BcR α z θ from rfl]

/-! ## The projector piece -/

/-- **The projector piece.**  `BcR α · K0f f` is the constant `K0f f` times the fixed
`ℋ³`-function `BcR α`, so its level-three square is `(K0f f)² · HkSq α 3 (BcR α)`; with
`|K0f f| ≤ C₆|f|_{ℋ⁴}` and `|BcR α|_{ℋ³}² ≤ C₇` this is `C₆²C₇ |f|²_{ℋ⁴}`. -/
theorem proj_le (C6 C7 : ℝ) (h6 : 0 < C6) (h7 : 0 < C7)
    (hK0 : ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → HkMem α 4 f →
      |K0f f| ≤ C6 * HkNorm α 4 f)
    (hB0 : ∀ (α : ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen (BcR α) ∧ HkMem α 3 (BcR α) ∧
      HkSq α 3 (BcR α) ≤ C7) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → HkMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => BcR α z θ * K0f f) ∧
      HkMem α 3 (fun z θ => BcR α z θ * K0f f) ∧
      HkSq α 3 (fun z θ => BcR α z θ * K0f f) ≤ C * HkSq α 4 f := by
  refine ⟨C6 ^ 2 * C7 + 1, by positivity, ?_⟩
  intro α f hα hα1 _hsm hmem4
  obtain ⟨hBsm, hBmem, hBsq⟩ := hB0 α hα hα1
  set c : ℝ := K0f f with hc
  have hK0b : |c| ≤ C6 * HkNorm α 4 f := hK0 α f hα hα1 hmem4
  have hfun : (fun z θ => BcR α z θ * K0f f) = fun z θ => c * BcR α z θ := by
    funext z θ; rw [hc]; ring
  rw [hfun]
  have hident : ∀ z θ, Work.Spaces.HkIntegrand α 3 (fun z θ => c * BcR α z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α 3 (BcR α) z θ :=
    fun z θ => Work.FTS.GalBasis.hkIntegrand_const_mul α 3 c (BcR α) z θ
  have hmem : HkMem α 3 (fun z θ => c * BcR α z θ) := by
    constructor
    · intro z hz
      rw [show (fun θ => Work.Spaces.HkIntegrand α 3 (fun z θ => c * BcR α z θ) z θ)
          = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α 3 (BcR α) z θ from funext (hident z)]
      exact (hBmem.1 z hz).const_mul _
    · have hz : (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 3 (fun z θ => c * BcR α z θ) z θ)
          = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 3 (BcR α) z θ := by
        funext z
        rw [show (fun θ => Work.Spaces.HkIntegrand α 3 (fun z θ => c * BcR α z θ) z θ)
            = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α 3 (BcR α) z θ from
              funext (hident z), MeasureTheory.integral_const_mul]
      rw [hz]
      exact hBmem.2.const_mul _
  have hsq : HkSq α 3 (fun z θ => c * BcR α z θ) = c ^ 2 * HkSq α 3 (BcR α) := by
    rw [show (fun z θ => c * BcR α z θ) = c • BcR α from rfl,
      Work.FTS.EllipticEst.HkSq_smul]
  refine ⟨?_, hmem, ?_⟩
  · exact Work.FTS.EllipticEst.smoothOpen_const_mul' c hBsm
  · rw [hsq]
    have hc2 : c ^ 2 ≤ (C6 * HkNorm α 4 f) ^ 2 := by
      have h1 := abs_le.mp hK0b
      have h2 : (0:ℝ) ≤ C6 * HkNorm α 4 f :=
        mul_nonneg h6.le (Work.Spaces.HkNorm_nonneg α 4 f)
      nlinarith [h1.1, h1.2, h2]
    have hbig : c ^ 2 * HkSq α 3 (BcR α) ≤ (C6 * HkNorm α 4 f) ^ 2 * C7 :=
      mul_le_mul hc2 hBsq (Work.Spaces.HkSq_nonneg α 3 (BcR α))
        (sq_nonneg (C6 * HkNorm α 4 f))
    have hnorm_sq : HkNorm α 4 f ^ 2 = HkSq α 4 f := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    have htarget : (C6 * HkNorm α 4 f) ^ 2 * C7 = (C6 ^ 2 * C7) * HkSq α 4 f := by
      rw [mul_pow, hnorm_sq]; ring
    calc c ^ 2 * HkSq α 3 (BcR α) ≤ (C6 * HkNorm α 4 f) ^ 2 * C7 := hbig
      _ = (C6 ^ 2 * C7) * HkSq α 4 f := htarget
      _ ≤ (C6 ^ 2 * C7 + 1) * HkSq α 4 f := by
          have h0 : (0:ℝ) ≤ HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
          nlinarith [h0]

/-! ## The assembly -/

/-- **Assembly of the three pieces.**  Given the three piece estimates, the sum
`locOp f + AcR α · Mf f - BcR α · K0f f` is in `ℋ³` with a bound `C₃(1+|f|_{ℋ⁴})⁴`. -/
theorem assemble
    (C_loc C_A C_B : ℝ) (hCloc : 0 < C_loc) (hCA : 0 < C_A) (hCB : 0 < C_B)
    (hloc : ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      HkMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen (locOp f) ∧ HkMem α 3 (locOp f) ∧
      HkSq α 3 (locOp f) ≤ C_loc * HkSq α 4 f)
    (hA : ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      HkMem α 4 f → Work.Construction.L12 f 0 = 0 →
      ContDiffOn ℝ 3 (Function.uncurry (fun z θ => AcR α z θ * Mf f z θ))
        Work.FTS.EllipticEst.Q0 ∧
      HkMem α 3 (fun z θ => AcR α z θ * Mf f z θ) ∧
      HkSq α 3 (fun z θ => AcR α z θ * Mf f z θ) ≤ C_A * HkSq α 4 f)
    (hB : ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      HkMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => BcR α z θ * K0f f) ∧
      HkMem α 3 (fun z θ => BcR α z θ * K0f f) ∧
      HkSq α 3 (fun z θ => BcR α z θ * K0f f) ≤ C_B * HkSq α 4 f) :
    ∃ C3 : ℝ, 0 < C3 ∧ ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → HkMem α 6 f →
      Work.Construction.L12 f 0 = 0 →
      HkMem α 3 (fun z θ => locOp f z θ + AcR α z θ * Mf f z θ - BcR α z θ * K0f f) ∧
      HkNorm α 3 (fun z θ => locOp f z θ + AcR α z θ * Mf f z θ - BcR α z θ * K0f f)
        ≤ C3 * (1 + HkNorm α 4 f) ^ 4 := by
  refine ⟨Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) + 1, by
    have h1 : (0:ℝ) ≤ 4 * C_loc + 4 * C_A + 4 * C_B := by linarith
    have h2 := Real.sqrt_nonneg (4 * C_loc + 4 * C_A + 4 * C_B)
    linarith, ?_⟩
  intro α f hα hα1 hsm hmem6 h0
  have hmem4 : HkMem α 4 f := Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hmem6
  obtain ⟨hLs, hLm, hLq⟩ := hloc α f hα hα1 hsm hmem4
  obtain ⟨hAsm, hAm, hAq⟩ := hA α f hα hα1 hsm hmem4 h0
  obtain ⟨hBs, hBm, hBq⟩ := hB α f hα hα1 hsm hmem4
  have hLsm : ContDiffOn ℝ 3 (Function.uncurry (locOp f)) Work.FTS.EllipticEst.Q0 :=
    hLs.forall 3
  have hBsm : ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => BcR α z θ * K0f f)) Work.FTS.EllipticEst.Q0 :=
    hBs.forall 3
  obtain ⟨hm3, hs3⟩ := Work.FTS.StrongPersist.L3Aux.HkMem_HkSq_add3_le α 3 (by norm_num)
    hLsm hAsm hBsm hLm hAm hBm
  have hSqnn : (0:ℝ) ≤ HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have hbound : HkSq α 3
      (fun z θ => locOp f z θ + AcR α z θ * Mf f z θ - BcR α z θ * K0f f)
      ≤ (4 * C_loc + 4 * C_A + 4 * C_B) * HkSq α 4 f := by
    linarith [hs3, hLq, hAq, hBq, hSqnn]
  refine ⟨hm3, ?_⟩
  have hsqrt : HkNorm α 3
        (fun z θ => locOp f z θ + AcR α z θ * Mf f z θ - BcR α z θ * K0f f)
      ≤ Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) * HkNorm α 4 f := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    refine (Real.sqrt_le_sqrt hbound).trans_eq ?_
    rw [Real.sqrt_mul (by linarith : (0:ℝ) ≤ 4 * C_loc + 4 * C_A + 4 * C_B)]
  have hXn : HkNorm α 4 f ≤ (1 + HkNorm α 4 f) ^ 4 := by
    set x := HkNorm α 4 f with hx
    have hx0 : 0 ≤ x := Work.Spaces.HkNorm_nonneg α 4 f
    have h3 : (1:ℝ) ≤ (1 + x) ^ 3 := one_le_pow₀ (by linarith) (n := 3)
    have h4 : (1 + x) ≤ (1 + x) ^ 4 := by
      have : (1 + x) ^ 4 = (1 + x) * (1 + x) ^ 3 := by ring
      rw [this]
      exact le_mul_of_one_le_right (by linarith) h3
    linarith
  have hs : (0:ℝ) ≤ Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) := Real.sqrt_nonneg _
  have hX4 : (0:ℝ) ≤ (1 + HkNorm α 4 f) ^ 4 := by positivity
  calc HkNorm α 3
        (fun z θ => locOp f z θ + AcR α z θ * Mf f z θ - BcR α z θ * K0f f)
      ≤ Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) * HkNorm α 4 f := hsqrt
    _ ≤ (Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) + 1)
          * (1 + HkNorm α 4 f) ^ 4 := by
        calc Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) * HkNorm α 4 f
            ≤ Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) * (1 + HkNorm α 4 f) ^ 4 :=
              mul_le_mul_of_nonneg_left hXn hs
          _ ≤ (Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) + 1)
                * (1 + HkNorm α 4 f) ^ 4 := by
              nlinarith [hs, hX4]

/-! ## The target -/

theorem L3_lin_mem : ∃ α₂ C3 : ℝ, 0 < α₂ ∧ 0 < C3 ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongPersist.H6Adm α f →
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.linPart α f) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.linPart α f)
        ≤ C3 * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 := by
  obtain ⟨C_loc, hCloc, hloc⟩ := Work.FTS.StrongPersist.L3Aux.locOp_HkSq_le
  obtain ⟨C_A, hCA, hA⟩ := Work.FTS.StrongPersist.L3Aux.Acoef_Mf_le
  obtain ⟨C6, hC6, hK0⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  obtain ⟨C7, hC7, hB0⟩ := Work.FTS.StrongPersist.L3Aux.bcoef_gamCoef_le
  obtain ⟨C_B, hCB, hB⟩ := proj_le C6 C7 hC6 hC7 hK0 hB0
  obtain ⟨C3, hC3, hassemble⟩ := assemble C_loc C_A C_B hCloc hCA hCB hloc hA hB
  refine ⟨1, C3, one_pos, hC3, ?_⟩
  intro α hα f hf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem6 : HkMem α 6 f := hf.reg.2
  have h0 : Work.Construction.L12 f 0 = 0 := hf.l12
  have hres := hassemble α f hα0 hα1 hsm hmem6 h0
  rw [linPart_eq_raw α f]
  refine ⟨hres.1, ?_⟩
  simpa only [Work.FTS.Nonlin.Xn] using hres.2

end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.TermBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The per-term bound of the level-6 `T2` slot

For a slot `(a, b)` with `a + b ≤ 6` and a Leibniz summand
`D_z^{b1}D_θ^{a1}f · D_z^{b-b1+1}D_θ^{a-a1}g · D_z^bD_θ^a g` with `a1 + b1 ≥ 1`, the
product-measure integral of its absolute value is bounded by `Λ · |g|²_{ℋ⁶}`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)
open Work.FTS.StrongPersist.N6Trans.T1SixAux (SlotW6 slotW6_z slotW6_mixed)

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem term_bound {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (h : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (ha1 : a1 ≤ a) (hb1 : b1 ≤ b) (hp : 1 ≤ a1 + b1) (hab : a + b ≤ 6)
    (hΛE1 : Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
      ≤ Λ)
    (hΛE2 : Real.sqrt (10 * excC02) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
      ≤ Λ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.mixed b1 a1 f p.1 p.2|
      * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
      * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
    (∫ p, canonW q p.1 p.2
      * |Work.Spaces.mixed b1 a1 f p.1 p.2|
      * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
      * |Work.Spaces.mixed b a g p.1 p.2| ∂pm) ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  have hsame : Kf * Work.Spaces.HkSq α 6 g ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    have hsq : Work.Spaces.HkSq α 6 g = (Work.Spaces.HkNorm α 6 g) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 g)]
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hΛ1 (sq_nonneg _)
  have hcross : Kg * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g))
      ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    have hsq : Work.Spaces.HkNorm α 6 g = Real.sqrt (Work.Spaces.HkSq α 6 g) := rfl
    rw [hsq]
    calc Kg * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g))
        = (Kg * Real.sqrt (Work.Spaces.HkSq α 6 f)) * Real.sqrt (Work.Spaces.HkSq α 6 g) := by
          ring
      _ ≤ (Λ * Real.sqrt (Work.Spaces.HkSq α 6 g)) * Real.sqrt (Work.Spaces.HkSq α 6 g) :=
          mul_le_mul_of_nonneg_right hΛ2 (Real.sqrt_nonneg _)
      _ = Λ * Real.sqrt (Work.Spaces.HkSq α 6 g) ^ 2 := by ring
  by_cases ha1z : a1 = 0
  · subst ha1z
    by_cases hb16 : b1 = 6
    · -- ## case D: `a = 0`, `b = b1 = 6`
      subst hb16
      have hb6 : b = 6 := by omega
      have ha0 : a = 0 := by omega
      subst hb6
      subst ha0
      simp only [Nat.sub_self, Nat.sub_zero, Nat.zero_add, Work.Spaces.mixed_zero_right]
      have hsl1 : SlotW6 α q (Work.Spaces.DzIter 6 f) f :=
        slotW6_z α (q := q) hq0 (hqη rfl) f 6 (by norm_num)
      have hsl2 : SlotW6 α q (Work.Spaces.DzIter 6 g) g :=
        slotW6_z α (q := q) hq0 (hqη rfl) g 6 (by norm_num)
      have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          canonW q z θ * |Work.Spaces.DzIter 6 f z θ| * |Work.Spaces.DzIter 1 g z θ|
            * |Work.Spaces.DzIter 6 g z θ| ≤ Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by
        intro z θ hz hθ hθ2
        have hzI : z ∈ Work.Spaces.Iz := hz.le
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
        have hpt2 := pair_cross_le (α := α) (q := q) hzI hθI hsl1 hsl2
        have hG : |Work.Spaces.DzIter 1 g z θ| ≤ Kg := h.gpure 1 (by norm_num) z θ hz hθ hθ2
        calc canonW q z θ * |Work.Spaces.DzIter 6 f z θ| * |Work.Spaces.DzIter 1 g z θ|
              * |Work.Spaces.DzIter 6 g z θ|
            = (canonW q z θ * |Work.Spaces.DzIter 6 f z θ| * |Work.Spaces.DzIter 6 g z θ|)
              * |Work.Spaces.DzIter 1 g z θ| := by ring
          _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) * Kg :=
              mul_le_mul hpt2 hG (abs_nonneg _)
                (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          _ = Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by ring
      have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          canonW q p.1 p.2 * |Work.Spaces.DzIter 6 f p.1 p.2| * |Work.Spaces.DzIter 1 g p.1 p.2|
            * |Work.Spaces.DzIter 6 g p.1 p.2|) pm :=
        aesm_canonW_abs_mul (q := q) ((hfs.DzIter 6).continuousOn)
          ((hgs.DzIter 1).continuousOn) ((hgs.DzIter 6).continuousOn)
      refine ⟨?_, ?_⟩
      · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
          (F := fun z θ => canonW q z θ * |Work.Spaces.DzIter 6 f z θ|
            * |Work.Spaces.DzIter 1 g z θ| * |Work.Spaces.DzIter 6 g z θ|) haesm
          (fun z θ hz hθ hθ2 => by
            rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
            exact hpt z θ hz hθ hθ2)).1
      · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
          (F := fun z θ => canonW q z θ * |Work.Spaces.DzIter 6 f z θ|
            * |Work.Spaces.DzIter 1 g z θ| * |Work.Spaces.DzIter 6 g z θ|) haesm
          (fun z θ hz hθ hθ2 => by
            rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
            exact hpt z θ hz hθ hθ2)).2.trans hcross
    · -- ## case A: `a1 = 0`, with the top slot `b1 = 5` treated separately
      by_cases hb1five : b1 = 5
      · by_cases ha0 : a = 0
        · exact term_bound_A5a hα hα1 hfs hfm hgs hgm h hKf0 hKg0 hΛ1 hΛ2 hq0 hqγ hqη hab
            ha0 rfl hb1five
        · have haeq : a = 1 := by omega
          have hb5 : b = 5 := by omega
          exact term_bound_A5b hα hα1 hfs hfm hgs hgm h hKf0 hKg0 hΛ1 hΛ2 hq0 hqγ hqη hab
            haeq rfl hb1five hb5 hΛE1
      have hb14 : b1 ≤ 4 := by omega
      have hb1pos : 1 ≤ b1 := by omega
      have hord1 : a - 0 + (b - b1 + 1) ≤ 6 := by omega
      have hsl1 : SlotW6 α q (Work.Spaces.mixed (b - b1 + 1) (a - 0) g) g := by
        rcases eq_or_ne (a - 0) 0 with h0 | h0
        · rw [h0, Work.Spaces.mixed_zero_right]
          exact slotW6_z α (q := q) hq0 (hqη (by omega)) g (b - b1 + 1) (by omega)
        · exact slotW6_mixed α (q := q) hq0 hqγ g (b - b1 + 1) (a - 0)
            (Nat.one_le_iff_ne_zero.mpr h0) hord1
      have hsl2 : SlotW6 α q (Work.Spaces.mixed b a g) g := by
        rcases eq_or_ne a 0 with h0 | h0
        · rw [h0, Work.Spaces.mixed_zero_right]
          exact slotW6_z α (q := q) hq0 (hqη h0) g b (by omega)
        · exact slotW6_mixed α (q := q) hq0 hqγ g b a (Nat.one_le_iff_ne_zero.mpr h0) hab
      have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          canonW q z θ * |Work.Spaces.mixed b1 0 f z θ|
            * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|
            * |Work.Spaces.mixed b a g z θ| ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ := by
        intro z θ hz hθ hθ2
        have hzI : z ∈ Work.Spaces.Iz := hz.le
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
        simp only [Work.Spaces.mixed_zero_right]
        have hF : |Work.Spaces.DzIter b1 f z θ| ≤ Kf := h.fpure b1 hb14 z θ hz hθ hθ2
        have hpt2 := slotW6_pair_le (α := α) (q := q) hzI hθI hsl1 hsl2
        calc canonW q z θ * |Work.Spaces.DzIter b1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ| * |Work.Spaces.mixed b a g z θ|
            = |Work.Spaces.DzIter b1 f z θ| * (canonW q z θ
              * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|
              * |Work.Spaces.mixed b a g z θ|) := by ring
          _ ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ :=
              mul_le_mul hF hpt2 (by have h1 : 0 ≤ canonW q z θ := canonW_nonneg hθI; positivity) hKf0
      have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          canonW q p.1 p.2 * |Work.Spaces.mixed b1 0 f p.1 p.2|
            * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2|) pm :=
        aesm_canonW_abs_mul (q := q) ((hfs.mixed b1 0).continuousOn)
          ((hgs.mixed (b - b1 + 1) (a - 0)).continuousOn)
          ((hgs.mixed b a).continuousOn)
      refine ⟨?_, ?_⟩
      · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
          (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 0 f z θ|
            * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|
            * |Work.Spaces.mixed b a g z θ|) haesm
          (fun z θ hz hθ hθ2 => by
            rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
            exact hpt z θ hz hθ hθ2)).1
      · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
          (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 0 f z θ|
            * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|
            * |Work.Spaces.mixed b a g z θ|) haesm
          (fun z θ hz hθ hθ2 => by
            rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
            exact hpt z θ hz hθ hθ2)).2.trans hsame
  · have ha1pos : 1 ≤ a1 := Nat.one_le_iff_ne_zero.mpr ha1z
    have hapos : 1 ≤ a := le_trans ha1pos ha1
    have hFbody : (fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|)
        = (fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|) := rfl
    by_cases ha2z : a - a1 = 0
    · -- ## case C: the middle factor is pure
      by_cases hg16 : b - b1 + 1 = 6
      · -- ## case C2: the `σ`-gain
        have hb5 : b = 5 := by omega
        have hb1z : b1 = 0 := by omega
        have ha1e : a1 = 1 := by omega
        have hsl1 : SlotW6 α Work.Spaces.eta (Work.Spaces.DzIter 6 g) g :=
          slotW6_z α (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl g 6 (by norm_num)
        have hηγ : Work.Spaces.eta ≤ Work.Spaces.gam α := by
          rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
        have hsl2 : SlotW6 α Work.Spaces.eta (Work.Spaces.mixed 5 1 g) g :=
          slotW6_mixed α (q := Work.Spaces.eta) Work.Spaces.eta_pos hηγ g 5 1
            (by norm_num) (by norm_num)
        have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ| ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ := by
          intro z θ hz hθ hθ2
          have hzI : z ∈ Work.Spaces.Iz := hz.le
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          have hae : a = 1 := by omega
          have hidx1 : (5 - 0 + 1 : ℕ) = 6 := by norm_num
          have hidx2 : (1 - 1 : ℕ) = 0 := by norm_num
          rw [hb1z, ha1e, hb5, hae, hidx1, hidx2, Work.Spaces.mixed_zero_left,
            Work.Spaces.mixed_zero_right]
          have hDth : Work.Spaces.Dth f z θ
              = Real.sin (2 * θ) * Work.Spaces.pth f z θ := rfl
          have hσ0 : 0 < Real.sin (2 * θ) :=
            Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
          have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
          have hσt : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q)
              ≤ Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
            have h1 : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q)
                = Real.sin (2 * θ) ^ (1 - q) := by
              rw [show (1 : ℝ) - q = 1 + (-q) by ring, Real.rpow_add hσ0, Real.rpow_one]
            rw [h1]
            exact Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (by
              have hγη : Work.Spaces.gam α ≤ 1 + Work.Spaces.eta := by
                rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
              linarith)
          have hpth : |Work.Spaces.pth f z θ| ≤ Kf := h.pthf z θ hz hθ hθ2
          have hstep1 : canonW q z θ * |Work.Spaces.Dth f z θ|
              ≤ Kf * canonW Work.Spaces.eta z θ := by
            rw [hDth, abs_mul, abs_of_nonneg hσ0.le]
            simp only [canonW]
            calc (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-q)
                  * (Real.sin (2 * θ) * |Work.Spaces.pth f z θ|)
                = (Work.Spaces.w z) ^ 2
                    * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q))
                    * |Work.Spaces.pth f z θ| := by ring
              _ ≤ (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
                    * Kf := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_left hσt (sq_nonneg _)) hpth
                    (abs_nonneg _) (by positivity)
              _ = Kf * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)) := by ring
          have hpair := slotW6_pair_le (α := α) (q := Work.Spaces.eta) hzI hθI hsl1 hsl2
          calc canonW q z θ * |Work.Spaces.Dth f z θ| * |Work.Spaces.DzIter 6 g z θ|
                * |Work.Spaces.mixed 5 1 g z θ|
              = (canonW q z θ * |Work.Spaces.Dth f z θ|)
                * (|Work.Spaces.DzIter 6 g z θ| * |Work.Spaces.mixed 5 1 g z θ|) := by ring
            _ ≤ (Kf * canonW Work.Spaces.eta z θ)
                * (|Work.Spaces.DzIter 6 g z θ| * |Work.Spaces.mixed 5 1 g z θ|) :=
                mul_le_mul_of_nonneg_right hstep1 (by positivity)
            _ = Kf * (canonW Work.Spaces.eta z θ * |Work.Spaces.DzIter 6 g z θ|
                * |Work.Spaces.mixed 5 1 g z θ|) := by ring
            _ ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ :=
                mul_le_mul_of_nonneg_left hpair hKf0
        have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
            canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2|) pm :=
          aesm_canonW_abs_mul (q := q) ((hfs.mixed b1 a1).continuousOn)
            ((hgs.mixed (b - b1 + 1) (a - a1)).continuousOn)
            ((hgs.mixed b a).continuousOn)
        refine ⟨?_, ?_⟩
        · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).1
        · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).2.trans hsame
      · -- ## case C1: the middle factor is pure
        by_cases hg5 : b - b1 + 1 = 5
        · have hcase : (a = 1 ∧ b1 = 0) ∨ (a = 1 ∧ b1 = 1) ∨ (a = 2 ∧ b1 = 0) := by
            omega
          rcases hcase with ⟨h1a, h1b⟩ | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
          · exact term_bound_C1sigma hα hα1 hfs hfm hgs hgm h hKf0 hKg0 hΛ1 hΛ2 hq0 hqγ
              hqη hab h1a (by omega) h1b (by omega)
          · exact term_bound_C1E11 hα hα1 hfs hfm hgs hgm h hKf0 hKg0 hΛ1 hΛ2 hq0 hqγ
              hqη hab h2a (by omega) h2b (by omega) hΛE1
          · exact term_bound_C1E02 hα hα1 hfs hfm hgs hgm h hKf0 hKg0 hΛ1 hΛ2 hq0 hqγ
              hqη hab h3a (by omega) h3b (by omega) hΛE2
        have hg14 : b - b1 + 1 ≤ 4 := by omega
        have hord1 : a - a1 + (b - b1 + 1) ≤ 6 := by omega
        have hsl1 : SlotW6 α q (Work.Spaces.mixed b1 a1 f) f :=
          slotW6_mixed α (q := q) hq0 hqγ f b1 a1 ha1pos (by omega)
        have hsl2 : SlotW6 α q (Work.Spaces.mixed b a g) g :=
          slotW6_mixed α (q := q) hq0 hqγ g b a hapos hab
        have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ| ≤ Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by
          intro z θ hz hθ hθ2
          have hzI : z ∈ Work.Spaces.Iz := hz.le
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          have hcast : Work.Spaces.mixed (b - b1 + 1) (a - a1) g
              = Work.Spaces.DzIter (b - b1 + 1) g := by
            rw [ha2z, Work.Spaces.mixed_zero_right]
          rw [hcast]
          have hG : |Work.Spaces.DzIter (b - b1 + 1) g z θ| ≤ Kg :=
            h.gpure (b - b1 + 1) hg14 z θ hz hθ hθ2
          have hpair := pair_cross_le (α := α) (q := q) hzI hθI hsl1 hsl2
          calc canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
                * |Work.Spaces.DzIter (b - b1 + 1) g z θ| * |Work.Spaces.mixed b a g z θ|
              = (canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ| * |Work.Spaces.mixed b a g z θ|)
                * |Work.Spaces.DzIter (b - b1 + 1) g z θ| := by ring
            _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) * Kg :=
                mul_le_mul hpair hG (abs_nonneg _)
                  (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            _ = Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by ring
        have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
            canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2|) pm :=
          aesm_canonW_abs_mul (q := q) ((hfs.mixed b1 a1).continuousOn)
            ((hgs.mixed (b - b1 + 1) (a - a1)).continuousOn)
            ((hgs.mixed b a).continuousOn)
        refine ⟨?_, ?_⟩
        · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).1
        · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).2.trans hcross
    · -- ## case B: both `F` and `G` are mixed
      have ha2pos : 1 ≤ a - a1 := Nat.one_le_iff_ne_zero.mpr ha2z
      by_cases hp4 : a1 + b1 ≤ 4
      · -- bound `F`
        have hsl1 : SlotW6 α q (Work.Spaces.mixed (b - b1 + 1) (a - a1) g) g :=
          slotW6_mixed α (q := q) hq0 hqγ g (b - b1 + 1) (a - a1) ha2pos (by omega)
        have hsl2 : SlotW6 α q (Work.Spaces.mixed b a g) g :=
          slotW6_mixed α (q := q) hq0 hqγ g b a hapos hab
        have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ| ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ := by
          intro z θ hz hθ hθ2
          have hzI : z ∈ Work.Spaces.Iz := hz.le
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          have hF : |Work.Spaces.mixed b1 a1 f z θ| ≤ Kf :=
            h.fmix b1 a1 ha1pos hp4 z θ hz hθ hθ2
          have hpair := slotW6_pair_le (α := α) (q := q) hzI hθI hsl1 hsl2
          calc canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
                * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|
              = |Work.Spaces.mixed b1 a1 f z θ| * (canonW q z θ
                * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
                * |Work.Spaces.mixed b a g z θ|) := by ring
            _ ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ :=
                mul_le_mul hF hpair (by have h1 : 0 ≤ canonW q z θ := canonW_nonneg hθI; positivity) hKf0
        have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
            canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2|) pm :=
          aesm_canonW_abs_mul (q := q) ((hfs.mixed b1 a1).continuousOn)
            ((hgs.mixed (b - b1 + 1) (a - a1)).continuousOn)
            ((hgs.mixed b a).continuousOn)
        refine ⟨?_, ?_⟩
        · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).1
        · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).2.trans hsame
      · -- `p = 5`: bound `G`
        have hp5 : a1 + b1 = 5 := by omega
        have hg14 : a - a1 + (b - b1 + 1) ≤ 4 := by omega
        have hsl1 : SlotW6 α q (Work.Spaces.mixed b1 a1 f) f :=
          slotW6_mixed α (q := q) hq0 hqγ f b1 a1 ha1pos (by omega)
        have hsl2 : SlotW6 α q (Work.Spaces.mixed b a g) g :=
          slotW6_mixed α (q := q) hq0 hqγ g b a hapos hab
        have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ| ≤ Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by
          intro z θ hz hθ hθ2
          have hzI : z ∈ Work.Spaces.Iz := hz.le
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          have hG : |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| ≤ Kg :=
            h.gmix (b - b1 + 1) (a - a1) ha2pos hg14 z θ hz hθ hθ2
          have hpair := pair_cross_le (α := α) (q := q) hzI hθI hsl1 hsl2
          calc canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
                * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|
              = (canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ| * |Work.Spaces.mixed b a g z θ|)
                * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| := by ring
            _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) * Kg :=
                mul_le_mul hpair hG (abs_nonneg _)
                  (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            _ = Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by ring
        have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
            canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2|) pm :=
          aesm_canonW_abs_mul (q := q) ((hfs.mixed b1 a1).continuousOn)
            ((hgs.mixed (b - b1 + 1) (a - a1)).continuousOn)
            ((hgs.mixed b a).continuousOn)
        refine ⟨?_, ?_⟩
        · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).1
        · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).2.trans hcross

end Work.FTS.StrongPersist.N6Trans.SixAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.slotT1Six =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans

set_option autoImplicit false


end Work.FTS.StrongPersist.N6Trans
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6_prod =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist


end Work.FTS.StrongPersist
end
