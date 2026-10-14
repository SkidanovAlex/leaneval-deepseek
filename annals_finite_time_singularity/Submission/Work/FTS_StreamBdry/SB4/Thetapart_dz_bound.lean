import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.logW_fderiv_integral_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.H6Pair_ones3
import Submission.Work.FTS.TransportS.t2SlotGuarded
import Submission.Work.FTS_LocDatum3a.L12_Jeps_interchange_mine
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.SysAux.L12_tail_weight
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.angular_L2_noTrace
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.l12_zero_plainE
import Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE
import Submission.Work.FTS_StreamBdry.SB4.slice_L12_c2
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.factor_bound
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.GronwallAbsorb =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/GronwallAbsorb.lean` — LEAF L-C (**PROVED**, session 23)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 L-C).  Grönwall with an
`ε`-absorbed quadratic defect (continuous induction on the bound `2(1+E0)e^{2(Λ+1)T}`).

**Status: proved.**  The statement is byte-identical to the delegated sibling
`Work.FTS.StrongEps.E4R3.Apriori4Proofs.gronwall_absorb_proof`
(`Submission/Work/FTS/StrongEps/E4R3/Apriori4Proofs/gronwall_absorb_proof.lean`), which this file
now re-exports; the proof is the barrier/first-crossing argument, with its two auxiliary
real-analysis lemmas (`grAux_gronwall_le_exp`, `grAux_no_cross_up`) in the sibling module.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

set_option autoImplicit false

/-- **LEAF (L-C), proved** `e' ≤ Λ(1+e) + εC₁(1+e)²`, `ε` small ⟹ `1+e ≤ (1+E0)e^{2(Λ+1)T}`. -/
theorem gronwall_absorb {e : ℝ → ℝ} {T Λ C₁ ε E0 : ℝ} (hT : 0 < T) (hΛ : 0 ≤ Λ) (hC₁ : 0 ≤ C₁)
    (hε : 0 ≤ ε) (hE0 : 0 ≤ E0)
    (hcont : ContinuousOn e (Icc 0 T))
    (hd : ∀ τ ∈ Ioo 0 T, ∃ e' : ℝ, HasDerivAt e e' τ ∧
      e' ≤ Λ * (1 + e τ) + ε * C₁ * (1 + e τ) ^ 2)
    (he0 : e 0 ≤ E0)
    (hsmall : ε * C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T)) ≤ Λ + 1) :
    ∀ τ ∈ Icc 0 T, 1 + e τ ≤ (1 + E0) * Real.exp (2 * (Λ + 1) * T) :=
  Work.FTS.StrongEps.E4R3.Apriori4Proofs.gronwall_absorb_proof hT hΛ hC₁ hε hE0 hcont hd he0 hsmall

end Work.FTS.StrongEps.EpsE4Thr.E4R4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.JepsGainQuant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/JepsGainQuant.lean` — S3 (PROVED, corollary of `HkSq_Jeps_step_le`)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 S3; REVIEW fix F3: range `1 ≤ k ≤ 7`,
corollary of the proved `StrongEps.HkSq_Jeps_step_le`; do NOT use the stub `HkSq_Jeps_succ_le`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps

set_option autoImplicit false


end Work.FTS.StrongEps.EpsE4Thr.E4R4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.RawE6Deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/RawE6Deriv.lean` — OPEN LEAF S4 (research-low/mid; RISK R2 — dispatch FIRST)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 S4 / Risk R2; REVIEW fix F5).
The raw level-six energy identity along a regular solution.

**R2 (REVIEW F5).** Per-slice `HkMem 6` + joint `C¹` (all `EpsRegP` gives) does NOT yield
`HasDerivAt rawE6`: domination and the global pieces (`L12(·)(0)` inside `P₀`, the elliptic solve
`E`) need a bound uniform in `τ`.  This leaf therefore carries the uniform-in-`τ` bound
`hbdd6 : ∃ B, ∀ τ ∈ [0,T], Xn6 α (slice g τ) ≤ B` as an EXPLICIT hypothesis (`EpsRegP` is not
edited).  Its consumer (the `ℋ⁶`-half `sixthChapterB_leaf`) does not have `hbdd6` from `EpsRegP`;
if this probe confirms `hbdd6` is needed, the lead decides whether to add it to `EpsRegP` (then
re-prove `EpsRegP.mono`, `RegGlueP`, `Reduction.exists_sol_of_localStep_apriori`, `EpsMemRegP`,
`EpsUniformMem_of_parts3`; `LocalStep3` must output it).
Route: L²-Fréchet differentiability of `τ ↦ D^a g(τ)` from `g(τ+h) − g(τ) = ∫ P₀JX`; continuity of
`s ↦ P₀JX(s)` into weighted L² from the `J` gain, `EpsRHSPLipXProof`, `EpsSlotLipP` and `hbdd6`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)
open Work.FTS.StrongEps

set_option autoImplicit false


end Work.FTS.StrongEps.EpsE4Thr.E4R4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.RawE6Ineq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/RawE6Ineq.lean` — OPEN LEAF L-A (research-low given S1–S5, F6)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 L-A; REVIEW fix F1).
The raw energy inequality with an `ε`-small superlinear defect.  Write `X = epsWP`, `x = P₀Jg`,
`e = rawE6`:
`IP6(P₀JX, g) = IP6(X, x) + c(Jg)·IP6(X, bump) − c_X·IP6(bump, g) + O(ε|X|₆|g|₆)`;
with S2 and `HkSq_Jeps_step_le` the defect is `≤ C|g|₆² + Cε(1+e)^{3/2}`;
`IP6(X, x) ≤ CL·Sq6 x + |H6Pair|` (`H6Aux.H6Lin_IP6`, one-sided, + `H6Pair`).
`IP6_lo_coeffs` needs only `HQo 6`, so the raw slices qualify.  Inputs: S1 `Jeps_IP6_transfer`,
S2 `epsWP_semitame`, S3 `Jeps_gain_quant`, S5 `L6Ctx_JfamP`, F6 `rawSlice_L12_zero`,
`IP6_cs/lo_coeffs`, `hkNorm_Pz_le`, `HkSq_Jeps_sub_le`, `HkSq_JfamP_le`, `Pz_l12`.

The pairing estimate is the PROVED `StrongPersist.H6Pair_ones3` (REVIEW F1 — NOT the duplicate
node `H6Pair6`): `rawE6_ineq_ones3` below instantiates it (needs `0 < Ce`, from `core1_1a3`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false



end Work.FTS.StrongEps.EpsE4Thr.E4R4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.RawSliceL12Zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/RawSliceL12Zero.lean` — OPEN SUB-LEAF of L-A (REVIEW fix F6)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling_REVIEW.md` F6).  The raw slice's zero mode
vanishes along a regular ε-solution; L-A (`rawE6_ineq`) needs it for `|c(Jg)| ≲ ε|g|₅`.
Route: `StrongEps.L12_slice_eq_zero_of_hkMem` (PROVED; needs `hc1` = `hreg.1`, `SmoothOpen`/
`HkMem 4` of slices from `hreg.2`, a uniform `ℋ⁴` bound `B` of `epsRHSP` and `HkMem 4` of
`J_ε epsWP`) with `h0 := l12_zero_of_epsDatum hα hρ hd`.  The uniform `B` is the same regularity
issue as R2 (`rawE6_deriv`): if it cannot be produced from `EpsRegP`, return "missing hypothesis".
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps

set_option autoImplicit false


end Work.FTS.StrongEps.EpsE4Thr.E4R4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.FakeTimeSlots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/FakeTimeSlots.lean` — fake-time (`τ`-)regularity of the `ε`-scheme's
# families, by induction on the slot order

The level-four (and level-six) a-priori machinery consumes the *joint* regularity of the slots
`mixed a b (slice g τ)` and `mixed a b (epsRHSP α ρ ε Φs E g τ)` in `(τ, z, θ)`.  The tree carries
the strong form of that regularity (`ContDiffOn ℝ n … (Icc 0 T ×ˢ Quad)`) as an *interface
hypothesis* (`DiagCurveISolution`, items (I)–(IV)), and the hypotheses of the a-priori chapter
(`EpsRegP` = joint `C¹` on the open quadrant plus per-slice `EpsDatumP`, `IsEpsSolP` = the
pointwise ODE, and `Xn6 ≤ M`) do not yield it directly — see
`NOTES_fourthChapterB_leaf_proof.md` §3–§5.

This file starts the *honest* producer of that regularity, by induction on the slot order `n`:

* **order 0 (`n = 0`, this file).**  `EpsRegP` gives joint continuity of the flow on the open
  slab (`continuousOn_slice_fam_reorder`), and the mollifier preserves it
  (`JepsJoint.Jeps_fam_continuous` — continuity of `g` is the *only* input).  Hence the mollified
  family, and (with the `L₁₂`-zero-mode scalar's continuity, isolated as the interface
  `hL12` below) its projection `Pz`, are jointly continuous.
* **order `n → n + 1` (next).**  From the ODE's integral form
  `slice g τ = slice g σ + ∫_σ^τ epsRHSP … u du` the order-`(n+1)` slots of the flow are the
  τ-primitives of the order-`(n+1)` slots of the right-hand side; exchanging `∂_z`, `∂_θ` with the
  τ-integral is Clairaut plus the parametric-derivative lemma, whose inputs are exactly the joint
  continuity of the order-`(n+1)` right-hand-side slots (the induction hypothesis at the next
  order) and a τ-uniform domination.  The right-hand-side slots themselves are *finite smooth
  combinations* of the flow's slots (through `dynLin`, `dynRHS`, the mollifier and the projection),
  so the step is `flow ≤ n ⟹ RHS ≤ n` for the orders the operators do not raise, and the two
  chains interleave.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false



/-- the slab of the fake-time chain. -/
abbrev slab (T : ℝ) : Set (ℝ × (ℝ × ℝ)) := Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad





end Work.FTS.StrongEps.E4R3.Apriori4Proofs
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Jeps_IP6_transfer_proof =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs


end Work.FTS.StrongEps.E4R3.Apriori4Proofs
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.theta_part_jets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

theorem theta_part_jets {a C₀ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S →
      Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ, 0 ≤ τ → ∃ C : ℝ, 0 < C ∧
      (∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter k (fun z _ => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z) z 0| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp a)
          (Work.Construction.Theta (Work.FTS.Regularity.pExp a)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ)) z θ
          / Real.sin (2 * θ)) z θ| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (fun z θ => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z
          * Work.Construction.c2m θ) z θ| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.Construction.Vop (Work.Construction.Theta
          (Work.FTS.Regularity.pExp a) (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ)))
          z θ| ≤ C) := by
  intro τ hτ
  obtain ⟨CL, hCL0, hL12jet, hFKjet, hL12diff, hFKdiff, hL12d⟩ :=
    theta_part_l12 ha ha13 hOK τ hτ
  obtain ⟨Cθ, hCθ0, hc2, hc3, hc4⟩ := theta_part_theta
    (α := Work.FTS.Regularity.pExp a) (Work.FTS.Regularity.pExp_pos ha) hCL0
    hL12jet hFKjet hL12diff hFKdiff hL12d
  refine ⟨max CL Cθ + 1, by
      have h : (0 : ℝ) ≤ max CL Cθ := le_trans hCL0.le (le_max_left _ _)
      linarith, ?_, ?_, ?_, ?_⟩
  · intro k hk z hz
    have h1 := hL12jet k hk z hz
    rw [← Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z) k z 0] at h1
    exact le_trans h1 (by have h : CL ≤ max CL Cθ := le_max_left _ _; linarith)
  · intro j i hji z θ hz hθ0 hθ1
    exact le_trans (hc2 j i hji z θ hz hθ0 hθ1)
      (by have h : Cθ ≤ max CL Cθ := le_max_right _ _; linarith)
  · intro j i hji z θ hz hθ0 hθ1
    exact le_trans (hc3 j i hji z θ hz hθ0 hθ1)
      (by have h : Cθ ≤ max CL Cθ := le_max_right _ _; linarith)
  · intro j i hji z θ hz hθ0 hθ1
    exact le_trans (hc4 j i hji z θ hz hθ0 hθ1)
      (by have h : Cθ ≤ max CL Cθ := le_max_right _ _; linarith)

end Work.FTS_StreamBdry.Inputs
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB4.Thetapart_dz_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB4.Thetapart_dz_bound`

The `Θ`-part of `U(Φ)/sin 2θ` is *radial*: for the singular part
`Θ α F = (1/(4α)) sin 2θ · L₁₂(F)(z)` of the stream function,

`U(Θ α F)(z,θ)/sin 2θ = -(3/(4α)) L₁₂(F)(z) + (1/4) (F,K)_{L²_θ}(z)`

on the open quadrant (this is the second identity of
`Work.FTS_RegExport.RXT.SysAux.Theta_ops`, which needs only the index-raising identity
`z ∂_z L₁₂(F) = -(F,K)_{L²_θ}`).  Hence `D_z` of that quotient is a radial function, and the
target of this file bounds it by `K·z` for `0 < z ≤ 1`.

The ingredients are all available in the workspace:

* `Work.FTS_RegExport.RXT.SysAux.FK_L12_slice_facts` gives, for a slice `F` that is `C⁴` on the
  open quadrant, whose `mixed`-jets of order `≤ 2` are bounded by `B·z^{3/2}/(1+z)²`, and which
  carries `L₁₂(F)(0) = 0`: the pointwise bounds on `(F,K)_{L²_θ}` and on its `D_z`-jet
  (`z·∂_z(F,K)`), the `C²`-regularity of `z ↦ (F,K)_{L²_θ}(z)`, and the derivative identity
  `∂_z L₁₂(F) = -(F,K)/z`;
* the two analytic inputs are `Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved` (the jet
  bounds at rate `z^{3/2}/(1+z)²`, from `LimApprox`) and
  `Work.FTS_RegExport.RXB.l12_zero_lim_proved` (`L₁₂(slice g τ)(0) = 0`), both from the
  `DynOK'` hypothesis; the `C⁴`-regularity of the slice comes from `RegPkgMin.c4`, i.e. from the
  `DynOK` half of `DynOK'`.
-/

noncomputable section

open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB4

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The `Θ`-part of `U(Φ)/sin 2θ` is radial and `O(z)` near `z = 0`.**

For a slice `F` that is `C⁴` on the open quadrant, whose `mixed`-jets of order `≤ 2` decay like
`z^{3/2}/(1+z)²` and which carries `L₁₂(F)(0) = 0`, the `D_z`-derivative of the quotient
`U(Θ α F)/sin 2θ` is `O(z)` on `0 < z ≤ 1` (uniformly in `θ ∈ (0,π/2)`). -/
lemma thetapart_dz_aux {α B : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ}
    (hCd : ContDiffOn ℝ 4 (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    (hb : ∀ b c : ℕ, c + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b c F z θ| ≤ B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    (hL12zero : Work.Construction.L12 F 0 = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.Dz (fun z θ => Work.Construction.Uop α (Work.Construction.Theta α F) z θ
        / Work.Construction.s2 θ) z θ| ≤ K * z := by
  obtain ⟨C, hCpos, hFKj, -, hFKcont, -, hL12d⟩ :=
    Work.FTS_RegExport.RXT.SysAux.FK_L12_slice_facts (B := B) hCd hb hL12zero
  -- the index-raising identity in the form consumed by `Theta_ops`
  have hL12d' : ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => Work.Construction.L12 F z') z = -Work.Construction.FK F z := by
    intro z hz
    rw [(hL12d z hz).deriv]
    field_simp
  -- the closed form of `U(Θ α F)`
  have hOps : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Construction.Uop α (Work.Construction.Theta α F) z θ
        = (1 / 2) * (-(3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z
            + (1 / 2) * Real.sin (2 * θ) * Work.Construction.FK F z) := by
    intro z θ hz hθ hθ2
    have h := (Work.FTS_RegExport.RXT.SysAux.Theta_ops (αG := α) hα hL12d'
      z θ hz hθ hθ2).2.1
    rw [← h]
    ring
  -- the radial function `W = U(Θ α F)/sin 2θ`
  set W : ℝ → ℝ := fun z => -(3 / (4 * α)) * Work.Construction.L12 F z
    + (1 / 4) * Work.Construction.FK F z with hWdef
  have hW_eq : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Uop α (Work.Construction.Theta α F) z θ / Work.Construction.s2 θ
        = W z := by
    intro z θ hzθ
    obtain ⟨hz, hθ0, hθ2⟩ := mem_Qd.mp hzθ
    have hs2 : Work.Construction.s2 θ ≠ 0 := ne_of_gt (s2_pos_of_Qd hzθ)
    rw [hOps z θ hz hθ0 hθ2, hWdef]
    simp only [Work.Construction.s2_eq] at hs2 ⊢
    field_simp
    ring
  refine ⟨(3 / (4 * α)) * C + C / 4, by positivity, ?_⟩
  intro z θ hzθ hz1
  obtain ⟨hz, hθ0, hθ2⟩ := mem_Qd.mp hzθ
  -- unfold `D_z` and `pz`
  rw [Work.Spaces.Dz, Work.Spaces.pz]
  -- the `z`-slice of the quotient agrees with `W` on a neighbourhood of `z`
  have heq : (fun z' : ℝ => Work.Construction.Uop α (Work.Construction.Theta α F) z' θ
        / Work.Construction.s2 θ) =ᶠ[𝓝 z] W := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact hW_eq z' θ (mem_Qd.mpr ⟨hz', hθ0, hθ2⟩)
  rw [Filter.EventuallyEq.deriv_eq heq]
  -- the derivative of `W`, via `HasDerivAt`
  have hFKdiff : DifferentiableOn ℝ (fun z' : ℝ => Work.Construction.FK F z') (Set.Ioi 0) :=
    hFKcont.differentiableOn (by norm_num)
  have hFKdiffAt : DifferentiableAt ℝ (fun z' : ℝ => Work.Construction.FK F z') z :=
    hFKdiff.differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hWh : HasDerivAt W
      (-(3 / (4 * α)) * (-(Work.Construction.FK F z) / z)
        + (1 / 4) * deriv (fun z' : ℝ => Work.Construction.FK F z') z) z := by
    rw [hWdef]
    exact ((hL12d z hz).const_mul (-(3 / (4 * α)))).add
      (hFKdiffAt.hasDerivAt.const_mul (1 / 4))
  have hWderiv : deriv W z
      = -(3 / (4 * α)) * (-(Work.Construction.FK F z) / z)
        + (1 / 4) * deriv (fun z' : ℝ => Work.Construction.FK F z') z := hWh.deriv
  rw [hWderiv]
  -- the two pieces: the `L₁₂`-derivative is `-(F,K)/z`, and `z·∂_z(F,K)` is the `D_z`-jet
  have hpiece1 : z * (-(3 / (4 * α)) * (-(Work.Construction.FK F z) / z))
      = (3 / (4 * α)) * Work.Construction.FK F z := by
    first | (field_simp; ring) | field_simp | ring
  have hpiece2 : z * ((1 / 4) * deriv (fun z' : ℝ => Work.Construction.FK F z') z)
      = (1 / 4) * Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK F z) z 0 := by
    show z * ((1 / 4) * deriv (fun z' : ℝ => Work.Construction.FK F z') z)
      = (1 / 4) * (z * deriv (fun z' : ℝ => Work.Construction.FK F z') z)
    ring
  rw [mul_add, hpiece1, hpiece2]
  -- bounds on the two pieces
  have h1 : |Work.Construction.FK F z| ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    simpa only [Work.Spaces.DzIter_zero] using hFKj 0 (by norm_num) z hz
  have h2 : |Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK F z) z 0|
      ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := hFKj 1 (by norm_num) z hz
  have hcoef1 : 0 ≤ 3 / (4 * α) := by positivity
  have hcoef2 : 0 ≤ (1 : ℝ) / 4 := by norm_num
  -- `z^{3/2}/(1+z)² ≤ z` for `0 < z ≤ 1`
  have hwt_le : z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ z := by
    have h := Work.FTS_RegExport.RXT.SysAux.L12Wt_div_le_one hz
    rw [Work.FTS_RegExport.RXT.SysAux.L12Wt, div_le_iff₀ hz] at h
    simpa using h
  have hKnn : 0 ≤ (3 / (4 * α)) * C + C / 4 := by positivity
  calc |(3 / (4 * α)) * Work.Construction.FK F z
          + (1 / 4) * Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK F z) z 0|
      ≤ |(3 / (4 * α)) * Work.Construction.FK F z|
          + |(1 / 4) * Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK F z) z 0| :=
        abs_add_le _ _
    _ = (3 / (4 * α)) * |Work.Construction.FK F z|
          + (1 / 4) * |Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK F z) z 0| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hcoef1, abs_of_nonneg hcoef2]
    _ ≤ (3 / (4 * α)) * (C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
          + (1 / 4) * (C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hcoef1)
          (mul_le_mul_of_nonneg_left h2 hcoef2)
    _ = ((3 / (4 * α)) * C + C / 4) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by ring
    _ ≤ ((3 / (4 * α)) * C + C / 4) * z := mul_le_mul_of_nonneg_left hwt_le hKnn

theorem Thetapart_dz_bound {a C₀ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.Dz (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp a)
        (Work.Construction.Theta (Work.FTS.Regularity.pExp a) (Work.FTS.Galerkin.slice g τ)) z θ
          / Work.Construction.s2 θ) z θ| ≤ K * z := by
  intro τ hτ
  have hα : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have hα1 : Work.FTS.Regularity.pExp a ≤ 1 := Work.FTS.Regularity.pExp_le_one ha13
  have hregMin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp a) g :=
    Work.FTS.Final.DynOK.regPkgMin hOK.1
  -- the jet bounds at the weight `z^{3/2}/(1+z)²` on a horizon containing `τ`
  obtain ⟨B, -, hB⟩ :=
    lim_mixed_plainE hα hα1 hOK.2 (τ + 1) (by linarith)
  refine thetapart_dz_aux (α := Work.FTS.Regularity.pExp a) (B := B)
    (F := Work.FTS.Galerkin.slice g τ) hα ?_ ?_ ?_
  · exact hregMin.c4 τ hτ
  · intro b c hbc z θ hz hθ0 hθ2
    exact hB τ ⟨hτ, by linarith⟩ b c hbc z θ hz hθ0 hθ2
  · exact l12_zero_plainE hα hOK.2 τ hτ

end Work.FTS_StreamBdry.SB4
end
end
