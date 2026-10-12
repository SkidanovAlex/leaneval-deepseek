import ChallengeDeps
import Submission.Work.BoseFixB1.slidingB_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.slidingBC_holds` — FS `eq:BSsliding2` (Bratteli–Solovej Thm 3.10)

**The target** `Work.BoseFixB1.slidingBC_holds` is, verbatim, FS `final_v2.tex`
`eq:BSsliding2` at FS's own parameters in the frozen vocabulary of
`Submission/Work/BoseFixB1/Defs.lean`:

    `(b/(2ℓ²))·cnPlus ℓ Φ + (1/C)·∫_u sbWord h μ u Φ ≤ wordB v h μ n Φ`

with `sbWord = sbKin + sbPot`, `sbKin = Work.UBBInputs8.tBwordBInd` (FS `eq:appTB`
with FS's own box indicator `Q_{B(u)} = 1_{B(u)} − P_{B(u)}`), `sbPot = qLHSwordB`
(FS `eq:HBU`), the sliding cutoff `c_sb = (dsℓ)⁻¹` and the anchored cutoffs
`(2sℓ)⁻¹`, `(2dsℓ)⁻¹` (FS `eq:T'u`).  FS cite it from Bratteli–Solovej Thm 3.10;
the corpus records it as the a-priori chapter's one open analytic input.

## Reduction (all machine-checked in `Submission/Work/BoseFixB1/`)

The chapter's `slidingB_holds.lean` isolates the two halves of (★) and proves the
bookkeeping:

* `Work.BoseFixB1.KineticHalf v h` — FS `eq:BSsliding2`'s kinetic content (the
  sliding small-box words + the `(b/2ℓ²)cnPlus` gap dominated by the anchored
  large-box word `kinFormB`), **with** the `u`-marginal integrability of `sbKin`;
* `Work.BoseFixB1.PotentialHalf v h` — FS `lem:LocPotential` at FS's parameters,
  **proved** here (`Work.BoseFixB1.potentialHalf_holds`, from the delegated
  `Work.BoseFixB1.sbPot_integral_le_potWordU`);
* `Work.BoseFixB1.slidingB_of_kineticHalf : KineticHalf v h → SlidingB v h` —
  **proved** (with the constant forced to `C = 1`: at the constant one-particle
  state both sides of the kinetic half vanish and the two sides of (★) read
  `(1/C)·(−μ8π(a v)ℓ³) ≤ −μ8π(a v)ℓ³`).

So the *whole* remaining content of the target is `KineticHalf v h`.  **It is proved**: the
inequality is `Work.BoseFixB1.kineticHalf_of_oneBody` (the `N`-body ⟸ `N = 1` slot reduction,
`kineticHalf_of_oneBody.lean`) applied to the `N = 1` inequality
`Work.BoseFixB1.oneBodyKineticHalf_core` (`Core/oneBody_assembly.lean`), and the `u`-marginal
integrability is `Work.BoseFixB1.integrable_sbKin_all` below (from the proved
`Work.BoseFixB1.integrable_sbKin_marginal`).  This file is therefore `sorry`-free.

## The kinetic half's content (the `N = 1` ledger, all proved)

The `N = 1` inequality is the anchored-mean / `symA` route of
`Core/SKELETON_oneBody_assembly.lean`'s design note; at `N = 1` both words collapse to explicit
Fourier integrals by proved bridges and the ledger reads, with `ℓ = sideAt μ (a v)`,
`d = (paramsAt μ (a v)).d`, `s = (paramsAt μ (a v)).s`, `ε_T = (paramsAt μ (a v)).eT`,
`b = (paramsAt μ (a v)).b`, `c_sb = sbCut μ (a v) = (dsℓ)⁻¹`, `ψ = slotFun1 φ`,
`M = ℓ⁻³∫_{acube ℓ}ψ`, `E = ∫_{acube ℓ}(ψ − M)²`, `F = fsKinCoeff c_sb`:

    (b/2ℓ²)·cnPlus ℓ φ + ∫_u sbKin
      = (b/2ℓ²)·E + ∫_u (tbGapCoeff (ℓd) ε_T·cnPlusBoxInd) + ∫_u tBwordKinInd
        [definitions; `cnPlus ℓ φ = E`]
      ≤ (b/2ℓ²)·E + neuWord + (2π)⁻³∫_u bsW F (χ_{B(u)}(ψ − m_u)) + (b/8ℓ²)·E
        [`cnPlusBoxInd_integral_u_le_neuFrac`; `integral_tBwordKinInd_eq_bsW`;
         `Core.meanMismatch_le` — the crux, which converts the sliding mean `m_u` into `M`]
      ≤ (b/2ℓ²)·E + neuWord + mainWord + (b/8ℓ²)·E + (b/8ℓ²)·E
        [`Core.spectral_chain` (the two-cut `symA` comparison at scale `dℓ`, via
         `Core.symA_fsKinCoeff_mix_scaled`) and `Core.pnorm_payment`]
      ≤ neuWord + gapWord + momWord + mainWord      [`gapWord = bℓ⁻²E = 2·(b/2ℓ²)E`,
                                                    `momWord ≥ 0`, `b/2 + b/8 + b/8 ≤ b`]
      = kinFormB 1 ℓ d s ε_T b φ.                   [`kinFormBOne_eq_fsT`, `fsT`]

The two superscripts of FS's own proof are used exactly where FS uses them: the far region's gain
is the cutoff surplus `2(c_sb − c_big)‖q‖` inside `symA_fsKinCoeff_mix`'s three-region estimate,
and the low region's profile tail is `Core.symA_zero_decay_pow` (exponent 16, from
`Work.BoseKinLoc.Tprime.profHat_decay_twelve`), which is also what makes the constant
`(symA 1 (fsKinCoeff (1/(2s))) 0)/(dℓ)²` payable by `b/(8ℓ²)`.  No numerical bound on the bump is
needed: every threshold is an explicit function of the bump's data.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The `u`-marginal integrability conjunct of `KineticHalf`, proved.**

The sliding kinetic word `sbKin` depends on `v` only through the *scalars*
`a v`, `sideAt μ (a v)`, `paramsAt μ (a v)` (its `M` slot is ignored), and is supported in the
bounded `u`-region where the sliding box `dlBox ℓ d u` is non-empty, where it is uniformly
bounded (`Work.BSKinetic.slotWord_bounds`); so it is `u`-integrable for every smooth box state
and every admissible `μ` — no hypothesis on `v` beyond `0 < sideAt μ (a v)`, `0 < (paramsAt μ (a v)).d`
(both supplied by `Adm`) is needed.  This is `Work.BoseFixB1.integrable_sbKin_marginal`.

The smallness threshold is taken to be `1`: the integrability is *monotone* in the threshold
(`Adm.mono`), with no diluteness condition, so any positive `ε₀` works. -/
theorem integrable_sbKin_all {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v))),
        MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
          sbKin (v := v) μ (paramsAt μ (_root_.BoseGases.a v)).M u (Φ : X n → ℝ)) :=
  ⟨1, one_pos, fun μ hAdm n Φ =>
    integrable_sbKin_marginal (adm_ell_pos hAdm) (adm_d_pos hAdm) Φ⟩

/-- **The kinetic half of FS `eq:BSsliding2` from its one-body instance.**

`Work.BoseFixB1.kineticHalf_of_oneBody` (proved, in `kineticHalf_of_oneBody.lean`) reduces the
`N`-body kinetic inequality to its `N = 1` (fibre) instances, the slot bookkeeping being
`Work.BSKinetic.tBwordBInd_slotSwap_nosupp` + `kinFormB_succ_eq_slotSum` +
`Work.BSKinetic.cnPlus_eq_slotSum`; the integrability conjunct is the proved
`integrable_sbKin_all` above.  The remaining input is the `N = 1` inequality at FS's parameters
(FS `eq:BSsliding2`'s kinetic core), proved in
`Submission/Work/BoseFixB1/Core/oneBody_assembly.lean` as
`Work.BoseFixB1.oneBodyKineticHalf_core` (assembling `Core.meanMismatch_le`,
`Core.spectral_chain`, `Core.pnorm_payment`, `BoseFixB1P.integral_tBwordKinInd_eq_bsW`,
`BoseFixB1P.cnPlusBoxInd_integral_u_le_neuFrac`, `kinFormBOne_eq_fsT`, `momWord_nonneg`). -/
theorem kineticHalf_of_oneBodyKineticHalf {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) : KineticHalf v h :=
  kineticHalf_of_oneBody h (oneBodyKineticHalf_core h) (integrable_sbKin_all h)

/-- **The target, reduced to the kinetic half.**  `SlidingB v h` follows from
`KineticHalf v h` (the chapter's `slidingB_of_kineticHalf`, whose potential half is
the proved `potentialHalf_holds`) — see the module docstring. -/
theorem slidingBC_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseFixB1.SlidingB v h :=
  slidingB_of_kineticHalf hv1 hvrad hR hv_supp hav (kineticHalf_of_oneBodyKineticHalf h)

end Work.BoseFixB1
