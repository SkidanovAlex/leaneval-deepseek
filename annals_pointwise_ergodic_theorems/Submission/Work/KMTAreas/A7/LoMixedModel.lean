/-
# The mixed case `(l₁,l₂) = (0,l₂)` of the §8 model estimate (Area A7)

Target: `Work.KMTAreas.A7.LoMixedModel`, i.e. `Work.KMTAreas.A7.LoMixedModelStatement P p₁ p₂`.

## The mathematical content

For the mixed range `l₁ = 0`, `l₂ ≥ 1` the twisted bilinear multiplier of §6 has arithmetic kernel
`K(j₁,j₂) = ∑_{α₂ ∈ (ℚ/ℤ)_{l₂}} m_Ẑ(0,α₂) e(-j₂α₂)`, which is **independent of `j₁`** because
`(ℚ/ℤ)_0 = diffFreqs ρ 0 = {0}` is a singleton.  Hence (the paper's `form-1` for the mixed case)
the multiplier *factorises exactly* as the product of the two one-variable convolutions

  `Btwist ρ P 0 l₂ m₁ m₂ h k = (cw m₁ * h) · (κ * k)`,
  `κ j = (∑_{α₂ ∈ (ℚ/ℤ)_{l₂}} m_Ẑ(0,α₂) e(-jα₂)) · cw m₂ j`   (`loMixedGKer`),

and `κ` is the average over the residues of the arithmetic characters (`loMixedGKer_eq_fiberAvg`).
With the variational product rule, Hölder in `x` and Minkowski in `t`, the estimate for
`loMixedTuple` reduces to the two *linear factor* estimates `MixedFSideEstimate` (paper `(lin-1)` at
arithmetic height `0`) and `MixedGSideEstimate` (paper `(lin-2)`/sampling, the fibre average over the
residues).

## Contents and status

* the shared vocabulary lives in the **base module `Work.KMTAreas.A7.LoMixedBase`** (it is imported
  both here and by the `g`-side cluster `A7/MixedGSideAux.lean` + `A7MixedG/` + `A7G/` + `A7LV/`,
  which imports *this* file's definitions — so the definitions had to move out to `LoMixedBase` to
  break the import cycle);
* **`loMixedModel_of_inputs`** — PROVED (axiom-clean): the whole reduction
  `MixedFSideEstimate P p₁ → MixedGSideEstimate P p₂ → LoMixedModelStatement P p₁ p₂`;
* **`loMixedFSide`** — PROVED (axiom-clean): the `f`-side factor estimate;
* **`loMixedGSide`** — the `g`-side factor estimate, closed through the fleet's axiom-clean assembly
  `Work.KMTAreas.A7.MixedGSideHolds_of_pieces` applied to the *twisted* linear input
  `Work.KMTAreas.A7.LinVarGuard` (the paper's `(lin-2)` without the fibre cut) and
  `Work.KMTAreas.A7.LoWireFiberGuard` (the fibre/sampling estimate, axiom-clean);
* **`LoMixedModel`** — the target, from `loMixedModel_of_inputs` and the two factor estimates.

## The single remaining obligation of this file (session 4 update)

`Work.KMTAreas.A7MixedG.LinVarGuard` was routed through the `A7G/` chapter
(`lowpassAlphaTransferG` / `maximalLowpass` / `chainPartLowpass`), which is *not* reducible to one
statement.  It is routed through

* `loMixedLinVarG` — a verbatim copy of the proof of `Work.KMTAreas.A7Hi.LinVarG`
  (`Submission/Work/KMTAreas/A7Hi/LinVarG.lean`) with its `hLowpass` input replaced by the
  **`A7HiRep` assembly** `Work.KMTAreas.A7Hi.loMixedLowpassVarG`
  (`Submission/Work/KMTAreas/A7/LoMixedLowpass.lean`, sorry-free), which derives the low-pass
  estimate from the **repaired** canonical crux `Work.KMTAreas.A7HiRep.chainPartSqFunPosMemLp`
  through the *verbatim copy* of `Work.KMTAreas.A7Hi.lowpassVarGRepOfChainPartSqFunPos`
  (`Submission/Work/KMTAreas/A7HiRep/assembly.lean`, **axiom-clean**) with the `⊤`/`MemLp` case split
  (see the WARNING below);
* the *proved, axiom-clean* clipped-low-pass bound `A7Hi.lacunaryBumpLowpassClipBoundG` and
  poor-scales bound `A7Hi.lacunaryBumpBadPartBoundG` (`A7Hi/LinVarG.lean`'s own wiring), and the
  *proved, axiom-clean* `A7.gmixedFam_eq_gcl` / `A7MixedG`-free bookkeeping of
  `A7/LinVarGuardWiring.lean`;
* `Work.KMTAreas.A7.LoWireFiberGuard` for the fibre/sampling half.

Consequently **`#print axioms Work.KMTAreas.A7.LoMixedModel` reaches exactly one non-proved
statement**,

  `Work.KMTAreas.A7HiRep.chainPartSqFunPosMemLp`
    (`Submission/Work/KMTAreas/A7HiRep/chainPartSqFunPosMemLp.lean`, `Cρ₀ ≥ 2`)

— the workspace's **repaired registered canonical crux**

  `∃ C > 0, ∀ l₁ m₀, GoodMajorArcs ρ Cρ₀ l₁ (-(m₀:ℤ)) → ∀ f, MemLp f p Measure.count →`
  `  ‖chainPart r (m ↦ lpf ρ l₁ m₀ m f)‖_{ℓᵖ} ≤ C ‖sqFun ρ l₁ m₀ f‖_{ℓᵖ}`

(with `C` independent of `l₁, m₀`, on the good major arcs for a narrowness constant `≥ 2`).  Its own
file records two **proved** sub-cases (`chainPartSqFunSmallHeight` for bounded arithmetic height,
`chainPartZeroHeight` for `l₁ = 0`), the proven JSW pair `eLpNorm_lpf_telescope_le_sqFun` +
`chainPartSqFunPos_of_lFreeLepingle`, and the auxiliary machinery in
`A7HiRep/chainPartSqFunPosAux.lean`; the *sharp* `l₁`-free case is also carried at arbitrary `Cρ₀`
as `A7HiRep.chainPartSqFun` (a *stronger* statement; the file
`Submission/Work/KMTAreas/A7HiRep/chainPartSqFun.lean`).

Everything else in this file's closure is axiom-clean: `#print axioms` of
`loMixedFSide`, `loMixedModel_of_inputs`, `loMixedGSide`, `loMixedLinVarGuard`, `loMixedLinVarG`,
`A7Hi.lowpassVarGRepOfChainPartSqFunPos`, `A7Hi.lacunaryBumpVarEstimate_assemblyG`,
`A7Hi.lacunaryBumpLowpassClipBoundG`, `A7Hi.lacunaryBumpBadPartBoundG`, `A7.gmixedFam_eq_gcl`,
`A7.MixedGSideHolds_of_pieces`, `A7.LoWireFiberGuard` is `[propext, Classical.choice, Quot.sound]`
(checked individually, session 3).

### Why this is the right pin, and what a *weaker* pin would need

* The crux is a *strengthening* of the paper: Krause–Mirek–Tao's `(lin-2)` is the *continuous*
  variational estimate `‖(T_{φ̃_{N,t,j}} G)_N‖_{L^{p₂}(ℝ;V^r)} ≲ max(1,s)^{O(1)}‖G‖_{L^{p₂}(ℝ)}`
  (`papersrc/convergence_of_bilinear_averages.tex`, l. 2556–2578), where the Ionescu--Wainger
  projections enter only through the *single-scale* bound `‖Π_{≤l,≤k}‖_{ℓ^q} ≲ ⟨l⟩` (Lemma
  `iw-prop`, already in the tree as `A7.kmtProj_lp_bound_uniform` / `A7Hi.iwLqBound_narrow_bump`);
  the low-frequency case `j₂ = 0` is then discharged by "Lépingle's inequality and a standard
  square function argument (JSW Thm 1.1 + Lemma 3.2)" for the *continuous* dilated-bump family,
  i.e. by `Work.KMTAreas.A7Hi.DilVar` (PROVED).  What this file needs *in addition* is the same
  statement for the *discrete* IW projections `kmtProj ρ l` — harder, and its proof requires the
  operator-level super-orthogonality of the Ionescu–Wainger multiplier theorem; see
  `NOTES_A7Hi2_SupPieceHolds_SESSION2.md` §3 and `NOTES_A7MixedG_chainGLCrux_SESSION*.md`.
* The loss *class* accepted by `lossWeight c ρ 0 l₂ k₁ k₂ = ⟨L⟩^c 2^{cρL}` (`L ≥ l₂`) is: any
  *polynomial* factor in `l₂, k₁, k₂` times `2^{O(ρ l₂)}`.  So a `⟨l₂⟩^{O(1)}` (polynomial, not
  `l₂`-free) version of the crux would **suffice** for this file (and is what the paper's argument
  gives).  The two *available* lossy routes are however not in this class:
  `#(iwArithFreqs ρ l₂) ≲ 2^{O(l₂2^{ρl₂/2})}` (`A7Hi.eLpNorm_chainPart_le_uniform`) and
  `sieveMass ρ l₂ ≈ 2^{Θ(l₂/ρ)}` (`A7Hi2.eLpNorm_variationalNorm_lpf_le_sieveMass_uncond`).
  The linear-loss ("Rep") route the `A7Hi/` chapter is building for exactly this purpose —
  `A7Hi.chainLeLinRep` (`A7Hi/chainLeLinRep.lean`), `A7Hi.lacunaryMaxPieceLinRep`
  (`A7Hi/lacunaryMaxPieceLinRep.lean`), `A7Hi.lowpassNarrowVarRep`
  (`A7Hi/lowpassNarrowVarRep.lean`, the KMSZ/sampling route) — is the alternative pin; its recorded
  remaining input for the `φ_N` (`d = 1`) family is `A7Hi.lpfLargeScaleRep`, and the
  `d`-scaled (`varphitildeN`) analogue does not exist yet.

### WARNING — the pin is the *repaired* crux; the unrepaired one is `unsafe` (session 4: FIXED)

The statement `A7HiRep.chainPartSqFunPos` quantifies `f : ℤ → ℂ` with **no integrability
hypothesis**, while its right-hand side is `C ‖sqFun ρ l₁ m₀ f‖_{ℓᵖ}` — with no `‖f‖_{ℓᵖ}` (or
`supPart`) term to absorb the pathological case.  The tree itself flags this:
`Submission/Work/KMTAreas/A7HiRep/chainPartSqFunPosMemLp.lean` (its docstring, and
`NOTES_A7HiRep_chainPartSqFunPos_SESSION.md` §S5.6/§S5.7) records that the statement is
"**unsafe**" as written and recommends verbatim "add `MemLp f p Measure.count`"; the *repaired*
canonical crux is `Work.KMTAreas.A7HiRep.chainPartSqFunPosMemLp`, and that is what this file is
now pinned on.

The mechanism (reconstruction, from a walk with increments `≈ 1/m`): take any `f` whose low-pass
walk `m ↦ lpf ρ l₁ m₀ m f` has `sup_m ‖…‖ < ∞`, increments satisfying `Σ_m ‖Δ_m(x)‖² < ∞` (so
`sqFun x < ∞`, whence also `‖sqFun‖_{ℓᵖ} < ∞` on a localized `f`), but `Σ_m ‖Δ_m(x)‖` divergent.
Then the *geometric* chains `N(i) = R^i` give block sums `Γ_i ≈ log R` **constant in `i`**, so
`(Σ_{i<J}|Γ_i|^r)^{1/r} = J^{1/r} log R → ∞` and `chainPart r (walk) (x) = ⊤`: the inequality
`⊤ ≤ C ‖sqFun‖_{ℓᵖ}` fails.  Not formalised; it is the tree's recorded verdict plus this
reconstruction.  (`A7Hi/chainPartNeTopOfMemLp.lean` shows the repaired statement's finiteness
layer: `MemLp` forces `chainPart r < ⊤` whenever `sqFun ∈ ℓᵖ`.)

**How the repair was made usable (session 4).**  `A7HiRep/assembly.lean`'s
`lowpassVarGRepOfChainPartSqFunPos` takes the defective crux as an input, so it cannot be re-pinned
in place.  The new module **`Submission/Work/KMTAreas/A7/LoMixedLowpass.lean`** contains
`Work.KMTAreas.A7Hi.loMixedLowpassVarG`, a *verbatim copy* of that proof with

* the input replaced by `A7HiRep.chainPartSqFunPosMemLp`, and
* the dichotomy `eLpNorm f p Measure.count = ⊤` / `MemLp f p Measure.count` inserted where the crux
  is invoked — harmless because the low-pass estimate's right-hand side carries `eLpNorm f p count`
  as a factor, so the `⊤` branch is exactly `le_top`.

This file's `loMixedLinVarG` now cites `loMixedLowpassVarG`.  (`chainPartSqFunPosMemLp.lean` *does*
build in the current workspace — the session-3 memory-cap obstruction is gone; it is replayed in
~13 s.)

A second, independent obstruction worth recording: `A7Hi.lowpassVarGRepOfChainPartSqFunPos` and
`A7Hi2.lowpassVarG_of_pieces` fix the low-pass loss to exactly `C(1+l₂)²`, so a merely
*poly-lossy* (`⟨l₂⟩^{O(1)}`) route to the low-pass estimate — which is all
`LoMixedModelStatement` accepts, and all the paper proves — does **not** plug into
`A7Hi.lacunaryBumpVarEstimate_assemblyG` as it stands; the linear-loss ("Rep") pieces
`A7Hi.chainLeLinRep` / `A7Hi.lacunaryMaxPieceLinRep` / `A7Hi.lowpassNarrowVarRep` would need a
parallel copy of the assembly (`A7Hi/Gassembly.lean`, ~640 lines of proof, out of bounds for an
in-place edit only because the file is not mine).  (As of session 4 `A7Hi.lowpassNarrowVarRep` is
itself still tainted — its remaining input is the KMSZ/MSW large-scale sampling bound
`A7Hi.lpfLargeScaleRep`, whose module does **not** build in the current workspace: it imports
`Work.KMTPlan.A6.Decim.Defs`, which has no `.olean`.)

See `NOTES_A7_LoMixedModel_SESSION2.md` and `NOTES_A7_LoMixedModel_SESSION3.md` for the routes, the
referee remarks and the traps.

See `NOTES_A7_LoMixedModel_SESSION2.md` and `NOTES_A7_LoMixedModel_SESSION3.md` for the routes, the
referee remarks and the traps.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.MixedGSideHolds
import Submission.Work.KMTAreas.A7MixedG.LinVarGuard
import Submission.Work.A7MixedG.FiberLargeResidueHolds
import Submission.Work.KMTAreas.A7HiRep.chainPartSqFunPosAux
import Submission.Work.KMTAreas.A7HiRep.chainPartSubAdd
import Submission.Work.KMTAreas.A7MixedG.FiberGuard
import Submission.Port.Aesm

set_option autoImplicit false

set_option maxHeartbeats 4000000



namespace Work.KMTAreas.A7



noncomputable section



open MeasureTheory Polynomial Finset Filter Topology

open scoped ENNReal NNReal BigOperators

open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTContract Work.Analysis.EndVar



local notation "Circ" => Work.Analysis.IonescuWainger.Circle/-! ## Measurability in `t` of the two pieces of the mixed model integrand -/

/-- `Tm ρ 0 (φ_{N,t}) f` is measurable in `t`. -/
theorem measurable_Tm_zero_varphiNt (ρ : ℝ) (N k : ℕ) (f : ℤ → ℂ) (y : ℤ) :
    Measurable (fun t : ℝ => Tm ρ 0 (varphiNt N k t) f y) := by
  have h := measurable_iwConv_varphiNt (diffFreqs ρ 0) N k f y
  simpa only [Tm] using h

/-- **The IW kernel of the `φ̃` symbol depends measurably on the parameter.** -/
theorem measurable_iwKernel_varphitildeNt_local (A : Finset Work.Analysis.IonescuWainger.Circle)
    (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) :
    Measurable (fun t : ℝ =>
      iwKernel (iwSymbolSet A (periodize (varphitildeNt P P.natDegree N k t))) j) := by
  have h := measurable_fourierCoeff_iwSymbolSet A j
    (φ := fun t ξ => varphitildeNt P P.natDegree N k t ξ)
    (measurable_varphitildeNt_uncurry P N k)
  simpa only [iwKernel] using h

/-- `Tm ρ l (φ̃_{N,t}) g` is measurable in `t`. -/
theorem measurable_Tm_varphitildeNt (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ) (g : ℤ → ℂ) (y : ℤ) :
    Measurable (fun t : ℝ => Tm ρ l (varphitildeNt P P.natDegree N k t) g y) := by
  have hfun : (fun t : ℝ => Tm ρ l (varphitildeNt P P.natDegree N k t) g y)
      = fun t : ℝ =>
          ∑' j : ℤ, iwKernel (iwSymbolSet (diffFreqs ρ l)
            (periodize (varphitildeNt P P.natDegree N k t))) j * g (y - j) := by
    funext t
    rw [Tm, iwConv_eq_tsum_mul]
  rw [hfun]
  exact Measurable.tsum (fun j : ℤ =>
    (measurable_iwKernel_varphitildeNt_local (diffFreqs ρ l) P N k j).mul_const _)

/-- `convOp (cw m) (Tm ρ 0 (φ_{N,t}) f)` is measurable in `t`. -/
theorem measurable_convOp_Tm_zero_varphiNt (ρ : ℝ) (m : ℝ → ℂ) (N k : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    Measurable (fun t : ℝ => convOp (cw m) (Tm ρ 0 (varphiNt N k t) f) x) := by
  have hfun : (fun t : ℝ => convOp (cw m) (Tm ρ 0 (varphiNt N k t) f) x)
      = fun t : ℝ => ∑' j : ℤ, cw m j * Tm ρ 0 (varphiNt N k t) f (x - j) := by
    funext t; rw [convOp]
  rw [hfun]
  exact Measurable.tsum (fun j : ℤ =>
    measurable_const.mul (measurable_Tm_zero_varphiNt ρ N k f (x - j)))

/-- `convOp (loMixedGKer ρ P l₂ m₂) (Tm ρ l₂ (φ̃_{N,t}) g)` is measurable in `t`. -/
theorem measurable_convOp_GKer_Tm_varphitildeNt (ρ : ℝ) (P : Polynomial ℤ) (l₂ N k : ℕ)
    (m₂ : ℝ → ℂ) (g : ℤ → ℂ) (x : ℤ) :
    Measurable (fun t : ℝ =>
      convOp (loMixedGKer ρ P l₂ m₂) (Tm ρ l₂ (varphitildeNt P P.natDegree N k t) g) x) := by
  have hfun : (fun t : ℝ =>
        convOp (loMixedGKer ρ P l₂ m₂) (Tm ρ l₂ (varphitildeNt P P.natDegree N k t) g) x)
      = fun t : ℝ => ∑' j : ℤ,
          loMixedGKer ρ P l₂ m₂ j * Tm ρ l₂ (varphitildeNt P P.natDegree N k t) g (x - j) := by
    funext t; rw [convOp]
  rw [hfun]
  exact Measurable.tsum (fun j : ℤ =>
    measurable_const.mul (measurable_Tm_varphitildeNt ρ P l₂ N k g (x - j)))

/-- `Tm` kills the zero sequence. -/
theorem Tm_zero_local (ρ : ℝ) (l : ℕ) (ψ : ℝ → ℂ) : Tm ρ l ψ (0 : ℤ → ℂ) = 0 := by
  funext n
  rw [Tm, iwConv_eq_tsum_mul]
  simp

/-- `smallBtwist` vanishes when its first argument does. -/
theorem smallBtwist_zero_left_apply_local (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (k : ℤ → ℂ) (x : ℤ) : smallBtwist ρ P l₁ l₂ m₁ m₂ (0 : ℤ → ℂ) k x = 0 := by
  simp only [smallBtwist]
  simp

/-- `smallBtwist` vanishes when its second argument does. -/
theorem smallBtwist_zero_right_apply_local (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h : ℤ → ℂ) (x : ℤ) : smallBtwist ρ P l₁ l₂ m₁ m₂ h (0 : ℤ → ℂ) x = 0 := by
  simp only [smallBtwist]
  simp

/-- The mixed model tuple vanishes when `f = 0` (pointwise). -/
theorem loMixedTuple_zero_left_apply_local (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal)
    (g : ℤ → ℂ) (l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    loMixedTuple ρ P C₀ a (0 : ℤ → ℂ) g l₂ k₁ k₂ n x = 0 := by
  rw [loMixedTuple]
  by_cases h : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
  · rw [if_pos h, loMixedOp]
    have h0 : ∀ t : ℝ, smallBtwist ρ P 0 l₂
        (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂))
        (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂))
        (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) (0 : ℤ → ℂ))
        (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x = 0 := by
      intro t
      rw [Tm_zero_local, smallBtwist_zero_left_apply_local]
    rw [intervalIntegral.integral_congr (fun t _ => h0 t)]
    simp
  · rw [if_neg h]

/-- The mixed model tuple vanishes when `g = 0` (pointwise). -/
theorem loMixedTuple_zero_right_apply_local (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal)
    (f : ℤ → ℂ) (l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    loMixedTuple ρ P C₀ a f (0 : ℤ → ℂ) l₂ k₁ k₂ n x = 0 := by
  rw [loMixedTuple]
  by_cases h : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
  · rw [if_pos h, loMixedOp]
    have h0 : ∀ t : ℝ, smallBtwist ρ P 0 l₂
        (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂))
        (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂))
        (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f)
        (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (0 : ℤ → ℂ)) x = 0 := by
      intro t
      rw [Tm_zero_local, smallBtwist_zero_right_apply_local]
    rw [intervalIntegral.integral_congr (fun t _ => h0 t)]
    simp
  · rw [if_neg h]

/-- **The mixed model operator is the `t`-integral of the product of the two factors**: this is
`btwistZero_factor` applied to the integrand of `loMixedOp`. -/
theorem loMixedOp_eq_integral_product (ρ : ℝ) (P : ℤ[X]) (N l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ)
    (x : ℤ) :
    loMixedOp ρ P N l₂ k₁ k₂ f g x
      = ∫ t in (1/2 : ℝ)..1,
          (convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ 0 (varphiNt N k₁ t) f) x)
          * (convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g) x) := by
  rw [loMixedOp]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [convOp]
  exact btwistZero_factor ρ P l₂ _ _ _ _ x

/-- The interval integral of `if c then X t else 0` is `if c then` the integral of `X`. -/
theorem intervalIntegral_ite_const_local (a b : ℝ) (c : Prop) [Decidable c] (X : ℝ → ℂ) :
    (∫ t in a..b, (if c then X t else 0)) = if c then ∫ t in a..b, X t else 0 := by
  by_cases h : c
  · rw [if_pos h]
    exact intervalIntegral.integral_congr (fun t _ => by rw [if_pos h])
  · rw [if_neg h]
    refine (intervalIntegral.integral_congr (fun t _ => by rw [if_neg h])).trans ?_
    simp

/-- The `ℓ^q` norm of the variational norm of the vanishing mixed tuple is zero (first variable). -/
theorem eLpNorm_varnorm_loMixedTuple_zero_left (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal)
    (g : ℤ → ℂ) (l₂ k₁ k₂ : ℕ) (r : NNReal) (hr1 : 1 ≤ r) (q : ENNReal) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => loMixedTuple ρ P C₀ a (0 : ℤ → ℂ) g l₂ k₁ k₂ n x)) q
      MeasureTheory.Measure.count = 0 := by
  have h : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => loMixedTuple ρ P C₀ a (0 : ℤ → ℂ) g l₂ k₁ k₂ n x))
      = (0 : ℤ → ENNReal) := by
    funext x
    rw [show (fun n : ℕ => loMixedTuple ρ P C₀ a (0 : ℤ → ℂ) g l₂ k₁ k₂ n x)
        = fun _ : ℕ => (0 : ℂ) from
        funext (fun n => loMixedTuple_zero_left_apply_local ρ P C₀ a g l₂ k₁ k₂ n x)]
    exact variationalNorm_zero r hr1
  rw [h]
  exact MeasureTheory.eLpNorm_zero

/-- The `ℓ^q` norm of the variational norm of the vanishing mixed tuple is zero (second variable). -/
theorem eLpNorm_varnorm_loMixedTuple_zero_right (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal)
    (f : ℤ → ℂ) (l₂ k₁ k₂ : ℕ) (r : NNReal) (hr1 : 1 ≤ r) (q : ENNReal) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => loMixedTuple ρ P C₀ a f (0 : ℤ → ℂ) l₂ k₁ k₂ n x)) q
      MeasureTheory.Measure.count = 0 := by
  have h : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => loMixedTuple ρ P C₀ a f (0 : ℤ → ℂ) l₂ k₁ k₂ n x))
      = (0 : ℤ → ENNReal) := by
    funext x
    rw [show (fun n : ℕ => loMixedTuple ρ P C₀ a f (0 : ℤ → ℂ) l₂ k₁ k₂ n x)
        = fun _ : ℕ => (0 : ℂ) from
        funext (fun n => loMixedTuple_zero_right_apply_local ρ P C₀ a f l₂ k₁ k₂ n x)]
    exact variationalNorm_zero r hr1
  rw [h]
  exact MeasureTheory.eLpNorm_zero

/-- **The reduction of the mixed §8 estimate to its two factor estimates.** -/
theorem loMixedModel_of_inputs (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤)
    (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hF : MixedFSideEstimate P p₁) (hG : MixedGSideEstimate P p₂) :
    LoMixedModelStatement P p₁ p₂ := by
  classical
  intro C₀ r hC₀ hr
  obtain ⟨cF, hcF, ρF, hρF, hF'⟩ := hF C₀ r hC₀ hr
  obtain ⟨cG, hcG, ρG, hρG, hG'⟩ := hG C₀ r hC₀ hr
  refine ⟨cF + cG, by linarith, min ρF ρG, lt_min hρF hρG, ?_⟩
  intro ρ hρ hρle
  obtain ⟨KF, hKF⟩ := hF' ρ hρ (le_trans hρle (min_le_left _ _))
  obtain ⟨KG, hKG⟩ := hG' ρ hρ (le_trans hρle (min_le_right _ _))
  refine ⟨fun Λ => max 1 (KF Λ * KG Λ), ?_⟩
  intro a Λ l₂ k₁ k₂ f g hΛ ha ha1 hl₂
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hp1' : (1 : ENNReal) ≤ p₁ := le_of_lt hp₁
  have hp2' : (1 : ENNReal) ≤ p₂ := le_of_lt hp₂
  have hq1 : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  -- ## The vanishing cases
  by_cases hf0 : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = 0
  · have hz : f = 0 := by
      have h := (MeasureTheory.eLpNorm_eq_zero_iff (p := p₁)
        (ne_of_gt (lt_trans zero_lt_one hp₁))).mp hf0
      funext x
      simpa using MeasureTheory.Measure.ae_count_iff.mp h x
    rw [hz, eLpNorm_varnorm_loMixedTuple_zero_left ρ P C₀ a g l₂ k₁ k₂ r hr1]
    exact bot_le
  by_cases hg0 : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = 0
  · have hz : g = 0 := by
      have h := (MeasureTheory.eLpNorm_eq_zero_iff (p := p₂)
        (ne_of_gt (lt_trans zero_lt_one hp₂))).mp hg0
      funext x
      simpa using MeasureTheory.Measure.ae_count_iff.mp h x
    rw [hz, eLpNorm_varnorm_loMixedTuple_zero_right ρ P C₀ a f l₂ k₁ k₂ r hr1]
    exact bot_le
  -- ## The infinite cases
  have hK0 : ((max 1 (KF Λ * KG Λ) : NNReal) : ENNReal) ≠ 0 := by
    rw [Ne, ENNReal.coe_eq_zero]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hL0 : ENNReal.ofReal (lossWeight (cF + cG) ρ 0 l₂ k₁ k₂) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact lt_of_lt_of_le zero_lt_one
      (one_le_lossWeight_local (c := cF + cG) (ρ := ρ) (by positivity) hρ.le 0 l₂ k₁ k₂)
  by_cases hfT : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = ⊤
  · have htop : ((max 1 (KF Λ * KG Λ) : NNReal) : ENNReal) *
        ENNReal.ofReal (lossWeight (cF + cG) ρ 0 l₂ k₁ k₂) *
        MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = ⊤ := by
      rw [hfT, mul_assoc, ENNReal.top_mul hg0, ENNReal.mul_top (mul_ne_zero hK0 hL0)]
    rw [htop]
    exact le_top
  by_cases hgT : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = ⊤
  · have htop : ((max 1 (KF Λ * KG Λ) : NNReal) : ENNReal) *
        ENNReal.ofReal (lossWeight (cF + cG) ρ 0 l₂ k₁ k₂) *
        MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = ⊤ := by
      rw [hgT, ENNReal.mul_top (mul_ne_zero (mul_ne_zero hK0 hL0) hf0)]
    rw [htop]
    exact le_top
  -- ## The main case
  have hFb : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0))
        p₁ MeasureTheory.Measure.count
        ≤ (KF Λ : ENNReal) * ENNReal.ofReal (lossWeight cF ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count :=
    fun t ht => hKF a Λ l₂ k₁ k₂ t f hΛ ha ha1 hl₂ ht
  have hGb : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x else 0))
        p₂ MeasureTheory.Measure.count
        ≤ (KG Λ : ENNReal) * ENNReal.ofReal (lossWeight cG ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
    fun t ht => hKG a Λ l₂ k₁ k₂ t g hΛ ha ha1 hl₂ ht
  have hCFtop : ((KF Λ : ENNReal) * ENNReal.ofReal (lossWeight cF ρ 0 l₂ k₁ k₂) *
      MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hfT
  have hCGtop : ((KG Λ : ENNReal) * ENNReal.ofReal (lossWeight cG ρ 0 l₂ k₁ k₂) *
      MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hgT
  have hCFreal : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ n : ℕ, ∀ x : ℤ,
      ‖(if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
          convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0 : ℂ)‖
        ≤ ((KF Λ : ENNReal) * ENNReal.ofReal (lossWeight cF ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count).toReal := by
    intro t ht n x
    have h1 : ‖(if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
          convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0 : ℂ)‖ₑ
        ≤ PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ =>
            if loGuard ρ C₀ a 0 l₂ k₁ k₂ m then
              convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ 0 (varphiNt (Nat.floor (a m)) k₁ t) f) x else 0) :=
      enorm_apply_le_variationalNorm (r := r)
        (fun m : ℕ =>
            if loGuard ρ C₀ a 0 l₂ k₁ k₂ m then
              convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ 0 (varphiNt (Nat.floor (a m)) k₁ t) f) x else 0) n
    have h2 : PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ =>
            if loGuard ρ C₀ a 0 l₂ k₁ k₂ m then
              convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ 0 (varphiNt (Nat.floor (a m)) k₁ t) f) x else 0)
        ≤ (KF Λ : ENNReal) * ENNReal.ofReal (lossWeight cF ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count :=
      le_of_eLpNorm_count_le hp1' (hFb t ht) x
    have h3 : ‖(if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
          convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0 : ℂ)‖ₑ
        ≤ ENNReal.ofReal (((KF Λ : ENNReal) * ENNReal.ofReal (lossWeight cF ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count).toReal) := by
      rw [ENNReal.ofReal_toReal hCFtop]
      exact le_trans h1 h2
    rw [← ofReal_norm] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
  have hCGreal : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ n : ℕ, ∀ x : ℤ,
      ‖(if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
          convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x else 0 : ℂ)‖
        ≤ ((KG Λ : ENNReal) * ENNReal.ofReal (lossWeight cG ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count).toReal := by
    intro t ht n x
    have h1 : ‖(if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
          convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x else 0 : ℂ)‖ₑ
        ≤ PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ =>
            if loGuard ρ C₀ a 0 l₂ k₁ k₂ m then
              convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t) g) x else 0) :=
      enorm_apply_le_variationalNorm (r := r)
        (fun m : ℕ =>
            if loGuard ρ C₀ a 0 l₂ k₁ k₂ m then
              convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t) g) x else 0) n
    have h2 : PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ =>
            if loGuard ρ C₀ a 0 l₂ k₁ k₂ m then
              convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t) g) x else 0)
        ≤ (KG Λ : ENNReal) * ENNReal.ofReal (lossWeight cG ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
      le_of_eLpNorm_count_le hp2' (hGb t ht) x
    have h3 : ‖(if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
          convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x else 0 : ℂ)‖ₑ
        ≤ ENNReal.ofReal (((KG Λ : ENNReal) * ENNReal.ofReal (lossWeight cG ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count).toReal) := by
      rw [ENNReal.ofReal_toReal hCGtop]
      exact le_trans h1 h2
    rw [← ofReal_norm] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
  -- ## Step 1: the pointwise bound by the `t`-integral of the product
  have hInt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)
      ≤ ∫⁻ t in Set.Ioc (1/2 : ℝ) 1,
          (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
              convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0))
          * (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
              convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x else 0)) := by
    intro x
    have hA : (fun n : ℕ => loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)
        = fun n : ℕ => ∫ t in (1/2 : ℝ)..1,
            (if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
              (convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x)
              * (convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x) else 0) := by
      funext n
      rw [loMixedTuple]
      by_cases h : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
      · rw [if_pos h]
        rw [intervalIntegral_ite_const_local (1/2 : ℝ) 1 (loGuard ρ C₀ a 0 l₂ k₁ k₂ n)
          (fun t => (convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x)
            * (convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x)), if_pos h]
        exact loMixedOp_eq_integral_product ρ P (Nat.floor (a n)) l₂ k₁ k₂ f g x
      · rw [if_neg h]
        rw [intervalIntegral_ite_const_local (1/2 : ℝ) 1 (loGuard ρ C₀ a 0 l₂ k₁ k₂ n)
          (fun t => (convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x)
            * (convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x)), if_neg h]
    rw [hA]
    refine (le_of_eq (congrArg (fun fam => PointwiseErgodicTheorems.variationalNorm r fam) (funext (fun n => intervalIntegral.integral_of_le (show (1/2 : ℝ) ≤ 1 by norm_num))))).trans ?_
    refine (variationalNorm_integral_le (r := r) hr1
      (ν := MeasureTheory.volume.restrict (Set.Ioc (1/2 : ℝ) 1))
      (g := fun t n => (if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
          (convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x)
          * (convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x)
        else 0))
      (fun n => by
        refine MeasureTheory.Integrable.of_bound ?_
          ((((KF Λ : ENNReal) * ENNReal.ofReal (lossWeight cF ρ 0 l₂ k₁ k₂) *
              MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count).toReal)
            * (((KG Λ : ENNReal) * ENNReal.ofReal (lossWeight cG ρ 0 l₂ k₁ k₂) *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count).toReal)) ?_
        · have hm : Measurable (fun t : ℝ =>
              if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
                (convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                  (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x)
                * (convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                  (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x)
              else 0) := by
            by_cases h : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
            · rw [show (fun t : ℝ => if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
                    (convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                      (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x)
                    * (convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                      (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x)
                  else 0)
                = fun t : ℝ =>
                    (convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                      (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x)
                    * (convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                      (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x) from
                funext (fun t => by rw [if_pos h])]
              exact (measurable_convOp_Tm_zero_varphiNt ρ
                  (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)) (Nat.floor (a n)) k₁ f x).mul
                (measurable_convOp_GKer_Tm_varphitildeNt ρ P l₂ (Nat.floor (a n)) k₂
                  (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)) g x)
            · rw [show (fun t : ℝ => if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
                    (convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                      (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x)
                    * (convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                      (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x)
                  else 0) = fun _ : ℝ => (0 : ℂ) from funext (fun t => by rw [if_neg h])]
              exact measurable_const
          exact hm.aestronglyMeasurable
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t htI
          have htI' : t ∈ Set.Icc (1/2 : ℝ) 1 := Set.Ioc_subset_Icc_self htI
          by_cases h : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
          · rw [if_pos h, norm_mul]
            have hA' : ‖(convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x : ℂ)‖
                ≤ ((KF Λ : ENNReal) * ENNReal.ofReal (lossWeight cF ρ 0 l₂ k₁ k₂) *
                    MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count).toReal := by
              simpa [h] using hCFreal t htI' n x
            have hB' : ‖(convOp (loMixedGKer ρ P l₂
                (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x : ℂ)‖
                ≤ ((KG Λ : ENNReal) * ENNReal.ofReal (lossWeight cG ρ 0 l₂ k₁ k₂) *
                    MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count).toReal := by
              simpa [h] using hCGreal t htI' n x
            exact mul_le_mul hA' hB' (norm_nonneg _) (by positivity)
          · rw [if_neg h]
            simp only [norm_zero]; positivity)).trans ?_
    refine MeasureTheory.lintegral_mono (fun t => ?_)
    have hcongr : (fun n : ℕ => (if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
          (convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x)
          * (convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x)
        else 0))
        = fun n : ℕ =>
            (if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
              convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0)
            * (if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
              convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x else 0) := by
      funext n
      by_cases h : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
      · rw [if_pos h, if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, if_neg h, mul_zero]
    rw [hcongr]
    exact variationalNorm_mul_le_one r hr1 _ _
  -- ## Step 2: the `eLpNorm` estimate
  have hHold : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
        (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0))
        * (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x else 0)))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ (max 1 (KF Λ * KG Λ) : NNReal) * ENNReal.ofReal (lossWeight (cF + cG) ρ 0 l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    intro t htI
    have htI' : t ∈ Set.Icc (1/2 : ℝ) 1 := Set.Ioc_subset_Icc_self htI
    refine (Commons.MeasureTheory.Function.eLpNorm_mul_le_eLpNorm_mul_eLpNorm
      (p := (p₁⁻¹ + p₂⁻¹)⁻¹) (q := p₁) (r := p₂) (inv_inv _)
      (Measurable.of_discrete.aemeasurable) (Measurable.of_discrete.aemeasurable)).trans ?_
    refine (mul_le_mul' (hFb t htI') (hGb t htI')).trans ?_
    calc ((KF Λ : ENNReal) * ENNReal.ofReal (lossWeight cF ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count)
          * ((KG Λ : ENNReal) * ENNReal.ofReal (lossWeight cG ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
        = ((KF Λ : ENNReal) * (KG Λ : ENNReal)) *
            (ENNReal.ofReal (lossWeight cF ρ 0 l₂ k₁ k₂) *
              ENNReal.ofReal (lossWeight cG ρ 0 l₂ k₁ k₂)) *
            (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by ring
      _ = ((KF Λ : ENNReal) * (KG Λ : ENNReal)) *
            ENNReal.ofReal (lossWeight (cF + cG) ρ 0 l₂ k₁ k₂) *
            (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by
          rw [← ENNReal.ofReal_mul (lossWeight_nonneg_local hcF 0 l₂ k₁ k₂),
            lossWeight_mul_local]
      _ ≤ ((max 1 (KF Λ * KG Λ) : NNReal) : ENNReal) *
            ENNReal.ofReal (lossWeight (cF + cG) ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
          have hmain : ((KF Λ : ENNReal) * (KG Λ : ENNReal)) ≤
              ((max 1 (KF Λ * KG Λ) : NNReal) : ENNReal) :=
            ENNReal.coe_le_coe.mpr (le_max_right _ _)
          calc ((KF Λ : ENNReal) * (KG Λ : ENNReal)) *
                ENNReal.ofReal (lossWeight (cF + cG) ρ 0 l₂ k₁ k₂) *
                (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                  MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
              = (((KF Λ : ENNReal) * (KG Λ : ENNReal)) *
                  ENNReal.ofReal (lossWeight (cF + cG) ρ 0 l₂ k₁ k₂)) *
                (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                  MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := rfl
            _ ≤ (((max 1 (KF Λ * KG Λ) : NNReal) : ENNReal) *
                  ENNReal.ofReal (lossWeight (cF + cG) ρ 0 l₂ k₁ k₂)) *
                (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                  MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :=
                mul_le_mul' (mul_le_mul' hmain le_rfl) le_rfl
            _ = ((max 1 (KF Λ * KG Λ) : NNReal) : ENNReal) *
                  ENNReal.ofReal (lossWeight (cF + cG) ρ 0 l₂ k₁ k₂) *
                  MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                  MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
    (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x))
    (g := fun x : ℤ => ∫⁻ t in Set.Ioc (1/2 : ℝ) 1,
        (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0))
        * (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x else 0)))
    (fun x => hInt x)).trans ?_
  exact eLpNorm_lintegral_le _ hq1 _ _ hHold

/-! ## Elementary pieces -/

/-- At arithmetic height `0` the exact-height multiplier is the `≤ 0` projection. -/
private theorem Tm_zero_eq_Tle_aux (ρ : ℝ) (φ : ℝ → ℂ) (f : ℤ → ℂ) : Tm ρ 0 φ f = Tle ρ 0 φ f := by
  funext x
  rw [Tm, Tle, diffFreqs, if_pos rfl]

/-- **The `f`-side ingredient `2^{k₁} ≤ N` of the main regime.** -/
private theorem two_pow_le_of_mainRegime_aux {ρ : ℝ} (hρ : 0 < ρ) {k₁ k₂ N : ℕ} (hN : 1 ≤ N)
    (h : mainRegime ρ k₁ k₂ N) : 2 ^ k₁ ≤ N := by
  have hlogtan : (logN N).toNat = Nat.log 2 (max N 2) := by
    rw [logN]; exact Int.toNat_natCast _
  have hu : 1 ≤ uScale ρ (max k₁ k₂) := uScale_pos hρ.le _
  have hk2 : k₁ + 2 ≤ (logN N).toNat := by
    have h1 := h.1
    omega
  have hmax4 : 4 ≤ max N 2 := by
    have h3 : 2 ≤ Nat.log 2 (max N 2) := by rw [← hlogtan]; omega
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Nat.log 2 (max N 2) := Nat.pow_le_pow_right (by norm_num) h3
      _ ≤ max N 2 := Nat.pow_log_le_self 2 (by omega)
  have hmaxN : max N 2 = N := by omega
  have hk : k₁ ≤ Nat.log 2 N := by
    have h1 : k₁ ≤ Nat.log 2 (max N 2) := by omega
    rwa [hmaxN] at h1
  calc 2 ^ k₁ ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right (by norm_num) hk
    _ ≤ N := Nat.pow_log_le_self 2 (by omega)

/-- **Minkowski for the `ℝ≥0∞`-valued translation family** (`ℓ^q` Young step of the fixed
kernel convolution). -/
private theorem eLpNorm_tsum_enorm_mul_sub_le_aux {q : ℝ} (hq : 1 ≤ q) (K : ℤ → ℂ) (W : ℤ → ℝ≥0∞) :
    MeasureTheory.eLpNorm (fun x : ℤ => ∑' j : ℤ, ‖K j‖ₑ * W (x - j))
        (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ (∑' j : ℤ, ‖K j‖ₑ) * MeasureTheory.eLpNorm W (ENNReal.ofReal q)
        MeasureTheory.Measure.count := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hmink := Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm
    (μ := MeasureTheory.Measure.count) (p := ENNReal.ofReal q)
    (ENNReal.one_le_ofReal.mpr hq) (f := fun j : ℤ => fun x : ℤ => ‖K j‖ₑ * W (x - j))
    (fun j => (measurable_of_countable (fun x : ℤ => ‖K j‖ₑ * W (x - j))).aemeasurable)
  have hconst : ∀ j : ℤ,
      MeasureTheory.eLpNorm (fun x : ℤ => ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q)
          MeasureTheory.Measure.count
        = ‖K j‖ₑ * MeasureTheory.eLpNorm W (ENNReal.ofReal q) MeasureTheory.Measure.count := by
    intro j
    rw [show MeasureTheory.eLpNorm (fun x : ℤ => ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q)
          MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (fun x : ℤ => ‖K j‖ₑ * W x) (ENNReal.ofReal q)
          MeasureTheory.Measure.count from
        Commons.Analysis.Convolution.eLpNorm_sub_right_ennreal (fun y : ℤ => ‖K j‖ₑ * W y) j hq0]
    exact Commons.Analysis.Convolution.eLpNorm_const_mul_ennreal_of_pos
      (f := W) (measurable_of_countable W).aemeasurable (‖K j‖ₑ) hq0
  refine hmink.trans_eq ?_
  rw [tsum_congr hconst, ENNReal.tsum_mul_right]

/-- **Young inequality for the variational norm of a fixed-kernel convolution family.** -/
private theorem eLpNorm_variationalNorm_convOp_le {r : NNReal} (hr1 : 1 ≤ r)
    (κ : ℤ → ℂ) (hκ : Summable fun j : ℤ => ‖κ j‖) (w : ℕ → ℤ → ℂ) {q : ℝ} (hq : 1 ≤ q) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => convOp κ (w n) x)) (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ (∑' j : ℤ, ‖κ j‖ₑ) * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x))
        (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => convOp κ (w n) x)
      ≤ ∑' j : ℤ, ‖κ j‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n (x - j)) := by
    intro x
    have h := variationalNorm_tsum_conv (r := r) hr1 κ hκ w x
    simp only [convOp] at h ⊢
    refine h.trans ?_
    refine ENNReal.tsum_le_tsum (fun j => ?_)
    rw [show ‖κ j‖ₑ = ENNReal.ofReal ‖κ j‖ from by simp]
  exact (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
      (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => convOp κ (w n) x))
      (g := fun x : ℤ => ∑' j : ℤ, ‖κ j‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n (x - j))) hpt).trans
    (eLpNorm_tsum_enorm_mul_sub_le_aux hq κ
      (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x)))

/-- The `1 + lmaxR` comparison of the loss weight. -/
private theorem one_add_pow_two_le_lossWeight_aux {ρ : ℝ} (hρ : 0 < ρ) (l₂ k₁ k₂ : ℕ) :
    (1 + (k₁ : ℝ)) ^ 2 ≤ lossWeight 2 ρ 0 l₂ k₁ k₂ := by
  rw [lossWeight]
  have hL1 : (k₁ : ℝ) ≤ lmaxR 0 l₂ k₁ k₂ := by
    rw [lmaxR, Work.Analysis.EndVar.lmax]
    push_cast
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hLnn : (0 : ℝ) ≤ lmaxR 0 l₂ k₁ k₂ := by
    rw [lmaxR, Work.Analysis.EndVar.lmax]; positivity
  have hbase : (1 + (k₁ : ℝ)) ≤ 1 + lmaxR 0 l₂ k₁ k₂ := by linarith
  have h1 : (1 + (k₁ : ℝ)) ^ 2 ≤ (1 + lmaxR 0 l₂ k₁ k₂) ^ (2 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1 + (k₁ : ℝ)) hbase
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa [Real.rpow_natCast] using h
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * lmaxR 0 l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num)
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hρ.le) hLnn)
  calc (1 + (k₁ : ℝ)) ^ 2
      ≤ (1 + lmaxR 0 l₂ k₁ k₂) ^ (2 : ℝ) := h1
    _ = (1 + lmaxR 0 l₂ k₁ k₂) ^ (2 : ℝ) * 1 := (mul_one _).symm
    _ ≤ (1 + lmaxR 0 l₂ k₁ k₂) ^ (2 : ℝ) * (2 : ℝ) ^ (2 * ρ * lmaxR 0 l₂ k₁ k₂) :=
        mul_le_mul_of_nonneg_left h2
          (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + lmaxR 0 l₂ k₁ k₂) _)

end

end Work.KMTAreas.A7

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar

noncomputable section


/-- **The `f`-side factor estimate of the mixed range** (`l₁ = 0`), i.e. the paper's `(lin-1)` at
arithmetic height `0` with the bounded window convolution `cw (mStarF u)`, `u = loMixedU ρ P.natDegree
l₂ k₁ k₂`, attached.

`Tm ρ 0 φ f = Tle ρ 0 φ f` (`Tm_zero_eq_Tle_aux`), and the guard `loGuard ρ C₀ a 0 l₂ k₁ k₂` is a
tail in `n` (it is `Work.KMTAreas.A7.core`, whose monotonicity is `core_mono`), with
`mainRegime ρ k₁ k₂ ⌊a n⌋` supplying `2^{k₁} ≤ ⌊a n⌋` (`two_pow_le_of_mainRegime_aux`).  Clipping
the family at the tail (factor `3`, `variationalNorm_prependZeros_le`) and reindexing by the first
admissible scale reduces the estimate to the height-`0` linear lacunary variational estimate
`Work.KMTAreas.A7.LoLinVar`, applied to the lacunary tail `n ↦ a (n + m)`.

The window convolution `convOp (cw (mStarF u))` is a fixed kernel of uniformly bounded `ℓ¹` mass
(`vpc_exists_cw_mStarF_tsum_le`): the Young inequality for the variational norm
(`variationalNorm_tsum_conv`), Minkowski's inequality (`eLpNorm_tsum_enorm_mul_sub_le_aux`) and the
mass bound transfer it to the estimate.  The weight `lossWeight 2 ρ 0 l₂ k₁ k₂` dominates
`(1+k₁)²` (`one_add_pow_two_le_lossWeight_aux`).  `hA1` is not needed. -/
theorem loMixedFSide (P : Polynomial ℤ) (p₁ : ENNReal) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) :
    Work.KMTAreas.A7.MixedFSideEstimate P p₁ := by
  classical
  intro C₀ r hC₀ hr
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hq1 : (1 : ℝ) ≤ p₁.toReal := by
    have h : ((1 : ENNReal)).toReal ≤ p₁.toReal :=
      (ENNReal.toReal_le_toReal (by simp) htp₁.ne).mpr hp₁.le
    simpa using h
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨Ck, hCkpos, hCk⟩ := Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le
  set Ck' : ℝ := max Ck 1 with hCk'def
  have hCk'0 : 0 < Ck' := by rw [hCk'def]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCk'ge : Ck ≤ Ck' := by rw [hCk'def]; exact le_max_left _ _
  set CLO : NNReal → NNReal := fun Λ =>
      if h : 1 < Λ then
        Classical.choose (Work.KMTAreas.A7.LoLinVar ρ hρ hρ1 p₁ hp₁ htp₁ r hr Λ h)
      else 0 with hCLOdef
  have hCLO : ∀ (Λ : NNReal) (hΛ : 1 < Λ), ∀ (a : ℕ → NNReal)
      (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (k : ℕ)
      (hkN : ∀ n, 2 ^ k ≤ Nat.floor (a n)) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
      (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ 0 (varphiNt (Nat.floor (a n)) k t) f x))
        p₁ MeasureTheory.Measure.count
        ≤ (CLO Λ : ENNReal) * ENNReal.ofReal ((1 + (k : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count := by
    intro Λ hΛ
    rw [hCLOdef]
    simp only [dif_pos hΛ]
    exact Classical.choose_spec
      (Work.KMTAreas.A7.LoLinVar ρ hρ hρ1 p₁ hp₁ htp₁ r hr Λ hΛ)
  set KF : NNReal → NNReal := fun Λ => ⟨3 * ((CLO Λ : ℝ) * Ck' + 1),
    mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (CLO Λ).2 hCk'0.le) zero_le_one)⟩ with hKFdef
  have hKFval : ∀ Λ : NNReal,
      (KF Λ : ENNReal) = ENNReal.ofReal (3 * ((CLO Λ : ℝ) * Ck' + 1)) := by
    intro Λ
    rw [hKFdef]
    exact ENNReal.coe_nnreal_eq _
  refine ⟨KF, ?_⟩
  intro a Λ l₂ k₁ k₂ t f hΛ ha ha1 hl₂ ht
  let u : ℕ := loMixedU ρ P.natDegree l₂ k₁ k₂
  let κ : ℤ → ℂ := cw (mStarF u)
  let w : ℕ → ℤ → ℂ := fun n => Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f
  let G : ℕ → Prop := fun n => loGuard ρ C₀ a 0 l₂ k₁ k₂ n
  let E : ℕ → ℤ → ℂ := fun n x => if G n then convOp κ (w n) x else 0
  change MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => E n x)) p₁ MeasureTheory.Measure.count
      ≤ (KF Λ : ENNReal) * ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
  have haMono : Monotone a := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    have h2 : Λ < a (n + 1) / a n := ha n
    have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
    have h3 : a n ≤ Λ * a n := by
      simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
    exact le_trans h3 h1.le
  have hGmono : ∀ n m : ℕ, n ≤ m → G n → G m := by
    intro n m hnm hn
    exact core_mono haMono hnm hn
  have hκsum : Summable (fun j : ℤ => ‖κ j‖) := (hCk u).1
  have hκle : (∑' j : ℤ, ‖κ j‖) ≤ Ck := (hCk u).2
  have hκmass : (∑' j : ℤ, ‖κ j‖ₑ) ≤ ENNReal.ofReal Ck' := by
    have h1 : (∑' j : ℤ, ‖κ j‖ₑ) = ENNReal.ofReal (∑' j : ℤ, ‖κ j‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hκsum]
      exact tsum_congr (fun j => by simp)
    rw [h1]
    exact (ENNReal.ofReal_le_ofReal hκle).trans (ENNReal.ofReal_le_ofReal hCk'ge)
  have hWge := one_add_pow_two_le_lossWeight_aux hρ l₂ k₁ k₂
  have hWpos : 0 < lossWeight 2 ρ 0 l₂ k₁ k₂ := lt_of_lt_of_le (by positivity) hWge
  have harith : 3 * ((∑' j : ℤ, ‖κ j‖ₑ) *
        ((CLO Λ : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2)))
      ≤ (KF Λ : ENNReal) * ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) := by
    rw [hKFval]
    have e1 : (∑' j : ℤ, ‖κ j‖ₑ) ≤ ENNReal.ofReal Ck' := hκmass
    have e2 : (CLO Λ : ENNReal) = ENNReal.ofReal (CLO Λ : ℝ) := ENNReal.coe_nnreal_eq _
    have e3 : ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2)
        ≤ ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) := ENNReal.ofReal_le_ofReal hWge
    have hfold : ENNReal.ofReal (3 * (Ck' * ((CLO Λ : ℝ) * lossWeight 2 ρ 0 l₂ k₁ k₂)))
        = (3 : ENNReal) * (ENNReal.ofReal Ck' *
            (ENNReal.ofReal (CLO Λ : ℝ) * ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂))) := by
      calc ENNReal.ofReal (3 * (Ck' * ((CLO Λ : ℝ) * lossWeight 2 ρ 0 l₂ k₁ k₂)))
          = ENNReal.ofReal 3 * ENNReal.ofReal
              (Ck' * ((CLO Λ : ℝ) * lossWeight 2 ρ 0 l₂ k₁ k₂)) :=
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)
        _ = ENNReal.ofReal 3 * (ENNReal.ofReal Ck' * ENNReal.ofReal
              ((CLO Λ : ℝ) * lossWeight 2 ρ 0 l₂ k₁ k₂)) :=
            congrArg (fun z => ENNReal.ofReal 3 * z) (ENNReal.ofReal_mul hCk'0.le)
        _ = ENNReal.ofReal 3 * (ENNReal.ofReal Ck' * (ENNReal.ofReal (CLO Λ : ℝ) *
              ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂))) :=
            congrArg (fun z => ENNReal.ofReal 3 * (ENNReal.ofReal Ck' * z))
              (ENNReal.ofReal_mul (CLO Λ).2)
        _ = (3 : ENNReal) * (ENNReal.ofReal Ck' * (ENNReal.ofReal (CLO Λ : ℝ) *
              ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂))) :=
            congrArg (fun z => z * (ENNReal.ofReal Ck' * (ENNReal.ofReal (CLO Λ : ℝ) *
              ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂)))) (ENNReal.ofReal_ofNat 3)
    have hfold2 : ENNReal.ofReal ((3 * ((CLO Λ : ℝ) * Ck' + 1)) *
          lossWeight 2 ρ 0 l₂ k₁ k₂)
        = ENNReal.ofReal (3 * ((CLO Λ : ℝ) * Ck' + 1)) *
            ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) := by
      rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 3 * ((CLO Λ : ℝ) * Ck' + 1))]
    calc 3 * ((∑' j : ℤ, ‖κ j‖ₑ) *
          ((CLO Λ : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2)))
        ≤ 3 * (ENNReal.ofReal Ck' * (ENNReal.ofReal (CLO Λ : ℝ) *
            ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂))) := by
          refine mul_le_mul' le_rfl (mul_le_mul' e1 (mul_le_mul' ?_ e3))
          rw [e2]
      _ = ENNReal.ofReal (3 * (Ck' * ((CLO Λ : ℝ) * lossWeight 2 ρ 0 l₂ k₁ k₂))) :=
          hfold.symm
      _ ≤ ENNReal.ofReal (3 * ((CLO Λ : ℝ) * Ck' + 1)) *
            ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) := by
          rw [← hfold2]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (CLO Λ : ℝ) * Ck' * lossWeight 2 ρ 0 l₂ k₁ k₂
              ≤ ((CLO Λ : ℝ) * Ck' + 1) * lossWeight 2 ρ 0 l₂ k₁ k₂ :=
            mul_le_mul_of_nonneg_right (by linarith) hWpos.le
          have h2 : 3 * (Ck' * ((CLO Λ : ℝ) * lossWeight 2 ρ 0 l₂ k₁ k₂))
              = 3 * ((CLO Λ : ℝ) * Ck' * lossWeight 2 ρ 0 l₂ k₁ k₂) := by ring
          have h3 : (3 * ((CLO Λ : ℝ) * Ck' + 1)) * lossWeight 2 ρ 0 l₂ k₁ k₂
              = 3 * (((CLO Λ : ℝ) * Ck' + 1) * lossWeight 2 ρ 0 l₂ k₁ k₂) := by ring
          rw [h2, h3]
          exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  by_cases hne : ∃ n : ℕ, G n
  · set m : ℕ := Nat.find hne with hmdef
    have hmG : G m := Nat.find_spec hne
    have hGhead : ∀ n : ℕ, n < m → ¬ G n := by
      intro n hn hc
      exact Nat.find_min hne hn hc
    have hGtail : ∀ n : ℕ, m ≤ n → G n := fun n hn => hGmono m n hn hmG
    let E' : ℕ → ℤ → ℂ := fun n x => convOp κ (w (n + m)) x
    have hE0 : ∀ n : ℕ, n < m → ∀ x : ℤ, E n x = 0 := by
      intro n hn x
      show (if G n then convOp κ (w n) x else 0) = 0
      rw [if_neg (hGhead n hn)]
    have hEm : ∀ n : ℕ, m ≤ n → ∀ x : ℤ, E n x = E' (n - m) x := by
      intro n hn x
      have hGn : G n := hGtail n hn
      have hsub : n - m + m = n := Nat.sub_add_cancel hn
      show (if G n then convOp κ (w n) x else 0) = convOp κ (w (n - m + m)) x
      rw [if_pos hGn, hsub]
    have hptclip : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => E n x)
        ≤ 3 * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => E' n x) := by
      intro x
      have hfun : (fun n : ℕ => E n x)
          = fun n : ℕ => if n < m then 0 else (fun k : ℕ => E' k x) (n - m) := by
        funext n
        by_cases hn : n < m
        · rw [hE0 n hn x, if_pos hn]
        · have hn' : m ≤ n := le_of_not_gt hn
          rw [if_neg hn]
          exact hEm n hn' x
      rw [hfun]
      exact Submission.PointwiseErgodicTheorems.variationalNorm_prependZeros_le hr1 m
        (fun k : ℕ => E' k x)
    have hstep1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => E n x)) p₁ MeasureTheory.Measure.count
        ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => E' n x)) p₁ MeasureTheory.Measure.count := by
      refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
        (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => E n x))
        (g := fun x : ℤ => (3 : ENNReal) * PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => E' n x)) hptclip).trans ?_
      exact MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm)
        (f := fun x : ℤ => (3 : ENNReal) * PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => E' n x))
        (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => E' n x))
        (c := 3) (Filter.Eventually.of_forall (fun x => by
          rw [enorm_eq_self, enorm_eq_self]
          exact le_rfl)) p₁
    have hstep2 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => E' n x)) p₁ MeasureTheory.Measure.count
        ≤ (∑' j : ℤ, ‖κ j‖ₑ) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w (n + m) x))
          p₁ MeasureTheory.Measure.count := by
      have h := eLpNorm_variationalNorm_convOp_le (r := r) hr1 κ hκsum
        (fun n : ℕ => w (n + m)) (q := p₁.toReal) hq1
      rw [ENNReal.ofReal_toReal htp₁.ne] at h
      exact h
    have hstep3 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => w (n + m) x)) p₁ MeasureTheory.Measure.count
        ≤ (CLO Λ : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count := by
      have hfam : ∀ n : ℕ, w (n + m)
          = Tle ρ 0 (varphiNt (Nat.floor (a (n + m))) k₁ t) f := by
        intro n
        show Tm ρ 0 (varphiNt (Nat.floor (a (n + m))) k₁ t) f
          = Tle ρ 0 (varphiNt (Nat.floor (a (n + m))) k₁ t) f
        exact Tm_zero_eq_Tle_aux ρ _ f
      have hrew : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => w (n + m) x))
          = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Tle ρ 0 (varphiNt (Nat.floor (a (n + m))) k₁ t) f x) := by
        funext x
        exact congrArg (fun (v : ℕ → ℤ → ℂ) =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n x)) (funext hfam)
      rw [hrew]
      refine hCLO Λ hΛ (fun n : ℕ => a (n + m)) ?_ ?_ k₁ ?_ t ht f
      · intro n
        have hh := ha (n + m)
        simpa [Nat.add_right_comm] using hh
      · intro n; exact ha1 (n + m)
      · intro n
        have hfloor1 : 1 ≤ Nat.floor (a (n + m)) :=
          Nat.le_floor (by exact_mod_cast ha1 (n + m))
        exact two_pow_le_of_mainRegime_aux hρ hfloor1
          ((hGtail (n + m) (Nat.le_add_left m n)).2.2)
    have hall : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => E n x)) p₁ MeasureTheory.Measure.count
        ≤ (3 * ((∑' j : ℤ, ‖κ j‖ₑ) *
            ((CLO Λ : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2)))) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count := by
      calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => E n x)) p₁ MeasureTheory.Measure.count
          ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => E' n x)) p₁ MeasureTheory.Measure.count := hstep1
        _ ≤ 3 * ((∑' j : ℤ, ‖κ j‖ₑ) * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w (n + m) x))
            p₁ MeasureTheory.Measure.count) := mul_le_mul' le_rfl hstep2
        _ ≤ 3 * ((∑' j : ℤ, ‖κ j‖ₑ) * ((CLO Λ : ENNReal) *
              ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count)) :=
              mul_le_mul' le_rfl (mul_le_mul' le_rfl hstep3)
        _ = (3 * ((∑' j : ℤ, ‖κ j‖ₑ) *
              ((CLO Λ : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2)))) *
              MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count := by ac_rfl
    exact hall.trans (mul_le_mul' harith le_rfl)
  · have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => E n x)) = 0 := by
      funext x
      have hthis : (fun n : ℕ => E n x) = (0 : ℕ → ℂ) := by
        funext n
        show (if G n then convOp κ (w n) x else 0) = (0 : ℂ)
        rw [if_neg (fun hc => hne ⟨n, hc⟩)]
      have h0 : PointwiseErgodicTheorems.variationalNorm r (0 : ℕ → ℂ) = 0 := by
        have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul
          (r := r) hr1 (0 : ℂ) (0 : ℕ → ℂ)
        simpa using h
      rw [hthis]
      exact h0
    rw [hzero, MeasureTheory.eLpNorm_zero]
    exact zero_le

/-! ## The two factor estimates -/


/-! ## The `g`-side factor, wired onto the canonical crux `A7HiRep.chainPartSqFunPos` -/

/-! ## The target -/

end

end Work.KMTAreas.A7
