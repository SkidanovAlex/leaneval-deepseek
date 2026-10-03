import Mathlib
import Submission.Work.KMTAreas.A7.residueLp_fiberOp_le_of_projection
import Submission.Work.KMTAreas.A7Hi.fourierCoeff_mul_l1
import Submission.Work.KMTAreas.A7Hi.FiberVarReduce
import Submission.Work.KMTAreas.A7.eLpNorm_varNorm_fiberOp_le_of_mass
import Submission.Work.KMTAreas.A7Hi.FiberOpTexFixNarrow
import Submission.Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top
import Submission.Work.KMTAreas.A7Hi.chainPartSqFunOfBandSumSq
import Submission.Work.KMTAreas.A7.tex_hasFreqSupport_of_memlp
import Submission.Work.KMTAreas.A7.fiberVarSamplingLargeLoss_bdd
import Submission.Work.KMTAreas.A7Hi.winRotResidueBoundDec
import Submission.Port.Aesm


/-
# STATUS and REDUCTION (session notes for the next stretch)

## What this file owes
`Work.KMTAreas.A7Hi.FiberVarSampling`, the fibre variational sampling estimate.  It is *not yet
proved*: the statement below is the requested one, unchanged, and the proof is still a `sorry`.
The reduction recorded here is complete (every step below is either already proved in the workspace
or delegated), so the remaining work is assembly plus the two delegated lemmas.

## The reduction (verified against the workspace's assets this session)

Notation: `L := max (max l₁ l₂) (max k₁ k₂)`, `U := uScale ρ L = ⌊2^{2ρL}⌋`,
`m := mStarF U = etaCut kmtEta (-(2U))` (a smooth bump of width `2^{-2U}`, supported in the arc
`realArc (-(2U))`), `q := arithQ ρ (max l₁ l₂)`, `T_{n₀} := fiberOp ρ l₁ (mStarF U) n₀`,
`u_n := Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n = if core … n then Tex ρ l₁ (varphiNt (⌊a n⌋) k₁ t) f else 0`.

* **Step 0 (Tonelli; PROVED in the workspace).**  `residueLp p q A x = (q⁻¹ Σ_{n₀<q} (A x n₀)^p)^{1/p}`
  is an `ℓᵖ`-average in `n₀`, so `eLpNorm (residueLp …) p = (q⁻¹ Σ_{n₀<q} (eLpNorm (A · n₀) p)^p)^{1/p}`
  (`Submission.Work.KMTAreas.A7.fiberVarSamplingCoreG.eLpNorm_residueLp`) and hence it suffices to
  bound `eLpNorm (fun x => variationalNorm r (n ↦ T_{n₀} (u_n) x)) p` *uniformly in* `n₀`
  (`… .eLpNorm_residueLp_le_of_single`).  Both lemmas are sorry-free and are safe to import (their
  proofs do not use the `sorry` of their file's main declaration).

* **Step 1 (pointwise variation ≤ square function; PROVED).**
  `variationalNorm r (n ↦ w_n x) ≤ c (Σ_n ‖w_n x‖²)^{1/2}` for `r ≥ 2`
  (`Submission.Work.KMTAreas.A7.variationalNorm_le_sqSum`).

* **Step 2 (single-scale fibre bound, uniform in the residue; DELEGATED).**
  `Submission.Work.KMTAreas.A7Hi.FiberOpUniformLp` (in flight): under the narrowness hypothesis
  `GoodMajorArcs ρ Cρ l₁ (-(2U))` the fibre is bounded on `ℓᵖ(ℤ)` with norm `C(ρ,p)⟨l₁⟩`, uniformly
  in `n₀`.  Route: `fiberOpP_eq_translate_iwConv` writes the fibre as a translate of the
  Ionescu–Wainger convolution with the symbol `m̃·e(-n₀·)` (`m̃ = periodize m`), which is still
  supported in `realArc (-(2U))`; the exact-height frequency set is a difference of height-`≤ l₁`
  sets, so the IW multiplier theorem (`Work.KMTContract.AreaA1`, proved and clean) applies, the
  continuous multiplier norm of the modulated bump being `O(1)` by Mikhlin.

* **Step 3 (Khintchine/MZ amplification to the square function; DELEGATED).**
  `Submission.Work.KMTAreas.A7Hi.SqSumAmplification` (in flight): a linear `T` bounded on `ℓ^q`
  (`q` even, `q ≥ p ≥ 2`) is bounded on the `ℓ²`-valued space `ℓᵖ(ℓ²)`.  This is the classical
  Khintchine argument of `Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns'`, run with the *fixed*
  operator `T_{n₀}` (uniformly in `n₀`).

* **Step 4 (square function ≤ variation, DELEGATED).**  For the *lacunary* family
  `n ↦ Tex ρ l₁ (varphiNt (⌊a n⌋) k₁ t) f` the square function is controlled by the variational norm
  (classical Littlewood–Paley/`cz-shift` comparison; the paper's §8 uses the same input).  This is
  the only step for which no delegation has been issued yet; the correct statement is
  `‖(Σ_n ‖u_n‖²)^{1/2}‖_{ℓᵖ} ≤ C(Λ) · lossWeight A ρ l₁ l₂ k₁ k₂ · ‖V^r_n(u_•)‖_{ℓᵖ}`
  for the clipped family `u = Hcl …`; it follows from the `Lacunary Λ a` hypothesis
  (the lacunarity constant is exactly what `C(Λ)` absorbs) and the proved continuous-multiplier
  bounds `lacunaryBump_mult_bound_k1pos` / `_k0_diff` for the signed sums of the bump family.

* **Step 5 (arithmetic bookkeeping).**  Two regimes:
  * `GoodMajorArcs ρ Cρ l₁ (-(2U))` holds whenever `2U ≥ Cρ · 2^{ρ l₁}` (i.e. `2ρL ≳ ρl₁`, true as
    `l₁ ≤ L` and `L` large): then Steps 2–4 apply.
  * otherwise `L ≤ B(ρ)` for an explicit `B`, and the crude Young bound
    `fiberOpVarNonFareyBounded` (PROVED, clean) gives the fiber estimate with a `ρ`-dependent
    constant (absorbed by `C(Λ)`, which is chosen after `ρ`), while `lossWeight ≥ 1`.
    (The `ρ`-dependence of `C(Λ)` is legitimate: the quantifiers of the target put
    `∃ C : NNReal → NNReal` *after* `ρ` and `p`.)

* **Step 6 (constants).**  `A := 2` and `C Λ := C(ρ,p,r)·C(Λ)` absorb the `⟨l₁⟩` losses into
  `lossWeight A ρ l₁ l₂ k₁ k₂ = (1+lmaxR)^A 2^{Aρ·lmaxR}`; `ρ₀` is any positive number ≤ 1.

## Traps (read the session notes before changing anything)
* The *uniform-in-`n₀`* operator bound (Step 2) is only claimed with a `ρ`-dependent constant; a
  `ρ`-uniform version is FALSE (`NOTES_A7_fiberVarSampling_SESSION.md` §2(a)), and the residue
  average of Step 0 is what allows the `ρ`-dependent constant to be used.
* `lossWeight A ρ l₁ l₂ k₁ k₂ ≥ 1`, so a bounded multiplicative error is free.
-/


/-
## STATUS UPDATE (later in the same session)

The pieces of the reduction below have been *proved* (sorry-free, axiom-clean, in this directory):

* `Work.KMTAreas.A7Hi.eLpNormResidueLpEq`  — `‖residueLp p q F‖_{ℓᵖ} = (q⁻¹ Σ_{n₀<q} ‖F·n₀‖_{ℓᵖ}^p)^{1/p}`
  (the Tonelli/reduction step; `Work.KMTAreas.A7Hi.residueLpVariationalShift` is the shift form).
* `Work.KMTAreas.A7Hi.LinVar` — the paper's (lin-1)/(lin-2) *absolute* estimate
  `‖V^r_n(Hcl … n)‖_{ℓᵖ} ≤ C(Λ)·lossWeight·‖f‖_{ℓᵖ}` (assembled from `LowpassVar`, `DilVar`,
  `LinVarG`, `LnatBoundOnBad`, `lowpassNarrowVar`, `Work.KMTAreas.A7.lacunaryBump{LowpassClipBoundGen,
  BadPartBound}`, …).
* `Work.KMTAreas.A7Hi.SqSumAmplificationLp` — the Khintchine/MZ square-function amplification from an
  `ℓᵖ` operator bound (`SqSumAmplification` as first requested was FALSE; see
  `SqSumAmplification_counterexample.lean`).
* `Work.KMTAreas.A7Hi.FiberOpUniformLp`, `DilVar`, `LnatBoundOnBad` — the single-scale fibre bound
  (uniform in `n₀`, via the IW multiplier theorem at the exact height) and the bad-scale bounds.

The remaining gaps for the statement below are exactly two:

1. **the rephasing bound** `Work.KMTAreas.A7Hi.fiberOpNarrowBandBound` (stub, in flight): on the
   *range of the cut* `fiberOp ρ l m' 0` (with the bump `m` inside the plateau of `m'` and the arcs
   non-aliasing), the rephasing `fiberOp ρ l m M` is bounded in the `ℓᵖ(ℤ;V^r)` norm by the input's
   variational norm.  This is the discrete shadow of KMT §8 `form-1` (Haar invariance of the adelic
   translation); `fiberOpRephasingUniformBound` is the variant with a kernel-mass parameter.
2. **the range-of-the-cut bookkeeping** — *delegated as* `Work.KMTAreas.A7Hi.FiberOpCutTex`
   (`Submission/Work/KMTAreas/A7Hi/FiberOpCutTex.lean`): `fiberOp ρ l m' 0 (Tex ρ l φ f) = Tex ρ l φ f`
   under (separately named) plateau / support / non-aliasing / circle-side packet-support hypotheses.
   Caveat found in review: the packet condition must be stated *on the circle*
   (`∀ ξ, periodize φ ξ ≠ 0 → ∃ θ, |θ| ≤ δ ∧ (θ : Circle) = ξ`); the naive `∀ θ : ℝ, δ < |θ| → …`
   is 1-periodicity-inconsistent and would force `periodize φ ≡ 0`.  What remains of this item is only
   the instantiation of `δ := 2^{-2u-1}`, `u := uScale ρ L` against `mStarF_plateau`. — `fiberOp ρ l₁ (mStarF (uScale ρ L)) 0 (Hcl … n) = Hcl … n`
   (the plateau/non-aliasing identity for the concrete family; symbol-level input:
   `Work.KMTAreas.A7.aliasingSymbolProduct`, plateau: `Work.KMTAreas.A7.mStarF_plateau`), together
   with the two-regime split (the wide-band regime uses the crude `fiberOpVarNonFareyBounded`, whose
   applicability is certified by `LnatBoundOnBad`).

Once (1) and (2) are available, the assembly is: `eLpNormResidueLpEq` (Step 0) → the per-`n₀`
bound `‖V^r_n(fiberOp ρ l₁ (mStarF U) n₀ (Hcl n))‖_{ℓᵖ} ≤ C(ρ,p)·(1+l₁)·lossWeight·‖V^r(Hcl)‖`
(Step 2 + `fiberOpNarrowBandBound`), with `C(Λ) := C(ρ,p,r)·C` and `A := 2`.
-/

/-
## SESSION 3 (2026-09-28) — THE ROUTE, and what is delegated

**Read `NOTES_A7Hi_FiberVarSampling_ROUTE.md` at the workspace root before touching this file.**
It supersedes the reduction sketched above: the crux is *not* the quantitative Shannon sampling
result and *not* Rubio de Francia.  The fibre of the cut at the residue `n₀`, applied to the
exact-height projection, is (algebraically, no approximation)

  `fiberOp ρ l m n₀ (Tex ρ l φ f) = y ↦ ee (n₀ y) · (Tex ρ l φ f y - E y)`,

where `E` is the Ionescu–Wainger multiplier with the *single* narrow profile
`η ↦ (1 - ee (-n₀ η)) · periodize φ η`.  Hence

  `Vʳ_n(fiberOp … (Hcl … n)) ≤ Vʳ_n(Hcl … n) + Vʳ_n(E)`

(`Vʳ` is subadditive and is invariant under multiplication by the fixed unimodular function
`ee (n₀ ·)`), and `E` is a narrow-symbol IW family applied to a *fixed* input (the projection at
the widest profile, which is an element of the family), so the proved absolute narrow-symbol
variational estimate bounds `Vʳ(E)` by a small multiple of `‖Vʳ(Hcl)‖`.  No `#(ℚ/ℤ)_{l₁}` loss,
no `q`-loss, no sampling result, and the bound holds for every `n₀` separately, so the
`residueLp` average costs nothing.

**Delegated this session**: `Work.KMTAreas.A7Hi.fiberTwistGate`
(`Submission/Work/KMTAreas/A7Hi/fiberTwistGate.lean`) — the algebraic identity above.

**Still to do here**: the assembly (subadditivity + the supremum term of `variationalNorm` + the
narrow-symbol variational estimate + the case split `L ≤ B(ρ)` via the proved
`Work.KMTAreas.A7.fiberOpVarNonFareyBounded` and `L > B(ρ)` via
`Work.KMTAreas.A7.farey_and_strict_of_large_L`), and the `Hcl`/`core` bookkeeping, which can be
copied from `Submission/Work/KMTAreas/A7/fiberVarSampling.lean` (`fiberVarSampling_of_core`).
-/

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-- **Translation invariance of `eLpNorm` for the counting measure of `ℤ`.** -/
theorem eLpNorm_count_sub {p : ENNReal} (hp0 : p ≠ 0) (hpt : p ≠ ∞) (F : ℤ → ENNReal)
    (c : ℤ) :
    eLpNorm (fun y : ℤ => F (y - c)) p Measure.count = eLpNorm F p Measure.count := by
  have key : (fun y : ℤ => F (y + (-c))) = fun y : ℤ => F (y - c) := by
    funext y; rw [sub_eq_add_neg]
  rw [← key]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt]
  have h1 : (∫⁻ y : ℤ, ‖F (y + (-c))‖ₑ ^ p.toReal ∂Measure.count)
      = ∫⁻ y : ℤ, ‖F y‖ₑ ^ p.toReal ∂Measure.count := by
    rw [lintegral_count, lintegral_count]
    simp only [enorm_eq_self]
    exact Equiv.tsum_eq (Equiv.addRight (-c)) (fun z : ℤ => F z ^ p.toReal)
  rw [h1]

/-- `fourier (T := 1) n` is additive in its argument. -/
theorem fourier_add_arg (n : ℤ) (x y : Work.Analysis.IonescuWainger.Circle) :
    fourier (T := 1) n (x + y) = fourier (T := 1) n x * fourier (T := 1) n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- `e(-M·)(-α) = e(M·)(α)` on the circle. -/
theorem fourier_neg_neg' (M : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    fourier (T := 1) (-M) (-α) = fourier (T := 1) M α := by
  rw [fourier_apply, fourier_apply, smul_neg, neg_smul, neg_neg]

/-! ## The fibre as a translated Ionescu--Wainger convolution (copy of the `A7` chapter)

The module `Submission/Work/KMTAreas/A7/fiberVarSamplingCoreG.lean` proves these, but carries a
`sorry` and therefore cannot be imported into a `sorry`-free closure; the (short) proof texts are
reproduced here, in the namespace `Work.KMTAreas.A7Hi`, with `Freq` written out as
`Work.Analysis.IonescuWainger.Circle` and `circleMeasure` as
`Work.Analysis.IonescuWainger.circleMeasure`.  `fourier_add_arg` and `fourier_neg_neg'` below are
the local versions (already proved above). -/

/-- Translating the argument of a symbol by `α` multiplies its Fourier coefficients by the
character `e(-jα)`. -/
theorem fourierCoeff_comp_sub' (M : Work.Analysis.IonescuWainger.Circle → ℂ)
    (α : Work.Analysis.IonescuWainger.Circle) (j : ℤ) :
    fourierCoeff (fun ξ : Work.Analysis.IonescuWainger.Circle => M (ξ - α)) j
      = fourier (T := 1) (-j) α * fourierCoeff M j := by
  have hL : (∫ t : Work.Analysis.IonescuWainger.Circle, fourier (T := 1) (-j) t • M (t - α)
        ∂Work.Analysis.IonescuWainger.circleMeasure)
      = ∫ s : Work.Analysis.IonescuWainger.Circle, fourier (T := 1) (-j) (s + α) • M s
        ∂Work.Analysis.IonescuWainger.circleMeasure := by
    rw [← MeasureTheory.integral_add_right_eq_self
      (fun t : Work.Analysis.IonescuWainger.Circle => fourier (T := 1) (-j) t • M (t - α)) α]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by simp)
  have hpt : ∀ s : Work.Analysis.IonescuWainger.Circle, fourier (T := 1) (-j) (s + α) • M s
      = fourier (T := 1) (-j) α • (fourier (T := 1) (-j) s • M s) := by
    intro s
    rw [fourier_add_arg, mul_smul, smul_comm]
  show (∫ t : Work.Analysis.IonescuWainger.Circle, fourier (T := 1) (-j) t • M (t - α)
        ∂Work.Analysis.IonescuWainger.circleMeasure)
      = fourier (T := 1) (-j) α * (∫ t : Work.Analysis.IonescuWainger.Circle,
          fourier (T := 1) (-j) t • M t ∂Work.Analysis.IonescuWainger.circleMeasure)
  rw [hL]
  rw [show (∫ s : Work.Analysis.IonescuWainger.Circle, fourier (T := 1) (-j) (s + α) • M s
        ∂Work.Analysis.IonescuWainger.circleMeasure)
      = ∫ s : Work.Analysis.IonescuWainger.Circle, fourier (T := 1) (-j) α •
          (fourier (T := 1) (-j) s • M s) ∂Work.Analysis.IonescuWainger.circleMeasure from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_smul, smul_eq_mul]

/-- **The twisted Ionescu--Wainger symbol**: the translates of `Φ` with the coefficients `e(M α)`. -/
noncomputable def iwTwist (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Phi : Work.Analysis.IonescuWainger.Circle → ℂ) (M : ℤ) :
    Work.Analysis.IonescuWainger.Circle → ℂ :=
  fun ξ => ∑ α ∈ A, fourier (T := 1) M α * Phi (ξ - α)

/-- **The kernel of a twisted IW symbol.** -/
theorem iwKernel_iwTwist (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Phi : Work.Analysis.IonescuWainger.Circle → ℂ) (M j : ℤ)
    (hint : ∀ α ∈ A, Integrable (fun ξ : Work.Analysis.IonescuWainger.Circle => Phi (ξ - α))
      Work.Analysis.IonescuWainger.circleMeasure) :
    Work.Analysis.IWMultiplier.iwKernel (iwTwist A Phi M) j
      = (∑ α ∈ A, fourier (T := 1) (M - j) α) * fourierCoeff Phi j := by
  simp only [Work.Analysis.IWMultiplier.iwKernel]
  change fourierCoeff (fun ξ : Work.Analysis.IonescuWainger.Circle =>
      ∑ α ∈ A, fourier (T := 1) M α * Phi (ξ - α)) j
      = (∑ α ∈ A, fourier (T := 1) (M - j) α) * fourierCoeff Phi j
  rw [show (fun ξ : Work.Analysis.IonescuWainger.Circle =>
      ∑ α ∈ A, fourier (T := 1) M α * Phi (ξ - α))
      = (∑ α ∈ A, fun ξ : Work.Analysis.IonescuWainger.Circle =>
          fourier (T := 1) M α * Phi (ξ - α)) from by
        funext ξ; rw [Finset.sum_apply]]
  rw [fourierCoeff.sum A _ (fun α hα => (hint α hα).const_mul _), Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun α _ =>
    fourierCoeff.const_mul (fun ξ : Work.Analysis.IonescuWainger.Circle => Phi (ξ - α))
      (fourier (T := 1) M α) j)]
  rw [Finset.sum_congr rfl (fun α _ => by rw [fourierCoeff_comp_sub' Phi α j])]
  rw [Finset.sum_congr rfl (fun α _ => (mul_assoc _ _ _).symm), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have hchar : fourier (T := 1) M α * fourier (T := 1) (-j) α
      = fourier (T := 1) (M - j) α := by
    rw [fourier_apply, fourier_apply, fourier_apply, ← Circle.coe_mul, ← AddCircle.toCircle_add,
      ← add_zsmul, show M + -j = M - j from by ring]
  rw [hchar]

/-- **The twist is a character times a plain IW symbol.** -/
theorem iwTwist_eq_fourier_mul (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Phi : Work.Analysis.IonescuWainger.Circle → ℂ) (M : ℤ) :
    iwTwist A Phi M
      = fun ξ : Work.Analysis.IonescuWainger.Circle =>
          fourier (T := 1) M ξ *
            Work.Analysis.IonescuWainger.iwSymbolSet A (fun η :
              Work.Analysis.IonescuWainger.Circle => Phi η * fourier (T := 1) (-M) η) ξ := by
  funext ξ
  simp only [iwTwist, Work.Analysis.IonescuWainger.iwSymbolSet_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have h : fourier (T := 1) M ξ * fourier (T := 1) (-M) (ξ - α)
      = fourier (T := 1) M α := by
    rw [sub_eq_add_neg, fourier_add_arg, ← mul_assoc, ← fourier_add,
      show M + -M = (0 : ℤ) from by ring, fourier_zero, one_mul]
    exact fourier_neg_neg' M α
  rw [← h]; ring

/-- **Multiplying a symbol by a character shifts its kernel.** -/
theorem iwKernel_fourier_mul (M : ℤ) (σ : Work.Analysis.IonescuWainger.Circle → ℂ) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel
        (fun ξ : Work.Analysis.IonescuWainger.Circle => fourier (T := 1) M ξ * σ ξ) j
      = Work.Analysis.IWMultiplier.iwKernel σ (j - M) := by
  simp only [Work.Analysis.IWMultiplier.iwKernel, fourierCoeff]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show fourier (T := 1) (-j) t • (fourier (T := 1) M t * σ t)
      = fourier (T := 1) (-(j - M)) t • σ t
  simp only [smul_eq_mul]
  have h : fourier (T := 1) (-j) t * fourier (T := 1) M t
      = fourier (T := 1) (-(j - M)) t := by
    rw [mul_comm, ← fourier_add]
    congr 1
    ring
  rw [← mul_assoc, h]

/-- `fourierCoeff (periodize φ) = cw φ` for an integrable `φ`. -/
theorem fourierCoeff_periodize_eq_cw {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) :
    fourierCoeff (Work.Analysis.IonescuWainger.periodize φ) j = Work.KMTAreas.A7.cw φ j := by
  have h := Work.KMTPlan.A6.IwKernelArithChar
    (A := ({(0 : Work.Analysis.IonescuWainger.Circle)} : Finset
      Work.Analysis.IonescuWainger.Circle)) hφ j
  have hsym : Work.Analysis.IonescuWainger.iwSymbolSet
      ({(0 : Work.Analysis.IonescuWainger.Circle)} : Finset Work.Analysis.IonescuWainger.Circle)
      (Work.Analysis.IonescuWainger.periodize φ) = Work.Analysis.IonescuWainger.periodize φ := by
    funext ξ; simp [Work.Analysis.IonescuWainger.iwSymbolSet]
  have hone : (∑ α ∈ ({(0 : Work.Analysis.IonescuWainger.Circle)} : Finset
      Work.Analysis.IonescuWainger.Circle), fourier (T := 1) (-j) α) = 1 := by simp
  rw [hsym, hone, one_mul] at h
  simpa [Work.Analysis.IWMultiplier.iwKernel] using h

/-- **The fibre `fiberOpP` is the convolution with the kernel of the twisted IW symbol.** -/
theorem fiberOpP_eq_twistedIwConv (ρ : ℝ) (P : Polynomial ℤ) (l : ℕ) (m : ℝ → ℂ)
    (hm : Integrable m)
    (hint : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      Integrable (fun ξ : Work.Analysis.IonescuWainger.Circle =>
        Work.Analysis.IonescuWainger.periodize m (ξ - α))
        Work.Analysis.IonescuWainger.circleMeasure) (n₀ : ℤ) (v : ℤ → ℂ) :
    Work.KMTAreas.A7.fiberOpP ρ P l m n₀ v
      = fun x : ℤ => ∑' j : ℤ,
          Work.Analysis.IWMultiplier.iwKernel
            (iwTwist (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
              (Work.Analysis.IonescuWainger.periodize m) (P.eval n₀)) j * v (x - j) := by
  funext x
  simp only [Work.KMTAreas.A7.fiberOpP]
  refine tsum_congr (fun j => ?_)
  rw [iwKernel_iwTwist (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
      (Work.Analysis.IonescuWainger.periodize m) (P.eval n₀) j hint,
    fourierCoeff_periodize_eq_cw hm j]

/-- Reindexing a translate of an IW convolution. -/
theorem iwConv_sub_eq (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Phi : Work.Analysis.IonescuWainger.Circle → ℂ) (v : ℤ → ℂ) (x M : ℤ) :
    Work.Analysis.IWMultiplier.iwConv A Phi v (x - M)
      = ∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet A Phi) (j - M) * v (x - j) := by
  simp only [Work.Analysis.IWMultiplier.iwConv_apply, smul_eq_mul]
  rw [← (Equiv.subRight M).tsum_eq
    (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Phi) j * v (x - M - j))]
  exact tsum_congr (fun j => by rw [Equiv.subRight_apply]; congr 1; ring)

/-- **The fibre `fiberOpP` is a translate of an Ionescu--Wainger convolution** (discrete `form-1`):

  `fiberOpP ρ P l m n₀ v = fun x ↦ (iwConv (ℚ/ℤ)_l (m̃ · e(-P(n₀)·)) v) (x - P(n₀))`. -/
theorem fiberOpP_eq_translate_iwConv (ρ : ℝ) (P : Polynomial ℤ) (l : ℕ) (m : ℝ → ℂ)
    (hm : Integrable m)
    (hint : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      Integrable (fun ξ : Work.Analysis.IonescuWainger.Circle =>
        Work.Analysis.IonescuWainger.periodize m (ξ - α))
        Work.Analysis.IonescuWainger.circleMeasure) (n₀ : ℤ) (v : ℤ → ℂ) :
    Work.KMTAreas.A7.fiberOpP ρ P l m n₀ v
      = fun x : ℤ => Work.Analysis.IWMultiplier.iwConv
          (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (fun η : Work.Analysis.IonescuWainger.Circle =>
            Work.Analysis.IonescuWainger.periodize m η * fourier (T := 1) (-(P.eval n₀)) η) v
          (x - P.eval n₀) := by
  funext x
  rw [fiberOpP_eq_twistedIwConv ρ P l m hm hint n₀ v, iwTwist_eq_fourier_mul, iwConv_sub_eq]
  exact tsum_congr (fun j => by rw [iwKernel_fourier_mul])

/-- **A distance bound for the translated arcs.**  If `ζ - α` and `ζ - β` lie in the arcs of
radii `ε₁`, `ε₂` around `0`, then `‖α - β‖ < r` as soon as `ε₁ + ε₂ < r`. -/
theorem norm_sub_lt_of_mem_arcSet_translate {ζ α β : Work.Analysis.IonescuWainger.Circle}
    {ε₁ ε₂ r : ℝ}
    (h₁ : ζ - α ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 ε₁)
    (h₂ : ζ - β ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 ε₂) (hε : ε₁ + ε₂ < r) :
    ‖α - β‖ < r := by
  obtain ⟨θ₁, hθ₁, he₁⟩ := h₁
  obtain ⟨θ₂, hθ₂, he₂⟩ := h₂
  have h₁' : (θ₁ : Work.Analysis.IonescuWainger.Circle) = ζ - α := by
    simpa using he₁.symm
  have h₂' : (θ₂ : Work.Analysis.IonescuWainger.Circle) = ζ - β := by
    simpa using he₂.symm
  rw [QuotientAddGroup.norm_lt_iff]
  refine ⟨θ₂ - θ₁, ?_, ?_⟩
  · rw [AddCircle.coe_sub, h₂', h₁']; abel
  · rw [Real.norm_eq_abs]
    calc |θ₂ - θ₁| ≤ |θ₂| + |θ₁| := abs_sub _ _
      _ ≤ ε₂ + ε₁ := by linarith
      _ < r := by linarith

/-- **The aliasing product identity for the fibre's symbol** (the pointwise half of the gate
identity; see `NOTES_A7Hi_FiberVarSampling_ROUTE.md` §2/§10). -/
theorem gateSymbolProduct (A : Finset Work.Analysis.IonescuWainger.Circle) (δ : ℝ) (hδ : 0 < δ)
    (mt pt chi : Work.Analysis.IonescuWainger.Circle → ℂ)
    (hm1 : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ → mt θ = 1)
    (hms : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      mt θ ≠ 0 → θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * δ))
    (hna : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → 8 * δ ≤ ‖α - β‖)
    (hp : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      pt θ ≠ 0 → θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ)
    (ζ : Work.Analysis.IonescuWainger.Circle) :
    (∑ α ∈ A, (fun ξ : Work.Analysis.IonescuWainger.Circle => mt ξ * chi ξ) (ζ - α)) *
        (∑ α ∈ A, pt (ζ - α))
      = ∑ α ∈ A, (fun ξ : Work.Analysis.IonescuWainger.Circle => chi ξ * pt ξ) (ζ - α) := by
  by_cases h : ∃ α ∈ A, pt (ζ - α) ≠ 0
  · obtain ⟨α₀, hα₀, hpt₀⟩ := h
    have harc₀ : ζ - α₀ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ := hp _ hpt₀
    have huniq : ∀ α ∈ A, pt (ζ - α) ≠ 0 → α = α₀ := by
      intro α hαA hptα
      by_contra hne
      have hlt := norm_sub_lt_of_mem_arcSet_translate (ζ := ζ) (α := α) (β := α₀)
        (hp _ hptα) harc₀ (by linarith : δ + δ < 8 * δ)
      linarith [hna α hαA α₀ hα₀ hne]
    have hmtzero : ∀ α ∈ A, α ≠ α₀ → mt (ζ - α) = 0 := by
      intro α hαA hne
      by_contra hmt
      have hlt := norm_sub_lt_of_mem_arcSet_translate (ζ := ζ) (α := α) (β := α₀)
        (hms _ hmt) harc₀ (by linarith : 2 * δ + δ < 8 * δ)
      linarith [hna α hαA α₀ hα₀ hne]
    have hptzero : ∀ α ∈ A, α ≠ α₀ → pt (ζ - α) = 0 := by
      intro α hαA hne
      by_contra hpt
      exact hne (huniq α hαA hpt)
    have hsum1 : (∑ α ∈ A, (fun ξ : Work.Analysis.IonescuWainger.Circle => mt ξ * chi ξ)
        (ζ - α)) = mt (ζ - α₀) * chi (ζ - α₀) := by
      refine Finset.sum_eq_single α₀ (fun α hαA hne => ?_) (fun hnot => absurd hα₀ hnot)
      show mt (ζ - α) * chi (ζ - α) = 0
      rw [hmtzero α hαA hne, zero_mul]
    have hsum2 : (∑ α ∈ A, pt (ζ - α)) = pt (ζ - α₀) := by
      refine Finset.sum_eq_single α₀ (fun α hαA hne => hptzero α hαA hne) (fun hnot =>
        absurd hα₀ hnot)
    have hsum3 : (∑ α ∈ A, (fun ξ : Work.Analysis.IonescuWainger.Circle => chi ξ * pt ξ)
        (ζ - α)) = chi (ζ - α₀) * pt (ζ - α₀) := by
      refine Finset.sum_eq_single α₀ (fun α hαA hne => ?_) (fun hnot => absurd hα₀ hnot)
      show chi (ζ - α) * pt (ζ - α) = 0
      rw [hptzero α hαA hne, mul_zero]
    rw [hsum1, hsum2, hsum3, hm1 _ harc₀, one_mul]
  · push_neg at h
    have hsum2 : (∑ α ∈ A, pt (ζ - α)) = 0 := Finset.sum_eq_zero (fun α hαA => h α hαA)
    have hsum3 : (∑ α ∈ A, (fun ξ : Work.Analysis.IonescuWainger.Circle => chi ξ * pt ξ)
        (ζ - α)) = 0 := by
      refine Finset.sum_eq_zero (fun α hαA => ?_)
      show chi (ζ - α) * pt (ζ - α) = 0
      rw [h α hαA, mul_zero]
    rw [hsum2, hsum3, mul_zero]

/-- **The twist splits off the correction**: `iwSymbolSet` of the twisted profile is the plain one
minus the narrow-profile one.  This is the algebraic step that turns the gate identity
`Work.KMTAreas.A7Hi.fiberOp_Tex_eq_twisted` into `fiberOp ρ l m n₀ (Tex ρ l φ f) = (v - E)(· - n₀)`
with `v = Tex ρ l φ f` and `E = iwConv A (iwSymbolSet A ((1 - fourier (-n₀))·periodize φ)) f`
(see `NOTES_A7Hi_FiberVarSampling_ROUTE.md` §19). -/
theorem iwSymbolSet_twist_split (A : Finset Work.Analysis.IonescuWainger.Circle) (n₀ : ℤ)
    (Phi : Work.Analysis.IonescuWainger.Circle → ℂ)
    (ζ : Work.Analysis.IonescuWainger.Circle) :
    Work.Analysis.IonescuWainger.iwSymbolSet A
        (fun ξ : Work.Analysis.IonescuWainger.Circle => fourier (T := 1) (-n₀) ξ * Phi ξ) ζ
      = Work.Analysis.IonescuWainger.iwSymbolSet A Phi ζ
        - Work.Analysis.IonescuWainger.iwSymbolSet A
            (fun ξ : Work.Analysis.IonescuWainger.Circle =>
              (1 - fourier (T := 1) (-n₀) ξ) * Phi ξ) ζ := by
  simp only [Work.Analysis.IonescuWainger.iwSymbolSet_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  ring

/-- **The twisted Ionescu–Wainger symbol factors through the plain one.**  For every finite set `A`
of frequencies, every `n₀ : ℤ`, every profile `φ̃` on the circle and every `ζ`,

  `∑_{α∈A} fourier n₀ α · φ̃(ζ-α) = fourier n₀ ζ · ( (∑_{α∈A} φ̃(ζ-α)) - ∑_{α∈A} (1 - fourier (-n₀)(ζ-α)) φ̃(ζ-α) )`,

i.e. the twisted symbol is the (plain) Ionescu–Wainger symbol of `φ̃` minus the *narrow* symbol
with the profile `(1 - fourier (-n₀)) φ̃`, modulated by `fourier n₀`.  This is the symbol-level
content of the gate identity of `NOTES_A7Hi_FiberVarSampling_ROUTE.md` §2/§10: the correction
profile vanishes at the origin and is `O(n₀ β)` on the packets. -/
theorem iwSymbolSet_twist_factor (A : Finset Work.Analysis.IonescuWainger.Circle) (n₀ : ℤ)
    (ph : Work.Analysis.IonescuWainger.Circle → ℂ) (ζ : Work.Analysis.IonescuWainger.Circle) :
    (∑ α ∈ A, fourier (T := 1) n₀ α * ph (ζ - α))
      = fourier (T := 1) n₀ ζ * ((∑ α ∈ A, ph (ζ - α))
          - ∑ α ∈ A, (1 - fourier (T := 1) (-n₀) (ζ - α)) * ph (ζ - α)) := by
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have h : fourier (T := 1) n₀ ζ * fourier (T := 1) (-n₀) (ζ - α)
      = fourier (T := 1) n₀ α := by
    rw [sub_eq_add_neg, fourier_add_arg, ← mul_assoc, ← fourier_add,
      show n₀ + -n₀ = (0 : ℤ) from by ring, fourier_zero, one_mul]
    exact fourier_neg_neg' n₀ α
  calc fourier (T := 1) n₀ α * ph (ζ - α)
      = fourier (T := 1) n₀ ζ * (fourier (T := 1) (-n₀) (ζ - α) * ph (ζ - α)) := by
        rw [← mul_assoc, h]
    _ = fourier (T := 1) n₀ ζ * ph (ζ - α)
          - fourier (T := 1) n₀ ζ * ((1 - fourier (T := 1) (-n₀) (ζ - α)) * ph (ζ - α)) := by
        ring

/-- **The fibre kernel of the bump `mStarF U` is summable** (the summability hypothesis needed by
the gate identity of the fibre; see `NOTES_A7Hi_FiberVarSampling_ROUTE.md` §13/§14). -/
theorem summable_cw_mStarF (U : ℕ) :
    Summable (fun j : ℤ => Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j) :=
  (Work.KMTAreas.A7.summable_cw_etaCut (-(2 * (U : ℤ)))).of_norm

/-- **The `residueLp` average of the translates `F (· - n₀)` has the same `ℓᵖ`-norm as `F`.**  This
is what makes the residue average over the fibre residues `n₀ < q` free in the sampling estimate:
the fibre at the residue `n₀` is the *shift* `(v - E)(· - n₀)` of a single family, and the
`n₀`-average of the translates of a function has exactly the `ℓᵖ`-norm of that function. -/
theorem eLpNorm_residueLp_shift {p : ℝ} (hp : 0 < p) {q : ℕ} (hq : 1 ≤ q) (F : ℤ → ENNReal) :
    eLpNorm (fun x : ℤ => (Work.KMTAreas.A7.residueLp p q (fun y n₀ => F (y - (n₀ : ℤ))) x : ENNReal))
        (ENNReal.ofReal p) Measure.count
      = eLpNorm F (ENNReal.ofReal p) Measure.count := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  rw [eLpNormResidueLpEq p hp q (fun y n₀ => F (y - (n₀ : ℤ)))]
  have hconst : ∀ n₀ : ℕ,
      eLpNorm (fun y : ℤ => F (y - (n₀ : ℤ))) (ENNReal.ofReal p) Measure.count
        = eLpNorm F (ENNReal.ofReal p) Measure.count :=
    fun n₀ => eLpNorm_count_sub hp0 hpt F (n₀ : ℤ)
  simp only [hconst]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hq0 : (q : ENNReal) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqt : (q : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top q
  change ((q : ENNReal) ^ (-1 : ℝ) *
      ((q : ENNReal) * eLpNorm F (ENNReal.ofReal p) Measure.count ^ p)) ^ (1 / p)
      = eLpNorm F (ENNReal.ofReal p) Measure.count
  rw [ENNReal.rpow_neg_one, ← mul_assoc, ENNReal.inv_mul_cancel hq0 hqt, one_mul, one_div]
  exact ENNReal.rpow_rpow_inv hp.ne' _

/-- **The small-`L` case of the fibre sampling estimate** (`L = max (max l₁ l₂) (max k₁ k₂) ≤ B ρ`).

Here the crude Young bound for the fibre kernel applies to *every* family `u` and *every* residue
`n₀` (`Work.KMTAreas.A7.fiberOpVarNonFareyBounded`, proved), with an absolute constant; averaging
over the residues `n₀ < arithQ ρ (max l₁ l₂)` with the Tonelli identity
`Work.KMTAreas.A7Hi.eLpNormResidueLpEq` costs nothing, because the bound is the *same* for every
`n₀`.  This is case 1 of the two-case split of `NOTES_A7Hi_FiberVarSampling_ROUTE.md` §9. -/
theorem FiberVarSampling_smallL (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (r : NNReal) (hr : 2 < r)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (B : ℝ → ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
        max (max l₁ l₂) (max k₁ k₂) ≤ B ρ →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
                  (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
                    (max (max l₁ l₂) (max k₁ k₂)))) n₀
                  (Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y)) x)
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p
                MeasureTheory.Measure.count := by
  obtain ⟨Cb, hCb, hmain⟩ :=
    Work.KMTAreas.A7.fiberOpVarNonFareyBounded r hr ρ hρ hρ1 p hp hptop B
  refine ⟨Cb, hCb, fun a Λ l₁ l₂ k₁ k₂ t f hL => ?_⟩
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hq
  set W : ℤ → ℕ → ENNReal := fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
      (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
      (Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y) with hW
  set X : ENNReal := MeasureTheory.eLpNorm (fun x : ℤ =>
    PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x))
    (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count with hX
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (lt_trans (zero_lt_one : (0 : ENNReal) < 1) hp).ne' hptop.ne
  have hpr : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop.ne
  have hq0 : (q : ENNReal) ≠ 0 := by
    rw [hq]; exact_mod_cast (Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂)).ne'
  have hqt : (q : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top q
  have hpt : ∀ n₀ : ℕ, MeasureTheory.eLpNorm (fun y : ℤ => W y n₀)
      (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count ≤ ENNReal.ofReal Cb * X := by
    intro n₀
    have h := hmain l₁ l₂ k₁ k₂ hL n₀
      (fun n : ℕ => Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n)
    have h1 : MeasureTheory.eLpNorm (fun y : ℤ => W y n₀)
        (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
              (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
                (max (max l₁ l₂) (max k₁ k₂)))) n₀
              (Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y))
          p MeasureTheory.Measure.count := by rw [hpr, hW]
    rw [h1, hX, hpr]
    exact h
  have hgoal : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal q
      (fun y n₀ => W y n₀) x)
      (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count ≤ ENNReal.ofReal Cb * X := by
    rw [Work.KMTAreas.A7Hi.eLpNormResidueLpEq p.toReal hp0 q (fun y n₀ => W y n₀)]
    have hsum : (∑ n₀ ∈ Finset.range q,
          (MeasureTheory.eLpNorm (fun y : ℤ => W y n₀) (ENNReal.ofReal p.toReal)
            MeasureTheory.Measure.count) ^ p.toReal)
        ≤ ∑ _n₀ ∈ Finset.range q, (ENNReal.ofReal Cb * X) ^ p.toReal :=
      Finset.sum_le_sum (fun n₀ _ => ENNReal.rpow_le_rpow (hpt n₀) hp0.le)
    have hsum' : (∑ n₀ ∈ Finset.range q,
          (MeasureTheory.eLpNorm (fun y : ℤ => W y n₀) (ENNReal.ofReal p.toReal)
            MeasureTheory.Measure.count) ^ p.toReal)
        ≤ (q : ENNReal) * (ENNReal.ofReal Cb * X) ^ p.toReal := by
      refine hsum.trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hstep : (q : ENNReal)⁻¹ * (∑ n₀ ∈ Finset.range q,
          (MeasureTheory.eLpNorm (fun y : ℤ => W y n₀) (ENNReal.ofReal p.toReal)
            MeasureTheory.Measure.count) ^ p.toReal)
        ≤ (q : ENNReal)⁻¹ * ((q : ENNReal) * (ENNReal.ofReal Cb * X) ^ p.toReal) :=
      mul_le_mul' le_rfl hsum'
    have hstep2 : (q : ENNReal)⁻¹ * ((q : ENNReal) * (ENNReal.ofReal Cb * X) ^ p.toReal)
        = (ENNReal.ofReal Cb * X) ^ p.toReal := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 hqt, one_mul]
    change ((q : ENNReal) ^ (-1 : ℝ) * ∑ n₀ ∈ Finset.range q,
        (MeasureTheory.eLpNorm (fun y : ℤ => W y n₀) (ENNReal.ofReal p.toReal)
          MeasureTheory.Measure.count) ^ p.toReal) ^ (1 / p.toReal)
        ≤ ENNReal.ofReal Cb * X
    rw [ENNReal.rpow_neg_one]
    refine le_trans (ENNReal.rpow_le_rpow hstep (by positivity)) ?_
    rw [hstep2, one_div]
    exact le_of_eq (ENNReal.rpow_rpow_inv hp0.ne' (ENNReal.ofReal Cb * X))
  rw [hpr] at hgoal
  simpa [hq, hW, hX, hpr] using hgoal


private theorem fourierCoeff_iwSymbolSet (A : Finset Work.Analysis.IonescuWainger.Circle)
    {Ψ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hΨ : MeasureTheory.Integrable Ψ Work.Analysis.IonescuWainger.circleMeasure) (j : ℤ) :
    fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ) j
      = (∑ α ∈ A, fourier (T := 1) (-j) α) * fourierCoeff Ψ j := by
  have hint : ∀ α ∈ A, MeasureTheory.Integrable
      (fun ξ : Work.Analysis.IonescuWainger.Circle => Ψ (ξ - α))
      Work.Analysis.IonescuWainger.circleMeasure := by
    intro α _
    simpa only [sub_eq_add_neg] using hΨ.comp_add_right (-α)
  have h1 : (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ)
      = ∑ α ∈ A, (fun ξ : Work.Analysis.IonescuWainger.Circle => Ψ (ξ - α)) := by
    funext ξ
    simp only [Work.Analysis.IonescuWainger.iwSymbolSet_apply, Finset.sum_apply]
  rw [h1]
  trans ∑ α ∈ A, fourierCoeff (fun ξ : Work.Analysis.IonescuWainger.Circle => Ψ (ξ - α)) j
  · simpa only [Finset.sum_apply] using
      congrFun (fourierCoeff.sum A (fun α ξ => Ψ (ξ - α)) hint) j
  · rw [Finset.sum_congr rfl (fun α _ => fourierCoeff_comp_sub' Ψ α j), Finset.sum_mul]

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Elementary integrability of Ionescu--Wainger symbols -/

/-- The Ionescu--Wainger symbol of an integrable profile is integrable: it is a finite sum of
translates. -/
private theorem integrable_iwSymbolSet (A : Finset Circ) {Ψ : Circ → ℂ}
    (hΨ : MeasureTheory.Integrable Ψ Work.Analysis.IonescuWainger.circleMeasure) :
    MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ)
      Work.Analysis.IonescuWainger.circleMeasure := by
  have hterm : ∀ α ∈ A, MeasureTheory.Integrable (fun ξ : Circ => Ψ (ξ - α))
      Work.Analysis.IonescuWainger.circleMeasure := fun α _ => hΨ.comp_sub_right α
  have hsum : (∑ α ∈ A, fun ξ : Circ => Ψ (ξ - α))
      = Work.Analysis.IonescuWainger.iwSymbolSet A Ψ := by
    funext ξ
    simp [Work.Analysis.IonescuWainger.iwSymbolSet]
  rw [← hsum]
  exact integrable_finsetSum' A hterm

/-- If an integrable profile has absolutely summable Fourier coefficients, so does the
Ionescu--Wainger symbol built from it (`‖∑_α fourier (-j) α‖ ≤ #A`). -/
private theorem summable_fourierCoeff_iwSymbolSet (A : Finset Circ) {Ψ : Circ → ℂ}
    (hΨ : MeasureTheory.Integrable Ψ Work.Analysis.IonescuWainger.circleMeasure)
    (hs : Summable (fun j : ℤ => fourierCoeff Ψ j)) :
    Summable (fun j : ℤ =>
      ‖fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ) j‖) := by
  have hnorm : Summable (fun j : ℤ => ‖fourierCoeff Ψ j‖) := hs.norm
  have hbound : Summable (fun j : ℤ => ((A.card : ℕ) : ℝ) * ‖fourierCoeff Ψ j‖) :=
    hnorm.mul_left _
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hbound
  rw [fourierCoeff_iwSymbolSet A hΨ j, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖∑ α ∈ A, fourier (T := 1) (-j) α‖ ≤ ∑ α ∈ A, ‖fourier (T := 1) (-j) α‖ :=
        norm_sum_le _ _
    _ = ∑ _α ∈ A, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [fourier_apply]
        exact Circle.norm_coe _
    _ = ((A.card : ℕ) : ℝ) := by simp

/-! ## The fibre as a translate of an Ionescu--Wainger convolution -/

/-- **The fibre is a translate of an Ionescu--Wainger convolution.**  If `mt` is a circle profile
whose Fourier coefficients are the `cw m`, then for every `v : ℤ → ℂ`

`fiberOp ρ l m n₀ v = τ_{n₀} (iwConv (ℚ/ℤ)_l (mt · e(-n₀·)) v)`.

Indeed the `j`-th kernel of the fibre is `(∑_{α} fourier (n₀-j) α) · cw m j =
fourierCoeff (iwSymbolSet A (mt·χ)) (j - n₀)`, which is exactly the `(j-n₀)`-th coefficient of the
twisted symbol; reindexing the convolution sum by `j ↦ j - n₀` gives the translate. -/
private theorem fiberOp_eq_translate_iwConv (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (mt : Circ → ℂ) (n₀ : ℤ)
    (hmt : ∀ j : ℤ, fourierCoeff mt j = Work.KMTAreas.A7.cw m j)
    (hmtint : MeasureTheory.Integrable
      (fun ξ : Circ => mt ξ * fourier (T := 1) (-n₀) ξ)
      Work.Analysis.IonescuWainger.circleMeasure)
    (v : ℤ → ℂ) :
    Work.KMTAreas.A7.fiberOp ρ l m n₀ v
      = fun y : ℤ => Work.Analysis.IWMultiplier.iwConv
          (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (fun ξ : Circ => mt ξ * fourier (T := 1) (-n₀) ξ) v (y - n₀) := by
  funext y
  rw [Work.Analysis.IWMultiplier.iwConv_apply]
  simp only [smul_eq_mul]
  change (∑' j : ℤ, (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
        fourier (T := 1) (n₀ - j) α) * Work.KMTAreas.A7.cw m j * v (y - j))
      = ∑' j : ℤ, fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
          (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (fun ξ : Circ => mt ξ * fourier (T := 1) (-n₀) ξ)) j * v (y - n₀ - j)
  rw [← (Equiv.subRight n₀).tsum_eq
    (fun j : ℤ => fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (fun ξ : Circ => mt ξ * fourier (T := 1) (-n₀) ξ)) j * v (y - n₀ - j))]
  simp only [Equiv.subRight_apply]
  refine tsum_congr (fun j => ?_)
  have hcoeff : fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
      (fun ξ : Circ => mt ξ * fourier (T := 1) (-n₀) ξ)) (j - n₀)
      = (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
            fourier (T := 1) (n₀ - j) α) * Work.KMTAreas.A7.cw m j := by
    rw [fourierCoeff_iwSymbolSet _ hmtint (j - n₀)]
    rw [show -(j - n₀) = n₀ - j from by ring]
    congr 1
    have hcomm : (fun ξ : Circ => mt ξ * fourier (T := 1) (-n₀) ξ)
        = fun ξ : Circ => fourier (T := 1) (-n₀) ξ * mt ξ := by
      funext ξ; rw [mul_comm]
    rw [hcomm]
    change Work.Analysis.IWMultiplier.iwKernel
      (fun ξ : Circ => fourier (T := 1) (-n₀) ξ * mt ξ) (j - n₀) = Work.KMTAreas.A7.cw m j
    rw [iwKernel_fourier_mul]
    rw [show j - n₀ - (-n₀) = j from by ring]
    exact hmt j
  rw [hcoeff, show y - n₀ - (j - n₀) = y - j from by ring]

/-! ## Composition of Ionescu--Wainger convolutions -/

/-- **Composition of two Ionescu--Wainger convolutions.**  If the pointwise product of the two
symbols is the third symbol (`gateSymbolProduct`), then the corresponding convolutions compose, for
every bounded input.  In kernel form this is the identity `K₁ ⋆ K₂ = K₃` for the coefficient
sequences, which is the convolution theorem `fourierCoeff_mul_l1`, followed by the reassociation
`tsum_conv_conv` of the double `tsum`. -/
private theorem iwConv_comp (A : Finset Circ) (Ψ₁ Ψ₂ Ψ₃ : Circ → ℂ)
    (h1 : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁)
      Work.Analysis.IonescuWainger.circleMeasure)
    (h2 : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂)
      Work.Analysis.IonescuWainger.circleMeasure)
    (h3 : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₃)
      Work.Analysis.IonescuWainger.circleMeasure)
    (hs1 : Summable (fun j : ℤ =>
      fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁) j))
    (hs2 : Summable (fun j : ℤ =>
      fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂) j))
    (hgate : ∀ ζ : Circ, Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁ ζ
        * Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂ ζ
      = Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₃ ζ)
    (f : ℤ → ℂ) {B : ℝ} (hf : ∀ y : ℤ, ‖f y‖ ≤ B) :
    Work.Analysis.IWMultiplier.iwConv A Ψ₁ (Work.Analysis.IWMultiplier.iwConv A Ψ₂ f)
      = Work.Analysis.IWMultiplier.iwConv A Ψ₃ f := by
  have hFG : MeasureTheory.Integrable (fun ξ : Circ =>
      Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁ ξ
        * Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂ ξ)
      Work.Analysis.IonescuWainger.circleMeasure :=
    h3.congr (Filter.Eventually.of_forall (fun ξ => (hgate ξ).symm))
  have hK : ∀ m : ℤ, (∑' j : ℤ,
        fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁) j
          * fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂) (m - j))
      = fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₃) m := by
    intro m
    rw [← fourierCoeff_mul_l1 h1 h2 hFG hs1 hs2 m]
    exact congrFun (fourierCoeff_congr_ae (Filter.Eventually.of_forall hgate)) m
  funext n
  simp only [Work.Analysis.IWMultiplier.iwConv_apply, smul_eq_mul]
  change (∑' j : ℤ, fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁) j
        * (∑' i : ℤ, fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂) i
          * f (n - j - i)))
      = ∑' m : ℤ, fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₃) m * f (n - m)
  rw [tsum_conv_conv
    (a := fun j : ℤ => fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁) j)
    (b := fun i : ℤ => fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂) i)
    (u := f) (C := B) hs1.norm hs2.norm hf n]
  exact tsum_congr (fun m => by rw [hK m])

/-! ## The gate identity -/

/-- **The gate identity** (KMT §8, `form-1`): the fibre of the twisted projection, evaluated on the exact-height projection `Tex ρ l φ f`, is the translate by `n₀` of the Ionescu–Wainger multiplier whose profile is `periodize φ` twisted by the character `fourier (T := 1) (-n₀)`.

This is the piece that reduces the target `Work.KMTAreas.A7Hi.FiberVarSampling` to a comparison of the variational norm of one family with itself (see `NOTES_A7Hi_FiberVarSampling_ROUTE.md` §2/§7/§15).  The hypotheses are the ones that make the fibre's kernel summable (`hm` + `hmsum`, cf. §13: an integrable but non-smooth `m` has `cw m` decaying only like `1/j` and then the `tsum` in `fiberOp` collapses to the junk value `0`), the circle-side plateau/support conditions on `periodize m` (`hm1`, `hms` — *not* the line conditions, which do not imply them), the `8δ`-separation of the frequency set (`hna`) and the circle-side support of `periodize φ` (`hφpacket`).  The input `f` is assumed **bounded** (`hf`): for unbounded `f` both sides are `tsum`s that may be non-summable (junk), which is a separate issue.  (The parameter `B` is only used to make `Tex ρ l φ f` bounded.) -/
private theorem gateIdentity (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j))
    (hm1 : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ →
      Work.Analysis.IonescuWainger.periodize m θ = 1)
    (hms : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize m θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * δ))
    (hna : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l, α ≠ β → 8 * δ ≤ ‖α - β‖)
    (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (hφsum : Summable (fun j : ℤ => Work.KMTAreas.A7.cw φ j))
    (hφpacket : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize φ ξ ≠ 0 →
      ∃ θ : ℝ, |θ| ≤ δ ∧ (θ : Work.Analysis.IonescuWainger.Circle) = ξ)
    (n₀ : ℤ) (f : ℤ → ℂ) (B : ℝ) (hf : ∀ y : ℤ, ‖f y‖ ≤ B) :
    Work.KMTAreas.A7.fiberOp ρ l m n₀ (Work.KMTAreas.A7.Tex ρ l φ f) =
      fun y : ℤ => Work.Analysis.IWMultiplier.iwConv
          (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (fun ζ : Work.Analysis.IonescuWainger.Circle =>
            fourier (T := 1) (-n₀) ζ *
              Work.Analysis.IonescuWainger.periodize φ ζ) f (y - n₀) := by
  have hm_int : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.periodize m)
      Work.Analysis.IonescuWainger.circleMeasure := Work.KMTPlan.A6.IntegrablePeriodize hm
  have hφ_int : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.periodize φ)
      Work.Analysis.IonescuWainger.circleMeasure := Work.KMTPlan.A6.IntegrablePeriodize hφ
  have hmtint : MeasureTheory.Integrable
      (fun ξ : Circ => Work.Analysis.IonescuWainger.periodize m ξ
        * fourier (T := 1) (-n₀) ξ) Work.Analysis.IonescuWainger.circleMeasure := by
    refine hm_int.mul_bdd (c := 1) (fourier (T := 1) (-n₀)).continuous.aestronglyMeasurable ?_
    filter_upwards with ξ
    rw [fourier_apply]
    exact le_of_eq (Circle.norm_coe _)
  have hchi_int : MeasureTheory.Integrable
      (fun ξ : Circ => fourier (T := 1) (-n₀) ξ
        * Work.Analysis.IonescuWainger.periodize φ ξ) Work.Analysis.IonescuWainger.circleMeasure := by
    refine (hφ_int.mul_bdd (c := 1)
      (fourier (T := 1) (-n₀)).continuous.aestronglyMeasurable ?_).congr ?_
    · filter_upwards with ξ
      rw [fourier_apply]
      exact le_of_eq (Circle.norm_coe _)
    · exact Filter.Eventually.of_forall (fun ξ => mul_comm _ _)
  have hpt_sum : Summable (fun j : ℤ =>
      fourierCoeff (Work.Analysis.IonescuWainger.periodize φ) j) := by
    simpa only [fourierCoeff_periodize_eq_cw hφ] using hφsum
  have htwist_sum : Summable (fun j : ℤ => fourierCoeff
      (fun ξ : Circ => Work.Analysis.IonescuWainger.periodize m ξ
        * fourier (T := 1) (-n₀) ξ) j) := by
    have hshift : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m (j + n₀)) :=
      (Equiv.summable_iff (Equiv.addRight n₀)).mpr hmsum
    refine hshift.congr (fun j => ?_)
    have hcomm : (fun ξ : Circ => Work.Analysis.IonescuWainger.periodize m ξ
          * fourier (T := 1) (-n₀) ξ)
        = fun ξ : Circ => fourier (T := 1) (-n₀) ξ
          * Work.Analysis.IonescuWainger.periodize m ξ := by
      funext ξ; rw [mul_comm]
    rw [hcomm]
    change Work.KMTAreas.A7.cw m (j + n₀) = Work.Analysis.IWMultiplier.iwKernel
      (fun ξ : Circ => fourier (T := 1) (-n₀) ξ
        * Work.Analysis.IonescuWainger.periodize m ξ) j
    rw [iwKernel_fourier_mul]
    rw [show j - (-n₀) = j + n₀ from by ring]
    exact (fourierCoeff_periodize_eq_cw hm (j + n₀)).symm
  have hs1 : Summable (fun j : ℤ => fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
      (fun ξ : Circ => Work.Analysis.IonescuWainger.periodize m ξ
        * fourier (T := 1) (-n₀) ξ)) j) :=
    (summable_fourierCoeff_iwSymbolSet _ hmtint htwist_sum).of_norm
  have hs2 : Summable (fun j : ℤ => fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
      (Work.Analysis.IonescuWainger.periodize φ)) j) :=
    (summable_fourierCoeff_iwSymbolSet _ hφ_int hpt_sum).of_norm
  have h1 : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
      (fun ξ : Circ => Work.Analysis.IonescuWainger.periodize m ξ
        * fourier (T := 1) (-n₀) ξ)) Work.Analysis.IonescuWainger.circleMeasure :=
    integrable_iwSymbolSet _ hmtint
  have h2 : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
      (Work.Analysis.IonescuWainger.periodize φ)) Work.Analysis.IonescuWainger.circleMeasure :=
    integrable_iwSymbolSet _ hφ_int
  have h3 : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
      (fun ξ : Circ => fourier (T := 1) (-n₀) ξ
        * Work.Analysis.IonescuWainger.periodize φ ξ))
      Work.Analysis.IonescuWainger.circleMeasure :=
    integrable_iwSymbolSet _ hchi_int
  have hp : ∀ θ : Circ, Work.Analysis.IonescuWainger.periodize φ θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ := by
    intro θ hθ
    obtain ⟨t, ht, htθ⟩ := hφpacket θ hθ
    exact ⟨t, ht, by rw [zero_add]; exact htθ.symm⟩
  have hgate : ∀ ζ : Circ, Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (fun ξ : Circ => Work.Analysis.IonescuWainger.periodize m ξ
          * fourier (T := 1) (-n₀) ξ) ζ
      * Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (Work.Analysis.IonescuWainger.periodize φ) ζ
      = Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (fun ξ : Circ => fourier (T := 1) (-n₀) ξ
          * Work.Analysis.IonescuWainger.periodize φ ξ) ζ := by
    intro ζ
    exact gateSymbolProduct _ δ hδ _ _ _ hm1 hms hna hp ζ
  rw [fiberOp_eq_translate_iwConv ρ l m (Work.Analysis.IonescuWainger.periodize m) n₀
    (fun j => fourierCoeff_periodize_eq_cw hm j) hmtint (Work.KMTAreas.A7.Tex ρ l φ f)]
  rw [show Work.KMTAreas.A7.Tex ρ l φ f
      = Work.Analysis.IWMultiplier.iwConv
          (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (Work.Analysis.IonescuWainger.periodize φ) f from rfl]
  rw [iwConv_comp (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l) _ _ _
    h1 h2 h3 hs1 hs2 hgate f hf]

/-- **The `0`-fibre fixes `Tex`-outputs** (the `n₀ = 0` instance of the gate identity
`gateIdentity`): for bounded `f`, `fiberOp ρ l m 0 (Tex ρ l φ f) = Tex ρ l φ f`.

This is the *correct* replacement for the false "range identity"
(`NOTES_A7Hi_FiberVarSampling_SESSION8.md` §0/§2, `…SESSION12.md` §2): at `n₀ ≠ 0` the fibre is
the *rephased* synthesis `y ↦ iwConv A (fourier (-n₀) · periodize φ) f (y - n₀)` and is **not**
the input (numerics: `ρ = 1`, `l = 1`, `A = {1/2}`, `n₀ = 1`, `f = δ₀` gives
`fiberOp 1 (Tex φ f)(y) = (-1)^{y+1} \hatφ(y)` while `Tex φ f(y) = (1 + (-1)^y)\hatφ(y)`).

Exactly at `n₀ = 0` the statement is what identifies the right-hand side of the packet-rotation
crux `A7Hi.PacketRotationResidueBoundLpGeTwo` with `Vʳ (w n)` for `w n = Tex ρ l₁ φ f`. -/
theorem fiberOp_zero_Tex_eq_self (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j))
    (hm1 : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ →
      Work.Analysis.IonescuWainger.periodize m θ = 1)
    (hms : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize m θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * δ))
    (hna : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l, α ≠ β → 8 * δ ≤ ‖α - β‖)
    (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (hφsum : Summable (fun j : ℤ => Work.KMTAreas.A7.cw φ j))
    (hφpacket : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize φ ξ ≠ 0 →
      ∃ θ : ℝ, |θ| ≤ δ ∧ (θ : Work.Analysis.IonescuWainger.Circle) = ξ)
    (f : ℤ → ℂ) (B : ℝ) (hf : ∀ y : ℤ, ‖f y‖ ≤ B) :
    Work.KMTAreas.A7.fiberOp ρ l m 0 (Work.KMTAreas.A7.Tex ρ l φ f)
      = Work.KMTAreas.A7.Tex ρ l φ f := by
  rw [gateIdentity ρ l m δ hδ hm hmsum hm1 hms hna φ hφ hφsum hφpacket 0 f B hf]
  funext y
  simp only [neg_zero, fourier_zero, one_mul, mul_one, sub_zero]
  rfl

/-- **The fibre splits as the translate of (input minus correction).**  This is the gate identity
`gateIdentity` (copied above from `Submission/Work/KMTAreas/A7Hi/fiberOp_Tex_eq_twisted.lean`,
which cannot be imported here — it imports this file) combined with the *linearity of `iwConv` in
the symbol*, `Work.KMTAreas.A7.FpieceEqTm.iwConv_sub_of_bounded`, and the algebraic split
`iwSymbolSet_twist_split`.

The four `Integrable`/`Summable` hypotheses are those of `iwConv_sub_of_bounded`; in the
application they are discharged for the concrete profiles by
`Work.KMTAreas.A7.kmt_MemLp_periodize_varphiNt`, `Work.KMTAreas.A7.kmt_summable_tmKernel_varphiNt`
and the shift identity `iwKernel_fourier_mul`. -/
theorem fiberOp_Tex_eq_sub_correction (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j))
    (hm1 : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ →
      Work.Analysis.IonescuWainger.periodize m θ = 1)
    (hms : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize m θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * δ))
    (hna : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l, α ≠ β → 8 * δ ≤ ‖α - β‖)
    (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (hφsum : Summable (fun j : ℤ => Work.KMTAreas.A7.cw φ j))
    (hφpacket : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize φ ξ ≠ 0 →
      ∃ θ : ℝ, |θ| ≤ δ ∧ (θ : Work.Analysis.IonescuWainger.Circle) = ξ)
    (n₀ : ℤ)
    (hint1 : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
      (Work.Analysis.IonescuWainger.periodize φ)) Work.Analysis.IonescuWainger.circleMeasure)
    (hint2 : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
      (fun ζ : Work.Analysis.IonescuWainger.Circle =>
        (1 - fourier (T := 1) (-n₀) ζ) *
          Work.Analysis.IonescuWainger.periodize φ ζ)) Work.Analysis.IonescuWainger.circleMeasure)
    (hκ1 : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) j‖))
    (hκ2 : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (fun ζ : Work.Analysis.IonescuWainger.Circle =>
          (1 - fourier (T := 1) (-n₀) ζ) *
            Work.Analysis.IonescuWainger.periodize φ ζ)) j‖))
    (f : ℤ → ℂ) (B : ℝ) (hf : ∀ y : ℤ, ‖f y‖ ≤ B) :
    Work.KMTAreas.A7.fiberOp ρ l m n₀ (Work.KMTAreas.A7.Tex ρ l φ f) =
      fun y : ℤ => Work.KMTAreas.A7.Tex ρ l φ f (y - n₀) -
          Work.Analysis.IWMultiplier.iwConv
            (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
            (fun ζ : Work.Analysis.IonescuWainger.Circle =>
              (1 - fourier (T := 1) (-n₀) ζ) *
                Work.Analysis.IonescuWainger.periodize φ ζ) f (y - n₀) := by
  rw [gateIdentity ρ l m δ hδ hm hmsum hm1 hms hna φ hφ hφsum hφpacket n₀ f B hf]
  funext y
  have hsub := Work.KMTAreas.A7.iwConv_sub_of_bounded
    (A := Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
    (Φ := Work.Analysis.IonescuWainger.periodize φ)
    (Ψ := fun ζ : Work.Analysis.IonescuWainger.Circle =>
      (1 - fourier (T := 1) (-n₀) ζ) * Work.Analysis.IonescuWainger.periodize φ ζ)
    (f := f) (B := B) hf hint1 hint2 hκ1 hκ2
  have hΦ : ((Work.Analysis.IonescuWainger.periodize φ : Work.Analysis.IonescuWainger.Circle → ℂ)
      - (fun ζ : Work.Analysis.IonescuWainger.Circle =>
          (1 - fourier (T := 1) (-n₀) ζ) * Work.Analysis.IonescuWainger.periodize φ ζ))
      = (fun ζ : Work.Analysis.IonescuWainger.Circle =>
          fourier (T := 1) (-n₀) ζ * Work.Analysis.IonescuWainger.periodize φ ζ) := by
    funext ζ
    simp only [Pi.sub_apply]
    ring
  rw [hΦ] at hsub
  rw [hsub]
  simp only [Work.KMTAreas.A7.Tex, Pi.sub_apply]


/-! ## The windows of a sequence, and the consumption of the packet-rotation crux

`Work.KMTAreas.A7Hi.PacketRotationResidueBoundLpGeTwo` (proved, axiom-clean) is the
residue-averaged packet-rotation bound for a family of `ℓ²` band-`δ` envelopes.  Here we record
the *algebra* that turns it into a statement about the fibre of the `mStarF`-cut:

* `windowEnvelopes m u : Circ → ℤ → ℂ` — the `α`-th `m`-window of `u`, written with the
  compensating modulation so that `winSynth A (windowEnvelopes m u) = fiberOpSet A m 0 u`;
* `winSynth_windowEnvelopes`, `winRot_windowEnvelopes` — the two synthesis identities.

Consequently the crux applied to the windows of the family `w n := if S n then Tex … f else 0`
gives exactly

  `‖residueLp p q (fun y n₀ => Vʳ_n (fiberOp ρ l₁ (mStarF U) n₀ (w n) y))‖_{ℓᵖ}
     ≤ C ‖Vʳ_n (fiberOp ρ l₁ (mStarF U) 0 (w n))‖_{ℓᵖ}`,

and the target's right-hand side is reached by the *range identity*
`fiberOp ρ l₁ (mStarF U) 0 (w n) = w n` (which holds for bounded `f` by
`Work.KMTAreas.A7.FiberOpWideCutEqSelf`).
-/

/-- `e(aα) · (e(bα) · z) = z` when `a + b = 0`: the cancellation of a character with its
inverse. -/
theorem fourier_cancel {a b : ℤ} (h : a + b = 0) (α : Circ) (z : ℂ) :
    fourier (T := 1) a α * (fourier (T := 1) b α * z) = z := by
  rw [← mul_assoc, ← fourier_add, h, fourier_zero, one_mul]

/-- **The `m`-windows of a sequence.**  The `α`-th window is the `m`-cut of the modulation of
`u` by `-α`, written with the compensating modulation `e(α ·)` so that the `winSynth` of the
family is the `n₀ = 0` fibre (see `winSynth_windowEnvelopes`). -/
noncomputable def windowEnvelopes (m : ℝ → ℂ) (u : ℤ → ℂ) : Circ → ℤ → ℂ :=
  fun α x => fourier (T := 1) x α *
    Work.KMTAreas.A7Rep.winModRep α
      (Work.KMTAreas.A7Rep.winConvRep m (Work.KMTAreas.A7Rep.winModRep (-α) u)) x

/-- The compensating modulation cancels: the envelopes are the `m`-windows of `u`. -/
theorem windowEnvelopes_eq (m : ℝ → ℂ) (u : ℤ → ℂ) (α : Circ) (x : ℤ) :
    windowEnvelopes m u α x
      = Work.KMTAreas.A7Rep.winConvRep m (Work.KMTAreas.A7Rep.winModRep (-α) u) x := by
  simp only [windowEnvelopes, Work.KMTAreas.A7Rep.winModRep]
  exact fourier_cancel (add_neg_cancel x) α _

/-- **The unrotated synthesis of the windows is the fibre at residue `0`.** -/
theorem winSynth_windowEnvelopes (A : Finset Circ) (m : ℝ → ℂ) (u : ℤ → ℂ) (x : ℤ)
    (hsumm : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j * u (x - j))) :
    winSynth A (windowEnvelopes m u) x = Work.KMTAreas.A7.fiberOpSet A m 0 u x := by
  rw [Work.KMTAreas.A7Rep.fiberOpSet_apply_eq_windowRotation A m 0 u x hsumm]
  simp only [winSynth, windowEnvelopes_eq]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [fourier_zero, one_mul]
  rfl

/-- **The rotated synthesis of the windows is the fibre at residue `-j`.** -/
theorem winRot_windowEnvelopes (A : Finset Circ) (m : ℝ → ℂ) (u : ℤ → ℂ) (j x : ℤ)
    (hsumm : Summable (fun j' : ℤ => Work.KMTAreas.A7.cw m j' * u (x - j'))) :
    winRot A (windowEnvelopes m u) j x = Work.KMTAreas.A7.fiberOpSet A m (-j) u x := by
  rw [Work.KMTAreas.A7Rep.fiberOpSet_apply_eq_windowRotation A m (-j) u x hsumm]
  simp only [winRot, windowEnvelopes, Work.KMTAreas.A7Rep.winModRep]
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  exact fourier_cancel (neg_add_cancel x) α _

/-- **The fibre `fiberOp` for the exact-height set is `fiberOpSet` at that set.** -/
theorem fiberOp_eq_fiberOpSet (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ) (u : ℤ → ℂ) :
    Work.KMTAreas.A7.fiberOp ρ l m n₀ u
      = Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l) m n₀ u :=
  rfl


/-! ## Reduction of the target to the packet-rotation crux

The two synthesis identities of the previous section turn the target's left-hand side into the
left-hand side of `Work.KMTAreas.A7Hi.PacketRotationResidueBoundLpGeTwo` (up to the reindexing
`n₀ ↦ -n₀` of the residue average), and its right-hand side into the variational norm of the
*range-`0`* fibre.  The remaining inputs are therefore (a) the *range identity*
`fiberOp ρ l₁ (mStarF U) 0 (w n) = w n` and (b) the crux for the concrete envelopes (with its `ℓ²`
band hypothesis), which for `1 < p ≤ 2` holds because `w n ∈ ℓᵖ ⊆ ℓ²`. -/

/-- `fourier q α = 1` when `q • α = 0`. -/
theorem fourier_qmul_eq_one {q : ℕ} {α : Work.Analysis.IonescuWainger.Circle} (hα : q • α = 0) :
    fourier (T := 1) (q : ℤ) α = 1 := by
  have h := Work.KMTAreas.A7Hi.fourier_neg_qmul_eq_one hα (-1)
  rwa [show -((q : ℤ) * (-1)) = (q : ℤ) by ring] at h

/-- `fiberOp` depends on `n₀` only modulo any `q` killing the frequency set. -/
theorem fiberOp_add_q (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (u : ℤ → ℂ) (q : ℕ)
    (hq : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l, q • α = 0) (n₀ : ℤ) :
    Work.KMTAreas.A7.fiberOp ρ l m (n₀ + (q : ℤ)) u = Work.KMTAreas.A7.fiberOp ρ l m n₀ u := by
  funext x
  simp only [Work.KMTAreas.A7.fiberOp, Work.KMTAreas.A7.arithCharSet]
  refine tsum_congr fun j => ?_
  have hshift : (n₀ + (q : ℤ)) - j = (n₀ - j) + (q : ℤ) := by ring
  rw [hshift]
  have hsum : (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
        fourier (T := 1) ((n₀ - j) + (q : ℤ)) α)
      = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
        fourier (T := 1) (n₀ - j) α := by
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [fourier_add, fourier_qmul_eq_one (hq α hα), mul_one]
  rw [hsum]

/-- **Reindexing a sum over `range q` by the reflection `n₀ ↦ (q - n₀) % q`.** -/
theorem sum_range_mod_neg (q : ℕ) (hq : 0 < q) (F : ℕ → ENNReal) :
    (∑ n₀ ∈ Finset.range q, F ((q - n₀) % q)) = ∑ s ∈ Finset.range q, F s := by
  have hmaps : ∀ n₀ ∈ Finset.range q, (q - n₀) % q ∈ Finset.range q := fun n₀ _ =>
    Finset.mem_range.mpr (Nat.mod_lt _ hq)
  have hinv : ∀ n₀ ∈ Finset.range q, (q - (q - n₀) % q) % q = n₀ := by
    intro n₀ hn₀
    have hn₀' : n₀ < q := Finset.mem_range.mp hn₀
    rcases Nat.eq_zero_or_pos n₀ with h0 | hpos
    · subst h0; simp
    · have h1 : (q - n₀) % q = q - n₀ := Nat.mod_eq_of_lt (by omega)
      rw [h1, Nat.sub_sub_self (by omega), Nat.mod_eq_of_lt hn₀']
  have hinj : ∀ a ∈ Finset.range q, ∀ b ∈ Finset.range q,
      (q - a) % q = (q - b) % q → a = b := by
    intro a ha b hb hab
    have h1 : (q - (q - a) % q) % q = (q - (q - b) % q) % q := by rw [hab]
    rwa [hinv a ha, hinv b hb] at h1
  rw [← Finset.sum_image hinj]
  refine Finset.sum_congr ?_ fun x _ => rfl
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨n₀, hn₀, rfl⟩ := Finset.mem_image.mp hx
    exact hmaps n₀ hn₀
  · rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-- **The residue average is invariant under the reflection of the residue.** -/
theorem residueLp_mod_neg (p : ℝ) (q : ℕ) (hq : 0 < q) (W : ℤ → ℕ → ENNReal) :
    Work.KMTAreas.A7.residueLp p q W
      = Work.KMTAreas.A7.residueLp p q (fun y n₀ => W y ((q - n₀) % q)) := by
  funext x
  simp only [Work.KMTAreas.A7.residueLp]
  rw [show (∑ n₀ ∈ Finset.range q, ENNReal.rpow (W x n₀) p)
      = ∑ n₀ ∈ Finset.range q, ENNReal.rpow (W x ((q - n₀) % q)) p from
    (sum_range_mod_neg q hq (fun s => ENNReal.rpow (W x s) p)).symm]

/-- **Assembly: the crux plus the range identity give the fibre variational sampling bound.**

`hcrux` is the conclusion of the packet-rotation crux for the concrete envelopes
`windowEnvelopes (mStarF U) (w n)`; `hrange` is the range identity; `hsumm` is the summability
needed by the two synthesis identities.

**Warning (session 8).**  The hypothesis `hrange` (the *range identity* for an arbitrary `f`) is
**FALSE** — a child produced a counterexample at `ρ = 1/2`, `l = 2` with `f` growing like
`e^{|k|}/|ĉ_{6+12k}|` on the residue class `6 (12)`, where the two sides of the identity are
`tsum`s in different summability regimes (see `NOTES_A7Hi_FiberVarSampling_SESSION8.md` §2).  This
theorem is therefore only a *blueprint* of how the crux is consumed; the usable form of the last
step is the norm-level statement `‖Vʳ(fiberOp ρ l₁ (mStarF U) 0 (w n))‖ ≤ C‖Vʳ(w)‖`, which the
counterexample does **not** refute. -/
theorem fiberVarSampling_of_windowCrux (ρ : ℝ) (l₁ : ℕ) (q : ℕ) (hq : 0 < q)
    (hqnsmul : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁, q • α = 0)
    (U : ℕ) (p : ℝ) (r : NNReal) (C : ℝ)
    (w : ℕ → ℤ → ℂ)
    (hsumm : ∀ (n : ℕ) (x : ℤ), Summable (fun j : ℤ =>
      Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j * w n (x - j)))
    (hrange : ∀ n : ℕ, Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U) 0 (w n) = w n)
    (hcrux : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q
        (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          winRot (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁)
            (fun α : Circ => windowEnvelopes (Work.KMTAreas.A7.mStarF U) (w n) α)
            (n₀ : ℤ) y)) x) (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            winSynth (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁)
              (fun α : Circ => windowEnvelopes (Work.KMTAreas.A7.mStarF U) (w n) α) x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q
        (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U) (n₀ : ℤ) (w n) y)) x)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  set A : Finset Circ := Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ with hA
  have hq'A : ∀ α ∈ A, q • α = 0 := fun α hα => hqnsmul α (by simpa [hA] using hα)
  -- the crux's right-hand side is the target's right-hand side
  have hR : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        winSynth A (fun α : Circ => windowEnvelopes (Work.KMTAreas.A7.mStarF U) (w n) α) x))
      = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x) := by
    funext x
    refine congrArg (fun v => PointwiseErgodicTheorems.variationalNorm r v) (funext fun n => ?_)
    rw [winSynth_windowEnvelopes A (Work.KMTAreas.A7.mStarF U) (w n) x (hsumm n x)]
    rw [← fiberOp_eq_fiberOpSet, hrange n]
  -- the target's residue average is the crux's residue average
  have hL : (fun x : ℤ => Work.KMTAreas.A7.residueLp p q
        (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U) (n₀ : ℤ) (w n) y)) x)
      = fun x : ℤ => Work.KMTAreas.A7.residueLp p q
        (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          winRot A (fun α : Circ => windowEnvelopes (Work.KMTAreas.A7.mStarF U) (w n) α)
            (n₀ : ℤ) y)) x := by
    funext x
    rw [residueLp_mod_neg p q hq]
    -- the `winRot` family is the fibre at `-n₀`
    have hwin : ∀ n₀ : ℕ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          winRot A (fun α : Circ => windowEnvelopes (Work.KMTAreas.A7.mStarF U) (w n) α)
            (n₀ : ℤ) x)
        = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U) (-(n₀ : ℤ)) (w n) x) := by
      intro n₀
      refine congrArg (fun v => PointwiseErgodicTheorems.variationalNorm r v) (funext fun n => ?_)
      rw [winRot_windowEnvelopes A (Work.KMTAreas.A7.mStarF U) (w n) (n₀ : ℤ) x (hsumm n x),
        fiberOp_eq_fiberOpSet]
    -- the fibre is invariant under subtracting the period `q`
    have hper : ∀ n₀ : ℕ, n₀ < q → PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U)
            (((q - n₀) % q : ℕ) : ℤ) (w n) x)
        = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U) (-(n₀ : ℤ)) (w n) x) := by
      intro n₀ hn₀
      refine congrArg (fun v => PointwiseErgodicTheorems.variationalNorm r v) (funext fun n => ?_)
      rcases Nat.eq_zero_or_pos n₀ with h0 | hpos
      · subst h0
        simp
      · have h2 : (q - n₀) % q = q - n₀ := Nat.mod_eq_of_lt (by omega)
        have hK : -(n₀ : ℤ) = (((q - n₀) % q : ℕ) : ℤ) - (q : ℤ) := by
          rw [h2]; omega
        rw [hK]
        have h := fiberOp_add_q ρ l₁ (Work.KMTAreas.A7.mStarF U) (w n) q hq'A
          ((((q - n₀) % q : ℕ) : ℤ) - (q : ℤ))
        rw [show ((((q - n₀) % q : ℕ) : ℤ) - (q : ℤ)) + (q : ℤ)
            = (((q - n₀) % q : ℕ) : ℤ) by ring] at h
        exact congrFun h x
    have hterm : ∀ n₀ ∈ Finset.range q,
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U)
              (((q - n₀) % q : ℕ) : ℤ) (w n) x)
          = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            winRot A (fun α : Circ => windowEnvelopes (Work.KMTAreas.A7.mStarF U) (w n) α)
              (n₀ : ℤ) x) := by
      intro n₀ hn₀
      exact (hper n₀ (Finset.mem_range.mp hn₀)).trans (hwin n₀).symm
    have hsum_eq : (∑ n₀ ∈ Finset.range q, ENNReal.rpow (PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U)
            (((q - n₀) % q : ℕ) : ℤ) (w n) x)) p)
        = ∑ n₀ ∈ Finset.range q, ENNReal.rpow (PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => winRot A
            (fun α : Circ => windowEnvelopes (Work.KMTAreas.A7.mStarF U) (w n) α)
            (n₀ : ℤ) x)) p := by
      refine Finset.sum_congr rfl fun n₀ hn₀ => ?_
      rw [hterm n₀ hn₀]
    simp only [Work.KMTAreas.A7.residueLp]
    rw [hsum_eq]
  rw [hL, ← hR]
  exact hcrux

/-! ## The `f`-side assembly from the narrow-bump fibre bound -/

/-- **The assembly of the large-scale `f`-side fibre estimate from the narrow-bump fibre bound.**
`Hfib` is the shape of `Work.KMTAreas.A7Hi.FiberOpVarUniformLpNoLossClean` (the `Vʳ`-valued `ℓᵖ`
bound for the fibre `fiberOp ρ l (mStarF u) n₀` of a narrow bump, uniform in the height, the
residue and the input family); the conclusion is `Work.KMTAreas.A7.FiberVarSamplingLargeLoss`,
verbatim.

Only two analytic inputs are used: the fibre bound itself, for large
`L := max (max l₁ l₂) (max k₁ k₂)` — where `GoodMajorArcs ρ Cρ l₁ (-(2 · uScale ρ L))` follows
from `l₁ ≤ L` and `L ≥ Bnar` by `goodMajorArcs_mStargF` — and the crude Young fibre bound
`fiberOpVarNonFareyBounded` for bounded `L`.  The residue aggregation is the Minkowski step
`eLpNorm_residueLp_le` over the `q = arithQ ρ (max l₁ l₂)` residues. -/
theorem largeLoss_of_fiberBound
    (Hfib : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ →
      ∀ (r : NNReal), 2 < r →
      ∃ C : ℝ, 0 < C ∧ ∃ Cρ : ℝ, 0 < Cρ ∧
        ∀ (l u : ℕ) (hgm : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(2 * (u : ℤ))))
          (n₀ : ℤ) (v : ℕ → ℤ → ℂ),
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l (Work.KMTAreas.A7.mStarF u) n₀ (v n) x))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n x)) p
              MeasureTheory.Measure.count) :
    Work.KMTAreas.A7.FiberVarSamplingLargeLoss := by
  refine ⟨1, zero_le_one, ?_⟩
  intro ρ hρ hρ1 p hp hptop r hr
  have hpne : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hp0 : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hpne (ne_of_lt hptop)
  have hpe : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hptop)
  obtain ⟨Cfib, hCfib, Cρ, hCρ, Hcore⟩ := Hfib ρ hρ hρ1 p hp hptop r hr
  obtain ⟨Bnar, hBnar⟩ := Work.KMTAreas.A7Hi.goodMajorArcs_mStargF ρ hρ 1 (le_refl 1) Cρ hCρ
  obtain ⟨Cnon, hCnon, Hnon⟩ :=
    Work.KMTAreas.A7.fiberOpVarNonFareyBounded r hr ρ hρ hρ1 p hp hptop (fun _ => max Bnar 1)
  refine ⟨max (max Cnon Cfib) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro l₁ l₂ k₁ k₂ t f N S _ ht hfarey hstrict hna
  set L : ℕ := max (max l₁ l₂) (max k₁ k₂) with hLdef
  set U : ℕ := Work.KMTAreas.A7.uScale ρ L with hUdef
  set w : ℕ → ℤ → ℂ :=
    (fun n => if S n then Work.KMTAreas.A7.Tex ρ l₁ (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f
      else 0) with hwdef
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hqdef
  set RHS : ENNReal := MeasureTheory.eLpNorm (fun x : ℤ =>
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x)) p MeasureTheory.Measure.count
    with hRHSdef
  have hper : ∀ n₀ : ℤ, MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U) n₀ (w n) x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (max (max Cnon Cfib) 1) * RHS := by
    intro n₀
    by_cases hcase : (L : ℝ) ≤ ((max Bnar 1 : ℕ) : ℝ)
    · have hLe : L ≤ max Bnar 1 := by exact_mod_cast hcase
      refine (Hnon l₁ l₂ k₁ k₂ ?_ n₀ w).trans ?_
      · exact hLe
      · refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
        exact le_trans (le_max_left Cnon Cfib) (le_max_left _ _)
    · push_neg at hcase
      have hBL : Bnar ≤ L := by
        have h1 : max Bnar 1 < L := by exact_mod_cast hcase
        omega
      have hl₁L : l₁ ≤ L := by rw [hLdef]; omega
      have hgm : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(2 * (U : ℤ))) := by
        have h := hBnar L l₁ hl₁L hBL
        simp only [Nat.cast_one, one_mul, ← hUdef] at h
        exact h
      refine (Hcore l₁ U hgm n₀ w).trans ?_
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
      exact le_trans (le_max_right Cnon Cfib) (le_max_left _ _)
  have hres := Work.KMTAreas.A7.eLpNorm_residueLp_le (p := p.toReal) hp0
    (W := fun x n₀ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U) n₀ (w n) x))
    (C := ENNReal.ofReal (max (max Cnon Cfib) 1) * RHS) (q := q)
    (by intro n₀ hn₀; rw [hpe]; exact hper n₀)
  rw [hpe] at hres
  refine hres.trans ?_
  have hloss : (1 : ENNReal) ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg 1 ρ zero_le_one hρ.le l₁ l₂ k₁ k₂)
  calc ENNReal.ofReal (max (max Cnon Cfib) 1) * RHS
      ≤ ENNReal.ofReal (max (max Cnon Cfib) 1) *
          (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂) * RHS) := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        exact le_mul_of_one_le_left bot_le hloss
    _ = (ENNReal.ofReal (max (max Cnon Cfib) 1) *
          ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂)) * RHS := by
        rw [mul_assoc]
    _ = ENNReal.ofReal (max (max Cnon Cfib) 1 *
          Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂) * RHS := by
        rw [← ENNReal.ofReal_mul (by positivity)]

/-- **The narrow-bump fibre bound from the sharp kernel-mass bound.**  `Hmass` is the statement of
`Work.KMTAreas.A7Hi.FiberOpKernelMassBound` (the `ℓ¹`-mass of the fibre kernel
`j ↦ (∑_{α ∈ iwArithFreqsNew ρ l} e(α(n₀-j))) · cw (mStarF u) j` is bounded, uniformly in `l`, `u`
and `n₀`, whenever the bump is narrow in the quantitative sense `GoodMajorArcs ρ Cρ l (-(2u))`).
The conclusion is the fibre bound `Work.KMTAreas.A7Hi.FiberOpVarUniformLpNoLossClean`.

The proof is the proved pair `Work.KMTAreas.A7.fiberOpVarYoungExact` (Young's inequality for the
variational norm, unconditional) and
`Work.KMTAreas.A7.eLpNorm_varNorm_fiberOp_le_of_mass` (which turns the kernel-mass bound into the
`ℓᵖ(ℤ; Vʳ)` bound); see also `Work.KMTAreas.A7Hi.variationalNorm_tsum_le`. -/
theorem fiberOpVarUniformLpNoLoss_of_kernelMass
    (Hmass : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ Cρ : ℝ, 0 < Cρ ∧
        ∀ (l u : ℕ) (hgm : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(2 * (u : ℤ))))
          (n₀ : ℤ),
          (∑' j : ℤ, ‖(∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
              fourier (T := 1) (n₀ - j) α) * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖)
            ≤ C)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧ ∃ Cρ : ℝ, 0 < Cρ ∧
      ∀ (l u : ℕ) (hgm : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(2 * (u : ℤ))))
        (n₀ : ℤ) (v : ℕ → ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l (Work.KMTAreas.A7.mStarF u) n₀ (v n) x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n x)) p
            MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, Cρ, hCρpos, H⟩ := Hmass ρ hρ hρ1
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hpR1 : (1 : ℝ) ≤ p.toReal := by
    have h1 : ((1 : ENNReal)).toReal ≤ p.toReal :=
      ENNReal.toReal_mono (ne_of_lt hptop) (le_of_lt hp)
    simpa using h1
  have hpe : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hptop)
  refine ⟨C, hCpos, Cρ, hCρpos, ?_⟩
  intro l u hgm n₀ v
  set kk : ℤ → ℂ := fun j => (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      fourier (T := 1) (n₀ - j) α) * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j with hkk
  have hsum : Summable (fun j : ℤ => ‖kk j‖) := by
    have hcard : (0 : ℝ) ≤
        ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l).card : ℝ) := Nat.cast_nonneg _
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      (((summable_cw_mStarF u).norm).mul_left
        ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l).card : ℝ))
    rw [hkk]
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
            fourier (T := 1) (n₀ - j) α‖
        ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
            ‖fourier (T := 1) (n₀ - j) α‖ := norm_sum_le _ _
      _ = ∑ _α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [fourier_apply]
          exact _root_.Circle.norm_coe _
      _ = ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l).card : ℝ) := by simp
  have hmassENN : (∑' j : ℤ, ‖kk j‖ₑ) ≤ ENNReal.ofReal C := by
    have h1 : (∑' j : ℤ, ‖kk j‖ₑ) = ENNReal.ofReal (∑' j : ℤ, ‖kk j‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j : ℤ => norm_nonneg _) hsum]
      exact tsum_congr (fun j => (ofReal_norm (kk j)).symm)
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (H l u hgm n₀)
  have hkey := Work.KMTAreas.A7.eLpNorm_varNorm_fiberOp_le_of_mass r hr1 ρ l u n₀ v hCpos.le
    hpR1 hmassENN
  rw [← hpe]
  exact hkey

/-- **`ℓᵖ(ℤ) ⊆ ℓ²(ℤ)` for `p ≤ 2`** (counting measure): every `ℓᵖ`-function is `ℓ²`.  This is the
"`ℓ²` fact" of the corrected core's wiring (`FiberVarSamplingLargeLossMemLp`, `p ≤ 2`): it supplies
the `Memℓp · 2` hypothesis of the crux for the concrete input. -/
theorem MemLpTwoOfMemLpLeTwo (f : ℤ → ℂ) (p : ENNReal) (hp : 0 < p) (hp2 : p ≤ 2)
    (hptop : p < ⊤) (hf : MeasureTheory.MemLp f p MeasureTheory.Measure.count) :
    Memℓp f 2 := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 (ne_of_lt hptop)
  have hpR2 : p.toReal ≤ 2 := by
    have h := ENNReal.toReal_mono (by norm_num : (2 : ENNReal) ≠ ⊤) hp2
    simpa using h
  obtain ⟨C, hC⟩ := Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top hp0 hf.eLpNorm_lt_top
  have hsum := Work.KMTAreas.A7Hi.summable_of_eLpNorm_ne_top hp0 hptop hf.eLpNorm_lt_top
  have h2sum : Summable (fun i : ℤ => ‖f i‖ ^ (2 : ℝ)) := by
    have hC1 : ∀ i : ℤ, ‖f i‖ ≤ max C 1 := fun i => le_trans (hC i) (le_max_left _ _)
    refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (norm_nonneg _) _) (fun i => ?_)
      (hsum.mul_left ((max C 1) ^ (2 - p.toReal)))
    rcases eq_or_ne ‖f i‖ 0 with h0 | h0
    · rw [h0]
      simp [Real.zero_rpow (ne_of_gt hpR), Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
    · have hpos : 0 < ‖f i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have h2 : ‖f i‖ ^ (2 - p.toReal) ≤ (max C 1) ^ (2 - p.toReal) :=
        Real.rpow_le_rpow (norm_nonneg _) (hC1 i) (sub_nonneg.mpr hpR2)
      conv_lhs => rw [show (2 : ℝ) = (2 - p.toReal) + p.toReal from by ring, Real.rpow_add hpos]
      exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg _) p.toReal)
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  exact h2sum

/-- **The band and `ℓ²` facts for the concrete `Tex`-family** (the input of the crux on the window
envelopes).  For `f ∈ ℓ²`, the exact-height projection `Tex ρ l₁ (φ_{N,t}) f` is `ℓ²` and its circle
Fourier support is contained in the union of the arcs of radius `δ = 2^{k₁}/N`
(`= 2^{(k₁:ℝ) - logN N}`) around the exact-height arithmetic frequencies.  The radius is the packet
band; the Shannon condition `δ·arithQ ρ (max l₁ l₂) ≤ 1/8` that the crux needs is then *literally*
the Farey hypothesis of the target. -/
theorem tex_varphiNt_memLpTwo_freqSupport (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (l₁ k₁ N : ℕ) (t : ℝ) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ∃ hh : Memℓp (Work.KMTAreas.A7.Tex ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) f) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTAreas.A7.Tex ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) f) hh
        (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
          Work.BourgainPlan.IonescuWainger.arcSet α
            ((2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) := by
  have hsum := (Work.KMTAreas.A7.varphiNt_IW_facts ρ l₁ N k₁ t).2.2
  refine Work.KMTAreas.A7.hasFreqSupport_Tex_of_memℓp ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) _
    (Work.KMTAreas.A7.integrable_varphiNt N k₁ t)
    (Work.KMTAreas.A7.cw_varphiNt_summable N k₁ t) ?_ f hf
  intro ξ hξ
  obtain ⟨θ, hθ, hθξ⟩ := Work.KMTPlan.A6.periodize_ne_zero
    (fun x => Work.KMTAreas.A7.varphiNt_support N k₁ t x) hsum hξ
  exact ⟨θ, hθ, by rw [hθξ, zero_add]⟩

/-- **The corrected (`paper`-shaped) core of the fibre sampling estimate.**  This is
`Work.KMTAreas.A7.FiberVarSamplingLargeLoss` verbatim with the one hypothesis the source carries and
the workspace's formulation dropped: the input lies in `ℓᵖ` (`MemLp f p.toReal count`).

This is the version the §9 route proves: `crux` (PROVED) + the tame range identity
(`fiberOp_mStarF_Sclip_eq_self_tame`, below) + the window-envelope band/`ℓ²` facts.  The
*un-hypothesised* version is strictly stronger than the source and its natural intermediates are
false (see `NOTES_A7Hi_FiberVarSampling_SESSION9.md` §7-§10). -/
def FiberVarSamplingLargeLossMemLp : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ → ∀ (r : NNReal), 2 < r →
      ∃ C : ℝ, 0 < C ∧
        ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          (∀ n : ℕ, (2 : ℝ) ^ k₁ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) * 8
            ≤ (N n : ℝ)) →
          (∀ n : ℕ, k₁ + 2 * Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) + 1
            ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
          Work.Analysis.IonescuWainger.NonAliasing
            (-(2 * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) →
          MeasureTheory.MemLp f p MeasureTheory.Measure.count →
          MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                Work.KMTAreas.A7.fiberOp ρ l₁
                  (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
                    (max (max l₁ l₂) (max k₁ k₂)))) n₀
                  (if S n then Work.KMTAreas.A7.Tex ρ l₁
                    (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) y)) x)
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₁
                  (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) x))
              p MeasureTheory.Measure.count

/-- The fibre variational sampling estimate (paper §8, `form-1` + the quantitative Shannon/aliasing transfer): the `ℓ^p` norm over `x` of the residue average over `n₀ < arithQ ρ (max l₁ l₂)` of the variational norms of the fibres of `Hcl` is bounded by the `ℓ^p` norm of the variational norm of `Hcl`, with the loss `lossWeight A ρ l₁ l₂ k₁ k₂`.  Import `Submission.Work.KMTAreas.A7.LargeInterface` for `fiberOp`, `Hcl`, `residueLp`, `arithQ`, `mStarF`, `uScale`, `lossWeight`.  The existing file `Submission/Work/KMTAreas/A7/fiberVarSampling.lean` contains a complete proof of this statement from the analytic core `Work.KMTAreas.A7.fiberOpVarSamplingCoreTex` (the core is `fiberVarSampling` for an arbitrary scale sequence `N` in the main regime and above `splitCut`, with an arbitrary clipping predicate); fill the core in your own file (do NOT import `Submission.Work.KMTAreas.A7.fiberOpVarSamplingCoreTex` in the final proof, as its `sorry` would poison the axiom check).  See `NOTES_A7_fiberVarSampling_SESSION.md` and `NOTES_A7_fiberVarSampling_SESSION2.md`. -/
theorem FiberVarSampling (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
                    (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
                      (max (max l₁ l₂) (max k₁ k₂)))) n₀
                    (Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y)) x) p
              MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p
                  MeasureTheory.Measure.count := by sorry

end Work.KMTAreas.A7Hi

/-
## CORRECTION (later in the same session) to the status lists above

* `Submission/Work/KMTAreas/A7Hi/FiberOpUniformLp.lean` has **no `sorry` but does not compile**
  (errors near lines 201, 360 and 405: a `mul_one` rewrite shape, a stuck `IsOrderedRing` instance,
  and an `iwConv`-difference shape).  Do not import it and do not cite it as proved; the usable
  Ionescu–Wainger ingredients are `Work.KMTContract.AreaA1` (proved, axiom-clean) together with
  `Work.KMTAreas.A7.opArc_iwArithFreqs_endpoint`.
* Proved, sorry-free and axiom-clean in this area (checked): `LinVar`, `DilVar`, `LinVarG`,
  `LowpassVar`, `LnatBoundOnBad`, `eLpNormResidueLpEq`, `residueLpVariationalShift`,
  `SqSumAmplificationLp` (the corrected Khintchine/MZ amplification; the version first requested,
  `SqSumAmplification`, is FALSE — see `SqSumAmplification_counterexample.lean`), `BadPart`, and
  `FiberOpCutBoundLevelOne` (kernel-mass bound ⟹ cut bound, at *every* level `ρ, l`).
* `Submission/Work/KMTAreas/A7Hi/fiberOpGateBound.lean` holds the *correct* remaining statement of
  the crux (the cut as a gate on the band, symbol-level), as a `sorry` stub awaiting proof; the
  companion level-one instance `FiberOpCutBoundLevelOneBump` is in flight.
* The `O(B)` fibre-kernel-mass bound is FALSE and must not be requested: the level character is
  `q₀`-periodic with period-average `#P_{≤l}` while `8δ ≤ 1/q₀` makes the bump sample many periods,
  so the fibre kernel mass is `≳ #P_{≤l}·B`.  See the comment block in
  `Submission/Work/KMTAreas/A7Hi/FiberOpCutBoundLevelOne.lean` for the record and the numerics.
-/
