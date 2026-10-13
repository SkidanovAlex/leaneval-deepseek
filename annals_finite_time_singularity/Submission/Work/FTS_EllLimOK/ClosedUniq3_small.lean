/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ClosedUniq3_small` — order-`3` jet uniqueness in the Fatou package class

Target: `Work.FTS_EllLimOK.SmallUniq3`, i.e. there is `α₁ > 0` such that for every `α ∈ (0, α₁]`
and every constant `Ce`, two order-`3` jet-cluster-limits (`IsJetLimit3 α E fn f Ψ`,
`IsJetLimit3 α E fn f Ψ'`) of the same operator `E` along the same sequence have the same `C³`
jets on the open quadrant.

## Reduction (the mathematical content)

Both `Ψ` and `Ψ'` carry `FatouPkg α f ·`, hence both solve the *same* elliptic law
`IsBslSolPos α f ·` on the open quadrant, are `C³` there, and satisfy the weighted
`ℋ⁰`/`L²` memberships.  Their difference `δ = Ψ - Ψ'` therefore satisfies

* `bslOp α δ = 0` on `Qd` (linearity of the law);
* the Dirichlet **values** `δ z 0 = 0`, `δ z (π/2) = 0` for `z ≥ 0`;
* the decay clause `δ z θ → 0` as `z → ∞` for `θ ∈ Iθ`;
* `ContDiffOn ℝ 3` on `Qd`;
* the memberships `HkMem α 0` of `δ`, `pth δ`, `pthIter 2 δ`, `z² pzIter 2 δ`, `δ/cos θ`,
  `L2Mem` of the last three, and `ZDecay δ`.

So `SmallUniq3` follows from the **uniqueness of the trivial solution of the homogeneous
problem in the Fatou class**, restricted to the open quadrant.  The route (see
`NOTES_closedUniq3.md` next to this file, and the delegated slice lemmas in
`Submission/Work/FTS_EllLimOK/SliceTrace/`) is:

1. *Slice traces.*  For each `z > 0` the slice `θ ↦ δ z θ` extends to the closed interval: the
   memberships `HkMem α 0 (pthIter 2 δ)` (weight `sin(2θ)^{-η}`, `η = 99/100 < 1`) give
   `∂_θθδ ∈ L¹`, hence the *derivative* of the slice is absolutely continuous with a finite
   one-sided limit at `0` and at `π/2`; the memberships `HkMem α 0 (pth δ)` (weight
   `sin(2θ)^{-γ}`, `γ = 1 + α/10 > 1`) then force both one-sided derivative limits to be `0`
   (`SliceTrace.deriv_tendsto_zero_at_zero`, `…_at_pi_div_two`); `pth δ ∈ L¹` gives the value
   limits (`SliceTrace.tendsto_self_at_zero`, and its `π/2` mirror).
2. *Angular moment.*  Integrating the equation against `sin θ cos²θ` — an element of the kernel
   of the formal adjoint of `Lzero` (whose boundary terms vanish since `sinθcos²θ` vanishes at
   both endpoints) — shows that `F_*^(δ)(z) = ∫_θ δ z θ sinθcos²θ dθ` solves the Euler ODE
   `α²z²F'' + α(5+α)zF' = 0` weakly on `(0,∞)`.  Its solutions are `c₁ + c₂z^{-5/α}`; the decay
   clause kills `c₁`, and the membership `∫ (F_*)^2 z^{-4} < ∞` (a Cauchy–Schwarz consequence of
   `HkMem α 0 δ`) kills `c₂`, since `∫₀ z^{-10/α-4} = ∞`.  Hence `F_*^δ ≡ 0`.
3. *Angular gap.*  With the slices orthogonal to `sin θ cos²θ`, the slice Poincaré gap
   (`coercive_slice_fts`) gives `angQ(f) = ∫f'² - 6∫f² + (1/2)∫(f/cos)² ≥ 0`.
4. *`θ`-energy.*  The `θ`-integration by parts `∫(Lzero δ)δ = angQ(δ_slice) + boundary` has
   boundary term `-(δ δ')` at `θ = 0⁺` (the `π/2` term is killed by `cos π/2 = 0`), which
   **vanishes** by step 1 (the derivative trace is `0`).  With `Φ(z) = ∫_θ (δ z θ)² dθ` the
   equation therefore gives `(α²z²/2)Φ'' + (α(5+α)z/2)Φ' ≥ 0` on `(0,∞)`.
5. *Conclusion.*  `Φ ≥ 0`, `Φ` is integrable (`L2Mem (δ/cos θ)`), `Φ'` is bounded near `0` (step
   1: the slices are bounded on compact `z`-intervals), so
   `EllipticEst.phi_eq_zero_of_euler_gap` gives `Φ ≡ 0`, i.e. `δ = 0` a.e. on `Qd`; by continuity
   (`ContDiffOn ℝ 3`) `δ ≡ 0` on `Qd`, hence the jets of `Ψ` and `Ψ'` agree there.

Steps 2–5 are the remaining work; the slice-trace facts of step 1 are delegated (see the
`SliceTrace/` directory).  The lemmas below are the bookkeeping part: the level-`0` membership
integrand of a difference is dominated by the sum of the integrands, which is what lets all the
memberships of `FatouPkg` be transferred to `δ = Ψ - Ψ'`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.UniqFatou
import Submission.Work.FTS_EllLimOK.Locality
import Submission.Work.FTS_EllLimOK.HkMem_zero_diff
import Submission.Work.FTS.H2.STBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The level-`0` membership integrand of a difference -/

/-- At level `0` the `HkIntegrand` is a single square,
`(g z θ · w z / sin(2θ)^{η/2})²` (the mixed sum is empty). -/
theorem hkIntegrand_zero_eq' (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp

/-- Pointwise, the level-`0` `HkIntegrand` of a difference is dominated by the sum of the two
level-`0` `HkIntegrand`s.  (At level `0` the `HkIntegrand` is a single square,
`(g z θ · w z / sin(2θ)^{η/2})²`.) -/
theorem hkIntegrand_zero_sub_le (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 (fun z θ => f z θ - g z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α 0 f z θ + 2 * Work.Spaces.HkIntegrand α 0 g z θ := by
  rw [hkIntegrand_zero_eq', hkIntegrand_zero_eq', hkIntegrand_zero_eq']
  nlinarith [sq_nonneg (f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
      + g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))]

/-- Pointwise domination of the squared level-`0` integrand of `L2Sq` for a difference. -/
theorem l2Integrand_sub_le (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    ((f z θ - g z θ)) ^ 2 ≤ 2 * (f z θ) ^ 2 + 2 * (g z θ) ^ 2 := by
  nlinarith [sq_nonneg (f z θ + g z θ)]

/-- **`HkMem α 0` is inherited by differences** (at level `0`, with the natural measurability
hypotheses). -/
theorem HkMem_zero_sub {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) (hg : Work.Spaces.HkMem α 0 g)
    (hm : ∀ z ∈ Work.Spaces.Iz, AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 0 (fun z θ => f z θ - g z θ) z θ)
      (volume.restrict Work.Spaces.Iθ))
    (hmz : AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => f z θ - g z θ) z θ)
      (volume.restrict Work.Spaces.Iz)) :
    Work.Spaces.HkMem α 0 (fun z θ => f z θ - g z θ) := by
  constructor
  · intro z hz
    refine MeasureTheory.Integrable.mono'
      (((hf.1 z hz).const_mul 2).add ((hg.1 z hz).const_mul 2)) (hm z hz) ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hkIntegrand_zero_eq']; exact sq_nonneg _)]
    exact hkIntegrand_zero_sub_le α f g z θ
  · refine MeasureTheory.Integrable.mono'
      ((hf.2.const_mul 2).add (hg.2.const_mul 2)) hmz ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 0 (fun z θ => f z θ - g z θ) z θ) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono'
        (((hf.1 z hz).const_mul 2).add ((hg.1 z hz).const_mul 2)) (hm z hz) ?_
      filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hkIntegrand_zero_eq']; exact sq_nonneg _)]
      exact hkIntegrand_zero_sub_le α f g z θ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (MeasureTheory.integral_nonneg fun θ => by
        rw [hkIntegrand_zero_eq']; exact sq_nonneg _)]
    have h2 : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => f z θ - g z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
          (2 * Work.Spaces.HkIntegrand α 0 f z θ
            + 2 * Work.Spaces.HkIntegrand α 0 g z θ) :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => by
          rw [hkIntegrand_zero_eq']; exact sq_nonneg _)
        (((hf.1 z hz).const_mul 2).add ((hg.1 z hz).const_mul 2))
        (Filter.Eventually.of_forall fun θ => hkIntegrand_zero_sub_le α f g z θ)
    have h3 : (∫ θ in Work.Spaces.Iθ,
          2 * Work.Spaces.HkIntegrand α 0 f z θ + 2 * Work.Spaces.HkIntegrand α 0 g z θ)
        = 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) := by
      rw [MeasureTheory.integral_add ((hf.1 z hz).const_mul 2) ((hg.1 z hz).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    calc (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => f z θ - g z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
          (2 * Work.Spaces.HkIntegrand α 0 f z θ
            + 2 * Work.Spaces.HkIntegrand α 0 g z θ) := h2
      _ = 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) := h3

/-- **`L2Mem` is inherited by differences** (with the natural measurability hypotheses). -/
theorem L2Mem_sub {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.L2Mem f) (hg : Work.Spaces.L2Mem g)
    (hm : ∀ z ∈ Work.Spaces.Iz, AEStronglyMeasurable
      (fun θ => ((f z θ - g z θ)) ^ 2) (volume.restrict Work.Spaces.Iθ))
    (hmz : AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, ((f z θ - g z θ)) ^ 2)
      (volume.restrict Work.Spaces.Iz)) :
    Work.Spaces.L2Mem (fun z θ => f z θ - g z θ) := by
  constructor
  · intro z hz
    refine MeasureTheory.Integrable.mono'
      (((hf.1 z hz).const_mul 2).add ((hg.1 z hz).const_mul 2)) (hm z hz) ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact l2Integrand_sub_le f g z θ
  · refine MeasureTheory.Integrable.mono'
      ((hf.2.const_mul 2).add (hg.2.const_mul 2)) hmz ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have h1 : MeasureTheory.IntegrableOn (fun θ => ((f z θ - g z θ)) ^ 2) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono'
        (((hf.1 z hz).const_mul 2).add ((hg.1 z hz).const_mul 2)) (hm z hz) ?_
      filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact l2Integrand_sub_le f g z θ
    have h2 : (∫ θ in Work.Spaces.Iθ, ((f z θ - g z θ)) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (2 * (f z θ) ^ 2 + 2 * (g z θ) ^ 2) :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)
        (((hf.1 z hz).const_mul 2).add ((hg.1 z hz).const_mul 2))
        (Filter.Eventually.of_forall fun θ => l2Integrand_sub_le f g z θ)
    have h3 : (∫ θ in Work.Spaces.Iθ, 2 * (f z θ) ^ 2 + 2 * (g z θ) ^ 2)
        = 2 * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
          + 2 * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := by
      rw [MeasureTheory.integral_add ((hf.1 z hz).const_mul 2) ((hg.1 z hz).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
    calc (∫ θ in Work.Spaces.Iθ, ((f z θ - g z θ)) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (2 * (f z θ) ^ 2 + 2 * (g z θ) ^ 2) := h2
      _ = 2 * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
          + 2 * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := h3

/-! ## The obstruction: the level-`0` memberships cannot control the `θ = 0` traces

Every `HkMem` of `FatouPkg` is a **level-`0`** membership, and (as `hkIntegrand_zero_eq'` above
records) `HkIntegrand α 0 f` carries the single angular weight `sin(2θ)^{-η/2}`, i.e.
`sin(2θ)^{-η}` after squaring, with `η = 99/100 < 1`.  That weight is **integrable at `θ = 0`**
(`weight_integrableOn` below), and the mixed slots carrying the *non*-integrable weight
`sin(2θ)^{-γ}` (`γ = 1 + α/10 > 1`) occur in `HkIntegrand α k` only for `k ≥ 1`, which
`FatouPkg` never uses.

The lemmas below make the consequence formal: a *radial* profile lies in `ℋ⁰` as soon as its
`z`-mass `(g·w)²` is integrable, **whatever its angular trace at `θ = 0` is**
(`HkMem_zero_radial`), and consequently `HkMem α 0` (resp. `HkMem α 0 (pth ·)`) is satisfied by a
profile whose value (resp. derivative) trace at `θ = 0⁺` is the nonzero constant `1`
(`HkMem_zero_trace_not_forced`, `HkMem_zero_deriv_trace_not_forced`).

This is exactly the deficiency that blocks the port of `EllipticEst.bslSol_unique_fts`: the
angular rigidity against `sin θ cos²θ`, the `θ`-energy identity, the `F_*`-ODE and the
decoupling of the `θ`-eigen-expansion *all* carry a boundary term at `θ = 0` of the form
`-μ(0)∫Jg + (1/2)μ'(0)∫J²` with `J(z) = lim_{θ→0⁺}Ψ z θ-Ψ' z θ`, `g(z) = lim ∂_θ(Ψ-Ψ')`, and the
theorem `EllipticEst.bslSol_unique_fts` consumes `EllHypN`, which needs `SmoothNbhd`,
`IsBslSol` on *all* `z ≥ 0` **and** the extra membership `HkMem α 0 (∂_θ²(z ∂_z·))` --- none of
which follows from `FatouPkg`.  The tree's own precedent (`FTS/StrongEps/EComparison/
HomClsZeroRefute.lean`, `NOTES_HomClsZero_FALSE.md`) refutes an analogous class-based uniqueness
statement by precisely this loophole, with the documented repair being an angular trace
condition.  See `NOTES_closedUniq3.md` §7 and `NOTES_theta0_trace.md`. -/

/-- The angular weight of the level-`0` integrand, `sin(2θ)^{-η}` (`η = 99/100 < 1`), is
integrable on `[0, π/2]`. -/
theorem eta_lt_one : Work.Spaces.eta < 1 := by
  unfold Work.Spaces.eta; norm_num

/-- `sin(2θ)^{-η}` is integrable at `θ = 0` (the exponent exceeds `-1`). -/
theorem weight_integrableOn :
    IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have h : (0:ℝ) ≤ Real.pi / 2 := by positivity
  have := (intervalIntegrable_iff_integrableOn_Icc_of_le h).mp
    (Work.FTS.H2.intervalIntegrable_sin_rpow (-(Work.Spaces.eta)) (by linarith [eta_lt_one]))
  simpa [Work.Spaces.Iθ] using this

/-- For a `θ`-independent profile the level-`0` integrand is `(g z · w z)² · sin(2θ)^{-η}`:
the only angular factor is the integrable weight. -/
theorem hkIntegrand_zero_radial {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (α : ℝ) (g : ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 (fun z _ => g z) z θ
      = (g z * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := by
  rw [hkIntegrand_zero_eq']
  have hs : 0 ≤ Real.sin (2 * θ) := by
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hpow : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
      = (Real.sin (2 * θ) ^ Work.Spaces.eta) ^ (1 / 2 : ℝ) := by
    rw [show Work.Spaces.eta / 2 = Work.Spaces.eta * (1 / 2) from by ring,
      ← Real.rpow_mul hs]
  rw [hpow, ← Real.sqrt_eq_rpow, mul_pow, div_pow, mul_pow,
    Real.sq_sqrt (Real.rpow_nonneg hs _), Real.rpow_neg hs]
  ring

/-- Per-slice integrability of the level-`0` integrand, for *every* radial profile. -/
theorem sliceIntegrable_zero_radial (α : ℝ) (g : ℝ → ℝ) (z : ℝ) :
    IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 (fun z _ => g z) z θ) Work.Spaces.Iθ := by
  refine MeasureTheory.IntegrableOn.congr_fun
    (MeasureTheory.Integrable.const_mul weight_integrableOn ((g z * Work.Spaces.w z) ^ 2))
    (fun θ hθ => ?_) measurableSet_Icc
  rw [hkIntegrand_zero_radial hθ α g z]

/-- **A radial profile is in `ℋ⁰` as soon as its `z`-mass `(g·w)²` is integrable** --- the
angular trace at `θ = 0` is not seen by the membership. -/
theorem HkMem_zero_radial (α : ℝ) {g : ℝ → ℝ}
    (hint : IntegrableOn (fun z => (g z * Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    Work.Spaces.HkMem α 0 (fun z _ => g z) := by
  constructor
  · intro z _
    exact sliceIntegrable_zero_radial α g z
  · have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z _ => g z) z θ)
        = fun z => (g z * Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) := by
      funext z
      rw [MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => hkIntegrand_zero_radial hθ α g z)]
      exact MeasureTheory.integral_const_mul _ _
    rw [hfun]
    exact MeasureTheory.Integrable.mul_const hint _

/-- The `z`-mass of the indicator profile `1_{[1,2]}(z)` is integrable (it is supported in
`[1,2]`, where `w ≤ 9`). -/
theorem integrableOn_indicator_w_sq :
    IntegrableOn (fun z : ℝ => ((if z ∈ Set.Icc (1:ℝ) 2 then (1:ℝ) else 0)
      * Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  have hbound : ∀ z ∈ Set.Icc (0:ℝ) 2,
      ‖((if z ∈ Set.Icc (1:ℝ) 2 then (1:ℝ) else 0) * Work.Spaces.w z) ^ 2‖ ≤ 81 := by
    intro z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hmem : z ∈ Set.Icc (1:ℝ) 2
    · rw [if_pos hmem]
      have h1 : (1:ℝ) ≤ z := hmem.1
      have h2 : z ≤ 2 := hmem.2
      have hw0 : 0 ≤ Work.Spaces.w z := by
        unfold Work.Spaces.w; exact div_nonneg (sq_nonneg _) (by positivity)
      have hw : Work.Spaces.w z ≤ 9 := by
        unfold Work.Spaces.w
        rw [div_le_iff₀ (by nlinarith : (0:ℝ) < z ^ 2)]
        nlinarith
      nlinarith [hw, hw0]
    · rw [if_neg hmem]; norm_num
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ => ((if z ∈ Set.Icc (1:ℝ) 2 then (1:ℝ) else 0) * Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Icc (0:ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.pow_const ?_ 2
    refine Measurable.mul ?_ ?_
    · exact Measurable.ite measurableSet_Icc measurable_const measurable_const
    · unfold Work.Spaces.w; fun_prop
  have h1 : IntegrableOn
      (fun z : ℝ => ((if z ∈ Set.Icc (1:ℝ) 2 then (1:ℝ) else 0) * Work.Spaces.w z) ^ 2)
      (Set.Icc (0:ℝ) 2) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ hmeas 81 ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      exact hbound z hz
  refine MeasureTheory.IntegrableOn.of_forall_sdiff_eq_zero h1 measurableSet_Ici ?_
  intro x hx
  obtain ⟨hxIci, hxnot⟩ := hx
  have hx2 : 2 < x := by
    by_contra h
    exact hxnot ⟨by linarith [Set.mem_Ici.mp hxIci], le_of_not_gt h⟩
  have hxnotmem : x ∉ Set.Icc (1:ℝ) 2 := fun h => absurd h.2 (not_le.mpr hx2)
  rw [if_neg hxnotmem]
  ring

/-- `HkMem α 0` holds for the indicator profile `1_{[1,2]}(z)`. -/
theorem HkMem_zero_indicator (α : ℝ) :
    Work.Spaces.HkMem α 0 (fun z _ => if z ∈ Set.Icc (1:ℝ) 2 then (1:ℝ) else 0) :=
  HkMem_zero_radial α integrableOn_indicator_w_sq

/-- **The obstruction, formalised.**  `HkMem α 0` does **not** force the angular *value* trace at
`θ = 0⁺` to vanish: the indicator profile is in `ℋ⁰` and its trace is `1 ≠ 0` at every
`z ∈ (1,2)`. -/
theorem HkMem_zero_trace_not_forced (α : ℝ) :
    ∃ f : ℝ → ℝ → ℝ, Work.Spaces.HkMem α 0 f ∧
      ∀ z ∈ Set.Ioo (1:ℝ) 2,
        Filter.Tendsto (fun θ => f z θ) (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 (1:ℝ)) := by
  refine ⟨fun z _ => if z ∈ Set.Icc (1:ℝ) 2 then (1:ℝ) else 0, HkMem_zero_indicator α, ?_⟩
  intro z hz
  have hmem : z ∈ Set.Icc (1:ℝ) 2 := ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have : (fun θ : ℝ => (fun z _ => if z ∈ Set.Icc (1:ℝ) 2 then (1:ℝ) else 0) z θ)
      = fun _ : ℝ => (1:ℝ) := by
    funext θ
    show (if (z ∈ Set.Icc (1:ℝ) 2) then (1:ℝ) else 0) = 1
    rw [if_pos hmem]
  rw [this]
  exact tendsto_const_nhds

/-- **The obstruction, derivative form.**  `HkMem α 0 (pth ·)` does **not** force the angular
*derivative* trace at `θ = 0⁺` to vanish either. -/
theorem HkMem_zero_deriv_trace_not_forced (α : ℝ) :
    ∃ f : ℝ → ℝ → ℝ, Work.Spaces.HkMem α 0 (Work.Spaces.pth f) ∧
      ∀ z ∈ Set.Ioo (1:ℝ) 2,
        Filter.Tendsto (fun θ => Work.Spaces.pth f z θ) (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 (1:ℝ)) := by
  refine ⟨fun z θ => (if z ∈ Set.Icc (1:ℝ) 2 then (1:ℝ) else 0) * θ, ?_, ?_⟩
  · have hpth : Work.Spaces.pth (fun z θ => (if z ∈ Set.Icc (1:ℝ) 2 then (1:ℝ) else 0) * θ)
        = fun z _ => (if z ∈ Set.Icc (1:ℝ) 2 then (1:ℝ) else 0) := by
      funext z θ
      simp only [Work.Spaces.pth]
      simpa using ((hasDerivAt_id θ).const_mul
        ((if z ∈ Set.Icc (1:ℝ) 2 then (1:ℝ) else 0))).deriv
    rw [hpth]
    exact HkMem_zero_indicator α
  · intro z hz
    have hmem : z ∈ Set.Icc (1:ℝ) 2 := ⟨le_of_lt hz.1, le_of_lt hz.2⟩
    have hpth : Work.Spaces.pth
        (fun z θ => (if z ∈ Set.Icc (1:ℝ) 2 then (1:ℝ) else 0) * θ) z
        = fun _ : ℝ => (1:ℝ) := by
      funext θ
      simp only [Work.Spaces.pth]
      rw [if_pos hmem]
      simpa using ((hasDerivAt_id θ).const_mul (1:ℝ)).deriv
    simp only [hpth]
    exact tendsto_const_nhds

/-! ## The target

**Status: PROVED** (the theorem below is `sorry`-free, axioms
`[propext, Classical.choice, Quot.sound]`), *after* the interface repair of the previous stretch.
The obstruction recorded in the section above is real: `FatouPkg`'s memberships are all at level `0`
with the weight `sin(2θ)^{-η}` (`η = 99/100`, integrable at `θ = 0`) and cannot constrain the
`θ = 0` traces that every step of the uniqueness argument needs — that is what
`HkMem_zero_trace_not_forced` / `HkMem_zero_deriv_trace_not_forced` / `weight_integrableOn` above
machine-check.  The repair that was installed (see `Defs3.FatouPkg` and `NOTES.md` §0bis) is the
conjunct **`BoxReg Ψ`** — `Ψ` is jointly `C²` on every closed box `[a,b] × [0,π/2]`, `0 < a ≤ b` —
together with its sequence-level producer `Defs3.BoxData` in `FatouData` (whose bridge from
primitive estimates is `FTS_EllLimOK.BoxReg_of_uniform`).  With it, the port of
`EllipticEst.bslSol_unique_fts` goes through: `UniqFatou.eqOn_of_same_law` (the θ-energy chain
`Fstar_zero`, `EnergyGap`, `phi_eq_zero_of_euler_gap_weighted`) plus
`Locality.mixed_congr_of_eqOn_isOpen`.  `NOTES_theta0_trace.md` has the analysis of the
obstruction; `NOTES_STATUS_closedUniq3.md` the state of the proof. -/

theorem ClosedUniq3_small : Work.FTS_EllLimOK.SmallUniq3 := by
  refine ⟨1, by norm_num, ?_⟩
  intro α hα hα1 Ce E hE fn f hL Ψ Ψ' hΨ hΨ' j i hji z θ hzθ
  obtain ⟨hsolΨ, -, hHkΨ, -, -, -, hHkcΨ, -, -, -, -, hboxΨ⟩ := hΨ.1
  obtain ⟨hsolΨ', -, hHkΨ', -, -, -, hHkcΨ', -, -, -, -, hboxΨ'⟩ := hΨ'.1
  have hHkδ : Work.Spaces.HkMem α 0 (Work.FTS_EllLimOK.diff Ψ Ψ') :=
    HkMem_zero_diff hHkΨ hHkΨ' hboxΨ hboxΨ'
  have heq : Set.EqOn (Function.uncurry Ψ) (Function.uncurry Ψ') Work.Construction.Qd :=
    fun p hp => Work.FTS_EllLimOK.eqOn_of_same_law hα hsolΨ hsolΨ' hboxΨ hboxΨ'
      hHkΨ hHkcΨ hHkΨ' hHkcΨ' hHkδ p.1 p.2 hp
  exact mixed_congr_of_eqOn_isOpen (isOpen_Ioi.prod isOpen_Ioo) heq hzθ j i

end Work.FTS_EllLimOK
