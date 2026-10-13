import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.SliceA.not_integrableOn_sinCos2_of_tendsto
import Submission.Work.FTS.EllipticEst.l2etaEndpointZeroLeft
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.cascadeBalance

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

/-- **The source's slice has no amplitude of order `N+2` (`N ≥ 2`).**  If
`(π/2-θ)^{N+2}·G(z,θ)` has a limit `c` as `θ → (π/2)⁻`, then `c = 0`. -/
theorem sourceAmp_vanishes {α : ℝ} {G : ℝ → ℝ → ℝ} (hSOG : Work.FTS.EllipticEst.SmoothOpen G)
    (hmem : Work.Spaces.HkMem α 0 G) {z : ℝ} (hz : 0 < z) {N : ℕ} (hN : 2 ≤ N) {c : ℝ}
    (hlim : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * G z θ) Lθ (nhds c)) :
    c = 0 := by
  by_contra hc
  have hG := Work.FTS.EllipticEst.endpt_slice_mul_sinCos2_integrable_of_HkMem hSOG hmem hz
  -- turn the signed integrability into `sinθcos²θ·|G z ·| ∈ L¹`
  have hGabs : MeasureTheory.IntegrableOn
      (fun θ => Real.sin θ * Real.cos θ ^ 2 * |G z θ|) Work.Spaces.Iθ := by
    have h2 : MeasureTheory.Integrable
        (fun θ => |G z θ * Work.Elliptic.sinCos2 θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hG.abs
    refine h2.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hsin : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    simp only [Pi.mul_apply, Work.Elliptic.sinCos2, abs_mul, abs_of_nonneg hsin,
      abs_of_nonneg (sq_nonneg (Real.cos θ))]
    ring
  exact (Work.FTS.EllipticEst.H2W.SliceA.not_integrableOn_sinCos2_of_tendsto N
      (fun θ => G z θ) c hN hc hlim) hGabs

/-- **The sourceless cascade balance.**  Same as `cascadeBalance`, but the vanishing of the
source's order-`(N+2)` component is *derived* (from `HkMem α 0 G` and the existence of the
limit), not assumed: the only extra hypothesis is that `lim (π/2-θ)^{N+2}·G(z,θ)` exists. -/
theorem cascadeBalance_sourceless {α : ℝ} {G Φ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hSOG : Work.FTS.EllipticEst.SmoothOpen G) (hmem : Work.Spaces.HkMem α 0 G)
    {N : ℕ} (hN : 2 ≤ N) {B B₁ B₂ c : ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Φ z θ = G z θ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Φ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h0 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * Φ z θ) Lθ (nhds B))
    (h1 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 1) *
        deriv (fun θ' => Φ z θ') θ) Lθ (nhds ((N : ℝ) * B)))
    (h2 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        deriv (fun s => deriv (fun θ' => Φ z θ') s) θ) Lθ
      (nhds ((N : ℝ) * ((N : ℝ) + 1) * B)))
    (hB₁ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * Work.Spaces.pz Φ z θ)
      Lθ (nhds B₁))
    (hB₂ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.pzIter 2 Φ z θ) Lθ (nhds B₂))
    (hlimG : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * G z θ) Lθ (nhds c)) :
    (1 - (N : ℝ) ^ 2) * B = α ^ 2 * z ^ 2 * B₂ + α * (5 + α) * z * B₁ := by
  have hc : c = 0 := sourceAmp_vanishes hSOG hmem hz hN hlimG
  refine cascadeBalance hz hN heq hsm h0 h1 h2 hB₁ hB₂ ?_
  rw [hc] at hlimG
  exact hlimG

/-- `π/2 - θ → 0` along `θ → (π/2)⁻` (local copy, the tree's is private). -/
theorem tendsto_shift_zero : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) Lθ (nhds 0) := by
  have h : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (Real.pi / 2 - Real.pi / 2)) :=
    ((tendsto_const_nhds.sub tendsto_id)).mono_left nhdsWithin_le_nhds
  simpa using h

/-- **The amplitudes of a slice are `2`-separated.**  If `(π/2-θ)^{N-2}u` has a finite limit `A`
(`N ≥ 2`) then `(π/2-θ)^{N}u → 0`: the order-`N` amplitude is killed by the mere *finiteness* of
the order-`(N-2)` amplitude.  (So no slice can have two nonzero power amplitudes two orders
apart — this is why `NOTES_weakPhiPoleBound.md` §K's recursion cannot be phrased as a two-term
limit statement.) -/
theorem amp_next_vanishes {u : ℝ → ℝ} {N : ℕ} (hN : 2 ≤ N) {A c : ℝ}
    (hA : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N - 2) * u θ) Lθ (nhds A))
    (hc : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * u θ) Lθ (nhds c)) :
    c = 0 := by
  have hsq : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ 2) Lθ (nhds 0) := by
    have h := tendsto_shift_zero.pow 2
    simpa using h
  have hprod : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ 2
      * ((Real.pi / 2 - θ) ^ (N - 2) * u θ)) Lθ (nhds (0 * A)) := hsq.mul hA
  rw [zero_mul] at hprod
  have hprod' : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * u θ) Lθ (nhds 0) :=
    hprod.congr (fun θ => by
      rw [← mul_assoc, ← pow_add]
      have hk : 2 + (N - 2) = N := by omega
      rw [hk])
  have h0 : (0 : ℝ) = c := tendsto_nhds_unique hprod' hc
  exact h0.symm

/-- **Closure of the cascade balance in the amplitude world.**  At a fixed `z`, suppose that

* the slice and its first two `z`-derivatives have amplitudes at order `N` resp. `N+2`,
* the *order-`N` amplitudes of the two radial slices also exist* (this is the extra input),
* the source has no order-`(N+2)` component (automatic by `sourceAmp_vanishes` when the limit
  exists, and then `cascadeBalance_sourceless` applies).

Then the order-`N` amplitude of the slice is **zero** (`N ≥ 2`).  Contrapositive, in the language
of the node: *a nonzero power amplitude of order `≥ 2` in a slice forces the next-order amplitudes
of `∂_zΦ(z,·)` and `∂_z²Φ(z,·)` to fail to exist* — the cascade cannot start from a
power-like behaviour. -/
theorem cascadeAmp_zero_of_radialAmp_exists {α : ℝ} {G Φ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hSOG : Work.FTS.EllipticEst.SmoothOpen G) (hmem : Work.Spaces.HkMem α 0 G)
    {N : ℕ} (hN : 2 ≤ N) {B B₁ B₂ c A₁ A₂ : ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Φ z θ = G z θ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Φ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h0 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * Φ z θ) Lθ (nhds B))
    (h1 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 1) *
        deriv (fun θ' => Φ z θ') θ) Lθ (nhds ((N : ℝ) * B)))
    (h2 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        deriv (fun s => deriv (fun θ' => Φ z θ') s) θ) Lθ
      (nhds ((N : ℝ) * ((N : ℝ) + 1) * B)))
    (hB₁ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * Work.Spaces.pz Φ z θ)
      Lθ (nhds B₁))
    (hB₂ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.pzIter 2 Φ z θ) Lθ (nhds B₂))
    (hlimG : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * G z θ) Lθ (nhds c))
    (hA₁ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * Work.Spaces.pz Φ z θ)
      Lθ (nhds A₁))
    (hA₂ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * Work.Spaces.pzIter 2 Φ z θ)
      Lθ (nhds A₂)) :
    B = 0 := by
  have hbal := cascadeBalance_sourceless hz hSOG hmem hN heq hsm h0 h1 h2 hB₁ hB₂ hlimG
  have hz₁ : B₁ = 0 := amp_next_vanishes (u := fun θ => Work.Spaces.pz Φ z θ)
    (N := N + 2) (by omega) hA₁ hB₁
  have hz₂ : B₂ = 0 := amp_next_vanishes (u := fun θ => Work.Spaces.pzIter 2 Φ z θ)
    (N := N + 2) (by omega) hA₂ hB₂
  have hcoef : (1 : ℝ) - (N : ℝ) ^ 2 ≠ 0 := by
    have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have : (1 - (N : ℝ) ^ 2) * B = 0 := by rw [hbal, hz₁, hz₂]; ring
  exact (mul_eq_zero.mp this).resolve_left hcoef

end Work.FTS.EllipticEst.H2W.WeakPureAux
