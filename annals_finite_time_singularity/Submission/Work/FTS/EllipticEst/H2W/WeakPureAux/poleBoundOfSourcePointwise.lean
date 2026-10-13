/-
Copyright: work module for the Elgindi finite-time singularity project.

# `poleBoundOfSourcePointwise`: the pole bound for a slice from a *pointwise* source bound

Let `u` be `C²` on the open interval `I = (0, π/2)` and suppose that

  `Lzero1 u = g`  on `I`,   `|g θ| ≤ C (θ⁻² + (π/2 - θ)⁻²)`  on `I`.

Then `|u θ| ≤ C' (θ⁻¹ + (π/2 - θ)⁻¹)` on `I`.

This is the *pointwise-source* form of the one-variable growth theorem: the sibling
`H2W.lzero1SliceGrowth` (and its corollary `WeakPureAux.lzeroSlicePoleBound`) assume the
`L¹`-integrability of `sin θ cos²θ · |Lzero1 u|`, i.e. the *mass*

  `∫_θ^{π/4} sin s cos²s · |g s| ds`

to be finite near `θ = 0`.  Under the present hypothesis the mass is *not* finite there:
`sin s cos² s ≈ s` while `|g s| ≈ s⁻²`, so the integrand behaves like `s⁻¹`.  The present
statement is nevertheless true, and the proof is the same Wronskian/reduction-of-order
argument, run with a *growing* bound on the Wronskian functional.

## The argument

`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` is a second-order ODE on `I`, so
`D u θ = cos θ (u θ (sin 2θ)' - u' θ sin 2θ)` (a Wronskian-type functional) and
`R u θ = u θ / sin 2θ` satisfy the two exact identities

* `(D u)' θ = 2 · Lzero1 u θ · sin θ cos²θ = 2 g θ · sin θ cos²θ`,
* `(R u)' θ = - D u θ / (cos θ sin²(2θ)).

Integrating the first from `π/4` to `s` (resp. from `s` to `π/4`) gives a bound on `|D u s|`
in terms of the mass `M(s) = ∫ sin r cos²r |g r| dr` of the source on the corresponding
half; integrating the second gives

  `|R u θ| ≤ |R u (π/4)| + B(θ) · ∫ 1/(cos s sin²(2s)) ds`,

where `B(θ) = |D u (π/4)| + 2 M(θ)`.  The pointwise hypothesis on `g` bounds the mass:

* on the left, `M(θ) ≤ C(π/4 + 4/π) θ⁻¹` (using `sin s cos² s ≤ s` and `s ≥ θ`),
* on the right, `M(θ) ≤ C(π/4 + 4/π)` (using `sin s cos² s ≤ (π/2 - s)²`).

The two explicit kernel estimates `H2W.lzeroGrowthKernelLeft` / `...Right` then give
`|u θ| = |R u θ| sin 2θ ≤ C' θ⁻¹` on `(0, π/4]` and `|u θ| ≤ C' (π/2 - θ)⁻¹` on
`[π/4, π/2)`, which is the claim.

The constants are completely explicit, e.g. the final `C'` may be taken to be
`max CL CR` with `CL`, `CR` as in the two half-bounds below; all that matters here is that
they are finite and nonnegative.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.lzero1SliceGrowth
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthKernelLeft
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthKernelRight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

/-! ## Elementary bounds for the weight `sin θ cos²θ` -/

/-- `sin θ cos²θ ≤ θ` for `θ ≥ 0`. -/
theorem sinCos2_le_self {θ : ℝ} (hθ : 0 ≤ θ) : Work.Elliptic.sinCos2 θ ≤ θ := by
  rw [Work.Elliptic.sinCos2]
  simpa using mul_le_mul (Real.sin_le hθ) (Real.cos_sq_le_one θ) (sq_nonneg _) hθ

/-- `sin θ cos²θ ≤ (π/2 - θ)²` (with no restriction on `θ`). -/
theorem sinCos2_le_tsq (θ : ℝ) :
    Work.Elliptic.sinCos2 θ ≤ (Real.pi / 2 - θ) ^ 2 := by
  rw [Work.Elliptic.sinCos2]
  have hcos : Real.cos θ = Real.sin (Real.pi / 2 - θ) := by rw [Real.sin_pi_div_two_sub]
  rw [hcos]
  calc Real.sin θ * Real.sin (Real.pi / 2 - θ) ^ 2
      ≤ 1 * Real.sin (Real.pi / 2 - θ) ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.sin_le_one θ) (sq_nonneg _)
    _ ≤ (Real.pi / 2 - θ) ^ 2 := by simpa using Real.sin_sq_le_sq (x := Real.pi / 2 - θ)

/-- `sin θ cos²θ ≤ 1`. -/
theorem sinCos2_le_one (θ : ℝ) : Work.Elliptic.sinCos2 θ ≤ 1 := by
  rw [Work.Elliptic.sinCos2]
  simpa using mul_le_mul (Real.sin_le_one θ) (Real.cos_sq_le_one θ) (sq_nonneg _)
    (by norm_num : (0:ℝ) ≤ 1)

/-! ## The two mass bounds for the source

With `sin θ cos²θ` the angular weight of the `i = 0` slot, the pointwise source bound
`|g θ| ≤ C (θ⁻² + (π/2 - θ)⁻²)` gives the folded estimates below.  Both constants are
`C (π/4 + 4/π)`: at `θ = 0` the weight `sin s cos² s ≈ s` cancels one power of `s`, leaving
the integrable `s⁻¹` on the *relative* interval `[θ, π/4]` (giving `θ⁻¹`), and at `θ = π/2`
the weight `≈ (π/2 - s)²` cancels the second-order pole exactly. -/

theorem sinCos2MassBound {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    {C : ℝ} (hC : 0 < C)
    (hb : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |g θ| ≤ C * (1 / θ ^ 2 + 1 / (Real.pi / 2 - θ) ^ 2)) :
    (∀ θ ∈ Set.Ioc (0:ℝ) (Real.pi / 4),
        (∫ s in θ..(Real.pi / 4), Work.Elliptic.sinCos2 s * |g s|)
          ≤ (C * (Real.pi / 4 + 4 / Real.pi)) * θ⁻¹)
      ∧ (∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        (∫ s in (Real.pi / 4)..θ, Work.Elliptic.sinCos2 s * |g s|)
          ≤ C * (Real.pi / 4 + 4 / Real.pi)) := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hcont : ContinuousOn (fun s : ℝ => Work.Elliptic.sinCos2 s * |g s|)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.H2W.LzeroGrowth.continuous_sinCos2.continuousOn).mul hg.abs
  constructor
  · intro θ hθ
    obtain ⟨hθ0, hθ4⟩ := hθ
    have hsub : Set.uIcc θ (Real.pi/4) ⊆ Set.Ioo 0 (Real.pi/2) := by
      rw [Set.uIcc_of_le hθ4]
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2, hπ]⟩
    have hInt : IntervalIntegrable (fun s : ℝ => Work.Elliptic.sinCos2 s * |g s|)
        volume θ (Real.pi/4) :=
      (hcont.mono hsub).intervalIntegrable
    have hpt : ∀ s ∈ Set.Icc θ (Real.pi / 4),
        Work.Elliptic.sinCos2 s * |g s| ≤ C / θ + 4 * C / Real.pi := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hθ0 hs.1
      have hs4 : s ≤ Real.pi / 4 := hs.2
      have hsI : s ∈ Set.Ioo (0:ℝ) (Real.pi/2) := ⟨hs0, by linarith [hπ]⟩
      have h1 : Work.Elliptic.sinCos2 s ≤ s := sinCos2_le_self hs0.le
      have h2 : |g s| ≤ C * (1 / s ^ 2 + 1 / (Real.pi / 2 - s) ^ 2) := hb s hsI
      have h3 : Work.Elliptic.sinCos2 s * |g s|
          ≤ s * (C * (1 / s ^ 2 + 1 / (Real.pi / 2 - s) ^ 2)) :=
        mul_le_mul h1 h2 (abs_nonneg _) hs0.le
      have hA : s * (1 / s ^ 2) = 1 / s := by field_simp
      have ht4 : Real.pi / 4 ≤ Real.pi / 2 - s := by linarith
      have hsq : (Real.pi / 4) ^ 2 ≤ (Real.pi / 2 - s) ^ 2 :=
        pow_le_pow_left₀ (by linarith [hπ]) ht4 2
      have h2a : 1 / (Real.pi / 2 - s) ^ 2 ≤ 16 / Real.pi ^ 2 := by
        have h := one_div_le_one_div_of_le (show (0:ℝ) < (Real.pi/4)^2 by positivity) hsq
        rwa [show (1:ℝ) / (Real.pi/4)^2 = 16 / Real.pi^2 by field_simp; ring] at h
      have h2b : s * (1 / (Real.pi / 2 - s) ^ 2) ≤ 4 / Real.pi := by
        calc s * (1 / (Real.pi / 2 - s) ^ 2) ≤ (Real.pi / 4) * (16 / Real.pi ^ 2) :=
              mul_le_mul hs4 h2a (by positivity) (by linarith [hπ])
          _ = 4 / Real.pi := by field_simp; ring
      have key : s * (C * (1 / s ^ 2 + 1 / (Real.pi / 2 - s) ^ 2))
          ≤ C * (1 / θ + 4 / Real.pi) := by
        have h3' : 1 / s ≤ 1 / θ := one_div_le_one_div_of_le hθ0 hs.1
        have : s * (1 / s ^ 2) + s * (1 / (Real.pi / 2 - s) ^ 2) ≤ 1 / θ + 4 / Real.pi := by
          rw [hA]; linarith
        calc s * (C * (1 / s ^ 2 + 1 / (Real.pi / 2 - s) ^ 2))
            = C * (s * (1 / s ^ 2) + s * (1 / (Real.pi / 2 - s) ^ 2)) := by ring
          _ ≤ C * (1 / θ + 4 / Real.pi) := mul_le_mul_of_nonneg_left this hC.le
      have hfin : C * (1 / θ + 4 / Real.pi) = C / θ + 4 * C / Real.pi := by ring
      linarith [h3, key, hfin]
    have hInt2 : IntervalIntegrable (fun _ : ℝ => C / θ + 4 * C / Real.pi) volume θ (Real.pi/4) :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hθ4 hInt hInt2 hpt
    have hconst : (∫ s in θ..(Real.pi/4), (C / θ + 4 * C / Real.pi))
        = (Real.pi / 4 - θ) * (C / θ + 4 * C / Real.pi) := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
    have hgoal : (Real.pi / 4 - θ) * (C / θ + 4 * C / Real.pi)
        ≤ (C * (Real.pi / 4 + 4 / Real.pi)) / θ := by
      rw [le_div_iff₀ hθ0]
      have hkey : ((Real.pi/4 - θ) * (C/θ + 4*C/Real.pi)) * θ
          = C * (Real.pi/4 - 4*θ^2/Real.pi) := by
        field_simp
        ring
      rw [hkey]
      apply mul_le_mul_of_nonneg_left _ hC.le
      have h1 : -4*θ^2/Real.pi ≤ 4/Real.pi := by
        rw [div_le_div_iff_of_pos_right Real.pi_pos]
        nlinarith [sq_nonneg θ]
      have h2 : -4*θ^2/Real.pi = -(4*θ^2/Real.pi) := by ring
      rw [h2] at h1
      linarith
    calc (∫ s in θ..(Real.pi/4), Work.Elliptic.sinCos2 s * |g s|)
        ≤ (Real.pi / 4 - θ) * (C / θ + 4 * C / Real.pi) := by rw [← hconst]; exact hmono
      _ ≤ (C * (Real.pi / 4 + 4 / Real.pi)) / θ := hgoal
      _ = (C * (Real.pi / 4 + 4 / Real.pi)) * θ⁻¹ := by rw [div_eq_mul_inv]
  · intro θ hθ
    obtain ⟨hθ1, hθ2⟩ := hθ
    have hsub : Set.uIcc (Real.pi/4) θ ⊆ Set.Ioo 0 (Real.pi/2) := by
      rw [Set.uIcc_of_le hθ1]
      intro s hs
      exact ⟨by linarith [hs.1, hπ], by linarith [hs.2, hθ2]⟩
    have hInt : IntervalIntegrable (fun s : ℝ => Work.Elliptic.sinCos2 s * |g s|)
        volume (Real.pi/4) θ :=
      (hcont.mono hsub).intervalIntegrable
    have hpt : ∀ s ∈ Set.Icc (Real.pi / 4) θ,
        Work.Elliptic.sinCos2 s * |g s| ≤ C * (16 / Real.pi ^ 2 + 1) := by
      intro s hs
      have hs0 : 0 < s := by linarith [hπ, hs.1]
      have hsI : s ∈ Set.Ioo (0:ℝ) (Real.pi/2) := ⟨hs0, lt_of_le_of_lt hs.2 hθ2⟩
      have h1 : |g s| ≤ C * (1 / s ^ 2 + 1 / (Real.pi / 2 - s) ^ 2) := hb s hsI
      have h2 : 0 ≤ Work.Elliptic.sinCos2 s :=
        Work.FTS.EllipticEst.H2W.LzeroGrowth.sinCos2_nonneg ⟨hs0.le, le_of_lt hsI.2⟩
      have h3 : Work.Elliptic.sinCos2 s * |g s| ≤
          Work.Elliptic.sinCos2 s * (C * (1 / s ^ 2 + 1 / (Real.pi / 2 - s) ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 h2
      have hsq16 : 1 / s ^ 2 ≤ 16 / Real.pi ^ 2 := by
        have hs4 : Real.pi / 4 ≤ s := hs.1
        have hsq : (Real.pi / 4) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by linarith [hπ]) hs4 2
        have h := one_div_le_one_div_of_le (show (0:ℝ) < (Real.pi/4)^2 by positivity) hsq
        rwa [show (1:ℝ) / (Real.pi/4)^2 = 16 / Real.pi^2 by field_simp; ring] at h
      have hA : Work.Elliptic.sinCos2 s * (1 / s ^ 2) ≤ 16 / Real.pi ^ 2 := by
        have hle1 : Work.Elliptic.sinCos2 s * (1/s^2) ≤ 1 * (1/s^2) :=
          mul_le_mul_of_nonneg_right (sinCos2_le_one s) (by positivity)
        linarith [hle1, hsq16]
      have htpos : 0 < Real.pi / 2 - s := by linarith [hsI.2]
      have hB : Work.Elliptic.sinCos2 s * (1 / (Real.pi / 2 - s) ^ 2) ≤ 1 := by
        have hle := sinCos2_le_tsq s
        have ht2 : 0 < (Real.pi / 2 - s) ^ 2 := pow_pos htpos 2
        rw [mul_one_div, div_le_one ht2]
        exact hle
      have key : Work.Elliptic.sinCos2 s * (C * (1 / s ^ 2 + 1 / (Real.pi / 2 - s) ^ 2))
          ≤ C * (16 / Real.pi ^ 2 + 1) := by
        have : Work.Elliptic.sinCos2 s * (1 / s ^ 2)
            + Work.Elliptic.sinCos2 s * (1 / (Real.pi / 2 - s) ^ 2) ≤ 16 / Real.pi ^ 2 + 1 := by
          linarith
        calc Work.Elliptic.sinCos2 s * (C * (1 / s ^ 2 + 1 / (Real.pi / 2 - s) ^ 2))
            = C * (Work.Elliptic.sinCos2 s * (1 / s ^ 2)
                + Work.Elliptic.sinCos2 s * (1 / (Real.pi / 2 - s) ^ 2)) := by ring
          _ ≤ C * (16 / Real.pi ^ 2 + 1) := mul_le_mul_of_nonneg_left this hC.le
      linarith [h3, key]
    have hInt2 : IntervalIntegrable (fun _ : ℝ => C * (16 / Real.pi ^ 2 + 1)) volume (Real.pi/4) θ :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hθ1 hInt hInt2 hpt
    have hconst : (∫ s in (Real.pi/4)..θ, (C * (16 / Real.pi ^ 2 + 1)))
        = (θ - Real.pi / 4) * (C * (16 / Real.pi ^ 2 + 1)) := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
    have hgoal : (θ - Real.pi / 4) * (C * (16 / Real.pi ^ 2 + 1))
        ≤ C * (Real.pi / 4 + 4 / Real.pi) := by
      have hle : θ - Real.pi / 4 ≤ Real.pi / 4 := by linarith
      have hnn : 0 ≤ C * (16 / Real.pi ^ 2 + 1) := by positivity
      calc (θ - Real.pi / 4) * (C * (16 / Real.pi ^ 2 + 1))
          ≤ (Real.pi / 4) * (C * (16 / Real.pi ^ 2 + 1)) := mul_le_mul_of_nonneg_right hle hnn
        _ = C * (Real.pi / 4 + 4 / Real.pi) := by field_simp; ring
    calc (∫ s in (Real.pi/4)..θ, Work.Elliptic.sinCos2 s * |g s|)
        ≤ (θ - Real.pi / 4) * (C * (16 / Real.pi ^ 2 + 1)) := by rw [← hconst]; exact hmono
      _ ≤ C * (Real.pi / 4 + 4 / Real.pi) := hgoal

/-! ## The Wronskian functional and the reduction-of-order identities -/

/-- The mass of the source on the *left* half `[θ, π/4]`. -/
def Ml (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ s in θ..(Real.pi/4), Work.Elliptic.sinCos2 s * |g s|

/-- The mass of the source on the *right* half `[π/4, θ]`. -/
def Mr (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ s in (Real.pi/4)..θ, Work.Elliptic.sinCos2 s * |g s|

/-- `g` is continuous on the open interval, being `Lzero1 u` there. -/
theorem cont_g {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi/2)))
    (h : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ContinuousOn g (Set.Ioo 0 (Real.pi/2)) :=
  (Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_Lzero1 hu).congr
    (fun θ hθ => (h θ hθ).symm)

theorem sinCos2_nonneg' {s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi/2)) :
    0 ≤ Work.Elliptic.sinCos2 s :=
  Work.FTS.EllipticEst.H2W.LzeroGrowth.sinCos2_nonneg ⟨hs.1.le, hs.2.le⟩

/-- The weighted source `sin s cos²s |g s|` is continuous on the open interval. -/
theorem mass_cont {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioo 0 (Real.pi/2))) :
    ContinuousOn (fun s : ℝ => Work.Elliptic.sinCos2 s * |g s|) (Set.Ioo 0 (Real.pi/2)) :=
  (Work.FTS.EllipticEst.H2W.LzeroGrowth.continuous_sinCos2.continuousOn).mul hg.abs

/-- **The fundamental theorem for the Wronskian functional**:
`D u b - D u a = ∫_a^b 2 g s sin s cos²s ds`. -/
theorem Dfun_sub_eq {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi/2)))
    (h : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {a b : ℝ} (hsub : Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi/2)) :
    Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u b - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u a
      = ∫ s in a..b, 2 * g s * Work.Elliptic.sinCos2 s := by
  have hftc : ∫ s in a..b, 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s
      = Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u b
        - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => Work.FTS.EllipticEst.H2W.Lzero1Growth.Dfun_hasDerivAt hu (hsub hs))
      (Work.FTS.EllipticEst.H2W.Lzero1Growth.intervalIntegrable_two_mul hu hsub)
  rw [← hftc]
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  rw [h s (hsub hs)]

/-- The oscillation bound for the Wronskian functional on `[a, b]`. -/
theorem Dfun_abs_sub_le {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi/2)))
    (h : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {a b : ℝ} (hab : a ≤ b) (hsub : Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi/2)) :
    |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u b - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u a|
      ≤ 2 * (∫ s in a..b, Work.Elliptic.sinCos2 s * |g s|) := by
  rw [Dfun_sub_eq hu h hsub]
  have h1 : |∫ s in a..b, 2 * g s * Work.Elliptic.sinCos2 s|
      ≤ ∫ s in a..b, |2 * g s * Work.Elliptic.sinCos2 s| :=
    intervalIntegral.abs_integral_le_integral_abs hab
  have h2 : (∫ s in a..b, |2 * g s * Work.Elliptic.sinCos2 s|)
      = 2 * (∫ s in a..b, Work.Elliptic.sinCos2 s * |g s|) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hnn : 0 ≤ Work.Elliptic.sinCos2 s := sinCos2_nonneg' (hsub hs)
    rw [abs_mul, abs_mul, abs_of_nonneg hnn, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    ring
  linarith [h1, h2]

/-- Pointwise bound on `D u` on the left half: `|D u s| ≤ |D u (π/4)| + 2 Ml g θ`. -/
theorem Dfun_le_left {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi/2)))
    (h : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (Real.pi/4)) {s : ℝ} (hs : s ∈ Set.Icc θ (Real.pi/4)) :
    |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s|
      ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)| + 2 * Ml g θ := by
  have hπ := Real.pi_pos
  have hIcc0 : ∀ r ∈ Set.Icc θ (Real.pi/4), r ∈ Set.Ioo 0 (Real.pi/2) := fun r hr =>
    ⟨by linarith [hr.1, hθ.1], by linarith [hr.2, hπ]⟩
  have hsub0 : Set.uIcc θ (Real.pi/4) ⊆ Set.Ioo 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hθ.2]; exact hIcc0
  have hIcc1 : ∀ r ∈ Set.Icc s (Real.pi/4), r ∈ Set.Ioo 0 (Real.pi/2) := fun r hr =>
    ⟨by linarith [hr.1, hs.1, hθ.1], by linarith [hr.2, hπ]⟩
  have hsub1 : Set.uIcc s (Real.pi/4) ⊆ Set.Ioo 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hs.2]; exact hIcc1
  have hstep := Dfun_abs_sub_le hu h hs.2 hsub1
  have hInt : IntervalIntegrable (fun r : ℝ => Work.Elliptic.sinCos2 r * |g r|) volume θ (Real.pi/4) :=
    ((mass_cont (cont_g hu h)).mono hsub0).intervalIntegrable
  have hmono : (∫ r in s..(Real.pi/4), Work.Elliptic.sinCos2 r * |g r|) ≤ Ml g θ := by
    rw [Ml]
    refine intervalIntegral.integral_mono_interval hs.1 hs.2 (le_refl _) ?_ hInt
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg (sinCos2_nonneg' (hIcc0 r ⟨hr.1.le, hr.2⟩)) (abs_nonneg _)
  have h2 : |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)
      - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s| ≤ 2 * Ml g θ := le_trans hstep (by linarith)
  have hcomm : |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s
      - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)|
      = |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)
          - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s| := abs_sub_comm _ _
  calc |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s|
      = |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)
          + (Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s
              - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4))| := by ring_nf
    _ ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)|
        + |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s
            - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)| := abs_add_le _ _
    _ ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)| + 2 * Ml g θ := by
        rw [hcomm]; linarith

/-- Pointwise bound on `D u` on the right half: `|D u s| ≤ |D u (π/4)| + 2 Mr g θ`. -/
theorem Dfun_le_right {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi/2)))
    (h : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi/4) (Real.pi/2)) {s : ℝ} (hs : s ∈ Set.Icc (Real.pi/4) θ) :
    |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s|
      ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)| + 2 * Mr g θ := by
  have hπ := Real.pi_pos
  have hIcc0 : ∀ r ∈ Set.Icc (Real.pi/4) θ, r ∈ Set.Ioo 0 (Real.pi/2) := fun r hr =>
    ⟨by linarith [hr.1, hπ], by linarith [hr.2, hθ.2]⟩
  have hsub0 : Set.uIcc (Real.pi/4) θ ⊆ Set.Ioo 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hθ.1]; exact hIcc0
  have hIcc1 : ∀ r ∈ Set.Icc (Real.pi/4) s, r ∈ Set.Ioo 0 (Real.pi/2) := fun r hr =>
    ⟨by linarith [hr.1, hπ], by linarith [hr.2, hs.2, hθ.2]⟩
  have hsub1 : Set.uIcc (Real.pi/4) s ⊆ Set.Ioo 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hs.1]; exact hIcc1
  have hstep := Dfun_abs_sub_le hu h hs.1 hsub1
  have hInt : IntervalIntegrable (fun r : ℝ => Work.Elliptic.sinCos2 r * |g r|) volume (Real.pi/4) θ :=
    ((mass_cont (cont_g hu h)).mono hsub0).intervalIntegrable
  have hmono : (∫ r in (Real.pi/4)..s, Work.Elliptic.sinCos2 r * |g r|) ≤ Mr g θ := by
    rw [Mr]
    refine intervalIntegral.integral_mono_interval (le_refl _) hs.1 hs.2 ?_ hInt
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg (sinCos2_nonneg' (hIcc0 r ⟨hr.1.le, hr.2⟩)) (abs_nonneg _)
  have h2 : |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s
      - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)| ≤ 2 * Mr g θ :=
    le_trans hstep (by linarith)
  calc |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s|
      = |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)
          + (Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s
              - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4))| := by ring_nf
    _ ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)|
        + |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s
            - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)| := abs_add_le _ _
    _ ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)| + 2 * Mr g θ := by linarith

/-- The growth bound for the quotient `R u = u/sin 2θ` on the left half. -/
theorem Rfun_bound_left {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi/2)))
    {θ B : ℝ} (hθ : θ ∈ Set.Ioc 0 (Real.pi/4))
    (hD : ∀ s ∈ Set.Icc θ (Real.pi/4), |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s| ≤ B) :
    |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ|
      ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)|
        + B * (∫ s in θ..(Real.pi/4), 1/(Real.cos s * (Real.sin (2*s))^2)) := by
  have hπ := Real.pi_pos
  have hIcc : ∀ r ∈ Set.Icc θ (Real.pi/4), r ∈ Set.Ioo 0 (Real.pi/2) := fun r hr =>
    ⟨by linarith [hr.1, hθ.1], by linarith [hr.2, hπ]⟩
  have hsub : Set.uIcc θ (Real.pi/4) ⊆ Set.Ioo 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hθ.2]; exact hIcc
  have hftc : ∫ s in θ..(Real.pi/4),
      (-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s)
        / (Real.cos s * (Real.sin (2*s))^2))
      = Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)
        - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => Work.FTS.EllipticEst.H2W.Lzero1Growth.Rfun_hasDerivAt hu (hsub hs))
      (((Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_Rderiv hu).mono hsub).intervalIntegrable)
  have h1 : |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ
      - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)|
      ≤ ∫ s in θ..(Real.pi/4),
          |-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s)
            / (Real.cos s * (Real.sin (2*s))^2)| := by
    rw [abs_sub_comm, ← hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hθ.2
  have hpt : ∀ s ∈ Set.Icc θ (Real.pi/4),
      |-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s)
        / (Real.cos s * (Real.sin (2*s))^2)|
        ≤ B * (1/(Real.cos s * (Real.sin (2*s))^2)) := by
    intro s hs
    have hsI := hIcc s hs
    have hden : 0 < Real.cos s * (Real.sin (2*s))^2 := by
      refine mul_pos ?_ (pow_pos ?_ 2)
      · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hsI.1, hπ], hsI.2⟩
      · exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hsI.1]) (by linarith [hsI.2, hπ])
    rw [abs_div, abs_neg, abs_of_pos hden, div_le_iff₀ hden]
    rw [show B * (1/(Real.cos s * (Real.sin (2*s))^2)) * (Real.cos s * (Real.sin (2*s))^2) = B by
      rw [mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hden), mul_one]]
    exact hD s hs
  have hinv : ContinuousOn (fun s : ℝ => B * (1/(Real.cos s * (Real.sin (2*s))^2)))
      (Set.Ioo 0 (Real.pi/2)) :=
    Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_invker.const_mul B
  have h2 : (∫ s in θ..(Real.pi/4),
        |-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s)
          / (Real.cos s * (Real.sin (2*s))^2)|)
      ≤ B * (∫ s in θ..(Real.pi/4), 1/(Real.cos s * (Real.sin (2*s))^2)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hθ.2 ?_ ?_ hpt
    · exact (((Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_Rderiv hu).abs).mono
        hsub).intervalIntegrable
    · exact (hinv.mono hsub).intervalIntegrable
  calc |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ|
      = |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)
          + (Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ
              - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4))| := by ring_nf
    _ ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)|
        + |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ
            - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)| := abs_add_le _ _
    _ ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)|
        + B * (∫ s in θ..(Real.pi/4), 1/(Real.cos s * (Real.sin (2*s))^2)) := by
        have := le_trans h1 h2
        linarith

/-- The growth bound for the quotient `R u = u/sin 2θ` on the right half. -/
theorem Rfun_bound_right {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi/2)))
    {θ B : ℝ} (hθ : θ ∈ Set.Ico (Real.pi/4) (Real.pi/2))
    (hD : ∀ s ∈ Set.Icc (Real.pi/4) θ, |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s| ≤ B) :
    |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ|
      ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)|
        + B * (∫ s in (Real.pi/4)..θ, 1/(Real.cos s * (Real.sin (2*s))^2)) := by
  have hπ := Real.pi_pos
  have hIcc : ∀ r ∈ Set.Icc (Real.pi/4) θ, r ∈ Set.Ioo 0 (Real.pi/2) := fun r hr =>
    ⟨by linarith [hr.1, hπ], by linarith [hr.2, hθ.2]⟩
  have hsub : Set.uIcc (Real.pi/4) θ ⊆ Set.Ioo 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hθ.1]; exact hIcc
  have hftc : ∫ s in (Real.pi/4)..θ,
      (-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s)
        / (Real.cos s * (Real.sin (2*s))^2))
      = Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ
        - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => Work.FTS.EllipticEst.H2W.Lzero1Growth.Rfun_hasDerivAt hu (hsub hs))
      (((Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_Rderiv hu).mono hsub).intervalIntegrable)
  have h1 : |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ
      - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)|
      ≤ ∫ s in (Real.pi/4)..θ,
          |-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s)
            / (Real.cos s * (Real.sin (2*s))^2)| := by
    rw [← hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hθ.1
  have hpt : ∀ s ∈ Set.Icc (Real.pi/4) θ,
      |-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s)
        / (Real.cos s * (Real.sin (2*s))^2)|
        ≤ B * (1/(Real.cos s * (Real.sin (2*s))^2)) := by
    intro s hs
    have hsI := hIcc s hs
    have hden : 0 < Real.cos s * (Real.sin (2*s))^2 := by
      refine mul_pos ?_ (pow_pos ?_ 2)
      · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hsI.1, hπ], hsI.2⟩
      · exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hsI.1]) (by linarith [hsI.2, hπ])
    rw [abs_div, abs_neg, abs_of_pos hden, div_le_iff₀ hden]
    rw [show B * (1/(Real.cos s * (Real.sin (2*s))^2)) * (Real.cos s * (Real.sin (2*s))^2) = B by
      rw [mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hden), mul_one]]
    exact hD s hs
  have hinv : ContinuousOn (fun s : ℝ => B * (1/(Real.cos s * (Real.sin (2*s))^2)))
      (Set.Ioo 0 (Real.pi/2)) :=
    Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_invker.const_mul B
  have h2 : (∫ s in (Real.pi/4)..θ,
        |-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s)
          / (Real.cos s * (Real.sin (2*s))^2)|)
      ≤ B * (∫ s in (Real.pi/4)..θ, 1/(Real.cos s * (Real.sin (2*s))^2)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hθ.1 ?_ ?_ hpt
    · exact (((Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_Rderiv hu).abs).mono
        hsub).intervalIntegrable
    · exact (hinv.mono hsub).intervalIntegrable
  calc |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ|
      = |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)
          + (Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ
              - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4))| := by ring_nf
    _ ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)|
        + |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ
            - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)| := abs_add_le _ _
    _ ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)|
        + B * (∫ s in (Real.pi/4)..θ, 1/(Real.cos s * (Real.sin (2*s))^2)) := by
        have := le_trans h1 h2
        linarith

/-! ## The two half-bounds -/

/-- The pole bound on the left half `(0, π/4]`. -/
theorem leftHalf {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi/2)))
    (h : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {C : ℝ} (hC : 0 < C)
    (hb : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      |g θ| ≤ C * (1 / θ ^ 2 + 1 / (Real.pi / 2 - θ) ^ 2)) :
    ∀ θ ∈ Set.Ioc (0:ℝ) (Real.pi/4),
      |u θ| ≤ (Real.pi^2 * (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)|
        + |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)|
        + C * (Real.pi/4 + 4/Real.pi) + 1)) * θ⁻¹ := by
  intro θ hθ
  have hπ := Real.pi_pos
  have hθpos : 0 < θ := hθ.1
  set R := |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)| with hRdef
  set A := |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)| with hAdef
  set K := C * (Real.pi/4 + 4/Real.pi) with hKdef
  have hRnn : 0 ≤ R := by rw [hRdef]; exact abs_nonneg _
  have hAnn : 0 ≤ A := by rw [hAdef]; exact abs_nonneg _
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  have hinvnn : 0 ≤ θ⁻¹ := inv_nonneg.mpr hθpos.le
  have hmass : Ml g θ ≤ K * θ⁻¹ := by
    have hb' := (sinCos2MassBound (cont_g hu h) hC hb).1 θ hθ
    simpa only [Ml, hKdef] using hb'
  have hD : ∀ s ∈ Set.Icc θ (Real.pi/4),
      |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s| ≤ A + 2 * K * θ⁻¹ := by
    intro s hs
    have h1 := Dfun_le_left hu h hθ hs
    rw [← hAdef] at h1
    have h2m : 2 * Ml g θ ≤ 2 * (K * θ⁻¹) := by linarith
    linarith
  have hRf := Rfun_bound_left hu hθ hD
  rw [← hRdef] at hRf
  have hker : (∫ s in θ..(Real.pi/4), 1/(Real.cos s * (Real.sin (2*s))^2))
      ≤ (Real.pi^2/8) * θ⁻¹ := by
    have hk := lzeroGrowthKernelLeft hθ
    rwa [div_eq_mul_inv] at hk
  have hBnn : 0 ≤ A + 2 * K * θ⁻¹ := by positivity
  have hstep : |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ|
      ≤ R + (A + 2 * K * θ⁻¹) * ((Real.pi^2/8) * θ⁻¹) := by
    refine le_trans hRf ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hker hBnn)
  have hsinpos : 0 < Real.sin (2*θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · linarith
    · linarith [hθ.2, hπ]
  have hsinIoo : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) := ⟨hθpos, by linarith [hθ.2, hπ]⟩
  have huabs : |u θ| = |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ| * Real.sin (2*θ) := by
    rw [← Work.FTS.EllipticEst.H2W.Lzero1Growth.Rfun_mul_sin (u := u) hsinIoo, abs_mul,
      abs_of_pos hsinpos]
  have hRHSnn : 0 ≤ R + (A + 2 * K * θ⁻¹) * ((Real.pi^2/8) * θ⁻¹) := by positivity
  have hsinle : Real.sin (2*θ) ≤ 2*θ := Real.sin_le (by linarith)
  have hexp : (R + (A + 2 * K * θ⁻¹) * ((Real.pi^2/8) * θ⁻¹)) * (2 * θ)
      = 2 * R * θ + A * (Real.pi^2/4) + (K * (Real.pi^2/2)) * θ⁻¹ := by
    have hθne : θ ≠ 0 := ne_of_gt hθpos
    field_simp
    ring
  have hfin : 2 * R * θ + A * (Real.pi^2/4) + (K * (Real.pi^2/2)) * θ⁻¹
      ≤ Real.pi^2 * (R + A + K + 1) * θ⁻¹ := by
    have hθ1 : θ ≤ 1 := by linarith [hθ.2, Real.pi_lt_four]
    have h1inv : 1 ≤ θ⁻¹ := (one_le_inv₀ hθpos).mpr hθ1
    have hθle : θ ≤ θ⁻¹ := le_trans hθ1 h1inv
    have hpi2 : (2:ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
    have e1 : 2 * R * θ ≤ 2 * R * θ⁻¹ := mul_le_mul_of_nonneg_left hθle (by linarith)
    have e2 : A * (Real.pi^2/4) ≤ A * (Real.pi^2/4) * θ⁻¹ := by
      calc A * (Real.pi^2/4) = A * (Real.pi^2/4) * 1 := (mul_one _).symm
        _ ≤ A * (Real.pi^2/4) * θ⁻¹ := mul_le_mul_of_nonneg_left h1inv (by positivity)
    have e3 : 2*R + A*(Real.pi^2/4) + K*(Real.pi^2/2) ≤ Real.pi^2 * (R + A + K + 1) := by
      nlinarith [hRnn, hAnn, hKnn, hpi2, Real.pi_gt_three]
    have e4 : (2*R + A*(Real.pi^2/4) + K*(Real.pi^2/2)) * θ⁻¹
        ≤ Real.pi^2 * (R + A + K + 1) * θ⁻¹ :=
      mul_le_mul_of_nonneg_right e3 hinvnn
    have e5 : 2*R*θ + A*(Real.pi^2/4) + (K*(Real.pi^2/2))*θ⁻¹
        ≤ (2*R + A*(Real.pi^2/4) + K*(Real.pi^2/2)) * θ⁻¹ := by
      have hh : (2*R + A*(Real.pi^2/4) + K*(Real.pi^2/2)) * θ⁻¹
          = 2*R*θ⁻¹ + A*(Real.pi^2/4)*θ⁻¹ + (K*(Real.pi^2/2))*θ⁻¹ := by ring
      rw [hh]; linarith
    linarith [e4, e5]
  calc |u θ| = |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ| * Real.sin (2*θ) := huabs
    _ ≤ (R + (A + 2 * K * θ⁻¹) * ((Real.pi^2/8) * θ⁻¹)) * (2*θ) :=
        mul_le_mul hstep hsinle (le_of_lt hsinpos) hRHSnn
    _ = 2 * R * θ + A * (Real.pi^2/4) + (K * (Real.pi^2/2)) * θ⁻¹ := hexp
    _ ≤ Real.pi^2 * (R + A + K + 1) * θ⁻¹ := hfin

/-- The pole bound on the right half `[π/4, π/2)`. -/
theorem rightHalf {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi/2)))
    (h : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {C : ℝ} (hC : 0 < C)
    (hb : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      |g θ| ≤ C * (1 / θ ^ 2 + 1 / (Real.pi / 2 - θ) ^ 2)) :
    ∀ θ ∈ Set.Ico (Real.pi/4) (Real.pi/2),
      |u θ| ≤ (Real.pi^2 * (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)|
        + |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)|
        + 2 * (C * (Real.pi/4 + 4/Real.pi)) + 1)) * (Real.pi/2 - θ)⁻¹ := by
  intro θ hθ
  have hπ := Real.pi_pos
  set t := Real.pi/2 - θ with htdef
  have htpos : 0 < t := by rw [htdef]; linarith [hθ.2]
  set R := |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)| with hRdef
  set A := |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)| with hAdef
  set K := C * (Real.pi/4 + 4/Real.pi) with hKdef
  have hRnn : 0 ≤ R := by rw [hRdef]; exact abs_nonneg _
  have hAnn : 0 ≤ A := by rw [hAdef]; exact abs_nonneg _
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  have hmass : Mr g θ ≤ K := by
    have hb' := (sinCos2MassBound (cont_g hu h) hC hb).2 θ hθ
    simpa only [Mr, hKdef] using hb'
  have hD : ∀ s ∈ Set.Icc (Real.pi/4) θ,
      |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s| ≤ A + 2 * K := by
    intro s hs
    have h1 := Dfun_le_right hu h hθ hs
    rw [← hAdef] at h1
    linarith
  have hRf := Rfun_bound_right hu hθ hD
  rw [← hRdef] at hRf
  have hker : (∫ s in (Real.pi/4)..θ, 1/(Real.cos s * (Real.sin (2*s))^2))
      ≤ (Real.pi^3/64) / t^2 := by
    have hk := lzeroGrowthKernelRight hθ
    rwa [← htdef] at hk
  have hBnn : 0 ≤ A + 2 * K := by positivity
  have hstep : |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ|
      ≤ R + (A + 2 * K) * ((Real.pi^3/64) / t^2) := by
    refine le_trans hRf ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hker hBnn)
  have hsinpos : 0 < Real.sin (2*θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · linarith [hθ.1, hπ]
    · linarith [hθ.2, hπ]
  have hsinIoo : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) := ⟨by linarith [hθ.1, hπ], hθ.2⟩
  have htt : 2*θ = Real.pi - 2*t := by rw [htdef]; ring
  have huabs : |u θ| = |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ| * Real.sin (2*θ) := by
    rw [← Work.FTS.EllipticEst.H2W.Lzero1Growth.Rfun_mul_sin (u := u) hsinIoo, abs_mul,
      abs_of_pos hsinpos]
  have hRHSnn : 0 ≤ R + (A + 2 * K) * ((Real.pi^3/64) / t^2) := by positivity
  have hsinle : Real.sin (2*θ) ≤ 2 * t := by
    rw [htt, Real.sin_pi_sub]
    exact Real.sin_le (by linarith)
  have hexp : (R + (A + 2 * K) * ((Real.pi^3/64) / t^2)) * (2 * t)
      = 2 * R * t + (A + 2*K) * (Real.pi^3/32) / t := by
    have htne : t ≠ 0 := ne_of_gt htpos
    field_simp
    ring
  have hfin : 2 * R * t + (A + 2*K) * (Real.pi^3/32) / t
      ≤ Real.pi^2 * (R + A + 2*K + 1) / t := by
    have htle : t ≤ Real.pi/4 := by rw [htdef]; linarith [hθ.1]
    have e1 : 2 * R * t ≤ R * (Real.pi^2/8) / t := by
      rw [le_div_iff₀ htpos]
      have ht2 : t^2 ≤ (Real.pi/4)^2 := pow_le_pow_left₀ htpos.le htle 2
      nlinarith [ht2, hRnn]
    have hA2K : 0 ≤ A + 2*K := by positivity
    have hpi : Real.pi^3/32 ≤ Real.pi^2 := by nlinarith [Real.pi_lt_four, hπ]
    have e2 : (A + 2*K) * (Real.pi^3/32) / t ≤ (A + 2*K) * Real.pi^2 / t := by
      rw [div_le_div_iff_of_pos_right htpos]
      nlinarith [hA2K, hpi]
    have e3 : R * (Real.pi^2/8) / t + (A + 2*K) * Real.pi^2 / t
        ≤ Real.pi^2 * (R + A + 2*K + 1) / t := by
      rw [← add_div, div_le_div_iff_of_pos_right htpos]
      nlinarith [hRnn, hAnn, hKnn, hπ]
    linarith [e1, e2, e3]
  calc |u θ| = |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ| * Real.sin (2*θ) := huabs
    _ ≤ (R + (A + 2 * K) * ((Real.pi^3/64) / t^2)) * (2 * t) :=
        mul_le_mul hstep hsinle (le_of_lt hsinpos) hRHSnn
    _ = 2 * R * t + (A + 2*K) * (Real.pi^3/32) / t := hexp
    _ ≤ Real.pi^2 * (R + A + 2*K + 1) / t := hfin
    _ = Real.pi^2 * (R + A + 2*K + 1) * (Real.pi/2 - θ)⁻¹ := by rw [htdef, div_eq_mul_inv]

/-- **The pole bound from a pointwise source bound.** -/
theorem poleBoundOfSourcePointwise {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {C : ℝ} (hC : 0 < C)
    (hb : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |g θ| ≤ C * (1 / θ ^ 2 + 1 / (Real.pi / 2 - θ) ^ 2)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |u θ| ≤ C' * (1 / θ + 1 / (Real.pi / 2 - θ)) := by
  set CL := Real.pi^2 * (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)|
      + |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)|
      + C * (Real.pi/4 + 4/Real.pi) + 1) with hCLdef
  set CR := Real.pi^2 * (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi/4)|
      + |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi/4)|
      + 2 * (C * (Real.pi/4 + 4/Real.pi)) + 1) with hCRdef
  have hCLnn : 0 ≤ CL := by rw [hCLdef]; positivity
  have hCRnn : 0 ≤ CR := by rw [hCRdef]; positivity
  have hmaxnn : 0 ≤ max CL CR := le_trans hCLnn (le_max_left _ _)
  refine ⟨max CL CR, hmaxnn, ?_⟩
  intro θ hθ
  have htpos : 0 < Real.pi/2 - θ := by linarith [hθ.2]
  have hθnn : 0 ≤ θ⁻¹ := inv_nonneg.mpr hθ.1.le
  have htnn : 0 ≤ (Real.pi/2 - θ)⁻¹ := inv_nonneg.mpr htpos.le
  rcases le_or_gt θ (Real.pi/4) with hle | hgt
  · have hL := leftHalf hu h hC hb θ ⟨hθ.1, hle⟩
    calc |u θ| ≤ CL * θ⁻¹ := hL
      _ ≤ max CL CR * θ⁻¹ := mul_le_mul_of_nonneg_right (le_max_left _ _) hθnn
      _ ≤ max CL CR * (θ⁻¹ + (Real.pi/2 - θ)⁻¹) :=
          mul_le_mul_of_nonneg_left (by linarith) hmaxnn
      _ = max CL CR * (1/θ + 1/(Real.pi/2 - θ)) := by rw [← one_div, ← one_div]
  · have hR := rightHalf hu h hC hb θ ⟨le_of_lt hgt, hθ.2⟩
    calc |u θ| ≤ CR * (Real.pi/2 - θ)⁻¹ := hR
      _ ≤ max CL CR * (Real.pi/2 - θ)⁻¹ := mul_le_mul_of_nonneg_right (le_max_right _ _) htnn
      _ ≤ max CL CR * (θ⁻¹ + (Real.pi/2 - θ)⁻¹) :=
          mul_le_mul_of_nonneg_left (by linarith) hmaxnn
      _ = max CL CR * (1/θ + 1/(Real.pi/2 - θ)) := by rw [← one_div, ← one_div]

end Work.FTS.EllipticEst.H2W.WeakPureAux
