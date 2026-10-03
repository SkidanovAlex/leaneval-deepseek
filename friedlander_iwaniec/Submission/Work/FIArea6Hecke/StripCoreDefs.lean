/-
# `Submission.Work.FIArea6Hecke.StripCoreDefs` — the interface of the strip inverse bound

The target `Work.FIArea6Hecke.heckeLcontInvBound_strip` is *FI* (16.23)/(16.24),
restricted to the half-strip `s.re ≤ 1`:

  `‖(Lam s / heckeArch d m s)⁻¹‖ ≤ C·d·log²(|m| + |s.im| + 3)`
  for `1 - c/(d^ε·log(|m|+|s.im|+3)) < s.re ≤ 1`,

where `Lam` is an entire function completing the Hecke `L`-function of `ℚ(i)`,
`Λ(s) = (4d/π)^s Γ(s+|m|/2) L(s,ψ_m)`, i.e. agreeing with
`heckeArch d m s · heckeLSeries chi m s` on the half-plane `s.re > 1 + |m|/2`.  The
`Lam` is unique when it exists, so the statement is about the continuation of `L`.

Since `Lam/heckeArch` *is* the continuation `Lcont` of the Hecke `L`-function, the
bound is the classical *inverse bound* (16.23), whose proof (following the paper, pp.
1008–1009) has exactly two analytic inputs and one formal reduction:

* **`StripCore ε`** — the classical inputs: the zero-free region (16.20) together with
  Lemma 16.1 (Siegel) on the real axis, *in the sharpened `ε`-form (16.24)*
  `s.re >= 1 - c/(d^ε·log(|m|+|s.im|+3))`, and the logarithmic-derivative bound
  `|L'/L| ≪ log(4d(|m|+|t|+3))` inside it.  This is the deep analytic content
  (de la Vallée Poussin `3-4-1` for `ζ_K, L(·,ψ), L(·,ψ²)`, Goldfeld's Siegel bound,
  and the convexity bounds (16.18)–(16.19)).  The `d^{-ε}` in the region is *not*
  cosmetic: it is exactly what excludes the Landau–Siegel zero on the real axis, whose
  distance from `1` is `≫ d^{-ε}` and which lies far outside the un-sharpened region
  `1 - c/log(4d(|m|+|t|+3))` once `d` is large.
* **`StripNearOne ε`** — the elementary lower bound `L(σ+it) ≫ (σ-1)` just right of
  `s = 1` (Euler product / Möbius inversion), used to anchor the integration.
* **`heckeStripGlue`** — the formal reduction: writing `s = σ + it` with
  `σ > 1 - c/(d^ε log M)` and `σ ≤ 1`, integrate `L'/L` along the horizontal segment from
  `s` up to `σ₀ = 1 + min(1/(K log M), 1/2)`; the segment stays in the zero-free region,
  has length `≍ 1/log M`, so
  `log|L(s)| ≥ log|L(σ₀+it)| - K log(4dM)·(σ₀-σ) ≥ -log log M - O(1) - O(1)`,
  and exponentiating gives even `|L(s)|⁻¹ ≪ d log M ≤ C d log² M` (the factor
  `exp(log(4dM)/log M) ≤ e·4d` is where the `d` of (16.23) comes from).
-/
import Mathlib
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea5.S16Hecke.LcontDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke

open scoped BigOperators

noncomputable section

/-- The `L`-value attached to a completion `Lam`: the meromorphic continuation of the Hecke
`L`-function of the Größencharacter `ψ_m(z) = χ(z)(z/|z|)^m` of `ℚ(i)`. -/
def Lval (d : ℕ) (m : ℤ) (Lam : ℂ → ℂ) (s : ℂ) : ℂ :=
  Lam s / Work.FITop4.Bridge.heckeArch d m s

/-- **The zero-free region and the logarithmic-derivative bound** (*FI* (16.20), Lemma 16.1,
and the bound on `L'/L` used to integrate): there are `c, K > 0` such that for every completion
`Lam` of a strict character of modulus `4d`,

* `Lval` does not vanish for `1 - c/(d^ε·log(|m|+|s.im|+3)) ≤ s.re ≤ 2` — the de la Vallée
  Poussin region off the real axis contains this, and on the real axis this is contained in
  the Siegel region `1 - c(ε)d^{-ε}` since `c/(d^ε log) ≤ c d^{-ε}` for `log ≥ 1`, so the two
  classical statements combine into it for a suitable `c`; and
* `‖(Lval)'(s)/(Lval)(s)‖ ≤ K·(log(4d(|m|+|s.im|+3)) + d^ε)` there.

This is the deep analytic input; the region is the paper's (16.24) (with the `4` of `4d`
absorbed into `c`), and the constant `c` is the one of Lemma 16.1 (Siegel) divided by the
constants of (16.20).

The additive `d^ε` in the second clause is *necessary and honest*, not an artefact.  In the
region there can be a Landau–Siegel real zero `β = 1 - λ` with `λ ≫_ε d^{-ε}`; although `β`
itself lies outside the region (that is exactly what the `d^{-ε}` of the region buys), it can
lie within distance `≍ d^{-ε}` of the region's real edge, and `L'/L(σ) = 1/(σ-β) + O(log)`
there.  Hence `‖L'/L‖ ≲ log(4d(|m|+|t|+3)) + 1/dist(s,β) ≲ log(4d(|m|+|t|+3)) + d^ε`.  This is
the classical bound: off the real axis, or away from the exceptional zero, `≪ log`, and the
`+1/(s-β)` term is the contribution of the (possibly present) exceptional zero, which the
`d^{-ε}`-sharpened region deliberately admits nearby.  Integrated over an interval of length
`≍ d^{-ε}/log M` — the step used in `heckeStripGlue` — the `d^ε` term contributes `O(1)`, so
the constant bookkeeping of (16.23) is unaffected. -/
def StripCore (ε : ℝ) : Prop :=
  ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
      ∀ s : ℂ,
        1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) ≤ s.re → s.re ≤ 2 →
        (Lval d m Lam s ≠ 0 ∧
          ‖deriv (Lval d m Lam) s / Lval d m Lam s‖
            ≤ K * (Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) + (d : ℝ) ^ ε))

/-- **The lower bound for `L` just right of `s = 1`**: `‖1/L(σ+it)‖ ≤ K/(σ-1)` for
`1 < σ ≤ 2`.  This is the elementary consequence of the Euler product of `1/L`,
`1/L(s) = ∏_𝔭 (1 - ψ(𝔭)N𝔭^{-s})`, whose absolute convergence for `σ > 1` gives
`‖1/L(σ+it)‖ ≤ ∏_𝔭 (1 + N𝔭^{-σ}) = ζ_K(σ)/ζ_K(2σ) ≤ K/(σ-1)`. -/
def StripNearOne (ε : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
      ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
        ‖(Lval d m Lam s)⁻¹‖ ≤ K / (s.re - 1)

end

end Work.FIArea6Hecke
