/-
# `Submission.Work.FIArea6Hecke.R.LogDerivStatementDefs` — the analytic input of the
log-derivative bound `R/heckeStripLogDeriv`, as a `Prop`.

The target `Work.FIArea6Hecke.R.heckeStripLogDeriv` is the second conjunct of `StripCore ε`:

  `‖(Lval d m Lam)'(s)/Lval d m Lam s‖ ≤ K·(log(4d(|m|+|s.im|+3)) + d^ε)`
  for `1 - c/(d^ε·log(|m|+|s.im|+3)) ≤ s.re ≤ 2`,

where `Lval d m Lam = Lam s / heckeArch d m s` and `Lam` is an entire completion of
`Λ(s,ψ) = (4d/π)^s Γ(s+|m|/2)L(s,ψ)`, `ψ(z) = χ(z)(z/|z|)^m`.

## How the target is reduced (the assembly in `R/heckeStripLogDeriv`)

The norm bound is *not* obtained by bounding `L'/L` directly (the Hadamard expansion gives the
*norm* only with a `log²`-loss: the sum over the zeros with `|γ-t| ≤ 1` has `≪ log(4dM)` terms each
of size `≪ 1/dist(s,ρ) ≪ log(4dM)`).  It is obtained by the classical **one-sided ⟹ two-sided**
argument (Landau–Littlewood), exactly as in
`Commons/NumberTheory/Zeta/zeta_inv_le_log_zeroFree` (`hzeta_bound`):

* put `F := -Lval'(s)/Lval(s)`;
* on a ball `B(cb,R)` (zero-free, by `R/heckeStripZFR` and its companions) the **one-sided**
  bound `Re F ≤ Bnd` holds — this is `LogDerivReLower` below (up to sign);
* `G := F - F cb` satisfies `G cb = 0` and `Re G ≤ Bnd + |F cb|`, so Borel–Carathéodory
  (`Commons.Analysis.Complex.borelCaratheodory_deriv_le`) bounds `‖G'‖ ≤ 8(Bnd+|F cb|)/R` on the
  ball, and the mean-value inequality along the segment from `cb` to `s` gives
  `‖G s‖ ≤ 4(Bnd + |F cb|)`;
* at the centre `cb` (chosen with `cb.re > 1`, in the half-plane of absolute convergence) the
  *crude* Dirichlet-series bound `‖L'/L(σ+it)‖ ≤ 1/(σ-1) + O(log(4dM))` is sharp enough — one takes
  `cb = 1 + c/(3·log(4dM))` in the regime where the zero-free depth is logarithmic in `log(4dM)`
  (`d^ε ≲ log(4dM)`, the case `d` small), where `1/(cb.re-1) ≍ log(4dM)`, and
  `cb = 1 + c'·d^{-ε}/4` in the regime `d^ε ≳ log(4dM)`, where `1/(cb.re-1) ≍ d^ε`.  The two
  choices are what turns the `+ d^ε` in the target into the *honest* exceptional-zero term
  (the real zero `β` has `1-β ≥ c'd^{-ε}` by Lemma 16.1, so it is the only zero that can sit at
  distance `≍ d^{-ε}` from `1`, and the centre must be kept clear of it).

## The two inputs a proof of `LogDerivReLower` needs

1. **The Hadamard partial fraction of the completion** `Λ` — `FIArea5/HeckeZFR/Lam_partialFraction`
   (the four sub-lemmas `Lam_zeroCount`, `Lam_goodRadius`, `Lam_factorZero`, `Lam_cofactorBound`,
   `Lam_pfConv` are the in-flight parts), which needs the circle growth of `Λ`; the latter comes from
   Hecke's functional equation (`heckeFE_primitive_full`) plus the convexity strip bound
   `heckeLStripBound2` (16.18) and the half-plane growth `heckeLambda_stripGrowth`.
2. **The zero-free region inputs** `ZFRoffAxis` (de la Vallée Poussin, 16.20) and
   `ZFRrealAxis ε` (Lemma 16.1, Landau–Siegel) of `R/ZFRStatementDefs`, used *twice*:
   (a) to know that at a point `s` of the region every zero of `Λ` lies to its **left**
   (`u.re ≤ 1 - c'·min(1/log(4d+|m|+|u.im|), d^{-ε}) < s.re`), and (b) to know that the zeros
   within `|u.im - t| ≤ 1` are at real-part distance `≫ min(1/log(4d(|m|+|t|+3)), d^{-ε})`.

With the partial fraction at the base point `s₁ := 2 + it` (the same imaginary part as `s`), the
kernel is `(2-σ)/[(s-u)(2+it-u)]`, whose real part is bounded by `4/(δ²+1)` (with `δ = |t-u.im|`)
because `2 - β_u ≥ 1`; the sum of these kernels against the divisor is controlled by the
**weighted zero sum** `Σ_u ord(u)/(1+δ_u²) ≪ log(4d(|m|+|t|+3))`, which is itself a consequence of
the partial fraction evaluated at `2 + it` (all zeros lie in the critical strip, so every kernel has
nonnegative real part there) together with the bound at `σ = 2`
(`LSeriesBound.heckeLSeries_logDeriv_norm_le`, `LamBaseBound`, `DigammaShift`).  This gives

  `Re (Λ'/Λ)(s) ≥ Re (Λ'/Λ)(2+it) - C·log(4d(|m|+|t|+3)) ≥ -C·log(4d(|m|+|t|+3))`,

and subtracting the archimedean part `log(4d/π) + ψ(s+|m|/2)` (bounded above by
`DigammaShift.digamma_re_le_of_half_le`) yields `Re (Lval'/Lval)(s) ≥ -C'·log(4dM)`.  This is the
input below.  Note that only the *lower* bound of the real part is needed — the hard direction
(controlling the positive kernels) is exactly what is replaced by Borel–Carathéodory above.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FIArea6Hecke.ZFRDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- **The one-sided logarithmic-derivative bound in the zero-free region**
(*FI* (16.20)/(16.23)): the real part of `(Lval d m Lam)'(s)/Lval d m Lam s` is
`≥ -C·log(4d(|m|+|s.im|+3))` for every strict character `χ` mod `4d`, every `m : ℤ`, every entire
completion `Lam` of `Λ(s,ψ)` and every `s` with

  `1 - c·min(1/log(4d + |m| + |s.im| + 1), d^{-ε}) ≤ re s ≤ 2`.

**Why the region is necessary** (two independent reasons, both machine-relevant):

* near a zero `ρ` of `Lam` (`Lval` has the same zeros, `heckeArch` being zero-free in `re s > 0`)
  the expansion `Lval = (z-ρ)^n g`, `g ρ ≠ 0`, gives `Re((Lval)'(s)/Lval s) = -n/|s-ρ| + O(1)`;
  so the bound is *false* for points of the critical strip that come closer to a zero than
  `1/(C log(4d(|m|+|im s|+3)))`;
* the region above is zero-free: by `ZFRoffAxis` no zero has `re u > 1 - c''/log(4d+|m|+|im u|)`
  (unless it is real with `ψ` real), and by `ZFRrealAxis ε` no real zero of real `ψ` has
  `re u > 1 - c'd^{-ε}`.  Hence for `c ≤ min(c'',c')/4` every zero lies **left** of `s`, and even in
  the band `|im u - im s| ≤ 1` (where the zero's own height is comparable to `t = im s`) at distance
  `≫ min(1/log(4d+|m|+|t|+1), d^{-ε})`.

**Proof route.**  Take the Hadamard partial fraction at the pair `(s, s₁ := 2 + i·im s)`; the kernel
is `(2-σ)/[(s-u)(2+it-u)]`.  Since every zero lies in `-1 ≤ re u ≤ 1`
(`HeckeNonvanishing.Lam_zero_re_bounds`) and `σ ≥ 1/2`, one has

* `Re kernel ≥ 0` when `re u ≤ σ` and the kernel is not small, and
* `|Re kernel| ≤ 2` whenever `σ - re u ≥ 0` and the kernel is *negative*,
* `|Re kernel| ≤ 2/δ_u² + 2/δ_u³` when `δ_u := |t - im u| ≥ 1` (independently of `re u`),

so `Re (Λ'/Λ)(s) ≥ Re (Λ'/Λ)(2+it) - 2·#\{δ_u < 1\} - Σ_{δ_u ≥ 1} (2/δ_u² + 2/δ_u³)`, and both
sums are `≪ log(4d(|m|+|t|+3))` by the **weighted zero sum**
`Σ_u ord(u)/(1+δ_u²) ≪ log(4d(|m|+|t|+3))`.  The latter follows from the partial fraction at the
pair `(2+it, -1+it)` — each kernel has nonnegative real part, so
`Σ_u ord(u)(2-re u)/((2-re u)²+δ_u²) ≤ Re[(Λ'/Λ)(2+it) - (Λ'/Λ)(-1+it)]` — together with the
functional equation `Re (Λ'/Λ)(-1+it) = -Re (Λ'/Λ)(2+it)`
(`FELogDeriv.logDeriv_FE_at_neg_one`) and the bound `|(Λ'/Λ)(2+it)| ≪ log(4d(|m|+|t|+3))`
(`LamBaseBound.Lam_logDeriv_re_at_two_le`, `LSeriesBound.heckeLSeries_logDeriv_norm_le`,
`DigammaShift`).  Subtracting the archimedean part `log(4d/π) + ψ(s+|m|/2)`, bounded above by
`DigammaShift.digamma_re_le_of_half_le` (valid because `re s ≥ 1/2 ≥ 1/2 - |m|/2`), gives the claim.
The bound has *no* `d^ε`: the exceptional real zero contributes the *positive* `1/(σ-β)` to the real
part, so it never obstructs a *lower* bound; the `d^ε` of the target reappears from the *centre* of
the Borel–Carathéodory ball (`R/heckeStripLogDeriv`). -/
def LogDerivReLower (ε : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
      ∀ s : ℂ,
        1 - c * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1))
            (1 / (d : ℝ) ^ ε) ≤ s.re → s.re ≤ 2 →
          -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)))
            ≤ (deriv (Lval d m Lam) s / Lval d m Lam s).re

end

end Work.FIArea6Hecke.R
