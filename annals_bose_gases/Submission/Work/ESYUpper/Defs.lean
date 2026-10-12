import ChallengeDeps
import Submission.LhyIntegral
import Submission.Work.SecondOrder.Main
import Submission.Work.TrialState.Basic.integral_mul_pairSum_eq_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/ESYUpper` — the ESY / Yau–Yin upper-bound chapter (vocabulary)

This chapter is the **upper-bound** side of the second-order (Lee–Huang–Yang)
box theorem: the variational computation of Erdős–Schlein–Yau
(arXiv:0806.4873, the LaTeX source `nextorder2.tex` is kept in
`Submission/Work/TrialState/_refs/esy/`) and of Yau–Yin for general potentials.
The Fournais–Solovej Annals paper proves only the *lower* bound and cites `[YY]`
for the upper bound (`final_v2.tex` §1: *"We shall not discuss the upper bound
further in this paper"*).

The chapter supplies, in the corpus's per-sector language
(`Submission/Work/SecondOrder`), the variational family of ESY — the
**pair-excited (quasi-free, squeezed) state** `quasiFreeState` — and

1. the **momentum-space variational core** of the ESY computation, i.e. the
   per-mode minimisation of ESY's Lemma `le-ep` (their eq. `(min)`, `(ep)`,
   `(minval)`) and the sign (AM–GM) lemmas that make the second-order term
   positive — all of it *proved*, see `Min.lean`;
2. the **model Bogoliubov integral** `Φ(0) = √512/15` of ESY (their eq.
   `def:Phi`) and the identification of the resulting constant with the corpus
   LHY constant `128/(15√π)` — see `Phi.lean`;
3. the **Rayleigh-quotient reduction** which removes the *normalisation*
   conjunct of the residual (the coupling constant `s` of `quasiFreeState` is
   exactly the normalisation degree of freedom, and the energy word is
   homogeneous of degree `2`), see `Scale.lean` and `NOTES.md` §3;
4. the **named stage residual** `ESYSqueezeBound` / `ESYUpperBound'` (the
   ESY/Yau–Yin variational computation for the concrete family) and its
   packaging into `Work.SecondOrder.SecondOrderUpperBound'` and into the
   consumer's `hEgc` shape — see `Main.lean`.

## Conventions

* `minVal a b c` is ESY's `m_p` (Lemma `le-ep`), `argMin a b c` their `e_p`,
  `modeVal a b c e` their per-mode quadratic form `(min)`.  The dictionary to
  ESY's notation is `a = p²/ϱ`, `b = V̂_p`, `c = f̂_p` (so their
  `e = e_p`, and `a + 2b = p²/ϱ + 2V̂_p`, `a + 2c = p²/ϱ + 2f̂_p`).
* `PhiESY h` is ESY's `Φ(h)` (`def:Phi`), `lhyC = 128/(15√π)` the corpus LHY
  constant.
* The per-sector family is `Work.SecondOrder.quasiFreeState`; its `s` is the
  condensate amplitude, `c` the squeezing amplitude, `r` the kernel cutoff.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.ESYUpper

open Submission.BoseGases
open _root_.BoseGases
open Work.SecondOrder

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The momentum-space variational core (ESY Lemma `le-ep`) -/

/-- ESY's `m_p`: the **minimal value** of the per-mode quadratic form
(Lemma `le-ep`, eq. `(minval)`):

`m_p = ½ ( √((a+2b)(a+2c)) − (a+b+c) )`.

With the ESY dictionary `a = p²/ϱ`, `b = V̂_p`, `c = f̂_p`. -/
noncomputable def minVal (a b c : ℝ) : ℝ :=
  (1 / 2) * (Real.sqrt ((a + 2 * b) * (a + 2 * c)) - (a + b + c))

/-- ESY's `e_p`: the **minimiser** of the per-mode quadratic form
(Lemma `le-ep`, eq. `(ep)`), in the form `e_p = ½(1 − √((a+2b)/(a+2c)))`
(the two forms
`½(1 − √((a+2b)/(a+2c)))` and `½(1 − √(1 + 2(b−c)/(a+2c)))` agree because
`(a+2b)/(a+2c) = 1 + 2(b−c)/(a+2c)`). -/
noncomputable def argMin (a b c : ℝ) : ℝ :=
  (1 / 2) * (1 - Real.sqrt ((a + 2 * b) / (a + 2 * c)))

/-- ESY's per-mode quadratic form (eq. `(min)`):

`a e²/(1−2e) + b e/(1−2e) − c e`.

It is the energy contribution (per momentum, in units of the density) of the
squeezed mode with amplitude `e`, and it is a *convex* function of `e` on
`(−∞, 1/2)` with minimum `minVal a b c` at `e = argMin a b c`. -/
noncomputable def modeVal (a b c e : ℝ) : ℝ :=
  a * e ^ 2 / (1 - 2 * e) + b * e / (1 - 2 * e) - c * e

/-- ESY's bracket `F(x,p)/√x` of their eq. `(8.4)`, at the data `x = p²/ϱ`,
`b = V̂_p`, `c = f̂_p`:

`√((x+2c)(x+2b)) − (x+b+c) + (b−c)²/(2x)`,

i.e. twice `(minVal x b c + (b−c)²/(4x))`; it is the per-mode integrand of the
ESY second-order correction `Q` (eq. `(omega)`), and it is **nonnegative**
(`Min.lean`, `esyF_nonneg`). -/
noncomputable def esyF (x b c : ℝ) : ℝ :=
  Real.sqrt ((x + 2 * b) * (x + 2 * c)) - (x + b + c) + (b - c) ^ 2 / (2 * x)

/-- The `p`-summand of ESY's `Q` (eq. `(omega)`), at density `ϱ`:

`(ϱ/2)·( √((p²/ϱ+2f)(p²/ϱ+2V)) − (p²/ϱ+V+f) + ϱ(V−f)²/(2p²) )`.

This is the value of the per-mode quadratic form at the optimal amplitude,
plus the compensating term coming from the scattering equation — the quantity
whose mode sum is `Q`.  `esyModeQ_eq` records the equivalent form
`ϱ·minVal (p²/ϱ) V f + ϱ²(V−f)²/(4p²)`. -/
noncomputable def esyModeQ (ϱ p2 V f : ℝ) : ℝ :=
  (ϱ / 2) * (Real.sqrt ((p2 / ϱ + 2 * f) * (p2 / ϱ + 2 * V))
    - (p2 / ϱ + V + f) + ϱ * (V - f) ^ 2 / (2 * p2))

/-- The total ESY second-order correction `Q` (eq. `(omega)`), as a sum over a
finite set of momenta `s` (the box's dual-lattice momenta `p ≠ 0`). -/
noncomputable def esyQ {ι : Type*} (s : Finset ι) (ϱ : ℝ) (p2 V f : ι → ℝ) : ℝ :=
  ∑ p ∈ s, esyModeQ ϱ (p2 p) (V p) (f p)

/-- The optimal per-mode amplitude `e_p = argMin (‖p‖²/ϱ) (V p) (f p)` of a
mode `p` of the box, as a function of `p` (kinetic energy `‖p‖²`, density `ϱ`,
potential coefficients `V`, `f`). -/
noncomputable def optAmp (ϱ : ℝ) (V f : ℝ³ → ℝ) : ℝ³ → ℝ :=
  fun p => argMin (‖p‖ ^ 2 / ϱ) (V p) (f p)

/-- The box's **mode wave-vectors** in the orthant, in the corpus's
normalisation: for a centred box of side `ℓ = 2s` the Neumann modes have wave
numbers `π(k+1)/s`, `k ∈ {0,…,n-1}³` (a finite truncation of the orthant
lattice).  The set is `π/s`-separated and every element has norm `≥ π/s`, i.e.
it satisfies the geometric hypotheses of `Work.ESYUpper.AmplitudeBounds` with
`Δ = π/s = 2π/ℓ` (`orthantModes_props`). -/
noncomputable def orthantModes (s : ℝ) (n : ℕ) : Finset ℝ³ :=
  (Fintype.piFinset (fun _ : Fin 3 => Finset.range n)).image
    (fun k : Fin 3 → ℕ =>
      (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => Real.pi * ((k i : ℝ) + 1) / s))

/-! ## The ESY amplitude algebra (the `e_p` form of `Ω₂ + Ω₄`) -/

/-- ESY's `θ_p = |c_p|²/(1−|c_p|²)`, expressed through the amplitude `e_p` via
their relation `(rel)`: `θ_p = e_p²/(1−2e_p)`. -/
noncomputable def thetaE (e : ℝ) : ℝ := e ^ 2 / (1 - 2 * e)

/-- ESY's `e_p(1−e_p)/(1−2e_p)`, the amplitude combination that replaces
`Re c_p/(1−|c_p|²)` in their rewriting of `E_M` and of `Ω₄`. -/
noncomputable def ampE (e : ℝ) : ℝ := e * (1 - e) / (1 - 2 * e)

/-- ESY's `Ω₂` (eq. `(omega2)`): the *linear* corrections in the amplitude, for
a finite mode set `s` (the box's momenta `p ≠ 0`), with `V0 = V̂_0`,
`V p = V̂_p`, `Λ = |Λ|` the volume, and `θ_p = thetaE (e p)`. -/
noncomputable def Omega2 {ι : Type*} (s : Finset ι) (V0 Λ : ℝ) (V : ι → ℝ)
    (e : ι → ℝ) : ℝ :=
  - (∑ p ∈ s, (V p + V0) / Λ * (∑ m ∈ s, thetaE (e m)) * thetaE (e p))
    + V0 / (2 * Λ) * (∑ m ∈ s, thetaE (e m)) ^ 2

/-- ESY's `Ω₄` (eq. `(omega3)`) in the `θ`-form: the quartic remainder.  Here
`Vsub p r = V̂_{p−r}`, `V2p p = V̂_{2p}`, and the diagonal compensation term
`V0 θ_p(1+4θ_p) + V̂_{2p}θ_p(1+2θ_p)` is ESY's second bracket (the conversion
from their `|c_p|²` form to the `θ` form uses
`θ(1+4θ) = (e(1−e)/(1−2e))²·(1+3(e/(1−e))²)` and
`θ(1+2θ) = (e(1−e)/(1−2e))²·(1−2e+2e²)/(1−e)²`, both verified identically).

*Note on the index set*: ESY sum over `r ≠ 0, ±p`.  An abstract index type `ι`
carries no negation, so the sum below runs over `r ≠ p` only; the extra terms
`r = −p` are *nonnegative* (all data is nonnegative), so the quantity defined
here dominates ESY's `Ω₄` — which is all an upper-bound stage needs. -/
noncomputable def Omega4 {ι : Type*} [DecidableEq ι] (s : Finset ι) (V0 Λ : ℝ) (Vsub : ι → ι → ℝ)
    (V2p : ι → ℝ) (e : ι → ℝ) : ℝ :=
  ∑ p ∈ s, ((1 / (2 * Λ)) * (∑ r ∈ s.filter (fun r => r ≠ p),
        (V0 + Vsub p r) * (thetaE (e p) * thetaE (e r)))
      + (1 / (2 * Λ)) * (V0 * (thetaE (e p) * (1 + 4 * thetaE (e p)))
          + V2p p * (thetaE (e p) * (1 + 2 * thetaE (e p)))))

/-! ## The model integral and the LHY constant -/

/-- ESY's model function (`def:Phi`):

`Φ(h) = ∫₀^∞ y^{1/2} ( √((y+2h)(y+2+2h)) − (y+1+2h) + 1/(2y) ) dy`.

`PhiESY_zero` (`Phi.lean`) proves `Φ(0) = √512/15`; this is the origin of the
sharp constant `128/(15√π)` in the second-order term. -/
noncomputable def PhiESY (h : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ),
    Real.sqrt y * (Real.sqrt ((y + 2 * h) * (y + 2 + 2 * h)) - (y + 1 + 2 * h)
      + 1 / (2 * y))

/-- The corpus's LHY constant `128/(15√π)` (the sharp constant of
`Submission.LhyIntegral`, FS `thm:LHY-Box`). -/
noncomputable def lhyC : ℝ := 128 / (15 * Real.sqrt π)

/-! ## The corpus-side residual -/

/-- **The ESY variational residual, Rayleigh form.**  For the concrete
pair-excited family of `Work.SecondOrder.quasiFreeState` there are data
`(c, r)` — squeezing amplitude and kernel cutoff — such that the (unnormalised,
`s = 1`) state is *continuous*, has *nonzero* box norm square, and satisfies the
**Rayleigh-quotient inequality**

`pairStateE ≤ θ · pairStateZ`,  `θ := −4πμ²(a v)ℓ³(1 − C(μ(a v)³)^{1/2})`.

The condensate amplitude `s` is *not* mentioned: it is exactly the
normalisation degree of freedom, and the energy word `pairStateE` and the norm
square `pairStateZ` are both homogeneous of degree `2` in the state
(`Scale.lean`), so `Rayleigh` reaches the normalized residual
`Work.SecondOrder.QuasiFreeBound` for every `1 ≤ N` (`Main.quasiFreeBound_of_rayleigh`).

This is the chapter's named residual: the ESY/Yau–Yin variational computation.
See `NOTES.md` for its decomposition into ESY's Lemmas `lm:EM`, `le-ep`, `lm:E`
and the mode-sum limit. -/
def ESYRayleigh (N : ℕ) (ℓ μ C : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  ∃ c r : ℝ, ∃ hr : 0 < r,
    Continuous (quasiFreeState N 1 c r hr (Classical.choose h)) ∧
      0 < pairStateZ N ℓ (TrialState.orbConst 1) (bogWeight c)
            (bogKernel r hr (Classical.choose h)) ∧
      pairStateE N ℓ μ v h (TrialState.orbConst 1) (bogWeight c)
          (bogKernel r hr (Classical.choose h))
        ≤ (- 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * pairStateZ N ℓ (TrialState.orbConst 1) (bogWeight c)
                (bogKernel r hr (Classical.choose h))

/-- **The dilute-window ESY residual.**  `ESYRayleigh` in the nonempty sector
and the dilute window `μ(a v)³ ≤ ε`.  This is the hypothesis-corrected form in
which the chapter expects the ESY variational computation to be delivered
(cf. `Work.SecondOrder.SecondOrderUpperBound'`). -/
def ESYUpperBound' (N : ℕ) (ℓ μ C ε : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  1 ≤ N → μ * (a v) ^ 3 ≤ ε → ESYRayleigh N ℓ μ C v h

end Work.ESYUpper
