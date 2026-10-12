import ChallengeDeps
import Submission.Work.MGroupInput.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MGroupInput.Residual` — the one corpus piece the honest `m`-arm lacks

`Work.MGroupInput.MGroupWindow Cn` (FS's `m`-arm on the window `u ≥ Cn μ`,
`Defs.lean`) is what replaces the FALSE `Work.DLRepoint.MGroupInput`
(`NoGo.lean`).  Its per-state content, at a normalised state `Φ` on `X (N+1)`,
is FS's chain

```
qLHSword ≥ A₀  (lm:appinteractionestimate, eq:A₀)
pDiagForm + q4PairWord ≥ A₂-payment  (lm:appbogolubov, eq:simpleaprioribog)
```

`A₀` is in the corpus: `Work.SmallBoxA0.pot_sharp_summary` is
`lm:appinteractionestimate` transcribed (the `A₀` square form plus the
`A₂ = q4PairWord` pairing and the two `n₊`-error blocks).  The `A₂` half is the
corpus's PROVED refined `lm:appbogolubov` at the faithful word
(`Work.BlockBound4.diagW_lm_appbogolubov_explicitC`, i.e. FS's
`eq:refinedaprioribog`) — **and that is exactly what the `m`-arm cannot use**:
its error bracket contains the log / quartic / interior terms

```
C[ (av)²c₀log(1/(c₀av))·(N+1)²/s³ + (av)⁴c₀⁻³·((N+1)/s³)⁴·s³ + av c₀³(N+1) ]
```

(the `Γ`-family: quartic in the count), which dwarf the `m`-arm's target
`(1/18)μu·8π(av)s³` at the group window `u ∈ [2μ,3μ)`; that is why the DL
re-point carried the `m`-arm as a named input in the first place.

The piece the corpus still lacks is therefore FS's **simple** Bogoliubov
payment (`eq:simpleaprioribog`, `final_v2.tex` l.3776), whose error is *linear*
in the count:

```
pDiagForm s (fsKinCoeff c₀) Φ + q4PairWord Φ
  ≥ −½((1+ε)ĝω(0) + εa)·(n+1)n/s³
    − C_ε a(dsℓ)^{-3}·n                       (n = N+1 the particle count)
    − C_ε a((n+1)/s³)·n₊ ,
```

with `ε` FS's fixed `1/20` (FS's own choice, `final_v2.tex` l.3949) and `n₊`
the corpus's `cnPlus`.  `SimpleA2 E` below is that statement with the two
error constants collapsed into one `E` (the DL chapter's other constants are
free; the `1/20` is FS's).

## Two honest caveats (for whoever proves `SimpleA2`)

1. **Regime.**  FS's `eq:simpleaprioribog` needs `eq:appbogassumptions`
   (`(R/(dℓ))² < C_ε^{-1}`, `a(dsℓ)^{-1}ln(dsℓ a^{-1}) < C_ε^{-1}`) *only*
   because the loss factor of the `B²/𝒜` integral is
   `(1+C(R/(dℓ))²)(1+C(dsℓ)^{-1}a)`, which must be dominated by `(1+ε)`.
   In the chapter's small-box vocabulary the corpus's own loss factor is
   `Work.BlockBound4.d4Eta Ct R0 s c₀ v`; a `SimpleA2` proof must either carry
   `d4Eta ≤ 1/20` as a hypothesis or produce the `(1+ε)` coefficient directly.
   (The *other* free constant `K_s` of `lm:appbogolubov` costs only the `n₊`
   slot, which the `m`-arm's `cgap`-regime absorbs.)
2. **Size of `E`.**  `SimpleA2 E` is only *useful* for the repair if `E` is
   small: the window consequence of the chain is `MGroupWindow (6 + E′)` with
   `E′` the arithmetic constant of `marm_arith`'s `C`-slot, and the corpus's
   block window (`hblk`, `D4Regime`) delivers the remainder arm only for
   counts `≤ 9μs³`, i.e. `Cn = 6 + E′ ≤ 8`.  See `README.md` §4.

The natural route to `SimpleA2` is a re-run of the corpus's PROVED refined
derivation (`Work.BlockBound4.diagW_lm_appbogolubov_explicitC`): same
`A₁`-shift, same two-mode `Fock2Mode`/`bogS` zero-point bound, but with
`𝒜(p)/|ℬ(p)|` forced `≥ 2/ε` (K_s large, free) so that the *simple* zero-point
bound `h(p) ≥ −½(1+ε/2)ℬ²/𝒜·(n₀/|B|)∫χ²` applies in the *whole* range (no
`|p| > 2(dsℓ)^{-1}` refinement, hence no log/quartic/interior terms).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.MGroupInput

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **FS's simple Bogoliubov payment at the faithful word** (`eq:simpleaprioribog`)
with the two error constants collapsed into `E` (FS's `ε` fixed at `1/20`).

At a normalised state `Φ` on `X (N+1)` (`n := N+1` particles, box side `s`):

```
pDiagForm s (fsKinCoeff c₀) Φ + q4PairWord Φ
  ≥ −½((1+1/20)·ĝω(0) + (1/20)·a)·(n+1)n/s³
    − E·a·n − E·a·((n+1)/s³)·n₊ .
```

This is the one input `Work.MGroupInput.MGroupWindow` still lacks; the corpus's
PROVED refined `lm:appbogolubov`
(`Work.BlockBound4.diagW_lm_appbogolubov_explicitC`) is its *refined* sibling
and does not imply it (its loss bracket is quartic in `n`). -/
def SimpleA2 (E : ℝ) (s c₀ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  ∀ (N : ℕ) (Φ : X (N + 1) → ℝ), ContDiff ℝ ∞ Φ →
    (∫ x in abox (N + 1) s, (Φ x) ^ 2) = 1 →
    - (1 / 2) * ((1 + 1 / 20) * g0w0Mass (v := v) h + (1 / 20) * (a v))
        * Work.BlockBound4.d4MassCoeff (N + 1) s
      - E * (a v) * ((N : ℝ) + 1)
      - E * (a v) * (((N : ℝ) + 2) / s ^ 3) * cnPlus s Φ
    ≤ pDiagForm s (fsKinCoeff c₀) Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)

/-- **FS's simple Bogoliubov payment with the two error constants SPLIT**: `E₁`
multiplies the *count-linear* error `a·(N+1)` and `E₂` the `n₊`-coefficient
`a·((N+2)/s³)`.  The split matters because the two constants have opposite
freedom in FS's derivation: `E₁` is `C₀²/K_s`-controlled (`K_s → ∞` makes it
arbitrarily small, its cost landing in the `n₊` slot), while `E₂` is `C·K_s`
and is *absorbed by the `cgap` regime*.  The single-`E` form `SimpleA2` forces
`E ≥ C·K_s` and therefore makes the `m`-arm's window `6μ + E ≤ u`
unreachable. -/
def SimpleA2Two (E₁ E₂ : ℝ) (s c₀ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  ∀ (N : ℕ) (Φ : X (N + 1) → ℝ), ContDiff ℝ ∞ Φ →
    (∫ x in abox (N + 1) s, (Φ x) ^ 2) = 1 →
    - (1 / 2) * ((1 + 1 / 20) * g0w0Mass (v := v) h + (1 / 20) * (a v))
        * Work.BlockBound4.d4MassCoeff (N + 1) s
      - E₁ * (a v) * ((N : ℝ) + 1)
      - E₂ * (a v) * (((N : ℝ) + 2) / s ^ 3) * cnPlus s Φ
    ≤ pDiagForm s (fsKinCoeff c₀) Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)

/-- **The residual in its usable form**: the count-linear constant `E₁` can be
made arbitrarily small, at the price of an `n₊`-coefficient `E₂` (which the
`m`-arm's `cgap` regimes absorbs). -/
def SimpleA2Small (s c₀ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ E₁ E₂ : ℝ,
    0 ≤ E₁ ∧ E₁ ≤ ε ∧ 0 ≤ E₂ ∧ SimpleA2Two E₁ E₂ s c₀ v h

/-- **The named residual of the `m`-arm**: some `E ≥ 0` for which the simple
Bogoliubov payment holds.  (FS's lemma; the constant is data-dependent, so it
is existentially quantified here.) -/
def SimpleA2Exists (s c₀ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ SimpleA2 E s c₀ v h

end Work.MGroupInput
