import Mathlib
import Submission.Work.ZeroDensity.LogFree.Defs

/-!
# `Work.ZeroDensity.LogFree.RouteDefs` — the two deep interfaces of the L7 assembly

The L7 assembly (`LogFree/logFreeNPOfParams`) is proved from exactly two deep inputs, both stated
here as `Prop`s so that the assembly can be proved against the *interfaces* while the two inputs
are being built in parallel:

* `DualityCount p` — **L5** of `JUTILA_UNIFIED_LEAD.md` §3: the Halász duality count for a
  `1/L`-separated system of non-exceptional zeros (`L = log (q(T+2))`, `X = (q(T+2))^x`):

      |S| ≤ C_S·(2 + log₂(1+λ))·X^{2−2σ},    λ = (1−σ)L.

* `BoxUpgrade p` — **L6**: the box/parity upgrade turning a bound `M` for *every* such separated
  system into a bound for the whole non-principal zero count,
  `Σ' N(σ,T,χ) ≤ C₀·((1+λ)(M+1) + 1)`.

Both are stated for a parameter packet `p : Params`; the constants may depend on `p` (and, for
`DualityCount`, on the non-exceptionality threshold `c₀`) but never on `q`, `T`, `σ` or on the
system.  `Lscale q T = log (q(T+2))`, `Dpow q T a = (q(T+2))^a`, `zeroMult χ ρ` is the
multiplicity of `ρ` as a zero of the completed `L`-function of the primitive character inducing
`χ`, and `famCountNP q σ T = Σ'_{χ ≠ 1} N(σ,T,χ)`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.LinnikContract

/-- **L5 of `JUTILA_UNIFIED_LEAD.md` §3 — the Halász duality count.**

For every non-exceptionality threshold `c₀ > 0` there are `C_S > 0` and `D₀ > 0` such that, for
every `q ≥ 2`, every `T ≥ 1` with `D₀ ≤ q(T+2)`, every `σ ∈ [p.σ₀, 1]` and every finite indexed
system `(χ i, ρ i)` of zeros with `χ i ≠ 1`, `ρ i` a zero of the completed `L`-function of
`χ i` at height `≤ T`, `σ ≤ Re (ρ i) < 1`, non-exceptional (`c₀ ≤ (1 − Re ρ i)·L`) and `1/L`-separated
within each character, one has

  `m ≤ C_S·(2 + log₂(1+λ))·X^{2−2σ}`,  `λ = (1−σ)·L`, `X^{2−2σ} = (q(T+2))^{2x(1−σ)}`.

Route (Heath-Brown (1992) §11, Lemma 11.1, at scale `𝓓 = q(T+2)`): apply the Halász duality
frame `Work.ZeroDensity.Jutila.halaszDualityFrame` with `a_n = (Σψ)(n)·n^{-1/2}g(n)^{1/2}`,
`f_i(n) = (Σθ)(n)·χ_i(n)·n^{1/2−ρ_i}·g(n)^{1/2}` truncated at `N = ⌈X L³⌉`; the detector lower
bound `V = 1 − C/L` is **L1** (`LogFree/hybridDetector`), the `ℓ²` mass `Σ|a_n|² ≤ A` is
**L2(a)** (Graham's mean values, `Density4`/`Jutila` — "already present"), and the bilinear form
`B = ‖G‖` is split into the same-character blocks, bounded by `Q(1)·‖K‖ + m·κ` with **L2(b)**,
**L3(b)** and the damped large sieve **L4** on the pole Gram matrix, and the cross-character part
`≤ m·κ` (Schur) with **L3(a)**; then `A·κ ≤ 1/8` absorbs the cross terms for `𝓓 ≥ 𝓓₀` and
`Q(1) ≤ C/(wL)` cancels the `L` of L4. -/
def DualityCount (p : Params) : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∃ C_S : ℝ, 0 < C_S ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T σ : ℝ), 1 ≤ T →
      D₀ ≤ scale q T → p.σ₀ ≤ σ → σ ≤ 1 →
      ∀ (m : ℕ) (χ : Fin m → DirichletCharacter ℂ q) (ρ : Fin m → ℂ),
        (∀ i, χ i ≠ 1) → (∀ i, zeroMult (χ i) (ρ i) ≠ 0) →
        (∀ i, σ ≤ (ρ i).re) → (∀ i, (ρ i).re < 1) → (∀ i, |(ρ i).im| ≤ T) →
        (∀ i, c₀ ≤ (1 - (ρ i).re) * Lscale q T) →
        (∀ i j, i ≠ j → χ i = χ j → 1 / Lscale q T ≤ |(ρ i).im - (ρ j).im|) →
        (m : ℝ) ≤ C_S * (2 + log2 (1 + (1 - σ) * Lscale q T)) * Dpow q T (2 * p.x * (1 - σ))

/-- **L6 of `JUTILA_UNIFIED_LEAD.md` §3 — the box upgrade with a general exponent.**

There are `C₀ > 0`, `c₀ > 0` and `D₀ > 0` such that for every `q ≥ 2`, every `T ≥ 1` with
`D₀ ≤ q(T+2)` and every `σ ∈ [p.σ₀, 1]`: if `M ≥ 0` bounds the cardinality of *every* system of
`c₀`-non-exceptional, `1/L`-separated zeros as in `DualityCount` (with `L = Lscale q T`), then

  `Σ'_{χ ≠ 1} N(σ,T,χ) ≤ C₀·((1+λ)·(M+1) + 1)`,  `λ = (1−σ)·L`.

Route (generalises the proved `jutilaNonPrincipal_of_jBound`): take the box scale `Δ = 1/L` (so
`Δ ≤ 1−σ` as soon as `λ ≥ 1`; for `λ < 1` reduce to `σ' = 1 − 1/L`, where the count only increases
and `λ' = 1`), bound each box by `boxMass_le_linnik_real` — generalised from `4/5 ≤ σ` to
`1/2 ≤ σ` — apply the parity split `erase_zeroCountIn_le_two_mul_paritySplit` to get
`Σ' N ≤ 2B·J` with `B ≤ C(λ+1)` and `J` the number of boxes of the larger parity class, and
observe that `J ≤ m + K`, where `m` is the size of the system obtained by choosing one
non-exceptional zero in each box of that class (so that `m ≤ M` by hypothesis) and `K` is the
number of boxes containing *only* exceptional zeros; `K ≤ 8` by the exceptional-zero theory
(uniform zero-free regions `Commons…LFunction_zeroFree_{offAxis,uniform_realAxis}`, which show that
every zero with `1 − Re ρ > 0` small is a real zero of a real character, so lives in the single box
around `t = 0`, together with Landau's two-real-zero repulsion
`Work.LinnikAreas.OtherCharRepel.twoRealCharRepel`, which shows that at most one character mod `q`
has such a zero — and crudely, `K ≤ q − 1 ≤ 8` for `q < 9`).  The `+1`s in the statement absorb
this `K` and the per-character slack. -/
def BoxUpgrade (p : Params) : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T σ : ℝ), 1 ≤ T →
      D₀ ≤ scale q T → p.σ₀ ≤ σ → σ ≤ 1 →
      ∀ M : ℝ, 0 ≤ M →
        (∀ (m : ℕ) (χ : Fin m → DirichletCharacter ℂ q) (ρ : Fin m → ℂ),
          (∀ i, χ i ≠ 1) → (∀ i, zeroMult (χ i) (ρ i) ≠ 0) →
          (∀ i, σ ≤ (ρ i).re) → (∀ i, (ρ i).re < 1) → (∀ i, |(ρ i).im| ≤ T) →
          (∀ i, c₀ ≤ (1 - (ρ i).re) * Lscale q T) →
          (∀ i j, i ≠ j → χ i = χ j → 1 / Lscale q T ≤ |(ρ i).im - (ρ j).im|) →
          (m : ℝ) ≤ M) →
        famCountNP q σ T ≤ C₀ * ((1 + (1 - σ) * Lscale q T) * (M + 1) + 1)

end Work.ZeroDensity.LogFree

namespace Work.ZeroDensity.LogFree

open Work.LinnikContract

/-- **A relaxed form of `DualityCount`** in which the log-free factor `2 + log₂(1+λ)` is replaced by
an arbitrary fixed power `(1+λ)^4` of `λ = (1-σ)·Lscale q T`.  This form is *all that the L7
assembly needs*: the absorption step `absorb_ineq_slack` converts any fixed power of `(1+λ)` into
`exp(θλ) = D^{θ(1-σ)}` and pays for it out of the slack `c - 2x > 0`.  It is genuinely weaker and
correspondingly easier: the same-character pole blocks can be bounded by the *crude row sums* of the
pole Gram matrix (`|K_ij| ≤ C(1-β_i)^{-1}(1+|γ_i-γ_j|)^{3/2}e^{-π|γ_i-γ_j|/2}X^{2-2σ}` from the
proved vertical `Γ`-bound `Work.LinnikAreas.Density4.Ssm_fixed_bound.Gamma_vertical_uniform`
together with the `1/L`-separation), without the damped large sieve `L4`. -/
def DualityCountSlack (p : Params) : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∃ C_S : ℝ, 0 < C_S ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T σ : ℝ), 1 ≤ T →
      D₀ ≤ scale q T → p.σ₀ ≤ σ → σ ≤ 1 →
      ∀ (m : ℕ) (χ : Fin m → DirichletCharacter ℂ q) (ρ : Fin m → ℂ),
        (∀ i, χ i ≠ 1) → (∀ i, zeroMult (χ i) (ρ i) ≠ 0) →
        (∀ i, σ ≤ (ρ i).re) → (∀ i, (ρ i).re < 1) → (∀ i, |(ρ i).im| ≤ T) →
        (∀ i, c₀ ≤ (1 - (ρ i).re) * Lscale q T) →
        (∀ i j, i ≠ j → χ i = χ j → 1 / Lscale q T ≤ |(ρ i).im - (ρ j).im|) →
        (m : ℝ) ≤ C_S * (1 + (1 - σ) * Lscale q T) ^ 4 * Dpow q T (2 * p.x * (1 - σ))

end Work.ZeroDensity.LogFree
