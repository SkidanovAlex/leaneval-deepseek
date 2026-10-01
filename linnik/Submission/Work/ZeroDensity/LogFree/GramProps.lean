import Mathlib
import Submission.Work.ZeroDensity.LogFree.RouteDefs

/-!
# `Work.ZeroDensity.LogFree.GramProps` — the interfaces of the L5 duality count

The Halász duality count `DualityCount p` (L5 of `JUTILA_UNIFIED_LEAD.md` §3) is assembled from
independent analytic inputs, stated here as `Prop`s so that the assembly
(`LogFree/dualityOfGram.lean`) can be proved against the interfaces:

* `MassBound p` — **L2(a)**: the `ℓ²` mass `Σ_n (Σ_{d|n}ψ_d)² n^{-1} g(n)` of the Halász weight
  `a_n = (Σψ)(n)·n^{-1/2}g(n)^{1/2}` is bounded by a constant depending only on `p`;
* `PoleResidueBound p` — **L2(b)**: the pole residue `Q(1) = Σ_{d,e≤W}θ_dθ_e/[d,e]` is `O(1/𝓛)`;
* `DetectorBound p` — **L1 at an arbitrary non-exceptionality threshold**: for every `c₀ > 0` the
  Heath-Brown detector `Density4.detSum` is bounded below by `1 − C/𝓛` on the zeros with
  `λ(ρ) = (1−Re ρ)·𝓛 ≥ c₀`;
* `GramCross p` — **L3(a)**: the cross-character Gram entries (`χ_i ≠ χ_j`) are
  `O(𝓛^E 𝓓^{−η})`;
* `GramSame p` — **L3(b)**: for `χ_i = χ_j` the `q`-free Gram entry differs from the pole term
  `Q(1)·K_ij` by `O(𝓛^E 𝓓^{−η})`.  The hypothesis `4w + η ≤ u` is the range condition of the
  crude estimate `Σ_{d,e} |θ_dθ_e| [d,e]^{2−β−β'} ≤ 𝓓^{4w}` for the Taylor remainder of
  `Li_{s}(e^{-y})`;
* `PoleLargeSieve p` — **L4**: the damped large sieve for the pole Gram matrix `K_ij`;
* `DetectorTruncation p` — the tail of the detector beyond `⌈X 𝓛^{10}⌉` is `O(1/𝓛)`, which
  converts the infinite sum `Density4.detSum` into the finite sums used by the Halász frame;
* `NearLineCount p` — the count of the *very* near-line zeros `λ(ρ) ≤ c₁` (those below the
  threshold of the uniform zero-free regions, hence at most one Siegel zero) is bounded.

`DualityCount p` quantifies over an arbitrary non-exceptionality threshold `c₀`; the assembly splits
the system at the fixed threshold `c₁` of `NearLineCount`, applies `DetectorBound`/`GramCross` at
`c₁`, and counts the finitely many remaining zeros by `NearLineCount`.  Consequently no input has
to hold below a positive threshold, and all constants are independent of `q`, `T`, `c₀` and of the
zero system.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.LinnikContract

/-- **L2(a)** of `JUTILA_UNIFIED_LEAD.md` §3: the `ℓ²` mass of the Halász weight. -/
def MassBound (p : Params) : Prop :=
  ∃ C_A : ℝ, 0 < C_A ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T : ℝ), 1 ≤ T → D₀ ≤ scale q T →
    ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N,
        (psiSum (Dpow q T p.u) (Dpow q T p.v) n) ^ 2 * ((n : ℝ))⁻¹
          * gfun (Dpow q T p.x) (Dpow q T p.u / (Lscale q T) ^ 2) n)
        ≤ C_A

/-- **L2(b)**: the pole residue `Q(1) = Σ_{d,e ≤ W} θ_d θ_e / [d,e]` is `O(1/𝓛)`. -/
def PoleResidueBound (p : Params) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T : ℝ), 1 ≤ T → D₀ ≤ scale q T →
      poleResidue (Dpow q T p.w) ≤ C / Lscale q T

/-- **L1 for an arbitrary non-exceptionality threshold**: for every `c₀ > 0` the detector is
bounded below by `1 − C/𝓛` on the zeros with `λ(ρ) ≥ c₀`. -/
def DetectorBound (p : Params) : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T : ℝ), 1 ≤ T → D₀ ≤ scale q T →
    ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ ρ : ℂ,
      zeroMult χ ρ ≠ 0 → p.σ₀ ≤ ρ.re → ρ.re < 1 → |ρ.im| ≤ T →
      c₀ ≤ (1 - ρ.re) * Lscale q T →
      1 - C / Lscale q T ≤
        ‖Work.LinnikAreas.Density4.detSum q (Dpow q T p.u) (Dpow q T p.v) (Dpow q T p.w)
          (Dpow q T p.x) (Lscale q T) χ ρ‖

/-- **L3(a)**: the cross-character Gram entry `G_ij` (`χ_i ≠ χ_j`) is `O(𝓛^E 𝓓^{−η})` for zeros
with `λ ≥ c₀`. -/
def GramCross (p : Params) : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ, 0 < C ∧ ∃ E : ℝ, ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T : ℝ), 1 ≤ T → D₀ ≤ scale q T →
    ∀ (χ χ' : DirichletCharacter ℂ q) (ρ ρ' : ℂ),
      χ ≠ 1 → χ' ≠ 1 → χ ≠ χ' →
      zeroMult χ ρ ≠ 0 → zeroMult χ' ρ' ≠ 0 →
      p.σ₀ ≤ ρ.re → ρ.re < 1 → p.σ₀ ≤ ρ'.re → ρ'.re < 1 →
      |ρ.im| ≤ T → |ρ'.im| ≤ T →
      c₀ ≤ (1 - ρ.re) * Lscale q T → c₀ ≤ (1 - ρ'.re) * Lscale q T →
      ‖gramEntry q (Dpow q T p.w) (Dpow q T p.x)
          (Dpow q T p.u / (Lscale q T) ^ 2) χ χ' ρ ρ'‖
        ≤ C * (Lscale q T) ^ E * Dpow q T (-p.η)

/-- **L3(b)**: for a single character, the `q`-free Gram entry is the pole term plus a small
remainder.  The hypothesis `4w + η ≤ u` is the range condition under which the Taylor remainder
of `Li_s(e^{−y})` at `y = [d,e]/U'` is dominated by `𝓓^{−η}`. -/
def GramSame (p : Params) : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ, 0 < C ∧ ∃ E : ℝ, ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T : ℝ), 1 ≤ T → D₀ ≤ scale q T →
    ∀ (ρ ρ' : ℂ),
      p.σ₀ ≤ ρ.re → ρ.re < 1 → p.σ₀ ≤ ρ'.re → ρ'.re < 1 →
      |ρ.im| ≤ T → |ρ'.im| ≤ T →
      c₀ ≤ (1 - ρ.re) * Lscale q T → c₀ ≤ (1 - ρ'.re) * Lscale q T →
      ‖gramEntryFree (Dpow q T p.w) (Dpow q T p.x) (Dpow q T p.u / (Lscale q T) ^ 2) ρ ρ'
        - ((poleResidue (Dpow q T p.w) : ℂ)
            * poleK (Dpow q T p.x) (Dpow q T p.u / (Lscale q T) ^ 2) ρ ρ')‖
        ≤ C * (Lscale q T) ^ E * Dpow q T (-p.η)

/-- **L4**: the damped large sieve for the pole Gram matrix
`K_ij = Γ(2-ρ_i-\barρ_j)(X^{2-ρ_i-\barρ_j} - U'^{2-ρ_i-\barρ_j})` of a `1/𝓛`-separated system. -/
def PoleLargeSieve (p : Params) : Prop :=
  ∃ C_K : ℝ, 0 < C_K ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T σ : ℝ), 1 ≤ T → D₀ ≤ scale q T →
      p.σ₀ ≤ σ → σ ≤ 1 →
      ∀ (m : ℕ) (ρ : Fin m → ℂ) (z : Fin m → ℂ),
        (∀ i, σ ≤ (ρ i).re) → (∀ i, (ρ i).re < 1) → (∀ i, |(ρ i).im| ≤ T) →
        (∀ i j, i ≠ j → 1 / Lscale q T ≤ |(ρ i).im - (ρ j).im|) →
        (poleGram m (Dpow q T p.x) (Dpow q T p.u / (Lscale q T) ^ 2) ρ z).re
          ≤ C_K * (2 + log2 (1 + (1 - σ) * Lscale q T)) * Lscale q T
              * Dpow q T (2 * p.x * (1 - σ)) * ∑ i, ‖z i‖ ^ 2

/-- **The detector truncation**: past `⌈X 𝓛^{10}⌉` the terms of the Heath-Brown detector
`Density4.detSum` decay super-exponentially, so the difference between the infinite detector sum
and its truncation at `N` is `O(1/𝓛)` uniformly in the character and the zero. -/
def DetectorTruncation (p : Params) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T : ℝ), 1 ≤ T → D₀ ≤ scale q T →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), χ ≠ 1 → zeroMult χ ρ ≠ 0 →
      p.σ₀ ≤ ρ.re → ρ.re < 1 → |ρ.im| ≤ T →
    ∀ N : ℕ, ⌈Dpow q T p.x * (Lscale q T) ^ 10⌉₊ ≤ N →
      ‖(∑ n ∈ Finset.Icc 1 N, ((psiSum (Dpow q T p.u) (Dpow q T p.v) n : ℝ) : ℂ)
            * ((thetaS (Dpow q T p.w) n : ℝ) : ℂ) * χ (n : ZMod q) * ((n : ℂ) ^ (-ρ))
            * (((gfun (Dpow q T p.x) (Dpow q T p.u / (Lscale q T) ^ 2) n : ℝ) : ℂ)))
          - Work.LinnikAreas.Density4.detSum q (Dpow q T p.u) (Dpow q T p.v) (Dpow q T p.w)
              (Dpow q T p.x) (Lscale q T) χ ρ‖
        ≤ C / Lscale q T

/-- **The near-line count**: there is a threshold `c₁ > 0` (that of the uniform zero-free regions)
such that every `1/𝓛`-separated system of non-principal, non-exceptional zeros with
`λ(ρ) ≤ c₁` in the strip `p.σ₀ ≤ Re ρ < 1`, `|Im ρ| ≤ T` has cardinality at most `K`. -/
def NearLineCount (p : Params) : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ K : ℝ, 0 ≤ K ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T σ : ℝ), 1 ≤ T → D₀ ≤ scale q T → p.σ₀ ≤ σ →
      ∀ (m : ℕ) (χ : Fin m → DirichletCharacter ℂ q) (ρ : Fin m → ℂ),
        (∀ i, χ i ≠ 1) → (∀ i, zeroMult (χ i) (ρ i) ≠ 0) →
        (∀ i, σ ≤ (ρ i).re) → (∀ i, (ρ i).re < 1) → (∀ i, |(ρ i).im| ≤ T) →
        (∀ i, (1 - (ρ i).re) * Lscale q T ≤ c₁) →
        (∀ i j, i ≠ j → χ i = χ j → 1 / Lscale q T ≤ |(ρ i).im - (ρ j).im|) →
        (m : ℝ) ≤ K

end Work.ZeroDensity.LogFree
