import Mathlib
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp

/-!
# The signed lacunary profile-difference symbol `Θ_ε` of MST §4.4

Mirek–Stein–Trojan (arXiv:1512.07518) reduce the `ℓᵖ` estimate for the level model `ν^s_{2^n}`
(their Theorem 7) to the multiplier `T_ε` whose symbol is

`ξ ↦ Σ_{β ∈ 𝒰_{(s+1)^l} ∖ 𝒰_{s^l}} Θ(ξ − β) η_s(ξ − β)`,  with
`Θ = Σ_{j=0}^{2^{κ_s−i}−1} ε_j Σ_{m ∈ I_j^i} (Φ_{2^{m+1}} − Φ_{2^m})`,

`I_j^i = [j 2^i, (j+1) 2^i)` and `ε_j ∈ {±1}` a Rademacher sign.  The inner sum telescopes:

`Σ_{m ∈ I_j^i} (Φ_{2^{m+1}} − Φ_{2^m}) = Φ_{2^{(j+1)2^i}} − Φ_{2^{j2^i}}`,

so the symbol is a signed sum of *lacunary* differences of the oscillatory profile `Φ_N`
(`polyProfile`).

## WARNING (session 28): `Θ_ε` does **not** satisfy Mikhlin conditions

`MST_ROUTE.md` §7 (`(iv)`) asserts that `Θ_ε` is "a MIKHLIN multiplier uniformly in the signs:
`|∂^α Θ_ε(ξ)| ≲_α |ξ|^{−α}`".  **That assertion is false**, and so is its localized version with the
level bump; two reviewers refuted the drafted statement `mstThetaEps_mikhlin` with explicit sign
sequences and explicit frequencies.  The counterexample: for `P = X²` one has exactly
`θ·Φ'_N(θ) = e(θN²)/2 − Φ_N(θ)/2`, so with `N_j = 2^j`, `θ = 1/5` and `ε_j = (−1)^j` the phases
`e(θN_j²) = e(4^j/5)` alternate in step with the signs, each summand tends to the fixed non-zero
value `(e(1/5) − e(4/5))/2`, and `|θ|·‖Θ'(θ)‖ ≍ M` grows linearly in `M` (numerically verified).
The same phenomenon occurs *inside* the support of the level bump, at `θ = 4^{−K}/5` with
`K ≍ s(d−χ)/2`.

Consequently the ℓʳ half of §5 (`level_lr_*_mst`, MST Theorem 7) must **not** route the operator
`T_ε f = Σ_{β ∈ 𝒰_{(s+1)^l} ∖ 𝒰_{s^l}} F⁻¹(Θ_ε(·−β)η_s(·−β)f̂)` through `mikhlin_multiplier_lift`.
The correct input is the *continuous multiplier bound* (MST's citation
`[bigs, Section 11]`/Duoandikoetxea–Rubio de Francia: `Θ_ε` is a continuous singular Radon
transform, hence bounded on `L^r(ℝ)` uniformly in the signs), i.e. MST_ROUTE's `(C2)`.  The right
interface for that is `IWMult r ψ A` — the *multiplier-norm* hypothesis, which `iwEndpoint2r` and
`iwRangeBound` (`Maximal/iw_superset.lean`) consume directly, so `level_lr_small_n_mst` should be
stated against `IWMult` (or against `(C2)` directly) rather than against `IWSupersetBoundLift`'s
Mikhlin data.  For `(C2)` itself the corpus has the *band-localized* brick
`Work.BourgainPlan.Maximal.bandedBlockMultiplier_lp` (uniform in the signs and in the number of
bands); the remaining gap is the passage from the banded symbol to the raw lacunary sum, for which
`ψ` should be taken to be a partition of unity and the tails handled by the `O(1)` `L^r`-bound of
frequency-multiplication by a bump.  See `MST_LANE_NOTE.md` Addendum 4.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

/-- **The signed lacunary profile-difference symbol** `Θ_ε` of MST §4.4: a sum of `M` lacunary
profile differences `Φ_{2^{(j+1)2^i}} − Φ_{2^{j2^i}}` with signs `ε j`. -/
noncomputable def mstThetaEps (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) : ℝ → ℂ :=
  fun θ => ∑ j ∈ Finset.range M,
    ε j * (polyProfile P (2 ^ ((j + 1) * 2 ^ i)) θ - polyProfile P (2 ^ (j * 2 ^ i)) θ)

@[simp] theorem mstThetaEps_apply (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) (θ : ℝ) :
    mstThetaEps P i M ε θ
      = ∑ j ∈ Finset.range M,
          ε j * (polyProfile P (2 ^ ((j + 1) * 2 ^ i)) θ
            - polyProfile P (2 ^ (j * 2 ^ i)) θ) := rfl

end Work.BourgainPlan.Maximal
