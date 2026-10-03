/-
# `Submission.Work.FIRed6Axis.Statement` — the axis-aware reduction and its inputs, as `Prop`s

This module states, as `Prop`-valued definitions, the objects the axis repair is assembled from, so
that the corresponding lemmas can be delegated (and proved) independently:

* `NearMassBound` — the *mass* half of the (5.16) trivial bound for the near-axis zone: the τ-mass of
  a part of the annulus `(N, 2N]` lying in the near zone `nearArg (4ϑ)` is
  `≪ (ϑN + √N + N^{5/6} + N^{2/3} + 1)·(log N)^{20}`.  Route:
  `4^{ω(n)} ≤ 16Σ_{d³≤n}τ(d)^6` (`Work.FIArea6.tau_small_divisor_localization`) gives
  `τ(n) ≤ 4Σ_{d|n, d³≤n}τ(d)^3`, so with `n ≤ 2N` and `T ⊆ (N,2N]`
  `Σ_{z∈T}τ(|z|²) ≤ 4Σ_{d ≤ (2N)^{1/3}}τ(d)^3·#{z ∈ T : d | |z|²}`.  The near zone is
  *axis-aligned*: around one axis side it is a strip of radial extent `≍√N` (in the interval
  `(√N, √(2N)]`) and transverse extent `≍ϑ√N`, contained in a rectangle of side lengths
  `W₁ ≍ √N`, `W₂ ≍ ϑ√N`.  If `d | z.re² + z.im²` then (for fixed `z.re`) the residue class of
  `z.im` mod `d` is one of at most `M(d) ≤ 2^{ω(d)}·O(1)` classes, so
  `#{z ∈ rect : d | |z|²} ≤ (W₁/d + 1)·M(d)·(W₂/d + 1)`; summing
  `τ(d)^3M(d)(W₁/d+1)(W₂/d+1)` over `d ≤ (2N)^{1/3}` needs only the Euler-product bounds
  `Σ_{d≤X}τ(d)^3M(d)/d² ≤ Σ 2^{7ω(d)}/d² ≪ (log X)^{O(1)}`,
  `Σ_{d≤X}τ(d)^3M(d)/d ≪ (log X)^{O(1)}` and `Σ_{d≤X}τ(d)^3M(d) ≪ X(log X)^{O(1)}`
  (the first two from `Work.FIArea6.weighted_tau_sum_le`, the last from
  `Σ_{d≤X}a_d ≤ XΣ_{d≤X}a_d/d`).  The `W₁/d` and `1` cross terms produce the `√N·(2N)^{1/3}` and
  `(2N)^{2/3}` terms recorded above.
* `NearAxisBound` — the full (5.16) trivial bound for the near cells: the per-window sum of the two
  sieve errors over the near cells is bounded by the mass bound times the per-`z` count
  `Σ_{w ∈ ann M}Z(Re wz) ≤ 16 M^{3/4}|z|^{-1/2}` (`Work.FITop4.Red5.disk_per_c_bound`).
* `FarT1Bound` — the Cauchy–Schwarz step `T1` of `Work.FITop4.Red5.window_T1_le`, restricted to a
  subfamily `S` of the angular cells (no arithmetic content; it is a copy of `window_T1_le`).
* `WindowAxisBound` — the per-window far/near split: the per-window sieve bound of
  `window_bound_act` with the Cauchy step applied to the far cells `k ∉ S` only and the near cells
  `k ∈ S` bounded by `NearAxisBound`.
* `ClassSplit6` — the far-piece class split: the restriction of a far round-4 `IsBetaCoeff` to a
  class mod `8` is a round-6 `IsBetaCoeff6` (via `FarPiece_isAxisFree`).
* `ReductionAxis` — the axis-aware §§4–5.2 reduction: the conclusion of
  `Work.FITop4.Red6.reduction_save6_maj`, every piece additionally in a *far* cell, and one extra
  error term `c·ϑ·x^{3/4}(log x)^{Kaxis}` for the near-axis cells.
* `Prop41Axis` — the round-6 composition statement (`Areas6` ⇒ `Prop41StatementPiBig`).
-/
import Mathlib
import Submission.Work.FIRed6Axis.Defs6Axis
import Submission.Work.FITop4.Areas6
import Submission.Work.FITop4.Areas6b
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FITop4.Red5.window_setup
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.pieceDefs

set_option autoImplicit false

namespace Work.FIRed6Axis

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The exponent of the near-axis error term of `ReductionAxis`. -/
def Kaxis : ℕ := 100000

/-- **The (5.16) mass bound for the near-axis zone.**  The τ-mass of the part of the annulus
`(N, 2N]` of squarefree norm that lies within the angular distance `4ϑ` of one of the four axes is
at most `C·(ϑN + √N + N^{2/3} + 1)·(log(2+N))^{20}`. -/
def NearMassBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N ϑ : ℝ) (T : Finset GaussianInt),
    1 ≤ N → 0 < ϑ → ϑ ≤ 1 →
    (∀ z ∈ T, N < (Work.FIPlan.gnorm z : ℝ) ∧ (Work.FIPlan.gnorm z : ℝ) ≤ 2 * N ∧
      Squarefree (Work.FIPlan.gnorm z) ∧ nearArg (4 * ϑ) z) →
    ∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
      ≤ C * (ϑ * N + Real.sqrt N + N ^ ((5 : ℝ) / 6) + N ^ ((2 : ℝ) / 3) + 1)
          * (Real.log (2 + N)) ^ (20 : ℕ)

/-- **The (5.16) trivial bound for the near-axis cells, in the form consumed by the far/near split
of the Cauchy step.**  Over one dyadic window `(Mn, 2Mn]`, the sum of the two sieve errors `T1` and
`T2` restricted to the near cells `k ∈ S` is at most the mass bound of `NearMassBound` times the
per-`z` geometric factor `M^{3/4}N^{-1/4}`. -/
def NearAxisBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (x N Pz Mn : ℕ) (Ccoe τ θ ϑ : ℝ) (K K' : ℕ)
      (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
      (Pa : Fin K → Fin K' → Work.FITop.Params) (S : Finset (Fin K')),
    1 ≤ Mn → 1 ≤ N → 0 < θ → θ ≤ 1 → 0 < ϑ → ϑ ≤ 1 → 4 * Real.pi * θ ≤ ϑ →
    (N : ℝ) ≤ (Mn : ℝ) →
    (∀ i, (N : ℝ) ≤ a i) → (∀ i k, (Pa i k).N = a i) →
    (∀ i u, 0 ≤ p i u) → (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) →
    (∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1) →
    (∀ k α, 0 ≤ q k α) →
    (∀ k α, q k α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) →
    (∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1) →
    (∀ k ∈ S, ∀ i, ∀ z, Work.FITop4.InPolarBox (Pa i k) (φ k) z → nearArg (4 * ϑ) z) →
    (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ i, ∑ k ∈ S, ∑ w ∈ Work.FITop4.Red5.wSph m,
        (‖∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
            Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
          + ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
              2 * Work.FITop4.Red5.badInd m x τ (Work.FIPlan.gnorm z)
                * ‖Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z
                    * Work.FITop3.Zc w z‖))
      ≤ C * (Mn : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4)
          * (ϑ * (N : ℝ) + Real.sqrt (N : ℝ) + (N : ℝ) ^ ((5 : ℝ) / 6)
              + (N : ℝ) ^ ((2 : ℝ) / 3) + 1)
          * (Real.log (2 + (N : ℝ))) ^ (20 : ℕ)

/-- **The `T1` Cauchy–Schwarz step of one window, restricted to a subfamily of angular cells**
(copy of `Work.FITop4.Red5.window_T1_le` with the `k`-sum filtered by `S`; no arithmetic). -/
def FarT1Bound : Prop :=
  ∀ (x N Pz Mn : ℕ) (C τ θ : ℝ) (K K' : ℕ)
    (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params) (f : Fin K → Fin K' → ℤ → ℝ) (S : Finset (Fin K')),
    (1 ≤ N) → (1 ≤ Mn) →
    (∀ i k, (Pa i k).M = (Mn : ℝ)) → (∀ i k, (Pa i k).N = a i) →
    (∀ i, (N : ℝ) ≤ a i) →
    (∀ i u, p i u ≠ 0 → u ≤ 2 * (N : ℝ)) →
    (∀ i k, Work.FITop3.IsMajorant (Pa i k) (f i k)) →
    (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn),
        ∑ i, ∑ k ∈ S, ∑ w ∈ Work.FITop4.Red5.wSph m,
          ‖∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
             Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
      ≤ ∑ i, ∑ k ∈ S, Real.sqrt (100 * (Pa i k).M
          * Work.FITop3.Dform (Pa i k) (f i k)
              (Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i)))

/-- **The per-window far/near split.**  This is `Work.FITop4.Red5.window_bound_act` with the
assertion of the two sieve errors split at the angular cell level *before* the Cauchy–Schwarz step:
the far cells `k ∉ S` go through `FarT1Bound`, the near cells `k ∈ S` through `NearAxisBound`, and
the `T2`/`T3` estimates are used in their full-family forms (`T2` for the far part by monotonicity
of the nonnegative summand, `T3` unchanged).

The near constant `Cnear` is *hoisted* (it must not depend on the window data): it is the constant
of `NearAxisBound`, so that the reduction can accumulate the near error over the window ladder with
a single constant. -/
def WindowAxisBound : Prop :=
  ∃ Cnear : ℝ, 0 < Cnear ∧
    ∀ (x N Pz Mn : ℕ) (C τ θ ϑ : ℝ) (K K' : ℕ)
      (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
      (Pa : Fin K → Fin K' → Work.FITop.Params) (f : Fin K → Fin K' → ℤ → ℝ) (S : Finset (Fin K'))
      (c2 c3 : ℝ),
    (1 ≤ Mn) → (1 ≤ N) → (2 ≤ Pz) → (0 < θ) → (θ ≤ 1) → (0 < ϑ) → (ϑ ≤ 1) →
    (4 * Real.pi * θ ≤ ϑ) → ((N : ℝ) ≤ (Mn : ℝ)) →
    (∀ i, (N : ℝ) ≤ a i) →
    (∀ i k, (Pa i k).M = (Mn : ℝ)) → (∀ i k, (Pa i k).N = a i) →
    (∀ i k, (Pa i k).C = C) → (∀ i k, (Pa i k).Pz = Pz) →
    (∀ i k, (Pa i k).θ = θ) → (∀ i k, (Pa i k).τ = τ) →
    (∀ i u, 0 ≤ p i u) → (∀ i u, p i u ≤ 1) →
    (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) →
    (∀ i u, p i u ≠ 0 → u ≤ 2 * (N : ℝ)) →
    (∀ k α, 0 ≤ q k α) → (∀ k, q k 0 = 0) →
    (∀ k α, q k α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) →
    (∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1) →
    (∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1) →
    (∀ i k, Work.FITop3.IsMajorant (Pa i k) (f i k)) →
    ((∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
              (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ Work.FITop4.Red5.wSph mm, ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
            2 * Work.FITop4.Red5.badInd mm x τ (Work.FIPlan.gnorm z)
              * ‖Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z
                  * Work.FITop3.Zc w z‖)
        ≤ c2 * Work.FITop4.Red5.T2RHS x N Mn Pz θ) →
    ((∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ Work.FITop4.Red5.wSph mm,
          ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
          Work.FITop4.Red5.cGInd mm N x Pz τ (Work.FIPlan.gnorm z)
            * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        ≤ c3 * Work.FITop4.Red5.T3RHS x N Mn θ) →
    (∀ k ∈ S, ∀ i, ∀ z, Work.FITop4.InPolarBox (Pa i k) (φ k) z → nearArg (4 * ϑ) z) →
    (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), Work.FITop4.Red5.Iterm x N Pz C τ m)
        ≤ (∑ i, ∑ k ∈ (Finset.univ.filter (fun k : Fin K' => k ∉ S)),
              Real.sqrt (100 * (Pa i k).M
                * Work.FITop3.Dform (Pa i k) (f i k)
                    (Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i))))
          + c2 * Work.FITop4.Red5.T2RHS x N Mn Pz θ
          + c3 * Work.FITop4.Red5.T3RHS x N Mn θ
          + Cnear * (Mn : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4)
              * (ϑ * (N : ℝ) + Real.sqrt (N : ℝ) + (N : ℝ) ^ ((5 : ℝ) / 6)
                  + (N : ℝ) ^ ((2 : ℝ) / 3) + 1)
              * (Real.log (2 + (N : ℝ))) ^ (20 : ℕ)


/-- **The far-piece class split.**  Restricting a round-4 `IsBetaCoeff` whose cell is *far*
(angular distance `≥ 2ϑ` of every point of its polar box from the axes) to one class modulo `8`
produces a round-6 `IsBetaCoeff6`. -/
def ClassSplit6 : Prop :=
  ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    Work.FITop4.IsBetaCoeff Pa φ β → FarPiece Pa φ →
    Work.FITop4.IsBetaCoeff6 Pa φ z0 (clsRestrict z0 β)

/-- **The axis-aware §§4–5.2 reduction** (statement of `reduction_save6_axis`): the conclusion of
`Work.FITop4.Red6.reduction_save6_maj`, with every piece in a far cell and one extra error term
`c·ϑ·x^{3/4}(log x)^{Kaxis}` for the near-axis cells. -/
def ReductionAxis : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ (x N Pz : ℕ) (C τ η : ℝ),
      x₀ ≤ x → 1 ≤ N → 1 ≤ C → 2 ≤ Pz → 0 < η → η < 3 / 32 →
      (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) →
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ) →
      (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(Work.FITop4.BmaxBig η)) →
      2 * (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2)
        * (Real.log (x : ℝ)) ^ (-(Work.FITop4.BmaxBig η - 1)) →
      C ≤ (N : ℝ) ^ (1 - η) →
      (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ) →
      Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) →
      (Real.log (x : ℝ)) ^ (Work.FITop4.Asave + 124) ≤ τ →
      τ ≤ (x : ℝ) ^ (η / 3) →
      1 ≤ (Work.FITop4.varthetaOf x Work.FITop4.Asave) * (x : ℝ) →
      ∃ (ι : Type) (_ : Fintype ι) (Pa : ι → Work.FITop.Params) (f : ι → ℤ → ℝ)
        (φ : ι → ℝ) (β : ι → GaussianInt → ℂ),
        (∀ i, (Pa i).x = x ∧ (Pa i).η = η ∧ (Pa i).A = Work.FITop4.Asave ∧
              (Pa i).A' = Work.FITop4.Aprime Work.FITop4.Asave ∧
              (Pa i).ϑ = Work.FITop4.varthetaOf x Work.FITop4.Asave ∧
              (Pa i).θ = Work.FITop4.thetaOf x Work.FITop4.Asave ∧
              (Pa i).τ = Work.FITop4.tauOf x Work.FITop4.Asave ∧ (Pa i).Pz = Pz ∧
              (Pa i).C = C ∧
              (N : ℝ) ≤ (Pa i).N ∧ (Pa i).N ≤ 2 * (N : ℝ)) ∧
        (∀ i, Work.FITop4.IsMajorant6 (Pa i) (f i)) ∧
        (∀ i, Work.FITop4.IsBetaCoeff (Pa i) (φ i) (β i)) ∧
        (∀ i, FarPiece (Pa i) (φ i)) ∧
        (∑ i, ((((Pa i).M * (Pa i).N) ^ ((3 : ℝ) / 4)))) ≤
            c * (Work.FITop4.thetaOf x Work.FITop4.Asave) ^ (-(2 : ℝ)) * (x : ℝ) ^ ((3 : ℝ) / 4) ∧
        Work.FITop4.BformPiTau x N Pz C τ ≤
            (∑ i, Real.sqrt (100 * (Pa i).M
              * Work.FITop4.Dform (Pa i) (f i) (β i)))
          + c * ((Work.FITop4.thetaOf x Work.FITop4.Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
                * (Real.log (x : ℝ)) ^ (100 : ℕ)
              + (Work.FITop4.varthetaOf x Work.FITop4.Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
                * (Real.log (x : ℝ)) ^ (65536 : ℕ))
          + c * (Work.FITop4.varthetaOf x Work.FITop4.Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (x : ℝ)) ^ Kaxis

/-- **The round-6 composition**: the seven corrected areas imply the frozen-exponent,
`Π`-restricted target. -/
def Prop41Axis : Prop :=
  Work.FITop4.Area1Sieve6 → Work.FITop4.Area2_6b → Work.FITop4.Area3_6 → Work.FITop4.Area4_6 →
    Work.FITop4.Area6_6 → Work.FITop4.Area7_6 →
    Work.FITop4.Prop41StatementPiBig

end

end Work.FIRed6Axis
