import Mathlib
import Submission.Work.BourgainPlan.Maximal.canonical_arcs
import Submission.Work.BourgainPlan.Maximal.kmsz_variation_defs
import Submission.Work.BourgainPlan.Maximal.minor_arc_lp

/-!
# The major-arc half of KMSZ (6.5): the interface

Kosz–Mirek–Słomian–Zhang, arXiv:2606.12663, §6.3.  The variational inequality (6.5) for the
integer shift system,

`‖V^ρ_{ℤ,p}(A_{N;ℤ} f : N ∈ D_τ)‖_{ℓᵖ(ℤ)} ≲_{ρ,p,P} ‖f‖_{ℓᵖ(ℤ)}`,

is proved by splitting the averages along the canonical major arcs,

`A_N f = A_N (f − Π_{≤l(N),≤−dL(N)} f) + A_N (Π_{≤l(N),≤−dL(N)} f)`,

and bounding the two pieces separately: the **minor-arc** piece is (6.17), which is the landed
`Work.BourgainPlan.Maximal.kmsz_variation_of_minorAndMajor` (modulo the single named input
`IWProjectionBound` = KMSZ (6.11)), and the **major-arc** piece is §6.3 — the content of

      `Work.BourgainPlan.Maximal.KMSZMajorArcStatement ρ P p`

below, whose proof needs KMSZ Theorem 5.2 (the Rademacher–Menshov-seminorm refinement of the
Ionescu–Wainger multiplier theorem, their (6.20) + (6.21) + (6.22) + (6.23) + (6.24)) together with
the major-arc approximation (6.19) and the multiplier realisation of the model
`T_ℤ[J_G | m_N η_{≤−dL(N)} K_{Σ_l}]`.

The present module only contains the *vocabulary* of that statement — the shape of the admissible
families of Ionescu–Wainger projections (KMSZ's own parameters: the level exponent `α`, the
smoothing scale `−dL(N)`, the range condition `m ≤ −6 max{p,p/(p−1)}(l+1)` of (6.11)) and the
`ρ`-variation over an index tail.  The consumer is
`Work.BourgainPlan.Maximal.kmsz_variation_of_minorAndMajor`, which assembles

      (6.5)  ⟸  `IWProjectionBound`  +  `KMSZMajorArcStatement`.

## Why the family is admissible *from a threshold* `K` on, and why the variant is a *tail* one

KMSZ carry out the decomposition only for `N ≥ C₀`, `C₀` a large constant depending on `P` and on
the auxiliary even integer `p₀` — for the finitely many small scales the smoothing scale `−dL(N)` is
larger (coarser) than the range condition `m ≤ −6 max{p,p'}(l+1)` allows.  Consequently our
statement is about the index tail `{k : K ≤ k}` and the variation is the tail variation
`varRhoFrom ρ K`; the finitely many scales below the threshold are handled in the assembly by the
`ℓᵖ` bound `IWProjectionBound` itself (they cost a constant), exactly as the minor-arc half
handles them through `Work.BourgainPlan.Maximal.opArc_initial_scale_lp`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- The exponent `max{p, p/(p-1)}` of the Ionescu–Wainger range condition (KMSZ (6.11)); it is
`max ((1+p)/2) (((1+p)/2)/((1+p)/2 - 1))` in the form used by the corpus's
`opArc_initial_scale_lp` and `minor_arc_lp_subtwo_small`. -/
def kmszMq (p : ℝ) : ℝ := max ((1 + p) / 2) (((1 + p) / 2) / ((1 + p) / 2 - 1))

/-- The level exponent `α₀(P,p)` of the KMSZ decomposition: the level `l(N) = ⌊α Log N⌋` is always
taken with `α ≤ α₀`, which is small enough for both halves of the argument (the minor-arc
interpolation (6.16) needs `α` at most `d/(64 (6 max{p,p'}+1))`, and the major-arc level splitting
needs the level to grow no faster than the scale). -/
def kmszAlpha₀ (P : Polynomial ℤ) (p : ℝ) : ℝ :=
  (P.natDegree : ℝ) / (64 * (6 * kmszMq p + 1))

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The `ρ`-variation of a sequence over the **index tail** `[lo, ∞)`:
`varRhoFrom ρ lo a = ⨆_{hi} varRho ρ lo hi a`.  This is the form in which KMSZ (6.18) is stated
(the variation over `D_{τ,l} = {N ∈ D_τ : N ≥ C₀, N ≥ 2^{l/α}}`). -/
def varRhoFrom (ρ : ℝ) (lo : ℕ) (a : ℕ → E) : ℝ≥0∞ := ⨆ hi : ℕ, varRho ρ lo hi a

/-- `varRhoAll` is the tail variation from `0`. -/
lemma varRhoFrom_zero (ρ : ℝ) (a : ℕ → E) : varRhoFrom ρ 0 a = varRhoAll ρ a := rfl

/-- **The admissibility of a family of Ionescu–Wainger projections for the major-arc analysis**
(KMSZ §6.3): the level `l k` at the scale `N_k = 2^{k+1}` grows at most like `α₀ (k+1)` (so that
`N_k ≥ 2^{l k / α₀}`, the condition defining `D_{τ,l}`), the smoothing scale `m k` satisfies the
Ionescu–Wainger range condition `m ≤ −6 max{p,p'}(l+1)` of (6.11), and — this is the scale of the
KMSZ smoothing `m_N = −d L(N) = −d (Log N − l(N))` — it is at least as coarse as `N^{-d}` (so that
the projection is a genuine averaging of the arcs rather than an unbounded sharp frequency
projection) and at least as fine as `N^{-(d-1/2)}` (so that the major-arc approximation (6.19) with
`M = 2^{-m k}` has a power gain, `2^{l}(2^{m k}N^{d-1} + N^{-1}) \le 2^{l}(2^{-(k+1)/2}+N^{-1})`).
All conditions are imposed only from the threshold `K` on. -/
def kmszMajorData (P : Polynomial ℤ) (p : ℝ) (K : ℕ) (l : ℕ → ℕ) (m : ℤ → ℤ) : Prop :=
  (∀ k : ℕ, K ≤ k → (l k : ℝ) ≤ kmszAlpha₀ P p * ((k : ℝ) + 1)) ∧
  (∀ k : ℕ, K ≤ k → (m k : ℝ) ≤ -(6 * kmszMq p) * ((l k : ℝ) + 1)) ∧
  (∀ k : ℕ, K ≤ k → -((P.natDegree : ℝ) * ((k : ℝ) + 1)) ≤ (m k : ℝ)) ∧
  (∀ k : ℕ, K ≤ k → (m k : ℝ) ≤ -(((P.natDegree : ℝ) - 1 / 2) * ((k : ℝ) + 1)))

/-- **The major-arc half of KMSZ (6.5)** (their §6.3).  For every admissible family of dyadic
Ionescu–Wainger projections — level `l k`, smoothing scale `m k`, bump `φ k` bounded by `1` and
supported in the ball of radius `2^{m k - 1}` — the tail `ρ`-variation of the projected polynomial
averages is bounded on `ℓᵖ(ℤ)` by `C‖g‖_{ℓᵖ}`, uniformly in the family and in the threshold `K`.

This is exactly the piece of KMSZ §6.3 that is *not* the minor-arc estimate: it is (6.19) (the
major-arc approximation, landed in this corpus as
`Work.BourgainPlan.Maximal.major_arc_nbd_bound`), the model reduction (6.20), KMSZ Theorem 5.2 in
the form (6.21), the factorisation (6.22), the `ℓ²` gain (6.23) and the interpolation (6.24).  Its
*proof* is the deep remaining input of this route (KMSZ Theorem 5.2, the Rademacher–Menshov
refinement of the Ionescu–Wainger multiplier theorem); as a statement it is a theorem of the
source. -/
def KMSZMajorArcStatement (ρ : ℝ) (P : Polynomial ℤ) (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (K : ℕ) (l : ℕ → ℕ) (m : ℤ → ℤ)
      (φ : ℕ → Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      (hφ : ∀ k : ℕ, MemLp (φ k) ⊤ (AddCircle.haarAddCircle (T := 1))),
      kmszMajorData P p K l m →
      (∀ (k : ℕ) ξ, ‖φ k ξ‖ ≤ 1) →
      (∀ (k : ℕ) ξ, (2 : ℝ) ^ (m k - 1) < ‖ξ‖ → φ k ξ = 0) →
      ∀ (g : ℤ → ℂ) (hg : Memℓp g 2), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
        ∫⁻ mm : ℤ, (varRhoFrom ρ K (fun k : ℕ => discAvgZC P (2 ^ (k + 1))
            (fun j => opArc (φ k) (hφ k) (canonicalFinset (2 ^ (l k))) g hg j) mm)) ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ mm : ℤ, ‖g mm‖ₑ ^ p ∂MeasureTheory.Measure.count

end

end Work.BourgainPlan.Maximal
