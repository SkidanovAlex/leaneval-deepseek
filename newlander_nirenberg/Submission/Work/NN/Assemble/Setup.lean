/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The perturbation assembly of the analytic core, in the flat model `ℂⁿ`

This module is the home of the **assembly**: the step that is *missing* in the repository, namely
the passage from the flat Poincaré operators (the `(0,1)`- and `(0,2)`-level `∂̄`-solvers on nested
polydiscs) to the local holomorphic frame of an integrable almost complex structure.

Everything is done in the flat model `ℂⁿ = Fin n → ℂ` of `Work.WN.Core.CnPert` (here re-exported
by `Work.NN.Core`), with the structure `J = JstdCn n + A`; `A` is the perturbation, it vanishes at
the origin, and it is small on the polydisc on which the flat operators are available.

## The three analytic inputs consumed here

1. `T1` — the `(0,1)`-level solver: for data `f` which are `C¹` and closed on a polydisc
   `P(ρ)`, `T1 f` solves `∂̄_j (T1 f) = f_j` on any smaller polydisc `P(ρ')`, with a gain of one
   derivative in the `C^{k,α}` scale and mapping smooth data to smooth primitives.  Available:
   `Work.NN.Core.dbarHonestOne` (proved), `Work.NN.Core.open_poincare_one` (proved),
   `Work.NN.Final.flatOne` (proved).
2. `T2` — the `(0,2)`-level solver: for data `η` which are `C¹`, antisymmetric and closed as a
   `(0,2)`-form on `P(ρ)`, `T2 η` is a `(0,1)`-potential with `∂̄_j (T2 η)_l - ∂̄_l (T2 η)_j = η_{jl}`
   on `P(ρ')`, again with a gain of one derivative.  In flight:
   `Work.NN.Core.dbarHonestTwo`, `Work.NN.Core.open_poincare_two`, `Work.NN.Final.flatTwo`.
   (Together with `T1`, this gives the *projection* `Π₀ = 1 - T2 ∂̄` onto `∂̄`-closed forms.)
3. `E` — a *linear extension operator* from the small polydisc `pd n ρ 1` to the data polydisc
   `pd n ρ 4`, bounded in every `C^{k,α}` (Seeley's extension, built from the moment data of
   `Work.NN.Final.exists_moment_data`).  In flight: `Work.NN.Final.exists_seeley`,
   `Work.NN.Final.exists_extension`.  It is needed because the flat solvers are *interior*
   estimates: the solution of `∂̄₀v = h` is controlled on a strictly smaller polydisc than the one
   on which `h` is controlled, so a fixed-point iteration on a single `C^{k,α}` space would shrink
   the region at every step; the extension operator turns the iteration into a genuine self-map of
   `C^{1,α}(pd n ρ 1)`.

## Why the region bookkeeping is what it is

With the fixed radii ratios of the interfaces (`data` on `pd n ρ 4`, `solutions` on `pd n ρ 2`),
the chain
`v` (controlled on `pd n ρ 1`) ↦ `E v` (on `pd n ρ 4`) ↦ `h := g - L_A(E v)` (on `pd n ρ 4`)
↦ `Π₀ h` (closed on `pd n ρ 2`) ↦ `T1` *instantiated at the radii `ρ/2`* (data on `pd n ρ 2`,
equation on `pd n ρ 1`) is exactly self-consistent.  The last step is why the assembly consumes
the flat solvers in the *radius-parametrised* form (`∀ ρ ρ', ρ' < ρ`) used by
`Work.NN.Core.dbarHonestOne` / `dbarHonestTwo`, rather than at a single ratio.

The perturbation is *integrable*: `∂̄_J² = 0`, i.e.
`proj02 J (dOne (dbarCn J w)) = 0` for every smooth `w` (see `Work.NN.Final.proj02_integrable_flat`
for the transport of `Work.NN.Core.dbar_sq_zero`), which is what makes `Π₀` a projection and what
kills the defect in the last step of the contraction.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set Filter
open Work.NN.Core

namespace Work.NN.Assemble

/-- The flat model `ℂⁿ`. -/
abbrev Cn (n : ℕ) := Work.NN.Core.Cn n

/-- Polydisc of multi-radius `c * ρ`. -/
abbrev pd (n : ℕ) (ρ : Fin n → ℝ) (c : ℝ) := Work.NN.Final.pd n ρ c

/-- **The `J`-holomorphic-frame predicate in the flat model `ℂⁿ`**: `n` independent `J`-holomorphic
functions on an open set, with invertible differential. -/
def IsHolFrame {n : ℕ} (J : Cn n → Cn n →L[ℝ] Cn n) (V : Set (Cn n))
    (u : Fin n → Cn n → ℂ) : Prop :=
  (∀ j, ContDiffOn ℝ ∞ (u j) V) ∧
  (∀ j y, y ∈ V → dbarCn J (u j) y = 0) ∧
  (∀ y, y ∈ V → Function.Bijective (fderiv ℝ (fun y : Cn n => fun j => u j y) y))

lemma IsHolFrame.contDiff {n : ℕ} {J : Cn n → Cn n →L[ℝ] Cn n} {V : Set (Cn n)}
    {u : Fin n → Cn n → ℂ} (h : IsHolFrame J V u) (j : Fin n) : ContDiffOn ℝ ∞ (u j) V :=
  h.1 j

/-- **The frame from a first-order correction**: if `v` is smooth, the corrected coordinates
`u_j(y) = y_j - v_j(y)` satisfy the `∂̄_J`-equation and their differential is invertible, then they
are a `J`-holomorphic frame.  This is the shape in which the contraction produces the frame. -/
theorem isHolFrame_of_corrections {n : ℕ} {J : Cn n → Cn n →L[ℝ] Cn n} {V : Set (Cn n)}
    {v : Fin n → Cn n → ℂ}
    (hsm : ∀ j, ContDiffOn ℝ ∞ (fun y : Cn n => y j - v j y) V)
    (hhol : ∀ j y, y ∈ V → dbarCn J (fun z : Cn n => z j - v j z) y = 0)
    (hbij : ∀ y, y ∈ V → Function.Bijective (fderiv ℝ (fun y : Cn n => fun j => y j - v j y) y)) :
    IsHolFrame J V (fun j y => y j - v j y) :=
  ⟨hsm, hhol, hbij⟩

/-- **The perturbation of an almost complex structure is small on a small polydisc.**  If
`A : ℂⁿ → ℂⁿ →L[ℝ] ℂⁿ` is `C¹` and `A 0 = 0`, then for every `ε > 0` there is a polydisc (centred
at `0`) on which `‖A z‖ ≤ ε`.  This is what makes the small perturbation argument available: the
hypothesis `∀ z ∈ pd n ρ 4, ‖A z‖ ≤ ε` of the assembly is satisfied by shrinking the polydisc
(equivalently, by the rescaling `A_λ z = A (λ z)` when the polydisc is kept fixed). -/
theorem exists_polydisc_norm_le {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n}
    (hA : ContDiff ℝ 1 A) (hA0 : A 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : Cn n, (∀ j, ‖z j‖ < δ) → ‖A z‖ ≤ ε := by
  have hcont : ContinuousAt A 0 := hA.continuous.continuousAt
  have hpre : A ⁻¹' Metric.ball (0 : Cn n →L[ℝ] Cn n) ε ∈ nhds (0 : Cn n) := by
    have h1 : Metric.ball (0 : Cn n →L[ℝ] Cn n) ε ∈ nhds (A 0) :=
      Metric.isOpen_ball.mem_nhds (by rw [hA0]; simpa using hε)
    exact hcont h1
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨δ / 2, half_pos hδpos, fun z hz => ?_⟩
  have hz' : z ∈ Metric.ball (0 : Cn n) δ := by
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).mpr
      (fun j => le_of_lt (hz j))) (by linarith)
  simpa [dist_eq_norm] using le_of_lt (Metric.mem_ball.mp (hδsub hz'))

/-- **The extension operator** (`Seeley`): a linear extension from the small polydisc `pd n ρ 1` to
the data polydisc `pd n ρ 4`, bounded at every order in the `C^{k,α}` scale.  The hypotheses are
the ones under which the flat solvers are stated (smoothness of the extended function on the small
polydisc); the choice `pd n ρ 1 ⊂ pd n ρ 4` is the one forced by the radius bookkeeping of
`Work.NN.Final.FlatOne`/`FlatTwo` (see the module docstring). -/
structure Extension (n : ℕ) (α : ℝ) (ρ : Fin n → ℝ) where
  /-- the constant in the `C^{k,α}` estimate -/
  C : ℕ → ℝ
  hC : ∀ k, 0 < C k
  /-- the extension operator -/
  E : (Cn n → ℂ) →ₗ[ℝ] (Cn n → ℂ)
  /-- it does not change the values on the small polydisc -/
  eq : ∀ v : Cn n → ℂ, (∀ m : ℕ, ContDiffOn ℝ m v (pd n ρ 1)) →
    ∀ z ∈ pd n ρ 1, E v z = v z
  /-- and it is bounded in every `C^{k,α}` -/
  est : ∀ (k : ℕ) (v : Cn n → ℂ), (∀ m : ℕ, ContDiffOn ℝ m v (pd n ρ 1)) →
    Work.CR.Flat.holderNorm k α (E v) (pd n ρ 4)
      ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α v (pd n ρ 1)
  /-- it preserves smoothness -/
  smooth : ∀ v : Cn n → ℂ, (∀ m : ℕ, ContDiffOn ℝ m v (pd n ρ 1)) →
    ∀ m : ℕ, ContDiffOn ℝ m (E v) (pd n ρ 4)

/-- **The order-0 projection onto `dbar_0`-closed `(0,1)`-forms on the polydiscs of the radius
algebra `pd n ρ 4 ⊃ pd n ρ 2`.**  This is the *strengthened* form of the `(0,2)`-input that the
assembly needs: unlike `Work.NN.Final.FlatTwo` (whose estimate consumes `C^{k+1}` data for a
`C^{k+1}` output, so that `T2 ∘ dbar_0` loses a derivative), here the composite is bounded at every
level with `C^k` data.  A realisation is `P = 1 - T2 (dbar_0 ·)` with `T2` a `(0,2)`-solver in the
class of `Work.NN.Final.uS2`/`Work.NN.Core.TelTwoDF.S2` (the loss-free recursion). -/
structure Proj (n : ℕ) (α : ℝ) (ρ : Fin n → ℝ) where
  /-- the constant of the `C^{k,α}` bound -/
  C : ℕ → ℝ
  hC : ∀ k, 0 < C k
  /-- the projection -/
  P : (Fin n → Cn n → ℂ) →ₗ[ℝ] (Fin n → Cn n → ℂ)
  /-- `f - P f` is `dbar_0`-closed on the inner polydisc -/
  closed : ∀ f : Fin n → Cn n → ℂ, (∀ j, ContDiffOn ℝ ∞ (f j) (pd n ρ 4)) →
    Work.NN.Final.Clos1 n ρ 2 (fun j z => f j z - P f j z)
  /-- `P` is bounded in every `C^{k,α}` -/
  est : ∀ (k : ℕ) (f : Fin n → Cn n → ℂ), (∀ j, ContDiffOn ℝ ∞ (f j) (pd n ρ 4)) → ∀ j,
    Work.CR.Flat.holderNorm k α (P f j) (pd n ρ 2)
      ≤ ENNReal.ofReal (C k) * ∑ j, Work.CR.Flat.holderNorm k α (f j) (pd n ρ 4)
  /-- `P` sends smooth data to smooth forms -/
  smooth : ∀ f : Fin n → Cn n → ℂ, (∀ j, ContDiffOn ℝ ∞ (f j) (pd n ρ 4)) →
    ∀ j, ContDiffOn ℝ ∞ (P f j) (pd n ρ 2)

end Work.NN.Assemble
