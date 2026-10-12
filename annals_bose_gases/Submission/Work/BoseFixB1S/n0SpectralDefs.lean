import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SKELETON — the `n₀` spectral layer (`FINDING_perBoxFWeightB1.md` §7.7, obligation (Q1-b))

**SKELETON: `n0ProjOp_partition_and_eigen` at the bottom carries a marked `sorry`; nothing in the
`Solution` closure may import this file.**

## Why this layer exists

FS `lm:appinteractionestimate` completes the square with the *operator* weights
`(n₀+1)^{1/2} ± (μ|B|)^{1/2}`, `n₀ = Σᵢ P_{B,i}` (`NOTES_crux_FScompletion.md` §1, §3).  The
collapsing identity `boxCrossPart − 2μP = (2/V)Σᵢ⟨qᵢ, f(xᵢ)(n₀−1−c)pᵢ⟩` is *proved*
(`BoseFixB1S.boxCrossPart_sub_twoMuP_eq_operatorB1`) and the AM–GM engine that consumes the
`√`-factorisation is *proved* (`BoseFixB1S.weighted_amgm_integral`).  Missing is the `√` itself:
there is **no functional calculus for `n₀`** here nor in Mathlib.

## THE TRAPS (both hit already — read before editing)

1. **Composition, not pointwise product.**  `P_{B,i}P_{B,j}` is `Ψ ↦ P_{B,i}(P_{B,j}Ψ)`, *not*
   `x ↦ P_{B,i}Ψ x · P_{B,j}Ψ x`.  With the pointwise reading the partition of unity reads
   `Σ_{S}(∏_{i∈S}aᵢ(x))(∏_{i∉S}(Ψx−aᵢ(x))) = (Ψx)^N` (`Finset.prod_add`), false for `N ≥ 2`
   (e.g. `A = acube ℓ`, `Ψ ≡ 2`: `2^N ≠ 2`).  One reviewed-and-refuted statement was lost to this.
   Only the **single-slot** complement `1 − P_{B,i}` is pointwise.
2. **`Function.End` is only a `Monoid`** (its `Mul` *is* `Function.comp`, but there is no
   `CommMonoid`/`AddCommMonoid`), so `∏`/`∑`/`•` do not elaborate on it
   (`failed to synthesize CommMonoid (Function.End …)`).  Hence `n0Iter` below is a
   **typeclass-free list recursion**, and sums/smuls of operators are taken **pointwise on
   `X N → ℝ`** (where the `CommMonoid` does exist).  A sum of operators acting pointwise is
   correct — only *products* had to be compositions.

## The mathematics

Under the standing hypotheses (`MeasurableSet A`, `volA = |A|`, `A ⊆ acube ℓ`), each `P_{B,i}` is
an orthogonal projection and the `P_{B,i}` commute.  Then

* the subset idempotents `n0ProjOp S` are mutually orthogonal projections summing to the identity
  (`1 = ∏ᵢ(P_{B,i} + (1−P_{B,i}))` — this half needs **no** commutation, the expansion of a product
  of sums respects any fixed order), and `n₀ := Σᵢ P_{B,i}` acts on each as `S.card` (*this* half
  needs `P_{B,i}P_{B,j} = P_{B,j}P_{B,i}`, from the symmetric double-slot-mean form
  `BoseFixB1S.Q0C.boxPInd_pair_ins2`);
* hence `n0LagrangeOp k` (`k = 0..N`) are the Lagrange idempotents of `n₀`, and
  `g(n₀) = Σ_{k≤N} g k • n0LagrangeOp k`, in particular
  `√(n₀+1) = Σ_{k≤N} √(k+1) • n0LagrangeOp k` — exactly what `Θ±` need.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **`n₀` acting on functions**: `(n₀Ψ)(x) = Σᵢ (P_{B,i}Ψ)(x)`.  (The `Λ`/`n₀ = ΣᵢP_{B,i}` of the
`boxCrossJoint` crux.) -/
def n0Op {N : ℕ} (volA : ℝ) (A : Set E3) (Ψ : X N → ℝ) : X N → ℝ :=
  fun x => ∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Ψ x

/-- **The slot-wise operator iteration.**  Walks the slot list left to right; at slot `i` applies
either `P_{B,i}` (when `b i = true`) or the *single-slot complement* `1 − P_{B,i}` (pointwise
difference of applied values), always by **composition** of the resulting functions.  Typeclass-free
on purpose (see trap 2 in the module docstring). -/
def n0Iter {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool) :
    List (Fin N) → (X N → ℝ) → (X N → ℝ)
  | [], Ψ => Ψ
  | i :: l, Ψ =>
      if b i then n0Iter volA A b l (fun x => Work.UBBInputs8.boxPInd volA A i Ψ x)
      else n0Iter volA A b l (fun x => Ψ x - Work.UBBInputs8.boxPInd volA A i Ψ x)

/-- **The subset idempotent** `∏_{i∈S} P_{B,i} · ∏_{i∉S}(1 − P_{B,i})`, as an endomorphism built by
the slot-wise composition `n0Iter` over the canonical slot list. -/
def n0ProjOp {N : ℕ} (volA : ℝ) (A : Set E3) (S : Finset (Fin N)) :
    (X N → ℝ) → (X N → ℝ) :=
  n0Iter volA A (fun i => decide (i ∈ S)) (List.ofFn (fun i : Fin N => i))

/-- **The Lagrange idempotent of index `k`**: the (pointwise) sum of the subset idempotents of
cardinality `k`.  Sums of operators are pointwise — only products compose. -/
def n0LagrangeOp {N : ℕ} (volA : ℝ) (A : Set E3) (k : ℕ) : (X N → ℝ) → (X N → ℝ) :=
  fun Ψ => fun x => ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)),
    n0ProjOp volA A S Ψ x

/-- **The functional calculus**: `g(n₀)`, as the explicit (pointwise) finite sum over the Lagrange
idempotents.  This is the object `Θ₊`/`Θ₋` are built from: `n0FunOp (fun r => Real.sqrt (r+1))`
is `√(n₀+1)`. -/
def n0FunOp {N : ℕ} (volA : ℝ) (A : Set E3) (g : ℝ → ℝ) : (X N → ℝ) → (X N → ℝ) :=
  fun Ψ => fun x => ∑ k ∈ Finset.range (N + 1), g (k : ℝ) * n0LagrangeOp volA A k Ψ x

/-! ## The obligation (SKELETON `sorry`) -/

/-- **(Q1-b)(i) — partition of unity and the eigen-property.**  The subset idempotents sum to the
identity (no commutation needed), and `n₀` acts on each as its cardinality (needs
`P_{B,i}P_{B,j} = P_{B,j}P_{B,i}`). -/
theorem n0ProjOp_partition_and_eigen {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Ψ : X N → ℝ} (hΨc : Continuous Ψ) :
    (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)),
        (∑ S : Finset (Fin N), (n0ProjOp volA A S) Ψ x) = Ψ x)
      ∧ ∀ S : Finset (Fin N),
          (fun x => n0Op volA A ((n0ProjOp volA A S) Ψ) x)
            =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)]
              fun x => (S.card : ℝ) * ((n0ProjOp volA A S) Ψ x) := by sorry

end Work.BoseFixB1S
