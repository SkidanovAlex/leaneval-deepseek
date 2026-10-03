import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs

/-!
# Tao's Ionescu–Wainger major arcs: the arithmetic vocabulary (1-dimensional)

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
Definition `major-arc` (local copy `REFS/Tao_2008.05066_IonescuWainger.tex`), specialised to
`d = 1` (which is all the polynomial ergodic theorem on `ℤ` needs: its multipliers are scalar).

For a finite set `S` of **pairwise coprime** integers `≥ 2` (in the application,
`S = taoSetS ρ N` of `TaoDefs.lean`) and `A ⊆ S` put `Q_A = ∏_{q ∈ A} q`.  Then

* `sigmaSubA A` is Tao's `Σ_{⊆ A} = 𝕋[Q_A]`, the `Q_A`-torsion subgroup of the circle;
* `sigmaA A` is Tao's `Σ_A`, the points of *exact* denominator `Q_A`, encoded as `a/Q_A` with
  `gcd(a, Q_A) = 1`;
* `sigmaLe S k` is Tao's `Σ_{≤ k} = ⋃_{A ∈ binom(S,≤k)} Σ_{⊆ A}`;
* `sigmaComp S k A₀` is Tao's `Σ_{(A₀)} = ⋃_{A ∈ binom(S∖A₀, ≤k−|A₀|)} Σ_A`.

The mathematical content needed downstream is the *denominator orthogonality* of Tao's Lemma
`ortho`(ii): a signed sum of points of `Σ_A`, over a family of sets carrying a **nonce**, is never
`0` in `𝕋`.  The heart of that is the purely arithmetic statement
`sigmaA_sum_ne_zero` below (the `θ`-perturbations of the arc system are handled separately, by the
`ε`-smallness of the `(r,c)`-good condition).
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- The circle `𝕋 = ℝ/ℤ`. -/
abbrev Circle : Type := AddCircle (1 : ℝ)

/-- The point `a / Q` of the circle. -/
noncomputable def arcPt (Q : ℕ) (a : ℤ) : Circle := (((a : ℝ) / (Q : ℝ) : ℝ) : Circle)

/-- `Q_A = ∏_{q ∈ A} q`. -/
def QA (A : Finset ℕ) : ℕ := ∏ q ∈ A, q

/-- Tao's `Σ_{⊆ A} = 𝕋[Q_A]`: the points `a/Q_A`. -/
noncomputable def sigmaSubA (A : Finset ℕ) : Set Circle := Set.range (arcPt (QA A))

/-- Tao's `Σ_A`: the points of *exact* denominator `Q_A`, i.e. `a/Q_A` with `gcd(a, Q_A) = 1`. -/
noncomputable def sigmaA (A : Finset ℕ) : Set Circle :=
  {x | ∃ a : ℤ, Nat.Coprime a.natAbs (QA A) ∧ x = arcPt (QA A) a}

/-- Tao's `Σ_{≤ k} = ⋃_{A ∈ binom(S,≤k)} Σ_{⊆ A}`. -/
noncomputable def sigmaLe (S : Finset ℕ) (k : ℕ) : Set Circle :=
  ⋃ A ∈ S.powerset.filter (fun A => A.card ≤ k), sigmaSubA A

/-- Tao's `Σ_{(A₀)} = ⋃_{A ∈ binom(S∖A₀, ≤k−|A₀|)} Σ_A`. -/
noncomputable def sigmaComp (S : Finset ℕ) (k : ℕ) (A₀ : Finset ℕ) : Set Circle :=
  ⋃ A ∈ (S \ A₀).powerset.filter (fun A => A.card ≤ k - A₀.card), sigmaA A

end Work.BourgainPlan.IonescuWainger
