import Mathlib
import Submission.Work.Stems.Hurewicz

/-!
# The drive's contract for the rational Hurewicz theorem in the stable range

Written by the project lead. **Do not edit.** Consumers: area THOM (injectivity for the Thom space of the
universal oriented bundle) and area STEMS (applied to `Sⁿ` it gives `Work.Drive.StableStemsTorsion`).

`Work.Drive.RationalHurewiczStable`: if `X` is `(k−1)`-connected (`k ≥ 2`: every `πᵢ(X, x₀)`, `i < k`,
including `π₀`, is trivial), then in degrees `1 ≤ i ≤ 2k − 2` the Hurewicz map is injective modulo
torsion: a class whose Hurewicz image (`Work.Stems.hurewiczChain`, the singular class of the cube pushed
to the sphere) has finite order has itself finite order. This is the injectivity half of the rational
Hurewicz theorem (Serre; e.g. Klaus–Kreck, *A quick proof of the rational Hurewicz theorem*), whose
range for a `(k−1)`-connected space is `i ≤ 2k − 2`.
-/

namespace Work.Drive

open scoped Topology

/-- **The rational Hurewicz theorem in the stable range (injectivity form).** -/
def RationalHurewiczStable : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
    (∀ i < k, Subsingleton (HomotopyGroup (Fin i) X x₀)) →
    ∀ (i : ℕ), i + 1 ≤ 2 * k - 2 →
      ∀ p : GenLoop (Fin (i + 1)) X x₀,
        (∃ N : ℕ, 0 < N ∧
          (N : ℤ) • Work.Stems.hurewiczChain (i + 1) (Nat.succ_le_succ (Nat.zero_le i)) x₀ p = 0) →
        ∃ N : ℕ, 0 < N ∧ (show HomotopyGroup (Fin (i + 1)) X x₀ from Quotient.mk _ p) ^ N = 1

/-- **The same statement one degree short of the boundary** (range `i + 1 ≤ 2k − 3`). It avoids the top
degree `2k − 2`, which is the genuinely stable case. It is all that area THOM needs: the Thom space
of a rank-`k` bundle is `(k−1)`-connected and the relevant degree is `k + 8 ≤ 2k − 3` once `k ≥ 11`. -/
def RationalHurewiczStable3 : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
    (∀ i < k, Subsingleton (HomotopyGroup (Fin i) X x₀)) →
    ∀ (i : ℕ), i + 1 ≤ 2 * k - 3 →
      ∀ p : GenLoop (Fin (i + 1)) X x₀,
        (∃ N : ℕ, 0 < N ∧
          (N : ℤ) • Work.Stems.hurewiczChain (i + 1) (Nat.succ_le_succ (Nat.zero_le i)) x₀ p = 0) →
        ∃ N : ℕ, 0 < N ∧ (show HomotopyGroup (Fin (i + 1)) X x₀ from Quotient.mk _ p) ^ N = 1

/-- The full statement implies the one-short statement. -/
theorem rationalHurewiczStable3_of_stable (h : RationalHurewiczStable) : RationalHurewiczStable3 :=
  fun k hk X _ x₀ hc i hi p hp => h k hk X x₀ hc i (by omega) p hp

end Work.Drive
