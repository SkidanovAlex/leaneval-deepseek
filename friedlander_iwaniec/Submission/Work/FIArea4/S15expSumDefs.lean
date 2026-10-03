/-
# FI §15: shared definitions for the variance half (`S15expSum_bound`)

The separated §15 sum `S15expSum` is a sum over the index set `S15ixSet` (pairs `(z1,z2)` of the
box with `(z1,z2) = 1` and `Δ ≠ 0`, and moduli `d` with `X < d ≤ Y`, `4d ∣ |Δ|`).  For the
variance argument of FI (15.1)–(15.2) it is convenient to fix the modulus `d`; this module
isolates the resulting *per-modulus* sum `S15pD` and the elementary reindexing
`S15expSum = Σ_d S15pD`.
-/
import Mathlib
import Submission.Work.FIArea4.S15cutDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Commutation of a triple sum. -/
lemma sum_comm3 {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c) = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c
      = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, f a b c := by
          refine Finset.sum_congr rfl (fun a _ => ?_); exact Finset.sum_comm
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := Finset.sum_comm

/-- **The per-modulus §15 sum**: the separated sum `S15expSum` with the modulus `d` fixed. -/
def S15pD (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Work.FIPlan.GaussCoprime z1 z2 ∧ X < d ∧
        4 * d ∣ Work.FIPlan.absDelta z1 z2 ∧ 0 < Work.FIPlan.absDelta z1 z2
      then S15coef β ((z1, z2), d) * S15theta ℓ z1 z2 * S15phase X j u t ((z1, z2), d)
      else 0)

/-- The Jacobi weight `(r | d')`, `d' = oddPart d`, for a (possibly negative) integer `r`. -/
def jwG (m : ℕ) (r : ℤ) : ℂ := ((jacobiSym r (Work.FIPlan.oddPart m) : ℤ) : ℂ)

/-- The `a`-th class sum of the *signed* box `gBox R`: the sum over `z` with `(Re z, m) = 1` and
`Im z ≡ a·Re z (mod m)` of `u z · (Re z | oddPart m)`. -/
def clsSumG (R : ℤ) (m : ℕ) (u : GaussianInt → ℂ) (a : ℕ) : ℂ :=
  ∑ z ∈ (Work.FIPlan.gBox R).filter (fun z =>
      Nat.Coprime z.re.natAbs m ∧ ((z.im : ZMod m) = (a : ZMod m) * (z.re : ZMod m))),
    u z * jwG m z.re

/-- The local variance of the *signed* box (the object the class Cauchy–Schwarz of FI §§11–12,15
bounds a twisted pair sum over `gBox R` by). -/
def EvarG (R : ℤ) (m : ℕ) (u : GaussianInt → ℂ) : ℝ :=
  ∑ a ∈ Finset.range m, Complex.normSq (clsSumG R m u a)

/-- **Reindexing of the separated sum by the modulus.**  `S15expSum` is the sum of its
per-modulus pieces `S15pD` over `d ∈ [1, S15Y Pa X j]`. -/
lemma S15expSum_eq_sum_pD (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ)
    (u t : ℝ) :
    S15expSum Pa X j β ℓ u t = ∑ d ∈ Finset.Icc 1 (S15Y Pa X j), S15pD Pa X j d β ℓ u t := by
  classical
  let G : (GaussianInt × GaussianInt) × ℕ → ℂ := fun p =>
    (if Work.FIPlan.GaussCoprime p.1.1 p.1.2 ∧ X < p.2 ∧
        4 * p.2 ∣ Work.FIPlan.absDelta p.1.1 p.1.2 ∧ 0 < Work.FIPlan.absDelta p.1.1 p.1.2
     then S15coef β p * S15theta ℓ p.1.1 p.1.2 * S15phase X j u t p else 0)
  have h1 : S15expSum Pa X j β ℓ u t
      = ∑ p ∈ (Work.FITop.boxN Pa ×ˢ Work.FITop.boxN Pa) ×ˢ Finset.Icc 1 (S15Y Pa X j),
          G p := by
    unfold S15expSum S15ixSet
    rw [Finset.sum_filter]
    rfl
  have h2 : (∑ p ∈ (Work.FITop.boxN Pa ×ˢ Work.FITop.boxN Pa) ×ˢ
        Finset.Icc 1 (S15Y Pa X j), G p)
      = ∑ d ∈ Finset.Icc 1 (S15Y Pa X j), S15pD Pa X j d β ℓ u t := by
    rw [Finset.sum_product, Finset.sum_product, sum_comm3]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    unfold S15pD
    rfl
  exact h1.trans h2

/-- The per-modulus §15 sum **without** the coprimality filter `GaussCoprime` (the sum over all
pairs of the box satisfying the modulus/cut conditions). -/
def S15pDng (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 ∧ 0 < Work.FIPlan.absDelta z1 z2
      then S15coef β ((z1, z2), d) * S15theta ℓ z1 z2 * S15phase X j u t ((z1, z2), d)
      else 0)

/-- `S15expSum` with the coprimality filter `GaussCoprime` dropped. -/
def S15expSumng (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ)
    (u t : ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 (S15Y Pa X j), S15pDng Pa X j d β ℓ u t


end

end Work.FIArea4
