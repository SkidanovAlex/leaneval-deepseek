import Mathlib
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Alt.B_eq_inter_localizations
import Submission.Work.SpecLin.Alt.denomIdeal
import Submission.Work.SpecLin.Setup.krullDimLE_tensor
import Submission.Work.SpecLin.Setup.height_le_one_of_under_bot
import Submission.Work.SpecLin.Setup.hartogsBridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000

namespace Work.SpecLin.Setup

open Work.SpecLin.Alt

universe u

/-- **The denominator-ideal characterisation of `InLocalization`.**

`x : FractionRing B` lies in the localisation of the domain `B` at the prime `I` if and only if
the denominator ideal of `x` (the ideal of all `b` with `x * b ∈ B`) is not contained in `I`. -/
theorem inLocalization_iff_denomIdeal_not_le {B : Type u} [CommRing B] [IsDomain B]
    (x : FractionRing B) (I : Ideal B) :
    InLocalization x I ↔ ¬ (denomIdeal x : Ideal B) ≤ I := by
  constructor
  · rintro ⟨b, s, hs, hbs⟩ hle
    have hsD : s ∈ denomIdeal x := by
      rw [mem_denomIdeal]
      exact ⟨b, hbs⟩
    exact hs (hle hsD)
  · intro h
    by_contra hcon
    exact h (fun d hd => by
      by_contra hdI
      exact hcon (by
        rw [mem_denomIdeal] at hd
        obtain ⟨b, hb⟩ := hd
        exact ⟨b, d, hdI, hb⟩))

/-- **The "horizontal" form of the bridge implies the height-one form.**

If the denominator ideal of `x` is contained in a prime `q ≤ N` lying over the generic point of
`Spec R` (`q ∩ R = ⊥`), then it is contained in a prime of height one: primes over the generic
point have height `≤ 1` (`height_le_one_of_under_bot`), and the height is not `0` because the
denominator ideal of an element of a fraction field is nonzero (`denomIdeal_ne_bot`). -/
theorem denomIdeal_le_of_horizontal {K : Type u} [Field K] (A : Type u) [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Ring.KrullDimLE 1 A]
    (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    (N : Ideal (TensorProduct K A R)) [N.IsMaximal]
    (x : FractionRing (TensorProduct K A R))
    (H : ∃ q : Ideal (TensorProduct K A R), q.IsPrime ∧ q ≤ N ∧
      q.comap (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) = ⊥ ∧
      (denomIdeal x : Ideal (TensorProduct K A R)) ≤ q) :
    ∃ q : Ideal (TensorProduct K A R), q.IsPrime ∧ q.height = 1 ∧ q ≤ N ∧
      (denomIdeal x : Ideal (TensorProduct K A R)) ≤ q := by
  obtain ⟨q, hq, hqN, hqbot, hDq⟩ := H
  have hheight : q.height = 1 := by
    refine le_antisymm ?_ ?_
    · exact height_le_one_of_under_bot (K := K) A hA R q hqbot
    · rw [Order.one_le_iff_ne_zero]
      intro h0
      have hbot : q = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp h0
      have hDne : (denomIdeal x : Ideal (TensorProduct K A R)) ≠ ⊥ := denomIdeal_ne_bot x
      rw [hbot] at hDq
      exact hDne (le_bot_iff.mp hDq)
  exact ⟨q, hq, hheight, hqN, hDq⟩

/-- **The `N`-localised Hartogs/`S2` statement for the relative curve.**

If the denominator ideal of `x ∈ Frac(A ⊗[K] R)` is contained in a maximal ideal `N ⊇ P` of the
relative chart `B = A ⊗[K] R`, then (provided `x` lies in the localisation at the fibre prime
`P = 𝔪_R·B`) it is contained in a height-one prime `≤ N`.

This is the "principal ideal"/`S2` content at `N`; combined with
`inLocalization_iff_denomIdeal_not_le` it proves `hartogsRelativeCurve`. -/
theorem denomIdeal_le_of_le_maximal {K : Type u} [Field K] (A : Type u) [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] [Algebra.Smooth K A] [Ring.KrullDimLE 1 A]
    (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    [IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))]
    (N : Ideal (TensorProduct K A R)) [N.IsMaximal]
    (hPN : ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))) ≤ N)
    (x : FractionRing (TensorProduct K A R))
    (hxP : Work.SpecLin.Alt.InLocalization x ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (hD : (denomIdeal x : Ideal (TensorProduct K A R)) ≤ N) :
    ∃ q : Ideal (TensorProduct K A R), q.IsPrime ∧ q.height = 1 ∧ q ≤ N ∧
      (denomIdeal x : Ideal (TensorProduct K A R)) ≤ q :=
  hartogsBridge A hA R N hPN x hxP hD

theorem hartogsRelativeCurve {K : Type u} [Field K] (A : Type u) [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] [Algebra.Smooth K A] [Ring.KrullDimLE 1 A]
    (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    [IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))]
    (N : Ideal (TensorProduct K A R)) [N.IsMaximal]
    (hPN : ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))) ≤ N)
    (x : FractionRing (TensorProduct K A R))
    (hxP : Work.SpecLin.Alt.InLocalization x ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (hxq : ∀ p : Ideal (TensorProduct K A R), p.IsPrime → p.height = 1 → p ≤ N →
      Work.SpecLin.Alt.InLocalization x p) :
    Work.SpecLin.Alt.InLocalization x N := by
  by_contra hxN
  rw [inLocalization_iff_denomIdeal_not_le] at hxN
  push Not at hxN
  obtain ⟨q, hq, hq1, hqN, hDq⟩ :=
    denomIdeal_le_of_le_maximal A hA R N hPN x hxP hxN
  have := hxq q hq hq1 hqN
  rw [inLocalization_iff_denomIdeal_not_le] at this
  exact this hDq

end Work.SpecLin.Setup
