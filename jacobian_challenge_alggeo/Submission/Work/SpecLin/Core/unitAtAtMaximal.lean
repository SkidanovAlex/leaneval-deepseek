import Mathlib
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Alt.conservationNumber_noetherian
import Submission.Work.SpecLin.Setup.krullDimLE_tensor
import Submission.Work.SpecLin.Alt.B_eq_inter_localizations
import Submission.Work.SpecLin.Setup.unitOfGenericUnit
import Submission.Work.SpecLin.Setup.height_le_one_of_under_bot
import Submission.Work.SpecLin.Core.underBotPrime.exists_prime_le_under_bot
import Submission.Work.Setup.curveHartogsCrux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Core

universe u

/-- **The `S2`/Hartogs core of `unitAtAtMaximal`.**

`A` is a finitely generated smooth `K`-domain of Krull dimension one, `R` a valuation ring which
is a `K`-algebra, `B = A ⊗[K] R` a domain whose special fibre `A ⊗[K] κ(R)` is a domain (so that
the fibre prime `P = 𝔪_R·B` is prime), `N ⊇ P` a maximal ideal, and `x ∈ Frac B` a rational
function which is *regular* at `P` (`x ∈ B_P`) but **not** regular at `N` (`x ∉ B_N`).

Then `x` already fails to be regular at some height-one prime `q ≤ N`, which in fact lies over the
generic point of `Spec R`.

Proof.  By the denominator-ideal characterisation of `InLocalization`,
`hxN` says `D := denomIdeal x ≤ N`.  The local Hartogs theorem
`Work.SpecLin.Core.underBotPrime.hartogsCrux_comap_eq_bot` produces a prime `q ≤ N` with
`D ≤ q` and `q ∩ R = ⊥`; its height is `≤ 1` because it lies over the generic point of `Spec R`
(`height_le_one_of_under_bot`, the generic fibre being a curve), and `≥ 1` because `D ≠ 0`. -/
theorem InLocalization_of_notMem_maximalIdeal
    {K : Type u} [Field K] (A : Type u) [CommRing A] [IsDomain A]
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
    (hxN : ¬ Work.SpecLin.Alt.InLocalization x N) :
    ∃ q : Ideal (TensorProduct K A R), q.IsPrime ∧ q.height = 1 ∧ q ≤ N ∧
      ¬ Work.SpecLin.Alt.InLocalization x q := by
  classical
  -- the denominator ideal of `x` is contained in `N`
  have hD : (Work.SpecLin.Alt.denomIdeal x : Ideal (TensorProduct K A R)) ≤ N := by
    by_contra h
    exact hxN ((Work.Setup.inLocalization_iff_not_le_denomIdeal x N).mpr h)
  obtain ⟨q, hqprime, hqN, hqbot, hDq⟩ :=
    Work.SpecLin.Core.underBotPrime.hartogsCrux_comap_eq_bot (K := K) A hA R N hPN x hxP hD
  refine ⟨q, hqprime, le_antisymm ?_ ?_, hqN, ?_⟩
  · exact Work.SpecLin.Setup.height_le_one_of_under_bot (K := K) A hA R q hqbot
  · rw [Order.one_le_iff_ne_zero]
    intro h0
    exact (Work.SpecLin.Alt.denomIdeal_ne_bot x)
      (le_bot_iff.mp (le_trans hDq (le_of_eq (Ideal.height_eq_zero_iff_eq_bot.mp h0))))
  · exact fun h => (Work.Setup.inLocalization_iff_not_le_denomIdeal x q).mp h hDq

theorem unitAtAtMaximal {K : Type u} [Field K] (A : Type u) [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] [Algebra.Smooth K A] [Ring.KrullDimLE 1 A]
    (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    [IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))]
    (N : Ideal (TensorProduct K A R)) [N.IsMaximal]
    (hPN : ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))) ≤ N)
    (u : FractionRing (TensorProduct K A R))
    (hP : Work.SpecLin.Alt.IsUnitAt u ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (hht : forall p : Ideal (TensorProduct K A R), p.IsPrime -> p.height = 1 -> p ≤ N ->
      Work.SpecLin.Alt.IsUnitAt u p) :
    Work.SpecLin.Alt.IsUnitAt u N := by
  refine ⟨?_, ?_⟩
  · by_contra h
    obtain ⟨q, hq, hq1, hqN, hxq⟩ :=
      InLocalization_of_notMem_maximalIdeal (K := K) A hA R N hPN u hP.1 h
    exact hxq (hht q hq hq1 hqN).1
  · by_contra h
    obtain ⟨q, hq, hq1, hqN, hxq⟩ :=
      InLocalization_of_notMem_maximalIdeal (K := K) A hA R N hPN u⁻¹ hP.2 h
    exact hxq (hht q hq hq1 hqN).2

end Work.SpecLin.Core
