import Mathlib
import Submission.Work.StemsB.RangeModelPlan
import Submission.Work.StemsB.fg_abelian_decomposition
import Submission.Work.StemsB.rangeModel_ratH_iso
import Submission.Work.StemsB.fgRangeModel_acyclic_two

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.StemsB

/-- **The finitely generated case, from the free case and `C3FiniteTwo`.**

Same reduction as `Work.StemsB.fgCase_of_free_and_C3`, with the `k ≥ 2` restriction `C3FiniteTwo`
of `C3Finite`: the structure theorem for finitely generated abelian groups
(`Work.StemsB.fg_abelian_decomposition`) writes `A ≃+ ℤ^r × F` with `F` finite, the model
hypothesis transports along the isomorphism of coefficient groups
(`Work.RatHurewicz.isEMSpaceUpTo_of_addEquiv`), and the `(free) × (finite)` case is
`Work.StemsB.fgRangeModel_acyclic_two`. -/
theorem fgCase_of_free_and_C3_two
    (hfree : ∀ (r : ℕ) (k N : ℕ) (hk : 2 ≤ k) (hN : 2 * k - 1 ≤ N)
      (Y : Type) [TopologicalSpace Y] (y : Y),
        Work.Serre.IsEMSpaceUpTo (Fin r → ℤ) k (by omega) N Y y →
        ∀ i : ℕ, k < i → i ≤ 2 * k - 1 →
          CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of Y) i))
    (hC3 : Work.StemsB.C3FiniteTwo)
    (A : Type) [AddCommGroup A] [Module.Finite ℤ A] (k N : ℕ) (hk : 2 ≤ k) (hN : 2 * k - 1 ≤ N)
    (X : Type) [TopologicalSpace X] (pt : X)
    (hX : Work.Serre.IsEMSpaceUpTo A k (by omega) N X pt) :
    ∀ i : ℕ, k < i → i ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) i) := by
  -- the structure theorem for finitely generated abelian groups
  obtain ⟨r, F, hFadd, hFfin, ⟨e⟩⟩ := Work.StemsB.fg_abelian_decomposition A
  letI : AddCommGroup F := hFadd
  letI : Finite F := hFfin
  -- transport the model hypothesis across `A ≃+ ℤ^r × F`
  have hX' : Work.Serre.IsEMSpaceUpTo ((Fin r → ℤ) × F) k (by omega) N X pt :=
    Work.RatHurewicz.isEMSpaceUpTo_of_addEquiv (by omega) pt hX e
  -- and apply the (free) × (finite) case
  exact Work.StemsB.fgRangeModel_acyclic_two hfree hC3 r F k N hk hN X pt hX'

end Work.StemsB
