import Mathlib
import Submission.Work.StemsB.RangeModelPlan
import Submission.Work.StemsB.rangeModel_ratH_iso
import Submission.Work.StemsB.fgRangeModel_acyclic
import Submission.Work.Serre.serreC0Range

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.StemsB

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- `Work.StemsB.fgRangeModel_acyclic` with the `k ≥ 2` restriction `C3FiniteTwo` of `C3Finite`.

The proof is the same as for `fgRangeModel_acyclic`; the only hypothesis actually consumed from
`hC3` is the vanishing of the rational homology of a range model of `K(F,k)` for a *finite* `F`
in degrees `0 < i ≤ N`, which `C3FiniteTwo` supplies in the range `k ≥ 2` needed here. -/
theorem fgRangeModel_acyclic_two
    (hfree : ∀ (r : ℕ) (k N : ℕ) (hk : 2 ≤ k) (hN : 2 * k - 1 ≤ N)
      (Y : Type) [TopologicalSpace Y] (y : Y),
        Work.Serre.IsEMSpaceUpTo (Fin r → ℤ) k (by omega) N Y y →
        ∀ i : ℕ, k < i → i ≤ 2 * k - 1 →
          CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of Y) i))
    (hC3 : Work.StemsB.C3FiniteTwo)
    (r : ℕ) (F : Type) [AddCommGroup F] [Finite F] (k N : ℕ) (hk : 2 ≤ k) (hN : 2 * k - 1 ≤ N)
    (X : Type) [TopologicalSpace X] (pt : X)
    (hX : Work.Serre.IsEMSpaceUpTo ((Fin r → ℤ) × F) k (by omega) N X pt) :
    ∀ i : ℕ, k < i → i ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) i) := by
  intro i hi1 hi2
  have hkN : k ≤ N := by omega
  -- range models of `K(ℤ,k)` and of `K(F,k)` through degree `N`
  obtain ⟨L, tL, l₀, hL⟩ := Work.Serre.serreC0Range ℤ k N (by omega) hkN
  letI : TopologicalSpace L := tL
  obtain ⟨T, tT, t₀, hT⟩ := Work.Serre.serreC0Range F k N (by omega) hkN
  letI : TopologicalSpace T := tT
  -- the product model is a range model of `K(ℤ^r × F, k)` through `N`
  have hprod : Work.Serre.IsEMSpaceUpTo ((Fin r → ℤ) × F) k (by omega) N ((Fin r → L) × T)
      ((fun _ => l₀), t₀) :=
    Work.RatHurewicz.isEMSpaceUpTo_freeTorsion (A := (Fin r → ℤ) × F) (F := F) k N hk hN r
      l₀ t₀ (AddEquiv.refl _) hL hT
  -- the two classical cases
  have hPEM : Work.Serre.IsEMSpaceUpTo (Fin r → ℤ) k (by omega) N (Fin r → L) (fun _ => l₀) :=
    Work.RatHurewicz.isEMSpaceUpTo_pi_fin (by omega) r l₀ hL
  have hP : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Fin r → L)) j) :=
    fun j hj1 hj2 => hfree r k N hk hN (Fin r → L) (fun _ => l₀) hPEM j hj1 hj2
  have hTvan : ∀ j : ℕ, 0 < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of T) j) :=
    fun j hj1 hj2 => hC3 F k hk N T t₀ hT j hj1 (by omega)
  -- connectivities
  have hPc : Work.Serre.Conn (Fin r → L) (fun _ => l₀) k :=
    Work.Stems.conn_fin_prod k r l₀ (fun j hj => hL.2 j (by omega) (Or.inl hj))
  have hTc : Work.Serre.Conn T t₀ k := fun j hj => hT.2 j (by omega) (Or.inl hj)
  -- the product step
  have hvan := productModel_ratH_vanishing (fun _ => l₀) t₀ k hk hPc hTc hP hTvan i hi1 hi2
  -- the comparison of range models of `K(ℤ^r × F, k)`
  obtain ⟨e⟩ := Work.StemsB.rangeModel_ratH_iso ((Fin r → ℤ) × F) k N hk X pt hX
    ((Fin r → L) × T) ((fun _ => l₀), t₀) hprod i (by omega)
  exact CategoryTheory.Limits.IsZero.of_iso hvan e

end

end Work.StemsB
