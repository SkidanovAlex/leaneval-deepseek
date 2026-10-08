import Mathlib
import Submission.Work.CORE3.Defs

/-!
# CORE3: any subgroup of order 8 is dihedral of order 8

`Work.CORE3.IsoDihedralFourOfCardEight`.

In the Case (1b) situation (`V = O₂(Ĥ)` elementary abelian of type (2,2), `|S| = 8`) any
subgroup `T ≤ G` of order `8` that contains `V = O₂(Ĥ)` is a Sylow 2-subgroup of `G`
(`|S| = 8` shows that the 2-part of `|G|` is exactly `8`).  By Bender's standing hypothesis
(`BenderCtx.sylow`) it is cyclic or dihedral, and it cannot be cyclic because it contains the
Klein four-group `V`.  Hence it is dihedral, and comparison of orders pins the index down to
`4`, i.e. `T ≃* DihedralGroup 4`.

The proof is a small, self-contained group-theoretic computation, so it is done directly here
rather than delegated.
-/

open Subgroup Work.GW2

namespace Work.CORE3

theorem IsoDihedralFourOfCardEight {G : Type} [Group G] [Finite G] (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case1bData B) (T : Subgroup G)
    (hT : Nat.card T = 8) (hVT : Work.GW2.pCoreIn 2 B.Hhat ≤ T) :
    Nonempty (T ≃* DihedralGroup 4) := by
  -- `|S| = 8` and `S` is a Sylow 2-subgroup, so the 2-part of `|G|` is `8`.
  have h8 : Nat.card (B.S : Subgroup G) = 8 := D.S8
  have hfac : Nat.card T = 2 ^ (Nat.card G).factorization 2 := by
    rw [hT, ← h8]
    exact Sylow.card_eq_multiplicity B.S
  -- Hence `T` is itself a Sylow 2-subgroup.
  let P : Sylow 2 G := Sylow.ofCard T hfac
  have hP : (P : Subgroup G) = T := Sylow.coe_ofCard T hfac
  rcases hBc.sylow P with hcyc | ⟨n, e⟩
  · -- `T` cannot be cyclic: it contains the Klein four-group `O₂(Ĥ)`.
    exfalso
    have hle : Work.GW2.pCoreIn 2 B.Hhat ≤ (P : Subgroup G) := by rw [hP]; exact hVT
    have hcycV : IsCyclic ↥(Work.GW2.pCoreIn 2 B.Hhat) :=
      isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have hVcard : Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) = 4 := D.four.1
    have hVsq : ∀ v ∈ (Work.GW2.pCoreIn 2 B.Hhat : Subgroup G), v ^ 2 = 1 := D.four.2
    -- A cyclic group with all elements of order dividing `2` has order at most `2`.
    obtain ⟨g, hg⟩ :=
      IsCyclic.exists_ofOrder_eq_natCard (α := ↥(Work.GW2.pCoreIn 2 B.Hhat)) (h := hcycV)
    have hg2 : g ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hVsq g.1 g.2
    have hdvd : orderOf g ∣ 2 := by rw [orderOf_dvd_iff_pow_eq_one]; exact hg2
    have hle2 : orderOf g ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · -- Otherwise `T` is dihedral; comparing with `|T| = 8` gives `DihedralGroup 4`.
    obtain ⟨e⟩ := e
    have e' : T ≃* DihedralGroup n := hP ▸ e
    have hn : n = 4 := by
      have h2n : 2 * n = 8 := by
        rw [← DihedralGroup.nat_card, ← Nat.card_congr e'.toEquiv]
        exact hT
      omega
    exact ⟨hn ▸ e'⟩

end Work.CORE3
