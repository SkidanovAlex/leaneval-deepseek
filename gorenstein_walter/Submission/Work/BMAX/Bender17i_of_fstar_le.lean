/-
# BMAX — Bender 1981, Lemma 2.3(i): `F_π(B) ≤ A` from `F*(A) ≤ B`

The target of this file is

  `Work.BMAX.Bender17i_of_fstar_le`:
  for a finite simple group `G`, a coatomic (maximal) subgroup `A`, a proper subgroup
  `B ≠ ⊤` with `F*(A) ≤ B`, and `F*(A)` *not* a `p`-group for any prime `p`,
  `F_π(B) ≤ A`, where `π = π(F(A)) = primesOf (fittingIn A)`.

## Structure of the proof

`F_π(B) = O_π(F(B))` is contained in the join of the `q`-cores `O_q(B)`, `q ∈ π`
(`Work.BMAX.fittingPiIn_le_iSup_pCoreIn`), so it suffices to show `O_q(B) ≤ A` for a prime
`q ∈ π`.

Fix such a `q`.  Since `F(A) ◁ A` is nontrivial (as `q ∣ |F(A)|`) and `A` is a coatom of the
simple group `G`, any subgroup `M ≤ G` normalising a nontrivial normal subgroup `N` of `A`
lies in `A` (`Work.BMAX.le_coatom_of_le_normalizer_of_ne_bot`).  So it suffices to exhibit
`⊥ ≠ N ≤ A`, `N ◁ A`, normalised by `O_q(B)`:

* **Layer case** `layerIn A ≠ ⊥`: take `N = layerIn A = E(A)`; the Thompson `P × K` lemma
  (Bender 1970, 1.1), applied with `P = O_q(A)`, `K = O^q(E(A)) = E(A)` and target `O_q(B)`,
  gives `⁅O_q(B), E(A)⁆ = ⊥` (`Work.BMAX.pCoreIn_commutator_layerIn`).

* **Fitting case** `layerIn A = ⊥`: then `F*(A) = F(A)`, and since `F*(A)` is not a `p`-group
  (hypothesis) while `q ∣ |F(A)|`, some prime `r ≠ q` divides `|F(A)|`.  Then `O_r(A) ≠ ⊥`
  and the Thompson lemma with `P = O_q(A)`, `K = O_r(A)` gives
  `⁅O_q(B), O_r(A)⁆ = ⊥` (`Work.BMAX.pCoreIn_commutator_pCoreIn`).

The two commutator statements are the two halves of Bender 1970, 1.7(ii) (Thompson's lemma
applied to the action of `O_q(B)`, cf. the sibling files
`Submission/Work/BMAX/pCoreIn_commutator_layerIn.lean` and
`Submission/Work/BMAX/pCoreIn_commutator_pCoreIn.lean`).

The elementary bridges are `Work.BMAX.fittingPiIn_le_iSup_pCoreIn` (`F_π = ⨆_{q ∈ π} O_q`),
`Work.BMAX.pCoreIn_eq_bot_iff_mem_primesOf` (`O_q(A) = ⊥ ↔ q ∉ π(F(A))`) and
`Work.BMAX.fittingIn_isPGroup_of_unique_pCore` ("only one prime left" ⟹ `F(A)` is a `p`-group).
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.LayerCentralizesFitting
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.Bender17i_dedekind_basic
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le
import Submission.Work.BMAX.fittingPiIn_le_iSup_pCoreIn
import Submission.Work.BMAX.pCoreIn_commutator_layerIn
import Submission.Work.BMAX.pCoreIn_commutator_pCoreIn

set_option linter.style.haveILetI false

namespace Work.BMAX

open Subgroup

theorem Bender17i_of_fstar_le (G : Type) [Group G] [Finite G] (hG : IsSimpleGroup G)
    (A B : Subgroup G) (hA : IsCoatom A) (hB : B ≠ ⊤) (hR : Work.GW2.fstarIn A ≤ B)
    (hnot : ¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn A)) :
    Work.GW2.fittingPiIn (Work.GW2.primesOf (Work.GW2.fittingIn A)) B ≤ A := by
  set π : Set ℕ := Work.GW2.primesOf (Work.GW2.fittingIn A) with hπ
  -- `F_π(B)` is contained in the join of the `O_q(B)`, `q ∈ π`
  refine le_trans (Work.BMAX.fittingPiIn_le_iSup_pCoreIn B π ?_) ?_
  · intro q hq
    exact Nat.prime_of_mem_primeFactors hq
  · refine iSup_le fun q => iSup_le fun hqπ => ?_
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqπ
    by_cases hL : Work.GW2.layerIn A = ⊥
    · -- Fitting case: some prime `r ≠ q` divides `|F(A)|`
      have hex : ∃ r : ℕ, r.Prime ∧ r ≠ q ∧ r ∈ π := by
        by_contra hcon
        push Not at hcon
        have hbot : ∀ s : ℕ, s.Prime → s ≠ q → Work.GW2.pCoreIn s A = ⊥ :=
          fun s hs hsne => (pCoreIn_eq_bot_iff_mem_primesOf A hs).mpr (hcon s hs hsne)
        have hqg : IsPGroup q ↥(Work.GW2.fittingIn A) :=
          fittingIn_isPGroup_of_unique_pCore hq hbot
        have hfeq : Work.GW2.fstarIn A = Work.GW2.fittingIn A := by
          rw [Work.GW2.fstarIn_eq_sup, hL, sup_bot_eq]
        exact hnot ⟨q, hq, hfeq ▸ hqg⟩
      obtain ⟨r, hr, hqr, hrπ⟩ := hex
      have hrbot : Work.GW2.pCoreIn r A ≠ ⊥ :=
        fun hb => ((pCoreIn_eq_bot_iff_mem_primesOf A hr).mp hb) hrπ
      have hcomm := pCoreIn_commutator_pCoreIn G hG A B hA hB hR q r hq hqπ hr hrπ hqr.symm
      have hM_N : Work.GW2.pCoreIn q B ≤
          Subgroup.normalizer ((Work.GW2.pCoreIn r A : Subgroup G) : Set G) :=
        (Subgroup.le_normalizer_iff_commutator_le_right).mpr (hcomm ▸ bot_le)
      exact le_coatom_of_le_normalizer_of_ne_bot (hG := hG) (A := A)
        (N := Work.GW2.pCoreIn r A) (M := Work.GW2.pCoreIn q B)
        hA hrbot (Subgroup.map_subtype_le _) (le_normalizer_pCoreIn A r) hM_N
    · -- Layer case: `E(A) ≠ ⊥`
      have hcomm := pCoreIn_commutator_layerIn G hG A B hA hB hR q hq hqπ
      have hM_N : Work.GW2.pCoreIn q B ≤
          Subgroup.normalizer ((Work.GW2.layerIn A : Subgroup G) : Set G) :=
        (Subgroup.le_normalizer_iff_commutator_le_right).mpr (hcomm ▸ bot_le)
      exact le_coatom_of_le_normalizer_of_ne_bot (hG := hG) (A := A)
        (N := Work.GW2.layerIn A) (M := Work.GW2.pCoreIn q B)
        hA hL (Work.GW2.layerIn_le_self A) (le_normalizer_layerIn A) hM_N

end Work.BMAX
