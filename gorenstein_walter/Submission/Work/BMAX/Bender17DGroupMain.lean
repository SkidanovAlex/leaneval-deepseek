/-
# BMAX — Bender 1970, 1.7(i)+(ii) in the `D`-group form of Bender 1981, Lemma 2.3

This file assembles the two clauses of `Work.GW2.Bender17MainProp`:

* (i) `F_π(B) ≤ A` unless `F*(A)` is a `p`-group, and
* (ii) `F_{π'}(B) ∩ A = ⊥`, where `π = π(F(A))`,

for `A` a coatomic `D`-subgroup of a finite simple group `G` and `B ≠ ⊤` with `A ⇝ B`
(`Work.GW2.BRel`).

The pieces are the auxiliary files of the area:

* `BRel_witness_facts` — the witness `X ≤ F(A)` with `N_G(X) ∩ F*(A) ≤ B`, together with
  `E(A) ≤ N_G(X)` and `Z(F(A)) ≤ N_G(X)`;
* `pCoreIn_eq_bot_iff_not_mem_primesOf` — `O_q(A) = ⊥ ↔ q ∉ π(F(A))`;
* `commutator_pCoreIn_inf_pResidualIn_fstarIn` — Bender's first paragraph of 1.7:
  `[O_q(B) ∩ A, O^q(F*(A))] = ⊥` for `q ∉ π(F(A))`;
* `centralizer_pResidualIn_witness_le` and `commutator_pCoreIn_pResidualIn_witness` —
  Bender's second paragraph: `[O_p(B), O^p(S)] = ⊥` and `C_B(O^p(S)) ≤ A` for `p ∈ π(F(A))`;
* `fstarIn_le_pResidualIn_of_notMem_primesOf`, `inf_fittingIn_le_pCoreIn_of_le_pCoreIn`,
  `eq_bot_of_le_fstarIn_of_inf_fittingIn_eq_bot` — the elementary structural steps;
* `Work.BMAX.fittingPiIn_compl_inf_eq_bot` (`Bender17ii`) — the glue from the prime-by-prime
  statement to `F_{π'}(B) ∩ A = ⊥`;
* `Work.BMAX.PiCoreJoin` — `F_π(B) = ⨆_{q ∈ π} O_q(B)`.
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.BRel_witness_facts
import Submission.Work.BMAX.pCoreIn_eq_bot_iff_not_mem_primesOf
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le
import Submission.Work.BMAX.commutator_pCoreIn_inf_pResidualIn_fstarIn
import Submission.Work.BMAX.commutator_pCoreIn_pResidualIn_witness
import Submission.Work.BMAX.CommutatorWitnessFinal
import Submission.Work.BMAX.eq_bot_of_le_fstarIn_of_inf_fittingIn_eq_bot
import Submission.Work.BMAX.fstarIn_le_pResidualIn_of_notMem_primesOf
import Submission.Work.BMAX.inf_fittingIn_le_pCoreIn_of_le_pCoreIn
import Submission.Work.BMAX.fittingPiIn_compl_inf_eq_bot
import Submission.Work.BMAX.fittingPiIn_le_iSup_pCoreIn

set_option linter.style.haveILetI false

open scoped MatrixGroups

namespace Work.BMAX

open Subgroup

/-! ## 1. `C_A(F*(A)) ≤ F*(A)` for a `D`-subgroup, from the toolkit -/

/-- `FStarProp` of the toolkit, transported to the ambient group: the centralizer in `A` of
`F*(A)` lies in `F*(A)`. -/
theorem centralizer_fstarIn_inf_le_17 {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (A : Subgroup G) (hdih : Work.GW2.DihOrCycSylow ↥A) (hD : Work.GW2.IsDGroup ↥A) :
    Subgroup.centralizer (Work.GW2.fstarIn A : Set G) ⊓ A ≤ Work.GW2.fstarIn A := by
  classical
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have h := T.fstar ↥A T.ft hdih hD
  refine Subgroup.mem_map.mpr ⟨⟨x, hx2⟩, h ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp hx1) (y : G) ⟨y, hy, rfl⟩

/-! ## 2. `O^p(F*(A)) ≠ ⊥` when `F*(A)` is not a `p`-group -/

/-- If `F*(A)` is not a `p`-group then `O^p(F*(A)) ≠ ⊥`: `O^p(H) = ⊥` would force `H` to be a
`p`-group. -/
theorem pResidualIn_ne_bot_of_fstarIn_not_isPGroup {G : Type} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hnot : ¬ ∃ q : ℕ, q.Prime ∧ IsPGroup q ↥(Work.GW2.fstarIn A)) :
    pResidualIn p (Work.GW2.fstarIn A) ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hbot
  exact hnot ⟨p, hp, (pResidualIn_eq_bot_iff_isPGroup (p := p) (Work.GW2.fstarIn A)).mp hbot⟩

/-! ## 3. Clause (i), prime by prime -/

/-- **Bender 1981, Lemma 2.3(i), prime by prime.**  If `F*(A)` is not a `p`-group and
`p ∈ π(F(A))`, then `O_p(B) ≤ A`.

By Bender's second paragraph of 1.7, `O_p(B) ≤ C_B(O^p(S))` and `C_B(O^p(S)) ≤ A`, where
`S = N_G(X) ∩ F*(A) ≤ B` is the witness of `A ⇝ B`. -/
theorem pCoreIn_le_coatom_of_not_isPGroup {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (hG : IsSimpleGroup G)
    (A B X : Subgroup G) (hA : IsCoatom A) (hB : B ≠ ⊤)
    (hA_dih : Work.GW2.DihOrCycSylow ↥A) (hA_D : Work.GW2.IsDGroup ↥A)
    (hB_dih : Work.GW2.DihOrCycSylow ↥B) (hB_D : Work.GW2.IsDGroup ↥B)
    (hX : X ≤ Work.GW2.fittingIn A)
    (hSB : Subgroup.normalizer (X : Set G) ⊓ Work.GW2.fstarIn A ≤ B)
    (hSl : Work.GW2.layerIn A ≤ Subgroup.normalizer (X : Set G))
    (hZs : Work.GW2.zcenterIn (Work.GW2.fittingIn A) ≤ Subgroup.normalizer (X : Set G))
    (hnot : ¬ ∃ q : ℕ, q.Prime ∧ IsPGroup q ↥(Work.GW2.fstarIn A))
    (q : ℕ) (hq : q.Prime) (hqpi : q ∈ Work.GW2.primesOf (Work.GW2.fittingIn A)) :
    Work.GW2.pCoreIn q B ≤ A := by
  classical
  set S : Subgroup G := Subgroup.normalizer (X : Set G) ⊓ Work.GW2.fstarIn A with hS
  have hSf : S ≤ Work.GW2.fstarIn A := inf_le_right
  have hSl' : Work.GW2.layerIn A ≤ S := le_inf hSl (Work.GW2.layerIn_le_fstarIn A)
  have hZs' : Work.GW2.zcenterIn (Work.GW2.fittingIn A) ≤ S :=
    le_inf hZs
      (le_trans (Work.GW2.zcenterIn_le (Work.GW2.fittingIn A))
        (Work.GW2.fittingIn_le_fstarIn A))
  have hne : pResidualIn q (Work.GW2.fstarIn A) ≠ ⊥ :=
    pResidualIn_ne_bot_of_fstarIn_not_isPGroup A q hq hnot
  have hgam := CommutatorWitnessFinal hG A B S hA hB hA_dih hA_D hB_dih hB_D
    hSB hSf hSl' hZs' q hq hqpi
  have hdel := centralizer_pResidualIn_witness_le hG A B S hA hB hA_D hSB hSf hSl' hZs'
    q hq hqpi hne
  refine le_trans (le_inf ?_ ?_) hdel
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hgam
  · intro x hx
    exact Subgroup.map_subtype_le _ hx

/-! ## 4. Clause (ii), prime by prime -/

/-- **Bender 1981, Lemma 2.3(ii), prime by prime.**  For `q ∉ π(F(A))` the `q`-core of `B`
meets `A` trivially.

Indeed `Q := O_q(B) ∩ A` centralizes `O^q(F*(A)) ⊇ F*(A)` (Bender's first paragraph), hence
`Q ≤ C_A(F*(A)) ≤ F*(A)`; and `Q ∩ F(A) ⊆ O_q(A) = ⊥`, so that the structural lemma
`eq_bot_of_le_fstarIn_of_inf_fittingIn_eq_bot` gives `Q = ⊥`. -/
theorem pCoreIn_inf_coatom_eq_bot {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (hG : IsSimpleGroup G)
    (A B X : Subgroup G) (hA : IsCoatom A) (hB : B ≠ ⊤)
    (hA_dih : Work.GW2.DihOrCycSylow ↥A) (hA_D : Work.GW2.IsDGroup ↥A)
    (hX : X ≤ Work.GW2.fittingIn A)
    (hSB : Subgroup.normalizer (X : Set G) ⊓ Work.GW2.fstarIn A ≤ B)
    (hSl : Work.GW2.layerIn A ≤ Subgroup.normalizer (X : Set G))
    (q : ℕ) (hq : q.Prime) (hqpi : q ∉ Work.GW2.primesOf (Work.GW2.fittingIn A)) :
    Work.GW2.pCoreIn q B ⊓ A = ⊥ := by
  classical
  have hmain := commutator_pCoreIn_inf_pResidualIn_fstarIn hG A B X hA hB hA_D hX hSB hSl
    q hq hqpi
  have hfstar_le := fstarIn_le_pResidualIn_of_notMem_primesOf A q hq hqpi
  have hQc : Work.GW2.pCoreIn q B ⊓ A ≤
      Subgroup.centralizer (Work.GW2.fstarIn A : Set G) :=
    le_trans ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hmain)
      (Subgroup.centralizer_le hfstar_le)
  have hQf : Work.GW2.pCoreIn q B ⊓ A ≤ Work.GW2.fstarIn A :=
    le_trans (le_inf hQc inf_le_right)
      (centralizer_fstarIn_inf_le_17 T A hA_dih hA_D)
  have hQF : (Work.GW2.pCoreIn q B ⊓ A) ⊓ Work.GW2.fittingIn A = ⊥ := by
    have h1 : (Work.GW2.pCoreIn q B ⊓ A) ⊓ Work.GW2.fittingIn A ≤
        Work.GW2.pCoreIn q A :=
      inf_fittingIn_le_pCoreIn_of_le_pCoreIn A B (Work.GW2.pCoreIn q B ⊓ A) q hq
        inf_le_left inf_le_right
    have h2 : Work.GW2.pCoreIn q A = ⊥ :=
      (pCoreIn_eq_bot_iff_not_mem_primesOf A q hq).mpr hqpi
    exact le_bot_iff.mp (h2 ▸ h1)
  exact eq_bot_of_le_fstarIn_of_inf_fittingIn_eq_bot A (Work.GW2.pCoreIn q B ⊓ A) hQf hQF hQc

/-! ## 5. The target -/

theorem Bender17DGroupMain : Work.GW2.Bender17MainProp := by
  intro T G _ _ hG A B hA_dih hA_D hB_dih hB_D hA hB hrel
  obtain ⟨X, hX, hSB, hSl, hZs, -⟩ := BRel_witness_facts (A := A) (B := B) hrel
  refine ⟨?_, ?_⟩
  · -- clause (i)
    intro hnot
    have hpi : ∀ q ∈ Work.GW2.primesOf (Work.GW2.fittingIn A), q.Prime := fun q hq =>
      Nat.prime_of_mem_primeFactors hq
    refine le_trans (fittingPiIn_le_iSup_pCoreIn B (Work.GW2.primesOf (Work.GW2.fittingIn A)) hpi) ?_
    refine iSup_le fun q => iSup_le fun hqpi => ?_
    exact pCoreIn_le_coatom_of_not_isPGroup T hG A B X hA hB hA_dih hA_D hB_dih hB_D hX hSB
      hSl hZs hnot q (hpi q hqpi) hqpi
  · -- clause (ii)
    exact fittingPiIn_compl_inf_eq_bot A B fun q hq hqpi =>
      pCoreIn_inf_coatom_eq_bot T hG A B X hA hB hA_dih hA_D hX hSB hSl q hq hqpi

end Work.BMAX
