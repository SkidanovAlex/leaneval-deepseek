/-
# BMAX — Bender 1970, 1.7(iii), with no Dedekind hypothesis (GW design 18, §C)

`Work.BMAX.Core18Bender17iiiCond : Work.GW2.Bender17iiiProp` is the same proof as
`Bender17iiiCond_of_layer`, except that the `LayerDedekindProp` input is gone: the two
"mixed case" steps that used it are replaced by
`Work.BMAX.layerIn_eq_bot_of_mixed` (`Core18Aux.lean`), which shows that the mixed case —
`F*(A)` not a `p`-group while `F*(B)` is a `q`-group — is *empty*.  Hence `Lemma23Prop` no
longer needs `Work.GW2.LayerDedekindProp`.

* `Work.BMAX.layerIn_eq_bot_of_mixed T A B … (hfstB_of_hnotA hnotA) hEA hL` contradicts
  `hL : layerIn A ≠ ⊥` and closes the goal by `absurd`; symmetrically for the other side.
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.BRel_witness_facts
import Submission.Work.BMAX.Bender17i
import Submission.Work.BMAX.Core18Aux
import Submission.Work.BMAX.FstarSamePrime
import Submission.Work.BMAX.GWPiEq

namespace Work.BMAX

open Subgroup

/-- **The `F*`-half of `A ⇝ B ⇒ F*(A) ≤ B`.**  If `F(A) ≤ N_G(X)` for a witness `X ≤ F(A)` of
`A ⇝ B` (with `E(A) ≤ N_G(X)` supplied by `BRel_witness_facts`), then `F*(A) ≤ B`. -/
theorem fstarIn_le_of_fittingIn_le_normalizer {G : Type} [Group G] {A B X : Subgroup G}
    (hF : Work.GW2.fittingIn A ≤ Subgroup.normalizer (X : Set G))
    (hE : Work.GW2.layerIn A ≤ Subgroup.normalizer (X : Set G))
    (hXB : Subgroup.normalizer (X : Set G) ⊓ Work.GW2.fstarIn A ≤ B) :
    Work.GW2.fstarIn A ≤ B := by
  refine le_trans ?_ hXB
  refine le_inf ?_ le_rfl
  rw [Work.GW2.fstarIn_eq_sup]
  exact sup_le hF hE

/-- `F(K) ≤ F_π(K)` when every prime dividing `|F(K)|` lies in `π`. -/
theorem fittingIn_le_fittingPiIn_of_primeFactors_subset {G : Type} [Group G] [Finite G]
    {K : Subgroup G} {π : Set ℕ}
    (h : ∀ q ∈ (Nat.card ↥(Work.GW2.fitting K)).primeFactors, q ∈ π) :
    Work.GW2.fittingIn K ≤ Work.GW2.fittingPiIn π K := by
  rw [fittingPiIn_eq_fittingIn_of_primeFactors_subset (K := K) h]

/-- **The assembly, with the mixed case closed by `layerIn_eq_bot_of_mixed`** (design 18 §C); no Dedekind input.  `hLayer` below is Bender
1970 §1.6/§1.7 in the form: `A` coatomic, `F(A)` a `p`-group, `E(A) ≠ 1` ⟹ `F(A)` Dedekind.
Everything else is derived from the workspace's `sorry`-free content (`Work.BMAX.Bender17i`,
`Work.BMAX.GWPiEq`, `Work.BMAX.BRel_witness_facts`, `LayerCentralizesFitting`). -/
theorem Core18Bender17iiiCond : Work.GW2.Bender17iiiProp := by
  intro T G _ _ hG A B hAsyl hDA hBsyl hDB hcA hBne hrelAB hcB hrelBA hside
  by_cases hAB : A = B
  · subst hAB
    exact ⟨Work.GW2.fstarIn_le_self A, Work.GW2.fstarIn_le_self A⟩
  · -- `A ≠ B`, so `¬ B ≤ A` and `¬ A ≤ B` (both are coatomic).
    have hBleA : ¬ B ≤ A := by
      intro hBA
      rcases lt_or_eq_of_le hBA with hlt | heq
      · exact hcA.ne_top (hcB.lt_iff.mp hlt)
      · exact hAB heq.symm
    have hAleB : ¬ A ≤ B := by
      intro hAB'
      rcases lt_or_eq_of_le hAB' with hlt | heq
      · exact hcB.ne_top (hcA.lt_iff.mp hlt)
      · exact hAB heq
    -- the two witnesses and the layers
    obtain ⟨XA, hXAF, hXBA, hSlA, -, -⟩ := Work.BMAX.BRel_witness_facts A B hrelAB
    obtain ⟨XB, hXBF, hXBB, hSlB, -, -⟩ := Work.BMAX.BRel_witness_facts B A hrelBA
    have hEA : Work.GW2.layerIn A ≤ B :=
      le_trans (le_inf hSlA (Work.GW2.layerIn_le_fstarIn A)) hXBA
    have hEB : Work.GW2.layerIn B ≤ A :=
      le_trans (le_inf hSlB (Work.GW2.layerIn_le_fstarIn B)) hXBB
    have hpi := GWPiEq T G hG A B hAsyl hDA hBsyl hDB hcA hBne hrelAB hcB hrelBA
    -- ### Bender 1970, 1.7(i): `F_π(B) ≤ A` under `hnot_A`, whence `F*(B) ≤ A`.
    have hfstB_of_hnotA :
        (¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn A)) →
          Work.GW2.fstarIn B ≤ A := fun hnotA => by
      have hI := Bender17i G hG A B hcA hBne hrelAB hnotA
      rw [Work.GW2.fstarIn_eq_sup]
      refine sup_le ?_ hEB
      refine le_trans ?_ hI
      refine fittingIn_le_fittingPiIn_of_primeFactors_subset ?_
      intro r hr
      have hr' : r ∈ Work.GW2.primesOf (Work.GW2.fittingIn B) := by
        rw [Work.GW2.mem_primesOf, Work.GW2.fittingIn,
          Subgroup.card_map_of_injective B.subtype_injective]
        exact hr
      rwa [hpi]
    -- symmetrically `F*(A) ≤ B` under `hnot_B`
    have hfstA_of_hnotB :
        (¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B)) →
          Work.GW2.fstarIn A ≤ B := fun hnotB => by
      have hI := Bender17i G hG B A hcB hcA.ne_top hrelBA hnotB
      rw [Work.GW2.fstarIn_eq_sup]
      refine sup_le ?_ hEA
      refine le_trans ?_ hI
      refine fittingIn_le_fittingPiIn_of_primeFactors_subset ?_
      intro r hr
      have hr' : r ∈ Work.GW2.primesOf (Work.GW2.fittingIn A) := by
        rw [Work.GW2.mem_primesOf, Work.GW2.fittingIn,
          Subgroup.card_map_of_injective A.subtype_injective]
        exact hr
      rwa [← hpi]
    -- ### The mixed case: `F*(A)` is not a `p`-group and `F*(B)` *is* a `q`-group.
    -- Then `F(A)` is a `q`-group, the layer case applies, and `F*(A) ≤ B`.
    have hfstA_of_mixed :
        (¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn A)) →
          (¬ ¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B)) →
          Work.GW2.fstarIn A ≤ B := fun hnotA hnnotB => by
      by_cases hFA : Work.GW2.fittingIn A = ⊥
      · rw [Work.GW2.fstarIn_eq_sup, hFA, bot_sup_eq]
        exact hEA
      · obtain ⟨q, hq, hPqB⟩ := not_not.mp hnnotB
        have hπB : Work.GW2.primesOf (Work.GW2.fittingIn B) ⊆ {q} := by
          intro r hr
          rw [Set.mem_singleton_iff]
          rw [Work.GW2.mem_primesOf] at hr
          have hcard : Nat.card ↥(Work.GW2.fittingIn B) = Nat.card ↥(Work.GW2.fitting B) :=
            Subgroup.card_map_of_injective B.subtype_injective
          exact primeFactors_fitting_subset_singleton hq hPqB r (hcard ▸ hr)
        have hπA : Work.GW2.primesOf (Work.GW2.fittingIn A) ⊆ {q} := by
          intro r hr
          rw [hpi] at hr
          exact hπB hr
        have huniq : ∀ r : ℕ, r.Prime → r ≠ q → Work.GW2.pCoreIn r A = ⊥ := by
          intro r hr hrq
          rw [Work.BMAX.pCoreIn_eq_bot_iff_mem_primesOf A hr]
          intro hmem
          exact hrq (Set.mem_singleton_iff.mp (hπA hmem))
        have hPg : IsPGroup q ↥(Work.GW2.fittingIn A) :=
          Work.BMAX.fittingIn_isPGroup_of_unique_pCore hq huniq
        have hL : Work.GW2.layerIn A ≠ ⊥ := by
          intro hbot
          refine hnotA ⟨q, hq, ?_⟩
          rw [Work.GW2.fstarIn_eq_sup, hbot, sup_bot_eq]
          exact hPg
        exact absurd (layerIn_eq_bot_of_mixed T A B hBsyl hDB q hq hPqB hEA
          (hfstB_of_hnotA hnotA)) hL
    -- symmetrically for the other mixed case
    have hfstB_of_mixed :
        (¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B)) →
          (¬ ¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn A)) →
          Work.GW2.fstarIn B ≤ A := fun hnotB hnnotA => by
      by_cases hFB : Work.GW2.fittingIn B = ⊥
      · rw [Work.GW2.fstarIn_eq_sup, hFB, bot_sup_eq]
        exact hEB
      · obtain ⟨q, hq, hPqA⟩ := not_not.mp hnnotA
        have hπA : Work.GW2.primesOf (Work.GW2.fittingIn A) ⊆ {q} := by
          intro r hr
          rw [Set.mem_singleton_iff]
          rw [Work.GW2.mem_primesOf] at hr
          have hcard : Nat.card ↥(Work.GW2.fittingIn A) = Nat.card ↥(Work.GW2.fitting A) :=
            Subgroup.card_map_of_injective A.subtype_injective
          exact primeFactors_fitting_subset_singleton hq hPqA r (hcard ▸ hr)
        have hπB : Work.GW2.primesOf (Work.GW2.fittingIn B) ⊆ {q} := by
          intro r hr
          rw [← hpi] at hr
          exact hπA hr
        have huniq : ∀ r : ℕ, r.Prime → r ≠ q → Work.GW2.pCoreIn r B = ⊥ := by
          intro r hr hrq
          rw [Work.BMAX.pCoreIn_eq_bot_iff_mem_primesOf B hr]
          intro hmem
          exact hrq (Set.mem_singleton_iff.mp (hπB hmem))
        have hPg : IsPGroup q ↥(Work.GW2.fittingIn B) :=
          Work.BMAX.fittingIn_isPGroup_of_unique_pCore hq huniq
        have hL : Work.GW2.layerIn B ≠ ⊥ := by
          intro hbot
          refine hnotB ⟨q, hq, ?_⟩
          rw [Work.GW2.fstarIn_eq_sup, hbot, sup_bot_eq]
          exact hPg
        exact absurd (layerIn_eq_bot_of_mixed T B A hAsyl hDA q hq hPqA hEB
          (hfstA_of_hnotB hnotB)) hL
    -- ### Assembly
    rcases hside with hnotA | hnotB
    · refine ⟨?_, hfstB_of_hnotA hnotA⟩
      by_cases hnotB : ¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B)
      · exact hfstA_of_hnotB hnotB
      · exact hfstA_of_mixed hnotA hnotB
    · refine ⟨hfstA_of_hnotB hnotB, ?_⟩
      by_cases hnotA : ¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn A)
      · exact hfstB_of_hnotA hnotA
      · exact hfstB_of_mixed hnotB hnotA

end Work.BMAX
