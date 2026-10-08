import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.section3_prop2
import Submission.Work.NormalComplement.sec1_lemma3
import Submission.Work.NormalComplement.sec1_lemma3_structure
import Submission.Work.NormalComplement.sec2_lemma1
import Submission.Work.NormalComplement.appV_prod
import Submission.Work.NormalComplement.appI_five_b
import Submission.Work.NormalComplement.appI_five_c_prime
import Submission.Work.Hering.AppVII.appVII
import Submission.Work.NormalComplement.sec3_step1
import Submission.Work.NormalComplement.sec3_step2
import Submission.Work.NormalComplement.sec3_step3_v
import Submission.Work.NormalComplement.sec3_fitting_cyclic
import Submission.Work.NormalComplement.sec3_comm_le_fitting

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- **Peterfalvi I Ch. III §3 Proposition 1** (p.177): if `C_K(X) = 1` for every `1 ≠ X ⊴ V`, then
`E`, acting on `Inv H`, is a Frobenius group with kernel `K` and complement `E ⊓ V`
(`Design.FrobPacket H t W`).

Route (see `_design/Sec3.lean`, `sec3_prop1_step1`…`step3`, `sec1_lemma3`, `sec2_lemma1`): step 1
gives `C_V(K) = 1`, `(|K|,|F(V)|) = 1` and `K` an abelian subgroup with `D = ⟨K⟩ ⋊ V`
(App. I (5)(b)); step 2: every prime `p ∣ |E:E'|` divides `|F(E ⊓ V)|` (App. VII, `hVII`); step 3:
`F(E ⊓ V)` acts fixed-point-freely on `K` (maximality + `sec1_lemma3`).  Then `F(E ⊓ V)` is cyclic
(`appI_five_c_prime`), `(E ⊓ V)/F(E ⊓ V)` embeds in its automorphism group, and `K ⊆ E'`, `K ⊴ E`
(`sec2_lemma1`) give the `FrobPacket`. -/
theorem sec3_prop1 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hV : Work.NormalComplement.AppVProp)
    (hVII : Work.NormalComplement.Design.AppVIIProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G}
    (h : Work.NormalComplement.Design.Setup3 G H t W)
    (hN : Work.NormalComplement.Design.NoCentralizedNormal H t) :
    Work.NormalComplement.Design.FrobPacket H t W := by
  classical
  -- **Step 1**: `C_V(K) = 1`, `(|K|, |F(V)|) = 1`, and `K` a normal complement of `V` in `D`.
  obtain ⟨hCV, hCop, K, hKset, hKnc, hKab⟩ := sec3_step1 hFT h hN
  -- `|K| = |Inv H| ≥ 2` (Ch. I §2)
  have hK2 : 2 ≤ (Kset (twoPoint H t) t).ncard := by
    have hfour : HasFourGroup G := h.sit.1.1
    have h2 : 2 ≤ (involutions (H : Set G)).ncard :=
      Work.ThmF.Bender.cardInvGeTwo h.se hfour
    have hKn : (K : Set G).ncard = (involutions (H : Set G)).ncard :=
      Kset_ncard h.se h.invol h.notMem hKset
    rw [← hKset, hKn]
    exact h2
  -- **Step 2**: every prime `p ∣ |E : E'|` divides `|F(E ⊓ V)|`.
  have hst2 : ∀ p : ℕ, p.Prime →
      p ∣ (Design.Ecomm H t W).relIndex (Design.Egrp H t W) →
      p ∣ Nat.card ↥(Design.fitSub (Design.Egrp H t W ⊓ centD H t)) :=
    sec3_step2 hFT hVII h hN ⟨K, hKset, hKnc⟩ hCV
  -- **Step 3**: `F(E ⊓ V)` acts fixed-point-freely on `K`.
  have hFpf : Design.FpfOn (Design.fitSub (Design.Egrp H t W ⊓ centD H t))
      (Kset (twoPoint H t) t) :=
    sec3_step3_v hFT hC4 hMod hV hVII h hN hst2
  -- `F(E ⊓ V)` is cyclic, hence `E' ⊓ V ≤ F(E ⊓ V)`.
  have hcyc : IsCyclic ↥(Design.fitSub (Design.Egrp H t W ⊓ centD H t)) :=
    sec3_fitting_cyclic hFT h hK2 hFpf
  have hcommle : Design.Ecomm H t W ⊓ centD H t ≤
      Design.fitSub (Design.Egrp H t W ⊓ centD H t) :=
    sec3_comm_le_fitting hFT h K hKset hKnc hcyc
  -- `K ≤ E'` (§2 Lemma 1), hence `K ≤ E`
  have hKleE : K ≤ Design.Egrp H t W := by
    have h1 : K ≤ Design.Ecomm H t W := by
      intro x hx
      have hx' : x ∈ Kset (twoPoint H t) t := by rw [← hKset]; exact hx
      exact (sec2_lemma1 hFT h).1 hx'
    exact h1.trans (Subgroup.commutator_le_self (Design.Egrp H t W))
  -- `E = K (E ⊓ V)`
  have hEeq : Design.Egrp H t W = K ⊔ (Design.Egrp H t W ⊓ centD H t) := by
    refine le_antisymm ?_ ?_
    · intro e he
      have heW : e ∈ W := he.1
      have heD : e ∈ twoPoint H t := he.2
      -- every element of `D = K ⊔ V` is a product `v * k` with `v ∈ V`, `k ∈ K`
      have hdec : (twoPoint H t : Set G) = (centD H t : Set G) * (K : Set G) := by
        have hle : centD H t ≤ Subgroup.normalizer (K : Set G) :=
          le_trans inf_le_left hKnc.2.1
        have hcm := Subgroup.coe_mul_of_left_le_normalizer_right (centD H t) K hle
        rw [sup_comm, hKnc.2.2.2] at hcm
        exact hcm
      have hem : e ∈ (centD H t : Set G) * (K : Set G) := by
        rw [← hdec]; exact heD
      obtain ⟨v, hv, k, hk, hvk⟩ := Set.mem_mul.mp hem
      rw [← hvk]
      refine (K ⊔ (Design.Egrp H t W ⊓ centD H t)).mul_mem
        (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left hk)
      refine ⟨⟨?_, hv.1⟩, hv⟩
      have hvk' : v = e * k⁻¹ := by rw [← hvk]; group
      rw [hvk']
      exact W.mul_mem heW (W.inv_mem (hKleE hk).1)
    · exact sup_le hKleE inf_le_left
  -- every element of `(E ⊓ V)#` acts fixed-point-freely on `K`
  have hFpfEgrp : Design.FpfOn (Design.Egrp H t W ⊓ centD H t)
      (Kset (twoPoint H t) t) := by
    intro v hv hne k hk hconv
    by_cases hvE : v ∈ Design.Ecomm H t W
    · exact hFpf v (hcommle ⟨hvE, hv.2⟩) hne k hk hconv
    · exact (sec2_lemma1 hFT h).2.2 v hv hvE k hk hconv
  refine ⟨K, hKset, ?_, ?_, ?_, ?_⟩
  · -- `K` is `E`-invariant
    intro w hw k hk
    have hw' : w ∈ Subgroup.normalizer (K : Set G) := hKnc.2.1 hw.2
    rw [Subgroup.mem_normalizer_iff] at hw'
    exact (hw' k).mp hk
  · -- `K ⊓ (E ⊓ V) = ⊥`
    exact le_bot_iff.mp (le_trans (inf_le_inf (le_refl K) inf_le_right) hKnc.2.2.1.le)
  · -- `K (E ⊓ V) = E`
    have h1 : (W ⊓ centD H t : Subgroup G) = Design.Egrp H t W ⊓ centD H t := by
      ext x
      simp only [Design.Egrp, Submission.Blueprint.centD, Subgroup.mem_inf]
      tauto
    rw [h1, ← hEeq]
  · -- `(E ⊓ V)#` acts fixed-point-freely on `K`
    intro k hk hk1 v hv hv1 hfix
    have hkKset : k ∈ Kset (twoPoint H t) t := by rw [← hKset]; exact hk
    have hvE : v ∈ Design.Egrp H t W ⊓ centD H t := ⟨⟨hv.1, hv.2.1⟩, hv.2⟩
    exact hk1 (hFpfEgrp v hvE hv1 k hkKset hfix)

end Work.NormalComplement
