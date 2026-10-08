import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.OutsideS0OrderTwo
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.Dihedral.Defs
import Submission.Work.CORE3.ncard_involutionSet_eq_sum
import Submission.Work.CORE3.nat_card_involutions_dihedral_four
import Submission.Work.CORE3.pCoreIn_two_Hhat_le_S_and_centralizer
import Submission.Work.CORE3.ncard_invSet_eq_one_of_le_centralizer

set_option linter.style.haveILetI false

namespace Work.CORE3

open Work.GW2

/-- `O(K)`, transported into the ambient group, is a normal subgroup of `K`
(`(oddCoreIn K).subgroupOf K = oddCore ↥K`). -/
theorem subgroupOf_oddCoreIn_normal_aux {G : Type} [Group G] (K : Subgroup G) :
    ((oddCoreIn K).subgroupOf K).Normal := by
  have hinj : Function.Injective (fun L : Subgroup ↥K => L.map K.subtype) :=
    Subgroup.map_injective (f := K.subtype) Subtype.val_injective
  have heq : (oddCoreIn K).subgroupOf K = oddCore ↥K := by
    apply hinj
    calc ((oddCoreIn K).subgroupOf K).map K.subtype
        = oddCoreIn K ⊓ K := Subgroup.subgroupOf_map_subtype _ _
      _ = oddCoreIn K := inf_eq_left.mpr (Subgroup.map_subtype_le (oddCore ↥K))
      _ = (oddCore ↥K).map K.subtype := rfl
  rw [heq]
  infer_instance

/-- The involutions of a Klein four-group `V ≤ S`, counted inside the involutions of `S`:
`V` has order `4` and exponent `2`, so it contributes exactly `3` involutions. -/
theorem nat_card_involutions_in_fourgroup_aux {G : Type} [Group G] [Finite G] (S V : Subgroup G)
    (hVS : V ≤ S) (hcard : Nat.card V = 4) (hsq : ∀ v ∈ V, v ^ 2 = 1) :
    Nat.card {s : {s : ↥S // orderOf (s : G) = 2} // (s : G) ∈ V} = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcoe : ({v : G | v ∈ V ∧ v ≠ 1} : Set G) = (V : Set G) \ {1} := by
    ext v
    simp [Set.mem_sdiff, Set.mem_singleton_iff]
  have hsetcard : ({v : G | v ∈ V ∧ v ≠ 1} : Set G).ncard = 3 := by
    rw [hcoe, Set.ncard_sdiff (show ({1} : Set G) ⊆ (V : Set G) from fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact V.one_mem),
      Set.ncard_singleton]
    have hV : (V : Set G).ncard = Nat.card V := (Nat.card_coe_set_eq (V : Set G)).symm
    rw [hV, hcard]
  rw [show Nat.card {s : {s : ↥S // orderOf (s : G) = 2} // (s : G) ∈ V} =
      ({s : {s : ↥S // orderOf (s : G) = 2} | (s : G) ∈ V} : Set _).ncard from
    Nat.card_coe_set_eq _,
    Set.ncard_congr (t := {v : G | v ∈ V ∧ v ≠ 1}) (fun (a : {s : ↥S // orderOf (s : G) = 2}) _ =>
      (a.1 : G)) ?_ ?_ ?_]
  · exact hsetcard
  · -- the value lies in the target set
    intro a ha
    refine ⟨ha, ?_⟩
    intro h
    have h2 := a.2
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · -- injectivity
    intro a b _ _ hab
    exact Subtype.ext (Subtype.ext hab)
  · -- surjectivity
    intro v hv
    refine ⟨⟨⟨v, hVS hv.1⟩, orderOf_eq_prime (hsq v hv.1) hv.2⟩, hv.1, rfl⟩

/-- **Bender 1981 §3, p. 223, first count**: in the subcase `V = O₂(Ĥ)` of type `(2,2)`, the
centralizer `H = C_G(t) = U ⊔ S` has exactly `3 + 2|K|` involutions, where `K = I_U(s)` is the
Hall subgroup of `F(U)` associated with the involutions `s ∈ Ĥ − V`.

The argument: every involution of `H` has `S`-component an involution `s ∈ S` (the `U`-component
is inverted by `s`), giving the identity `|I(H)| = Σ_{s ∈ S, s²=1} |I_U(s)|` of
`Work.CORE3.ncard_involutionSet_eq_sum`.  Since `|S| = 8` and `S` is dihedral, `S` has exactly
`5` involutions: the central `t` and `4` reflections.  The four-group `V = O₂(Ĥ)` is contained in
`S` and is the unique Klein subgroup of `S`, so exactly `2` of the `4` reflections lie in `V`;
for those two `I_U(s) = {1}` (`V` centralizes `U`), while the remaining two reflections lie in
`Ĥ − V` and therefore satisfy `I_U(s) = K` by definition of `K`.  Hence the sum is
`3·1 + 2·|K| = 3 + 2|K|`. -/
theorem InvCountH {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) :
    (Work.GW2.involutionSet B.H).ncard = 3 + 2 * Nat.card D.K := by
  classical
  -- ## 0. Structural facts about `H = U ⊔ S = C_G(t)`
  have hUS : B.U ⊔ (B.S : Subgroup G) = B.H := Work.CORE3.H_eq_U_sup_S G I.T hBc B
  have hdisj : B.U ⊓ (B.S : Subgroup G) = ⊥ := Work.CORE2A.inf_U_S_eq_bot B
  have hUnorm : (B.U.subgroupOf B.H).Normal := subgroupOf_oddCoreIn_normal_aux B.H
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  haveI : Fintype ↥(B.S : Subgroup G) := Fintype.ofFinite _
  -- ## 1. `S ≅ D₈` and the count of involutions of `S`
  obtain ⟨n, hn2, ⟨e⟩⟩ := SylowDihedral G hBc B
  have hn4 : n = 4 := by
    have hcard : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have h8 := D.S8
    rw [hcard] at h8
    omega
  subst hn4
  have hα5 : Nat.card {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} = 5 :=
    (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun a => by
      simp [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]))).trans
      nat_card_involutions_dihedral_four
  -- ## 2. Facts about `V = O₂(Ĥ)`
  have hVleS : pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) :=
    (pCoreIn_two_Hhat_le_S_and_centralizer B).1
  have hVcent : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) :=
    (pCoreIn_two_Hhat_le_S_and_centralizer B).2
  have hαV : Nat.card {s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} //
      (s : G) ∈ pCoreIn 2 B.Hhat} = 3 :=
    nat_card_involutions_in_fourgroup_aux (B.S : Subgroup G) (pCoreIn 2 B.Hhat) hVleS
      D.four.1 D.four.2
  -- ## 3. The counting identity of `ncard_involutionSet_eq_sum`
  have hcount := ncard_involutionSet_eq_sum (H := B.H) (U := B.U) (S := (B.S : Subgroup G))
    (le_sup_left.trans (le_of_eq hUS)) (le_sup_right.trans (le_of_eq hUS))
    hUnorm hUS hdisj hUodd
  rw [hcount]
  -- ## 4. Evaluate the sum: `I_U(s)` is trivial on `S ∩ V` and equals `K` off `V`.
  have hstep : ∀ s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2},
      (invSet B.U (s : G)).ncard =
        if (s : G) ∈ pCoreIn 2 B.Hhat then 1 else Nat.card D.K := by
    intro s
    by_cases hmem : (s : G) ∈ pCoreIn 2 B.Hhat
    · rw [if_pos hmem]
      exact ncard_invSet_eq_one_of_le_centralizer B.U (s : G) (hVcent hmem) hUodd
    · rw [if_neg hmem]
      have hmemHhat : (s : G) ∈ B.Hhat :=
        Work.CORE2A.bSetup_S_le_Hhat B (by simpa using s.1.2)
      have hK : (D.K : Set G) = invSet B.U (s : G) := D.inv (s : G) hmemHhat s.2 hmem
      rw [← hK]
      exact (Nat.card_coe_set_eq (D.K : Set G)).symm
  rw [Finset.sum_congr rfl (fun s _ => hstep s)]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ :
      Finset {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2})
      (fun s => (s : G) ∈ pCoreIn 2 B.Hhat)
      (fun s => if (s : G) ∈ pCoreIn 2 B.Hhat then (1 : ℕ) else Nat.card D.K)]
  -- ## 5. The cardinalities of the two filtered index sets
  have hcardP : (Finset.univ.filter
      (fun s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} =>
        (s : G) ∈ pCoreIn 2 B.Hhat)).card = 3 := by
    have h : (Finset.univ.filter
        (fun s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} =>
          (s : G) ∈ pCoreIn 2 B.Hhat)).card =
        Fintype.card {s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} //
          (s : G) ∈ pCoreIn 2 B.Hhat} :=
      (Fintype.card_of_subtype _ (fun x => by simp)).symm
    rw [h, Fintype.card_eq_nat_card]
    exact hαV
  have hcardNotP : (Finset.univ.filter
      (fun s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} =>
        ¬ (s : G) ∈ pCoreIn 2 B.Hhat)).card = 2 := by
    have h : (Finset.univ.filter
        (fun s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} =>
          ¬ (s : G) ∈ pCoreIn 2 B.Hhat)).card =
        Fintype.card {s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} //
          ¬ (s : G) ∈ pCoreIn 2 B.Hhat} :=
      (Fintype.card_of_subtype _ (fun x => by simp)).symm
    have hcompl := Fintype.card_subtype_compl
      (fun s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} =>
        (s : G) ∈ pCoreIn 2 B.Hhat)
    rw [h, hcompl, Fintype.card_eq_nat_card, hα5, Fintype.card_eq_nat_card, hαV]
  -- ## 6. Sum up
  have h1 : (Finset.univ.filter
      (fun s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} =>
        (s : G) ∈ pCoreIn 2 B.Hhat)).sum
      (fun s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} =>
        if (s : G) ∈ pCoreIn 2 B.Hhat then (1 : ℕ) else Nat.card D.K) = 3 := by
    rw [Finset.sum_congr rfl (fun s hs => if_pos (Finset.mem_filter.mp hs).2)]
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    exact hcardP
  have h2 : (Finset.univ.filter
      (fun s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} =>
        ¬ (s : G) ∈ pCoreIn 2 B.Hhat)).sum
      (fun s : {s : ↥(B.S : Subgroup G) // orderOf (s : G) = 2} =>
        if (s : G) ∈ pCoreIn 2 B.Hhat then (1 : ℕ) else Nat.card D.K)
      = 2 * Nat.card D.K := by
    rw [Finset.sum_congr rfl (fun s hs => if_neg (Finset.mem_filter.mp hs).2)]
    rw [Finset.sum_const, smul_eq_mul, hcardNotP]
  rw [h1, h2]

end Work.CORE3
