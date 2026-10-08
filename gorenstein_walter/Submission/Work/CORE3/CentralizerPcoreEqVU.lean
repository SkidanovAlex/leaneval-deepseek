import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.PcoreInBasic
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.BCountSum
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.LeCentralizerOfCoprimeNormal
import Submission.Work.CORE3.RelIndexCentralizerFourGroup
import Submission.Work.CORE3.CommuteOfCentralizingFourGroup
import Submission.Work.CORE3.DihedralFourNotCommutative

namespace Work.CORE3

open Subgroup

/-- Bender 1981 §3, p. 223, the subcase `V = O₂(Ĥ)` of type (2,2): `C_Ĥ(O₂(Ĥ)) = O₂(Ĥ)·O(Ĥ)`,
i.e. the centralizer in `Ĥ` of the four-group `V = O₂(Ĥ)` is the normal subgroup `V ⊔ U`
(`U = O(H) = O(Ĥ)`).

Mathematical route.  Write `V = O₂(Ĥ)`, `U = O(H)`, `VU = V ⊔ U`, `C = C_G(V) ⊓ Ĥ`.

* `Thm 2.6` (`I.h26`) gives `O(Ĥ) = U`, `S ⊓ C_G(U) = V` (so `t ∈ V` and `V ≤ S`) and, since
  `V` is a four-group and `V ≤ S₀` with `S₀` cyclic is impossible, the second alternative:
  `V` is a four-group, `[Ĥ : VU] = 6` and `Ĥ/VU` is not cyclic of order `6`.
* `V` and `U` are normal in `Ĥ` of coprime order, so they commute: `VU ≤ C`.  Hence
  `[Ĥ : C]` divides `[Ĥ : VU] = 6`.
* `t ∈ V`, so `C ≤ C_G(t) = H`, and `[Ĥ : H] = 3`: the three involutions of `V` are conjugate
  under `C_G(V)`-conjugation in `Ĥ` (`I.T.fus` for the four-group `V`, together with
  `N_G(V) = Ĥ`), so orbit-stabiliser at `t` gives `[Ĥ : C_Ĥ(t)] = 3`
  (`Work.CORE3.RelIndexCentralizerFourGroup`).
* Hence `[Ĥ : C] = 3·[H : C] | 6`, so `[Ĥ : C] ∈ {3,6}`.  If it is `6` then `C = VU` by
  cardinality.  If it is `3` then `[H : C] = 1`, i.e. `H ≤ C`, so `S ≤ C ≤ C_G(V)`; as `V ≤ S`
  this makes `V` central in `S`, whence `S` is commutative
  (`Work.CORE3.CommuteOfCentralizingFourGroup`, `|S : V| = 2`, `|S| = 8`), contradicting
  `S ≅ D₈` non-commutative (`Work.CORE3.DihedralFourNotCommutative`). -/
theorem CentralizerPcoreEqVU (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) :
    Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓ B.Hhat
      = Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ### Bender's Theorem 2.6
  obtain ⟨hUeq, hVS, hdisj⟩ := I.h26 G I.T.ft h B
  have hV4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat) := D.four
  -- ### `V ⊄ S₀`
  have hVnotS0 : ¬ Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0 := fun hle =>
    Work.CORE3.not_isCyclic_of_isFourGroup' hV4
      (Work.CORE3.isCyclic_of_le_of_isCyclic' hle B.S0_cyclic)
  -- ### `[Ĥ : V ⊔ U] = 6`
  have hWrel : (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 := by
    rcases hdisj with ⟨hle, -⟩ | ⟨-, hrel, -⟩
    · exact absurd hle hVnotS0
    · exact hrel
  -- ### `V ≤ S` and `t ∈ V`
  have hVleS : Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := by
    rw [← hVS]; exact inf_le_left
  have htV : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := by
    rw [← hVS]
    refine ⟨Work.CORE2A.bSetup_t_mem_S B, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (Work.CORE2A.bSetup_U_le_H B hy)
  -- ### `V ⊔ U ≤ C`
  have hVleC : Work.GW2.pCoreIn 2 B.Hhat ≤
      Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff_isMulCommutative]
    exact Work.CORE2A.IsFourGroup.isMulCommutative' hV4
  have hUleC : B.U ≤ Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    have hcop : (Nat.card (Work.GW2.oddCoreIn B.Hhat)).Coprime
        (Nat.card (Work.GW2.pCoreIn 2 B.Hhat)) := by
      have hodd : Odd (Nat.card (Work.GW2.oddCoreIn B.Hhat)) := by
        rw [hUeq]; exact Work.CORE2A.bSetup_U_odd B
      have hc4 : Nat.card (Work.GW2.pCoreIn 2 B.Hhat) = 4 := D.four.1
      rw [hc4, show (4 : ℕ) = 2 ^ 2 from rfl]
      exact Nat.Coprime.pow_right 2 hodd.coprime_two_right
    have h := Work.CORE3.LeCentralizerOfCoprimeNormal (A := Work.GW2.oddCoreIn B.Hhat)
      (B := Work.GW2.pCoreIn 2 B.Hhat) (K := B.Hhat)
      (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _)
      (Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat))
      (Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.pCore 2 ↥B.Hhat)) hcop
    rw [hUeq] at h
    exact h
  have hWleC : Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U ≤
      Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓ B.Hhat := by
    refine le_inf (sup_le hVleC hUleC) ?_
    exact sup_le (Work.CORE2A.pCoreIn_le_Hhat B) (Work.CORE2A.bSetup_U_le_Hhat B)
  have hWleHhat : Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U ≤ B.Hhat :=
    le_trans hWleC inf_le_right
  -- ### `[Ĥ : C]` divides `6`
  let C : Subgroup G :=
    Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓ B.Hhat
  have hWleC' : Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U ≤ C := hWleC
  have hdvd : C.relIndex B.Hhat ∣ 6 := by
    have h := Subgroup.relIndex_dvd_of_le_left (B.Hhat) hWleC'
    rwa [hWrel] at h
  have hCleHhat : C ≤ B.Hhat := inf_le_right
  -- ### `[Ĥ : H] = 3`
  obtain ⟨n, hn2, ⟨e⟩⟩ := Work.CORE3.SylowDihedral G h B
  have hcardS : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hn4 : n = 4 := by rw [D.S8] at hcardS; omega
  have hdih4 : Nonempty (↥(B.S : Subgroup G) ≃* DihedralGroup 4) := by
    rw [hn4] at e
    exact ⟨e⟩
  have hnoIdx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN h2
    haveI : N.Normal := hN
    rcases h.simple.eq_bot_or_eq_top_of_normal N with hb | ht
    · rw [hb, Subgroup.index_bot] at h2
      have hd := Subgroup.card_subgroup_dvd_card (B.S : Subgroup G)
      rw [D.S8, h2] at hd
      have hle := Nat.le_of_dvd (by norm_num) hd
      omega
    · rw [ht, Subgroup.index_top] at h2
      omega
  have hfus := I.T.fus G B.S 4 (by norm_num) hdih4 hnoIdx
  have hNHat : Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) =
      B.Hhat := Work.CORE3.NormalizerPcoreEqHhat G h B hV4
  have hKHat : B.Hhat ≤
      Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := hNHat.ge
  have htrans : ∀ x ∈ Work.GW2.pCoreIn 2 B.Hhat, ∀ y ∈ Work.GW2.pCoreIn 2 B.Hhat,
      x ≠ 1 → y ≠ 1 → ∃ g ∈ B.Hhat, g * x * g⁻¹ = y := by
    intro x hx y hy hx1 hy1
    obtain ⟨g, hg, hgxy⟩ := hfus.2 (Work.GW2.pCoreIn 2 B.Hhat) hV4 x hx y hy hx1 hy1
    exact ⟨g, hNHat ▸ hg, hgxy⟩
  have hrelH : B.H.relIndex B.Hhat = 3 := by
    have hh := Work.CORE3.RelIndexCentralizerFourGroup (V := Work.GW2.pCoreIn 2 B.Hhat)
      (K := B.Hhat) hV4 hKHat htrans htV (Work.CORE2A.bSetup_t_ne_one B)
    rwa [inf_eq_left.mpr B.H_le_Hhat] at hh
  -- ### `C ≤ H`
  have hCleH : C ≤ B.H := by
    have hsub : ({B.t} : Set G) ⊆ ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact htV
    exact le_trans (inf_le_left : C ≤ Subgroup.centralizer
      ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G))
      (Subgroup.centralizer_le hsub)
  -- ### `[Ĥ : C] = 3 · [H : C]`
  have hCrel : C.relIndex B.Hhat = 3 * C.relIndex B.H := by
    have hh := Subgroup.relIndex_mul_relIndex (H := C) (K := B.H) (L := B.Hhat) hCleH
      B.H_le_Hhat
    rw [hrelH] at hh
    omega
  -- ### the two cases
  have hcases : C.relIndex B.Hhat = 3 ∨ C.relIndex B.Hhat = 6 := by
    have h3m : 3 * C.relIndex B.H ∣ 6 := by rw [← hCrel]; exact hdvd
    have hle : 3 * C.relIndex B.H ≤ 6 := Nat.le_of_dvd (by norm_num) h3m
    have hmle : C.relIndex B.H ≤ 2 := by omega
    rcases Nat.eq_zero_or_pos (C.relIndex B.H) with h0 | hpos
    · rw [h0, mul_zero] at h3m
      exact absurd h3m (by norm_num)
    · interval_cases C.relIndex B.H <;> omega
  change C = Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U
  rcases hcases with h3 | h6
  · -- ### the case `[Ĥ : C] = 3`: `C = H`, so `S ≤ C_G(V)`, forcing `S` commutative
    exfalso
    have hm1 : C.relIndex B.H = 1 := by omega
    have hHC : B.H ≤ C := Subgroup.relIndex_eq_one.mp hm1
    have hSH : (B.S : Subgroup G) ≤ C := le_trans (Work.CORE2A.bSetup_S_le_H B) hHC
    have hScent : (B.S : Subgroup G) ≤
        Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
      le_trans hSH (inf_le_left : C ≤ Subgroup.centralizer
        ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G))
    -- `V` is central in `S`
    have hcardV' : Nat.card ((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf (B.S : Subgroup G)) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleS).toEquiv]
      exact D.four.1
    have hcent' : ∀ v ∈ (Work.GW2.pCoreIn 2 B.Hhat).subgroupOf (B.S : Subgroup G),
        ∀ s : ↥(B.S : Subgroup G), v * s = s * v := by
      intro v hv s
      have hvV : ((v : ↥(B.S : Subgroup G)) : G) ∈ Work.GW2.pCoreIn 2 B.Hhat := hv
      have hcomm := (Subgroup.mem_centralizer_iff.mp (hScent s.2))
        ((v : ↥(B.S : Subgroup G)) : G) hvV
      exact Subtype.ext hcomm
    have hcommS := Work.CORE3.CommuteOfCentralizingFourGroup
      ((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf (B.S : Subgroup G)) hcardV' D.S8 hcent'
    obtain ⟨x, y, hxy⟩ := Work.CORE3.DihedralFourNotCommutative hdih4
    exact hxy (hcommS.is_comm.comm x y)
  · -- ### the case `[Ĥ : C] = 6`: `C` and `V ⊔ U` have the same index, so they are equal
    have hcardC : Nat.card ↥C = Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) := by
      have h1 := Subgroup.relIndex_mul_card C B.Hhat
      have h2 := Subgroup.relIndex_mul_card (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) B.Hhat
      rw [inf_eq_left.mpr hCleHhat, h6] at h1
      rw [inf_eq_left.mpr hWleHhat, hWrel] at h2
      omega
    exact (Subgroup.eq_of_le_of_card_ge hWleC' (le_of_eq hcardC)).symm

end Work.CORE3
