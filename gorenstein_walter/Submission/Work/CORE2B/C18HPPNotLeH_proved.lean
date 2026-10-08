import Mathlib
import Submission.Work.CORE2B.HallPerPrime_Xodd
import Submission.Work.CORE2B.HallPerPrime_aux
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.pCoreIn_le_of_relIndex_not_dvd
import Submission.Work.CORE2B.oddCoreIn_card_map_mulAut

namespace Work.CORE2B

-- GW design pass 18, item A′, leaf H1 (copied from `Core18HPPNotLeH.lean`): Bender p. 222,
-- "since `t` and `s` are conjugate, `P ⊄ C_G(t)`" — the `t`-invariant Sylow `P` of `O(C_G(s))`
-- is not contained in `C_G(t)`.
-- Sketch: if `P ≤ H = C(t)`, then `H = U ⊔ S` (`T.split`) and `P` is odd, so `P ≤ U`; `s = t^g`
-- gives `O(C(s)) = U^{g⁻¹}` with the same order, so `P` is a Sylow `p`-subgroup of `U` and hence
-- contains the normal `p`-subgroup `O_p(U) = pCoreIn p B.U`; so `O_p(U) ≤ P ≤ C(s)`, contradicting
-- `hXlt`.  (`p = 2` gives `O_2(U) = ⊥` by `pCoreIn_two_eq_bot`, again contradicting `hXlt`.)
theorem C18HPPNotLeH_proved (T : Work.GW2.LocalToolkit) (G : Type) [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (s : G)
    (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) (p : ℕ) (hp : Nat.Prime p) (P : Subgroup G)
    (hPK : P ≤ Work.GW2.oddCoreIn (Subgroup.centralizer ({s} : Set G)))
    (hPp : IsPGroup p P)
    (hPsyl : ¬ p ∣ P.relIndex (Work.GW2.oddCoreIn (Subgroup.centralizer ({s} : Set G))))
    (hXlt : ¬ Work.GW2.pCoreIn p B.U ≤ Subgroup.centralizer ({s} : Set G)) :
    ¬ P ≤ Subgroup.centralizer ({B.t} : Set G) := by
  classical
  -- `C = C_G(s)`, `K = O(C_G(s))`; `H = C_G(t)`, `U = O(H)`, `S` the dihedral Sylow.
  set C : Subgroup G := Subgroup.centralizer ({s} : Set G) with hCdef
  set K : Subgroup G := Work.GW2.oddCoreIn C with hKdef
  -- `S` is dihedral and `s ∈ S − S₀` is an involution, hence conjugate to `t` (`T.fus`)
  obtain ⟨n, hn2, hiso⟩ := S_dihedral_iso hCtx B
  have hs2 : orderOf s = 2 := orderOf_eq_two_of_mem_S_notMem_S0 hCtx B hs hs0
  have hno2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 :=
    fun N hN => hallXodd_no_index_two hCtx N hN
  obtain ⟨g, hg⟩ := isConj_iff.mp ((T.fus G (B.S) n hn2 hiso hno2).1 s B.t hs2 B.t_order)
  -- `H = U ⊔ S` (`T.split`)
  have hsplit : B.U ⊔ (B.S : Subgroup G) = B.H :=
    T.split G (B.S) n hn2 hiso B.t (B.S0_le B.t_mem) B.t_order (t_central_in_S B)
  -- the conjugation `φ = conj g⁻¹` sends `t` to `s`, hence `H = C_G(t)` to `C = C_G(s)`
  set φ : MulAut G := MulAut.conj g⁻¹ with hφdef
  have hφt : φ B.t = s := by
    rw [hφdef, MulAut.conj_apply, inv_inv, ← hg]
    group
  have hHmap : B.H.map φ.toMonoidHom = C := by
    show (Subgroup.centralizer ({B.t} : Set G)).map φ.toMonoidHom = C
    rw [hallXodd_map_centralizer φ ({B.t} : Set G), Set.image_singleton, hφt]
  -- hence `|O(C_G(s))| = |O(C_G(t))| = |U|`
  have hcardKU : Nat.card K = Nat.card B.U := by
    have h := oddCoreIn_card_map_mulAut (G := G) φ B.H
    rw [hHmap] at h
    exact h
  intro hPle
  -- `P ≤ K = O(C(s))` has odd order
  have hKodd : Odd (Nat.card K) := by
    show Odd (Nat.card ↥((Work.GW2.oddCore ↥C).map C.subtype))
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact oddCore_odd (G := ↥C)
  have hPodd : Odd (Nat.card P) := Odd.of_dvd_nat hKodd (Subgroup.card_dvd_of_le hPK)
  -- `H` normalises `U` and `H = U ⊔ S`, so the odd-order subgroup `P ≤ H` lies in `U`
  have hHU : B.H ≤ Subgroup.normalizer (B.U : Set G) := by
    have h := le_normalizer_map_subtype_local B.H (Work.GW2.oddCore ↥B.H)
      (Work.GW2.oddCore_normal ↥B.H)
    simpa [Work.GW2.BenderSetup.U, Work.GW2.oddCoreIn] using h
  have hUn : (B.U.subgroupOf B.H).Normal := by
    refine (Subgroup.normal_subgroupOf_iff (Subgroup.map_subtype_le (H := B.H)
      (Work.GW2.oddCore ↥B.H))).mpr ?_
    intro x k hx hk
    exact (Subgroup.mem_normalizer_iff.mp (hHU hk) x).mp hx
  have hPU : P ≤ B.U :=
    hallXodd_odd_subgroup_le_of_sup (C := B.H) (U := B.U) (S := (B.S : Subgroup G))
      hsplit hUn B.S.isPGroup' P hPle hPodd
  -- the index of `P` in `K` and in `U` agree, because those two groups have the same order
  have hrelK : P.relIndex K * Nat.card P = Nat.card K := by
    have h := Subgroup.relIndex_mul_card P K
    rwa [inf_eq_left.mpr hPK] at h
  have hrelU : P.relIndex B.U * Nat.card P = Nat.card B.U := by
    have h := Subgroup.relIndex_mul_card P B.U
    rwa [inf_eq_left.mpr hPU] at h
  have hrel : ¬ p ∣ P.relIndex B.U := by
    have heq : P.relIndex K = P.relIndex B.U :=
      Nat.mul_right_cancel (Nat.card_pos (α := ↥P)) (by rw [hrelK, hrelU, hcardKU])
    exact heq ▸ hPsyl
  -- so `P` is a Sylow `p`-subgroup of `U` and contains the normal `p`-subgroup `O_p(U)`
  have hcore : Work.GW2.pCoreIn p B.U ≤ P :=
    pCoreIn_le_of_relIndex_not_dvd p hp hPU hPp hrel
  -- but `P ≤ K ≤ C_G(s)`, contradicting the hypothesis
  exact hXlt (le_trans hcore (le_trans hPK (show K ≤ C from (in_le_self C p ∅).1)))

end Work.CORE2B
