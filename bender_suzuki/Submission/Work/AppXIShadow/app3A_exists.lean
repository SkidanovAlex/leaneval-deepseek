import Mathlib
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.ThreePoints.ThmC.exists_normal_commutator_le
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.AppXIShadow

open LeanEval.GroupTheory.Defs

/-- A finite group of even order contains an element of order `2` (Cauchy for `p = 2`). -/
theorem app3A_exists_involution {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (h : Even (Nat.card ↥C)) : ∃ u ∈ C, orderOf u = 2 := by
  haveI : Fintype ↥C := Fintype.ofFinite ↥C
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Fintype.card ↥C := by
    rw [Fintype.card_eq_nat_card]; exact even_iff_two_dvd.mp h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥C) 2 h2
  exact ⟨(u : G), u.2, (orderOf_injective C.subtype C.subtype_injective u).trans hu⟩

/-- **Peterfalvi I, Appendix III (2), existence form.**  Let the finite group `F` act on `Ω`, let
`a : Ω` have a strongly embedded stabiliser `H = Stab_F a`, and let `F` have 2-rank `1`
(`¬ HasFourGroup F`).  Assuming the Brauer–Suzuki and Feit–Thompson blocks, there is a normal
subgroup `A ⊴ F` contained in `O(F) = O_{2'}(F)`, not contained in `H`, with `⁅A,A⁆ ≤ H`.

Proof: `H` has even order (`hstrong.2.1`), so pick an involution `u ∈ H`; by strong embeddedness
the centraliser of an involution of `H` lies in `H`, so `C_F(u) ≤ H`.  Brauer–Suzuki (`hBrSz`,
2-rank `1`) gives `O(F) · C_F(u) = F`, whence `O(F) ⊔ H = ⊤`; as `H ≠ ⊤` this implies
`¬ O(F) ≤ H`.  Feit–Thompson (`hFT`) makes `O(F)` solvable of odd order, so
`exists_normal_commutator_le` produces the required `A`. -/
theorem app3A_exists {F Ω : Type} [Group F] [Finite F] [MulAction F Ω] (a : Ω)
    (hstrong : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (MulAction.stabilizer F a))
    (hrank : ¬ Submission.Blueprint.HasFourGroup F)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hFT : Submission.Blueprint.FeitThompsonProp) :
    ∃ A : Subgroup F, A.Normal ∧ A ≤ Submission.Blueprint.oddCore F ∧
      ¬ A ≤ MulAction.stabilizer F a ∧ ⁅A, A⁆ ≤ MulAction.stabilizer F a := by
  classical
  set H : Subgroup F := MulAction.stabilizer F a with hHdef
  -- an involution `u ∈ H`
  obtain ⟨u, huH, hu2⟩ := app3A_exists_involution (C := H) hstrong.2.1
  -- Peterfalvi I Ch. I §1 (2): the centraliser of an involution of `H` lies in `H`
  have hCuH : Subgroup.centralizer ({u} : Set F) ≤ H := by
    intro y hy
    by_contra hyH
    have hyu : u * y = y * u := (Subgroup.mem_centralizer_iff.mp hy) u rfl
    have huy : y * u * y⁻¹ = u := by rw [← hyu, mul_assoc, mul_inv_cancel, mul_one]
    have hmem : u ∈ H ⊓ H.map (MulAut.conj y).toMonoidHom := by
      refine ⟨huH, ?_⟩
      refine Subgroup.mem_map.mpr ⟨u, huH, ?_⟩
      show (MulAut.conj y) u = u
      rw [MulAut.conj_apply]
      exact huy
    have h2 : 2 ∣ Nat.card ↥(H ⊓ H.map (MulAut.conj y).toMonoidHom) := by
      have h3 : orderOf (⟨u, hmem⟩ : ↥(H ⊓ H.map (MulAut.conj y).toMonoidHom)) = 2 := by
        rw [← Subgroup.orderOf_coe (⟨u, hmem⟩ : ↥(H ⊓ H.map (MulAut.conj y).toMonoidHom))]
        exact hu2
      rw [← h3]
      exact orderOf_dvd_natCard _
    exact (Nat.not_even_iff_odd.mpr (hstrong.2.2 y hyH)) (even_iff_two_dvd.mpr h2)
  -- Brauer–Suzuki: `F = O(F) · H`
  have hOH : Submission.Blueprint.oddCore F ⊔ H = ⊤ := by
    have h := sup_le_sup_left hCuH (Submission.Blueprint.oddCore F)
    rw [hBrSz F hrank u hu2] at h
    exact top_le_iff.mp h
  -- `O(F) ⊄ H`, since `H ≠ ⊤`
  have hOnotle : ¬ Submission.Blueprint.oddCore F ≤ H := by
    intro hle
    have htop : (⊤ : Subgroup F) ≤ H := by
      rw [← hOH]
      exact sup_le hle le_rfl
    exact hstrong.1 (hHdef ▸ top_le_iff.mp htop)
  -- `O(F)` is solvable of odd order (Feit–Thompson)
  have hOsolv : Group.IsSolvable ↥(Submission.Blueprint.oddCore F) :=
    hFT ↥(Submission.Blueprint.oddCore F) Work.BrauerSuzuki.OddCore.oddCard_oddCore
  -- the normal subgroup `A ⊴ F` with `A ≤ O(F)`, `A ⊄ H` and `⁅A,A⁆ ≤ H`
  obtain ⟨A, hAnorm, hAle, hAnotle, hAder, -⟩ :=
    Work.ThreePoints.ThmC.exists_normal_commutator_le (Submission.Blueprint.oddCore F) H
      (Work.BrauerSuzuki.oddCore_normal F) hOsolv
      Work.BrauerSuzuki.OddCore.oddCard_oddCore hOnotle
  exact ⟨A, hAnorm, hAle, hAnotle, hAder⟩

end Work.AppXIShadow
