import Mathlib
import Submission.Work.BG.invJCard
import Submission.Work.BG.kappaExists
import Submission.Work.BG.thmCSmallAux
import Submission.Work.BG.splitglue.Split
import Submission.Work.BG.S_le_H

namespace Work.BG

open scoped Pointwise

/-- A natural number dividing `4` which is odd equals `1`. -/
theorem eq_one_of_dvd_four_of_odd {a : ℕ} (h : a ∣ 4) (ho : Odd a) : a = 1 := by
  have hcop : Nat.Coprime a 2 := Nat.coprime_two_right.mpr ho
  have h1 : a ∣ 2 := hcop.dvd_of_dvd_mul_left (by simpa using h)
  have h2 : a ∣ 1 := hcop.dvd_of_dvd_mul_left (by simpa using h1)
  exact Nat.dvd_one.mp h2

open OddOrder.RepresentationTheory Work.GW2 Work.BG Subgroup in
/-- **`B` is normalised by `N_G(S)` in the `|S| = 4` case** (first half of `Work.BG.nOrbBInv`).

For Bender–Glauberman data `D` with `D.n = 2` (`S ≅ V₄`), `B = B₁ ⊓ B₂` is invariant under
conjugation by every element of `N_G(S)`.

Route.  (a) `H = C_G(t) = U · S` (`Work.GW2.CentralizerSplitProp`, proved as
`Work.BG.SplitGlue.centralizerSplitProp`), and `C_G(S) ≤ C_G(t) = H` because `t ∈ S`
(`Work.BG.S_le_H`, `D.t_mem`).
(b) *Every odd-order element of `C_G(S)` lies in `B`*: write `c ∈ C_G(S)` as `c = u * s` with
`u ∈ U`, `s ∈ S` (`Subgroup.mem_sup`, (a)); since `s ∈ S` is centralised by `c` and `S` is
abelian (`D.n = 2`), also `u` centralises `S`, i.e. `u ∈ C_U(S) = B`
(use `Work.BG.S_eq_closure` : `S = ⟨t₁,t₂⟩`, and `Work.GW2.BGData.B = B1 ⊓ B2`); then
`s = u⁻¹ * c` has odd order (product of two odd-order elements) and lies in the `2`-group `S`,
so `s = 1` and `c = u ∈ B`.
(c) For `x ∈ N_G(S)` and `b ∈ B`: `x⁻¹ b x` centralises `x⁻¹ S x = S` (because `b` centralises
`S`, `Work.BG.B_le_centralizer_S`) and has odd order (conjugate of `b ∈ B ≤ U`,
`Work.BG.odd_card_U`), so (b) applies. -/
theorem l41vBInv {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (hn : D.n = 2) :
    ∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- `S ≤ C_G(t)`: the centrality hypothesis of `CentralizerSplitProp`.
  have hcentr : ∀ x ∈ (D.S : Subgroup G), x * D.t = D.t * x := fun x hx =>
    ((Subgroup.mem_centralizer_iff.mp (BGData_S_le_centralizer_t D hx)) D.t
      (Set.mem_singleton D.t)).symm
  -- (a) `H = U ⊔ S` (Bender's centralizer splitting).
  have hUS : D.U ⊔ (D.S : Subgroup G) = D.H :=
    SplitGlue.centralizerSplitProp G D.S D.n D.two_le D.dih D.t (D.S0_le D.t_mem) D.t_order hcentr
  -- `|S| = 4`.
  have hcardS : Nat.card ↥(D.S : Subgroup G) = 4 := by
    obtain ⟨e⟩ := D.dih
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hn]
  -- every element of `U` has odd order.
  have hU_odd : ∀ u ∈ D.U, Odd (orderOf u) := by
    intro u hu
    have hd : orderOf u ∣ Nat.card ↥D.U := by
      have h := orderOf_dvd_natCard (⟨u, hu⟩ : ↥D.U)
      rwa [Subgroup.orderOf_mk u hu] at h
    exact Odd.of_dvd_nat (odd_card_U D) hd
  -- (b) every odd-order element of `C_G(S)` lies in `B`.
  have hB_of_odd : ∀ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G),
      Odd (orderOf c) → c ∈ D.B := by
    intro c hc hcodd
    -- `c ∈ H = C_G(t)`.
    have hcH : c ∈ D.H := by
      show c ∈ Subgroup.centralizer ({D.t} : Set G)
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_iff.mp hc D.t (D.S0_le D.t_mem)
    -- write `c = u * s` with `u ∈ U`, `s ∈ S`.
    have hcProd : c ∈ (↑D.U : Set G) * (↑(D.S : Subgroup G) : Set G) := by
      rw [← coe_U_sup_S D]
      exact show c ∈ D.U ⊔ (D.S : Subgroup G) from by rw [hUS]; exact hcH
    obtain ⟨u, hu, s, hs, hus⟩ := hcProd
    -- `u` and `c` commute: `u = c * s⁻¹` and `s ∈ S` commutes with `c ∈ C_G(S)`.
    have hsc : Commute s c := Subgroup.mem_centralizer_iff.mp hc s hs
    have huc : Commute u c := by
      have hu_eq : u = c * s⁻¹ := by rw [← hus]; group
      have hsc' : s⁻¹ * c = c * s⁻¹ := hsc.inv_left
      calc u * c = (c * s⁻¹) * c := by rw [hu_eq]
        _ = c * (s⁻¹ * c) := by rw [mul_assoc]
        _ = c * (c * s⁻¹) := by rw [hsc']
        _ = c * u := by rw [hu_eq]
    -- `s = u⁻¹ * c` has odd order.
    have hs_eq : s = u⁻¹ * c := by rw [← hus]; group
    have hsodd : Odd (orderOf s) := by
      rw [hs_eq]
      exact Odd.of_dvd_nat
        ((show Odd (orderOf u⁻¹) from by rw [orderOf_inv]; exact hU_odd u hu).mul hcodd)
        huc.inv_left.orderOf_mul_dvd_mul_orderOf
    -- `orderOf s ∣ |S| = 4`, so `s = 1`.
    have hsdvd : orderOf s ∣ 4 := by
      have hd : orderOf s ∣ Nat.card ↥(D.S : Subgroup G) := by
        have h := orderOf_dvd_natCard (⟨s, hs⟩ : ↥(D.S : Subgroup G))
        rwa [Subgroup.orderOf_mk s hs] at h
      rwa [hcardS] at hd
    have hs1 : s = 1 :=
      orderOf_eq_one_iff.mp (eq_one_of_dvd_four_of_odd hsdvd hsodd)
    -- hence `c = u ∈ U`, and `c` centralises `S`, so `c ∈ B = B₁ ⊓ B₂`.
    have hcU : c ∈ D.U := by
      rw [← hus, hs1]
      simpa using hu
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hcU, ?_⟩,
      Subgroup.mem_inf.mpr ⟨hcU, ?_⟩⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hc D.t1 D.t1_mem).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hc D.t2 D.t2_mem).symm
  -- (c) conjugation by `x ∈ N_G(S)`.
  intro x hxN b hbB
  have hbU : b ∈ D.U := (show D.B ≤ D.U from inf_le_left.trans inf_le_left) hbB
  refine hB_of_odd (x⁻¹ * b * x) ?_ ?_
  · -- `x⁻¹ b x` centralises `S`.
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hxv : x * v * x⁻¹ ∈ (D.S : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hxN v).mp hv
    have hbcomm : (x * v * x⁻¹) * b = b * (x * v * x⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (B_le_centralizer_S D hbB) (x * v * x⁻¹) hxv
    calc v * (x⁻¹ * b * x) = x⁻¹ * ((x * v * x⁻¹) * b) * x := by group
      _ = x⁻¹ * (b * (x * v * x⁻¹)) * x := by rw [hbcomm]
      _ = (x⁻¹ * b * x) * v := by group
  · -- `x⁻¹ b x` is a conjugate of `b`, so has odd order.
    have hsemi : SemiconjBy x (x⁻¹ * b * x) b := by rw [SemiconjBy]; group
    rw [SemiconjBy.orderOf_eq x hsemi]
    exact hU_odd b hbU

end Work.BG
