import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.invJCard
import Submission.Work.BG.splitglue.Split
import Submission.Work.BG.kappaExists
import Submission.Work.BG.S_le_H
import Submission.Work.BG.BInvAux.Basic
import Submission.Work.BG.BInvAux.odd_order_mem_B
import Submission.Work.BG.BInvAux.decomp_centralizer

/-!
# Area BG: `B` is `N_G(S)`-invariant and `C_G(S)` acts on `B` by inner automorphisms

Bender–Glauberman 1981, the group-theoretic input of Lemma 4.2 for the case `n = 2`
(`S ≅ V₄`): writing `B = B₁ ⊓ B₂` with `Bᵢ = U ⊓ C_G(tᵢ)`, `U = O(C_G(t))` and `H = C_G(t)`,

* every element of `N_G(S)` normalises `B`;
* every element of `C_G(S)` acts on `B` as conjugation by an element of `B` (so `C_G(S)` acts
  trivially on the class functions of `B`, which is what `Work.GW2.C23.NOrbProp` needs).

The two ingredients are proved in the companion modules `Submission/Work/BG/BInvAux/`:

* `BInvAux.decomp_centralizer`: `C_G(S) ≤ H = U ⊔ S`, so a `c ∈ C_G(S)` is `u * s` with
  `u ∈ B`, `s ∈ S`;
* `BInvAux.odd_order_mem_B`: an odd-order element of `C_G(S)` lies in `B` (its companion
  `Work.BG.C_odd_mem_U` shows it lies in `U`).

For `x ∈ N_G(S)` and `b ∈ B`: `x⁻¹ b x` centralises `S` (since `b` does and `x⁻¹ S x = S`) and
has odd order (it is conjugate to `b ∈ B ≤ U`, and `U` has odd order), so it lies in `B`.
For `c = u * s ∈ C_G(S)` and `b ∈ B`: `u⁻¹ b u ∈ B` centralises `s ∈ S`, so
`c⁻¹ b c = s⁻¹ (u⁻¹ b u) s = u⁻¹ b u = b₀ b b₀⁻¹` with `b₀ = u⁻¹ ∈ B`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup in
theorem l42BNinv {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (hn : D.n = 2) :
    (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B) ∧
    (∀ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B,
        ∃ b₀ ∈ D.B, c⁻¹ * b * c = b₀ * b * b₀⁻¹) := by
  haveI : Fintype G := Fintype.ofFinite G
  constructor
  · -- `N_G(S)` normalises `B`
    intro x hx b hb
    have hbU : b ∈ D.U := hb.1.1
    have hbC : b ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) :=
      BInvAux.B_le_centralizer_S' D hb
    have hodd_b : Odd (orderOf b) :=
      Odd.of_dvd_nat (odd_card_U D) (Subgroup.orderOf_dvd_natCard D.U hbU)
    -- `x⁻¹ b x` centralises `S`
    have hconjC : x⁻¹ * b * x ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hxs : x * s * x⁻¹ ∈ (D.S : Subgroup G) :=
        (Subgroup.mem_normalizer_iff.mp hx s).mp hs
      have hcomm : (x * s * x⁻¹) * b = b * (x * s * x⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hbC (x * s * x⁻¹) hxs
      calc s * (x⁻¹ * b * x) = x⁻¹ * ((x * s * x⁻¹) * b) * x := by group
        _ = x⁻¹ * (b * (x * s * x⁻¹)) * x := by rw [hcomm]
        _ = (x⁻¹ * b * x) * s := by group
    -- it has odd order, being conjugate to `b`
    have hodd_conj : Odd (orderOf (x⁻¹ * b * x)) := by
      have hsemi : SemiconjBy x⁻¹ b (x⁻¹ * b * x) := by
        rw [SemiconjBy]
        group
      rw [← SemiconjBy.orderOf_eq x⁻¹ hsemi]
      exact hodd_b
    exact BInvAux.odd_order_mem_B D hn hconjC hodd_conj
  · -- `C_G(S)` acts on `B` by inner automorphisms
    intro c hc b hb
    obtain ⟨u, hu, s, hs, hcs⟩ := BInvAux.decomp_centralizer D hn hc
    refine ⟨u⁻¹, D.B.inv_mem hu, ?_⟩
    have hX : u⁻¹ * b * u ∈ D.B := D.B.mul_mem (D.B.mul_mem (D.B.inv_mem hu) hb) hu
    have hcomm : s * (u⁻¹ * b * u) = (u⁻¹ * b * u) * s :=
      Subgroup.mem_centralizer_iff.mp (BInvAux.B_le_centralizer_S' D hX) s hs
    rw [hcs]
    calc (u * s)⁻¹ * b * (u * s) = s⁻¹ * (u⁻¹ * b * u) * s := by group
      _ = u⁻¹ * b * u := by
        rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      _ = u⁻¹ * b * u⁻¹⁻¹ := by rw [inv_inv]

end Work.BG
