import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.GLUE.Defs
import Submission.Work.BG.sq_eq_one_eq_of_isCyclic
import Submission.Work.BG.S_le_H
import Submission.Work.BG.odd_card_inf_conj
import Submission.Work.BG.four_dvd_card_S
import Submission.Work.BG.cardDvdOfFree

/-!
# Area BG: the strong-embedding step of Bender–Glauberman Theorem B

`Work.BG.strongEmbed` proves `Work.GW2.C16.StrongEmbedProp`: if `D` is Bender–Glauberman data on a
finite group `G` and `G₁ ≤ G` is a proper subgroup containing `H = C_G(t)` in which all involutions
are conjugate, then `4 ∣ |G : G₁| - 1`.

The route is the classical one.

* The involution `t ∈ S₀` is central in the Sylow `2`-subgroup `S` (`Work.BG.S_le_H`), so
  `S ≤ H ≤ G₁`.
* `x ↦ C_G(x)` maps involutions of `G₁` into `G₁` (the one-class hypothesis conjugates any
  involution of `G₁` to `t` by an element of `G₁`); consequently `G₁ ∩ G₁^a` has odd order for
  `a ∉ G₁` (`Work.BG.odd_card_inf_conj`).
* Hence the left action of `S` on the coset space `G ⧸ G₁` fixes the coset `G₁` and is free away
  from it, so `|S| ∣ |G ⧸ G₁| - 1` (Burnside counting: `Work.BG.cardDvdOfFree`).
* Finally `4 ∣ |S|` (`Work.BG.four_dvd_card_S`), so `4 ∣ |G : G₁| - 1`.
-/

namespace Work.BG

open Work.GW2 Subgroup

theorem strongEmbed : Work.GW2.C16.StrongEmbedProp := by
  intro G _ _ D G1 hne hHle hcl
  -- ### The four ingredients
  -- (1) `t` is central in `S`, so `S ≤ C_G(t) = D.H`.
  have hSH : (D.S : Subgroup G) ≤ D.H := S_le_H D
  -- (2) Strong embedding: `G₁ ∩ G₁^a` has odd order for `a ∉ G₁`.
  have hodd : ∀ a : G, a ∉ G1 →
      Odd (Nat.card (G1 ⊓ G1.map (MulAut.conj a).toMonoidHom : Subgroup G)) :=
    fun a ha => odd_card_inf_conj D G1 hHle hcl ha
  -- (3) `4 ∣ |S|`.
  have hfour : 4 ∣ Nat.card ↥(D.S : Subgroup G) := four_dvd_card_S D
  have hSG1 : (D.S : Subgroup G) ≤ G1 := le_trans hSH hHle
  -- ### The coset `G₁` is fixed by `S`
  have hfix : ∀ s : ↥(D.S : Subgroup G),
      s • (QuotientGroup.mk (1 : G) : G ⧸ G1) = QuotientGroup.mk 1 := by
    intro s
    rw [show s • (QuotientGroup.mk (1 : G) : G ⧸ G1)
        = QuotientGroup.mk ((s : G) * 1) from rfl]
    rw [QuotientGroup.eq]
    simpa using Subgroup.inv_mem G1 (hSG1 s.2)
  -- ### `S` acts freely away from the coset `G₁`
  have hfree : ∀ (s : ↥(D.S : Subgroup G)), s ≠ 1 → ∀ x : G ⧸ G1,
      x ≠ QuotientGroup.mk (1 : G) → s • x ≠ x := by
    intro s hs x hx hcon
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    -- `a ∉ G₁`
    have ha : a ∉ G1 := by
      intro haG1
      exact hx ((QuotientGroup.eq).mpr (by simpa using Subgroup.inv_mem G1 haG1))
    -- `s⁻¹` lies in `G₁` and in `a G₁ a⁻¹`
    have h1 : ((s : G) * a)⁻¹ * a ∈ G1 := by
      have hc : (QuotientGroup.mk ((s : G) * a) : G ⧸ G1) = QuotientGroup.mk a := hcon
      exact (QuotientGroup.eq).mp hc
    have hkey : a⁻¹ * (s : G)⁻¹ * a ∈ G1 := by
      simpa [mul_inv_rev, mul_assoc] using h1
    have hs'G1 : (s : G)⁻¹ ∈ G1 := hSG1 (Subgroup.inv_mem (D.S : Subgroup G) s.2)
    have hs'map : (s : G)⁻¹ ∈ G1.map (MulAut.conj a).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨a⁻¹ * (s : G)⁻¹ * a, hkey, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    have hmem : (s : G)⁻¹ ∈ G1 ⊓ G1.map (MulAut.conj a).toMonoidHom := ⟨hs'G1, hs'map⟩
    -- `⟨s⁻¹⟩` lies in the intersection, whose order is odd
    have hle : Subgroup.zpowers (s : G)⁻¹ ≤ G1 ⊓ G1.map (MulAut.conj a).toMonoidHom :=
      Subgroup.zpowers_le.mpr hmem
    have hdvd : Nat.card ↥(Subgroup.zpowers (s : G)⁻¹) ∣
        Nat.card ↥(G1 ⊓ G1.map (MulAut.conj a).toMonoidHom) := Subgroup.card_dvd_of_le hle
    have hodd' : Odd (Nat.card ↥(Subgroup.zpowers (s : G)⁻¹)) :=
      Odd.of_dvd_nat (hodd a ha) hdvd
    rw [Nat.card_zpowers] at hodd'
    -- but `s⁻¹` generates a `2`-group, so its order is a power of `2`, hence can only be `1`
    have hs'ne : (s⁻¹ : ↥(D.S : Subgroup G)) ≠ 1 := by simpa using hs
    have hcoe : ((s⁻¹ : ↥(D.S : Subgroup G)) : G) = (s : G)⁻¹ := rfl
    have hodd'' : Odd (orderOf (s⁻¹ : ↥(D.S : Subgroup G))) := by
      rw [← Subgroup.orderOf_coe (s⁻¹ : ↥(D.S : Subgroup G)), hcoe]
      exact hodd'
    have h2dvd : 2 ∣ orderOf (s⁻¹ : ↥(D.S : Subgroup G)) :=
      IsPGroup.dvd_orderOf (p := 2) (D.S.isPGroup' : IsPGroup 2 ↥(D.S : Subgroup G)) hs'ne
    exact hodd''.not_two_dvd_nat h2dvd
  -- ### Burnside: `|S| ∣ |G : G₁| - 1`
  have hdvd : Nat.card ↥(D.S : Subgroup G) ∣ G1.index - 1 := by
    have h := cardDvdOfFree (G := ↥(D.S : Subgroup G)) (X := G ⧸ G1)
      (x₀ := QuotientGroup.mk (1 : G)) hfix hfree
    simpa [Subgroup.index_eq_card] using h
  exact dvd_trans hfour hdvd

end Work.BG
