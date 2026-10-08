import Mathlib.GroupTheory.Index
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Group
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.exists_smul_eq_of_ne_of_card_eq_one_add
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.mem_sup_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.BNPair

open scoped Pointwise

theorem normalizer_eq_sup_zpowers {G : Type*} [Group G] [Finite G]
    (B U T : Subgroup G) (w : G)
    (hB : B = U ⊔ T)
    (hUT : U ⊓ T = ⊥)
    (hTnU : T ≤ Subgroup.normalizer (U : Set G))
    (hwB : w ∉ B)
    (hwT : w ∈ Subgroup.normalizer (T : Set G))
    (hCU : ∀ u ∈ U, (∀ t ∈ T, u * t = t * u) → u = 1)
    (hindex : B.index = Nat.card U + 1)
    (hfree : ∀ u : U, u ≠ 1 → ∀ x : G ⧸ B, (u : G) • x = x → x = ((1 : G) : G ⧸ B)) :
    Subgroup.normalizer (T : Set G) = T ⊔ Subgroup.zpowers w := by
  classical
  let N : Subgroup G := Subgroup.normalizer (T : Set G)
  change N = T ⊔ Subgroup.zpowers w
  have hUB : U ≤ B := by rw [hB]; exact le_sup_left
  have hTB : T ≤ B := by rw [hB]; exact le_sup_right
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hwN : w ∈ N := hwT
  -- ## Step A: `U ⊓ N = ⊥`
  have hUN : U ⊓ N = ⊥ := by
    apply le_antisymm
    · intro u hu
      rw [Subgroup.mem_inf] at hu
      obtain ⟨huU, huN⟩ := hu
      have hcomm : ∀ t ∈ T, u * t = t * u := by
        intro t ht
        have h1 : u * t * u⁻¹ * t⁻¹ ∈ T := by
          have hx : u * t * u⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp huN t).mp ht
          exact T.mul_mem hx (T.inv_mem ht)
        have h2 : u * t * u⁻¹ * t⁻¹ ∈ U := by
          have htN : t ∈ Subgroup.normalizer (U : Set G) := hTnU ht
          have h3 : t * u⁻¹ * t⁻¹ ∈ U :=
            (Subgroup.mem_normalizer_iff.mp htN u⁻¹).mp (U.inv_mem huU)
          have h4 : u * (t * u⁻¹ * t⁻¹) ∈ U := U.mul_mem huU h3
          simpa only [mul_assoc] using h4
        have hbot : u * t * u⁻¹ * t⁻¹ = 1 := by
          have hmem : u * t * u⁻¹ * t⁻¹ ∈ U ⊓ T := Subgroup.mem_inf.mpr ⟨h2, h1⟩
          rw [hUT] at hmem
          simpa using hmem
        have h : u * t * u⁻¹ = t := by
          calc u * t * u⁻¹ = (u * t * u⁻¹ * t⁻¹) * t := by group
            _ = 1 * t := by rw [hbot]
            _ = t := one_mul t
        calc u * t = (u * t * u⁻¹) * u := by group
          _ = t * u := by rw [h]
      exact Subgroup.mem_bot.mpr (hCU u huU hcomm)
    · exact bot_le
  -- ## Step B: `B ⊓ N = T`
  have hBN : B ⊓ N = T := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxB, hxN⟩ := hx
      have hx' : x ∈ U ⊔ T := by rw [← hB]; exact hxB
      obtain ⟨a, haU, b, hbT, hab⟩ :=
        Commons.GroupTheory.Subgroup.mem_sup_mul U T hTnU hx'
      have haN : a ∈ N := by
        have h1 : x * b⁻¹ ∈ N := N.mul_mem hxN (N.inv_mem (hTN hbT))
        simpa [hab, mul_assoc] using h1
      have ha1 : a = 1 := by
        have hmem : a ∈ U ⊓ N := Subgroup.mem_inf.mpr ⟨haU, haN⟩
        rw [hUN] at hmem
        simpa using hmem
      simpa [hab, ha1] using hbT
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hTB hx, hTN hx⟩
  -- ## Setup of the quotient action
  set z : G ⧸ B := ((1 : G) : G ⧸ B) with hz
  have hsmul_z : ∀ a : G, a • z = (a : G ⧸ B) := by
    intro a; rw [hz]; simp
  have hz_eq : ∀ b ∈ B, (b : G ⧸ B) = z := by
    intro b hb
    rw [hz, QuotientGroup.eq]
    simpa using B.inv_mem hb
  have hcard : Nat.card (G ⧸ B) = Nat.card U + 1 :=
    (Subgroup.index_eq_card B).symm.trans hindex
  have hfixz : ∀ u : U, (u : G) • z = z := by
    intro u
    rw [hsmul_z]
    exact hz_eq _ (hUB u.2)
  have htrans : ∀ x y : G ⧸ B, x ≠ z → y ≠ z → ∃ u : U, (u : G) • x = y := by
    intro x y hx hy
    exact Commons.GroupTheory.GroupAction.exists_smul_eq_of_ne_of_card_eq_one_add z hcard hfixz
      (fun u hu x hx => hfree u hu x hx) hx hy
  -- ## Uniqueness of the `T`-fixed point away from `z`
  have huniq : ∀ x y : G ⧸ B, x ≠ z → y ≠ z →
      (∀ t ∈ T, t • x = x) → (∀ t ∈ T, t • y = y) → x = y := by
    intro x y hx hy hxT hyT
    obtain ⟨u, hu⟩ := htrans x y hx hy
    have hu1 : (u : G) = 1 := by
      apply hCU (u : G) u.2
      intro t ht
      have hconjU : t * (u : G) * t⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hTnU ht) (u : G)).mp u.2
      set v : G := (u : G)⁻¹ * (t * (u : G) * t⁻¹) with hvdef
      have hvU : v ∈ U := U.mul_mem (U.inv_mem u.2) hconjU
      have hvfix : v • x = x := by
        have htinv : t⁻¹ • x = x := hxT t⁻¹ (T.inv_mem ht)
        calc v • x = ((u : G)⁻¹ * (t * (u : G) * t⁻¹)) • x := by rw [hvdef]
          _ = (u : G)⁻¹ • ((t * (u : G) * t⁻¹) • x) := by rw [mul_smul]
          _ = (u : G)⁻¹ • (t • ((u : G) • (t⁻¹ • x))) := by simp only [mul_smul]
          _ = (u : G)⁻¹ • (t • ((u : G) • x)) := by rw [htinv]
          _ = (u : G)⁻¹ • (t • y) := by rw [hu]
          _ = (u : G)⁻¹ • y := by rw [hyT t ht]
          _ = x := by rw [← hu]; exact inv_smul_smul (u : G) x
      have hv1 : v = 1 := by
        by_contra hne
        exact hx (hfree ⟨v, hvU⟩ (by simpa using hne) x hvfix)
      have hconj : t * (u : G) * t⁻¹ = (u : G) := by
        have h := hv1
        rw [hvdef] at h
        calc t * (u : G) * t⁻¹ = (u : G) * ((u : G)⁻¹ * (t * (u : G) * t⁻¹)) := by
              group
          _ = (u : G) * 1 := by rw [h]
          _ = (u : G) := mul_one _
      calc (u : G) * t = (t * (u : G) * t⁻¹) * t := by rw [hconj]
        _ = t * (u : G) := by group
    rw [← hu, hu1, one_smul]
  -- ## Main argument
  apply le_antisymm
  · intro g hgN
    by_cases hgB : g ∈ B
    · have hmem : g ∈ B ⊓ N := Subgroup.mem_inf.mpr ⟨hgB, hgN⟩
      rw [hBN] at hmem
      exact Subgroup.mem_sup_left hmem
    · have hx_ne : (g : G ⧸ B) ≠ z := by
        intro h
        apply hgB
        rw [hz, QuotientGroup.eq] at h
        exact by simpa using B.inv_mem h
      have hw_ne : (w : G ⧸ B) ≠ z := by
        intro h
        apply hwB
        rw [hz, QuotientGroup.eq] at h
        exact by simpa using B.inv_mem h
      have hgTfix : ∀ t ∈ T, t • (g • z) = g • z := by
        intro t ht
        have hconjT : g⁻¹ * t * g ∈ T := by
          have := (Subgroup.mem_normalizer_iff.mp (N.inv_mem hgN) t).mp ht
          simpa using this
        calc t • (g • z) = (t * g) • z := by rw [mul_smul]
          _ = (g * (g⁻¹ * t * g)) • z := by rw [show t * g = g * (g⁻¹ * t * g) by group]
          _ = g • ((g⁻¹ * t * g) • z) := by rw [mul_smul]
          _ = g • z := by rw [hsmul_z, hz_eq _ (hTB hconjT)]
      have hwTfix : ∀ t ∈ T, t • (w • z) = w • z := by
        intro t ht
        have hconjT : w⁻¹ * t * w ∈ T := by
          have := (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (T : Set G)).inv_mem hwT) t).mp ht
          simpa using this
        calc t • (w • z) = (t * w) • z := by rw [mul_smul]
          _ = (w * (w⁻¹ * t * w)) • z := by rw [show t * w = w * (w⁻¹ * t * w) by group]
          _ = w • ((w⁻¹ * t * w) • z) := by rw [mul_smul]
          _ = w • z := by rw [hsmul_z, hz_eq _ (hTB hconjT)]
      have hgw : g • z = w • z :=
        huniq (g • z) (w • z) (by rw [hsmul_z]; exact hx_ne) (by rw [hsmul_z]; exact hw_ne)
          hgTfix hwTfix
      have hgwB : g⁻¹ * w ∈ B := by
        have h : (g : G ⧸ B) = (w : G ⧸ B) := by
          rw [← hsmul_z g, ← hsmul_z w]; exact hgw
        rwa [QuotientGroup.eq] at h
      have hgwN : g⁻¹ * w ∈ N := N.mul_mem (N.inv_mem hgN) hwN
      have hgwT : g⁻¹ * w ∈ T := by
        have hmem : g⁻¹ * w ∈ B ⊓ N := Subgroup.mem_inf.mpr ⟨hgwB, hgwN⟩
        rwa [hBN] at hmem
      have hgeq : g = w * (g⁻¹ * w)⁻¹ := by group
      rw [hgeq]
      exact (T ⊔ Subgroup.zpowers w).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
        (Subgroup.mem_sup_left (T.inv_mem hgwT))
  · apply sup_le
    · exact hTN
    · intro x hx
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨k, rfl⟩ := hx
      exact N.zpow_mem hwN k

end Commons.GroupTheory.BNPair