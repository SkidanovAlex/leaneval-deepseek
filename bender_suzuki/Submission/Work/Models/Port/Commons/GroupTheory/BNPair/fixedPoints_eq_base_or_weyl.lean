import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.exists_smul_eq_of_ne_of_card_eq_one_add

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.BNPair

/-- In a saturated BN-pair setup, the points of `G ⧸ B` fixed by the torus `T` are exactly
the base point and its image under the Weyl element `w`. -/
theorem fixedPoints_eq_base_or_weyl {G : Type*} [Group G] [Finite G]
    (B U T : Subgroup G) (w : G) (hB : B = U ⊔ T) (hUT : U ⊓ T = ⊥)
    (hTnU : T ≤ Subgroup.normalizer (U : Set G)) (hwB : w ∉ B)
    (hwT : w ∈ Subgroup.normalizer (T : Set G))
    (hCU : ∀ u ∈ U, (∀ t ∈ T, u * t = t * u) → u = 1)
    (hindex : B.index = Nat.card U + 1)
    (hfree : ∀ u : U, u ≠ 1 → ∀ x : G ⧸ B, (u : G) • x = x → x = ((1 : G) : G ⧸ B))
    {x : G ⧸ B} (hx : ∀ t ∈ T, t • x = x) :
    x = ((1 : G) : G ⧸ B) ∨ x = w • ((1 : G) : G ⧸ B) := by
  classical
  have hUB : U ≤ B := by rw [hB]; exact le_sup_left
  have hTB : T ≤ B := by rw [hB]; exact le_sup_right
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
  rcases eq_or_ne x z with hxz | hxz
  · exact Or.inl hxz
  · refine Or.inr ?_
    have hw_ne : (w : G ⧸ B) ≠ z := by
      intro h
      apply hwB
      rw [hz, QuotientGroup.eq] at h
      exact by simpa using B.inv_mem h
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
    have hxw : x = w • z :=
      huniq x (w • z) hxz (by rw [hsmul_z]; exact hw_ne) hx hwTfix
    rw [hxw, hsmul_z]

end Commons.GroupTheory.BNPair