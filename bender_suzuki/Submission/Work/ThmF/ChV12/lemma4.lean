import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmG.nilpotent_of_K_ne_one
import Submission.Work.ThreePoints.ThmC.ch1_sec6_cor1
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.DoubleTransitivity.Sec2.inv_class
import Submission.Work.DoubleTransitivity.Sec1.restrict
import Submission.Work.ThompsonFrobenius.thompsonFrobenius
import Submission.Work.ThmF.ChV12.glaubermanZJ_free
import Submission.Work.ThmF.ChV12.odd_card_centralizer_of_conj_ut

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi II, Ch. V §2, Lemma 4 (p. 246): strongly real elements

`x` strongly real (`x = a * b`, `a`, `b` involutions) with `x² ≠ 1`; `H = Q ⋊ D` split rank-one
data with `t ∉ H` an involution.  Then

* `x` is conjugate to `u * t` for some `u ∈ Q₀# = Inv(H)`, and
* `|C_G(x)|` is odd.

The proof follows the source, with one deviation: the source quotes Ch. V §1 Prop. 1 (c)
("the involutions of `H` commute pairwise"), whose proof in the paper goes through Ch. V §1
Prop. 1 (b) (`Q` nilpotent, Thompson's theorem on Frobenius kernels) and Prop. 1 (a)
(`C_Q(k) = 1` for `k ∈ K#`, i.e. Ch. II §4 Prop. 2 (c) — available here as part of `ChIIFourProp`).
`Work.ThmG.nilpotent_of_K_ne_one` performs exactly that reduction, and Thompson's theorem is
available in the workspace; here it is used in the Feit–Thompson-free form
(`Work.ThmF.ChV12.glaubermanZJ_free` derives Glauberman's `ZJ`-theorem, whence
`ThompsonFrobeniusProp`, without the odd order theorem).

The two conclusions are then obtained as follows.

* `inv(H) ⊆ Q` and `Inv(H) ⊆ Z(Q)` (`Work.ThmF.ChV12.prop1c`), so involutions of `H` (and, by
  conjugation, of any conjugate of `H`) commute.  Hence two non-commuting involutions `a`, `b`
  lie in *distinct* conjugates of `H`; with `x = a * b`, Ch. I §6 Cor. 1
  (`Work.ThreePoints.ThmC.ch1_sec6_cor1`) conjugates the triple `(H(a),H(b),a)` to
  `(H, H(t), s)`, and the two-point stabiliser of `(H,H(t))` moves `b` onto `t`.
* For the oddness of `|C_G(x)|`, `N_G(⟨x⟩)` has a proper strongly embedded subgroup
  `N_G(⟨x⟩) ∩ H`, hence one class of involutions (`Work.DoubleTransitivity.Sec2.inv_class`);
  since `C_G(x) ⊴ N_G(⟨x⟩)` and `u ∈ N_G(⟨x⟩) ∖ C_G(x)`, `C_G(x)` has no involution.
-/

namespace Work.ThmF.ChV12

open LeanEval.GroupTheory.Defs Submission.Blueprint
open Work.ThmF

variable {G : Type} [Group G] [Finite G]

/-- **Thompson's theorem on Frobenius kernels** in the form used below, with the vestigial
Feit–Thompson hypothesis of the area removed: a finite group with a fixed-point-free
automorphism of prime order is nilpotent. -/
theorem thompsonFrobeniusFree : ThompsonFrobeniusProp := by
  intro Q _ _ α hq hfpf
  exact Work.ThompsonFrobenius.isNilpotent_of_fpf_pow glaubermanZJ_free (Nat.card Q) Q rfl α
    (orderOf α) hq (pow_orderOf_eq_one α) hfpf

/-- **Peterfalvi II, Ch. V §1 Prop. 1 (c).**  In split rank-one data `H = Q ⋊ D`, the involutions
of `H` commute pairwise: `Prop. 1 (b)` makes `Q` nilpotent, `Prop. 1 (a)` (Ch. II §4 Prop. 2 (c))
supplies a fixed-point-free element of `K#`, and `Work.ThmF.ChV12.prop1c` then puts every
involution of `H` in `Z(Q)`. -/
theorem involutions_of_H_commute (hS : Situation G) (hC4 : ChIIFourProp)
    (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) :
    ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G), u * v = v * u := by
  have hfour : HasFourGroup G := hS.1.1
  -- `K = J(D,t) ≠ 1`
  have hK : ∃ z ∈ invertedBy (twoPoint H t) t, z ≠ 1 := by
    have hcard : (Kset H t).ncard = (involutions (H : Set G)).ncard :=
      Work.ThmF.Bender.cardKsetEqInv h.stronglyEmbedded h.invol h.not_mem
    have h2 : 2 ≤ (Kset H t).ncard := by
      rw [hcard]
      exact Work.ThmF.Bender.cardInvGeTwo h.stronglyEmbedded hfour
    have hne : ∃ z ∈ Kset H t, z ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hsub : Kset H t ⊆ ({1} : Set G) := fun z hz => by
        rw [Set.mem_singleton_iff]
        exact hcon z hz
      have hle := Set.ncard_le_ncard hsub
      rw [Set.ncard_singleton] at hle
      omega
    obtain ⟨z, hz, hz1⟩ := hne
    exact ⟨z, hz, hz1⟩
  have hnil : Group.IsNilpotent ↥Q :=
    Work.ThmG.nilpotent_of_K_ne_one hS hC4 thompsonFrobeniusFree h hK
  have hD : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
      ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b :=
    Work.ThmF.Bender.DTransitiveInv h.stronglyEmbedded h.invol h.not_mem
  have hcent := prop1c hS H Q t h hD hnil
  intro u hu v hv
  have hu' := hcent u hu
  rw [Work.ThmF.mem_centerOf] at hu'
  exact hu'.2 v ((show centerOf Q ≤ Q from inf_le_left) (hcent v hv))

/-- Commutativity of the involutions of `H` transfers to every conjugate of `H`. -/
theorem involution_commute_conj {H : Subgroup G}
    (hcomm : ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G), u * v = v * u) :
    ∀ g : G, ∀ u ∈ involutions (conj g H : Set G), ∀ v ∈ involutions (conj g H : Set G),
      u * v = v * u := by
  intro g u hu v hv
  have hu' : g⁻¹ * u * g ∈ involutions (H : Set G) := by
    refine ⟨?_, ?_⟩
    · exact Work.Models.mem_conj_iff.mp hu.1
    · have h := Work.ThmF.Bender.orderOf_conj_eq g⁻¹ u
      rw [inv_inv] at h
      rw [h]
      exact hu.2
  have hv' : g⁻¹ * v * g ∈ involutions (H : Set G) := by
    refine ⟨?_, ?_⟩
    · exact Work.Models.mem_conj_iff.mp hv.1
    · have h := Work.ThmF.Bender.orderOf_conj_eq g⁻¹ v
      rw [inv_inv] at h
      rw [h]
      exact hv.2
  have h := hcomm _ hu' _ hv'
  calc u * v = g * (g⁻¹ * u * g) * (g⁻¹ * v * g) * g⁻¹ := by group
    _ = g * ((g⁻¹ * u * g) * (g⁻¹ * v * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * v * g) * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
    _ = v * u := by group

/-- **First half of Peterfalvi II, Ch. V §2 Lemma 4 (p. 246).**  If `a`, `b` are involutions with
`x = a * b` and `x² ≠ 1`, and the involutions of every conjugate of `H` commute, then `x` is
conjugate to `u * t` for some non-trivial `u ∈ Q₀ = Inv(H) ∪ {1}`. -/
theorem exists_conj_eq_inv_mul_t {H : Subgroup G}
    (hH : IsStronglyEmbedded H) (h2t : IsTwoTransitiveOn H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H)
    (hcomm : ∀ g : G, ∀ u ∈ involutions (conj g H : Set G),
      ∀ v ∈ involutions (conj g H : Set G), u * v = v * u)
    {x : G} (hx2 : x * x ≠ 1) (hsr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = x) :
    ∃ u ∈ Q0 H, u ≠ 1 ∧ ∃ g : G, g * x * g⁻¹ = u * t := by
  obtain ⟨a, b, ha2, hb2, hab⟩ := hsr
  have ha1 : a ≠ 1 := fun h => hx2 (by rw [← hab, h]; simp [hb2])
  have hb1 : b ≠ 1 := fun h => hx2 (by rw [← hab, h]; simp [ha2])
  have hao : orderOf a = 2 := Work.ThreePoints.orderOf_eq_two_of ha1 ha2
  have hbo : orderOf b = 2 := Work.ThreePoints.orderOf_eq_two_of hb1 hb2
  -- `a` and `b` do not commute
  have hnab : a * b ≠ b * a := by
    intro h
    apply hx2
    rw [← hab]
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [h]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  -- the conjugates of `H` containing `a`, `b` and `t`
  obtain ⟨g₁, hg₁⟩ := Work.ThmF.Bender.exists_conj_of_involution hH hao
  obtain ⟨g₂, hg₂⟩ := Work.ThmF.Bender.exists_conj_of_involution hH hbo
  obtain ⟨τ, hτ⟩ := Work.ThmF.Bender.exists_conj_of_involution hH ht
  -- `H(a) ≠ H(b)`
  have hne : conj g₁ H ≠ conj g₂ H := by
    intro hEq
    have hb₁ : b ∈ conj g₁ H := by rw [hEq]; exact hg₂
    exact hnab (hcomm g₁ a ⟨hg₁, hao⟩ b ⟨hb₁, hbo⟩)
  -- `H ≠ H(t)`
  have hne' : conj (1 : G) H ≠ conj τ H := by
    rw [Work.Models.conj_one]
    intro hEq
    exact htH (hEq ▸ hτ)
  -- some involution of `H`
  obtain ⟨s, hsH, hso⟩ := Work.ThmF.Bender.exists_involution_mem_of_isStronglyEmbedded hH
  -- Ch. I §6 Cor. 1 conjugates `(H(a),H(b),a)` to `(H,H(t),s)`
  obtain ⟨xg, hxg₁, hxg₂, hxga⟩ :=
    Work.ThreePoints.ThmC.ch1_sec6_cor1 hH h2t hne hne' ⟨hg₁, hao⟩
      ⟨by rw [Work.Models.conj_one]; exact hsH, hso⟩
  -- the involution `xg * b * xg⁻¹` of `H(t)`
  have hwinv : xg * b * xg⁻¹ ∈ involutions (conj τ H : Set G) := by
    refine ⟨?_, ?_⟩
    · have hmem : xg * b * xg⁻¹ ∈ conj xg (conj g₂ H) :=
        Subgroup.mem_map.mpr ⟨b, hg₂, MulAut.conj_apply xg b⟩
      rwa [hxg₂] at hmem
    · have h := Work.ThmF.Bender.orderOf_conj_eq xg b
      rw [h]
      exact hbo
  have htinv : t ∈ involutions (conj τ H : Set G) := ⟨hτ, ht⟩
  -- the two-point stabiliser of `(H(t),H)` moves `xg * b * xg⁻¹` onto `t`
  have hne'' : conj τ H ≠ conj (1 : G) H := fun h => hne' h.symm
  obtain ⟨d, hd, hdw⟩ :=
    Work.ThreePoints.ThmC.twoPoint_transitive_on_involutions_conj hH hne'' hwinv htinv
  have hdH : d ∈ H := by
    have h2 := hd.2
    rwa [Work.Models.conj_one] at h2
  -- `u₀ = d * s * d⁻¹ ∈ Q₀#`
  have hu₀ : d * s * d⁻¹ ∈ involutions (H : Set G) := by
    refine ⟨?_, ?_⟩
    · have hmem : d * s * d⁻¹ ∈ conj d H :=
        Subgroup.mem_map.mpr ⟨s, hsH, MulAut.conj_apply d s⟩
      rwa [Work.Models.conj_self_of_mem_normalizer (H.le_normalizer hdH)] at hmem
    · have h := Work.ThmF.Bender.orderOf_conj_eq d s
      rw [h]
      exact hso
  refine ⟨d * s * d⁻¹, Work.ThmF.involutions_subset_Q0 H hu₀, ?_, ⟨d * xg, ?_⟩⟩
  · intro h1
    have h2 := hu₀.2
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · calc (d * xg) * x * (d * xg)⁻¹
        = d * (xg * (a * b) * xg⁻¹) * d⁻¹ := by rw [← hab]; group
      _ = d * ((xg * a * xg⁻¹) * (xg * b * xg⁻¹)) * d⁻¹ := by group
      _ = (d * (xg * a * xg⁻¹) * d⁻¹) * (d * (xg * b * xg⁻¹) * d⁻¹) := by group
      _ = (d * s * d⁻¹) * (d * (xg * b * xg⁻¹) * d⁻¹) := by rw [hxga]
      _ = (d * s * d⁻¹) * t := by rw [hdw]

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem lemma4 {G : Type} [Group G] [Finite G] (hS : Situation G) (hC4 : ChIIFourProp) (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) (x : G) (hx2 : x * x ≠ 1) (hsr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = x) : (∃ u ∈ Q0 H, u ≠ 1 ∧ ∃ g : G, g * x * g⁻¹ = u * t) ∧ Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set G))) := by
  have hcommH := Work.ThmF.ChV12.involutions_of_H_commute hS hC4 H Q t h
  have hcomm := Work.ThmF.ChV12.involution_commute_conj (G := G) hcommH
  have hgoal1 := Work.ThmF.ChV12.exists_conj_eq_inv_mul_t (G := G) h.stronglyEmbedded h.twoTransitive
    h.invol h.not_mem hcomm hx2 hsr
  refine ⟨hgoal1, ?_⟩
  obtain ⟨u, huQ0, hu1, g, hg⟩ := hgoal1
  have hu : u ∈ Submission.Blueprint.involutions (H : Set G) := by
    rw [Work.ThmF.mem_Q0_iff] at huQ0
    rcases huQ0 with ⟨huH, huo⟩ | h1
    · exact ⟨huH, huo⟩
    · exact absurd h1 hu1
  exact Work.ThmF.ChV12.odd_card_centralizer_of_conj_ut h.stronglyEmbedded h.invol h.not_mem
    hu hx2 ⟨g, hg⟩

end Work.ThmF.ChV12
