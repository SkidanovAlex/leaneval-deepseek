import Mathlib
import Submission.Work.PGroup.normal_typePP_of_not_isCyclic
import Submission.Work.ThmF.ChV12.cyclic_of_abelian_faithful_irreducible
import Submission.Work.ThmF.ChV12.center_cyclic_of_irreducible
import Submission.Work.ThmF.ChV12.Cp2_action_finrank_ge
import Submission.Work.ThmF.ChV12.baseChange_action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ThmF.ChV12

/-!
# The Bender dimension bound for a faithful irreducible `𝔽₂`-representation of an odd `p`-group

A nonabelian finite `p`-group `P` (`p` odd) acting faithfully and irreducibly on a finite
`𝔽₂`-vector space `V` satisfies `p ≤ dim_{𝔽₂} V`.

The proof reduces the statement to a statement about the weight spaces of a
(normal) subgroup `W ≅ C_p × C_p` of `P`:

* since `V` is irreducible, the centre `Z(P)` is cyclic, so `W ⊄ Z(P)`;
* `W` is elementary abelian of order `p²`, hence `K ⊗_{𝔽₂} V` (for an algebraically closed
  field `K`) decomposes into `W`-weight spaces `V_χ`;
* conjugating by an element of `P ∖ C_P(W)` permutes the weights `χ` in orbits of `p`-power
  length `> 1`, so `|S| ≥ p` where `S = {χ : V_χ ≠ 0}`;
* the weight spaces are independent, so `dim V ≥ |S| ≥ p`.
-/

/-- **The group-theoretic reduction.**  A nonabelian finite `p`-group (`p` odd) with cyclic
centre admits a normal elementary abelian subgroup `W` of order `p²` together with an
element `g` whose conjugation action `σ` on `W` is nontrivial of `p`-power order. -/
theorem exists_conj_action_of_not_central
    {P : Type*} [Group P] [Finite P] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hP : IsPGroup p P) (hnab : ¬ IsMulCommutative P)
    (hcenter : IsCyclic ↥(Subgroup.center P)) :
    ∃ (W : Subgroup P) (g : P) (σ : MulAut ↥W),
      W.Normal ∧ Work.LocalPrelim.IsTypePP p W ∧ σ ≠ 1 ∧
      (∃ k, 0 < k ∧ orderOf σ = p ^ k) ∧
      (∀ w : ↥W, (σ w : P) = g * (w : P) * g⁻¹) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hncP : ¬ IsCyclic P := fun h => hnab (@IsCyclic.isMulCommutative P _ h)
  have hodd' : Odd p := hp.odd_of_ne_two hodd
  obtain ⟨W, hWle, hWnorm, hWtype⟩ :=
    Work.PGroup.normal_typePP_of_not_isCyclic (G := P) hp hodd'
      (P := (⊤ : Subgroup P)) (hP.to_subgroup ⊤)
      (by intro h; exact hncP ((Subgroup.topEquiv (G := P)).isCyclic.mp h))
  haveI hWnormal : W.Normal := by
    have h2 := hWnorm.map (Subgroup.subtype (⊤ : Subgroup P))
      (fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩)
    rwa [Subgroup.subgroupOf_map_subtype, inf_top_eq] at h2
  have hWexp : ∀ x : ↥W, x ^ p = 1 := hWtype.1.2
  have hWcard : Nat.card ↥W = p ^ 2 := hWtype.2
  have hWnotCyc : ¬ IsCyclic ↥W := by
    intro hcyc
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
    have hord : orderOf g = p ^ 2 := by
      have h1 : Nat.card ↥(Subgroup.zpowers g) = orderOf g := Nat.card_zpowers g
      rw [hg] at h1
      rw [← h1, ← hWcard]
      exact Nat.card_congr (Subgroup.topEquiv (G := ↥W)).toEquiv
    have hdvd : orderOf g ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hWexp g)
    rw [hord] at hdvd
    have hle := Nat.le_of_dvd hp.pos hdvd
    nlinarith [hp.two_le]
  have hnotle : ¬ (W ≤ Subgroup.center P) := by
    intro hle
    haveI : IsCyclic ↥(Subgroup.center P) := hcenter
    exact hWnotCyc (isCyclic_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle))
  obtain ⟨x, hxW, hxnc⟩ : ∃ x, x ∈ W ∧ x ∉ Subgroup.center P := by
    by_contra h
    exact hnotle (fun y hy => by
      by_contra hy'
      exact h ⟨y, hy, hy'⟩)
  obtain ⟨g, hg⟩ : ∃ g : P, g * x ≠ x * g := by
    by_contra h
    exact hxnc (Subgroup.mem_center_iff.mpr (fun g => by by_contra h'; exact h ⟨g, h'⟩))
  have hσne : MulAut.conjNormal (H := W) g ≠ 1 := by
    intro h
    have h1 : (MulAut.conjNormal (H := W) g) ⟨x, hxW⟩ = ⟨x, hxW⟩ := by rw [h]; rfl
    have h2 : g * x * g⁻¹ = x := by
      have := congrArg (fun w : ↥W => (w : P)) h1
      rwa [MulAut.conjNormal_apply] at this
    have h3 : g * x = x * g := by
      have := congrArg (fun y => y * g) h2
      simpa [mul_assoc] using this
    exact hg h3
  have hσpow : ∃ k, 0 < k ∧ orderOf (MulAut.conjNormal (H := W) g) = p ^ k := by
    have hd1 : orderOf (MulAut.conjNormal (H := W) g) ∣ orderOf g := orderOf_map_dvd _ g
    have hd2 : orderOf g ∣ Nat.card P := orderOf_dvd_natCard g
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    have hd : orderOf (MulAut.conjNormal (H := W) g) ∣ p ^ n := by
      rw [← hn]; exact dvd_trans hd1 hd2
    obtain ⟨k, hk, hkp⟩ := (Nat.dvd_prime_pow hp).mp hd
    refine ⟨k, ?_, hkp⟩
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hkp
      exact hσne (orderOf_eq_one_iff.mp hkp)
    · exact hpos
  exact ⟨W, g, MulAut.conjNormal (H := W) g, hWnormal, hWtype, hσne, hσpow,
    fun w => MulAut.conjNormal_apply g w⟩

/-- **Bender's dimension bound.**  Let `P` be a finite nonabelian `p`-group with `p` odd and
`V` a finite `𝔽₂`-vector space carrying a faithful irreducible representation of `P`.  Then
`p ≤ dim_{𝔽₂} V`. -/
theorem irreducible_pgroup_finrank_ge {P : Type} [Group P] [Finite P] {p : ℕ}
    (hp : Nat.Prime p) (hodd : p ≠ 2) (hP : IsPGroup p P) (hnab : ¬ IsMulCommutative P)
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : P →* (V ≃ₗ[ZMod 2] V)) (hfaith : Function.Injective ρ)
    (hirr : ∀ W : Submodule (ZMod 2) V, W ≠ ⊥ →
      (∀ g : P, ∀ x ∈ W, ρ g x ∈ W) → W = ⊤) :
    p ≤ Module.finrank (ZMod 2) V := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- The centre of `P` is cyclic (Schur + Wedderburn).
  have hcenter : IsCyclic ↥(Subgroup.center P) := center_cyclic_of_irreducible ρ hfaith hirr
  -- A normal `(p,p)`-subgroup with a nontrivial `p`-power-order conjugation action.
  obtain ⟨W, g, σ, hWnormal, hWtype, _hσne, hσpow, hσconj⟩ :=
    exists_conj_action_of_not_central hp hodd hP hnab hcenter
  haveI hWnormalI : W.Normal := hWnormal
  letI hWcommI : CommGroup ↥W :=
    { (inferInstance : Group ↥W) with mul_comm := isMulCommutative_iff.mp hWtype.1.1 }
  -- Base change to an algebraically closed field of characteristic `2 ≠ p`.
  let K := AlgebraicClosure (ZMod 2)
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hchar : ringChar K ≠ p := by rw [ringChar.eq K 2]; exact hodd.symm
  obtain ⟨ρW, σV, hρWinj, hcompat, hfin⟩ :=
    baseChange_action (F := ZMod 2) (K := K) ρ hfaith W.subtype
      (Subgroup.subtype_injective W) g σ hσconj
  -- The weight-space bound over `K`.
  have key : p ≤ Module.finrank K (TensorProduct (ZMod 2) K V) :=
    Cp2_action_finrank_ge (K := K) hp hchar hWtype.2 ρW hρWinj σ hσpow σV hcompat
  rwa [hfin] at key

end Work.ThmF.ChV12
