import Mathlib
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.CharCore.IrrDegreeAux
import Submission.Work.CharCore.dvd_of_isIntegral_rat
import Submission.Work.FeitSibley.Coherence.congr_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.irr_congr_mod_card_Q`

Peterfalvi II, Appendice XII, step (7): if `ψ ∈ Irr G` is constant on `Z^#`, where `Z ⊴ H`,
`Z ≤ Q₁`, `Z` centralises `Q₁` and `Q` is a T.I. Hall subgroup of `G`, then
`ψ(z) ≡ ψ(1) mod |Q|` for every `z ∈ Z^#`: the difference `(ψ z - ψ 1)/|Q|` is an algebraic
integer.

The proof is the class-algebra argument of the source:

* `congr_master` computes, for any admissible `ψ`, the congruence
  `ψ(z)(U₁₁ - U₁₂) ≡ ψ(1)|C₁| mod |Q|`, where `U₁₁`, `U₁₂` count the pairs with `1 ≠ xy ∈ Z` in
  `C₁ × C₁` and `C₁ × C₁⁻¹` (`C₁` the class of `z`); the two sides come from the trace identity
  `centralChar_mul_eq_pair_sum` applied to the class sums of `C₁` and `C₁⁻¹`, the splitting
  `sum_pair_split`, and the free-action integrality `isIntegral_sum_pairs_out_Z`;
* applying `congr_master` to the trivial character gives `U₁₁ - U₁₂ ≡ |C₁| mod |Q|`;
* subtracting the two congruences leaves `|C₁| (ψ z - ψ 1) ≡ 0 mod |Q|`, and `|C₁| = |G : Q|` is
  coprime to `|Q|` by `card_class_eq_index` and the Hall hypothesis.
-/

namespace Work.FeitSibley.Coherence

open Classical

theorem irr_congr_mod_card_Q {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {Z : Subgroup G} (hZH : Z ≤ h.H) (hZQ1 : Z ≤ h.Q1)
    (hZnorm : h.H ≤ Subgroup.normalizer (Z : Set G))
    (hZcent : ∀ z ∈ Z, ∀ y ∈ h.Q1, z * y = y * z) (hZne : Z ≠ ⊥)
    (hQhall : Nat.Coprime (Nat.card h.Q) h.Q.index)
    (hnotconj : ∀ z ∈ Z, z ≠ 1 → ∀ g : G, g * z * g⁻¹ ≠ z⁻¹)
    {psi : G → ℂ} (hpsi : psi ∈ Work.CharCore.Irr G)
    (hconst : ∀ z ∈ Z, z ≠ 1 → ∀ z' ∈ Z, z' ≠ 1 → psi z = psi z') :
    ∀ z ∈ Z, z ≠ 1 →
      IsIntegral ℤ ((psi z - psi 1) / (Nat.card h.Q : ℂ)) := by
  intro z hz hz1
  have hconst' : ∀ z' ∈ Z, z' ≠ 1 → psi z' = psi z :=
    fun z' h1 h2 => (hconst z hz hz1 z' h1 h2).symm
  have hnc : ∀ g : G, g * z * g⁻¹ ≠ z⁻¹ := hnotconj z hz hz1
  -- the congruence for `psi`
  have hA := congr_master h hZnorm hZQ1 hz hz1 hnc hpsi hconst'
  -- the congruence for the trivial character
  have htriv : (fun _ : G => (1 : ℂ)) ∈ Work.CharCore.Irr G :=
    Work.CharCore.principalChar_mem_Irr
  have hconstT : ∀ z' ∈ Z, z' ≠ 1 →
      (fun _ : G => (1 : ℂ)) z' = (fun _ : G => (1 : ℂ)) z := fun _ _ _ => rfl
  have hB := congr_master h hZnorm hZQ1 hz hz1 hnc htriv hconstT
  set n : ℕ := Nat.card h.Q with hn
  set K : ℤ := (Ucount Z (ConjClasses.mk z) (ConjClasses.mk z) : ℤ)
      - (Ucount Z (ConjClasses.mk z) (ConjClasses.mk z⁻¹) : ℤ) with hK
  set kk : ℕ := Fintype.card (ConjClasses.mk z).carrier with hkk
  have hn0 : n ≠ 0 := by rw [hn]; exact Nat.card_pos.ne'
  -- the trivial character gives `K ≡ κ mod n`
  have hB' : IsIntegral ℤ (((K - (kk : ℤ) : ℤ) : ℂ) / (n : ℂ)) := by
    convert hB using 1
    simp only [hK, hkk, hn]
    push_cast
    ring
  obtain ⟨s, hs⟩ := dvd_of_isIntegral_int_div hn0 hB'
  -- the congruence for `psi`, in terms of `K` and `κ`
  have hA' : IsIntegral ℤ (((psi z) * (K : ℂ) - (psi 1) * (kk : ℂ)) / (n : ℂ)) := by
    convert hA using 1
    simp only [hK, hkk, hn]
    push_cast
    ring
  -- substitute `K = κ + n s`
  have hsC : (K : ℂ) = (kk : ℂ) + (n : ℂ) * (s : ℂ) := by
    have hcast : (K : ℂ) - (kk : ℂ) = (n : ℂ) * (s : ℂ) := by
      have h1 := congrArg (fun t : ℤ => (t : ℂ)) hs
      push_cast at h1
      exact h1
    rw [← hcast]
    ring
  have hstep : IsIntegral ℤ (((kk : ℂ) * (psi z - psi 1)) / (n : ℂ)) := by
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hsplit : ((psi z) * (K : ℂ) - (psi 1) * (kk : ℂ)) / (n : ℂ)
        = ((kk : ℂ) * (psi z - psi 1)) / (n : ℂ) + (s : ℂ) * psi z := by
      rw [hsC]
      field_simp
      ring
    rw [hsplit] at hA'
    have hBint : IsIntegral ℤ ((s : ℂ) * psi z) :=
      (isIntegral_intCast s).mul (isIntegral_irr_value hpsi z)
    have := hA'.sub hBint
    convert this using 1
    ring
  -- `κ = |G : Q|`
  have hZQ : ∀ z ∈ Z, ∀ y ∈ h.Q, z * y = y * z := by
    intro z hz y hy
    have hmem := Z_le_centralizer_Q h hZQ1 hZcent hz
    exact (Subgroup.mem_centralizer_iff.mp hmem y hy).symm
  have hκ : (kk : ℕ) = h.Q.index := by
    rw [hkk]
    exact card_class_eq_index h hZQ1 hZQ hz hz1
  have hcop : Nat.Coprime kk n := by
    rw [hκ, hn]
    exact hQhall.symm
  -- cancel the factor `κ`, coprime to `n`
  have hx : IsIntegral ℤ (psi z - psi 1) :=
    (isIntegral_irr_value hpsi z).sub (isIntegral_irr_value hpsi 1)
  have hfin := isIntegral_div_of_coprime hn0 hx hstep hcop
  simpa [hn] using hfin

end Work.FeitSibley.Coherence
