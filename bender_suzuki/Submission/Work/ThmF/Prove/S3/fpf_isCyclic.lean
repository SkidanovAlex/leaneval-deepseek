import Mathlib
import Submission.Work.Frobenius.Complement.isCyclic_of_card_eq_mul_primes
import Submission.Work.Frobenius.Complement.isPGroup_isCyclic_of_no_basicGroup
import Submission.Work.Frobenius.Complement.sylow_isCyclic_of_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Odd `ℓ`-subgroups of a fixed-point-free coprime automorphism group are cyclic

Let a finite group `A` act on a nontrivial finite group `E` by group automorphisms, with
`(|A|, |E|) = 1`, in such a way that every `a ≠ 1` has only the identity as a fixed point
(`hfpf`).  Then every `ℓ`-subgroup `B ≤ A` for an odd prime `ℓ` is cyclic.

The argument is the classical one (Burnside's theorem on Frobenius complements):

* A subgroup `Q ≤ B` with `Q ≅ C_ℓ × C_ℓ` would be abelian of order `ℓ²`, hence an abelian
  `ℓ`-group acting fixed-point-freely on the nontrivial group `E`; by
  `isPGroup_abelian_fpf_isCyclic` it would be cyclic, contradicting
  `not_isCyclic_multiplicative_zmod_prod`.
* Therefore `B` (an odd `ℓ`-group) has no `C_ℓ × C_ℓ` subgroup and is cyclic by
  `isPGroup_isCyclic_of_no_basicGroup`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped IsMulCommutative

namespace Work.ThmF.Prove.S3

theorem fpf_isCyclic {A E : Type*} [Group A] [Finite A] [Group E] [Finite E] [Nontrivial E] [MulDistribMulAction A E] (hcop : (Nat.card A).Coprime (Nat.card E)) (hfpf : ∀ a : A, a ≠ 1 → ∀ e : E, a • e = e → e = 1) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {B : Subgroup A} (hB : IsPGroup ℓ B) : IsCyclic ↥B := by
  refine Work.Frobenius.Complement.isPGroup_isCyclic_of_no_basicGroup hℓ hℓ2 hB ?_
  -- `B` has no subgroup isomorphic to `C_ℓ × C_ℓ`
  intro Q hQ
  obtain ⟨e⟩ := hQ
  -- `Q` is abelian, being isomorphic to a commutative group
  haveI : IsMulCommutative ↥Q := by
    rw [isMulCommutative_iff]
    intro a b
    exact e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  have hQp : IsPGroup ℓ ↥Q := hB.to_subgroup Q
  -- the restricted action of `Q` on `E`
  let ρQ : ↥Q →* MulAut E :=
    (MulDistribMulAction.toMulAut A E).comp (B.subtype.comp Q.subtype)
  have hfpfQ : ∀ q : ↥Q, q ≠ 1 → ∀ n : E, ρQ q n = n → n = 1 := by
    intro q hq n hn
    have ha : ((q : ↥B) : A) ≠ 1 := by
      intro h
      exact hq (Subtype.ext (Subtype.ext h))
    have hn' : ((q : ↥B) : A) • n = n := by
      simpa [ρQ] using hn
    exact hfpf _ ha n hn'
  -- an abelian `ℓ`-group acting fixed-point-freely on `E` must be cyclic
  have hcyc : IsCyclic ↥Q :=
    Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic hℓ hQp ρQ hfpfQ
  exact Work.Frobenius.Complement.not_isCyclic_multiplicative_zmod_prod hℓ
    ((MulEquiv.isCyclic e).mp hcyc)

end Work.ThmF.Prove.S3
