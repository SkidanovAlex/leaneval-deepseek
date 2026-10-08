import Mathlib
import Submission.Work.Frobenius.Main
import Submission.Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic
import Submission.Work.Frobenius.Complement.isPGroup_isCyclic_of_no_basicGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Sylow subgroups of odd order of a Frobenius complement are cyclic

This is FT 3.16 (ii) (Burnside): if `H` is a Frobenius complement in a finite group `G`, then
every Sylow subgroup of `H` of odd prime order `p` is cyclic.

The proof has two ingredients.

* A finite abelian `p`-group acting faithfully and fixed-point-freely on a nontrivial finite
  group is cyclic (`isPGroup_abelian_fpf_isCyclic`, proved separately).
* A finite `p`-group of *odd* order with no subgroup isomorphic to `C_p × C_p` is cyclic
  (`isPGroup_isCyclic_of_no_basicGroup`, proved separately).

Combining them: a subgroup `V ≤ H` isomorphic to `C_p × C_p` is abelian of order `p²`, so it
acts fixed-point-freely on the Frobenius kernel and would have to be cyclic — impossible. Hence
any Sylow `p`-subgroup `P` of `H` has no `C_p × C_p` subgroup, and is therefore cyclic.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Frobenius.Complement

/-- `C_p × C_p` is not a cyclic group. -/
theorem not_isCyclic_multiplicative_zmod_prod {p : ℕ} (hp : p.Prime) :
    ¬ IsCyclic (Multiplicative (ZMod p × ZMod p)) := by
  rw [show IsCyclic (Multiplicative (ZMod p × ZMod p)) ↔
      IsCyclic (Multiplicative (ZMod p) × Multiplicative (ZMod p)) from Iff.rfl]
  rw [Group.isCyclic_prod_iff]
  rintro ⟨-, -, hcop⟩
  rw [show Nat.card (Multiplicative (ZMod p)) = p from Nat.card_zmod p] at hcop
  exact hp.ne_one (Nat.coprime_self p |>.mp hcop)

/-- An abelian subgroup of a Frobenius complement whose order is a power of a prime `p` is cyclic.

Concretely, `V` acts fixed-point-freely by conjugation on the Frobenius kernel `K`, a nontrivial
finite group, so `isPGroup_abelian_fpf_isCyclic` applies. -/
theorem isCyclic_of_isPGroup_le_isFrobeniusComplement {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : IsFrobeniusComplement H) {p : ℕ} (hp : p.Prime) {V : Subgroup H}
    (hVp : IsPGroup p V) (hVc : IsMulCommutative V) : IsCyclic V := by
  obtain ⟨K, hKmem, hKnorm, hKcomp⟩ := frobenius_theorem hH
  haveI : K.Normal := hKnorm
  have hKne : K ≠ ⊥ := kernel_ne_bot hH hKmem
  have hinf : K ⊓ H = ⊥ := frobenius_inf_eq_bot hH hKmem
  have hsup : K ⊔ H = ⊤ := frobenius_sup_eq_top hH hKmem
  have hfpf : IsFixedPointFreeOn K H :=
    (frobenius_fpf_iff hKnorm hinf hsup hH.ne_bot hKne).mp hH
  haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  haveI : IsMulCommutative V := hVc
  refine isPGroup_abelian_fpf_isCyclic hp hVp
    ((MulAut.conjNormal (H := K)).comp (H.subtype.comp V.subtype)) ?_
  intro v hv k hk
  have hval : ((v : H) : G) * (k : G) * (((v : H) : G))⁻¹ = (k : G) := by
    have h1 := congrArg (fun x : ↥K => (x : G)) hk
    rwa [show (MulAut.conjNormal (H := K)).comp (H.subtype.comp V.subtype) v k
        = (MulAut.conjNormal ((v : H) : G)) k from rfl, MulAut.conjNormal_apply] at h1
  have hvne : ((v : H) : G) ≠ 1 := by
    intro h; apply hv; apply Subtype.ext; show (v : H) = 1; exact Subtype.ext h
  have := hfpf ((v : H).2) hvne (k := (k : G)) k.2 hval
  exact Subtype.ext this

/-- A Frobenius complement contains no subgroup isomorphic to `C_p × C_p`. -/
theorem no_basicGroup_subgroup' {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsFrobeniusComplement H) {p : ℕ} (hp : p.Prime) (V : Subgroup H) :
    ¬ Nonempty (V ≃* Multiplicative (ZMod p × ZMod p)) := by
  rintro ⟨e⟩
  have hcard : Nat.card V = p ^ 2 := by
    rw [Nat.card_congr e.toEquiv, show Nat.card (Multiplicative (ZMod p × ZMod p))
      = Nat.card (ZMod p × ZMod p) from rfl, Nat.card_prod, Nat.card_zmod]
    ring
  have hVp : IsPGroup p V := IsPGroup.of_card hcard
  have hVc : IsMulCommutative V := by
    rw [isMulCommutative_iff]
    intro a b
    exact e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  have hcyc := isCyclic_of_isPGroup_le_isFrobeniusComplement hH hp hVp hVc
  exact not_isCyclic_multiplicative_zmod_prod hp ((MulEquiv.isCyclic e).mp hcyc)

theorem sylow_isCyclic_of_odd {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : IsFrobeniusComplement H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (P : Sylow p H) : IsCyclic P := by
  refine isPGroup_isCyclic_of_no_basicGroup hp hp2 P.isPGroup' ?_
  intro Q hQ
  obtain ⟨e⟩ := hQ
  refine no_basicGroup_subgroup' hH hp (Q.map (P : Subgroup H).subtype) ⟨?_⟩
  exact (Subgroup.equivMapOfInjective Q (P : Subgroup H).subtype
    (P : Subgroup H).subtype_injective).symm.trans e

end Work.Frobenius.Complement
