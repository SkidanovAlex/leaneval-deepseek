import Mathlib
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.Symplectic.centralProduct_of_structure
import Submission.Work.PGroup.Symplectic.omega1_eq_pow_eq_one_of_class_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# If `Ω₁(H)` is commutative then a class-two `p`-group `H` with cyclic centre is commutative

This is the "abelian end" of the analysis of `p`-groups of symplectic type (Feit–Thompson §3,
Gorenstein Theorem 5.4.9).  Let `H` be a finite `p`-group, `p` an odd prime, of nilpotency class
at most two (`⁅H, H⁆ ≤ Z(H)`) in which every `p`-th power is central (`x ^ p ∈ Z(H)`), whose
centre is cyclic, and whose abelian characteristic subgroups are all cyclic.  Then

  `Ω₁(H) = ⟨x ∈ H | x ^ p = 1⟩` commutative  ⟹  `H` commutative.

The proof runs as follows.

* `Ω₁(H)` is characteristic (it is `omega1 H p ⊤`), and it is commutative by hypothesis, so it is
  cyclic by `hdc`; write `Ω₁(H) = ⟨a⟩`.
* Since `H` has class at most two and every `p`-th power is central, every commutator has order
  dividing `p` (`commutator_pow_eq_one_of_pow_mem_center`), so `⁅H, H⁆ ≤ Ω₁(H)`, while
  `Ω₁(H) = {x | x ^ p = 1}` (`omega1_eq_pow_eq_one_of_class_two`).  In particular `a ^ p = 1`
  and `|Ω₁(H)| ∣ p`.
* If `H` is not commutative then `⁅H, H⁆ ≠ 1`, hence `Ω₁(H) ≠ 1`, so `|Ω₁(H)| = p` and
  `⁅H, H⁆ = Ω₁(H)` (its order divides `p` and is not `1`).  Thus `Ω₁(H) = ⁅H, H⁆ ≤ Z(H)`
  and `Ω₁(H)` is central.
* The `p`-th power map `℘ : H →* Z(H)`, `x ↦ x ^ p`, is a homomorphism (class two plus `p`
  odd), its kernel is `Ω₁(H) ≤ Z(H)`, and its image is contained in the cyclic group `Z(H)`.
  A homomorphism onto a cyclic group with kernel contained in the centre makes its domain
  commutative, so `H` is commutative.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup.Symplectic

variable {G : Type*} [Group G]

/-- In a group of nilpotency class at most two in which every `p`-th power is central, every
commutator has order dividing `p`.  (Class two gives `⁅a,b⁆ ^ p = ⁅a ^ p, b⁆`, and `a ^ p` is
central, so that commutator is trivial.) -/
theorem commutator_pow_eq_one_of_pow_mem_center {p : ℕ}
    (hclass : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ Subgroup.center G)
    (hquot : ∀ x : G, x ^ p ∈ Subgroup.center G) (a b : G) : ⁅a, b⁆ ^ p = 1 := by
  have hmem : ⁅a, b⁆ ∈ Subgroup.center G :=
    hclass (Subgroup.commutator_mem_commutator trivial trivial)
  have hc : Commute a ⁅a, b⁆ := Subgroup.mem_center_iff.mp hmem a
  rw [← (hc.commutatorElement_pow_left p).symm]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp (hquot a) b).symm

theorem isMulCommutative_of_isMulCommutative_omega1 {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) (hHpg : IsPGroup p H)
    (hclass : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ Subgroup.center H)
    (hquot : ∀ x : H, x ^ p ∈ Subgroup.center H)
    (hcyc : ∃ a : H, Subgroup.center H = Subgroup.zpowers a)
    (hdc : ∀ A : Subgroup H, A.Characteristic → IsMulCommutative A → ∃ a : H, A = Subgroup.zpowers a)
    (hab : IsMulCommutative (Work.PGroup.omega1 H p ⊤)) : IsMulCommutative H := by
  classical
  by_cases hHnab : IsMulCommutative H
  · exact hHnab
  · haveI : Fact p.Prime := ⟨hp⟩
    -- commutators have order dividing `p`
    have hcomm : ∀ a b : H, ⁅a, b⁆ ^ p = 1 := fun a b =>
      commutator_pow_eq_one_of_pow_mem_center hclass hquot a b
    -- `Ω₁(H)` is the set of elements of `p`-th power one
    have hΩmem : ∀ x : H, x ∈ Work.PGroup.omega1 H p ⊤ ↔ x ^ p = 1 :=
      omega1_eq_pow_eq_one_of_class_two hp hodd hclass hquot
    -- `Ω₁(H)` is characteristic, hence cyclic by `hdc`
    have hcharTop : (⊤ : Subgroup H).Characteristic := by
      rw [Subgroup.characteristic_iff_map_eq]
      intro φ
      simp
    have hΩchar : (Work.PGroup.omega1 H p ⊤).Characteristic :=
      Work.PGroup.omega1_characteristic p hcharTop
    obtain ⟨a, ha⟩ := hdc _ hΩchar hab
    have haΩ : a ∈ Work.PGroup.omega1 H p ⊤ := ha ▸ Subgroup.mem_zpowers a
    have hap : a ^ p = 1 := (hΩmem a).mp haΩ
    -- `⁅H, H⁆ ≤ Ω₁(H)` and `⁅H, H⁆ ≠ 1`
    have hH'le : (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H) ≤
        Work.PGroup.omega1 H p ⊤ := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      exact (hΩmem _).mpr (hcomm x y)
    have hH'ne : (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H) ≠ ⊥ := by
      intro hbot
      refine hHnab ?_
      rw [isMulCommutative_iff]
      intro x y
      have h1 := commutator_eq_bot_iff_le_centralizer.mp hbot
        (show x ∈ (⊤ : Subgroup H) from trivial)
      exact ((Subgroup.mem_centralizer_iff.mp h1) y trivial).symm
    -- `a ≠ 1`, so `Ω₁(H)` has order `p` and `⁅H, H⁆ = Ω₁(H) ≤ Z(H)`
    obtain ⟨b, hbne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH'ne
    have ha1 : a ≠ 1 := by
      intro ha1
      have hbΩ : (b : H) ∈ Work.PGroup.omega1 H p ⊤ := hH'le b.2
      have hbot : (b : H) ∈ (⊥ : Subgroup H) := by
        rw [← Subgroup.zpowers_eq_bot.mpr ha1, ← ha]
        exact hbΩ
      exact hbne (Subtype.ext (Subgroup.mem_bot.mp hbot))
    have horder : orderOf a = p := orderOf_eq_prime hap ha1
    have hcardΩ : Nat.card ↥(Work.PGroup.omega1 H p ⊤) = p := by
      rw [ha, Nat.card_zpowers, horder]
    have hcardH' : Nat.card ↥(⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H) = p := by
      have hdvd := Subgroup.card_dvd_of_le hH'le
      rw [hcardΩ] at hdvd
      have hne : Nat.card ↥(⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H) ≠ 1 := by
        intro h1
        exact hH'ne (Subgroup.card_eq_one.mp h1)
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
      · exact absurd h hne
      · exact h
    have hΩZ : Work.PGroup.omega1 H p ⊤ ≤ Subgroup.center H :=
      (Subgroup.eq_of_le_of_card_ge hH'le (by rw [hcardΩ, hcardH'])) ▸ hclass
    -- the `p`-th power map into the cyclic centre
    haveI : IsCyclic ↥(Subgroup.center H) := by
      obtain ⟨c, hc⟩ := hcyc
      exact hc ▸ Subgroup.isCyclic_zpowers c
    let ℘ : H →* ↥(Subgroup.center H) :=
      { toFun := fun x => ⟨x ^ p, hquot x⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y =>
          Subtype.ext (pow_mul_eq_of_class_two hp hodd hclass hcomm x y) }
    have hker : ℘.ker ≤ Subgroup.center H := by
      intro x hx
      have hxp : (x : H) ^ p = 1 := by
        have h1 : (℘ x).val = 1 := congrArg Subtype.val hx
        simpa [℘] using h1
      exact hΩZ ((hΩmem x).mpr hxp)
    exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center ℘ hker

end Work.PGroup.Symplectic
