import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.abelian_split
import Submission.Work.Coprime.fixedPoints_ne_bot_of_isPGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.ThreePoints.ThmC

/-- Core of the Baer/Blackburn step: a finite group `U` acts on a finite abelian group `G` of
`p`-power order (`p` prime); `X ≤ U` has order coprime to `p` and is normal in `U`, `P ≤ U` is a
`p`-subgroup.  If the action of `X` on `G` is nontrivial, then `[G,X]` contains an element of order
exactly `p` which is fixed by `P` and not fixed by `X`. -/
theorem exists_orderOf_prime_mem_commutator_fixed {U G : Type*} [Group U] [Group G] [Finite U]
    [Finite G] [IsMulCommutative G] [MulDistribMulAction U G] {p : ℕ} (hp : p.Prime)
    {X P : Subgroup U} (hXn : (⊤ : Subgroup U) ≤ Subgroup.normalizer (X : Set U))
    (hXp : Nat.Coprime (Nat.card X) p) (hPp : IsPGroup p P) (hGp : IsPGroup p G) :
    letI : MulDistribMulAction X G := MulDistribMulAction.compHom G (Subgroup.subtype X)
    letI : MulDistribMulAction P G := MulDistribMulAction.compHom G (Subgroup.subtype P)
    FT.commutator X (⊤ : Subgroup G) ≠ ⊥ →
      ∃ g : G, g ∈ FT.commutator X (⊤ : Subgroup G) ∧ orderOf g = p ∧
        (∀ q : P, q • g = g) ∧ g ∉ FT.fixedPoints X G := by
  intro hcomm
  haveI : Fact p.Prime := ⟨hp⟩
  -- `H = [G,X]` is a nontrivial finite `p`-group.
  have hHp : IsPGroup p ↥(FT.commutator X (⊤ : Subgroup G)) := hGp.to_subgroup _
  have hHnt : Nontrivial ↥(FT.commutator X (⊤ : Subgroup G)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hcomm
  -- `P` maps `H` into itself: elementwise, via the closure description of the commutator.
  have hmem : ∀ (q : P) (y : G), y ∈ FT.commutator X (⊤ : Subgroup G) →
      q • y ∈ FT.commutator X (⊤ : Subgroup G) := by
    intro q
    have hq : (q : U) ∈ Subgroup.normalizer (X : Set U) := hXn (Subgroup.mem_top (q : U))
    let T : Subgroup G :=
      { carrier := {y : G | q • y ∈ FT.commutator X (⊤ : Subgroup G)}
        one_mem' := by
          show q • (1 : G) ∈ FT.commutator X (⊤ : Subgroup G)
          rw [smul_one]
          exact (FT.commutator X (⊤ : Subgroup G)).one_mem
        mul_mem' := by
          intro a b ha hb
          show q • (a * b) ∈ FT.commutator X (⊤ : Subgroup G)
          rw [smul_mul']
          exact (FT.commutator X (⊤ : Subgroup G)).mul_mem ha hb
        inv_mem' := by
          intro a ha
          show q • a⁻¹ ∈ FT.commutator X (⊤ : Subgroup G)
          rw [smul_inv']
          exact (FT.commutator X (⊤ : Subgroup G)).inv_mem ha }
    have hHT : FT.commutator X (⊤ : Subgroup G) ≤ T := by
      rw [FT.commutator_def']
      refine (Subgroup.closure_le T).mpr ?_
      rintro y ⟨a, x, -, rfl⟩
      show q • (x⁻¹ * (a • x)) ∈ FT.commutator X (⊤ : Subgroup G)
      have hgen : q • (x⁻¹ * (a • x)) =
          (q • x)⁻¹ * ((⟨(q : U) * (a : U) * (q : U)⁻¹,
            (Subgroup.mem_normalizer_iff.mp hq (a : U)).mp a.2⟩ : X) • (q • x)) := by
        rw [smul_mul', smul_inv']
        congr 1
        change (q : U) • ((a : U) • x) =
          ((q : U) * (a : U) * (q : U)⁻¹) • ((q : U) • x)
        rw [smul_smul (q : U) (a : U) x,
          smul_smul ((q : U) * (a : U) * (q : U)⁻¹) (q : U) x,
          show (q : U) * (a : U) * (q : U)⁻¹ * (q : U) = (q : U) * (a : U) by group]
      rw [hgen]
      exact Subgroup.subset_closure ⟨_, q • x, trivial, rfl⟩
    intro y hy
    exact hHT hy
  -- The induced action of `P` on the `p`-group `H` (built by hand, to keep the action visible).
  let instH : MulDistribMulAction P ↥(FT.commutator X (⊤ : Subgroup G)) :=
    { smul := fun q y => ⟨q • (y : G), hmem q (y : G) y.2⟩
      one_smul := fun y => Subtype.ext (one_smul P (y : G))
      mul_smul := fun q₁ q₂ y => Subtype.ext (mul_smul q₁ q₂ (y : G))
      smul_one := fun q => Subtype.ext (smul_one q)
      smul_mul := fun q y₁ y₂ => Subtype.ext (smul_mul' q (y₁ : G) (y₂ : G)) }
  letI : MulDistribMulAction P ↥(FT.commutator X (⊤ : Subgroup G)) := instH
  -- `C_H(P) ≠ 1`, so it contains an element of order `p`.
  have hfix : FT.fixedPoints P ↥(FT.commutator X (⊤ : Subgroup G)) ≠ ⊥ :=
    Work.Coprime.fixedPoints_ne_bot_of_isPGroup P p hp hPp hHp hHnt
  obtain ⟨w, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfix
  have hw1 : (w : ↥(FT.commutator X (⊤ : Subgroup G))) ≠ 1 := fun h => hwne (Subtype.ext h)
  have hwfix : ∀ q : P, q • (w : ↥(FT.commutator X (⊤ : Subgroup G)))
      = (w : ↥(FT.commutator X (⊤ : Subgroup G))) := w.2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hHp) (w : ↥(FT.commutator X (⊤ : Subgroup G)))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hw1 (orderOf_eq_one_iff.mp hk)
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  -- A suitable power of `w` has order exactly `p`.
  have hx1 : ((w : ↥(FT.commutator X (⊤ : Subgroup G))) ^ p ^ k') ≠ 1 := by
    intro h
    have hdvd : orderOf (w : ↥(FT.commutator X (⊤ : Subgroup G))) ∣ p ^ k' :=
      (orderOf_dvd_iff_pow_eq_one).mpr h
    rw [hk] at hdvd
    have hpos : 0 < p ^ k' := pow_pos hp.pos k'
    have hle : p ^ (k' + 1) ≤ p ^ k' := Nat.le_of_dvd hpos hdvd
    have hlt : p ^ k' < p ^ (k' + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self k')
    omega
  have hxord : orderOf ((w : ↥(FT.commutator X (⊤ : Subgroup G))) ^ p ^ k') = p := by
    refine orderOf_eq_prime ?_ hx1
    rw [← pow_mul, ← pow_succ, ← hk, pow_orderOf_eq_one]
  refine ⟨(((w : ↥(FT.commutator X (⊤ : Subgroup G))) ^ p ^ k' :
      ↥(FT.commutator X (⊤ : Subgroup G))) : G),
      ((w : ↥(FT.commutator X (⊤ : Subgroup G))) ^ p ^ k').2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hxord]
  · intro q
    exact congrArg Subtype.val (show q • ((w : ↥(FT.commutator X (⊤ : Subgroup G))) ^ p ^ k')
        = ((w : ↥(FT.commutator X (⊤ : Subgroup G))) ^ p ^ k') by
      rw [smul_pow', hwfix q])
  · intro hmem'
    have hcopG : Nat.Coprime (Nat.card X) (Nat.card G) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hGp
      rw [hn]
      exact hXp.pow_right n
    have hbot : FT.fixedPoints X G ⊓ FT.commutator X (⊤ : Subgroup G) = ⊥ :=
      (Work.Coprime.abelian_split X hcopG).disjoint.eq_bot
    have hmem_inf : (((w : ↥(FT.commutator X (⊤ : Subgroup G))) ^ p ^ k' :
        ↥(FT.commutator X (⊤ : Subgroup G))) : G)
        ∈ FT.fixedPoints X G ⊓ FT.commutator X (⊤ : Subgroup G) :=
      ⟨hmem', ((w : ↥(FT.commutator X (⊤ : Subgroup G))) ^ p ^ k').2⟩
    rw [hbot] at hmem_inf
    exact hx1 (Subtype.ext (Subgroup.mem_bot.mp hmem_inf))

end Work.ThreePoints.ThmC
