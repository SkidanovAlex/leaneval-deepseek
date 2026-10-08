/-
Area `A7REC`, file `Char/c1bDegree.lean`: the **degree leaf** of the `C1b` design.

`c1bDegree` says that every non-trivial irreducible complex character `χ` of a simple group
`G` with `Nat.card G = 2520` has degree `χ(1) ∈ ℕ` at least `2`.  This is the elementary
representation-theoretic input that `A7C1bProp` (`Char/C1b.lean`) uses as `∀ i, 2 ≤ f i`
(equivalently: the character table of the underlying `G ≃* A₇` has a `1` only in the trivial
column).

The mathematics: `G` is simple of order `2520`, so it is *non-abelian* (a simple *abelian*
group has prime order, and `2520` is not prime) — here derived through Cauchy's theorem:
`2 ∣ 2520` gives an element `z` of order `2`, whose (therefore non-trivial, proper) cyclic
subgroup `⟨z⟩` would be normal in an abelian group.  A non-abelian simple group is perfect
(`⁅G,G⁆` is normal, hence `⊥` or `⊤`; `⊥` would make `G` abelian), and a degree-one
irreducible character `θ` is a homomorphism `G →* ℂˣ` (via
`IsIrreducibleCharacter.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one`), hence
trivial on `⁅G,G⁆ = ⊤`: `θ` is the trivial character.  So `χ ≠ 1` forces `χ(1) ≠ 1`, and
`χ(1) > 0` is a positive integer.

The two supporting facts are proved here:

* `exists_noncommuting_pair` — a simple group of order `2520` is non-abelian;
* `degree_ge_two` — a non-trivial irreducible character of a finite non-abelian simple group
  has degree at least `2`.
-/
import Mathlib
import Submission.Work.A7REC.Char.c1bLib
import Submission.OddOrder.GroupTheory.RepresentationTheory.LinearCharacter

set_option autoImplicit false

namespace Work.A7REC.Char

open OddOrder.RepresentationTheory

/-- **A simple group of order `2520` is non-abelian.**

Assume `G` abelian.  Since `2 ∣ 2520`, Cauchy's theorem produces `z : G` with `orderOf z = 2`.
In an abelian group `⟨z⟩` is normal, and `⟨z⟩ ≅ ℤ/2` is neither `⊥` (as `z ≠ 1`) nor `⊤`
(as `Nat.card G = 2520 ≠ 2`), contradicting the simplicity of `G`. -/
lemma exists_noncommuting_pair {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hcard : Nat.card G = 2520) : ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  push_neg at h
  haveI : IsMulCommutative G := ⟨⟨fun a b => h a b⟩⟩
  haveI : Fintype G := Fintype.ofFinite G
  have hdvd : 2 ∣ Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card (G := G) 2 hdvd
  have hcard_zp : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hz]
  haveI : IsSimpleGroup G := hsimple
  haveI : (Subgroup.zpowers z).Normal := Subgroup.normal_of_isMulCommutative _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers z) with hbot | htop
  · rw [hbot, Subgroup.card_bot] at hcard_zp
    norm_num at hcard_zp
  · rw [htop, Subgroup.card_top, hcard] at hcard_zp
    norm_num at hcard_zp

/-- **The degree of a non-trivial irreducible character of a finite non-abelian simple group
is at least `2`.**

If `(χ : ClassFunction G ℂ) 1 = 1` then `χ` is a degree-one irreducible character: it is
multiplicative, hence (as `G` is finite) the linear character of a homomorphism
`G →* ℂˣ`, and a degree-one irreducible character vanishes on commutators
(`IsIrreducibleCharacter.apply_eq_one_of_mem_commutator_of_apply_one_eq_one`).  Now
`⁅G,G⁆` is normal in the simple group `G`, so it is `⊥` or `⊤`: the first case makes `G`
abelian, contradicting `hnab`; in the second case `χ` is `1` on all of `G`, i.e. `χ` is the
trivial character, contradicting `hne`.  Hence `χ(1) ≠ 1`, and `χ(1) > 0` gives `2 ≤ χ(1)`. -/
lemma degree_ge_two {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (χ : IrreducibleCharacter G)
    (hne : χ ≠ trivialIrreducibleCharacter G) (d : ℕ)
    (hd : (χ : ClassFunction G ℂ) 1 = (d : ℂ)) : 2 ≤ d := by
  haveI : IsSimpleGroup G := hsimple
  have key : (χ : ClassFunction G ℂ) 1 = 1 → χ = trivialIrreducibleCharacter G := by
    intro h1
    have hcomm : ∀ n ∈ commutator G, (χ : ClassFunction G ℂ) n = 1 := fun n hn =>
      IsIrreducibleCharacter.apply_eq_one_of_mem_commutator_of_apply_one_eq_one
        χ.isIrreducible h1 hn
    haveI : (commutator G).Normal := Subgroup.commutator_normal ⊤ ⊤
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hbot | htop
    · obtain ⟨a, b, hab⟩ := hnab
      have hcomm' : IsMulCommutative G := (commutator_eq_bot_iff G).mp hbot
      letI := hcomm'
      exact absurd (IsMulCommutative.is_comm.comm a b) hab
    · apply IrreducibleCharacter.ext
      rw [IrreducibleCharacter.coe_trivialIrreducibleCharacter]
      ext g
      rw [trivialClassFunction_apply]
      exact hcomm g (htop ▸ Subgroup.mem_top g)
  obtain ⟨d', hd'pos, hd'⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  have hdd' : d = d' := Nat.cast_injective (by rw [← hd, hd'])
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [Nat.cast_one] at hd
    exact hne (key hd)
  omega

theorem c1bDegree {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hcard : Nat.card G = 2520) (χ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hne : χ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter G) :
    ∃ f : ℕ, 2 ≤ f ∧ (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) 1 = (f : ℂ) := by
  obtain ⟨f, -, hf⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  exact ⟨f, degree_ge_two hsimple (exists_noncommuting_pair hsimple hcard) χ hne f hf, hf⟩

end Work.A7REC.Char
