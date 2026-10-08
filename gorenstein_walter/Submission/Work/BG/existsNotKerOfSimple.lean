import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.ThmABCCharDefs

/-!
# `Work.BG.existsNotKerOfSimple`

A `±Irr(G)`-class function `χ` of a finite simple group `G` whose inner product with the trivial
character vanishes cannot be constant on a nontrivial subgroup `K`.

Mathematically: `χ` (or `-χ`) is the character of an irreducible representation `ρ`.  The set
`{g | χ g = χ 1}` is the kernel `ker ρ` of that representation (via the equality case of the
triangle inequality, `rep_eq_id_of_character_eq_one`), a normal subgroup.  If a nontrivial `K`
were contained in it, simplicity would force `ker ρ = ⊤`, i.e. `χ` constant on `G`; then
`inner χ triv = χ 1 ≠ 0`, contradicting the hypothesis.
-/

namespace Work.BG

open OddOrder.RepresentationTheory
open scoped BigOperators

/-- An irreducible character has nonzero degree `φ 1`. -/
private lemma irr_apply_one_ne_zero {G : Type} [Group G] [Finite G]
    {φ : OddOrder.RepresentationTheory.ClassFunction G ℂ}
    (hφ : OddOrder.RepresentationTheory.IsIrreducibleCharacter φ) : φ 1 ≠ 0 := by
  obtain ⟨n, hpos, hval, _⟩ := hφ.exists_natDegree_charValue_one_dvd_card (G := G)
  rw [hval]
  exact_mod_cast hpos.ne'

/-- A `±Irr(G)`-class function has nonzero value at `1`. -/
private lemma pmIrr_apply_one_ne_zero {G : Type} [Group G] [Finite G]
    {χ : OddOrder.RepresentationTheory.ClassFunction G ℂ} (h : IsPmIrr χ) : χ 1 ≠ 0 := by
  rcases h with h | h
  · exact irr_apply_one_ne_zero h
  · have hh := irr_apply_one_ne_zero h
    have : -χ 1 ≠ 0 := hh
    exact neg_ne_zero.mp this

/-- If `χ` is constant with value `χ 1`, its inner product with the trivial character is `χ 1`. -/
private lemma inner_trivialClassFunction_of_const {G : Type} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (h : ∀ g, χ g = χ 1) :
    OddOrder.RepresentationTheory.ClassFunction.inner χ
      (OddOrder.RepresentationTheory.trivialClassFunction G) = χ 1 := by
  rw [OddOrder.RepresentationTheory.ClassFunction.inner_eq_inv_card_mul_innerSum]
  have hsum : OddOrder.RepresentationTheory.ClassFunction.innerSum χ
      (OddOrder.RepresentationTheory.trivialClassFunction G) = (Nat.card G : ℂ) * χ 1 := by
    simp only [OddOrder.RepresentationTheory.ClassFunction.innerSum,
      OddOrder.RepresentationTheory.trivialClassFunction_apply, star_one, mul_one]
    rw [Finset.sum_congr rfl (fun g _ => h g)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [hsum, ← mul_assoc, invOf_mul_self, one_mul]

/-- **Kernel argument.**  An irreducible character of a finite group that is constant (equal to
its degree) on a nontrivial subgroup `K` of a *simple* group is constant on all of `G`. -/
private lemma irr_const_of_const_on_subgroup {G : Type} [Group G] [Finite G]
    (K : Subgroup G) (φ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hφ : OddOrder.RepresentationTheory.IsIrreducibleCharacter φ)
    (hKconst : ∀ k ∈ K, φ k = φ 1) (hKne : K ≠ ⊥) (hsimple : IsSimpleGroup G) :
    ∀ g : G, φ g = φ 1 := by
  obtain ⟨V, _, _, _, ρ, hirr, hchar⟩ := hφ
  -- `K` lies in the kernel of the witnessing representation.
  have hNle : K ≤ ρ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have hc : ρ.character k = ρ.character 1 := by
      rw [← congrFun hchar k, ← congrFun hchar 1, hKconst k hk]
    have hid : ρ k = LinearMap.id := rep_eq_id_of_character_eq_one ρ hc
    rw [hid]
    rfl
  -- simplicity: the (normal) kernel is `⊥` or `⊤`; `K ≠ ⊥` rules out `⊥`.
  have hNtop : (ρ.ker : Subgroup G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker) with h | h
    · exact absurd (le_bot_iff.mp (h ▸ hNle)) hKne
    · exact h
  intro g
  have hg : g ∈ ρ.ker := by rw [hNtop]; trivial
  have hg' : ρ g = (1 : V →ₗ[ℂ] V) := MonoidHom.mem_ker.mp hg
  have hchar_eq : ρ.character g = ρ.character 1 := by
    simp only [Representation.character]
    rw [hg', show ρ (1 : G) = (1 : V →ₗ[ℂ] V) from map_one ρ]
  rw [congrFun hchar g, congrFun hchar 1, hchar_eq]

theorem existsNotKerOfSimple {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (K : Subgroup G) (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) :
    K ≠ ⊥ → IsSimpleGroup G → Work.BG.IsPmIrr χ →
    OddOrder.RepresentationTheory.ClassFunction.inner χ
      (OddOrder.RepresentationTheory.trivialClassFunction G) = 0 →
    ∃ k ∈ K, χ k ≠ χ 1 := by
  intro hKne hsimple hpm hinner
  by_contra hcon
  push Not at hcon
  have hdeg : χ 1 ≠ 0 := pmIrr_apply_one_ne_zero hpm
  -- Reduce `±Irr` to a genuine irreducible character.
  have hconstχ : ∀ g : G, χ g = χ 1 := by
    rcases hpm with hirr | hirr
    · exact irr_const_of_const_on_subgroup K χ hirr hcon hKne hsimple
    · have hc : ∀ k ∈ K, (-χ) k = (-χ) 1 := by
        intro k hk
        rw [OddOrder.RepresentationTheory.ClassFunction.neg_apply,
          OddOrder.RepresentationTheory.ClassFunction.neg_apply, hcon k hk]
      intro g
      have h := irr_const_of_const_on_subgroup K (-χ) hirr hc hKne hsimple g
      simpa using h
  have hinner_eq : OddOrder.RepresentationTheory.ClassFunction.inner χ
      (OddOrder.RepresentationTheory.trivialClassFunction G) = χ 1 :=
    inner_trivialClassFunction_of_const χ hconstχ
  rw [hinner_eq] at hinner
  exact hdeg hinner

end Work.BG
