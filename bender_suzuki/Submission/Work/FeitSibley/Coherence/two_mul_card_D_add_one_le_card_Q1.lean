import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.FeitSibley.GroupTheory.D_dvd_card_sub_one
import Submission.Work.FeitSibley.Coherence.conj_map_injOn_of_fpf
import Submission.Work.FeitSibley.Coherence.isPGroup_two_of_conj_transitive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `2·|D| + 1 ≤ |Q₁|` for the Feit–Sibley data

`D` acts fixed point freely by conjugation on `Q₁` (`h.D_fpf_Q1`), and `Q₁ ⊴ H` with `D ≤ H`, so
`Q₁` is `D`-invariant.  Hence `D` acts freely on `Q₁` away from `1` and `|Q₁| = 1 + k·|D|`, where
`k ≥ 1` is the number of nontrivial orbits (`k ≥ 1` because `Q₁ ≠ ⊥`, see `h.Q1_ne_bot`).

The point of this file is to rule out the extremal case `k = 1`, i.e. `|Q₁| = |D| + 1`:

`Q₁` is a `D`-invariant subgroup of order `|D| + 1`, so `Q₁ \ {1}` has exactly `|D|` elements and
the map `d ↦ d·x·d⁻¹` is injective on `D` for `x ∈ Q₁`, `x ≠ 1`
(`conj_map_injOn_of_fpf`).  Counting cardinalities, this map is *bijective* onto `Q₁ \ {1}`: all
nonidentity elements of `Q₁` are conjugate.  Since `|D|` is odd, `|Q₁| = |D| + 1` is even, so by
Cauchy `Q₁` contains an element of order `2`; every nonidentity element of `Q₁` is conjugate to it
and therefore also has order `2`.  Thus `Q₁` has exponent `2` and is a `2`-group
(`isPGroup_two_of_conj_transitive`), contradicting `h.Q1_not_two`.

So `|Q₁| ≠ |D| + 1`, and the general counting lemma
`two_mul_card_D_add_one_le_card_of_ne` (from `Coherence/coherent_scriptS.lean`) applied to
`A = Q₁` gives `2·|D| + 1 ≤ |Q₁|`.

This is exactly the numerical input used in Peterfalvi II, Appendice XII, steps (1)–(2) (the
hypothesis `hnum` of `Work.FeitSibley.Coherence.coherent_scriptS_of_coherent_scriptSR`).
-/

namespace Work.FeitSibley.Coherence

variable {G : Type} [Group G] [Fintype G]

/-- A finite subgroup with one element removed has `|A| - 1` elements. -/
theorem card_subtype_ne_one_aux {G : Type} [Group G] [Fintype G] (A : Subgroup G) (a : ↥A) :
    Fintype.card {x : ↥A // x ≠ a} = Nat.card ↥A - 1 := by
  rw [Nat.card_eq_fintype_card]
  have h : (Finset.univ.filter (fun x : ↥A => x ≠ a)).card = Fintype.card ↥A - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
  simpa [Fintype.card_subtype] using h

/-- **`D` acts transitively by conjugation on the nonidentity elements of a `D`-invariant
`A ≤ Q₁` of order `|D| + 1`.**

`D` acts freely on `A \ {1}` (`h.D_fpf_Q1`), so for `y ∈ A`, `y ≠ 1` the map `d ↦ d·y·d⁻¹` is
injective on `D`.  Its image lies in `A \ {1}`, and both sets have `|D|` elements because
`|A| = |D| + 1`; hence the map is bijective and every nonidentity element of `A` is a conjugate
of `y`. -/
theorem conj_transitive_of_card_eq (h : Work.FeitSibley.FSData G) (A : Subgroup G)
    (hA : A ≤ h.Q1) (hAn : h.D ≤ Subgroup.normalizer (A : Set G))
    (hcard : Nat.card ↥A = Nat.card h.D + 1) :
    ∀ y z : G, y ∈ A → z ∈ A → y ≠ 1 → z ≠ 1 → ∃ d ∈ h.D, d * y * d⁻¹ = z := by
  intro y z hyA hzA hy1 hz1
  -- the conjugation map lands in `A` (which is `D`-invariant)
  have hmem : ∀ d : G, d ∈ h.D → d * y * d⁻¹ ∈ A := fun d hd =>
    (Subgroup.mem_normalizer_iff.mp (hAn hd) y).mp hyA
  -- and never hits `1` for `y ≠ 1`
  have hne : ∀ d : G, d ∈ h.D → d * y * d⁻¹ ≠ 1 := by
    intro d hd hd1
    have h1 : y = d⁻¹ * (d * y * d⁻¹) * d := by group
    rw [hd1] at h1
    exact hy1 (by simpa using h1)
  let ψ : ↥h.D → ↥A := fun d => ⟨(d : G) * y * (d : G)⁻¹, hmem (d : G) d.2⟩
  have hψne : ∀ d : ↥h.D, ψ d ≠ 1 := by
    intro d hd
    refine hne (d : G) d.2 ?_
    have h2 := congrArg Subtype.val hd
    simpa only [Subgroup.coe_one] using h2
  let φ : ↥h.D → {x : ↥A // x ≠ 1} := fun d => ⟨ψ d, hψne d⟩
  have hφval : ∀ d : ↥h.D, (((φ d : ↥A)) : G) = (d : G) * y * (d : G)⁻¹ := fun d => rfl
  have hinj : Function.Injective φ := by
    intro d e hde
    have h1 : (d : G) * y * (d : G)⁻¹ = (e : G) * y * (e : G)⁻¹ := by
      have hde' := congrArg (fun w : {x : ↥A // x ≠ 1} => (((w : ↥A) : G))) hde
      rwa [hφval d, hφval e] at hde'
    exact Subtype.ext (conj_map_injOn_of_fpf h hA hyA hy1 d.2 e.2 h1)
  -- the two finite sets have the same cardinality
  have hcardA : Fintype.card ↥A = Fintype.card ↥h.D + 1 := by
    rw [← Nat.card_eq_fintype_card (α := ↥A), ← Nat.card_eq_fintype_card (α := ↥h.D)]
    exact hcard
  have hcards : Fintype.card ↥h.D = Fintype.card {x : ↥A // x ≠ 1} := by
    rw [card_subtype_ne_one_aux A 1, Nat.card_eq_fintype_card, hcardA]
    omega
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcards⟩
  obtain ⟨d, hd⟩ := hbij.2 ⟨⟨z, hzA⟩, by
    intro hh
    refine hz1 ?_
    have h2 := congrArg Subtype.val hh
    simpa only [Subgroup.coe_one] using h2⟩
  refine ⟨(d : G), d.2, ?_⟩
  have hd' : (((φ d : ↥A)) : G) = z :=
    congrArg (fun w : {x : ↥A // x ≠ 1} => (((w : ↥A) : G))) hd
  rwa [hφval d] at hd'

/-- **`2·|D| + 1 ≤ |Q₁|`.**  See the module docstring for the argument. -/
theorem two_mul_card_D_add_one_le_card_Q1 {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) :
    2 * Nat.card h.D + 1 ≤ Nat.card h.Q1 := by
  have hAn : h.D ≤ Subgroup.normalizer (h.Q1 : Set G) := le_trans h.D_le_H h.Q1_normal_in_H
  refine two_mul_card_D_add_one_le_card_of_ne h h.Q1 le_rfl hAn h.Q1_ne_bot ?_
  -- the exceptional case `|Q₁| = |D| + 1` is impossible
  intro hcard
  have htrans := conj_transitive_of_card_eq h h.Q1 le_rfl hAn hcard
  have heven : Even (Nat.card ↥h.Q1) := by
    obtain ⟨m, hm⟩ := h.D_odd
    exact ⟨m + 1, by omega⟩
  exact h.Q1_not_two (isPGroup_two_of_conj_transitive h h.Q1 htrans heven)

end Work.FeitSibley.Coherence
