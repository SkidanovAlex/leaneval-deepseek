import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All
import Submission.Work.Clifford.All
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.card_classes_meeting_Q
import Submission.Work.ZassenhausTwoGroup.card_H_classes_eq_card_induced
import Submission.Work.ZassenhausTwoGroup.feit_lemma3_5_classes

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `bf35_chars`: Feit's Lemma 3.5 in character form

In the rank-one Zassenhaus set-up `H = Q ⋊ D` (`D = twoPoint H t`) of a finite simple group `G`
with `Q` not a `2`-group, Feit (*On a class of doubly transitive permutation groups*, Illinois J.
Math. **4** (1960), Lemma 3.5, p. 182) shows that `G` has at least `q = |D|` non-trivial
irreducible characters which are not exceptional characters associated with `Q`; in the form used
by his §3 (and needed by the area's derivation of `χ₁(1) = |D|`) this is the statement proved
here:

> for every `χ` that is injective across the fibres of `ζ ↦ Ind_Q^G ζ` on the non-trivial
> irreducible characters of `Q`, the number of `ψ ∈ Irr G` with `ψ ≠ 1` and `ψ ≠ χ ζ` for all
> non-trivial `ζ ∈ Irr Q` is at least `|twoPoint H t|`.

## The count

Write `q = |D| = |twoPoint H t|`, `A` for the number of `G`-classes meeting `Q ∖ 1`, `B` for the
number of `G`-classes of non-identity elements which are not conjugate into `Q`, and
`N = #{Ind_Q^G ζ | ζ ∈ Irr Q, ζ ≠ 1}`.  The proof combines four counts.

* `card_Irr_eq_card_conjClasses`: `|Irr G| = k(G)`, the number of conjugacy classes.
* `one_add_le_card_conjClasses`: every class is the class of `1`, meets `Q ∖ 1`, or avoids all
  conjugates of `Q`; these three families are disjoint, so `1 + A + B ≤ k(G)`.
* `feit_lemma3_5_classes` (Feit's Lemma 3.5, elementary by his footnote 9) gives `q ≤ B`.
* `card_classes_meeting_Q` + `card_H_classes_eq_card_induced` (the fusion count of `Q ∖ 1` and
  Brauer's permutation lemma for the Frobenius group `H = Q ⋊ D`) give `A = N`.
* `card_badChar_le`: since `χ` is constant on the fibres of `ζ ↦ Ind_Q^G ζ`, the characters
  excluded in the statement — the trivial one and the `χ ζ` — are at most `1 + N` in number.

Hence the number of good characters is `k(G) - #{excluded} ≥ (1 + A + B) - (1 + N) = A + B - N
= B ≥ q`, which is the claim (the subtraction bookkeeping is pure arithmetic, closed by `omega`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

variable {G : Type} [Group G] [Fintype G]

/-- The `G`-conjugacy classes of non-identity elements which are not conjugate into `Q`: the
classes counted by `feit_lemma3_5_classes`. -/
private noncomputable abbrev ClsAvoidQ (Q : Subgroup G) : Type :=
  {c : ConjClasses G // ∀ x ∈ c.carrier, x ≠ 1 ∧ ∀ g : G, g * x * g⁻¹ ∉ Q}

/-- The non-trivial irreducible characters of `Q`. -/
private noncomputable abbrev IrrNT (Q : Subgroup G) [Fintype ↥Q] : Finset (↥Q → ℂ) :=
  (Work.CharCore.Irr ↥Q).filter (fun ζ => ζ ≠ 1)

/-- The number of irreducible characters of `G` is the number of conjugacy classes of `G`. -/
private theorem card_Irr_eq_card_conjClasses_of_clifford :
    (Work.CharCore.Irr G).card = Nat.card (ConjClasses G) := by
  have hset : (Work.CharCore.Irr G : Set (G → ℂ)) = Work.Clifford.Irr G := by
    ext χ
    exact charCore_mem_iff_clifford χ
  have h1 : Nat.card {χ : G → ℂ // χ ∈ Work.Clifford.Irr G} = (Work.CharCore.Irr G).card := by
    rw [← hset]
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [← h1]
  exact Work.Clifford.card_Irr_eq_card_conjClasses

/-- Collapsing a class to "the class of `1`", "meets `Q ∖ 1`" or "avoids `Q`", for the counting
of `one_add_le_card_conjClasses`. -/
private def threePartMap (Q : Subgroup G) :
    Fin 1 ⊕ (ClassesMeetingQ Q ⊕ ClsAvoidQ Q) → ConjClasses G
  | Sum.inl _ => ConjClasses.mk 1
  | Sum.inr (Sum.inl c) => c.1
  | Sum.inr (Sum.inr c) => c.1

/-- **The three-part count.**  Every `G`-conjugacy class is either the class of `1`, meets
`Q ∖ 1`, or consists of non-identity elements none of whose conjugates lie in `Q`; the three
families are disjoint, so their sizes add up to at most `k(G)`. -/
private theorem one_add_le_card_conjClasses (Q : Subgroup G) :
    1 + Nat.card (ClassesMeetingQ Q) + Nat.card (ClsAvoidQ Q) ≤ Nat.card (ConjClasses G) := by
  classical
  have hinj : Function.Injective (threePartMap Q) := by
    intro p q hpq
    rcases p with _ | (c | c) <;> rcases q with _ | (d | d) <;>
      dsimp only [threePartMap] at hpq
    · exact congrArg Sum.inl (Subsingleton.elim _ _)
    · exfalso
      obtain ⟨x, hx, -, hx1⟩ := d.2
      refine hx1 (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp ?_))
      exact (ConjClasses.mem_carrier_iff_mk_eq.mp hx).trans hpq.symm
    · exfalso
      have h1 : (1 : G) ∈ d.1.carrier := hpq ▸ (ConjClasses.mem_carrier_mk (a := (1 : G)))
      exact (d.2 1 h1).1 rfl
    · exfalso
      obtain ⟨x, hx, -, hx1⟩ := c.2
      refine hx1 (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp ?_))
      exact (ConjClasses.mem_carrier_iff_mk_eq.mp hx).trans hpq
    · simp only [Sum.inr.injEq, Sum.inl.injEq]
      exact Subtype.ext hpq
    · exfalso
      obtain ⟨x, hx, hxQ, -⟩ := c.2
      have hx' : x ∈ d.1.carrier := hpq ▸ hx
      have h3 := (d.2 x hx').2 1
      simp only [one_mul, inv_one, mul_one] at h3
      exact h3 hxQ
    · exfalso
      have h1 : (1 : G) ∈ c.1.carrier := hpq.symm ▸ (ConjClasses.mem_carrier_mk (a := (1 : G)))
      exact (c.2 1 h1).1 rfl
    · exfalso
      obtain ⟨x, hx, hxQ, -⟩ := d.2
      have hx' : x ∈ c.1.carrier := hpq.symm ▸ hx
      have h3 := (c.2 x hx').2 1
      simp only [one_mul, inv_one, mul_one] at h3
      exact h3 hxQ
    · simp only [Sum.inr.injEq]
      exact Subtype.ext hpq
  have hcard := Nat.card_le_card_of_injective (threePartMap Q) hinj
  have h1 : Nat.card (Fin 1) = 1 := by rw [Nat.card_eq_fintype_card]; simp
  rw [Nat.card_sum, Nat.card_sum, h1] at hcard
  omega

/-- **Feit's Lemma 3.5 as a class count.**  At least `|twoPoint H t|` conjugacy classes of `G`
avoid all conjugates of `Q`. -/
private theorem card_twoPoint_le_card_clsAvoidQ {H Q : Subgroup G} {t : G} [IsSimpleGroup G]
    (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H) (hQ2 : ¬ IsPGroup 2 Q) :
    Nat.card (Submission.Blueprint.twoPoint H t) ≤ Nat.card (ClsAvoidQ Q) := by
  classical
  refine (feit_lemma3_5_classes H Q t h hZ hQ2).trans ?_
  refine Nat.card_le_card_of_injective
    (fun c : {c : ConjClasses G // ∀ x ∈ c.carrier, goodPred Q x} =>
      (⟨c.1, ?_⟩ : ClsAvoidQ Q)) ?_
  · intro x hx
    have h := c.2 x hx
    rw [goodPred] at h
    exact ⟨h.1, h.2.2.2⟩
  · intro c d hcd
    exact Subtype.ext (congrArg (fun z : ClsAvoidQ Q => (z : ConjClasses G)) hcd)

/-- **The excluded characters are few.**  The irreducible characters of `G` which are either
trivial or of the form `χ ζ` (`ζ ∈ Irr Q`, `ζ ≠ 1`) number at most `1 + N`, where
`N = #{Ind_Q^G ζ}`: since `χ` is constant on the fibres of the induction map (hypothesis
`hχorb`), the image of `χ` on the non-trivial irreducible characters of `Q` is no larger than the
image of `ζ ↦ Ind_Q^G ζ`. -/
private theorem card_badChar_le {Q : Subgroup G} [Fintype ↥Q] (χ : (↥Q → ℂ) → G → ℂ)
    (hχorb : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ = Work.Induction.indFun Q ζ' → χ ζ = χ ζ') :
    ((Work.CharCore.Irr G).filter (fun ψ => ¬ (ψ ≠ (fun _ => (1 : ℂ)) ∧
      ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ψ ≠ χ ζ))).card ≤
      1 + ((IrrNT Q).image (fun ζ => Work.Induction.indFun (G := G) Q ζ)).card := by
  classical
  -- a section of the induction map on `IrrNT Q`
  let sel : (G → ℂ) → (↥Q → ℂ) := fun y =>
    if hy : y ∈ (IrrNT Q).image (fun ζ => Work.Induction.indFun (G := G) Q ζ)
      then (Finset.mem_image.mp hy).choose else 0
  have hsel : ∀ y (hy : y ∈ (IrrNT Q).image (fun ζ => Work.Induction.indFun (G := G) Q ζ)),
      sel y ∈ IrrNT Q ∧ Work.Induction.indFun (G := G) Q (sel y) = y := by
    intro y hy
    have hspec := (Finset.mem_image.mp hy).choose_spec
    simpa only [sel, dif_pos hy] using hspec
  -- the trivial character and the `χ ζ` cover the excluded ones
  have hsub : ((Work.CharCore.Irr G).filter (fun ψ => ¬ (ψ ≠ (fun _ => (1 : ℂ)) ∧
      ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ψ ≠ χ ζ))) ⊆
      insert (fun _ => (1 : ℂ)) ((IrrNT Q).image (fun ζ => χ ζ)) := by
    intro ψ hψ
    rw [Finset.mem_filter] at hψ
    obtain ⟨-, hψnot⟩ := hψ
    rw [Finset.mem_insert]
    by_cases h1 : ψ = (fun _ => (1 : ℂ))
    · exact Or.inl h1
    · refine Or.inr ?_
      refine Finset.mem_image.mpr ?_
      rw [not_and_or] at hψnot
      rcases hψnot with h | h
      · exact absurd h1 h
      · push_neg at h
        obtain ⟨ζ, hζIrr, hζ1, hζeq⟩ := h
        exact ⟨ζ, by rw [IrrNT, Finset.mem_filter]; exact ⟨hζIrr, hζ1⟩, hζeq.symm⟩
  have hcd := Finset.card_le_card hsub
  have hins := Finset.card_insert_le (fun _ => (1 : ℂ)) ((IrrNT Q).image (fun ζ => χ ζ))
  -- `χ` does not have more values than the induction map on `IrrNT Q`
  have himg : ((IrrNT Q).image (fun ζ => χ ζ)).card ≤
      ((IrrNT Q).image (fun ζ => Work.Induction.indFun (G := G) Q ζ)).card := by
    have h1 : ((IrrNT Q).image (fun ζ => χ ζ)) ⊆
        Finset.image (fun y => χ (sel y))
          ((IrrNT Q).image (fun ζ => Work.Induction.indFun (G := G) Q ζ)) := by
      intro ψ hψ
      obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.mp hψ
      have hy : Work.Induction.indFun (G := G) Q ζ ∈
          (IrrNT Q).image (fun ζ => Work.Induction.indFun (G := G) Q ζ) :=
        Finset.mem_image.mpr ⟨ζ, hζ, rfl⟩
      refine Finset.mem_image.mpr ⟨Work.Induction.indFun (G := G) Q ζ, hy, ?_⟩
      obtain ⟨hmem, heq⟩ := hsel (Work.Induction.indFun (G := G) Q ζ) hy
      rw [IrrNT, Finset.mem_filter] at hmem
      rw [IrrNT, Finset.mem_filter] at hζ
      exact hχorb (sel (Work.Induction.indFun (G := G) Q ζ)) hmem.1 hmem.2 ζ hζ.1 hζ.2 heq
    calc ((IrrNT Q).image (fun ζ => χ ζ)).card
        ≤ (Finset.image (fun y => χ (sel y))
            ((IrrNT Q).image (fun ζ => Work.Induction.indFun (G := G) Q ζ))).card :=
          Finset.card_le_card h1
      _ ≤ ((IrrNT Q).image (fun ζ => Work.Induction.indFun (G := G) Q ζ)).card :=
          Finset.card_image_le
  omega

theorem bf35_chars {G : Type} [Group G] [Fintype G] [IsSimpleGroup G] (H Q : Subgroup G) [Fintype ↥Q] (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) (χ : (↥Q → ℂ) → G → ℂ)
    (hχirr : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → χ ζ ∈ Work.CharCore.Irr G)
    (hχrel : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' → χ ζ ≠ χ ζ')
    (hχorb : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ = Work.Induction.indFun Q ζ' → χ ζ = χ ζ') :
    Nat.card (Submission.Blueprint.twoPoint H t) ≤
      ((Work.CharCore.Irr G).filter (fun ψ => ψ ≠ (fun _ => (1 : ℂ)) ∧
        ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ψ ≠ χ ζ)).card := by
  classical
  -- `|Irr G| = k(G)`
  have hIrr : (Work.CharCore.Irr G).card = Nat.card (ConjClasses G) :=
    card_Irr_eq_card_conjClasses_of_clifford
  -- `1 + A + B ≤ k(G)`, where `A` counts the classes meeting `Q ∖ 1` and `B` the classes
  -- avoiding `Q`
  have hthree : 1 + Nat.card (ClassesMeetingQ Q) + Nat.card (ClsAvoidQ Q) ≤
      Nat.card (ConjClasses G) := one_add_le_card_conjClasses Q
  -- `A = N`: fusion for `Q ∖ 1` plus Brauer's permutation lemma for `H = Q ⋊ D`
  have hAN : ((IrrNT Q).image (fun ζ => Work.Induction.indFun (G := G) Q ζ)).card ≤
      Nat.card (ClassesMeetingQ Q) := by
    have hB2 : Nat.card (HClassesMeetingQ H Q) = Nat.card
        ((((IrrNT Q).image (fun ζ => Work.Induction.indFun (G := G) Q ζ)) : Finset (G → ℂ)) :
          Set (G → ℂ)) := by
      rw [IrrNT]
      exact card_H_classes_eq_card_induced H Q t h hZ
    have hB1 : Nat.card (HClassesMeetingQ H Q) = Nat.card (ClassesMeetingQ Q) :=
      (card_classes_meeting_Q H Q t h hZ).symm
    rw [← hB1, hB2, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  -- Feit's Lemma 3.5: `|D| ≤ B`
  have hB : Nat.card (Submission.Blueprint.twoPoint H t) ≤ Nat.card (ClsAvoidQ Q) :=
    card_twoPoint_le_card_clsAvoidQ h hZ hQ2
  -- the trivial character and the `χ ζ` are at most `1 + N` characters
  have hE := card_badChar_le (G := G) (Q := Q) χ hχorb
  -- the good characters are the complement of those
  have hSE := Finset.card_filter_add_card_filter_not
    (s := Work.CharCore.Irr G)
    (p := fun ψ : G → ℂ => ψ ≠ (fun _ => (1 : ℂ)) ∧
      ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ψ ≠ χ ζ)
  omega

end Work.ZassenhausTwoGroup
