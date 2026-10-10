import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.Motivic.cInv_add_defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- **The weight of an inserted point.**  For a finite set `s` of points not containing `a`, the
weight of `insert a s` with respect to a test point `w` is the weight of `s` plus one when the
residue field of `a` is `𝕜`-isomorphic to `κ(w)`. -/
lemma wgt_insert_of_resEquiv {𝕜 : Type} [Field 𝕜]
    {X W : AlgebraicGeometry.Scheme.{0}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    {s : Set X} {a : X} (w : W) (ha : a ∉ s) (hs : s.Finite)
    (hw : ResEquiv 𝕜 a w) :
    Work.Motivic.wgt 𝕜 w (insert a s) = Work.Motivic.wgt 𝕜 w s + 1 := by
  simp only [Work.Motivic.wgt]
  have hset : insert a s ∩ {x | ResEquiv 𝕜 x w} = insert a (s ∩ {x | ResEquiv 𝕜 x w}) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx1, hx2⟩
      rcases hx1 with rfl | hx1s
      · exact Or.inl rfl
      · exact Or.inr ⟨hx1s, hx2⟩
    · intro hx
      rcases hx with rfl | ⟨hx1s, hx2⟩
      · exact ⟨Or.inl rfl, hw⟩
      · exact ⟨Or.inr hx1s, hx2⟩
  rw [hset, Set.ncard_insert_of_notMem (s := s ∩ {x | ResEquiv 𝕜 x w})
        (fun hc => ha hc.1) (hs.subset Set.inter_subset_left)]

/-- **The weight of an inserted point, degenerate case.**  If the residue field of `a` is *not*
`𝕜`-isomorphic to `κ(w)` then inserting `a` does not change the weight. -/
lemma wgt_insert_of_not_resEquiv {𝕜 : Type} [Field 𝕜]
    {X W : AlgebraicGeometry.Scheme.{0}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    {s : Set X} {a : X} (w : W) (ha : a ∉ s)
    (hw : ¬ ResEquiv 𝕜 a w) :
    Work.Motivic.wgt 𝕜 w (insert a s) = Work.Motivic.wgt 𝕜 w s := by
  simp only [Work.Motivic.wgt]
  have hset : insert a s ∩ {x | ResEquiv 𝕜 x w} = s ∩ {x | ResEquiv 𝕜 x w} := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx1, hx2⟩
      rcases hx1 with rfl | hx1s
      · exact absurd hx2 hw
      · exact ⟨hx1s, hx2⟩
    · intro hx
      exact ⟨Or.inr hx.1, hx.2⟩
  rw [hset]

/-- **Class partition (matching) of two finite sets of points.**

Let `A ⊆ X`, `B ⊆ Y` be *finite* sets of points of two `𝕜`-schemes and suppose that for every test
point `w` of every `𝕜`-scheme the number of points of `A` whose residue field is `𝕜`-isomorphic to
`κ(w)` equals the corresponding number for `B`.  Then the two sets have the same number of points,
class by class: there is a bijection `A ≃ B` matching the residue fields (`ResEquiv`).

This is the "multiset of structured residue fields" content of the hypothesis
`∀ Z z, cInv 𝕜 z φ = 0` (every field over `𝕜` being realisable as a test point), in the form needed
to transport it to the cylinder points.

Proof route: induction on `A.Finite` (via `Set.Finite.induction_on`), with the statement
universally quantified over the finite set `B`.  If `A = ∅`, then `B = ∅` (else `h` at a point of
`B` would give `0 = ncard ≠ 0`, using `B.Finite`).  Otherwise pick `a ∈ A`; `h` at the test point
`a` (the scheme `X` itself, `ResEquiv 𝕜 a a` being reflexive) gives a `b ∈ B` with
`ResEquiv 𝕜 b a`, i.e. `ResEquiv 𝕜 a b` by symmetry.  The hypothesis is inherited by
`(A ∖ {a}, B ∖ {b})`: for a test point `w` with `¬ ResEquiv 𝕜 a w` neither `a` nor `b` is counted
(`ResEquiv 𝕜 b w` would give `ResEquiv 𝕜 a w` by `ResEquiv.symm`/`.trans`), while for
`ResEquiv 𝕜 a w` both are counted, so removing the singleton from both sides preserves the
equality (`Set.ncard_insert_of_notMem` / `Set.ncard_sdiff` bookkeeping).  The induction hypothesis
gives a bijection `A ∖ {a} ≃ B ∖ {b}`, and the two pieces are glued with `Equiv.Set.insert` (or by
hand with `Equiv.ofBijective`). -/
theorem exists_bijection_of_ncard_of_resEquiv {𝕜 : Type} [Field 𝕜]
    {X Y : AlgebraicGeometry.Scheme.{0}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    {A : Set X} {B : Set Y} (hA : A.Finite) (hB : B.Finite)
    (h : ∀ (W : AlgebraicGeometry.Scheme.{0})
      [W.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (w : W),
      (A ∩ {x | ResEquiv 𝕜 x w}).ncard = (B ∩ {y | ResEquiv 𝕜 y w}).ncard) :
    ∃ e : ↥A ≃ ↥B, ∀ a : ↥A, ResEquiv 𝕜 a.1 (e a).1 := by
  classical
  suffices key : ∀ (A : Set X) (hA : A.Finite) (B : Set Y) (hB : B.Finite),
      (∀ (W : AlgebraicGeometry.Scheme.{0})
        [W.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (w : W),
        Work.Motivic.wgt 𝕜 w A = Work.Motivic.wgt 𝕜 w B) →
      ∃ e : ↥A ≃ ↥B, ∀ a : ↥A, ResEquiv 𝕜 a.1 (e a).1 from key A hA B hB h
  intro A hA
  refine Set.Finite.induction_on (motive := fun A _ =>
      ∀ (B : Set Y) (hB : B.Finite),
        (∀ (W : AlgebraicGeometry.Scheme.{0})
          [W.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (w : W),
          Work.Motivic.wgt 𝕜 w A = Work.Motivic.wgt 𝕜 w B) →
        ∃ e : ↥A ≃ ↥B, ∀ a : ↥A, ResEquiv 𝕜 a.1 (e a).1) A hA ?_ ?_
  · intro B hB hh
    have hBempty : B = ∅ := by
      by_contra hne
      obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.2 hne
      have hmem : b ∈ B ∩ {y | ResEquiv 𝕜 y b} := ⟨hb, Work.Motivic.ResEquiv.refl 𝕜 b⟩
      have h1 : Work.Motivic.wgt 𝕜 b B ≠ 0 := by
        simp only [Work.Motivic.wgt]
        intro hz
        have hempty := (Set.ncard_eq_zero (hB.subset Set.inter_subset_left)).1 hz
        rw [hempty] at hmem
        exact hmem
      have h2 : Work.Motivic.wgt 𝕜 b (∅ : Set X) = Work.Motivic.wgt 𝕜 b B := hh Y b
      rw [Work.Motivic.wgt_empty] at h2
      exact h1 h2.symm
    subst hBempty
    exact ⟨Equiv.equivOfIsEmpty _ _, fun x => x.2.elim⟩
  · intro a s ha hs ih B hB hh
    -- the point of `B` matching `a`
    have hb_exists : ∃ b ∈ B, ResEquiv 𝕜 b a := by
      have h1 : 0 < Work.Motivic.wgt 𝕜 a (insert a s) := by
        simp only [Work.Motivic.wgt]
        exact (Set.ncard_pos ((hs.insert a).subset Set.inter_subset_left)).2
          ⟨a, Set.mem_insert_iff.2 (Or.inl rfl), Work.Motivic.ResEquiv.refl 𝕜 a⟩
      have h2 : Work.Motivic.wgt 𝕜 a (insert a s) = Work.Motivic.wgt 𝕜 a B := hh X a
      rw [h2] at h1
      exact (Set.ncard_pos (hB.subset Set.inter_subset_left)).1 h1
    obtain ⟨b, hbB, hba⟩ := hb_exists
    have hab : ResEquiv 𝕜 a b := Work.Motivic.ResEquiv.symm hba
    have hb_notmem : b ∉ (B \ {b}) := by simp
    have hBeq : B = insert b (B \ {b}) := by
      ext x
      constructor
      · intro hx
        by_cases hxb : x = b
        · exact Or.inl hxb
        · exact Or.inr ⟨hx, by simpa [Set.mem_singleton_iff] using hxb⟩
      · rintro (rfl | ⟨hx, _⟩)
        · exact hbB
        · exact hx
    have hB' : (B \ {b}).Finite := hB.sdiff
    -- the hypothesis is inherited by the complements of `a` and `b`
    have hh' : ∀ (W : AlgebraicGeometry.Scheme.{0})
        [W.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (w : W),
        Work.Motivic.wgt 𝕜 w s = Work.Motivic.wgt 𝕜 w (B \ {b}) := by
      intro W _ w
      have hW := hh W w
      rw [hBeq] at hW
      by_cases hw : ResEquiv 𝕜 a w
      · have hbw : ResEquiv 𝕜 b w :=
          Work.Motivic.ResEquiv.trans (Work.Motivic.ResEquiv.symm hab) hw
        rw [wgt_insert_of_resEquiv w ha hs hw,
            wgt_insert_of_resEquiv w hb_notmem hB' hbw] at hW
        omega
      · have hbw : ¬ ResEquiv 𝕜 b w := fun hbw => hw (Work.Motivic.ResEquiv.trans hab hbw)
        rw [wgt_insert_of_not_resEquiv w ha hw,
            wgt_insert_of_not_resEquiv w hb_notmem hbw] at hW
        exact hW
    obtain ⟨e', he'⟩ := ih (B \ {b}) hB' hh'
    -- glue the induction bijection with the correspondence `a ↔ b`
    let E : ↥(insert a s) ≃ ↥B :=
      ((Equiv.Set.insert ha).trans ((e'.sumCongr (Equiv.refl PUnit)).trans
        (Equiv.Set.insert hb_notmem).symm)).trans (Set.equivOfEq hBeq).symm
    have hE_a : (E ⟨a, Or.inl rfl⟩).1 = b := by simp [E]
    have hE_s : ∀ y : ↥s, (E ⟨y.1, Or.inr y.2⟩).1 = (e' y).1 := by intro y; simp [E]
    refine ⟨E, ?_⟩
    intro x
    by_cases hx : (x : X) = a
    · have hxa : x = ⟨a, Or.inl rfl⟩ := Subtype.ext hx
      rw [hxa, hE_a]
      exact hab
    · have hxs : (x : X) ∈ s := (Set.mem_insert_iff.1 x.2).resolve_left hx
      let y : ↥s := ⟨x.1, hxs⟩
      have hxa : x = ⟨y.1, Or.inr y.2⟩ := Subtype.ext rfl
      rw [hxa, hE_s y]
      exact he' y

end Work.CY3Stab.Prod
