import Mathlib
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.mk_ne_one_of_subword_terminal
import Submission.Work.OROneRel.isCyclicallyReducedRelator_pow
import Submission.Work.OROneRel.exists_complement_of_isSubwordOf_pow

/-!
# Weinbaum's theorem: definitions and reductions

This module collects the vocabulary and the general (case-independent) reductions used by the proof
of Weinbaum's theorem in `Submission.Work.OROneRel.weinbaum_at`.  It is imported both by that file
and by the files proving the two cases of the final case split
(`Submission.Work.OROneRel.weinbaumAt_of_expSum_eq_zero`,
`Submission.Work.OROneRel.weinbaumAt_of_expSum_ne_zero`).

## What is proved here

* `expSum`, `expVec` : the exponent sum in a generator, and the exponent-sum vector (the image in the
  free abelian group on `α`);
* `expVec_mem_zpowers_of_mem_normalClosure`, `expSum_eq_zpow_of_mem_normalClosure` : the
  **abelianisation criterion** -- if `v` lies in the normal closure of `r`, then `σ(v) = σ(r) ^ k`
  for an integer `k`;
* `exists_complement_counterexample` : cutting out the complementary arc of the cyclic word of `r`
  turns a counterexample into another counterexample, whose length with `v` adds up to `relatorNorm
  r`;
* `weinbaumAt_of_le_half` : consequently, if Weinbaum's theorem holds for subwords `v` with
  `2 * relatorNorm v ≤ relatorNorm r`, then it holds in general.

## What remains

The remaining case of the induction is the Magnus breakdown, in the following precise form.  Let
`a` be a generator occurring in `r` with exponent sum zero, and put `K = ker (expSum a)`.  Then
`K ≃* F((α \ {a}) × ℤ)` by the Magnus map `magnusMap a` (proved in
`Submission.Work.OROneRel.magnusMap_injective_range`, with the section given by
`Submission.Work.OROneRel.exists_magnusRewrite`), and, writing `r' = (magnusMap a)⁻¹ r`,

`N ∩ K = ⟨ ⋃_{c ∈ ℤ} (magShiftAut a c) '' ⟨⟨r'⟩⟩ ⟩`,

so what has to be shown is the **localisation of short subwords**: for `v` a subword of a power of the
cyclic word of `r` with `2 * relatorNorm v ≤ relatorNorm r` (see `weinbaumAt_of_le_half`), the
element `(magnusMap a)⁻¹ v` lies in the normal closure `⟨⟨r'⟩⟩` of *one* shifted copy of `r'`, where
the induction hypothesis (applied to that shifted relator, of length `letterCountNot a r`) applies.

That localisation is exactly the content of the deep input `MagnusMoldavanskiiAt` of
`Submission.Work.OROneRel.Interface` (the Magnus--Moldavanskii amalgam decomposition of `⟨α | r⟩`).

Two warnings for anyone continuing.

* The naive transfer "`v ∈ ⟨⟨r⟩⟩` iff `v' ∈ ⟨⟨r'⟩⟩` for the *unshifted* rewriting" is **false**: for
  `r = [a,b]` one has `b_2 b_1^{-1} ∈ N ∩ K` (`b_i = a ^ i b a ^ (-i)`) while its rewriting is not in
  `⟨⟨b_1 b_0^{-1}⟩⟩`.  The shift/unlocalised amalgam is essential.
* The case in which *every* generator occurring in `r` has nonzero exponent sum and some generator
  occurs in `r` with both orientations is not covered by the abelianisation criterion and needs the
  classical "root adjunction" trick of Magnus' proof of the Freiheitssatz.

## Main declarations

* `Work.OROneRel.expSum`, `Work.OROneRel.expVec`, `Work.OROneRel.MonochromaticRelator`;
* `Work.OROneRel.magnusMap`, `Work.OROneRel.letterCountNot`;
* `Work.OROneRel.expVec_mem_zpowers_of_mem_normalClosure` : the abelianisation criterion;
* `Work.OROneRel.exists_complement_counterexample`, `Work.OROneRel.weinbaumAt_of_le_half` : the
  reduction to the half-length case;
* `Work.OROneRel.weinbaum_at` : Weinbaum's theorem.

## Used/produced elsewhere

* `Submission.Work.OROneRel.magnusMap_injective_range` : the Magnus map is injective with range the
  kernel of the exponent sum;
* `Submission.Work.OROneRel.exists_magnusRewrite` : the Magnus rewriting, length preserving;
* `Submission.Work.OROneRel.weinbaumAt_of_monochromatic` : Weinbaum for relators in which no
  generator occurs with both orientations (the abelianisation criterion settles this case).
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### Exponent sums -/

/-- The exponent sum of the generator `a` in the free group element `w`, as a homomorphism into the
multiplicative integers. -/
noncomputable def expSum (a : α) : FreeGroup α →* Multiplicative ℤ := by
  classical
  exact FreeGroup.lift fun x => if x = a then Multiplicative.ofAdd (1 : ℤ) else 1

/-- The exponent-sum vector of a free group element: its image in the free abelian group on `α`. -/
noncomputable def expVec : FreeGroup α →* Multiplicative (α →₀ ℤ) := by
  classical
  exact FreeGroup.lift fun a => Multiplicative.ofAdd (Finsupp.single a 1)

/-- A relator is *monochromatic* if no generator occurs in it with both orientations. -/
noncomputable def MonochromaticRelator (r : FreeGroup α) : Prop := by
  classical
  exact ∀ a : α, ¬ ((a, true) ∈ FreeGroup.toWord r ∧ (a, false) ∈ FreeGroup.toWord r)

/-! ### The abelianisation criterion -/

/-- The exponent-sum vector is invariant under conjugation: `expVec` lands in an abelian group. -/
theorem expVec_conj (c r : FreeGroup α) : expVec (c * r * c⁻¹) = expVec r := by
  rw [map_mul, map_mul, map_inv]
  exact mul_inv_cancel_comm _ _

/-- The exponent-sum vector is invariant under inversion. -/
theorem expVec_inv (r : FreeGroup α) : expVec r⁻¹ = (expVec r)⁻¹ := map_inv _ _

/-- **Abelianisation criterion.**  If `v` lies in the normal closure of `r` then the exponent-sum
vector of `v` is an integral power of that of `r`. -/
theorem expVec_mem_zpowers_of_mem_normalClosure {r v : FreeGroup α}
    (h : v ∈ Subgroup.normalClosure ({r} : Set (FreeGroup α))) :
    ∃ k : ℤ, expVec v = (expVec r) ^ k := by
  classical
  have hN : (Subgroup.normalClosure ({r} : Set (FreeGroup α))) ≤
      (Subgroup.zpowers (expVec r)).comap expVec := by
    refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hN h)
  exact ⟨k, hk.symm⟩

/-- Consequence of the criterion, in the "per generator" form: if `v` lies in the normal closure of
`r` then `σ_a(v) = σ_a(r) ^ k` for a single integer `k`. -/
theorem expSum_eq_zpow_of_mem_normalClosure {r v : FreeGroup α} (a : α)
    (h : v ∈ Subgroup.normalClosure ({r} : Set (FreeGroup α))) :
    ∃ k : ℤ, expSum a v = (expSum a r) ^ k := by
  classical
  obtain ⟨k, hk⟩ := expVec_mem_zpowers_of_mem_normalClosure h
  refine ⟨k, ?_⟩
  have h1 : expSum a = (Finsupp.applyAddHom a).toMultiplicative.comp expVec := by
    refine FreeGroup.ext_hom _ _ fun b => ?_
    show expSum a (FreeGroup.of b) =
      Multiplicative.ofAdd ((expVec (FreeGroup.of b)).toAdd a)
    rw [expSum, expVec, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    by_cases hb : b = a
    · subst hb
      simp
    · simp [hb, Finsupp.single_eq_of_ne (show a ≠ b from fun h => hb h.symm)]
  rw [h1]
  simp only [MonoidHom.comp_apply, hk, map_zpow]

/-- The number of letters of `w` other than the generator `a` (the length of the Magnus rewriting
of `w`, see `exists_magnusRewrite`). -/
noncomputable def letterCountNot (a : α) (w : FreeGroup α) : ℕ := by
  classical
  exact (FreeGroup.toWord w).countP fun p => p.1 ≠ a

/-! ### The Magnus kernel -/

/-- The Magnus map: `(y, i) ↦ a ^ i * of y * a ^ (-i)`.  Its range is the kernel of the exponent
sum in `a`. -/
noncomputable def magnusMap (a : α) : FreeGroup ({x : α // x ≠ a} × ℤ) →* FreeGroup α := by
  classical
  exact FreeGroup.lift fun p =>
    (FreeGroup.of a) ^ (p.2) * FreeGroup.of (p.1 : α) * (FreeGroup.of a) ^ (-p.2)

theorem magnusMap_apply (a : α) (y : {x : α // x ≠ a}) (i : ℤ) :
    magnusMap a (FreeGroup.of (y, i)) =
      (FreeGroup.of a) ^ i * FreeGroup.of (y : α) * (FreeGroup.of a) ^ (-i) := by
  classical
  simp [magnusMap]


/-! ### Reduction to subwords of length at most half the relator

Any counterexample `v` to Weinbaum's theorem produces, by cutting out the complementary arc of the
cyclic word of `r`, a counterexample of length `relatorNorm r - relatorNorm v`; applying the cut
twice shows that if there is a counterexample at all then there is one with
`2 * relatorNorm v ≤ relatorNorm r`.  Consequently the theorem follows from its "half-length" form.
-/

/-- A counterexample produces a counterexample of complementary length.  If `v` is a nontrivial
subword of a power of `r` of length `< r` representing `1` in `⟨α | r⟩`, then so is its complement in
the cyclic word of `r`. -/
theorem exists_complement_counterexample {r v : FreeGroup α} {k : ℕ}
    (hr : IsCyclicallyReducedRelator r) (hsub : IsSubwordOf v (r ^ k))
    (hlen : relatorNorm v < relatorNorm r) (hv1 : v ≠ 1)
    (hcontra : PresentedGroup.mk ({r} : Set (FreeGroup α)) v = 1) :
    ∃ (s : FreeGroup α) (m : ℕ), IsSubwordOf s (r ^ m) ∧ s ≠ 1 ∧
      relatorNorm s = relatorNorm r - relatorNorm v ∧
      PresentedGroup.mk ({r} : Set (FreeGroup α)) s = 1 := by
  obtain ⟨u, s, hconj, hnorm, hsnorm, hsubs, hs1⟩ :=
    exists_complement_of_isSubwordOf_pow hr hsub hlen
  refine ⟨s, 2, hsubs, hs1, hsnorm, ?_⟩
  -- `v * s` is a conjugate of `r`, hence trivial in `⟨α | r⟩`; so is its inverse and hence `s`.
  have hvs : PresentedGroup.mk ({r} : Set (FreeGroup α)) (v * s) = 1 := by
    rw [hconj]
    have h1 : PresentedGroup.mk ({r} : Set (FreeGroup α)) r = 1 :=
      PresentedGroup.one_of_mem (Set.mem_singleton r)
    rw [map_mul, map_mul, map_inv, h1]
    simp
  have hv : PresentedGroup.mk ({r} : Set (FreeGroup α)) v = 1 := hcontra
  have : PresentedGroup.mk ({r} : Set (FreeGroup α)) s =
      (PresentedGroup.mk ({r} : Set (FreeGroup α)) v)⁻¹ *
        PresentedGroup.mk ({r} : Set (FreeGroup α)) (v * s) := by
    rw [map_mul]
    simp
  rw [this, hv, hvs]
  simp

/-- **Reduction to the half-length case.**  If Weinbaum's theorem is known for all subwords `v` with
`2 * relatorNorm v ≤ relatorNorm r`, then it holds in general. -/
theorem weinbaumAt_of_le_half
    (h : ∀ (β : Type u) (r v : FreeGroup β) (k : ℕ), IsCyclicallyReducedRelator r →
      ¬ IsProperPower r → IsSubwordOf v (r ^ k) → 2 * relatorNorm v ≤ relatorNorm r →
      v ≠ 1 → PresentedGroup.mk ({r} : Set (FreeGroup β)) v ≠ 1)
    (r : FreeGroup α) : WeinbaumAt r := by
  classical
  intro hr hp k v hsub hlen hv1 hcontra
  -- `v` is nontrivial, hence has length at least one
  have hvpos : 1 ≤ relatorNorm v := by
    refine Nat.one_le_iff_ne_zero.mpr fun h0 => hv1 ?_
    simp only [relatorNorm] at h0
    exact FreeGroup.norm_eq_zero.mp h0
  -- cutting out the complementary arc of the cyclic word of `r` gives another counterexample
  obtain ⟨s, m, hsubs, hs1, hsnorm, hscontra⟩ :=
    exists_complement_counterexample hr hsub hlen hv1 hcontra
  -- the two lengths add up to `relatorNorm r`, so the smaller one is at most half of it
  have hnle : relatorNorm v ≤ relatorNorm r := le_of_lt hlen
  have hsum : relatorNorm v + relatorNorm s = relatorNorm r := by omega
  rcases le_total (relatorNorm v) (relatorNorm s) with hvs | hsv
  · exact h α r v k hr hp hsub (by omega) hv1 hcontra
  · exact h α r s m hr hp hsubs (by omega) hs1 hscontra

/-! ### Assembling the induction

The proof of Weinbaum's theorem splits, for a relator `r`, according to whether some generator
occurring in `r` has exponent sum zero.  Both cases are recorded as separate files:
`Submission.Work.OROneRel.weinbaumAt_of_expSum_eq_zero` (the Magnus/Moldavanskii case) and
`Submission.Work.OROneRel.weinbaumAt_of_expSum_ne_zero` (the remaining case, where the abelianisation
criterion covers the monochromatic relators).  The assembly of the two is the following case split.
-/

/-- **Assembly.**  Weinbaum's theorem follows from the two cases "some generator occurring in `r` has
exponent sum zero" and "every generator occurring in `r` has nonzero exponent sum". -/
theorem weinbaum_at_of_cases {α : Type u}
    (hzero : ∀ {β : Type u} (r : FreeGroup β) {a : β}, a ∈ relatorLetters r →
      expSum a r = 1 → WeinbaumAt r)
    (hnonzero : ∀ {β : Type u} (r : FreeGroup β),
      (∀ a ∈ relatorLetters r, expSum a r ≠ 1) → WeinbaumAt r)
    (r : FreeGroup α) : WeinbaumAt r := by
  classical
  by_cases h : ∃ a ∈ relatorLetters r, expSum a r = 1
  · obtain ⟨a, ha, h1⟩ := h
    exact hzero r ha h1
  · exact hnonzero r fun a ha h1 => h ⟨a, ha, h1⟩

end Work.OROneRel
