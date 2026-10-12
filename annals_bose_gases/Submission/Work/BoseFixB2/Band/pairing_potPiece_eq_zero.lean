import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Band.PotSplit
import Submission.Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable
import Submission.Work.BoseFixB2.DvApriori.Band.jointProj_pairing_eq_zero_of_free_ne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Band.pairing_potPiece_eq_zero`

**Vanishing of a few-slot weighted sector pairing across a band of width `≥ 3`.**

If `W : X N → ℝ` is integrable on the box `abox N ℓ` and is *constant along the
configuration variable of every slot outside `A`* — with `|A| ≤ 2` — then for every smooth
`Φ` the weighted pairing of two joint sectors `E_S Φ`, `E_T Φ` vanishes as soon as the two
sector sets `S`, `T ⊆ {0,…,N−1}` differ in at least three slots.

This is the generality needed by the FS §6 band argument: each summand of the localised
potential word `potWordU` — the one-slot pieces `potOnePiece` and the two-slot pieces
`potPairPiece` of `Band.PotSplit` — is a weight of this shape with `A` the (one or two)
slots it involves, and the band statement follows because the three differing slots cannot
all be contained in `A`.

ROUTE.  The argument is the "one free slot" orthogonality
`DvApriori.Band.jointProj_pairing_eq_zero_of_free_ne`, applied with the slot set
`A' = A ∩ {0,…,N−1}`:

* the slots of the symmetric difference `S △ T` all lie in `{0,…,N−1}` (as `S, T` do), so
  `3 ≤ (S △ T).card` forces a differing slot outside `A'` — indeed outside `A` — since
  `|A'| ≤ |A| ≤ 2`; this is `sdiff_ne_of_card_le` below;
* `W` is constant along that slot because it is not in `A` (`hWin`);
* `S ∩ ({0,…,N−1} ∖ A') = S ∖ A` (as `S ⊆ {0,…,N−1}`), so the differing slot also
  separates the two intersections that the free-slot lemma tests.
-/

namespace Work.BoseFixB2.Band

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## 1. The combinatorial core: three differing slots cannot all be frozen -/

/-- **Three differing slots have to contain a free one.**  If `(S △ T).card ≥ 3` and
`A.card ≤ 2`, then `S ∖ A ≠ T ∖ A`: otherwise `S △ T ⊆ A` would force
`(S △ T).card ≤ A.card ≤ 2`. -/
theorem sdiff_ne_of_card_le {S T A : Finset ℕ} (hA : A.card ≤ 2)
    (hcard : 3 ≤ (S \ T).card + (T \ S).card) : S \ A ≠ T \ A := by
  classical
  intro heq
  have h1 : S \ T ⊆ A := by
    intro j hj
    rw [Finset.mem_sdiff] at hj
    by_contra hjA
    have hmem : j ∈ S \ A := Finset.mem_sdiff.mpr ⟨hj.1, hjA⟩
    rw [heq] at hmem
    exact hj.2 (Finset.mem_sdiff.mp hmem).1
  have h2 : T \ S ⊆ A := by
    intro j hj
    rw [Finset.mem_sdiff] at hj
    by_contra hjA
    have hmem : j ∈ T \ A := Finset.mem_sdiff.mpr ⟨hj.1, hjA⟩
    rw [← heq] at hmem
    exact hj.2 (Finset.mem_sdiff.mp hmem).1
  have hdisj : Disjoint (S \ T) (T \ S) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have hunion : ((S \ T) ∪ (T \ S)).card = (S \ T).card + (T \ S).card :=
    Finset.card_union_of_disjoint hdisj
  have hle : ((S \ T) ∪ (T \ S)).card ≤ A.card :=
    Finset.card_le_card (Finset.union_subset h1 h2)
  omega

/-! ## 2. The free-slot lemma with the slot set intersected into the range -/

/-- **The free-slot orthogonality in the `card`-form.**  `DvApriori.Band.jointProj_pairing_eq_zero_of_free_ne`
with the slot set `A` replaced by `A ∩ {0,…,N−1}`, so that the hypothesis on `A` is only a
cardinality bound `|A| ≤ 2`. -/
theorem pairing_eq_zero_of_card_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Finset ℕ}
    (hA : A.card ≤ 2) {W : Submission.BoseGases.X N → ℝ}
    (hWint : MeasureTheory.IntegrableOn W (Submission.BoseGases.abox N ℓ))
    (hWin : ∀ (j : ℕ) (hj : j < N), j ∉ A →
      ∀ (x : Submission.BoseGases.X N) (z : EuclideanSpace ℝ (Fin 3)),
        W (Function.update x ⟨j, hj⟩ z) = W x)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {S T : Finset ℕ} (hS : S ⊆ Finset.range N) (hT : T ⊆ Finset.range N)
    (hcard : 3 ≤ (S \ T).card + (T \ S).card) :
    (∫ x in Submission.BoseGases.abox N ℓ,
      Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x) = 0 := by
  classical
  -- `W` is constant along every slot outside `A ∩ [N)`: such a slot `< N` is outside `A`
  have hWin' : ∀ (j : ℕ) (hj : j < N), j ∉ A ∩ Finset.range N →
      ∀ (x : Submission.BoseGases.X N) (z : EuclideanSpace ℝ (Fin 3)),
        W (Function.update x ⟨j, hj⟩ z) = W x :=
    fun j hj hjA => hWin j hj
      (fun h => hjA (Finset.mem_inter.mpr ⟨h, Finset.mem_range.mpr hj⟩))
  -- the two sector intersections with the free slots are `S ∖ A` and `T ∖ A`
  have hSA : S ∩ (Finset.range N \ (A ∩ Finset.range N)) = S \ A := by
    ext j
    constructor
    · intro hj
      obtain ⟨hjS, hj1⟩ := Finset.mem_inter.mp hj
      obtain ⟨hjrn, hjA⟩ := Finset.mem_sdiff.mp hj1
      exact Finset.mem_sdiff.mpr ⟨hjS, fun hA' => hjA (Finset.mem_inter.mpr ⟨hA', hjrn⟩)⟩
    · intro hj
      obtain ⟨hjS, hjA⟩ := Finset.mem_sdiff.mp hj
      exact Finset.mem_inter.mpr ⟨hjS, Finset.mem_sdiff.mpr
        ⟨hS hjS, fun h => hjA (Finset.mem_inter.mp h).1⟩⟩
  have hTA : T ∩ (Finset.range N \ (A ∩ Finset.range N)) = T \ A := by
    ext j
    constructor
    · intro hj
      obtain ⟨hjT, hj1⟩ := Finset.mem_inter.mp hj
      obtain ⟨hjrn, hjA⟩ := Finset.mem_sdiff.mp hj1
      exact Finset.mem_sdiff.mpr ⟨hjT, fun hA' => hjA (Finset.mem_inter.mpr ⟨hA', hjrn⟩)⟩
    · intro hj
      obtain ⟨hjT, hjA⟩ := Finset.mem_sdiff.mp hj
      exact Finset.mem_inter.mpr ⟨hjT, Finset.mem_sdiff.mpr
        ⟨hT hjT, fun h => hjA (Finset.mem_inter.mp h).1⟩⟩
  have hne : S ∩ (Finset.range N \ (A ∩ Finset.range N))
      ≠ T ∩ (Finset.range N \ (A ∩ Finset.range N)) := by
    rw [hSA, hTA]
    exact sdiff_ne_of_card_le hA hcard
  have hint : MeasureTheory.IntegrableOn
      (fun x => Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x)
      (Submission.BoseGases.abox N ℓ) :=
    Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable hℓ
      (Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ).continuous
      (Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ).continuous hWint
  exact Work.BoseFixB2.DvApriori.Band.jointProj_pairing_eq_zero_of_free_ne hℓ
    Finset.inter_subset_right hWin' hS hT hne hΦ hint

/-! ## 3. The lemma of the node -/

theorem pairing_potPiece_eq_zero {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Finset ℕ} (hA : A.card ≤ 2)
    {W : Submission.BoseGases.X N → ℝ}
    (hWint : MeasureTheory.IntegrableOn W (Submission.BoseGases.abox N ℓ))
    (hWin : ∀ (j : ℕ) (hj : j < N), j ∉ A →
      ∀ (x : Submission.BoseGases.X N) (z : EuclideanSpace ℝ (Fin 3)),
        W (Function.update x ⟨j, hj⟩ z) = W x)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {S T : Finset ℕ} (hS : S ⊆ Finset.range N) (hT : T ⊆ Finset.range N)
    (hcard : 3 ≤ (S \ T).card + (T \ S).card) :
    (∫ x in Submission.BoseGases.abox N ℓ,
      Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x) = 0 :=
  pairing_eq_zero_of_card_le hℓ hA hWint hWin hΦ hS hT hcard

end

end Work.BoseFixB2.Band
