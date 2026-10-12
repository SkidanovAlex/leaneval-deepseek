import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.Band.Support
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.Band.jointProj_pairing_eq_zero_of_free_ne`

**Weighted orthogonality of two joint sectors which differ in a *free* slot.**

Let `W : X n → ℝ` be constant along the configuration variable of every slot `j < n`
with `j ∉ A` ("free" slots), i.e. `W` depends only on the slots of `A`.  If two sector
sets `S, T ⊆ {0,…,n−1}` do **not** agree on the free slots, i.e.

  `S ∩ ({0,…,n−1} ∖ A) ≠ T ∩ ({0,…,n−1} ∖ A)`,

then the box pairing

  `∫_{abox n ℓ} (E_SΦ)(x) · W(x) · (E_TΦ)(x) dx = 0`,   `E_R := jointProj ℓ R`,

for every smooth `Φ`.

ROUTE.  Pick a free slot `j ∉ A`, `j < n` in which `S` and `T` differ, say `j ∈ S`,
`j ∉ T` (the other case is the mirror image).  Then

* `E_SΦ` is mean-free in the slot `j`:  `P_j E_SΦ = 0`
  (`BoseFixB2.Sector.jointProj_aP_eq_zero`, since `j ∈ S` puts the factor `Q_j` into the
  iterated product);
* `W · E_TΦ` is constant along the slot `j`:  `W` by hypothesis, and `E_TΦ` because
  `j ∉ T` puts the factor `P_j` into the iterated product
  (`BoseFixB2.Sector.constIn_jointProj`).

Peeling the box integral in the slot `j` and using that the inner cube integral of a
function constant in the slot is the constant times `ℓ³` gives, for every base point,
`(W·E_TΦ)(x)·∫_y (E_SΦ)(x_j→y) dy = (W·E_TΦ)(x)·ℓ³·(P_j E_SΦ)(x) = 0`.  This is exactly
`Work.BoseFixB2.DvApriori.integral_mul_eq_zero_of_meanFree` of `Band.Support`, which
requires no regularity of `W` beyond integrability of the product.
-/

namespace Work.BoseFixB2.DvApriori.Band

open Submission.BoseGases MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## 1. The free slot in which the two sectors differ -/

/-- **Extraction of a free differing slot.**  If `S, T ⊆ {0,…,n−1}` do not agree on the
slots outside `A`, there is a slot `j < n`, `j ∉ A` which lies in exactly one of `S`,
`T`. -/
lemma exists_free_slot_of_ne {n : ℕ} {A S T : Finset ℕ} (hS : S ⊆ Finset.range n)
    (hT : T ⊆ Finset.range n)
    (hST : S ∩ (Finset.range n \ A) ≠ T ∩ (Finset.range n \ A)) :
    ∃ j, j < n ∧ j ∉ A ∧ ((j ∈ S ∧ j ∉ T) ∨ (j ∈ T ∧ j ∉ S)) := by
  classical
  -- since `S ⊆ range n`, the intersection with `range n \ A` is just `S \ A`
  have hSA : S ∩ (Finset.range n \ A) = S \ A := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_range]
    constructor
    · rintro ⟨hjS, _, hjA⟩; exact ⟨hjS, hjA⟩
    · rintro ⟨hjS, hjA⟩; exact ⟨hjS, Finset.mem_range.mp (hS hjS), hjA⟩
  have hTA : T ∩ (Finset.range n \ A) = T \ A := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_range]
    constructor
    · rintro ⟨hjT, _, hjA⟩; exact ⟨hjT, hjA⟩
    · rintro ⟨hjT, hjA⟩; exact ⟨hjT, Finset.mem_range.mp (hT hjT), hjA⟩
  have hne : S \ A ≠ T \ A := by rw [← hSA, ← hTA]; exact hST
  by_contra hcon
  refine hne (Finset.ext fun j => ?_)
  rw [Finset.mem_sdiff, Finset.mem_sdiff]
  constructor
  · intro hj
    obtain ⟨hjS, hjA⟩ := hj
    by_cases hjT : j ∈ T
    · exact ⟨hjT, hjA⟩
    · exact absurd ⟨j, Finset.mem_range.mp (hS hjS), hjA, Or.inl ⟨hjS, hjT⟩⟩ hcon
  · intro hj
    obtain ⟨hjT, hjA⟩ := hj
    by_cases hjS : j ∈ S
    · exact ⟨hjS, hjA⟩
    · exact absurd ⟨j, Finset.mem_range.mp (hT hjT), hjA, Or.inr ⟨hjT, hjS⟩⟩ hcon

/-! ## 2. The peeling in one free differing slot -/

/-- **One-slot peeling of the weighted pairing.**  If `W` is constant along the slot `j`
(`j ∉ A`), the sector `S` contains `j` and the sector `T` does not, then the weighted
pairing of the two sectors against `W` vanishes. -/
private lemma pairing_eq_zero_of_slot {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {A S T : Finset ℕ}
    {W : Submission.BoseGases.X n → ℝ}
    (hWin : ∀ (j : ℕ) (hj : j < n), j ∉ A →
      ∀ (x : Submission.BoseGases.X n) (z : EuclideanSpace ℝ (Fin 3)),
        W (Function.update x ⟨j, hj⟩ z) = W x)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {j : ℕ} (hjn : j < n) (hjA : j ∉ A) (hjS : j ∈ S) (hjT : j ∉ T)
    (hint : MeasureTheory.IntegrableOn
      (fun x => Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x)
      (Submission.BoseGases.abox n ℓ)) :
    (∫ x in Submission.BoseGases.abox n ℓ,
      Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x) = 0 := by
  -- the `T`-sector does not depend on the slot `j`
  have hTconst : Work.BoseFixB2.Sector.ConstIn ⟨j, hjn⟩ (Work.BoseFixB2.jointProj ℓ T Φ) :=
    Work.BoseFixB2.Sector.constIn_jointProj hℓ hjn hjT hΦ.continuous
  -- hence `W · E_TΦ` is constant along the slot `j`
  have hf : ∀ (x : Submission.BoseGases.X n) (z : EuclideanSpace ℝ (Fin 3)),
      W (Function.update x ⟨j, hjn⟩ z)
          * Work.BoseFixB2.jointProj ℓ T Φ (Function.update x ⟨j, hjn⟩ z)
        = W x * Work.BoseFixB2.jointProj ℓ T Φ x := by
    intro x z
    rw [hWin j hjn hjA x z, hTconst x z]
  -- the `S`-sector is mean-free in the slot `j`
  have hg : Submission.BoseGases.aP ℓ ⟨j, hjn⟩ (Work.BoseFixB2.jointProj ℓ S Φ) = 0 :=
    Work.BoseFixB2.Sector.jointProj_aP_eq_zero hℓ hjS hjn hΦ
  -- integrability in the order needed by the mean-free peeling
  have hint' : MeasureTheory.IntegrableOn
      (fun x => (W x * Work.BoseFixB2.jointProj ℓ T Φ x) * Work.BoseFixB2.jointProj ℓ S Φ x)
      (Submission.BoseGases.abox n ℓ) :=
    hint.congr (Filter.Eventually.of_forall fun x => by ring)
  have hmain := Work.BoseFixB2.DvApriori.integral_mul_eq_zero_of_meanFree
    hℓ ⟨j, hjn⟩ hf hg hint'
  calc (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (W x * Work.BoseFixB2.jointProj ℓ T Φ x) * Work.BoseFixB2.jointProj ℓ S Φ x :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = 0 := hmain

/-! ## 3. The target -/

theorem jointProj_pairing_eq_zero_of_free_ne {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.range n) {W : Submission.BoseGases.X n → ℝ}
    (hWin : ∀ (j : ℕ) (hj : j < n), j ∉ A →
      ∀ (x : Submission.BoseGases.X n) (z : EuclideanSpace ℝ (Fin 3)),
        W (Function.update x ⟨j, hj⟩ z) = W x)
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hST : S ∩ (Finset.range n \ A) ≠ T ∩ (Finset.range n \ A))
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hint : MeasureTheory.IntegrableOn
      (fun x => Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x)
      (Submission.BoseGases.abox n ℓ)) :
    (∫ x in Submission.BoseGases.abox n ℓ,
      Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x) = 0 := by
  obtain ⟨j, hjn, hjA, hmem⟩ := exists_free_slot_of_ne hS hT hST
  rcases hmem with ⟨hjS, hjT⟩ | ⟨hjT, hjS⟩
  · exact pairing_eq_zero_of_slot hℓ hWin hΦ hjn hjA hjS hjT hint
  · -- mirror image: exchange the roles of `S` and `T`
    have hsym := pairing_eq_zero_of_slot (S := T) (T := S) hℓ hWin hΦ hjn hjA hjT hjS
      (hint.congr (Filter.Eventually.of_forall fun x => by ring))
    calc (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x)
        = ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseFixB2.jointProj ℓ T Φ x * W x * Work.BoseFixB2.jointProj ℓ S Φ x :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = 0 := hsym

end

end Work.BoseFixB2.DvApriori.Band
