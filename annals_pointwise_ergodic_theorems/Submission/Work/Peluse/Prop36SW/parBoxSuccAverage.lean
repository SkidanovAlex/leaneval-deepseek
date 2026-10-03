import Mathlib
import Submission.Work.Peluse.UControl.parBox_card
import Submission.Work.Peluse.ladderBaseDefs

/-!
# The one-step Fubini of the parameter box (`Icc` version)

`Work.Peluse.Prop36SW.parBoxSuccAverage` identifies the uniform average over the *closed*
parameter box `D.parBox (ℓ+2) M` with the iterated average over the closed box
`D.parBox (ℓ+1) M` at the levels `≤ ℓ` and the closed level-`(ℓ+1)` direction box
`∏_{s : D.S (ℓ+1)} [-M, M]`, glued by `Work.Peluse.padUpdate`.

The proof is a card-splitting bijection: the map
`joinIdx D ℓ : D.Idx (ℓ+1) × (D.S (ℓ+1) → ℤ) → D.Idx (ℓ+2)`,
`p ↦ padUpdate D ℓ p.1 p.2` (read at the levels `Fin (ℓ+2)`) is injective
(`padUpdate_inj`), lands in the level-`(ℓ+2)` box exactly on the product box
(`joinIdx_mem`), and `D.pad (ℓ+2) ∘ joinIdx = padUpdate D ℓ` (`pad_joinIdx`).  Since the two
boxes have the same cardinality (`parBox_succ_card`, from `parBox_card`), the image of the
product box is the whole level-`(ℓ+2)` box, and the average identity follows by
`Finset.sum_image`, `Finset.sum_product` and `Finset.card_product`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

open Work.Peluse.UControl

/-- The joint family obtained from a level-`(ℓ+1)` parameter family and a level-`(ℓ+1)` direction
family: the level-`(ℓ+2)` parameters whose levels `≤ ℓ` are the old parameters and whose level `ℓ+1`
is the new one. -/
private noncomputable def joinIdx (D : IdxDatum) (ℓ : ℕ) :
    D.Idx (ℓ + 1) × (D.S (ℓ + 1) → ℤ) → D.Idx (ℓ + 2) :=
  fun p j t => padUpdate D ℓ p.1 p.2 (j : ℕ) t

/-- Splitting off the peel of `pad`. -/
private lemma pad_joinIdx (D : IdxDatum) (ℓ : ℕ) (al : D.Idx (ℓ + 1))
    (s : D.S (ℓ + 1) → ℤ) :
    D.pad (ℓ + 2) (joinIdx D ℓ (al, s)) = padUpdate D ℓ al s := by
  funext j' t
  by_cases h : j' < ℓ + 2
  · rw [IdxDatum.pad, dif_pos h]
    rfl
  · rw [IdxDatum.pad, dif_neg h]
    have hj : j' ≠ ℓ + 1 := by omega
    have hlt : ¬ j' < ℓ + 1 := by omega
    rw [padUpdate_of_ne D ℓ al s hj t, IdxDatum.pad, dif_neg hlt]

/-- The joint family of a pair in the two boxes lies in the level-`(ℓ+2)` box. -/
private lemma joinIdx_mem (D : IdxDatum) (ℓ M : ℕ) {p : D.Idx (ℓ + 1) × (D.S (ℓ + 1) → ℤ)}
    (hp : p ∈ (D.parBox (ℓ + 1) M) ×ˢ
      Fintype.piFinset (fun _ : D.S (ℓ + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ))) :
    joinIdx D ℓ p ∈ D.parBox (ℓ + 2) M := by
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [IdxDatum.mem_parBox]
  intro j t
  by_cases h : (j : ℕ) = ℓ + 1
  · simp only [joinIdx]
    rw [padUpdate, dif_pos h]
    exact Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hp2 (h ▸ t))
  · have hj : (j : ℕ) ≠ ℓ + 1 := h
    have hlt : (j : ℕ) < ℓ + 1 := by have := j.isLt; omega
    simp only [joinIdx]
    rw [padUpdate_of_ne D ℓ p.1 p.2 hj t, pad_apply_of_lt D p.1 hlt t]
    exact (IdxDatum.mem_parBox.mp hp1) ⟨(j : ℕ), hlt⟩ t

/-- The joint map is injective. -/
private lemma joinIdx_inj (D : IdxDatum) (ℓ : ℕ) : Function.Injective (joinIdx D ℓ) := by
  intro p q h
  apply padUpdate_inj D ℓ
  change padUpdate D ℓ p.1 p.2 = padUpdate D ℓ q.1 q.2
  rw [← pad_joinIdx D ℓ p.1 p.2, ← pad_joinIdx D ℓ q.1 q.2]
  exact congrArg (D.pad (ℓ + 2)) h

/-- The cardinality of the level-`(ℓ+2)` box is the product of the level-`(ℓ+1)` box and the
level-`(ℓ+1)` direction box. -/
private lemma parBox_succ_card (D : IdxDatum) (ℓ M : ℕ) :
    (D.parBox (ℓ + 2) M).card = (D.parBox (ℓ + 1) M).card *
      (Fintype.piFinset (fun _ : D.S (ℓ + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ))).card := by
  have hcardIcc : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
    rw [Int.card_Icc]
    have h : (M : ℤ) + 1 - (-(M : ℤ)) = ((2 * M + 1 : ℕ) : ℤ) := by omega
    rw [h, Int.toNat_natCast]
  have hPt : (Fintype.piFinset (fun _ : D.S (ℓ + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ))).card
      = (2 * M + 1) ^ Fintype.card (D.S (ℓ + 1)) := by
    rw [Fintype.card_piFinset]
    simp only [Finset.prod_const, hcardIcc, Finset.card_univ]
  have hcast : (∑ j : Fin (ℓ + 1), Fintype.card (D.S (Fin.castSucc j)))
      = (∑ j : Fin (ℓ + 1), Fintype.card (D.S j)) :=
    Finset.sum_congr rfl fun j _ => rfl
  have hlast : Fintype.card (D.S (Fin.last (ℓ + 1))) = Fintype.card (D.S (ℓ + 1)) := rfl
  rw [parBox_card, parBox_card, hPt, Fin.sum_univ_castSucc, hcast, hlast, pow_add]

theorem parBoxSuccAverage (D : Work.Peluse.UControl.IdxDatum) (ℓ M : ℕ) (Φ : ((j' : ℕ) → D.S j' → ℤ) → ℝ) : (((Work.Peluse.UControl.IdxDatum.parBox D (ℓ + 2) M).card : ℝ)⁻¹ * ∑ a ∈ Work.Peluse.UControl.IdxDatum.parBox D (ℓ + 2) M, Φ (Work.Peluse.UControl.IdxDatum.pad D (ℓ + 2) a)) = (((Work.Peluse.UControl.IdxDatum.parBox D (ℓ + 1) M).card : ℝ)⁻¹ * ∑ al ∈ Work.Peluse.UControl.IdxDatum.parBox D (ℓ + 1) M, ((Fintype.piFinset (fun _ : D.S (ℓ + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ))).card : ℝ)⁻¹ * ∑ s ∈ Fintype.piFinset (fun _ : D.S (ℓ + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ)), Φ (Work.Peluse.padUpdate D ℓ al s)) := by
  classical
  set B1 : Finset (D.Idx (ℓ + 1)) := D.parBox (ℓ + 1) M with hB1
  set B2 : Finset (D.Idx (ℓ + 2)) := D.parBox (ℓ + 2) M with hB2
  set Pt : Finset (D.S (ℓ + 1) → ℤ) :=
    Fintype.piFinset (fun _ : D.S (ℓ + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ)) with hPt
  have hbij : B2 = (B1 ×ˢ Pt).image (joinIdx D ℓ) := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact joinIdx_mem D ℓ M hq
    · rw [Finset.card_image_of_injective _ (joinIdx_inj D ℓ), Finset.card_product, hB2, hB1,
        hPt, parBox_succ_card]
  have hsum : ∑ a ∈ B2, Φ (D.pad (ℓ + 2) a) = ∑ p ∈ B1 ×ˢ Pt, Φ (padUpdate D ℓ p.1 p.2) := by
    rw [hbij, Finset.sum_image (g := joinIdx D ℓ) (fun x _ y _ hxy => joinIdx_inj D ℓ hxy)]
    exact Finset.sum_congr rfl fun p _ => congrArg Φ (pad_joinIdx D ℓ p.1 p.2)
  have hcard : B2.card = B1.card * Pt.card := by
    rw [hB2, hB1, hPt, parBox_succ_card]
  have hR : (↑B1.card)⁻¹ * ∑ al ∈ B1, (↑Pt.card)⁻¹ * ∑ s ∈ Pt, Φ (padUpdate D ℓ al s)
      = (↑B1.card)⁻¹ * (↑Pt.card)⁻¹ * ∑ p ∈ B1 ×ˢ Pt, Φ (padUpdate D ℓ p.1 p.2) := by
    have h1 : ∑ al ∈ B1, (↑Pt.card)⁻¹ * ∑ s ∈ Pt, Φ (padUpdate D ℓ al s)
        = (↑Pt.card)⁻¹ * ∑ al ∈ B1, ∑ s ∈ Pt, Φ (padUpdate D ℓ al s) :=
      (Finset.mul_sum B1 (fun al => ∑ s ∈ Pt, Φ (padUpdate D ℓ al s)) (↑Pt.card)⁻¹).symm
    have h2 : ∑ al ∈ B1, ∑ s ∈ Pt, Φ (padUpdate D ℓ al s)
        = ∑ p ∈ B1 ×ˢ Pt, Φ (padUpdate D ℓ p.1 p.2) :=
      (Finset.sum_product B1 Pt
        (fun p : D.Idx (ℓ + 1) × (D.S (ℓ + 1) → ℤ) => Φ (padUpdate D ℓ p.1 p.2))).symm
    rw [h1, h2]
    ring
  rw [hsum, hcard, hR]
  have hcast2 : ((↑(B1.card * Pt.card) : ℝ))⁻¹ = (↑B1.card)⁻¹ * (↑Pt.card)⁻¹ := by
    rw [Nat.cast_mul, mul_inv_rev]
    ring
  rw [hcast2]

end Work.Peluse.Prop36SW
