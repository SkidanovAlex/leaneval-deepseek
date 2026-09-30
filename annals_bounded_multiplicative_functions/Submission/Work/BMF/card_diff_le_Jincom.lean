import Mathlib
import Submission.Work.BMF.vkford51_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset

/-- **Fibres of the difference map are largest at the origin.**  For a finite type `ι`, a map
`f : ι → β` into an additive commutative group and any `g : β`, the number of ordered pairs
`(x, y)` with `f x - f y = g` is at most the number of pairs with `f x = f y`.

This is the Cauchy–Schwarz (autocorrelation) inequality: writing `m v` for the size of the fibre
`f ⁻¹' {v}` over the (finite) image of `f`, the left-hand count is `∑_v m v · m (v - g)` and the
right-hand one is `∑_v (m v)²`; Cauchy–Schwarz gives `(∑_v m v · m (v - g))² ≤ (∑_v (m v)²)²`
because `v ↦ v - g` is injective and `m` vanishes off the image of `f`. -/
theorem card_sub_le_card_sub_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : Type*} [AddCommGroup β] [DecidableEq β] (f : ι → β) (g : β) :
    (((Finset.univ : Finset (ι × ι)).filter (fun p => f p.1 - f p.2 = g)).card : ℝ)
      ≤ (((Finset.univ : Finset (ι × ι)).filter (fun p => f p.1 - f p.2 = 0)).card : ℝ) := by
  classical
  set img : Finset β := (Finset.univ : Finset ι).image f with himg
  set m : β → ℕ := fun v => ((Finset.univ : Finset ι).filter (fun a => f a = v)).card with hm
  have key_mem : ∀ a ∈ (Finset.univ : Finset ι), f a ∈ img := by
    intro a _; rw [himg]; exact Finset.mem_image_of_mem f (Finset.mem_univ a)
  have hmzero : ∀ v, v ∉ img → m v = 0 := by
    intro v hv
    rw [hm, Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro a _ hfa
    exact hv (by rw [himg]; exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, hfa⟩)
  -- the count of pairs with a prescribed difference is the autocorrelation of the fibre sizes
  have hE : ∀ g' : β,
      (((Finset.univ : Finset (ι × ι)).filter (fun p => f p.1 - f p.2 = g')).card : ℝ)
        = ∑ v ∈ img, (m v : ℝ) * (m (v - g') : ℝ) := by
    intro g'
    have h1 : ((Finset.univ : Finset (ι × ι)).filter (fun p => f p.1 - f p.2 = g')).card
        = ∑ a ∈ (Finset.univ : Finset ι),
            ((Finset.univ : Finset ι).filter (fun b => f a - f b = g')).card := by
      rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.card_filter]
    have h2 : ∀ a : ι, ((Finset.univ : Finset ι).filter (fun b => f a - f b = g')).card
        = m (f a - g') := by
      intro a
      have hfe : (Finset.univ : Finset ι).filter (fun b => f a - f b = g')
          = (Finset.univ : Finset ι).filter (fun b => f b = f a - g') := by
        apply Finset.filter_congr
        intro b _
        constructor
        · intro h; rw [sub_eq_iff_eq_add] at h; rw [h, add_sub_cancel_left]
        · intro h; rw [h, sub_sub_cancel]
      rw [hfe]
    have h3 : ∑ a ∈ (Finset.univ : Finset ι), m (f a - g')
        = ∑ v ∈ img, m v * m (v - g') := by
      rw [← Finset.sum_fiberwise_of_maps_to' key_mem (fun v => m (v - g'))]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_const_nat (fun a _ => rfl)]
    have hnat : ((Finset.univ : Finset (ι × ι)).filter (fun p => f p.1 - f p.2 = g')).card
        = ∑ v ∈ img, m v * m (v - g') := by
      rw [h1, Finset.sum_congr rfl (fun a _ => h2 a), h3]
    rw [hnat, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro v _
    push_cast
    ring
  have hL := hE g
  have hR : (((Finset.univ : Finset (ι × ι)).filter (fun p => f p.1 - f p.2 = 0)).card : ℝ)
      = ∑ v ∈ img, (m v : ℝ) ^ 2 := by
    rw [hE 0]
    apply Finset.sum_congr rfl
    intro v _
    rw [sub_zero, sq]
  -- the shift `v ↦ v - g` is injective and `m` vanishes off the image
  have hInj : Set.InjOn (fun v : β => v - g) (↑img : Set β) := by
    intro a _ b _ h
    exact sub_left_injective h
  have hshift : ∑ v ∈ img, (m (v - g) : ℝ) ^ 2 ≤ ∑ v ∈ img, (m v : ℝ) ^ 2 := by
    have e1 : ∑ v ∈ img, (m (v - g) : ℝ) ^ 2
        = ∑ w ∈ img.image (fun v : β => v - g), (m w : ℝ) ^ 2 :=
      (Finset.sum_image (s := img) (g := fun v : β => v - g)
        (f := fun w => (m w : ℝ) ^ 2) hInj).symm
    have e2 : ∑ w ∈ img.image (fun v : β => v - g), (m w : ℝ) ^ 2
        ≤ ∑ w ∈ img ∪ img.image (fun v : β => v - g), (m w : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        (fun w _ _ => sq_nonneg _)
    have e3 : ∑ w ∈ img ∪ img.image (fun v : β => v - g), (m w : ℝ) ^ 2
        = ∑ w ∈ img, (m w : ℝ) ^ 2 :=
      (Finset.sum_subset Finset.subset_union_left
        (fun w _ hw => by rw [hmzero w hw]; simp)).symm
    rw [e1]
    exact le_trans e2 (le_of_eq e3)
  -- Cauchy–Schwarz
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq img (fun v => (m v : ℝ)) (fun v => (m (v - g) : ℝ))
  have hmain : (((Finset.univ : Finset (ι × ι)).filter (fun p => f p.1 - f p.2 = g)).card : ℝ) ^ 2
      ≤ (((Finset.univ : Finset (ι × ι)).filter (fun p => f p.1 - f p.2 = 0)).card : ℝ) ^ 2 := by
    rw [hL, hR]
    calc (∑ v ∈ img, (m v : ℝ) * (m (v - g) : ℝ)) ^ 2
        ≤ (∑ v ∈ img, (m v : ℝ) ^ 2) * (∑ v ∈ img, (m (v - g) : ℝ) ^ 2) := hcs
      _ ≤ (∑ v ∈ img, (m v : ℝ) ^ 2) * (∑ v ∈ img, (m v : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hshift (Finset.sum_nonneg (fun v _ => sq_nonneg _))
      _ = (∑ v ∈ img, (m v : ℝ) ^ 2) ^ 2 := by ring
  -- conclude `A ≤ B` from `A² ≤ B²` with `A, B ≥ 0`
  have hA : (0 : ℝ)
      ≤ (((Finset.univ : Finset (ι × ι)).filter (fun p => f p.1 - f p.2 = g)).card : ℝ) :=
    Nat.cast_nonneg _
  have hB : (0 : ℝ)
      ≤ (((Finset.univ : Finset (ι × ι)).filter (fun p => f p.1 - f p.2 = 0)).card : ℝ) :=
    Nat.cast_nonneg _
  have hs : Real.sqrt
        ((((Finset.univ : Finset (ι × ι)).filter (fun p => f p.1 - f p.2 = g)).card : ℝ) ^ 2)
      ≤ Real.sqrt
        ((((Finset.univ : Finset (ι × ι)).filter (fun p => f p.1 - f p.2 = 0)).card : ℝ) ^ 2) :=
    Real.sqrt_le_sqrt hmain
  rw [Real.sqrt_sq hA, Real.sqrt_sq hB] at hs
  exact hs

/-- Quantification over the subtype `↥(Finset.Icc h g)` is the same as quantification over
`ℕ` restricted by `h ≤ j ≤ g`. -/
private lemma forall_Icc_iff {P : ℕ → Prop} (h g : ℕ) :
    (∀ j : ↥(Finset.Icc h g), P (j : ℕ)) ↔ (∀ j : ℕ, h ≤ j → j ≤ g → P j) := by
  constructor
  · intro H j hj1 hj2
    exact H ⟨j, Finset.mem_Icc.mpr ⟨hj1, hj2⟩⟩
  · intro H j
    exact H (j : ℕ) (Finset.mem_Icc.mp j.2).1 (Finset.mem_Icc.mp j.2).2

/-- **The number of pairs of `s`-tuples in `[1,M₂]` with a prescribed difference vector of power
sums is at most the number of pairs whose power sums agree.**  This is Ford's bound
`#{Σ b_i^j - Σ b'_i^j = δ_j (h ≤ j ≤ g)} ≤ J_{s,g,h}[1,M₂]`, a consequence of Cauchy–Schwarz on
the fibres of the power-sum map (`card_sub_le_card_sub_zero`). -/
theorem card_diff_le_Jincom (s g h M₂ : ℕ) (δ : ℕ → ℤ) :
    (((Finset.univ : Finset (Pair s M₂)).filter
        (fun p => ∀ j : ℕ, h ≤ j → j ≤ g → dvec j p = δ j)).card : ℝ)
      ≤ Jincom s g h (Finset.Icc 1 M₂) := by
  classical
  set key : (Fin s → Finset.Icc 1 M₂) → ((↥(Finset.Icc h g)) → ℤ) :=
    (fun a j => ∑ i, ((a i).1 : ℤ) ^ ((j : ℕ))) with hkey
  set gv : ((↥(Finset.Icc h g)) → ℤ) := (fun j => δ (j : ℕ)) with hgv
  -- the two predicates agree
  have hiff : ∀ p : Pair s M₂,
      (key p.1 - key p.2 = gv) ↔ (∀ j : ℕ, h ≤ j → j ≤ g → dvec j p = δ j) := by
    intro p
    rw [funext_iff, ← forall_Icc_iff h g]
    simp only [Pi.sub_apply, hkey, hgv, dvec]
  have hiff0 : ∀ p : Pair s M₂,
      (key p.1 - key p.2 = 0) ↔ (∀ j : ℕ, h ≤ j → j ≤ g → dvec j p = 0) := by
    intro p
    rw [funext_iff, ← forall_Icc_iff h g]
    simp only [Pi.sub_apply, Pi.zero_apply, hkey, dvec]
  have hcardL : ((Finset.univ : Finset (Pair s M₂)).filter
        (fun p => ∀ j : ℕ, h ≤ j → j ≤ g → dvec j p = δ j)).card
      = ((Finset.univ : Finset (Pair s M₂)).filter (fun p => key p.1 - key p.2 = gv)).card :=
    congrArg Finset.card (Finset.filter_congr (fun p _ => (hiff p).symm))
  have hcardR : ((Finset.univ : Finset (Pair s M₂)).filter (fun p => key p.1 - key p.2 = 0)).card
      = ((Finset.univ : Finset (Pair s M₂)).filter
          (fun p => ∀ j : ℕ, h ≤ j → j ≤ g → dvec j p = 0)).card :=
    congrArg Finset.card (Finset.filter_congr (fun p _ => hiff0 p))
  -- the fibre-zero count is `Jincom`
  have hJin : (((Finset.univ : Finset (Pair s M₂)).filter
        (fun p => ∀ j : ℕ, h ≤ j → j ≤ g → dvec j p = 0)).card : ℝ)
      = Jincom s g h (Finset.Icc 1 M₂) := by
    have hfe : (Finset.univ : Finset (Pair s M₂)).filter
          (fun p => ∀ j : ℕ, h ≤ j → j ≤ g → dvec j p = 0)
        = (Finset.univ : Finset (Pair s M₂)).filter
            (fun xy => ∀ j : ℕ, h ≤ j → j ≤ g →
              (∑ i, (xy.1 i : ℕ) ^ j) = (∑ i, (xy.2 i : ℕ) ^ j)) := by
      apply Finset.filter_congr
      intro p _
      constructor
      · intro H j hj1 hj2
        have hsub : dvec j p = 0 := H j hj1 hj2
        simp only [dvec] at hsub
        have h1 : ((∑ i, ((p.1 i).1 : ℕ) ^ j : ℕ) : ℤ)
            = ((∑ i, ((p.2 i).1 : ℕ) ^ j : ℕ) : ℤ) := by
          simpa only [Nat.cast_sum, Nat.cast_pow] using sub_eq_zero.mp hsub
        exact Nat.cast_injective h1
      · intro H j hj1 hj2
        simp only [dvec, sub_eq_zero]
        have h1 : ((∑ i, ((p.1 i).1 : ℕ) ^ j : ℕ) : ℤ)
            = ((∑ i, ((p.2 i).1 : ℕ) ^ j : ℕ) : ℤ) :=
          congrArg (Nat.cast : ℕ → ℤ) (H j hj1 hj2)
        simpa only [Nat.cast_sum, Nat.cast_pow] using h1
    rw [hfe, Jincom]
  -- Cauchy–Schwarz plus the two identifications
  have hgen := card_sub_le_card_sub_zero (ι := Fin s → Finset.Icc 1 M₂) key gv
  rw [hcardL]
  refine le_trans hgen ?_
  rw [hcardR]
  exact le_of_eq hJin

end Work.BMF
