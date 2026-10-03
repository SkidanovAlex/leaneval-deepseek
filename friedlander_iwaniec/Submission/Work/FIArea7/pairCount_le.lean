import Mathlib
import Submission.Work.FIArea7.oddPartKernelDefs
import Submission.Work.FIArea7.sq_iff_sqfreeKernel_eq
import Submission.Work.FIArea7.Kern_of_mem_gBox

namespace Work.FIArea7

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Counting the pairs `(w, z)` for which the odd part of `|w|²|z|²` is a square

The number of pairs `(w, z)` in `gBox R × gBox R` for which `oddPart (|w|² |z|²)` is a perfect
square is at most `2 |gBox R| + 1 + ∑_{d ∈ Sset R} aCount R d ^ 2`.

The proof is a double count.  For `w ≠ 0` the value `Kern (|w|²)` is a squarefree number all of
whose prime factors are `≡ 1 (mod 4)` and which is `≤ (2R+1)²`, so it lies in `Sset R`; the
diagonal term `d = 0` (i.e. `w = 0`) contributes at most `1`.  The pairs with `w = 0` or `z = 0`
contribute at most `2 |gBox R|`.
-/

/-! ## Auxiliary facts -/

/-- `|z|² = 0` only for `z = 0`. -/
private lemma aux_gnorm_eq_zero (z : GaussianInt) : Work.FIPlan.gnorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h2 : z.re.natAbs ^ 2 + z.im.natAbs ^ 2 = 0 := by
      rw [← gnorm_eq_natAbs_sq_add]; exact h
    have h3 : z.re.natAbs = 0 := by nlinarith [Nat.zero_le z.re.natAbs]
    have h4 : z.im.natAbs = 0 := by nlinarith [Nat.zero_le z.im.natAbs]
    exact Zsqrtd.ext (by simpa using h3) (by simpa using h4)
  · rintro rfl
    simp [Work.FIPlan.gnorm]

/-- The odd part is multiplicative. -/
private lemma aux_oddPart_mul (a b : ℕ) :
    Work.FIPlan.oddPart (a * b) = Work.FIPlan.oddPart a * Work.FIPlan.oddPart b := by
  unfold Work.FIPlan.oddPart
  exact Nat.ordCompl_mul a b 2

/-- The odd part vanishes only at `0`. -/
private lemma aux_oddPart_eq_zero {n : ℕ} : Work.FIPlan.oddPart n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    rw [Work.FIPlan.oddPart] at h
    have := Nat.ordCompl_pos (p := 2) hn
    omega
  · rintro rfl
    simp [Work.FIPlan.oddPart]

/-- `Nat.sqrt m ^ 2 = m` exactly when `m` is a perfect square. -/
private lemma aux_sqrt_sq_eq (m : ℕ) : Nat.sqrt m ^ 2 = m ↔ ∃ s : ℕ, m = s ^ 2 := by
  constructor
  · intro h; exact ⟨Nat.sqrt m, h.symm⟩
  · rintro ⟨s, rfl⟩
    simp only [pow_two, Nat.sqrt_eq]

/-- The defining condition, expressed through the kernel `Kern = sqfreeKernel ∘ oddPart`. -/
private lemma aux_cond_iff (a b : ℕ) :
    (Nat.sqrt (Work.FIPlan.oddPart (a * b)) ^ 2 = Work.FIPlan.oddPart (a * b))
      ↔ (a = 0 ∨ b = 0) ∨ Kern a = Kern b := by
  rw [aux_sqrt_sq_eq, aux_oddPart_mul]
  by_cases ha : a = 0
  · subst ha
    constructor
    · intro _; exact Or.inl (Or.inl rfl)
    · intro _; exact ⟨0, by simp [Work.FIPlan.oddPart]⟩
  · by_cases hb : b = 0
    · subst hb
      constructor
      · intro _; exact Or.inl (Or.inr rfl)
      · intro _; exact ⟨0, by simp [Work.FIPlan.oddPart]⟩
    · have hoa : Work.FIPlan.oddPart a ≠ 0 := fun h => ha (aux_oddPart_eq_zero.mp h)
      have hob : Work.FIPlan.oddPart b ≠ 0 := fun h => hb (aux_oddPart_eq_zero.mp h)
      have key := sq_iff_sqfreeKernel_eq (Work.FIPlan.oddPart a) (Work.FIPlan.oddPart b) hoa hob
      constructor
      · intro h; exact Or.inr (key.mp h)
      · rintro (h | h)
        · rcases h with h | h
          · exact absurd h ha
          · exact absurd h hb
        · exact key.mpr h

/-- The kernel of the norm of a nonzero element of the box belongs to `Sset R`. -/
private lemma aux_Kern_mem_Sset (R : ℤ) (w : GaussianInt) (hw : w ∈ Work.FIPlan.gBox R)
    (h0 : w ≠ 0) : Kern (Work.FIPlan.gnorm w) ∈ Sset R := by
  have hg : Work.FIPlan.gnorm w ≠ 0 := fun h => h0 ((aux_gnorm_eq_zero w).mp h)
  rcases Kern_of_mem_gBox R w hw with h | h
  · exact absurd h (Kern_ne_zero hg)
  · obtain ⟨hsf, hprime, hle⟩ := h
    rw [Sset, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Kern_ne_zero hg, hsf, hprime⟩

/-- At most one element of the box has kernel `0` (namely `w = 0`). -/
private lemma aux_aCount_zero_le_one (R : ℤ) : aCount R 0 ≤ 1 := by
  rw [aCount]
  have hsub : (Work.FIPlan.gBox R).filter (fun w => Kern (Work.FIPlan.gnorm w) = 0) ⊆ {0} := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_singleton]
    have hgz : Work.FIPlan.gnorm w = 0 := by
      by_contra hne
      exact (Kern_ne_zero hne) hw.2
    exact (aux_gnorm_eq_zero w).mp hgz
  calc ((Work.FIPlan.gBox R).filter (fun w => Kern (Work.FIPlan.gnorm w) = 0)).card
      ≤ ({0} : Finset GaussianInt).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton 0

/-- Double count: the pairs of box elements with equal `f`-value are the disjoint union, over
`d` in the image of `f`, of the squares of the fibres. -/
private lemma aux_card_filter_prod_eq_sum_sq (B : Finset GaussianInt) (f : GaussianInt → ℕ) :
    ((B ×ˢ B).filter (fun p : GaussianInt × GaussianInt => f p.1 = f p.2)).card
      = ∑ d ∈ B.image f, ((B.filter (fun w => f w = d)).card) ^ 2 := by
  have hset : (B ×ˢ B).filter (fun p : GaussianInt × GaussianInt => f p.1 = f p.2)
      = (B.image f).biUnion
          (fun d => (B.filter (fun w => f w = d)) ×ˢ (B.filter (fun w => f w = d))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨f p.1, ⟨p.1, h1, rfl⟩, ⟨⟨h1, rfl⟩, h2, h3.symm⟩⟩
    · rintro ⟨d, ⟨w, hw, hwd⟩, hp1, hp2⟩
      exact ⟨⟨hp1.1, hp2.1⟩, by rw [hp1.2, hp2.2]⟩
  rw [hset, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.card_product, sq]
  · intro d _ d' _ hne
    show Disjoint ((B.filter (fun w => f w = d)) ×ˢ (B.filter (fun w => f w = d)))
      ((B.filter (fun w => f w = d')) ×ˢ (B.filter (fun w => f w = d')))
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_product, Finset.mem_filter] at hp hp'
    exact hne (by rw [← hp.1.2, ← hp'.1.2])

/-! ## The main counting lemma -/

/-- The counting lemma of Area 7, in the natural-number form used internally. -/
private lemma pairCount_aux (R : ℤ) (B : Finset GaussianInt) (hB : B = Work.FIPlan.gBox R) :
    ((B ×ˢ B).filter (fun p : GaussianInt × GaussianInt =>
        Nat.sqrt (Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2)) ^ 2
          = Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2))).card
      ≤ 2 * B.card + 1 + ∑ d ∈ Sset R, (aCount R d) ^ 2 := by
  -- the "odd part is a square" pairs are contained in the equal-kernel pairs together with the
  -- pairs having a zero coordinate
  have hQcard : ((B ×ˢ B).filter (fun p : GaussianInt × GaussianInt =>
        Nat.sqrt (Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2)) ^ 2
          = Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2))).card
      ≤ ((B ×ˢ B).filter (fun p : GaussianInt × GaussianInt =>
            Kern (Work.FIPlan.gnorm p.1) = Kern (Work.FIPlan.gnorm p.2))).card
        + ((B ×ˢ B).filter (fun p : GaussianInt × GaussianInt =>
            p.1 = 0 ∨ p.2 = 0)).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hpred⟩ := hp
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    rcases (aux_cond_iff (Work.FIPlan.gnorm p.1) (Work.FIPlan.gnorm p.2)).mp hpred with h | h
    · rcases h with h | h
      · exact Or.inr ⟨⟨hp1, hp2⟩, Or.inl ((aux_gnorm_eq_zero p.1).mp h)⟩
      · exact Or.inr ⟨⟨hp1, hp2⟩, Or.inr ((aux_gnorm_eq_zero p.2).mp h)⟩
    · exact Or.inl ⟨⟨hp1, hp2⟩, h⟩
  -- the equal-kernel pairs
  have hCcard : ((B ×ˢ B).filter (fun p : GaussianInt × GaussianInt =>
            Kern (Work.FIPlan.gnorm p.1) = Kern (Work.FIPlan.gnorm p.2))).card
      ≤ 1 + ∑ d ∈ Sset R, (aCount R d) ^ 2 := by
    have hE := aux_card_filter_prod_eq_sum_sq B (fun w => Kern (Work.FIPlan.gnorm w))
    have hE' : ((B ×ˢ B).filter (fun p : GaussianInt × GaussianInt =>
          Kern (Work.FIPlan.gnorm p.1) = Kern (Work.FIPlan.gnorm p.2))).card
        = ∑ d ∈ B.image (fun w => Kern (Work.FIPlan.gnorm w)),
            ((B.filter (fun w => Kern (Work.FIPlan.gnorm w) = d)).card) ^ 2 := hE
    rw [hE']
    have hfib : ∀ d : ℕ, (B.filter (fun w => Kern (Work.FIPlan.gnorm w) = d)).card = aCount R d := by
      intro d
      rw [aCount, hB]
    simp only [hfib]
    -- every nonzero value of the kernel lies in `Sset R`
    have hsub : (B.image (fun w => Kern (Work.FIPlan.gnorm w))).filter
        (fun d => d ∉ Sset R) ⊆ {0} := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_image] at hd
      obtain ⟨⟨w, hw, hwd⟩, hdnS⟩ := hd
      rw [Finset.mem_singleton]
      by_contra hne
      have hw0 : w ≠ 0 := by
        rintro rfl
        exact hne (by rw [← hwd, (aux_gnorm_eq_zero (0 : GaussianInt)).mpr rfl, Kern_zero])
      have hmem : Kern (Work.FIPlan.gnorm w) ∈ Sset R :=
        aux_Kern_mem_Sset R w (by rw [← hB]; exact hw) hw0
      rw [hwd] at hmem
      exact absurd hmem hdnS
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := B.image (fun w => Kern (Work.FIPlan.gnorm w)))
      (p := fun d => d ∈ Sset R) (f := fun d => (aCount R d) ^ 2)
    have h1 : ∑ d ∈ (B.image (fun w => Kern (Work.FIPlan.gnorm w))).filter
          (fun d => d ∈ Sset R), (aCount R d) ^ 2
        ≤ ∑ d ∈ Sset R, (aCount R d) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => (Finset.mem_filter.mp hd).2)
        (fun _ _ _ => Nat.zero_le _)
    have h2 : ∑ d ∈ (B.image (fun w => Kern (Work.FIPlan.gnorm w))).filter
          (fun d => d ∉ Sset R), (aCount R d) ^ 2 ≤ 1 := by
      have h3 : ∑ d ∈ (B.image (fun w => Kern (Work.FIPlan.gnorm w))).filter
            (fun d => d ∉ Sset R), (aCount R d) ^ 2
          ≤ ∑ d ∈ ({0} : Finset ℕ), (aCount R d) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      have h4 : (aCount R 0) ^ 2 ≤ 1 := by
        have h0 := aux_aCount_zero_le_one R
        calc (aCount R 0) ^ 2 = (aCount R 0) * (aCount R 0) := pow_two _
          _ ≤ 1 * 1 := Nat.mul_le_mul h0 h0
          _ = 1 := one_mul 1
      calc ∑ d ∈ (B.image (fun w => Kern (Work.FIPlan.gnorm w))).filter
            (fun d => d ∉ Sset R), (aCount R d) ^ 2
          ≤ ∑ d ∈ ({0} : Finset ℕ), (aCount R d) ^ 2 := h3
        _ = (aCount R 0) ^ 2 := Finset.sum_singleton ..
        _ ≤ 1 := h4
    omega
  -- the pairs with a zero coordinate
  have hAcard : ((B ×ˢ B).filter (fun p : GaussianInt × GaussianInt =>
            p.1 = 0 ∨ p.2 = 0)).card ≤ 2 * B.card := by
    have hsub : (B ×ˢ B).filter (fun p : GaussianInt × GaussianInt => p.1 = 0 ∨ p.2 = 0)
        ⊆ (B.filter (fun b : GaussianInt => b = 0) ×ˢ B)
            ∪ (B ×ˢ (B.filter (fun b : GaussianInt => b = 0))) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨h1, h2⟩, hz | hz⟩ := hp
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr
          ⟨by rw [Finset.mem_filter]; exact ⟨h1, hz⟩, h2⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_product.mpr
          ⟨h1, by rw [Finset.mem_filter]; exact ⟨h2, hz⟩⟩))
    have hcard0 : (B.filter (fun b : GaussianInt => b = 0)).card ≤ 1 := by
      calc (B.filter (fun b : GaussianInt => b = 0)).card ≤ ({0} : Finset GaussianInt).card :=
            Finset.card_le_card
              (fun b hb => Finset.mem_singleton.mpr (Finset.mem_filter.mp hb).2)
        _ = 1 := Finset.card_singleton 0
    have h1 : ((B.filter (fun b : GaussianInt => b = 0)) ×ˢ B).card ≤ B.card := by
      rw [Finset.card_product]
      calc (B.filter (fun b : GaussianInt => b = 0)).card * B.card ≤ 1 * B.card :=
            Nat.mul_le_mul_right _ hcard0
        _ = B.card := one_mul _
    have h2 : (B ×ˢ (B.filter (fun b : GaussianInt => b = 0))).card ≤ B.card := by
      rw [Finset.card_product]
      calc B.card * (B.filter (fun b : GaussianInt => b = 0)).card ≤ B.card * 1 :=
            Nat.mul_le_mul_left _ hcard0
        _ = B.card := mul_one _
    refine le_trans (Finset.card_le_card hsub) ?_
    calc ((B.filter (fun b : GaussianInt => b = 0) ×ˢ B)
            ∪ (B ×ˢ (B.filter (fun b : GaussianInt => b = 0)))).card
        ≤ ((B.filter (fun b : GaussianInt => b = 0)) ×ˢ B).card
            + (B ×ˢ (B.filter (fun b : GaussianInt => b = 0))).card := Finset.card_union_le _ _
      _ ≤ B.card + B.card := Nat.add_le_add h1 h2
      _ = 2 * B.card := by ring
  omega

theorem pairCount_le (R : ℤ) :
    ((((Work.FIPlan.gBox R) ×ˢ (Work.FIPlan.gBox R)).filter
        (fun p : GaussianInt × GaussianInt =>
          Nat.sqrt (Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2)) ^ 2
            = Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2))).card : ℝ)
      ≤ 2 * ((Work.FIPlan.gBox R).card : ℝ) + 1
        + ∑ d ∈ Sset R, ((aCount R d : ℝ)) ^ 2 := by
  have h := pairCount_aux R (Work.FIPlan.gBox R) rfl
  have hcast : (((((Work.FIPlan.gBox R) ×ˢ (Work.FIPlan.gBox R)).filter
        (fun p : GaussianInt × GaussianInt =>
          Nat.sqrt (Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2)) ^ 2
            = Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2))).card : ℝ))
      ≤ 2 * ((Work.FIPlan.gBox R).card : ℝ) + 1
        + ∑ d ∈ Sset R, ((aCount R d : ℝ)) ^ 2 := by
    have h'' : ((((Work.FIPlan.gBox R) ×ˢ (Work.FIPlan.gBox R)).filter
        (fun p : GaussianInt × GaussianInt =>
          Nat.sqrt (Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2)) ^ 2
            = Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2))).card : ℝ)
        ≤ ((2 * (Work.FIPlan.gBox R).card + 1
            + ∑ d ∈ Sset R, (aCount R d) ^ 2 : ℕ) : ℝ) := Nat.cast_le (α := ℝ) |>.mpr h
    push_cast at h''
    exact h''
  exact hcast

end

end Work.FIArea7
