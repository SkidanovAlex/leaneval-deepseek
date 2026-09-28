import Mathlib

/-!
# Cardinality of coordinate boxes in `ℤ^ι`

For a finite index type `ι` and `B : ℕ`, the coordinate box
`∏ i, [-B, B] ⊆ (ι → ℤ)` has `(2B+1)^|ι|` elements.  Moreover, for `g ≥ 1`
the vectors of the box all of whose coordinates are divisible by `g` are in
bijection (via `a ↦ a / g`, with inverse `k ↦ g • k`) with the box of radius
`B / g`, so their number is `(2⌊B/g⌋+1)^|ι|`.
-/

set_option autoImplicit false

namespace Work.HP

/-- A single interval of integers `[-B, B]` has `2B+1` elements. -/
private lemma box_single_card (B : ℕ) :
    (Finset.Icc (-(B : ℤ)) (B : ℤ)).card = 2 * B + 1 := by
  rw [Int.card_Icc]; omega

/-- The coordinates of the box that are divisible by `g` are exactly the
multiples `g * k` of an integer `k` of the box of radius `B / g`. -/
private lemma box_div_iff (B g : ℕ) (hg : 1 ≤ g) (a : ℤ) :
    ((g : ℤ) ∣ a ∧ -(B : ℤ) ≤ a ∧ a ≤ (B : ℤ)) ↔
      ∃ k : ℤ, -(((B / g : ℕ) : ℤ)) ≤ k ∧ k ≤ ((B / g : ℕ) : ℤ) ∧
        a = (g : ℤ) * k := by
  have hgpos : (0 : ℤ) < (g : ℤ) := by omega
  constructor
  · rintro ⟨hdvd, hlo, hhi⟩
    refine ⟨a / (g : ℤ), ?_, ?_, ?_⟩
    · rw [Int.natCast_ediv, neg_le, Int.le_ediv_iff_mul_le hgpos]
      have hm : a / (g : ℤ) * (g : ℤ) = a := Int.ediv_mul_cancel hdvd
      have hmul : -(a / (g : ℤ)) * (g : ℤ) = -a := by rw [neg_mul, hm]
      rw [hmul]; linarith
    · rw [Int.natCast_ediv, Int.le_ediv_iff_mul_le hgpos]
      have hm : a / (g : ℤ) * (g : ℤ) = a := Int.ediv_mul_cancel hdvd
      rw [hm]; linarith
    · have hm : a / (g : ℤ) * (g : ℤ) = a := Int.ediv_mul_cancel hdvd
      rw [mul_comm]; exact hm.symm
  · rintro ⟨k, hklo, hkhi, rfl⟩
    refine ⟨⟨k, rfl⟩, ?_, ?_⟩
    · rw [Int.natCast_ediv] at hklo
      have hk : -k ≤ (B : ℤ) / (g : ℤ) := by linarith
      have h2 : (-k) * (g : ℤ) ≤ (B : ℤ) := (Int.le_ediv_iff_mul_le hgpos).mp hk
      have h3 : (-k) * (g : ℤ) = -((g : ℤ) * k) := by ring
      rw [h3] at h2; linarith
    · rw [Int.natCast_ediv] at hkhi
      have h2 : k * (g : ℤ) ≤ (B : ℤ) := (Int.le_ediv_iff_mul_le hgpos).mp hkhi
      have h3 : k * (g : ℤ) = (g : ℤ) * k := mul_comm _ _
      rw [h3] at h2; linarith

/-- The number of vectors in the box `∏ i, [-B, B]` all of whose coordinates
are divisible by `g` equals the size of the box of radius `B / g`. -/
private lemma box_filter_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B g : ℕ) (hg : 1 ≤ g) :
    (((Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
        (fun a => ∀ i, (g : ℤ) ∣ a i)).card)
      = (2 * (B / g) + 1) ^ Fintype.card ι := by
  have hgpos : (0 : ℤ) < (g : ℤ) := by omega
  have hgne : (g : ℤ) ≠ 0 := ne_of_gt hgpos
  have hdiv : ∀ a : ℤ, ((g : ℤ) ∣ a ∧ -(B : ℤ) ≤ a ∧ a ≤ (B : ℤ)) ↔
      ∃ k : ℤ, -(((B / g : ℕ) : ℤ)) ≤ k ∧ k ≤ ((B / g : ℕ) : ℤ) ∧
        a = (g : ℤ) * k := fun a => box_div_iff B g hg a
  have hcard :
      (Fintype.piFinset (fun _ : ι => Finset.Icc (-(((B / g : ℕ) : ℤ))) (((B / g : ℕ) : ℤ)))).card
      = ((Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
          (fun a => ∀ i, (g : ℤ) ∣ a i)).card := by
    refine Finset.card_bij
      (fun (k : ι → ℤ)
          (_ : k ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (-(((B / g : ℕ) : ℤ))) (((B / g : ℕ) : ℤ))))
          (i : ι) => (g : ℤ) * k i) ?_ ?_ ?_
    · intro k hk
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [Fintype.mem_piFinset]
        intro i
        have hki := (Fintype.mem_piFinset.mp hk) i
        rw [Finset.mem_Icc] at hki
        exact Finset.mem_Icc.mpr
          ⟨((hdiv ((g : ℤ) * k i)).mpr ⟨k i, hki.1, hki.2, rfl⟩).2.1,
           ((hdiv ((g : ℤ) * k i)).mpr ⟨k i, hki.1, hki.2, rfl⟩).2.2⟩
      · intro i
        exact ⟨k i, rfl⟩
    · intro k1 _ k2 _ heq
      funext i
      exact mul_left_cancel₀ hgne (congrFun heq i)
    · intro b hb
      obtain ⟨hbS, hbP⟩ := Finset.mem_filter.mp hb
      have hbS' : ∀ i, -(B : ℤ) ≤ b i ∧ b i ≤ (B : ℤ) := by
        intro i
        exact Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hbS) i)
      let k : ι → ℤ := fun i => Classical.choose ((hdiv (b i)).mp ⟨hbP i, hbS' i⟩)
      have hk : k ∈ Fintype.piFinset
          (fun _ : ι => Finset.Icc (-(((B / g : ℕ) : ℤ))) (((B / g : ℕ) : ℤ))) := by
        rw [Fintype.mem_piFinset]
        intro i
        exact Finset.mem_Icc.mpr
          ⟨(Classical.choose_spec ((hdiv (b i)).mp ⟨hbP i, hbS' i⟩)).1,
           (Classical.choose_spec ((hdiv (b i)).mp ⟨hbP i, hbS' i⟩)).2.1⟩
      exact ⟨k, hk, by
        funext i
        exact (Classical.choose_spec ((hdiv (b i)).mp ⟨hbP i, hbS' i⟩)).2.2.symm⟩
  rw [← hcard, Fintype.card_piFinset]
  rw [Finset.prod_congr rfl (fun _ _ => (by rw [Int.card_Icc]; omega :
    (Finset.Icc (-(((B / g : ℕ) : ℤ))) (((B / g : ℕ) : ℤ))).card = 2 * (B / g) + 1))]
  rw [Finset.prod_const, Finset.card_univ]

/-- Cardinality of the coordinate box `∏ᵢ [-B, B] ⊂ (ι → ℤ)` and, for `g ≥ 1`, of the subset of vectors all of whose coordinates are divisible by `g`.  The second count follows from the bijection `a ↦ a / g` onto the box of radius `B / g`. -/
theorem box_card {ι : Type*} [Fintype ι] [DecidableEq ι] (B : ℕ) :
    ((Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ))).card : ℝ)
        = (2 * (B : ℝ) + 1) ^ Fintype.card ι ∧
    ∀ g : ℕ, 1 ≤ g →
      (((Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
          (fun a => ∀ i, (g : ℤ) ∣ a i)).card : ℝ)
        = (2 * ((B / g : ℕ) : ℝ) + 1) ^ Fintype.card ι := by
  constructor
  · have hS : (Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ))).card
        = (2 * B + 1) ^ Fintype.card ι := by
      rw [Fintype.card_piFinset]
      rw [Finset.prod_congr rfl (fun _ _ => box_single_card B)]
      rw [Finset.prod_const, Finset.card_univ]
    rw [hS]; push_cast; ring
  · intro g hg
    rw [box_filter_card B g hg]; push_cast; ring

end Work.HP
