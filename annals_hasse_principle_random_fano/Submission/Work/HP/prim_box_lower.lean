import Mathlib
import Submission.Work.HP.div_count

/-!
# A lower bound for the number of primitive vectors in a box

For a finite index type `ι` and `B : ℕ`, the number of primitive vectors in the
coordinate box `∏ᵢ [-B, B] ⊂ (ι → ℤ)` is at least
`#box - 1 - Σ_{g=2}^{B} #{vectors of the box all of whose coordinates are divisible by g}`.

Route: a vector of the box is either zero, primitive, or nonzero and non-primitive.
In the last case its gcd `d` satisfies `2 ≤ d ≤ B` and divides every coordinate, so the
vector lies in the union, over `2 ≤ g ≤ B`, of the sets of vectors whose coordinates are
all divisible by `g`.  Hence the number of nonzero non-primitive vectors is at most the
sum of the cardinalities of those sets; each such cardinality is at most `(2 * (B/g) + 1)^N`
(`Work.HP.div_count`).  The rest is arithmetic.
-/

namespace Work.HP

section gcdFacts

variable {ι : Type*} [Fintype ι]

/-- The gcd of the coordinates of `a` is nonzero as soon as `a` is. -/
private lemma gcd_univ_ne_zero {a : ι → ℤ} (hne : a ≠ 0) : Finset.univ.gcd a ≠ 0 := by
  intro h
  refine hne (funext fun i => ?_)
  exact (Finset.gcd_eq_zero_iff.mp h) i (Finset.mem_univ i)

/-- The gcd of a finset of integers is normalized, hence nonnegative. -/
private lemma gcd_univ_nonneg {a : ι → ℤ} : (0 : ℤ) ≤ Finset.univ.gcd a :=
  (Int.nonneg_iff_normalize_eq_self _).mp (Finset.normalize_gcd)

end gcdFacts

/-- A nonzero vector whose coordinates are bounded by `B` and whose gcd is not `1` has a
common divisor `g` with `2 ≤ g ≤ B` (namely the absolute value of its gcd). -/
private lemma exists_dvd_coords_of_gcd_ne_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a : ι → ℤ} {B : ℕ} (hne : a ≠ 0) (hgcd : Finset.univ.gcd a ≠ 1)
    (hB : ∀ i, |a i| ≤ (B : ℤ)) :
    ∃ g ∈ Finset.Icc 2 B, ∀ i, (g : ℤ) ∣ a i := by
  have hnn : (0 : ℤ) ≤ Finset.univ.gcd a := gcd_univ_nonneg
  have hcast : (((Finset.univ.gcd a).natAbs : ℕ) : ℤ) = Finset.univ.gcd a :=
    Int.natAbs_of_nonneg hnn
  have hne0 : (Finset.univ.gcd a).natAbs ≠ 0 := by
    intro h
    exact gcd_univ_ne_zero hne (by rw [← hcast, h]; norm_num)
  have hne1 : (Finset.univ.gcd a).natAbs ≠ 1 := by
    intro h
    exact hgcd (by rw [← hcast, h]; norm_num)
  refine ⟨(Finset.univ.gcd a).natAbs, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    constructor
    · omega
    · have hex : ∃ i, a i ≠ 0 := by
        by_contra h
        exact hne (funext fun i => by by_contra hi; exact h ⟨i, hi⟩)
      obtain ⟨i, hi⟩ := hex
      have h1 : (Finset.univ.gcd a).natAbs ≤ (a i).natAbs :=
        Int.natAbs_le_of_dvd_ne_zero (Finset.gcd_dvd (Finset.mem_univ i)) hi
      have h2 : (a i).natAbs ≤ B := by
        have h := hB i
        rw [Int.abs_eq_natAbs] at h
        exact_mod_cast h
      omega
  · intro i
    exact Int.natAbs_dvd.mpr (Finset.gcd_dvd (Finset.mem_univ i))

/-- The number of primitive vectors in the coordinate box `∏ᵢ [-B, B] ⊂ (ι → ℤ)` is at least `#box - 1 - Σ_{g=2}^{B} #{vectors of the box all of whose coordinates are divisible by g}`.  Route: a vector in the box is either zero, primitive, or non-primitive and non-zero; the latter have `2 ≤ gcd ≤ B`, and the gcd divides every coordinate, so they lie in the union over `2 ≤ g ≤ B` of the `g`-divisible vectors.  The number of `g`-divisible vectors of the box of radius `B` is `(2 * (B/g) + 1)^N`, by the bijection `a ↦ a/g` with the box of radius `B/g`. -/
theorem prim_box_lower {ι : Type*} [Fintype ι] [DecidableEq ι] (B : ℕ) :
    ((Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ))).card : ℝ) - 1
      - ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ (Fintype.card ι)
    ≤ (((Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
          (fun a => Finset.univ.gcd a = 1)).card : ℝ) := by
  classical
  set box : Finset (ι → ℤ) := Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ)) with hbox
  set prim : Finset (ι → ℤ) := box.filter (fun a => Finset.univ.gcd a = 1) with hprim
  set rest : Finset (ι → ℤ) := box.filter (fun a => a ≠ 0 ∧ Finset.univ.gcd a ≠ 1) with hrest
  set divg : ℕ → Finset (ι → ℤ) := fun g => box.filter (fun a => ∀ i, (g : ℤ) ∣ a i) with hdivg
  -- the nonzero non-primitive vectors are covered by the union of the `g`-divisible sets
  have hcover : rest ⊆ Finset.biUnion (Finset.Icc 2 B) divg := by
    intro a ha
    rw [hrest, Finset.mem_filter] at ha
    obtain ⟨hboxmem, hne, hgcd⟩ := ha
    have hcoords : ∀ i, a i ∈ Finset.Icc (-(B : ℤ)) (B : ℤ) := by
      rw [hbox, Fintype.mem_piFinset] at hboxmem
      exact hboxmem
    obtain ⟨g, hg, hgd⟩ := exists_dvd_coords_of_gcd_ne_one hne hgcd (fun i => by
      have := hcoords i; rw [Finset.mem_Icc] at this; exact abs_le.mpr this)
    rw [Finset.mem_biUnion]
    refine ⟨g, hg, ?_⟩
    rw [hdivg, Finset.mem_filter]
    exact ⟨by rw [hbox, Fintype.mem_piFinset]; exact hcoords, hgd⟩
  have hrest_le : rest.card ≤ ∑ g ∈ Finset.Icc 2 B, (divg g).card :=
    le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
  have hsum_le : (∑ g ∈ Finset.Icc 2 B, (divg g).card)
      ≤ ∑ g ∈ Finset.Icc 2 B, (2 * (B / g) + 1) ^ Fintype.card ι := by
    apply Finset.sum_le_sum
    intro g hg
    have hg1 : 1 ≤ g := le_trans (by norm_num) (Finset.mem_Icc.mp hg).1
    simp only [hdivg, hbox]
    exact div_count B g hg1
  -- decomposition of the box into zero, primitive, and nonzero non-primitive vectors
  have hzero_le : (box.filter (fun a => a = 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    rw [ha.2, hb.2]
  have hsplit1 : (box.filter (fun a => a = 0)).card + (box.filter (fun a => a ≠ 0)).card
      = box.card :=
    Finset.card_filter_add_card_filter_not (s := box) (p := fun a => a = 0)
  have hsplit2 : (box.filter (fun a => a ≠ 0)).card
      = ((box.filter (fun a => a ≠ 0)).filter (fun a => Finset.univ.gcd a = 1)).card
        + ((box.filter (fun a => a ≠ 0)).filter (fun a => Finset.univ.gcd a ≠ 1)).card :=
    (Finset.card_filter_add_card_filter_not (s := box.filter (fun a => a ≠ 0))
      (p := fun a => Finset.univ.gcd a = 1)).symm
  have hff1 : (box.filter (fun a => a ≠ 0)).filter (fun a => Finset.univ.gcd a = 1)
      = box.filter (fun a => a ≠ 0 ∧ Finset.univ.gcd a = 1) := by
    rw [Finset.filter_filter]
  have hff2 : (box.filter (fun a => a ≠ 0)).filter (fun a => Finset.univ.gcd a ≠ 1)
      = rest := by
    rw [hrest, Finset.filter_filter]
  have hA_le : (box.filter (fun a => a ≠ 0 ∧ Finset.univ.gcd a = 1)).card ≤ prim.card := by
    apply Finset.card_le_card
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [hprim, Finset.mem_filter]
    exact ⟨ha.1, ha.2.2⟩
  have hb : box.card ≤ prim.card + 1 + rest.card := by
    have h2 := hsplit2
    rw [hff1, hff2] at h2
    omega
  have hcardNat : box.card ≤ prim.card + 1
      + ∑ g ∈ Finset.Icc 2 B, (2 * (B / g) + 1) ^ Fintype.card ι := by
    have h := le_trans hrest_le hsum_le
    omega
  have hs : ((∑ g ∈ Finset.Icc 2 B, (2 * (B / g) + 1) ^ Fintype.card ι : ℕ) : ℝ)
      = ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ (Fintype.card ι) := by
    push_cast
    rfl
  have hR : (box.card : ℝ) ≤ (prim.card : ℝ) + 1
      + ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ (Fintype.card ι) := by
    have h' : (box.card : ℝ) ≤ (prim.card : ℝ) + 1
        + ((∑ g ∈ Finset.Icc 2 B, (2 * (B / g) + 1) ^ Fintype.card ι : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    rwa [hs] at h'
  linarith

end Work.HP
