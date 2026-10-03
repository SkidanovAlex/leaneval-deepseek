import Mathlib
import Submission.Work.Peluse.Pel51.defs

/-!
# Regime two of the `badP` comparison (`lemma51P 1` from `lemma51P 2`)

The datum `b = (b₀, b₀ + 1)` on `Fin 2` has the property that the two directions differ by one,
so the gcd condition of the level-`2` bad set is *automatic*

  `gcd(a + b₀, a + b₀ + 1) = 1`  and  `1 ≤ 1/η`  because  `η ≤ 1`,

while the size condition of the level-`1` bad set is the `i = 0` half of the level-`2` size
condition.  Hence

  `bad₂ ⊆ bad₁ ∪ {a : η M₁ ≤ |a + b₀| ∧ |a + b₀ + 1| < η M₁}`,

and the extra set has at most **one** element: if `y := η M₁` and `x := a + b₀`, the two
conditions read `y ≤ |x|` and `|x + 1| < y`; the first forces `x < 0` (for `x ≥ 0` one has
`|x + 1| = x + 1 ≥ |x| ≥ y`), and then they read `y ≤ -x < y + 1`, i.e. `-x` is an integer in
the interval `[y, y + 1)` of length one.  So `#bad₂ ≤ #bad₁ + 1`.

The file assembles the following pieces:

* `gcd_self_add_one_int` : `Int.gcd z (z+1) = 1` (Bézout witness `1 = (-1)·z + 1·(z+1)`);
* `gcd_ratio_le_one`    : the level-`2` *gcd* condition, given `η > 0` and `η ≤ 1`;
* `badP_one_mem_iff` / `badP_two_mem_iff` : the two bad sets, unfolded (the `t = 1` pairwise
  condition and the `t = 2` gcd condition are the only things removed);
* `int_le_of_cast_lt_add_one` / `int_eq_of_shift_bad` : the one-element combinatorial core;
* `badP_regime_two` : the target.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Pel51

open Work.Peluse

/-- `Int.gcd z (z + 1) = 1`: the Bézout identity `1 = (-1) * z + 1 * (z + 1)` exhibits `1` as a
`ℤ`-linear combination, so `gcd z (z+1) ∣ 1`. -/
lemma gcd_self_add_one_int (z : ℤ) : Int.gcd z (z + 1) = 1 := by
  have hdvd : Int.gcd z (z + 1) ∣ 1 := by
    rw [Int.gcd_dvd_iff]
    exact ⟨-1, 1, by push_cast; ring⟩
  exact Nat.dvd_one.mp hdvd

/-- The gcd/size ratio bound used for the level-`2` datum `(b₀, b₀ + 1)`: if `w - z = 1` then the
gcd of `z` and `w` is `1`, and `1 ≤ 1/η` because `η ≤ 1`. -/
lemma gcd_ratio_le_one {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {z w : ℤ} (h : w - z = 1) :
    ((Int.gcd z w : ℕ) : ℝ) ≤ 1 / η := by
  have hdvd : Int.gcd z w ∣ 1 := by
    rw [Int.gcd_dvd_iff]
    exact ⟨-1, 1, by ring_nf; linarith⟩
  rw [Nat.dvd_one.mp hdvd]
  push_cast
  exact (one_le_div hη0).mpr hη1

/-- The level-`1` bad set of `badP`, unfolded: the pairwise gcd condition on `Fin 1` is vacuous,
so only the size condition remains. -/
lemma badP_one_mem_iff {M₁ : ℕ} {b₀ : ℤ} {η : ℝ} {a : ℕ} :
    a ∈ badP 1 M₁ (fun _ : Fin 1 => b₀) η ↔
      a ∈ Finset.Icc 1 M₁ ∧ ¬ (η * (M₁ : ℝ) ≤ ((|((a : ℤ) + b₀)| : ℤ) : ℝ)) := by
  rw [badP, Finset.mem_filter]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    intro hB
    exact h ⟨fun i k hik => absurd (Subsingleton.elim i k) hik, fun i => by simpa using hB⟩
  · rintro ⟨hm, hB⟩
    refine ⟨hm, ?_⟩
    rintro ⟨-, h2⟩
    exact hB (by simpa using h2 0)

/-- The level-`2` bad set for the datum `(b₀, b₀ + 1)`, unfolded: the pairwise gcd condition is
automatic (`gcd_ratio_le_one`), so it reduces to the conjunction of the two size conditions. -/
lemma badP_two_mem_iff {M₁ : ℕ} {b₀ : ℤ} {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (a : ℕ) :
    a ∈ badP 2 M₁ (fun i : Fin 2 => if i = 0 then b₀ else b₀ + 1) η ↔
      a ∈ Finset.Icc 1 M₁ ∧
        ¬ ((η * (M₁ : ℝ) ≤ ((|((a : ℤ) + b₀)| : ℤ) : ℝ))
          ∧ (η * (M₁ : ℝ) ≤ ((|((a : ℤ) + (b₀ + 1))| : ℤ) : ℝ))) := by
  rw [badP, Finset.mem_filter]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨hm, fun ⟨hP, hQ⟩ => h ⟨?_, ?_⟩⟩
    · intro i k hik
      have hcases : (i = 0 ∧ k = 1) ∨ (i = 1 ∧ k = 0) := by
        revert hik
        fin_cases i <;> fin_cases k <;> simp_all
      have e0 : (if (0 : Fin 2) = 0 then b₀ else b₀ + 1) = b₀ := if_pos rfl
      have e1 : (if (1 : Fin 2) = 0 then b₀ else b₀ + 1) = b₀ + 1 :=
        if_neg (by decide)
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [e0, e1]
        exact gcd_ratio_le_one hη0 hη1 (by ring)
      · rw [Int.gcd_comm, e0, e1]
        exact gcd_ratio_le_one hη0 hη1 (by ring)
    · intro i
      fin_cases i
      · simpa using hP
      · simpa using hQ
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    rintro ⟨-, hB⟩
    exact h ⟨by simpa using hB 0, by simpa using hB 1⟩

/-- Integrality step: an integer strictly below `n + 1` is at most `n`. -/
lemma int_le_of_cast_lt_add_one {m n : ℤ} (h : (m : ℝ) < (n : ℝ) + 1) : m ≤ n := by
  by_contra hmn
  have hlt : n < m := not_le.mp hmn
  have h1 : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ m)
  linarith

/-- The combinatorial core: at most one integer `x` satisfies `y ≤ |x|` and `|x + 1| < y`.

Indeed the first inequality with `x ≥ 0` gives `|x + 1| = x + 1 ≥ |x| ≥ y`, so `x < 0`; then
`y ≤ |x| = -x` and `|x + 1| = -x - 1 < y`, i.e. `y ≤ -x < y + 1`, and an interval of length one
contains at most one integer. -/
lemma int_eq_of_shift_bad {y : ℝ} {x x' : ℤ}
    (h1 : y ≤ ((|x| : ℤ) : ℝ)) (h2 : ((|x + 1| : ℤ) : ℝ) < y)
    (h1' : y ≤ ((|x'| : ℤ) : ℝ)) (h2' : ((|x' + 1| : ℤ) : ℝ) < y) : x = x' := by
  have key : ∀ z : ℤ, y ≤ ((|z| : ℤ) : ℝ) → ((|z + 1| : ℤ) : ℝ) < y →
      (y ≤ ((-z : ℤ) : ℝ)) ∧ (((-z : ℤ) : ℝ) < y + 1) := by
    intro z hz hz'
    have hzR : y ≤ |(z : ℝ)| := by
      simpa only [Int.cast_abs] using hz
    have hzR' : |(z : ℝ) + 1| < y := by
      have hcast : (((z + 1 : ℤ)) : ℝ) = (z : ℝ) + 1 := by push_cast; ring
      simpa only [Int.cast_abs, hcast] using hz'
    have hzneg : z < 0 := by
      by_contra h
      have hz0 : (0 : ℝ) ≤ (z : ℝ) := by
        exact_mod_cast (not_lt.mp h : (0 : ℤ) ≤ z)
      rw [abs_of_nonneg hz0] at hzR
      have hz1 : (0 : ℝ) ≤ (z : ℝ) + 1 := by linarith
      rw [abs_of_nonneg hz1] at hzR'
      linarith
    have hzle : (z : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hzneg)
    rw [abs_of_nonpos hzle] at hzR
    have hz1le : (z : ℝ) + 1 ≤ 0 := by exact_mod_cast (by omega : z + 1 ≤ 0)
    rw [abs_of_nonpos hz1le] at hzR'
    have hneg : ((-z : ℤ) : ℝ) = -(z : ℝ) := by push_cast; ring
    constructor
    · rw [hneg]; linarith
    · rw [hneg]; linarith
  obtain ⟨hn, hn'⟩ := key x h1 h2
  obtain ⟨hm, hm'⟩ := key x' h1' h2'
  have hle : (-x : ℤ) ≤ (-x' : ℤ) := int_le_of_cast_lt_add_one (by linarith)
  have hle' : (-x' : ℤ) ≤ (-x : ℤ) := int_le_of_cast_lt_add_one (by linarith)
  have hneg_eq : (-x : ℤ) = (-x' : ℤ) := le_antisymm hle hle'
  omega

theorem badP_regime_two (M₁ : ℕ) (b₀ : ℤ) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (Work.Peluse.Pel51.badP 2 M₁ (fun i : Fin 2 => if i = 0 then b₀ else b₀ + 1) η).card
      ≤ (Work.Peluse.Pel51.badP 1 M₁ (fun _ : Fin 1 => b₀) η).card + 1 := by
  have hcard : ((badP 2 M₁ (fun i : Fin 2 => if i = 0 then b₀ else b₀ + 1) η) \
      (badP 1 M₁ (fun _ : Fin 1 => b₀) η)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_sdiff] at ha hb
    obtain ⟨ha2, ha1⟩ := ha
    obtain ⟨hb2, hb1⟩ := hb
    have h2a := (badP_two_mem_iff hη0 hη1 a).mp ha2
    have h2b := (badP_two_mem_iff hη0 hη1 b).mp hb2
    have hPa : η * (M₁ : ℝ) ≤ ((|((a : ℤ) + b₀)| : ℤ) : ℝ) := by
      by_contra hcon
      exact ha1 ((badP_one_mem_iff (a := a)).mpr ⟨h2a.1, hcon⟩)
    have hPb : η * (M₁ : ℝ) ≤ ((|((b : ℤ) + b₀)| : ℤ) : ℝ) := by
      by_contra hcon
      exact hb1 ((badP_one_mem_iff (a := b)).mpr ⟨h2b.1, hcon⟩)
    have hQa : ¬ (η * (M₁ : ℝ) ≤ ((|((a : ℤ) + (b₀ + 1))| : ℤ) : ℝ)) :=
      fun hq => h2a.2 ⟨hPa, hq⟩
    have hQb : ¬ (η * (M₁ : ℝ) ≤ ((|((b : ℤ) + (b₀ + 1))| : ℤ) : ℝ)) :=
      fun hq => h2b.2 ⟨hPb, hq⟩
    have hxa : ((|((a : ℤ) + b₀) + 1| : ℤ) : ℝ) < η * (M₁ : ℝ) := by
      have hz : ((a : ℤ) + (b₀ + 1)) = ((a : ℤ) + b₀) + 1 := by ring
      rw [hz] at hQa
      exact not_le.mp hQa
    have hxb : ((|((b : ℤ) + b₀) + 1| : ℤ) : ℝ) < η * (M₁ : ℝ) := by
      have hz : ((b : ℤ) + (b₀ + 1)) = ((b : ℤ) + b₀) + 1 := by ring
      rw [hz] at hQb
      exact not_le.mp hQb
    have hshift := int_eq_of_shift_bad (y := η * (M₁ : ℝ))
      (x := (a : ℤ) + b₀) (x' := (b : ℤ) + b₀) hPa hxa hPb hxb
    have hab : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast hab
  have hmain := Finset.card_sdiff_add_card_inter
    (badP 2 M₁ (fun i : Fin 2 => if i = 0 then b₀ else b₀ + 1) η)
    (badP 1 M₁ (fun _ : Fin 1 => b₀) η)
  have hinter : ((badP 2 M₁ (fun i : Fin 2 => if i = 0 then b₀ else b₀ + 1) η)
      ∩ (badP 1 M₁ (fun _ : Fin 1 => b₀) η)).card
      ≤ (badP 1 M₁ (fun _ : Fin 1 => b₀) η).card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

end Work.Peluse.Pel51
