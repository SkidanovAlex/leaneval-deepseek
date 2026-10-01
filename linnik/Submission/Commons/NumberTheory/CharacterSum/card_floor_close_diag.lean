import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star

namespace Commons.NumberTheory.CharacterSum

open Finset

/-- If `⌊(N - a p)/l⌋` and `⌊(N - a' p)/l⌋` differ by at most `h`, then
`|a - a'| * p ≤ (h + 2) * l`. -/
private theorem abs_mul_le_of_div_close (p l : ℕ) (N : ℤ) (h : ℕ) (hl : 0 < l) (a a' : ℕ)
    (hc : |(N - (a : ℤ) * (p : ℤ)) / (l : ℤ)
            - (N - (a' : ℤ) * (p : ℤ)) / (l : ℤ)| ≤ (h : ℤ)) :
    |(a : ℤ) - (a' : ℤ)| * (p : ℤ) ≤ ((h : ℤ) + 2) * (l : ℤ) := by
  have hlz : (0 : ℤ) < (l : ℤ) := by exact_mod_cast hl
  have hlzne : (l : ℤ) ≠ 0 := hlz.ne'
  set A : ℤ := N - (a : ℤ) * (p : ℤ) with hA
  set A' : ℤ := N - (a' : ℤ) * (p : ℤ) with hA'
  set q : ℤ := A / (l : ℤ) with hq
  set q' : ℤ := A' / (l : ℤ) with hq'
  set r : ℤ := A % (l : ℤ) with hr
  set r' : ℤ := A' % (l : ℤ) with hr'
  have hAeq : A = (l : ℤ) * q + r := by
    rw [hq, hr]; exact (Int.mul_ediv_add_emod A (l : ℤ)).symm
  have hA'eq : A' = (l : ℤ) * q' + r' := by
    rw [hq', hr']; exact (Int.mul_ediv_add_emod A' (l : ℤ)).symm
  have hqle : |q - q'| ≤ (h : ℤ) := by simpa only [hq, hq', hA, hA'] using hc
  have hr0 : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg _ hlzne
  have hr1 : r ≤ (l : ℤ) := le_of_lt (by rw [hr]; exact Int.emod_lt_of_pos _ hlz)
  have hr'0 : 0 ≤ r' := by rw [hr']; exact Int.emod_nonneg _ hlzne
  have hr'1 : r' ≤ (l : ℤ) := le_of_lt (by rw [hr']; exact Int.emod_lt_of_pos _ hlz)
  have hkey : ((a : ℤ) - (a' : ℤ)) * (p : ℤ) = (l : ℤ) * (q' - q) + (r' - r) := by
    have h1 : A' - A = ((a : ℤ) - (a' : ℤ)) * (p : ℤ) := by rw [hA, hA']; ring
    rw [← h1, hA'eq, hAeq]; ring
  have hqq : |q' - q| ≤ (h : ℤ) := by rw [abs_sub_comm]; exact hqle
  have hrsub : |r' - r| ≤ (l : ℤ) * 2 := by
    rw [abs_le]; constructor <;> linarith [hr0, hr1, hr'0, hr'1]
  calc |(a : ℤ) - (a' : ℤ)| * (p : ℤ)
      = |((a : ℤ) - (a' : ℤ)) * (p : ℤ)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (p : ℤ))]
    _ = |(l : ℤ) * (q' - q) + (r' - r)| := by rw [hkey]
    _ ≤ |(l : ℤ) * (q' - q)| + |r' - r| := abs_add_le _ _
    _ = (l : ℤ) * |q' - q| + |r' - r| := by rw [abs_mul, abs_of_pos hlz]
    _ ≤ (l : ℤ) * (h : ℤ) + (l : ℤ) * 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hqq (le_of_lt hlz)) hrsub
    _ = ((h : ℤ) + 2) * (l : ℤ) := by ring

/-- A finite set of integers all lying within distance `D` of `c` has at most `2D + 1`
elements. -/
private theorem card_le_two_mul_add_one_of_abs_sub_le (s : Finset ℤ) (c : ℤ) (D : ℕ)
    (hs : ∀ x ∈ s, |x - c| ≤ (D : ℤ)) : s.card ≤ 2 * D + 1 := by
  have hsub : s ⊆ Finset.Icc (c - (D : ℤ)) (c + (D : ℤ)) := by
    intro x hx
    rw [Finset.mem_Icc]
    have h := hs x hx
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have hz : c + (D : ℤ) + 1 - (c - (D : ℤ)) = ((2 * D + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hz, Int.toNat_natCast] at hcard
  exact hcard

/-- The naturals `a' < l` with `|a' - a| ≤ D` number at most `2D + 1`. -/
private theorem card_filter_abs_sub_le (l a D : ℕ) :
    ((Finset.range l).filter (fun a' : ℕ => |(a' : ℤ) - (a : ℤ)| ≤ (D : ℤ))).card ≤ 2 * D + 1 := by
  have hinj : Function.Injective (fun x : ℕ => (x : ℤ)) := fun _ _ hxy => Nat.cast_injective hxy
  have hsub : ((Finset.range l).filter (fun a' : ℕ => |(a' : ℤ) - (a : ℤ)| ≤ (D : ℤ))).image
        (fun x : ℕ => (x : ℤ))
      ⊆ Finset.Icc ((a : ℤ) - (D : ℤ)) ((a : ℤ) + (D : ℤ)) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_Icc]
    have h := hy.2
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  calc ((Finset.range l).filter (fun a' : ℕ => |(a' : ℤ) - (a : ℤ)| ≤ (D : ℤ))).card
      = (((Finset.range l).filter
            (fun a' : ℕ => |(a' : ℤ) - (a : ℤ)| ≤ (D : ℤ))).image (fun x : ℕ => (x : ℤ))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (Finset.Icc ((a : ℤ) - (D : ℤ)) ((a : ℤ) + (D : ℤ))).card := Finset.card_le_card hsub
    _ ≤ 2 * D + 1 := by
        rw [Int.card_Icc]
        have hz : (a : ℤ) + (D : ℤ) + 1 - ((a : ℤ) - (D : ℤ)) = ((2 * D + 1 : ℕ) : ℤ) := by
          push_cast; ring
        rw [hz, Int.toNat_natCast]

/-- Diagonal collision count for floors of `(N - a*p)/l`.

For `l` ranging over `[P+1, 2P]` and `a, a' < l`, the number of pairs with
`|⌊(N - a p)/l⌋ - ⌊(N - a' p)/l⌋| ≤ h` is at most `(2(h+2)/p) * (2P)³ + (2P)²`.

Mathematical content: for fixed `l`, `(N - a p) = l * ⌊(N - a p)/l⌋ + r` with `0 ≤ r < l`,
so `|a - a'| * p = |l(⌊(N-ap)/l⌋ - ⌊(N-a'p)/l⌋) + (r - r')| ≤ h*l + l = (h+1)l`; hence
for each `(l,a)` there are at most `2*⌊(h+1)l/p⌋ + 1` admissible `a'`, and summing over
`l ≤ 2P`, `a < l` gives the bound. -/
theorem card_floor_close_diag (P p : ℕ) (N : ℤ) (h : ℕ) (hp : 0 < p) :
    (∑ l ∈ Finset.Icc (P + 1) (2 * P), ∑ a ∈ Finset.range l, ∑ a' ∈ Finset.range l,
        (if |(N - (a : ℤ) * (p : ℤ)) / (l : ℤ)
              - (N - (a' : ℤ) * (p : ℤ)) / (l : ℤ)| ≤ (h : ℤ) then (1 : ℝ) else 0))
    ≤ (2 * ((h : ℝ) + 2) / (p : ℝ)) * (2 * P : ℝ) ^ 3 + (2 * P : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  set s : Finset ℕ := Finset.Icc (P + 1) (2 * P) with hs
  have hsm : ∀ l, l ∈ s ↔ l ∈ Finset.Icc (P + 1) (2 * P) := fun l => by rw [hs]
  have hm : ∀ l, l ∈ s → P + 1 ≤ l ∧ l ≤ 2 * P := fun l hl => Finset.mem_Icc.mp ((hsm l).mp hl)
  have hcard : s.card = P := by rw [hs, Nat.card_Icc]; omega
  have hper : ∀ l ∈ s,
      (∑ a ∈ Finset.range l, ∑ a' ∈ Finset.range l,
        (if |(N - (a : ℤ) * (p : ℤ)) / (l : ℤ)
              - (N - (a' : ℤ) * (p : ℤ)) / (l : ℤ)| ≤ (h : ℤ) then (1 : ℝ) else 0))
      ≤ (2 * ((h : ℝ) + 2) / (p : ℝ)) * (l : ℝ) ^ 2 + (l : ℝ) := by
    intro l hl
    have hlpos : 0 < l := by have := (hm l hl).1; omega
    set D : ℕ := ((h + 2) * l) / p with hD
    have hinner : ∀ a ∈ Finset.range l,
        (∑ a' ∈ Finset.range l,
          (if |(N - (a : ℤ) * (p : ℤ)) / (l : ℤ)
                - (N - (a' : ℤ) * (p : ℤ)) / (l : ℤ)| ≤ (h : ℤ) then (1 : ℝ) else 0))
        ≤ (2 * (D : ℝ) + 1) := by
      intro a ha
      rw [Finset.sum_boole]
      have hsub : (Finset.range l).filter
            (fun a' : ℕ => |(N - (a : ℤ) * (p : ℤ)) / (l : ℤ)
                - (N - (a' : ℤ) * (p : ℤ)) / (l : ℤ)| ≤ (h : ℤ))
          ⊆ (Finset.range l).filter (fun a' : ℕ => |(a' : ℤ) - (a : ℤ)| ≤ (D : ℤ)) := by
        intro a' ha'
        rw [Finset.mem_filter] at ha' ⊢
        refine ⟨ha'.1, ?_⟩
        have hA := abs_mul_le_of_div_close p l N h hlpos a a' ha'.2
        let d : ℕ := ((a' : ℤ) - (a : ℤ)).natAbs
        have hdabs : |(a' : ℤ) - (a : ℤ)| = (d : ℤ) := (Int.natCast_natAbs _).symm
        have hcast : (d : ℤ) * (p : ℤ) ≤ (((h + 2) * l : ℕ) : ℤ) := by
          have h2 : |(a : ℤ) - (a' : ℤ)| = |(a' : ℤ) - (a : ℤ)| := abs_sub_comm _ _
          have hR : ((h : ℤ) + 2) * (l : ℤ) = (((h + 2) * l : ℕ) : ℤ) := by push_cast; ring
          rw [h2, hdabs, hR] at hA
          exact hA
        have hnat : d * p ≤ (h + 2) * l := by exact_mod_cast hcast
        have hdle : d ≤ D := by
          rw [hD]
          exact (Nat.le_div_iff_mul_le hp).mpr hnat
        rw [hdabs]
        exact_mod_cast hdle
      calc (((Finset.range l).filter
              (fun a' : ℕ => |(N - (a : ℤ) * (p : ℤ)) / (l : ℤ)
                  - (N - (a' : ℤ) * (p : ℤ)) / (l : ℤ)| ≤ (h : ℤ))).card : ℝ)
          ≤ (((Finset.range l).filter (fun a' : ℕ => |(a' : ℤ) - (a : ℤ)| ≤ (D : ℤ))).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ ((2 * D + 1 : ℕ) : ℝ) := by exact_mod_cast card_filter_abs_sub_le l a D
        _ = 2 * (D : ℝ) + 1 := by push_cast; ring
    have hDle : (D : ℝ) ≤ ((h : ℝ) + 2) * (l : ℝ) / (p : ℝ) := by
      have hmul : (D : ℝ) * (p : ℝ) ≤ (((h + 2) * l : ℕ) : ℝ) := by
        have hml := Nat.mul_div_le ((h + 2) * l) p
        rw [hD]
        have h' : ((p * (((h + 2) * l) / p) : ℕ) : ℝ) ≤ (((h + 2) * l : ℕ) : ℝ) := by
          exact_mod_cast hml
        simpa [Nat.cast_mul, mul_comm] using h'
      rw [le_div_iff₀ hpR]
      calc (D : ℝ) * (p : ℝ) ≤ (((h + 2) * l : ℕ) : ℝ) := hmul
        _ = ((h : ℝ) + 2) * (l : ℝ) := by push_cast; ring
    have hstep : (2 * (D : ℝ) + 1) ≤ 2 * (((h : ℝ) + 2) * (l : ℝ) / (p : ℝ)) + 1 := by
      linarith [hDle]
    calc (∑ a ∈ Finset.range l, ∑ a' ∈ Finset.range l,
            (if |(N - (a : ℤ) * (p : ℤ)) / (l : ℤ)
                  - (N - (a' : ℤ) * (p : ℤ)) / (l : ℤ)| ≤ (h : ℤ) then (1 : ℝ) else 0))
        ≤ ∑ a ∈ Finset.range l, (2 * (D : ℝ) + 1) := Finset.sum_le_sum hinner
      _ = (l : ℝ) * (2 * (D : ℝ) + 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (l : ℝ) * (2 * (((h : ℝ) + 2) * (l : ℝ) / (p : ℝ)) + 1) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (2 * ((h : ℝ) + 2) / (p : ℝ)) * (l : ℝ) ^ 2 + (l : ℝ) := by
            field_simp
  have hl2 : (∑ l ∈ s, (l : ℝ) ^ 2) ≤ (2 * P : ℝ) ^ 3 := by
    have hs2 : ∀ l ∈ s, (l : ℝ) ^ 2 ≤ (2 * P : ℝ) ^ 2 := by
      intro l hl
      have h1 : l ≤ 2 * P := (hm l hl).2
      have h2 : (l : ℝ) ≤ (2 * P : ℝ) := by exact_mod_cast h1
      have hl0 : (0 : ℝ) ≤ (l : ℝ) := by positivity
      nlinarith [h2, hl0]
    calc (∑ l ∈ s, (l : ℝ) ^ 2) ≤ ∑ l ∈ s, (2 * P : ℝ) ^ 2 := Finset.sum_le_sum hs2
      _ = (s.card : ℝ) * (2 * P : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (P : ℝ) * (2 * P : ℝ) ^ 2 := by rw [hcard]
      _ ≤ (2 * P : ℝ) * (2 * P : ℝ) ^ 2 := by
            have h2 : (P : ℝ) ≤ (2 * P : ℝ) := by
              have : (0 : ℝ) ≤ (P : ℝ) := by positivity
              linarith
            exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (2 * P : ℝ) ^ 3 := by ring
  have hl1 : (∑ l ∈ s, (l : ℝ)) ≤ (2 * P : ℝ) ^ 2 := by
    have hs1 : ∀ l ∈ s, (l : ℝ) ≤ (2 * P : ℝ) := by
      intro l hl
      exact_mod_cast (hm l hl).2
    calc (∑ l ∈ s, (l : ℝ)) ≤ ∑ l ∈ s, (2 * P : ℝ) := Finset.sum_le_sum hs1
      _ = (s.card : ℝ) * (2 * P : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (P : ℝ) * (2 * P : ℝ) := by rw [hcard]
      _ ≤ (2 * P : ℝ) * (2 * P : ℝ) := by
            have h2 : (P : ℝ) ≤ (2 * P : ℝ) := by
              have : (0 : ℝ) ≤ (P : ℝ) := by positivity
              linarith
            exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (2 * P : ℝ) ^ 2 := by ring
  have hcoef : (0 : ℝ) ≤ 2 * ((h : ℝ) + 2) / (p : ℝ) := by positivity
  calc (∑ l ∈ s, ∑ a ∈ Finset.range l, ∑ a' ∈ Finset.range l,
          (if |(N - (a : ℤ) * (p : ℤ)) / (l : ℤ)
                - (N - (a' : ℤ) * (p : ℤ)) / (l : ℤ)| ≤ (h : ℤ) then (1 : ℝ) else 0))
      ≤ ∑ l ∈ s, ((2 * ((h : ℝ) + 2) / (p : ℝ)) * (l : ℝ) ^ 2 + (l : ℝ)) :=
        Finset.sum_le_sum hper
    _ = (2 * ((h : ℝ) + 2) / (p : ℝ)) * (∑ l ∈ s, (l : ℝ) ^ 2) + ∑ l ∈ s, (l : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (2 * ((h : ℝ) + 2) / (p : ℝ)) * (2 * P : ℝ) ^ 3 + (2 * P : ℝ) ^ 2 := by
        exact add_le_add (mul_le_mul_of_nonneg_left hl2 hcoef) hl1

end Commons.NumberTheory.CharacterSum