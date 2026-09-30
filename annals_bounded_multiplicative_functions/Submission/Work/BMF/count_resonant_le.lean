import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.TentDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Counting resonances: `# { d ∈ [-K,K] : nint (d γ) < δ } ≤ 4Kδ + 2Kγ + 4δ/γ + 2`

The set `S = { d ∈ ℤ : |d| ≤ K, nint (d γ) < δ }` of "resonant" integers (where `nint` is the
distance to the nearest integer) is counted by grouping `d` according to `round (d γ)`:

* each fibre `{d : round (d γ) = m, nint (d γ) < δ}` is contained in the open interval
  `((m-δ)/γ, (m+δ)/γ)` of length `2δ/γ`, hence has at most `2δ/γ + 1` elements;
* the image of `d ↦ round (d γ)` on `[-K,K]` lies in `[-Kγ-1/2, Kγ+1/2]`, hence has at most
  `2Kγ + 2` elements.

Multiplying the two bounds gives `(2Kγ+2)(2δ/γ+1) = 4Kδ + 2Kγ + 4δ/γ + 2`.
-/

namespace Work.BMF

open Finset

/-- If `(z : ℝ) ≤ y` and `0 ≤ y`, then also `(z.toNat : ℝ) ≤ y`. -/
lemma cast_toNat_le {z : ℤ} {y : ℝ} (h : (z : ℝ) ≤ y) (hy : 0 ≤ y) : (z.toNat : ℝ) ≤ y := by
  rcases lt_or_ge z 0 with hz | hz
  · have hz' : z.toNat = 0 := Int.toNat_of_nonpos hz.le
    rw [hz']; simpa using hy
  · have hz' : (z.toNat : ℝ) = (z : ℝ) := by
      have : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
      exact_mod_cast this
    rw [hz']; exact h

/-- The nearest integer to `x` differs from `x` by at most `1/2`, so
`|round x| ≤ |x| + 1/2`. -/
lemma abs_round_cast_le (x : ℝ) : |((round x : ℤ) : ℝ)| ≤ |x| + 1 / 2 := by
  have h1 : ((round x : ℤ) : ℝ) ≤ x + 1 / 2 := round_le_add_half x
  have h2 : x - 1 / 2 < ((round x : ℤ) : ℝ) := sub_half_lt_round x
  rcases lt_or_ge ((round x : ℤ) : ℝ) 0 with hneg | hpos
  · rw [abs_of_neg hneg]
    have : -((round x : ℤ) : ℝ) ≤ -x + 1 / 2 := by linarith
    linarith [neg_le_abs x]
  · rw [abs_of_nonneg hpos]
    linarith [le_abs_self x]

/-- The number of integers `d ∈ [-K, K]` lying strictly inside the open interval `(a, b)` is at
most `b - a + 1`. -/
lemma card_int_open_interval_le (K : ℕ) (a b : ℝ) (hab : a ≤ b) :
    (((Finset.Icc (-((K : ℤ))) (K : ℤ)).filter (fun d : ℤ => a < (d : ℝ) ∧ (d : ℝ) < b)).card : ℝ)
      ≤ b - a + 1 := by
  set T := (Finset.Icc (-((K : ℤ))) (K : ℤ)).filter (fun d : ℤ => a < (d : ℝ) ∧ (d : ℝ) < b) with hT
  have hsub : T ⊆ Finset.Icc (⌊a⌋ + 1) (⌈b⌉ - 1) := by
    intro d hd
    rw [hT, Finset.mem_filter] at hd
    obtain ⟨-, ha, hb⟩ := hd
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have h := (Int.floor_lt).mpr ha
      omega
    · have h := (Int.lt_ceil).mpr hb
      omega
  have hcard : T.card ≤ (⌈b⌉ - ⌊a⌋ - 1).toNat := by
    have h1 : T.card ≤ (Finset.Icc (⌊a⌋ + 1) (⌈b⌉ - 1)).card := Finset.card_le_card hsub
    rw [Int.card_Icc] at h1
    have he : (⌈b⌉ - 1 + 1 - (⌊a⌋ + 1) : ℤ) = ⌈b⌉ - ⌊a⌋ - 1 := by ring
    rwa [he] at h1
  have hle : ((⌈b⌉ - ⌊a⌋ - 1 : ℤ) : ℝ) ≤ b - a + 1 := by
    have h1 : ((⌈b⌉ : ℤ) : ℝ) < b + 1 := Int.ceil_lt_add_one b
    have h2 : a - 1 < ((⌊a⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor a
    have h3 : ((⌈b⌉ - ⌊a⌋ - 1 : ℤ) : ℝ) < b - a + 1 := by push_cast; linarith
    linarith
  have hy : (0 : ℝ) ≤ b - a + 1 := by linarith
  calc (T.card : ℝ) ≤ ((⌈b⌉ - ⌊a⌋ - 1).toNat : ℝ) := by exact_mod_cast hcard
    _ ≤ b - a + 1 := cast_toNat_le hle hy

/-- The number of distinct nearest integers `round (d * γ)` for `d ∈ [-K, K]` is at most
`2 * K * γ + 2`. -/
lemma image_round_card_le (K : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    (((Finset.Icc (-((K : ℤ))) (K : ℤ)).image (fun d : ℤ => round ((d : ℝ) * γ))).card : ℝ)
      ≤ 2 * (K : ℝ) * γ + 2 := by
  set N : ℤ := ⌊(K : ℝ) * γ + 1 / 2⌋ with hN
  have hsub : (Finset.Icc (-((K : ℤ))) (K : ℤ)).image (fun d : ℤ => round ((d : ℝ) * γ))
      ⊆ Finset.Icc (-N) N := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨d, hd, rfl⟩ := hm
    rw [Finset.mem_Icc] at hd
    obtain ⟨hd1, hd2⟩ := hd
    rw [Finset.mem_Icc]
    have hdabs : |(d : ℝ)| ≤ (K : ℝ) := by
      rw [abs_le]
      exact ⟨by exact_mod_cast hd1, by exact_mod_cast hd2⟩
    have hbnd : |((round ((d : ℝ) * γ) : ℤ) : ℝ)| ≤ (K : ℝ) * γ + 1 / 2 := by
      have h1 := abs_round_cast_le ((d : ℝ) * γ)
      have h2 : |(d : ℝ) * γ| = |(d : ℝ)| * γ := by rw [abs_mul, abs_of_pos hγ]
      have h3 : |(d : ℝ)| * γ ≤ (K : ℝ) * γ := mul_le_mul_of_nonneg_right hdabs hγ.le
      linarith [h1, h3]
    obtain ⟨hb1, hb2⟩ := abs_le.mp hbnd
    constructor
    · have hh : -((round ((d : ℝ) * γ) : ℤ)) ≤ N := by
        rw [hN]
        apply Int.le_floor.mpr
        push_cast
        linarith
      omega
    · rw [hN]
      apply Int.le_floor.mpr
      exact hb2
  have hcard : ((Finset.Icc (-((K : ℤ))) (K : ℤ)).image (fun d : ℤ => round ((d : ℝ) * γ))).card
      ≤ (Finset.Icc (-N) N).card := Finset.card_le_card hsub
  have hmain : ((Finset.Icc (-N) N).card : ℝ) ≤ 2 * (K : ℝ) * γ + 2 := by
    rw [Int.card_Icc]
    have he : N + 1 - (-N) = 2 * N + 1 := by ring
    rw [he]
    apply cast_toNat_le
    · have hNle : ((N : ℤ) : ℝ) ≤ (K : ℝ) * γ + 1 / 2 := by rw [hN]; exact Int.floor_le _
      push_cast
      linarith
    · have hKa : (0 : ℝ) ≤ (K : ℝ) := by positivity
      nlinarith [mul_nonneg hKa hγ.le]
  calc (((Finset.Icc (-((K : ℤ))) (K : ℤ)).image (fun d : ℤ => round ((d : ℝ) * γ))).card : ℝ)
      ≤ ((Finset.Icc (-N) N).card : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * (K : ℝ) * γ + 2 := hmain

theorem count_resonant_le (K : ℕ) (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) :
    (((Finset.Icc (-((K : ℤ))) (K : ℤ)).filter (fun d : ℤ => nint ((d : ℝ) * γ) < δ)).card : ℝ)
      ≤ 4 * (K : ℝ) * δ + 2 * (K : ℝ) * γ + 4 * δ / γ + 2 := by
  classical
  set S : Finset ℤ :=
    (Finset.Icc (-((K : ℤ))) (K : ℤ)).filter (fun d : ℤ => nint ((d : ℝ) * γ) < δ) with hS
  set g : ℤ → ℤ := fun d => round ((d : ℝ) * γ) with hg
  have hmap : Set.MapsTo g ↑S ↑(S.image g) := fun x hx => Finset.mem_image_of_mem g hx
  have hsum : (S.card : ℝ) = ∑ m ∈ S.image g, ((S.filter (fun d => g d = m)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    push_cast
    rfl
  have hfib : ∀ m ∈ S.image g, ((S.filter (fun d => g d = m)).card : ℝ) ≤ 2 * δ / γ + 1 := by
    intro m _
    set a : ℝ := ((m : ℝ) - δ) / γ with ha
    set b : ℝ := ((m : ℝ) + δ) / γ with hb
    have hTeq : S.filter (fun d => g d = m)
        = (Finset.Icc (-((K : ℤ))) (K : ℤ)).filter
            (fun d : ℤ => nint ((d : ℝ) * γ) < δ ∧ round ((d : ℝ) * γ) = m) := by
      rw [hS, hg, Finset.filter_filter]
    have hsub : (Finset.Icc (-((K : ℤ))) (K : ℤ)).filter
            (fun d : ℤ => nint ((d : ℝ) * γ) < δ ∧ round ((d : ℝ) * γ) = m)
        ⊆ (Finset.Icc (-((K : ℤ))) (K : ℤ)).filter
            (fun d : ℤ => a < (d : ℝ) ∧ (d : ℝ) < b) := by
      intro d hd
      rw [Finset.mem_filter] at hd ⊢
      obtain ⟨hdmem, hnint, hround⟩ := hd
      have habs : |(d : ℝ) * γ - (m : ℝ)| < δ := by
        have h := hnint
        simp only [nint] at h
        rw [hround] at h
        exact h
      obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
      refine ⟨hdmem, ?_, ?_⟩
      · rw [ha, div_lt_iff₀ hγ]; linarith
      · rw [hb, lt_div_iff₀ hγ]; linarith
    have hab : a ≤ b := by
      rw [ha, hb]
      apply div_le_div_of_nonneg_right (by linarith) hγ.le
    have hmain := card_int_open_interval_le K a b hab
    have hba : b - a = 2 * δ / γ := by rw [ha, hb]; field_simp; ring
    calc ((S.filter (fun d => g d = m)).card : ℝ)
        = (((Finset.Icc (-((K : ℤ))) (K : ℤ)).filter
            (fun d : ℤ => nint ((d : ℝ) * γ) < δ ∧ round ((d : ℝ) * γ) = m)).card : ℝ) := by
          rw [hTeq]
      _ ≤ (((Finset.Icc (-((K : ℤ))) (K : ℤ)).filter
            (fun d : ℤ => a < (d : ℝ) ∧ (d : ℝ) < b)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ b - a + 1 := hmain
      _ = 2 * δ / γ + 1 := by rw [hba]
  have hcard2 : ((S.image g).card : ℝ) ≤ 2 * (K : ℝ) * γ + 2 := by
    have hsub2 : S.image g ⊆
        (Finset.Icc (-((K : ℤ))) (K : ℤ)).image (fun d : ℤ => round ((d : ℝ) * γ)) := by
      rw [hg]
      apply Finset.image_subset_image
      rw [hS]
      exact Finset.filter_subset _ _
    have h1 : (S.image g).card ≤
        ((Finset.Icc (-((K : ℤ))) (K : ℤ)).image (fun d : ℤ => round ((d : ℝ) * γ))).card :=
      Finset.card_le_card hsub2
    calc ((S.image g).card : ℝ)
        ≤ (((Finset.Icc (-((K : ℤ))) (K : ℤ)).image
            (fun d : ℤ => round ((d : ℝ) * γ))).card : ℝ) := by exact_mod_cast h1
      _ ≤ 2 * (K : ℝ) * γ + 2 := image_round_card_le K γ hγ
  have hpos : (0 : ℝ) ≤ 2 * δ / γ + 1 := by
    have h : (0 : ℝ) < 2 * δ / γ := by positivity
    linarith
  calc (S.card : ℝ)
      = ∑ m ∈ S.image g, ((S.filter (fun d => g d = m)).card : ℝ) := hsum
    _ ≤ ∑ m ∈ S.image g, (2 * δ / γ + 1) := Finset.sum_le_sum hfib
    _ = ((S.image g).card : ℝ) * (2 * δ / γ + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (K : ℝ) * γ + 2) * (2 * δ / γ + 1) := mul_le_mul_of_nonneg_right hcard2 hpos
    _ = 4 * (K : ℝ) * δ + 2 * (K : ℝ) * γ + 4 * δ / γ + 2 := by
        field_simp
        ring

end Work.BMF
