import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.windows
import Submission.Work.Core.Ablock_res

/-!
# The collision-free windows of the non-resonant case (AJ §9)

For the non-resonant case of AJ §9 the two windows must have two extra properties which AJ's
own (centred, equal-size) windows have by construction, but which our *balanced* geometry has
to enforce explicitly:

* **no collisions**: no difference of two distinct sites of `I₁ ∪ I₂` may be a multiple of
  `q_n` other than a tiny one — otherwise `fracDist ((i-j)α)` is comparable to `Δ_n` and the
  Lagrange products pick up a deficit of order `β q_n`, which the non-resonant rate `o(1)`
  cannot afford;
* **block alignment**: both windows must be exact unions of blocks of `q_{n-1}` consecutive
  sites, because the trigonometric product estimates (AJ Lemma 9.6 / `irrat-1`) apply to such
  blocks.

Both are achieved by taking the windows *centred* at `-K/2` and `y - K/2` (the centres of
`A2blk K` and of `I2set y K`) with lengths `2a' q_{n-1}` and `2b' q_{n-1}`, `a' + b' = s`,
`a'/b' ≈ 3/2`.  The difference set is then exactly `[y - T + 1, y + T - 1]` with
`T = s q_{n-1}` (AJ's difference set), which contains no multiple of `q_n` while
`T ≤ dist (y, q_n ℤ)`.
-/

noncomputable section

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-- Half the scale of the non-resonant case: `T = s q_{n-1}`. -/
def Tnr (q : ℕ → ℕ) (n s : ℕ) : ℤ := (s : ℤ) * (q (n - 1) : ℤ)

/-- The scale `K = 2T - 1 = 2 s q_{n-1} - 1`. -/
def Knr (q : ℕ → ℕ) (n s : ℕ) : ℕ := 2 * s * q (n - 1) - 1

/-- The first window: `2 a'` blocks of `q_{n-1}` sites, centred at `-K/2 = -T + 1/2`. -/
def I1nr (q : ℕ → ℕ) (n s a' : ℕ) : Finset ℤ :=
  Finset.Icc (-Tnr q n s + 1 - (a' : ℤ) * (q (n - 1) : ℤ))
    (-Tnr q n s + (a' : ℤ) * (q (n - 1) : ℤ))

/-- The second window: `2 b'` blocks of `q_{n-1}` sites, centred at `y - K/2`. -/
def I2nr (q : ℕ → ℕ) (n s b' : ℕ) (y : ℤ) : Finset ℤ :=
  Finset.Icc (y - Tnr q n s + 1 - (b' : ℤ) * (q (n - 1) : ℤ))
    (y - Tnr q n s + (b' : ℤ) * (q (n - 1) : ℤ))

lemma Tnr_pos {q : ℕ → ℕ} {n s : ℕ} (hq : 0 < q (n - 1)) (hs : 1 ≤ s) : 0 < Tnr q n s := by
  unfold Tnr
  exact mul_pos (by exact_mod_cast hs) (by exact_mod_cast hq)

lemma Knr_cast (q : ℕ → ℕ) {n s : ℕ} (hs : 1 ≤ s) (hq : 1 ≤ q (n - 1)) :
    ((Knr q n s : ℕ) : ℤ) = 2 * Tnr q n s - 1 := by
  have h : 1 ≤ 2 * s * q (n - 1) :=
    Nat.mul_le_mul (show 1 ≤ 2 * s by omega) (show 1 ≤ q (n - 1) by omega)
  unfold Knr Tnr
  rw [Nat.cast_sub h]
  push_cast
  ring

/-! ## Cardinality, difference set, containment -/

lemma card_I1nr (q : ℕ → ℕ) (n s a' : ℕ) : (I1nr q n s a').card = 2 * a' * q (n - 1) := by
  rw [I1nr, Int.card_Icc]
  have h : -Tnr q n s + (a' : ℤ) * (q (n - 1) : ℤ)
      + 1 - (-Tnr q n s + 1 - (a' : ℤ) * (q (n - 1) : ℤ))
      = ((2 * a' * q (n - 1) : ℕ) : ℤ) := by
    push_cast; ring
  rw [h, Int.toNat_natCast]

lemma card_I2nr (q : ℕ → ℕ) (n s b' : ℕ) (y : ℤ) :
    (I2nr q n s b' y).card = 2 * b' * q (n - 1) := by
  rw [I2nr, Int.card_Icc]
  have h : y - Tnr q n s + (b' : ℤ) * (q (n - 1) : ℤ)
      + 1 - (y - Tnr q n s + 1 - (b' : ℤ) * (q (n - 1) : ℤ))
      = ((2 * b' * q (n - 1) : ℕ) : ℤ) := by
    push_cast; ring
  rw [h, Int.toNat_natCast]

/-- The difference set of the two windows is exactly AJ's: `[y - T + 1, y + T - 1]`. -/
lemma I2nr_sub_I1nr {q : ℕ → ℕ} {n s a' b' : ℕ} {y : ℤ} {i j : ℤ}
    (hab : a' + b' = s)
    (hi : i ∈ I2nr q n s b' y) (hj : j ∈ I1nr q n s a') :
    y - Tnr q n s + 1 ≤ i - j ∧ i - j ≤ y + Tnr q n s - 1 := by
  simp only [I2nr, I1nr, Finset.mem_Icc] at hi hj
  obtain ⟨h1, h2⟩ := hi
  obtain ⟨h3, h4⟩ := hj
  have habZ : ((a' : ℕ) : ℤ) + ((b' : ℕ) : ℤ) = (s : ℤ) := by exact_mod_cast hab
  simp only [Tnr] at *
  constructor <;> nlinarith [habZ]

/-- The two windows are disjoint as soon as `y ≥ T`. -/
lemma disjoint_I1nr_I2nr {q : ℕ → ℕ} {n s a' b' : ℕ} {y : ℤ}
    (hab : a' + b' = s) (hy : Tnr q n s ≤ y) :
    Disjoint (I1nr q n s a') (I2nr q n s b' y) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [I1nr, Finset.mem_Icc] at hx1
  simp only [I2nr, Finset.mem_Icc] at hx2
  obtain ⟨h1, h2⟩ := hx1
  obtain ⟨h3, h4⟩ := hx2
  have habZ : ((a' : ℕ) : ℤ) + ((b' : ℕ) : ℤ) = (s : ℤ) := by exact_mod_cast hab
  have hfac : ((a' : ℤ) + (b' : ℤ)) * (q (n - 1) : ℤ) = (s : ℤ) * (q (n - 1) : ℤ) := by
    rw [habZ]
  simp only [Tnr] at *
  nlinarith [hfac]

lemma card_union_I1nr_I2nr {q : ℕ → ℕ} {n s a' b' : ℕ} {y : ℤ}
    (hab : a' + b' = s) (hs : 1 ≤ s) (hq : 0 < q (n - 1)) (hy : Tnr q n s ≤ y) :
    (I1nr q n s a' ∪ I2nr q n s b' y).card = Knr q n s + 1 := by
  rw [Finset.card_union_of_disjoint (disjoint_I1nr_I2nr hab hy), card_I1nr, card_I2nr]
  have habZ : ((a' : ℕ) : ℤ) + ((b' : ℕ) : ℤ) = (s : ℤ) := by exact_mod_cast hab
  have hp : 1 ≤ 2 * s * q (n - 1) :=
    Nat.mul_le_mul (show 1 ≤ 2 * s by omega) (show 1 ≤ q (n - 1) by omega)
  have hsum : 2 * a' * q (n - 1) + 2 * b' * q (n - 1) = 2 * s * q (n - 1) := by
    have hZ : ((2 * a' * q (n - 1) + 2 * b' * q (n - 1) : ℕ) : ℤ)
        = ((2 * s * q (n - 1) : ℕ) : ℤ) := by
      push_cast
      rw [← habZ]
      ring
    exact_mod_cast hZ
  rw [hsum]
  unfold Knr
  omega

lemma I1nr_subset_A2blk {q : ℕ → ℕ} {n s a' : ℕ}
    (hs : 1 ≤ s) (hq : 1 ≤ q (n - 1))
    (hfit : 8 * ((a' : ℤ) * (q (n - 1) : ℤ)) + 6 ≤ 5 * Tnr q n s) :
    I1nr q n s a' ⊆ A2blk (Knr q n s) := by
  intro x hx
  simp only [I1nr, Finset.mem_Icc] at hx
  obtain ⟨h1, h2⟩ := hx
  have hK : ((Knr q n s : ℕ) : ℤ) = 2 * Tnr q n s - 1 := Knr_cast q hs hq
  have hb2 : 13 * ((Knr q n s : ℕ) : ℤ) - 15 ≤ 16 * b1316 (Knr q n s) :=
    (Work.Core.int_bounds (Knr q n s)).2.1
  have hb4 : 16 * b316 (Knr q n s) ≤ 3 * ((Knr q n s : ℕ) : ℤ) + 15 :=
    (Work.Core.int_bounds (Knr q n s)).2.2.2
  simp only [A2blk, Finset.mem_Icc]
  constructor
  · have hl : -b1316 (Knr q n s) ≤ -Tnr q n s + 1 - (a' : ℤ) * (q (n - 1) : ℤ) := by
      rw [hK] at hb2; nlinarith
    linarith
  · have hu : -Tnr q n s + (a' : ℤ) * (q (n - 1) : ℤ) ≤ -b316 (Knr q n s) := by
      rw [hK] at hb4; nlinarith
    linarith

lemma I2nr_subset_I2set {q : ℕ → ℕ} {n s a' b' : ℕ} {y : ℤ}
    (hab : a' + b' = s) (hs : 1 ≤ s) (hq : 1 ≤ q (n - 1))
    (hfit : 10 * ((b' : ℤ) * (q (n - 1) : ℤ)) + 37 ≤ 4 * Tnr q n s) :
    I2nr q n s b' y ⊆ I2set y (Knr q n s) := by
  intro x hx
  simp only [I2nr, Finset.mem_Icc] at hx
  obtain ⟨h1, h2⟩ := hx
  have hfl : 10 * b7 (Knr q n s) ≤ 7 * ((Knr q n s : ℕ) : ℤ) := ten_mul_b7_le _
  have hce : 3 * ((Knr q n s : ℕ) : ℤ) ≤ 10 * b3 (Knr q n s) := b3_le_ten_mul _
  have hfl' : 7 * ((Knr q n s : ℕ) : ℤ) - 10 < 10 * b7 (Knr q n s) := by
    have h := Int.lt_floor_add_one ((7 : ℝ) * ((Knr q n s : ℕ) : ℝ) / 10)
    have h' : (7 : ℝ) * ((Knr q n s : ℕ) : ℝ) / 10
        < ((b7 (Knr q n s) : ℤ) : ℝ) + 1 := by
      simpa only [b7] using h
    have h'' : (10 : ℝ) * ((b7 (Knr q n s) : ℤ) : ℝ)
        > 7 * ((Knr q n s : ℕ) : ℝ) - 10 := by linarith
    exact_mod_cast h''
  have hce' : 10 * b3 (Knr q n s) < 3 * ((Knr q n s : ℕ) : ℤ) + 10 := by
    have h := Int.ceil_lt_add_one ((3 : ℝ) * ((Knr q n s : ℕ) : ℝ) / 10)
    have h' : ((b3 (Knr q n s) : ℤ) : ℝ)
        < (3 : ℝ) * ((Knr q n s : ℕ) : ℝ) / 10 + 1 := by
      simpa only [b3] using h
    have h'' : (10 : ℝ) * ((b3 (Knr q n s) : ℤ) : ℝ)
        < 3 * ((Knr q n s : ℕ) : ℝ) + 10 := by linarith
    exact_mod_cast h''
  have hK : ((Knr q n s : ℕ) : ℤ) = 2 * Tnr q n s - 1 := Knr_cast q hs hq
  simp only [I2set, Finset.mem_Icc]
  constructor
  · have hl : y - b7 (Knr q n s) + 3
        ≤ y - Tnr q n s + 1 - (b' : ℤ) * (q (n - 1) : ℤ) := by
      rw [hK] at hfl hfl'
      nlinarith
    linarith
  · have hu : y - Tnr q n s + (b' : ℤ) * (q (n - 1) : ℤ) ≤ y - b3 (Knr q n s) := by
      rw [hK] at hce hce'
      nlinarith
    linarith

end Work.TMC16Core.Core
