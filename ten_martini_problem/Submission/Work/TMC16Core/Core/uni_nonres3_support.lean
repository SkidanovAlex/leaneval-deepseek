import Mathlib
import Submission.Work.TMC16Core.Core.geom
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.TMC16Core.Core.sum_Dnr_blocks

/-!
# Support lemmas for `Core.uni_nonres3`

`Dnr q n s a' b' y` is the block-aligned translate (by `Tnr q n s - 1`) of the two windows
`I1nr q n s a'` and `I2nr q n s b' y`; it is the union of the two intervals
`I₁ = [-(a':ℤ) L, (a':ℤ) L - 1]` and `I₂ = [y - (b':ℤ) L, y + (b':ℤ) L - 1]`, `L = q(n-1)`,
each a union of consecutive `L`-blocks.  Collected here: the transfer of `Uniform` along the
shift, the range check for the `θ`-hypothesis, elementary bounds on the elements of `Dnr`,
and the block base points / block assignment used by the four block sums.
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core

noncomputable section

/-- Pointwise: `2 * fracDist w ≤ |sin (π w)|`. -/
theorem two_mul_fracDist_le_abs_sin (w : ℝ) :
    2 * fracDist w ≤ |Real.sin (Real.pi * w)| := by
  have h : 2 / Real.pi * (Real.pi * Basic.nn w) ≤ Basic.S w := Basic.two_div_pi_mul_le_S w
  have key : 2 / Real.pi * (Real.pi * Basic.nn w) = 2 * Basic.nn w := by field_simp
  rw [key] at h
  have hnn : Basic.nn w = fracDist w := rfl
  have hS : Basic.S w = |Real.sin (Real.pi * w)| := rfl
  rwa [hnn, hS] at h

theorem Uniform_congr {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') {ε : ℝ} {z : ι → ℝ} {z' : ι' → ℝ} (h : ∀ i, z' (e i) = z i) :
    Uniform ε z ↔ Uniform ε z' := by
  have h' : ∀ i' : ι', z' i' = z (e.symm i') := fun i' => by
    rw [← h (e.symm i'), Equiv.apply_symm_apply]
  have hcard : Fintype.card ι' = Fintype.card ι := Fintype.card_congr e.symm
  have hmap' : ∀ j : ι', (Finset.univ.erase (e.symm j)).map e.toEmbedding = Finset.univ.erase j := by
    intro j
    rw [Finset.map_erase, Finset.map_univ_equiv]
    simp only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
  have hmap : ∀ j : ι, (Finset.univ.erase j).map e.toEmbedding = Finset.univ.erase (e j) := by
    intro j
    rw [Finset.map_erase, Finset.map_univ_equiv]
    simp only [Equiv.coe_toEmbedding]
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact (h' i) ▸ (h' j) ▸ H.1 (e.symm i) (e.symm j)
        (fun hc => hij (by simpa using congrArg e hc))
    · intro j x hx
      have hH := H.2 (e.symm j) x hx
      have hprod : (∏ i' ∈ Finset.univ.erase j,
            (x - Real.cos (2 * Real.pi * z' i')) / (Real.cos (2 * Real.pi * z' j) - Real.cos (2 * Real.pi * z' i')))
          = ∏ i ∈ Finset.univ.erase (e.symm j),
            (x - Real.cos (2 * Real.pi * z i)) / (Real.cos (2 * Real.pi * z (e.symm j)) - Real.cos (2 * Real.pi * z i)) := by
        rw [← hmap' j, Finset.prod_map]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp only [Equiv.coe_toEmbedding, h i, h' j]
      rw [hcard, hprod]
      exact hH
  · intro H
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact (h i) ▸ (h j) ▸ H.1 (e i) (e j) (fun hc => hij (by simpa using congrArg e.symm hc))
    · intro j x hx
      have hH := H.2 (e j) x hx
      have hprod : (∏ i' ∈ Finset.univ.erase (e j),
            (x - Real.cos (2 * Real.pi * z' i')) / (Real.cos (2 * Real.pi * z' (e j)) - Real.cos (2 * Real.pi * z' i')))
          = ∏ i ∈ Finset.univ.erase j,
            (x - Real.cos (2 * Real.pi * z i)) / (Real.cos (2 * Real.pi * z j) - Real.cos (2 * Real.pi * z i)) := by
        rw [← hmap j, Finset.prod_map]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp only [Equiv.coe_toEmbedding, h i, h j]
      rw [← hcard, ← hprod]
      exact hH

/-! ## The shifted index set of the non-resonant configuration

`I1nr q n s a'` (length `2 a' q(n-1)`) and `I2nr q n s b' y` (length `2 b' q(n-1)`) are the two
windows; shifting every index by `T - 1` (`T = Tnr q n s = s q(n-1)`, the centre shift that
appears in the phase `θ + (j + (K-1)/2) α` with `K = Knr q n s = 2T - 1`) turns them into the
two block-aligned intervals `D1 = Icc (-a'q(n-1)) (a'q(n-1)-1)` and
`D2 = Icc (y-b'q(n-1)) (y+b'q(n-1)-1)`, i.e. `Dnr`.  This is the parametrisation in which the
block estimates `hblk` are applied. -/

noncomputable def Dnr (q : ℕ → ℕ) (n s a' b' : ℕ) (y : ℤ) : Finset ℤ :=
  Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ))) ((a' : ℤ) * (q (n - 1) : ℤ) - 1) ∪
  Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ)) (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)

lemma shift_mem_I1 {q : ℕ → ℕ} {n s a' : ℕ} {j : ℤ}
    (hj : j ∈ I1nr q n s a') :
    j + Tnr q n s - 1 ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
      ((a' : ℤ) * (q (n - 1) : ℤ) - 1) := by
  simp only [I1nr, Tnr, Finset.mem_Icc] at hj ⊢
  constructor <;> omega

lemma shift_mem_I2 {q : ℕ → ℕ} {n s b' : ℕ} {y j : ℤ}
    (hj : j ∈ I2nr q n s b' y) :
    j + Tnr q n s - 1 ∈ Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
      (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1) := by
  simp only [I2nr, Tnr, Finset.mem_Icc] at hj ⊢
  constructor <;> omega

lemma unshift_mem_I1 {q : ℕ → ℕ} {n s a' : ℕ} {d : ℤ}
    (hd : d ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ))) ((a' : ℤ) * (q (n - 1) : ℤ) - 1)) :
    d - Tnr q n s + 1 ∈ I1nr q n s a' := by
  simp only [I1nr, Tnr, Finset.mem_Icc] at hd ⊢
  constructor <;> omega

lemma unshift_mem_I2 {q : ℕ → ℕ} {n s b' : ℕ} {y d : ℤ}
    (hd : d ∈ Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ)) (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)) :
    d - Tnr q n s + 1 ∈ I2nr q n s b' y := by
  simp only [I2nr, Tnr, Finset.mem_Icc] at hd ⊢
  constructor <;> omega

/-- The shift `j ↦ j + T - 1` as an equivalence between the two windows and `Dnr`. -/
noncomputable def shiftEquiv (q : ℕ → ℕ) (n s a' b' : ℕ) (y : ℤ) :
    {j : ℤ // j ∈ I1nr q n s a' ∪ I2nr q n s b' y} ≃ {d : ℤ // d ∈ Dnr q n s a' b' y} where
  toFun j := ⟨j.1 + Tnr q n s - 1, by
    rcases Finset.mem_union.1 j.2 with hj | hj
    · exact Finset.mem_union_left _ (shift_mem_I1 hj)
    · exact Finset.mem_union_right _ (shift_mem_I2 hj)⟩
  invFun d := ⟨d.1 - Tnr q n s + 1, by
    rcases Finset.mem_union.1 d.2 with hd | hd
    · exact Finset.mem_union_left _ (unshift_mem_I1 hd)
    · exact Finset.mem_union_right _ (unshift_mem_I2 hd)⟩
  left_inv j := by ext; simp; omega
  right_inv d := by ext; simp; omega

/-- `(K-1)/2 = T - 1` for `K = Knr q n s = 2T - 1`, `T = Tnr q n s`. -/
lemma knr_half {q : ℕ → ℕ} {n s : ℕ} (hs : 1 ≤ s) (hq : 1 ≤ q (n - 1)) :
    (((Knr q n s : ℕ) : ℝ) - 1) / 2 = (Tnr q n s : ℝ) - 1 := by
  have h := Knr_cast q hs hq
  have h2 : ((Knr q n s : ℕ) : ℝ) = 2 * (Tnr q n s : ℝ) - 1 := by
    have hcast : ((Knr q n s : ℕ) : ℝ) = (((Knr q n s : ℕ) : ℤ) : ℝ) := by push_cast; ring
    rw [hcast, h]; push_cast; ring
  rw [h2]; ring

/-- **Step 1 of the proof of `uni_nonres2`.**  Under the shift `j ↦ j + T - 1` the phase
`θ + (j + (K-1)/2)α` becomes `θ + d α` with `d = j + T - 1`, and the index set
`I1nr ∪ I2nr` becomes `Dnr`; hence the two `Uniform` statements are equivalent. -/
theorem uniform_nr_shift {α : ℝ} {q : ℕ → ℕ} {n s a' b' : ℕ} {y : ℤ} {θ ε : ℝ}
    (hs : 1 ≤ s) (hq : 1 ≤ q (n - 1)) :
    Uniform ε (fun j : {j : ℤ // j ∈ I1nr q n s a' ∪ I2nr q n s b' y} =>
        θ + (((j : ℤ) : ℝ) + (((Knr q n s : ℕ) : ℝ) - 1) / 2) * α)
      ↔ Uniform ε (fun d : {d : ℤ // d ∈ Dnr q n s a' b' y} => θ + (d : ℝ) * α) :=
  Uniform_congr (shiftEquiv q n s a' b' y) (fun j => by
    show θ + ((j.1 + Tnr q n s - 1 : ℤ) : ℝ) * α =
      θ + ((j.1 : ℝ) + (((Knr q n s : ℕ) : ℝ) - 1) / 2) * α
    rw [knr_half hs hq]
    push_cast
    ring)

/-! ## The Lagrange factor split

The two elementary factor bounds behind the estimate: on `[-1,1]` a numerator factor is at most
`2`, and `|cos b - cos a| = 2 |sin ((a+b)/2)| |sin ((a-b)/2)|` (`Real.cos_sub_cos`), so the
factor `(x - cos a)/(cos b - cos a)` is at most `1/(|sin ((a+b)/2)| |sin ((a-b)/2)|)` — the
two `2`'s cancel, which is why the numerator needs no separate block estimate. -/

theorem Dnr_add_abs_le {q : ℕ → ℕ} {n s a' b' : ℕ} {y d k : ℤ}
    (hab : a' + b' = s) (hd : d ∈ Dnr q n s a' b' y) (hk : k ∈ Dnr q n s a' b' y) :
    |d + k| ≤ 2 * |y| + 6 * (s : ℤ) * (q (n - 1) : ℤ) + 4 := by
  set Y : ℤ := |y| with hY
  have hY0 : 0 ≤ Y := by rw [hY]; exact abs_nonneg y
  have hy1 : y ≤ Y := by rw [hY]; exact le_abs_self y
  have hy2 : -Y ≤ y := by rw [hY]; exact neg_abs_le y
  have hL : (0 : ℤ) ≤ (q (n - 1) : ℤ) := Int.natCast_nonneg _
  have hs0 : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg _
  have habZ : ((a' : ℤ) + (b' : ℤ)) = (s : ℤ) := by exact_mod_cast hab
  have ha' : (a' : ℤ) ≤ (s : ℤ) := by omega
  have hb' : (b' : ℤ) ≤ (s : ℤ) := by omega
  have haL : (a' : ℤ) * (q (n - 1) : ℤ) ≤ (s : ℤ) * (q (n - 1) : ℤ) :=
    mul_le_mul_of_nonneg_right ha' hL
  have hbL : (b' : ℤ) * (q (n - 1) : ℤ) ≤ (s : ℤ) * (q (n - 1) : ℤ) :=
    mul_le_mul_of_nonneg_right hb' hL
  have hbL0 : (0 : ℤ) ≤ (b' : ℤ) * (q (n - 1) : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) hL
  have hsL0 : (0 : ℤ) ≤ (s : ℤ) * (q (n - 1) : ℤ) := mul_nonneg hs0 hL
  have hhalf1 : ∀ m : ℤ, -((a' : ℤ) * (q (n - 1) : ℤ)) ≤ m →
      m ≤ (a' : ℤ) * (q (n - 1) : ℤ) - 1 →
      |m| ≤ Y + (s : ℤ) * (q (n - 1) : ℤ) := by
    intro m hm1 hm2
    rw [abs_le]
    constructor <;> linarith
  have hhalf2 : ∀ m : ℤ, y - (b' : ℤ) * (q (n - 1) : ℤ) ≤ m →
      m ≤ y + (b' : ℤ) * (q (n - 1) : ℤ) - 1 →
      |m| ≤ Y + (s : ℤ) * (q (n - 1) : ℤ) := by
    intro m hm1 hm2
    rw [abs_le]
    constructor <;> linarith
  simp only [Dnr, Finset.mem_union, Finset.mem_Icc] at hd hk
  have hd' : |d| ≤ Y + (s : ℤ) * (q (n - 1) : ℤ) := by
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hhalf1 d h1 h2
    · exact hhalf2 d h1 h2
  have hk' : |k| ≤ Y + (s : ℤ) * (q (n - 1) : ℤ) := by
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hhalf1 k h1 h2
    · exact hhalf2 k h1 h2
  have hsum : |d + k| ≤ |d| + |k| := by
    refine abs_le.2 ⟨?_, ?_⟩
    · have h1 := neg_abs_le d; have h2 := neg_abs_le k; linarith
    · have h1 := le_abs_self d; have h2 := le_abs_self k; linarith
  calc |d + k| ≤ |d| + |k| := hsum
    _ ≤ 2 * Y + 2 * ((s : ℤ) * (q (n - 1) : ℤ)) := by linarith
    _ ≤ 2 * Y + 6 * (s : ℤ) * (q (n - 1) : ℤ) + 4 := by linarith

/-! ## The `fracDist` toolkit for the difference bound

`fracDist` is the distance to `ℤ`, so it is subadditive and hence satisfies the reverse
triangle inequality; iterating gives `fracDist (n * u) ≤ n * fracDist u`.  These are the
elementary inputs of the `havoid` bound (both the multiples trick and the `m = M qₙ + t`
decomposition). -/



/-! ## Element bounds -/

/-- Every element of `Dnr` is bounded by `|y| + s L`. -/
lemma Dnr_abs_le {q : ℕ → ℕ} {n s a' b' : ℕ} {y d : ℤ}
    (hab : a' + b' = s) (hy : Tnr q n s ≤ y) (hd : d ∈ Dnr q n s a' b' y) :
    |d| ≤ |y| + (s : ℤ) * (q (n - 1) : ℤ) := by
  have ha's : (a' : ℤ) ≤ (s : ℤ) := by exact_mod_cast (by omega : a' ≤ s)
  have hb's : (b' : ℤ) ≤ (s : ℤ) := by exact_mod_cast (by omega : b' ≤ s)
  have hL : (0 : ℤ) ≤ (q (n - 1) : ℤ) := Int.natCast_nonneg _
  have haL : (a' : ℤ) * (q (n - 1) : ℤ) ≤ (s : ℤ) * (q (n - 1) : ℤ) :=
    mul_le_mul_of_nonneg_right ha's hL
  have hbL : (b' : ℤ) * (q (n - 1) : ℤ) ≤ (s : ℤ) * (q (n - 1) : ℤ) :=
    mul_le_mul_of_nonneg_right hb's hL
  have habs : 0 ≤ |y| := abs_nonneg y
  simp only [Dnr, Finset.mem_union, Finset.mem_Icc] at hd
  rw [abs_le]
  rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · constructor <;> linarith [le_abs_self y, neg_abs_le y]
  · constructor <;> linarith [le_abs_self y, neg_abs_le y]

/-- Two elements of the *first* interval of `Dnr` differ by less than `q n`. -/
lemma Dnr_inter1_diff_lt {q : ℕ → ℕ} {n s a' : ℕ} {k k' : ℤ}
    (hk : k ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ))) ((a' : ℤ) * (q (n - 1) : ℤ) - 1))
    (hk' : k' ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ))) ((a' : ℤ) * (q (n - 1) : ℤ) - 1))
    (hTn : 2 * s * q (n - 1) ≤ q n) (ha's : (a' : ℤ) ≤ (s : ℤ)) :
    |k - k'| < (q n : ℤ) := by
  rw [Finset.mem_Icc] at hk hk'
  obtain ⟨h1, h2⟩ := hk
  obtain ⟨h3, h4⟩ := hk'
  have hL : (0 : ℤ) ≤ (q (n - 1) : ℤ) := Int.natCast_nonneg _
  have hTnZ : 2 * (s : ℤ) * (q (n - 1) : ℤ) ≤ (q n : ℤ) := by exact_mod_cast hTn
  have haL : (a' : ℤ) * (q (n - 1) : ℤ) ≤ (s : ℤ) * (q (n - 1) : ℤ) :=
    mul_le_mul_of_nonneg_right ha's hL
  rw [abs_lt]
  constructor <;> nlinarith [h1, h2, h3, h4, haL, hTnZ]

/-- Two elements of the *second* interval of `Dnr` differ by less than `q n`. -/
lemma Dnr_inter2_diff_lt {q : ℕ → ℕ} {n s b' : ℕ} {y k k' : ℤ}
    (hk : k ∈ Finset.Icc (y - ((b' : ℤ) * (q (n - 1) : ℤ))) (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1))
    (hk' : k' ∈ Finset.Icc (y - ((b' : ℤ) * (q (n - 1) : ℤ))) (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1))
    (hTn : 2 * s * q (n - 1) ≤ q n) (hb's : (b' : ℤ) ≤ (s : ℤ)) :
    |k - k'| < (q n : ℤ) := by
  rw [Finset.mem_Icc] at hk hk'
  obtain ⟨h1, h2⟩ := hk
  obtain ⟨h3, h4⟩ := hk'
  have hL : (0 : ℤ) ≤ (q (n - 1) : ℤ) := Int.natCast_nonneg _
  have hTnZ : 2 * (s : ℤ) * (q (n - 1) : ℤ) ≤ (q n : ℤ) := by exact_mod_cast hTn
  have hbL : (b' : ℤ) * (q (n - 1) : ℤ) ≤ (s : ℤ) * (q (n - 1) : ℤ) :=
    mul_le_mul_of_nonneg_right hb's hL
  rw [abs_lt]
  constructor <;> nlinarith [h1, h2, h3, h4, hbL, hTnZ]

/-! ## Block base points -/

/-- The base points of the `2 a'` blocks of the first interval of `Dnr`. -/
def nrP1 (q : ℕ → ℕ) (n s a' : ℕ) : Finset ℤ :=
  (Finset.range (2 * a')).image
    (fun t : ℕ => -(((a' : ℤ) * (q (n - 1) : ℤ))) + (t : ℤ) * (q (n - 1) : ℤ))

/-- The base points of the `2 b'` blocks of the second interval of `Dnr`. -/
def nrP2 (q : ℕ → ℕ) (n s b' : ℕ) (y : ℤ) : Finset ℤ :=
  (Finset.range (2 * b')).image
    (fun t : ℕ => y - ((b' : ℤ) * (q (n - 1) : ℤ)) + (t : ℤ) * (q (n - 1) : ℤ))

/-- All `2 s` block base points of `Dnr`. -/
def nrP (q : ℕ → ℕ) (n s a' b' : ℕ) (y : ℤ) : Finset ℤ :=
  nrP1 q n s a' ∪ nrP2 q n s b' y

/-- The block with base point `p` (of length `L`). -/
def nrBlock (L : ℕ) (p : ℤ) : Finset ℤ := Finset.Icc p (p + (L : ℤ) - 1)

lemma nrP1_mem_Icc {q : ℕ → ℕ} {n s a' : ℕ} {p : ℤ}
    (hq : 0 < q (n - 1)) (hp : p ∈ nrP1 q n s a') :
    p ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ))) ((a' : ℤ) * (q (n - 1) : ℤ) - 1) := by
  rw [nrP1, Finset.mem_image] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  simp only [Finset.mem_range] at ht
  have hL : (1 : ℤ) ≤ (q (n - 1) : ℤ) := by exact_mod_cast hq
  simp only [Finset.mem_Icc]
  have ht' : ((t : ℤ) + 1) ≤ 2 * (a' : ℤ) := by
    have : t + 1 ≤ 2 * a' := by omega
    exact_mod_cast this
  constructor <;> nlinarith [ht', hL]

lemma nrP2_mem_Icc {q : ℕ → ℕ} {n s b' : ℕ} {y p : ℤ}
    (hq : 0 < q (n - 1)) (hp : p ∈ nrP2 q n s b' y) :
    p ∈ Finset.Icc (y - ((b' : ℤ) * (q (n - 1) : ℤ))) (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1) := by
  rw [nrP2, Finset.mem_image] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  simp only [Finset.mem_range] at ht
  have hL : (1 : ℤ) ≤ (q (n - 1) : ℤ) := by exact_mod_cast hq
  simp only [Finset.mem_Icc]
  have ht' : ((t : ℤ) + 1) ≤ 2 * (b' : ℤ) := by
    have : t + 1 ≤ 2 * b' := by omega
    exact_mod_cast this
  constructor <;> nlinarith [ht', hL]

/-- Block base points of the first interval, as an index set. -/
lemma nrP1_mem {q : ℕ → ℕ} {n s a' : ℕ} {t : ℕ} (ht : t < 2 * a') :
    -(((a' : ℤ) * (q (n - 1) : ℤ))) + (t : ℤ) * (q (n - 1) : ℤ) ∈ nrP1 q n s a' := by
  rw [nrP1, Finset.mem_image]
  exact ⟨t, Finset.mem_range.mpr ht, rfl⟩

lemma nrP2_mem {q : ℕ → ℕ} {n s b' : ℕ} {y : ℤ} {t : ℕ} (ht : t < 2 * b') :
    y - ((b' : ℤ) * (q (n - 1) : ℤ)) + (t : ℤ) * (q (n - 1) : ℤ) ∈ nrP2 q n s b' y := by
  rw [nrP2, Finset.mem_image]
  exact ⟨t, Finset.mem_range.mpr ht, rfl⟩

lemma nrP1_card {q : ℕ → ℕ} {n s a' : ℕ} (hq : 0 < q (n - 1)) :
    (nrP1 q n s a').card = 2 * a' := by
  rw [nrP1, Finset.card_image_of_injOn (f := fun t : ℕ =>
    -(((a' : ℤ) * (q (n - 1) : ℤ))) + (t : ℤ) * (q (n - 1) : ℤ))]
  · simp
  · intro x _ y' _ h
    have hL : (q (n - 1) : ℤ) ≠ 0 := by
      have : (0 : ℤ) < (q (n - 1) : ℤ) := by exact_mod_cast hq
      omega
    have : (x : ℤ) * (q (n - 1) : ℤ) = (y' : ℤ) * (q (n - 1) : ℤ) := by linarith
    have hxy : (x : ℤ) = (y' : ℤ) := mul_right_cancel₀ hL this
    exact_mod_cast hxy

lemma nrP2_card {q : ℕ → ℕ} {n s b' : ℕ} {y : ℤ} (hq : 0 < q (n - 1)) :
    (nrP2 q n s b' y).card = 2 * b' := by
  rw [nrP2, Finset.card_image_of_injOn (f := fun t : ℕ =>
    y - ((b' : ℤ) * (q (n - 1) : ℤ)) + (t : ℤ) * (q (n - 1) : ℤ))]
  · simp
  · intro x _ y' _ h
    have hL : (q (n - 1) : ℤ) ≠ 0 := by
      have : (0 : ℤ) < (q (n - 1) : ℤ) := by exact_mod_cast hq
      omega
    have : (x : ℤ) * (q (n - 1) : ℤ) = (y' : ℤ) * (q (n - 1) : ℤ) := by linarith
    have hxy : (x : ℤ) = (y' : ℤ) := mul_right_cancel₀ hL this
    exact_mod_cast hxy

/-- The blocks based at the points of `nrP1` are contained in the first interval of `Dnr`. -/
lemma nrBlock_mem_of_nrP1 {q : ℕ → ℕ} {n s a' : ℕ} {p x : ℤ}
    (hp : p ∈ nrP1 q n s a') (hx : x ∈ nrBlock (q (n - 1)) p) :
    x ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ))) ((a' : ℤ) * (q (n - 1) : ℤ) - 1) := by
  rw [nrP1, Finset.mem_image] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  simp only [Finset.mem_range] at ht
  simp only [nrBlock, Finset.mem_Icc] at hx
  have hL0 : (0 : ℤ) ≤ (q (n - 1) : ℤ) := Int.natCast_nonneg _
  have ht1 : ((t : ℤ) + 1) ≤ 2 * (a' : ℤ) := by
    have : t + 1 ≤ 2 * a' := by omega
    exact_mod_cast this
  simp only [Finset.mem_Icc]
  constructor
  · have : (0 : ℤ) ≤ (t : ℤ) * (q (n - 1) : ℤ) := mul_nonneg (Int.natCast_nonneg _) hL0
    linarith [hx.1]
  · have h2 : ((t : ℤ) + 1) * (q (n - 1) : ℤ) ≤ 2 * (a' : ℤ) * (q (n - 1) : ℤ) :=
      mul_le_mul_of_nonneg_right ht1 hL0
    have he : -((a' : ℤ) * (q (n - 1) : ℤ)) + (t : ℤ) * (q (n - 1) : ℤ) + (q (n - 1) : ℤ) - 1
        = ((t : ℤ) + 1) * (q (n - 1) : ℤ) - ((a' : ℤ) * (q (n - 1) : ℤ)) - 1 := by ring
    nlinarith [hx.2, h2, he]

lemma nrBlock_mem_of_nrP2 {q : ℕ → ℕ} {n s b' : ℕ} {y p x : ℤ}
    (hp : p ∈ nrP2 q n s b' y) (hx : x ∈ nrBlock (q (n - 1)) p) :
    x ∈ Finset.Icc (y - ((b' : ℤ) * (q (n - 1) : ℤ))) (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1) := by
  rw [nrP2, Finset.mem_image] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  simp only [Finset.mem_range] at ht
  simp only [nrBlock, Finset.mem_Icc] at hx
  have hL0 : (0 : ℤ) ≤ (q (n - 1) : ℤ) := Int.natCast_nonneg _
  have ht1 : ((t : ℤ) + 1) ≤ 2 * (b' : ℤ) := by
    have : t + 1 ≤ 2 * b' := by omega
    exact_mod_cast this
  simp only [Finset.mem_Icc]
  constructor
  · have : (0 : ℤ) ≤ (t : ℤ) * (q (n - 1) : ℤ) := mul_nonneg (Int.natCast_nonneg _) hL0
    linarith [hx.1]
  · have h2 : ((t : ℤ) + 1) * (q (n - 1) : ℤ) ≤ 2 * (b' : ℤ) * (q (n - 1) : ℤ) :=
      mul_le_mul_of_nonneg_right ht1 hL0
    have he : y - (b' : ℤ) * (q (n - 1) : ℤ) + (t : ℤ) * (q (n - 1) : ℤ) + (q (n - 1) : ℤ) - 1
        = y + (((t : ℤ) + 1) * (q (n - 1) : ℤ) - (b' : ℤ) * (q (n - 1) : ℤ)) - 1 := by ring
    nlinarith [hx.2, h2, he]
lemma fracDist_eq_self {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1 / 2) : fracDist x = x := by
  rcases lt_or_eq_of_le h1 with hlt | heq
  · have hr : round x = 0 := round_eq_iff.mpr (by constructor <;> linarith)
    simp only [fracDist, hr, Int.cast_zero, sub_zero, abs_of_pos h0]
  · subst heq
    have hr : round (1 / 2 : ℝ) = 1 := round_eq_iff.mpr (by constructor <;> norm_num)
    simp only [fracDist, hr, Int.cast_one]
    norm_num

/-- `|sin (π u)| = sin (π · fracDist u)`. -/
lemma abs_sin_eq_sin_fracDist (u : ℝ) :
    |Real.sin (Real.pi * u)| = Real.sin (Real.pi * fracDist u) := by
  have h : |Real.sin (Real.pi * u)| = Basic.S u := rfl
  rw [h]
  exact Basic.S_eq_sin_nn u

/-- On `(0,1/2]` the elementary factor bound `-log (sin (π x)) ≤ log (1/(2x))`. -/
lemma neg_log_sin_le {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1 / 2) :
    -Real.log (Real.sin (Real.pi * x)) ≤ Real.log (1 / (2 * x)) := by
  have hsin : 2 * x ≤ Real.sin (Real.pi * x) := by
    have h := Basic.two_div_pi_mul_le_S x
    rw [Basic.S_eq_sin_nn] at h
    have h2 : 2 / Real.pi * (Real.pi * Basic.nn x) = 2 * Basic.nn x := by field_simp
    rw [h2] at h
    have hnn : Basic.nn x = x := by
      rw [show Basic.nn x = fracDist x from rfl, fracDist_eq_self h0 h1]
    rw [hnn] at h
    exact h
  have h2 : (0:ℝ) < 2 * x := by linarith
  have hlog := Real.log_le_log h2 hsin
  have e1 : Real.log (2 * x) = Real.log 2 + Real.log x := Real.log_mul (by norm_num) (ne_of_gt h0)
  have e2 : Real.log (1 / (2 * x)) = -(Real.log 2 + Real.log x) := by
    rw [one_div, Real.log_inv, e1]
  rw [e2]; linarith


/-- Product of the first `n` positive integers. -/
lemma prod_range_add_one (n : ℕ) :
    ∏ r ∈ Finset.range n, ((r : ℝ) + 1) = (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring

/-- **Counting lemma.**  If `T` is a set of indices whose values are pairwise `δ`-separated and
satisfy `v a + δ ≤ U`, then `|T| · δ ≤ U - c` (for `c ≤ U`). -/
lemma card_mul_le {M : ℕ} {v : Fin M → ℝ} {c δ : ℝ}
    (hδ : 0 < δ) (hc : ∀ p, c ≤ v p) (hsep : ∀ a b : Fin M, a ≠ b → δ ≤ |v a - v b|) :
    ∀ n : ℕ, ∀ (U : ℝ) (T : Finset (Fin M)), T.card ≤ n → c ≤ U →
      (∀ a ∈ T, v a + δ ≤ U) → (T.card : ℝ) * δ ≤ U - c := by
  intro n
  induction n with
  | zero =>
    intro U T hT hcU _
    have : T = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hT)
    simp [this]
    linarith
  | succ n ih =>
    intro U T hT hcU h1
    rcases T.eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp; linarith
    · obtain ⟨m, hmT, hmax⟩ := Finset.exists_max_image T v hne
      have hlt : (T.erase m).card ≤ n := by
        have := Finset.card_erase_add_one hmT
        omega
      have h1' : ∀ a ∈ T.erase m, v a + δ ≤ v m := by
        intro a ha
        have haT : a ∈ T := Finset.mem_of_mem_erase ha
        have hne' : a ≠ m := Finset.ne_of_mem_erase ha
        have hv : v a < v m := by
          rcases lt_or_eq_of_le (hmax a haT) with h | h
          · exact h
          · exfalso
            have h2 := hsep a m hne'
            rw [h, sub_self, abs_zero] at h2
            linarith
        have h2 := hsep a m hne'
        rw [abs_of_neg (by linarith)] at h2
        linarith
      have hmU : v m + δ ≤ U := h1 m hmT
      have hmc : c ≤ v m := hc m
      have ih' := ih (v m) (T.erase m) hlt hmc h1'
      have hcard' : ((T.erase m).card : ℝ) + 1 = (T.card : ℝ) := by
        have h := Finset.card_erase_add_one hmT
        rw [← h]
        push_cast
        ring
      nlinarith [ih', hcard', hmU, hmc]

/-- **Single-cluster bound.**  If `v : Fin M → ℝ` takes values in `[c, 1/2]` that are pairwise
`δ`-separated, then the total logarithmic cost is at most
`log(1/(2c)) + (M-1) log(1/(2δ)) - log((M-1)!)`. -/
lemma cluster_single {M : ℕ} {v : Fin M → ℝ} {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hM : 1 ≤ M)
    (hb : ∀ p : Fin M, c ≤ v p ∧ v p ≤ 1 / 2)
    (hsep : ∀ p q : Fin M, p ≠ q → δ ≤ |v p - v q|) :
    ∑ p : Fin M, -Real.log (Real.sin (Real.pi * v p)) ≤
      Real.log (1 / (2 * c)) + ((M : ℝ) - 1) * Real.log (1 / (2 * δ))
        - Real.log (((M - 1).factorial : ℝ)) := by
  have hpos : ∀ p : Fin M, 0 < v p := fun p => lt_of_lt_of_le hc (hb p).1
  have hsingle : ∀ p : Fin M, -Real.log (Real.sin (Real.pi * v p)) ≤ Real.log (1 / (2 * v p)) :=
    fun p => neg_log_sin_le (hpos p) (hb p).2
  set N : Fin M → ℕ := fun p => (Finset.univ.filter (fun q : Fin M => v q < v p)).card with hN
  have hcount : ∀ p : Fin M, c + δ * (N p : ℝ) ≤ v p := by
    intro p
    have h1 : ∀ a ∈ Finset.univ.filter (fun q : Fin M => v q < v p), v a + δ ≤ v p := by
      intro a ha
      rw [Finset.mem_filter] at ha
      have h2 := hsep a p (by rintro rfl; exact absurd ha.2 (lt_irrefl _))
      rw [abs_of_neg (by linarith [ha.2])] at h2
      linarith
    have hcardle : (Finset.univ.filter (fun q : Fin M => v q < v p)).card ≤ M :=
      le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
    have h2 := card_mul_le hδ (fun p => (hb p).1) hsep M (v p)
      (Finset.univ.filter (fun q : Fin M => v q < v p)) hcardle (hb p).1 h1
    simp only [hN]
    linarith
  have hNmem : ∀ p : Fin M, N p ∈ Finset.range M := by
    intro p
    simp only [Finset.mem_range, hN]
    have : (Finset.univ.filter (fun q : Fin M => v q < v p)).card ≤ M - 1 := by
      have hsub : Finset.univ.filter (fun q : Fin M => v q < v p) ⊆ Finset.univ.erase p := by
        intro a ha
        rw [Finset.mem_filter] at ha
        rw [Finset.mem_erase]
        exact ⟨fun h => absurd (h ▸ ha.2) (lt_irrefl _), Finset.mem_univ a⟩
      calc (Finset.univ.filter (fun q : Fin M => v q < v p)).card
          ≤ (Finset.univ.erase p).card := Finset.card_le_card hsub
        _ = M - 1 := by simp [Finset.card_erase_of_mem (Finset.mem_univ p), Fintype.card_fin]
    omega
  have hNinj : ∀ p q : Fin M, p ≠ q → N p ≠ N q := by
    intro p q hpq hcon
    have hvne : v p ≠ v q := by
      intro h
      have := hsep p q hpq
      rw [h, sub_self, abs_zero] at this
      linarith
    rcases lt_or_gt_of_ne hvne with hlt | hlt
    · have hsub2 : Finset.univ.filter (fun r : Fin M => v r < v p) ⊂
          Finset.univ.filter (fun r : Fin M => v r < v q) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro a ha
          rw [Finset.mem_filter] at ha ⊢
          exact ⟨ha.1, by linarith [ha.2]⟩
        · intro heq
          have hp1 : p ∈ Finset.univ.filter (fun r : Fin M => v r < v q) := by
            rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt⟩
          rw [← heq] at hp1
          rw [Finset.mem_filter] at hp1
          exact absurd hp1.2 (lt_irrefl _)
      have := Finset.card_lt_card hsub2
      simp only [hN] at hcon
      omega
    · have hsub2 : Finset.univ.filter (fun r : Fin M => v r < v q) ⊂
          Finset.univ.filter (fun r : Fin M => v r < v p) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro a ha
          rw [Finset.mem_filter] at ha ⊢
          exact ⟨ha.1, by linarith [ha.2]⟩
        · intro heq
          have hq1 : q ∈ Finset.univ.filter (fun r : Fin M => v r < v p) := by
            rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt⟩
          rw [← heq] at hq1
          rw [Finset.mem_filter] at hq1
          exact absurd hq1.2 (lt_irrefl _)
      have := Finset.card_lt_card hsub2
      simp only [hN] at hcon
      omega
  have himage : (Finset.univ.image N) = Finset.range M := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hr
      exact hNmem p
    · rw [Finset.card_image_of_injOn]
      · simp
      · intro p _ q _ h
        by_contra hpq
        exact hNinj p q hpq h
  have hsum : ∑ p : Fin M, Real.log (1 / (2 * v p))
      ≤ ∑ r ∈ Finset.range M, Real.log (1 / (2 * (c + δ * (r : ℝ)))) := by
    have h1 : ∑ p : Fin M, Real.log (1 / (2 * v p))
        ≤ ∑ p : Fin M, Real.log (1 / (2 * (c + δ * (N p : ℝ)))) := by
      refine Finset.sum_le_sum (fun p _ => ?_)
      have hm : (0:ℝ) < 2 * v p := by linarith [hpos p]
      have hm2 : (0:ℝ) < 2 * (c + δ * (N p : ℝ)) := by
        have hNn : (0:ℝ) ≤ (N p : ℝ) := Nat.cast_nonneg _
        nlinarith [hδ, hNn, hc]
      have hle : c + δ * (N p : ℝ) ≤ v p := hcount p
      have hpos1 : (0:ℝ) < 1 / (2 * v p) := by positivity
      have hle2 : 1 / (2 * v p) ≤ 1 / (2 * (c + δ * (N p : ℝ))) :=
        one_div_le_one_div_of_le (a := 2 * (c + δ * (N p : ℝ))) (b := 2 * v p) hm2
          (by linarith)
      exact Real.log_le_log hpos1 hle2
    have h2 : ∑ p : Fin M, Real.log (1 / (2 * (c + δ * (N p : ℝ))))
        = ∑ r ∈ Finset.range M, Real.log (1 / (2 * (c + δ * (r : ℝ)))) := by
      rw [← himage, Finset.sum_image]
      intro p _ q _ h
      by_contra hpq
      exact hNinj p q hpq h
    linarith [h1, h2.le, h2.ge]
  set g : ℕ → ℝ := fun r => Real.log (1 / (2 * (c + δ * (r : ℝ)))) with hg
  have hg0 : g 0 = Real.log (1 / (2 * c)) := by simp [hg]
  have hkey : ∀ r : ℕ, g (r + 1) ≤ Real.log (1 / (2 * δ)) - Real.log ((r : ℝ) + 1) := by
    intro r
    have h1 : 2 * (c + δ * ((r + 1 : ℕ) : ℝ)) ≥ 2 * (δ * ((r : ℝ) + 1)) := by
      push_cast; nlinarith [hc, hδ]
    have h2 : (0:ℝ) < 2 * (δ * ((r : ℝ) + 1)) := by positivity
    have h3 : (0:ℝ) < 2 * (c + δ * ((r + 1 : ℕ) : ℝ)) := by
      have : (0:ℝ) ≤ δ * ((r + 1 : ℕ) : ℝ) := by positivity
      linarith [hc]
    have h4 : Real.log (2 * (δ * ((r : ℝ) + 1))) ≤ Real.log (2 * (c + δ * ((r + 1 : ℕ) : ℝ))) :=
      Real.log_le_log h2 h1
    simp only [hg]
    rw [one_div, Real.log_inv, one_div, Real.log_inv]
    have h5 : (0:ℝ) < (r : ℝ) + 1 := by positivity
    have hexp : Real.log (2 * (δ * ((r : ℝ) + 1))) = Real.log (2 * δ) + Real.log ((r : ℝ) + 1) := by
      rw [show 2 * (δ * ((r:ℝ)+1)) = (2*δ) * ((r:ℝ)+1) by ring,
        Real.log_mul (by positivity) (ne_of_gt h5)]
    rw [hexp] at h4
    linarith
  have hfact : ∑ r ∈ Finset.range (M - 1), Real.log ((r : ℝ) + 1)
      = Real.log (((M - 1).factorial : ℝ)) := by
    have hnz : ∀ r ∈ Finset.range (M - 1), ((r : ℝ) + 1) ≠ 0 := by
      intro r _
      positivity
    have h1 := (Real.log_prod (s := Finset.range (M - 1)) (f := fun r : ℕ => (r : ℝ) + 1) hnz).symm
    rw [prod_range_add_one] at h1
    exact h1
  have hsplit : ∑ r ∈ Finset.range M, g r
      = ∑ r ∈ Finset.range (M - 1), g (r + 1) + g 0 := by
    conv_lhs => rw [show M = (M - 1) + 1 by omega]
    rw [Finset.sum_range_succ']
  have hbound : ∑ r ∈ Finset.range (M - 1), g (r + 1)
      ≤ ((M : ℝ) - 1) * Real.log (1 / (2 * δ)) - Real.log (((M - 1).factorial : ℝ)) := by
    have h1 : ∑ r ∈ Finset.range (M - 1), g (r + 1)
        ≤ ∑ r ∈ Finset.range (M - 1),
            (Real.log (1 / (2 * δ)) - Real.log ((r : ℝ) + 1)) :=
      Finset.sum_le_sum (fun r _ => hkey r)
    have h2 : ∑ r ∈ Finset.range (M - 1),
        (Real.log (1 / (2 * δ)) - Real.log ((r : ℝ) + 1))
        = (((M - 1 : ℕ)) : ℝ) * Real.log (1 / (2 * δ)) - Real.log (((M - 1).factorial : ℝ)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, hfact]
      simp
    rw [h2] at h1
    have hcast : (((M - 1 : ℕ)) : ℝ) = (M : ℝ) - 1 := by
      push_cast [Nat.cast_sub hM]
      ring
    rwa [hcast] at h1
  have hA : ∑ p : Fin M, -Real.log (Real.sin (Real.pi * v p))
      ≤ ∑ p : Fin M, Real.log (1 / (2 * v p)) :=
    Finset.sum_le_sum (fun p _ => hsingle p)
  have hfin : ∑ p : Fin M, Real.log (1 / (2 * v p))
      ≤ ∑ r ∈ Finset.range (M - 1), g (r + 1) + g 0 := by
    rw [← hsplit]
    exact hsum
  linarith [hA, hfin, hbound, hg0]



/-! ## Cluster bound, `Finset` form -/

/-- **Cluster bound, `Finset` form.**  This is `cluster_single` (proved above) with the index set
an arbitrary `Finset ι` rather than `Finset.univ : Finset (Fin M)`. -/
theorem minsum_finset {ι : Type*} [DecidableEq ι] {S : Finset ι} {v : ι → ℝ} {c δ : ℝ}
    (hS : 1 ≤ S.card) (hc : 0 < c) (hδ : 0 < δ)
    (hb : ∀ p ∈ S, c ≤ v p ∧ v p ≤ 1 / 2)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → δ ≤ |v p - v q|) :
    ∑ p ∈ S, -Real.log (Real.sin (Real.pi * (v p)))
      ≤ Real.log (1 / (2 * c)) + ((S.card : ℝ) - 1) * Real.log (1 / (2 * δ))
        - Real.log (((S.card - 1).factorial : ℕ) : ℝ) := by
  classical
  set e : S ≃ Fin S.card := Finset.equivFin S with he
  have hsum : (∑ p ∈ S, -Real.log (Real.sin (Real.pi * (v p))))
      = ∑ i : Fin S.card, -Real.log (Real.sin (Real.pi * (v (e.symm i)))) := by
    have h1 : (∑ p ∈ S, -Real.log (Real.sin (Real.pi * (v p))))
        = ∑ p : S, -Real.log (Real.sin (Real.pi * (v p))) := by
      rw [← Finset.sum_attach S (fun p => -Real.log (Real.sin (Real.pi * (v p))))]
      rfl
    have h2 : (∑ p : S, -Real.log (Real.sin (Real.pi * (v p))))
        = ∑ i : Fin S.card, -Real.log (Real.sin (Real.pi * (v (e.symm i)))) :=
      (Equiv.sum_comp e.symm (fun p : S => -Real.log (Real.sin (Real.pi * (v p))))).symm
    rw [h1, h2]
  rw [hsum]
  exact cluster_single hc hδ hS
    (fun i => hb (e.symm i) (e.symm i).2)
    (fun i j hij => hsep (e.symm i) (e.symm i).2 (e.symm j) (e.symm j).2
      (fun h => hij (e.symm.injective (Subtype.ext h))))


end

end Work.TMC16Core.Core
