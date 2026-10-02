import Mathlib
import Submission.Work.LinnikAreas2.T13SideDefs
import Submission.Work.LinnikAreas.Density4.T13.Basic
import Submission.Work.LinnikAreas.Density4.T13.Num1

open scoped BigOperators
noncomputable section
namespace Work.LinnikAreas2
open Work.LinnikAreas.Density4
open Work.LinnikAreas.Density4.T13

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

/-! (t13cert) A tiny fixed-point interval engine: an enclosure `A : ℤ × ℤ` of `x : ℝ` means
`A.1 / 10^20 ≤ x ≤ A.2 / 10^20`.  All endpoint arithmetic is integer arithmetic with
outward rounding, so the numerical side conditions below are closed `decide` goals. -/

private def t13N : ℤ := 100000000000000000000

private theorem t13N_pos : (0:ℝ) < (t13N:ℝ) := by norm_num [t13N]

private theorem t13N_ne : (t13N:ℝ) ≠ 0 := ne_of_gt t13N_pos

private def zMem (A : ℤ × ℤ) (x : ℝ) : Prop := (A.1:ℝ) / t13N ≤ x ∧ x ≤ (A.2:ℝ) / t13N

private def zofNatI (a : ℕ) : ℤ × ℤ := ((a:ℤ) * t13N, (a:ℤ) * t13N)
private def zoneI : ℤ × ℤ := (t13N, t13N)
private def zaddI (A B : ℤ × ℤ) : ℤ × ℤ := (A.1 + B.1, A.2 + B.2)
private def znegI (A : ℤ × ℤ) : ℤ × ℤ := (-A.2, -A.1)
private def zsubI (A B : ℤ × ℤ) : ℤ × ℤ := (A.1 - B.2, A.2 - B.1)
private def zmulI (A B : ℤ × ℤ) : ℤ × ℤ :=
  (min (min (A.1 * B.1) (A.1 * B.2)) (min (A.2 * B.1) (A.2 * B.2)) / t13N,
   -((-(max (max (A.1 * B.1) (A.1 * B.2)) (max (A.2 * B.1) (A.2 * B.2)))) / t13N))
private def zinvI (B : ℤ × ℤ) : ℤ × ℤ := (t13N * t13N / B.2, -((-(t13N * t13N)) / B.1))
private def zdivI (A B : ℤ × ℤ) : ℤ × ℤ := zmulI A (zinvI B)
private def zdivNatI (A : ℤ × ℤ) (m : ℕ) : ℤ × ℤ := (A.1 / (m:ℤ), -((-A.2) / (m:ℤ)))

private theorem zfl (a n : ℤ) (hn : 0 < n) : ((a / n : ℤ) : ℝ) ≤ (a:ℝ) / n := by
  have h := Int.ediv_mul_le a (ne_of_gt hn)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hn']
  exact_mod_cast h

private theorem zcl (a n : ℤ) (hn : 0 < n) : (a:ℝ) / n ≤ ((-((-a) / n) : ℤ) : ℝ) := by
  have h := zfl (-a) n hn
  push_cast at h ⊢
  rw [neg_div] at h
  linarith

private theorem zofNat_mem (a : ℕ) : zMem (zofNatI a) (a:ℝ) := by
  have : ((a:ℤ) * t13N : ℤ) / (t13N:ℝ) = (a:ℝ) := by
    push_cast; exact mul_div_cancel_right₀ _ t13N_ne
  exact ⟨this.le, this.ge⟩

private theorem zone_mem : zMem zoneI (1:ℝ) := by
  have : (t13N:ℝ) / (t13N:ℝ) = 1 := div_self t13N_ne
  exact ⟨this.le, this.ge⟩

private theorem zadd_mem {A B : ℤ × ℤ} {x y : ℝ} (hx : zMem A x) (hy : zMem B y) :
    zMem (zaddI A B) (x + y) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  simp only [zMem, zaddI, Int.cast_add, add_div]
  exact ⟨by linarith, by linarith⟩

private theorem zneg_mem {A : ℤ × ℤ} {x : ℝ} (hx : zMem A x) : zMem (znegI A) (-x) := by
  obtain ⟨h1, h2⟩ := hx
  simp only [zMem, znegI, Int.cast_neg, neg_div]
  exact ⟨by linarith, by linarith⟩

private theorem zsub_mem {A B : ℤ × ℤ} {x y : ℝ} (hx : zMem A x) (hy : zMem B y) :
    zMem (zsubI A B) (x - y) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  simp only [zMem, zsubI, Int.cast_sub, sub_div]
  exact ⟨by linarith, by linarith⟩

private theorem zcorner (a b : ℤ) : (a:ℝ) / t13N * ((b:ℝ) / t13N) = ((a * b : ℤ) : ℝ) / t13N / t13N := by
  push_cast; ring

private theorem zmul_mem {A B : ℤ × ℤ} {x y : ℝ} (hx : zMem A x) (hy : zMem B y) :
    zMem (zmulI A B) (x * y) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  have L := Iv.min4_le_mul h1 h2 h3 h4
  have U := Iv.mul_le_max4 h1 h2 h3 h4
  rw [zcorner, zcorner, zcorner, zcorner] at L U
  have hN : (0:ℤ) < t13N := by norm_num [t13N]
  set m := min (min (A.1 * B.1) (A.1 * B.2)) (min (A.2 * B.1) (A.2 * B.2)) with hm
  set M := max (max (A.1 * B.1) (A.1 * B.2)) (max (A.2 * B.1) (A.2 * B.2)) with hM
  have fl : ((m / t13N : ℤ) : ℝ) / t13N ≤ (m:ℝ) / t13N / t13N :=
    div_le_div_of_nonneg_right (zfl m t13N hN) t13N_pos.le
  have cl : (M:ℝ) / t13N / t13N ≤ ((-((-M) / t13N) : ℤ) : ℝ) / t13N :=
    div_le_div_of_nonneg_right (zcl M t13N hN) t13N_pos.le
  have mono : ∀ p q : ℤ, p ≤ q → (p:ℝ) / t13N / t13N ≤ (q:ℝ) / t13N / t13N := fun p q h =>
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by exact_mod_cast h) t13N_pos.le)
      t13N_pos.le
  refine ⟨le_trans fl (le_trans ?_ L), le_trans U (le_trans ?_ cl)⟩
  · exact le_min (le_min (mono _ _ (min_le_of_left_le (min_le_left _ _)))
      (mono _ _ (min_le_of_left_le (min_le_right _ _))))
      (le_min (mono _ _ (min_le_of_right_le (min_le_left _ _)))
      (mono _ _ (min_le_of_right_le (min_le_right _ _))))
  · exact max_le (max_le (mono _ _ (le_max_of_le_left (le_max_left _ _)))
      (mono _ _ (le_max_of_le_left (le_max_right _ _))))
      (max_le (mono _ _ (le_max_of_le_right (le_max_left _ _)))
      (mono _ _ (le_max_of_le_right (le_max_right _ _))))

private theorem zinv_mem {B : ℤ × ℤ} {y : ℝ} (hy : zMem B y) (hpos : 0 < B.1) :
    zMem (zinvI B) y⁻¹ := by
  obtain ⟨h3, h4⟩ := hy
  have hN : (0:ℤ) < t13N := by norm_num [t13N]
  have hB1 : (0:ℝ) < B.1 := by exact_mod_cast hpos
  have hB1' : (0:ℝ) < (B.1:ℝ) / t13N := div_pos hB1 t13N_pos
  have hypos : 0 < y := lt_of_lt_of_le hB1' h3
  have hB2' : (0:ℝ) < (B.2:ℝ) / t13N := lt_of_lt_of_le hypos h4
  have hB2 : (0:ℤ) < B.2 := by
    have : (0:ℝ) < B.2 := by
      have := mul_pos hB2' t13N_pos
      rwa [div_mul_cancel₀ _ t13N_ne] at this
    exact_mod_cast this
  have e : ∀ q : ℝ, 0 < q → ((t13N * t13N : ℤ) : ℝ) / q / t13N = (q / t13N)⁻¹ := by
    intro q hq; push_cast; field_simp [t13N_ne]
  constructor
  · simp only [zinvI]
    calc ((t13N * t13N / B.2 : ℤ) : ℝ) / t13N
        ≤ ((t13N * t13N : ℤ) : ℝ) / (B.2:ℝ) / t13N :=
          div_le_div_of_nonneg_right (zfl _ _ hB2) t13N_pos.le
      _ = ((B.2:ℝ) / t13N)⁻¹ := e _ (by exact_mod_cast hB2)
      _ ≤ y⁻¹ := (inv_le_inv₀ hB2' hypos).mpr h4
  · simp only [zinvI]
    calc y⁻¹ ≤ ((B.1:ℝ) / t13N)⁻¹ := (inv_le_inv₀ hypos hB1').mpr h3
      _ = ((t13N * t13N : ℤ) : ℝ) / (B.1:ℝ) / t13N := (e _ hB1).symm
      _ ≤ ((-((-(t13N * t13N)) / B.1) : ℤ) : ℝ) / t13N :=
          div_le_div_of_nonneg_right (zcl _ _ hpos) t13N_pos.le

private theorem zdiv_mem {A B : ℤ × ℤ} {x y : ℝ} (hx : zMem A x) (hy : zMem B y)
    (hpos : 0 < B.1) : zMem (zdivI A B) (x / y) := by
  rw [div_eq_mul_inv]; exact zmul_mem hx (zinv_mem hy hpos)

private theorem zdivNat_mem {A : ℤ × ℤ} {x : ℝ} (hx : zMem A x) (m : ℕ) (hm : 0 < m) :
    zMem (zdivNatI A m) (x / (m:ℝ)) := by
  obtain ⟨h1, h2⟩ := hx
  have hm' : (0:ℤ) < (m:ℤ) := by exact_mod_cast hm
  have hmr : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have e : ∀ q : ℤ, (q:ℝ) / (m:ℤ) / t13N = (q:ℝ) / t13N / (m:ℝ) := by
    intro q; push_cast; ring
  constructor
  · simp only [zdivNatI]
    calc ((A.1 / (m:ℤ) : ℤ) : ℝ) / t13N ≤ (A.1:ℝ) / (m:ℤ) / t13N :=
          div_le_div_of_nonneg_right (zfl _ _ hm') t13N_pos.le
      _ = (A.1:ℝ) / t13N / (m:ℝ) := e _
      _ ≤ x / (m:ℝ) := div_le_div_of_nonneg_right h1 hmr.le
  · simp only [zdivNatI]
    calc x / (m:ℝ) ≤ (A.2:ℝ) / t13N / (m:ℝ) := div_le_div_of_nonneg_right h2 hmr.le
      _ = (A.2:ℝ) / (m:ℤ) / t13N := (e _).symm
      _ ≤ ((-((-A.2) / (m:ℤ)) : ℤ) : ℝ) / t13N :=
          div_le_div_of_nonneg_right (zcl _ _ hm') t13N_pos.le

private theorem zwiden {A : ℤ × ℤ} {x : ℝ} (B : ℤ × ℤ) (hx : zMem A x) (h : B.1 ≤ A.1 ∧ A.2 ≤ B.2) :
    zMem B x := by
  obtain ⟨h1, h2⟩ := hx
  have c1 : (B.1:ℝ) ≤ A.1 := by exact_mod_cast h.1
  have c2 : (A.2:ℝ) ≤ B.2 := by exact_mod_cast h.2
  exact ⟨le_trans (div_le_div_of_nonneg_right c1 t13N_pos.le) h1,
    le_trans h2 (div_le_div_of_nonneg_right c2 t13N_pos.le)⟩

/-- `|t| ≤ max (-T.1) T.2 / N` for `t` enclosed by `T`. -/
private theorem zabs_le {T : ℤ × ℤ} {t : ℝ} (ht : zMem T t) :
    |t| ≤ ((max (-T.1) T.2 : ℤ) : ℝ) / t13N := by
  obtain ⟨h1, h2⟩ := ht
  rw [abs_le]
  have a1 : ((-T.1 : ℤ) : ℝ) / t13N ≤ ((max (-T.1) T.2 : ℤ) : ℝ) / t13N :=
    div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) t13N_pos.le
  have a2 : (T.2 : ℝ) / t13N ≤ ((max (-T.1) T.2 : ℤ) : ℝ) / t13N :=
    div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) t13N_pos.le
  rw [Int.cast_neg, neg_div] at a1
  constructor <;> linarith

/-! Taylor partial sums with their last term. -/

private def zsinT (X : ℤ × ℤ) : ℕ → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => ((0, 0), X)
  | k + 1 => ((zaddI (zsinT X k).1 (zsinT X k).2),
      zdivNatI (zmulI (zsinT X k).2 (znegI (zmulI X X))) ((2 * k + 2) * (2 * k + 3)))

private def zcosT (X : ℤ × ℤ) : ℕ → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => ((0, 0), zoneI)
  | k + 1 => ((zaddI (zcosT X k).1 (zcosT X k).2),
      zdivNatI (zmulI (zcosT X k).2 (znegI (zmulI X X))) ((2 * k + 1) * (2 * k + 2)))

private def zexpT (X : ℤ × ℤ) : ℕ → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => ((0, 0), zoneI)
  | k + 1 => ((zaddI (zexpT X k).1 (zexpT X k).2), zdivNatI (zmulI (zexpT X k).2 X) (k + 1))

private theorem zzero_mem : zMem ((0:ℤ), (0:ℤ)) (0:ℝ) := by simp [zMem]

private theorem zsinT_mem {X : ℤ × ℤ} {x : ℝ} (hx : zMem X x) : ∀ k : ℕ,
    zMem (zsinT X k).1 (∑ i ∈ Finset.range k, (-1:ℝ)^i * x^(2*i+1) / ((2*i+1).factorial : ℝ)) ∧
    zMem (zsinT X k).2 ((-1:ℝ)^k * x^(2*k+1) / ((2*k+1).factorial : ℝ))
  | 0 => by
    refine ⟨by simpa [zsinT] using zzero_mem, ?_⟩
    simpa [zsinT] using hx
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := zsinT_mem hx k
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_range_succ]; exact zadd_mem ih1 ih2
    · have h := zdivNat_mem (zmul_mem ih2 (zneg_mem (zmul_mem hx hx))) ((2 * k + 2) * (2 * k + 3))
        (by positivity)
      have e : (-1:ℝ)^(k+1) * x^(2*(k+1)+1) / ((2*(k+1)+1).factorial : ℝ) =
          (-1:ℝ)^k * x^(2*k+1) / ((2*k+1).factorial : ℝ) * -(x * x) /
            (((2 * k + 2) * (2 * k + 3) : ℕ) : ℝ) := by
        rw [show 2*(k+1)+1 = (2*k+1) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      rw [e]; exact h

private theorem zcosT_mem {X : ℤ × ℤ} {x : ℝ} (hx : zMem X x) : ∀ k : ℕ,
    zMem (zcosT X k).1 (∑ i ∈ Finset.range k, (-1:ℝ)^i * x^(2*i) / ((2*i).factorial : ℝ)) ∧
    zMem (zcosT X k).2 ((-1:ℝ)^k * x^(2*k) / ((2*k).factorial : ℝ))
  | 0 => by
    refine ⟨by simpa [zcosT] using zzero_mem, ?_⟩
    simpa [zcosT] using zone_mem
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := zcosT_mem hx k
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_range_succ]; exact zadd_mem ih1 ih2
    · have h := zdivNat_mem (zmul_mem ih2 (zneg_mem (zmul_mem hx hx))) ((2 * k + 1) * (2 * k + 2))
        (by positivity)
      have e : (-1:ℝ)^(k+1) * x^(2*(k+1)) / ((2*(k+1)).factorial : ℝ) =
          (-1:ℝ)^k * x^(2*k) / ((2*k).factorial : ℝ) * -(x * x) /
            (((2 * k + 1) * (2 * k + 2) : ℕ) : ℝ) := by
        rw [show 2*(k+1) = (2*k) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      rw [e]; exact h

private theorem zexpT_mem {X : ℤ × ℤ} {x : ℝ} (hx : zMem X x) : ∀ k : ℕ,
    zMem (zexpT X k).1 (∑ m ∈ Finset.range k, x^m / (m.factorial : ℝ)) ∧
    zMem (zexpT X k).2 (x^k / (k.factorial : ℝ))
  | 0 => by
    refine ⟨by simpa [zexpT] using zzero_mem, ?_⟩
    simpa [zexpT] using zone_mem
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := zexpT_mem hx k
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_range_succ]; exact zadd_mem ih1 ih2
    · have h := zdivNat_mem (zmul_mem ih2 hx) (k + 1) (by positivity)
      have e : x^(k+1) / ((k+1).factorial : ℝ) = x^k / (k.factorial : ℝ) * x / ((k + 1 : ℕ) : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; field_simp; ring
      rw [e]; exact h

private def zsinB (X : ℤ × ℤ) (n : ℕ) : ℤ × ℤ :=
  ((zsinT X n).1.1 - max (-(zsinT X n).2.1) (zsinT X n).2.2,
   (zsinT X n).1.2 + max (-(zsinT X n).2.1) (zsinT X n).2.2)

private def zcosB (X : ℤ × ℤ) (n : ℕ) : ℤ × ℤ :=
  ((zcosT X n).1.1 - max (-(zcosT X n).2.1) (zcosT X n).2.2,
   (zcosT X n).1.2 + max (-(zcosT X n).2.1) (zcosT X n).2.2)

private def zexpB (X : ℤ × ℤ) (n : ℕ) : ℤ × ℤ :=
  ((zexpT X n).1.1 - 2 * max (-(zexpT X n).2.1) (zexpT X n).2.2,
   (zexpT X n).1.2 + 2 * max (-(zexpT X n).2.1) (zexpT X n).2.2)

/-- generic: from `|f - s| ≤ r`, `s ∈ S`, `r ≤ c·R/N` get `f ∈ [S.1 - cR, S.2 + cR]`. -/
private theorem zenc {S : ℤ × ℤ} {f s r : ℝ} {R c : ℤ} (hs : zMem S s) (h : |f - s| ≤ r)
    (hr : r ≤ (c:ℝ) * ((R:ℤ):ℝ) / t13N) : zMem (S.1 - c * R, S.2 + c * R) f := by
  obtain ⟨h1, h2⟩ := hs
  rw [abs_le] at h
  simp only [zMem]
  push_cast
  rw [sub_div, add_div]
  constructor <;> nlinarith [h.1, h.2]

private theorem zsin_mem {X : ℤ × ℤ} {x : ℝ} (hx : zMem X x) (hx0 : 0 ≤ x) (n : ℕ) :
    zMem (zsinB X n) (Real.sin x) := by
  obtain ⟨h1, h2⟩ := zsinT_mem hx n
  have ht := (t13_sin_cos_taylor x hx0 n).1
  have hab := zabs_le h2
  have e : |(-1:ℝ)^n * x^(2*n+1) / ((2*n+1).factorial : ℝ)| = x^(2*n+1) / ((2*n+1).factorial : ℝ) := by
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_of_nonneg hx0,
      Nat.abs_cast]
  rw [e] at hab
  have := zenc (c := 1) (R := max (-(zsinT X n).2.1) (zsinT X n).2.2) h1 ht (by simpa using hab)
  simpa [zsinB] using this

private theorem zcos_mem {X : ℤ × ℤ} {x : ℝ} (hx : zMem X x) (hx0 : 0 ≤ x) (n : ℕ) :
    zMem (zcosB X n) (Real.cos x) := by
  obtain ⟨h1, h2⟩ := zcosT_mem hx n
  have ht := (t13_sin_cos_taylor x hx0 n).2
  have hab := zabs_le h2
  have e : |(-1:ℝ)^n * x^(2*n) / ((2*n).factorial : ℝ)| = x^(2*n) / ((2*n).factorial : ℝ) := by
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_of_nonneg hx0,
      Nat.abs_cast]
  rw [e] at hab
  have := zenc (c := 1) (R := max (-(zcosT X n).2.1) (zcosT X n).2.2) h1 ht (by simpa using hab)
  simpa [zcosB] using this

private theorem zexp_pt_mem (w : ℤ) (n : ℕ) (hn : 2 * |w| ≤ ((n:ℤ) + 1) * t13N) :
    zMem (zexpB (w, w) n) (Real.exp ((w:ℝ) / t13N)) := by
  have hx : zMem (w, w) ((w:ℝ) / t13N) := ⟨le_rfl, le_rfl⟩
  obtain ⟨h1, h2⟩ := zexpT_mem hx n
  have hcond : |(w:ℝ) / t13N| / ((n:ℝ) + 1) ≤ 1 / 2 := by
    have hn' : (2:ℝ) * |(w:ℝ)| ≤ ((n:ℝ) + 1) * t13N := by exact_mod_cast hn
    rw [abs_div, abs_of_pos t13N_pos, div_div, div_le_iff₀ (mul_pos t13N_pos (by positivity))]
    linarith
  have ht := Work.LinnikAreas.A7.exp_rem_bound ((w:ℝ) / t13N) n hcond
  have hab := zabs_le h2
  have e : |((w:ℝ) / t13N) ^ n / (n.factorial : ℝ)| = |(w:ℝ) / t13N| ^ n / (n.factorial : ℝ) := by
    rw [abs_div, abs_pow, Nat.abs_cast]
  rw [e] at hab
  have := zenc (c := 2) (R := max (-(zexpT (w, w) n).2.1) (zexpT (w, w) n).2.2) h1 ht
    (le_trans (mul_le_mul_of_nonneg_right hab (by norm_num : (0:ℝ) ≤ 2))
      (le_of_eq (by rw [Int.cast_ofNat]; ring)))
  simpa [zexpB] using this

private theorem zexp_mem {W : ℤ × ℤ} {w : ℝ} (hW : zMem W w) (n1 n2 : ℕ)
    (h1 : 2 * |W.1| ≤ ((n1:ℤ) + 1) * t13N) (h2 : 2 * |W.2| ≤ ((n2:ℤ) + 1) * t13N) :
    zMem ((zexpB (W.1, W.1) n1).1, (zexpB (W.2, W.2) n2).2) (Real.exp w) :=
  ⟨le_trans (zexp_pt_mem W.1 n1 h1).1 (Real.exp_le_exp.mpr hW.1),
   le_trans (Real.exp_le_exp.mpr hW.2) (zexp_pt_mem W.2 n2 h2).2⟩

/-! The atoms. -/

private theorem ztan_mem {S C : ℤ × ℤ} {x : ℝ} (hS : zMem S (Real.sin x)) (hC : zMem C (Real.cos x))
    (h : 0 < (znegI C).1) : zMem (zdivI (znegI S) (znegI C)) (Real.tan x) := by
  rw [Real.tan_eq_sin_div_cos, ← neg_div_neg_eq]
  exact zdiv_mem (zneg_mem hS) (zneg_mem hC) h

private theorem zcsq_mem {C : ℤ × ℤ} {x : ℝ} (hC : zMem C (Real.cos x)) :
    zMem (zmulI C C) (Real.cos x ^ 2) := by
  rw [pow_two]; exact zmul_mem hC hC

private theorem zsin2_mem {S C : ℤ × ℤ} {x : ℝ} (hS : zMem S (Real.sin x)) (hC : zMem C (Real.cos x)) :
    zMem (zmulI (zmulI (zofNatI 2) S) C) (Real.sin (2 * x)) := by
  rw [Real.sin_two_mul]
  have h := zmul_mem (zmul_mem (zofNat_mem 2) hS) hC
  simpa using h

private theorem zcos2_mem {C : ℤ × ℤ} {x : ℝ} (hC : zMem C (Real.cos x)) :
    zMem (zsubI (zmulI (zofNatI 2) (zmulI C C)) zoneI) (Real.cos (2 * x)) := by
  rw [Real.cos_two_mul, pow_two]
  have h := zsub_mem (zmul_mem (zofNat_mem 2) (zmul_mem hC hC)) zone_mem
  simpa using h

private theorem zW_mem {P L Z T : ℤ × ℤ} {th lam z : ℝ} (hth : zMem P th) (hlam : zMem L lam)
    (hz : zMem Z z) (hT : zMem T (Real.tan th)) (hlam0 : 0 < lam) (hT0 : T.2 < 0)
    (hpos : 0 < (znegI (zmulI L T)).1) :
    zMem (zdivI (znegI (zmulI (zmulI (zofNatI 2) P) Z)) (znegI (zmulI L T)))
      (-(2 * gammaT th lam * z)) := by
  have hTneg : Real.tan th < 0 := by
    have h2 : (T.2:ℝ) / t13N < 0 := div_neg_of_neg_of_pos (by exact_mod_cast hT0) t13N_pos
    linarith [hT.2]
  rw [neg_two_gammaT_mul_eq th lam z (ne_of_gt hlam0) (ne_of_lt hTneg), ← neg_div_neg_eq]
  have h := zdiv_mem (zneg_mem (zmul_mem (zmul_mem (zofNat_mem 2) hth) hz))
    (zneg_mem (zmul_mem hlam hT)) hpos
  simpa using h

private theorem zFT_mem {M D : ℤ × ℤ} {th lam z : ℝ}
    (hθ1 : Real.pi / 2 < th) (hθ2 : th < Real.pi) (hlam : 0 < lam) (hz : z ≠ 0)
    (hM : zMem M (Mreal th lam z (Real.tan th) (Real.cos th ^ 2) (Real.sin (2 * th))
      (Real.cos (2 * th)) (Real.exp (-(2 * gammaT th lam * z)))))
    (hD : zMem D (Dreal lam z (Real.tan th))) (hpos : 0 < D.1) :
    zMem (zdivI M D) (FT th lam z) := by
  rw [FTreal_spec th lam z hθ1 hθ2 hlam hz]
  have hTne : Real.tan th ≠ 0 := ne_of_lt (tan_neg_of_half_pi_lt hθ1 hθ2)
  have hz2 : (0:ℝ) < z ^ 2 := by positivity
  have hWne : z ^ 2 + (lam * Real.tan th) ^ 2 ≠ 0 := by positivity
  rw [FTreal_eq th lam z _ _ _ _ _ hz (ne_of_gt hlam) hTne hWne]
  exact zdiv_mem hM hD hpos

private theorem zC_mem {M D : ℤ × ℤ} {th lam : ℝ}
    (hθ1 : Real.pi / 2 < th) (hθ2 : th < Real.pi) (hlam : 0 < lam)
    (hM : zMem M (M0real th lam (Real.tan th))) (hD : zMem D (D0real (Real.tan th)))
    (hpos : 0 < D.1) : zMem (zdivI M D) (fT th lam 0 / 6) := by
  rw [t13_ft_zero th lam hθ1 hθ2 hlam]
  have hTne : Real.tan th ≠ 0 := ne_of_lt (tan_neg_of_half_pi_lt hθ1 hθ2)
  have hM0 : lam * (1 + Real.tan th ^ 2) * (3 - th * Real.tan th - 3 * th / Real.tan th) / 6
      = M0real th lam (Real.tan th) / D0real (Real.tan th) := by
    rw [← M0_eq th lam (Real.tan th) hTne]
    simp only [f0real]
    ring
  rw [hM0]
  exact zdiv_mem hM hD hpos

/-- `π/2 < θ` from an enclosure of `θ`. -/
private theorem zpi1 {P : ℤ × ℤ} {th : ℝ} (hth : zMem P th) (h : 1575 * 100000000000000000 ≤ P.1) :
    Real.pi / 2 < th := by
  have hp := Real.pi_lt_d2
  have h' : ((1575 * 100000000000000000 : ℤ) : ℝ) ≤ (P.1 : ℝ) := by exact_mod_cast h
  have e : (P.1:ℝ) / t13N ≥ 1575 / 1000 := by
    rw [ge_iff_le, le_div_iff₀ t13N_pos]; norm_num [t13N] at h' ⊢; linarith
  linarith [hth.1]

/-- `θ < π` from an enclosure of `θ`. -/
private theorem zpi2 {P : ℤ × ℤ} {th : ℝ} (hth : zMem P th) (h : P.2 ≤ 314 * 1000000000000000000) :
    th < Real.pi := by
  have hp := Real.pi_gt_d2
  have h' : (P.2 : ℝ) ≤ ((314 * 1000000000000000000 : ℤ) : ℝ) := by exact_mod_cast h
  have e : (P.2:ℝ) / t13N ≤ 314 / 100 := by
    rw [div_le_iff₀ t13N_pos]; norm_num [t13N] at h' ⊢; linarith
  linarith [hth.2]

/-- real consequences of the integer side conditions of `ratio_bound` / `ratio_side`. -/
private theorem zden {P Q R : ℤ × ℤ} (h : 0 < (Q.1 - R.2) ^ 2 - P.2 * R.2) :
    0 < ((Q.1:ℝ) / t13N - (R.2:ℝ) / t13N) ^ 2 - (P.2:ℝ) / t13N * ((R.2:ℝ) / t13N) := by
  have e : ((Q.1:ℝ) / t13N - (R.2:ℝ) / t13N) ^ 2 - (P.2:ℝ) / t13N * ((R.2:ℝ) / t13N) =
      (((Q.1 - R.2) ^ 2 - P.2 * R.2 : ℤ) : ℝ) / (t13N:ℝ) ^ 2 := by
    push_cast; field_simp [t13N_ne]
  rw [e]
  exact div_pos (by exact_mod_cast h) (pow_pos t13N_pos 2)

private theorem zle_div {a b : ℤ} (h : a ≤ b) : (a:ℝ) / t13N ≤ (b:ℝ) / t13N :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) t13N_pos.le

private theorem z0le {a : ℤ} (h : 0 ≤ a) : (0:ℝ) ≤ (a:ℝ) / t13N :=
  div_nonneg (by exact_mod_cast h) t13N_pos.le

private theorem zfinal {P Q R : ℤ × ℤ} {A B f : ℝ} (hA : zMem P A) (hB : zMem Q B) (hc : zMem R (f / 6))
    (n : ℕ) (h : 0 ≤ P.1 ∧ 0 ≤ R.1 ∧ R.2 ≤ P.1 ∧ R.2 ≤ Q.1 ∧ 0 < (Q.1 - R.2) ^ 2 - P.2 * R.2 ∧
      P.2 * (P.2 - R.1) < ((n:ℤ) + 1) * ((Q.1 - R.2) ^ 2 - P.2 * R.2)) :
    A * (A - f / 6) / ((B - f / 6) ^ 2 - A * f / 6) < ((n:ℕ):ℝ) + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rw [mul_div_assoc A f 6]
  refine ratio_bound hA.1 hA.2 hB.1 hB.2 hc.1 hc.2 (z0le h1) (z0le h2) (zle_div h3) (zle_div h4)
    (zden h5) ?_
  have en : (P.2:ℝ) / t13N * ((P.2:ℝ) / t13N - (R.1:ℝ) / t13N) =
      ((P.2 * (P.2 - R.1) : ℤ) : ℝ) / (t13N:ℝ) ^ 2 := by
    push_cast; field_simp [t13N_ne]
  have ed : ((Q.1:ℝ) / t13N - (R.2:ℝ) / t13N) ^ 2 - (P.2:ℝ) / t13N * ((R.2:ℝ) / t13N) =
      (((Q.1 - R.2) ^ 2 - P.2 * R.2 : ℤ) : ℝ) / (t13N:ℝ) ^ 2 := by
    push_cast; field_simp [t13N_ne]
  have hN2 : (0:ℝ) < (t13N:ℝ) ^ 2 := pow_pos t13N_pos 2
  have hd : (0:ℝ) < (((Q.1 - R.2) ^ 2 - P.2 * R.2 : ℤ) : ℝ) := by exact_mod_cast h5
  rw [en, ed, div_div_div_cancel_right₀ (ne_of_gt hN2), div_lt_iff₀ hd]
  exact_mod_cast h6

private theorem zside {P Q R : ℤ × ℤ} {A B c : ℝ} (hA : zMem P A) (hB : zMem Q B) (hc : zMem R c)
    (h : 0 ≤ P.1 ∧ 0 ≤ R.1 ∧ R.2 ≤ Q.1 ∧ 0 < (Q.1 - R.2) ^ 2 - P.2 * R.2) :
    c < B ∧ (B - c) ^ 2 > A * c := by
  obtain ⟨h1, h2, h4, h5⟩ := h
  exact ratio_side hA.1 hA.2 hB.1 hB.2 hc.1 hc.2 (z0le h1) (z0le h2) (zle_div h4) (zden h5)

theorem side_0 : sideCond ((8:ℝ)/10) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 1021) (zofNatI 500)) ((1021:ℝ)/(500:ℝ)) := zdiv_mem (zofNat_mem 1021) (zofNat_mem 500) (by decide)
  have hθ1 : Real.pi / 2 < ((1021:ℝ)/(500:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1021:ℝ)/(500:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 8) (zofNatI 10)) ((8:ℝ)/10) := zdiv_mem (zofNat_mem 8) (zofNat_mem 10) (by decide)
  have hS := zwiden (89102251537529194883, 89102251537529299564) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-45395911390155794107, -45395911390154615161) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-196278142257660759344, -196278142257655431343) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (20607887709427695243, 20607887709428765631) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-80897558309221058965, -80897558309218862988) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-58784224581144609514, -58784224581142468738) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (90511351878798487635, 90511351878800944583) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (247221254970125353997, 247221254970131634625) (zexp_mem hWA 17 17 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5104180856761992325515, 5104180856765918968931) (FT ((1021:ℝ)/(500:ℝ)) ((8:ℝ)/10) ((((-87:ℝ)/(250:ℝ))))) := zwiden (5104180856761992325515, 5104180856765918968931) (zFT_mem (lam := ((8:ℝ)/10)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 113) (zofNatI 250)) (((113:ℝ)/(250:ℝ))) := zdiv_mem (zofNat_mem 113) (zofNat_mem 250) (by decide)
  have hWB := zwiden (-117560721405798928021, -117560721405795736814) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (30863151738281264503, 30863151738282320547) (zexp_mem hWB 19 19 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3095414285615566401162, 3095414285616945842980) (FT ((1021:ℝ)/(500:ℝ)) ((8:ℝ)/10) ((((113:ℝ)/(250:ℝ))))) := zwiden (3095414285615566401162, 3095414285616945842980) (zFT_mem (lam := ((8:ℝ)/10)) (z := ((((113:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (655352999265141893888, 655352999265207278140) (fT ((1021:ℝ)/(500:ℝ)) ((8:ℝ)/10) 0 / 6) := zwiden (655352999265141893888, 655352999265207278140) (zC_mem (lam := ((8:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((8:ℝ)/10) ((348:ℝ)/1000) = ((1021:ℝ)/(500:ℝ)) := by norm_num [theta13]
  have hzB : ((8:ℝ)/10) - ((348:ℝ)/1000) = (((113:ℝ)/(250:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_1 : sideCond ((8:ℝ)/10) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 61) (zofNatI 30)) ((61:ℝ)/(30:ℝ)) := zdiv_mem (zofNat_mem 61) (zofNat_mem 30) (by decide)
  have hθ1 : Real.pi / 2 < ((61:ℝ)/(30:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((61:ℝ)/(30:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 8) (zofNatI 10)) ((8:ℝ)/10) := zdiv_mem (zofNat_mem 8) (zofNat_mem 10) (by decide)
  have hS := zwiden (89492331580807011622, 89492331580807106786) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-44621996685837493875, -44621996685836420012) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-200556537644163943065, -200556537644158903247) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (19911225882307964512, 19911225882308922871) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-79866530464132896164, -79866530464130889185) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-60177548235384070976, -60177548235382154258) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (101384545087279129684, 101384545087281677427) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (275617941515981603640, 275617941515988705715) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5303527242442713629787, 5303527242446545835812) (FT ((61:ℝ)/(30:ℝ)) ((8:ℝ)/10) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5303527242442713629787, 5303527242446545835812) (zFT_mem (lam := ((8:ℝ)/10)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 2) (zofNatI 5)) (((2:ℝ)/(5:ℝ))) := zdiv_mem (zofNat_mem 2) (zofNat_mem 5) (by decide)
  have hWB := zwiden (-101384545087281677427, -101384545087279129684) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (36282108287278825312, 36282108287279829728) (zexp_mem hWB 18 18 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3229713857172638528996, 3229713857174029029460) (FT ((61:ℝ)/(30:ℝ)) ((8:ℝ)/10) ((((2:ℝ)/(5:ℝ))))) := zwiden (3229713857172638528996, 3229713857174029029460) (zFT_mem (lam := ((8:ℝ)/10)) (z := ((((2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (677642474620795898451, 677642474620858975880) (fT ((61:ℝ)/(30:ℝ)) ((8:ℝ)/10) 0 / 6) := zwiden (677642474620795898451, 677642474620858975880) (zC_mem (lam := ((8:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((8:ℝ)/10) ((4:ℝ)/10) = ((61:ℝ)/(30:ℝ)) := by norm_num [theta13]
  have hzB : ((8:ℝ)/10) - ((4:ℝ)/10) = (((2:ℝ)/(5:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_2 : sideCond ((8:ℝ)/10) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 152) (zofNatI 75)) ((152:ℝ)/(75:ℝ)) := zdiv_mem (zofNat_mem 152) (zofNat_mem 75) (by decide)
  have hθ1 : Real.pi / 2 < ((152:ℝ)/(75:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((152:ℝ)/(75:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 8) (zofNatI 10)) ((8:ℝ)/10) := zdiv_mem (zofNat_mem 8) (zofNat_mem 10) (by decide)
  have hS := zwiden (89787820644048139220, 89787820644048227829) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-44024393965076260173, -44024393965075260804) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-203950157077181546845, -203950157077176715832) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (19381472639921550437, 19381472639922430371) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-79057087785983728983, -79057087785981856340) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-61237054720156899126, -61237054720155139258) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (109307752702032937840, 109307752702035527123) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (298344158077877580688, 298344158077885615736) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5459997795290092560456, 5459997795293905112949) (FT ((152:ℝ)/(75:ℝ)) ((8:ℝ)/10) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5459997795290092560456, 5459997795293905112949) (zFT_mem (lam := ((8:ℝ)/10)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 9) (zofNatI 25)) (((9:ℝ)/(25:ℝ))) := zdiv_mem (zofNat_mem 9) (zofNat_mem 25) (by decide)
  have hWB := zwiden (-89433615847119976737, -89433615847117858232) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (40887893938747251895, 40887893938748286590) (zexp_mem hWB 17 17 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3336845500145280801412, 3336845500146700858397) (FT ((152:ℝ)/(75:ℝ)) ((8:ℝ)/10) ((((9:ℝ)/(25:ℝ))))) := zwiden (3336845500145280801412, 3336845500146700858397) (zFT_mem (lam := ((8:ℝ)/10)) (z := ((((9:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (695819873356814382931, 695819873356875800270) (fT ((152:ℝ)/(75:ℝ)) ((8:ℝ)/10) 0 / 6) := zwiden (695819873356814382931, 695819873356875800270) (zC_mem (lam := ((8:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((8:ℝ)/10) ((44:ℝ)/100) = ((152:ℝ)/(75:ℝ)) := by norm_num [theta13]
  have hzB : ((8:ℝ)/10) - ((44:ℝ)/100) = (((9:ℝ)/(25:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_3 : sideCond ((8:ℝ)/10) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 121) (zofNatI 60)) ((121:ℝ)/(60:ℝ)) := zdiv_mem (zofNat_mem 121) (zofNat_mem 60) (by decide)
  have hθ1 : Real.pi / 2 < ((121:ℝ)/(60:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((121:ℝ)/(60:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 8) (zofNatI 10)) ((8:ℝ)/10) := zdiv_mem (zofNat_mem 8) (zofNat_mem 10) (by decide)
  have hS := zwiden (90223567892715859448, 90223567892715938468) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-43124329521842911789, -43124329521842015525) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-209217323244454521303, -209217323244449989846) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (18597077967084147993, 18597077967084921010) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-77816617448836964304, -77816617448835278866) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-62805844065831704014, -62805844065830157980) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (120488747979436263569, 120488747979438873322) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (333638364637200943568, 333638364637209764211) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5699702563040770547878, 5699702563044512007495) (FT ((121:ℝ)/(60:ℝ)) ((8:ℝ)/10) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5699702563040770547878, 5699702563044512007495) (zFT_mem (lam := ((8:ℝ)/10)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 3) (zofNatI 10)) (((3:ℝ)/(10:ℝ))) := zdiv_mem (zofNat_mem 3) (zofNat_mem 10) (by decide)
  have hWB := zwiden (-72293248787663323994, -72293248787661758141) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (48532695173553043825, 48532695173553910206) (zexp_mem hWB 16 16 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3503955024296903168665, 3503955024298358197436) (FT ((121:ℝ)/(60:ℝ)) ((8:ℝ)/10) ((((3:ℝ)/(10:ℝ))))) := zwiden (3503955024296903168665, 3503955024298358197436) (zFT_mem (lam := ((8:ℝ)/10)) (z := ((((3:ℝ)/(10:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (724912877041924717257, 724912877041983743023) (fT ((121:ℝ)/(60:ℝ)) ((8:ℝ)/10) 0 / 6) := zwiden (724912877041924717257, 724912877041983743023) (zC_mem (lam := ((8:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((8:ℝ)/10) ((5:ℝ)/10) = ((121:ℝ)/(60:ℝ)) := by norm_num [theta13]
  have hzB : ((8:ℝ)/10) - ((5:ℝ)/10) = (((3:ℝ)/(10:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_4 : sideCond ((8:ℝ)/10) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 601) (zofNatI 300)) ((601:ℝ)/(300:ℝ)) := zdiv_mem (zofNat_mem 601) (zofNat_mem 300) (by decide)
  have hθ1 : Real.pi / 2 < ((601:ℝ)/(300:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((601:ℝ)/(300:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 8) (zofNatI 10)) ((8:ℝ)/10) := zdiv_mem (zofNat_mem 8) (zofNat_mem 10) (by decide)
  have hS := zwiden (90790522162497027964, 90790522162497097676) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-41917551043222170421, -41917551043221394056) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-216593097408964902427, -216593097408960724546) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (17570810854610709811, 17570810854611360678) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-76114326939745316015, -76114326939743847839) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-64858378290778580378, -64858378290777278644) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (134114769495562915761, 134114769495565503119) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (382342911852442654360, 382342911852452605236) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (6028462362285956116554, 6028462362289620314262) (FT ((601:ℝ)/(300:ℝ)) ((8:ℝ)/10) ((((-29:ℝ)/(50:ℝ))))) := zwiden (6028462362285956116554, 6028462362289620314262) (zFT_mem (lam := ((8:ℝ)/10)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 11) (zofNatI 50)) (((11:ℝ)/(50:ℝ))) := zdiv_mem (zofNat_mem 11) (zofNat_mem 50) (by decide)
  have hWB := zwiden (-50871119463835190838, -50871119463834209426) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (60126999966556247855, 60126999966557194622) (zexp_mem hWB 14 14 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3739155004089198892554, 3739155004090832190931) (FT ((601:ℝ)/(300:ℝ)) ((8:ℝ)/10) ((((11:ℝ)/(50:ℝ))))) := zwiden (3739155004089198892554, 3739155004090832190931) (zFT_mem (lam := ((8:ℝ)/10)) (z := ((((11:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (767475114356439122888, 767475114356495427497) (fT ((601:ℝ)/(300:ℝ)) ((8:ℝ)/10) 0 / 6) := zwiden (767475114356439122888, 767475114356495427497) (zC_mem (lam := ((8:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((8:ℝ)/10) ((58:ℝ)/100) = ((601:ℝ)/(300:ℝ)) := by norm_num [theta13]
  have hzB : ((8:ℝ)/10) - ((58:ℝ)/100) = (((11:ℝ)/(50:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_5 : sideCond ((825:ℝ)/1000) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 4109) (zofNatI 2000)) ((4109:ℝ)/(2000:ℝ)) := zdiv_mem (zofNat_mem 4109) (zofNat_mem 2000) (by decide)
  have hθ1 : Real.pi / 2 < ((4109:ℝ)/(2000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((4109:ℝ)/(2000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 825) (zofNatI 1000)) ((825:ℝ)/1000) := zdiv_mem (zofNat_mem 825) (zofNat_mem 1000) (by decide)
  have hS := zwiden (88527856399589361627, 88527856399589482079) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-46506114020563847915, -46506114020562499568) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-190357457861233537227, -190357457861227759208) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (21628186412935598984, 21628186412936853113) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-82341731674308227641, -82341731674305728279) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-56743627174128802032, -56743627174126293774) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (91052429916058841966, 91052429916061605731) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (248562540312060836873, 248562540312067935110) (zexp_mem hWA 17 17 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5057138231507430658470, 5057138231511820279877) (FT ((4109:ℝ)/(2000:ℝ)) ((825:ℝ)/1000) ((((-87:ℝ)/(250:ℝ))))) := zwiden (5057138231507430658470, 5057138231511820279877) (zFT_mem (lam := ((825:ℝ)/1000)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 477) (zofNatI 1000)) (((477:ℝ)/(1000:ℝ))) := zdiv_mem (zofNat_mem 477) (zofNat_mem 1000) (by decide)
  have hWB := zwiden (-124804623764256856131, -124804623764253067867) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (28706510632505513913, 28706510632506822899) (zexp_mem hWB 19 19 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3017564382342614348546, 3017564382344110555400) (FT ((4109:ℝ)/(2000:ℝ)) ((825:ℝ)/1000) ((((477:ℝ)/(1000:ℝ))))) := zwiden (3017564382342614348546, 3017564382344110555400) (zFT_mem (lam := ((825:ℝ)/1000)) (z := ((((477:ℝ)/(1000:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (645201159121589296670, 645201159121660460625) (fT ((4109:ℝ)/(2000:ℝ)) ((825:ℝ)/1000) 0 / 6) := zwiden (645201159121589296670, 645201159121660460625) (zC_mem (lam := ((825:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((825:ℝ)/1000) ((348:ℝ)/1000) = ((4109:ℝ)/(2000:ℝ)) := by norm_num [theta13]
  have hzB : ((825:ℝ)/1000) - ((348:ℝ)/1000) = (((477:ℝ)/(1000:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_6 : sideCond ((825:ℝ)/1000) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 491) (zofNatI 240)) ((491:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 491) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((491:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((491:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 825) (zofNatI 1000)) ((825:ℝ)/1000) := zdiv_mem (zofNat_mem 825) (zofNat_mem 1000) (by decide)
  have hS := zwiden (88927579650141191789, 88927579650141303014) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-45737135651107344553, -45737135651106114078) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-194431895185790158789, -194431895185784684765) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (20918855775676819017, 20918855775677944586) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-81345855471663315772, -81345855471661025565) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-58162288448646361966, -58162288448644110828) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (102032559109847656389, 102032559109850529256) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (277409783850232336494, 277409783850240395875) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5250422995304609619091, 5250422995308902124105) (FT ((491:ℝ)/(240:ℝ)) ((825:ℝ)/1000) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5250422995304609619091, 5250422995308902124105) (zFT_mem (lam := ((825:ℝ)/1000)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 17) (zofNatI 40)) (((17:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 17) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-108409594054216187334, -108409594054213134914) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (33820740732922780235, 33820740732924079871) (zexp_mem hWB 18 18 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3145421910650472356695, 3145421910651986336574) (FT ((491:ℝ)/(240:ℝ)) ((825:ℝ)/1000) ((((17:ℝ)/(40:ℝ))))) := zwiden (3145421910650472356695, 3145421910651986336574) (zFT_mem (lam := ((825:ℝ)/1000)) (z := ((((17:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (666134863046917062856, 666134863046985754479) (fT ((491:ℝ)/(240:ℝ)) ((825:ℝ)/1000) 0 / 6) := zwiden (666134863046917062856, 666134863046985754479) (zC_mem (lam := ((825:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((825:ℝ)/1000) ((4:ℝ)/10) = ((491:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((825:ℝ)/1000) - ((4:ℝ)/10) = (((17:ℝ)/(40:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_7 : sideCond ((825:ℝ)/1000) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2447) (zofNatI 1200)) ((2447:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2447) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2447:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2447:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 825) (zofNatI 1000)) ((825:ℝ)/1000) := zdiv_mem (zofNat_mem 825) (zofNat_mem 1000) (by decide)
  have hS := zwiden (89230515468078734807, 89230515468078845761) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-45143273134554183917, -45143273134553031194) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-197660712820092520058, -197660712820087227054) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (20379151093008574584, 20379151093009615339) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-80563150634250906181, -80563150634248748842) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-59241697813982850832, -59241697813980769322) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (110042662503745036683, 110042662503747984755) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (300544794982029717947, 300544794982038928044) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5401965745604499761117, 5401965745608807088083) (FT ((2447:ℝ)/(1200:ℝ)) ((825:ℝ)/1000) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5401965745604499761117, 5401965745608807088083) (zFT_mem (lam := ((825:ℝ)/1000)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 77) (zofNatI 200)) (((77:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 77) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-96287329690779486660, -96287329690776907098) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (38179430006737924940, 38179430006739500933) (zexp_mem hWB 17 17 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3247329339087773103207, 3247329339089352641204) (FT ((2447:ℝ)/(1200:ℝ)) ((825:ℝ)/1000) ((((77:ℝ)/(200:ℝ))))) := zwiden (3247329339087773103207, 3247329339089352641204) (zFT_mem (lam := ((825:ℝ)/1000)) (z := ((((77:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (683182246293689467007, 683182246293756884532) (fT ((2447:ℝ)/(1200:ℝ)) ((825:ℝ)/1000) 0 / 6) := zwiden (683182246293689467007, 683182246293756884532) (zC_mem (lam := ((825:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((825:ℝ)/1000) ((44:ℝ)/100) = ((2447:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((825:ℝ)/1000) - ((44:ℝ)/100) = (((77:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_8 : sideCond ((825:ℝ)/1000) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 487) (zofNatI 240)) ((487:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 487) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((487:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((487:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 825) (zofNatI 1000)) ((825:ℝ)/1000) := zdiv_mem (zofNat_mem 825) (zofNat_mem 1000) (by decide)
  have hS := zwiden (89677479186988897777, 89677479186988990214) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-44248725706704518049, -44248725706703489967) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-202666806229412480442, -202666806229407562744) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (19579497266670822676, 19579497266671732503) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-79362283572275582294, -79362283572273656573) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-60841005466658354648, -60841005466656534994) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (121361559169772180653, 121361559169775125777) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (336563142947772958742, 336563142947783001136) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5633821201944367216682, 5633821201948556481030) (FT ((487:ℝ)/(240:ℝ)) ((825:ℝ)/1000) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5633821201944367216682, 5633821201948556481030) (zFT_mem (lam := ((825:ℝ)/1000)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 13) (zofNatI 40)) (((13:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 13) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-78885013460353831756, -78885013460351917424) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (45436695585746744833, 45436695585748044547) (zexp_mem hWB 16 16 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3406138545236724300916, 3406138545238317105094) (FT ((487:ℝ)/(240:ℝ)) ((825:ℝ)/1000) ((((13:ℝ)/(40:ℝ))))) := zwiden (3406138545236724300916, 3406138545238317105094) (zFT_mem (lam := ((825:ℝ)/1000)) (z := ((((13:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (710421742504602419795, 710421742504666513412) (fT ((487:ℝ)/(240:ℝ)) ((825:ℝ)/1000) 0 / 6) := zwiden (710421742504602419795, 710421742504666513412) (zC_mem (lam := ((825:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((825:ℝ)/1000) ((5:ℝ)/10) = ((487:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((825:ℝ)/1000) - ((5:ℝ)/10) = (((13:ℝ)/(40:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_9 : sideCond ((825:ℝ)/1000) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2419) (zofNatI 1200)) ((2419:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2419) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2419:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2419:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 825) (zofNatI 1000)) ((825:ℝ)/1000) := zdiv_mem (zofNat_mem 825) (zofNat_mem 1000) (by decide)
  have hS := zwiden (90259473502198761663, 90259473502198848717) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-43049128250243109791, -43049128250242213164) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-209666205033294744054, -209666205033290174906) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (18532274431058021936, 18532274431058793917) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-77711833011911557144, -77711833011909863609) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-62935451137883956128, -62935451137882412166) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (135185536359268847793, 135185536359271795450) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (386458910104697259081, 386458910104708718904) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5951195987033256389257, 5951195987037392510865) (FT ((2419:ℝ)/(1200:ℝ)) ((825:ℝ)/1000) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5951195987033256389257, 5951195987037392510865) (zFT_mem (lam := ((825:ℝ)/1000)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 49) (zofNatI 200)) (((49:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 49) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-57104235186244120492, -57104235186242875360) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (56493626931949511735, 56493626931950283652) (zexp_mem hWB 15 15 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3629341234078461362259, 3629341234080115072681) (FT ((2419:ℝ)/(1200:ℝ)) ((825:ℝ)/1000) ((((49:ℝ)/(200:ℝ))))) := zwiden (3629341234078461362259, 3629341234080115072681) (zFT_mem (lam := ((825:ℝ)/1000)) (z := ((((49:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (750174691633966073372, 750174691634027583225) (fT ((2419:ℝ)/(1200:ℝ)) ((825:ℝ)/1000) 0 / 6) := zwiden (750174691633966073372, 750174691634027583225) (zC_mem (lam := ((825:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((825:ℝ)/1000) ((58:ℝ)/100) = ((2419:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((825:ℝ)/1000) - ((58:ℝ)/100) = (((49:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_10 : sideCond ((85:ℝ)/100) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2067) (zofNatI 1000)) ((2067:ℝ)/(1000:ℝ)) := zdiv_mem (zofNat_mem 2067) (zofNat_mem 1000) (by decide)
  have hθ1 : Real.pi / 2 < ((2067:ℝ)/(1000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2067:ℝ)/(1000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 85) (zofNatI 100)) ((85:ℝ)/100) := zdiv_mem (zofNat_mem 85) (zofNat_mem 100) (by decide)
  have hS := zwiden (87939628964196539377, 87939628964196677860) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-47609050165272627128, -47609050165271086292) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-184712000468232716626, -184712000468226447665) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (22666216576392988489, 22666216576394455645) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-83734444137438027073, -83734444137435185201) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-54667566847214023022, -54667566847211088710) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (91629576367735777883, 91629576367738887712) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (250001257953965369906, 250001257953973398984) (zexp_mem hWA 17 17 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5018658492991295383487, 5018658492996209224285) (FT ((2067:ℝ)/(1000:ℝ)) ((85:ℝ)/100) ((((-87:ℝ)/(250:ℝ))))) := zwiden (5018658492991295383487, 5018658492996209224285) (zFT_mem (lam := ((85:ℝ)/100)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 251) (zofNatI 500)) (((251:ℝ)/(500:ℝ))) := zdiv_mem (zofNat_mem 251) (zofNat_mem 500) (by decide)
  have hWB := zwiden (-132178296944267016182, -132178296944262530165) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (26665943224203961744, 26665943224205201574) (zexp_mem hWB 20 20 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2945852775226331810455, 2945852775227924276800) (FT ((2067:ℝ)/(1000:ℝ)) ((85:ℝ)/100) ((((251:ℝ)/(500:ℝ))))) := zwiden (2945852775226331810455, 2945852775227924276800) (zFT_mem (lam := ((85:ℝ)/100)) (z := ((((251:ℝ)/(500:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (635957324990999897105, 635957324991077425626) (fT ((2067:ℝ)/(1000:ℝ)) ((85:ℝ)/100) 0 / 6) := zwiden (635957324990999897105, 635957324991077425626) (zC_mem (lam := ((85:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((85:ℝ)/100) ((348:ℝ)/1000) = ((2067:ℝ)/(1000:ℝ)) := by norm_num [theta13]
  have hzB : ((85:ℝ)/100) - ((348:ℝ)/1000) = (((251:ℝ)/(500:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_11 : sideCond ((85:ℝ)/100) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 247) (zofNatI 120)) ((247:ℝ)/(120:ℝ)) := zdiv_mem (zofNat_mem 247) (zofNat_mem 120) (by decide)
  have hθ1 : Real.pi / 2 < ((247:ℝ)/(120:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((247:ℝ)/(120:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 85) (zofNatI 100)) ((85:ℝ)/100) := zdiv_mem (zofNat_mem 85) (zofNat_mem 100) (by decide)
  have hS := zwiden (88348932966077720264, 88348932966077846975) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-46845128281983664770, -46845128281982259023) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-188597910190927857746, -188597910190921927735) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (21944660437553741148, 21944660437555058197) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-82774341967445845917, -82774341967443243275) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-56110679124892517704, -56110679124889883606) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (102718789407560055767, 102718789407563285643) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (279320000582621606808, 279320000582630729771) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5206548657446189391118, 5206548657450989886985) (FT ((247:ℝ)/(120:ℝ)) ((85:ℝ)/100) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5206548657446189391118, 5206548657450989886985) (zFT_mem (lam := ((85:ℝ)/100)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 9) (zofNatI 20)) (((9:ℝ)/(20:ℝ))) := zdiv_mem (zofNat_mem 9) (zofNat_mem 20) (by decide)
  have hWB := zwiden (-115558638083508696348, -115558638083505062738) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (31487284735632077509, 31487284735633272968) (zexp_mem hWB 19 19 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3067822138535771828111, 3067822138537372669240) (FT ((247:ℝ)/(120:ℝ)) ((85:ℝ)/100) ((((9:ℝ)/(20:ℝ))))) := zwiden (3067822138535771828111, 3067822138537372669240) (zFT_mem (lam := ((85:ℝ)/100)) (z := ((((9:ℝ)/(20:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (655642772326566618479, 655642772326641265488) (fT ((247:ℝ)/(120:ℝ)) ((85:ℝ)/100) 0 / 6) := zwiden (655642772326566618479, 655642772326641265488) (zC_mem (lam := ((85:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((85:ℝ)/100) ((4:ℝ)/10) = ((247:ℝ)/(120:ℝ)) := by norm_num [theta13]
  have hzB : ((85:ℝ)/100) - ((4:ℝ)/10) = (((9:ℝ)/(20:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_12 : sideCond ((85:ℝ)/100) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 1231) (zofNatI 600)) ((1231:ℝ)/(600:ℝ)) := zdiv_mem (zofNat_mem 1231) (zofNat_mem 600) (by decide)
  have hθ1 : Real.pi / 2 < ((1231:ℝ)/(600:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1231:ℝ)/(600:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 85) (zofNatI 100)) ((85:ℝ)/100) := zdiv_mem (zofNat_mem 85) (zofNat_mem 100) (by decide)
  have hS := zwiden (88659268205606453312, 88659268205606574873) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-46255098759448572125, -46255098759447259386) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-191674584172190486848, -191674584172184784236) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (21395341612462193942, 21395341612463408360) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-82018864135815418292, -82018864135812978105) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-57209316775075612116, -57209316775073183280) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (110816905670935866867, 110816905670939164507) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (302880773931000619147, 302880773931011003937) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5353706780378491177914, 5353706780383283501641) (FT ((1231:ℝ)/(600:ℝ)) ((85:ℝ)/100) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5353706780378491177914, 5353706780383283501641) (zFT_mem (lam := ((85:ℝ)/100)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 41) (zofNatI 100)) (((41:ℝ)/(100:ℝ))) := zdiv_mem (zofNat_mem 41) (zofNat_mem 100) (by decide)
  have hWB := zwiden (-103261207557011494200, -103261207557008421398) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (35607564826766215994, 35607564826767421490) (zexp_mem hWB 18 18 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3164961429429178052892, 3164961429430798814250) (FT ((1231:ℝ)/(600:ℝ)) ((85:ℝ)/100) ((((41:ℝ)/(100:ℝ))))) := zwiden (3164961429429178052892, 3164961429430798814250) (zFT_mem (lam := ((85:ℝ)/100)) (z := ((((41:ℝ)/(100:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (671652511948070191500, 671652511948142995469) (fT ((1231:ℝ)/(600:ℝ)) ((85:ℝ)/100) 0 / 6) := zwiden (671652511948070191500, 671652511948142995469) (zC_mem (lam := ((85:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((85:ℝ)/100) ((44:ℝ)/100) = ((1231:ℝ)/(600:ℝ)) := by norm_num [theta13]
  have hzB : ((85:ℝ)/100) - ((44:ℝ)/100) = (((41:ℝ)/(100:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_13 : sideCond ((85:ℝ)/100) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 49) (zofNatI 24)) ((49:ℝ)/(24:ℝ)) := zdiv_mem (zofNat_mem 49) (zofNat_mem 24) (by decide)
  have hθ1 : Real.pi / 2 < ((49:ℝ)/(24:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((49:ℝ)/(24:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 85) (zofNatI 100)) ((85:ℝ)/100) := zdiv_mem (zofNat_mem 85) (zofNat_mem 100) (by decide)
  have hS := zwiden (89117378557587318798, 89117378557587423279) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-45366208118198244459, -45366208118197069555) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-196439998523573100028, -196439998523567782274) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (20580928390235696988, 20580928390236763007) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-80858350851835374380, -80858350851833185493) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-58838143219528606024, -58838143219526473986) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (122274526693477170073, 122274526693480480156) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (339649924355046090259, 339649924355057483065) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5578580252277284726849, 5578580252281963922909) (FT ((49:ℝ)/(24:ℝ)) ((85:ℝ)/100) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5578580252277284726849, 5578580252281963922909) (zFT_mem (lam := ((85:ℝ)/100)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 7) (zofNatI 20)) (((7:ℝ)/(20:ℝ))) := zdiv_mem (zofNat_mem 7) (zofNat_mem 20) (by decide)
  have hWB := zwiden (-85592168685436336110, -85592168685434019051) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (42489139374063756443, 42489139374064820827) (zexp_mem hWB 17 17 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3316207337189226340597, 3316207337190866663182) (FT ((49:ℝ)/(24:ℝ)) ((85:ℝ)/100) ((((7:ℝ)/(20:ℝ))))) := zwiden (3316207337189226340597, 3316207337190866663182) (zFT_mem (lam := ((85:ℝ)/100)) (z := ((((7:ℝ)/(20:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (697195050130556318855, 697195050130625707726) (fT ((49:ℝ)/(24:ℝ)) ((85:ℝ)/100) 0 / 6) := zwiden (697195050130556318855, 697195050130625707726) (zC_mem (lam := ((85:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((85:ℝ)/100) ((5:ℝ)/10) = ((49:ℝ)/(24:ℝ)) := by norm_num [theta13]
  have hzB : ((85:ℝ)/100) - ((5:ℝ)/10) = (((7:ℝ)/(20:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_14 : sideCond ((85:ℝ)/100) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 1217) (zofNatI 600)) ((1217:ℝ)/(600:ℝ)) := zdiv_mem (zofNat_mem 1217) (zofNat_mem 600) (by decide)
  have hθ1 : Real.pi / 2 < ((1217:ℝ)/(600:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1217:ℝ)/(600:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 85) (zofNatI 100)) ((85:ℝ)/100) := zdiv_mem (zofNat_mem 85) (zofNat_mem 100) (by decide)
  have hS := zwiden (89714321982798195464, 89714321982798289870) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-44173979118558161852, -44173979118557140276) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-203093141647975313784, -203093141647970403296) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (19513404311667222637, 19513404311668125180) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-79260771718074702481, -79260771718072786074) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-60973191376665554726, -60973191376663749640) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (136296007285686925273, 136296007285690221529) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (390774340397141816697, 390774340397154778102) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5885833799625875087138, 5885833799630469542883) (FT ((1217:ℝ)/(600:ℝ)) ((85:ℝ)/100) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5885833799625875087138, 5885833799630469542883) (zFT_mem (lam := ((85:ℝ)/100)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 27) (zofNatI 100)) (((27:ℝ)/(100:ℝ))) := zdiv_mem (zofNat_mem 27) (zofNat_mem 100) (by decide)
  have hWB := zwiden (-63448141322648896230, -63448141322647361764) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (53021037712331211391, 53021037712332357538) (zexp_mem hWB 15 15 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3528504263128051570010, 3528504263129824845326) (FT ((1217:ℝ)/(600:ℝ)) ((85:ℝ)/100) ((((27:ℝ)/(100:ℝ))))) := zwiden (3528504263128051570010, 3528504263129824845326) (zFT_mem (lam := ((85:ℝ)/100)) (z := ((((27:ℝ)/(100:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (734386882961821396436, 734386882961887467042) (fT ((1217:ℝ)/(600:ℝ)) ((85:ℝ)/100) 0 / 6) := zwiden (734386882961821396436, 734386882961887467042) (zC_mem (lam := ((85:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((85:ℝ)/100) ((58:ℝ)/100) = ((1217:ℝ)/(600:ℝ)) := by norm_num [theta13]
  have hzB : ((85:ℝ)/100) - ((58:ℝ)/100) = (((27:ℝ)/(100:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_15 : sideCond ((875:ℝ)/1000) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 4159) (zofNatI 2000)) ((4159:ℝ)/(2000:ℝ)) := zdiv_mem (zofNat_mem 4159) (zofNat_mem 2000) (by decide)
  have hθ1 : Real.pi / 2 < ((4159:ℝ)/(2000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((4159:ℝ)/(2000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 875) (zofNatI 1000)) ((875:ℝ)/1000) := zdiv_mem (zofNat_mem 875) (zofNat_mem 1000) (by decide)
  have hS := zwiden (87337661140690762712, 87337661140690921795) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-48704547492753438659, -48704547492751679268) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-179321368612835813193, -179321368612829008802) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (23721329464737038872, 23721329464738752680) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-85074825298655749291, -85074825298652521107) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-52557341070525922256, -52557341070522494640) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (92241863146660946982, 92241863146664447124) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (251536678394900803783, 251536678394909892893) (zexp_mem hWA 17 17 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (4988245583063802762327, 4988245583069310452982) (FT ((4159:ℝ)/(2000:ℝ)) ((875:ℝ)/1000) ((((-87:ℝ)/(250:ℝ))))) := zwiden (4988245583063802762327, 4988245583069310452982) (zFT_mem (lam := ((875:ℝ)/1000)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 527) (zofNatI 1000)) (((527:ℝ)/(1000:ℝ))) := zdiv_mem (zofNat_mem 527) (zofNat_mem 1000) (by decide)
  have hWB := zwiden (-139688108845667136880, -139688108845661836378) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (24736727870635535296, 24736727870636978054) (zexp_mem hWB 20 20 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2879743639305456204368, 2879743639307178954144) (FT ((4159:ℝ)/(2000:ℝ)) ((875:ℝ)/1000) ((((527:ℝ)/(1000:ℝ))))) := zwiden (2879743639305456204368, 2879743639307178954144) (zFT_mem (lam := ((875:ℝ)/1000)) (z := ((((527:ℝ)/(1000:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (627560755215537522411, 627560755215622060025) (fT ((4159:ℝ)/(2000:ℝ)) ((875:ℝ)/1000) 0 / 6) := zwiden (627560755215537522411, 627560755215622060025) (zC_mem (lam := ((875:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((875:ℝ)/1000) ((348:ℝ)/1000) = ((4159:ℝ)/(2000:ℝ)) := by norm_num [theta13]
  have hzB : ((875:ℝ)/1000) - ((348:ℝ)/1000) = (((527:ℝ)/(1000:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_16 : sideCond ((875:ℝ)/1000) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 497) (zofNatI 240)) ((497:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 497) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((497:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((497:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 875) (zofNatI 1000)) ((875:ℝ)/1000) := zdiv_mem (zofNat_mem 875) (zofNat_mem 1000) (by decide)
  have hS := zwiden (87756481940983726308, 87756481940983872825) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-47945801456872086968, -47945801456870480083) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-183032672881534759474, -183032672881528319613) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (22987998773416434503, 22987998773417975372) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-84151097193919871201, -84151097193916910411) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-54024002453167130994, -54024002453164049256) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (103442369251678133207, 103442369251681772998) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (281348433623568477116, 281348433623578832525) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5171344331366495659290, 5171344331371882443799) (FT ((497:ℝ)/(240:ℝ)) ((875:ℝ)/1000) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5171344331366495659290, 5171344331371882443799) (zFT_mem (lam := ((875:ℝ)/1000)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 19) (zofNatI 40)) (((19:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 19) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-122837813486372105435, -122837813486367783183) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (29276702146010508972, 29276702146011938192) (zexp_mem hWB 19 19 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2996317023050743036125, 2996317023052477395902) (FT ((497:ℝ)/(240:ℝ)) ((875:ℝ)/1000) ((((19:ℝ)/(40:ℝ))))) := zwiden (2996317023050743036125, 2996317023052477395902) (zFT_mem (lam := ((875:ℝ)/1000)) (z := ((((19:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (646093742730647108794, 646093742730728471855) (fT ((497:ℝ)/(240:ℝ)) ((875:ℝ)/1000) 0 / 6) := zwiden (646093742730647108794, 646093742730728471855) (zC_mem (lam := ((875:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((875:ℝ)/1000) ((4:ℝ)/10) = ((497:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((875:ℝ)/1000) - ((4:ℝ)/10) = (((19:ℝ)/(40:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_17 : sideCond ((875:ℝ)/1000) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2477) (zofNatI 1200)) ((2477:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2477) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2477:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2477:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 875) (zofNatI 1000)) ((875:ℝ)/1000) := zdiv_mem (zofNat_mem 875) (zofNat_mem 1000) (by decide)
  have hS := zwiden (88074168112853843829, 88074168112853987928) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-47359697119267551604, -47359697119266046967) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-185968605101203633175, -185968605101197420609) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (22429409112286167077, 22429409112287592261) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-83423318517124341278, -83423318517121554395) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-55141181775427665846, -55141181775424815478) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (111629697046561792644, 111629697046565523149) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (305352594504189195611, 305352594504201039463) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5314607864182821942183, 5314607864188217345189) (FT ((2477:ℝ)/(1200:ℝ)) ((875:ℝ)/1000) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5314607864182821942183, 5314607864188217345189) (zFT_mem (lam := ((875:ℝ)/1000)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 87) (zofNatI 200)) (((87:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 87) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-110361177761945460386, -110361177761941772272) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (33167099589753113175, 33167099589754704911) (zexp_mem hWB 18 18 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3089092782721885112128, 3089092782723659705982) (FT ((2477:ℝ)/(1200:ℝ)) ((875:ℝ)/1000) ((((87:ℝ)/(200:ℝ))))) := zwiden (3089092782721885112128, 3089092782723659705982) (zFT_mem (lam := ((875:ℝ)/1000)) (z := ((((87:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (661147930057778301300, 661147930057857851008) (fT ((2477:ℝ)/(1200:ℝ)) ((875:ℝ)/1000) 0 / 6) := zwiden (661147930057778301300, 661147930057857851008) (zC_mem (lam := ((875:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((875:ℝ)/1000) ((44:ℝ)/100) = ((2477:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((875:ℝ)/1000) - ((44:ℝ)/100) = (((87:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_18 : sideCond ((875:ℝ)/1000) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 493) (zofNatI 240)) ((493:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 493) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((493:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((493:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 875) (zofNatI 1000)) ((875:ℝ)/1000) := zdiv_mem (zofNat_mem 875) (zofNat_mem 1000) (by decide)
  have hS := zwiden (88543353519094941642, 88543353519095063602) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-46476602151970810009, -46476602151969464574) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-190511675594475452940, -190511675594469675470) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (21600745475924526654, 21600745475925777280) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-82303884294165716529, -82303884294163220575) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-56798509048150946692, -56798509048148445440) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (123227043187432076481, 123227043187435813774) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (342900602953673979795, 342900602953686968951) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5533279741933585791585, 5533279741938841745046) (FT ((493:ℝ)/(240:ℝ)) ((875:ℝ)/1000) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5533279741933585791585, 5533279741938841745046) (zFT_mem (lam := ((875:ℝ)/1000)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 3) (zofNatI 8)) (((3:ℝ)/(8:ℝ))) := zdiv_mem (zofNat_mem 3) (zofNat_mem 8) (by decide)
  have hWB := zwiden (-92420282390576860331, -92420282390574057361) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (39684765047219856214, 39684765047221263052) (zexp_mem hWB 17 17 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3233427994776101622840, 3233427994777882561230) (FT ((493:ℝ)/(240:ℝ)) ((875:ℝ)/1000) ((((3:ℝ)/(8:ℝ))))) := zwiden (3233427994776101622840, 3233427994777882561230) (zFT_mem (lam := ((875:ℝ)/1000)) (z := ((((3:ℝ)/(8:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (685132223581209085267, 685132223581284609433) (fT ((493:ℝ)/(240:ℝ)) ((875:ℝ)/1000) 0 / 6) := zwiden (685132223581209085267, 685132223581284609433) (zC_mem (lam := ((875:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((875:ℝ)/1000) ((5:ℝ)/10) = ((493:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((875:ℝ)/1000) - ((5:ℝ)/10) = (((3:ℝ)/(8:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_19 : sideCond ((875:ℝ)/1000) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2449) (zofNatI 1200)) ((2449:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2449) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2449:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2449:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 875) (zofNatI 1000)) ((875:ℝ)/1000) := zdiv_mem (zofNat_mem 875) (zofNat_mem 1000) (by decide)
  have hS := zwiden (89155152783111116489, 89155152783111229387) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-45291927892507667423, -45291927892506493941) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-196845568143417149534, -196845568143411800134) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (20513587322200077377, 20513587322201140363) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-80760175021963561670, -80760175021961366962) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-58972825355599845246, -58972825355597719274) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (137445914087874949243, 137445914087878686076) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (395293816198196675116, 395293816198211541792) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5831544686113648886865, 5831544686118826281394) (FT ((2449:ℝ)/(1200:ℝ)) ((875:ℝ)/1000) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5831544686113648886865, 5831544686118826281394) (zFT_mem (lam := ((875:ℝ)/1000)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 59) (zofNatI 200)) (((59:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 59) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-69907835613662435159, -69907835613660534529) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (49704318956068390198, 49704318956069397122) (zexp_mem hWB 16 16 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3435782942430401481203, 3435782942432236170362) (FT ((2449:ℝ)/(1200:ℝ)) ((875:ℝ)/1000) ((((59:ℝ)/(200:ℝ))))) := zwiden (3435782942430401481203, 3435782942432236170362) (zFT_mem (lam := ((875:ℝ)/1000)) (z := ((((59:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (719981879105517542549, 719981879105589537384) (fT ((2449:ℝ)/(1200:ℝ)) ((875:ℝ)/1000) 0 / 6) := zwiden (719981879105517542549, 719981879105589537384) (zC_mem (lam := ((875:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((875:ℝ)/1000) ((58:ℝ)/100) = ((2449:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((875:ℝ)/1000) - ((58:ℝ)/100) = (((59:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_20 : sideCond ((9:ℝ)/10) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 523) (zofNatI 250)) ((523:ℝ)/(250:ℝ)) := zdiv_mem (zofNat_mem 523) (zofNat_mem 250) (by decide)
  have hθ1 : Real.pi / 2 < ((523:ℝ)/(250:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((523:ℝ)/(250:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 9) (zofNatI 10)) ((9:ℝ)/10) := zdiv_mem (zofNat_mem 9) (zofNat_mem 10) (by decide)
  have hS := zwiden (86722046985319753454, 86722046985319754797) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-49792434833777655008, -49792434833777639082) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-174167114492039693276, -174167114492039634870) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (24792865666759928245, 24792865666759944106) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-86362037463366756651, -86362037463366727690) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-50414268666480143510, -50414268666480111788) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (92888564988385076573, 92888564988385107725) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (253168642008358830728, 253168642008359230499) (zexp_mem hWA 17 17 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (4965478601713197450894, 4965478601713269810946) (FT ((523:ℝ)/(250:ℝ)) ((9:ℝ)/10) ((((-87:ℝ)/(250:ℝ))))) := zwiden (4965478601713197450894, 4965478601713269810946) (zFT_mem (lam := ((9:ℝ)/10)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 69) (zofNatI 125)) (((69:ℝ)/(125:ℝ))) := zdiv_mem (zofNat_mem 69) (zofNat_mem 125) (by decide)
  have hWB := zwiden (-147340482395369481219, -147340482395369431805) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (22914396061898308457, 22914396061898702082) (zexp_mem hWB 20 20 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2818764682852772624483, 2818764682852817796953) (FT ((523:ℝ)/(250:ℝ)) ((9:ℝ)/10) ((((69:ℝ)/(125:ℝ))))) := zwiden (2818764682852772624483, 2818764682852817796953) (zFT_mem (lam := ((9:ℝ)/10)) (z := ((((69:ℝ)/(125:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (619957282287948408760, 619957282287949138137) (fT ((523:ℝ)/(250:ℝ)) ((9:ℝ)/10) 0 / 6) := zwiden (619957282287948408760, 619957282287949138137) (zC_mem (lam := ((9:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((9:ℝ)/10) ((348:ℝ)/1000) = ((523:ℝ)/(250:ℝ)) := by norm_num [theta13]
  have hzB : ((9:ℝ)/10) - ((348:ℝ)/1000) = (((69:ℝ)/(125:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_21 : sideCond ((9:ℝ)/10) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 25) (zofNatI 12)) ((25:ℝ)/(12:ℝ)) := zdiv_mem (zofNat_mem 25) (zofNat_mem 12) (by decide)
  have hθ1 : Real.pi / 2 < ((25:ℝ)/(12:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((25:ℝ)/(12:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 9) (zofNatI 10)) ((9:ℝ)/10) := zdiv_mem (zofNat_mem 9) (zofNat_mem 10) (by decide)
  have hS := zwiden (87150319144126544669, 87150319144126710736) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-49038983197828346530, -49038983197826514290) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-177716407358114536630, -177716407358107557980) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (24048218730767111815, 24048218730768908840) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-85475260723884157070, -85475260723880800588) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-51903562538465776370, -51903562538462182320) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (104202638314660722247, 104202638314664814141) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (283495590465906841911, 283495590465918573347) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5144334388692862403052, 5144334388698900288706) (FT ((25:ℝ)/(12:ℝ)) ((9:ℝ)/10) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5144334388692862403052, 5144334388698900288706) (zFT_mem (lam := ((9:ℝ)/10)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI zoneI (zofNatI 2)) (((1:ℝ)/(2:ℝ))) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hWB := zwiden (-130253297893331017676, -130253297893325902809) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (27184234928546579360, 27184234928548468653) (zexp_mem hWB 19 19 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2930380845495732570495, 2930380845497626209766) (FT ((25:ℝ)/(12:ℝ)) ((9:ℝ)/10) ((((1:ℝ)/(2:ℝ))))) := zwiden (2930380845495732570495, 2930380845497626209766) (zFT_mem (lam := ((9:ℝ)/10)) (z := ((((1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (637423356225854068278, 637423356225942606652) (fT ((25:ℝ)/(12:ℝ)) ((9:ℝ)/10) 0 / 6) := zwiden (637423356225854068278, 637423356225942606652) (zC_mem (lam := ((9:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((9:ℝ)/10) ((4:ℝ)/10) = ((25:ℝ)/(12:ℝ)) := by norm_num [theta13]
  have hzB : ((9:ℝ)/10) - ((4:ℝ)/10) = (((1:ℝ)/(2:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_22 : sideCond ((9:ℝ)/10) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 623) (zofNatI 300)) ((623:ℝ)/(300:ℝ)) := zdiv_mem (zofNat_mem 623) (zofNat_mem 300) (by decide)
  have hθ1 : Real.pi / 2 < ((623:ℝ)/(300:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((623:ℝ)/(300:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 9) (zofNatI 10)) ((9:ℝ)/10) := zdiv_mem (zofNat_mem 9) (zofNat_mem 10) (by decide)
  have hS := zwiden (87475306610520028054, 87475306610520184754) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-48456895622764687418, -48456895622762977568) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-180521895772101475924, -180521895772094782646) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (23480707333953458156, 23480707333955115237) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-84775636039906289322, -84775636039903146065) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-53038585332093083688, -53038585332089769526) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (112480456170365699645, 112480456170369870466) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (307961491540705362579, 307961491540718726049) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5284147876105853131493, 5284147876111868296142) (FT ((623:ℝ)/(300:ℝ)) ((9:ℝ)/10) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5284147876105853131493, 5284147876111868296142) (zFT_mem (lam := ((9:ℝ)/10)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 23) (zofNatI 50)) (((23:ℝ)/(50:ℝ))) := zdiv_mem (zofNat_mem 23) (zofNat_mem 50) (by decide)
  have hWB := zwiden (-117593204178113955487, -117593204178109595084) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (30853128159029225053, 30853128159030641880) (zexp_mem hWB 19 19 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3019153197914666928384, 3019153197916529957610) (FT ((623:ℝ)/(300:ℝ)) ((9:ℝ)/10) ((((23:ℝ)/(50:ℝ))))) := zwiden (3019153197914666928384, 3019153197916529957610) (zFT_mem (lam := ((9:ℝ)/10)) (z := ((((23:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (651595124181633336424, 651595124181719335202) (fT ((623:ℝ)/(300:ℝ)) ((9:ℝ)/10) 0 / 6) := zwiden (651595124181633336424, 651595124181719335202) (zC_mem (lam := ((9:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((9:ℝ)/10) ((44:ℝ)/100) = ((623:ℝ)/(300:ℝ)) := by norm_num [theta13]
  have hzB : ((9:ℝ)/10) - ((44:ℝ)/100) = (((23:ℝ)/(50:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_23 : sideCond ((9:ℝ)/10) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 31) (zofNatI 15)) ((31:ℝ)/(15:ℝ)) := zdiv_mem (zofNat_mem 31) (zofNat_mem 15) (by decide)
  have hθ1 : Real.pi / 2 < ((31:ℝ)/(15:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((31:ℝ)/(15:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 9) (zofNatI 10)) ((9:ℝ)/10) := zdiv_mem (zofNat_mem 9) (zofNat_mem 10) (by decide)
  have hS := zwiden (87955493761756183283, 87955493761756321379) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-47579734311213525281, -47579734311211989780) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-184859152820090321643, -184859152820084065596) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (22638311171255234795, 22638311171256695970) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-83697980487919288510, -83697980487916455982) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-54723377657489530410, -54723377657486608060) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (124218696302860960626, 124218696302865164487) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (346317903344538746578, 346317903344553507865) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5497324241266720045458, 5497324241272610678628) (FT ((31:ℝ)/(15:ℝ)) ((9:ℝ)/10) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5497324241266720045458, 5497324241272610678628) (zFT_mem (lam := ((9:ℝ)/10)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 2) (zofNatI 5)) (((2:ℝ)/(5:ℝ))) := zdiv_mem (zofNat_mem 2) (zofNat_mem 5) (by decide)
  have hWB := zwiden (-99374957042292131590, -99374957042288768500) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (37018604683997641276, 37018604683998942076) (zexp_mem hWB 18 18 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3157157533441256214848, 3157157533443127618629) (FT ((31:ℝ)/(15:ℝ)) ((9:ℝ)/10) ((((2:ℝ)/(5:ℝ))))) := zwiden (3157157533441256214848, 3157157533443127618629) (zFT_mem (lam := ((9:ℝ)/10)) (z := ((((2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (674144410430459458325, 674144410430541433119) (fT ((31:ℝ)/(15:ℝ)) ((9:ℝ)/10) 0 / 6) := zwiden (674144410430459458325, 674144410430541433119) (zC_mem (lam := ((9:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((9:ℝ)/10) ((5:ℝ)/10) = ((31:ℝ)/(15:ℝ)) := by norm_num [theta13]
  have hzB : ((9:ℝ)/10) - ((5:ℝ)/10) = (((2:ℝ)/(5:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_24 : sideCond ((9:ℝ)/10) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 154) (zofNatI 75)) ((154:ℝ)/(75:ℝ)) := zdiv_mem (zofNat_mem 154) (zofNat_mem 75) (by decide)
  have hθ1 : Real.pi / 2 < ((154:ℝ)/(75:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((154:ℝ)/(75:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 9) (zofNatI 10)) ((9:ℝ)/10) := zdiv_mem (zofNat_mem 9) (zofNat_mem 10) (by decide)
  have hS := zwiden (88582053272187361733, 88582053272187481236) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-46402799894870144444, -46402799894868812247) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-190898078290277522780, -190898078290271784673) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (21532198380832370529, 21532198380833606883) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-82209105845320855779, -82209105845318384698) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-56935603238335258942, -56935603238332786234) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (138635157683161770940, 138635157683165938212) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (400022886939430770176, 400022886939447553325) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5787621402781927180013, 5787621402787679953836) (FT ((154:ℝ)/(75:ℝ)) ((9:ℝ)/10) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5787621402781927180013, 5787621402787679953836) (zFT_mem (lam := ((9:ℝ)/10)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 8) (zofNatI 25)) (((8:ℝ)/(25:ℝ))) := zdiv_mem (zofNat_mem 8) (zofNat_mem 25) (by decide)
  have hWB := zwiden (-76488362859677759014, -76488362859675459829) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (46538808568779481915, 46538808568780814348) (zexp_mem hWB 16 16 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3350424531387254564535, 3350424531389213279834) (FT ((154:ℝ)/(75:ℝ)) ((9:ℝ)/10) ((((8:ℝ)/(25:ℝ))))) := zwiden (3350424531387254564535, 3350424531389213279834) (zFT_mem (lam := ((9:ℝ)/10)) (z := ((((8:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (706845615777977327516, 706845615778054615976) (fT ((154:ℝ)/(75:ℝ)) ((9:ℝ)/10) 0 / 6) := zwiden (706845615777977327516, 706845615778054615976) (zC_mem (lam := ((9:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((9:ℝ)/10) ((58:ℝ)/100) = ((154:ℝ)/(75:ℝ)) := by norm_num [theta13]
  have hzB : ((9:ℝ)/10) - ((58:ℝ)/100) = (((8:ℝ)/(25:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_25 : sideCond ((925:ℝ)/1000) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 4209) (zofNatI 2000)) ((4209:ℝ)/(2000:ℝ)) := zdiv_mem (zofNat_mem 4209) (zofNat_mem 2000) (by decide)
  have hθ1 : Real.pi / 2 < ((4209:ℝ)/(2000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((4209:ℝ)/(2000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 925) (zofNatI 1000)) ((925:ℝ)/1000) := zdiv_mem (zofNat_mem 925) (zofNat_mem 1000) (by decide)
  have hS := zwiden (86092882686542825860, 86092882686542827416) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-50872542208161527413, -50872542208161509041) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-169232515124300000864, -169232515124299936688) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (25880155507211742662, 25880155507211761356) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-87595276165868975639, -87595276165868942421) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-48239688985576514676, -48239688985576477288) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (93569137874656632159, 93569137874656667644) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (254897515591681731893, 254897515591682185649) (zexp_mem hWA 17 17 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (4950002939995339142287, 4950002939995421101916) (FT ((4209:ℝ)/(2000:ℝ)) ((925:ℝ)/1000) ((((-87:ℝ)/(250:ℝ))))) := zwiden (4950002939995339142287, 4950002939995421101916) (zFT_mem (lam := ((925:ℝ)/1000)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 577) (zofNatI 1000)) (((577:ℝ)/(1000:ℝ))) := zdiv_mem (zofNat_mem 577) (zofNat_mem 1000) (by decide)
  have hWB := zwiden (-155141932625508325376, -155141932625508266540) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (21194693838918843913, 21194693838918935664) (zexp_mem hWB 21 21 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2762498477878143666558, 2762498477878165733202) (FT ((4209:ℝ)/(2000:ℝ)) ((925:ℝ)/1000) ((((577:ℝ)/(1000:ℝ))))) := zwiden (2762498477878143666558, 2762498477878165733202) (zFT_mem (lam := ((925:ℝ)/1000)) (z := ((((577:ℝ)/(1000:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (613098583730717926462, 613098583730718732346) (fT ((4209:ℝ)/(2000:ℝ)) ((925:ℝ)/1000) 0 / 6) := zwiden (613098583730717926462, 613098583730718732346) (zC_mem (lam := ((925:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((925:ℝ)/1000) ((348:ℝ)/1000) = ((4209:ℝ)/(2000:ℝ)) := by norm_num [theta13]
  have hzB : ((925:ℝ)/1000) - ((348:ℝ)/1000) = (((577:ℝ)/(1000:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

end Work.LinnikAreas2
