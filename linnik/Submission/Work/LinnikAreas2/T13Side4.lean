import Mathlib
import Submission.Work.LinnikAreas2.T13SideDefs
import Submission.Work.LinnikAreas.Density4.T13.Basic
import Submission.Work.LinnikAreas.Density4.T13.Num4

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

theorem side_78 : sideCond ((1175:ℝ)/1000) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 529) (zofNatI 240)) ((529:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 529) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((529:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((529:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1175) (zofNatI 1000)) ((1175:ℝ)/1000) := zdiv_mem (zofNat_mem 1175) (zofNat_mem 1000) (by decide)
  have hS := zwiden (80603730473838584233, 80603730473838591587) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-59186473401452049094, -59186473401451990970) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-136186067257491273654, -136186067257491127486) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (35030386337007840098, 35030386337007908902) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-95413010994953155414, -95413010994953053007) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-29939227325984319804, -29939227325984182196) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (137744378892731917755, 137744378892732065931) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (396475391531445761044, 396475391531446447956) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5622412761110743300396, 5622412761110962586731) (FT ((529:ℝ)/(240:ℝ)) ((1175:ℝ)/1000) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5622412761110743300396, 5622412761110962586731) (zFT_mem (lam := ((1175:ℝ)/1000)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 27) (zofNatI 40)) (((27:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 27) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-185954911505188289008, -185954911505188088969) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (15574283664014813128, 15574283664015145098) (zexp_mem hWB 22 22 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2624163907805024079870, 2624163907805086770594) (FT ((529:ℝ)/(240:ℝ)) ((1175:ℝ)/1000) ((((27:ℝ)/(40:ℝ))))) := zwiden (2624163907805024079870, 2624163907805086770594) (zFT_mem (lam := ((1175:ℝ)/1000)) (z := ((((27:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (606962440741919873920, 606962440741921913193) (fT ((529:ℝ)/(240:ℝ)) ((1175:ℝ)/1000) 0 / 6) := zwiden (606962440741919873920, 606962440741921913193) (zC_mem (lam := ((1175:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1175:ℝ)/1000) ((5:ℝ)/10) = ((529:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((1175:ℝ)/1000) - ((5:ℝ)/10) = (((27:ℝ)/(40:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_79 : sideCond ((1175:ℝ)/1000) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2629) (zofNatI 1200)) ((2629:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2629) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2629:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2629:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1175) (zofNatI 1000)) ((1175:ℝ)/1000) := zdiv_mem (zofNat_mem 1175) (zofNat_mem 1000) (by decide)
  have hS := zwiden (81385695400524050997, 81385695400524067137) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-58106527896382889369, -58106527896382829557) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-140062912631181980183, -140062912631181808230) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (33763685841731159794, 33763685841731229305) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-94580803603141446354, -94580803603141330239) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-32472628316537680412, -32472628316537541390) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (154420981799962593844, 154420981799962785282) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (468426873939432165225, 468426873939433133873) (zexp_mem hWA 21 21 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5872880840104712533205, 5872880840104983948048) (FT ((2629:ℝ)/(1200:ℝ)) ((1175:ℝ)/1000) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5872880840104712533205, 5872880840104983948048) (zFT_mem (lam := ((1175:ℝ)/1000)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 119) (zofNatI 200)) (((119:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 119) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-158414627880996305591, -158414627880996109202) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (20512283609895208628, 20512283609895371797) (zexp_mem hWB 21 21 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2753741158231730531778, 2753741158231792549799) (FT ((2629:ℝ)/(1200:ℝ)) ((1175:ℝ)/1000) ((((119:ℝ)/(200:ℝ))))) := zwiden (2753741158231730531778, 2753741158231792549799) (zFT_mem (lam := ((1175:ℝ)/1000)) (z := ((((119:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (624155195838323280148, 624155195838325717586) (fT ((2629:ℝ)/(1200:ℝ)) ((1175:ℝ)/1000) 0 / 6) := zwiden (624155195838323280148, 624155195838325717586) (zC_mem (lam := ((1175:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1175:ℝ)/1000) ((58:ℝ)/100) = ((2629:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1175:ℝ)/1000) - ((58:ℝ)/100) = (((119:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_80 : sideCond ((12:ℝ)/10) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 1121) (zofNatI 500)) ((1121:ℝ)/(500:ℝ)) := zdiv_mem (zofNat_mem 1121) (zofNat_mem 500) (by decide)
  have hθ1 : Real.pi / 2 < ((1121:ℝ)/(500:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1121:ℝ)/(500:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 12) (zofNatI 10)) ((12:ℝ)/10) := zdiv_mem (zofNat_mem 12) (zofNat_mem 10) (by decide)
  have hS := zwiden (78307363405621593529, 78307363405621601062) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-62192900209428449862, -62192900209428365985) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-125910454636991349997, -125910454636991168072) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (38679568364599148895, 38679568364599253228) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-97403240758985468071, -97403240758985327336) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-22640863270801702210, -22640863270801493544) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (103276570936784309074, 103276570936784458300) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (280882349148511858137, 280882349148512388930) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5209175562364242000651, 5209175562364491129125) (FT ((1121:ℝ)/(500:ℝ)) ((12:ℝ)/10) ((((-87:ℝ)/(250:ℝ))))) := zwiden (5209175562364242000651, 5209175562364491129125) (zFT_mem (lam := ((12:ℝ)/10)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 213) (zofNatI 250)) (((213:ℝ)/(250:ℝ))) := zdiv_mem (zofNat_mem 213) (zofNat_mem 250) (by decide)
  have hWB := zwiden (-252849535741782639284, -252849535741782273942) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (7977896885710837120, 7977896885710895874) (zexp_mem hWB 26 26 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2372881975773159393811, 2372881975773204612013) (FT ((1121:ℝ)/(500:ℝ)) ((12:ℝ)/10) ((((213:ℝ)/(250:ℝ))))) := zwiden (2372881975773159393811, 2372881975773204612013) (zFT_mem (lam := ((12:ℝ)/10)) (z := ((((213:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (577297238061126828868, 577297238061129331948) (fT ((1121:ℝ)/(500:ℝ)) ((12:ℝ)/10) 0 / 6) := zwiden (577297238061126828868, 577297238061129331948) (zC_mem (lam := ((12:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((12:ℝ)/10) ((348:ℝ)/1000) = ((1121:ℝ)/(500:ℝ)) := by norm_num [theta13]
  have hzB : ((12:ℝ)/10) - ((348:ℝ)/1000) = (((213:ℝ)/(250:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_81 : sideCond ((12:ℝ)/10) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 67) (zofNatI 30)) ((67:ℝ)/(30:ℝ)) := zdiv_mem (zofNat_mem 67) (zofNat_mem 30) (by decide)
  have hθ1 : Real.pi / 2 < ((67:ℝ)/(30:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((67:ℝ)/(30:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 12) (zofNatI 10)) ((12:ℝ)/10) := zdiv_mem (zofNat_mem 12) (zofNat_mem 10) (by decide)
  have hS := zwiden (78843420935120421740, 78843420935120428898) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-61511909214780702403, -61511909214780625660) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-128175863733677175953, -128175863733677004401) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (37837149752474136472, 37837149752474230885) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-96996187014877361095, -96996187014877231274) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-24325700495051727056, -24325700495051538230) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (116159848314538435498, 116159848314538591007) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (319503640824169737946, 319503640824170291452) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5367995800410724061637, 5367995800410966506526) (FT ((67:ℝ)/(30:ℝ)) ((12:ℝ)/10) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5367995800410724061637, 5367995800410966506526) (zFT_mem (lam := ((12:ℝ)/10)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 4) (zofNatI 5)) (((4:ℝ)/(5:ℝ))) := zdiv_mem (zofNat_mem 4) (zofNat_mem 5) (by decide)
  have hWB := zwiden (-232319696629077182012, -232319696629076870996) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (9795990993634203442, 9795990993634270548) (zexp_mem hWB 25 25 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2446840695863193555789, 2446840695863239119854) (FT ((67:ℝ)/(30:ℝ)) ((12:ℝ)/10) ((((4:ℝ)/(5:ℝ))))) := zwiden (2446840695863193555789, 2446840695863239119854) (zFT_mem (lam := ((12:ℝ)/10)) (z := ((((4:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (586185140094024762827, 586185140094027140243) (fT ((67:ℝ)/(30:ℝ)) ((12:ℝ)/10) 0 / 6) := zwiden (586185140094024762827, 586185140094027140243) (zC_mem (lam := ((12:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((12:ℝ)/10) ((4:ℝ)/10) = ((67:ℝ)/(30:ℝ)) := by norm_num [theta13]
  have hzB : ((12:ℝ)/10) - ((4:ℝ)/10) = (((4:ℝ)/(5:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_82 : sideCond ((12:ℝ)/10) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 167) (zofNatI 75)) ((167:ℝ)/(75:ℝ)) := zdiv_mem (zofNat_mem 167) (zofNat_mem 75) (by decide)
  have hθ1 : Real.pi / 2 < ((167:ℝ)/(75:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((167:ℝ)/(75:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 12) (zofNatI 10)) ((12:ℝ)/10) := zdiv_mem (zofNat_mem 12) (zofNat_mem 10) (by decide)
  have hS := zwiden (79251745222735610405, 79251745222735617536) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-60984923375786994428, -60984923375786922521) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-129953012705106129869, -129953012705105964947) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (37191608791506022099, 37191608791506109805) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-96663232196118492505, -96663232196118369831) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-25616782416987955802, -25616782416987780390) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (125652253449044449588, 125652253449044609149) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (351318324709848002629, 351318324709848815102) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5491206328442409966998, 5491206328442664869600) (FT ((167:ℝ)/(75:ℝ)) ((12:ℝ)/10) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5491206328442409966998, 5491206328442664869600) (zFT_mem (lam := ((12:ℝ)/10)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 19) (zofNatI 25)) (((19:ℝ)/(25:ℝ))) := zdiv_mem (zofNat_mem 19) (zofNat_mem 25) (by decide)
  have hWB := zwiden (-217035710502895233984, -217035710502894958379) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (11413685078897005671, 11413685078897114089) (zexp_mem hWB 24 24 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2505401560988430853114, 2505401560988479227974) (FT ((167:ℝ)/(75:ℝ)) ((12:ℝ)/10) ((((19:ℝ)/(25:ℝ))))) := zwiden (2505401560988430853114, 2505401560988479227974) (zFT_mem (lam := ((12:ℝ)/10)) (z := ((((19:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (593356417431059718042, 593356417431062017062) (fT ((167:ℝ)/(75:ℝ)) ((12:ℝ)/10) 0 / 6) := zwiden (593356417431059718042, 593356417431062017062) (zC_mem (lam := ((12:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((12:ℝ)/10) ((44:ℝ)/100) = ((167:ℝ)/(75:ℝ)) := by norm_num [theta13]
  have hzB : ((12:ℝ)/10) - ((44:ℝ)/100) = (((19:ℝ)/(25:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_83 : sideCond ((12:ℝ)/10) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 133) (zofNatI 60)) ((133:ℝ)/(60:ℝ)) := zdiv_mem (zofNat_mem 133) (zofNat_mem 60) (by decide)
  have hθ1 : Real.pi / 2 < ((133:ℝ)/(60:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((133:ℝ)/(60:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 12) (zofNatI 10)) ((12:ℝ)/10) := zdiv_mem (zofNat_mem 12) (zofNat_mem 10) (by decide)
  have hS := zwiden (79857621738150718763, 79857621738150725054) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-60189369911359302401, -60189369911359237939) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-132677284802543840192, -132677284802543687643) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (36227602503264367583, 36227602503264445182) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-96131598700779236132, -96131598700779125602) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-27544794993471264834, -27544794993471109636) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (139226712769359082533, 139226712769359242701) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (402396255643632608559, 402396255643633376232) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5677409012343620166438, 5677409012343861218297) (FT ((133:ℝ)/(60:ℝ)) ((12:ℝ)/10) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5677409012343620166438, 5677409012343861218297) (zFT_mem (lam := ((12:ℝ)/10)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 7) (zofNatI 10)) (((7:ℝ)/(10:ℝ))) := zdiv_mem (zofNat_mem 7) (zofNat_mem 10) (by decide)
  have hWB := zwiden (-194917397877102939781, -194917397877102715546) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (14239164154093010065, 14239164154093113827) (zexp_mem hWB 23 23 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2595980990690187141567, 2595980990690234908660) (FT ((133:ℝ)/(60:ℝ)) ((12:ℝ)/10) ((((7:ℝ)/(10:ℝ))))) := zwiden (2595980990690187141567, 2595980990690234908660) (zFT_mem (lam := ((12:ℝ)/10)) (z := ((((7:ℝ)/(10:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (604686705677878037819, 604686705677880183937) (fT ((133:ℝ)/(60:ℝ)) ((12:ℝ)/10) 0 / 6) := zwiden (604686705677878037819, 604686705677880183937) (zC_mem (lam := ((12:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((12:ℝ)/10) ((5:ℝ)/10) = ((133:ℝ)/(60:ℝ)) := by norm_num [theta13]
  have hzB : ((12:ℝ)/10) - ((5:ℝ)/10) = (((7:ℝ)/(10:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_84 : sideCond ((12:ℝ)/10) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 661) (zofNatI 300)) ((661:ℝ)/(300:ℝ)) := zdiv_mem (zofNat_mem 661) (zofNat_mem 300) (by decide)
  have hθ1 : Real.pi / 2 < ((661:ℝ)/(300:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((661:ℝ)/(300:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 12) (zofNatI 10)) ((12:ℝ)/10) := zdiv_mem (zofNat_mem 12) (zofNat_mem 10) (by decide)
  have hS := zwiden (80653024541893093937, 80653024541893101849) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-59119283082973832181, -59119283082973773974) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-136424226303111241507, -136424226303111093803) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (34950896322447890571, 34950896322447959395) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-95362979787804283344, -95362979787804180097) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-30098207355104218858, -30098207355104081210) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (156122482538888726096, 156122482538888895600) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (476465354126312631144, 476465354126313529263) (zexp_mem hWA 21 21 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5927569433661570947336, 5927569433661818798187) (FT ((661:ℝ)/(300:ℝ)) ((12:ℝ)/10) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5927569433661570947336, 5927569433661818798187) (zFT_mem (lam := ((12:ℝ)/10)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 31) (zofNatI 50)) (((31:ℝ)/(50:ℝ))) := zdiv_mem (zofNat_mem 31) (zofNat_mem 50) (by decide)
  have hWB := zwiden (-166889550300191578056, -166889550300191396861) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (18845509882250688756, 18845509882251089984) (zexp_mem hWB 21 21 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2721889274045860931903, 2721889274045934917937) (FT ((661:ℝ)/(300:ℝ)) ((12:ℝ)/10) ((((31:ℝ)/(50:ℝ))))) := zwiden (2721889274045860931903, 2721889274045934917937) (zFT_mem (lam := ((12:ℝ)/10)) (z := ((((31:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (620931769265981523299, 620931769265983629899) (fT ((661:ℝ)/(300:ℝ)) ((12:ℝ)/10) 0 / 6) := zwiden (620931769265981523299, 620931769265983629899) (zC_mem (lam := ((12:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((12:ℝ)/10) ((58:ℝ)/100) = ((661:ℝ)/(300:ℝ)) := by norm_num [theta13]
  have hzB : ((12:ℝ)/10) - ((58:ℝ)/100) = (((31:ℝ)/(50:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_85 : sideCond ((1225:ℝ)/1000) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 4509) (zofNatI 2000)) ((4509:ℝ)/(2000:ℝ)) := zdiv_mem (zofNat_mem 4509) (zofNat_mem 2000) (by decide)
  have hθ1 : Real.pi / 2 < ((4509:ℝ)/(2000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((4509:ℝ)/(2000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1225) (zofNatI 1000)) ((1225:ℝ)/1000) := zdiv_mem (zofNat_mem 1225) (zofNat_mem 1000) (by decide)
  have hS := zwiden (77523854714822167564, 77523854714822176218) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-63166858004456383643, -63166858004456287795) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-122728685839262470156, -122728685839262270228) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (39900519501551433967, 39900519501551555056) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-97938766454585578771, -97938766454585419227) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-20198960996897132066, -20198960996896889888) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (104370390090404531048, 104370390090404701073) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (283971558463835941723, 283971558463836559493) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5270661571471318636641, 5270661571471605586528) (FT ((4509:ℝ)/(2000:ℝ)) ((1225:ℝ)/1000) ((((-87:ℝ)/(250:ℝ))))) := zwiden (5270661571471318636641, 5270661571471605586528) (zFT_mem (lam := ((1225:ℝ)/1000)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 877) (zofNatI 1000)) (((877:ℝ)/(1000:ℝ))) := zdiv_mem (zofNat_mem 877) (zofNat_mem 1000) (by decide)
  have hWB := zwiden (-263025379624381962187, -263025379624381533704) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (7206017131697080619, 7206017131697194018) (zexp_mem hWB 26 26 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2353254620932257358470, 2353254620932309769856) (FT ((4509:ℝ)/(2000:ℝ)) ((1225:ℝ)/1000) ((((877:ℝ)/(1000:ℝ))))) := zwiden (2353254620932257358470, 2353254620932309769856) (zFT_mem (lam := ((1225:ℝ)/1000)) (z := ((((877:ℝ)/(1000:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (577075698234268774095, 577075698234271555513) (fT ((4509:ℝ)/(2000:ℝ)) ((1225:ℝ)/1000) 0 / 6) := zwiden (577075698234268774095, 577075698234271555513) (zC_mem (lam := ((1225:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1225:ℝ)/1000) ((348:ℝ)/1000) = ((4509:ℝ)/(2000:ℝ)) := by norm_num [theta13]
  have hzB : ((1225:ℝ)/1000) - ((348:ℝ)/1000) = (((877:ℝ)/(1000:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_86 : sideCond ((1225:ℝ)/1000) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 539) (zofNatI 240)) ((539:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 539) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((539:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((539:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1225) (zofNatI 1000)) ((1225:ℝ)/1000) := zdiv_mem (zofNat_mem 1225) (zofNat_mem 1000) (by decide)
  have hS := zwiden (78068382531129878316, 78068382531129888753) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-62492620756159561686, -62492620756159471779) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-124924161583406182042, -124924161583405985613) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (39053276489731736303, 39053276489731848674) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-97573956451293844496, -97573956451293691072) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-21893447020536527394, -21893447020536302652) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (117404563542933207868, 117404563542933392761) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (323505404913788516092, 323505404913789183592) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5429840034218234001530, 5429840034218524198195) (FT ((539:ℝ)/(240:ℝ)) ((1225:ℝ)/1000) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5429840034218234001530, 5429840034218524198195) (zFT_mem (lam := ((1225:ℝ)/1000)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 33) (zofNatI 40)) (((33:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 33) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-242146912307300122568, -242146912307299741229) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (8879107657328086562, 8879107657328223589) (zexp_mem hWB 25 25 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2425230984876559129871, 2425230984876614759776) (FT ((539:ℝ)/(240:ℝ)) ((1225:ℝ)/1000) ((((33:ℝ)/(40:ℝ))))) := zwiden (2425230984876559129871, 2425230984876614759776) (zFT_mem (lam := ((1225:ℝ)/1000)) (z := ((((33:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (585465355195975896406, 585465355195978648046) (fT ((539:ℝ)/(240:ℝ)) ((1225:ℝ)/1000) 0 / 6) := zwiden (585465355195975896406, 585465355195978648046) (zC_mem (lam := ((1225:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1225:ℝ)/1000) ((4:ℝ)/10) = ((539:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((1225:ℝ)/1000) - ((4:ℝ)/10) = (((33:ℝ)/(40:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_87 : sideCond ((1225:ℝ)/1000) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2687) (zofNatI 1200)) ((2687:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2687) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2687:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2687:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1225) (zofNatI 1000)) ((1225:ℝ)/1000) := zdiv_mem (zofNat_mem 1225) (zofNat_mem 1000) (by decide)
  have hS := zwiden (78483262070269350725, 78483262070269370780) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-61970780008076620502, -61970780008076526663) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-126645593391015581315, -126645593391015357179) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (38403775748094173140, 38403775748094289447) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-97273379361457744817, -97273379361457572664) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-23192448503811653720, -23192448503811421106) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (127011463614113180836, 127011463614113407147) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (356126078815067378046, 356126078815068493035) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5553278865171781974170, 5553278865172138691448) (FT ((2687:ℝ)/(1200:ℝ)) ((1225:ℝ)/1000) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5553278865171781974170, 5553278865172138691448) (zFT_mem (lam := ((1225:ℝ)/1000)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 157) (zofNatI 200)) (((157:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 157) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-226599997584270510477, -226599997584270106719) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (10372625890971847364, 10372625890971908907) (zexp_mem hWB 25 25 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2482214106575846627957, 2482214106575906253777) (FT ((2687:ℝ)/(1200:ℝ)) ((1225:ℝ)/1000) ((((157:ℝ)/(200:ℝ))))) := zwiden (2482214106575846627957, 2482214106575906253777) (zFT_mem (lam := ((1225:ℝ)/1000)) (z := ((((157:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (592236595486942414336, 592236595486945574831) (fT ((2687:ℝ)/(1200:ℝ)) ((1225:ℝ)/1000) 0 / 6) := zwiden (592236595486942414336, 592236595486945574831) (zC_mem (lam := ((1225:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1225:ℝ)/1000) ((44:ℝ)/100) = ((2687:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1225:ℝ)/1000) - ((44:ℝ)/100) = (((157:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_88 : sideCond ((1225:ℝ)/1000) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 107) (zofNatI 48)) ((107:ℝ)/(48:ℝ)) := zdiv_mem (zofNat_mem 107) (zofNat_mem 48) (by decide)
  have hθ1 : Real.pi / 2 < ((107:ℝ)/(48:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((107:ℝ)/(48:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1225) (zofNatI 1000)) ((1225:ℝ)/1000) := zdiv_mem (zofNat_mem 1225) (zofNat_mem 1000) (by decide)
  have hS := zwiden (79099035411536167454, 79099035411536174484) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-61182861954672856531, -61182861954672782956) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-129282993446982845499, -129282993446982678539) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (37433425969645462715, 37433425969645552747) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-96790107286635952903, -96790107286635827905) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-25133148060709074570, -25133148060708894506) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (140755395790143708364, 140755395790143890212) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (408594876803472899508, 408594876803473795745) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5739737450917443668384, 5739737450917721031271) (FT ((107:ℝ)/(48:ℝ)) ((1225:ℝ)/1000) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5739737450917443668384, 5739737450917721031271) (zFT_mem (lam := ((1225:ℝ)/1000)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 29) (zofNatI 40)) (((29:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 29) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-204095323895708640808, -204095323895708377127) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (12990482150314691704, 12990482150314932867) (zexp_mem hWB 23 23 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2570338643261331541825, 2570338643261392386148) (FT ((107:ℝ)/(48:ℝ)) ((1225:ℝ)/1000) ((((29:ℝ)/(40:ℝ))))) := zwiden (2570338643261331541825, 2570338643261392386148) (zFT_mem (lam := ((1225:ℝ)/1000)) (z := ((((29:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (602937082435590137855, 602937082435592508420) (fT ((107:ℝ)/(48:ℝ)) ((1225:ℝ)/1000) 0 / 6) := zwiden (602937082435590137855, 602937082435592508420) (zC_mem (lam := ((1225:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1225:ℝ)/1000) ((5:ℝ)/10) = ((107:ℝ)/(48:ℝ)) := by norm_num [theta13]
  have hzB : ((1225:ℝ)/1000) - ((5:ℝ)/10) = (((29:ℝ)/(40:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_89 : sideCond ((1225:ℝ)/1000) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2659) (zofNatI 1200)) ((2659:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2659) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2659:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2659:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1225) (zofNatI 1000)) ((1225:ℝ)/1000) := zdiv_mem (zofNat_mem 1225) (zofNat_mem 1000) (by decide)
  have hS := zwiden (79907751812265600374, 79907751812265618332) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-60122801001860933624, -60122801001860858292) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-132907566648121395505, -132907566648121199105) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (36147512003093610255, 36147512003093700840) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-96085557214298763046, -96085557214298621059) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-27704975993812779490, -27704975993812598320) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (157873517386454891184, 157873517386455126377) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (484881901804725578573, 484881901804726833346) (zexp_mem hWA 21 21 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5990055329401940081898, 5990055329402282732267) (FT ((2659:ℝ)/(1200:ℝ)) ((1225:ℝ)/1000) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5990055329401940081898, 5990055329402282732267) (zFT_mem (lam := ((1225:ℝ)/1000)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 129) (zofNatI 200)) (((129:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 129) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-175566239162523373298, -175566239162523111748) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (17279274790672666808, 17279274790672796949) (zexp_mem hWB 22 22 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2692804033472044945557, 2692804033472110539277) (FT ((2659:ℝ)/(1200:ℝ)) ((1225:ℝ)/1000) ((((129:ℝ)/(200:ℝ))))) := zwiden (2692804033472044945557, 2692804033472110539277) (zFT_mem (lam := ((1225:ℝ)/1000)) (z := ((((129:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (618281048716950307499, 618281048716953135354) (fT ((2659:ℝ)/(1200:ℝ)) ((1225:ℝ)/1000) 0 / 6) := zwiden (618281048716950307499, 618281048716953135354) (zC_mem (lam := ((1225:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1225:ℝ)/1000) ((58:ℝ)/100) = ((2659:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1225:ℝ)/1000) - ((58:ℝ)/100) = (((129:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_90 : sideCond ((125:ℝ)/100) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2267) (zofNatI 1000)) ((2267:ℝ)/(1000:ℝ)) := zdiv_mem (zofNat_mem 2267) (zofNat_mem 1000) (by decide)
  have hθ1 : Real.pi / 2 < ((2267:ℝ)/(1000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2267:ℝ)/(1000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 125) (zofNatI 100)) ((125:ℝ)/100) := zdiv_mem (zofNat_mem 125) (zofNat_mem 100) (by decide)
  have hS := zwiden (76728233079445415191, 76728233079445425126) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-64130946106433755017, -64130946106433645568) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-119643070526520758786, -119643070526520539104) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (41127782485062967643, 41127782485063108025) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-98413083609196044624, -98413083609195863923) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-17744435029874064714, -17744435029873783950) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (105502608253454935989, 105502608253455129709) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (287205006326943029516, 287205006326943749764) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5338804825230248653923, 5338804825230579530329) (FT ((2267:ℝ)/(1000:ℝ)) ((125:ℝ)/100) ((((-87:ℝ)/(250:ℝ))))) := zwiden (5338804825230248653923, 5338804825230579530329) (zFT_mem (lam := ((125:ℝ)/100)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 451) (zofNatI 500)) (((451:ℝ)/(500:ℝ))) := zdiv_mem (zofNat_mem 451) (zofNat_mem 500) (by decide)
  have hWB := zwiden (-273457909898323353442, -273457909898322851328) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (6492132680648324445, 6492132680648380046) (zexp_mem hWB 27 27 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2335695944110022094918, 2335695944110075756393) (FT ((2267:ℝ)/(1000:ℝ)) ((125:ℝ)/100) ((((451:ℝ)/(500:ℝ))))) := zwiden (2335695944110022094918, 2335695944110075756393) (zFT_mem (lam := ((125:ℝ)/100)) (z := ((((451:ℝ)/(500:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (577302185433288481739, 577302185433291573473) (fT ((2267:ℝ)/(1000:ℝ)) ((125:ℝ)/100) 0 / 6) := zwiden (577302185433288481739, 577302185433291573473) (zC_mem (lam := ((125:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((125:ℝ)/100) ((348:ℝ)/1000) = ((2267:ℝ)/(1000:ℝ)) := by norm_num [theta13]
  have hzB : ((125:ℝ)/100) - ((348:ℝ)/1000) = (((451:ℝ)/(500:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_91 : sideCond ((125:ℝ)/100) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 271) (zofNatI 120)) ((271:ℝ)/(120:ℝ)) := zdiv_mem (zofNat_mem 271) (zofNat_mem 120) (by decide)
  have hθ1 : Real.pi / 2 < ((271:ℝ)/(120:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((271:ℝ)/(120:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 125) (zofNatI 100)) ((125:ℝ)/100) := zdiv_mem (zofNat_mem 125) (zofNat_mem 100) (by decide)
  have hS := zwiden (77281146101198550940, 77281146101198561279) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-63463567952686171219, -63463567952686070098) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-121772457165997815161, -121772457165997604839) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (40276244572852023868, 40276244572852152219) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-98090745341097657213, -98090745341097487794) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-19447510854295952264, -19447510854295695562) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (118691317147611089117, 118691317147611294264) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (327695019574413191603, 327695019574413949177) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5498618045093145688436, 5498618045093472191199) (FT ((271:ℝ)/(120:ℝ)) ((125:ℝ)/100) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5498618045093145688436, 5498618045093472191199) (zFT_mem (lam := ((125:ℝ)/100)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 17) (zofNatI 20)) (((17:ℝ)/(20:ℝ))) := zdiv_mem (zofNat_mem 17) (zofNat_mem 20) (by decide)
  have hWB := zwiden (-252219048938674000310, -252219048938673564376) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (8028355372642085852, 8028355372642148600) (zexp_mem hWB 26 26 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2405801566688992313448, 2405801566689046830196) (FT ((271:ℝ)/(120:ℝ)) ((125:ℝ)/100) ((((17:ℝ)/(20:ℝ))))) := zwiden (2405801566688992313448, 2405801566689046830196) (zFT_mem (lam := ((125:ℝ)/100)) (z := ((((17:ℝ)/(20:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (585212801526464211776, 585212801526467189832) (fT ((271:ℝ)/(120:ℝ)) ((125:ℝ)/100) 0 / 6) := zwiden (585212801526464211776, 585212801526467189832) (zC_mem (lam := ((125:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((125:ℝ)/100) ((4:ℝ)/10) = ((271:ℝ)/(120:ℝ)) := by norm_num [theta13]
  have hzB : ((125:ℝ)/100) - ((4:ℝ)/10) = (((17:ℝ)/(20:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_92 : sideCond ((125:ℝ)/100) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 1351) (zofNatI 600)) ((1351:ℝ)/(600:ℝ)) := zdiv_mem (zofNat_mem 1351) (zofNat_mem 600) (by decide)
  have hθ1 : Real.pi / 2 < ((1351:ℝ)/(600:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1351:ℝ)/(600:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 125) (zofNatI 100)) ((125:ℝ)/100) := zdiv_mem (zofNat_mem 125) (zofNat_mem 100) (by decide)
  have hS := zwiden (77702516067778394933, 77702516067778409814) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-62946953832069194271, -62946953832069094922) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-123441264965854333971, -123441264965854115501) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (39623189967366381139, 39623189967366506214) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-97822733831081246287, -97822733831081073158) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-20753620065267237722, -20753620065266987572) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (128415188694948609089, 128415188694948837137) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (361160360978985783704, 361160360978986988126) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5622502846703485248301, 5622502846703855827778) (FT ((1351:ℝ)/(600:ℝ)) ((125:ℝ)/100) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5622502846703485248301, 5622502846703855827778) (zFT_mem (lam := ((125:ℝ)/100)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 81) (zofNatI 100)) (((81:ℝ)/(100:ℝ))) := zdiv_mem (zofNat_mem 81) (zofNat_mem 100) (by decide)
  have hWB := zwiden (-236400688279337632001, -236400688279337212186) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (9404264938080805502, 9404264938080901593) (zexp_mem hWB 25 25 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2461297413141522218641, 2461297413141582769888) (FT ((1351:ℝ)/(600:ℝ)) ((125:ℝ)/100) ((((81:ℝ)/(100:ℝ))))) := zwiden (2461297413141522218641, 2461297413141582769888) (zFT_mem (lam := ((125:ℝ)/100)) (z := ((((81:ℝ)/(100:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (591600313479565074117, 591600313479568184586) (fT ((1351:ℝ)/(600:ℝ)) ((125:ℝ)/100) 0 / 6) := zwiden (591600313479565074117, 591600313479568184586) (zC_mem (lam := ((125:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((125:ℝ)/100) ((44:ℝ)/100) = ((1351:ℝ)/(600:ℝ)) := by norm_num [theta13]
  have hzB : ((125:ℝ)/100) - ((44:ℝ)/100) = (((81:ℝ)/(100:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_93 : sideCond ((125:ℝ)/100) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 269) (zofNatI 120)) ((269:ℝ)/(120:ℝ)) := zdiv_mem (zofNat_mem 269) (zofNat_mem 120) (by decide)
  have hθ1 : Real.pi / 2 < ((269:ℝ)/(120:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((269:ℝ)/(120:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 125) (zofNatI 100)) ((125:ℝ)/100) := zdiv_mem (zofNat_mem 125) (zofNat_mem 100) (by decide)
  have hS := zwiden (78328090021565124414, 78328090021565133200) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-62166794300282197723, -62166794300282112892) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-125996668966425505961, -125996668966425319896) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (38647103135735885982, 38647103135735991456) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-97388125206092524167, -97388125206092380349) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-22705793728528228036, -22705793728528017088) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (142331805121864385705, 142331805121864596067) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (415087041671794260125, 415087041671795324750) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5809551583934947305813, 5809551583935272256477) (FT ((269:ℝ)/(120:ℝ)) ((125:ℝ)/100) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5809551583934947305813, 5809551583935272256477) (zFT_mem (lam := ((125:ℝ)/100)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 3) (zofNatI 4)) (((3:ℝ)/(4:ℝ))) := zdiv_mem (zofNat_mem 3) (zofNat_mem 4) (by decide)
  have hWB := zwiden (-213497707682796894100, -213497707682796578558) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (11824730094878932572, 11824730094879021767) (zexp_mem hWB 24 24 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2547110593790746902487, 2547110593790802234895) (FT ((269:ℝ)/(120:ℝ)) ((125:ℝ)/100) ((((3:ℝ)/(4:ℝ))))) := zwiden (2547110593790746902487, 2547110593790802234895) (zFT_mem (lam := ((125:ℝ)/100)) (z := ((((3:ℝ)/(4:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (601698182385861783264, 601698182385864451217) (fT ((269:ℝ)/(120:ℝ)) ((125:ℝ)/100) 0 / 6) := zwiden (601698182385861783264, 601698182385864451217) (zC_mem (lam := ((125:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((125:ℝ)/100) ((5:ℝ)/10) = ((269:ℝ)/(120:ℝ)) := by norm_num [theta13]
  have hzB : ((125:ℝ)/100) - ((5:ℝ)/10) = (((3:ℝ)/(4:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_94 : sideCond ((125:ℝ)/100) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 1337) (zofNatI 600)) ((1337:ℝ)/(600:ℝ)) := zdiv_mem (zofNat_mem 1337) (zofNat_mem 600) (by decide)
  have hθ1 : Real.pi / 2 < ((1337:ℝ)/(600:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1337:ℝ)/(600:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 125) (zofNatI 100)) ((125:ℝ)/100) := zdiv_mem (zofNat_mem 125) (zofNat_mem 100) (by decide)
  have hS := zwiden (79149993658989339004, 79149993658989351753) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-61116924855411001813, -61116924855410923247) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-129505851032656937669, -129505851032656750327) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (37352785037819455014, 37352785037819551049) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-96748084295254189945, -96748084295254049990) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-25294429924361089972, -25294429924360897902) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (159675668461642052745, 159675668461642284694) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (493699420070547767865, 493699420070549058143) (zexp_mem hWA 21 21 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (6060486379955110941632, 6060486379955457759813) (FT ((1337:ℝ)/(600:ℝ)) ((125:ℝ)/100) ((((-29:ℝ)/(50:ℝ))))) := zwiden (6060486379955110941632, 6060486379955457759813) (zFT_mem (lam := ((125:ℝ)/100)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 67) (zofNatI 100)) (((67:ℝ)/(100:ℝ))) := zdiv_mem (zofNat_mem 67) (zofNat_mem 100) (by decide)
  have hWB := zwiden (-184452927360862639215, -184452927360862371275) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (15809972508933030460, 15809972508933324485) (zexp_mem hWB 22 22 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2666339864762071120085, 2666339864762146428905) (FT ((1337:ℝ)/(600:ℝ)) ((125:ℝ)/100) ((((67:ℝ)/(100:ℝ))))) := zwiden (2666339864762071120085, 2666339864762146428905) (zFT_mem (lam := ((125:ℝ)/100)) (z := ((((67:ℝ)/(100:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (616182912762811295343, 616182912762814014010) (fT ((1337:ℝ)/(600:ℝ)) ((125:ℝ)/100) 0 / 6) := zwiden (616182912762811295343, 616182912762814014010) (zC_mem (lam := ((125:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((125:ℝ)/100) ((58:ℝ)/100) = ((1337:ℝ)/(600:ℝ)) := by norm_num [theta13]
  have hzB : ((125:ℝ)/100) - ((58:ℝ)/100) = (((67:ℝ)/(100:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_95 : sideCond ((1275:ℝ)/1000) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2717) (zofNatI 1200)) ((2717:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2717) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2717:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2717:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1275) (zofNatI 1000)) ((1275:ℝ)/1000) := zdiv_mem (zofNat_mem 1275) (zofNat_mem 1000) (by decide)
  have hS := zwiden (76909629205237191543, 76909629205237214389) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-63913292322590754633, -63913292322590635486) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-120334325474973107522, -120334325474972847448) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (40849089355129230686, 40849089355129382988) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-98310952276327786728, -98310952276327574253) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-18301821289741538628, -18301821289741234024) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (129864770345463661673, 129864770345463943906) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (366433804393220195762, 366433804393221701289) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5699071768405754619131, 5699071768406215976857) (FT ((2717:ℝ)/(1200:ℝ)) ((1275:ℝ)/1000) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5699071768405754619131, 5699071768406215976857) (zFT_mem (lam := ((1275:ℝ)/1000)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 167) (zofNatI 200)) (((167:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 167) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-246447916451050893548, -246447916451050357948) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (8505312952588651193, 8505312952588856939) (zexp_mem hWB 25 25 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2442550832659560071126, 2442550832659637390604) (FT ((2717:ℝ)/(1200:ℝ)) ((1275:ℝ)/1000) ((((167:ℝ)/(200:ℝ))))) := zwiden (2442550832659560071126, 2442550832659637390604) (zFT_mem (lam := ((1275:ℝ)/1000)) (z := ((((167:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (591437357740644766829, 591437357740648512496) (fT ((2717:ℝ)/(1200:ℝ)) ((1275:ℝ)/1000) 0 / 6) := zwiden (591437357740644766829, 591437357740648512496) (zC_mem (lam := ((1275:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1275:ℝ)/1000) ((44:ℝ)/100) = ((2717:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1275:ℝ)/1000) - ((44:ℝ)/100) = (((167:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_96 : sideCond ((1275:ℝ)/1000) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 541) (zofNatI 240)) ((541:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 541) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((541:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((541:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1275) (zofNatI 1000)) ((1275:ℝ)/1000) := zdiv_mem (zofNat_mem 1275) (zofNat_mem 1000) (by decide)
  have hS := zwiden (77544906026886288627, 77544906026886299855) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-63141013210760129453, -63141013210760031394) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-122812261133737495999, -122812261133737287485) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (39867875492813728086, 39867875492813851918) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-97925278717415612827, -97925278717415446567) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-20264249014372543828, -20264249014372296164) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (143957438767770881185, 143957438767771125948) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (421889981907472900564, 421889981907474173442) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5887044225317430587370, 5887044225317813759143) (FT ((541:ℝ)/(240:ℝ)) ((1275:ℝ)/1000) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5887044225317430587370, 5887044225317813759143) (zFT_mem (lam := ((1275:ℝ)/1000)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 31) (zofNatI 40)) (((31:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 31) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-223134030090045245220, -223134030090044865836) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (10738440622330886721, 10738440622331077091) (zexp_mem hWB 24 24 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2526184135818766107235, 2526184135818833872031) (FT ((541:ℝ)/(240:ℝ)) ((1275:ℝ)/1000) ((((31:ℝ)/(40:ℝ))))) := zwiden (2526184135818766107235, 2526184135818833872031) (zFT_mem (lam := ((1275:ℝ)/1000)) (z := ((((31:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (600956923624037706739, 600956923624040727802) (fT ((541:ℝ)/(240:ℝ)) ((1275:ℝ)/1000) 0 / 6) := zwiden (600956923624037706739, 600956923624040727802) (zC_mem (lam := ((1275:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1275:ℝ)/1000) ((5:ℝ)/10) = ((541:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((1275:ℝ)/1000) - ((5:ℝ)/10) = (((31:ℝ)/(40:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_97 : sideCond ((1275:ℝ)/1000) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2689) (zofNatI 1200)) ((2689:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2689) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2689:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2689:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1275) (zofNatI 1000)) ((1275:ℝ)/1000) := zdiv_mem (zofNat_mem 1275) (zofNat_mem 1000) (by decide)
  have hS := zwiden (78379868480234088970, 78379868480234109191) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-62101499313794474811, -62101499313794379478) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-126212521994334321907, -126212521994334095594) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (38565962170212037851, 38565962170212156259) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-97350146972811194345, -97350146972811019785) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-22868075659575924298, -22868075659575687482) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (161530640702979064639, 161530640702979356225) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (502942873971990879029, 502942873971992530526) (zexp_mem hWA 21 21 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (6139053085126236978763, 6139053085126675860888) (FT ((2689:ℝ)/(1200:ℝ)) ((1275:ℝ)/1000) ((((-29:ℝ)/(50:ℝ))))) := zwiden (6139053085126236978763, 6139053085126675860888) (zFT_mem (lam := ((1275:ℝ)/1000)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 139) (zofNatI 200)) (((139:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 139) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-193558267738914918235, -193558267738914568836) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (14434014057984684751, 14434014057984796339) (zexp_mem hWB 23 23 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2642366600246804754756, 2642366600246877032916) (FT ((2689:ℝ)/(1200:ℝ)) ((1275:ℝ)/1000) ((((139:ℝ)/(200:ℝ))))) := zwiden (2642366600246804754756, 2642366600246877032916) (zFT_mem (lam := ((1275:ℝ)/1000)) (z := ((((139:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (614619957160933504904, 614619957160936821801) (fT ((2689:ℝ)/(1200:ℝ)) ((1275:ℝ)/1000) 0 / 6) := zwiden (614619957160933504904, 614619957160936821801) (zC_mem (lam := ((1275:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1275:ℝ)/1000) ((58:ℝ)/100) = ((2689:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1275:ℝ)/1000) - ((58:ℝ)/100) = (((139:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_98 : sideCond ((13:ℝ)/10) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 34) (zofNatI 15)) ((34:ℝ)/(15:ℝ)) := zdiv_mem (zofNat_mem 34) (zofNat_mem 15) (by decide)
  have hθ1 : Real.pi / 2 < ((34:ℝ)/(15:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((34:ℝ)/(15:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 13) (zofNatI 10)) ((13:ℝ)/10) := zdiv_mem (zofNat_mem 13) (zofNat_mem 10) (by decide)
  have hS := zwiden (76749605798405446940, 76749605798405457004) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-64105366466383931045, -64105366466383821817) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-119724151079694928442, -119724151079694708745) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (41094980097893674056, 41094980097893814099) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-98401232117145737922, -98401232117145557353) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-17810039804212651888, -17810039804212371802) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (145633919962323650683, 145633919962323917953) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (429022508797615959477, 429022508797617408974) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5972448600831435810633, 5972448600831863612591) (FT ((34:ℝ)/(15:ℝ)) ((13:ℝ)/10) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5972448600831435810633, 5972448600831863612591) (zFT_mem (lam := ((13:ℝ)/10)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 4) (zofNatI 5)) (((4:ℝ)/(5:ℝ))) := zdiv_mem (zofNat_mem 4) (zofNat_mem 5) (by decide)
  have hWB := zwiden (-233014271939718268724, -233014271939717841093) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (9728186209001255414, 9728186209001336488) (zexp_mem hWB 25 25 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2507458901499841904727, 2507458901499905534778) (FT ((34:ℝ)/(15:ℝ)) ((13:ℝ)/10) ((((4:ℝ)/(5:ℝ))))) := zwiden (2507458901499841904727, 2507458901499905534778) (zFT_mem (lam := ((13:ℝ)/10)) (z := ((((4:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (600702379326371481254, 600702379326374697655) (fT ((34:ℝ)/(15:ℝ)) ((13:ℝ)/10) 0 / 6) := zwiden (600702379326371481254, 600702379326374697655) (zC_mem (lam := ((13:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((13:ℝ)/10) ((5:ℝ)/10) = ((34:ℝ)/(15:ℝ)) := by norm_num [theta13]
  have hzB : ((13:ℝ)/10) - ((5:ℝ)/10) = (((4:ℝ)/(5:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_99 : sideCond ((13:ℝ)/10) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 169) (zofNatI 75)) ((169:ℝ)/(75:ℝ)) := zdiv_mem (zofNat_mem 169) (zofNat_mem 75) (by decide)
  have hθ1 : Real.pi / 2 < ((169:ℝ)/(75:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((169:ℝ)/(75:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 13) (zofNatI 10)) ((13:ℝ)/10) := zdiv_mem (zofNat_mem 13) (zofNat_mem 10) (by decide)
  have hS := zwiden (77597496606492232241, 77597496606492241598) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-63076370539255324718, -63076370539255229256) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-123021499086095751337, -123021499086095550316) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (39786285204054250207, 39786285204054370636) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-97891368977394245261, -97891368977394085303) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-20427429591891499586, -20427429591891258728) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (163440267075555257775, 163440267075555524968) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (512639493667620808708, 512639493667622415199) (zexp_mem hWA 21 21 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (6225989601961447328087, 6225989601961865237806) (FT ((169:ℝ)/(75:ℝ)) ((13:ℝ)/10) ((((-29:ℝ)/(50:ℝ))))) := zwiden (6225989601961447328087, 6225989601961865237806) (zFT_mem (lam := ((13:ℝ)/10)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 18) (zofNatI 25)) (((18:ℝ)/(25:ℝ))) := zdiv_mem (zofNat_mem 18) (zofNat_mem 25) (by decide)
  have hWB := zwiden (-202891366024827548236, -202891366024827216548) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (13147827367076052916, 13147827367076277115) (zexp_mem hWB 23 23 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2620768024203372108266, 2620768024203445580200) (FT ((169:ℝ)/(75:ℝ)) ((13:ℝ)/10) ((((18:ℝ)/(25:ℝ))))) := zwiden (2620768024203372108266, 2620768024203445580200) (zFT_mem (lam := ((13:ℝ)/10)) (z := ((((18:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (613577289687930729305, 613577289687933700021) (fT ((169:ℝ)/(75:ℝ)) ((13:ℝ)/10) 0 / 6) := zwiden (613577289687930729305, 613577289687933700021) (zC_mem (lam := ((13:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((13:ℝ)/10) ((58:ℝ)/100) = ((169:ℝ)/(75:ℝ)) := by norm_num [theta13]
  have hzB : ((13:ℝ)/10) - ((58:ℝ)/100) = (((18:ℝ)/(25:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_100 : sideCond ((1325:ℝ)/1000) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2719) (zofNatI 1200)) ((2719:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2719) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2719:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2719:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1325) (zofNatI 1000)) ((1325:ℝ)/1000) := zdiv_mem (zofNat_mem 1325) (zofNat_mem 1000) (by decide)
  have hS := zwiden (76803000281777286957, 76803000281777310010) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-64041386210147966191, -64041386210147845122) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-119927135914505376523, -119927135914505113804) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (41012991477173145772, 41012991477173300841) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-98371412062868075660, -98371412062867860163) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-17974017045653708456, -17974017045653398318) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (165406514618091065574, 165406514618091429909) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (522819004344424905588, 522819004344427114745) (zexp_mem hWA 21 21 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (6321575268823057507689, 6321575268823627359688) (FT ((2719:ℝ)/(1200:ℝ)) ((1325:ℝ)/1000) ((((-29:ℝ)/(50:ℝ))))) := zwiden (6321575268823057507689, 6321575268823627359688) (zFT_mem (lam := ((1325:ℝ)/1000)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 149) (zofNatI 200)) (((149:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 149) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-212461816190479509107, -212461816190479041125) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (11947858103161835007, 11947858103161937095) (zexp_mem hWB 24 24 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2601440612911179844051, 2601440612911261610939) (FT ((2719:ℝ)/(1200:ℝ)) ((1325:ℝ)/1000) ((((149:ℝ)/(200:ℝ))))) := zwiden (2601440612911179844051, 2601440612911261610939) (zFT_mem (lam := ((1325:ℝ)/1000)) (z := ((((149:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (613042354981177941928, 613042354981181869634) (fT ((2719:ℝ)/(1200:ℝ)) ((1325:ℝ)/1000) 0 / 6) := zwiden (613042354981177941928, 613042354981181869634) (zC_mem (lam := ((1325:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1325:ℝ)/1000) ((58:ℝ)/100) = ((2719:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1325:ℝ)/1000) - ((58:ℝ)/100) = (((149:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

end Work.LinnikAreas2
