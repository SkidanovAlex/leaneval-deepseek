import Mathlib
import Submission.Work.LinnikAreas2.T13SideDefs
import Submission.Work.LinnikAreas.Density4.T13.Basic
import Submission.Work.LinnikAreas.Density4.T13.Num2

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

theorem side_26 : sideCond ((925:ℝ)/1000) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 503) (zofNatI 240)) ((503:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 503) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((503:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((503:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 925) (zofNatI 1000)) ((925:ℝ)/1000) := zdiv_mem (zofNat_mem 925) (zofNat_mem 1000) (by decide)
  have hS := zwiden (86530539287209945426, 86530539287209948910) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-50124502697429502691, -50124502697429484035) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-172631217529560571416, -172631217529560500211) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (25124657706646156211, 25124657706646174914) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-86746004998235692825, -86746004998235657045) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-49750684586707687578, -49750684586707650172) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (104999121164295166237, 104999121164295209802) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (285762600411517285257, 285762600411517560105) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5125117244018563261645, 5125117244018636856379) (FT ((503:ℝ)/(240:ℝ)) ((925:ℝ)/1000) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5125117244018563261645, 5125117244018636856379) (zFT_mem (lam := ((925:ℝ)/1000)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 21) (zofNatI 40)) (((21:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 21) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-137811346528137462866, -137811346528137405687) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (25205361270192343477, 25205361270192458289) (zexp_mem hWB 20 20 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2869549724382516370220, 2869549724382543582315) (FT ((503:ℝ)/(240:ℝ)) ((925:ℝ)/1000) ((((21:ℝ)/(40:ℝ))))) := zwiden (2869549724382516370220, 2869549724382543582315) (zFT_mem (lam := ((925:ℝ)/1000)) (z := ((((21:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (629574291499791705457, 629574291499792614205) (fT ((503:ℝ)/(240:ℝ)) ((925:ℝ)/1000) 0 / 6) := zwiden (629574291499791705457, 629574291499792614205) (zC_mem (lam := ((925:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((925:ℝ)/1000) ((4:ℝ)/10) = ((503:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((925:ℝ)/1000) - ((4:ℝ)/10) = (((21:ℝ)/(40:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_27 : sideCond ((925:ℝ)/1000) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2507) (zofNatI 1200)) ((2507:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2507) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2507:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2507:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 925) (zofNatI 1000)) ((925:ℝ)/1000) := zdiv_mem (zofNat_mem 925) (zofNat_mem 1000) (by decide)
  have hS := zwiden (86862777269496350621, 86862777269496537891) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-49546522834906067326, -49546522834904108974) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-175315586845388460662, -175315586845381153253) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (24548579250296743034, 24548579250298683625) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-86074971549729398213, -86074971549725810483) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-50902841499406513932, -50902841499402632750) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (113368786386594580501, 113368786386599307242) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (310709393676479989925, 310709393676495274236) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5261886225359145160524, 5261886225365944778512) (FT ((2507:ℝ)/(1200:ℝ)) ((925:ℝ)/1000) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5261886225359145160524, 5261886225365944778512) (zFT_mem (lam := ((925:ℝ)/1000)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 97) (zofNatI 200)) (((97:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 97) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-124963321357956054573, -124963321357950844416) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (28660990220349656355, 28660990220351376559) (zexp_mem hWB 19 19 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2954640193654169677655, 2954640193656201835630) (FT ((2507:ℝ)/(1200:ℝ)) ((925:ℝ)/1000) ((((97:ℝ)/(200:ℝ))))) := zwiden (2954640193654169677655, 2954640193656201835630) (zFT_mem (lam := ((925:ℝ)/1000)) (z := ((((97:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (642928937632000957358, 642928937632095228009) (fT ((2507:ℝ)/(1200:ℝ)) ((925:ℝ)/1000) 0 / 6) := zwiden (642928937632000957358, 642928937632095228009) (zC_mem (lam := ((925:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((925:ℝ)/1000) ((44:ℝ)/100) = ((2507:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((925:ℝ)/1000) - ((44:ℝ)/100) = (((97:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_28 : sideCond ((925:ℝ)/1000) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 499) (zofNatI 240)) ((499:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 499) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((499:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((499:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 925) (zofNatI 1000)) ((925:ℝ)/1000) := zdiv_mem (zofNat_mem 925) (zofNat_mem 1000) (by decide)
  have hS := zwiden (87353891137462126864, 87353891137462287387) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-48675432233770828328, -48675432233769073165) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-179461973173521492354, -179461973173514691440) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (23692977031442453037, 23692977031444161704) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-85039768168354794223, -85039768168351571546) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-52614045937115093926, -52614045937111676592) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (125249249632088023065, 125249249632092769829) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (349905347539934474412, 349905347539951320587) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5470209532232987038638, 5470209532239620939556) (FT ((499:ℝ)/(240:ℝ)) ((925:ℝ)/1000) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5470209532232987038638, 5470209532239620939556) (zFT_mem (lam := ((925:ℝ)/1000)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 17) (zofNatI 40)) (((17:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 17) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-106461862187278854355, -106461862187274819604) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (34485935150426330502, 34485935150427914789) (zexp_mem hWB 18 18 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3086830455610182908216, 3086830455612208841970) (FT ((499:ℝ)/(240:ℝ)) ((925:ℝ)/1000) ((((17:ℝ)/(40:ℝ))))) := zwiden (3086830455610182908216, 3086830455612208841970) (zFT_mem (lam := ((925:ℝ)/1000)) (z := ((((17:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (664152973481813290340, 664152973481902670726) (fT ((499:ℝ)/(240:ℝ)) ((925:ℝ)/1000) 0 / 6) := zwiden (664152973481813290340, 664152973481902670726) (zC_mem (lam := ((925:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((925:ℝ)/1000) ((5:ℝ)/10) = ((499:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((925:ℝ)/1000) - ((5:ℝ)/10) = (((17:ℝ)/(40:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_29 : sideCond ((925:ℝ)/1000) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2479) (zofNatI 1200)) ((2479:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2479) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2479:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2479:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 925) (zofNatI 1000)) ((925:ℝ)/1000) := zdiv_mem (zofNat_mem 925) (zofNat_mem 1000) (by decide)
  have hS := zwiden (87995112995659528283, 87995112995659674922) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-47506421554155304009, -47506421554153772566) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-185227828400739083244, -185227828400732803465) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (22568600888809661436, 22568600888811116504) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-83606658653546765660, -83606658653543931143) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-54862798222380677128, -54862798222377766992) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (139863793093863727318, 139863793093868470804) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (404968026439352433425, 404968026439371777961) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5753464190899048553762, 5753464190905573860837) (FT ((2479:ℝ)/(1200:ℝ)) ((925:ℝ)/1000) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5753464190899048553762, 5753464190905573860837) (zFT_mem (lam := ((925:ℝ)/1000)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 69) (zofNatI 200)) (((69:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 69) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-83194842443766590392, -83194842443763768835) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (43520050439828386865, 43520050439829664102) (zexp_mem hWB 17 17 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3271768820269480715513, 3271768820271553453265) (FT ((2479:ℝ)/(1200:ℝ)) ((925:ℝ)/1000) ((((69:ℝ)/(200:ℝ))))) := zwiden (3271768820269480715513, 3271768820271553453265) (zFT_mem (lam := ((925:ℝ)/1000)) (z := ((((69:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (694877621459226130000, 694877621459310849134) (fT ((2479:ℝ)/(1200:ℝ)) ((925:ℝ)/1000) 0 / 6) := zwiden (694877621459226130000, 694877621459310849134) (zC_mem (lam := ((925:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((925:ℝ)/1000) ((58:ℝ)/100) = ((2479:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((925:ℝ)/1000) - ((58:ℝ)/100) = (((69:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_30 : sideCond ((95:ℝ)/100) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2117) (zofNatI 1000)) ((2117:ℝ)/(1000:ℝ)) := zdiv_mem (zofNat_mem 2117) (zofNat_mem 1000) (by decide)
  have hθ1 : Real.pi / 2 < ((2117:ℝ)/(1000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2117:ℝ)/(1000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 95) (zofNatI 100)) ((95:ℝ)/100) := zdiv_mem (zofNat_mem 95) (zofNat_mem 100) (by decide)
  have hS := zwiden (85450266550001631870, 85450266550001633675) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-51944700851325287956, -51944700851325266780) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-164502374928628621312, -164502374928628550774) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (26982519465336718953, 26982519465336740954) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-88773770672116852748, -88773770672116814681) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-46034961069326562094, -46034961069326518092) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (94283201279281904202, 94283201279281944634) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (256724159405823098056, 256724159405823615281) (zexp_mem hWA 17 17 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (4941522943358785366613, 4941522943358878442241) (FT ((2117:ℝ)/(1000:ℝ)) ((95:ℝ)/100) ((((-87:ℝ)/(250:ℝ))))) := zwiden (4941522943358785366613, 4941522943358878442241) (zFT_mem (lam := ((95:ℝ)/100)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 301) (zofNatI 500)) (((301:ℝ)/(500:ℝ))) := zdiv_mem (zofNat_mem 301) (zofNat_mem 500) (by decide)
  have hWB := zwiden (-163099101063585432959, -163099101063585363017) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (19573550201471743851, 19573550201471984135) (zexp_mem hWB 21 21 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2710575172007342369354, 2710575172007376700818) (FT ((2117:ℝ)/(1000:ℝ)) ((95:ℝ)/100) ((((301:ℝ)/(500:ℝ))))) := zwiden (2710575172007342369354, 2710575172007376700818) (zFT_mem (lam := ((95:ℝ)/100)) (z := ((((301:ℝ)/(500:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (606941550583401115450, 606941550583402006566) (fT ((2117:ℝ)/(1000:ℝ)) ((95:ℝ)/100) 0 / 6) := zwiden (606941550583401115450, 606941550583402006566) (zC_mem (lam := ((95:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((95:ℝ)/100) ((348:ℝ)/1000) = ((2117:ℝ)/(1000:ℝ)) := by norm_num [theta13]
  have hzB : ((95:ℝ)/100) - ((348:ℝ)/1000) = (((301:ℝ)/(500:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_31 : sideCond ((95:ℝ)/100) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 253) (zofNatI 120)) ((253:ℝ)/(120:ℝ)) := zdiv_mem (zofNat_mem 253) (zofNat_mem 120) (by decide)
  have hθ1 : Real.pi / 2 < ((253:ℝ)/(120:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((253:ℝ)/(120:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 95) (zofNatI 100)) ((95:ℝ)/100) := zdiv_mem (zofNat_mem 95) (zofNat_mem 100) (by decide)
  have hS := zwiden (85897239209575637543, 85897239209575640230) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-51202190345462208017, -51202190345462187796) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-167760868490244799448, -167760868490244727946) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (26216642961729412740, 26216642961729433448) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-87962535843167833407, -87962535843167795916) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-47566714076541174520, -47566714076541133104) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (105831509604664977609, 105831509604665022848) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (288151182613844438840, 288151182613844742515) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5113356902740444665044, 5113356902740522487330) (FT ((253:ℝ)/(120:ℝ)) ((95:ℝ)/100) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5113356902740444665044, 5113356902740522487330) (zFT_mem (lam := ((95:ℝ)/100)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 11) (zofNatI 20)) (((11:ℝ)/(20:ℝ))) := zdiv_mem (zofNat_mem 11) (zofNat_mem 20) (by decide)
  have hWB := zwiden (-145518325706414406416, -145518325706414344213) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (23335759555461096860, 23335759555461409451) (zexp_mem hWB 20 20 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2813413262807894558450, 2813413262807937615569) (FT ((253:ℝ)/(120:ℝ)) ((95:ℝ)/100) ((((11:ℝ)/(20:ℝ))))) := zwiden (2813413262807894558450, 2813413262807937615569) (zFT_mem (lam := ((95:ℝ)/100)) (z := ((((11:ℝ)/(20:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (622495511891224521960, 622495511891225438688) (fT ((253:ℝ)/(120:ℝ)) ((95:ℝ)/100) 0 / 6) := zwiden (622495511891224521960, 622495511891225438688) (zC_mem (lam := ((95:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((95:ℝ)/100) ((4:ℝ)/10) = ((253:ℝ)/(120:ℝ)) := by norm_num [theta13]
  have hzB : ((95:ℝ)/100) - ((4:ℝ)/10) = (((11:ℝ)/(20:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_32 : sideCond ((95:ℝ)/100) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 1261) (zofNatI 600)) ((1261:ℝ)/(600:ℝ)) := zdiv_mem (zofNat_mem 1261) (zofNat_mem 600) (by decide)
  have hθ1 : Real.pi / 2 < ((1261:ℝ)/(600:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1261:ℝ)/(600:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 95) (zofNatI 100)) ((95:ℝ)/100) := zdiv_mem (zofNat_mem 95) (zofNat_mem 100) (by decide)
  have hS := zwiden (86236675796246172825, 86236675796246179567) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-50628408503656628930, -50628408503656606060) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-170332582723823499262, -170332582723823409001) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (25632357476131285406, 25632357476131308565) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-87320513004194997385, -87320513004194951113) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-48735285047737429188, -48735285047737382870) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (114294457725707358065, 114294457725707419321) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (313598894489479414562, 313598894489479648314) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5247453450561566669651, 5247453450561655268214) (FT ((1261:ℝ)/(600:ℝ)) ((95:ℝ)/100) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5247453450561566669651, 5247453450561655268214) (zFT_mem (lam := ((95:ℝ)/100)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 51) (zofNatI 100)) (((51:ℝ)/(100:ℝ))) := zdiv_mem (zofNat_mem 51) (zofNat_mem 100) (by decide)
  have hWB := zwiden (-132477666909342690576, -132477666909342619576) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (26586232773392929978, 26586232773392994458) (zexp_mem hWB 20 20 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2895109747121106733689, 2895109747121135254525) (FT ((1261:ℝ)/(600:ℝ)) ((95:ℝ)/100) ((((51:ℝ)/(100:ℝ))))) := zwiden (2895109747121106733689, 2895109747121135254525) (zFT_mem (lam := ((95:ℝ)/100)) (z := ((((51:ℝ)/(100:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (635091455727707465081, 635091455727708637498) (fT ((1261:ℝ)/(600:ℝ)) ((95:ℝ)/100) 0 / 6) := zwiden (635091455727707465081, 635091455727708637498) (zC_mem (lam := ((95:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((95:ℝ)/100) ((44:ℝ)/100) = ((1261:ℝ)/(600:ℝ)) := by norm_num [theta13]
  have hzB : ((95:ℝ)/100) - ((44:ℝ)/100) = (((51:ℝ)/(100:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_33 : sideCond ((95:ℝ)/100) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 251) (zofNatI 120)) ((251:ℝ)/(120:ℝ)) := zdiv_mem (zofNat_mem 251) (zofNat_mem 120) (by decide)
  have hθ1 : Real.pi / 2 < ((251:ℝ)/(120:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((251:ℝ)/(120:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 95) (zofNatI 100)) ((95:ℝ)/100) := zdiv_mem (zofNat_mem 95) (zofNat_mem 100) (by decide)
  have hS := zwiden (86738639645398863520, 86738639645398865890) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-49763524719071516136, -49763524719071499267) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-174301639875916847825, -174301639875916783976) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (24764083924656401400, 24764083924656418190) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-86328408761848861394, -86328408761848829770) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-50471832150687197200, -50471832150687163620) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (126318627153038469594, 126318627153038516023) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (353667235211967235278, 353667235211967678018) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5451511617551583168196, 5451511617551665118272) (FT ((251:ℝ)/(120:ℝ)) ((95:ℝ)/100) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5451511617551583168196, 5451511617551665118272) (zFT_mem (lam := ((95:ℝ)/100)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 9) (zofNatI 20)) (((9:ℝ)/(20:ℝ))) := zdiv_mem (zofNat_mem 9) (zofNat_mem 20) (by decide)
  have hWB := zwiden (-113686764437734664421, -113686764437734622634) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (32082237934343012795, 32082237934343654999) (zexp_mem hWB 18 18 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3021947960786002140761, 3021947960786084789019) (FT ((251:ℝ)/(120:ℝ)) ((95:ℝ)/100) ((((9:ℝ)/(20:ℝ))))) := zwiden (3021947960786002140761, 3021947960786084789019) (zFT_mem (lam := ((95:ℝ)/100)) (z := ((((9:ℝ)/(20:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (655088211317349797475, 655088211317350640179) (fT ((251:ℝ)/(120:ℝ)) ((95:ℝ)/100) 0 / 6) := zwiden (655088211317349797475, 655088211317350640179) (zC_mem (lam := ((95:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((95:ℝ)/100) ((5:ℝ)/10) = ((251:ℝ)/(120:ℝ)) := by norm_num [theta13]
  have hzB : ((95:ℝ)/100) - ((5:ℝ)/10) = (((9:ℝ)/(20:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_34 : sideCond ((95:ℝ)/100) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 1247) (zofNatI 600)) ((1247:ℝ)/(600:ℝ)) := zdiv_mem (zofNat_mem 1247) (zofNat_mem 600) (by decide)
  have hθ1 : Real.pi / 2 < ((1247:ℝ)/(600:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1247:ℝ)/(600:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 95) (zofNatI 100)) ((95:ℝ)/100) := zdiv_mem (zofNat_mem 95) (zofNat_mem 100) (by decide)
  have hS := zwiden (87394423661751713879, 87394423661751875982) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-48602620431724177854, -48602620431722435146) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-179814221713672100931, -179814221713665319936) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (23622147128300831081, 23622147128302525085) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-84951960021628413341, -84951960021625209708) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-52755705743398337838, -52755705743394949830) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (141132017355441199338, 141132017355446522435) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (410136634698167268449, 410136634698189262045) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5728567300222177780389, 5728567300229490583211) (FT ((1247:ℝ)/(600:ℝ)) ((95:ℝ)/100) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5728567300222177780389, 5728567300229490583211) (zFT_mem (lam := ((95:ℝ)/100)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 37) (zofNatI 100)) (((37:ℝ)/(100:ℝ))) := zdiv_mem (zofNat_mem 37) (zofNat_mem 100) (by decide)
  have hWB := zwiden (-90032493830198643623, -90032493830195247853) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (40643757114720714170, 40643757114722283057) (zexp_mem hWB 17 17 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3199234939481713467435, 3199234939483936249314) (FT ((1247:ℝ)/(600:ℝ)) ((95:ℝ)/100) ((((37:ℝ)/(100:ℝ))))) := zwiden (3199234939481713467435, 3199234939483936249314) (zFT_mem (lam := ((95:ℝ)/100)) (z := ((((37:ℝ)/(100:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (683989209666399999875, 683989209666491674266) (fT ((1247:ℝ)/(600:ℝ)) ((95:ℝ)/100) 0 / 6) := zwiden (683989209666399999875, 683989209666491674266) (zC_mem (lam := ((95:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((95:ℝ)/100) ((58:ℝ)/100) = ((1247:ℝ)/(600:ℝ)) := by norm_num [theta13]
  have hzB : ((95:ℝ)/100) - ((58:ℝ)/100) = (((37:ℝ)/(100:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_35 : sideCond ((975:ℝ)/1000) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 4259) (zofNatI 2000)) ((4259:ℝ)/(2000:ℝ)) := zdiv_mem (zofNat_mem 4259) (zofNat_mem 2000) (by decide)
  have hθ1 : Real.pi / 2 < ((4259:ℝ)/(2000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((4259:ℝ)/(2000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 975) (zofNatI 1000)) ((975:ℝ)/1000) := zdiv_mem (zofNat_mem 975) (zofNat_mem 1000) (by decide)
  have hS := zwiden (84794298983160106979, 84794298983160109068) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-53008743240662243338, -53008743240662218950) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-159962854803385836188, -159962854803385758649) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (28099268599544524861, 28099268599544550718) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-89896784461405635300, -89896784461405591725) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-43801462800910950278, -43801462800910898564) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (95030523585229790284, 95030523585229836352) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (258649903107365067367, 258649903107365659323) (zexp_mem hWA 17 17 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (4939795846815452522889, 4939795846815558475604) (FT ((4259:ℝ)/(2000:ℝ)) ((975:ℝ)/1000) ((((-87:ℝ)/(250:ℝ))))) := zwiden (4939795846815452522889, 4939795846815558475604) (zFT_mem (lam := ((975:ℝ)/1000)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 627) (zofNatI 1000)) (((627:ℝ)/(1000:ℝ))) := zdiv_mem (zofNat_mem 627) (zofNat_mem 1000) (by decide)
  have hWB := zwiden (-171218788183733067221, -171218788183732984219) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (18047051220555509831, 18047051220555573750) (zexp_mem hWB 22 22 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2662666335680382410981, 2662666335680405024616) (FT ((4259:ℝ)/(2000:ℝ)) ((975:ℝ)/1000) ((((627:ℝ)/(1000:ℝ))))) := zwiden (2662666335680382410981, 2662666335680405024616) (zFT_mem (lam := ((975:ℝ)/1000)) (z := ((((627:ℝ)/(1000:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (601447739758226566206, 601447739758227552119) (fT ((4259:ℝ)/(2000:ℝ)) ((975:ℝ)/1000) 0 / 6) := zwiden (601447739758226566206, 601447739758227552119) (zC_mem (lam := ((975:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((975:ℝ)/1000) ((348:ℝ)/1000) = ((4259:ℝ)/(2000:ℝ)) := by norm_num [theta13]
  have hzB : ((975:ℝ)/1000) - ((348:ℝ)/1000) = (((627:ℝ)/(1000:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_36 : sideCond ((975:ℝ)/1000) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 509) (zofNatI 240)) ((509:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 509) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((509:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((509:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 975) (zofNatI 1000)) ((975:ℝ)/1000) := zdiv_mem (zofNat_mem 975) (zofNat_mem 1000) (by decide)
  have hS := zwiden (85250517863072302859, 85250517863072306898) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-52271877755424016438, -52271877755423992229) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-163090597705237948053, -163090597705237864791) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (27323492040779895799, 27323492040779921109) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-89124092966502141517, -89124092966502096017) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-45353015918440208402, -45353015918440157782) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (106699648211237835611, 106699648211237890343) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (290663624233779665051, 290663624233780024906) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5108775977531932267399, 5108775977532025521917) (FT ((509:ℝ)/(240:ℝ)) ((975:ℝ)/1000) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5108775977531932267399, 5108775977532025521917) (zFT_mem (lam := ((975:ℝ)/1000)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 23) (zofNatI 40)) (((23:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 23) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-153380744303654467368, -153380744303654388691) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (21571278762517650516, 21571278762517729871) (zexp_mem hWB 21 21 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2761607514403632751518, 2761607514403659271539) (FT ((509:ℝ)/(240:ℝ)) ((975:ℝ)/1000) ((((23:ℝ)/(40:ℝ))))) := zwiden (2761607514403632751518, 2761607514403659271539) (zFT_mem (lam := ((975:ℝ)/1000)) (z := ((((23:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (616141566088270399798, 616141566088271473801) (fT ((509:ℝ)/(240:ℝ)) ((975:ℝ)/1000) 0 / 6) := zwiden (616141566088270399798, 616141566088271473801) (zC_mem (lam := ((975:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((975:ℝ)/1000) ((4:ℝ)/10) = ((509:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((975:ℝ)/1000) - ((4:ℝ)/10) = (((23:ℝ)/(40:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_37 : sideCond ((975:ℝ)/1000) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2537) (zofNatI 1200)) ((2537:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2537) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2537:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2537:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 975) (zofNatI 1000)) ((975:ℝ)/1000) := zdiv_mem (zofNat_mem 975) (zofNat_mem 1000) (by decide)
  have hS := zwiden (85597100017850878567, 85597100017850890972) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-51702383586581717314, -51702383586581686454) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-165557357475615295031, -165557357475615172218) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (26731364685340313717, 26731364685340345629) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-88511481980438550550, -88511481980438484892) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-46537270629319372566, -46537270629319308742) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (115257392922086951976, 115257392922087038865) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (316633234537711719836, 316633234537712043807) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5240543456393024914764, 5240543456393148778098) (FT ((2537:ℝ)/(1200:ℝ)) ((975:ℝ)/1000) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5240543456393024914764, 5240543456393148778098) (zFT_mem (lam := ((975:ℝ)/1000)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 107) (zofNatI 200)) (((107:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 107) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-140142511848446740438, -140142511848446634790) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (24624578434578146164, 24624578434578312594) (zexp_mem hWB 20 20 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2840168509643212348408, 2840168509643257263242) (FT ((2537:ℝ)/(1200:ℝ)) ((975:ℝ)/1000) ((((107:ℝ)/(200:ℝ))))) := zwiden (2840168509643212348408, 2840168509643257263242) (zFT_mem (lam := ((975:ℝ)/1000)) (z := ((((107:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (628031168015128332969, 628031168015129937923) (fT ((2537:ℝ)/(1200:ℝ)) ((975:ℝ)/1000) 0 / 6) := zwiden (628031168015128332969, 628031168015129937923) (zC_mem (lam := ((975:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((975:ℝ)/1000) ((44:ℝ)/100) = ((2537:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((975:ℝ)/1000) - ((44:ℝ)/100) = (((107:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_38 : sideCond ((975:ℝ)/1000) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 101) (zofNatI 48)) ((101:ℝ)/(48:ℝ)) := zdiv_mem (zofNat_mem 101) (zofNat_mem 48) (by decide)
  have hθ1 : Real.pi / 2 < ((101:ℝ)/(48:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((101:ℝ)/(48:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 975) (zofNatI 1000)) ((975:ℝ)/1000) := zdiv_mem (zofNat_mem 975) (zofNat_mem 1000) (by decide)
  have hS := zwiden (86109835417360302035, 86109835417360304008) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-50843841754878465437, -50843841754878446723) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-169361386640493386776, -169361386640493320557) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (25850962443951210088, 25850962443951229119) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-87563096909977927112, -87563096909977892876) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-48298075112097579824, -48298075112097541762) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (127426900601654819122, 127426900601654869009) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (357608635681277889782, 357608635681278397004) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5440877653126628670372, 5440877653126718735100) (FT ((101:ℝ)/(48:ℝ)) ((975:ℝ)/1000) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5440877653126628670372, 5440877653126718735100) (zFT_mem (lam := ((975:ℝ)/1000)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 19) (zofNatI 40)) (((19:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 19) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-121055555571572125559, -121055555571572078166) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (29803166023649176485, 29803166023649314705) (zexp_mem hWB 19 19 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2962068902159278823917, 2962068902159310029799) (FT ((101:ℝ)/(48:ℝ)) ((975:ℝ)/1000) ((((19:ℝ)/(40:ℝ))))) := zwiden (2962068902159278823917, 2962068902159310029799) (zFT_mem (lam := ((975:ℝ)/1000)) (z := ((((19:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (646888269703960969642, 646888269703961846843) (fT ((101:ℝ)/(48:ℝ)) ((975:ℝ)/1000) 0 / 6) := zwiden (646888269703960969642, 646888269703961846843) (zC_mem (lam := ((975:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((975:ℝ)/1000) ((5:ℝ)/10) = ((101:ℝ)/(48:ℝ)) := by norm_num [theta13]
  have hzB : ((975:ℝ)/1000) - ((5:ℝ)/10) = (((19:ℝ)/(40:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_39 : sideCond ((975:ℝ)/1000) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2509) (zofNatI 1200)) ((2509:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2509) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2509:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2509:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 975) (zofNatI 1000)) ((975:ℝ)/1000) := zdiv_mem (zofNat_mem 975) (zofNat_mem 1000) (by decide)
  have hS := zwiden (86780079126950229145, 86780079126950419717) (zsin_mem hq1 (by norm_num) 11) (by decide)
  have hC := zwiden (-49691225248732370323, -49691225248730377463) (zcos_mem hq1 (by norm_num) 11) (by decide)
  have hT := zwiden (-174638638295938720544, -174638638295931333170) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (24692178667200593635, 24692178667202574189) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-86244169180002232962, -86244169179998584755) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-50615642665598812730, -50615642665594851622) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (142440159853983726067, 142440159853989753130) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (415537051883510729783, 415537051883535968834) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5712507889760668385247, 5712507889768943091391) (FT ((2509:ℝ)/(1200:ℝ)) ((975:ℝ)/1000) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5712507889760668385247, 5712507889768943091391) (zFT_mem (lam := ((975:ℝ)/1000)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 79) (zofNatI 200)) (((79:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 79) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-97006660590217159460, -97006660590213054821) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (37905778977649935925, 37905778977652162680) (zexp_mem hWB 17 17 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3132310347150734413196, 3132310347153178589353) (FT ((2509:ℝ)/(1200:ℝ)) ((975:ℝ)/1000) ((((79:ℝ)/(200:ℝ))))) := zwiden (3132310347150734413196, 3132310347153178589353) (zFT_mem (lam := ((975:ℝ)/1000)) (z := ((((79:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (674101954469823294737, 674101954469923445219) (fT ((2509:ℝ)/(1200:ℝ)) ((975:ℝ)/1000) 0 / 6) := zwiden (674101954469823294737, 674101954469923445219) (zC_mem (lam := ((975:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((975:ℝ)/1000) ((58:ℝ)/100) = ((2509:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((975:ℝ)/1000) - ((58:ℝ)/100) = (((79:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_40 : sideCond (1) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 1071) (zofNatI 500)) ((1071:ℝ)/(500:ℝ)) := zdiv_mem (zofNat_mem 1071) (zofNat_mem 500) (by decide)
  have hθ1 : Real.pi / 2 < ((1071:ℝ)/(500:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1071:ℝ)/(500:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem zoneI (1) := zone_mem
  have hS := zwiden (84125082479616007685, 84125082479616010098) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-54064503121713848219, -54064503121713820157) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-155601323645253328001, -155601323645253242772) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (29229704977978034048, 29229704977978064392) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-90963615686672694743, -90963615686672644919) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-41540590044043931904, -41540590044043871216) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (95811010155598913755, 95811010155598966238) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (260676529350412173064, 260676529350412853212) (zexp_mem hWA 17 17 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (4944626776101830093677, 4944626776101950973680) (FT ((1071:ℝ)/(500:ℝ)) (1) ((((-87:ℝ)/(250:ℝ))))) := zwiden (4944626776101830093677, 4944626776101950973680) (zFT_mem (lam := (1)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 163) (zofNatI 250)) (((163:ℝ)/(250:ℝ))) := zdiv_mem (zofNat_mem 163) (zofNat_mem 250) (by decide)
  have hWB := zwiden (-179507984544398063181, -179507984544397964852) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (16611418835618368636, 16611418835618523399) (zexp_mem hWB 22 22 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2618479747272541092203, 2618479747272571664660) (FT ((1071:ℝ)/(500:ℝ)) (1) ((((163:ℝ)/(250:ℝ))))) := zwiden (2618479747272541092203, 2618479747272571664660) (zFT_mem (lam := (1)) (z := ((((163:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (596582898622253344518, 596582898622254435750) (fT ((1071:ℝ)/(500:ℝ)) (1) 0 / 6) := zwiden (596582898622253344518, 596582898622254435750) (zC_mem (lam := (1)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 (1) ((348:ℝ)/1000) = ((1071:ℝ)/(500:ℝ)) := by norm_num [theta13]
  have hzB : (1) - ((348:ℝ)/1000) = (((163:ℝ)/(250:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_41 : sideCond (1) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 32) (zofNatI 15)) ((32:ℝ)/(15:ℝ)) := zdiv_mem (zofNat_mem 32) (zofNat_mem 15) (by decide)
  have hθ1 : Real.pi / 2 < ((32:ℝ)/(15:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((32:ℝ)/(15:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem zoneI (1) := zone_mem
  have hS := zwiden (84590476296594583797, 84590476296594586117) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-53333397790833392596, -53333397790833366996) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-158606951367222853497, -158606951367222773014) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (28444513199152694711, 28444513199152722018) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-90229950432846843208, -90229950432846797422) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-43110973601694610578, -43110973601694555964) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (107603522541406108177, 107603522541406162798) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (293302767421374214223, 293302767421374608114) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5111149930659758742834, 5111149930659854760351) (FT ((32:ℝ)/(15:ℝ)) (1) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5111149930659758742834, 5111149930659854760351) (zFT_mem (lam := (1)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 3) (zofNatI 5)) (((3:ℝ)/(5:ℝ))) := zdiv_mem (zofNat_mem 3) (zofNat_mem 5) (by decide)
  have hWB := zwiden (-161405283812109244197, -161405283812109162267) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (19907914134406846171, 19907914134407044473) (zexp_mem hWB 21 21 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2713809035352616778033, 2713809035352651499286) (FT ((32:ℝ)/(15:ℝ)) (1) ((((3:ℝ)/(5:ℝ))))) := zwiden (2713809035352616778033, 2713809035352651499286) (zFT_mem (lam := (1)) (z := ((((3:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (610471984811106114171, 610471984811107157789) (fT ((32:ℝ)/(15:ℝ)) (1) 0 / 6) := zwiden (610471984811106114171, 610471984811107157789) (zC_mem (lam := (1)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 (1) ((4:ℝ)/10) = ((32:ℝ)/(15:ℝ)) := by norm_num [theta13]
  have hzB : (1) - ((4:ℝ)/10) = (((3:ℝ)/(5:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_42 : sideCond (1) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 319) (zofNatI 150)) ((319:ℝ)/(150:ℝ)) := zdiv_mem (zofNat_mem 319) (zofNat_mem 150) (by decide)
  have hθ1 : Real.pi / 2 < ((319:ℝ)/(150:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((319:ℝ)/(150:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem zoneI (1) := zone_mem
  have hS := zwiden (84944149866724641793, 84944149866724645172) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-52768280277259615433, -52768280277259590490) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-160975778290298379058, -160975778290298296561) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (27844914034194234841, 27844914034194261166) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-89647134161617421694, -89647134161617375752) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-44310171931611530318, -44310171931611477668) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (116257656061256977059, 116257656061257036817) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (319816293010048081473, 319816293010048330153) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5240907112944714617783, 5240907112944803436945) (FT ((319:ℝ)/(150:ℝ)) (1) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5240907112944714617783, 5240907112944803436945) (zFT_mem (lam := (1)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 14) (zofNatI 25)) (((14:ℝ)/(25:ℝ))) := zdiv_mem (zofNat_mem 14) (zofNat_mem 25) (by decide)
  have hWB := zwiden (-147964289532508955948, -147964289532508879893) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (22771899338285095197, 22771899338285528518) (zexp_mem hWB 20 20 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2789467235991647492539, 2789467235991703791743) (FT ((319:ℝ)/(150:ℝ)) (1) ((((14:ℝ)/(25:ℝ))))) := zwiden (2789467235991647492539, 2789467235991703791743) (zFT_mem (lam := (1)) (z := ((((14:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (621702248715768329082, 621702248715769410247) (fT ((319:ℝ)/(150:ℝ)) (1) 0 / 6) := zwiden (621702248715768329082, 621702248715769410247) (zC_mem (lam := (1)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 (1) ((44:ℝ)/100) = ((319:ℝ)/(150:ℝ)) := by norm_num [theta13]
  have hzB : (1) - ((44:ℝ)/100) = (((14:ℝ)/(25:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_43 : sideCond (1) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 127) (zofNatI 60)) ((127:ℝ)/(60:ℝ)) := zdiv_mem (zofNat_mem 127) (zofNat_mem 60) (by decide)
  have hθ1 : Real.pi / 2 < ((127:ℝ)/(60:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((127:ℝ)/(60:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem zoneI (1) := zone_mem
  have hS := zwiden (85467576702727773811, 85467576702727776143) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-51916214543852737779, -51916214543852716162) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-164625979481872301442, -164625979481872228400) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (26952933325633442892, 26952933325633465339) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-88743060972840103822, -88743060972840064449) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-46094133348733114216, -46094133348733069322) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (128574279304424259692, 128574279304424316819) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (361735390486143057241, 361735390486143653758) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5438018474074898417163, 5438018474075002362431) (FT ((127:ℝ)/(60:ℝ)) (1) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5438018474074898417163, 5438018474075002362431) (zFT_mem (lam := (1)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI zoneI (zofNatI 2)) (((1:ℝ)/(2:ℝ))) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hWB := zwiden (-128574279304424316819, -128574279304424259692) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (27644516580367651667, 27644516580368057327) (zexp_mem hWB 19 19 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2906802173790255951447, 2906802173790312920438) (FT ((127:ℝ)/(60:ℝ)) (1) ((((1:ℝ)/(2:ℝ))))) := zwiden (2906802173790255951447, 2906802173790312920438) (zFT_mem (lam := (1)) (z := ((((1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (639498212591174580072, 639498212591175552165) (fT ((127:ℝ)/(60:ℝ)) (1) 0 / 6) := zwiden (639498212591174580072, 639498212591175552165) (zC_mem (lam := (1)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 (1) ((5:ℝ)/10) = ((127:ℝ)/(60:ℝ)) := by norm_num [theta13]
  have hzB : (1) - ((5:ℝ)/10) = (((1:ℝ)/(2:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_44 : sideCond (1) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 631) (zofNatI 300)) ((631:ℝ)/(300:ℝ)) := zdiv_mem (zofNat_mem 631) (zofNat_mem 300) (by decide)
  have hθ1 : Real.pi / 2 < ((631:ℝ)/(300:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((631:ℝ)/(300:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem zoneI (1) := zone_mem
  have hS := zwiden (86152175381338768000, 86152175381338772161) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-50772065912891980519, -50772065912891959841) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-169684202981118309895, -169684202981118232590) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (25778026770630456794, 25778026770630477792) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-87482478540007238742, -87482478540007198887) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-48443946458739086412, -48443946458739044416) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (143788674714650012755, 143788674714650078699) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (421178583735335749653, 421178583735336262071) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5704936886952712213762, 5704936886952815804076) (FT ((631:ℝ)/(300:ℝ)) (1) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5704936886952712213762, 5704936886952815804076) (zFT_mem (lam := (1)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 21) (zofNatI 50)) (((21:ℝ)/(50:ℝ))) := zdiv_mem (zofNat_mem 21) (zofNat_mem 50) (by decide)
  have hWB := zwiden (-104122833414056953541, -104122833414056905788) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (35302078804369481935, 35302078804369628099) (zexp_mem hWB 18 18 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3070541592934299419139, 3070541592934338228739) (FT ((631:ℝ)/(300:ℝ)) (1) ((((21:ℝ)/(50:ℝ))))) := zwiden (3070541592934299419139, 3070541592934338228739) (zFT_mem (lam := (1)) (z := ((((21:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (665146400082781289006, 665146400082782341956) (fT ((631:ℝ)/(300:ℝ)) (1) 0 / 6) := zwiden (665146400082781289006, 665146400082782341956) (zC_mem (lam := (1)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 (1) ((58:ℝ)/100) = ((631:ℝ)/(300:ℝ)) := by norm_num [theta13]
  have hzB : (1) - ((58:ℝ)/100) = (((21:ℝ)/(50:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_45 : sideCond ((1025:ℝ)/1000) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 4309) (zofNatI 2000)) ((4309:ℝ)/(2000:ℝ)) := zdiv_mem (zofNat_mem 4309) (zofNat_mem 2000) (by decide)
  have hθ1 : Real.pi / 2 < ((4309:ℝ)/(2000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((4309:ℝ)/(2000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1025) (zofNatI 1000)) ((1025:ℝ)/1000) := zdiv_mem (zofNat_mem 1025) (zofNat_mem 1000) (by decide)
  have hS := zwiden (83442721603086495374, 83442721603086498167) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-55111815534146626147, -55111815534146593877) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-151406228944474580166, -151406228944474486443) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (30373122114698018145, 30373122114698053715) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-91973597613129094736, -91973597613129037803) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-39253755770603963710, -39253755770603892570) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (96624693645662390346, 96624693645662450162) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (262806264131898110865, 262806264131898895408) (zexp_mem hWA 17 17 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (4955864650412090246884, 4955864650412228505641) (FT ((4309:ℝ)/(2000:ℝ)) ((1025:ℝ)/1000) ((((-87:ℝ)/(250:ℝ))))) := zwiden (4955864650412090246884, 4955864650412228505641) (zFT_mem (lam := ((1025:ℝ)/1000)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 677) (zofNatI 1000)) (((677:ℝ)/(1000:ℝ))) := zdiv_mem (zofNat_mem 677) (zofNat_mem 1000) (by decide)
  have hWB := zwiden (-187973901144004249309, -187973901144004132944) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (15262993522614086818, 15262993522614135781) (zexp_mem hWB 23 23 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2577754956874310350045, 2577754956874335339936) (FT ((4309:ℝ)/(2000:ℝ)) ((1025:ℝ)/1000) ((((677:ℝ)/(1000:ℝ))))) := zwiden (2577754956874310350045, 2577754956874335339936) (zFT_mem (lam := ((1025:ℝ)/1000)) (z := ((((677:ℝ)/(1000:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (592316551939272114384, 592316551939273323261) (fT ((4309:ℝ)/(2000:ℝ)) ((1025:ℝ)/1000) 0 / 6) := zwiden (592316551939272114384, 592316551939273323261) (zC_mem (lam := ((1025:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1025:ℝ)/1000) ((348:ℝ)/1000) = ((4309:ℝ)/(2000:ℝ)) := by norm_num [theta13]
  have hzB : ((1025:ℝ)/1000) - ((348:ℝ)/1000) = (((677:ℝ)/(1000:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_46 : sideCond ((1025:ℝ)/1000) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 103) (zofNatI 48)) ((103:ℝ)/(48:ℝ)) := zdiv_mem (zofNat_mem 103) (zofNat_mem 48) (by decide)
  have hθ1 : Real.pi / 2 < ((103:ℝ)/(48:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((103:ℝ)/(48:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1025) (zofNatI 1000)) ((1025:ℝ)/1000) := zdiv_mem (zofNat_mem 1025) (zofNat_mem 1000) (by decide)
  have hS := zwiden (83917217640294388902, 83917217640294391877) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-54386584591344463045, -54386584591344433316) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-154297642094719305432, -154297642094719215616) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (29579005835114637406, 29579005835114669744) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-91279417117282694686, -91279417117282641554) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-40841988329770725188, -40841988329770660512) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (108543249607104530690, 108543249607104593927) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (296072004165932495420, 296072004165932955923) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5120302348725893593421, 5120302348726005037771) (FT ((103:ℝ)/(48:ℝ)) ((1025:ℝ)/1000) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5120302348725893593421, 5120302348726005037771) (zFT_mem (lam := ((1025:ℝ)/1000)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 5) (zofNatI 8)) (((5:ℝ)/(8:ℝ))) := zdiv_mem (zofNat_mem 5) (zofNat_mem 8) (by decide)
  have hWB := zwiden (-169598827511100928011, -169598827511100829203) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (18341787210929410079, 18341787210929467911) (zexp_mem hWB 22 22 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2669729835487097925815, 2669729835487124013818) (FT ((103:ℝ)/(48:ℝ)) ((1025:ℝ)/1000) ((((5:ℝ)/(8:ℝ))))) := zwiden (2669729835487097925815, 2669729835487124013818) (zFT_mem (lam := ((1025:ℝ)/1000)) (z := ((((5:ℝ)/(8:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (605450759463295336490, 605450759463296509036) (fT ((103:ℝ)/(48:ℝ)) ((1025:ℝ)/1000) 0 / 6) := zwiden (605450759463295336490, 605450759463296509036) (zC_mem (lam := ((1025:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1025:ℝ)/1000) ((4:ℝ)/10) = ((103:ℝ)/(48:ℝ)) := by norm_num [theta13]
  have hzB : ((1025:ℝ)/1000) - ((4:ℝ)/10) = (((5:ℝ)/(8:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_47 : sideCond ((1025:ℝ)/1000) ((44:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2567) (zofNatI 1200)) ((2567:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2567) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2567:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2567:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1025) (zofNatI 1000)) ((1025:ℝ)/1000) := zdiv_mem (zofNat_mem 1025) (zofNat_mem 1000) (by decide)
  have hS := zwiden (84277927365000134475, 84277927365000147864) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-53825932031500984143, -53825932031500946205) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-156574952228746464422, -156574952228746329188) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (28972309590597595777, 28972309590597636619) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-90726759802085495849, -90726759802085417488) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-42055380818804808446, -42055380818804726762) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (117295443452881497860, 117295443452881600579) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (323152588056669367351, 323152588056669767438) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5248346999040287565872, 5248346999040435481755) (FT ((2567:ℝ)/(1200:ℝ)) ((1025:ℝ)/1000) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5248346999040287565872, 5248346999040435481755) (zFT_mem (lam := ((1025:ℝ)/1000)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 117) (zofNatI 200)) (((117:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 117) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-155949623681672128043, -155949623681671991473) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (21024195668527937483, 21024195668528054610) (zexp_mem hWB 21 21 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2742695216198511848476, 2742695216198554816038) (FT ((2567:ℝ)/(1200:ℝ)) ((1025:ℝ)/1000) ((((117:ℝ)/(200:ℝ))))) := zwiden (2742695216198511848476, 2742695216198554816038) (zFT_mem (lam := ((1025:ℝ)/1000)) (z := ((((117:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (616063937406201489876, 616063937406203277103) (fT ((2567:ℝ)/(1200:ℝ)) ((1025:ℝ)/1000) 0 / 6) := zwiden (616063937406201489876, 616063937406203277103) (zC_mem (lam := ((1025:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1025:ℝ)/1000) ((44:ℝ)/100) = ((2567:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1025:ℝ)/1000) - ((44:ℝ)/100) = (((117:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_48 : sideCond ((1025:ℝ)/1000) ((5:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 511) (zofNatI 240)) ((511:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 511) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((511:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((511:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1025) (zofNatI 1000)) ((1025:ℝ)/1000) := zdiv_mem (zofNat_mem 1025) (zofNat_mem 1000) (by decide)
  have hS := zwiden (84811963853118767881, 84811963853118772142) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-52980475529927793026, -52980475529927766608) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-160081545144323857436, -160081545144323769569) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (28069307873772748619, 28069307873772776613) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-89867563511305592128, -89867563511305542801) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-43861384252454502762, -43861384252454446774) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (129761102098618631766, 129761102098618703306) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (366054125729469102202, 366054125729469828304) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5442702452483079814358, 5442702452483208039318) (FT ((511:ℝ)/(240:ℝ)) ((1025:ℝ)/1000) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5442702452483079814358, 5442702452483208039318) (zFT_mem (lam := ((1025:ℝ)/1000)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 21) (zofNatI 40)) (((21:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 21) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-136249157203549638471, -136249157203549563355) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (25602208414407411110, 25602208414407510278) (zexp_mem hWB 20 20 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2855800275665957141937, 2855800275665989347896) (FT ((511:ℝ)/(240:ℝ)) ((1025:ℝ)/1000) ((((21:ℝ)/(40:ℝ))))) := zwiden (2855800275665957141937, 2855800275665989347896) (zFT_mem (lam := ((1025:ℝ)/1000)) (z := ((((21:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (632869227120916244671, 632869227120917420863) (fT ((511:ℝ)/(240:ℝ)) ((1025:ℝ)/1000) 0 / 6) := zwiden (632869227120916244671, 632869227120917420863) (zC_mem (lam := ((1025:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1025:ℝ)/1000) ((5:ℝ)/10) = ((511:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((1025:ℝ)/1000) - ((5:ℝ)/10) = (((21:ℝ)/(40:ℝ))) := by norm_num

  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_49 : sideCond ((1025:ℝ)/1000) ((58:ℝ)/100) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2539) (zofNatI 1200)) ((2539:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2539) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2539:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2539:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1025) (zofNatI 1000)) ((1025:ℝ)/1000) := zdiv_mem (zofNat_mem 1025) (zofNat_mem 1000) (by decide)
  have hS := zwiden (85510810533600101726, 85510810533600114191) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-51844973545048196570, -51844973545048165293) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-164935585239135398778, -164935585239135275232) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (26879012818867441237, 26879012818867473669) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-88666114198602531633, -88666114198602465216) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-46241974362265117526, -46241974362265052662) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (145178134940918133439, 145178134940918243934) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (427071537957942166926, 427071537957942923260) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5705571473768809130116, 5705571473768973783778) (FT ((2539:ℝ)/(1200:ℝ)) ((1025:ℝ)/1000) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5705571473768809130116, 5705571473768973783778) (zFT_mem (lam := ((1025:ℝ)/1000)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 89) (zofNatI 200)) (((89:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 89) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-111386672497773480260, -111386672497773395484) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (32828710774695866772, 32828710774696329853) (zexp_mem hWB 18 18 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (3013526537982572098505, 3013526537982656317260) (FT ((2539:ℝ)/(1200:ℝ)) ((1025:ℝ)/1000) ((((89:ℝ)/(200:ℝ))))) := zwiden (3013526537982572098505, 3013526537982656317260) (zFT_mem (lam := ((1025:ℝ)/1000)) (z := ((((89:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (657060964817447876774, 657060964817449569483) (fT ((2539:ℝ)/(1200:ℝ)) ((1025:ℝ)/1000) 0 / 6) := zwiden (657060964817447876774, 657060964817449569483) (zC_mem (lam := ((1025:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1025:ℝ)/1000) ((58:ℝ)/100) = ((2539:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1025:ℝ)/1000) - ((58:ℝ)/100) = (((89:ℝ)/(200:ℝ))) := by norm_num

  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_50 : sideCond ((105:ℝ)/100) ((348:ℝ)/1000) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 2167) (zofNatI 1000)) ((2167:ℝ)/(1000:ℝ)) := zdiv_mem (zofNat_mem 2167) (zofNat_mem 1000) (by decide)
  have hθ1 : Real.pi / 2 < ((2167:ℝ)/(1000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2167:ℝ)/(1000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 105) (zofNatI 100)) ((105:ℝ)/100) := zdiv_mem (zofNat_mem 105) (zofNat_mem 100) (by decide)
  have hS := zwiden (82747322971070268258, 82747322971070271484) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-56150516837526886025, -56150516837526848951) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-147366983656627869405, -147366983656627766357) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (31528805411213861663, 31528805411213903299) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-92926099034947131020, -92926099034947066040) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-36942389177572276674, -36942389177572193402) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (97471726225891682909, 97471726225891751070) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (265041773191213663364, 265041773191214571700) (zexp_mem hWA 17 17 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (4973398855318492125502, 4973398855318650595065) (FT ((2167:ℝ)/(1000:ℝ)) ((105:ℝ)/100) ((((-87:ℝ)/(250:ℝ))))) := zwiden (4973398855318492125502, 4973398855318650595065) (zFT_mem (lam := ((105:ℝ)/100)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 351) (zofNatI 500)) (((351:ℝ)/(500:ℝ))) := zdiv_mem (zofNat_mem 351) (zofNat_mem 500) (by decide)
  have hWB := zwiden (-196623999455678187503, -196623999455678050007) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (13998220178568718383, 13998220178568825399) (zexp_mem hWB 23 23 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2540259499584097568098, 2540259499584128426362) (FT ((2167:ℝ)/(1000:ℝ)) ((105:ℝ)/100) ((((351:ℝ)/(500:ℝ))))) := zwiden (2540259499584097568098, 2540259499584128426362) (zFT_mem (lam := ((105:ℝ)/100)) (z := ((((351:ℝ)/(500:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (588621642806007642452, 588621642806008982089) (fT ((2167:ℝ)/(1000:ℝ)) ((105:ℝ)/100) 0 / 6) := zwiden (588621642806007642452, 588621642806008982089) (zC_mem (lam := ((105:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((105:ℝ)/100) ((348:ℝ)/1000) = ((2167:ℝ)/(1000:ℝ)) := by norm_num [theta13]
  have hzB : ((105:ℝ)/100) - ((348:ℝ)/1000) = (((351:ℝ)/(500:ℝ))) := by norm_num

  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

theorem side_51 : sideCond ((105:ℝ)/100) ((4:ℝ)/10) := by
  unfold sideCond
  have hq1 : zMem (zdivI (zofNatI 259) (zofNatI 120)) ((259:ℝ)/(120:ℝ)) := zdiv_mem (zofNat_mem 259) (zofNat_mem 120) (by decide)
  have hθ1 : Real.pi / 2 < ((259:ℝ)/(120:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((259:ℝ)/(120:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 105) (zofNatI 100)) ((105:ℝ)/100) := zdiv_mem (zofNat_mem 105) (zofNat_mem 100) (by decide)
  have hS := zwiden (83230847089467024909, 83230847089467028966) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-55431273598662349980, -55431273598662315197) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-150151424793305816732, -150151424793305715192) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (30726260927697578153, 30726260927697616716) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-92271837137293536331, -92271837137293473932) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-38547478144604843694, -38547478144604766568) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (109519070279095914150, 109519070279095988346) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (298975278323185822876, 298975278323186365745) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5136101095391668332794, 5136101095391799260377) (FT ((259:ℝ)/(120:ℝ)) ((105:ℝ)/100) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5136101095391668332794, 5136101095391799260377) (zFT_mem (lam := ((105:ℝ)/100)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 13) (zofNatI 20)) (((13:ℝ)/(20:ℝ))) := zdiv_mem (zofNat_mem 13) (zofNat_mem 20) (by decide)
  have hWB := zwiden (-177968489203530981062, -177968489203530860494) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (16869129486512532217, 16869129486512667092) (zexp_mem hWB 22 22 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2629113077255602536109, 2629113077255636785544) (FT ((259:ℝ)/(120:ℝ)) ((105:ℝ)/100) ((((13:ℝ)/(20:ℝ))))) := zwiden (2629113077255602536109, 2629113077255636785544) (zFT_mem (lam := ((105:ℝ)/100)) (z := ((((13:ℝ)/(20:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (601045891021575529899, 601045891021576865250) (fT ((259:ℝ)/(120:ℝ)) ((105:ℝ)/100) 0 / 6) := zwiden (601045891021575529899, 601045891021576865250) (zC_mem (lam := ((105:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((105:ℝ)/100) ((4:ℝ)/10) = ((259:ℝ)/(120:ℝ)) := by norm_num [theta13]
  have hzB : ((105:ℝ)/100) - ((4:ℝ)/10) = (((13:ℝ)/(20:ℝ))) := by norm_num

  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hθe, hzB, hzA]
  exact zside hA hB hc (by decide)

end Work.LinnikAreas2
