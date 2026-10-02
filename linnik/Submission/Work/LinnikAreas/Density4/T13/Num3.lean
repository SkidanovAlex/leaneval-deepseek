import Mathlib
import Submission.Work.LinnikAreas.Density4.T13.Basic
import Submission.Work.LinnikAreas.Density4.t13_sin_cos_taylor

open scoped BigOperators
noncomputable section
namespace Work.LinnikAreas.Density4

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

/-- row 52: λ = (105:ℝ)/100, λ₁ = (44:ℝ)/100, N₀ = 21 -/
theorem row_52 : bnd13 ((105:ℝ)/100) ((44:ℝ)/100) < ((21 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 1291) (zofNatI 600)) ((1291:ℝ)/(600:ℝ)) := zdiv_mem (zofNat_mem 1291) (zofNat_mem 600) (by decide)
  have hθ1 : Real.pi / 2 < ((1291:ℝ)/(600:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1291:ℝ)/(600:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 105) (zofNatI 100)) ((105:ℝ)/100) := zdiv_mem (zofNat_mem 105) (zofNat_mem 100) (by decide)
  have hS := zwiden (83598536608587843133, 83598536608587851463) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-54875173593370991745, -54875173593370955001) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-152343092758228182872, -152343092758228065683) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (30112846769025969697, 30112846769026010025) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-91749684170960764212, -91749684170960693634) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-39774306461948060606, -39774306461947979950) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (118371076407347612287, 118371076407347704057) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (326647285149572899248, 326647285149573280058) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5262713115233827132850, 5262713115233962425272) (FT ((1291:ℝ)/(600:ℝ)) ((105:ℝ)/100) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5262713115233827132850, 5262713115233962425272) (zFT_mem (lam := ((105:ℝ)/100)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 61) (zofNatI 100)) (((61:ℝ)/(100:ℝ))) := zdiv_mem (zofNat_mem 61) (zofNat_mem 100) (by decide)
  have hWB := zwiden (-164105355928368407897, -164105355928368280670) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (19377578043636678266, 19377578043636960753) (zexp_mem hWB 21 21 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2699575539553268932162, 2699575539553319823687) (FT ((1291:ℝ)/(600:ℝ)) ((105:ℝ)/100) ((((61:ℝ)/(100:ℝ))))) := zwiden (2699575539553268932162, 2699575539553319823687) (zFT_mem (lam := ((105:ℝ)/100)) (z := ((((61:ℝ)/(100:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (611080004995539116718, 611080004995540673687) (fT ((1291:ℝ)/(600:ℝ)) ((105:ℝ)/100) 0 / 6) := zwiden (611080004995539116718, 611080004995540673687) (zC_mem (lam := ((105:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((105:ℝ)/100) ((44:ℝ)/100) = ((1291:ℝ)/(600:ℝ)) := by norm_num [theta13]
  have hzB : ((105:ℝ)/100) - ((44:ℝ)/100) = (((61:ℝ)/(100:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 21 (by decide)

/-- row 53: λ = (105:ℝ)/100, λ₁ = (5:ℝ)/10, N₀ = 19 -/
theorem row_53 : bnd13 ((105:ℝ)/100) ((5:ℝ)/10) < ((19 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 257) (zofNatI 120)) ((257:ℝ)/(120:ℝ)) := zdiv_mem (zofNat_mem 257) (zofNat_mem 120) (by decide)
  have hθ1 : Real.pi / 2 < ((257:ℝ)/(120:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((257:ℝ)/(120:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 105) (zofNatI 100)) ((105:ℝ)/100) := zdiv_mem (zofNat_mem 105) (zofNat_mem 100) (by decide)
  have hS := zwiden (84143099306707196851, 84143099306707200369) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-54036458424489788369, -54036458424489759327) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-155715422068765462004, -155715422068765371803) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (29199388390616102827, 29199388390616134215) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-90935901747891983370, -90935901747891930693) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-41601223218767794346, -41601223218767731570) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (130987831043594115542, 130987831043594191579) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (370572273698687888290, 370572273698688206435) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5454750478557697674667, 5454750478557806057488) (FT ((257:ℝ)/(120:ℝ)) ((105:ℝ)/100) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5454750478557697674667, 5454750478557806057488) (zFT_mem (lam := ((105:ℝ)/100)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 11) (zofNatI 20)) (((11:ℝ)/(20:ℝ))) := zdiv_mem (zofNat_mem 11) (zofNat_mem 20) (by decide)
  have hWB := zwiden (-144086614147953610737, -144086614147953527096) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (23672263456874707142, 23672263456874971538) (zexp_mem hWB 20 20 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2808753853444431832824, 2808753853444478344509) (FT ((257:ℝ)/(120:ℝ)) ((105:ℝ)/100) ((((11:ℝ)/(20:ℝ))))) := zwiden (2808753853444431832824, 2808753853444478344509) (zFT_mem (lam := ((105:ℝ)/100)) (z := ((((11:ℝ)/(20:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (626957941641237089938, 626957941641238303673) (fT ((257:ℝ)/(120:ℝ)) ((105:ℝ)/100) 0 / 6) := zwiden (626957941641237089938, 626957941641238303673) (zC_mem (lam := ((105:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((105:ℝ)/100) ((5:ℝ)/10) = ((257:ℝ)/(120:ℝ)) := by norm_num [theta13]
  have hzB : ((105:ℝ)/100) - ((5:ℝ)/10) = (((11:ℝ)/(20:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 19 (by decide)

/-- row 54: λ = (105:ℝ)/100, λ₁ = (58:ℝ)/100, N₀ = 17 -/
theorem row_54 : bnd13 ((105:ℝ)/100) ((58:ℝ)/100) < ((17 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 1277) (zofNatI 600)) ((1277:ℝ)/(600:ℝ)) := zdiv_mem (zofNat_mem 1277) (zofNat_mem 600) (by decide)
  have hθ1 : Real.pi / 2 < ((1277:ℝ)/(600:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1277:ℝ)/(600:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 105) (zofNatI 100)) ((105:ℝ)/100) := zdiv_mem (zofNat_mem 105) (zofNat_mem 100) (by decide)
  have hS := zwiden (84856084795686850847, 84856084795686858349) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-52909780505566311308, -52909780505566281949) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-160378825965380296200, -160378825965380193028) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (27994448731472017622, 27994448731472048691) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-89794336422030288127, -89794336422030230362) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-44011102537055964756, -44011102537055902618) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (146609228066624212422, 146609228066624307621) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (433227271460092873005, 433227271460093631526) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5714188936702945132578, 5714188936703094864409) (FT ((1277:ℝ)/(600:ℝ)) ((105:ℝ)/100) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5714188936702945132578, 5714188936703094864409) (zFT_mem (lam := ((105:ℝ)/100)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 47) (zofNatI 100)) (((47:ℝ)/(100:ℝ))) := zdiv_mem (zofNat_mem 47) (zofNat_mem 100) (by decide)
  have hWB := zwiden (-118804029640195559624, -118804029640195482480) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (30481803212576566848, 30481803212576677231) (zexp_mem hWB 19 19 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2960907774835414502696, 2960907774835455120809) (FT ((1277:ℝ)/(600:ℝ)) ((105:ℝ)/100) ((((47:ℝ)/(100:ℝ))))) := zwiden (2960907774835414502696, 2960907774835455120809) (zFT_mem (lam := ((105:ℝ)/100)) (z := ((((47:ℝ)/(100:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (649791007188363823337, 649791007188365241337) (fT ((1277:ℝ)/(600:ℝ)) ((105:ℝ)/100) 0 / 6) := zwiden (649791007188363823337, 649791007188365241337) (zC_mem (lam := ((105:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((105:ℝ)/100) ((58:ℝ)/100) = ((1277:ℝ)/(600:ℝ)) := by norm_num [theta13]
  have hzB : ((105:ℝ)/100) - ((58:ℝ)/100) = (((47:ℝ)/(100:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 17 (by decide)

/-- row 55: λ = (1075:ℝ)/1000, λ₁ = (348:ℝ)/1000, N₀ = 28 -/
theorem row_55 : bnd13 ((1075:ℝ)/1000) ((348:ℝ)/1000) < ((28 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 4359) (zofNatI 2000)) ((4359:ℝ)/(2000:ℝ)) := zdiv_mem (zofNat_mem 4359) (zofNat_mem 2000) (by decide)
  have hθ1 : Real.pi / 2 < ((4359:ℝ)/(2000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((4359:ℝ)/(2000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1075) (zofNatI 1000)) ((1075:ℝ)/1000) := zdiv_mem (zofNat_mem 1075) (zofNat_mem 1000) (by decide)
  have hS := zwiden (82038995238188794087, 82038995238188797807) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-57180444736889206974, -57180444736889164415) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-143473867011150557059, -143473867011150443766) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (32696032603084357430, 32696032603084406102) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-93820524669743427129, -93820524669743353044) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-34607934793831285140, -34607934793831187796) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (98352373451679012388, 98352373451679090054) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (267386163968794123776, 267386163968794377796) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (4997156580996964299411, 4997156580997089338281) (FT ((4359:ℝ)/(2000:ℝ)) ((1075:ℝ)/1000) ((((-87:ℝ)/(250:ℝ))))) := zwiden (4997156580996964299411, 4997156580997089338281) (zFT_mem (lam := ((1075:ℝ)/1000)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 727) (zofNatI 1000)) (((727:ℝ)/(1000:ℝ))) := zdiv_mem (zofNat_mem 727) (zofNat_mem 1000) (by decide)
  have hWB := zwiden (-205466021549915800199, -205466021549915637949) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (12813636693295062110, 12813636693295324250) (zexp_mem hWB 23 23 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2505785653075827586116, 2505785653075870600313) (FT ((4359:ℝ)/(2000:ℝ)) ((1075:ℝ)/1000) ((((727:ℝ)/(1000:ℝ))))) := zwiden (2505785653075827586116, 2505785653075870600313) (zFT_mem (lam := ((1075:ℝ)/1000)) (z := ((((727:ℝ)/(1000:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (585474220486327698341, 585474220486329183446) (fT ((4359:ℝ)/(2000:ℝ)) ((1075:ℝ)/1000) 0 / 6) := zwiden (585474220486327698341, 585474220486329183446) (zC_mem (lam := ((1075:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1075:ℝ)/1000) ((348:ℝ)/1000) = ((4359:ℝ)/(2000:ℝ)) := by norm_num [theta13]
  have hzB : ((1075:ℝ)/1000) - ((348:ℝ)/1000) = (((727:ℝ)/(1000:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 28 (by decide)

/-- row 56: λ = (1075:ℝ)/1000, λ₁ = (4:ℝ)/10, N₀ = 26 -/
theorem row_56 : bnd13 ((1075:ℝ)/1000) ((4:ℝ)/10) < ((26 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 521) (zofNatI 240)) ((521:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 521) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((521:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((521:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1075) (zofNatI 1000)) ((1075:ℝ)/1000) := zdiv_mem (zofNat_mem 1075) (zofNat_mem 1000) (by decide)
  have hS := zwiden (82531471888114641432, 82531471888114647115) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-56467301582255074129, -56467301582255033192) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-146157988031165869592, -146157988031165753567) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (31885561479813417750, 31885561479813463983) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-93206590262671527667, -93206590262671453676) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-36228877040373164500, -36228877040373072034) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (110531343358702481738, 110531343358702569751) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (302017094348258464979, 302017094348259109655) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5158455218873694829510, 5158455218873850223603) (FT ((521:ℝ)/(240:ℝ)) ((1075:ℝ)/1000) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5158455218873694829510, 5158455218873850223603) (zFT_mem (lam := ((1075:ℝ)/1000)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 27) (zofNatI 40)) (((27:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 27) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-186521641917810586454, -186521641917810437935) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (15486269100166738056, 15486269100166787168) (zexp_mem hWB 23 23 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2591729399679366224455, 2591729399679397660604) (FT ((521:ℝ)/(240:ℝ)) ((1075:ℝ)/1000) ((((27:ℝ)/(40:ℝ))))) := zwiden (2591729399679366224455, 2591729399679397660604) (zFT_mem (lam := ((1075:ℝ)/1000)) (z := ((((27:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (597228999327824930506, 597228999327826468430) (fT ((521:ℝ)/(240:ℝ)) ((1075:ℝ)/1000) 0 / 6) := zwiden (597228999327824930506, 597228999327826468430) (zC_mem (lam := ((1075:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1075:ℝ)/1000) ((4:ℝ)/10) = ((521:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((1075:ℝ)/1000) - ((4:ℝ)/10) = (((27:ℝ)/(40:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 26 (by decide)

/-- row 57: λ = (1075:ℝ)/1000, λ₁ = (44:ℝ)/100, N₀ = 24 -/
theorem row_57 : bnd13 ((1075:ℝ)/1000) ((44:ℝ)/100) < ((24 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 2597) (zofNatI 1200)) ((2597:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2597) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2597:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2597:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1075) (zofNatI 1000)) ((1075:ℝ)/1000) := zdiv_mem (zofNat_mem 1075) (zofNat_mem 1000) (by decide)
  have hS := zwiden (82906083750911225852, 82906083750911240427) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-55915841021010287280, -55915841021010240193) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-148269403154929714269, -148269403154929563342) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (31265812770868915004, 31265812770868967663) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-92715267973810343234, -92715267973810248858) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-37468374458262169992, -37468374458262064674) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (119484995658452106316, 119484995658452229380) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (330306213059523466418, 330306213059523969740) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5283899427428417195910, 5283899427428597085603) (FT ((2597:ℝ)/(1200:ℝ)) ((1075:ℝ)/1000) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5283899427428417195910, 5283899427428597085603) (zFT_mem (lam := ((1075:ℝ)/1000)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 127) (zofNatI 200)) (((127:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 127) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-172438573279811740128, -172438573279811562525) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (17828253125624694154, 17828253125624783026) (zexp_mem hWB 22 22 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2659861052616774502158, 2659861052616818602271) (FT ((2597:ℝ)/(1200:ℝ)) ((1075:ℝ)/1000) ((((127:ℝ)/(200:ℝ))))) := zwiden (2659861052616774502158, 2659861052616818602271) (zFT_mem (lam := ((1075:ℝ)/1000)) (z := ((((127:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (606718292568773512048, 606718292568775533253) (fT ((2597:ℝ)/(1200:ℝ)) ((1075:ℝ)/1000) 0 / 6) := zwiden (606718292568773512048, 606718292568775533253) (zC_mem (lam := ((1075:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1075:ℝ)/1000) ((44:ℝ)/100) = ((2597:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1075:ℝ)/1000) - ((44:ℝ)/100) = (((127:ℝ)/(200:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 24 (by decide)

/-- row 58: λ = (1075:ℝ)/1000, λ₁ = (5:ℝ)/10, N₀ = 22 -/
theorem row_58 : bnd13 ((1075:ℝ)/1000) ((5:ℝ)/10) < ((22 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 517) (zofNatI 240)) ((517:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 517) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((517:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((517:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1075) (zofNatI 1000)) ((1075:ℝ)/1000) := zdiv_mem (zofNat_mem 1075) (zofNat_mem 1000) (by decide)
  have hS := zwiden (83461087572217633977, 83461087572217639016) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-55083998232359842088, -55083998232359807737) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-151516030517892477257, -151516030517892373620) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (30342468612626184233, 30342468612626222078) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-91947408005977328238, -91947408005977265347) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-39315062774747631534, -39315062774747555844) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (132255046686667983773, 132255046686668074558) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (375298103506479393221, 375298103506479778032) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5474031899143614600599, 5474031899143744189170) (FT ((517:ℝ)/(240:ℝ)) ((1075:ℝ)/1000) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5474031899143614600599, 5474031899143744189170) (zFT_mem (lam := ((1075:ℝ)/1000)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 23) (zofNatI 40)) (((23:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 23) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-152093303689668285742, -152093303689668181339) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (21850791586301849963, 21850791586301925044) (zexp_mem hWB 21 21 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2765387048604937898923, 2765387048604971584399) (FT ((517:ℝ)/(240:ℝ)) ((1075:ℝ)/1000) ((((23:ℝ)/(40:ℝ))))) := zwiden (2765387048604937898923, 2765387048604971584399) (zFT_mem (lam := ((1075:ℝ)/1000)) (z := ((((23:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (621725839405762332981, 621725839405763736638) (fT ((517:ℝ)/(240:ℝ)) ((1075:ℝ)/1000) 0 / 6) := zwiden (621725839405762332981, 621725839405763736638) (zC_mem (lam := ((1075:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1075:ℝ)/1000) ((5:ℝ)/10) = ((517:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((1075:ℝ)/1000) - ((5:ℝ)/10) = (((23:ℝ)/(40:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 22 (by decide)

/-- row 59: λ = (1075:ℝ)/1000, λ₁ = (58:ℝ)/100, N₀ = 19 -/
theorem row_59 : bnd13 ((1075:ℝ)/1000) ((58:ℝ)/100) < ((19 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 2569) (zofNatI 1200)) ((2569:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2569) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2569:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2569:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1075) (zofNatI 1000)) ((1075:ℝ)/1000) := zdiv_mem (zofNat_mem 1075) (zofNat_mem 1000) (by decide)
  have hS := zwiden (84188100467163515046, 84188100467163528510) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-53966320420525101500, -53966320420525063022) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-156001187057296918379, -156001187057296782200) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (29123637397307804149, 29123637397307845681) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-90866440108126119319, -90866440108126039999) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-41752725205384391702, -41752725205384308638) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (148082753132084462569, 148082753132084593617) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (439658248563784647917, 439658248563785646801) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5730621671367403725908, 5730621671367605731318) (FT ((2569:ℝ)/(1200:ℝ)) ((1075:ℝ)/1000) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5730621671367403725908, 5730621671367605731318) (zFT_mem (lam := ((1075:ℝ)/1000)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 99) (zofNatI 200)) (((99:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 99) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-126380970345485989380, -126380970345485877538) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (28257544461811909733, 28257544461812222498) (zexp_mem hWB 19 19 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2912367040962795465740, 2912367040962864106112) (FT ((2569:ℝ)/(1200:ℝ)) ((1075:ℝ)/1000) ((((99:ℝ)/(200:ℝ))))) := zwiden (2912367040962795465740, 2912367040962864106112) (zFT_mem (lam := ((1075:ℝ)/1000)) (z := ((((99:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (643288027900553617297, 643288027900555500230) (fT ((2569:ℝ)/(1200:ℝ)) ((1075:ℝ)/1000) 0 / 6) := zwiden (643288027900553617297, 643288027900555500230) (zC_mem (lam := ((1075:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1075:ℝ)/1000) ((58:ℝ)/100) = ((2569:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1075:ℝ)/1000) - ((58:ℝ)/100) = (((99:ℝ)/(200:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 19 (by decide)

/-- row 60: λ = (11:ℝ)/10, λ₁ = (348:ℝ)/1000, N₀ = 34 -/
theorem row_60 : bnd13 ((11:ℝ)/10) ((348:ℝ)/1000) < ((34 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 274) (zofNatI 125)) ((274:ℝ)/(125:ℝ)) := zdiv_mem (zofNat_mem 274) (zofNat_mem 125) (by decide)
  have hθ1 : Real.pi / 2 < ((274:ℝ)/(125:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((274:ℝ)/(125:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 11) (zofNatI 10)) ((11:ℝ)/10) := zdiv_mem (zofNat_mem 11) (zofNat_mem 10) (by decide)
  have hS := zwiden (81317849079209246627, 81317849079209250918) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-58201438308094696495, -58201438308094647675) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-139717937293483649451, -139717937293483524880) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (33874074211309471644, 33874074211309528473) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-94656315530611046761, -94656315530610962366) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-32251851577381056712, -32251851577380943054) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (99267009568346073871, 99267009568346162380) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (269842992789951888261, 269842992789952181840) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5027100742366967453040, 5027100742367110584650) (FT ((274:ℝ)/(125:ℝ)) ((11:ℝ)/10) ((((-87:ℝ)/(250:ℝ))))) := zwiden (5027100742366967453040, 5027100742367110584650) (zFT_mem (lam := ((11:ℝ)/10)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 94) (zofNatI 125)) (((94:ℝ)/(125:ℝ))) := zdiv_mem (zofNat_mem 94) (zofNat_mem 125) (by decide)
  have hWB := zwiden (-214508020676426189969, -214508020676425998710) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (11705864777222274268, 11705864777222354763) (zexp_mem hWB 24 24 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2474147653292663509167, 2474147653292697246691) (FT ((274:ℝ)/(125:ℝ)) ((11:ℝ)/10) ((((94:ℝ)/(125:ℝ))))) := zwiden (2474147653292663509167, 2474147653292697246691) (zFT_mem (lam := ((11:ℝ)/10)) (z := ((((94:ℝ)/(125:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (582853169120911215914, 582853169120912863241) (fT ((274:ℝ)/(125:ℝ)) ((11:ℝ)/10) 0 / 6) := zwiden (582853169120911215914, 582853169120912863241) (zC_mem (lam := ((11:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((11:ℝ)/10) ((348:ℝ)/1000) = ((274:ℝ)/(125:ℝ)) := by norm_num [theta13]
  have hzB : ((11:ℝ)/10) - ((348:ℝ)/1000) = (((94:ℝ)/(125:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 34 (by decide)

/-- row 61: λ = (11:ℝ)/10, λ₁ = (4:ℝ)/10, N₀ = 30 -/
theorem row_61 : bnd13 ((11:ℝ)/10) ((4:ℝ)/10) < ((30 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 131) (zofNatI 60)) ((131:ℝ)/(60:ℝ)) := zdiv_mem (zofNat_mem 131) (zofNat_mem 60) (by decide)
  have hθ1 : Real.pi / 2 < ((131:ℝ)/(60:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((131:ℝ)/(60:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 11) (zofNatI 10)) ((11:ℝ)/10) := zdiv_mem (zofNat_mem 11) (zofNat_mem 10) (by decide)
  have hS := zwiden (81819201312189576192, 81819201312189580668) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-57494506664857991203, -57494506664857946236) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-142307858712699390614, -142307858712699271527) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (33056182966353948000, 33056182966353999708) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-94083092303140830903, -94083092303140752172) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-33887634067292104000, -33887634067292000584) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (111580541105920483538, 111580541105920576983) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (305202532449316963351, 305202532449317697635) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5187312516193278545499, 5187312516193448086009) (FT ((131:ℝ)/(60:ℝ)) ((11:ℝ)/10) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5187312516193278545499, 5187312516193448086009) (zFT_mem (lam := ((11:ℝ)/10)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 7) (zofNatI 10)) (((7:ℝ)/(10:ℝ))) := zdiv_mem (zofNat_mem 7) (zofNat_mem 10) (by decide)
  have hWB := zwiden (-195265946935361009720, -195265946935360846192) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (14189620074399469097, 14189620074399567143) (zexp_mem hWB 23 23 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2557373766965744323443, 2557373766965779755789) (FT ((131:ℝ)/(60:ℝ)) ((11:ℝ)/10) ((((7:ℝ)/(10:ℝ))))) := zwiden (2557373766965744323443, 2557373766965779755789) (zFT_mem (lam := ((11:ℝ)/10)) (z := ((((7:ℝ)/(10:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (593974984519641666698, 593974984519643257194) (fT ((131:ℝ)/(60:ℝ)) ((11:ℝ)/10) 0 / 6) := zwiden (593974984519641666698, 593974984519643257194) (zC_mem (lam := ((11:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((11:ℝ)/10) ((4:ℝ)/10) = ((131:ℝ)/(60:ℝ)) := by norm_num [theta13]
  have hzB : ((11:ℝ)/10) - ((4:ℝ)/10) = (((7:ℝ)/(10:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 30 (by decide)

/-- row 62: λ = (11:ℝ)/10, λ₁ = (44:ℝ)/100, N₀ = 28 -/
theorem row_62 : bnd13 ((11:ℝ)/10) ((44:ℝ)/100) < ((28 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 653) (zofNatI 300)) ((653:ℝ)/(300:ℝ)) := zdiv_mem (zofNat_mem 653) (zofNat_mem 300) (by decide)
  have hθ1 : Real.pi / 2 < ((653:ℝ)/(300:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((653:ℝ)/(300:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 11) (zofNatI 10)) ((11:ℝ)/10) := zdiv_mem (zofNat_mem 11) (zofNat_mem 10) (by decide)
  have hS := zwiden (82200676986320517042, 82200676986320523563) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-56947771712250520098, -56947771712250476001) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-144343974337871589853, -144343974337871466628) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (32430487029905955111, 32430487029906005337) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-93622907752188524888, -93622907752188444964) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-35139025940188089778, -35139025940187989326) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (120637757226867416613, 120637757226867519966) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (334135887238773392907, 334135887238773854452) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5311841130497267034239, 5311841130497423553472) (FT ((653:ℝ)/(300:ℝ)) ((11:ℝ)/10) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5311841130497267034239, 5311841130497423553472) (zFT_mem (lam := ((11:ℝ)/10)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 33) (zofNatI 50)) (((33:ℝ)/(50:ℝ))) := zdiv_mem (zofNat_mem 33) (zofNat_mem 50) (by decide)
  have hWB := zwiden (-180956635840301279949, -180956635840301124919) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (16372511943333786912, 16372511943333977491) (zexp_mem hWB 22 22 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2623330898671196634091, 2623330898671241186687) (FT ((653:ℝ)/(300:ℝ)) ((11:ℝ)/10) ((((33:ℝ)/(50:ℝ))))) := zwiden (2623330898671196634091, 2623330898671241186687) (zFT_mem (lam := ((11:ℝ)/10)) (z := ((((33:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (602950312721634833899, 602950312721636493630) (fT ((653:ℝ)/(300:ℝ)) ((11:ℝ)/10) 0 / 6) := zwiden (602950312721634833899, 602950312721636493630) (zC_mem (lam := ((11:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((11:ℝ)/10) ((44:ℝ)/100) = ((653:ℝ)/(300:ℝ)) := by norm_num [theta13]
  have hzB : ((11:ℝ)/10) - ((44:ℝ)/100) = (((33:ℝ)/(50:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 28 (by decide)

/-- row 63: λ = (11:ℝ)/10, λ₁ = (5:ℝ)/10, N₀ = 25 -/
theorem row_63 : bnd13 ((11:ℝ)/10) ((5:ℝ)/10) < ((25 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 13) (zofNatI 6)) ((13:ℝ)/(6:ℝ)) := zdiv_mem (zofNat_mem 13) (zofNat_mem 6) (by decide)
  have hθ1 : Real.pi / 2 < ((13:ℝ)/(6:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((13:ℝ)/(6:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 11) (zofNatI 10)) ((11:ℝ)/10) := zdiv_mem (zofNat_mem 11) (zofNat_mem 10) (by decide)
  have hS := zwiden (82766035212596046572, 82766035212596049844) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-56122931277574186342, -56122931277574149347) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-147472759046119300868, -147472759046119197825) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (31497834151873107394, 31497834151873148920) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-92901450127076266344, -92901450127076201431) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-37004331696253785212, -37004331696253702160) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (133563444695639309750, 133563444695639403086) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (380240760723631800210, 380240760723632208799) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5500461281549955282534, 5500461281550090599167) (FT ((13:ℝ)/(6:ℝ)) ((11:ℝ)/10) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5500461281549955282534, 5500461281550090599167) (zFT_mem (lam := ((11:ℝ)/10)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 3) (zofNatI 5)) (((3:ℝ)/(5:ℝ))) := zdiv_mem (zofNat_mem 3) (zofNat_mem 5) (by decide)
  have hWB := zwiden (-160276133634767283704, -160276133634767171700) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (20133978282134057671, 20133978282134237270) (zexp_mem hWB 21 21 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2725453525533461765053, 2725453525533503406730) (FT ((13:ℝ)/(6:ℝ)) ((11:ℝ)/10) ((((3:ℝ)/(5:ℝ))))) := zwiden (2725453525533461765053, 2725453525533503406730) (zFT_mem (lam := ((11:ℝ)/10)) (z := ((((3:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (617138753633457802612, 617138753633459206587) (fT ((13:ℝ)/(6:ℝ)) ((11:ℝ)/10) 0 / 6) := zwiden (617138753633457802612, 617138753633459206587) (zC_mem (lam := ((11:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((11:ℝ)/10) ((5:ℝ)/10) = ((13:ℝ)/(6:ℝ)) := by norm_num [theta13]
  have hzB : ((11:ℝ)/10) - ((5:ℝ)/10) = (((3:ℝ)/(5:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 25 (by decide)

/-- row 64: λ = (11:ℝ)/10, λ₁ = (58:ℝ)/100, N₀ = 22 -/
theorem row_64 : bnd13 ((11:ℝ)/10) ((58:ℝ)/100) < ((22 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 323) (zofNatI 150)) ((323:ℝ)/(150:ℝ)) := zdiv_mem (zofNat_mem 323) (zofNat_mem 150) (by decide)
  have hθ1 : Real.pi / 2 < ((323:ℝ)/(150:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((323:ℝ)/(150:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 11) (zofNatI 10)) ((11:ℝ)/10) := zdiv_mem (zofNat_mem 11) (zofNat_mem 10) (by decide)
  have hS := zwiden (83506961919222429949, 83506961919222434114) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-55014428207712364904, -55014428207712331677) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-151791020355485230997, -151791020355485131748) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (30265873110215342746, 30265873110215379306) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-91881755226984659275, -91881755226984599198) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-39468253779569314508, -39468253779569241388) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (149599618835806840198, 149599618835806938246) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (446378110544469672634, 446378110544470147241) (zexp_mem hWA 21 21 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5754753175459954482785, 5754753175460092680966) (FT ((323:ℝ)/(150:ℝ)) ((11:ℝ)/10) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5754753175459954482785, 5754753175460092680966) (zFT_mem (lam := ((11:ℝ)/10)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 13) (zofNatI 25)) (((13:ℝ)/(25:ℝ))) := zdiv_mem (zofNat_mem 13) (zofNat_mem 25) (by decide)
  have hWB := zwiden (-134123796197620013600, -134123796197619925695) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (26152171416198940383, 26152171416199021745) (zexp_mem hWB 20 20 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2867620459059972058087, 2867620459060007971512) (FT ((323:ℝ)/(150:ℝ)) ((11:ℝ)/10) ((((13:ℝ)/(25:ℝ))))) := zwiden (2867620459059972058087, 2867620459060007971512) (zFT_mem (lam := ((11:ℝ)/10)) (z := ((((13:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (637508986223920414988, 637508986223921791659) (fT ((323:ℝ)/(150:ℝ)) ((11:ℝ)/10) 0 / 6) := zwiden (637508986223920414988, 637508986223921791659) (zC_mem (lam := ((11:ℝ)/10)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((11:ℝ)/10) ((58:ℝ)/100) = ((323:ℝ)/(150:ℝ)) := by norm_num [theta13]
  have hzB : ((11:ℝ)/10) - ((58:ℝ)/100) = (((13:ℝ)/(25:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 22 (by decide)

/-- row 65: λ = (1125:ℝ)/1000, λ₁ = (348:ℝ)/1000, N₀ = 42 -/
theorem row_65 : bnd13 ((1125:ℝ)/1000) ((348:ℝ)/1000) < ((42 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 4409) (zofNatI 2000)) ((4409:ℝ)/(2000:ℝ)) := zdiv_mem (zofNat_mem 4409) (zofNat_mem 2000) (by decide)
  have hθ1 : Real.pi / 2 < ((4409:ℝ)/(2000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((4409:ℝ)/(2000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1125) (zofNatI 1000)) ((1125:ℝ)/1000) := zdiv_mem (zofNat_mem 1125) (zofNat_mem 1000) (by decide)
  have hS := zwiden (80583997171751798448, 80583997171751803394) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-59213338022975059744, -59213338022975003788) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-136090954947489873549, -136090954947489736589) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (35062193998230973302, 35062193998231039570) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-95432949275468114719, -95432949275468018677) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-29875612003538053396, -29875612003537920860) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (100216114082886900819, 100216114082887001677) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (272416277078626193973, 272416277078626533700) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5063228415379132118531, 5063228415379296152533) (FT ((4409:ℝ)/(2000:ℝ)) ((1125:ℝ)/1000) ((((-87:ℝ)/(250:ℝ))))) := zwiden (5063228415379132118531, 5063228415379296152533) (zFT_mem (lam := ((1125:ℝ)/1000)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 777) (zofNatI 1000)) (((777:ℝ)/(1000:ℝ))) := zdiv_mem (zofNat_mem 777) (zofNat_mem 1000) (by decide)
  have hWB := zwiden (-223758392650583908917, -223758392650583683725) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (10671602692133234996, 10671602692133419038) (zexp_mem hWB 24 24 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2445179297442382831993, 2445179297442425651109) (FT ((4409:ℝ)/(2000:ℝ)) ((1125:ℝ)/1000) ((((777:ℝ)/(1000:ℝ))))) := zwiden (2445179297442382831993, 2445179297442425651109) (zFT_mem (lam := ((1125:ℝ)/1000)) (z := ((((777:ℝ)/(1000:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (580739972199509614422, 580739972199511442355) (fT ((4409:ℝ)/(2000:ℝ)) ((1125:ℝ)/1000) 0 / 6) := zwiden (580739972199509614422, 580739972199511442355) (zC_mem (lam := ((1125:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1125:ℝ)/1000) ((348:ℝ)/1000) = ((4409:ℝ)/(2000:ℝ)) := by norm_num [theta13]
  have hzB : ((1125:ℝ)/1000) - ((348:ℝ)/1000) = (((777:ℝ)/(1000:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 42 (by decide)

/-- row 66: λ = (1125:ℝ)/1000, λ₁ = (4:ℝ)/10, N₀ = 36 -/
theorem row_66 : bnd13 ((1125:ℝ)/1000) ((4:ℝ)/10) < ((36 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 527) (zofNatI 240)) ((527:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 527) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((527:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((527:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1125) (zofNatI 1000)) ((1125:ℝ)/1000) := zdiv_mem (zofNat_mem 1125) (zofNat_mem 1000) (by decide)
  have hS := zwiden (81094146652520203788, 81094146652520210669) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-58512728347766790668, -58512728347766737418) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-138592318188518278268, -138592318188518140379) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (34237393786995451489, 34237393786995513806) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-94900795473457534494, -94900795473457440075) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-31525212426009097022, -31525212426008972388) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (112667246055982551254, 112667246055982663624) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (308537270039087649926, 308537270039088531308) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5222657676720646445503, 5222657676720850442865) (FT ((527:ℝ)/(240:ℝ)) ((1125:ℝ)/1000) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5222657676720646445503, 5222657676720850442865) (zFT_mem (lam := ((1125:ℝ)/1000)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 29) (zofNatI 40)) (((29:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 29) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-204209383476468577818, -204209383476468374148) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (12975673707664580532, 12975673707664816545) (zexp_mem hWB 23 23 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2525862759493092813405, 2525862759493141626594) (FT ((527:ℝ)/(240:ℝ)) ((1125:ℝ)/1000) ((((29:ℝ)/(40:ℝ))))) := zwiden (2525862759493092813405, 2525862759493141626594) (zFT_mem (lam := ((1125:ℝ)/1000)) (z := ((((29:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (591261733645950930715, 591261733645952788864) (fT ((527:ℝ)/(240:ℝ)) ((1125:ℝ)/1000) 0 / 6) := zwiden (591261733645950930715, 591261733645952788864) (zC_mem (lam := ((1125:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1125:ℝ)/1000) ((4:ℝ)/10) = ((527:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((1125:ℝ)/1000) - ((4:ℝ)/10) = (((29:ℝ)/(40:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 36 (by decide)

/-- row 67: λ = (1125:ℝ)/1000, λ₁ = (44:ℝ)/100, N₀ = 33 -/
theorem row_67 : bnd13 ((1125:ℝ)/1000) ((44:ℝ)/100) < ((33 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 2627) (zofNatI 1200)) ((2627:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2627) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2627:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2627:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1125) (zofNatI 1000)) ((1125:ℝ)/1000) := zdiv_mem (zofNat_mem 1125) (zofNat_mem 1000) (by decide)
  have hS := zwiden (81482426533187520891, 81482426533187536922) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-57970804430020658303, -57970804430020599395) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-140557695092102731561, -140557695092102561075) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (33606141662636959518, 33606141662637027818) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-94472036260778817922, -94472036260778703335) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-32787716674726080964, -32787716674725944364) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (121830029561364602418, 121830029561364751655) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (338143540578638985925, 338143540578639630635) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5346512544386010888547, 5346512544386233425681) (FT ((2627:ℝ)/(1200:ℝ)) ((1125:ℝ)/1000) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5346512544386010888547, 5346512544386233425681) (zFT_mem (lam := ((1125:ℝ)/1000)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 137) (zofNatI 200)) (((137:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 137) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-189667205112579215644, -189667205112578983310) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (15006720511460941544, 15006720511461014756) (zexp_mem hWB 23 23 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2589787546445190318701, 2589787546445237764796) (FT ((2627:ℝ)/(1200:ℝ)) ((1125:ℝ)/1000) ((((137:ℝ)/(200:ℝ))))) := zwiden (2589787546445190318701, 2589787546445237764796) (zFT_mem (lam := ((1125:ℝ)/1000)) (z := ((((137:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (599750904708789650995, 599750904708791969141) (fT ((2627:ℝ)/(1200:ℝ)) ((1125:ℝ)/1000) 0 / 6) := zwiden (599750904708789650995, 599750904708791969141) (zC_mem (lam := ((1125:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1125:ℝ)/1000) ((44:ℝ)/100) = ((2627:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1125:ℝ)/1000) - ((44:ℝ)/100) = (((137:ℝ)/(200:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 33 (by decide)

/-- row 68: λ = (1125:ℝ)/1000, λ₁ = (5:ℝ)/10, N₀ = 29 -/
theorem row_68 : bnd13 ((1125:ℝ)/1000) ((5:ℝ)/10) < ((29 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 523) (zofNatI 240)) ((523:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 523) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((523:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((523:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1125) (zofNatI 1000)) ((1125:ℝ)/1000) := zdiv_mem (zofNat_mem 1125) (zofNat_mem 1000) (by decide)
  have hS := zwiden (82058050828359541519, 82058050828359547568) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-57153095228958213648, -57153095228958168960) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-143575864963447519473, -143575864963447396626) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (32664762942503610156, 32664762942503661238) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-93797431865918532989, -93797431865918452733) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-34670474114992779688, -34670474114992677524) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (134913833709459494593, 134913833709459610355) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (385410316179339230986, 385410316179339742795) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5533995898072704836692, 5533995898072872691810) (FT ((523:ℝ)/(240:ℝ)) ((1125:ℝ)/1000) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5533995898072704836692, 5533995898072872691810) (zFT_mem (lam := ((1125:ℝ)/1000)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 5) (zofNatI 8)) (((5:ℝ)/(8:ℝ))) := zdiv_mem (zofNat_mem 5) (zofNat_mem 8) (by decide)
  have hWB := zwiden (-168642292136824512944, -168642292136824368241) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (18518074675726065907, 18518074675726127767) (zexp_mem hWB 22 22 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2688733066590918494922, 2688733066590955795465) (FT ((523:ℝ)/(240:ℝ)) ((1125:ℝ)/1000) ((((5:ℝ)/(8:ℝ))))) := zwiden (2688733066590918494922, 2688733066590955795465) (zFT_mem (lam := ((1125:ℝ)/1000)) (z := ((((5:ℝ)/(8:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (613166432040924818617, 613166432040926505580) (fT ((523:ℝ)/(240:ℝ)) ((1125:ℝ)/1000) 0 / 6) := zwiden (613166432040924818617, 613166432040926505580) (zC_mem (lam := ((1125:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1125:ℝ)/1000) ((5:ℝ)/10) = ((523:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((1125:ℝ)/1000) - ((5:ℝ)/10) = (((5:ℝ)/(8:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 29 (by decide)

/-- row 69: λ = (1125:ℝ)/1000, λ₁ = (58:ℝ)/100, N₀ = 25 -/
theorem row_69 : bnd13 ((1125:ℝ)/1000) ((58:ℝ)/100) < ((25 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 2599) (zofNatI 1200)) ((2599:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2599) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2599:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2599:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1125) (zofNatI 1000)) ((1125:ℝ)/1000) := zdiv_mem (zofNat_mem 1125) (zofNat_mem 1000) (by decide)
  have hS := zwiden (82812775578375919975, 82812775578375934641) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-56053940102418742033, -56053940102418694249) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-147737653101753345832, -147737653101753193725) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (31420442010055426951, 31420442010055480521) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-92839647239706604737, -92839647239706509151) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-37159115979889146098, -37159115979889038958) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (151160842745803106471, 151160842745803263923) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (453401757097384040963, 453401757097384800795) (zexp_mem hWA 21 21 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5786514898254463468649, 5786514898254681812979) (FT ((2599:ℝ)/(1200:ℝ)) ((1125:ℝ)/1000) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5786514898254463468649, 5786514898254681812979) (zFT_mem (lam := ((1125:ℝ)/1000)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 109) (zofNatI 200)) (((109:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 109) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-142039067752522032479, -142039067752521884529) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (24161960310697647746, 24161960310697867211) (zexp_mem hWB 20 20 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2826414468365773843957, 2826414468365836263733) (FT ((2599:ℝ)/(1200:ℝ)) ((1125:ℝ)/1000) ((((109:ℝ)/(200:ℝ))))) := zwiden (2826414468365773843957, 2826414468365836263733) (zFT_mem (lam := ((1125:ℝ)/1000)) (z := ((((109:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (632415713083703581654, 632415713083705708846) (fT ((2599:ℝ)/(1200:ℝ)) ((1125:ℝ)/1000) 0 / 6) := zwiden (632415713083703581654, 632415713083705708846) (zC_mem (lam := ((1125:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1125:ℝ)/1000) ((58:ℝ)/100) = ((2599:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1125:ℝ)/1000) - ((58:ℝ)/100) = (((109:ℝ)/(200:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 25 (by decide)

/-- row 70: λ = (115:ℝ)/100, λ₁ = (348:ℝ)/1000, N₀ = 54 -/
theorem row_70 : bnd13 ((115:ℝ)/100) ((348:ℝ)/1000) < ((54 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 2217) (zofNatI 1000)) ((2217:ℝ)/(1000:ℝ)) := zdiv_mem (zofNat_mem 2217) (zofNat_mem 1000) (by decide)
  have hθ1 : Real.pi / 2 < ((2217:ℝ)/(1000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2217:ℝ)/(1000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 115) (zofNatI 100)) ((115:ℝ)/100) := zdiv_mem (zofNat_mem 115) (zofNat_mem 100) (by decide)
  have hS := zwiden (79837554178683972015, 79837554178683977708) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-60215985774258551305, -60215985774258487218) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-132585314600651183583, -132585314600651033018) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (36259649427657005043, 36259649427657082225) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-96149940533504615191, -96149940533504506003) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-27480701144685989914, -27480701144685835550) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (101200269468995108076, 101200269468995223002) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (275110512527695934101, 275110512527696327738) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5105569738325161652185, 5105569738325350007157) (FT ((2217:ℝ)/(1000:ℝ)) ((115:ℝ)/100) ((((-87:ℝ)/(250:ℝ))))) := zwiden (5105569738325161652185, 5105569738325350007157) (zFT_mem (lam := ((115:ℝ)/100)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 401) (zofNatI 500)) (((401:ℝ)/(500:ℝ))) := zdiv_mem (zofNat_mem 401) (zofNat_mem 500) (by decide)
  have hWB := zwiden (-233225908373948761056, -233225908373948496199) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (9707619593495556745, 9707619593495622836) (zexp_mem hWB 25 25 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2418731875835717682892, 2418731875835756272681) (FT ((2217:ℝ)/(1000:ℝ)) ((115:ℝ)/100) ((((401:ℝ)/(500:ℝ))))) := zwiden (2418731875835717682892, 2418731875835756272681) (zFT_mem (lam := ((115:ℝ)/100)) (z := ((((401:ℝ)/(500:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (579118508455188365757, 579118508455190394814) (fT ((2217:ℝ)/(1000:ℝ)) ((115:ℝ)/100) 0 / 6) := zwiden (579118508455188365757, 579118508455190394814) (zC_mem (lam := ((115:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((115:ℝ)/100) ((348:ℝ)/1000) = ((2217:ℝ)/(1000:ℝ)) := by norm_num [theta13]
  have hzB : ((115:ℝ)/100) - ((348:ℝ)/1000) = (((401:ℝ)/(500:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 54 (by decide)

/-- row 71: λ = (115:ℝ)/100, λ₁ = (4:ℝ)/10, N₀ = 45 -/
theorem row_71 : bnd13 ((115:ℝ)/100) ((4:ℝ)/10) < ((45 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 53) (zofNatI 24)) ((53:ℝ)/(24:ℝ)) := zdiv_mem (zofNat_mem 53) (zofNat_mem 24) (by decide)
  have hθ1 : Real.pi / 2 < ((53:ℝ)/(24:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((53:ℝ)/(24:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 115) (zofNatI 100)) ((115:ℝ)/100) := zdiv_mem (zofNat_mem 115) (zofNat_mem 100) (by decide)
  have hS := zwiden (80356421197421981339, 80356421197421986748) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-59521807535915081228, -59521807535915022650) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-135003328232153418452, -135003328232153276500) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (35428455723425103803, 35428455723425173537) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-95659188735757567720, -95659188735757467138) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-29143088553149792394, -29143088553149652926) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (113792148991782437843, 113792148991782557522) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (312027609507625099339, 312027609507626112144) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5264510944544682685251, 5264510944544906924768) (FT ((53:ℝ)/(24:ℝ)) ((115:ℝ)/100) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5264510944544682685251, 5264510944544906924768) (zFT_mem (lam := ((115:ℝ)/100)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 3) (zofNatI 4)) (((3:ℝ)/(4:ℝ))) := zdiv_mem (zofNat_mem 3) (zofNat_mem 4) (by decide)
  have hWB := zwiden (-213360279359592295354, -213360279359592070956) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (11840991794703097173, 11840991794703174832) (zexp_mem hWB 24 24 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2497032239401258874985, 2497032239401298168156) (FT ((53:ℝ)/(24:ℝ)) ((115:ℝ)/100) ((((3:ℝ)/(4:ℝ))))) := zwiden (2497032239401258874985, 2497032239401298168156) (zFT_mem (lam := ((115:ℝ)/100)) (z := ((((3:ℝ)/(4:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (589069866608704200713, 589069866608706129989) (fT ((53:ℝ)/(24:ℝ)) ((115:ℝ)/100) 0 / 6) := zwiden (589069866608704200713, 589069866608706129989) (zC_mem (lam := ((115:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((115:ℝ)/100) ((4:ℝ)/10) = ((53:ℝ)/(24:ℝ)) := by norm_num [theta13]
  have hzB : ((115:ℝ)/100) - ((4:ℝ)/10) = (((3:ℝ)/(4:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 45 (by decide)

/-- row 72: λ = (115:ℝ)/100, λ₁ = (44:ℝ)/100, N₀ = 40 -/
theorem row_72 : bnd13 ((115:ℝ)/100) ((44:ℝ)/100) < ((40 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 1321) (zofNatI 600)) ((1321:ℝ)/(600:ℝ)) := zdiv_mem (zofNat_mem 1321) (zofNat_mem 600) (by decide)
  have hθ1 : Real.pi / 2 < ((1321:ℝ)/(600:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1321:ℝ)/(600:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 115) (zofNatI 100)) ((115:ℝ)/100) := zdiv_mem (zofNat_mem 115) (zofNat_mem 100) (by decide)
  have hS := zwiden (80751444616684279829, 80751444616684290664) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-58984779327539887893, -58984779327539827737) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-136902172962748829108, -136902172962748671116) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (34792041923185698128, 34792041923185769094) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-95262122821903634291, -95262122821903524355) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-30415916153628603744, -30415916153628461812) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (123062591829483112309, 123062591829483255074) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (342337161676099634742, 342337161676100293073) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5387925574191733163825, 5387925574191951825944) (FT ((1321:ℝ)/(600:ℝ)) ((115:ℝ)/100) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5387925574191733163825, 5387925574191951825944) (zFT_mem (lam := ((115:ℝ)/100)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 71) (zofNatI 100)) (((71:ℝ)/(100:ℝ))) := zdiv_mem (zofNat_mem 71) (zofNat_mem 100) (by decide)
  have hWB := zwiden (-198578273179393434322, -198578273179393203955) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (13727312401586220419, 13727312401586362225) (zexp_mem hWB 23 23 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2559054232348062470334, 2559054232348111526345) (FT ((1321:ℝ)/(600:ℝ)) ((115:ℝ)/100) ((((71:ℝ)/(100:ℝ))))) := zwiden (2559054232348062470334, 2559054232348111526345) (zFT_mem (lam := ((115:ℝ)/100)) (z := ((((71:ℝ)/(100:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (597097936131254155056, 597097936131256319435) (fT ((1321:ℝ)/(600:ℝ)) ((115:ℝ)/100) 0 / 6) := zwiden (597097936131254155056, 597097936131256319435) (zC_mem (lam := ((115:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((115:ℝ)/100) ((44:ℝ)/100) = ((1321:ℝ)/(600:ℝ)) := by norm_num [theta13]
  have hzB : ((115:ℝ)/100) - ((44:ℝ)/100) = (((71:ℝ)/(100:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 40 (by decide)

/-- row 73: λ = (115:ℝ)/100, λ₁ = (5:ℝ)/10, N₀ = 35 -/
theorem row_73 : bnd13 ((115:ℝ)/100) ((5:ℝ)/10) < ((35 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 263) (zofNatI 120)) ((263:ℝ)/(120:ℝ)) := zdiv_mem (zofNat_mem 263) (zofNat_mem 120) (by decide)
  have hθ1 : Real.pi / 2 < ((263:ℝ)/(120:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((263:ℝ)/(120:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 115) (zofNatI 100)) ((115:ℝ)/100) := zdiv_mem (zofNat_mem 115) (zofNat_mem 100) (by decide)
  have hS := zwiden (81337245040627769088, 81337245040627774555) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-58174329125490379813, -58174329125490330007) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-139816386821018132122, -139816386821018003018) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (33842525692008725040, 33842525692008782990) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-94634793263082805932, -94634793263082718549) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-32314948615982549920, -32314948615982434020) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI zoneI) (zofNatI 2)) (((-1:ℝ)/(2:ℝ))) := zdiv_mem (zneg_mem zone_mem) (zofNat_mem 2) (by decide)
  have hWA := zwiden (136307134290984497517, 136307134290984623549) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (390817824297882464464, 390817824297883037633) (zexp_mem hWA 20 20 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5574633849073188125597, 5574633849073373290385) (FT ((263:ℝ)/(120:ℝ)) ((115:ℝ)/100) ((((-1:ℝ)/(2:ℝ))))) := zwiden (5574633849073188125597, 5574633849073373290385) (zFT_mem (lam := ((115:ℝ)/100)) (z := ((((-1:ℝ)/(2:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 13) (zofNatI 20)) (((13:ℝ)/(20:ℝ))) := zdiv_mem (zofNat_mem 13) (zofNat_mem 20) (by decide)
  have hWB := zwiden (-177199274578280010613, -177199274578279846771) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (16999389645491306077, 16999389645491438058) (zexp_mem hWB 22 22 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2655028645829539061907, 2655028645829583118499) (FT ((263:ℝ)/(120:ℝ)) ((115:ℝ)/100) ((((13:ℝ)/(20:ℝ))))) := zwiden (2655028645829539061907, 2655028645829583118499) (zFT_mem (lam := ((115:ℝ)/100)) (z := ((((13:ℝ)/(20:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (609782160953717131306, 609782160953718917360) (fT ((263:ℝ)/(120:ℝ)) ((115:ℝ)/100) 0 / 6) := zwiden (609782160953717131306, 609782160953718917360) (zC_mem (lam := ((115:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((115:ℝ)/100) ((5:ℝ)/10) = ((263:ℝ)/(120:ℝ)) := by norm_num [theta13]
  have hzB : ((115:ℝ)/100) - ((5:ℝ)/10) = (((13:ℝ)/(20:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((5:ℝ)/10)) = (((-1:ℝ)/(2:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 35 (by decide)

/-- row 74: λ = (115:ℝ)/100, λ₁ = (58:ℝ)/100, N₀ = 29 -/
theorem row_74 : bnd13 ((115:ℝ)/100) ((58:ℝ)/100) < ((29 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 1307) (zofNatI 600)) ((1307:ℝ)/(600:ℝ)) := zdiv_mem (zofNat_mem 1307) (zofNat_mem 600) (by decide)
  have hθ1 : Real.pi / 2 < ((1307:ℝ)/(600:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((1307:ℝ)/(600:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 115) (zofNatI 100)) ((115:ℝ)/100) := zdiv_mem (zofNat_mem 115) (zofNat_mem 100) (by decide)
  have hS := zwiden (82105649909827442910, 82105649909827452431) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-57084693683025547439, -57084693683025499722) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-143831287535212078634, -143831287535211941726) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (32586622528848513921, 32586622528848568400) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-93739517494964685650, -93739517494964596423) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-34826754942302972158, -34826754942302863200) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 29)) (zofNatI 50)) (((-29:ℝ)/(50:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 29)) (zofNat_mem 50) (by decide)
  have hWA := zwiden (152767551481517139816, 152767551481517286154) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (460745440557281383092, 460745440557282114695) (zexp_mem hWA 21 21 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5825883842806331158750, 5825883842806538630067) (FT ((1307:ℝ)/(600:ℝ)) ((115:ℝ)/100) ((((-29:ℝ)/(50:ℝ))))) := zwiden (5825883842806331158750, 5825883842806538630067) (zFT_mem (lam := ((115:ℝ)/100)) (z := ((((-29:ℝ)/(50:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 57) (zofNatI 100)) (((57:ℝ)/(100:ℝ))) := zdiv_mem (zofNat_mem 57) (zofNat_mem 100) (by decide)
  have hWB := zwiden (-150133628180111815702, -150133628180111671889) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (22283219450351562952, 22283219450351634812) (zexp_mem hWB 21 21 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2788522336127411663026, 2788522336127456692539) (FT ((1307:ℝ)/(600:ℝ)) ((115:ℝ)/100) ((((57:ℝ)/(100:ℝ))))) := zwiden (2788522336127411663026, 2788522336127456692539) (zFT_mem (lam := ((115:ℝ)/100)) (z := ((((57:ℝ)/(100:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (627974406289817042240, 627974406289818967456) (fT ((1307:ℝ)/(600:ℝ)) ((115:ℝ)/100) 0 / 6) := zwiden (627974406289817042240, 627974406289818967456) (zC_mem (lam := ((115:ℝ)/100)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((115:ℝ)/100) ((58:ℝ)/100) = ((1307:ℝ)/(600:ℝ)) := by norm_num [theta13]
  have hzB : ((115:ℝ)/100) - ((58:ℝ)/100) = (((57:ℝ)/(100:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((58:ℝ)/100)) = (((-29:ℝ)/(50:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 29 (by decide)

/-- row 75: λ = (1175:ℝ)/1000, λ₁ = (348:ℝ)/1000, N₀ = 73 -/
theorem row_75 : bnd13 ((1175:ℝ)/1000) ((348:ℝ)/1000) < ((73 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 4459) (zofNatI 2000)) ((4459:ℝ)/(2000:ℝ)) := zdiv_mem (zofNat_mem 4459) (zofNat_mem 2000) (by decide)
  have hθ1 : Real.pi / 2 < ((4459:ℝ)/(2000:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((4459:ℝ)/(2000:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1175) (zofNatI 1000)) ((1175:ℝ)/1000) := zdiv_mem (zofNat_mem 1175) (zofNat_mem 1000) (by decide)
  have hS := zwiden (79078636730204799907, 79078636730204806460) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-61209224900273914712, -61209224900273841368) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-129193984826707093109, -129193984826706927594) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (37465692128923032457, 37465692128923122245) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-96806841208523348474, -96806841208523224452) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-25068615742153935086, -25068615742153755510) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 87)) (zofNatI 250)) (((-87:ℝ)/(250:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 87)) (zofNat_mem 250) (by decide)
  have hWA := zwiden (102220159901005230275, 102220159901005361237) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (277930695263675436996, 277930695263675893765) (zexp_mem hWA 18 18 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5154187239400228426677, 5154187239400444938284) (FT ((4459:ℝ)/(2000:ℝ)) ((1175:ℝ)/1000) ((((-87:ℝ)/(250:ℝ))))) := zwiden (5154187239400228426677, 5154187239400444938284) (zFT_mem (lam := ((1175:ℝ)/1000)) (z := ((((-87:ℝ)/(250:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 827) (zofNatI 1000)) (((827:ℝ)/(1000:ℝ))) := zdiv_mem (zofNat_mem 827) (zofNat_mem 1000) (by decide)
  have hWB := zwiden (-242919747810722510756, -242919747810722199533) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (8810751242515737909, 8810751242515877047) (zexp_mem hWB 25 25 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2394672384137311943771, 2394672384137358187277) (FT ((4459:ℝ)/(2000:ℝ)) ((1175:ℝ)/1000) ((((827:ℝ)/(1000:ℝ))))) := zwiden (2394672384137311943771, 2394672384137358187277) (zFT_mem (lam := ((1175:ℝ)/1000)) (z := ((((827:ℝ)/(1000:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (577974875497274209697, 577974875497276462969) (fT ((4459:ℝ)/(2000:ℝ)) ((1175:ℝ)/1000) 0 / 6) := zwiden (577974875497274209697, 577974875497276462969) (zC_mem (lam := ((1175:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1175:ℝ)/1000) ((348:ℝ)/1000) = ((4459:ℝ)/(2000:ℝ)) := by norm_num [theta13]
  have hzB : ((1175:ℝ)/1000) - ((348:ℝ)/1000) = (((827:ℝ)/(1000:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((348:ℝ)/1000)) = (((-87:ℝ)/(250:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 73 (by decide)

/-- row 76: λ = (1175:ℝ)/1000, λ₁ = (4:ℝ)/10, N₀ = 58 -/
theorem row_76 : bnd13 ((1175:ℝ)/1000) ((4:ℝ)/10) < ((58 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 533) (zofNatI 240)) ((533:ℝ)/(240:ℝ)) := zdiv_mem (zofNat_mem 533) (zofNat_mem 240) (by decide)
  have hθ1 : Real.pi / 2 < ((533:ℝ)/(240:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((533:ℝ)/(240:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1175) (zofNatI 1000)) ((1175:ℝ)/1000) := zdiv_mem (zofNat_mem 1175) (zofNat_mem 1000) (by decide)
  have hS := zwiden (79606140214996365465, 79606140214996373897) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-60521586562732684840, -60521586562732615611) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-131533465555272564692, -131533465555272400300) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (36628624400703370980, 36628624400703454778) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-96357798118938770909, -96357798118938650481) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-26742751198593258040, -26742751198593090444) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 2)) (zofNatI 5)) (((-2:ℝ)/(5:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 2)) (zofNat_mem 5) (by decide)
  have hWA := zwiden (114956047968892062683, 114956047968892206636) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (315680512476182417968, 315680512476182918881) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5312927253445977879166, 5312927253446199180321) (FT ((533:ℝ)/(240:ℝ)) ((1175:ℝ)/1000) ((((-2:ℝ)/(5:ℝ))))) := zwiden (5312927253445977879166, 5312927253446199180321) (zFT_mem (lam := ((1175:ℝ)/1000)) (z := ((((-2:ℝ)/(5:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 31) (zofNatI 40)) (((31:ℝ)/(40:ℝ))) := zdiv_mem (zofNat_mem 31) (zofNat_mem 40) (by decide)
  have hWB := zwiden (-222727342939728650358, -222727342939728371450) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (10782201404911204520, 10782201404911377819) (zexp_mem hWB 24 24 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2470735334764041006375, 2470735334764091525088) (FT ((533:ℝ)/(240:ℝ)) ((1175:ℝ)/1000) ((((31:ℝ)/(40:ℝ))))) := zwiden (2470735334764041006375, 2470735334764091525088) (zFT_mem (lam := ((1175:ℝ)/1000)) (z := ((((31:ℝ)/(40:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (587382516489664051453, 587382516489666307932) (fT ((533:ℝ)/(240:ℝ)) ((1175:ℝ)/1000) 0 / 6) := zwiden (587382516489664051453, 587382516489666307932) (zC_mem (lam := ((1175:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1175:ℝ)/1000) ((4:ℝ)/10) = ((533:ℝ)/(240:ℝ)) := by norm_num [theta13]
  have hzB : ((1175:ℝ)/1000) - ((4:ℝ)/10) = (((31:ℝ)/(40:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((4:ℝ)/10)) = (((-2:ℝ)/(5:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 58 (by decide)

/-- row 77: λ = (1175:ℝ)/1000, λ₁ = (44:ℝ)/100, N₀ = 51 -/
theorem row_77 : bnd13 ((1175:ℝ)/1000) ((44:ℝ)/100) < ((51 : ℕ) : ℝ) + 1 := by
  have hq1 : zMem (zdivI (zofNatI 2657) (zofNatI 1200)) ((2657:ℝ)/(1200:ℝ)) := zdiv_mem (zofNat_mem 2657) (zofNat_mem 1200) (by decide)
  have hθ1 : Real.pi / 2 < ((2657:ℝ)/(1200:ℝ)) := zpi1 hq1 (by decide)
  have hθ2 : ((2657:ℝ)/(1200:ℝ)) < Real.pi := zpi2 hq1 (by decide)
  have hq2 : zMem (zdivI (zofNatI 1175) (zofNatI 1000)) ((1175:ℝ)/1000) := zdiv_mem (zofNat_mem 1175) (zofNat_mem 1000) (by decide)
  have hS := zwiden (80007845451248053912, 80007845451248071736) (zsin_mem hq1 (by norm_num) 12) (by decide)
  have hC := zwiden (-59989537973293413043, -59989537973293338870) (zcos_mem hq1 (by norm_num) 12) (by decide)
  have hT := zwiden (-133369664368588162906, -133369664368587968289) (ztan_mem hS hC (by decide)) (by decide)
  have hC2i := zwiden (35987446662492034752, 35987446662492123745) (zcsq_mem hC) (by decide)
  have hS2i := zwiden (-95992673657180737301, -95992673657180597227) (zsin2_mem hS hC) (by decide)
  have hCC2i := zwiden (-28025106675015930496, -28025106675015752510) (zcos2_mem hC) (by decide)
  have hq3 : zMem (zdivI (znegI (zofNatI 11)) (zofNatI 25)) (((-11:ℝ)/(25:ℝ))) := zdiv_mem (zneg_mem (zofNat_mem 11)) (zofNat_mem 25) (by decide)
  have hWA := zwiden (124336333258154509432, 124336333258154692365) (zW_mem hq1 hq2 hq3 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEA := zwiden (346725540900865719788, 346725540900866560302) (zexp_mem hWA 19 19 (by decide) (by decide)) (by decide)
  have hq4 : zMem zoneI (1:ℝ) := zone_mem
  have hq5 : zMem (zofNatI 2) (2:ℝ) := (zofNat_mem 2)
  have hq6 : zMem (zdivI zoneI (zofNatI 2)) ((1:ℝ)/(2:ℝ)) := zdiv_mem zone_mem (zofNat_mem 2) (by decide)
  have hAM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEA)) (zmul_mem hq3 (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) hq3) (zmul_mem (zmul_mem hEA hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEA (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEA (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq3)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq3)))) (zmul_mem hq3 hq3)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEA hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEA hS2i) hq3))) (zmul_mem (zmul_mem hq3 hq3) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hAD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq3 hq3)) (zmul_mem (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq3 hq3) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hA : zMem (5436128681587260076007, 5436128681587539769581) (FT ((2657:ℝ)/(1200:ℝ)) ((1175:ℝ)/1000) ((((-11:ℝ)/(25:ℝ))))) := zwiden (5436128681587260076007, 5436128681587539769581) (zFT_mem (lam := ((1175:ℝ)/1000)) (z := ((((-11:ℝ)/(25:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hAM hAD (by decide)) (by decide)
  have hq7 : zMem (zdivI (zofNatI 147) (zofNatI 200)) (((147:ℝ)/(200:ℝ))) := zdiv_mem (zofNat_mem 147) (zofNat_mem 200) (by decide)
  have hWB := zwiden (-207698193056235679290, -207698193056235373711) (zW_mem hq1 hq2 hq7 hT (by norm_num) (by decide) (by decide)) (by decide)
  have hEB := zwiden (12530782980530092303, 12530782980530157402) (zexp_mem hWB 24 24 (by decide) (by decide)) (by decide)
  have hBM := (zmul_mem (zmul_mem (zmul_mem hq2 hq2) (zmul_mem (zadd_mem hq4 (zmul_mem hT hT)) (zadd_mem hq4 (zmul_mem hT hT)))) (zadd_mem (zadd_mem (zadd_mem (zadd_mem (zmul_mem (zmul_mem (zsub_mem (zmul_mem hq5 (zmul_mem hq1 hC2i)) hS2i) (zsub_mem hq4 hEB)) (zmul_mem hq7 (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zmul_mem (zneg_mem (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))))) hC2i) (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7))))))) (zmul_mem (zmul_mem (zmul_mem hq6 (zsub_mem (zmul_mem hq5 hq1) hS2i)) (zadd_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) hq7) (zmul_mem (zmul_mem hEB hS2i) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))) (zmul_mem (zneg_mem hq6) (zmul_mem (zsub_mem (zmul_mem (zsub_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hEB (zadd_mem (zmul_mem hCC2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))) (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hS2i (zmul_mem (zneg_mem hq2) hT)))))) (zsub_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))) (zmul_mem (zmul_mem hEB (zsub_mem (zmul_mem (zmul_mem hq5 hq1) (zmul_mem hCC2i (zmul_mem (zneg_mem hq2) hT))) (zmul_mem hS2i (zadd_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq5 (zmul_mem hq1 hq7)))))) (zmul_mem hq5 (zmul_mem (zmul_mem (zneg_mem hq2) hT) hq7)))) (zmul_mem hq7 hq7)))) (zmul_mem (zmul_mem (zadd_mem hq6 hC2i) (zsub_mem (zmul_mem (zsub_mem hq4 (zmul_mem hEB hCC2i)) (zmul_mem (zneg_mem hq2) hT)) (zmul_mem (zmul_mem hEB hS2i) hq7))) (zmul_mem (zmul_mem hq7 hq7) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))))
  have hBD := (zmul_mem (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem hq7 hq7)) (zmul_mem (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT))) (zadd_mem (zmul_mem hq7 hq7) (zmul_mem (zmul_mem (zneg_mem hq2) hT) (zmul_mem (zneg_mem hq2) hT)))))
  have hB : zMem (2530972753676730501227, 2530972753676783147440) (FT ((2657:ℝ)/(1200:ℝ)) ((1175:ℝ)/1000) ((((147:ℝ)/(200:ℝ))))) := zwiden (2530972753676730501227, 2530972753676783147440) (zFT_mem (lam := ((1175:ℝ)/1000)) (z := ((((147:ℝ)/(200:ℝ))))) hθ1 hθ2 (by norm_num) (by norm_num) hBM hBD (by decide)) (by decide)
  have hq8 : zMem (zdivI zoneI (zofNatI 6)) ((1:ℝ)/(6:ℝ)) := zdiv_mem zone_mem (zofNat_mem 6) (by decide)
  have hq9 : zMem (zofNatI 3) (3:ℝ) := (zofNat_mem 3)
  have hcM := (zmul_mem (zmul_mem hq2 (zadd_mem hq4 (zmul_mem hT hT))) (zmul_mem hq8 (zadd_mem (zsub_mem (zmul_mem hq1 (zmul_mem hT hT)) (zmul_mem hq9 hT)) (zmul_mem hq9 hq1))))
  have hcD := (zneg_mem hT)
  have hc : zMem (594972045055589825752, 594972045055592517911) (fT ((2657:ℝ)/(1200:ℝ)) ((1175:ℝ)/1000) 0 / 6) := zwiden (594972045055589825752, 594972045055592517911) (zC_mem (lam := ((1175:ℝ)/1000)) hθ1 hθ2 (by norm_num) hcM hcD (by decide)) (by decide)
  have hθe : theta13 ((1175:ℝ)/1000) ((44:ℝ)/100) = ((2657:ℝ)/(1200:ℝ)) := by norm_num [theta13]
  have hzB : ((1175:ℝ)/1000) - ((44:ℝ)/100) = (((147:ℝ)/(200:ℝ))) := by norm_num
  simp only [bnd13, hθe, hzB]
  have hzA : (-((44:ℝ)/100)) = (((-11:ℝ)/(25:ℝ))) := by norm_num
  rw [hzA]
  exact zfinal hA hB hc 51 (by decide)

end Work.LinnikAreas.Density4
