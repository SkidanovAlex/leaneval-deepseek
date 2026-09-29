import Mathlib
import Submission.Work.TMC7Core.Fourier.ac_defs

/-!
# `blk_first` : the first-block arithmetic estimate

For `α` close to a reduced rational `a/q` (`|α - a/q| < 1/q²`) and `s ≥ 1`,

`∑_{k ≤ min K q} (1/k) / (1 + (s·q·‖kα‖)²) ≤ 50/s² + 2/q`.

Since `q·‖kα‖ ≥ q·‖ka/q‖ - k/q` and `k ↦ q·‖ka/q‖` takes *distinct* integer values
symmetric under `k ↦ q-k`, the sum is controlled by a Cauchy–Schwarz (rearrangement) step
on the first half `k ≤ q/2` and a pairing step on the second half.
-/

namespace Work.TMC7Core.Fourier

open Finset

noncomputable section

/-! ## Local definitions -/

/-- Signed distance of `k*a` to the nearest multiple of `q`. -/
def blkZ (a : ℤ) (q : ℕ) (k : ℕ) : ℤ :=
  (k : ℤ) * a - (q : ℤ) * round ((k : ℝ) * (a : ℝ) / (q : ℝ))

/-- `dist (k*a) (q ℤ)`, as a natural number. -/
def blkK (a : ℤ) (q : ℕ) (k : ℕ) : ℕ := (blkZ a q k).natAbs

/-- `q * ‖k α‖`. -/
def blkD (α : ℝ) (q : ℕ) (k : ℕ) : ℝ := (q : ℝ) * fracDist ((k : ℝ) * α)

/-- The summand `(1/k) (1 + (s q ‖kα‖)²)⁻¹`. -/
def blkG (α : ℝ) (q : ℕ) (s : ℝ) (k : ℕ) : ℝ := (1 / (k : ℝ)) * fw s (blkD α q k)

/-! ## Elementary `fracDist` lemmas -/

lemma fracDist_le_abs (x : ℝ) : fracDist x ≤ |x| := by
  rw [fracDist]
  simpa using round_le x 0

lemma fracDist_neg (x : ℝ) : fracDist (-x) = fracDist x := by
  apply le_antisymm
  · have h := round_le (-x) (-round x)
    rw [fracDist, fracDist]
    refine h.trans (le_of_eq ?_)
    have : (-x - ((-round x : ℤ) : ℝ)) = -(x - (round x : ℝ)) := by push_cast; ring
    rw [this, abs_neg]
  · have h := round_le x (-round (-x))
    rw [fracDist, fracDist]
    refine h.trans (le_of_eq ?_)
    have : (x - ((-round (-x) : ℤ) : ℝ)) = -(-x - (round (-x) : ℝ)) := by push_cast; ring
    rw [this, abs_neg]

lemma fracDist_add_le (x y : ℝ) : fracDist (x + y) ≤ fracDist x + fracDist y := by
  have h := round_le (x + y) (round x + round y)
  have h2 : |(x + y) - (((round x + round y : ℤ)) : ℝ)| ≤ fracDist x + fracDist y := by
    have hc : (((round x + round y : ℤ)) : ℝ) = (round x : ℝ) + (round y : ℝ) := by
      push_cast; ring
    rw [hc, fracDist, fracDist]
    have he : (x + y) - ((round x : ℝ) + (round y : ℝ))
        = (x - (round x : ℝ)) + (y - (round y : ℝ)) := by ring
    rw [he]
    exact abs_add_le _ _
  exact h.trans h2

lemma fracDist_lipschitz (x y : ℝ) : |fracDist x - fracDist y| ≤ |x - y| := by
  rw [abs_sub_le_iff]
  constructor
  · have h := fracDist_add_le (x - y) y
    rw [sub_add_cancel] at h
    linarith [fracDist_le_abs (x - y)]
  · have h := fracDist_add_le (y - x) x
    rw [sub_add_cancel] at h
    have h2 : fracDist (y - x) = fracDist (x - y) := by
      have : y - x = -(x - y) := by ring
      rw [this, fracDist_neg]
    rw [h2] at h
    linarith [fracDist_le_abs (x - y)]

/-! ## `blkK` : integrality, symmetry, positivity, injectivity -/

lemma blkK_cast (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (k : ℕ) :
    (blkK a q k : ℝ) = (q : ℝ) * fracDist ((k : ℝ) * (a : ℝ) / (q : ℝ)) := by
  have hq0 : ((q : ℝ)) ≠ 0 := by positivity
  have hmain : (blkK a q k : ℝ)
      = |(k : ℝ) * (a : ℝ) - (q : ℝ) * (round ((k : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ)| := by
    simp only [blkK, blkZ, Nat.cast_natAbs]
    norm_cast
  have hR : (q : ℝ) * fracDist ((k : ℝ) * (a : ℝ) / (q : ℝ))
      = |(k : ℝ) * (a : ℝ) - (q : ℝ) * (round ((k : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ)| := by
    rw [fracDist]
    have h1 : (q : ℝ) * |(k : ℝ) * (a : ℝ) / (q : ℝ)
        - (round ((k : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ)|
        = |(q : ℝ)| * |(k : ℝ) * (a : ℝ) / (q : ℝ)
        - (round ((k : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ)| := by
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (q:ℝ))]
    rw [h1, ← abs_mul]
    congr 1
    rw [mul_sub]
    have hx : (q : ℝ) * ((k : ℝ) * (a : ℝ) / (q : ℝ)) = (k : ℝ) * (a : ℝ) := by
      field_simp
    rw [hx]
  rw [hmain, hR]

lemma blkK_symm (a : ℤ) (q : ℕ) (hq : 1 ≤ q) {k : ℕ} (hk : k ≤ q) :
    blkK a q (q - k) = blkK a q k := by
  rw [← Nat.cast_inj (R := ℝ)]
  rw [blkK_cast a q hq, blkK_cast a q hq]
  congr 1
  rw [Nat.cast_sub hk]
  have hq0 : ((q : ℝ)) ≠ 0 := by positivity
  have h1 : ((q : ℝ) - (k : ℝ)) * (a : ℝ) / (q : ℝ)
      = -((k : ℝ) * (a : ℝ) / (q : ℝ)) + (a : ℝ) := by
    field_simp
    ring
  rw [h1, fracDist_add_intCast, fracDist_neg]

lemma two_mul_blkK_le (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (k : ℕ) : 2 * blkK a q k ≤ q := by
  have h : (2 : ℝ) * (blkK a q k : ℝ) ≤ (q : ℝ) := by
    rw [blkK_cast a q hq]
    have h2 := fracDist_le_half ((k : ℝ) * (a : ℝ) / (q : ℝ))
    nlinarith [show (0:ℝ) < (q:ℝ) by exact_mod_cast hq]
  exact_mod_cast h

lemma blkK_le (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (k : ℕ) : blkK a q k ≤ q / 2 := by
  have := two_mul_blkK_le a q hq k
  omega

lemma blkK_pos (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime (Int.natAbs a) q)
    {k : ℕ} (hk1 : 1 ≤ k) (hkq : k < q) : 1 ≤ blkK a q k := by
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have hZ : blkZ a q k = 0 := Int.natAbs_eq_zero.mp (by simpa only [blkK] using h0)
  have hdvd : (q : ℤ) ∣ (k : ℤ) * a := by
    refine ⟨round ((k : ℝ) * (a : ℝ) / (q : ℝ)), ?_⟩
    rw [blkZ] at hZ
    linarith
  have hgcd : Int.gcd (q : ℤ) a = 1 := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, Nat.gcd_comm]
    exact hcop
  have hdvd' : (q : ℤ) ∣ a * (k : ℤ) := by
    rw [mul_comm]
    exact hdvd
  have hkq_dvd : (q : ℤ) ∣ (k : ℤ) := Int.dvd_of_dvd_mul_right_of_gcd_one hdvd' hgcd
  have hle : (q : ℤ) ≤ (k : ℤ) := Int.le_of_dvd (by exact_mod_cast hk1) hkq_dvd
  have : q ≤ k := by exact_mod_cast hle
  omega

lemma blkK_pos_le_half (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime (Int.natAbs a) q)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ q / 2) : 1 ≤ blkK a q k :=
  blkK_pos a q hq hcop hk1 (by omega)

/-- On `[1, q/2]` the values `blkK` are pairwise distinct. -/
lemma blkK_inj (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime (Int.natAbs a) q)
    {k k' : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ q / 2) (hk1' : 1 ≤ k') (hk2' : k' ≤ q / 2)
    (h : blkK a q k = blkK a q k') : k = k' := by
  have hgcd : Int.gcd (q : ℤ) a = 1 := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, Nat.gcd_comm]
    exact hcop
  have hsmall : ∀ n : ℕ, 0 < n → n ≤ q / 2 → ¬ (q ∣ n) := by
    intro n hn hle hd
    have := Nat.le_of_dvd hn hd
    omega
  have hnat : (blkZ a q k).natAbs = (blkZ a q k').natAbs := h
  rcases Int.natAbs_eq_natAbs_iff.mp hnat with hz | hz
  · -- difference divisible
    have hdvd : (q : ℤ) ∣ ((k : ℤ) - (k' : ℤ)) * a := by
      refine ⟨round ((k:ℝ)*(a:ℝ)/(q:ℝ)) - round ((k':ℝ)*(a:ℝ)/(q:ℝ)), ?_⟩
      have he : blkZ a q k - blkZ a q k'
          = ((k : ℤ) - (k' : ℤ)) * a
            - (q : ℤ) * (round ((k:ℝ)*(a:ℝ)/(q:ℝ)) - round ((k':ℝ)*(a:ℝ)/(q:ℝ))) := by
        rw [blkZ, blkZ]; ring
      rw [hz, sub_self] at he
      linarith
    have hdvd1 : (q : ℤ) ∣ ((k : ℤ) - (k' : ℤ)) := by
      refine Int.dvd_of_dvd_mul_right_of_gcd_one ?_ hgcd
      rw [mul_comm]
      exact hdvd
    rcases le_total k' k with hle | hle
    · have hcast : ((k : ℤ) - (k' : ℤ)) = ((k - k' : ℕ) : ℤ) := by
        rw [Nat.cast_sub hle]
      rw [hcast] at hdvd1
      have hnat2 : q ∣ (k - k') := Int.natCast_dvd_natCast.mp hdvd1
      rcases Nat.eq_zero_or_pos (k - k') with h0 | hpos
      · omega
      · exact absurd hnat2 (hsmall (k - k') hpos (by omega))
    · have hcast : ((k : ℤ) - (k' : ℤ)) = -(((k' - k : ℕ)) : ℤ) := by
        rw [Nat.cast_sub hle]; push_cast; ring
      rw [hcast] at hdvd1
      have h2 : (q : ℤ) ∣ (((k' - k : ℕ)) : ℤ) := dvd_neg.mp hdvd1
      have hnat2 : q ∣ (k' - k) := Int.natCast_dvd_natCast.mp h2
      rcases Nat.eq_zero_or_pos (k' - k) with h0 | hpos
      · omega
      · exact absurd hnat2 (hsmall (k' - k) hpos (by omega))
  · -- sum divisible
    have h0 : blkZ a q k + blkZ a q k' = 0 := by rw [hz]; ring
    have hdvd : (q : ℤ) ∣ ((k : ℤ) + (k' : ℤ)) * a := by
      refine ⟨round ((k:ℝ)*(a:ℝ)/(q:ℝ)) + round ((k':ℝ)*(a:ℝ)/(q:ℝ)), ?_⟩
      have he : blkZ a q k + blkZ a q k'
          = ((k : ℤ) + (k' : ℤ)) * a
            - (q : ℤ) * (round ((k:ℝ)*(a:ℝ)/(q:ℝ)) + round ((k':ℝ)*(a:ℝ)/(q:ℝ))) := by
        rw [blkZ, blkZ]; ring
      rw [h0] at he
      linarith
    have hdvd2 : (q : ℤ) ∣ ((k : ℤ) + (k' : ℤ)) := by
      refine Int.dvd_of_dvd_mul_right_of_gcd_one ?_ hgcd
      rw [mul_comm]
      exact hdvd
    have hcast : ((k : ℤ) + (k' : ℤ)) = ((k + k' : ℕ) : ℤ) := by push_cast; ring
    rw [hcast] at hdvd2
    have hnat2 : q ∣ (k + k') := Int.natCast_dvd_natCast.mp hdvd2
    have hpos : 0 < k + k' := by omega
    have hle2 : q ≤ k + k' := Nat.le_of_dvd hpos hnat2
    have hsum : k + k' = q := by omega
    omega

/-! ## The comparison `q‖kα‖` vs `dist (ka) (qℤ)` -/

lemma blkD_ge (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2)) (k : ℕ) :
    (blkK a q k : ℝ) - (k : ℝ) / (q : ℝ) ≤ blkD α q k := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hq0 : ((q:ℝ)) ≠ 0 := ne_of_gt hqpos
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hb : blkK a q 0 = 0 := by
      simp [blkK, blkZ, round_zero]
    rw [hb, blkD]
    simp [fracDist]
  · set x : ℝ := (k : ℝ) * α with hxdef
    set y : ℝ := (k : ℝ) * ((a : ℝ) / (q : ℝ)) with hydef
    have hmul : |y - x| = (k : ℝ) * |α - (a : ℝ) / (q : ℝ)| := by
      rw [hydef, hxdef, ← mul_sub, abs_mul, abs_of_nonneg (by positivity), abs_sub_comm]
    have h2 : fracDist y - fracDist x ≤ (k : ℝ) * |α - (a : ℝ) / (q : ℝ)| := by
      calc fracDist y - fracDist x ≤ |fracDist y - fracDist x| := le_abs_self _
        _ ≤ |y - x| := fracDist_lipschitz y x
        _ = (k : ℝ) * |α - (a : ℝ) / (q : ℝ)| := hmul
    have h3 : (k : ℝ) * |α - (a : ℝ) / (q : ℝ)| < (k : ℝ) * (1 / ((q : ℝ) ^ 2)) :=
      mul_lt_mul_of_pos_left hα (by exact_mod_cast hkpos)
    have hlt : fracDist y - fracDist x < (k : ℝ) * (1 / ((q : ℝ) ^ 2)) := lt_of_le_of_lt h2 h3
    have hmain : (q : ℝ) * fracDist y - (k : ℝ) / (q : ℝ) < (q : ℝ) * fracDist x := by
      have h4 := mul_lt_mul_of_pos_left hlt hqpos
      have he : (q : ℝ) * ((k : ℝ) * (1 / ((q : ℝ) ^ 2))) = (k : ℝ) / (q : ℝ) := by
        field_simp
      rw [he, mul_sub] at h4
      linarith
    have hcast : (q : ℝ) * fracDist y = (blkK a q k : ℝ) := by
      rw [hydef, blkK_cast a q hq]
      congr 1
      ring_nf
    rw [hcast] at hmain
    have hxD : blkD α q k = (q : ℝ) * fracDist x := by rw [blkD, hxdef]
    rw [hxD]
    exact le_of_lt hmain

lemma blkD_nonneg (α : ℝ) (q : ℕ) (k : ℕ) : 0 ≤ blkD α q k := by
  rw [blkD]
  exact mul_nonneg (by positivity) (fracDist_nonneg _)

lemma blkD_q_sub_ge_one (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2))
    {k' : ℕ} (hk2 : k' ≤ q / 2) (h2 : 2 ≤ blkK a q k') :
    1 ≤ blkD α q (q - k') := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hk'q : k' ≤ q := by omega
  have hge := blkD_ge α a q hq hα (q - k')
  rw [blkK_symm a q hq hk'q] at hge
  have hcast : (((q - k' : ℕ)) : ℝ) = (q:ℝ) - (k':ℝ) := Nat.cast_sub hk'q
  have hle1 : (((q - k' : ℕ)) : ℝ) / (q:ℝ) ≤ 1 := by
    rw [hcast, div_le_one hqpos]
    linarith [show (0:ℝ) ≤ (k':ℝ) by positivity]
  have h2' : (2:ℝ) ≤ (blkK a q k' : ℝ) := by exact_mod_cast h2
  linarith

/-! ## Elementary sum bounds -/

lemma sum_inv_sq_Icc_le (N : ℕ) : ∑ k ∈ Finset.Icc 1 N, (1/((k:ℝ)))^2 ≤ 2 := by
  have key : ∀ n : ℕ,
      ∑ k ∈ Finset.Icc 1 (n+1), (1/((k:ℝ)))^2 ≤ 2 - 1/(((n+1:ℕ)):ℝ) := by
    intro n
    induction n with
    | zero =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := 0) (by omega) (fun k => (1/((k:ℝ)))^2)]
      simp
      norm_num
    | succ n ih =>
      have hstep : (1/(((n+1+1:ℕ)):ℝ))^2
          ≤ 1/(((n+1:ℕ)):ℝ) - 1/(((n+1+1:ℕ)):ℝ) := by
        have h0 : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
        have h1 : (0:ℝ) < (((n+1+1:ℕ)):ℝ) := by positivity
        field_simp
        push_cast
        nlinarith
      rw [Finset.sum_Icc_succ_top (a := 1) (b := n+1) (by omega) (fun k => (1/((k:ℝ)))^2)]
      linarith
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    have := key n
    have hpos : (0:ℝ) < 1/(((n+1:ℕ)):ℝ) := by positivity
    linarith

lemma sum_inv_fourth_Icc_le (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (1/(((j:ℝ))^2))^2 ≤ 2 := by
  refine le_trans (Finset.sum_le_sum ?_) (sum_inv_sq_Icc_le N)
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj.1
  have hconv : (1/((j:ℝ)))^2 = 1/(((j:ℝ))^2) := by rw [div_pow, one_pow]
  rw [← hconv]
  have h1 : (1/((j:ℝ)))^2 ≤ 1 := by
    have hdiv : (1:ℝ)/(j:ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hj1
    nlinarith [hdiv, show (0:ℝ) ≤ 1/(j:ℝ) by positivity]
  have h0 : (0:ℝ) ≤ (1/((j:ℝ)))^2 := by positivity
  nlinarith [h0, h1]

lemma sum_inv_fourth_blkK_le (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime (Int.natAbs a) q)
    (t : ℕ) (ht : t ≤ q / 2) :
    ∑ k ∈ Finset.Icc 1 t, (1/(((blkK a q k : ℝ))^2))^2 ≤ 2 := by
  have hinj : Set.InjOn (fun k => blkK a q k) ((Finset.Icc 1 t : Finset ℕ) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_Icc] at hx hy
    exact blkK_inj a q hq hcop hx.1 (le_trans hx.2 ht) hy.1 (le_trans hy.2 ht) hxy
  have himg := Finset.sum_image (s := Finset.Icc 1 t) (g := fun k => blkK a q k)
    (f := fun j : ℕ => (1/(((j:ℝ))^2))^2) hinj
  rw [← himg]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (sum_inv_fourth_Icc_le (q / 2))
  · intro j hj
    simp only [Finset.mem_image, Finset.mem_Icc] at hj ⊢
    obtain ⟨k, hk, rfl⟩ := hj
    exact ⟨by exact_mod_cast blkK_pos_le_half a q hq hcop hk.1 (le_trans hk.2 ht),
      blkK_le a q hq k⟩
  · intro j hj hj2
    positivity

lemma fw_sum_le (s : ℝ) (hs : 1 ≤ s) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : 1/2 ≤ u + v) : fw s u + fw s v ≤ 1 + 16 / s^2 := by
  have hs0 : (0:ℝ) < s := lt_of_lt_of_le one_pos hs
  have hmax : (1:ℝ)/4 ≤ max u v := by
    have h2 : (u + v)/2 ≤ max u v := by
      rcases le_total u v with hle | hle
      · rw [max_eq_right hle]; linarith
      · rw [max_eq_left hle]; linarith
    linarith
  have hsum : fw s u + fw s v = fw s (max u v) + fw s (min u v) := by
    rcases le_total u v with hle | hle
    · rw [max_eq_right hle, min_eq_left hle, add_comm]
    · rw [max_eq_left hle, min_eq_right hle, add_comm]
  rw [hsum]
  have h1 : fw s (max u v) ≤ fw s (1/4) := fw_le_of_le s (by norm_num) hmax
  have h2 : fw s (min u v) ≤ 1 := fw_le_one s _
  have h3 : fw s (1/4) ≤ 16/s^2 := by
    rw [fw]
    have hs2 : (0:ℝ) < s^2/16 := by positivity
    have hpos : (0:ℝ) < 1 + (s*(1/4))^2 := by positivity
    have hkey : s^2/16 ≤ 1 + (s*(1/4))^2 := by nlinarith [sq_nonneg (s*(1/4))]
    have he : (16:ℝ)/s^2 = (s^2/16)⁻¹ := by rw [inv_div]
    rw [he]
    exact (inv_le_inv₀ hpos hs2).mpr hkey
  linarith

/-! ## Reindexing helpers -/

lemma sum_Icc_split (a b c : ℕ) (hab : a ≤ b + 1) (hbc : b ≤ c) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc a c, f k
      = ∑ k ∈ Finset.Icc a b, f k + ∑ k ∈ Finset.Icc (b+1) c, f k := by
  have hunion : Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b+1) c := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : k ≤ b
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_trans h2 hbc⟩
      · exact ⟨le_trans hab h1, h2⟩
  have hdisj : Disjoint (Finset.Icc a b) (Finset.Icc (b+1) c) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2; omega
  rw [hunion, Finset.sum_union hdisj]

lemma sum_Icc_last (a q : ℕ) (hq : 1 ≤ q) (ha : a ≤ q) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc a q, f k = ∑ k ∈ Finset.Icc a (q - 1), f k + f q := by
  conv_lhs => rw [show q = (q - 1) + 1 by omega]
  rw [Finset.sum_Icc_succ_top (a := a) (b := q - 1) (by omega) f]
  rw [show (q - 1) + 1 = q by omega]

lemma sum_Icc_rev (q m : ℕ) (hq : 1 ≤ q) (f : ℕ → ℝ) (hm : m ≤ q) :
    ∑ k ∈ Finset.Icc (q - m) (q - 1), f k = ∑ k' ∈ Finset.Icc 1 m, f (q - k') := by
  refine Finset.sum_bij (fun k' _ => q - k') ?_ ?_ ?_ ?_
  · intro k' hk'
    simp only [Finset.mem_Icc] at hk' ⊢
    constructor <;> omega
  · intro k1 h1 k2 h2 h
    simp only [Finset.mem_Icc] at h1 h2
    omega
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    exact ⟨q - b, by simp only [Finset.mem_Icc]; constructor <;> omega, by omega⟩
  · intro k' hk'
    congr 1
    simp only [Finset.mem_Icc] at hk'
    omega

/-! ## `blkG` elementary facts -/

lemma blkG_nonneg (α : ℝ) (q : ℕ) (s : ℝ) (k : ℕ) : 0 ≤ blkG α q s k := by
  rw [blkG]
  exact mul_nonneg (by positivity) (fw_nonneg s _)

lemma blkG_eq (α : ℝ) (q : ℕ) (s : ℝ) (k : ℕ) :
    (1 / (k : ℝ)) * (1 + (s * (q : ℝ) * fracDist ((k : ℝ) * α)) ^ 2)⁻¹ = blkG α q s k := by
  rw [blkG, blkD, fw]
  congr 1
  ring

/-! ## The first half `k ≤ q/2` -/

lemma blkG_half_block (α : ℝ) (a : ℤ) (q s : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hcop : Nat.Coprime (Int.natAbs a) q)
    (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2)) :
    ∑ k ∈ Finset.Icc 1 (q / 2), blkG α q s k ≤ 8 / (s : ℝ) ^ 2 := by
  have hs1r : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hs0 : ((s : ℝ)) ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hs1r)
  have hterm : ∀ k ∈ Finset.Icc 1 (q / 2),
      blkG α q s k ≤ (1/(k:ℝ)) * (4/((s:ℝ)^2 * (blkK a q k : ℝ)^2)) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hDge := blkD_ge α a q hq hα k
    have hkq : (k:ℝ)/(q:ℝ) ≤ 1/2 := by
      have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
      rw [div_le_iff₀ hqpos]
      have h2 : (2 * k : ℕ) ≤ q := by omega
      have := (Nat.cast_le (α := ℝ)).mpr h2
      push_cast at this
      linarith
    have hJ1 : (1:ℝ) ≤ (blkK a q k : ℝ) := by
      have := blkK_pos_le_half a q hq hcop hk.1 hk.2
      exact_mod_cast this
    have hhalf : (blkK a q k : ℝ)/2 ≤ blkD α q k := by linarith
    have hfw1 : fw s (blkD α q k) ≤ fw s ((blkK a q k : ℝ)/2) :=
      fw_le_of_le s (by positivity) hhalf
    have hfx : s * ((blkK a q k : ℝ)/2) ≠ 0 := by
      apply mul_ne_zero hs0
      intro hcon
      linarith
    have hfw2 : fw s ((blkK a q k : ℝ)/2) ≤ 1/(s * ((blkK a q k : ℝ)/2))^2 :=
      fw_le_inv_sq s _ hfx
    have hfw3 : (1:ℝ)/(s * ((blkK a q k : ℝ)/2))^2
        = 4/((s:ℝ)^2 * (blkK a q k : ℝ)^2) := by ring_nf
    have hfw : fw s (blkD α q k) ≤ 4/((s:ℝ)^2 * (blkK a q k : ℝ)^2) := by
      rw [hfw3] at hfw2
      exact hfw1.trans hfw2
    calc blkG α q s k = (1/(k:ℝ)) * fw s (blkD α q k) := rfl
      _ ≤ (1/(k:ℝ)) * (4/((s:ℝ)^2 * (blkK a q k : ℝ)^2)) :=
          mul_le_mul_of_nonneg_left hfw (by positivity)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 (q / 2))
    (fun k => (1/(k:ℝ))) (fun k => (1/((blkK a q k : ℝ))^2))
  have hb1 : ∑ k ∈ Finset.Icc 1 (q / 2), ((1/(k:ℝ)))^2 ≤ 2 := sum_inv_sq_Icc_le (q / 2)
  have hb2 : ∑ k ∈ Finset.Icc 1 (q / 2), ((1/((blkK a q k : ℝ))^2))^2 ≤ 2 :=
    sum_inv_fourth_blkK_le a q hq hcop (q / 2) (le_refl _)
  have hb1nn : (0:ℝ) ≤ ∑ k ∈ Finset.Icc 1 (q / 2), ((1/(k:ℝ)))^2 := by positivity
  have hb2nn : (0:ℝ) ≤ ∑ k ∈ Finset.Icc 1 (q / 2), ((1/((blkK a q k : ℝ))^2))^2 := by positivity
  have hS1nn : (0:ℝ) ≤
      ∑ k ∈ Finset.Icc 1 (q / 2), (1/(k:ℝ)) * (1/((blkK a q k : ℝ))^2) := by
    apply Finset.sum_nonneg
    intro k hk
    positivity
  have hS1 : (∑ k ∈ Finset.Icc 1 (q / 2), (1/(k:ℝ)) * (1/((blkK a q k : ℝ))^2)) ≤ 2 := by
    have h4 : ((∑ k ∈ Finset.Icc 1 (q / 2),
        (1/(k:ℝ)) * (1/((blkK a q k : ℝ))^2)))^2 ≤ 4 := by
      have h3 : (∑ k ∈ Finset.Icc 1 (q / 2), ((1/(k:ℝ)))^2)
          * (∑ k ∈ Finset.Icc 1 (q / 2), ((1/((blkK a q k : ℝ))^2))^2) ≤ 2 * 2 :=
        mul_le_mul hb1 hb2 hb2nn (by norm_num)
      linarith [hcs, h3]
    nlinarith [h4, hS1nn, sq_nonneg ((∑ k ∈ Finset.Icc 1 (q / 2),
      (1/(k:ℝ)) * (1/((blkK a q k : ℝ))^2)) - 2)]
  calc ∑ k ∈ Finset.Icc 1 (q / 2), blkG α q s k
      ≤ ∑ k ∈ Finset.Icc 1 (q / 2),
          (1/(k:ℝ)) * (4/((s:ℝ)^2 * (blkK a q k : ℝ)^2)) := Finset.sum_le_sum hterm
    _ = (4 / (s:ℝ)^2) * ∑ k ∈ Finset.Icc 1 (q / 2),
          ((1/(k:ℝ)) * (1/((blkK a q k : ℝ))^2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring_nf
    _ ≤ (4 / (s:ℝ)^2) * 2 :=
        mul_le_mul_of_nonneg_left hS1 (div_nonneg (by norm_num) (sq_nonneg _))
    _ = 8 / (s:ℝ)^2 := by ring

/-! ## The second half -/

lemma blkG_q_sub_le (α : ℝ) (a : ℤ) (q s : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2))
    {k' : ℕ} (hk2 : k' ≤ q / 2) (h2 : 2 ≤ blkK a q k') :
    blkG α q s (q - k') ≤ (2/(q:ℝ)) * (1/(s:ℝ)^2) := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hs1r : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hs2pos : (0:ℝ) < (s:ℝ)^2 := by nlinarith [hs1r]
  have hD := blkD_q_sub_ge_one α a q hq hα hk2 h2
  have hfw : fw s (blkD α q (q - k')) ≤ 1/(s:ℝ)^2 := by
    calc fw s (blkD α q (q - k')) ≤ fw s 1 := fw_le_of_le s (by norm_num) hD
      _ = 1/(1 + (s:ℝ)^2) := by rw [fw]; ring_nf
      _ ≤ 1/(s:ℝ)^2 := by
          apply one_div_le_one_div_of_le hs2pos
          linarith
  have hcoef : (1/(((q - k' : ℕ):ℝ))) ≤ 2/(q:ℝ) := by
    have hk'q : k' ≤ q := by omega
    have h2' : (q:ℝ)/2 ≤ (q:ℝ) - (k':ℝ) := by
      have hk2' : (2 * k' : ℕ) ≤ q := by omega
      have hh : (2:ℝ) * (k':ℝ) ≤ (q:ℝ) := by exact_mod_cast hk2'
      linarith
    have hcast : (((q - k' : ℕ)) : ℝ) = (q:ℝ) - (k':ℝ) := Nat.cast_sub hk'q
    rw [hcast]
    calc (1:ℝ)/((q:ℝ) - (k':ℝ)) ≤ 1/((q:ℝ)/2) := one_div_le_one_div_of_le (by linarith) h2'
      _ = 2/(q:ℝ) := by ring
  calc blkG α q s (q - k') = (1/(((q - k' : ℕ):ℝ))) * fw s (blkD α q (q - k')) := rfl
    _ ≤ (2/(q:ℝ)) * (1/(s:ℝ)^2) := mul_le_mul hcoef hfw (fw_nonneg s _) (by positivity)

lemma blkG_second_half (α : ℝ) (a : ℤ) (q s : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hcop : Nat.Coprime (Int.natAbs a) q)
    (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2)) :
    ∑ k' ∈ Finset.Icc 1 (q / 2), blkG α q s (q - k')
      ≤ 1 / (s : ℝ) ^ 2
        + ∑ k' ∈ (Finset.Icc 1 (q / 2)).filter (fun k' => ¬ (2 ≤ blkK a q k')),
            blkG α q s (q - k') := by
  have hsplit : ∑ k' ∈ Finset.Icc 1 (q/2), blkG α q s (q - k')
      = ∑ k' ∈ (Finset.Icc 1 (q/2)).filter (fun k' => 2 ≤ blkK a q k'),
          blkG α q s (q - k')
        + ∑ k' ∈ (Finset.Icc 1 (q/2)).filter (fun k' => ¬ (2 ≤ blkK a q k')),
          blkG α q s (q - k') := by
    rw [Finset.sum_filter_add_sum_filter_not]
  have hA2 : ∑ k' ∈ (Finset.Icc 1 (q/2)).filter (fun k' => 2 ≤ blkK a q k'),
        blkG α q s (q - k') ≤ 1/(s:ℝ)^2 := by
    have hterm : ∀ k' ∈ (Finset.Icc 1 (q/2)).filter (fun k' => 2 ≤ blkK a q k'),
        blkG α q s (q - k') ≤ (2/(q:ℝ)) * (1/(s:ℝ)^2) := by
      intro k' hk'
      rw [Finset.mem_filter, Finset.mem_Icc] at hk'
      exact blkG_q_sub_le α a q s hq hs hα hk'.1.2 hk'.2
    calc ∑ k' ∈ (Finset.Icc 1 (q/2)).filter (fun k' => 2 ≤ blkK a q k'),
          blkG α q s (q - k')
        ≤ ∑ k' ∈ (Finset.Icc 1 (q/2)).filter (fun k' => 2 ≤ blkK a q k'),
          (2/(q:ℝ)) * (1/(s:ℝ)^2) := Finset.sum_le_sum hterm
      _ ≤ ∑ k' ∈ Finset.Icc 1 (q/2), (2/(q:ℝ)) * (1/(s:ℝ)^2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro k' _ _; positivity
      _ = ((q/2 : ℕ) : ℝ) * ((2/(q:ℝ)) * (1/(s:ℝ)^2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp
      _ ≤ 1/(s:ℝ)^2 := by
          have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
          have h2 : (2:ℝ) * ((q/2 : ℕ) : ℝ) ≤ (q:ℝ) := by
            have hh : (2 * (q/2) : ℕ) ≤ q := by omega
            exact_mod_cast hh
          have heq : ((q/2 : ℕ) : ℝ) * ((2/(q:ℝ)) * (1/(s:ℝ)^2))
              = ((2 * ((q/2 : ℕ) : ℝ))/(q:ℝ)) * (1/(s:ℝ)^2) := by ring
          rw [heq]
          have h3 : (2 * ((q/2 : ℕ) : ℝ))/(q:ℝ) ≤ 1 := by
            rw [div_le_one hqpos]; linarith
          exact mul_le_of_le_one_left (by positivity) h3
  linarith [hsplit, hA2]

/-! ## The exceptional block `blkK = 1` -/

lemma blkG_sB_bound (α : ℝ) (a : ℤ) (q s : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hcop : Nat.Coprime (Int.natAbs a) q)
    (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2))
    (u : Finset ℕ) (hu : ∀ k' ∈ u, blkK a q k' = 1)
    (hu1 : ∀ k' ∈ u, 1 ≤ k') (hu2 : ∀ k' ∈ u, k' ≤ q / 2) :
    (∑ k' ∈ u, blkG α q s (q - k')) + blkG α q s q ≤ 2/(q:ℝ) + 32/(s:ℝ)^2 := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hs1r : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hs2pos : (0:ℝ) < (s:ℝ)^2 := by nlinarith [hs1r]
  have hcard : u.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    exact blkK_inj a q hq hcop (hu1 x hx) (hu2 x hx) (hu1 y hy) (hu2 y hy) (by rw [hu x hx, hu y hy])
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
  · rw [Finset.card_eq_zero.mp h0]
    simp only [Finset.sum_empty, zero_add, blkG]
    have h1 : fw s (blkD α q q) ≤ 1 := fw_le_one s _
    have h2 : (1/(q:ℝ)) * fw s (blkD α q q) ≤ 1/(q:ℝ) := by
      have h0 : (0:ℝ) ≤ 1/(q:ℝ) := div_nonneg (by norm_num) hqpos.le
      calc (1/(q:ℝ)) * fw s (blkD α q q) ≤ (1/(q:ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left h1 h0
        _ = 1/(q:ℝ) := by ring
    have h3 : (1:ℝ)/(q:ℝ) ≤ 2/(q:ℝ) := by
      rw [div_le_div_iff₀ hqpos hqpos]; linarith
    have h4 : (0:ℝ) ≤ 32/(s:ℝ)^2 := div_nonneg (by norm_num) (sq_nonneg _)
    linarith
  · obtain ⟨k0, hk0eq⟩ := Finset.card_eq_one.mp h1
    have hk0mem : k0 ∈ u := by rw [hk0eq]; exact Finset.mem_singleton_self k0
    have hk2 : k0 ≤ q / 2 := hu2 k0 hk0mem
    have hkK : blkK a q k0 = 1 := hu k0 hk0mem
    have hk0q : k0 ≤ q := by omega
    rw [hk0eq, Finset.sum_singleton]
    have hDsum : (1:ℝ)/2 ≤ blkD α q (q - k0) + blkD α q q := by
      have h1 : (blkK a q k0 : ℝ) - (k0:ℝ)/(q:ℝ) ≤ blkD α q k0 := blkD_ge α a q hq hα k0
      have h2 : blkD α q k0 ≤ blkD α q (q - k0) + blkD α q q := by
        rw [blkD, blkD, blkD]
        have hkey : fracDist ((k0:ℝ)*α) ≤ fracDist ((q:ℝ)*α) + fracDist (((q-k0:ℕ):ℝ)*α) := by
          have h := fracDist_add_le ((q:ℝ)*α) (-(((q-k0:ℕ):ℝ)*α))
          have he : (q:ℝ)*α + (-(((q-k0:ℕ):ℝ)*α)) = (k0:ℝ)*α := by
            rw [Nat.cast_sub hk0q]
            push_cast
            ring
          rwa [he, fracDist_neg] at h
        calc (q:ℝ) * fracDist ((k0:ℝ)*α)
            ≤ (q:ℝ) * (fracDist ((q:ℝ)*α) + fracDist (((q-k0:ℕ):ℝ)*α)) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
          _ = (q:ℝ) * fracDist (((q-k0:ℕ):ℝ)*α) + (q:ℝ) * fracDist ((q:ℝ)*α) := by ring
      have hk0half : (k0:ℝ) ≤ (q:ℝ)/2 := by
        have hh : (2 * k0 : ℕ) ≤ q := by omega
        have hh' : (2:ℝ) * (k0:ℝ) ≤ (q:ℝ) := by exact_mod_cast hh
        linarith
      have h3 : (1:ℝ)/2 ≤ (blkK a q k0 : ℝ) - (k0:ℝ)/(q:ℝ) := by
        rw [hkK]
        push_cast
        have hk0q2 : (k0:ℝ)/(q:ℝ) ≤ 1/2 := by
          rw [div_le_iff₀ hqpos]
          linarith
        linarith
      linarith
    have hfwcomb : fw s (blkD α q (q - k0)) + fw s (blkD α q q) ≤ 1 + 16/(s:ℝ)^2 :=
      fw_sum_le s hs1r (blkD_nonneg α q _) (blkD_nonneg α q _) hDsum
    have hc1 : (1/(((q - k0 : ℕ):ℝ))) ≤ 2/(q:ℝ) := by
      have hcast : (((q - k0 : ℕ)) : ℝ) = (q:ℝ) - (k0:ℝ) := Nat.cast_sub hk0q
      have h2' : (q:ℝ)/2 ≤ (q:ℝ) - (k0:ℝ) := by
        have hh : (2 * k0 : ℕ) ≤ q := by omega
        have hh' : (2:ℝ) * (k0:ℝ) ≤ (q:ℝ) := by exact_mod_cast hh
        linarith
      rw [hcast]
      calc (1:ℝ)/((q:ℝ) - (k0:ℝ)) ≤ 1/((q:ℝ)/2) := one_div_le_one_div_of_le (by linarith) h2'
        _ = 2/(q:ℝ) := by ring
    have hc2 : (1:ℝ)/(q:ℝ) ≤ 2/(q:ℝ) := by
      rw [div_le_div_iff₀ hqpos hqpos]; linarith
    calc blkG α q s (q - k0) + blkG α q s q
        = (1/(((q - k0 : ℕ):ℝ))) * fw s (blkD α q (q - k0))
          + (1/(q:ℝ)) * fw s (blkD α q q) := rfl
      _ ≤ (2/(q:ℝ)) * fw s (blkD α q (q - k0)) + (2/(q:ℝ)) * fw s (blkD α q q) :=
          add_le_add (mul_le_mul_of_nonneg_right hc1 (fw_nonneg s _))
            (mul_le_mul_of_nonneg_right hc2 (fw_nonneg s _))
      _ = (2/(q:ℝ)) * (fw s (blkD α q (q - k0)) + fw s (blkD α q q)) := by ring
      _ ≤ (2/(q:ℝ)) * (1 + 16/(s:ℝ)^2) :=
          mul_le_mul_of_nonneg_left hfwcomb (by positivity)
      _ = 2/(q:ℝ) + 32/((q:ℝ)*(s:ℝ)^2) := by ring_nf
      _ ≤ 2/(q:ℝ) + 32/(s:ℝ)^2 := by
          have h4 : (32:ℝ)/((q:ℝ)*(s:ℝ)^2) ≤ 32/(s:ℝ)^2 := by
            have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
            have h1 : (s:ℝ)^2 ≤ (q:ℝ) * (s:ℝ)^2 := by
              have := mul_le_mul_of_nonneg_right hq1 (sq_nonneg (s:ℝ))
              linarith [this]
            calc (32:ℝ)/((q:ℝ)*(s:ℝ)^2) = 32 * (1/((q:ℝ)*(s:ℝ)^2)) := by ring
              _ ≤ 32 * (1/(s:ℝ)^2) :=
                  mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hs2pos h1) (by norm_num)
              _ = 32/(s:ℝ)^2 := by ring
          linarith

/-! ## The main estimate -/

theorem blk_first (α : ℝ) (a : ℤ) (q s K : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hcop : Nat.Coprime (Int.natAbs a) q) (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2)) :
    (∑ k ∈ Finset.Icc 1 (min K q),
        (1 / (k : ℝ)) * (1 + ((s : ℝ) * (q : ℝ) * fracDist ((k : ℝ) * α)) ^ 2)⁻¹)
      ≤ 50 / ((s : ℝ) ^ 2) + 2 / (q : ℝ) := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hs1 : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hstep1 : (∑ k ∈ Finset.Icc 1 (min K q),
        (1 / (k : ℝ)) * (1 + ((s : ℝ) * (q : ℝ) * fracDist ((k : ℝ) * α)) ^ 2)⁻¹)
      ≤ ∑ k ∈ Finset.Icc 1 q, blkG α q (s:ℝ) k := by
    have hcongr : (∑ k ∈ Finset.Icc 1 (min K q),
        (1 / (k : ℝ)) * (1 + ((s : ℝ) * (q : ℝ) * fracDist ((k : ℝ) * α)) ^ 2)⁻¹)
        = ∑ k ∈ Finset.Icc 1 (min K q), blkG α q (s:ℝ) k :=
      Finset.sum_congr rfl (fun k _ => blkG_eq α q (s:ℝ) k)
    rw [hcongr]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk _; exact blkG_nonneg α q (s:ℝ) k
  have hchain : ∑ k ∈ Finset.Icc 1 q, blkG α q (s:ℝ) k
      ≤ (∑ k ∈ Finset.Icc 1 (q/2), blkG α q (s:ℝ) k)
        + (∑ k' ∈ Finset.Icc 1 (q/2), blkG α q (s:ℝ) (q - k')) + blkG α q (s:ℝ) q := by
    have h1 := sum_Icc_split 1 (q/2) q (by omega) (by omega) (blkG α q (s:ℝ))
    have h2 : ∑ k ∈ Finset.Icc (q/2+1) q, blkG α q (s:ℝ) k
        ≤ ∑ k' ∈ Finset.Icc 1 (q/2), blkG α q (s:ℝ) (q - k') + blkG α q (s:ℝ) q := by
      calc ∑ k ∈ Finset.Icc (q/2+1) q, blkG α q (s:ℝ) k
          ≤ ∑ k ∈ Finset.Icc (q - q/2) q, blkG α q (s:ℝ) k := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
            · intro k _ _; exact blkG_nonneg α q (s:ℝ) k
        _ = ∑ k ∈ Finset.Icc (q - q/2) (q-1), blkG α q (s:ℝ) k + blkG α q (s:ℝ) q :=
            sum_Icc_last (q - q/2) q hq (by omega) _
        _ = ∑ k' ∈ Finset.Icc 1 (q/2), blkG α q (s:ℝ) (q - k') + blkG α q (s:ℝ) q := by
            rw [sum_Icc_rev q (q/2) hq (blkG α q (s:ℝ)) (by omega)]
    rw [h1]
    linarith [h2]
  have hA := blkG_half_block α a q s hq hs hcop hα
  have hB := blkG_second_half α a q s hq hs hcop hα
  have hsB1 : ∀ k' ∈ (Finset.Icc 1 (q / 2)).filter (fun k' => ¬ (2 ≤ blkK a q k')),
      blkK a q k' = 1 := by
    intro k' hk'
    rw [Finset.mem_filter, Finset.mem_Icc] at hk'
    have hpos := blkK_pos a q hq hcop hk'.1.1 (by omega)
    omega
  have hsB2 : ∀ k' ∈ (Finset.Icc 1 (q / 2)).filter (fun k' => ¬ (2 ≤ blkK a q k')),
      1 ≤ k' := by
    intro k' hk'
    rw [Finset.mem_filter, Finset.mem_Icc] at hk'
    exact hk'.1.1
  have hsB3 : ∀ k' ∈ (Finset.Icc 1 (q / 2)).filter (fun k' => ¬ (2 ≤ blkK a q k')),
      k' ≤ q / 2 := by
    intro k' hk'
    rw [Finset.mem_filter, Finset.mem_Icc] at hk'
    exact hk'.1.2
  have hC := blkG_sB_bound α a q s hq hs hcop hα _ hsB1 hsB2 hsB3
  refine le_trans hstep1 (le_trans hchain ?_)
  calc (∑ k ∈ Finset.Icc 1 (q/2), blkG α q (s:ℝ) k)
        + (∑ k' ∈ Finset.Icc 1 (q/2), blkG α q (s:ℝ) (q - k')) + blkG α q (s:ℝ) q
      ≤ 8 / (s:ℝ)^2
        + (1 / (s:ℝ)^2
          + ∑ k' ∈ (Finset.Icc 1 (q/2)).filter (fun k' => ¬ (2 ≤ blkK a q k')),
              blkG α q (s:ℝ) (q - k'))
        + blkG α q (s:ℝ) q := by linarith [hA, hB]
    _ = 8 / (s:ℝ)^2 + 1 / (s:ℝ)^2
        + ((∑ k' ∈ (Finset.Icc 1 (q/2)).filter (fun k' => ¬ (2 ≤ blkK a q k')),
              blkG α q (s:ℝ) (q - k')) + blkG α q (s:ℝ) q) := by ring
    _ ≤ 8 / (s:ℝ)^2 + 1 / (s:ℝ)^2 + (2/(q:ℝ) + 32/(s:ℝ)^2) := by linarith [hC]
    _ = 41 / (s:ℝ)^2 + 2/(q:ℝ) := by ring
    _ ≤ 50 / (s:ℝ)^2 + 2/(q:ℝ) := by
        have hs2 : (0:ℝ) < (s:ℝ)^2 := by nlinarith [hs1]
        have hle : (41:ℝ)/(s:ℝ)^2 ≤ 50/(s:ℝ)^2 := by
          rw [div_le_div_iff₀ hs2 hs2]; linarith
        linarith

end

end Work.TMC7Core.Fourier
