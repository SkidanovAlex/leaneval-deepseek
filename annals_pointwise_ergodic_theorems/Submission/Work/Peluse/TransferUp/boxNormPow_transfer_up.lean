import Mathlib
import Submission.Work.Peluse.Concat.boxNormPow_succ_peel_gen
import Submission.Work.Peluse.Peel.boxNormPow_diag_peel
import Submission.Work.Peluse.Track.boxNormPow_one_arithIcc_window
import Submission.Work.Peluse.TransferUp.arithIcc_pairSum
import Submission.Work.Peluse.TransferUp.windowSum_sq_eq_corr

/-!
# Two-sided scale comparability of Peluse's box norms

The target of this file is `Work.Peluse.TransferUp.boxNormPow_transfer_up`: the box-norm power at a
*shorter* scale `H'` is bounded by a constant times the box-norm power at a *longer* scale `H`,
with a power of the scale ratio `(H'/H)^e` as the loss.

The proof strategy is:

* the box-norm power at scale `H` is, up to the factor `|S|⁻¹ H^{-2^t}` of the definition, the
  average of the `2^t`-fold cube correlations `T (d₁ m₁, …, d_t m_t)` over the *kernel*
  `∏_i ψ_{H}(m_i)`, `ψ_H(m) = (H-|m|)/H` (this is the "fold" of the box sum; it follows from the
  peel identity `boxSumPow_peel` and the shift invariance of the box norm);
* the quantity `N_t(H) := |S| H^t · boxNormPow t (…)` is *nondecreasing* in `H`; that is the
  content of this file.  For `t = 2` this is proved from the identity
  `∑_e ψ_H(e) · ∑_x G x · conj (G (x + c e)) = H⁻¹ ∑_x ‖∑_{n ≤ H} G (x + c n)‖² ≥ 0`
  (a sum of squares), and for `t ≥ 3` it follows from the peel recursion
  `N_t(H) = ∑_m ψ_H(m) · N_{t-1}(H; F · conj (F (· + d₀ m)))` together with the induction
  hypothesis applied to the *products* `F · conj (F (· + d₀ m))`.

The target follows with `c = 1`, `e = t`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace Work.Peluse.TransferUp

noncomputable section

open Work.Peluse

/-! ## The kernel `ψ` -/

/-- `ψ_H(m) = (H - |m|)/H` for `|m| ≤ H` and `0` for `|m| ≥ H`. -/
def psi (H : ℕ) (m : ℤ) : ℝ := (((H - m.natAbs : ℕ)) : ℝ) / (H : ℝ)

lemma psi_nonneg (H : ℕ) (m : ℤ) : 0 ≤ psi H m := by
  unfold psi
  positivity

lemma psi_eq_zero_of_le {H : ℕ} {m : ℤ} (h : H ≤ m.natAbs) : psi H m = 0 := by
  unfold psi
  rw [Nat.sub_eq_zero_of_le h]
  simp

lemma psi_eq_one_sub {H : ℕ} {m : ℤ} (hle : m.natAbs ≤ H) (hH : H ≠ 0) :
    psi H m = 1 - (m.natAbs : ℝ) / (H : ℝ) := by
  unfold psi
  rw [Nat.cast_sub hle]
  have hH' : (H : ℝ) ≠ 0 := by exact_mod_cast hH
  field_simp

lemma psi_mono {H' H : ℕ} (h : H' ≤ H) (m : ℤ) : psi H' m ≤ psi H m := by
  rcases Nat.eq_zero_or_pos H' with h0 | h0
  · subst h0
    rw [show psi 0 m = 0 from psi_eq_zero_of_le (Nat.zero_le _)]
    exact psi_nonneg H m
  · have hpos : (0 : ℝ) < (H' : ℝ) := by exact_mod_cast h0
    by_cases hle : m.natAbs ≤ H'
    · rw [psi_eq_one_sub hle (by omega), psi_eq_one_sub (le_trans hle h) (by omega)]
      have h2 : (0 : ℝ) ≤ (m.natAbs : ℝ) := by positivity
      have h3 : (m.natAbs : ℝ) / (H : ℝ) ≤ (m.natAbs : ℝ) / (H' : ℝ) :=
        div_le_div_of_nonneg_left h2 hpos (by exact_mod_cast h)
      linarith
    · rw [show psi H' m = 0 from psi_eq_zero_of_le (le_of_lt (not_le.mp hle))]
      exact psi_nonneg H m

lemma psi_cast_mul (H : ℕ) (m : ℤ) :
    psi H m * (H : ℝ) = (((H - m.natAbs : ℕ)) : ℝ) := by
  unfold psi
  rcases Nat.eq_zero_or_pos H with h | h
  · subst h; simp
  · field_simp

/-! ## The correlations -/

/-- The `1`-dimensional correlation `∑_x G x · conj (G (x + z))`. -/
def corr (G : ℤ → ℂ) (z : ℤ) : ℂ := ∑' x : ℤ, G x * star (G (x + z))

lemma corr_symm (F : ℤ → ℂ) (a b : ℤ) :
    corr (fun y : ℤ => F y * star (F (y + a))) b
      = corr (fun y : ℤ => F y * star (F (y + b))) a := by
  unfold corr
  refine tsum_congr (fun x => ?_)
  have hab : x + b + a = x + a + b := by ring
  simp only [star_mul, star_star]
  rw [hab]
  ring

/-! ## The level-one box-norm power over an arithmetic progression -/

/-- **Level-one box norm as a window-sum.**  For `d ≠ 0`, the level-one box-norm power with the
direction set `d[H]` is `(|S| H²)⁻¹` times the `ℓ²`-norm of the sliding window sums
`∑_{n ≤ H} G (x + d n)`. -/
theorem boxNormPow_one_arithIcc (d : ℤ) (hd : d ≠ 0) (H : ℕ) (S : Finset ℤ) (G : ℤ → ℂ)
    (hG : Work.Peluse.FinSuppZ G) :
    Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Work.Peluse.arithIcc d H) S G
      = ((S.card : ℝ))⁻¹ * ((H : ℝ))⁻¹ ^ 2 *
          ∑' x : ℤ, ‖∑ n ∈ Finset.Icc 1 H, G (x + d * (n : ℤ))‖ ^ 2 := by
  obtain ⟨N, hN⟩ := hG
  rw [Work.Peluse.Peel.boxNormPow_one_tsum (N := N) (Q := Work.Peluse.arithIcc d H)
      (S := S) hN,
    Work.Peluse.BoxNormDilation.card_arithIcc hd H]
  congr 1
  refine tsum_congr (fun x => ?_)
  rw [Work.Peluse.Track.sum_arithIcc_eq_Icc hd H G x]

/-! ## The monotone quantity -/

/-- `Npow t d S F H = |S| H^t ‖F‖^{2^t}_{□^t_{d₁[H],…,d_t[H]}(S)}`: the box-norm power
normalised by `|S|` (which cancels the `|S|⁻¹` of `boxNormPow`) and multiplied by `H^t`.  This is
the quantity that is *nondecreasing* in `H`. -/
def Npow (t : ℕ) (d : Fin t → ℤ) (S : Finset ℤ) (F : ℤ → ℂ) (H : ℕ) : ℝ :=
  (S.card : ℝ) * (H : ℝ) ^ t *
    Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) H) S F

lemma Npow_nonneg (t : ℕ) (d : Fin t → ℤ) (S : Finset ℤ) (F : ℤ → ℂ) (H : ℕ) :
    0 ≤ Npow t d S F H := by
  unfold Npow
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
    (by rw [Work.Peluse.boxNormPow]; exact norm_nonneg _)

/-! ## Auxiliary set manipulations -/

/-- A product of `F` with the conjugate of a translate of `F` is finitely supported. -/
lemma finSuppZ_mul_star_shift' {F : ℤ → ℂ} (hF : Work.Peluse.FinSuppZ F) (δ : ℤ) :
    Work.Peluse.FinSuppZ (fun y : ℤ => F y * star (F (y + δ))) := by
  obtain ⟨N, hN⟩ := hF
  refine ⟨max N (N + δ.natAbs), fun y hy => ?_⟩
  change F y * star (F (y + δ)) = 0
  have h1 : F y = 0 := hN y (lt_of_le_of_lt (le_max_left _ _) hy)
  rw [h1, zero_mul]

/-- For `|m| ≥ H` the kernel `ψ H` vanishes. -/
lemma psi_mul_eq_zero_of_le {H : ℕ} {m : ℤ} (h : H ≤ m.natAbs) (X : ℝ) :
    psi H m * X = 0 := by
  rw [psi_eq_zero_of_le h, zero_mul]

/-- The sum over the larger index set `[-H,H]` of a `ψ H`-weighted family equals the sum over
`[-(H-1),H-1]`: the two extra terms carry the coefficient `0`. -/
lemma sum_Icc_psi_eq (H : ℕ) (X : ℤ → ℝ) :
    (∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), psi H m * X m)
      = ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), psi H m * X m := by
  symm
  refine Finset.sum_subset ?_ ?_
  · intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    omega
  · intro m hm hnot
    have h1 : -(H : ℤ) ≤ m ∧ m ≤ (H : ℤ) := by simpa [Finset.mem_Icc] using hm
    have h2 : ¬ (-(H : ℤ) + 1 ≤ m ∧ m ≤ (H : ℤ) - 1) := by
      simpa [Finset.mem_Icc] using hnot
    have h3 : m = -(H : ℤ) ∨ m = (H : ℤ) := by omega
    rcases h3 with h3 | h3
    · subst h3
      exact psi_mul_eq_zero_of_le (H := H) (m := -(H : ℤ))
        (by rw [Int.natAbs_neg, Int.natAbs_natCast]) (X (-(H : ℤ)))
    · subst h3
      exact psi_mul_eq_zero_of_le (H := H) (m := (H : ℤ))
        (by rw [Int.natAbs_natCast]) (X (H : ℤ))

/-- For `H' ≤ H` the `ψ H'`-weighted sum over `[-(H-1),H-1]` equals the one over
`[-(H'-1),H'-1]`: the extra terms vanish. -/
lemma sum_Icc_psi_congr {H' H : ℕ} (h : H' ≤ H) (X : ℤ → ℝ) :
    (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), psi H' m * X m)
      = ∑ m ∈ Finset.Icc (-(H' : ℤ) + 1) ((H' : ℤ) - 1), psi H' m * X m := by
  symm
  refine Finset.sum_subset ?_ ?_
  · intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    omega
  · intro m hm hnot
    have h1 : -(H : ℤ) + 1 ≤ m ∧ m ≤ (H : ℤ) - 1 := by simpa [Finset.mem_Icc] using hm
    have h2 : ¬ (-(H' : ℤ) + 1 ≤ m ∧ m ≤ (H' : ℤ) - 1) := by
      simpa [Finset.mem_Icc] using hnot
    have h3 : H' ≤ m.natAbs := by
      rcases lt_or_ge m (-(H' : ℤ) + 1) with hlt | hge
      · have hle : (H' : ℤ) ≤ -m := by omega
        have := Int.le_natAbs (a := -m)
        rw [Int.natAbs_neg] at this
        omega
      · have hle : (H' : ℤ) ≤ m := by omega
        have := Int.le_natAbs (a := m)
        omega
    exact psi_mul_eq_zero_of_le h3 (X m)

/-! ## The peel recursion at the level of the box-norm power -/

/-- **The peel recursion.**  The box-norm power of order `t+1` over the arithmetic progressions
`d₀[H], …, d_t[H]` is the kernel average, over the *first* difference `m`, of the box-norm powers
of order `t` of the products `F · conj (F (· + d₀ m))`. -/
theorem boxNormPow_succ_recursion {t : ℕ} (ht : 1 ≤ t) (d : Fin (t+1) → ℤ) (hd0 : d 0 ≠ 0)
    (S : Finset ℤ) (F : ℤ → ℂ) (hF : Work.Peluse.FinSuppZ F) (H : ℕ) :
    Work.Peluse.boxNormPow (t+1) (fun i : Fin (t+1) => Work.Peluse.arithIcc (d i) H) S F
      = ((H : ℝ)^2)⁻¹ * ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          (((H - m.natAbs : ℕ)) : ℝ) *
            Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i.succ) H) S
              (fun y : ℤ => F y * star (F (y + d 0 * m))) := by
  classical
  set Ψ : ℤ → ℝ := fun z => Work.Peluse.boxNormPow t
      (fun i : Fin t => Work.Peluse.arithIcc (d i.succ) H) S
      (fun y : ℤ => F y * star (F (y + z))) with hΨ
  have hpeel := Work.Peluse.Concat.boxNormPow_succ_peel_gen ht
      (fun i : Fin (t+1) => Work.Peluse.arithIcc (d i) H) S hF
  have hcard : ((fun i : Fin (t+1) => Work.Peluse.arithIcc (d i) H) 0).card = H :=
    Work.Peluse.BoxNormDilation.card_arithIcc hd0 H
  have hstep : ∀ h h' : ℤ,
      Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i.succ) H) S
          (fun u : ℤ => F (u + h) * star (F (u + h'))) = Ψ (h' - h) := by
    intro h h'
    rw [hΨ]
    simp only
    rw [show (fun u : ℤ => F (u + h) * star (F (u + h')))
        = Work.Peluse.shift h (fun y : ℤ => F y * star (F (y + (h' - h)))) from by
      funext u; simp only [Work.Peluse.shift]; congr 1; ring]
    exact Work.Peluse.BoxNorm.boxNormPow_shift t _ S _ h (finSuppZ_mul_star_shift' hF (h' - h))
  have hpair := arithIcc_pairSum (c := d 0) hd0 H (fun z : ℤ => ((Ψ z : ℝ) : ℂ))
  have hreal : (∑ h ∈ Work.Peluse.arithIcc (d 0) H,
        ∑ h' ∈ Work.Peluse.arithIcc (d 0) H, Ψ (h' - h))
      = ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          (((H - m.natAbs : ℕ)) : ℝ) * Ψ (d 0 * m) := by
    have := congrArg Complex.re hpair
    simpa [Complex.ofReal_re] using this
  rw [hpeel]
  rw [show ((fun i : Fin (t+1) => Work.Peluse.arithIcc (d i) H) 0).card = H from hcard]
  rw [Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => hstep h h'))]
  rw [hreal, inv_pow]

/-! ## The level-one window identity -/

/-- The `ψ`-weighted correlation sum is `H⁻¹` times the `ℓ²`-norm of the window sums. -/
lemma sum_psi_corr_eq (d : ℤ) (H : ℕ) (G : ℤ → ℂ) (hG : Work.Peluse.FinSuppZ G) :
    (∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), psi H e * (corr G (d * e)).re)
      = (H : ℝ)⁻¹ * ∑' x : ℤ, ‖∑ n ∈ Finset.Icc 1 H, G (x + d * (n : ℤ))‖ ^ 2 := by
  have hL1 := windowSum_sq_eq_corr (H := H) (c := d) (G := G) hG
  have hre : (∑' x : ℤ, ‖∑ n ∈ Finset.Icc 1 H, G (x + d * (n : ℤ))‖ ^ 2)
      = ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          (((H - e.natAbs : ℕ)) : ℝ) * (corr G (d * e)).re := by
    have := congrArg Complex.re hL1
    simpa [Complex.ofReal_re, corr] using this
  rw [hre]
  rcases Nat.eq_zero_or_pos H with h | h
  · subst h
    simp
  · have hH : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [← psi_cast_mul H e]
    field_simp

/-- The `ψ`-weighted correlation sum is nonnegative. -/
lemma sum_psi_corr_nonneg (d : ℤ) (H : ℕ) (G : ℤ → ℂ) (hG : Work.Peluse.FinSuppZ G) :
    0 ≤ ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), psi H e * (corr G (d * e)).re := by
  rw [sum_psi_corr_eq d H G hG]
  have h1 : 0 ≤ ∑' x : ℤ, ‖∑ n ∈ Finset.Icc 1 H, G (x + d * (n : ℤ))‖ ^ 2 :=
    tsum_nonneg (fun x => by positivity)
  rcases Nat.eq_zero_or_pos H with h | h
  · subst h; simp
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) h1

/-! ## The recursion for `Npow` -/

/-- The peel recursion in the normalised form: `Npow (t+1) H` is the `ψ H`-kernel average of the
`Npow t H` of the products. -/
theorem Npow_succ {t : ℕ} (ht : 1 ≤ t) (d : Fin (t+1) → ℤ) (hd0 : d 0 ≠ 0) (S : Finset ℤ)
    (F : ℤ → ℂ) (hF : Work.Peluse.FinSuppZ F) {H : ℕ} (hH : 1 ≤ H) :
    Npow (t+1) d S F H
      = ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), psi H m *
          Npow t (fun i : Fin t => d i.succ) S
            (fun y : ℤ => F y * star (F (y + d 0 * m))) H := by
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp (by omega : 0 < H))
  have hrec := boxNormPow_succ_recursion ht d hd0 S F hF H
  have hpt : ∀ m : ℤ,
      (S.card : ℝ) * (H : ℝ) ^ (t+1) *
          (((H : ℝ) ^ 2)⁻¹ *
            (((((H - m.natAbs : ℕ)) : ℝ)) *
              Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i.succ) H) S
                (fun y : ℤ => F y * star (F (y + d 0 * m)))))
        = psi H m * ((S.card : ℝ) * (H : ℝ) ^ t *
            Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i.succ) H) S
              (fun y : ℤ => F y * star (F (y + d 0 * m)))) := by
    intro m
    have hcast : (H : ℝ) ^ (t + 1) = (H : ℝ) ^ t * H := by rw [pow_succ]
    have hpsi : psi H m * (H : ℝ) = (((H - m.natAbs : ℕ)) : ℝ) := psi_cast_mul H m
    rw [hcast, ← hpsi]
    field_simp
    try ring
  unfold Npow
  rw [hrec]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => hpt m)

/-- The level-one `Npow` in window form. -/
theorem Npow_one_eq (d : Fin 1 → ℤ) (hd : d 0 ≠ 0) (S : Finset ℤ) (G : ℤ → ℂ)
    (hG : Work.Peluse.FinSuppZ G) {H : ℕ} (hS : 0 < S.card) :
    Npow 1 d S G H
      = (H : ℝ)⁻¹ * ∑' x : ℤ, ‖∑ n ∈ Finset.Icc 1 H, G (x + d 0 * (n : ℤ))‖ ^ 2 := by
  have hfun : (fun i : Fin 1 => Work.Peluse.arithIcc (d i) H)
      = (fun _ : Fin 1 => Work.Peluse.arithIcc (d 0) H) := by
    funext i; fin_cases i; rfl
  have hScard : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hS)
  unfold Npow
  rw [hfun, boxNormPow_one_arithIcc (d 0) hd H S G hG]
  field_simp

/-! ## The base case: `Npow 2` is nondecreasing -/

/-- The `(m,e)`-double sum in which `Npow 2` is expressed. -/
def TwoSum (d : Fin 2 → ℤ) (S : Finset ℤ) (F : ℤ → ℂ) (H : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
    psi H m * (∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
      psi H e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re)

/-- `Npow 2` is the `(m,e)`-double sum of the `ψ ψ`-weighted correlations. -/
theorem Npow_two_eq {d : Fin 2 → ℤ} (hd : ∀ i, d i ≠ 0) (S : Finset ℤ) (F : ℤ → ℂ)
    (hF : Work.Peluse.FinSuppZ F) (hS : 0 < S.card) {H : ℕ} (hH : 1 ≤ H) :
    Npow 2 d S F H = TwoSum d S F H := by
  have hfun : (fun i : Fin 1 => d i.succ) = (fun _ : Fin 1 => d 1) := by
    funext i; fin_cases i; rfl
  unfold TwoSum
  rw [Npow_succ (t := 1) le_rfl d (hd 0) S F hF (H := H) hH]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [hfun, Npow_one_eq (fun _ : Fin 1 => d 1) (by simpa using hd 1) S _
      (finSuppZ_mul_star_shift' hF (d 0 * m)) hS]
  rw [← sum_psi_corr_eq (d 1) H (fun y : ℤ => F y * star (F (y + d 0 * m)))
      (finSuppZ_mul_star_shift' hF (d 0 * m))]

/-- **The base case.** `Npow 2` is nondecreasing in the scale. -/
theorem Npow_two_mono {d : Fin 2 → ℤ} (hd : ∀ i, d i ≠ 0) (S : Finset ℤ) (F : ℤ → ℂ)
    (hF : Work.Peluse.FinSuppZ F) (hS : 0 < S.card) {H' H : ℕ} (h1 : 1 ≤ H') (h2 : H' ≤ H) :
    Npow 2 d S F H' ≤ Npow 2 d S F H := by
  have hH1 : 1 ≤ H := le_trans h1 h2
  rw [Npow_two_eq hd S F hF hS h1, Npow_two_eq hd S F hF hS hH1]
  unfold TwoSum
  -- the `H'`-double sum, extended to the common index set
  have hfull : (∑ m ∈ Finset.Icc (-(H' : ℤ) + 1) ((H' : ℤ) - 1),
        psi H' m * (∑ e ∈ Finset.Icc (-(H' : ℤ) + 1) ((H' : ℤ) - 1),
          psi H' e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re))
      = ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
        psi H' m * (∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          psi H' e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re) := by
    rw [← sum_Icc_psi_congr h2 (fun m => ∑ e ∈ Finset.Icc (-(H' : ℤ) + 1) ((H' : ℤ) - 1),
        psi H' e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re)]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    congr 1
    exact (sum_Icc_psi_congr h2
      (fun e => (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re)).symm
  rw [hfull]
  -- rewrite the nested sums as double sums
  rw [show (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), psi H' m *
        (∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          psi H' e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re))
      = ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
        ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          psi H' m * (psi H' e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re) from by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum],
    show (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), psi H m *
        (∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          psi H e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re))
      = ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
        ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          psi H m * (psi H e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re) from by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]]
  -- the algebraic decomposition of the difference of the two common sums
  have key : (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
            psi H m * (psi H e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re))
        - (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
            psi H' m * (psi H' e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re))
      = (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
            ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
              (psi H m - psi H' m) *
                (psi H e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re))
        + (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
            ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
              (psi H e - psi H' e) *
                (psi H' m * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
  have hT1 : 0 ≤ ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
            ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
              (psi H m - psi H' m) *
                (psi H e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re) := by
    rw [show (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
            ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
              (psi H m - psi H' m) *
                (psi H e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re))
        = ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), (psi H m - psi H' m) *
            (∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
              psi H e * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re) from by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]]
    refine Finset.sum_nonneg (fun m _ => mul_nonneg (sub_nonneg.mpr (psi_mono h2 m)) ?_)
    exact sum_psi_corr_nonneg (d 1) H _ (finSuppZ_mul_star_shift' hF (d 0 * m))
  have hT2 : 0 ≤ ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
            ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
              (psi H e - psi H' e) *
                (psi H' m * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re) := by
    rw [show (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
            ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
              (psi H e - psi H' e) *
                (psi H' m * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re))
        = ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), (psi H e - psi H' e) *
            (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
              psi H' m * (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re) from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [Finset.mul_sum]]
    refine Finset.sum_nonneg (fun e _ => mul_nonneg (sub_nonneg.mpr (psi_mono h2 e)) ?_)
    have h1' : (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), psi H' m *
          (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re)
        = ∑ m ∈ Finset.Icc (-(H' : ℤ) + 1) ((H' : ℤ) - 1), psi H' m *
          (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re :=
      sum_Icc_psi_congr h2
        (fun m => (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re)
    rw [h1']
    rw [show (∑ m ∈ Finset.Icc (-(H' : ℤ) + 1) ((H' : ℤ) - 1), psi H' m *
          (corr (fun y : ℤ => F y * star (F (y + d 0 * m))) (d 1 * e)).re)
        = ∑ m ∈ Finset.Icc (-(H' : ℤ) + 1) ((H' : ℤ) - 1), psi H' m *
          (corr (fun y : ℤ => F y * star (F (y + d 1 * e))) (d 0 * m)).re from by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [corr_symm F (d 0 * m) (d 1 * e)]]
    exact sum_psi_corr_nonneg (d 0) H' _ (finSuppZ_mul_star_shift' hF (d 1 * e))
  linarith [key, hT1, hT2]

/-! ## The induction -/

/-- **Monotonicity of `Npow`.**  For `t ≥ 2` the quantity `Npow t H = |S| H^t ‖F‖^{2^t}` is
nondecreasing in the scale `H`. -/
theorem Npow_mono : ∀ t : ℕ, 2 ≤ t → ∀ (d : Fin t → ℤ), (∀ i, d i ≠ 0) → ∀ (S : Finset ℤ),
    0 < S.card → ∀ (F : ℤ → ℂ), Work.Peluse.FinSuppZ F → ∀ {H' H : ℕ}, 1 ≤ H' → H' ≤ H →
      Npow t d S F H' ≤ Npow t d S F H := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ t ih =>
    intro ht d hd S hS F hF H' H h1 h2
    rcases lt_or_ge t 2 with hlt | hge
    · have h1' : t = 1 := by omega
      subst h1'
      exact Npow_two_mono hd S F hF hS h1 h2
    · have ht' : 1 ≤ t := by omega
      have hH : 1 ≤ H := le_trans h1 h2
      rw [Npow_succ ht' d (hd 0) S F hF hH,
        Npow_succ ht' d (hd 0) S F hF h1]
      rw [← sum_Icc_psi_congr h2
        (fun m => Npow t (fun i : Fin t => d i.succ) S
            (fun y : ℤ => F y * star (F (y + d 0 * m))) H')]
      have key : (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), psi H m *
              Npow t (fun i : Fin t => d i.succ) S
                (fun y : ℤ => F y * star (F (y + d 0 * m))) H)
          - (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), psi H' m *
              Npow t (fun i : Fin t => d i.succ) S
                (fun y : ℤ => F y * star (F (y + d 0 * m))) H')
          = (∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), psi H m *
                (Npow t (fun i : Fin t => d i.succ) S
                    (fun y : ℤ => F y * star (F (y + d 0 * m))) H
                  - Npow t (fun i : Fin t => d i.succ) S
                    (fun y : ℤ => F y * star (F (y + d 0 * m))) H'))
            + ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), (psi H m - psi H' m) *
                Npow t (fun i : Fin t => d i.succ) S
                  (fun y : ℤ => F y * star (F (y + d 0 * m))) H' := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        ring
      have hA : 0 ≤ ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), psi H m *
                (Npow t (fun i : Fin t => d i.succ) S
                    (fun y : ℤ => F y * star (F (y + d 0 * m))) H
                  - Npow t (fun i : Fin t => d i.succ) S
                    (fun y : ℤ => F y * star (F (y + d 0 * m))) H') := by
        refine Finset.sum_nonneg (fun m _ => ?_)
        have hih := ih hge (fun i : Fin t => d i.succ) (fun i => hd i.succ) S hS
          (fun y : ℤ => F y * star (F (y + d 0 * m)))
          (finSuppZ_mul_star_shift' hF (d 0 * m)) h1 h2
        exact mul_nonneg (psi_nonneg H m) (sub_nonneg.mpr hih)
      have hB : 0 ≤ ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), (psi H m - psi H' m) *
                Npow t (fun i : Fin t => d i.succ) S
                  (fun y : ℤ => F y * star (F (y + d 0 * m))) H' := by
        refine Finset.sum_nonneg (fun m _ => ?_)
        exact mul_nonneg (sub_nonneg.mpr (psi_mono h2 m))
          (Npow_nonneg t (fun i : Fin t => d i.succ) S _ H')
      linarith [key, hA, hB]

/-! ## The target -/

theorem boxNormPow_transfer_up {k : ℕ} (hk : 2 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ (N : ℕ) (F : ℤ → ℂ), (∀ x : ℤ, ‖F x‖ ≤ 1) →
      Work.Peluse.SupportIn F N → ∀ (d : Fin k → ℤ), (∀ i, d i ≠ 0) →
      ∀ (H' H : ℕ), 1 ≤ H' → H' ≤ H → (∀ i, |d i| * (H : ℤ) ≤ 2 * (N : ℤ)) →
        c * (((H' : ℝ) / (H : ℝ)) ^ e) *
            Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H') (Work.Peluse.symIcc N) F
          ≤ Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H) (Work.Peluse.symIcc N) F := by
  refine ⟨1, one_pos, k, ?_⟩
  intro N F _hFb hFs d hd H' H h1 h2 _hdir
  have hS : 0 < (Work.Peluse.symIcc N).card := by
    rw [Work.Peluse.symIcc]
    apply Finset.card_pos.mpr
    exact ⟨0, by simp⟩
  have hmono := Npow_mono k hk d hd (Work.Peluse.symIcc N) hS F
      (Work.Peluse.FinSuppZ.of_supportIn hFs) h1 h2
  simp only [one_mul]
  have hmono' : (H' : ℝ) ^ k *
      Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H') (Work.Peluse.symIcc N) F
      ≤ (H : ℝ) ^ k *
      Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H) (Work.Peluse.symIcc N) F := by
    have hS' : (0 : ℝ) < ((Work.Peluse.symIcc N).card : ℝ) := by exact_mod_cast hS
    have h := hmono
    simp only [Npow] at h
    have h' : ((Work.Peluse.symIcc N).card : ℝ) *
        ((H' : ℝ) ^ k * Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H') (Work.Peluse.symIcc N) F)
        ≤ ((Work.Peluse.symIcc N).card : ℝ) *
        ((H : ℝ) ^ k * Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H) (Work.Peluse.symIcc N) F) := by
      nlinarith [h]
    exact le_of_mul_le_mul_left h' hS'
  have hle : (((H' : ℝ) / (H : ℝ)) ^ k) *
      Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H') (Work.Peluse.symIcc N) F
      ≤ Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H) (Work.Peluse.symIcc N) F := by
    have hHpos : (0 : ℝ) < (H : ℝ) ^ k := by
      exact pow_pos (by exact_mod_cast (by omega : 0 < H)) k
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hHpos]
    calc (H' : ℝ) ^ k *
          Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H') (Work.Peluse.symIcc N) F
        ≤ (H : ℝ) ^ k *
          Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H) (Work.Peluse.symIcc N) F := hmono'
      _ = Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H) (Work.Peluse.symIcc N) F *
          (H : ℝ) ^ k := by ring
  exact hle

end

end Work.Peluse.TransferUp
