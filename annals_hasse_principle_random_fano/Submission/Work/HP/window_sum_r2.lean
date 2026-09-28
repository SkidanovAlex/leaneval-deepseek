import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.WinR2Defs

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP

/-! ## Auxiliary lemmas for `window_sum_r2` -/

/-- The product of the window thresholds clears the three denominators of `winBp`:
the exponent `(n+2)k₀ + nk₁` with which `hnum` counts a window is exactly two more
(in each coordinate) than the exponents appearing in `winS`, which are precisely the
denominators of `winBp`. -/
lemma win_bp_mul (n : ℕ) (hn : 2 ≤ n) (Ksmall X Y : ℝ) (hX : 0 ≤ X) (k : Fin 2 → ℕ) :
    (∏ j : Fin 2, ((2 : ℝ) ^ (k j)) ^ (winE n j)) * winBp Ksmall X Y k
      ≤ Ksmall ^ 2 * 16 * winS n X Y k := by
  have hP : (∏ j : Fin 2, ((2 : ℝ) ^ (k j)) ^ (winE n j))
      = (2 : ℝ) ^ ((n + 2) * k 0 + n * k 1) := by
    rw [Fin.prod_univ_two, winE_zero, winE_one, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  have e1 : (n + 2) * k 0 + n * k 1
      = (n * k 0 + (n - 2) * k 1) + (2 * k 0 + 2 * k 1) := by
    have h1 : (n + 2) * k 0 = n * k 0 + 2 * k 0 := by ring
    have h2 : n * k 1 = (n - 2) * k 1 + 2 * k 1 := by
      conv_lhs => rw [← Nat.sub_add_cancel hn]
      rw [add_mul]
    rw [h1, h2]; ring
  have e2 : (n + 2) * k 0 + n * k 1
      = (n * k 0 + (n - 1) * k 1) + (2 * k 0 + k 1) := by
    have hn1 : 1 ≤ n := by omega
    have h1 : (n + 2) * k 0 = n * k 0 + 2 * k 0 := by ring
    have h2 : n * k 1 = (n - 1) * k 1 + k 1 := by
      conv_lhs => rw [← Nat.sub_add_cancel hn1]
      rw [add_mul, one_mul]
    rw [h1, h2]; ring
  have e3 : (n + 2) * k 0 + n * k 1
      = ((n + 1) * k 0 + (n - 1) * k 1) + (k 0 + k 1) := by
    have hn1 : 1 ≤ n := by omega
    have h1 : (n + 2) * k 0 = (n + 1) * k 0 + k 0 := by ring
    have h2 : n * k 1 = (n - 1) * k 1 + k 1 := by
      conv_lhs => rw [← Nat.sub_add_cancel hn1]
      rw [add_mul, one_mul]
    rw [h1, h2]; ring
  have ew1 : n * k 0 + (n - 2) * k 1 = (n + 1 - 1) * k 0 + (n + 1 - 3) * k 1 := by
    have a : n + 1 - 1 = n := by omega
    have b : n + 1 - 3 = n - 2 := by omega
    rw [a, b]
  have ew2 : n * k 0 + (n - 1) * k 1 = (n + 1 - 1) * k 0 + (n + 1 - 2) * k 1 := by
    have a : n + 1 - 1 = n := by omega
    have b : n + 1 - 2 = n - 1 := by omega
    rw [a, b]
  have ew3 : (n + 1) * k 0 + (n - 1) * k 1 = (n + 1) * k 0 + (n + 1 - 2) * k 1 := by
    have b : n + 1 - 2 = n - 1 := by omega
    rw [b]
  have h1 : (2 : ℝ) ^ ((n + 2) * k 0 + n * k 1)
        * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1)))
      = (16 * X ^ 2 * Y ^ 2) * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1) := by
    rw [← ew1, e1, pow_add, ← pow_add]
    field_simp
    ring
  have h2 : (2 : ℝ) ^ ((n + 2) * k 0 + n * k 1)
        * (8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1)))
      = (8 * X * Y ^ 2) * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1) := by
    rw [← ew2, e2, pow_add, ← pow_add]
    field_simp
    ring
  have h3 : (2 : ℝ) ^ ((n + 2) * k 0 + n * k 1)
        * (4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))
      = (4 * Y ^ 2) * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1) := by
    rw [← ew3, e3, pow_add, ← pow_add]
    field_simp
    ring
  have hp : (0 : ℝ) ≤ X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1) := by
    positivity
  have hq : (0 : ℝ) ≤ X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1) := by
    positivity
  have hr : (0 : ℝ) ≤ Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1) := by
    positivity
  have hdist : (2 : ℝ) ^ ((n + 2) * k 0 + n * k 1)
        * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
          + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
          + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))
      = 16 * (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1))
          + 8 * (X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1))
          + 4 * (Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)) := by
    rw [mul_add, mul_add, h1, h2, h3]
    ring
  have hmain : (2 : ℝ) ^ ((n + 2) * k 0 + n * k 1) * winBp Ksmall X Y k
      = Ksmall ^ 2 * (16 * (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1))
          + 8 * (X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1))
          + 4 * (Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1))) := by
    rw [winBp, ← hdist]
    ring
  rw [hP, hmain, winS]
  nlinarith [sq_nonneg Ksmall, hp, hq, hr]

/-- The number of lattices of `T` lying in a fixed dyadic window `k` is bounded by
`hnum` at scale `2 ^ k`. -/
theorem win_fiber_card (n : ℕ) (hn : 2 ≤ n)
    (Knum : ℝ) (hKnum : 0 < Knum)
    (hnum : ∀ (s : Fin 2 → ℝ) (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))), (∀ j, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j) →
      ((F.card : ℝ) ≤ Knum * ∏ j : Fin 2, s j ^ (n + 1 + 2 + 1 - 2 * (j.1 + 1))))
    (hwin1 : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = 2 →
      ∀ j : Fin 2, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin 2 L j))
    (T : Finset (Submodule ℤ (Fin (n + 1) → ℤ)))
    (hT : ∀ L ∈ T, IsPrimLat L ∧ rk L = 2)
    (k : Fin 2 → ℕ) :
    (((T.filter (fun L => kwin 2 L = k)).card : ℕ) : ℝ) ≤
      Knum * ∏ j : Fin 2, ((2 : ℝ) ^ (k j)) ^ (winE n j) := by
  have h1 : ∀ j : Fin 2, (1 : ℝ) ≤ (2 : ℝ) ^ (k j) := fun j => one_le_pow₀ (by norm_num)
  have h2 : ∀ L ∈ T.filter (fun L => kwin 2 L = k),
      IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (k j) := by
    intro L hL
    rw [Finset.mem_filter] at hL
    exact ⟨(hT L hL.1).1, (hT L hL.1).2, fun j => by
      have h := hwin1 L (hT L hL.1).2 j
      rwa [hL.2] at h⟩
  have hnum' := hnum (fun j => (2 : ℝ) ^ (k j)) (T.filter (fun L => kwin 2 L = k)) h1 h2
  exact hnum'

/-- The dyadic window `kwin 2 L` of a rank-`2` lattice with `detL L ≤ Δ+1`,
`lam L 1 ≤ X`, `lam L 2 ≤ Y` satisfies the four window conditions with the modulus
`winM Kmink Δ`. -/
theorem kwin_mem_cond (n : ℕ) (hn : 2 ≤ n)
    (Kmink : ℝ) (hKmink : 1 ≤ Kmink)
    (hmink : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmink * detL L)
    (hwin2 : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = 2 →
      ∀ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ 2 * lam L (j.1 + 1))
    (hwin3 : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = 2 → Monotone (kwin 2 L))
    (hwin4 : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = 2 →
      ∀ M : ℝ, 1 ≤ M → (∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j)) ≤ M →
        (∑ j : Fin 2, kwin 2 L j) ≤ ⌈Real.logb 2 M⌉₊)
    (X Y Δ : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hΔ : 1 ≤ Δ)
    (L : Submodule ℤ (Fin (n + 1) → ℤ)) (hrk : rk L = 2) (hdet : detL L ≤ Δ + 1)
    (hlam1 : lam L 1 ≤ X) (hlam2 : lam L 2 ≤ Y) :
    kwin 2 L ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (winM Kmink Δ + 1)) ∧
      winCond X Y (winM Kmink Δ) (kwin 2 L) := by
  have hlam : ∏ j : Fin 2, lam L (j.1 + 1) ≤ Kmink * (Δ + 1) := by
    rw [Fin.prod_univ_eq_prod_range (fun j => lam L (j + 1)) 2, ← hrk]
    calc ∏ j ∈ Finset.range (rk L), lam L (j + 1) ≤ Kmink * detL L := hmink L
      _ ≤ Kmink * (Δ + 1) := mul_le_mul_of_nonneg_left hdet (by linarith)
  have hprod : ∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ (2 : ℝ) ^ 2 * Kmink * (Δ + 1) := by
    have hstep1 : ∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ ∏ j : Fin 2, (2 * lam L (j.1 + 1)) :=
      Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => hwin2 L hrk j)
    have hstep2 : ∏ j : Fin 2, (2 * lam L (j.1 + 1)) = (2 : ℝ) ^ 2 * ∏ j : Fin 2, lam L (j.1 + 1) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j)
        ≤ ∏ j : Fin 2, (2 * lam L (j.1 + 1)) := hstep1
      _ = (2 : ℝ) ^ 2 * ∏ j : Fin 2, lam L (j.1 + 1) := hstep2
      _ ≤ (2 : ℝ) ^ 2 * (Kmink * (Δ + 1)) := mul_le_mul_of_nonneg_left hlam (by positivity)
      _ = (2 : ℝ) ^ 2 * Kmink * (Δ + 1) := by ring
  have hM : 1 ≤ (2 : ℝ) ^ 2 * Kmink * (Δ + 1) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ 2 := by norm_num
    have ha : (1 : ℝ) ≤ (2 : ℝ) ^ 2 * Kmink := by nlinarith [h1, hKmink]
    have hb : (0 : ℝ) < (2 : ℝ) ^ 2 * Kmink := by nlinarith [h1, hKmink]
    have h2 : (1 : ℝ) ≤ Δ + 1 := by linarith
    nlinarith [ha, h2, hb]
  have hsum : (∑ j : Fin 2, kwin 2 L j) ≤ winM Kmink Δ := by
    rw [winM]
    exact hwin4 L hrk _ hM hprod
  have hmem : kwin 2 L ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (winM Kmink Δ + 1)) := by
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)) hsum
  refine ⟨hmem, ?_⟩
  rw [winCond]
  refine ⟨hwin3 L hrk, hsum, ?_, ?_⟩
  · have h := hwin2 L hrk 0
    simp only [Fin.val_zero, zero_add] at h
    linarith
  · have h := hwin2 L hrk 1
    simp only [Fin.val_one, Nat.reduceAdd] at h
    linarith

/-- **Window sum, rank 2.**  Summing the second-moment bound `hbp` over a family of
primitive rank-`2` lattices with `detL L ≤ Δ + 1`, `lam L 1 ≤ X`, `lam L 2 ≤ Y`, grouped
into dyadic windows `kwin 2 L` and counted by `hnum`, is bounded by the arithmetic input
`harith`. -/
theorem window_sum_r2 (n : ℕ) (hn : 2 ≤ n)
    (Knum : ℝ) (hKnum : 0 < Knum)
    (hnum : ∀ (s : Fin 2 → ℝ) (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))), (∀ j, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j) →
      ((F.card : ℝ) ≤ Knum * ∏ j : Fin 2, s j ^ (n + 1 + 2 + 1 - 2 * (j.1 + 1))))
    (Kmink : ℝ) (hKmink : 1 ≤ Kmink)
    (hmink : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmink * detL L)
    (hwin : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = 2 →
      (∀ j : Fin 2, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin 2 L j)) ∧
      (∀ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ 2 * lam L (j.1 + 1)) ∧
      Monotone (kwin 2 L) ∧
      (∀ M : ℝ, 1 ≤ M → (∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j)) ≤ M →
        (∑ j : Fin 2, kwin 2 L j) ≤ ⌈Real.logb 2 M⌉₊))
    (Ksmall : ℝ) (hKsmall : 0 < Ksmall)
    (hsmall2 : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (X : ℝ), rk L = 2 → 1 ≤ X →
      (ballCount L X : ℝ) ≤ Ksmall * (X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1))
    (hsmallY : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (Y : ℝ), 1 ≤ Y → 2 ≤ rk L → lam L 2 ≤ Y →
      (ballCount L Y : ℝ) ≤ Ksmall * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)))
    (hbp : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (k : Fin 2 → ℕ) (X Y : ℝ), rk L = 2 →
      (∀ j : Fin 2, (2 : ℝ) ^ (k j) ≤ 2 * lam L (j.1 + 1)) → 1 ≤ X → 1 ≤ Y → X ≤ Y →
      lam L 1 ≤ X → lam L 2 ≤ Y →
      (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤
        Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
          + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
          + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1))))
    (Karith : ℝ) (hKarith : 0 < Karith)
    (harith : ∀ (X Y Δ : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊
            ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
          X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
            + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
            + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
        else 0))
      ≤ Karith * X ^ 2 * Y ^ 2 * Δ ^ (n - 1))
    (X Y Δ : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hΔ : 1 ≤ Δ) (hXY : X ≤ Y)
    (T : Finset (Submodule ℤ (Fin (n + 1) → ℤ)))
    (hT : ∀ L ∈ T, IsPrimLat L ∧ rk L = 2 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y) :
    (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ)) ≤
      (Knum * Ksmall ^ 2 * 16 * Karith) * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by
  classical
  set K : Finset (Fin 2 → ℕ) :=
    Fintype.piFinset (fun _ : Fin 2 => Finset.range (winM Kmink Δ + 1)) with hK
  have hwin1 : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = 2 →
      ∀ j : Fin 2, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin 2 L j) := fun L hrk => (hwin L hrk).1
  have hwin2 : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = 2 →
      ∀ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ 2 * lam L (j.1 + 1) := fun L hrk => (hwin L hrk).2.1
  have hwin3 : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = 2 → Monotone (kwin 2 L) :=
    fun L hrk => (hwin L hrk).2.2.1
  have hwin4 : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = 2 →
      ∀ M : ℝ, 1 ≤ M → (∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j)) ≤ M →
        (∑ j : Fin 2, kwin 2 L j) ≤ ⌈Real.logb 2 M⌉₊ := fun L hrk => (hwin L hrk).2.2.2
  -- step 1: the single-lattice bound, at the actual window of `L`
  have hper : ∀ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤ winBp Ksmall X Y (kwin 2 L) := by
    intro L hL
    obtain ⟨-, hrk, -, hl1, hl2⟩ := hT L hL
    have h := hbp L (kwin 2 L) X Y hrk (hwin2 L hrk) hX hY hXY hl1 hl2
    simpa only [winBp] using h
  -- step 2: the window of each `L ∈ T` lies in the index set and satisfies the conditions
  have hall : ∀ L ∈ T, (kwin 2 L ∈ K) ∧ winCond X Y (winM Kmink Δ) (kwin 2 L) := by
    intro L hL
    obtain ⟨-, hrk, hdet, hl1, hl2⟩ := hT L hL
    have hres := kwin_mem_cond n hn Kmink hKmink hmink hwin2 hwin3 hwin4 X Y Δ hX hY hΔ
      L hrk hdet hl1 hl2
    rw [hK]
    exact hres
  -- step 3: the counting bound on each fibre
  have hcnt : ∀ k ∈ K, (((T.filter (fun L => kwin 2 L = k)).card : ℕ) : ℝ)
      ≤ Knum * ∏ j : Fin 2, ((2 : ℝ) ^ (k j)) ^ (winE n j) := by
    intro k _
    exact win_fiber_card n hn Knum hKnum hnum hwin1 T
      (fun L hL => ⟨(hT L hL).1, (hT L hL).2.1⟩) k
  -- step 4: grouping the lattices of `T` by their window
  have hfib : (∑ L ∈ T, winBp Ksmall X Y (kwin 2 L))
      = ∑ k ∈ K, (((T.filter (fun L => kwin 2 L = k)).card : ℕ) : ℝ) * winBp Ksmall X Y k := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := K) (g := fun L => kwin 2 L)
        (fun L hL => (hall L hL).1) (fun L => winBp Ksmall X Y (kwin 2 L))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hinner : (∑ L ∈ T.filter (fun L => kwin 2 L = k), winBp Ksmall X Y (kwin 2 L))
        = ∑ L ∈ T.filter (fun L => kwin 2 L = k), winBp Ksmall X Y k :=
      Finset.sum_congr rfl (fun L hL => by
        rw [Finset.mem_filter] at hL
        rw [hL.2])
    rw [hinner, Finset.sum_const, nsmul_eq_mul]
  -- step 5: the pointwise bound over the index set
  have hpt : ∀ k ∈ K, (((T.filter (fun L => kwin 2 L = k)).card : ℕ) : ℝ) * winBp Ksmall X Y k
      ≤ Knum * Ksmall ^ 2 * 16 * winSum n X Y (winM Kmink Δ) k := by
    intro k hk
    by_cases hc : winCond X Y (winM Kmink Δ) k
    · have hbpnn : 0 ≤ winBp Ksmall X Y k := by rw [winBp]; positivity
      have hstep1 : (((T.filter (fun L => kwin 2 L = k)).card : ℕ) : ℝ) * winBp Ksmall X Y k
          ≤ (Knum * ∏ j : Fin 2, ((2 : ℝ) ^ (k j)) ^ (winE n j)) * winBp Ksmall X Y k :=
        mul_le_mul_of_nonneg_right (hcnt k hk) hbpnn
      have hstep2 : (∏ j : Fin 2, ((2 : ℝ) ^ (k j)) ^ (winE n j)) * winBp Ksmall X Y k
          ≤ Ksmall ^ 2 * 16 * winS n X Y k :=
        win_bp_mul n hn Ksmall X Y (le_trans zero_le_one hX) k
      have hstep3 : (Knum * ∏ j : Fin 2, ((2 : ℝ) ^ (k j)) ^ (winE n j)) * winBp Ksmall X Y k
          ≤ Knum * (Ksmall ^ 2 * 16 * winS n X Y k) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hstep2 (le_of_lt hKnum)
      have hstep4 : Knum * (Ksmall ^ 2 * 16 * winS n X Y k)
          = Knum * Ksmall ^ 2 * 16 * winSum n X Y (winM Kmink Δ) k := by
        rw [winSum_eq_winS hc]; ring
      exact le_trans (le_trans hstep1 hstep3) (le_of_eq hstep4)
    · have hzero : ((T.filter (fun L => kwin 2 L = k)).card : ℕ) = 0 := by
        by_contra hne
        obtain ⟨L, hL⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
        rw [Finset.mem_filter] at hL
        exact hc (by rw [← hL.2]; exact (hall L hL.1).2)
      rw [hzero, Nat.cast_zero, zero_mul, winSum_eq_zero hc, mul_zero]
  -- step 6: assemble
  calc (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ ∑ L ∈ T, winBp Ksmall X Y (kwin 2 L) := Finset.sum_le_sum hper
    _ = ∑ k ∈ K, (((T.filter (fun L => kwin 2 L = k)).card : ℕ) : ℝ) * winBp Ksmall X Y k := hfib
    _ ≤ ∑ k ∈ K, Knum * Ksmall ^ 2 * 16 * winSum n X Y (winM Kmink Δ) k := Finset.sum_le_sum hpt
    _ = Knum * Ksmall ^ 2 * 16 * ∑ k ∈ K, winSum n X Y (winM Kmink Δ) k := by
        rw [Finset.mul_sum]
    _ ≤ Knum * Ksmall ^ 2 * 16 * (Karith * X ^ 2 * Y ^ 2 * Δ ^ (n - 1)) := by
        rw [hK]
        exact mul_le_mul_of_nonneg_left (harith X Y Δ hX hY hΔ) (by positivity)
    _ = (Knum * Ksmall ^ 2 * 16 * Karith) * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by ring

end Work.HP
