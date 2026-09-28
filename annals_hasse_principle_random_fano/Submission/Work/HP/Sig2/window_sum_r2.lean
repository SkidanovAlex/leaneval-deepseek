import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.window_sum_ge3
import Submission.Work.HP.ball_prod_window_r2
import Submission.Work.HP.dyadic_sum_r2
import Submission.Work.HP.WinR2Defs
import Submission.Work.HP.Sig2.win_membership_r2
import Submission.Work.HP.Sig2.fiber_bound_r2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section
open Finset
open scoped BigOperators

namespace Work.HP.Sig2


/-! ## Inlined algebra for the rank-`2` window comparison -/

/-- Clearing the window denominators, first term. -/
private lemma window_pow_exp1 (n : ℕ) (hn : 2 ≤ n) (a b : ℕ) :
    (2 : ℝ) ^ (a * (n + 2) + b * n) / ((2 : ℝ) ^ (2 * a) * (2 : ℝ) ^ (2 * b))
      = (2 : ℝ) ^ (n * a + (n - 2) * b) := by
  have hexp : a * (n + 2) + b * n = 2 * a + 2 * b + (n * a + (n - 2) * b) := by
    have h2 : 2 ≤ n := hn
    have hcast : ((a * (n + 2) + b * n : ℕ) : ℤ)
        = ((2 * a + 2 * b + (n * a + (n - 2) * b) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h2]
      ring
    exact_mod_cast hcast
  rw [div_eq_iff (by positivity), hexp, pow_add, pow_add]
  ring

/-- Clearing the window denominators, second term. -/
private lemma window_pow_exp2 (n : ℕ) (hn : 2 ≤ n) (a b : ℕ) :
    (2 : ℝ) ^ (a * (n + 2) + b * n) / ((2 : ℝ) ^ (2 * a) * (2 : ℝ) ^ b)
      = (2 : ℝ) ^ (n * a + (n - 1) * b) := by
  have hexp : a * (n + 2) + b * n = 2 * a + b + (n * a + (n - 1) * b) := by
    have h2 : 1 ≤ n := by omega
    have hcast : ((a * (n + 2) + b * n : ℕ) : ℤ)
        = ((2 * a + b + (n * a + (n - 1) * b) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h2]
      ring
    exact_mod_cast hcast
  rw [div_eq_iff (by positivity), hexp, pow_add, pow_add]
  ring

/-- Clearing the window denominators, third term. -/
private lemma window_pow_exp3 (n : ℕ) (hn : 2 ≤ n) (a b : ℕ) :
    (2 : ℝ) ^ (a * (n + 2) + b * n) / ((2 : ℝ) ^ a * (2 : ℝ) ^ b)
      = (2 : ℝ) ^ ((n + 1) * a + (n - 1) * b) := by
  have hexp : a * (n + 2) + b * n = a + b + ((n + 1) * a + (n - 1) * b) := by
    have h2 : 1 ≤ n := by omega
    have hcast : ((a * (n + 2) + b * n : ℕ) : ℤ)
        = ((a + b + ((n + 1) * a + (n - 1) * b) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h2]
      ring
    exact_mod_cast hcast
  rw [div_eq_iff (by positivity), hexp, pow_add, pow_add]
  ring

/-- The rank-`2` window algebra: multiplying the two ball-count bounds at window `k` by the
lattice count `2 ^ (∑ j, k j * winE n j)` is dominated by `16 Ksmall^2` times the arithmetic
summand `winS n X Y k`. -/
private theorem window_algebra_r2_priv (n : ℕ) (hn : 2 ≤ n) (Ksmall X Y : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (k : Fin 2 → ℕ) :
    (2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j) * winBp Ksmall X Y k
      ≤ 16 * Ksmall ^ 2 * winS n X Y k := by
  have hE : (∑ j : Fin 2, k j * winE n j) = k 0 * (n + 2) + k 1 * n := by
    rw [Fin.sum_univ_two, winE_zero, winE_one]
  have hn1 : (n + 1 - 1) = n := by omega
  have hn2 : (n + 1 - 3) = n - 2 := by omega
  have hn3 : (n + 1 - 2) = n - 1 := by omega
  rw [hE]
  unfold winBp winS
  rw [hn1, hn2, hn3]
  have e1 : (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
        * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1)))
      = 16 * (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ (n * k 0 + (n - 2) * k 1)) := by
    rw [show (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
          * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1)))
        = 16 * (X ^ 2 * Y ^ 2) * ((2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
          / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))) from by field_simp <;> ring]
    rw [window_pow_exp1 n hn (k 0) (k 1)]
    ring
  have e2 : (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
        * (8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1)))
      ≤ 16 * (X * Y ^ 2 * (2 : ℝ) ^ (n * k 0 + (n - 1) * k 1)) := by
    rw [show (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
          * (8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1)))
        = 8 * (X * Y ^ 2) * ((2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
          / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))) from by field_simp <;> ring]
    rw [window_pow_exp2 n hn (k 0) (k 1)]
    have hx : 0 ≤ X * Y ^ 2 * (2 : ℝ) ^ (n * k 0 + (n - 1) * k 1) := by positivity
    nlinarith [hx]
  have e3 : (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
        * (4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))
      ≤ 16 * (Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n - 1) * k 1)) := by
    rw [show (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
          * (4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))
        = 4 * (Y ^ 2) * ((2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
          / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1))) from by field_simp <;> ring]
    rw [window_pow_exp3 n hn (k 0) (k 1)]
    have hy : 0 ≤ Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n - 1) * k 1) := by positivity
    nlinarith [hy]
  have hsplit : (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
        * (Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
          + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
          + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1))))
      = Ksmall ^ 2 *
        ((2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
            * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1)))
          + (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
            * (8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1)))
          + (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
            * (4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))) := by
    ring
  rw [hsplit, e1]
  have hK2 : 0 ≤ Ksmall ^ 2 := sq_nonneg Ksmall
  have h2e2 := mul_le_mul_of_nonneg_left e2 hK2
  have h2e3 := mul_le_mul_of_nonneg_left e3 hK2
  have h1 : 0 ≤ X ^ 2 * Y ^ 2 * (2 : ℝ) ^ (n * k 0 + (n - 2) * k 1) := by positivity
  have h2' : 0 ≤ X * Y ^ 2 * (2 : ℝ) ^ (n * k 0 + (n - 1) * k 1) := by positivity
  have h3 : 0 ≤ Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n - 1) * k 1) := by positivity
  nlinarith [hK2, h2e2, h2e3, h1, h2', h3]

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
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  set N : ℕ := ⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊ with hN
  have hwin1 : ∀ L ∈ T, ∀ j : Fin 2, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin 2 L j) :=
    fun L hL => (hwin L (hT L hL).2.1).1
  have hwin2 : ∀ L ∈ T, ∀ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ 2 * lam L (j.1 + 1) :=
    fun L hL => (hwin L (hT L hL).2.1).2.1
  have hwinL : ∀ L ∈ T, Monotone (kwin 2 L) ∧ (∑ j : Fin 2, kwin 2 L j) ≤ N ∧
      (∀ j : Fin 2, kwin 2 L j ≤ N) := by
    intro L hL
    obtain ⟨h1, h2, h3, h4, h5⟩ := hT L hL
    rw [hN]
    exact win_membership_r2 n Kmink Δ hKmink hΔ L h2 h3 (hmink L) (hwin L h2)
  have hcond4 : ∀ k ∈ T.image (fun L => kwin 2 L), Monotone k ∧ (∑ j : Fin 2, k j) ≤ N ∧
      (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y := by
    intro k hk
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨h1, h2, h3, h4, h5⟩ := hT L hL
    refine ⟨(hwinL L hL).1, (hwinL L hL).2.1, ?_, ?_⟩
    · have h := hwin2 L hL (0 : Fin 2)
      have h' : ((0 : Fin 2).1) + 1 = 1 := rfl
      rw [h'] at h
      linarith
    · have h := hwin2 L hL (1 : Fin 2)
      have h' : ((1 : Fin 2).1) + 1 = 2 := rfl
      rw [h'] at h
      linarith
  have himg_sub : T.image (fun L => kwin 2 L) ⊆
      (Fintype.piFinset (fun _ : Fin 2 => Finset.range (N + 1)) : Finset (Fin 2 → ℕ)) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro j
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((hwinL L hL).2.2 j)
  have hfib : (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      = ∑ k ∈ T.image (fun L => kwin 2 L),
          ∑ L ∈ T.filter (fun L => kwin 2 L = k), (ballCount L X : ℝ) * (ballCount L Y : ℝ) :=
    (Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image (fun L => kwin 2 L))
      (g := fun L => kwin 2 L) (fun i hi => Finset.mem_image_of_mem _ hi)
      (fun L => (ballCount L X : ℝ) * (ballCount L Y : ℝ))).symm
  have hinner : ∀ k ∈ T.image (fun L => kwin 2 L),
      (∑ L ∈ T.filter (fun L => kwin 2 L = k), (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j) * winBp Ksmall X Y k := by
    intro k hk
    have hTf : ∀ L ∈ T.filter (fun L => kwin 2 L = k),
        IsPrimLat L ∧ rk L = 2 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y :=
      fun L hL => hT L (Finset.mem_of_mem_filter L hL)
    have hw1 : ∀ L ∈ T.filter (fun L => kwin 2 L = k), ∀ j : Fin 2,
        lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin 2 L j) :=
      fun L hL => hwin1 L (Finset.mem_of_mem_filter L hL)
    have hw2 : ∀ L ∈ T.filter (fun L => kwin 2 L = k), ∀ j : Fin 2,
        (2 : ℝ) ^ (kwin 2 L j) ≤ 2 * lam L (j.1 + 1) :=
      fun L hL => hwin2 L (Finset.mem_of_mem_filter L hL)
    have hkk : ∀ L ∈ T.filter (fun L => kwin 2 L = k), kwin 2 L = k :=
      fun L hL => (Finset.mem_filter.mp hL).2
    exact fiber_bound_r2 n hn Knum hKnum hnum Ksmall hKsmall hbp
      X Y Δ hX hY hXY (T.filter (fun L => kwin 2 L = k)) k hTf hw1 hw2 hkk
  have hterm : ∀ k : Fin 2 → ℕ,
      Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j) * winBp Ksmall X Y k
      ≤ Knum * Ksmall ^ 2 * 16 * winS n X Y k := by
    intro k
    have h := window_algebra_r2_priv n hn Ksmall X Y hX0 hY0 k
    have hK0 : 0 ≤ Knum := le_of_lt hKnum
    calc Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j) * winBp Ksmall X Y k
        = Knum * ((2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j) * winBp Ksmall X Y k) := by ring
      _ ≤ Knum * (16 * Ksmall ^ 2 * winS n X Y k) := mul_le_mul_of_nonneg_left h hK0
      _ = Knum * Ksmall ^ 2 * 16 * winS n X Y k := by ring
  have hstep2 : (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ ∑ k ∈ T.image (fun L => kwin 2 L),
          Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j) * winBp Ksmall X Y k := by
    rw [hfib]
    exact Finset.sum_le_sum hinner
  have hstep3 : (∑ k ∈ T.image (fun L => kwin 2 L),
          Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j) * winBp Ksmall X Y k)
      ≤ Knum * Ksmall ^ 2 * 16 *
        (∑ k ∈ (Fintype.piFinset (fun _ : Fin 2 => Finset.range (N + 1)) : Finset (Fin 2 → ℕ)),
          (if Monotone k ∧ (∑ j : Fin 2, k j) ≤ N ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X
              ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
            winS n X Y k
          else 0)) := by
    have hA : (∑ k ∈ T.image (fun L => kwin 2 L),
          Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j) * winBp Ksmall X Y k)
        ≤ ∑ k ∈ T.image (fun L => kwin 2 L), Knum * Ksmall ^ 2 * 16 * winS n X Y k :=
      Finset.sum_le_sum (fun k _ => hterm k)
    have hA2 : (∑ k ∈ T.image (fun L => kwin 2 L), Knum * Ksmall ^ 2 * 16 * winS n X Y k)
        = Knum * Ksmall ^ 2 * 16 * (∑ k ∈ T.image (fun L => kwin 2 L), winS n X Y k) := by
      rw [Finset.mul_sum]
    have hA3 : (∑ k ∈ T.image (fun L => kwin 2 L), winS n X Y k)
        ≤ ∑ k ∈ (Fintype.piFinset (fun _ : Fin 2 => Finset.range (N + 1)) : Finset (Fin 2 → ℕ)),
          (if Monotone k ∧ (∑ j : Fin 2, k j) ≤ N ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X
              ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
            winS n X Y k
          else 0) := by
      rw [show (∑ k ∈ T.image (fun L => kwin 2 L), winS n X Y k)
          = ∑ k ∈ T.image (fun L => kwin 2 L),
            (if Monotone k ∧ (∑ j : Fin 2, k j) ≤ N ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X
                ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
              winS n X Y k
            else 0) from
        Finset.sum_congr rfl (fun k hk => (if_pos (hcond4 k hk)).symm)]
      exact Finset.sum_le_sum_of_subset_of_nonneg himg_sub
        (fun k _ _ => by
          by_cases hc : Monotone k ∧ (∑ j : Fin 2, k j) ≤ N ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X
              ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y
          · rw [if_pos hc, winS]; positivity
          · rw [if_neg hc])
    calc (∑ k ∈ T.image (fun L => kwin 2 L),
          Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j) * winBp Ksmall X Y k)
        ≤ _ := hA
      _ = _ := hA2
      _ ≤ Knum * Ksmall ^ 2 * 16 * _ := mul_le_mul_of_nonneg_left hA3 (by positivity)
  have hstep4 : (∑ k ∈ (Fintype.piFinset (fun _ : Fin 2 => Finset.range (N + 1)) :
          Finset (Fin 2 → ℕ)),
          (if Monotone k ∧ (∑ j : Fin 2, k j) ≤ N ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X
              ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
            winS n X Y k
          else 0))
      ≤ Karith * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by
    have h := harith X Y Δ hX hY hΔ
    simpa only [hN, winS] using h
  calc (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ _ := hstep2
    _ ≤ _ := hstep3
    _ ≤ Knum * Ksmall ^ 2 * 16 * (Karith * X ^ 2 * Y ^ 2 * Δ ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left hstep4 (by positivity)
    _ = (Knum * Ksmall ^ 2 * 16 * Karith) * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by ring

end Work.HP.Sig2
