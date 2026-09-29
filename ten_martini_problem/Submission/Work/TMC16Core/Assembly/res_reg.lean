import Mathlib
import Submission.Work.TMC16Core.Assembly.res_zero
import Submission.Work.TMC16Core.Assembly.res_regwin_s0qn
import Submission.Work.TMC16Core.Assembly.res_decay_pos
import Submission.Work.TMC16Core.Assembly.res_num_par
import Submission.Work.TMC16Core.Assembly.res_uniform_fix
import Submission.Work.TMC16Core.Assembly.uni_res
import Submission.Work.TMC16Core.Assembly.RegWin
import Submission.Work.TMC16Core.Core.res_card
import Submission.Work.TMC16Core.Core.setup
import Submission.Work.TMC16Core.Assembly.endgame_g
import Submission.Work.TMC16Core.Basic.genEigen_reflectPhase

open Work.TMC16Core
open Work.TMC16Core.Core

namespace Work.TMC16Core.Assembly

set_option maxHeartbeats 4000000

noncomputable section

/-! ## Temporary stubs: to be replaced by imports of the colleagues' modules -/


/-! ## Helpers -/

theorem card_I1r_I2r (qn ℓ : ℕ) (hℓ : 1 ≤ ℓ) : (I1r qn ∪ I2r qn ℓ).card = 2 * qn := by
  have hcard : (J1resG (5 * qn / 8) ∪ J2resG qn (5 * qn / 8) ℓ).card = 2 * qn := by
    have h := Core.res_card (qn := qn) (h := 5 * qn / 8) (ℓ := ℓ) hℓ (by omega) (le_refl _)
    simpa [Core.resW] using h.2.2.1
  have hinj : Function.Injective (fun j : ℤ => j - ((qn : ℤ) - 1)) := by
    intro a b hab
    have h : a + (-((qn : ℤ) - 1)) = b + (-((qn : ℤ) - 1)) := by
      simpa [sub_eq_add_neg] using hab
    exact add_right_cancel h
  rw [← image_shift_eq qn ℓ, Finset.card_image_of_injective _ hinj]
  exact hcard

theorem geo_I2r {qn ℓ H : ℕ} {y : ℤ} {b : ℝ} (hH : H = 5 * qn / 8) (hb0 : 0 ≤ b)
    (hb : b ≤ (H : ℝ) - 1)
    (hy : (|y - (ℓ : ℤ) * (qn : ℤ)| : ℝ) ≤ b) :
    ∀ x ∈ I2r qn ℓ, x ≤ y ∧ y ≤ x + ((2 * qn - 1 : ℕ) : ℤ) - 1 ∧
      ((H : ℝ) - 1 - b) ≤ ((y - x : ℤ) : ℝ) ∧
      ((H : ℝ) - 1 - b) ≤ ((x + ((2 * qn - 1 : ℕ) : ℤ) - 1 - y : ℤ) : ℝ) := by
  have hmem : ∀ x : ℤ, x ∈ I2r qn ℓ ↔
      ((ℓ : ℤ) - 1) * (qn : ℤ) + (H : ℤ) - (qn : ℤ) + 1 ≤ x ∧
        x ≤ ((ℓ : ℤ) + 1) * (qn : ℤ) - (H : ℤ) - (qn : ℤ) := by
    intro x
    rw [I2r, Finset.mem_Icc, ← hH]
  have hHle : (H : ℝ) ≤ 5 * (qn : ℝ) / 8 := by
    rw [hH]
    have h2 : (5 * qn / 8 : ℕ) * 8 ≤ 5 * qn := Nat.div_mul_le_self _ _
    have h3 : ((5 * qn / 8 : ℕ) : ℝ) * 8 ≤ 5 * (qn : ℝ) := by exact_mod_cast h2
    linarith
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by linarith [hb0, hb]
  have hqn2 : 2 ≤ qn := by
    have h : (1 : ℝ) < (qn : ℝ) := by linarith [hHle, hH1]
    have h' : (1 : ℕ) < qn := by exact_mod_cast h
    omega
  have hKcast : (((2 * qn - 1 : ℕ) : ℝ)) = 2 * (qn : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * qn)]; push_cast; ring
  have hyabs : |(y : ℝ) - (ℓ : ℝ) * (qn : ℝ)| ≤ b := by
    simpa [Int.cast_mul] using hy
  have hyL : -b ≤ (y : ℝ) - (ℓ : ℝ) * (qn : ℝ) := (abs_le.mp hyabs).1
  have hyU : (y : ℝ) - (ℓ : ℝ) * (qn : ℝ) ≤ b := (abs_le.mp hyabs).2
  intro x hx
  obtain ⟨hx1, hx2⟩ := (hmem x).mp hx
  have hx1R : ((ℓ : ℝ) - 1) * (qn : ℝ) + (H : ℝ) - (qn : ℝ) + 1 ≤ (x : ℝ) := by
    have h : ((((ℓ : ℤ) - 1) * (qn : ℤ) + (H : ℤ) - (qn : ℤ) + 1 : ℤ) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast hx1
    push_cast at h
    linarith
  have hx2R : (x : ℝ) ≤ ((ℓ : ℝ) + 1) * (qn : ℝ) - (H : ℝ) - (qn : ℝ) := by
    have h : (x : ℝ) ≤ ((((ℓ : ℤ) + 1) * (qn : ℤ) - (H : ℤ) - (qn : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hx2
    push_cast at h
    linarith
  have hxU : (x : ℝ) - (ℓ : ℝ) * (qn : ℝ) ≤ -(H : ℝ) := by linarith
  have hxL : (H : ℝ) - 2 * (qn : ℝ) + 1 ≤ (x : ℝ) - (ℓ : ℝ) * (qn : ℝ) := by linarith
  have hcasty : ((y - x : ℤ) : ℝ) = (y : ℝ) - (x : ℝ) := by push_cast; ring
  have hcastx : ((x + ((2 * qn - 1 : ℕ) : ℤ) - 1 - y : ℤ) : ℝ)
      = (x : ℝ) + ((2 * qn - 1 : ℕ) : ℝ) - 1 - (y : ℝ) := by push_cast; ring
  have e1 : (y : ℝ) - (x : ℝ) = ((y : ℝ) - (ℓ : ℝ) * (qn : ℝ))
      - ((x : ℝ) - (ℓ : ℝ) * (qn : ℝ)) := by ring
  have e2 : (x : ℝ) - (y : ℝ) = ((x : ℝ) - (ℓ : ℝ) * (qn : ℝ))
      - ((y : ℝ) - (ℓ : ℝ) * (qn : ℝ)) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h2 : (0 : ℝ) < (y : ℝ) - (x : ℝ) := by linarith [hyL, hxU, e1, hb]
    have h3 : (0 : ℤ) < y - x := by exact_mod_cast h2
    omega
  · have h2 : (y : ℝ) - (x : ℝ) ≤ ((2 * qn - 1 : ℕ) : ℝ) - 1 := by
      rw [hKcast]
      linarith [hyU, hxL, e1, hb]
    have h3 : y - x ≤ ((2 * qn - 1 : ℕ) : ℤ) - 1 := by exact_mod_cast h2
    omega
  · rw [hcasty]
    linarith [hyL, hxU, e1]
  · rw [hcastx, hKcast]
    linarith [hyU, hxL, e2]

theorem genEigen_const_mul {α lam θ E : ℝ} {u : ℤ → ℂ} (c : ℂ) (hc : c ≠ 0)
    (hu : IsGenEigen α lam θ E u) : IsGenEigen α lam θ E (fun n => c * u n) := by
  obtain ⟨hne, hrec, C, hC⟩ := hu
  have hCnn : 0 ≤ C := by
    have h := hC 0
    simp only [Int.cast_zero, abs_zero, add_zero, mul_one] at h
    linarith [norm_nonneg (u 0)]
  refine ⟨?_, ?_, ‖c‖ * C, ?_⟩
  · intro hf
    apply hne
    ext n
    have hn := congrFun hf n
    simp only [Pi.zero_apply] at hn ⊢
    exact (mul_eq_zero.mp hn).resolve_left hc
  · intro n
    have h := hrec n
    simp only [amoAct] at h
    simp only [amoAct]
    linear_combination c * h
  · intro n
    calc ‖c * u n‖ = ‖c‖ * ‖u n‖ := norm_mul _ _
      _ ≤ ‖c‖ * (C * (1 + |(n : ℝ)|)) := mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
      _ = (‖c‖ * C) * (1 + |(n : ℝ)|) := by ring


theorem res_reg (h4 : Work.TMC16Core.P_LEBasics) (h7 : Work.TMC16Core.P_BJ_dioph)
    {α b₀ lam : ℝ} (hα : Irrational α) (hb₀ : 0 < b₀)
    (hDioph : Work.TMC16Core.DiophBelow α b₀)
    (hlam : Real.exp (16 * b₀ / 9) < lam)
    {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i) (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    {E : ℝ} (hE : E ∈ Work.TMC16Core.amoSpec α lam) {θ : ℝ}
    (hθ : θ ∉ Work.TMC16Core.Theta α) {u : ℤ → ℂ}
    (hu : Work.TMC16Core.IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ℓ : ℕ, 1 ≤ ℓ →
      (ℓ : ℝ) ≤ 2 * Real.rpow (q (n + 1) : ℝ) (8 / 9) / (q n : ℝ) →
      30 * q n ≤ q (n + 1) →
      (∀ y : ℤ, (|y - (ℓ : ℤ) * (q n : ℤ)| : ℝ) ≤ Work.TMC16Core.Assembly.bG q n →
        Work.TMC16Core.Assembly.RegWin α lam θ (E : ℂ) (Real.log lam / 100)
          (((5 * q n / 8 : ℕ) : ℝ) - 1 - Work.TMC16Core.Assembly.bG q n)
          (2 * q n - 1) y) := by
  -- ## 0. elementary facts
  have hlam1 : 1 < lam := by
    have h0 : Real.exp 0 < Real.exp (16 * b₀ / 9) := Real.exp_lt_exp.mpr (by positivity)
    rw [Real.exp_zero] at h0
    linarith
  have hLpos : 0 < Real.log lam := Real.log_pos hlam1
  have hLb : 16 * b₀ / 9 < Real.log lam := by
    have h := Real.log_lt_log (Real.exp_pos (16 * b₀ / 9)) hlam
    rwa [Real.log_exp] at h
  have hqge : ∀ m : ℕ, m + 1 ≤ q m := by
    intro m
    induction m with
    | zero => have := hqpos 0; omega
    | succ k ih =>
        have h1 : q k < q (k + 1) := hmono (by omega)
        have h2 : k + 1 ≤ q k := ih
        have h3 : k + 1 + 1 ≤ q (k + 1) := by omega
        simpa using h3
  -- ## 1. the normalised eigenfunction and its reflection
  obtain ⟨hu_ne, hrec, C₀, hC₀⟩ := hu
  have huEig : IsGenEigen α lam θ E u := ⟨hu_ne, hrec, C₀, hC₀⟩
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0
    simp only [Int.cast_zero, abs_zero, add_zero, mul_one] at h
    linarith [norm_nonneg (u 0)]
  set c : ℂ := (u 0)⁻¹ with hcdef
  have hcne : c ≠ 0 := by
    rw [hcdef]
    exact inv_ne_zero (fun h => hu0 h)
  set v : ℤ → ℂ := fun n => c * u n with hvdef
  have hv0 : v 0 = 1 := by
    rw [hvdef, hcdef]
    field_simp
  have hvgen : IsGenEigen α lam θ E v := by
    rw [hvdef]
    exact genEigen_const_mul c hcne huEig
  have hvsol : IsFormalSol α lam θ (E : ℂ) v := hvgen.2.1
  have hCvnn : 0 ≤ ‖c‖ * C₀ := mul_nonneg (norm_nonneg _) hC₀nn
  have hpolyv : ∀ k : ℤ, ‖v k‖ ≤ (‖c‖ * C₀) * (1 + |(k : ℝ)|) := by
    intro k
    rw [hvdef]
    calc ‖c * u k‖ = ‖c‖ * ‖u k‖ := norm_mul _ _
      _ ≤ ‖c‖ * (C₀ * (1 + |(k : ℝ)|)) := mul_le_mul_of_nonneg_left (hC₀ k) (norm_nonneg _)
      _ = (‖c‖ * C₀) * (1 + |(k : ℝ)|) := by ring
  set v' : ℤ → ℂ := fun n => v (-n) with hv'def
  have hv'gen : IsGenEigen α lam (-θ) E v' := by
    rw [hv'def]
    exact Basic.genEigen_reflectPhase hvgen
  have hv'0 : v' 0 = 1 := by
    rw [hv'def]
    simpa using hv0
  have hv'ne : v' 0 ≠ 0 := by rw [hv'0]; norm_num
  have hv'sol : IsFormalSol α lam (-θ) (E : ℂ) v' := hv'gen.2.1
  have hpolyv' : ∀ k : ℤ, ‖v' k‖ ≤ (‖c‖ * C₀) * (1 + |(k : ℝ)|) := by
    intro k
    rw [hv'def]
    have h := hpolyv (-k)
    simpa using h
  -- ## 2. the numerical constants
  set εf : ℝ := min (Real.log lam / 1000) ((9 * Real.log lam / 64 - b₀ / 4) / 8) with hεfdef
  have hεfpos : 0 < εf := by
    rw [hεfdef]
    refine lt_min (by linarith) ?_
    have : b₀ / 4 < 9 * Real.log lam / 64 := by nlinarith [hLb]
    linarith
  have hεfA' : Real.log lam - (9 * Real.log lam / 32 - 2 * εf) = 23 * Real.log lam / 32 + 2 * εf := by
    ring
  -- ## 3. the thresholds
  obtain ⟨Nnum, hNum⟩ := res_num_par (L := Real.log lam) (b₀ := b₀) hb₀ hLb
  obtain ⟨Nwin, hWin⟩ := res_regwin_s0qn (q := q) (Δ := Δ) (θ := θ)
    h4 h7 hα hb₀ hDioph hlam hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hE hθ huEig hu0
  obtain ⟨Nwin', hWin'⟩ := res_regwin_s0qn (q := q) (Δ := Δ) (θ := -θ)
    h4 h7 hα hb₀ hDioph hlam hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hE (theta_neg hθ)
    hv'gen hv'ne
  obtain ⟨Nuni, hUni⟩ := res_uniform_fix (α := α) (b₀ := b₀) (L := Real.log lam)
    (q := q) (Δ := Δ) (θ := θ) hα hb₀ hDioph rfl hlam1 hLb hqpos hmono hΔpos hΔeq hΔup hΔlo
    hbest hθ
  obtain ⟨Q₀, hRes0⟩ := res_zero (L := Real.log lam) (εf := εf) (C := ‖c‖ * C₀)
    hLpos hεfpos hCvnn
  obtain ⟨Npd, hNpd⟩ := Filter.eventually_atTop.mp
    (Core.pd_eventually_bound_dioph h4 h7 hα hb₀ hDioph hlam hE hεfpos)
  obtain ⟨NdecA, hDecA⟩ := res_decay_pos (α := α) (lam := lam)
    (γ := 7 * Real.log lam / 10) (L := Real.log lam) (q := q)
    (by linarith) hLpos (by linarith) (by linarith) hqpos hmono (θ := θ) (E := (E : ℂ))
    (u := v) (C := ‖c‖ * C₀) hvsol hv0 hCvnn hpolyv
  obtain ⟨NdecB, hDecB⟩ := res_decay_pos (α := α) (lam := lam)
    (γ := 7 * Real.log lam / 10) (L := Real.log lam) (q := q)
    (by linarith) hLpos (by linarith) (by linarith) hqpos hmono (θ := -θ) (E := (E : ℂ))
    (u := v') (C := ‖c‖ * C₀) hv'sol hv'0 hCvnn hpolyv'
  refine ⟨({Q₀ + 1, Nnum, Nwin, Nwin', Nuni, 20 * Npd + 1, NdecA, NdecB, 41} : Finset ℕ).max'
    ⟨Q₀ + 1, by simp⟩, ?_⟩
  intro n hn ℓ hℓ hℓle h30 y hy
  -- ## 4. unpack the thresholds
  have hmax : ∀ a ∈ ({Q₀ + 1, Nnum, Nwin, Nwin', Nuni, 20 * Npd + 1, NdecA, NdecB, 41} : Finset ℕ),
      a ≤ n := fun a ha => le_trans (Finset.le_max' _ a ha) hn
  have hNQ : Q₀ + 1 ≤ n := hmax _ (by simp)
  have hNnum : Nnum ≤ n := hmax _ (by simp)
  have hNwin : Nwin ≤ n := hmax _ (by simp)
  have hNwin' : Nwin' ≤ n := hmax _ (by simp)
  have hNuni : Nuni ≤ n := hmax _ (by simp)
  have hNpd' : 20 * Npd + 1 ≤ n := hmax _ (by simp)
  have hNdecA : NdecA ≤ n := hmax _ (by simp)
  have hNdecB : NdecB ≤ n := hmax _ (by simp)
  have h41 : 41 ≤ n := hmax _ (by simp)
  have hnq : n ≤ q n := Nat.le_of_succ_le (hqge n)
  have hQ : Q₀ ≤ q n := le_trans (Nat.le_of_succ_le hNQ) hnq
  have hnum : Nnum ≤ q n := le_trans hNnum hnq
  have hpd20 : 20 * Npd + 1 ≤ q n := le_trans hNpd' hnq
  have hqn1 : 1 ≤ q n := by have := hqpos n; omega
  have hqnpos : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
  -- ## 5. the numerical facts at level `n`
  obtain ⟨hεApos, hεuA, hεfA, hgapδ, hbGnn, hbG20, hbG58, hg40, hkeyN, hgapN⟩ :=
    hNum q n hNnum hmono (hqpos n) εf hεfpos hεfdef.le
  have hK40 : 40 ≤ 2 * q n - 1 := by omega
  have hKcast : (((2 * q n - 1 : ℕ) : ℝ)) = 2 * (q n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * q n)]; push_cast; ring
  -- ## 6. the continuant bound
  have hbd : ∀ N : ℕ, (2 * q n - 1) / 40 ≤ N → N ≤ 2 * q n - 1 → ∀ ζ : ℝ,
      ‖pd α lam ζ (E : ℂ) (N + 1)‖ ≤ Real.exp ((N : ℝ) * (Real.log lam + εf)) := by
    intro N h1 h2 ζ
    have hN : Npd ≤ N := by
      have h3 : Npd ≤ (2 * q n - 1) / 40 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 40)]
        omega
      omega
    exact hNpd N hN ζ
  -- ## 7. the regularity windows at level `n`
  have hqne1 : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqn1
  have hrpownn : (0 : ℝ) ≤ Real.rpow (q (n + 1) : ℝ) (8 / 9) :=
    Real.rpow_nonneg (by positivity) _
  have hm0le : ((0 : ℤ) : ℝ) * (q n : ℝ)
      ≤ 100 * (Real.rpow (q (n + 1) : ℝ) (8 / 9) + (q n : ℝ)) := by
    rw [Int.cast_zero, zero_mul]; nlinarith [hrpownn, hqnpos]
  have hm1le : ((1 : ℤ) : ℝ) * (q n : ℝ)
      ≤ 100 * (Real.rpow (q (n + 1) : ℝ) (8 / 9) + (q n : ℝ)) := by
    rw [Int.cast_one, one_mul]; nlinarith [hrpownn, hqnpos]
  have hmq1 : (1 : ℤ) ≠ 0 → 10 * (|(1 : ℤ)| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ) := by
    intro _
    have h30' : (30 : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ) := by exact_mod_cast h30
    norm_num
    linarith
  have hregA : ∀ y : ℤ, ((((q n - 1 : ℕ) : ℝ))) / 20 + 3 ≤ (y : ℝ) →
      (y : ℝ) ≤ 95 * ((((q n - 1 : ℕ) : ℝ))) / 100 - 3 →
      RegWin α lam θ (E : ℂ) (7 * Real.log lam / 10) ((((q n - 1 : ℕ) : ℝ)) / 40) (q n - 1) y :=
    fun y h1 h2 => by
      have h := hWin n hNwin (0 : ℤ) (le_refl 0) (by omega)
        (by intro hc; exact absurd rfl hc) hm0le (y - (0 : ℤ) * (q n : ℤ)) (by simpa using h1)
        (by simpa using h2) h30
      simpa using h
  have hregA1 : ∀ y : ℤ, (q n : ℝ) + ((((q n - 1 : ℕ) : ℝ))) / 20 + 3 ≤ (y : ℝ) →
      (y : ℝ) ≤ (q n : ℝ) + 95 * ((((q n - 1 : ℕ) : ℝ))) / 100 - 3 →
      RegWin α lam θ (E : ℂ) (7 * Real.log lam / 10) ((((q n - 1 : ℕ) : ℝ)) / 40) (q n - 1) y :=
    fun y h1 h2 => by
      have hk1 : ((((q n - 1 : ℕ) : ℝ))) / 20 + 3 ≤ ((y - (q n : ℤ) : ℤ) : ℝ) := by
        push_cast; linarith
      have hk2 : ((y - (q n : ℤ) : ℤ) : ℝ) ≤ 95 * ((((q n - 1 : ℕ) : ℝ))) / 100 - 3 := by
        push_cast; linarith
      have h := hWin n hNwin (1 : ℤ) (by norm_num) (by norm_num) hmq1 hm1le
        (y - (q n : ℤ)) hk1 hk2 h30
      simpa using h
  have hregB : ∀ y : ℤ, ((((q n - 1 : ℕ) : ℝ))) / 20 + 3 ≤ (y : ℝ) →
      (y : ℝ) ≤ 95 * ((((q n - 1 : ℕ) : ℝ))) / 100 - 3 →
      RegWin α lam (-θ) (E : ℂ) (7 * Real.log lam / 10) ((((q n - 1 : ℕ) : ℝ)) / 40)
        (q n - 1) y :=
    fun y h1 h2 => by
      have h := hWin' n hNwin' (0 : ℤ) (le_refl 0) (by omega)
        (by intro hc; exact absurd rfl hc) hm0le (y - (0 : ℤ) * (q n : ℤ)) (by simpa using h1)
        (by simpa using h2) h30
      simpa using h
  have hregB1 : ∀ y : ℤ, (q n : ℝ) + ((((q n - 1 : ℕ) : ℝ))) / 20 + 3 ≤ (y : ℝ) →
      (y : ℝ) ≤ (q n : ℝ) + 95 * ((((q n - 1 : ℕ) : ℝ))) / 100 - 3 →
      RegWin α lam (-θ) (E : ℂ) (7 * Real.log lam / 10) ((((q n - 1 : ℕ) : ℝ)) / 40)
        (q n - 1) y :=
    fun y h1 h2 => by
      have hk1 : ((((q n - 1 : ℕ) : ℝ))) / 20 + 3 ≤ ((y - (q n : ℤ) : ℤ) : ℝ) := by
        push_cast; linarith
      have hk2 : ((y - (q n : ℤ) : ℤ) : ℝ) ≤ 95 * ((((q n - 1 : ℕ) : ℝ))) / 100 - 3 := by
        push_cast; linarith
      have h := hWin' n hNwin' (1 : ℤ) (by norm_num) (by norm_num) hmq1 hm1le
        (y - (q n : ℤ)) hk1 hk2 h30
      simpa using h
  -- ## 8. the decay of the normalised eigenfunction
  have hdecA := hDecA n hNdecA hregA hregA1
  have hdecB := hDecB n hNdecB hregB hregB1
  have hdec : ∀ k : ℤ, |k| ≤ 2 * (q n : ℤ) → ∀ d : ℕ, q n ≤ 5 * d →
      (∀ ℓ : ℤ, (d : ℤ) ≤ |k - ℓ * (q n : ℤ)|) →
      ‖v k‖ ≤ Real.exp (-(Real.log lam / 2) * (d : ℝ)) := by
    intro k hk d hd hsep
    have hdR : (q n : ℝ) ≤ 5 * (d : ℝ) := by exact_mod_cast hd
    have hrange : ∀ j : ℤ, 1 ≤ j → j ≤ 2 * (q n : ℤ) →
        (∀ ℓ : ℤ, (d : ℤ) ≤ |j - ℓ * (q n : ℤ)|) →
        (q n : ℝ) / 5 ≤ (j : ℝ) ∧ (j : ℝ) ≤ 9 * (q n : ℝ) / 5 := by
      intro j hj1 hj2 hsepj
      have hjq : (j : ℝ) ≤ 9 * (q n : ℝ) / 5 := by
        rcases le_total j (q n : ℤ) with hjq | hjq
        · have h : (j : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hjq
          linarith
        · have h := hsepj 2
          have h2 : |j - 2 * (q n : ℤ)| = 2 * (q n : ℤ) - j := by
            rw [abs_of_nonpos (by omega)]
            ring
          rw [h2] at h
          have h3 : (d : ℝ) ≤ 2 * (q n : ℝ) - (j : ℝ) := by
            have h4 : ((d : ℤ) : ℝ) ≤ ((2 * (q n : ℤ) - j : ℤ) : ℝ) := by exact_mod_cast h
            push_cast at h4
            simpa using h4
          linarith
      have hj5 : (q n : ℝ) / 5 ≤ (j : ℝ) := by
        have h := hsepj 0
        simp only [Int.cast_zero, zero_mul, sub_zero] at h
        have h2 : (d : ℤ) ≤ j := by
          rwa [abs_of_nonneg (by omega : (0 : ℤ) ≤ j)] at h
        have h3 : (d : ℝ) ≤ (j : ℝ) := by
          have h3' : ((d : ℤ) : ℝ) ≤ ((j : ℤ) : ℝ) := by exact_mod_cast h2
          simpa using h3'
        linarith
      exact ⟨hj5, hjq⟩
    rcases lt_or_ge 0 k with hkpos | hknonpos
    · have hkabs : |k| = k := abs_of_nonneg (le_of_lt hkpos)
      have hk2 : k ≤ 2 * (q n : ℤ) := by rw [hkabs] at hk; exact hk
      have h := hrange k (by omega) hk2 hsep
      exact hdecA k h.1 h.2 d hd hsep
    · have hklt : k < 0 := by
        rcases lt_or_eq_of_le hknonpos with h | h
        · exact h
        · exfalso
          have h1 := hsep 0
          simp only [Int.cast_zero, zero_mul, sub_zero] at h1
          rw [h] at h1
          simp only [abs_zero] at h1
          have hd0 : d = 0 := by omega
          have h3 : q n ≤ 5 * d := hd
          rw [hd0, mul_zero] at h3
          have := hqpos n
          omega
      have hk2 : -k ≤ 2 * (q n : ℤ) := by
        rw [abs_of_neg hklt] at hk
        omega
      have hsep' : ∀ ℓ : ℤ, (d : ℤ) ≤ |-k - ℓ * (q n : ℤ)| := by
        intro m
        have h := hsep (-m)
        have he : (-k : ℤ) - m * (q n : ℤ) = -(k - (-m) * (q n : ℤ)) := by ring
        rw [he, abs_neg]
        exact h
      have h := hrange (-k) (by omega) hk2 hsep'
      have hres := hdecB (-k) h.1 h.2 d hd hsep'
      have he : v' (-k) = v k := by rw [hv'def]; simp
      rwa [he] at hres
  -- ## 9. the `A`-bound on the resonant window
  have hAraw := hRes0 (q n) hQ hvsol hv0 hpolyv hdec hbd
  have hA : ∀ x ∈ I1r (q n),
      ‖pd α lam (θ + (x : ℝ) * α) (E : ℂ) ((2 * q n - 1) + 1)‖ ≤
        Real.exp ((((2 * q n - 1 : ℕ) : ℝ) + 1) * (Real.log lam - (9 * Real.log lam / 32 - 2 * εf))) := by
    intro x hx
    have h := hAraw x hx
    have h1 : ((2 * q n - 1 : ℕ) + 1) = 2 * q n := by omega
    have h2 : ((((2 * q n - 1 : ℕ) : ℝ)) + 1) = 2 * (q n : ℝ) := by rw [hKcast]; ring
    rw [h1, h2, hεfA']
    exact h
  -- ## 10. uniformity, cardinality and geometry
  have huni : Work.TMC16Core.Uniform (9 * Real.log lam / 64 + b₀ / 4)
      (fun j : {j : ℤ // j ∈ I1r (q n) ∪ I2r (q n) ℓ} =>
        θ + (((j : ℤ) : ℝ) + ((((2 * q n - 1 : ℕ) : ℝ)) - 1) / 2) * α) := by
    have h := hUni n hNuni ℓ hℓ hℓle
    convert h using 2 with j
    rw [hKcast]
    ring
  have hcard : (I1r (q n) ∪ I2r (q n) ℓ).card = (2 * q n - 1) + 1 := by
    rw [card_I1r_I2r (q n) ℓ hℓ]
    omega
  have hgeo : ∀ x ∈ I2r (q n) ℓ, x ≤ y ∧ y ≤ x + (((2 * q n - 1 : ℕ) : ℤ)) - 1 ∧
      ((((5 * q n / 8 : ℕ) : ℝ)) - 1 - bG q n) ≤ ((y - x : ℤ) : ℝ) ∧
      ((((5 * q n / 8 : ℕ) : ℝ)) - 1 - bG q n) ≤
        ((x + (((2 * q n - 1 : ℕ) : ℤ)) - 1 - y : ℤ) : ℝ) :=
    geo_I2r (qn := q n) (ℓ := ℓ) (H := 5 * q n / 8) rfl hbGnn hbG58 hy
  -- ## 11. the Cramer arithmetic
  have hkey : (Real.log lam + εf) * ((((2 * q n - 1 : ℕ) : ℝ)) - 1
        - ((((5 * q n / 8 : ℕ) : ℝ)) - 1 - bG q n))
      - ((((2 * q n - 1 : ℕ) : ℝ)) + 1) * (Real.log lam - (9 * Real.log lam / 32 - 2 * εf))
      + (Real.log lam / 100) * ((((5 * q n / 8 : ℕ) : ℝ)) - 1 - bG q n) < 0 := by
    rw [hεfA']
    exact hkeyN
  have hgap : 4 * ((((2 * q n - 1 : ℕ) : ℝ)) + 1)
        * Real.exp (Real.log lam - (9 * Real.log lam / 32 - 2 * εf))
      < Real.exp ((((2 * q n - 1 : ℕ) : ℝ))
          * ((9 * Real.log lam / 32 - 2 * εf) - (9 * Real.log lam / 64 + b₀ / 4))) := by
    rw [hεfA']
    exact hgapN
  -- ## 12. the endgame
  exact endgame_g (α := α) (lam := lam) (L := Real.log lam)
    (εA := 9 * Real.log lam / 32 - 2 * εf) (εu := 9 * Real.log lam / 64 + b₀ / 4)
    (εf := εf) (L₁ := Real.log lam / 100)
    (g := (((5 * q n / 8 : ℕ) : ℝ)) - 1 - bG q n)
    (E := (E : ℂ)) (θ := θ) (K := 2 * q n - 1)
    (I₁ := I1r (q n)) (I₂ := I2r (q n) ℓ) (y := y)
    hlam1 rfl (by linarith) hεfpos hεuA hεfA hK40 hgap hcard huni hA hg40 hgeo hbd
    (by linarith) (by linarith) hkey

end

end Work.TMC16Core.Assembly
