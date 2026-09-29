import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.RegWin
import Submission.Work.TMC16Core.Assembly.s0_reg
import Submission.Work.TMC16Core.Assembly.res_reg
import Submission.Work.TMC16Core.Assembly.nr_branch
import Submission.Work.TMC16Core.Assembly.level_sel
import Submission.Work.TMC16Core.Assembly.dispatch
import Submission.Work.TMC16Core.Assembly.hyDeltaBin
import Submission.Work.TMC16Core.Assembly.thirty_qn_le
import Submission.Work.TMC16Core.Assembly.nr_s_exists
import Submission.Work.TMC16Core.CF.cf_data_bridge

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! # `Assembly.Glue` — the top-level assembly of C16 (AJ §9)

* `R`  (resonant, `k₀ ≤ bG n`): `Assembly.res_reg` (AJ Lemmas 9.10–9.13);
* `B`/`A`/`C` (non-resonant, `k₀ > bG n`, `k₀ < 3q(n-1)+1`): `Assembly.s0_reg` with
  `H = q n`, `q(n-1)`, `4q(n-1)`;
* `N3` (non-resonant, `k₀ ≥ 3q(n-1)+1`): `Assembly.nr_branch`.
-/

/-- If `x^(8/9) < b` with `b ≥ 1` and `x ≥ 0` then `x ≤ b^2`. -/
lemma le_sq_of_rpow_eight_ninths_lt {x b : ℝ} (hx : 0 ≤ x) (hb : 1 ≤ b)
    (h : x ^ ((8 : ℝ) / 9) < b) : x ≤ b ^ 2 := by
  have h1 : x = (x ^ ((8 : ℝ) / 9)) ^ ((9 : ℝ) / 8) := by
    rw [← Real.rpow_mul hx]
    norm_num
  rw [h1]
  calc (x ^ ((8 : ℝ) / 9)) ^ ((9 : ℝ) / 8)
      ≤ b ^ ((9 : ℝ) / 8) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hx _) h.le (by norm_num)
    _ ≤ b ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb (by norm_num)
    _ = b ^ 2 := Real.rpow_two b

/-- `bG q n ≤ q n / 20 + 3` once `q n ≥ 20^9`. -/
lemma bG_le_div {q : ℕ → ℕ} {n : ℕ} (hmono : StrictMono q) (h : 20 ^ 9 ≤ q n) :
    bG q n ≤ (q n : ℝ) / 20 + 3 := by
  have hQ20 : (20 : ℝ) ≤ (q n : ℝ) := by
    have h1 : ((20 : ℕ) ^ 9 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast h
    calc (20 : ℝ) ≤ ((20 : ℕ) ^ 9 : ℝ) := by norm_num
      _ ≤ (q n : ℝ) := h1
  have hQpos : (0 : ℝ) < (q n : ℝ) := lt_of_lt_of_le (by norm_num) hQ20
  have hroot : (20 : ℝ) ≤ (q n : ℝ) ^ ((1 : ℝ) / 9) := by
    have h1 : (((20 : ℝ)) ^ (9 : ℕ)) ^ ((1 : ℝ) / 9) ≤ (q n : ℝ) ^ ((1 : ℝ) / 9) := by
      apply Real.rpow_le_rpow (by positivity)
      · exact_mod_cast h
      · norm_num
    have h2 : (((20 : ℝ)) ^ (9 : ℕ)) ^ ((1 : ℝ) / 9) = 20 := by
      rw [show (((20 : ℝ)) ^ (9 : ℕ)) = ((20 : ℝ)) ^ (((9 : ℕ) : ℝ)) from
        (Real.rpow_natCast 20 9).symm]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 20)]
      norm_num
    rw [h2] at h1; exact h1
  have hkey : (q n : ℝ) ^ ((8 : ℝ) / 9) ≤ (q n : ℝ) / 20 := by
    have h8 : (q n : ℝ) ^ ((8 : ℝ) / 9) * (q n : ℝ) ^ ((1 : ℝ) / 9) =
        (q n : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hQpos]; norm_num
    rw [Real.rpow_one] at h8
    have h20 := mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hQpos.le ((8 : ℝ) / 9))
    rw [h8] at h20
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 20)]
    linarith
  have hle : (q (n - 1) : ℝ) / 20 + 3 ≤ (q n : ℝ) / 20 + 3 := by
    have h1 : q (n - 1) ≤ q n := hmono.monotone (Nat.sub_le n 1)
    have h2 : (q (n - 1) : ℝ) ≤ (q n : ℝ) := by exact_mod_cast h1
    linarith
  rw [bG]
  exact max_le (le_trans hkey (by linarith)) hle

/-- The level bound `y ≤ bG q (n+1)` dominates the hypothesis
`y ≤ 100 (q(n+1)^{8/9} + q n)` of the branches. -/
lemma bG_le_hundred {q : ℕ → ℕ} {n : ℕ} (hqn : 1 ≤ q n) (hqn1 : 1 ≤ q (n + 1)) :
    bG q (n + 1) ≤ 100 * ((q (n + 1) : ℝ) ^ ((8 : ℝ) / 9) + (q n : ℝ)) := by
  have h0 : (0 : ℝ) ≤ (q (n + 1) : ℝ) ^ ((8 : ℝ) / 9) := Real.rpow_nonneg (by positivity) _
  have h1 : (0 : ℝ) ≤ (q n : ℝ) := by positivity
  have h2 : (1 : ℝ) ≤ (q (n + 1) : ℝ) ^ ((8 : ℝ) / 9) :=
    Real.one_le_rpow (by exact_mod_cast hqn1) (by norm_num)
  rw [bG, Nat.add_sub_cancel]
  refine max_le ?_ ?_ <;> linarith

/-- `y * Δ n ≤ 3/4` from the level bound `y ≤ bG q (n+1)`. -/
lemma hyDelta_of_bG {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ} {y : ℤ}
    (hΔpos : ∀ i, 0 < Δ i) (hΔup : Δ n < 1 / ((q (n + 1) : ℝ)))
    (hqpos : (0 : ℝ) < (q n : ℝ)) (hqle : (q n : ℝ) ≤ (q (n + 1) : ℝ))
    (hqleN : q n ≤ q (n + 1))
    (hqn : 20 ≤ q n) (hy1 : 0 < (y : ℝ))
    (hy : (y : ℝ) ≤ bG q (n + 1)) : (y : ℝ) * Δ n ≤ 3 / 4 := by
  have hb : (y : ℝ) ≤ max ((q (n + 1) : ℝ) ^ ((8 : ℝ) / 9)) ((q n : ℝ) / 20 + 3) := by
    rw [bG, Nat.add_sub_cancel] at hy; exact hy
  rcases le_max_iff.mp hb with h | h
  · refine hyDeltaBin (n := n) (y := y) hΔpos hΔup hqpos hqle
      (by exact_mod_cast (le_trans hqn hqleN)) ?_
    exact le_trans h (le_max_left _ _)
  · have hlt : (y : ℝ) * Δ n < (y : ℝ) * (1 / (q (n + 1) : ℝ)) :=
      mul_lt_mul_of_pos_left hΔup hy1
    have hq1 : (0 : ℝ) < (q (n + 1) : ℝ) := by
      have : (0 : ℝ) < (q n : ℝ) := hqpos
      linarith
    have hdiv : (y : ℝ) / (q (n + 1) : ℝ) ≤ (q n : ℝ) / 20 / (q n : ℝ) + 3 / (q n : ℝ) := by
      have h1 : (y : ℝ) / (q (n + 1) : ℝ) ≤ ((q n : ℝ) / 20 + 3) / (q (n + 1) : ℝ) :=
        div_le_div_of_nonneg_right h hq1.le
      have h2 : ((q n : ℝ) / 20 + 3) / (q (n + 1) : ℝ) ≤ ((q n : ℝ) / 20 + 3) / (q n : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hqpos hqle
      have h3 : ((q n : ℝ) / 20 + 3) / (q n : ℝ) = (q n : ℝ) / 20 / (q n : ℝ) + 3 / (q n : ℝ) :=
        add_div _ _ _
      linarith
    have h20 : (20 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqn
    have hfin : (q n : ℝ) / 20 / (q n : ℝ) + 3 / (q n : ℝ) ≤ 3 / 4 := by
      have h1 : (q n : ℝ) / 20 / (q n : ℝ) = 1 / 20 := by
        rw [div_div, mul_comm]
        field_simp
      have h2 : 3 / (q n : ℝ) ≤ 3 / 20 := by
        rw [div_le_div_iff₀ hqpos (by norm_num : (0 : ℝ) < 20)]
        linarith [h20]
      linarith [h1, h2]
    have : (y : ℝ) * (1 / (q (n + 1) : ℝ)) = (y : ℝ) / (q (n + 1) : ℝ) := by ring
    linarith

/-- `IsRegularBig` is monotone in the required window length. -/
lemma IsRegularBig_mono' {α lam θ : ℝ} {E : ℂ} {L₁ q q' : ℝ} {y : ℤ} (hq : q' ≤ q)
    (h : IsRegularBig α lam θ E L₁ q y) : IsRegularBig α lam θ E L₁ q' y := by
  obtain ⟨x₁, x₂, h1, h2, hlen, hd1, hd2, hdet, hg1, hg2⟩ := h
  exact ⟨x₁, x₂, h1, h2, le_trans hq hlen, hd1, hd2, hdet, hg1, hg2⟩

/-- **C16, the multiscale regularity family (AJ §9).** -/
theorem glue (h4 : Work.TMC16Core.P_LEBasics) (h7 : Work.TMC16Core.P_BJ_dioph)
    {α b₀ lam : ℝ} (hα : Irrational α) (hb₀ : 0 < b₀)
    (hDioph : Work.TMC16Core.DiophBelow α b₀)
    (hlam : Real.exp (16 * b₀ / 9) < lam)
    {E : ℝ} (hE : E ∈ Work.TMC16Core.amoSpec α lam) {θ : ℝ}
    (hθ : θ ∉ Work.TMC16Core.Theta α) {u : ℤ → ℂ}
    (hu : Work.TMC16Core.IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0) :
    Work.TMC16Core.RegFamily α lam θ E := by
  set L : ℝ := Real.log lam with hLdef
  have hlam1 : 1 < lam := Core.one_lt_lam (le_of_lt hb₀) hlam
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos hlam1
  have hLb : 16 * b₀ / 9 < L := by
    rw [hLdef]
    have h := Real.log_lt_log (Real.exp_pos (16 * b₀ / 9)) hlam
    rwa [Real.log_exp] at h
  obtain ⟨q, Δ, hqpos, hmono, hqstep, hΔpos, hΔeq, hΔup, hΔlo, hbest, hblkj, hqgr⟩ :=
    CF.cf_data_bridge hα (le_of_lt hb₀) hDioph (ε := 1) (by norm_num)
  obtain ⟨Ns0, hs0⟩ := s0_reg (q := q) (Δ := Δ) (L := L) (κ := 9 * L / 32 - b₀ / 2)
      h4 h7 hα hb₀ hDioph hLdef hlam (by linarith) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
      hE hθ hu hu0
  obtain ⟨Nres, hres⟩ := res_reg (q := q) (Δ := Δ) h4 h7 hα hb₀ hDioph hlam
      hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hE hθ hu hu0
  obtain ⟨Nnr, hnr⟩ := nr_branch (q := q) (Δ := Δ) (L := L) h4 h7 hα hb₀ hDioph hLdef hlam
      hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hE hθ hu hu0
  refine ⟨L / 100, div_pos hLpos (by norm_num), fun qq hqq => ?_⟩
  set N : ℕ := max (max Ns0 Nres) (max (max Nnr (Nat.ceil qq + 2)) (66 ^ 8 + 1)) with hN
  have hNs0 : Ns0 ≤ N := by rw [hN]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hNres : Nres ≤ N := by rw [hN]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hNqq : Nat.ceil qq + 2 ≤ N := by
    rw [hN]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hN66 : 66 ^ 8 + 1 ≤ N := by rw [hN]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hNnr : Nnr ≤ N := by
    rw [hN]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  refine ⟨bG q N, fun y hy => ?_⟩
  -- ## `y ≥ 1`
  have hy1 : 1 ≤ y := by
    by_contra hc
    have hy0 : y ≤ 0 := by omega
    have hy0' : (y : ℝ) ≤ 0 := by exact_mod_cast hy0
    have hb : (3 : ℝ) ≤ bG q N := by
      have h1 : (q (N - 1) : ℝ) / 20 + 3 ≤ bG q N := le_max_right _ _
      have h2 : (0 : ℝ) ≤ (q (N - 1) : ℝ) := by positivity
      linarith
    linarith [hy]
  have hy1' : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  -- ## level selection
  obtain ⟨n, hnN, hbn, hbny⟩ := level_sel hqpos hmono N y hy
  have hn66b : 66 ^ 8 + 1 ≤ n := le_trans hN66 hnN
  have hnq : n ≤ q n := self_le_of_strictMono hmono n
  have hn66 : 66 ^ 8 ≤ q n := by omega
  have hqL : 40 ≤ q n := by omega
  have hq20 : 20 ^ 9 ≤ q n := by
    have : 20 ^ 9 ≤ 66 ^ 8 := by norm_num
    omega
  have hq1 : 1 ≤ q n := by omega
  have hqL' : (40 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqL
  have hqnpos : (0 : ℝ) < (q n : ℝ) := by linarith
  have h1q : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hq1
  have hqmono : (q (n - 1) : ℝ) ≤ (q n : ℝ) := by
    have h : q (n - 1) ≤ q n := hmono.monotone (Nat.sub_le n 1)
    exact_mod_cast h
  have hqmono' : (q n : ℝ) ≤ (q (n + 1) : ℝ) := by
    have h : q n ≤ q (n + 1) := hmono.monotone (by omega)
    exact_mod_cast h
  have hq1' : 1 ≤ q (n + 1) := by
    have h : q n ≤ q (n + 1) := hmono.monotone (by omega)
    omega
  have hy100 : (y : ℝ) ≤ 100 * ((q (n + 1) : ℝ) ^ ((8 : ℝ) / 9) + (q n : ℝ)) :=
    le_trans hbny (bG_le_hundred hq1 hq1')
  have hqstep1 : (1 : ℕ) ≤ q (n - 1) := by
    have h : n - 1 ≤ q (n - 1) := self_le_of_strictMono hmono (n - 1)
    omega
  have hqstep1' : (1 : ℝ) ≤ (q (n - 1) : ℝ) := by exact_mod_cast hqstep1
  have hqstep40 : (40 : ℝ) ≤ (q (n - 1) : ℝ) := by
    have h : 40 ≤ q (n - 1) := by
      have h' : n - 1 ≤ q (n - 1) := self_le_of_strictMono hmono (n - 1)
      omega
    exact_mod_cast h
  -- ## the nearest multiple
  set mr : ℤ := round ((y : ℝ) / (q n : ℝ)) with hmrd
  set mf : ℤ := ⌊(y : ℝ) / (q n : ℝ)⌋ with hmfd
  have hqnext : 40 ^ 9 ≤ q (n + 1) := by
    have h1 : 40 ^ 9 ≤ 66 ^ 8 := by norm_num
    have h2 : q n ≤ q (n + 1) := hmono.monotone (by omega)
    omega
  obtain ⟨hmr0, hmf0, hmf1, hmf2, hmrcas, hk0half, hk0min, hmry, hmrmq, hmr0le⟩ :=
    dispatch (q := q) (n := n) (y := y) (mr := mr) (mf := mf)
      (hqpos n) (by omega) hqnext rfl rfl
  let kZ : ℤ := |y - mr * (q n : ℤ)|
  have hkZdef : kZ = |y - mr * (q n : ℤ)| := rfl
  have hkZ : (kZ : ℝ) = |(y : ℝ) - (mr : ℝ) * (((q n : ℤ)) : ℝ)| := by
    rw [hkZdef, Int.cast_abs]
    congr 1
    push_cast
    ring
  have hk0nn : (0 : ℤ) ≤ kZ := by rw [hkZdef]; exact abs_nonneg _
  have hkZhalf : (2 : ℤ) * kZ ≤ (q n : ℤ) := hk0half
  have hkZmin : ∀ ℓ : ℤ, kZ ≤ |y - ℓ * (q n : ℤ)| := hk0min
  have hkR : (kZ : ℝ) ≤ (q n : ℝ) / 2 := by
    have h : (2 : ℝ) * (kZ : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hkZhalf
    linarith
  have hqcast : (q n : ℝ) = (((q n : ℤ)) : ℝ) := by push_cast; ring
  have hyM : (mr : ℝ) * (q n : ℝ) - (y : ℝ) ≤ (kZ : ℝ) := by
    have h := neg_le_abs ((y : ℝ) - (mr : ℝ) * (((q n : ℤ)) : ℝ))
    rw [hkZ, hqcast]
    linarith
  have hyM' : (y : ℝ) ≤ (mr : ℝ) * (q n : ℝ) + (kZ : ℝ) := by
    have h := le_abs_self ((y : ℝ) - (mr : ℝ) * (((q n : ℤ)) : ℝ))
    rw [hkZ, hqcast]
    linarith
  -- ## `mr ≠ 0 ⟹ y ≤ q(n+1)^{8/9}`
  have hy_rpow : mr ≠ 0 → (y : ℝ) ≤ (q (n + 1) : ℝ) ^ ((8 : ℝ) / 9) := by
    intro hm0
    by_contra hcon
    have hcon' : (q (n + 1) : ℝ) ^ ((8 : ℝ) / 9) < (y : ℝ) := lt_of_not_ge hcon
    have hy2 : (y : ℝ) ≤ (q n : ℝ) / 20 + 3 := by
      have hb : (y : ℝ) ≤ max ((q (n + 1) : ℝ) ^ ((8 : ℝ) / 9)) ((q n : ℝ) / 20 + 3) := by
        rw [bG, Nat.add_sub_cancel] at hbny; exact hbny
      rcases le_max_iff.mp hb with h | h
      · exact absurd h (not_le.mpr hcon')
      · exact h
    have hm1 : (1 : ℤ) ≤ mr := by omega
    have hm1' : (1 : ℝ) ≤ (mr : ℝ) := by exact_mod_cast hm1
    have hM : (q n : ℝ) ≤ (mr : ℝ) * (q n : ℝ) := by nlinarith
    linarith [hM, hyM, hkR, hy2, hqL']
  have hmq : mr ≠ 0 → 10 * (mr + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ) :=
    fun h0 => hmrmq h0 (hy_rpow h0)
  -- ## the length bound of `RegFamily`
  have hqq_le : (qq : ℝ) ≤ (q (n - 1) : ℝ) - 1 := by
    have h1 : Nat.ceil qq + 1 ≤ n - 1 := by omega
    have h2 : n - 1 ≤ q (n - 1) := self_le_of_strictMono hmono (n - 1)
    have h3 : Nat.ceil qq + 1 ≤ q (n - 1) := le_trans h1 h2
    have h4 : (Nat.ceil qq : ℝ) + 1 ≤ (q (n - 1) : ℝ) := by exact_mod_cast h3
    have h5 : qq ≤ (Nat.ceil qq : ℝ) := Nat.le_ceil qq
    linarith
  -- ## the `s = 0`-type branches packaged
  have s0step : ∀ H : ℕ,
      (H = q (n - 1) ∨ H = q n ∨ (H = 4 * q (n - 1) ∧ H < q n)) →
      (q n : ℝ) ≤ (H : ℝ) ^ 2 →
      ((H : ℝ) - 1) / 20 + 3 ≤ (kZ : ℝ) →
      (kZ : ℝ) ≤ 95 * ((H : ℝ) - 1) / 100 - 3 →
      RegWin α lam θ (E : ℂ) (7 * L / 10) (((H - 1 : ℕ) : ℝ) / 40) (H - 1) y := by
    intro H hd hHq hlo hhi
    refine hs0 n (le_trans hNs0 hnN) H y mr hd hHq hy1 hy100 hmr0 hmq ?_ ?_
    · rw [← hkZ]; exact hlo
    · rw [← hkZ]; exact hhi
  have toBig_s0 : ∀ H : ℕ,
      (H = q (n - 1) ∨ H = q n ∨ (H = 4 * q (n - 1) ∧ H < q n)) →
      (q n : ℝ) ≤ (H : ℝ) ^ 2 →
      ((H : ℝ) - 1) / 20 + 3 ≤ (kZ : ℝ) →
      (kZ : ℝ) ≤ 95 * ((H : ℝ) - 1) / 100 - 3 →
      IsRegularBig α lam θ (E : ℂ) (L / 100) (qq : ℝ) y := by
    intro H hd hHq hlo hhi
    have hH1 : 1 ≤ H := by
      rcases hd with h | h | h
      · rw [h]; omega
      · rw [h]; omega
      · rw [h.1]; omega
    have hcast : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by
      rw [Nat.cast_sub hH1]; push_cast; ring
    have hqH : (q (n - 1) : ℝ) ≤ (H : ℝ) := by
      rcases hd with h | h | h
      · rw [h]
      · rw [h]; exact hqmono
      · rw [h.1]; push_cast; linarith [hqstep1']
    refine RegWin.toBig (s0step H hd hHq hlo hhi) ?_ ?_ ?_ ?_
    · rw [show (40 : ℝ) * (((H - 1 : ℕ) : ℝ) / 40) = ((H - 1 : ℕ) : ℝ) from by ring]
    · rw [hcast]; linarith [hqq_le, hqH]
    · linarith
    · linarith
  -- ## the branch dispatch
  by_cases hR : (kZ : ℝ) ≤ bG q n
  · -- ### R : resonant
    have hmr_ne : mr ≠ 0 := by
      intro h0
      have h1 : kZ = y := by
        rw [hkZdef, h0, Int.zero_mul, sub_zero]
        exact abs_of_nonneg (by omega : (0 : ℤ) ≤ y)
      have h1' : (kZ : ℝ) = (y : ℝ) := by exact_mod_cast h1
      linarith [hR, hbn]
    have hy_ge : (q n : ℝ) / 2 ≤ (y : ℝ) := by
      have hm1 : (1 : ℤ) ≤ mr := by omega
      have hm1' : (1 : ℝ) ≤ (mr : ℝ) := by exact_mod_cast hm1
      have hM : (q n : ℝ) ≤ (mr : ℝ) * (q n : ℝ) := by nlinarith
      linarith [hM, hyM, hkR]
    have h30 : (30 : ℝ) * (q n : ℝ) ≤ (q (n + 1) : ℝ) :=
      thirty_qn_le hn66 hy_ge (hy_rpow hmr_ne)
    have h30nat : 30 * q n ≤ q (n + 1) := by exact_mod_cast h30
    have hbGn : bG q n ≤ (q n : ℝ) / 20 + 3 := bG_le_div hmono hq20
    have hM2 : (mr : ℝ) * (q n : ℝ) ≤ 2 * (q (n + 1) : ℝ) ^ ((8 : ℝ) / 9) := by
      have h4 : (1 : ℝ) ≤ (q (n + 1) : ℝ) ^ ((8 : ℝ) / 9) :=
        Real.one_le_rpow (by linarith) (by norm_num)
      have h5 : (q n : ℝ) / 20 + 3 ≤ (y : ℝ) + 3 := by linarith [hkR, hy_ge]
      linarith [hyM', hR, hbGn, h5, h4, hy_rpow hmr_ne]
    have hℓb : ((mr.toNat : ℕ) : ℝ) ≤
        2 * (q (n + 1) : ℝ) ^ ((8 : ℝ) / 9) / (q n : ℝ) := by
      have hcast : ((mr.toNat : ℕ) : ℝ) = (mr : ℝ) := by
        have h : ((mr.toNat : ℕ) : ℤ) = mr := Int.toNat_of_nonneg hmr0
        exact_mod_cast h
      rw [hcast, le_div_iff₀ hqnpos]
      linarith
    have hky : (kZ : ℝ) ≤ bG q n := hR
    have hky' : |(y : ℝ) - (((mr.toNat : ℤ)) : ℝ) * (((q n : ℤ)) : ℝ)| ≤ bG q n := by
      have h1 : (((mr.toNat : ℤ)) : ℝ) = (mr : ℝ) := by
        have h : ((mr.toNat : ℕ) : ℤ) = mr := Int.toNat_of_nonneg hmr0
        exact_mod_cast h
      rw [h1, ← hkZ]
      exact hky
    have hres' := hres n (le_trans hNres hnN) mr.toNat (by omega) hℓb h30nat
    refine RegWin.toBig (hres' y hky') ?_ ?_ ?_ ?_
    · have hfloor : ((5 * q n / 8 : ℕ) : ℝ) ≥ 5 * (q n : ℝ) / 8 - 1 := by
        have h := (Nat.div_lt_iff_lt_mul (k := 8) (x := 5 * q n) (y := 5 * q n / 8 + 1)
            (by norm_num)).mp (Nat.lt_succ_self (5 * q n / 8))
        have h' : (5 * (q n : ℝ)) < (((5 * q n / 8 : ℕ) : ℝ) + 1) * 8 := by
          have h2 : ((5 * q n : ℕ) : ℝ) < ((((5 * q n / 8 + 1) * 8 : ℕ)) : ℝ) := by
            exact_mod_cast h
          push_cast at h2
          linarith [h2]
        linarith
      have hcast2 : ((2 * q n - 1 : ℕ) : ℝ) = 2 * (q n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * q n)]
        push_cast; ring
      rw [hcast2]
      have h5 : bG q n ≤ (q n : ℝ) / 20 + 3 := hbGn
      nlinarith
    · have hcast2 : ((2 * q n - 1 : ℕ) : ℝ) = 2 * (q n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * q n)]
        push_cast; ring
      rw [hcast2]
      linarith [hqq_le, hqmono]
    · linarith
    · linarith
  · -- ### non-resonant
    have hkgt : bG q n < (kZ : ℝ) := lt_of_not_ge hR
    have hrpow_lt : (q n : ℝ) ^ ((8 : ℝ) / 9) < (kZ : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hkgt
    have hqlo : (q (n - 1) : ℝ) / 20 + 3 ≤ (kZ : ℝ) :=
      le_trans (le_max_right _ _) hkgt.le
    by_cases hB : ((q n : ℝ) - 1) / 20 + 3 ≤ (kZ : ℝ)
    · -- ### B
      refine toBig_s0 (q n) (Or.inr (Or.inl rfl)) ?_ hB ?_
      · nlinarith [h1q]
      · linarith [hkR, hqL']
    · have hkB : (kZ : ℝ) < ((q n : ℝ) - 1) / 20 + 3 := lt_of_not_ge hB
      by_cases hN3 : 3 * (q (n - 1) : ℤ) + 1 ≤ kZ
      · -- ### N3
        have hk : (kZ.toNat : ℤ) = kZ := Int.toNat_of_nonneg hk0nn
        have h2kZ : (2 : ℤ) * (kZ.toNat : ℤ) ≤ (q n : ℤ) := by rw [hk]; exact hkZhalf
        have h3qZ : (3 : ℤ) * (q (n - 1) : ℤ) + 1 ≤ (kZ.toNat : ℤ) := by rw [hk]; exact hN3
        have hkQ : 2 * kZ.toNat ≤ q n := by exact_mod_cast h2kZ
        have h3q : 3 * q (n - 1) + 1 ≤ kZ.toNat := by exact_mod_cast h3qZ
        have hQ9 : 3 ^ 9 < q n := by omega
        have hqnm1 : n - 1 ≤ q (n - 1) := self_le_of_strictMono hmono (n - 1)
        have hqq72 : 72 ≤ q (n - 1) := by omega
        have hkR' : (q n : ℝ) ^ ((8 : ℝ) / 9) ≤ (kZ.toNat : ℝ) := by
          rw [show (kZ.toNat : ℝ) = (kZ : ℝ) by exact_mod_cast hk]
          exact hrpow_lt.le
        obtain ⟨s, hs3, hsq, h2sq, hsres⟩ :=
          nr_s_exists (Q := q n) (qq := q (n - 1)) (k := kZ.toNat)
            hQ9 hqq72 h3q hkQ hkR'
        have h2sqZ : (2 * (s : ℤ)) * (q (n - 1) : ℤ) < (q n : ℤ) := by
          have h : ((2 * (s * q (n - 1)) : ℕ) : ℤ) < (q n : ℤ) := by exact_mod_cast h2sq
          push_cast at h
          linarith
        have hsqZ : (s : ℤ) * (q (n - 1) : ℤ) ≤ kZ := by
          have h : ((s * q (n - 1) : ℕ) : ℤ) ≤ (kZ.toNat : ℤ) := by exact_mod_cast hsq
          push_cast at h
          linarith
        have hnres : ∀ ℓ : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - ℓ * (q n : ℤ)| :=
          fun ℓ => le_trans hsqZ (hkZmin ℓ)
        have hyΔ : (y : ℝ) * Δ n ≤ 3 / 4 :=
          hyDelta_of_bG (n := n) (y := y) hΔpos (hΔup n) hqnpos hqmono'
            (by exact_mod_cast (hmono.monotone (by omega : n ≤ n + 1))) (by omega) hy1' hbny
        have hmf1' : ((mf.toNat : ℤ) * (q n : ℤ)) ≤ y := by
          have h : (mf.toNat : ℤ) = mf := Int.toNat_of_nonneg hmf0
          rw [h]; exact hmf1
        have hmf2' : y < (((mf.toNat : ℤ) + 1) * (q n : ℤ)) := by
          have h : (mf.toNat : ℤ) = mf := Int.toNat_of_nonneg hmf0
          rw [h]; exact hmf2
        have hmain := hnr n (le_trans hNnr hnN) s mf.toNat y hs3 hy1 hyΔ hy100
          hmf1' hmf2' hnres h2sqZ (by
            have h : (q n : ℝ) ^ ((8 : ℝ) / 9) ≤ (kZ.toNat : ℝ) := hkR'
            linarith [hsres])
        have hqKnr : (qq : ℝ) ≤ (Core.Knr q n s : ℝ) := by
          have hcastK : ((Core.Knr q n s : ℕ) : ℝ) = 2 * (s : ℝ) * (q (n - 1) : ℝ) - 1 := by
            have h1 : 1 ≤ 2 * s * q (n - 1) := by
              have h2 : 6 ≤ 2 * s := by omega
              have h3 : 6 * q (n - 1) ≤ 2 * s * q (n - 1) := Nat.mul_le_mul_right _ h2
              have h4 : 1 ≤ 6 * q (n - 1) := by
                have h5 : 1 ≤ q (n - 1) := hqstep1
                omega
              omega
            unfold Core.Knr
            rw [Nat.cast_sub h1]
            push_cast; ring
          rw [hcastK]
          have h2 : (6 : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast (by omega : 6 ≤ 2 * s)
          have h3 : 6 * (q (n - 1) : ℝ) ≤ 2 * (s : ℝ) * (q (n - 1) : ℝ) := by
            nlinarith [h2, hqstep1']
          linarith [hqq_le, h3, hqstep1']
        exact IsRegularBig_mono' hqKnr hmain
      · -- ### A or C
        have hkN3 : kZ < 3 * (q (n - 1) : ℤ) + 1 := lt_of_not_ge hN3
        have hk3 : (kZ : ℝ) < 3 * (q (n - 1) : ℝ) + 1 := by exact_mod_cast hkN3
        by_cases hA : (kZ : ℝ) ≤ 95 * ((q (n - 1) : ℝ) - 1) / 100 - 3
        · -- ### A
          have hklt : (kZ : ℝ) < (q (n - 1) : ℝ) := by linarith [hqstep1', hA]
          have hqlo' : ((q (n - 1) : ℝ) - 1) / 20 + 3 ≤ (kZ : ℝ) := by linarith [hqlo]
          refine toBig_s0 (q (n - 1)) (Or.inl rfl) ?_ hqlo' hA
          exact le_sq_of_rpow_eight_ninths_lt (by positivity) hqstep1'
            (lt_trans hrpow_lt hklt)
        · -- ### C
          have hkA : 95 * ((q (n - 1) : ℝ) - 1) / 100 - 3 < (kZ : ℝ) := lt_of_not_ge hA
          have hH4lt : 4 * q (n - 1) < q n := by
            by_contra hc
            push_neg at hc
            have hc' : (q n : ℝ) ≤ 4 * (q (n - 1) : ℝ) := by exact_mod_cast hc
            linarith [hkB, hkA, hqstep40]
          have h4R : ((4 * q (n - 1) : ℕ) : ℝ) = 4 * (q (n - 1) : ℝ) := by push_cast; ring
          refine toBig_s0 (4 * q (n - 1)) (Or.inr (Or.inr ⟨rfl, hH4lt⟩)) ?_ ?_ ?_
          · -- `qₙ ≤ (4q(n-1))²`
            rw [h4R]
            refine le_sq_of_rpow_eight_ninths_lt (by positivity) ?_ (lt_trans hrpow_lt ?_)
            · linarith [hqstep1']
            · linarith [hk3]
          · -- lower
            rw [h4R]; linarith [hkA, hqstep40]
          · -- upper
            rw [h4R]; linarith [hk3, hqstep40]

end Work.TMC16Core.Assembly
