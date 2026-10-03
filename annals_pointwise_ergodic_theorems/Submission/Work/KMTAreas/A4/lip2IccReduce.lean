/-
# The `Icc` reduction of the windowed inverse Weyl estimate (`lip-2`, §5.2)

The windowed exponential sum

  `winSumIcc M γ ξ P s a b = ∑_{n ∈ Icc a b} win M γ (n - s) · e (ξ P n)`

is, via the sliding-window decomposition of the smoothing kernel (`Work.KMTAreas.A4.boxDecomp`),
an `ℓ¹`-combination of *sharp interval* sums of the unimodular sequence
`winPhase γ ξ P s n = e ((n - s) γ) · e (ξ P n)`.  Consequently a windowed sum of modulus at least
`ε` produces an interval `[c,d]` of length at most `C M` on which the sharp sum of `winPhase` is at
least `ε M / C`.

The restriction to `[a,b]` is handled by extending `winPhase` by zero outside `[a,b]`: the
extraction lemma `Work.KMTAreas.A4.winExtract_block` only needs the sequence to be *bounded* by
`1` (not unimodular), so the zero extension is admissible; the interval it returns is then
intersected with `[a,b]`, which only shortens it.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2GenWeylDefs

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## The integrand of `winSumIcc` against `winPhase` -/

/-- The integrand of the interval-restricted windowed sum is the unmodulated window `win M 0`
times the unimodular sequence `winPhase`. -/
theorem win_mul_ee_eq_win_zero_mul_winPhase (M : ℝ) (γ : FreqCircle) (ξ : ℝ)
    (P : Polynomial ℤ) (s n : ℤ) :
    win M γ (n - s) * ee (ξ * ((P.eval n : ℤ) : ℝ))
      = win M (0 : FreqCircle) (n - s) * winPhase γ ξ P s n := by
  have h0 : (fourier (n - s) (0 : FreqCircle) : ℂ) = 1 := by simp
  simp only [winPhase, win, h0, mul_one]
  ring

/-! ## Shifting the sliding decomposition -/

/-- Shifting the index of a `tsum` over `ℤ`: `∑_k f (k - s) = ∑_k f k`. -/
theorem tsum_comp_sub (f : ℤ → ℂ) (s : ℤ) :
    (∑' k : ℤ, f (k - s)) = ∑' k : ℤ, f k := by
  simpa only [Equiv.coe_addRight, sub_eq_add_neg] using (Equiv.addRight (-s)).tsum_eq f

/-- **The sliding decomposition for the shifted window.**  If `∑_k ρ_k 1_{[k,k+L-1]} = w` then
`∑_k ρ_{k-s} 1_{[k,k+L-1]} = w (· - s)`; this is the form in which the decomposition of the
window is consumed by `Work.KMTAreas.A4.winExtract_block`. -/
theorem sliding_shift (w ρ : ℤ → ℂ) (L : ℕ) (s : ℤ)
    (h : ∀ n : ℤ, (∑' k : ℤ,
        ρ k * (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0)) = w n) (n : ℤ) :
    (∑' k : ℤ, ρ (k - s) * (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0))
      = w (n - s) := by
  have h1 : (∑' k : ℤ, ρ (k - s) * (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0))
      = ∑' k : ℤ, ρ (k - s) * (if k - s ≤ n - s ∧ n - s ≤ k - s + (L : ℤ) - 1
          then (1 : ℂ) else 0) := by
    refine tsum_congr (fun k => ?_)
    by_cases hp : k ≤ n ∧ n ≤ k + (L : ℤ) - 1
    · have hq : k - s ≤ n - s ∧ n - s ≤ k - s + (L : ℤ) - 1 := ⟨by omega, by omega⟩
      rw [if_pos hp, if_pos hq]
    · have hq : ¬ (k - s ≤ n - s ∧ n - s ≤ k - s + (L : ℤ) - 1) := fun hh =>
        hp ⟨by omega, by omega⟩
      rw [if_neg hp, if_neg hq]
  have h2 : (∑' k : ℤ, ρ (k - s) * (if k - s ≤ n - s ∧ n - s ≤ k - s + (L : ℤ) - 1
          then (1 : ℂ) else 0)) = w (n - s) := by
    rw [tsum_comp_sub (fun j : ℤ => ρ j *
      (if j ≤ n - s ∧ n - s ≤ j + (L : ℤ) - 1 then (1 : ℂ) else 0)) s]
    show (∑' k : ℤ, ρ k * (if k ≤ n - s ∧ n - s ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0))
      = w (n - s)
    exact h (n - s)
  exact h1.trans h2

/-- **A `tsum` against a sequence supported in `[a,b]` is the `Icc`-sum.** -/
theorem tsum_mul_eq_sum_Icc_of_eq_zero {u : ℤ → ℂ} {a b : ℤ}
    (hu : ∀ n : ℤ, n ∉ Finset.Icc a b → u n = 0) (f : ℤ → ℂ) :
    (∑' n : ℤ, f n * u n) = ∑ n ∈ Finset.Icc a b, f n * u n := by
  rw [tsum_eq_sum (s := Finset.Icc a b) (fun n hn => by rw [hu n hn, mul_zero])]

/-! ## Extraction of a sharp interval from a restricted windowed sum -/

/-- **Extraction of a sharp interval from a windowed sum restricted to `[a,b]`.**  This is the
`Icc`-analogue of `Work.KMTAreas.A4.winExtract_block`: the sequence is only required to be
bounded by `1` on `[a,b]`, to agree with `g` there and to vanish outside, and the extracted block
is intersected with `[a,b]`. -/
theorem winExtract_Icc (M : ℝ) (L : ℕ) (s : ℤ) (ρ : ℤ → ℂ) (a b : ℤ) (u g : ℤ → ℂ) (A ε : ℝ)
    (hL : 1 ≤ L) (hA : 0 < A) (hε : 0 < ε)
    (hu1 : ∀ n : ℤ, ‖u n‖ ≤ 1)
    (hug : ∀ n : ℤ, n ∈ Finset.Icc a b → u n = g n)
    (hu0 : ∀ n : ℤ, n ∉ Finset.Icc a b → u n = 0)
    (hρ : Summable ρ) (hρb : (∑' k : ℤ, ‖ρ k‖) ≤ A / L)
    (hdecomp : ∀ n : ℤ, win M (0 : FreqCircle) (n - s)
      = ∑' k : ℤ, ρ (k - s) * (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0))
    (hwin : ε ≤ ‖∑' n : ℤ, win M (0 : FreqCircle) (n - s) * u n‖) :
    ∃ c d : ℤ, c ≤ d ∧ (((d - c : ℤ) : ℝ) + 1) ≤ (L : ℝ) ∧
      ε * (L : ℝ) / (2 * A) ≤ ‖∑ n ∈ Finset.Icc c d, g n‖ := by
  obtain ⟨c, d, hcd, hlen, hlow⟩ :=
    winExtract_block (K := 2) (by norm_num) (fun n : ℤ => win M (0 : FreqCircle) (n - s))
      L hL s ρ u A ε hA hε hu1 hρ hρb (fun n => hdecomp n) hwin
  set c' : ℤ := max c a with hc'
  set d' : ℤ := min d b with hd'
  have hfilter : (Finset.Icc c d).filter (fun n => n ∈ Finset.Icc a b) = Finset.Icc c' d' := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨max_le h1 h3, le_min h2 h4⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨le_trans (le_max_left _ _) h1, le_trans h2 (min_le_left _ _)⟩,
        ⟨le_trans (le_max_right _ _) h1, le_trans h2 (min_le_right _ _)⟩⟩
  have hsum : (∑ n ∈ Finset.Icc c d, u n) = ∑ n ∈ Finset.Icc c' d', g n := by
    rw [← hfilter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    by_cases hp : n ∈ Finset.Icc a b
    · rw [if_pos hp, hug n hp]
    · rw [if_neg hp, hu0 n hp]
  have hpos : 0 < ε * (L : ℝ) / (2 * A) := by positivity
  have hne : (Finset.Icc c' d') ≠ ∅ := by
    intro h0
    have h1 := hlow
    rw [hsum] at h1
    rw [h0] at h1
    simp at h1
    linarith
  have hc'd' : c' ≤ d' := by
    by_contra hcon
    exact hne (Finset.Icc_eq_empty_iff.mpr hcon)
  have hd'c' : d' - c' ≤ d - c := by
    rw [hc', hd']
    have h1 : min d b ≤ d := min_le_left _ _
    have h2 : c ≤ max c a := le_max_left _ _
    omega
  refine ⟨c', d', hc'd', ?_, ?_⟩
  · have h1 : ((d' - c' : ℤ) : ℝ) ≤ ((d - c : ℤ) : ℝ) := by exact_mod_cast hd'c'
    linarith
  · rw [hsum] at hlow
    exact hlow

/-! ## The reduction -/

theorem lip2IccReduce : ∃ C : ℝ, 0 < C ∧ ∀ (P : Polynomial ℤ) (M ε : ℝ) (γ : Work.Analysis.InverseTheory.FreqCircle) (ξ : ℝ) (s : ℤ) (a b : ℤ), 2 ≤ M → 0 < ε → ε ≤ 1 → a ≤ b → ε ≤ ‖Work.KMTAreas.A4.winSumIcc M γ ξ P s a b‖ → ∃ c d : ℤ, c ≤ d ∧ (((d - c : ℤ) : ℝ) + 1) ≤ C * M ∧ ε * M / C ≤ ‖∑ n ∈ Finset.Icc c d, Work.KMTAreas.A4.winPhase γ ξ P s n‖ := by
  obtain ⟨C', hC'pos, hbox⟩ := boxDecomp
  obtain ⟨Cα, hCαpos, hα⟩ := winDelta_decay
  set Cw : ℝ := (2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1) with hCw
  have hSnn : (0 : ℝ) ≤ schwartzSeminormSum lipSchPsi := schwartzSeminormSum_nonneg lipSchPsi
  have hCwpos : 0 < Cw := by rw [hCw]; positivity
  set A : ℝ := C' * (Cα + Cw) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  refine ⟨4 * A + 1, by positivity, ?_⟩
  intro P M ε γ ξ s a b hM hε0 hε1 hab hε
  have hM1 : 1 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  set L : ℕ := ⌊M⌋₊ with hL
  have hL1 : 1 ≤ L := by rw [hL]; exact Nat.floor_pos.mpr hM1
  have hLM : (L : ℝ) ≤ M := by rw [hL]; exact Nat.floor_le hMpos.le
  have hMle : M ≤ 2 * (L : ℝ) := by
    have hlt : M < (L : ℝ) + 1 := by rw [hL]; exact Nat.lt_floor_add_one M
    have h1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
    linarith
  have hD : ∀ n : ℤ, ‖win M (0 : FreqCircle) n - win M (0 : FreqCircle) (n - 1)‖
      ≤ Cα / M ^ 2 * jbDecay 12 ((n : ℝ) / M) := by
    intro n
    have h := hα M hM1 0 n
    simpa using h
  have hW : ∀ n : ℤ, ‖win M (0 : FreqCircle) n‖ ≤ Cw / M * jbDecay 12 ((n : ℝ) / M) := by
    intro n
    rw [hCw]
    exact win_zero_decay M hMpos n
  have hper : ∀ r : ℤ, (∑' j : ℤ, (win M (0 : FreqCircle) (r + j * (L : ℤ))
      - win M (0 : FreqCircle) (r + j * (L : ℤ) - 1))) = 0 := by
    intro r
    have h := winZero_classSum_vanish M hM1 r
    simpa only [← hL] using h
  obtain ⟨ρ, hρsumm, hρl1, hρid⟩ :=
    hbox (win M (0 : FreqCircle)) L M Cα Cw hCαpos hCwpos hM1 hL1 hLM hD hW hper
  have hρsum : Summable ρ := hρsumm.of_norm
  have hρb : (∑' k : ℤ, ‖ρ k‖) ≤ A / L := by rw [hA]; exact hρl1
  set u : ℤ → ℂ := fun n => if n ∈ Finset.Icc a b then winPhase γ ξ P s n else 0 with hu
  have hu_mem : ∀ n : ℤ, n ∈ Finset.Icc a b → u n = winPhase γ ξ P s n := by
    intro n hn
    simp only [hu]
    rw [if_pos hn]
  have hu_zero : ∀ n : ℤ, n ∉ Finset.Icc a b → u n = 0 := by
    intro n hn
    simp only [hu]
    rw [if_neg hn]
  have hu1 : ∀ n : ℤ, ‖u n‖ ≤ 1 := by
    intro n
    by_cases h : n ∈ Finset.Icc a b
    · rw [hu_mem n h, winPhase_norm]
    · rw [hu_zero n h, norm_zero]
      norm_num
  have hsum_eq : (∑ n ∈ Finset.Icc a b, win M γ (n - s) * ee (ξ * ((P.eval n : ℤ) : ℝ)))
      = ∑ n ∈ Finset.Icc a b, win M (0 : FreqCircle) (n - s) * winPhase γ ξ P s n :=
    Finset.sum_congr rfl (fun n _ => win_mul_ee_eq_win_zero_mul_winPhase M γ ξ P s n)
  have hε' : ε ≤ ‖∑ n ∈ Finset.Icc a b,
      win M (0 : FreqCircle) (n - s) * winPhase γ ξ P s n‖ := by
    rw [winSumIcc_eq_sum, hsum_eq] at hε
    exact hε
  have htsum : (∑' n : ℤ, win M (0 : FreqCircle) (n - s) * u n)
      = ∑ n ∈ Finset.Icc a b, win M (0 : FreqCircle) (n - s) * winPhase γ ξ P s n := by
    rw [tsum_mul_eq_sum_Icc_of_eq_zero hu_zero]
    exact Finset.sum_congr rfl (fun n hn => by rw [hu_mem n hn])
  have hεw : ε ≤ ‖∑' n : ℤ, win M (0 : FreqCircle) (n - s) * u n‖ := by
    rw [htsum]
    exact hε'
  have hdecomp : ∀ n : ℤ, win M (0 : FreqCircle) (n - s)
      = ∑' k : ℤ, ρ (k - s) * (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0) :=
    fun n => (sliding_shift (win M (0 : FreqCircle)) ρ L s hρid n).symm
  obtain ⟨c, d, hcd, hlen, hlow⟩ :=
    winExtract_Icc M L s ρ a b u (winPhase γ ξ P s) A ε hL1 hApos hε0 hu1 hu_mem hu_zero
      hρsum hρb hdecomp hεw
  refine ⟨c, d, hcd, ?_, ?_⟩
  · calc (((d - c : ℤ) : ℝ) + 1) ≤ (L : ℝ) := hlen
      _ ≤ M := hLM
      _ ≤ (4 * A + 1) * M := by nlinarith [hApos, hMpos.le]
  · have hstep : ε * M / (4 * A + 1) ≤ ε * (L : ℝ) / (2 * A) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc ε * M * (2 * A) ≤ ε * (2 * (L : ℝ)) * (2 * A) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMle hε0.le)
              (by positivity)
        _ = ε * (L : ℝ) * (4 * A) := by ring
        _ ≤ ε * (L : ℝ) * (4 * A + 1) := by
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact hstep.trans hlow

end Work.KMTAreas.A4
