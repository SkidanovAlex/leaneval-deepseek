import Mathlib
import Submission.Work.GM.Trace.Spart_defs
import Submission.Work.GM.Trace.hhat_norm_le_Azero

namespace Work.GM.Trace

open Complex Finset
open scoped BigOperators
open Submission.GM Submission.LargeValues

/-!
# GM Lemma 4.5: the size of `I_m` for `m` with a single non-zero coordinate

For `m : ℤ³` with `nzCount m = 1` exactly one of the three frequencies
`m₁N, m₂N, m₃N` appearing in

`I_m = N³ Σ_{t₁,t₂,t₃ ∈ W} ĥ_{t₁-t₂}(m₁N) ĥ_{t₂-t₃}(m₂N) ĥ_{t₃-t₁}(m₃N)`

is non-zero, namely `(rho m)·N`.  The corresponding factor is bounded by the decay
hypothesis `‖ĥ_t(ξ)‖ ≤ C (1+|t|)^j / |ξ|^j` (with `|t₁-t₂| ≤ T` because `W ⊆ [0,T]`),
while the other two factors are bounded by `Azero`; summing over the `|W|³` triples gives

`‖I_m‖ ≤ N³ |W|³ Azero² C (1+T)^j / (|rho m|^j N^j)`.
-/

/-- Bound for a single factor `ĥ_{t-s}(kN)` with `k ≠ 0`, using `t, s ∈ [0, T]` and the
decay hypothesis. -/
private theorem hhat_mul_bound (N : ℕ) (hN : 1 ≤ N) (T : ℝ) (hT : 0 ≤ T)
    (j : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ t ξ : ℝ, ξ ≠ 0 → ‖hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j)
    {t s : ℝ} (ht : t ∈ Set.Icc 0 T) (hs : s ∈ Set.Icc 0 T)
    {k : ℤ} (hk : k ≠ 0) :
    ‖hhat (t - s) ((k : ℝ) * N)‖ ≤ C * (1 + T) ^ j / (|(k : ℝ)| ^ j * (N : ℝ) ^ j) := by
  have hNpos' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkre : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hξne : (k : ℝ) * N ≠ 0 := mul_ne_zero hkre (ne_of_gt hNpos')
  have h1 : ‖hhat (t - s) ((k : ℝ) * N)‖ ≤ C * (1 + |t - s|) ^ j / |(k : ℝ) * N| ^ j :=
    hdec _ _ hξne
  have habs : |t - s| ≤ T := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [ht.2, hs.1], by linarith [hs.2, ht.1]⟩
  have hden : |(k : ℝ) * N| ^ j = |(k : ℝ)| ^ j * (N : ℝ) ^ j := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)), mul_pow]
  have hnum : (1 + |t - s|) ^ j ≤ (1 + T) ^ j :=
    pow_le_pow_left₀ (by positivity) (by linarith) j
  rw [hden] at h1
  have hdenpos : (0 : ℝ) < |(k : ℝ)| ^ j * (N : ℝ) ^ j :=
    mul_pos (pow_pos (abs_pos.mpr hkre) j) (pow_pos hNpos' j)
  calc ‖hhat (t - s) ((k : ℝ) * N)‖
      ≤ C * (1 + |t - s|) ^ j / (|(k : ℝ)| ^ j * (N : ℝ) ^ j) := h1
    _ ≤ C * (1 + T) ^ j / (|(k : ℝ)| ^ j * (N : ℝ) ^ j) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hdenpos)
        exact mul_le_mul_of_nonneg_left hnum hC

/-- Triangle-inequality bound for a triple sum. -/
private theorem norm_triple_sum_le (W : Finset ℝ) (F : ℝ → ℝ → ℝ → ℂ) (B : ℝ)
    (h : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ‖F a b c‖ ≤ B) :
    ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, F a b c‖ ≤ (W.card : ℝ) ^ 3 * B := by
  calc ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, F a b c‖
      ≤ ∑ a ∈ W, ‖∑ b ∈ W, ∑ c ∈ W, F a b c‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ W, ∑ b ∈ W, ‖∑ c ∈ W, F a b c‖ := by
        apply sum_le_sum; intro a ha
        exact norm_sum_le _ _
    _ ≤ ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ‖F a b c‖ := by
        apply sum_le_sum; intro a ha
        apply sum_le_sum; intro b hb
        exact norm_sum_le _ _
    _ ≤ ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, B := by
        apply sum_le_sum; intro a ha
        apply sum_le_sum; intro b hb
        apply sum_le_sum; intro c hc
        exact h a ha b hb c hc
    _ = (W.card : ℝ) ^ 3 * B := by
        simp [sum_const, nsmul_eq_mul]
        ring

theorem Iterm_bound_large (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T)
    (j : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ t ξ : ℝ, ξ ≠ 0 → ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j)
    (hAz : ∀ t ξ : ℝ, ‖Submission.GM.hhat t ξ‖ ≤ Work.GM.Trace.Azero)
    (m : ℤ × ℤ × ℤ) (hm : Submission.GM.nzCount m = 1) :
    ‖Submission.GM.Iterm N W m‖ ≤ (N : ℝ) ^ 3 * ((W.card : ℝ) ^ 3 * Work.GM.Trace.Azero ^ 2 * C *
      (1 + T) ^ j / (|(Work.GM.Trace.rho m : ℝ)| ^ j * (N : ℝ) ^ j)) := by
  classical
  have hT1 : (0 : ℝ) ≤ 1 + T := by linarith
  have hAz0 : (0 : ℝ) ≤ Work.GM.Trace.Azero := Work.GM.Trace.Azero_nonneg
  set B : ℝ := C * (1 + T) ^ j / (|(Work.GM.Trace.rho m : ℝ)| ^ j * (N : ℝ) ^ j) with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact div_nonneg (mul_nonneg hC (pow_nonneg hT1 j))
      (mul_nonneg (pow_nonneg (abs_nonneg _) j) (by positivity))
  have key : ∀ t1 ∈ W, ∀ t2 ∈ W, ∀ t3 ∈ W,
      ‖Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N) *
        Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N) *
        Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)‖ ≤ Work.GM.Trace.Azero ^ 2 * B := by
    intro t1 ht1 t2 ht2 t3 ht3
    have h1 := hW t1 ht1
    have h2 := hW t2 ht2
    have h3 := hW t3 ht3
    rcases nzCount_one_cases m hm with
      ⟨hm1, hm2, hm3⟩ | ⟨hm1, hm2, hm3⟩ | ⟨hm1, hm2, hm3⟩
    · have hr : Work.GM.Trace.rho m = m.1 := Work.GM.Trace.rho_of_ne_zero hm1
      have hb := hhat_mul_bound N hN T hT j C hC hdec h1 h2 hm1
      have hb' : ‖Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N)‖ ≤ B := by
        rw [hB, hr]; exact hb
      have hb2 : ‖Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N)‖ ≤ Work.GM.Trace.Azero :=
        hAz _ _
      have hb3 : ‖Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)‖ ≤ Work.GM.Trace.Azero :=
        hAz _ _
      calc ‖Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N) *
              Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N) *
              Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)‖
          = ‖Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N)‖ *
              ‖Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N)‖ *
              ‖Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)‖ := by rw [norm_mul, norm_mul]
        _ ≤ B * Work.GM.Trace.Azero * Work.GM.Trace.Azero :=
            mul_le_mul (mul_le_mul hb' hb2 (norm_nonneg _) hBnn) hb3 (norm_nonneg _)
              (mul_nonneg hBnn hAz0)
        _ = Work.GM.Trace.Azero ^ 2 * B := by ring
    · have hr : Work.GM.Trace.rho m = m.2.1 := Work.GM.Trace.rho_of_fst_eq_zero hm1 hm2
      have hb := hhat_mul_bound N hN T hT j C hC hdec h2 h3 hm2
      have hb' : ‖Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N)‖ ≤ B := by
        rw [hB, hr]; exact hb
      have hb1 : ‖Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N)‖ ≤ Work.GM.Trace.Azero :=
        hAz _ _
      have hb3 : ‖Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)‖ ≤ Work.GM.Trace.Azero :=
        hAz _ _
      calc ‖Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N) *
              Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N) *
              Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)‖
          = ‖Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N)‖ *
              ‖Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N)‖ *
              ‖Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)‖ := by rw [norm_mul, norm_mul]
        _ ≤ Work.GM.Trace.Azero * B * Work.GM.Trace.Azero :=
            mul_le_mul (mul_le_mul hb1 hb' (norm_nonneg _) hAz0) hb3 (norm_nonneg _)
              (mul_nonneg hAz0 hBnn)
        _ = Work.GM.Trace.Azero ^ 2 * B := by ring
    · have hr : Work.GM.Trace.rho m = m.2.2 := Work.GM.Trace.rho_of_fst_snd_eq_zero hm1 hm2
      have hb := hhat_mul_bound N hN T hT j C hC hdec h3 h1 hm3
      have hb' : ‖Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)‖ ≤ B := by
        rw [hB, hr]; exact hb
      have hb1 : ‖Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N)‖ ≤ Work.GM.Trace.Azero :=
        hAz _ _
      have hb2 : ‖Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N)‖ ≤ Work.GM.Trace.Azero :=
        hAz _ _
      calc ‖Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N) *
              Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N) *
              Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)‖
          = ‖Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N)‖ *
              ‖Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N)‖ *
              ‖Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)‖ := by rw [norm_mul, norm_mul]
        _ ≤ Work.GM.Trace.Azero * Work.GM.Trace.Azero * B :=
            mul_le_mul (mul_le_mul hb1 hb2 (norm_nonneg _) hAz0) hb' (norm_nonneg _)
              (mul_nonneg hAz0 hAz0)
        _ = Work.GM.Trace.Azero ^ 2 * B := by ring
  have hsum : ‖∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
      Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N) *
        Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N) *
        Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)‖
      ≤ (W.card : ℝ) ^ 3 * (Work.GM.Trace.Azero ^ 2 * B) :=
    norm_triple_sum_le W _ _ key
  have hI : Submission.GM.Iterm N W m = (N : ℂ) ^ 3 * (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
      Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N) *
        Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N) *
        Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)) := rfl
  rw [hI, norm_mul, norm_pow, Complex.norm_natCast]
  calc (N : ℝ) ^ 3 * ‖∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        Submission.GM.hhat (t1 - t2) ((m.1 : ℝ) * N) *
          Submission.GM.hhat (t2 - t3) ((m.2.1 : ℝ) * N) *
          Submission.GM.hhat (t3 - t1) ((m.2.2 : ℝ) * N)‖
      ≤ (N : ℝ) ^ 3 * ((W.card : ℝ) ^ 3 * (Work.GM.Trace.Azero ^ 2 * B)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (N : ℝ) ^ 3 * ((W.card : ℝ) ^ 3 * Work.GM.Trace.Azero ^ 2 * C *
        (1 + T) ^ j / (|(Work.GM.Trace.rho m : ℝ)| ^ j * (N : ℝ) ^ j)) := by
        rw [hB]; ring_nf

end Work.GM.Trace
