import Mathlib
import Submission.Work.GM.Energy.EnergyCore.fourth_moment_Rfun
import Submission.Work.GM.Energy.Basic.energy_le_three_mul_cube
import Submission.Work.GM.Energy.Basic.card_sq_le_energy
import Submission.Work.GM.Trace.sep_card_le

namespace Work.GM.Energy.EnergyCore2

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-- **Real-arithmetic core of the `K`-free fourth moment bound.**  Specialising the window
parameter to the single value `K = T^η` costs `(K+1)^2 ≤ 4 T^{2η}` in the main term, while the
locality error `((MM+1)/K^m)^2 · E · Wc^2` is absorbed into `16 T^{2η} MM^2 E` as soon as
`m η ≥ 12`: indeed a `1`-separated `W ⊆ [0,T]` has `Wc ≤ T+1`, so
`(MM+1)^2 Wc^2 ≤ 16 MM^2 T^2 ≤ 16 MM^2 T^{2η(m+1)}`, and `T^{2η(m+1)} = T^{2η}·(T^η)^{2m}`. -/
lemma arith_Kfree (C₀ Cloc T η ε : ℝ) (m : ℕ) (E MM Wc : ℝ)
    (hC₀ : 0 < C₀) (hCloc : 0 < Cloc) (hT : 1 ≤ T) (hη : 0 < η)
    (hmη : 12 ≤ (m : ℝ) * η) (hE : 0 ≤ E) (hWc : 0 ≤ Wc) (hMM : 1 ≤ MM)
    (hWcT : Wc ≤ T + 1) :
    C₀ * (Cloc + 1) ^ 2 * T ^ ε * (T ^ η + 1) ^ 2
        * (Wc ^ 4 * MM + MM ^ 2 * E + E ^ ((3 : ℝ) / 4) * Wc * T ^ ((1 : ℝ) / 2) * MM)
      + C₀ * (Cloc + 1) ^ 2 * T ^ ε * ((MM + 1) / (T ^ η) ^ (m : ℝ)) ^ 2 * E * Wc ^ 2
    ≤ (20 * C₀ + 1) * (Cloc + 1) ^ 2 * T ^ (ε + 2 * η)
        * (Wc ^ 4 * MM + MM ^ 2 * E + E ^ ((3 : ℝ) / 4) * Wc * T ^ ((1 : ℝ) / 2) * MM) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := le_of_lt hTpos
  -- the window cost `(K+1)^2 ≤ 4 T^{2η}` for `K = T^η`
  have hsq1 : (T ^ η + 1) ^ 2 ≤ 4 * T ^ (2 * η) := by
    have h2 : T ^ η + 1 ≤ 2 * T ^ η := by
      have h1 : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
      linarith
    have h3 : (T ^ η + 1) ^ 2 ≤ (2 * T ^ η) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
    have h5 : (T ^ η) ^ 2 = T ^ (2 * η) := by
      rw [← Real.rpow_two (T ^ η), ← Real.rpow_mul hT0 η 2]
      congr 1
      ring
    have h4 : (2 * T ^ η) ^ 2 = 4 * T ^ (2 * η) := by
      rw [mul_pow, h5]
      norm_num
    linarith
  -- the locality error is absorbed: `((MM+1)/(T^η)^m)^2 Wc^2 ≤ 16 T^{2η} MM^2`
  have herr : ((MM + 1) / (T ^ η) ^ (m : ℝ)) ^ 2 * Wc ^ 2 ≤ 16 * T ^ (2 * η) * MM ^ 2 := by
    have hQ2pos : 0 < ((T ^ η) ^ (m : ℝ)) ^ 2 := by positivity
    have hQ2 : ((T ^ η) ^ (m : ℝ)) ^ 2 = T ^ (2 * η * (m : ℝ)) := by
      rw [← Real.rpow_two ((T ^ η) ^ (m : ℝ)),
        ← Real.rpow_mul (Real.rpow_nonneg hT0 η) (m : ℝ) 2,
        ← Real.rpow_mul hT0 η ((m : ℝ) * 2)]
      congr 1
      ring
    have hTQ : T ^ (2 * η) * ((T ^ η) ^ (m : ℝ)) ^ 2 = T ^ (2 * η * ((m : ℝ) + 1)) := by
      rw [hQ2, ← Real.rpow_add hTpos (2 * η) (2 * η * (m : ℝ))]
      congr 1
      ring
    have hExp : (2 : ℝ) ≤ 2 * η * ((m : ℝ) + 1) := by nlinarith [hmη, hη]
    have hMMsq : (MM + 1) ^ 2 ≤ 4 * MM ^ 2 := by
      have h2 : MM + 1 ≤ 2 * MM := by linarith
      have h3 : (MM + 1) ^ 2 ≤ (2 * MM) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
      have h4 : (2 * MM) ^ 2 = 4 * MM ^ 2 := by ring
      linarith
    have hWcsq : Wc ^ 2 ≤ 4 * T ^ 2 := by
      have h2 : Wc ≤ 2 * T := by linarith
      have h3 : Wc ^ 2 ≤ (2 * T) ^ 2 := pow_le_pow_left₀ hWc h2 2
      have h4 : (2 * T) ^ 2 = 4 * T ^ 2 := by ring
      linarith
    have hT2le : T ^ 2 ≤ T ^ (2 * η * ((m : ℝ) + 1)) := by
      rw [← Real.rpow_two T]
      exact Real.rpow_le_rpow_of_exponent_le hT hExp
    have hMA : (MM + 1) ^ 2 * Wc ^ 2 ≤ 16 * MM ^ 2 * T ^ (2 * η * ((m : ℝ) + 1)) := by
      have h3 : (MM + 1) ^ 2 * Wc ^ 2 ≤ (4 * MM ^ 2) * (4 * T ^ 2) :=
        mul_le_mul hMMsq hWcsq (by positivity) (by positivity)
      have h4 : (4 * MM ^ 2) * (4 * T ^ 2) = 16 * MM ^ 2 * T ^ 2 := by ring
      have h5 : 16 * MM ^ 2 * T ^ 2 ≤ 16 * MM ^ 2 * T ^ (2 * η * ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hT2le (by positivity)
      linarith
    have hkey : (MM + 1) ^ 2 * Wc ^ 2
        ≤ (16 * T ^ (2 * η) * MM ^ 2) * ((T ^ η) ^ (m : ℝ)) ^ 2 := by
      calc (MM + 1) ^ 2 * Wc ^ 2 ≤ 16 * MM ^ 2 * T ^ (2 * η * ((m : ℝ) + 1)) := hMA
        _ = (16 * T ^ (2 * η) * MM ^ 2) * ((T ^ η) ^ (m : ℝ)) ^ 2 := by rw [← hTQ]; ring
    have hrew : ((MM + 1) / (T ^ η) ^ (m : ℝ)) ^ 2 * Wc ^ 2
        = (MM + 1) ^ 2 * Wc ^ 2 / ((T ^ η) ^ (m : ℝ)) ^ 2 := by
      rw [div_pow]; ring
    rw [hrew, div_le_iff₀ hQ2pos]
    exact hkey
  -- combine, on atoms
  set A : ℝ := C₀ * (Cloc + 1) ^ 2 * T ^ ε with hAdef
  set D : ℝ := C₀ * (Cloc + 1) ^ 2 * T ^ (ε + 2 * η) with hDdef
  set E' : ℝ := (20 * C₀ + 1) * (Cloc + 1) ^ 2 * T ^ (ε + 2 * η) with hEdef
  set B : ℝ := Wc ^ 4 * MM + MM ^ 2 * E + E ^ ((3 : ℝ) / 4) * Wc * T ^ ((1 : ℝ) / 2) * MM
    with hBdef
  set P : ℝ := (T ^ η + 1) ^ 2 with hPdef
  set Q : ℝ := ((MM + 1) / (T ^ η) ^ (m : ℝ)) ^ 2 with hQdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hPle : P ≤ 4 * T ^ (2 * η) := by rw [hPdef]; exact hsq1
  have hQle : Q * Wc ^ 2 ≤ 16 * T ^ (2 * η) * MM ^ 2 := by rw [hQdef]; exact herr
  have hmmE : MM ^ 2 * E ≤ B := by
    rw [hBdef]
    have h1 : 0 ≤ Wc ^ 4 * MM := by positivity
    have h2 : 0 ≤ E ^ ((3 : ℝ) / 4) * Wc * T ^ ((1 : ℝ) / 2) * MM := by positivity
    linarith
  have hAD : A * T ^ (2 * η) = D := by
    rw [hAdef, hDdef, Real.rpow_add hTpos ε (2 * η)]
    ring
  have hmain : A * P * B ≤ 4 * D * B := by
    have h2 : A * P ≤ A * (4 * T ^ (2 * η)) := mul_le_mul_of_nonneg_left hPle hA0
    have h3 : A * P * B ≤ A * (4 * T ^ (2 * η)) * B := mul_le_mul_of_nonneg_right h2 hB0
    have h4 : A * (4 * T ^ (2 * η)) * B = 4 * D * B := by
      rw [show A * (4 * T ^ (2 * η)) * B = 4 * (A * T ^ (2 * η)) * B by ring, hAD]
    linarith
  have herr' : A * Q * E * Wc ^ 2 ≤ 16 * D * B := by
    have h2 : A * (Q * Wc ^ 2) * E ≤ A * (16 * T ^ (2 * η) * MM ^ 2) * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQle hA0) hE
    have h3 : A * (16 * T ^ (2 * η) * MM ^ 2) * E = 16 * D * (MM ^ 2 * E) := by
      rw [show A * (16 * T ^ (2 * η) * MM ^ 2) * E
            = 16 * (A * T ^ (2 * η)) * (MM ^ 2 * E) by ring, hAD]
    have h4 : 16 * D * (MM ^ 2 * E) ≤ 16 * D * B := mul_le_mul_of_nonneg_left hmmE (by positivity)
    have h5 : A * Q * E * Wc ^ 2 = A * (Q * Wc ^ 2) * E := by ring
    rw [h5]
    linarith
  have hsum : A * P * B + A * Q * E * Wc ^ 2 ≤ 20 * D * B := by linarith
  have hDle : 20 * D ≤ E' := by
    rw [hDdef, hEdef]
    have h1 : 20 * C₀ ≤ 20 * C₀ + 1 := by linarith
    have h2 : 0 ≤ (Cloc + 1) ^ 2 * T ^ (ε + 2 * η) := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    simpa only [mul_assoc] using h3
  have h9 : 20 * D * B ≤ E' * B := mul_le_mul_of_nonneg_right hDle hB0
  linarith

/-- **GM §11 (11.6), `K`-free form with a small defect `T^{2η}`.** (Needed by the `GM §11` assembly
`GM/Energy/EnergyCore2/assembly_eta`, whose `hL9` slot is `EnergyCore.gcd_large`: that result consumes
the *fourth-moment bound at every scale* as a hypothesis, and the `K`-exposed form
`EnergyCore.fourth_moment_Rfun` cannot be converted into a `K`-free one with a uniform constant --
that is exactly the statement `GM/Energy/EnergyCore/gcd_large_K` which its prover REFUTED.)

Route: take the `K`-exposed bound `EnergyCore.fourth_moment_Rfun hHB m hm ε hε` (constant `C₀`) with
the *single* window `K = T^η` (legal: `T ≥ 1`, `η > 0`).  The window cost is
`(K+1)^2 ≤ 4 K^2 = 4 T^{2η}` because `K ≥ 1`, which gives the first term.  For the error term use
`E(W) ≤ |W|^3` and `E(W) ≥ |W|^2` (both proven, `Basic.energy_le_three_mul_cube`,
`Basic.card_sq_le_energy`, for `1`-separated `W`) and `|W| ≤ T+1` to get
`((M+1)/K^m)^2 E(W) |W|^2 ≤ (M+1)^2 |W|^5 T^{-2ηm} ≤ 4 M^2 |W|^2 T^{2η(m+1)}` up to an absolute
constant, which is at most `4 T^{2η}` times the main term `M^2 E(W)` as soon as `m·η ≥ 12`
(more than enough: `2η(m+1) ≥ 24 ≥ 3 + log_T 8` for `T ≥ 2`).  The range `T ≤ 2` is handled by the
trivial bound `‖R v‖ ≤ |W|` and `|W| ≤ T+1 ≤ 3`.  It is also fine to first prove the version with the
extra error `+ C(Cloc+1)^2 T^{-10} E(W)|W|^2` and then absorb it in the same way. -/
theorem fourth_moment_Kfree (hHB : Submission.GM.HBStatement) (m : ℕ) (hm : 2 ≤ m)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (hmη : 12 ≤ (m : ℝ) * η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Cloc : ℝ), 0 < Cloc →
      (∀ (N' : ℕ), 1 ≤ N' → ∀ (a : ℕ → ℂ), ∀ (K : ℝ), 1 ≤ K → ∀ t : ℝ,
        ‖∑ n ∈ Finset.Icc N' (2 * N'), a n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ≤
          Cloc * (∫ u in t - K..t + K,
                    ‖∑ n ∈ Finset.Icc N' (2 * N'), a n * (n : ℂ) ^ (Complex.I * (u : ℂ))‖)
            + Cloc / K ^ (m : ℝ) * (∑ n ∈ Finset.Icc N' (2 * N'), ‖a n‖)) →
      ∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
        (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
        (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
          ≤ C * (Cloc + 1) ^ 2 * T ^ (ε + 2 * η) *
              ((W.card : ℝ) ^ 4 * (M : ℝ)
                + (M : ℝ) ^ 2 * (Submission.GM.energy W : ℝ)
                + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
                    * T ^ ((1 : ℝ) / 2) * (M : ℝ)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := EnergyCore.fourth_moment_Rfun hHB m hm ε hε
  refine ⟨20 * C₀ + 1, by positivity, ?_⟩
  intro Cloc hCloc hloc M hM T hT W hWsub hsep
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hK1 : (1 : ℝ) ≤ T ^ η := Real.one_le_rpow hT hη.le
  have hbound := hC₀ Cloc hCloc hloc M hM T hT W hWsub hsep (T ^ η) hK1
  have hWcT : (W.card : ℝ) ≤ T + 1 :=
    Work.GM.Trace.sep_card_le W T 1 (le_of_lt hTpos) le_rfl hWsub hsep
  have hE0 : (0 : ℝ) ≤ (Submission.GM.energy W : ℝ) := by positivity
  have hWc0 : (0 : ℝ) ≤ (W.card : ℝ) := by positivity
  have hMM : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  refine le_trans hbound ?_
  exact arith_Kfree C₀ Cloc T η ε m (Submission.GM.energy W : ℝ) (M : ℝ) (W.card : ℝ)
    hC₀pos hCloc hT hη hmη hE0 hWc0 hMM hWcT

end Work.GM.Energy.EnergyCore2
