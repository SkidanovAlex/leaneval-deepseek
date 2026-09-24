import Mathlib
import Submission.Work.GM.Trace.Defs
import Submission.Work.GM.Trace.hhat_zero_decay
import Submission.Work.GM.Trace.hhat_norm_le_Azero
import Submission.Commons.Analysis.Metric.one_separated_real_card_le

namespace Work.GM.Trace

open Complex Finset
open scoped BigOperators
open Submission.GM Submission.LargeValues

/-!
# GM Lemma 4.5, the `m = 0` term

The sum `I_0 = N³ Σ_{t₁,t₂,t₃ ∈ W} ĥ_{t₁-t₂}(0) ĥ_{t₂-t₃}(0) ĥ_{t₃-t₁}(0)` is exactly
`N³ |W| Azero³` up to a tiny error, where `Azero = ĥ_0(0) = ∫ w² > 0`.  The diagonal
triples `t₁ = t₂ = t₃` contribute `Azero³` each; every other triple has at least one
difference `tᵢ - tⱼ ≠ 0`, which by separation is `≥ (M N)^ε`, so the corresponding factor
is `≤ C_j (M N)^{-ε j} ≤ C_j N^{-100}` (for `j = ⌈100/ε⌉`), while the other two factors are
`≤ Azero` by `hhat_norm_le_Azero`.
-/

/-- The summand of the `m = 0` term: `ĥ_{a-b}(0) ĥ_{b-c}(0) ĥ_{c-a}(0)`. -/
private noncomputable def Gfun (a b c : ℝ) : ℂ :=
  hhat (a - b) 0 * hhat (b - c) 0 * hhat (c - a) 0

/-- On the diagonal `a = b = c` the summand equals `Azero³`. -/
private theorem Gfun_self {t : ℝ} : Gfun t t t = (Azero : ℂ) ^ 3 := by
  simp only [Gfun, sub_self, hhat_zero_zero]
  ring

/-- The diagonal part of the triple sum: only the triples with `t₁ = t₂ = t₃` contribute. -/
private theorem diag_triple_sum (W : Finset ℝ) (G : ℝ → ℝ → ℝ → ℂ) (A : ℂ)
    (hG : ∀ t ∈ W, G t t t = A) :
    (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, (if t₁ = t₂ ∧ t₂ = t₃ then G t₁ t₂ t₃ else 0))
      = (W.card : ℂ) * A := by
  classical
  have key : ∀ t₁ ∈ W, ∀ t₂ ∈ W,
      (∑ t₃ ∈ W, (if t₁ = t₂ ∧ t₂ = t₃ then G t₁ t₂ t₃ else 0))
        = (if t₁ = t₂ then G t₁ t₂ t₂ else 0) := by
    intro t₁ h1 t₂ h2
    rw [show (∑ t₃ ∈ W, (if t₁ = t₂ ∧ t₂ = t₃ then G t₁ t₂ t₃ else 0))
          = ∑ t₃ ∈ W, (if t₂ = t₃ then (if t₁ = t₂ then G t₁ t₂ t₃ else 0) else 0) from ?_]
    · rw [sum_ite_eq]; simp [h2]
    · apply sum_congr rfl; intro t₃ h3
      by_cases h : t₂ = t₃ <;> by_cases h' : t₁ = t₂ <;> simp [h, h']
  have key2 : ∀ t₁ ∈ W, (∑ t₂ ∈ W, (if t₁ = t₂ then G t₁ t₂ t₂ else 0)) = G t₁ t₁ t₁ := by
    intro t₁ h1
    rw [sum_ite_eq]; simp [h1]
  rw [show (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, (if t₁ = t₂ ∧ t₂ = t₃ then G t₁ t₂ t₃ else 0))
      = (∑ t₁ ∈ W, ∑ t₂ ∈ W, (if t₁ = t₂ then G t₁ t₂ t₂ else 0)) from by
        apply sum_congr rfl; intro t₁ h1
        apply sum_congr rfl; intro t₂ h2
        exact key t₁ h1 t₂ h2]
  rw [show (∑ t₁ ∈ W, ∑ t₂ ∈ W, (if t₁ = t₂ then G t₁ t₂ t₂ else 0))
      = (∑ t₁ ∈ W, G t₁ t₁ t₁) from by
        apply sum_congr rfl; intro t₁ h1
        exact key2 t₁ h1]
  rw [sum_congr rfl (fun t h => hG t h)]
  simp [sum_const, nsmul_eq_mul]

/-- Triangle-inequality bound for a triple sum. -/
private theorem norm_triple_sum_le (W : Finset ℝ) (F : ℝ → ℝ → ℝ → ℂ) (B : ℝ)
    (h : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ‖F a b c‖ ≤ B) :
    ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, F a b c‖ ≤ (W.card : ℝ)^3 * B := by
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
    _ = (W.card : ℝ)^3 * B := by
        simp [sum_const, nsmul_eq_mul]
        ring

/-- If `|d| ≥ (M N)^ε ≥ 1` and `N` is large then `‖ĥ_d(0)‖ ≤ C / N^{100}`. -/
private theorem hhat_decay_le (N : ℕ) (hN1 : 1 ≤ N) {ε : ℝ} {j : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hdec : ∀ t : ℝ, 1 ≤ |t| → ‖hhat t 0‖ ≤ C / |t| ^ j)
    (hd1 : 1 ≤ (M N) ^ ε) (hbig : (N : ℝ) ^ 100 ≤ ((M N) ^ ε) ^ j)
    {d : ℝ} (hd : (M N) ^ ε ≤ |d|) :
    ‖hhat d 0‖ ≤ C / (N : ℝ) ^ 100 := by
  have hdj : ((M N) ^ ε) ^ j ≤ |d| ^ j :=
    pow_le_pow_left₀ (le_of_lt (lt_of_lt_of_le one_pos hd1)) hd j
  have hbig' : (N : ℝ) ^ 100 ≤ |d| ^ j := le_trans hbig hdj
  have hN100 : (0 : ℝ) < (N : ℝ) ^ 100 :=
    pow_pos (by exact_mod_cast (show 0 < N by omega)) 100
  have hjd : 1 / |d| ^ j ≤ 1 / (N : ℝ) ^ 100 :=
    one_div_le_one_div_of_le hN100 hbig'
  calc ‖hhat d 0‖ ≤ C / |d| ^ j := hdec d (le_trans hd1 hd)
    _ = C * (1 / |d| ^ j) := by ring
    _ ≤ C * (1 / (N : ℝ) ^ 100) := mul_le_mul_of_nonneg_left hjd hC
    _ = C / (N : ℝ) ^ 100 := by ring

/-- Final arithmetic: `N³ · |W|³ · P / N^{100} ≤ N^{-50}` for `N` large. -/
private theorem final_arith {N : ℕ} {c P : ℝ} (hN : 1 ≤ N) (hc : 0 ≤ c)
    (hc2 : c ≤ 2 * (N : ℝ) ^ 2) (hP : 0 ≤ P) (hP2 : 8 * P ≤ (N : ℝ)) :
    (N : ℝ) ^ 3 * c ^ 3 * (P / (N : ℝ) ^ 100) ≤ tinyN N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [tinyN]
  have hc2' : c ^ 3 ≤ (2 * (N : ℝ) ^ 2) ^ 3 := pow_le_pow_left₀ hc hc2 3
  have h1 : (N : ℝ) ^ 3 * c ^ 3 * (P / (N : ℝ) ^ 100)
      ≤ (N : ℝ) ^ 3 * (2 * (N : ℝ) ^ 2) ^ 3 * (P / (N : ℝ) ^ 100) := by
    apply mul_le_mul_of_nonneg_right _ (div_nonneg hP (by positivity))
    exact mul_le_mul_of_nonneg_left hc2' (by positivity)
  refine le_trans h1 ?_
  have h2 : (N : ℝ) ^ 3 * (2 * (N : ℝ) ^ 2) ^ 3 * (P / (N : ℝ) ^ 100)
      = 8 * P / (N : ℝ) ^ 91 := by
    field_simp
    ring
  rw [h2]
  have h3 : 8 * P / (N : ℝ) ^ 91 ≤ (N : ℝ) / (N : ℝ) ^ 91 :=
    div_le_div_of_nonneg_right hP2 (by positivity)
  refine le_trans h3 ?_
  have h4 : (N : ℝ) / (N : ℝ) ^ 91 = 1 / (N : ℝ) ^ 90 := by
    field_simp
  rw [h4]
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ hN1R (by norm_num)

theorem Iterm_zero_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      ‖Submission.GM.Iterm N W 0 -
          ((N : ℝ) ^ 3 * (W.card : ℝ) * Work.GM.Trace.Azero ^ 3 : ℝ)‖
        ≤ Work.GM.Trace.tinyN N := by
  classical
  set j : ℕ := Nat.ceil (100 / ε) with hjdef
  have hjle : 100 / ε ≤ (j : ℝ) := by
    rw [hjdef]; exact Nat.le_ceil _
  have hj100 : 100 ≤ ε * (j : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hjle (le_of_lt hε)
    have hc : ε * (100 / ε) = 100 := by field_simp
    linarith
  obtain ⟨C, hC0, hCdec⟩ := hhat_zero_decay j
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max 1 (8 * (Azero ^ 2 * C)))
  refine ⟨N₀, ?_⟩
  intro N hN W hW hsep
  have hNreal : (1 : ℝ) ≤ (N : ℝ) :=
    le_trans (le_max_left _ _) (le_trans hN₀ (by exact_mod_cast hN))
  have hP2 : 8 * (Azero ^ 2 * C) ≤ (N : ℝ) :=
    le_trans (le_max_right _ _) (le_trans hN₀ (by exact_mod_cast hN))
  have hN1 : 1 ≤ N := by exact_mod_cast hNreal
  have hMN1 : 1 ≤ M N := M_ge_one hN1
  have hd1 : 1 ≤ (M N) ^ ε := Real.one_le_rpow hMN1 hε.le
  have hMNN : (N : ℝ) ≤ M N := by
    rw [M]
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (6 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNreal (by norm_num)
  have hMN2 : M N ≤ (N : ℝ) ^ 2 := by
    rw [M, ← Real.rpow_natCast (N : ℝ) 2]
    exact Real.rpow_le_rpow_of_exponent_le hNreal (by norm_num)
  have hbig : (N : ℝ) ^ 100 ≤ ((M N) ^ ε) ^ j := by
    have step1 : (N : ℝ) ^ 100 ≤ (N : ℝ) ^ (ε * (j : ℝ)) := by
      rw [← Real.rpow_natCast (N : ℝ) 100]
      exact Real.rpow_le_rpow_of_exponent_le hNreal hj100
    have step2 : (N : ℝ) ^ (ε * (j : ℝ)) ≤ (M N) ^ (ε * (j : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hMNN (by positivity)
    have step3 : (M N) ^ (ε * (j : ℝ)) = ((M N) ^ ε) ^ j := by
      rw [Real.rpow_mul (le_of_lt (M_pos hN1)), Real.rpow_natCast]
    exact le_trans step1 (le_trans step2 (le_of_eq step3))
  have hdec : ∀ d : ℝ, (M N) ^ ε ≤ |d| → ‖hhat d 0‖ ≤ C / (N : ℝ) ^ 100 :=
    fun d hd => hhat_decay_le N hN1 hC0 hCdec hd1 hbig hd
  have hGle : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W,
      ‖(if a = b ∧ b = c then (0 : ℂ) else Gfun a b c)‖
        ≤ Azero ^ 2 * (C / (N : ℝ) ^ 100) := by
    have hBnn : (0 : ℝ) ≤ Azero ^ 2 * (C / (N : ℝ) ^ 100) :=
      mul_nonneg (pow_nonneg Azero_nonneg 2) (div_nonneg hC0 (by positivity))
    have hAn : (0 : ℝ) ≤ Azero := Azero_nonneg
    have hCdiv : (0 : ℝ) ≤ C / (N : ℝ) ^ 100 := div_nonneg hC0 (by positivity)
    intro a ha b hb c hc
    by_cases hne : a = b ∧ b = c
    · rw [if_pos hne]; simpa using hBnn
    · rw [if_neg hne]
      simp only [Gfun]
      rw [norm_mul, norm_mul]
      by_cases hab : a = b
      · have hbc : b ≠ c := fun h => hne ⟨hab, h⟩
        have h1 := hdec (b - c) (hsep b hb c hc hbc)
        have h2 : ‖hhat (a - b) 0‖ ≤ Azero := hhat_norm_le_Azero (a - b) 0
        have h3 : ‖hhat (c - a) 0‖ ≤ Azero := hhat_norm_le_Azero (c - a) 0
        calc ‖hhat (a - b) 0‖ * ‖hhat (b - c) 0‖ * ‖hhat (c - a) 0‖
            ≤ Azero * (C / (N : ℝ) ^ 100) * Azero := by
              apply mul_le_mul _ h3 (norm_nonneg _) (mul_nonneg hAn hCdiv)
              exact mul_le_mul h2 h1 (norm_nonneg _) hAn
          _ = Azero ^ 2 * (C / (N : ℝ) ^ 100) := by ring
      · have h1 := hdec (a - b) (hsep a ha b hb hab)
        have h2 : ‖hhat (b - c) 0‖ ≤ Azero := hhat_norm_le_Azero (b - c) 0
        have h3 : ‖hhat (c - a) 0‖ ≤ Azero := hhat_norm_le_Azero (c - a) 0
        calc ‖hhat (a - b) 0‖ * ‖hhat (b - c) 0‖ * ‖hhat (c - a) 0‖
            ≤ (C / (N : ℝ) ^ 100) * Azero * Azero := by
              apply mul_le_mul _ h3 (norm_nonneg _) (mul_nonneg hCdiv hAn)
              exact mul_le_mul h1 h2 (norm_nonneg _) hCdiv
          _ = Azero ^ 2 * (C / (N : ℝ) ^ 100) := by ring
  have hsumle : ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        (if a = b ∧ b = c then (0 : ℂ) else Gfun a b c)‖
      ≤ (W.card : ℝ) ^ 3 * (Azero ^ 2 * (C / (N : ℝ) ^ 100)) :=
    norm_triple_sum_le W _ _ hGle
  have hcard1 : (W.card : ℝ) ≤ M N + 1 :=
    Commons.Analysis.Metric.one_separated_real_card_le W (M N) (le_trans zero_le_one hMN1)
      (fun x hx => ⟨(hW x hx).1, (hW x hx).2⟩)
      (fun x hx y hy hxy => le_trans hd1 (hsep x hx y hy hxy))
  have hcard2 : (W.card : ℝ) ≤ 2 * (N : ℝ) ^ 2 := by
    calc (W.card : ℝ) ≤ M N + 1 := hcard1
      _ ≤ 2 * M N := by linarith
      _ ≤ 2 * (N : ℝ) ^ 2 := by linarith
  have hS : Submission.GM.Iterm N W 0
      = (N : ℂ) ^ 3 * (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, Gfun a b c) := by
    simp [Submission.GM.Iterm, Gfun]
  have hdiag := diag_triple_sum W Gfun ((Azero : ℂ) ^ 3) (fun t _ => Gfun_self)
  have hsplit : (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, Gfun a b c) - ((W.card : ℂ) * (Azero : ℂ) ^ 3)
      = ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (if a = b ∧ b = c then (0 : ℂ) else Gfun a b c) := by
    rw [← hdiag]
    simp only [← Finset.sum_sub_distrib]
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro b hb
    apply sum_congr rfl; intro c hc
    by_cases h : a = b ∧ b = c <;> simp [h]
  have htarget : (((N : ℝ) ^ 3 * (W.card : ℝ) * Azero ^ 3 : ℝ) : ℂ)
      = (N : ℂ) ^ 3 * ((W.card : ℂ) * (Azero : ℂ) ^ 3) := by
    push_cast
    ring
  rw [htarget, hS]
  rw [show (N : ℂ) ^ 3 * (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, Gfun a b c)
        - (N : ℂ) ^ 3 * ((W.card : ℂ) * (Azero : ℂ) ^ 3)
      = (N : ℂ) ^ 3 * ((∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, Gfun a b c)
        - ((W.card : ℂ) * (Azero : ℂ) ^ 3)) from by ring]
  rw [norm_mul, hsplit]
  have hnormN : ‖(N : ℂ) ^ 3‖ = (N : ℝ) ^ 3 := by
    rw [norm_pow]
    simp
  rw [hnormN]
  calc (N : ℝ) ^ 3 * ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
          (if a = b ∧ b = c then (0 : ℂ) else Gfun a b c)‖
      ≤ (N : ℝ) ^ 3 * ((W.card : ℝ) ^ 3 * (Azero ^ 2 * (C / (N : ℝ) ^ 100))) :=
        mul_le_mul_of_nonneg_left hsumle (by positivity)
    _ = (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * ((Azero ^ 2 * C) / (N : ℝ) ^ 100) := by
        rw [← mul_div_assoc]; ring
    _ ≤ tinyN N :=
        final_arith hN1 (Nat.cast_nonneg W.card) hcard2
          (mul_nonneg (pow_nonneg Azero_nonneg 2) hC0) hP2

end Work.GM.Trace
