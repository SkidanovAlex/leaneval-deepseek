import Mathlib
import Submission.Work.GM.Trace.Defs

namespace Work.GM.Trace

open scoped BigOperators

/-- `∑_{n ∈ ℤ} (1 + |n|)⁻²` converges. -/
theorem summable_inv_one_add_abs_sq : Summable (fun n : ℤ => ((1 + |(n:ℝ)|)^2)⁻¹) := by
  have hf : Summable (fun n : ℤ => ((|(n:ℝ)|)^2)⁻¹) := by
    have h := Real.summable_abs_int_rpow (b := (2:ℝ)) (by norm_num)
    refine h.congr (fun m => ?_)
    rw [Real.rpow_neg (abs_nonneg _)]
    congr 1
    exact Real.rpow_natCast _ 2
  have h0 : Summable (fun n : ℤ => if n = 0 then (1:ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by intro m hm; simp at hm; simp [hm])
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hf.add h0)
  by_cases hn : n = 0
  · subst hn; simp
  · have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
      have hz : (1:ℤ) ≤ |n| := Int.one_le_abs hn
      rw [← Int.cast_abs]
      exact_mod_cast hz
    simp only [hn, if_false, add_zero]
    have hpos : (0:ℝ) < |(n:ℝ)|^2 := by positivity
    have hle : |(n:ℝ)|^2 ≤ (1 + |(n:ℝ)|)^2 := by nlinarith [abs_nonneg (n:ℝ)]
    exact inv_anti₀ hpos hle

-- Summability of the families defining `Spart k` (`k = 0,1,2,3`), the first conjunct of
-- `TraceStatement`.  Each nonzero coordinate of `m` contributes a factor `(1+|m_i|)^{-j}` from
-- `hdec` (take `j = 2`); the remaining coordinates are bounded by `hAz`; since `W` is a `Finset`,
-- `(1+|t|)^2` is bounded on the finite set of differences `t_i - t_j`.  Note `nzCount m = 0` means
-- the index set is a singleton and `nzCount m ≥ 4` means it is empty, so `∀ k` is harmless.
theorem summable_Iterm (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ)
    (hdec : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, ξ ≠ 0 →
      ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j)
    (hAz : ∀ t ξ : ℝ, ‖Submission.GM.hhat t ξ‖ ≤ Work.GM.Trace.Azero) :
    ∀ k : ℕ, Summable (fun m : {m : ℤ × ℤ × ℤ // Submission.GM.nzCount m = k} =>
      Submission.GM.Iterm N W m) := by
  intro k
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  obtain ⟨C2, hC2nonneg, hC2⟩ := hdec 2
  -- the finite constant dominating `(1 + |t - s|)^2` for `t, s ∈ W`
  set B : ℝ := 1 + ∑ t ∈ W, ∑ s ∈ W, (1 + |t - s|)^2 with hBdef
  have hBsum : 0 ≤ ∑ t ∈ W, ∑ s ∈ W, (1 + |t - s|)^2 :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun s _ => by positivity
  have hBnonneg : 0 ≤ B := by rw [hBdef]; linarith
  have hBpos : 0 < B := by rw [hBdef]; linarith
  have hBbound : ∀ t ∈ W, ∀ s ∈ W, (1 + |t - s|)^2 ≤ B := by
    intro t ht s hs
    rw [hBdef]
    have h1 : (1 + |t - s|)^2 ≤ ∑ s' ∈ W, (1 + |t - s'|)^2 :=
      Finset.single_le_sum (f := fun s' => (1 + |t - s'|)^2) (fun s' _ => by positivity) hs
    have h2 : (∑ s' ∈ W, (1 + |t - s'|)^2) ≤ ∑ t' ∈ W, ∑ s' ∈ W, (1 + |t' - s'|)^2 :=
      Finset.single_le_sum (f := fun t' => ∑ s' ∈ W, (1 + |t' - s'|)^2)
        (fun t' _ => Finset.sum_nonneg fun s' _ => by positivity) ht
    linarith
  set K : ℝ := 1 + max Azero (4 * C2 * B) with hKdef
  have hAzero_le_K : Azero ≤ K := by
    rw [hKdef]; have h := le_max_left Azero (4 * C2 * B); linarith
  have h4C2B_le_K : 4 * C2 * B ≤ K := by
    rw [hKdef]; have h := le_max_right Azero (4 * C2 * B); linarith
  have hKnonneg : 0 ≤ K := by
    rw [hKdef]
    have h : 0 ≤ max Azero (4 * C2 * B) := le_max_of_le_left Azero_nonneg
    linarith
  -- the per-factor bound
  have hfactor : ∀ (s s' : ℝ), s ∈ W → s' ∈ W → ∀ n : ℤ,
      ‖Submission.GM.hhat (s - s') ((n:ℝ) * (N:ℝ))‖ ≤ K * ((1 + |(n:ℝ)|)^2)⁻¹ := by
    intro s s' hs hs' n
    by_cases hn : n = 0
    · subst hn
      rw [show (((0:ℤ)):ℝ) * (N:ℝ) = 0 by norm_num]
      have h2 : ((1 + |(((0:ℤ)):ℝ)|)^2)⁻¹ = (1:ℝ) := by norm_num
      rw [h2, mul_one]
      exact (hAz (s - s') 0).trans hAzero_le_K
    · have hξne : (n:ℝ) * (N:ℝ) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast hn) hNne
      have hn1 : (1:ℝ) ≤ |(n:ℝ)| := by
        have hz : (1:ℤ) ≤ |n| := Int.one_le_abs hn
        rw [← Int.cast_abs]
        exact_mod_cast hz
      have hBs := hBbound s hs s' hs'
      have hξeq : |(n:ℝ) * (N:ℝ)| = |(n:ℝ)| * (N:ℝ) := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hNpos)]
      have key : C2 * (1 + |s - s'|)^2 * (1 + |(n:ℝ)|)^2
          ≤ K * |(n:ℝ) * (N:ℝ)|^2 := by
        have hpow : (1 + |(n:ℝ)|)^2 ≤ 4 * |(n:ℝ) * (N:ℝ)|^2 := by
          have hA : (1 + |(n:ℝ)|)^2 ≤ 4 * |(n:ℝ)|^2 := by
            nlinarith [sq_nonneg (|(n:ℝ)| - 1), hn1, abs_nonneg (n:ℝ)]
          have hB' : |(n:ℝ)|^2 ≤ |(n:ℝ) * (N:ℝ)|^2 := by
            rw [hξeq]
            nlinarith [sq_nonneg ((N:ℝ) - 1), hN1, sq_nonneg (|(n:ℝ)|), abs_nonneg (n:ℝ)]
          linarith
        calc C2 * (1 + |s - s'|)^2 * (1 + |(n:ℝ)|)^2
            ≤ C2 * B * (1 + |(n:ℝ)|)^2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBs hC2nonneg)
                (by positivity)
          _ ≤ C2 * B * (4 * |(n:ℝ) * (N:ℝ)|^2) :=
              mul_le_mul_of_nonneg_left hpow (mul_nonneg hC2nonneg hBnonneg)
          _ = (4 * C2 * B) * |(n:ℝ) * (N:ℝ)|^2 := by ring
          _ ≤ K * |(n:ℝ) * (N:ℝ)|^2 :=
              mul_le_mul_of_nonneg_right h4C2B_le_K (by positivity)
      have hdiv : C2 * (1 + |s - s'|)^2 / |(n:ℝ) * (N:ℝ)|^2
          ≤ K * ((1 + |(n:ℝ)|)^2)⁻¹ := by
        rw [show K * ((1 + |(n:ℝ)|)^2)⁻¹ = K / (1 + |(n:ℝ)|)^2 by rw [div_eq_mul_inv]]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        exact key
      exact (hC2 (s - s') ((n:ℝ) * (N:ℝ)) hξne).trans hdiv
  -- pointwise domination of `Iterm` on the whole lattice
  have hbound : ∀ m : ℤ × ℤ × ℤ,
      ‖Submission.GM.Iterm N W m‖ ≤
        ((N:ℝ)^3 * (W.card:ℝ)^3 * K^3) *
          (((1 + |(m.1:ℝ)|)^2)⁻¹ * ((1 + |(m.2.1:ℝ)|)^2)⁻¹ *
            ((1 + |(m.2.2:ℝ)|)^2)⁻¹) := by
    intro m
    have hterm : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ∀ t₃ ∈ W,
        ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
          Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
          Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖
        ≤ K^3 * (((1 + |(m.1:ℝ)|)^2)⁻¹ * ((1 + |(m.2.1:ℝ)|)^2)⁻¹ *
            ((1 + |(m.2.2:ℝ)|)^2)⁻¹) := by
      intro t₁ ht₁ t₂ ht₂ t₃ ht₃
      have h1 := hfactor t₁ t₂ ht₁ ht₂ m.1
      have h2 := hfactor t₂ t₃ ht₂ ht₃ m.2.1
      have h3 := hfactor t₃ t₁ ht₃ ht₁ m.2.2
      have ha : (0:ℝ) ≤ ((1 + |(m.1:ℝ)|)^2)⁻¹ := by positivity
      have hb : (0:ℝ) ≤ ((1 + |(m.2.1:ℝ)|)^2)⁻¹ := by positivity
      have hc : (0:ℝ) ≤ ((1 + |(m.2.2:ℝ)|)^2)⁻¹ := by positivity
      calc ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
            Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
            Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖
          = ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N)‖ *
            ‖Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N)‖ *
            ‖Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖ := by rw [norm_mul, norm_mul]
        _ ≤ (K * ((1 + |(m.1:ℝ)|)^2)⁻¹) * (K * ((1 + |(m.2.1:ℝ)|)^2)⁻¹) *
            (K * ((1 + |(m.2.2:ℝ)|)^2)⁻¹) :=
              mul_le_mul
                (mul_le_mul h1 h2 (by positivity) (mul_nonneg hKnonneg ha))
                h3 (by positivity)
                (mul_nonneg (mul_nonneg hKnonneg ha) (mul_nonneg hKnonneg hb))
        _ = K^3 * (((1 + |(m.1:ℝ)|)^2)⁻¹ * ((1 + |(m.2.1:ℝ)|)^2)⁻¹ *
            ((1 + |(m.2.2:ℝ)|)^2)⁻¹) := by ring
    have hnormsum : ‖∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
          Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
          Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖
        ≤ (W.card : ℝ)^3 * (K^3 * (((1 + |(m.1:ℝ)|)^2)⁻¹ * ((1 + |(m.2.1:ℝ)|)^2)⁻¹ *
            ((1 + |(m.2.2:ℝ)|)^2)⁻¹)) := by
      have hstep : (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
            K^3 * (((1 + |(m.1:ℝ)|)^2)⁻¹ * ((1 + |(m.2.1:ℝ)|)^2)⁻¹ *
              ((1 + |(m.2.2:ℝ)|)^2)⁻¹))
          = (W.card : ℝ)^3 * (K^3 * (((1 + |(m.1:ℝ)|)^2)⁻¹ *
              ((1 + |(m.2.1:ℝ)|)^2)⁻¹ * ((1 + |(m.2.2:ℝ)|)^2)⁻¹)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      have h1 : ‖∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
            Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
            Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖
          ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
            K^3 * (((1 + |(m.1:ℝ)|)^2)⁻¹ * ((1 + |(m.2.1:ℝ)|)^2)⁻¹ *
              ((1 + |(m.2.2:ℝ)|)^2)⁻¹) := by
        refine (norm_sum_le W _).trans ?_
        refine Finset.sum_le_sum fun t₁ ht₁ => (norm_sum_le W _).trans ?_
        refine Finset.sum_le_sum fun t₂ ht₂ => (norm_sum_le W _).trans ?_
        exact Finset.sum_le_sum fun t₃ ht₃ => hterm t₁ ht₁ t₂ ht₂ t₃ ht₃
      rw [hstep] at h1
      exact h1
    have hmain : ‖Submission.GM.Iterm N W m‖ ≤
        (N:ℝ)^3 * ((W.card : ℝ)^3 * (K^3 * (((1 + |(m.1:ℝ)|)^2)⁻¹ *
          ((1 + |(m.2.1:ℝ)|)^2)⁻¹ * ((1 + |(m.2.2:ℝ)|)^2)⁻¹))) := by
      rw [Submission.GM.Iterm, norm_mul, norm_pow, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left hnormsum (by positivity)
    calc ‖Submission.GM.Iterm N W m‖
        ≤ (N:ℝ)^3 * ((W.card : ℝ)^3 * (K^3 * (((1 + |(m.1:ℝ)|)^2)⁻¹ *
          ((1 + |(m.2.1:ℝ)|)^2)⁻¹ * ((1 + |(m.2.2:ℝ)|)^2)⁻¹))) := hmain
      _ = ((N:ℝ)^3 * (W.card:ℝ)^3 * K^3) *
          (((1 + |(m.1:ℝ)|)^2)⁻¹ * ((1 + |(m.2.1:ℝ)|)^2)⁻¹ *
            ((1 + |(m.2.2:ℝ)|)^2)⁻¹) := by ring
  -- summability of the dominating family
  have hfnn : ∀ n : ℤ, (0:ℝ) ≤ ((1 + |(n:ℝ)|)^2)⁻¹ := fun n => by positivity
  have hfsum : Summable (fun n : ℤ => ((1 + |(n:ℝ)|)^2)⁻¹) := summable_inv_one_add_abs_sq
  have hprod2 : Summable (fun q : ℤ × ℤ =>
      ((1 + |(q.1:ℝ)|)^2)⁻¹ * ((1 + |(q.2:ℝ)|)^2)⁻¹) :=
    hfsum.mul_of_nonneg hfsum hfnn hfnn
  have hprod3 : Summable (fun m : ℤ × ℤ × ℤ =>
      ((1 + |(m.1:ℝ)|)^2)⁻¹ * ((1 + |(m.2.1:ℝ)|)^2)⁻¹ *
        ((1 + |(m.2.2:ℝ)|)^2)⁻¹) := by
    have h := hfsum.mul_of_nonneg hprod2 hfnn (fun q => by positivity)
    refine h.congr (fun m => ?_)
    ring
  have hBoundSummable : Summable (fun m : ℤ × ℤ × ℤ =>
      ((N:ℝ)^3 * (W.card:ℝ)^3 * K^3) *
        (((1 + |(m.1:ℝ)|)^2)⁻¹ * ((1 + |(m.2.1:ℝ)|)^2)⁻¹ *
          ((1 + |(m.2.2:ℝ)|)^2)⁻¹)) :=
    hprod3.mul_left _
  have hg := hBoundSummable.subtype (fun m => Submission.GM.nzCount m = k)
  exact Summable.of_norm_bounded hg (fun m => by simpa using hbound (m : ℤ × ℤ × ℤ))

end Work.GM.Trace
