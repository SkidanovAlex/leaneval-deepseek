import Mathlib
import Submission.Work.ZeroFreeTables.CertData
import Submission.Commons.NumberTheory.Linnik.lemma5_3
import Submission.Work.ZeroFreeTables.OffAxis.error_absorb
import Submission.Work.ZeroFreeTables.OffAxis.Ksum_eq_re_tsum

/-!
# The principal-character `K`-sum at a shifted point: Heath-Brown (1992), §6

The companion of `Commons.NumberTheory.Linnik.Ksum_principal_le` for a point `s = β + iτ`
off the real axis.  Heath-Brown's Lemma 5.3 (`Commons.NumberTheory.Linnik.lemma5_3`) gives

`∑_n Λ(n) χ₀(n) n^{-s} f(log n / L) = L · ∫₀^{x₀} e^{-(s-1)Lt} f(t) dt + O(ω(q) + (log L)²)`

for `|Re s - 1| ≤ √(log L)/L`, `|Im s| ≤ L`.  At `L = log q` and `s = β + iτ` the main term is
bounded using the decay hypothesis `hdec` applied at `z = (s-1)L`, whose real part is
`-L(1-β) ≥ -1` and whose imaginary part `τL` has modulus `≥ 1`: the integral is at most
`Cdec/|τL|`, so the main term is at most `L·Cdec/(|τ|L) = Cdec/|τ| ≤ Cdec`.  The error term
`C(ω(q) + (log L)²)` is absorbed into the slack `f(0)·ε·log q` for large `q`.
-/

open scoped BigOperators
open MeasureTheory Set Finset

namespace Work.ZeroFreeTables.OffAxis

-- HINT. Model this on `Commons.NumberTheory.Linnik.Ksum_principal_le`
-- (Submission/Commons/NumberTheory/Linnik/Ksum_principal_le.lean): it derives (HB (6.9)) from
-- `Commons.NumberTheory.Linnik.lemma5_3` (Submission/Commons/NumberTheory/Linnik/lemma5_3.lean),
-- whose error term `C * (ω(q) + (log L)^2)` it absorbs into the slack `f 0 * ε * L` using the
-- `private` lemmas `primeFactors_card_le_eps_log` / `exists_error_bound` of that file (copy them).
-- Here the point is shifted: for `s = β + i τ`, `s-1 = -λ/L + iτ` with `L = log q`,
-- Lemma 5.3 gives `Ksum = Re(∑) ≤ L * ‖∫₀^{x₀} exp(-(((s-1)*L) * t)) f t‖ + C(ω(q)+(log L)^2)`,
-- and `hdec` applied at `z = (s-1)*L` (whose real part is `-λ ≥ -1` by the hypothesis
-- `L*(1-β) ≤ 1`, and whose imaginary part is `τ*L` with `|τ*L| ≥ 1`) bounds the first term by
-- `L * Cdec / (|τ|*L) = Cdec/|τ| ≤ Cdec`.
theorem Ksum_principal_shift (x₀ B Cdec : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) (hCdec : 0 ≤ Cdec) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hdec : ∀ z : ℂ, -(1:ℝ) ≤ z.re → 1 ≤ |z.im| →
        ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * ((f t : ℝ):ℂ)‖ ≤ Cdec / |z.im|)
      {ε : ℝ} (hε : 0 < ε),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q → ∀ {β τ : ℝ},
        |β - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) →
        Real.log (q:ℝ) * (1 - β) ≤ 1 →
        |τ| ≤ Real.log (q:ℝ) → 1 ≤ |τ| →
        Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ)) ((β:ℂ) + (τ:ℂ)*Complex.I)
            (1 : DirichletCharacter ℂ q)
          ≤ f 0 * ε * Real.log (q:ℝ) + Cdec := by
  intro f hcont hsupp hf2 hBnd hf0 hdec ε hε
  -- Lemma 5.3 with its error constant
  obtain ⟨C, hCpos, hCbd⟩ :=
    Commons.NumberTheory.Linnik.lemma5_3 x₀ B hx₀ hB hcont hsupp hf2 hBnd
  -- absorb the error term into the slack
  obtain ⟨q₁, hq₁⟩ := error_absorb C (f 0) ε hCpos hf0 hε
  refine ⟨max q₁ 8, ?_⟩
  intro q hqNe hqq β τ hβbd hβlam hτL hτ1
  have hq₁q : q₁ ≤ q := le_trans (le_max_left _ _) hqq
  have hq8 : 8 ≤ q := le_trans (le_max_right _ _) hqq
  set L : ℝ := Real.log (q:ℝ) with hLdef
  have hL2 : 2 ≤ L := by
    rw [hLdef]
    have h1 : Real.log 8 ≤ Real.log (q:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq8)
    have h3 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    rw [h3] at h1
    have h4 : (2:ℝ) < 3 * Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    linarith
  have hLpos : 0 < L := by linarith
  have herr : C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) ≤ f 0 * ε * L := by
    rw [hLdef]; exact hq₁ q hq₁q
  -- the shifted point
  set s : ℂ := (β:ℂ) + (τ:ℂ)*Complex.I with hsdef
  let M : ℂ := ∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - 1) * L) * (t:ℂ))) * ((f t : ℝ):ℂ)
  let cterm : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
      ((f (Real.log n / L) : ℝ) : ℂ)
  -- the real `K`-sum is the real part of the complex sum
  have hKsum : Work.ZeroFreeTables.Ksum q f L s (1 : DirichletCharacter ℂ q)
      = (∑' n : ℕ, cterm n).re := by
    rw [Ksum_eq_re_tsum hLpos q hsupp s (1 : DirichletCharacter ℂ q)]
  -- Heath-Brown, Lemma 5.3 at `s = β + iτ`
  have hbound : ‖(∑' n, cterm n) - ((L:ℝ):ℂ) * M‖
      ≤ C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) := by
    have h := hCbd (q := q) (L := L) hL2 s ?_ ?_
    · simpa only [cterm, M] using h
    · have hsre : s.re = β := by rw [hsdef]; simp
      rw [hsre]
      have : Real.sqrt (Real.log L) / L
          = Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by rw [hLdef]
      rw [this]; exact hβbd
    · have hsim : s.im = τ := by rw [hsdef]; simp
      rw [hsim, hLdef]; exact hτL
  -- `hdec` at `z = (s-1)L`
  have hz_re : (((s - 1) * L)).re = (β - 1) * L := by
    rw [hsdef]
    have h2 : (((β:ℂ) + (τ:ℂ)*Complex.I) - 1) * (L:ℂ)
        = (((β-1)*L : ℝ) : ℂ) + ((τ*L : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h2]; simp
  have hz_im : (((s - 1) * L)).im = τ * L := by
    rw [hsdef]
    have h2 : (((β:ℂ) + (τ:ℂ)*Complex.I) - 1) * (L:ℂ)
        = (((β-1)*L : ℝ) : ℂ) + ((τ*L : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h2]; simp
  have hz_im1 : 1 ≤ |(((s - 1) * L)).im| := by
    rw [hz_im, abs_mul, abs_of_pos hLpos]
    nlinarith [hτ1, hL2]
  have hMnorm : ‖M‖ ≤ Cdec / |(((s - 1) * L)).im| := by
    have h := hdec ((s - 1) * L)
      (by rw [hz_re]; have hb : L * (1 - β) ≤ 1 := by rw [hLdef]; exact hβlam
          nlinarith [hb]) hz_im1
    simpa only [M] using h
  -- the main term is at most `Cdec`
  have hmain : (((L:ℝ):ℂ) * M).re ≤ Cdec := by
    have h2 : (((L:ℝ):ℂ) * M).re ≤ ‖((L:ℝ):ℂ) * M‖ := Complex.re_le_norm _
    have h3 : ‖((L:ℝ):ℂ) * M‖ = L * ‖M‖ := by
      rw [norm_mul]
      congr 1
      simp [Real.norm_eq_abs, abs_of_pos hLpos]
    have h4 : L * ‖M‖ ≤ L * (Cdec / |(((s - 1) * L)).im|) :=
      mul_le_mul_of_nonneg_left hMnorm hLpos.le
    have h5 : L * (Cdec / |(((s - 1) * L)).im|) = Cdec / |τ| := by
      rw [hz_im, abs_mul, abs_of_pos hLpos]; field_simp
    have h6 : Cdec / |τ| ≤ Cdec := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < |τ|)]
      nlinarith [hτ1, hCdec]
    linarith [h2, h3, h4, h5, h6]
  have herr_le : ((∑' n, cterm n) - ((L:ℝ):ℂ) * M).re
      ≤ C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) :=
    le_trans (Complex.re_le_norm _) hbound
  rw [hKsum]
  have hsplit : (∑' n, cterm n).re
      = (((L:ℝ):ℂ) * M).re + ((∑' n, cterm n) - ((L:ℝ):ℂ) * M).re := by
    rw [Complex.sub_re]; ring
  rw [hsplit]
  linarith [hmain, herr_le, herr]

end Work.ZeroFreeTables.OffAxis
