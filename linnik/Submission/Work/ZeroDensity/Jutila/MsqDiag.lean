import Mathlib
import Submission.Work.ZeroDensity.Jutila.mixedSelbergDefs
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.moebius_mul_selTheta_real
import Submission.Commons.NumberTheory.Sieve.selberg_double_sum_diagonalization
import Submission.Work.ZeroDensity.Jutila.selW_div_sum_reindex
import Submission.Work.ZeroDensity.Jutila.gcdBilinearDiagonalization

namespace Work.ZeroDensity.Jutila

open Finset

/-! ### Helper lemmas -/

/-- Bilinear form of `Commons.NumberTheory.Sieve.lcm_term`: for positive `d`, `e`,
`x·z/lcm(d,e) = (x/d)·(z/e)·gcd(d,e)`. -/
lemma selW_lcm_term_bilin {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) (x z : ℝ) :
    x * z / (Nat.lcm d e : ℝ) = x / (d : ℝ) * (z / (e : ℝ)) * (Nat.gcd d e : ℝ) := by
  rw [Commons.NumberTheory.Sieve.lcm_gcd_real hd he]
  field_simp

lemma Icc_one_filter_le {W Y : ℕ} (hWY : W ≤ Y) :
    (Finset.Icc 1 Y).filter (fun d => d ≤ W) = Finset.Icc 1 W := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

lemma sum_ite_Icc_le {W Y : ℕ} (hWY : W ≤ Y) (g : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 Y, (if d ≤ W then g d else 0)) = ∑ d ∈ Finset.Icc 1 W, g d := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  exact Icc_one_filter_le hWY

/-- **The `l`-divisible part of the real-cutoff Selberg sum, evaluated.**  For `1 ≤ l`,
`Σ_{d ≤ ⌊w⌋₊, l ∣ d} selW w d/d = (μ l / l)·Θ(w/l, l)` with
`Θ(y,k) = Σ_{m ≤ y, (m,k)=1} μ(m)log(y/m)/m = selTheta y k`.  This is
`selW_div_sum_reindex` combined with `moebius_mul_selTheta_real`. -/
lemma selW_div_sum_eq_selTheta (w : ℝ) (l : ℕ) (hl : 1 ≤ l) :
    (∑ d ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun d => l ∣ d), selW w d / (d : ℝ))
      = ((ArithmeticFunction.moebius l : ℝ) / (l : ℝ)) *
          Work.LinnikAreas.Density4.selTheta (w / (l : ℝ)) l := by
  rw [selW_div_sum_reindex w l hl]
  have hcongr : (∑ m ∈ Finset.Icc 1 (⌊w⌋₊ / l),
        (ArithmeticFunction.moebius (l * m) : ℝ) *
          Real.log (w / ((l * m : ℕ) : ℝ)) / (m : ℝ))
      = ∑ m ∈ Finset.Icc 1 (⌊w⌋₊ / l),
        (ArithmeticFunction.moebius (l * m) : ℝ) *
          Real.log ((w / (l : ℝ)) / (m : ℝ)) / (m : ℝ) :=
    Finset.sum_congr rfl (fun m _ => by
      have hlog : Real.log (w / ((l * m : ℕ) : ℝ)) = Real.log ((w / (l : ℝ)) / (m : ℝ)) := by
        congr 1
        rw [Nat.cast_mul, div_div]
      rw [hlog])
  rw [hcongr, Work.LinnikAreas.Density4.moebius_mul_selTheta_real w l hl, div_eq_mul_inv,
    div_eq_mul_inv]
  ring

/-- **Diagonalized form of the two-parameter Selberg form.**  For real cutoffs with
`⌊w⌋₊ ≤ ⌊y⌋₊`,

  `Msq w y = Σ_{l ≤ ⌊y⌋₊} φ(l)·(Σ_{l ∣ d ≤ ⌊w⌋₊} selW w d/d)·(Σ_{l ∣ e ≤ ⌊y⌋₊} selW y e/e)`.

The sum runs up to `⌊y⌋₊`; the terms with `l > ⌊w⌋₊` vanish because the first inner sum is then
empty.  (The `l ≤ ⌊w⌋₊` terms are evaluated in `MsqDiag`, which uses `selW_div_sum_eq_selTheta`.) -/
lemma Msq_eq_diag (w y : ℝ) (hWY : ⌊w⌋₊ ≤ ⌊y⌋₊) :
    Msq w y = ∑ l ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient l : ℝ) *
        (∑ d ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun d => l ∣ d), selW w d / (d : ℝ)) *
        (∑ e ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun e => l ∣ e), selW y e / (e : ℝ)) := by
  -- Step 1: replace `1/lcm(d,e)` by `gcd(d,e)/(d e)` termwise.
  have step1 : Msq w y = ∑ d ∈ Finset.Icc 1 ⌊w⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
      (selW w d / (d : ℝ)) * (selW y e / (e : ℝ)) * (Nat.gcd d e : ℝ) := by
    unfold Msq
    refine Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => ?_))
    exact selW_lcm_term_bilin (by have := (Finset.mem_Icc.mp hd).1; omega)
      (by have := (Finset.mem_Icc.mp he).1; omega) _ _
  -- Step 2: extend the `d`-range from `Icc 1 ⌊w⌋₊` to `Icc 1 ⌊y⌋₊` with an indicator.
  have step2 : (∑ d ∈ Finset.Icc 1 ⌊w⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        (selW w d / (d : ℝ)) * (selW y e / (e : ℝ)) * (Nat.gcd d e : ℝ))
      = ∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
          (if d ≤ ⌊w⌋₊ then selW w d / (d : ℝ) else 0) *
            (selW y e / (e : ℝ)) * (Nat.gcd d e : ℝ) := by
    rw [← sum_ite_Icc_le hWY (fun d => ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
      (selW w d / (d : ℝ)) * (selW y e / (e : ℝ)) * (Nat.gcd d e : ℝ))]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hdW : d ≤ ⌊w⌋₊
    · rw [if_pos hdW]
      exact Finset.sum_congr rfl (fun e _ => by rw [if_pos hdW])
    · rw [if_neg hdW,
        Finset.sum_eq_zero (fun e _ => by simp [if_neg hdW])]
  -- Step 3: bilinear gcd diagonalization.
  have step3 : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        (if d ≤ ⌊w⌋₊ then selW w d / (d : ℝ) else 0) *
          (selW y e / (e : ℝ)) * (Nat.gcd d e : ℝ))
      = ∑ l ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient l : ℝ) *
          (∑ d ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun d => l ∣ d),
            (if d ≤ ⌊w⌋₊ then selW w d / (d : ℝ) else 0)) *
          (∑ e ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun e => l ∣ e), selW y e / (e : ℝ)) := by
    have hTpos : ∀ d ∈ Finset.Icc 1 ⌊y⌋₊, 0 < d := by
      intro d hd
      have := (Finset.mem_Icc.mp hd).1
      omega
    have hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ Finset.Icc 1 ⌊y⌋₊ → l ∈ Finset.Icc 1 ⌊y⌋₊ := by
      intro l d hld hd
      obtain ⟨hd1, hdY⟩ := Finset.mem_Icc.mp hd
      have hdpos : 0 < d := by omega
      exact Finset.mem_Icc.mpr
        ⟨Nat.pos_of_dvd_of_pos hld hdpos, le_trans (Nat.le_of_dvd hdpos hld) hdY⟩
    exact gcdBilinearDiagonalization (Finset.Icc 1 ⌊y⌋₊) hTpos hTclosed _ _
  -- Step 4: collapse the `d`-filters using the indicator.
  have step4 : (∑ l ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient l : ℝ) *
        (∑ d ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun d => l ∣ d),
          (if d ≤ ⌊w⌋₊ then selW w d / (d : ℝ) else 0)) *
        (∑ e ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun e => l ∣ e), selW y e / (e : ℝ)))
      = ∑ l ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient l : ℝ) *
        (∑ d ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun d => l ∣ d), selW w d / (d : ℝ)) *
        (∑ e ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun e => l ∣ e), selW y e / (e : ℝ)) := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hAw : (∑ d ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun d => l ∣ d),
          (if d ≤ ⌊w⌋₊ then selW w d / (d : ℝ) else 0))
        = ∑ d ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun d => l ∣ d), selW w d / (d : ℝ) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hAw]
  rw [step1, step2, step3, step4]

/-- **Two-parameter Selberg diagonalization of `Msq`.**  For real cutoffs `1 ≤ w ≤ y`,
`Msq w y = Σ_{δ ≤ ⌊w⌋₊} (μ(δ)²·φ(δ)/δ²)·Θ_w(δ)·Θ_y(δ)` with `Θ_z(δ) = selTheta (z/δ) δ`.

Route.  (i) Prove the bilinear gcd-diagonalization
`Σ_{d,e ∈ T} a_d b_e gcd(d,e) = Σ_{l ∈ T} φ(l) (Σ_{l∣d} a_d)(Σ_{l∣e} b_e)` by adapting
`Commons.NumberTheory.Sieve.sum_gcd_rpow_diagonalization`
(`Submission/Commons/NumberTheory/Sieve/selberg_diagonalization_sigma.lean`), using the helpers
`totient_sum_eq_gcd`, `sum_sum_ite`, `triple_sum_swap` of
`Submission/Commons/NumberTheory/Sieve/selberg_double_sum_diagonalization.lean`.
(ii) Apply it with `T = Icc 1 ⌊y⌋₊`, `a d = (if d ≤ ⌊w⌋₊ then selW w d / d else 0)`,
`b e = selW y e / e`, the linearity conditions being those of `Icc`, and
`Commons.NumberTheory.Sieve.lcm_term` for `1/lcm(d,e) = gcd(d,e)/(d e)`.
(iii) Reindex the inner sums using the real-cutoff analogue of the two existing results
`selLam_div_sum_reindex` and `moebius_mul_sum_eq_moebius_mul_selTheta`
(`Submission/Work/LinnikAreas/Density4/`): for `1 ≤ l`,
`Σ_{d ∈ Icc 1 ⌊w⌋₊, l ∣ d} selW w d / d = (μ l / l)·selTheta (w/l) l`
(use `Nat.floor_div_natCast` to identify `⌊w⌋₊ / l` with `⌊w/l⌋₊`, and that
`log (w/(l m)) = log ((w/l)/m)`), and the terms with `l > ⌊w⌋₊` vanish because the first inner
sum is then empty. -/
theorem MsqDiag (w y : ℝ) (h1 : 1 ≤ w) (h2 : w ≤ y) :
    Work.ZeroDensity.Jutila.Msq w y
      = Finset.sum (Finset.Icc 1 ⌊w⌋₊) (fun δ => ((ArithmeticFunction.moebius δ : ℝ) ^ 2 *
            (Nat.totient δ : ℝ)) / ((δ : ℝ) ^ 2) *
            Work.LinnikAreas.Density4.selTheta (w / (δ : ℝ)) δ *
            Work.LinnikAreas.Density4.selTheta (y / (δ : ℝ)) δ) := by
  have hWY : ⌊w⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor h2
  rw [Msq_eq_diag w y hWY]
  -- discard the terms `l > ⌊w⌋₊` by replacing `if l ≤ ⌊w⌋₊ then ... else 0` and shrinking the range
  have hstep : (∑ l ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient l : ℝ) *
        (∑ d ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun d => l ∣ d), selW w d / (d : ℝ)) *
        (∑ e ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun e => l ∣ e), selW y e / (e : ℝ)))
      = ∑ l ∈ Finset.Icc 1 ⌊w⌋₊, ((ArithmeticFunction.moebius l : ℝ) ^ 2 *
            (Nat.totient l : ℝ)) / ((l : ℝ) ^ 2) *
            Work.LinnikAreas.Density4.selTheta (w / (l : ℝ)) l *
            Work.LinnikAreas.Density4.selTheta (y / (l : ℝ)) l := by
    have hterms : (∑ l ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient l : ℝ) *
          (∑ d ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun d => l ∣ d), selW w d / (d : ℝ)) *
          (∑ e ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun e => l ∣ e), selW y e / (e : ℝ)))
        = ∑ l ∈ Finset.Icc 1 ⌊y⌋₊, (if l ≤ ⌊w⌋₊ then
            ((ArithmeticFunction.moebius l : ℝ) ^ 2 * (Nat.totient l : ℝ)) / ((l : ℝ) ^ 2) *
              Work.LinnikAreas.Density4.selTheta (w / (l : ℝ)) l *
              Work.LinnikAreas.Density4.selTheta (y / (l : ℝ)) l else 0) := by
      refine Finset.sum_congr rfl (fun l hl => ?_)
      have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
      by_cases hlW : l ≤ ⌊w⌋₊
      · rw [if_pos hlW, selW_div_sum_eq_selTheta w l hl1, selW_div_sum_eq_selTheta y l hl1]
        ring
      · rw [if_neg hlW]
        have hzero : (∑ d ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun d => l ∣ d),
            selW w d / (d : ℝ)) = 0 := by
          refine Finset.sum_eq_zero (fun d hd => ?_)
          exfalso
          rw [Finset.mem_filter, Finset.mem_Icc] at hd
          obtain ⟨⟨hd1, hdW⟩, hld⟩ := hd
          have hld' : l ≤ d := Nat.le_of_dvd (by omega) hld
          omega
        rw [hzero]
        ring
    rw [hterms, sum_ite_Icc_le hWY (fun l =>
      ((ArithmeticFunction.moebius l : ℝ) ^ 2 * (Nat.totient l : ℝ)) / ((l : ℝ) ^ 2) *
        Work.LinnikAreas.Density4.selTheta (w / (l : ℝ)) l *
        Work.LinnikAreas.Density4.selTheta (y / (l : ℝ)) l)]
  exact hstep

end Work.ZeroDensity.Jutila
