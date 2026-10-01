/-
# ZeroFreeTables/P9/HbCombinationL_nonneg — HB (9.1) for the coefficient-correct functional

Heath-Brown's Lemma 9.1 rests on the pointwise (in `n`) inequality

  `0 ≤ χ₀(n) (1 + Re z₀) (K + Re z₁)²`,   `z_j = χ(n) n^{-iγ_j}`,

whose expansion — grouped by the eight pairs `(χ^j, σ + iΔ)` of the argument points `σ`,
`σ+iγ₀`, `σ+i(γ₁−γ₀)`, `σ+iγ₁`, `σ+i(γ₁+γ₀)`, `σ+i(2γ₁−γ₀)`, `σ+2iγ₁`, `σ+i(2γ₁+γ₀)` and the
characters `χ⁰, χ, χ⁰, χ, χ², χ, χ², χ³` with the coefficients `(K²+½), (K²+½), K, 2K, K, ¼, ½, ¼`
— is exactly HB (9.1):

  `0 ≤ HbCombinationL q χ K σ γ₀ γ₁ a λ₁`.

This is the coefficient-correct (`L`-weight, i.e. `u(y) = α + α²y + (1/3)α³y²`) analogue of
`P3/Pointwise91.lean`'s `Pointwise91`, whose proof it follows line by line: the same pointwise
kernel identity `HbKernelIdentity`, the same `tsum`-linearisation, and the same
summability of the von Mangoldt sums (`SummableVonMangoldtLogPow`).  The only change is the
weight, whose non-negativity and growth are supplied by `P3/WLBase.lean`
(`hbWL_nonneg`, `hbWL_abs_le`, `hbRawL_abs_le`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.WLBase
import Submission.Work.ZeroFreeTables.P3.Pointwise91
import Submission.Work.ZeroFreeTables.P9.SummableHbRawL

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.P9

noncomputable section

open Work.ZeroFreeTables.P3

/-! ## Summability of the `L`-summands -/

/-- `Summable` at an arbitrary point `s` with `Re s > 1`, from the case `s = Re s + i Im s`. -/
lemma summable_hbRawL' {q : ℕ} [NeZero q] (hq : 2 ≤ q) (ψ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) (a lam₁ : ℝ) : Summable (hbRawL q ψ s a lam₁) := by
  have h := SummableHbRawL (q := q) hq ψ hs s.im a lam₁
  rwa [Complex.re_add_im s] at h

/-- Summability of the `hbTermL` normal form. -/
lemma summable_hbTermL {q : ℕ} [NeZero q] (hq : 2 ≤ q) (ψ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (Δ a lam₁ : ℝ) : Summable (hbTermL q ψ σ Δ a lam₁) :=
  (SummableHbRawL (q := q) hq ψ hσ Δ a lam₁).congr
    (fun n => hbRawL_eq_hbTermL ψ σ Δ a lam₁ n)

/-- Summability of the eight summand families of HB (9.1). -/
lemma summable_hbChiL (q : ℕ) [NeZero q] (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (γ₀ γ₁ a lam₁ : ℝ) (i : Fin 8) :
    Summable (hbRawL q (hbChi q χ i) (hbPt σ γ₀ γ₁ i) a lam₁) := by
  fin_cases i <;>
    · simp only [hbChi, hbPt, hbDl]
      simp
      exact summable_hbRawL' hq _ (by simpa using hσ) _ _

/-! ## The pointwise identity -/

/-- For a unit `n` modulo `q` the eight summands of HB (9.1) combine, at the level of the single
integer `n`, into `Λ n · n^{-σ} · u(log n / log q) · hbKernel K (χ(n)n^{-iγ₀}) (χ(n)n^{-iγ₁})`. -/
lemma hbSummandL_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (K σ γ₀ γ₁ a lam₁ : ℝ)
    (n : ℕ) (hunit : IsUnit (n : ZMod q)) :
    hbSummandL q χ K σ γ₀ γ₁ a lam₁ n
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * hbWL (Real.log q) a lam₁ n
        * hbKernel K (χ (n : ZMod q) * hbE γ₀ n) (χ (n : ZMod q) * hbE γ₁ n) := by
  have hc : χ (n : ZMod q) ≠ 0 := MulChar.apply_ne_zero_iff.mpr hunit
  have hu : hbE γ₀ n ≠ 0 := hbE_ne_zero _ _
  rw [← kernel_expand K (χ (n : ZMod q)) (hbE γ₀ n) (hbE γ₁ n) hc hu]
  rw [hbSummandL]
  simp only [hbTermL]
  rw [MulChar.one_apply hunit, MulChar.pow_apply' χ (by norm_num : (2 : ℕ) ≠ 0),
      MulChar.pow_apply' χ (by norm_num : (3 : ℕ) ≠ 0)]
  rw [hbE_zero, hbE_sub_div γ₁ γ₀ n, hbE_add γ₁ γ₀ n, hbE_two_sub γ₁ γ₀ n, hbE_two γ₁ n,
    hbE_two_add γ₁ γ₀ n]
  simp only [one_mul, Complex.one_re]
  ring

/-- At a non-unit `n` modulo `q` every Dirichlet character vanishes, hence every summand of
HB (9.1) vanishes. -/
lemma hbSummandL_nonunit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (K σ γ₀ γ₁ a lam₁ : ℝ)
    (n : ℕ) (hunit : ¬ IsUnit (n : ZMod q)) :
    hbSummandL q χ K σ γ₀ γ₁ a lam₁ n = 0 := by
  have h0 : ∀ ψ : DirichletCharacter ℂ q, ψ (n : ZMod q) = 0 :=
    fun ψ => MulChar.map_nonunit ψ hunit
  simp [hbSummandL, hbTermL, h0]

/-- Non-negativity of the pointwise combination of HB (9.1). -/
lemma hbSummandL_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {K σ γ₀ γ₁ a lam₁ : ℝ} (hq : 2 ≤ q) (hσ : 1 < σ) (ha : 0 < a) (hlam : 0 ≤ lam₁) (n : ℕ) :
    0 ≤ hbSummandL q χ K σ γ₀ γ₁ a lam₁ n := by
  by_cases hunit : IsUnit (n : ZMod q)
  · rw [hbSummandL_unit χ K σ γ₀ γ₁ a lam₁ n hunit]
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · exact hbWL_nonneg (Real.log_pos (by exact_mod_cast (show 1 < q by omega))) ha hlam n
    · exact hbKernel_nonneg K _ _
        (by rw [norm_mul, norm_char_unit χ hunit, hbE_norm, one_mul])
        (by rw [norm_mul, norm_char_unit χ hunit, hbE_norm, one_mul])
  · rw [hbSummandL_nonunit χ K σ γ₀ γ₁ a lam₁ n hunit]

/-! ## Linearisation of the eight `tsum`s -/

lemma hbRawSumL_eq_finsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (K σ γ₀ γ₁ a lam₁ : ℝ)
    (n : ℕ) :
    hbRawSumL q χ K σ γ₀ γ₁ a lam₁ n
      = ∑ i : Fin 8, hbCoef K i * hbRawL q (hbChi q χ i) (hbPt σ γ₀ γ₁ i) a lam₁ n := rfl

/-- `HbCombinationL` as `(log q)⁻¹` times a finite combination of the eight absolutely
convergent `tsum`s. -/
lemma HbCombinationL_eq_finsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (K σ γ₀ γ₁ a lam₁ : ℝ) :
    HbCombinationL q χ K σ γ₀ γ₁ a lam₁
      = (Real.log q)⁻¹ * ∑ i : Fin 8, hbCoef K i
          * (∑' n, hbRawL q (hbChi q χ i) (hbPt σ γ₀ γ₁ i) a lam₁ n) := by
  simp only [HbCombinationL, SigmaP3L_eq_hbRawL, hbChi, hbPt, hbCoef, hbDl, Fin.sum_univ_eight]
  simp
  ring

/-- Linearity of `tsum` over the eight absolutely convergent series of HB (9.1). -/
lemma tsum_hbRawSumL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {K σ γ₀ γ₁ a lam₁ : ℝ}
    (hq : 2 ≤ q) (hσ : 1 < σ) :
    (∑' n, hbRawSumL q χ K σ γ₀ γ₁ a lam₁ n)
      = ∑ i : Fin 8, hbCoef K i
          * (∑' n, hbRawL q (hbChi q χ i) (hbPt σ γ₀ γ₁ i) a lam₁ n) := by
  rw [tsum_finset_lincomb Finset.univ
    (fun i => hbRawL q (hbChi q χ i) (hbPt σ γ₀ γ₁ i) a lam₁) (hbCoef K)
    (fun i _ => summable_hbChiL q hq χ hσ γ₀ γ₁ a lam₁ i)]
  rfl

/-- The two normal forms of the pointwise combination agree termwise. -/
lemma hbRawSumL_eq_hbSummandL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (K σ γ₀ γ₁ a lam₁ : ℝ) (n : ℕ) :
    hbRawSumL q χ K σ γ₀ γ₁ a lam₁ n = hbSummandL q χ K σ γ₀ γ₁ a lam₁ n := by
  simp only [hbRawSumL, hbSummandL, hbChi, hbCoef, hbDl, hbPt, Fin.sum_univ_eight,
    hbRawL_eq_hbTermL]
  simp
  ring

lemma tsum_hbSummandL_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (K σ γ₀ γ₁ a lam₁ : ℝ) :
    (∑' n, hbSummandL q χ K σ γ₀ γ₁ a lam₁ n)
      = ∑' n, hbRawSumL q χ K σ γ₀ γ₁ a lam₁ n := by
  apply tsum_congr
  intro n
  exact (hbRawSumL_eq_hbSummandL χ K σ γ₀ γ₁ a lam₁ n).symm

/-- HB (9.1) for the coefficient-correct functional: the eight-term combination is non-negative. -/
theorem HbCombinationL_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (K σ γ₀ γ₁ a lam₁ : ℝ) (hK : 0 ≤ K) (hσ : 1 < σ) (ha : 0 < a) (hlam : 0 ≤ lam₁) :
    0 ≤ Work.ZeroFreeTables.HbCombinationL q χ K σ γ₀ γ₁ a lam₁ := by
  rcases eq_or_ne q 1 with hq1 | hq1
  · subst hq1
    simp [Work.ZeroFreeTables.HbCombinationL, Work.ZeroFreeTables.SigmaP3L]
  · have hq2 : 2 ≤ q := by
      have hq0 : 0 < q := NeZero.pos q
      omega
    have hlogq : 0 ≤ (Real.log q)⁻¹ :=
      inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega)))
    rw [HbCombinationL_eq_finsum, ← tsum_hbRawSumL χ hq2 hσ,
      ← tsum_hbSummandL_eq χ K σ γ₀ γ₁ a lam₁]
    exact mul_nonneg hlogq (tsum_nonneg (fun n => hbSummandL_nonneg χ hq2 hσ ha hlam n))

end

end Work.ZeroFreeTables.P9
