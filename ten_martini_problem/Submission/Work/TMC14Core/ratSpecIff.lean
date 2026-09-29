import Mathlib
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMC14Core.chamCoef_norm
import Submission.Work.TMC14Core.disc_im_eq_zero

/-!
# TMC14Core: `ratSpec p q lam` is the sublevel set of the discriminant

For a rational approximant `p/q` (coprime, `q ≥ 1`), `0 < λ ≤ 1` and a real energy `E`,

  `E ∈ ratSpec p q lam ↔ ‖Δ(E)‖ ≤ 2 + 2λ^q`,

where `Δ = disc p q lam` is the discriminant of the periodic problem.

`⟹` is immediate from Chambers' formula
`tr A_q(θ) = Δ(E) + chamCoef · cos(2πqθ)` (`chambers`) and `‖chamCoef‖ = 2λ^q`
(`chamCoef_norm`): `‖Δ‖ ≤ ‖tr A_q‖ + ‖chamCoef‖`.

`⟸` uses in addition that `Δ(E)` is real at real energy (`disc_im_eq_zero`) and that
`chamCoef` is real: writing `Δ(E) = r`, `chamCoef = c` with `r, c ∈ ℝ`, the two phases
`θ = 0` and `θ = 1/(2q)` give `tr A_q = r + c` and `tr A_q = r - c` respectively, and
`min (|r+c|) (|r-c|) ≤ 2` because `|r| ≤ 2 + |c|` and `|c| ≤ 2`.
-/

namespace Work.TMC14Core

/-- Elementary real inequality behind the `⟸` direction: if `|r| ≤ 2 + |c|` and `|c| ≤ 2`
then one of `|r + c|`, `|r - c|` is at most `2`. -/
lemma abs_add_or_sub_le (r c : ℝ) (h : |r| ≤ 2 + |c|) (h2 : |c| ≤ 2) :
    |r + c| ≤ 2 ∨ |r - c| ≤ 2 := by
  rcases le_or_gt 0 r with hr0 | hr0 <;> rcases le_or_gt 0 c with hc0 | hc0
  · have h1 : |r| = r := abs_of_nonneg hr0
    have h2' : |c| = c := abs_of_nonneg hc0
    rw [h1, h2'] at h; rw [h2'] at h2
    rcases le_or_gt c r with hcr | hcr
    · right; rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ r - c)]; linarith
    · right; rw [abs_of_nonpos (by linarith : r - c ≤ 0)]; linarith
  · have h1 : |r| = r := abs_of_nonneg hr0
    have h2' : |c| = -c := abs_of_neg hc0
    rw [h1, h2'] at h; rw [h2'] at h2
    left
    rcases le_or_gt (-c) r with hcr | hcr
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ r + c)]; linarith
    · rw [abs_of_neg (by linarith : r + c < 0)]; linarith
  · have h1 : |r| = -r := abs_of_neg hr0
    have h2' : |c| = c := abs_of_nonneg hc0
    rw [h1, h2'] at h; rw [h2'] at h2
    left
    rcases le_or_gt r (-c) with hcr | hcr
    · rw [abs_of_nonpos (by linarith : r + c ≤ 0)]; linarith
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ r + c)]; linarith
  · have h1 : |r| = -r := abs_of_neg hr0
    have h2' : |c| = -c := abs_of_neg hc0
    rw [h1, h2'] at h; rw [h2'] at h2
    right
    rcases le_or_gt r c with hcr | hcr
    · rw [abs_of_nonpos (by linarith : r - c ≤ 0)]; linarith
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ r - c)]; linarith

theorem ratSpecIff (p : ℤ) (q : ℕ) (lam : ℝ) (hpq : Nat.Coprime p.natAbs q)
    (hq : 1 ≤ q) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (E : ℝ) :
    E ∈ ratSpec p q lam ↔ ‖(disc p q lam).eval (E : ℂ)‖ ≤ 2 + 2 * lam ^ q := by
  have hcn : ‖chamCoef p q lam‖ = 2 * lam ^ q := chamCoef_norm p q lam hlam
  obtain ⟨c, hc⟩ : ∃ c : ℝ, chamCoef p q lam = (c : ℂ) :=
    ⟨2 * (-lam) ^ q * (-1 : ℝ) ^ (p * ((q : ℤ) - 1)), by
      rw [chamCoef]; push_cast; ring⟩
  have hcabs : |c| = 2 * lam ^ q := by
    have h3 : ‖(c : ℂ)‖ = 2 * lam ^ q := by rw [← hc]; exact hcn
    simpa using h3
  have hcle : |c| ≤ 2 := by
    rw [hcabs]
    have h1 : lam ^ q ≤ 1 := pow_le_one₀ hlam.le hlam1
    linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (disc p q lam).eval (E : ℂ) = (r : ℂ) :=
    ⟨((disc p q lam).eval (E : ℂ)).re, by
      apply Complex.ext
      · simp
      · simpa [Complex.ofReal_im] using disc_im_eq_zero p q lam E⟩
  constructor
  · rintro ⟨θ, hθ⟩
    have hch := chambers p q lam (E : ℂ) hpq hq θ
    have hsplit : (disc p q lam).eval (E : ℂ)
        = trAq p q lam (E : ℂ) θ
          - chamCoef p q lam * ((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ) := by
      rw [hch]; ring
    rw [hsplit]
    calc ‖trAq p q lam (E : ℂ) θ - chamCoef p q lam * _‖
        ≤ ‖trAq p q lam (E : ℂ) θ‖ + ‖chamCoef p q lam * _‖ := norm_sub_le _ _
      _ ≤ 2 + 2 * lam ^ q := by
          have hcos : ‖((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ)‖ ≤ 1 := by
            have h : ‖((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ)‖
                = |Real.cos (2 * Real.pi * (q : ℝ) * θ)| := RCLike.norm_ofReal _
            rw [h]; exact Real.abs_cos_le_one _
          have h2 : ‖chamCoef p q lam * ((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ)‖
              ≤ 2 * lam ^ q := by
            rw [norm_mul, hcn]
            exact mul_le_of_le_one_right (by positivity) hcos
          linarith
  · intro h
    have hrle : |r| ≤ 2 + 2 * lam ^ q := by
      have h3 : ‖(r : ℂ)‖ ≤ 2 + 2 * lam ^ q := by rw [← hr]; exact h
      simpa using h3
    rw [ratSpec]
    have hcase := abs_add_or_sub_le r c (by rw [hcabs]; linarith) hcle
    rcases hcase with hcase | hcase
    · refine ⟨0, ?_⟩
      have hch := chambers p q lam (E : ℂ) hpq hq 0
      have hval : trAq p q lam (E : ℂ) 0 = ((r + c : ℝ) : ℂ) := by
        rw [hch, hr, hc]
        have hc0 : Real.cos (2 * Real.pi * (q : ℝ) * 0) = 1 := by simp
        rw [hc0]; push_cast; ring
      rw [hval]
      have hn : ‖((r + c : ℝ) : ℂ)‖ = |r + c| := RCLike.norm_ofReal _
      rw [hn]; exact hcase
    · refine ⟨1 / (2 * (q : ℝ)), ?_⟩
      have hch := chambers p q lam (E : ℂ) hpq hq (1 / (2 * (q : ℝ)))
      have hval : trAq p q lam (E : ℂ) (1 / (2 * (q : ℝ))) = ((r - c : ℝ) : ℂ) := by
        rw [hch, hr, hc]
        have hc1 : Real.cos (2 * Real.pi * (q : ℝ) * (1 / (2 * (q : ℝ)))) = -1 := by
          have hqR : (q : ℝ) ≠ 0 := by positivity
          have harg : 2 * Real.pi * (q : ℝ) * (1 / (2 * (q : ℝ))) = Real.pi := by field_simp
          rw [harg]; exact Real.cos_pi
        rw [hc1]; push_cast; ring
      rw [hval]
      have hn : ‖((r - c : ℝ) : ℂ)‖ = |r - c| := RCLike.norm_ofReal _
      rw [hn]; exact hcase

end Work.TMC14Core
