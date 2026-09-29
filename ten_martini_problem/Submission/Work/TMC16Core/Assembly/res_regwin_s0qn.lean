import Mathlib
import Submission.Work.TMC16Core.Assembly.RegWin
import Submission.Work.TMC16Core.Assembly.endgame_g
import Submission.Work.TMC16Core.Assembly.s0num
import Submission.Work.TMC16Core.Assembly.s0win
import Submission.Work.TMC16Core.Assembly.s0_uniform_qn
import Submission.Work.TMC16Core.Assembly.theta_strand
import Submission.Work.TMC16Core.Core.nr_ablock
import Submission.Work.TMC16Core.Core.setup
import Submission.Work.TMC16Core.Assembly.s0_reg

namespace Work.TMC16Core.Assembly

set_option maxHeartbeats 1000000

/-- The `s = 0`, scale-`qₙ` branch assembled from `s0_reg`: for the two resonant-free shifts
`m ∈ {0,1}` and every `k₀` in the admissible middle range, the site `y = m qₙ + k₀` is
`RegWin`-regular with the `s0` window of `qₙ - 1` sites.  This is `s0_reg` instantiated at
`H = qₙ`, `L = log lam`, `κ = b₀`. -/
theorem res_regwin_s0qn (h4 : Work.TMC16Core.P_LEBasics) (h7 : Work.TMC16Core.P_BJ_dioph)
    {α b₀ lam : ℝ} (hα : Irrational α) (hb₀ : 0 < b₀)
    (hDioph : Work.TMC16Core.DiophBelow α b₀)
    (hlam : Real.exp (16 * b₀ / 9) < lam)
    {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i) (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    {E : ℝ} (hE : E ∈ Work.TMC16Core.amoSpec α lam) {θ : ℝ}
    (hθ : θ ∉ Work.TMC16Core.Theta α) {u : ℤ → ℂ}
    (hu : Work.TMC16Core.IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℤ, 0 ≤ m → m ≤ 1 →
      (m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ)) →
      ((m : ℝ) * (q n : ℝ)
        ≤ 100 * (Real.rpow (q (n + 1) : ℝ) (8 / 9) + (q n : ℝ))) →
      ∀ k₀ : ℤ, ((((q n - 1 : ℕ) : ℝ))) / 20 + 3 ≤ (k₀ : ℝ) →
        (k₀ : ℝ) ≤ 95 * ((((q n - 1 : ℕ) : ℝ))) / 100 - 3 →
        30 * q n ≤ q (n + 1) →
        Work.TMC16Core.Assembly.RegWin α lam θ (E : ℂ) (7 * Real.log lam / 10)
          ((((q n - 1 : ℕ) : ℝ)) / 40) (q n - 1) (m * (q n : ℤ) + k₀) := by
  obtain ⟨N, hN⟩ :=
    s0_reg (α := α) (b₀ := b₀) (lam := lam) (L := Real.log lam) (κ := b₀)
      (q := q) (Δ := Δ)
      h4 h7 hα hb₀ hDioph rfl hlam hb₀ hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
      hE hθ hu hu0
  refine ⟨N, ?_⟩
  intro n hn m hm0 hm1 hmq hmle k₀ hk0lo hk0hi _
  have hqn1 : 1 ≤ q n := hqpos n
  have hqn1R : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqn1
  have hqn0R : (0 : ℝ) ≤ (q n : ℝ) := Nat.cast_nonneg _
  have hsub : (((q n - 1 : ℕ) : ℝ)) = (q n : ℝ) - 1 := by
    rw [Nat.cast_sub hqn1]; norm_num
  have hrpow_nn : 0 ≤ Real.rpow (q (n + 1) : ℝ) (8 / 9) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- `k₀ ≥ 3 ≥ 0`
  have hk0nn : (0 : ℤ) ≤ k₀ := by
    have h0 : (0 : ℝ) ≤ (((q n - 1 : ℕ) : ℝ)) / 20 := by positivity
    have h3 : (0 : ℝ) ≤ (k₀ : ℝ) := by linarith [hk0lo, h0]
    exact_mod_cast h3
  -- `q n ≤ (q n)^2`
  have hHq2 : (q n : ℝ) ≤ (q n : ℝ) ^ 2 := by nlinarith [hqn1R]
  -- `1 ≤ y = m qₙ + k₀`
  have hy1 : (1 : ℤ) ≤ m * (q n : ℤ) + k₀ := by
    have h0 : (0 : ℝ) ≤ (((q n - 1 : ℕ) : ℝ)) / 20 := by positivity
    have hk03 : (3 : ℝ) ≤ (k₀ : ℝ) := by linarith [hk0lo, h0]
    have hk03i : (3 : ℤ) ≤ k₀ := by exact_mod_cast hk03
    have hmul : (0 : ℤ) ≤ m * (q n : ℤ) := mul_nonneg hm0 (Int.natCast_nonneg _)
    omega
  -- `y ≤ 100 (q_{n+1}^{8/9} + qₙ)`
  have hyhi : ((m * (q n : ℤ) + k₀ : ℤ) : ℝ) ≤
      100 * (Real.rpow (q (n + 1) : ℝ) (8 / 9) + (q n : ℝ)) := by
    have hm1R : (m : ℝ) ≤ 1 := by exact_mod_cast hm1
    have hk0q : (k₀ : ℝ) ≤ 95 * ((q n : ℝ) - 1) / 100 - 3 := by
      rw [← hsub]; exact hk0hi
    have hcast : ((m * (q n : ℤ) + k₀ : ℤ) : ℝ) = (m : ℝ) * (q n : ℝ) + (k₀ : ℝ) := by
      push_cast; ring
    rw [hcast]
    nlinarith [hm1R, hk0q, hrpow_nn, hqn1R]
  -- the `m`-shift hypothesis, with `|m| = m`
  have hmq' : m ≠ 0 → 10 * (m + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ) := by
    intro hm
    have habs : |m| = m := abs_of_nonneg hm0
    have h := hmq hm
    rw [habs] at h
    exact h
  -- the two `k₀`-window bounds, rewritten through `y - m qₙ = k₀`
  have habs : |((m * (q n : ℤ) + k₀ : ℤ) : ℝ) - (m : ℝ) * (q n : ℝ)| = (k₀ : ℝ) := by
    have h : ((m * (q n : ℤ) + k₀ : ℤ) : ℝ) - (m : ℝ) * (q n : ℝ) = (k₀ : ℝ) := by
      push_cast; ring
    rw [h, abs_of_nonneg (by exact_mod_cast hk0nn)]
  have hlo : ((q n : ℝ) - 1) / 20 + 3
      ≤ |((m * (q n : ℤ) + k₀ : ℤ) : ℝ) - (m : ℝ) * (q n : ℝ)| := by
    rw [habs, ← hsub]
    exact hk0lo
  have hhi : |((m * (q n : ℤ) + k₀ : ℤ) : ℝ) - (m : ℝ) * (q n : ℝ)|
      ≤ 95 * ((q n : ℝ) - 1) / 100 - 3 := by
    rw [habs, ← hsub]
    exact hk0hi
  exact hN n hn (q n) (m * (q n : ℤ) + k₀) m (Or.inr (Or.inl rfl))
    hHq2 hy1 hyhi hm0 hmq' hlo hhi

end Work.TMC16Core.Assembly
