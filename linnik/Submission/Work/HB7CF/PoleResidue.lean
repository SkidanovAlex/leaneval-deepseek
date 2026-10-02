import Mathlib
import Submission.Work.ZeroDensity.LogFree.RouteDefs
import Submission.Work.ZeroDensity.LogFree.PoleDefs
import Submission.Work.ZeroDensity.LogFree.poleResidue_mul_log_sq
import Submission.Work.ZeroDensity.LogFree.innerDiffSq_sum_le
import Submission.Work.ZeroDensity.LogFree.exists_const_log_bound
import Submission.Work.ZeroDensity.Jutila.LzSqIntGood

/-!
# `Work.ZeroDensity.LogFree.poleResidueBound` — the pole residue of the damped large sieve

`Q(1) = poleResidue W = Σ_{d,e ≤ ⌈W⌉₊} θ_d θ_e / [d,e] ≤ C/log W`, uniformly in the (real)
cut-off `W = (q(T+2))^{w}`, which is the input (L4, "pole residue") of the Halász duality count
`DualityCount`.

The proof diagonalizes the pole residue into a sum of squares of Selberg weights
(`poleResidue_mul_log_sq`), compares the real cut-off `W` with the integer cut-off `⌈W⌉₊`
(`innerDiffSq_sum_le`) and applies the sharp Selberg-sieve value `selQ z ≤ log z + O(1)` proved in
the workspace (`Work.ZeroDensity.Jutila.selQ_le_log_add_const`).
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.HB7CF

open Work.LinnikContract
open Work.ZeroDensity.LogFree

/-- **The pole residue is `O(1/log W)`.**  There is `C > 0` with `poleResidue W ≤ C/log W` for
every real cut-off `W ≥ 4`. -/
lemma poleResidue_le_div_log :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℝ, 4 ≤ W → poleResidue W ≤ C / Real.log W := by
  obtain ⟨C₀, hC₀pos, hselQ⟩ := Work.ZeroDensity.Jutila.selQ_le_log_add_const
  obtain ⟨C₁, hC₁pos, harith⟩ := exists_const_log_bound C₀ hC₀pos
  refine ⟨C₁, hC₁pos, ?_⟩
  intro W hW4
  have hW1 : 1 < W := by linarith
  have hWpos : 0 < W := by linarith
  have hlogpos : 0 < Real.log W := Real.log_pos hW1
  have hz2 : 2 ≤ ⌈W⌉₊ := by
    have h : (2 : ℝ) ≤ ((⌈W⌉₊ : ℕ) : ℝ) := by
      have := Nat.le_ceil W; linarith
    exact_mod_cast h
  -- the diagonalization
  have h1 : poleResidue W * (Real.log W) ^ 2 = poleDiag W := poleResidue_mul_log_sq W hW1
  -- splitting the squares
  have h3 : poleDiag W
      ≤ 2 * (∑ l ∈ Finset.Icc 1 ⌈W⌉₊, (Nat.totient l : ℝ) * innerB ⌈W⌉₊ l ^ 2)
        + 2 * (∑ l ∈ Finset.Icc 1 ⌈W⌉₊,
            (Nat.totient l : ℝ) * (innerP W l - innerB ⌈W⌉₊ l) ^ 2) := by
    rw [poleDiag]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro l _
    have hsq : innerP W l ^ 2
        ≤ 2 * innerB ⌈W⌉₊ l ^ 2 + 2 * (innerP W l - innerB ⌈W⌉₊ l) ^ 2 := by
      nlinarith [sq_nonneg (2 * innerB ⌈W⌉₊ l - innerP W l)]
    have hphi : (0 : ℝ) ≤ (Nat.totient l : ℝ) := by positivity
    calc (Nat.totient l : ℝ) * innerP W l ^ 2
        ≤ (Nat.totient l : ℝ)
            * (2 * innerB ⌈W⌉₊ l ^ 2 + 2 * (innerP W l - innerB ⌈W⌉₊ l) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hphi
      _ = 2 * ((Nat.totient l : ℝ) * innerB ⌈W⌉₊ l ^ 2)
            + 2 * ((Nat.totient l : ℝ) * (innerP W l - innerB ⌈W⌉₊ l) ^ 2) := by ring
  have h4 : (∑ l ∈ Finset.Icc 1 ⌈W⌉₊, (Nat.totient l : ℝ) * innerB ⌈W⌉₊ l ^ 2)
      = Work.LinnikAreas.Density4.selQ ⌈W⌉₊ := (selQ_eq_sum_innerB ⌈W⌉₊).symm
  have h5 : (∑ l ∈ Finset.Icc 1 ⌈W⌉₊,
        (Nat.totient l : ℝ) * (innerP W l - innerB ⌈W⌉₊ l) ^ 2)
      ≤ (Real.log ((⌈W⌉₊ : ℝ) / W)) ^ 2 * (1 + Real.log (⌈W⌉₊ : ℝ)) ^ 3 :=
    innerDiffSq_sum_le W hW1
  have h6 : Work.LinnikAreas.Density4.selQ ⌈W⌉₊ ≤ Real.log (⌈W⌉₊ : ℝ) + C₀ := hselQ ⌈W⌉₊ hz2
  have h7 : poleResidue W * (Real.log W) ^ 2
      ≤ C₁ * Real.log W := by
    rw [h1]
    calc poleDiag W
        ≤ 2 * (∑ l ∈ Finset.Icc 1 ⌈W⌉₊, (Nat.totient l : ℝ) * innerB ⌈W⌉₊ l ^ 2)
          + 2 * (∑ l ∈ Finset.Icc 1 ⌈W⌉₊,
              (Nat.totient l : ℝ) * (innerP W l - innerB ⌈W⌉₊ l) ^ 2) := h3
      _ ≤ 2 * (Real.log (⌈W⌉₊ : ℝ) + C₀)
          + 2 * (Real.log ((⌈W⌉₊ : ℝ) / W)) ^ 2 * (1 + Real.log (⌈W⌉₊ : ℝ)) ^ 3 := by
          rw [h4]
          have h5' : 2 * (∑ l ∈ Finset.Icc 1 ⌈W⌉₊,
                (Nat.totient l : ℝ) * (innerP W l - innerB ⌈W⌉₊ l) ^ 2)
              ≤ 2 * (Real.log ((⌈W⌉₊ : ℝ) / W)) ^ 2 * (1 + Real.log (⌈W⌉₊ : ℝ)) ^ 3 := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left h5 (by norm_num)
          linarith [h5', h6]
      _ ≤ C₁ * Real.log W := harith W hW4
  have h8 : poleResidue W * Real.log W ≤ C₁ := by
    have h := h7
    rw [pow_two, ← mul_assoc] at h
    exact le_of_mul_le_mul_right h hlogpos
  exact (le_div_iff₀ hlogpos).mpr h8

theorem poleResidueBoundCF (p : Work.ZeroDensity.LogFree.Params) : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T : ℝ), 1 ≤ T → D₀ ≤ Work.ZeroDensity.LogFree.scale q T →
      Work.ZeroDensity.LogFree.poleResidue (Work.ZeroDensity.LogFree.Dpow q T p.w)
        ≤ C / Work.ZeroDensity.LogFree.Lscale q T := by
  obtain ⟨C₁, hC₁pos, hmain⟩ := poleResidue_le_div_log
  refine ⟨C₁ / p.w, div_pos hC₁pos p.hw, Real.exp (Real.log 4 / p.w), Real.exp_pos _, ?_⟩
  intro q hq _ T hT hD
  have hDpos : 0 < scale q T := by
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hT2 : (0 : ℝ) < T + 2 := by linarith
    rw [scale]
    exact mul_pos (by linarith) hT2
  have hlogD : Real.log 4 / p.w ≤ Real.log (scale q T) := by
    have h := Real.log_le_log (Real.exp_pos (Real.log 4 / p.w)) hD
    rwa [Real.log_exp] at h
  have hlogW : Real.log (Dpow q T p.w) = p.w * Lscale q T := by
    rw [Dpow, Lscale, Real.log_rpow hDpos]
  have hW4 : 4 ≤ Dpow q T p.w := by
    have hpos : 0 < Dpow q T p.w := Real.rpow_pos_of_pos hDpos p.w
    have hlogW4 : Real.log 4 ≤ Real.log (Dpow q T p.w) := by
      rw [hlogW]
      have h : p.w * (Real.log 4 / p.w) = Real.log 4 := by
        rw [mul_div_cancel₀ _ (ne_of_gt p.hw)]
      rw [← h]
      exact mul_le_mul_of_nonneg_left hlogD p.hw.le
    calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log (Dpow q T p.w)) := Real.exp_le_exp.mpr hlogW4
      _ = Dpow q T p.w := Real.exp_log hpos
  have hb := hmain (Dpow q T p.w) hW4
  have hL : Lscale q T ≠ 0 := by
    rw [Lscale]
    exact ne_of_gt (Real.log_pos (by
      rw [scale]
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      nlinarith))
  calc poleResidue (Dpow q T p.w)
      ≤ C₁ / Real.log (Dpow q T p.w) := hb
    _ = (C₁ / p.w) / Lscale q T := by
        rw [hlogW, div_div]

end Work.HB7CF
