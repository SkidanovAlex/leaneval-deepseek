/-
Workaround module: verbatim copy of `Submission/Work/ZeroFreeTables/lam0w/principalBound4.lean`
with the placeholder theorem `eulFacBounds` replaced by the proved `lam0_eulFacBounds` of
`Submission.Work.ZeroFreeTables.lam0_eulFacBounds` (the original placeholder is `sorry`-ed, so
anything routed through it has `sorryAx` in its axioms).  The theorem is renamed
`principalBound4_fm`; the mathematical content is unchanged.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le
import Submission.Work.ZeroFreeTables.lam0w.PrincipalDefs
import Submission.Work.ZeroFreeTables.lam0_fm_PrincipalAux
import Submission.Work.ZeroFreeTables.lam0_fm_zetaCorr
import Submission.Work.ZeroFreeTables.lam0_fm_eulFacBounds
import Submission.Work.ZeroFreeTables.lam0w.princCorrIteratedDeriv
import Submission.Work.ZeroFreeTables.lam0w.sigP3PoleExtraction

open DirichletCharacter Complex
open scoped BigOperators

set_option maxHeartbeats 2000000

noncomputable section

namespace Work.ZeroFreeTables.lam0w

/-- **Linnik: the principal-character `P₃` bound with a shift bounded by `a`.**
There is `L₀ = L₀(a,e)` such that for every modulus `q` with `log q ≤ L`, every `L ≥ L₀`,
every `0 ≤ λ₁ ≤ a` and every `s` with `Re s = 1 + a/L`, `|Im s| ≤ 4`,

`Σ(s,χ₀) ≤ Re P₃((a+λ₁)/((s-1)L)) + (a+λ₁)·e`.

The proof combines the exact pole-extraction reduction (`sigP3PoleExtraction`) with the bounds
on the corrector `princCorr q = zetaCorr - eulFac q` on the rectangle `1 < Re ≤ 2`, `|Im| ≤ 4`:
`zetaCorr` and its two derivatives are bounded by a constant (`zetaCorrBounded`), while the
Euler-factor part obeys the per-prime bounds of `lam0_eulFacBounds` and the prime-sum bounds of
`primeFactors_logPow_div_le` / `primeSumBound`; the resulting `O((log L)^4)/L` error is absorbed
by `absorbArith`. -/
theorem principalBound4_fm {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∃ L₀ : ℝ, ∀ {q : ℕ} [NeZero q] {L lam₁ : ℝ}, L₀ ≤ L → Real.log (q : ℝ) ≤ L →
      0 ≤ lam₁ → lam₁ ≤ a →
      ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 4 →
        Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
          ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re + (a + lam₁) * e := by
  obtain ⟨Cz, hCzpos, hCz⟩ := zetaCorrBounded_fm
  obtain ⟨D1, hD1pos, hD1b⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 1 (by norm_num)
  obtain ⟨D2, hD2pos, hD2b⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨D3, hD3pos, hD3b⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 3 (by norm_num)
  obtain ⟨L₀, hL₀3, hL₀a, hL₀b⟩ := absorbArith_fm ha he (le_of_lt hCzpos)
    (le_trans (by norm_num) (le_max_right D1 1))
    (le_trans (by norm_num) (le_max_right D2 1))
    (le_trans (by norm_num) (le_max_right D3 1))
  refine ⟨L₀, ?_⟩
  intro q _ L lam₁ hL₀L hlogq hlam0 hlam1 s hsre him
  have hL3 : (3 : ℝ) ≤ L := le_trans hL₀3 hL₀L
  have hLa : a ≤ L := le_trans hL₀a hL₀L
  have hLpos : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hα0 : (0 : ℝ) ≤ a + lam₁ := by linarith
  have hα2a : a + lam₁ ≤ 2 * a := by linarith
  have hsr : 1 < s.re := by
    rw [hsre]
    have : 0 < a / L := div_pos ha hLpos
    linarith
  have hre2 : s.re ≤ 2 := by
    rw [hsre]
    have : a / L ≤ 1 := by rw [div_le_one hLpos]; exact hLa
    linarith
  obtain ⟨hz0, hz1, hz2⟩ := hCz s hsr hre2 him
  obtain ⟨he0, he1, he2⟩ := lam0_eulFacBounds_fm q (le_of_lt hsr)
  have hD1b' : ∀ q' : ℕ, 3 ≤ q' → q'.primeFactors.sum (fun p => Real.log (p : ℝ) / (p : ℝ))
      ≤ D1 * (Real.log (Real.log (q' : ℝ))) ^ 2 := by
    intro q' hq'; simpa using hD1b q' hq'
  have hD2b' : ∀ q' : ℕ, 3 ≤ q' →
      q'.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
      ≤ D2 * (Real.log (Real.log (q' : ℝ))) ^ 3 := by
    intro q' hq'; simpa using hD2b q' hq'
  have hD3b' : ∀ q' : ℕ, 3 ≤ q' →
      q'.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
      ≤ D3 * (Real.log (Real.log (q' : ℝ))) ^ 4 := by
    intro q' hq'; simpa using hD3b q' hq'
  obtain ⟨hS1b, hS2b, hS3b⟩ := primeSumBound_fm D1 D2 D3 (le_of_lt hD1pos) (le_of_lt hD2pos)
    (le_of_lt hD3pos) hD1b' hD2b' hD3b' q hlogq hL3
  set S1 : ℝ := q.primeFactors.sum (fun p => Real.log (p : ℝ) / (p : ℝ)) with hS1def
  set S2 : ℝ := q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) with hS2def
  set S3 : ℝ := q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) with hS3def
  have hid0 : princCorr q s = zetaCorr s - eulFac q s := by
    have h := princCorrIteratedDeriv q hsr 0 (by norm_num)
    simpa only [iteratedDeriv_zero] using h
  have hid1 := princCorrIteratedDeriv q hsr 1 (by norm_num)
  have hid2 := princCorrIteratedDeriv q hsr 2 (by norm_num)
  have hn0 : ‖princCorr q s‖ ≤ Cz + 2 * S1 := by
    rw [hid0]
    calc ‖zetaCorr s - eulFac q s‖ ≤ ‖zetaCorr s‖ + ‖eulFac q s‖ := norm_sub_le _ _
      _ ≤ Cz + 2 * S1 := by linarith only [hz0, he0]
  have hn1 : ‖iteratedDeriv 1 (princCorr q) s‖ ≤ Cz + 4 * S2 := by
    rw [hid1]
    calc ‖iteratedDeriv 1 zetaCorr s - iteratedDeriv 1 (eulFac q) s‖
          ≤ ‖iteratedDeriv 1 zetaCorr s‖ + ‖iteratedDeriv 1 (eulFac q) s‖ := norm_sub_le _ _
      _ ≤ Cz + 4 * S2 := by linarith only [hz1, he1]
  have hn2 : ‖iteratedDeriv 2 (princCorr q) s‖ ≤ Cz + 16 * S3 := by
    rw [hid2]
    calc ‖iteratedDeriv 2 zetaCorr s - iteratedDeriv 2 (eulFac q) s‖
          ≤ ‖iteratedDeriv 2 zetaCorr s‖ + ‖iteratedDeriv 2 (eulFac q) s‖ := norm_sub_le _ _
      _ ≤ Cz + 16 * S3 := by linarith only [hz2, he2]
  set c : ℝ := (a + lam₁) / L with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg hα0 (le_of_lt hLpos)
  have hc2a : c ≤ 2 * a := by
    rw [hc]
    have h1 : (a + lam₁) / L ≤ 2 * a / L :=
      div_le_div_of_nonneg_right hα2a (le_of_lt hLpos)
    have h2 : 2 * a / L ≤ 2 * a := by
      rw [div_le_iff₀ hLpos]; exact le_mul_of_one_le_right (by linarith only [ha]) hL1
    linarith
  have ht0 : (0 : ℝ) ≤ (Real.log L) ^ 4 := by positivity
  have hD1'0 : 0 < max D1 1 := lt_of_lt_of_le one_pos (le_max_right D1 1)
  have hD2'0 : 0 < max D2 1 := lt_of_lt_of_le one_pos (le_max_right D2 1)
  have hD3'0 : 0 < max D3 1 := lt_of_lt_of_le one_pos (le_max_right D3 1)
  set K1 : ℝ := Cz + 2 * (max D1 1 * (1 + (Real.log L) ^ 4)) with hK1def
  set K2 : ℝ := Cz + 4 * (max D2 1 * (1 + (Real.log L) ^ 4)) with hK2def
  set K3 : ℝ := Cz + 16 * (max D3 1 * (1 + (Real.log L) ^ 4)) with hK3def
  have hK10 : (0 : ℝ) ≤ K1 := by
    rw [hK1def]
    exact add_nonneg hCzpos.le (mul_nonneg (by norm_num) (mul_nonneg hD1'0.le (by positivity)))
  have hK20 : (0 : ℝ) ≤ K2 := by
    rw [hK2def]
    exact add_nonneg hCzpos.le (mul_nonneg (by norm_num) (mul_nonneg hD2'0.le (by positivity)))
  have hK30 : (0 : ℝ) ≤ K3 := by
    rw [hK3def]
    exact add_nonneg hCzpos.le (mul_nonneg (by norm_num) (mul_nonneg hD3'0.le (by positivity)))
  have hcorr : c * (princCorr q s).re - c ^ 2 * (iteratedDeriv 1 (princCorr q) s).re
      + (1 / 3) * c ^ 3 * (iteratedDeriv 2 (princCorr q) s).re ≤ (a + lam₁) * e := by
    have tA : c * (princCorr q s).re - c ^ 2 * (iteratedDeriv 1 (princCorr q) s).re
        + (1 / 3) * c ^ 3 * (iteratedDeriv 2 (princCorr q) s).re
        ≤ c * (Cz + 2 * S1) + c ^ 2 * (Cz + 4 * S2) + (1 / 3) * c ^ 3 * (Cz + 16 * S3) := by
      have h1 : c * (princCorr q s).re ≤ c * (Cz + 2 * S1) :=
        mul_le_mul_of_nonneg_left (le_trans (Complex.re_le_norm (princCorr q s)) hn0) hc0
      have h2 : -c ^ 2 * (iteratedDeriv 1 (princCorr q) s).re ≤ c ^ 2 * (Cz + 4 * S2) := by
        have hh : -(iteratedDeriv 1 (princCorr q) s).re ≤ Cz + 4 * S2 :=
          le_trans (neg_le_abs _) (le_trans (abs_re_le_norm _) hn1)
        have := mul_le_mul_of_nonneg_left hh (sq_nonneg c)
        linarith only [this]
      have h3 : (1 / 3) * c ^ 3 * (iteratedDeriv 2 (princCorr q) s).re
          ≤ (1 / 3) * c ^ 3 * (Cz + 16 * S3) :=
        mul_le_mul_of_nonneg_left
          (le_trans (Complex.re_le_norm (iteratedDeriv 2 (princCorr q) s)) hn2)
          (mul_nonneg (by norm_num) (pow_nonneg hc0 3))
      linarith only [h1, h2, h3]
    have tB : c * (Cz + 2 * S1) + c ^ 2 * (Cz + 4 * S2) + (1 / 3) * c ^ 3 * (Cz + 16 * S3)
        ≤ c * (K1 + 2 * a * K2 + (4 * a ^ 2 / 3) * K3) := by
      have e1 : Cz + 2 * S1 ≤ K1 := by rw [hK1def]; linarith
      have e2 : Cz + 4 * S2 ≤ K2 := by rw [hK2def]; linarith
      have e3 : Cz + 16 * S3 ≤ K3 := by rw [hK3def]; linarith
      have g1 : c * (Cz + 2 * S1) ≤ c * K1 := mul_le_mul_of_nonneg_left e1 hc0
      have g2 : c ^ 2 * (Cz + 4 * S2) ≤ c * (2 * a * K2) := by
        have hle : c ^ 2 ≤ c * (2 * a) := by rw [sq]; exact mul_le_mul_of_nonneg_left hc2a hc0
        calc c ^ 2 * (Cz + 4 * S2) ≤ c ^ 2 * K2 := mul_le_mul_of_nonneg_left e2 (sq_nonneg c)
          _ ≤ c * (2 * a) * K2 := mul_le_mul_of_nonneg_right hle hK20
          _ = c * (2 * a * K2) := by ring
      have g3 : (1 / 3) * c ^ 3 * (Cz + 16 * S3) ≤ c * ((4 * a ^ 2 / 3) * K3) := by
        have hle : c ^ 3 ≤ c * (2 * a) ^ 2 := by
          have hsq : c ^ 2 ≤ (2 * a) ^ 2 := pow_le_pow_left₀ hc0 hc2a 2
          have := mul_le_mul_of_nonneg_left hsq hc0
          linarith only [this]
        calc (1 / 3) * c ^ 3 * (Cz + 16 * S3) ≤ (1 / 3) * c ^ 3 * K3 :=
              mul_le_mul_of_nonneg_left e3 (mul_nonneg (by norm_num) (pow_nonneg hc0 3))
          _ ≤ (1 / 3) * (c * (2 * a) ^ 2) * K3 := by
            have := mul_le_mul_of_nonneg_right hle hK30
            linarith only [this]
          _ = c * ((4 * a ^ 2 / 3) * K3) := by ring
      linarith only [g1, g2, g3]
    have hCbound : K1 + 2 * a * K2 + (4 * a ^ 2 / 3) * K3 ≤ e * L := by
      have h := hL₀b hL₀L
      rw [hK1def, hK2def, hK3def]
      linarith [h]
    have hfinal : c * (K1 + 2 * a * K2 + (4 * a ^ 2 / 3) * K3) ≤ c * (e * L) :=
      mul_le_mul_of_nonneg_left hCbound hc0
    have hce : c * (e * L) = (a + lam₁) * e := by
      rw [hc]; field_simp
    linarith only [tA, tB, hfinal, hce.le, hce.ge]
  have hpole := sigP3PoleExtraction q (L := L) (a := a) (lam₁ := lam₁) (s := s) hsr
  rw [hpole]
  linarith [hcorr]

end Work.ZeroFreeTables.lam0w
