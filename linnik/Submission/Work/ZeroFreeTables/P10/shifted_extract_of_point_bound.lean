import Mathlib
import Submission.Work.ZeroFreeTables.P9.nearP3sum_ge_kept
import Submission.Work.ZeroFreeTables.P9.P3NearSumL_eq_nearP3sum

namespace Work.ZeroFreeTables.P10

open scoped Classical BigOperators

/-- Extraction of a single zero `ρ` (with `|Im ρ| ≤ 10`, `Re ρ = 1 - lam/L`) from the
`P₃`-near-zero sum: the point bound `hm` on `Σ`, combined with the single-point
extraction `nearP3sum_ge_kept` (applied to `T = {ρ}`) and the identification
`P3NearSumL = nearP3sum`, gives the `Σ`-bound in terms of the `P₃`-term at the
shifted argument `(a+λ₁)/((a+λ) + (τ-ρ.im)L·i)`. -/
theorem shifted_extract_of_point_bound {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    {a δ c e lam1 lam L τ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hL : 0 < L) (ha : 0 < a)
    (hlam1 : 0 ≤ lam1) (hlam : 0 ≤ lam) (haδ : 2 * a ≤ δ * L) (hτ : |τ| ≤ 3)
    {ρ : ℂ} (hzero : Work.LinnikContract.zeroMult chi ρ ≠ 0) (him : |ρ.im| ≤ 10)
    (hre : ρ.re = 1 - lam / L)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult chi u ≠ 0 → |u.im| ≤ 10 →
      lam1 ≤ (1 - u.re) * L)
    (hm : Work.ZeroFreeTables.SigmaP3L N L chi
        (((1 + a / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I) a lam1
      ≤ -Work.ZeroFreeTables.P3NearSumL N L chi
          (((1 + a / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I) a lam1 δ
        + (a + lam1) * (c + e)) :
    Work.ZeroFreeTables.SigmaP3L N L chi
        (((1 + a / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I) a lam1
      ≤ -(Work.ZeroFreeTables.P3
            ((a + lam1) / (((a + lam : ℝ) : ℂ)
              + (((τ - ρ.im) * L : ℝ) : ℂ) * Complex.I))).re
        + 8 * (a + lam1) / (δ * L) + (a + lam1) * (c + e) := by
  classical
  set s : ℂ := ((1 + a / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I with hs
  have hsre : s.re = 1 + a / L := by simp [hs]
  have hsim : |s.im| ≤ 3 := by
    have h : s.im = τ := by simp [hs]
    rw [h]; exact hτ
  -- the finite set `T = {ρ}` of zeros to extract
  have hT : ∀ u ∈ ({ρ} : Finset ℂ), Work.LinnikContract.zeroMult chi u ≠ 0 := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    rw [hu]; exact hzero
  have hTim : ∀ u ∈ ({ρ} : Finset ℂ), |u.im| ≤ 10 := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    rw [hu]; exact him
  have hkey := Work.ZeroFreeTables.P9.nearP3sum_ge_kept chi hchi hL ha hlam1 hδ hδ1 haδ
    hsre hsim hmin ({ρ} : Finset ℂ) hT hTim
  rw [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] at hkey
  -- the two `P₃`-arguments agree
  have harg : (a + lam1) / ((s - ρ) * (L : ℂ))
      = (a + lam1) / (((a + lam : ℝ) : ℂ)
          + (((τ - ρ.im) * L : ℝ) : ℂ) * Complex.I) := by
    congr 1
    have hρ : ρ = ((1 - lam / L : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I := by
      rw [← Complex.re_add_im ρ, hre]
      simp
    have hLne : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL
    conv_lhs => rw [hs, hρ]
    push_cast
    field_simp
    ring
  have hPtTgt : (Work.ZeroFreeTables.P3 ((a + lam1) / ((s - ρ) * (L : ℂ)))).re
      = (Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam : ℝ) : ℂ)
          + (((τ - ρ.im) * L : ℝ) : ℂ) * Complex.I))).re := by
    rw [harg]
  -- `P3NearSumL` is `nearP3sum`
  have hnear : Work.ZeroFreeTables.P3NearSumL N L chi s a lam1 δ
      = Work.ZeroFreeTables.P9.nearP3sum N L chi s a lam1 δ :=
    Work.ZeroFreeTables.P9.P3NearSumL_eq_nearP3sum (s := s) chi hchi hprim hδ hδ1.le a lam1 L
  have h1 : -Work.ZeroFreeTables.P9.nearP3sum N L chi s a lam1 δ
      ≤ -(Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam : ℝ) : ℂ)
            + (((τ - ρ.im) * L : ℝ) : ℂ) * Complex.I))).re
        + 8 * (a + lam1) / (δ * L) := by
    rw [← hPtTgt]
    linarith [hkey]
  rw [hnear] at hm
  linarith [hm, h1]

end Work.ZeroFreeTables.P10
