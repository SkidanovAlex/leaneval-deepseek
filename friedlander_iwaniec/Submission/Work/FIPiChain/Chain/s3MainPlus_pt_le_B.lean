import Mathlib
import Submission.Work.FIPiChain.HasB
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.s3RemPlus_defs
import Submission.Work.FIChain.mu_gtil_interval_le
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Commons.NumberTheory.Sieve.sieve_mu_sum_coprime_powLog
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.zc_sharp_bounds
import Submission.Work.FIChain.S3plusC_machinery
import Submission.Work.FIChain.s3MainLevelDefs
import Submission.Work.FIChain.s3MainPlus_eq_levelSum
import Submission.Work.FIChain.s3LevelWindow_sum_le
import Submission.Work.FIChain.s3Density_sum_le
import Submission.Work.FIChain.s3MainLevelSum_le

open Work.FIChain

namespace Work.FIPiChain

variable [HasBc]

/-! ## The main (`(1.7)`) half of the `λ⁺` sum, pointwise in `(y,z)` (companion's (8.3))

`s3MainPlus lam x z sy sz Cm` (defined in `Submission.Work.FIChain.s3RemPlus_defs`) is the
`g(d)·A(L)`-part of the companion's (8.2) split of the `λ⁺` inner sum
(`Work.FIChain.S3plusC = s3MainPlus + s3RemPlus`, `Work.FIChain.S3plusC_eq_main_add_rem`, PROVED).
This is the companion's (8.3), POINTWISE in `(y,z)` on the windows
`z ∈ Icc (zc x B) (e·zc x B)`, `y ∈ Icc (Yc x B) (e·Yc x B)`, with `Cm = ⌊(zc x B)^{1-η}⌋₊`.

The proof goes through the *level sum* `K(n) = Work.FIChain.s3MainLevelSum` of
`Submission.Work.FIChain.s3MainLevelDefs`:

* `Work.FIChain.s3MainPlus_eq_levelSum` — the reindexing
  `s3MainPlus lam x z sy sz Cm = Σ_{n ∈ Icc 1 x} ã(n)·K(n)`
  (un-merge `ℓ = e·b`, write `Ã(m₁) − Ã(m₂) = Σ_{m₂ < n ≤ m₁} ã(n)`, swap the `n`-sum out of the
  `u`-integral);
* `Work.FIChain.s3MainLevelSum_le` — the analytic core `|K(n)| ≤ C(log x)^{-1}`, uniformly in
  `n ≤ x` (the sieve estimate `(2.4)` on the `b`-window, then the `g̃`-density counting);
* the triangle inequality `|Σ_n ã(n)K(n)| ≤ Σ_n ã(n)|K(n)| ≤ Ã(x)·C(log x)^{-1}`, using
  `ã ≥ 0` (`Work.FIChain.atilc_nonneg`) and `Σ_{n ≤ x}ã(n) = Ã(x)`
  (`Work.FIChain.sum_atilc_Icc_eq`). -/
theorem s3MainPlus_pt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ) →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        Work.FIChain.SieveInput Submission.ASP.FIgtil (Work.FIChain.Deltac x) lam C_sieve →
      ∀ z : ℝ, z ∈ Set.Icc (Work.FIChain.zc x B) (Real.exp 1 * Work.FIChain.zc x B) →
      ∀ y : ℝ, y ∈ Set.Icc (Work.FIChain.Yc x B) (Real.exp 1 * Work.FIChain.Yc x B) →
        |Work.FIChain.s3MainPlus lam x z (Work.FIChain.sc x B * y) (Work.FIChain.sc x B * z)
          (⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊)|
          ≤ C * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by
  obtain ⟨Cw, hCwpos, hW⟩ := Work.FIChain.s3LevelWindow_sum_le
  obtain ⟨Cd, hCdpos, hD⟩ := Work.FIChain.s3Density_sum_le
  obtain ⟨C₀, hC₀pos, hlev⟩ := Work.FIChain.s3MainLevelSum_le Cw hCwpos hW Cd hCdpos hD
  refine ⟨C₀, hC₀pos, fun B hB => ?_⟩
  obtain ⟨x₁, h₁⟩ := hlev B hB
  obtain ⟨x₂, h₂⟩ := Filter.eventually_atTop.mp (Work.FIChain.scale_factsC B hB)
  refine ⟨max x₁ x₂ + 16, fun x hx hYcHyp lam C_sieve hSi z hz y hy => ?_⟩
  have hx₁ : x₁ ≤ x := by omega
  have hx₂ : x₂ ≤ x := by omega
  have hx2 : 2 ≤ x := by omega
  have hx1 : 1 ≤ x := by omega
  obtain ⟨hYcF256, -, -, -, -, -, -, hDelLtZc, hZcLeX, hZc1, -, -, -, -, -, -⟩ := h₂ x hx₂
  set Cm : ℕ := ⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ with hCmdef
  -- the side conditions of the reindexing
  have hzc1 : (1 : ℝ) ≤ Work.FIChain.zc x B := by
    have hZ : (1 : ℝ) ≤ (Work.FIChain.Zc x B : ℝ) := by exact_mod_cast hZc1
    simpa [Work.FIChain.zc] using hZ
  have hzcpos : 0 < Work.FIChain.zc x B := lt_of_lt_of_le zero_lt_one hzc1
  have hz1 : 1 ≤ z := le_trans hzc1 hz.1
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hsc1 : (1 : ℝ) ≤ Work.FIChain.sc x B := by
    rw [Work.FIChain.sc]; exact one_le_pow₀ (by norm_num)
  have hscpos : 0 < Work.FIChain.sc x B := lt_of_lt_of_le zero_lt_one hsc1
  have hCm1 : 1 ≤ Cm := by
    rw [hCmdef]
    refine Nat.le_floor ?_
    have h0 : (0 : ℝ) < 1 - Work.FIChain.etac := by norm_num [Work.FIChain.etac]
    have h1 : (1 : ℝ) ≤ (Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac) :=
      Real.one_le_rpow hzc1 h0.le
    simpa using h1
  have hCmR : (1 : ℝ) ≤ (Cm : ℝ) := by exact_mod_cast hCm1
  have hCmposR : (0 : ℝ) < (Cm : ℝ) := by linarith
  have hCmle : (Cm : ℝ) ≤ Work.FIChain.zc x B := by
    have h1 : (Cm : ℝ) ≤ (Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac) := by
      rw [hCmdef]
      exact Nat.floor_le (Real.rpow_nonneg hzcpos.le _)
    have h2 : (Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac) ≤ Work.FIChain.zc x B :=
      Real.rpow_le_self_of_one_le hzc1 (by norm_num [Work.FIChain.etac])
    linarith
  have hCmz : (Cm : ℝ) ≤ z := le_trans hCmle hz.1
  have hsz1 : 1 ≤ Work.FIChain.sc x B * z := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Work.FIChain.sc x B * z := mul_le_mul hsc1 hz1 zero_le_one (le_of_lt hscpos)
  have hzsz : z ≤ Work.FIChain.sc x B * z := le_mul_of_one_le_left hzpos.le hsc1
  have hCmsz : (Cm : ℝ) ≤ Work.FIChain.sc x B * z := le_trans hCmz hzsz
  -- the reindexing
  rw [Work.FIChain.s3MainPlus_eq_levelSum lam x z (Work.FIChain.sc x B * y)
    (Work.FIChain.sc x B * z) Cm hx1 hCm1 hz1 hzsz hCmsz hCmz]
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hLnn : 0 ≤ Real.log (x : ℝ) := le_of_lt hLpos
  have hstep : ∀ n ∈ Finset.Icc 1 x,
      |Work.FIChain.s3MainLevelSum lam x z (Work.FIChain.sc x B * z) Cm
        (Work.FIChain.sc x B * y) n| ≤ C₀ * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) :=
    fun n hn => h₁ x hx₁ hYcHyp lam C_sieve hSi z hz y hy n (Finset.mem_Icc.mp hn).2
  calc |∑ n ∈ Finset.Icc 1 x, Work.FIChain.atilc n
        * Work.FIChain.s3MainLevelSum lam x z (Work.FIChain.sc x B * z) Cm
            (Work.FIChain.sc x B * y) n|
      ≤ ∑ n ∈ Finset.Icc 1 x, |Work.FIChain.atilc n
          * Work.FIChain.s3MainLevelSum lam x z (Work.FIChain.sc x B * z) Cm
              (Work.FIChain.sc x B * y) n| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ Finset.Icc 1 x, Work.FIChain.atilc n
          * |Work.FIChain.s3MainLevelSum lam x z (Work.FIChain.sc x B * z) Cm
              (Work.FIChain.sc x B * y) n| := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [abs_mul, abs_of_nonneg (Work.FIChain.atilc_nonneg n)]
    _ ≤ ∑ n ∈ Finset.Icc 1 x, Work.FIChain.atilc n * (C₀ * (Real.log (x : ℝ)) ^ (-(1 : ℤ))) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          exact mul_le_mul_of_nonneg_left (hstep n hn) (Work.FIChain.atilc_nonneg n)
    _ = (∑ n ∈ Finset.Icc 1 x, Work.FIChain.atilc n) * (C₀ * (Real.log (x : ℝ)) ^ (-(1 : ℤ))) :=
          (Finset.sum_mul _ _ _).symm
    _ = Work.FIChain.AcountAtilC x * (C₀ * (Real.log (x : ℝ)) ^ (-(1 : ℤ))) := by
          rw [Work.FIChain.sum_atilc_Icc_eq]
    _ = C₀ * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by ring

end Work.FIPiChain
