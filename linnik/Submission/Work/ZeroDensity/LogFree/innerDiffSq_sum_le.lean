import Mathlib
import Submission.Work.ZeroDensity.LogFree.PoleDefs
import Submission.Commons.Algebra.BigOperators.sum_Icc_filter_dvd
import Submission.Commons.Analysis.SpecialFunctions.Harmonic.harmonic_log_bounds

/-!
# `Work.ZeroDensity.LogFree.innerDiffSq_sum_le`

The perturbation of the diagonalized pole residue is `O(1/W^2)`: with `z = ⌈W⌉₊`,

  `Σ_{l ≤ z} φ(l)·(innerP W l - innerB z l)^2 ≤ (log(z/W))^2 · (1 + log z)^3`,

where `innerP` uses the real cut-off `W` and `innerB` the integer cut-off `z`.  The pointwise
input is `|thetaL W d - selLam z d| ≤ log(z/W)` (`thetaL_sub_selLam_abs_le`), whence
`|innerP W l - innerB z l| ≤ log(z/W)·Σ_{l∣d≤z}1/d ≤ log(z/W)·(1+log z)/l`; summing against
`φ(l) ≤ l` and `Σ_{l≤z}1/l ≤ 1 + log z` gives the claim.
-/

open scoped BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

theorem innerDiffSq_sum_le (W : ℝ) (hW : 1 < W) :
    (∑ l ∈ Finset.Icc 1 ⌈W⌉₊, (Nat.totient l : ℝ)
        * (Work.ZeroDensity.LogFree.innerP W l - Work.ZeroDensity.LogFree.innerB ⌈W⌉₊ l) ^ 2)
      ≤ (Real.log ((⌈W⌉₊ : ℝ) / W)) ^ 2 * (1 + Real.log (⌈W⌉₊ : ℝ)) ^ 3 := by
  have hWpos : 0 < W := by linarith
  have hzpos : 0 < ⌈W⌉₊ := Nat.ceil_pos.mpr hWpos
  have hzge : W ≤ ((⌈W⌉₊ : ℕ) : ℝ) := Nat.le_ceil W
  have hz1 : (1 : ℝ) ≤ ((⌈W⌉₊ : ℕ) : ℝ) := by exact_mod_cast hzpos
  have hlogz0 : 0 ≤ Real.log (((⌈W⌉₊ : ℕ)) : ℝ) := Real.log_nonneg hz1
  have hratio0 : 0 ≤ Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W) :=
    Real.log_nonneg (by rw [le_div_iff₀ hWpos, one_mul]; exact hzge)
  have hH : ∀ m : ℕ, 1 ≤ m →
      (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log ((m : ℕ) : ℝ) :=
    fun m hm => (Commons.Analysis.SpecialFunctions.Harmonic.harmonic_log_bounds).2.1 m hm
  -- the pointwise `l`-bound on the difference of the inner sums
  have hkey : ∀ l ∈ Finset.Icc 1 ⌈W⌉₊,
      (Work.ZeroDensity.LogFree.innerP W l - Work.ZeroDensity.LogFree.innerB ⌈W⌉₊ l) ^ 2
        ≤ (Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W)) ^ 2
            * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) ^ 2 * (1 / (l : ℝ)) ^ 2 := by
    intro l hl
    have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
    have hlz : l ≤ ⌈W⌉₊ := (Finset.mem_Icc.mp hl).2
    have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl1
    have hdiff : Work.ZeroDensity.LogFree.innerP W l - Work.ZeroDensity.LogFree.innerB ⌈W⌉₊ l
        = ∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d),
            (thetaL W d - Work.LinnikAreas.Density4.selLam ⌈W⌉₊ d) / (d : ℝ) := by
      rw [innerP, innerB, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d _
      ring
    have hharm : (∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d), (1 : ℝ) / (d : ℝ))
        ≤ (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) * (1 / (l : ℝ)) := by
      rw [Commons.Algebra.BigOperators.sum_Icc_filter_dvd l ⌈W⌉₊ (fun i => (1 : ℝ) / (i : ℝ))]
      have hterm : ∀ k ∈ Finset.Icc 1 (⌈W⌉₊ / l),
          (1 : ℝ) / (((l * k : ℕ)) : ℝ) = (1 / (l : ℝ)) * ((1 : ℝ) / (k : ℝ)) := by
        intro k _
        push_cast
        field_simp
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have hzdl1 : 1 ≤ ⌈W⌉₊ / l := (Nat.one_le_div_iff (by omega : 0 < l)).mpr hlz
      have hb := hH (⌈W⌉₊ / l) hzdl1
      have hlogle : Real.log (((⌈W⌉₊ / l : ℕ)) : ℝ) ≤ Real.log (((⌈W⌉₊ : ℕ)) : ℝ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast Nat.div_le_self ⌈W⌉₊ l
      have hb' : (∑ k ∈ Finset.Icc 1 (⌈W⌉₊ / l), (1 : ℝ) / (k : ℝ))
          ≤ 1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ) := by linarith
      calc (1 / (l : ℝ)) * (∑ k ∈ Finset.Icc 1 (⌈W⌉₊ / l), (1 : ℝ) / (k : ℝ))
          ≤ (1 / (l : ℝ)) * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) :=
            mul_le_mul_of_nonneg_left hb' (by positivity)
        _ = (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) * (1 / (l : ℝ)) := by ring
    have hpt : |∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d),
          (thetaL W d - Work.LinnikAreas.Density4.selLam ⌈W⌉₊ d) / (d : ℝ)|
        ≤ Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W) * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ))
            * (1 / (l : ℝ)) := by
      have hterm2 : ∀ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d),
          |(thetaL W d - Work.LinnikAreas.Density4.selLam ⌈W⌉₊ d) / (d : ℝ)|
            ≤ Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W) * ((1 : ℝ) / (d : ℝ)) := by
        intro d hd
        have hdmem : d ∈ Finset.Icc 1 ⌈W⌉₊ := (Finset.mem_filter.mp hd).1
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
        have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        rw [abs_div, abs_of_pos hdpos]
        have hb := thetaL_sub_selLam_abs_le hW hdmem
        rw [div_le_iff₀ hdpos]
        calc |thetaL W d - Work.LinnikAreas.Density4.selLam ⌈W⌉₊ d|
            ≤ Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W) := hb
          _ = Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W) * ((1 : ℝ) / (d : ℝ)) * (d : ℝ) := by
              field_simp
      calc |∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d),
              (thetaL W d - Work.LinnikAreas.Density4.selLam ⌈W⌉₊ d) / (d : ℝ)|
          ≤ ∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d),
              |(thetaL W d - Work.LinnikAreas.Density4.selLam ⌈W⌉₊ d) / (d : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d),
              Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W) * ((1 : ℝ) / (d : ℝ)) :=
            Finset.sum_le_sum hterm2
        _ = Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W)
              * (∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d), (1 : ℝ) / (d : ℝ)) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W) * ((1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) * (1 / (l : ℝ))) :=
            mul_le_mul_of_nonneg_left hharm hratio0
        _ = Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W) * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ))
              * (1 / (l : ℝ)) := by ring
    rw [hdiff]
    calc (∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d),
            (thetaL W d - Work.LinnikAreas.Density4.selLam ⌈W⌉₊ d) / (d : ℝ)) ^ 2
        = |∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d),
            (thetaL W d - Work.LinnikAreas.Density4.selLam ⌈W⌉₊ d) / (d : ℝ)| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W) * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ))
            * (1 / (l : ℝ))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hpt 2
      _ = (Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W)) ^ 2
            * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) ^ 2 * (1 / (l : ℝ)) ^ 2 := by ring
  -- sum the pointwise bounds
  have hterm3 : ∀ l ∈ Finset.Icc 1 ⌈W⌉₊,
      (Nat.totient l : ℝ)
        * (Work.ZeroDensity.LogFree.innerP W l - Work.ZeroDensity.LogFree.innerB ⌈W⌉₊ l) ^ 2
        ≤ (Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W)) ^ 2 * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) ^ 2
            * (1 / (l : ℝ)) := by
    intro l hl
    have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
    have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl1
    have hphi : (Nat.totient l : ℝ) ≤ (l : ℝ) := by exact_mod_cast Nat.totient_le l
    have hkeyl := hkey l hl
    have hphi2 : (Nat.totient l : ℝ) * (1 / (l : ℝ)) ^ 2 ≤ 1 / (l : ℝ) := by
      have h1 : (Nat.totient l : ℝ) * (1 / (l : ℝ)) ^ 2 ≤ (l : ℝ) * (1 / (l : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hphi (by positivity)
      have h2 : (l : ℝ) * (1 / (l : ℝ)) ^ 2 = 1 / (l : ℝ) := by field_simp
      linarith
    calc (Nat.totient l : ℝ)
          * (Work.ZeroDensity.LogFree.innerP W l - Work.ZeroDensity.LogFree.innerB ⌈W⌉₊ l) ^ 2
        ≤ (Nat.totient l : ℝ)
            * ((Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W)) ^ 2
                * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) ^ 2 * (1 / (l : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hkeyl (by positivity)
      _ = (Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W)) ^ 2 * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) ^ 2
            * ((Nat.totient l : ℝ) * (1 / (l : ℝ)) ^ 2) := by ring
      _ ≤ (Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W)) ^ 2 * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) ^ 2
            * (1 / (l : ℝ)) :=
          mul_le_mul_of_nonneg_left hphi2 (by positivity)
  have hsum : (∑ l ∈ Finset.Icc 1 ⌈W⌉₊,
        (Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W)) ^ 2 * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) ^ 2
          * (1 / (l : ℝ)))
      ≤ (Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W)) ^ 2
          * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) ^ 2
          * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) := by
    rw [← Finset.mul_sum]
    have hb := hH ⌈W⌉₊ hzpos
    have : (∑ x ∈ Finset.Icc 1 ⌈W⌉₊, (1 : ℝ) / (x : ℝ))
        ≤ 1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ) := hb
    exact mul_le_mul_of_nonneg_left this (by positivity)
  calc (∑ l ∈ Finset.Icc 1 ⌈W⌉₊, (Nat.totient l : ℝ)
        * (Work.ZeroDensity.LogFree.innerP W l - Work.ZeroDensity.LogFree.innerB ⌈W⌉₊ l) ^ 2)
      ≤ ∑ l ∈ Finset.Icc 1 ⌈W⌉₊,
          (Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W)) ^ 2 * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) ^ 2
            * (1 / (l : ℝ)) := Finset.sum_le_sum hterm3
    _ ≤ (Real.log (((⌈W⌉₊ : ℕ) : ℝ) / W)) ^ 2
          * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) ^ 2
          * (1 + Real.log (((⌈W⌉₊ : ℕ)) : ℝ)) := hsum
    _ = (Real.log ((⌈W⌉₊ : ℝ) / W)) ^ 2 * (1 + Real.log (⌈W⌉₊ : ℝ)) ^ 3 := by ring

end Work.ZeroDensity.LogFree
