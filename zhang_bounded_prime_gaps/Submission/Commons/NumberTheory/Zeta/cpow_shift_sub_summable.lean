import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Filter Finset intervalIntegral
open scoped Real Topology BigOperators Interval

namespace Commons.NumberTheory.Zeta

/-- Real telescoping difference of powers: `∑ (X+m)^r - (X+m+1)^r` converges to `X^r`
for negative exponent `r`. -/
private lemma hasSum_telescope_rpow_neg (X : ℕ) (hX : 1 ≤ X) {r : ℝ} (hr : r < 0) :
    HasSum (fun m : ℕ => ((((X + m : ℕ) : ℝ) ^ r) - (((X + m + 1 : ℕ) : ℝ) ^ r)))
      ((X : ℝ) ^ r) := by
  have h_nonneg : ∀ m : ℕ, 0 ≤ (((X + m : ℕ) : ℝ) ^ r) - (((X + m + 1 : ℕ) : ℝ) ^ r) := by
    intro m
    have hbase1 : (0 : ℝ) < ((X + m : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hle : ((X + m : ℕ) : ℝ) ≤ ((X + m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hpow : (((X + m + 1 : ℕ) : ℝ) ^ r) ≤ (((X + m : ℕ) : ℝ) ^ r) := by
      exact Real.rpow_le_rpow_of_nonpos hbase1 hle (le_of_lt hr)
    exact sub_nonneg.mpr hpow
  have hto : Tendsto (fun N : ℕ => ((X + N : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ)) (g := fun N : ℕ => ((X + N : ℕ) : ℝ))
      (fun N => by exact_mod_cast (by omega : N ≤ X + N)) tendsto_natCast_atTop_atTop
  have hdec : Tendsto (fun t : ℝ => t ^ r) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (y := -r) (by linarith : 0 < -r))
  have hN0 : Tendsto (fun N : ℕ => ((X + N : ℕ) : ℝ) ^ r) atTop (𝓝 0) := hdec.comp hto
  have hmain_t :
      Tendsto (fun N : ℕ => (X : ℝ) ^ r - ((X + N : ℕ) : ℝ) ^ r) atTop (𝓝 ((X : ℝ) ^ r)) := by
    simpa using (tendsto_const_nhds.sub hN0 : Tendsto (fun N : ℕ => (X : ℝ) ^ r - ((X + N : ℕ) : ℝ) ^ r)
      atTop (𝓝 ((X : ℝ) ^ r - 0)))
  have hsumN : ∀ N : ℕ,
      (∑ m ∈ Finset.range N, ((((X + m : ℕ) : ℝ) ^ r) - (((X + m + 1 : ℕ) : ℝ) ^ r)))
        = (X : ℝ) ^ r - (((X + N : ℕ) : ℝ) ^ r) := by
    intro N
    simpa [Nat.add_assoc] using (Finset.sum_range_sub' (fun j : ℕ => (((X + j : ℕ) : ℝ) ^ r)) N)
  have hpartial : Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.range N, ((((X + m : ℕ) : ℝ) ^ r) - (((X + m + 1 : ℕ) : ℝ) ^ r)))
      atTop (𝓝 ((X : ℝ) ^ r)) := by
    exact hmain_t.congr (fun N => (hsumN N).symm)
  exact (hasSum_iff_tendsto_nat_of_nonneg h_nonneg ((X : ℝ) ^ r)).2 hpartial

/-- Norm of the cpow integrand on the positive real axis. -/
private lemma norm_cpow_sub_integrand (w : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (w - 1)‖ = x ^ (w.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx (w - 1)]
  rw [Complex.sub_re, Complex.one_re]

/-- Difference of successive complex powers is the integral of the derivative. -/
private lemma cpow_succ_sub_eq_smul_integral (k : ℕ) (hk : 1 ≤ k) (w : ℂ) (hw : w.re < 0) :
    ((((k + 1 : ℕ) : ℂ) ^ w) - ((k : ℕ) : ℂ) ^ w)
      = w * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (w - 1)) := by
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hnot0 : 0 ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro hx
    have hx' : (0 : ℝ) ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
      simpa [Set.uIcc_of_le hkle] using hx
    linarith [hx'.1, show (0 : ℝ) < (k : ℝ) by exact_mod_cast (by omega : 0 < k)]
  have hw0 : w ≠ 0 := by
    intro h
    simp [h] at hw
  have hwne1 : w - 1 ≠ (-1 : ℂ) := by
    intro hh
    apply hw0
    calc
      w = (w - 1) + 1 := by ring
      _ = -1 + 1 := by rw [hh]
      _ = 0 := by ring
  have hint := integral_cpow (r := w - 1) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ))
    (Or.inr ⟨hwne1, hnot0⟩)
  have hw1 : w - 1 + 1 = w := by ring
  have hinteq : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (w - 1))
      = ((((k + 1 : ℕ) : ℂ) ^ w - ((k : ℕ) : ℂ) ^ w)) / w := by
    rw [hint, hw1]
    norm_cast
  have hmain : w * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (w - 1))
      = (((k + 1 : ℕ) : ℂ) ^ w) - ((k : ℕ) : ℂ) ^ w := by
    rw [hinteq]
    field_simp [hw0]
  exact hmain.symm

/-- Integral of the norm of the cpow integrand over `[k, k+1]`. -/
private lemma integral_norm_cpow_sub (k : ℕ) (hk : 1 ≤ k) (w : ℂ) (hw : w.re < 0) :
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (w - 1)‖)
      = (((k + 1 : ℕ) : ℝ) ^ (w.re) - (k : ℝ) ^ (w.re)) / w.re := by
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  calc
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (w - 1)‖)
        = ∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (w.re - 1) := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hx' : x ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
              simpa [Set.uIcc_of_le hkle] using hx
            have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast (by omega : 0 < k)) hx'.1
            exact norm_cpow_sub_integrand w hx0
    _ = (((k + 1 : ℕ) : ℝ) ^ (w.re) - (k : ℝ) ^ (w.re)) / w.re := by
      have hnot0 : 0 ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
        intro hx
        have hx' : (0 : ℝ) ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
          simpa [Set.uIcc_of_le hkle] using hx
        linarith [hx'.1, show (0 : ℝ) < (k : ℝ) by exact_mod_cast (by omega : 0 < k)]
      have hne : w.re - 1 ≠ (-1 : ℝ) := by linarith
      have hint := integral_rpow (r := w.re - 1) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ))
        (Or.inr ⟨hne, hnot0⟩)
      rw [hint]
      have hD : w.re - 1 + 1 = w.re := by ring
      rw [hD]

/-- Bound on the norm of the difference of successive complex powers by the telescoping
real power difference. -/
private lemma norm_cpow_succ_sub_le (k : ℕ) (hk : 1 ≤ k) (w : ℂ) (hw : w.re < 0) :
    ‖(((k + 1 : ℕ) : ℂ) ^ w) - ((k : ℕ) : ℂ) ^ w‖
      ≤ (‖w‖ / (-w.re)) * (((k : ℝ) ^ w.re) - (((k + 1 : ℕ) : ℝ) ^ w.re)) := by
  have hsub := cpow_succ_sub_eq_smul_integral k hk w hw
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  calc
    ‖(((k + 1 : ℕ) : ℂ) ^ w) - ((k : ℕ) : ℂ) ^ w‖
        = ‖w * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (w - 1))‖ := by
            rw [hsub]
    _ ≤ ‖w‖ * ‖(∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (w - 1))‖ := norm_mul_le _ _
    _ ≤ ‖w‖ * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (w - 1)‖) := by
            exact mul_le_mul_of_nonneg_left
              (intervalIntegral.norm_integral_le_integral_norm hkle) (norm_nonneg w)
    _ = (‖w‖ / (-w.re)) * (((k : ℝ) ^ w.re) - (((k + 1 : ℕ) : ℝ) ^ w.re)) := by
            rw [integral_norm_cpow_sub k hk w hw]
            have hrne : w.re ≠ 0 := by linarith
            field_simp [hrne]
            ring

theorem cpow_shift_sub_summable {w : ℂ} {N : ℕ} (hN : 1 ≤ N) (hw : w.re < 0) :
    Summable (fun m : ℕ => ((((N + m + 1 : ℕ) : ℂ) ^ w) - (((N + m : ℕ) : ℂ) ^ w))) := by
  let C : ℝ := ‖w‖ / (-w.re)
  let g : ℕ → ℝ := fun m : ℕ =>
      ((((N + m : ℕ) : ℝ) ^ w.re) - (((N + m + 1 : ℕ) : ℝ) ^ w.re))
  have hg0 : Summable g := by
    exact (hasSum_telescope_rpow_neg N hN hw).summable
  have hC : Summable (fun m : ℕ => C * g m) := hg0.mul_left C
  refine Summable.of_norm_bounded
    (f := fun m : ℕ => ((((N + m + 1 : ℕ) : ℂ) ^ w) - (((N + m : ℕ) : ℂ) ^ w)))
    (g := fun m : ℕ => C * g m) hC ?_
  intro m
  have hk : 1 ≤ N + m := by omega
  have hb := norm_cpow_succ_sub_le (k := N + m) hk w hw
  dsimp [C, g] at hb ⊢
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb

end Commons.NumberTheory.Zeta