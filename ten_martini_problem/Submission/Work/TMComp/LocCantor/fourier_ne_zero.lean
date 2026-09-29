import Mathlib
import Submission.Work.TMComp.LocCantor.Defs

/-!
# Nonvanishing of the Fourier transform of an exponentially decaying sequence

Let `u : ℤ → ℂ` be a nonzero sequence with exponential decay (`ExpDecay`: `‖u n‖ ≤ C e^{-c|n|}`,
`c > 0`).  Then its Fourier transform `U(x) = ∑'_n u n e^{2πinx}` (`Work.TMComp.fourier u`) is a
nonzero function.

The proof is Fourier inversion.  Since `∑_n ‖u n‖ < ∞`, the defining series can be integrated
term by term over one period (`intervalIntegral.hasSum_intervalIntegral_of_summable_norm`,
dominated convergence with the summable bound `‖u n‖`), and the orthogonality of the exponentials
`∫_0^1 e^{2πikx} dx = δ_{k0}` (`integral_fourierMode`) gives, for every `m : ℤ`,

`∫_0^1 U(x) · e^{-2πimx} dx = u m`.

Hence `U ≡ 0` forces `u m = 0` for every `m`, i.e. `u = 0`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Filter Topology Set

namespace Work.TMComp.LocCantor

/-- The `k`-th Fourier mode `x ↦ e^{2πikx}`, as a continuous function on `ℝ`. -/
def fourierMode (k : ℤ) : C(ℝ, ℂ) :=
  ⟨fun x => Complex.exp (2 * Real.pi * ((k : ℝ) : ℂ) * (x : ℂ) * Complex.I), by fun_prop⟩

lemma fourierMode_apply (k : ℤ) (x : ℝ) :
    fourierMode k x = Complex.exp (2 * Real.pi * ((k : ℝ) : ℂ) * (x : ℂ) * Complex.I) := rfl

/-- The Fourier modes have modulus one. -/
lemma norm_fourierMode (k : ℤ) (x : ℝ) : ‖fourierMode k x‖ = 1 := by
  rw [fourierMode_apply, Complex.norm_exp]
  have h : (2 * Real.pi * ((k : ℝ) : ℂ) * (x : ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [h, Real.exp_zero]

/-- `∫_0^1 e^{cx} dx = 0` when `e^c = 1` and `c ≠ 0`. -/
lemma integral_exp_mul_complex_zero_one {c : ℂ} (hc : c ≠ 0) (h1 : Complex.exp c = 1) :
    (∫ x in (0 : ℝ)..1, Complex.exp (c * (x : ℂ))) = 0 := by
  rw [integral_exp_mul_complex (a := 0) (b := 1) hc]
  have hb : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
    rw [show c * ((1 : ℝ) : ℂ) = c by simp, h1]
  have ha : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by simp
  rw [hb, ha, sub_self, zero_div]

/-- Orthogonality of the Fourier modes: `∫_0^1 e^{2πikx} dx = δ_{k,0}`. -/
lemma integral_fourierMode (k : ℤ) :
    (∫ x in (0 : ℝ)..1, fourierMode k x) = if k = 0 then 1 else 0 := by
  rw [show (∫ x in (0 : ℝ)..1, fourierMode k x)
      = ∫ x in (0 : ℝ)..1, Complex.exp ((2 * Real.pi * ((k : ℝ) : ℂ) * Complex.I) * (x : ℂ)) from
    intervalIntegral.integral_congr (fun x _ => by rw [fourierMode_apply]; congr 1; ring)]
  by_cases hk : k = 0
  · subst hk
    simp
  · have hkC : ((k : ℝ) : ℂ) ≠ 0 := by
      simp only [Complex.ofReal_ne_zero]; exact_mod_cast hk
    have hpC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hc : (2 * Real.pi * ((k : ℝ) : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpC) hkC) Complex.I_ne_zero
    have he : Complex.exp (2 * Real.pi * ((k : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [show 2 * Real.pi * ((k : ℝ) : ℂ) * Complex.I
            = (k : ℂ) * (2 * ↑Real.pi * Complex.I) by push_cast; ring,
        Complex.exp_int_mul_two_pi_mul_I k]
    rw [integral_exp_mul_complex_zero_one hc he, if_neg hk]

/-- `∑_{n : ℤ} e^{-c |n|}` converges for `c > 0`. -/
lemma summable_exp_neg_abs_int_mul (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-(c * |(n : ℝ)|))) := by
  have hbase : Real.exp (-c) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hgeo : Summable (fun k : ℤ => (Real.exp (-c)) ^ k.natAbs) := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · refine (summable_geometric_of_lt_one (Real.exp_pos (-c)).le hbase).congr (fun n => ?_)
      simp [Int.natAbs_natCast]
    · refine (summable_geometric_of_lt_one (Real.exp_pos (-c)).le hbase).congr (fun n => ?_)
      simp [Int.natAbs_neg, Int.natAbs_natCast]
  refine hgeo.congr (fun k => ?_)
  rw [show -(c * |(k : ℝ)|) = (k.natAbs : ℝ) * (-c) by
        rw [← Int.cast_abs, ← Int.natCast_natAbs k, Int.cast_natCast]; ring,
      Real.exp_nat_mul]

/-- An exponentially decaying sequence is absolutely summable. -/
lemma summable_norm_of_expDecay {u : ℤ → ℂ} (h : Work.TMContract.ExpDecay u) :
    Summable fun n : ℤ => ‖u n‖ := by
  obtain ⟨c, hc, C, hC⟩ := h
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_exp_neg_abs_int_mul c hc).mul_left (max C 0))
  exact le_trans (hC n) (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_nonneg _))

/-- **Fourier inversion at one integer frequency.**  For an exponentially decaying sequence `u`,
the `m`-th Fourier coefficient of `U = fourier u` is `u m`. -/
lemma fourier_integral_eq (u : ℤ → ℂ) (hdec : Work.TMContract.ExpDecay u) (m : ℤ) :
    (∫ x in (0 : ℝ)..1,
        Work.TMComp.fourier u x * Complex.exp (-(2 * Real.pi * (m : ℝ) * x * Complex.I)))
      = u m := by
  have hsum : Summable fun n : ℤ => ‖u n‖ := summable_norm_of_expDecay hdec
  have hbound : ∀ n : ℤ,
      ‖(u n • fourierMode (n - m)).restrict
        (⟨uIcc 0 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ ≤ ‖u n‖ := by
    intro n
    rw [ContinuousMap.norm_le _ (norm_nonneg _)]
    intro x
    show ‖u n • fourierMode (n - m) (x : ℝ)‖ ≤ ‖u n‖
    rw [norm_smul, norm_fourierMode, mul_one]
  have hsumm : Summable fun n : ℤ =>
      ‖(u n • fourierMode (n - m)).restrict
        (⟨uIcc 0 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsum
  have hHasSum :=
    intervalIntegral.hasSum_intervalIntegral_of_summable_norm (a := 0) (b := 1) hsumm
  -- the integrand is the term-by-term sum of the modes
  have hcongr : (fun x : ℝ =>
        Work.TMComp.fourier u x * Complex.exp (-(2 * Real.pi * (m : ℝ) * x * Complex.I)))
      = (fun x : ℝ => ∑' n : ℤ, (u n • fourierMode (n - m)) x) := by
    funext x
    rw [Work.TMComp.fourier, ← tsum_mul_right]
    refine tsum_congr (fun n => ?_)
    simp only [ContinuousMap.smul_apply, smul_eq_mul, fourierMode_apply]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  -- each summand integrates to `if n = m then u n else 0`
  have hterm : ∀ n : ℤ,
      (∫ x in (0 : ℝ)..1, (u n • fourierMode (n - m)) x) = if n = m then u n else 0 := by
    intro n
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul, integral_fourierMode (n - m)]
    by_cases hnm : n = m
    · simp [hnm]
    · simp [hnm, sub_ne_zero.mpr hnm]
  calc (∫ x in (0 : ℝ)..1,
        Work.TMComp.fourier u x * Complex.exp (-(2 * Real.pi * (m : ℝ) * x * Complex.I)))
      = ∫ x in (0 : ℝ)..1, ∑' n : ℤ, (u n • fourierMode (n - m)) x := by rw [hcongr]
    _ = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, (u n • fourierMode (n - m)) x := hHasSum.tsum_eq.symm
    _ = ∑' n : ℤ, (if n = m then u n else 0) := tsum_congr hterm
    _ = u m := by rw [tsum_eq_single m (fun b hb => by simp [hb])]; simp

theorem fourier_ne_zero {u : ℤ → ℂ} (hdec : Work.TMContract.ExpDecay u) (hu : u ≠ 0) :
    Work.TMComp.fourier u ≠ 0 := by
  intro h
  apply hu
  funext m
  show u m = 0
  have hzero : (fun x : ℝ =>
      Work.TMComp.fourier u x * Complex.exp (-(2 * Real.pi * (m : ℝ) * x * Complex.I)))
      = fun _ => (0 : ℂ) := by
    funext x
    rw [h]
    simp
  rw [← fourier_integral_eq u hdec m, hzero]
  simp

end Work.TMComp.LocCantor
