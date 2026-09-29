import Mathlib
import Submission.Work.A14D.PureSysDefs
import Submission.Work.A14D.ppc_aux

/-!
# Area A14D — closure properties of `PolyGrowth`

`PolyGrowth f` (`Submission/Work/A14D/PureSysDefs.lean`) says that the coefficients of the
rational power series `f` grow at most polynomially.  This file records that the class is closed
under the operations out of which the objects of the pure-system identity are built:
addition, negation, multiplication, powers, `d/dX`, finite sums, and substitution of a polynomial
along the symmetrisation coordinate `y = x²/(x−1)`.  It also records the resulting absolute
summability of `evp`.
-/

open scoped BigOperators

namespace Work.A14D

open PowerSeries

theorem polyGrowth_C (c : ℚ) : PolyGrowth (PowerSeries.C c) := by
  refine ⟨‖(c : ℂ)‖, norm_nonneg _, 0, fun n => ?_⟩
  rw [pow_zero, mul_one]
  rcases eq_or_ne n 0 with h | h
  · subst h; rw [PowerSeries.coeff_C, if_pos rfl]
  · rw [PowerSeries.coeff_C, if_neg h]; simp

theorem polyGrowth_zero : PolyGrowth (0 : PowerSeries ℚ) := by
  simpa using polyGrowth_C 0

theorem polyGrowth_one : PolyGrowth (1 : PowerSeries ℚ) := by
  simpa using polyGrowth_C 1

theorem polyGrowth_neg {f : PowerSeries ℚ} (hf : PolyGrowth f) : PolyGrowth (-f) := by
  obtain ⟨C, hC, k, hb⟩ := hf
  refine ⟨C, hC, k, fun n => ?_⟩
  have hcoe : ((PowerSeries.coeff n (-f) : ℚ) : ℂ)
      = -((PowerSeries.coeff n f : ℚ) : ℂ) := by
    rw [map_neg]; push_cast; ring
  rw [hcoe, norm_neg]
  exact hb n

theorem polyGrowth_add {f g : PowerSeries ℚ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (f + g) := by
  obtain ⟨Cf, hCf, kf, hbf⟩ := hf
  obtain ⟨Cg, hCg, kg, hbg⟩ := hg
  refine ⟨Cf + Cg, by positivity, max kf kg, fun n => ?_⟩
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have h1 : ((n : ℝ) + 1) ^ kf ≤ ((n : ℝ) + 1) ^ max kf kg :=
    pow_le_pow_right₀ hone (le_max_left kf kg)
  have h2 : ((n : ℝ) + 1) ^ kg ≤ ((n : ℝ) + 1) ^ max kf kg :=
    pow_le_pow_right₀ hone (le_max_right kf kg)
  have hcoeff : ((PowerSeries.coeff n (f + g) : ℚ) : ℂ)
      = ((PowerSeries.coeff n f : ℚ) : ℂ) + ((PowerSeries.coeff n g : ℚ) : ℂ) := by
    rw [map_add]; push_cast; ring
  rw [hcoeff]
  calc ‖((PowerSeries.coeff n f : ℚ) : ℂ) + ((PowerSeries.coeff n g : ℚ) : ℂ)‖
      ≤ ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ + ‖((PowerSeries.coeff n g : ℚ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ Cf * ((n : ℝ) + 1) ^ max kf kg + Cg * ((n : ℝ) + 1) ^ max kf kg :=
        add_le_add (le_trans (hbf n) (mul_le_mul_of_nonneg_left h1 hCf))
          (le_trans (hbg n) (mul_le_mul_of_nonneg_left h2 hCg))
    _ = (Cf + Cg) * ((n : ℝ) + 1) ^ max kf kg := by ring

theorem polyGrowth_mul {f g : PowerSeries ℚ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (f * g) := by
  obtain ⟨Cf, hCf, kf, hbf⟩ := hf
  obtain ⟨Cg, hCg, kg, hbg⟩ := hg
  refine ⟨Cf * Cg, by positivity, kf + kg + 1, fun n => ?_⟩
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcoeff : ((PowerSeries.coeff n (f * g) : ℚ) : ℂ)
      = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
          ((PowerSeries.coeff x.1 f : ℚ) : ℂ) * ((PowerSeries.coeff x.2 g : ℚ) : ℂ) := by
    rw [PowerSeries.coeff_mul]
    push_cast
    exact Finset.sum_congr rfl (fun x _ => by push_cast; ring)
  rw [hcoeff]
  have hterm : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal n,
      ‖((PowerSeries.coeff x.1 f : ℚ) : ℂ) * ((PowerSeries.coeff x.2 g : ℚ) : ℂ)‖
        ≤ Cf * Cg * ((n : ℝ) + 1) ^ (kf + kg) := by
    intro x hxmem
    have hxle : x.1 ≤ n := by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hxmem; omega
    have hyle : x.2 ≤ n := by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hxmem; omega
    have h1 : ((x.1 : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      have : (x.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hxle
      linarith
    have h2 : ((x.2 : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      have : (x.2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hyle
      linarith
    rw [norm_mul]
    calc ‖((PowerSeries.coeff x.1 f : ℚ) : ℂ)‖ * ‖((PowerSeries.coeff x.2 g : ℚ) : ℂ)‖
        ≤ (Cf * ((x.1 : ℝ) + 1) ^ kf) * (Cg * ((x.2 : ℝ) + 1) ^ kg) :=
          mul_le_mul (hbf x.1) (hbg x.2) (norm_nonneg _) (by positivity)
      _ = Cf * Cg * (((x.1 : ℝ) + 1) ^ kf * ((x.2 : ℝ) + 1) ^ kg) := by ring
      _ ≤ Cf * Cg * (((n : ℝ) + 1) ^ kf * ((n : ℝ) + 1) ^ kg) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (by positivity) h1 kf)
            (pow_le_pow_left₀ (by positivity) h2 kg)
            (by positivity) (by positivity)
      _ = Cf * Cg * ((n : ℝ) + 1) ^ (kf + kg) := by rw [← pow_add]
  calc ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
          ((PowerSeries.coeff x.1 f : ℚ) : ℂ) * ((PowerSeries.coeff x.2 g : ℚ) : ℂ)‖
      ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
          ‖((PowerSeries.coeff x.1 f : ℚ) : ℂ) * ((PowerSeries.coeff x.2 g : ℚ) : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, Cf * Cg * ((n : ℝ) + 1) ^ (kf + kg) :=
        Finset.sum_le_sum hterm
    _ = ((Finset.HasAntidiagonal.antidiagonal n).card : ℝ) * (Cf * Cg * ((n : ℝ) + 1) ^ (kf + kg)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((n : ℝ) + 1) * (Cf * Cg * ((n : ℝ) + 1) ^ (kf + kg)) := by
        rw [Finset.Nat.card_antidiagonal]; push_cast; ring
    _ = Cf * Cg * ((n : ℝ) + 1) ^ (kf + kg + 1) := by
        rw [pow_succ]; ring

theorem polyGrowth_derivative {f : PowerSeries ℚ} (hf : PolyGrowth f) :
    PolyGrowth (PowerSeries.derivative (R := ℚ) f) := by
  obtain ⟨C, hC, k, hb⟩ := hf
  exact poly_growth_deriv hC hb

theorem polyGrowth_sympY : PolyGrowth Submission.CDT.sympY := poly_growth_sympY

theorem polyGrowth_pow {f : PowerSeries ℚ} (hf : PolyGrowth f) (d : ℕ) :
    PolyGrowth (f ^ d) := by
  induction d with
  | zero => simpa using polyGrowth_one
  | succ d ih => rw [pow_succ]; exact polyGrowth_mul ih hf

theorem polyGrowth_finset_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ)
    (h : ∀ i ∈ s, PolyGrowth (f i)) : PolyGrowth (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polyGrowth_zero
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact polyGrowth_add (h a (Finset.mem_insert_self a t))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem polyGrowth_poly_subst_sympY (p : Polynomial ℚ) :
    PolyGrowth ((p : PowerSeries ℚ).subst Submission.CDT.sympY) := by
  rw [PowerSeries.subst_coe Submission.CDT.sympY_hasSubst p]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.aeval_add]; exact polyGrowth_add hp hq
  | monomial n r =>
      rw [Polynomial.aeval_monomial]
      exact polyGrowth_mul (polyGrowth_C r) (polyGrowth_pow polyGrowth_sympY n)

/-- Absolute summability of the `evp` series of a polynomially growing series on the unit disc. -/
theorem summable_norm_of_polyGrowth {f : PowerSeries ℚ} (hf : PolyGrowth f) {z : ℂ}
    (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n‖ := by
  obtain ⟨C, hC, k, hb⟩ := hf
  exact summable_abs_coeff_of_poly_growth hC hb hz

/-- Plain summability of the `evp` series of a polynomially growing series on the unit disc. -/
theorem summable_of_polyGrowth {f : PowerSeries ℚ} (hf : PolyGrowth f) {z : ℂ}
    (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n :=
  (summable_norm_of_polyGrowth hf hz).of_norm

/-- `PowerSeries.subst` along `sympY` is additive over finite sums. -/
theorem subst_finset_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) :
    PowerSeries.subst Submission.CDT.sympY (∑ i ∈ s, f i)
      = ∑ i ∈ s, PowerSeries.subst Submission.CDT.sympY (f i) := by
  have h := map_sum (PowerSeries.substAlgHom Submission.CDT.sympY_hasSubst) f s
  simpa only [PowerSeries.coe_substAlgHom] using h

end Work.A14D
