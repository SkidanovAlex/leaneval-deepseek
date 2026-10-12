import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseBoxFock.KinRowQuant
import Submission.Work.BoseBoxFock.SqrtKinDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Row2.hA_heat_integral`

The heat-kernel (subordination) identity of the `hA` row.  For `ℓ > 0` and the box lattice
`p n = kmomInt ℓ n = ℓ⁻¹ • 2πn`,

    (ℓ³)⁻¹ Σ_n ĉ(p_n)/(2‖p_n‖²) = ½ (ℓ³)⁻¹ ∫_{t>0} (Σ_n ĉ(p_n) e^{−t‖p_n‖²} − ĉ(0)) ,

where `ĉ = Work.BoseFixR.chat h`.

Both sides are the termwise identity `∫_{t>0} e^{−t‖p‖²} dt = ‖p‖⁻²` (`p ≠ 0`) summed over the
lattice: the term `n = 0` contributes `ĉ(0)/0 = 0` on the left and is exactly the subtracted
`ĉ(0)` on the right, since `p 0 = 0`.  The sum/integral interchange is Tonelli's theorem with the
dominating function `n ↦ |ĉ(p_n)|/‖p_n‖²`, which is exactly the summability hypothesis, because
`∫_{t>0} |ĉ(p_n)| e^{−t‖p_n‖²} dt = |ĉ(p_n)|/‖p_n‖²` for every `n`.

The mathematical content is packaged in the abstract form `HA.tsum_div_eq_integral` (an index
type `ι` with a distinguished point `z`), whose proof is: summability of every fibre
(`HA.summable_heat`, from `e^{−x} ≤ x⁻¹` and the dominating summable family), the per-fibre
integral `∫_{t>0} a e^{−tc} = a/c` (`HA.integral_mul_exp_neg`), the pointwise splitting of the
sum at `z` (`Summable.tsum_eq_add_tsum_ite`), and `integral_tsum_of_summable_integral_norm`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Topology

namespace Work.BoseRowsL.Row2

namespace HA

set_option autoImplicit false

/-! ## 1. Lattice bookkeeping -/

/-- The `2π`-lattice label `vec n` vanishes only at `n = 0`. -/
lemma vec_eq_zero_iff (n : Fin 3 → ℤ) : Work.BoseB4.vec n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have h2 : (fun i : Fin 3 => 2 * Real.pi * (n i : ℝ)) = 0 := by
      have hh := congrArg (fun v : ℝ³ => WithLp.ofLp v) h
      simpa [Work.BoseB4.vec] using hh
    ext i
    have hi := congrFun h2 i
    simp only [Pi.zero_apply] at hi
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hz : (n i : ℝ) = 0 := (mul_eq_zero.mp hi).resolve_left hpi
    exact_mod_cast hz
  · rintro rfl
    ext i
    simp [Work.BoseB4.vec]

/-- The zero label carries the zero momentum. -/
lemma kmomInt_zero (ℓ : ℝ) : Work.BoseBoxFock.kmomInt ℓ 0 = 0 := by
  have h : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
    ext i
    simp [Work.BoseB4.vec]
  rw [Work.BoseBoxFock.kmomInt, h, smul_zero]

/-- A label vanishes iff its lattice momentum does (`ℓ > 0`). -/
lemma kmomInt_eq_zero_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (n : Fin 3 → ℤ) :
    Work.BoseBoxFock.kmomInt ℓ n = 0 ↔ n = 0 := by
  rw [Work.BoseBoxFock.kmomInt, smul_eq_zero, vec_eq_zero_iff]
  simp [ne_of_gt (inv_pos.mpr hℓ)]

/-- The squared norm of a nonzero lattice momentum is positive. -/
lemma normSq_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    0 < ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 := by
  have hne : Work.BoseBoxFock.kmomInt ℓ n ≠ 0 := fun h => hn ((kmomInt_eq_zero_iff hℓ n).mp h)
  exact pow_pos (norm_pos_iff.mpr hne) 2

/-! ## 2. Two analytic inputs -/

/-- `e^{−x} ≤ x⁻¹` for `x > 0`. -/
lemma exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ x⁻¹ := by
  rw [← Real.log_le_log_iff (Real.exp_pos _) (inv_pos.mpr hx), Real.log_exp, Real.log_inv]
  linarith [Real.log_le_sub_one_of_pos hx]

/-- `∫_{t>0} a e^{−tc} = a/c` for `c > 0`. -/
lemma integral_mul_exp_neg (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ t in Set.Ioi (0 : ℝ), a * Real.exp (-(t * c)) = a / c := by
  rw [MeasureTheory.integral_const_mul]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 : ℝ)) (r := c) (by norm_num) hc
  rw [show (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * c))) = c⁻¹ from by
    simpa [mul_comm] using h]
  ring

/-! ## 3. Summability of the heat fibres -/

/-- **Summability of the heat fibres.**  If `C` vanishes at `z`, is positive elsewhere, and
`Σ_n |A n|/C n` converges, then for every `t > 0` the family `n ↦ A n e^{−t C n}` is summable.

The dominating family is `n ↦ t⁻¹(|A n|/C n) + [n = z]|A z|`: on `n ≠ z` it follows from
`e^{−t C n} ≤ (t C n)⁻¹`, and at `n = z` the fibre equals `A z` and both sides are `|A z|`. -/
lemma summable_heat {ι : Type*} [Countable ι] {z : ι} {A C : ι → ℝ} {t : ℝ}
    (ht : 0 < t) (hC0 : C z = 0) (hCpos : ∀ n, n ≠ z → 0 < C n)
    (hsumm : Summable (fun n => |A n| / C n)) :
    Summable (fun n => A n * Real.exp (-(t * C n))) := by
  classical
  refine Summable.of_norm_bounded
    (g := fun n => t⁻¹ * (|A n| / C n) + (if n = z then |A z| else 0)) ?_ ?_
  · exact (hsumm.mul_left t⁻¹).add (hasSum_ite_eq z (|A z|)).summable
  · intro n
    by_cases hn : n = z
    · rw [hn]
      rw [hC0, mul_zero, neg_zero, Real.exp_zero, mul_one, if_pos rfl, div_zero, mul_zero,
        zero_add, Real.norm_eq_abs]
    · rw [if_neg hn]
      have he : Real.exp (-(t * C n)) ≤ (t * C n)⁻¹ := exp_neg_le_inv (mul_pos ht (hCpos n hn))
      have h2 : ‖A n * Real.exp (-(t * C n))‖ = |A n| * Real.exp (-(t * C n)) := by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [h2]
      calc |A n| * Real.exp (-(t * C n)) ≤ |A n| * (t * C n)⁻¹ :=
            mul_le_mul_of_nonneg_left he (abs_nonneg _)
        _ = t⁻¹ * (|A n| / C n) := by ring_nf
        _ ≤ t⁻¹ * (|A n| / C n) + 0 := le_add_of_nonneg_right le_rfl

/-! ## 4. The abstract subordination identity -/

/-- **The abstract heat/subordination identity.**  For a countable index type with a
distinguished point `z` whose `C`-value vanishes, with `C` positive elsewhere and
`Σ |A n|/C n < ∞`,

    Σ_n A n / C n = ∫_{t > 0} ( Σ_n A n e^{−t C n} − A z ) .

The subtraction of `A z` removes the (`t`-independent) term of the sum at `z`, where the
exponential equals `1`. -/
theorem tsum_div_eq_integral {ι : Type*} [Countable ι] {z : ι} {A C : ι → ℝ}
    (hC0 : C z = 0) (hCpos : ∀ n, n ≠ z → 0 < C n)
    (hsumm : Summable (fun n => |A n| / C n)) :
    (∑' n, A n / C n) = ∫ t in Set.Ioi (0 : ℝ),
      ((∑' n, A n * Real.exp (-(t * C n))) - A z) := by
  classical
  -- each fibre (shifted at `z`) is integrable
  have hFint : ∀ n : ι, Integrable (fun t : ℝ => if n = z then 0 else A n * Real.exp (-(t * C n)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro n
    by_cases hn : n = z
    · refine (integrable_zero ℝ ℝ _).congr ?_
      exact Filter.Eventually.of_forall (fun s => by simp [hn])
    · refine ((exp_neg_integrableOn_Ioi (0 : ℝ) (b := C n) (hCpos n hn)).const_mul (A n)).congr ?_
      refine Filter.Eventually.of_forall (fun s => ?_)
      show A n * Real.exp (-C n * s) = (if n = z then 0 else A n * Real.exp (-(s * C n)))
      rw [if_neg hn, show -C n * s = -(s * C n) by ring]
  -- the integral of the norm of each fibre is `|A n|/C n`
  have hFn : ∀ n : ι, ∫ t in Set.Ioi (0 : ℝ),
        ‖(if n = z then 0 else A n * Real.exp (-(t * C n)))‖ = |A n| / C n := by
    intro n
    by_cases hn : n = z
    · rw [show (fun t : ℝ => ‖(if n = z then 0 else A n * Real.exp (-(t * C n)))‖)
          = fun _ => (0 : ℝ) from funext (fun t => by rw [if_pos hn, norm_zero])]
      simp [hC0, hn]
    · have hpt : ∀ t : ℝ, ‖(if n = z then 0 else A n * Real.exp (-(t * C n)))‖
          = |A n| * Real.exp (-(t * C n)) := by
        intro t
        rw [if_neg hn, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact integral_mul_exp_neg (a := |A n|) (c := C n) (hCpos n hn)
  have hsumm_int : Summable (fun n : ι => ∫ t in Set.Ioi (0 : ℝ),
      ‖(if n = z then 0 else A n * Real.exp (-(t * C n)))‖) := by
    rw [show (fun n : ι => ∫ t in Set.Ioi (0 : ℝ),
          ‖(if n = z then 0 else A n * Real.exp (-(t * C n)))‖) = fun n => |A n| / C n from
        funext hFn]
    exact hsumm
  -- Tonelli: the sum and the integral commute
  have key := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun n t => if n = z then 0 else A n * Real.exp (-(t * C n))) hFint hsumm_int
  -- the sum of the fibre integrals is the left-hand side
  have h1 : (∑' n, ∫ t in Set.Ioi (0 : ℝ),
        (if n = z then 0 else A n * Real.exp (-(t * C n)))) = ∑' n, A n / C n := by
    refine tsum_congr (fun n => ?_)
    by_cases hn : n = z
    · rw [show (fun t : ℝ => (if n = z then 0 else A n * Real.exp (-(t * C n))))
          = fun _ => (0 : ℝ) from funext (fun t => by rw [if_pos hn])]
      simp [hC0, hn]
    · rw [show (fun t : ℝ => (if n = z then 0 else A n * Real.exp (-(t * C n))))
          = fun t => A n * Real.exp (-(t * C n)) from funext (fun t => by rw [if_neg hn])]
      exact integral_mul_exp_neg (a := A n) (c := C n) (hCpos n hn)
  -- at each `t > 0` the integrand is the sum minus the `z`-term
  have h2 : (∫ t in Set.Ioi (0 : ℝ),
        ∑' n, (if n = z then 0 else A n * Real.exp (-(t * C n))))
      = ∫ t in Set.Ioi (0 : ℝ), ((∑' n, A n * Real.exp (-(t * C n))) - A z) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hsum : Summable (fun n => A n * Real.exp (-(t * C n))) :=
      summable_heat ht hC0 hCpos hsumm
    have hsplit := hsum.tsum_eq_add_tsum_ite z
    rw [hsplit, hC0, mul_zero, neg_zero, Real.exp_zero, mul_one]
    ring
  rw [← h2, ← key]
  exact h1.symm

end HA

/-! ## 5. The target -/

theorem hA_heat_integral {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hsumm : Summable (fun n : Fin 3 → ℤ => |Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)| / ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2)) :
    (ℓ ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n) / (2 * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))
      = (1 / 2) * ∫ t in Set.Ioi (0 : ℝ), (ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ,
          Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n) * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0) := by
  have hmain := HA.tsum_div_eq_integral (z := (0 : Fin 3 → ℤ))
    (A := fun n => Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n))
    (C := fun n => ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2)
    (by simp [HA.kmomInt_zero]) (fun n hn => HA.normSq_pos hℓ hn) hsumm
  have hL : (∑' n : Fin 3 → ℤ,
        Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n) / (2 * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))
      = (1 / 2) * ∑' n : Fin 3 → ℤ,
          Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n) / ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 := by
    rw [show (∑' n : Fin 3 → ℤ,
          Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n) / (2 * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))
        = ∑' n : Fin 3 → ℤ, (1 / 2) * (Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
            / ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2) from
      tsum_congr (fun n => by ring_nf)]
    rw [tsum_mul_left]
  have hR : (∫ t in Set.Ioi (0 : ℝ), (ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ,
        Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n) * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0))
      = (ℓ ^ 3)⁻¹ * ∫ t in Set.Ioi (0 : ℝ), ((∑' n : Fin 3 → ℤ,
        Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n) * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0) :=
    MeasureTheory.integral_const_mul _ _
  rw [hL, hR, hmain, HA.kmomInt_zero]
  ring

end Work.BoseRowsL.Row2
