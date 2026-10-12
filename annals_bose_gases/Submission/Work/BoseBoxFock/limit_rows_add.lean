import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.hatChi_lattice_tail_le
import Submission.Work.BoseBoxFock.pinQLimDefs
import Submission.Work.BoseRowsFS.CoulBilin.chat_add
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.limit_rows_add` — additivity of the four limit kernels in the weight

The four limit objects of `Submission/Work/BoseBoxFock/pinQLimDefs.lean` (`pinQBl`, `pinQCl`,
`pinQDl`, `latPer3`) are all **lattice sums over `ℤ³` whose summands are linear in the kernel
`W`** (the only `W`-dependence is through the Fourier transform `chat W`, which is linear in `W`
by `Work.BoseRowsFS.CoulBilin.chat_add`).  Hence they are additive in `W`, as this file proves.

The only mathematical content is **summability**, which has to be supplied in order to apply
`Summable.tsum_add`:

* for `pinQBl`, `pinQCl`, `pinQDl` the summand is `Ŵ(k_n)·χ̂(ℓ k_n)^{k}·(phase)` with `k ∈ {1,2}`
  and `‖phase‖ ≤ 1`; `Ŵ` is uniformly bounded by its `L¹` mass
  (`Work.BoseBoxFock.chat_abs_le_uniform`) and `χ̂` decays faster than any polynomial
  (`Work.BoseBoxFock.hatChi_decay_52`), so the family is dominated by
  `C·(1 + ‖vec n‖²)^{-52k}`, which is summable (`summable_vec_inv_one_add_norm_sq`); since
  `ℓ • kmomInt ℓ n = vec n` for `ℓ ≠ 0`, the momentum argument is exactly `vec n`;
* for `latPer3` the summand is `W (z + ℓ • latVec m)`, which is **finitely supported** because
  `W` has compact support.

The side condition `0 < ℓ` always holds for `ℓ = ellH v μ` (`Work.BoseBoxFock.ellH_pos`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Helpers -/

/-- A bounded, a.e. strongly measurable, compactly supported function is integrable. -/
private lemma integrable_of_bounded_compact {W : E3 → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W) :
    MeasureTheory.Integrable W := by
  obtain ⟨C, hC⟩ := hWb
  exact MeasureTheory.memLp_one_iff_integrable.mp
    (hWs.memLp_of_bound hWm C (Filter.Eventually.of_forall hC))

/-- The norm of a real number seen in `ℂ` (the `Complex.ofReal` spelling of
`RCLike.norm_ofReal`, which `rw` can match). -/
private lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- `chat` is additive in its kernel, in the `W + U` spelling. -/
private lemma chat_add' {W U : E3 → ℝ} (hW : MeasureTheory.Integrable W)
    (hU : MeasureTheory.Integrable U) (k : E3) :
    Work.BoseFixR.chat (W + U) k = Work.BoseFixR.chat W k + Work.BoseFixR.chat U k := by
  rw [show (W + U) = fun x => W x + U x from funext fun x => rfl]
  exact Work.BoseRowsFS.CoulBilin.chat_add hW hU k

/-- `ℓ • kmomInt ℓ n = vec n` for `ℓ ≠ 0`. -/
private lemma smul_kmomInt {ℓ : ℝ} (hℓ : ℓ ≠ 0) (n : Fin 3 → ℤ) :
    ℓ • kmomInt ℓ n = Work.BoseB4.vec n := by
  rw [kmomInt, smul_smul, mul_inv_cancel₀ hℓ, one_smul]

/-- The exponential of a purely imaginary phase has norm `1`. -/
private lemma norm_exp_I_mul_ofReal (r : ℝ) :
    ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Complex.I * (r : ℂ)).re = 0 := by simp
  rw [h, Real.exp_zero]

/-- The conjugate exponential of a purely imaginary phase has norm `1`. -/
private lemma norm_exp_neg_I_mul_ofReal (r : ℝ) :
    ‖Complex.exp (-(Complex.I * (r : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (-(Complex.I * (r : ℂ))).re = 0 := by simp
  rw [h, Real.exp_zero]

/-- Multiplication by a unimodular phase preserves summability. -/
private lemma summable_mul_phase {f : (Fin 3 → ℤ) → ℂ} (hf : Summable f)
    {phase : (Fin 3 → ℤ) → ℂ} (hphase : ∀ n, ‖phase n‖ ≤ 1) :
    Summable (fun n => f n * phase n) := by
  refine Summable.of_norm_bounded hf.norm (fun n => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hphase n)

/-! ## Summability of the lattice families -/

/-- **Summability of the `χ̂`-weighted lattice family.**  For `ℓ > 0`, the family
`n ↦ Ŵ(kmomInt ℓ n)·χ̂(ℓ • kmomInt ℓ n)^k` (`k ≥ 1`) is summable, by the uniform `L¹` bound on
`Ŵ` and the order-`52` decay of `χ̂`. -/
private lemma summable_hatChi_core {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ k) := by
  obtain ⟨B, hB0, hB⟩ := chat_abs_le_uniform (W := W)
  obtain ⟨C, hC0, hC⟩ := hatChi_decay_52
  have h52 : 2 ≤ 52 * k := by omega
  have hsumg : Summable (fun n : Fin 3 → ℤ =>
      (B * C ^ k) * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ (52 * k))⁻¹) :=
    (summable_vec_inv_one_add_norm_sq h52).mul_left (B * C ^ k)
  refine Summable.of_norm_bounded hsumg (fun n => ?_)
  rw [smul_kmomInt (ne_of_gt hℓ) n, norm_mul, norm_pow, norm_ofReal_complex,
    norm_ofReal_complex]
  have h1 : |Work.BoseFixR.chat W (kmomInt ℓ n)|
        * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)| ^ k
      ≤ B * (C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) ^ k :=
    mul_le_mul (hB _) (pow_le_pow_left₀ (abs_nonneg _) (hC _) k)
      (pow_nonneg (abs_nonneg _) k) hB0
  refine le_trans h1 ?_
  have hEq : B * (C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) ^ k
      = B * C ^ k * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ (52 * k))⁻¹ := by
    rw [mul_pow, inv_pow, ← pow_mul, ← mul_assoc]
  exact le_of_eq hEq

/-- The squared version: summands `Ŵ(kmomInt ℓ n)·χ̂(ℓ • kmomInt ℓ n)²`. -/
private lemma summable_hatChi_sq {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) :
    Summable (fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 2) :=
  summable_hatChi_core hℓ W 2 (by norm_num)

/-- The `pinQBl` summand family of a kernel `W` is summable. -/
private lemma summable_bl {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) (w : E3) :
    Summable (fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))) := by
  have h := summable_mul_phase (f := fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 1)
    (summable_hatChi_core hℓ W 1 le_rfl) (phase := fun n =>
      Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ)))
    (fun n => le_of_eq (norm_exp_I_mul_ofReal _))
  simpa only [pow_one] using h

/-- The `pinQCl` summand family of a kernel `W` is summable. -/
private lemma summable_cl {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) (y : E3) :
    Summable (fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))) := by
  have h := summable_mul_phase (f := fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 1)
    (summable_hatChi_core hℓ W 1 le_rfl) (phase := fun n =>
      Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ))))
    (fun n => le_of_eq (norm_exp_neg_I_mul_ofReal _))
  simpa only [pow_one] using h

/-- **Summability of the periodisation summand.**  For `ℓ > 0` and `W` compactly supported, the
family `m ↦ W (z + ℓ • latVec m)` is finitely supported, hence summable. -/
private lemma summable_latPer_shift {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWs : HasCompactSupport W) (z : E3) :
    Summable (fun m : Fin 3 → ℤ => ((W (z + ℓ • latVec m) : ℝ) : ℂ)) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x : E3, R < ‖x‖ → W x = 0 := by
    obtain ⟨R, hR⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : E3)).mp hWs.isCompact.isBounded
    refine ⟨R, fun x hx => ?_⟩
    by_contra hx0
    have hxmem : x ∈ tsupport W :=
      subset_closure (by simpa [Function.mem_support] using hx0)
    have hxR := hR hxmem
    simp only [Metric.mem_closedBall, dist_zero_right] at hxR
    linarith
  refine summable_of_ne_finset_zero (s := LatFourier.latFinSet ℓ (R + ‖z‖)) (fun m hm => ?_)
  have h1 : ((R + ‖z‖) + Real.sqrt 3 * ℓ) / ℓ < ‖latVec m‖ := by
    rw [← not_le]
    exact fun hc => hm ((LatFourier.mem_latFinSet).mpr hc)
  have h2 : R + ‖z‖ + Real.sqrt 3 * ℓ < ‖ℓ • latVec m‖ := by
    rw [LatFourier.latVec_norm_smul ℓ hℓ.le]
    have h3 := (div_lt_iff₀ hℓ).mp h1
    linarith
  have h3 : R < ‖z + ℓ • latVec m‖ := by
    have h4 : ‖ℓ • latVec m‖ ≤ ‖z + ℓ • latVec m‖ + ‖z‖ := by
      calc ‖ℓ • latVec m‖ = ‖(z + ℓ • latVec m) - z‖ := by congr 1; abel
        _ ≤ ‖z + ℓ • latVec m‖ + ‖z‖ := norm_sub_le _ _
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)]
  simp [hR _ h3]

/-! ## The additivity statements -/

/-- Additivity of the first `χ̂`-lattice sum in the weight. -/
private lemma pinQBl_add {ℓ : ℝ} (hℓ : 0 < ℓ) {Wa Wb : E3 → ℝ}
    (hIa : MeasureTheory.Integrable Wa) (hIb : MeasureTheory.Integrable Wb) (w : E3) :
    pinQBl ℓ (Wa + Wb) w = pinQBl ℓ Wa w + pinQBl ℓ Wb w := by
  have hsumA := summable_bl hℓ Wa w
  have hsumB := summable_bl hℓ Wb w
  have hpt : ∀ n : Fin 3 → ℤ,
      ((Work.BoseFixR.chat (Wa + Wb) (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))
      = (((Work.BoseFixR.chat Wa (kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ)))
        + (((Work.BoseFixR.chat Wb (kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))) := by
    intro n
    rw [chat_add' hIa hIb (kmomInt ℓ n)]
    push_cast
    ring
  rw [pinQBl]
  rw [show (fun n : Fin 3 → ℤ =>
        ((Work.BoseFixR.chat (Wa + Wb) (kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ)))
      = fun n : Fin 3 → ℤ =>
        (((Work.BoseFixR.chat Wa (kmomInt ℓ n) : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ)))
          + (((Work.BoseFixR.chat Wb (kmomInt ℓ n) : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))) from
      funext hpt]
  rw [Summable.tsum_add hsumA hsumB]
  rfl

/-- Additivity of the second `χ̂`-lattice sum in the weight. -/
private lemma pinQCl_add {ℓ : ℝ} (hℓ : 0 < ℓ) {Wa Wb : E3 → ℝ}
    (hIa : MeasureTheory.Integrable Wa) (hIb : MeasureTheory.Integrable Wb) (y : E3) :
    pinQCl ℓ (Wa + Wb) y = pinQCl ℓ Wa y + pinQCl ℓ Wb y := by
  have hsumA := summable_cl hℓ Wa y
  have hsumB := summable_cl hℓ Wb y
  have hpt : ∀ n : Fin 3 → ℤ,
      ((Work.BoseFixR.chat (Wa + Wb) (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))
      = (((Work.BoseFixR.chat Wa (kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ))))
        + (((Work.BoseFixR.chat Wb (kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))) := by
    intro n
    rw [chat_add' hIa hIb (kmomInt ℓ n)]
    push_cast
    ring
  rw [pinQCl]
  rw [show (fun n : Fin 3 → ℤ =>
        ((Work.BoseFixR.chat (Wa + Wb) (kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ))))
      = fun n : Fin 3 → ℤ =>
        (((Work.BoseFixR.chat Wa (kmomInt ℓ n) : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ))))
          + (((Work.BoseFixR.chat Wb (kmomInt ℓ n) : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))) from
      funext hpt]
  rw [Summable.tsum_add hsumA hsumB]
  rfl

/-- Additivity of the `θθ`-lattice sum in the weight. -/
private lemma pinQDl_add {ℓ : ℝ} (hℓ : 0 < ℓ) {Wa Wb : E3 → ℝ}
    (hIa : MeasureTheory.Integrable Wa) (hIb : MeasureTheory.Integrable Wb) :
    pinQDl ℓ (Wa + Wb) = pinQDl ℓ Wa + pinQDl ℓ Wb := by
  have hsumA := summable_hatChi_sq hℓ Wa
  have hsumB := summable_hatChi_sq hℓ Wb
  have hpt : ∀ n : Fin 3 → ℤ,
      ((Work.BoseFixR.chat (Wa + Wb) (kmomInt ℓ n) : ℝ) : ℂ)
        * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 2
      = (((Work.BoseFixR.chat Wa (kmomInt ℓ n) : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 2)
        + (((Work.BoseFixR.chat Wb (kmomInt ℓ n) : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 2) := by
    intro n
    rw [chat_add' hIa hIb (kmomInt ℓ n)]
    push_cast
    ring
  rw [pinQDl]
  rw [show (fun n : Fin 3 → ℤ =>
        ((Work.BoseFixR.chat (Wa + Wb) (kmomInt ℓ n) : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 2)
      = fun n : Fin 3 → ℤ =>
        (((Work.BoseFixR.chat Wa (kmomInt ℓ n) : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 2)
          + (((Work.BoseFixR.chat Wb (kmomInt ℓ n) : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 2) from
      funext hpt]
  rw [Summable.tsum_add hsumA hsumB]
  rfl

/-- Additivity of the `χχ`-periodisation in the weight. -/
private lemma latPer3_add {ℓ : ℝ} (hℓ : 0 < ℓ) {Wa Wb : E3 → ℝ}
    (hsa : HasCompactSupport Wa) (hsb : HasCompactSupport Wb) (z : E3) :
    latPer3 ℓ (Wa + Wb) z = latPer3 ℓ Wa z + latPer3 ℓ Wb z := by
  have hsumA := summable_latPer_shift hℓ hsa z
  have hsumB := summable_latPer_shift hℓ hsb z
  have hAdd : LatFourier.latPer ℓ (Wa + Wb) z
      = LatFourier.latPer ℓ Wa z + LatFourier.latPer ℓ Wb z := by
    have hcongr : (fun m : Fin 3 → ℤ => (((Wa + Wb) (z + ℓ • latVec m) : ℝ) : ℂ))
        = fun m : Fin 3 → ℤ =>
            ((Wa (z + ℓ • latVec m) : ℝ) : ℂ) + ((Wb (z + ℓ • latVec m) : ℝ) : ℂ) := by
      funext m
      rw [Pi.add_apply]
      push_cast
      ring
    rw [LatFourier.latPer, LatFourier.latPer, LatFourier.latPer, hcongr]
    exact Summable.tsum_add hsumA hsumB
  rw [latPer3, latPer3, latPer3, hAdd]
  ring

theorem limit_rows_add {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    {Wa Wb : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWam : MeasureTheory.AEStronglyMeasurable Wa MeasureTheory.volume)
    (hWab : ∃ C : ℝ, ∀ x, ‖Wa x‖ ≤ C) (hWas : HasCompactSupport Wa)
    (hWbm : MeasureTheory.AEStronglyMeasurable Wb MeasureTheory.volume)
    (hWbb : ∃ C : ℝ, ∀ x, ‖Wb x‖ ≤ C) (hWbs : HasCompactSupport Wb) :
    (∀ w, Work.BoseBoxFock.pinQBl (Work.BoseBoxFock.ellH v μ) (Wa + Wb) w
        = Work.BoseBoxFock.pinQBl (Work.BoseBoxFock.ellH v μ) Wa w
          + Work.BoseBoxFock.pinQBl (Work.BoseBoxFock.ellH v μ) Wb w)
    ∧ (∀ y, Work.BoseBoxFock.pinQCl (Work.BoseBoxFock.ellH v μ) (Wa + Wb) y
        = Work.BoseBoxFock.pinQCl (Work.BoseBoxFock.ellH v μ) Wa y
          + Work.BoseBoxFock.pinQCl (Work.BoseBoxFock.ellH v μ) Wb y)
    ∧ (Work.BoseBoxFock.pinQDl (Work.BoseBoxFock.ellH v μ) (Wa + Wb)
        = Work.BoseBoxFock.pinQDl (Work.BoseBoxFock.ellH v μ) Wa
          + Work.BoseBoxFock.pinQDl (Work.BoseBoxFock.ellH v μ) Wb)
    ∧ (∀ z, Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ) (Wa + Wb) z
        = Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ) Wa z
          + Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ) Wb z) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hIa : MeasureTheory.Integrable Wa := integrable_of_bounded_compact hWam hWab hWas
  have hIb : MeasureTheory.Integrable Wb := integrable_of_bounded_compact hWbm hWbb hWbs
  exact ⟨fun w => pinQBl_add hℓ hIa hIb w,
    fun y => pinQCl_add hℓ hIa hIb y,
    pinQDl_add hℓ hIa hIb,
    fun z => latPer3_add hℓ hWas hWbs z⟩

end Work.BoseBoxFock
