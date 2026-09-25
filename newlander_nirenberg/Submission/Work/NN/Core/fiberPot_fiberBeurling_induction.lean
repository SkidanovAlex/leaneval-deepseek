import Mathlib
import Submission.Work.NN.Core.fiberBeurling
import Submission.Work.NN.Core.fiberBeurling_fderiv_apply
import Submission.Work.NN.Core.dCoord_fiberPot_self
import Submission.Work.NN.Core.fiberPot_dbarCoord
import Submission.Work.NN.Core.fiberPot_dbarCoord_self
import Submission.Work.NN.Core.contDiff_fiberPot
import Submission.Work.NN.Core.holderNorm_le_wirtinger_coord_on
import Submission.Work.NN.Core.exists_holderNorm_wirtinger_le
import Submission.Work.NN.Core.holderNorm_zero_fiberPot_le
import Submission.Work.NN.Core.holderNorm_zero_fiberBeurling_le
import Submission.Work.NN.Core.dCoord_fiberPot
import Submission.Work.CR.Flat.Cauchy.holderNorm_le_sup_of_holomorphic_open

set_option maxHeartbeats 2000000

namespace Work.NN.Core

open scoped NNReal ENNReal Topology
open Set MeasureTheory Filter

noncomputable section

variable {n : ℕ}

/-! ### Elementary `ℝ≥0∞` combination lemmas -/

lemma add_le_ofReal_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {N x y : ℝ≥0∞}
    (hx : x ≤ ENNReal.ofReal a * N) (hy : y ≤ ENNReal.ofReal b * N) :
    x + y ≤ ENNReal.ofReal (a + b) * N := by
  refine (add_le_add hx hy).trans ?_
  rw [← add_mul, ENNReal.ofReal_add ha hb]

/-- Two terms, each bounded by `ofReal a * N`, are bounded by `ofReal (2 a) * N`. -/
lemma add_le_ofReal_two_mul {a : ℝ} (ha : 0 ≤ a) {N x y : ℝ≥0∞}
    (hx : x ≤ ENNReal.ofReal a * N) (hy : y ≤ ENNReal.ofReal a * N) :
    x + y ≤ ENNReal.ofReal (2 * a) * N := by
  calc x + y ≤ ENNReal.ofReal a * N + ENNReal.ofReal a * N := add_le_add hx hy
    _ = (ENNReal.ofReal a + ENNReal.ofReal a) * N := by rw [add_mul]
    _ = ENNReal.ofReal (a + a) * N := by rw [ENNReal.ofReal_add ha ha]
    _ = ENNReal.ofReal (2 * a) * N := by rw [show a + a = 2 * a by ring]

lemma ofReal_mul_le_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {N x : ℝ≥0∞}
    (hx : x ≤ ENNReal.ofReal b * N) :
    ENNReal.ofReal a * x ≤ ENNReal.ofReal (a * b) * N := by
  refine (mul_le_mul' (le_refl (ENNReal.ofReal a)) hx).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul ha]

lemma finset_sum_le_ofReal_mul {ι : Type*} [Fintype ι] {f : ι → ℝ≥0∞} {E : ℝ} (hE : 0 ≤ E)
    {N : ℝ≥0∞} (h : ∀ i, f i ≤ ENNReal.ofReal E * N) :
    ∑ i, f i ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * E) * N := by
  refine (Finset.sum_le_sum (fun i _ => h i)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- A sum over `Fin n` of terms bounded by `ofReal E * N` is bounded by
`ofReal (n * E) * N`. -/
lemma sum_fin_le_ofReal_mul {n : ℕ} {f : Fin n → ℝ≥0∞} {E : ℝ} (hE : 0 ≤ E) {N : ℝ≥0∞}
    (h : ∀ i, f i ≤ ENNReal.ofReal E * N) :
    ∑ i : Fin n, f i ≤ ENNReal.ofReal ((n : ℝ) * E) * N := by
  simpa using finset_sum_le_ofReal_mul (ι := Fin n) (E := E) hE h

/-! ### The Wirtinger derivatives of the fibrewise Beurling transform

The fibrewise Beurling transform is the truncated Beurling integral
`fiberBeurling R j u z = -(1/π) ∫_{‖s‖<2R} (u (z + s e_j) - u z)/s²`,
see `fiberBeurling_eq_shiftIntegral`.  Its first Wirtinger derivatives are computed by
differentiating under the integral sign, which is legitimate for `C²` data
(`hasFDerivAt_fiberIntegral`). -/

/-- Integrability of the scalar integrand obtained by applying the derivative of the truncated
Beurling integral to a fixed vector. -/
lemma integrable_fiberDerivIntegrand_div {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (j : Fin n)
    {u : Cn n → ℂ} (hu : ContDiff ℝ 2 u) (z : Cn n) (v : Cn n) :
    Integrable (fun s : ℂ =>
        ((fderiv ℝ u (z + s • Pi.single j (1 : ℂ))) v - (fderiv ℝ u z) v) / s ^ 2)
      (volume.restrict (Metric.ball (0 : ℂ) ρ)) := by
  have h := integrable_fiberDerivIntegrand hρ j hu z
  have h0 : Integrable (fun s : ℂ =>
      ((s ^ 2)⁻¹ • (fderiv ℝ u (z + s • Pi.single j (1 : ℂ)) - fderiv ℝ u z)) v)
      (volume.restrict (Metric.ball (0 : ℂ) ρ)) := by
    have h1 := ContinuousLinearMap.integrable_comp (ContinuousLinearMap.apply ℝ ℂ v) h
    simpa only [ContinuousLinearMap.apply_apply] using h1
  refine h0.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only []
  rw [smul_apply, smul_eq_mul, sub_apply, div_eq_mul_inv, mul_comm]

/-- The `(1,0)`-derivatives of the truncated Beurling integral are the Beurling integrals of the
`(1,0)`-derivatives of the data. -/
lemma fiberBeurling_dCoord_integral {R : ℝ} (hR : 0 < R) (j : Fin n) {u : Cn n → ℂ}
    (hu : ContDiff ℝ 2 u) (z : Cn n) (k : Fin n) :
    Work.CR.Flat.dCoord k (fiberBeurling R j u) z
      = -((Real.pi : ℂ))⁻¹ * ∫ s in Metric.ball (0 : ℂ) (2 * R),
          (Work.CR.Flat.dCoord k u (z + s • Pi.single j (1 : ℂ))
            - Work.CR.Flat.dCoord k u z) / s ^ 2 := by
  have hρ : (0 : ℝ) < 2 * R := by linarith
  have hAint : Integrable (fun s : ℂ =>
      ((fderiv ℝ u (z + s • Pi.single j (1 : ℂ))) (Pi.single k (1 : ℂ))
        - (fderiv ℝ u z) (Pi.single k (1 : ℂ))) / s ^ 2)
      (volume.restrict (Metric.ball (0 : ℂ) (2 * R))) :=
    integrable_fiberDerivIntegrand_div hρ j hu z (Pi.single k (1 : ℂ))
  have hBint : Integrable (fun s : ℂ =>
      ((fderiv ℝ u (z + s • Pi.single j (1 : ℂ))) (Pi.single k (Complex.I : ℂ))
        - (fderiv ℝ u z) (Pi.single k (Complex.I : ℂ))) / s ^ 2)
      (volume.restrict (Metric.ball (0 : ℂ) (2 * R))) :=
    integrable_fiberDerivIntegrand_div hρ j hu z (Pi.single k (Complex.I : ℂ))
  have hIBint : Integrable (fun s : ℂ => Complex.I *
      (((fderiv ℝ u (z + s • Pi.single j (1 : ℂ))) (Pi.single k (Complex.I : ℂ))
        - (fderiv ℝ u z) (Pi.single k (Complex.I : ℂ))) / s ^ 2))
      (volume.restrict (Metric.ball (0 : ℂ) (2 * R))) := hBint.const_mul Complex.I
  have hC : (∫ s in Metric.ball (0 : ℂ) (2 * R),
        (Work.CR.Flat.dCoord k u (z + s • Pi.single j (1 : ℂ))
          - Work.CR.Flat.dCoord k u z) / s ^ 2)
      = (1 / 2 : ℂ) * ((∫ s in Metric.ball (0 : ℂ) (2 * R),
            ((fderiv ℝ u (z + s • Pi.single j (1 : ℂ))) (Pi.single k (1 : ℂ))
              - (fderiv ℝ u z) (Pi.single k (1 : ℂ))) / s ^ 2)
          - Complex.I * (∫ s in Metric.ball (0 : ℂ) (2 * R),
            ((fderiv ℝ u (z + s • Pi.single j (1 : ℂ))) (Pi.single k (Complex.I : ℂ))
              - (fderiv ℝ u z) (Pi.single k (Complex.I : ℂ))) / s ^ 2)) := by
    rw [← MeasureTheory.integral_const_mul Complex.I,
      ← MeasureTheory.integral_sub hAint hIBint,
      ← MeasureTheory.integral_const_mul (1 / 2 : ℂ)]
    refine setIntegral_congr_fun measurableSet_ball (fun s _ => ?_)
    simp only [Work.CR.Flat.dCoord]
    ring
  rw [Work.CR.Flat.dCoord,
    fiberBeurling_fderiv_apply hR j hu z (Pi.single k (1 : ℂ)),
    fiberBeurling_fderiv_apply hR j hu z (Pi.single k (Complex.I : ℂ)), hC]
  ring

/-- The `(0,1)`-derivatives of the truncated Beurling integral are the Beurling integrals of the
`(0,1)`-derivatives of the data. -/
lemma fiberBeurling_dbarCoord_integral {R : ℝ} (hR : 0 < R) (j : Fin n) {u : Cn n → ℂ}
    (hu : ContDiff ℝ 2 u) (z : Cn n) (k : Fin n) :
    Work.CR.Flat.dbarCoord k (fiberBeurling R j u) z
      = -((Real.pi : ℂ))⁻¹ * ∫ s in Metric.ball (0 : ℂ) (2 * R),
          (Work.CR.Flat.dbarCoord k u (z + s • Pi.single j (1 : ℂ))
            - Work.CR.Flat.dbarCoord k u z) / s ^ 2 := by
  have hρ : (0 : ℝ) < 2 * R := by linarith
  have hAint : Integrable (fun s : ℂ =>
      ((fderiv ℝ u (z + s • Pi.single j (1 : ℂ))) (Pi.single k (1 : ℂ))
        - (fderiv ℝ u z) (Pi.single k (1 : ℂ))) / s ^ 2)
      (volume.restrict (Metric.ball (0 : ℂ) (2 * R))) :=
    integrable_fiberDerivIntegrand_div hρ j hu z (Pi.single k (1 : ℂ))
  have hBint : Integrable (fun s : ℂ =>
      ((fderiv ℝ u (z + s • Pi.single j (1 : ℂ))) (Pi.single k (Complex.I : ℂ))
        - (fderiv ℝ u z) (Pi.single k (Complex.I : ℂ))) / s ^ 2)
      (volume.restrict (Metric.ball (0 : ℂ) (2 * R))) :=
    integrable_fiberDerivIntegrand_div hρ j hu z (Pi.single k (Complex.I : ℂ))
  have hIBint : Integrable (fun s : ℂ => Complex.I *
      (((fderiv ℝ u (z + s • Pi.single j (1 : ℂ))) (Pi.single k (Complex.I : ℂ))
        - (fderiv ℝ u z) (Pi.single k (Complex.I : ℂ))) / s ^ 2))
      (volume.restrict (Metric.ball (0 : ℂ) (2 * R))) := hBint.const_mul Complex.I
  have hC : (∫ s in Metric.ball (0 : ℂ) (2 * R),
        (Work.CR.Flat.dbarCoord k u (z + s • Pi.single j (1 : ℂ))
          - Work.CR.Flat.dbarCoord k u z) / s ^ 2)
      = (1 / 2 : ℂ) * ((∫ s in Metric.ball (0 : ℂ) (2 * R),
            ((fderiv ℝ u (z + s • Pi.single j (1 : ℂ))) (Pi.single k (1 : ℂ))
              - (fderiv ℝ u z) (Pi.single k (1 : ℂ))) / s ^ 2)
          + Complex.I * (∫ s in Metric.ball (0 : ℂ) (2 * R),
            ((fderiv ℝ u (z + s • Pi.single j (1 : ℂ))) (Pi.single k (Complex.I : ℂ))
              - (fderiv ℝ u z) (Pi.single k (Complex.I : ℂ))) / s ^ 2)) := by
    rw [← MeasureTheory.integral_const_mul Complex.I,
      ← MeasureTheory.integral_add hAint hIBint,
      ← MeasureTheory.integral_const_mul (1 / 2 : ℂ)]
    refine setIntegral_congr_fun measurableSet_ball (fun s _ => ?_)
    simp only [Work.CR.Flat.dbarCoord]
    ring
  rw [Work.CR.Flat.dbarCoord,
    fiberBeurling_fderiv_apply hR j hu z (Pi.single k (1 : ℂ)),
    fiberBeurling_fderiv_apply hR j hu z (Pi.single k (Complex.I : ℂ)), hC]
  ring

/-- The Wirtinger derivatives of the fibrewise Beurling transform, for band-supported `C²` data
on the disc `‖z j‖ < R`:
* in the fibre direction `∂_j` commutes with the transform, and `∂̄_j` of the transform is `∂_j`
  of the data;
* in the transverse directions (`k ≠ j`) both `∂_k` and `∂̄_k` commute with the transform.

The fibre `(1,0)`- and the transverse identities follow from the integral representations above;
the fibre `(0,1)`-identity is the commutation `∂̄_j ∂_j (fiberPot) = ∂_j ∂̄_j (fiberPot)` together
with `∂_j (fiberPot) = fiberBeurling` and `∂̄_j (fiberPot) = u`. -/
theorem fiberBeurling_wirtinger_band {R : ℝ} (hR : 0 < R) (j : Fin n) {u : Cn n → ℂ}
    (hu : ContDiff ℝ 2 u) (hband : fiberBand R j u) {z : Cn n} (hz : ‖z j‖ < R) :
    (Work.CR.Flat.dCoord j (fiberBeurling R j u) z = fiberBeurling R j (Work.CR.Flat.dCoord j u) z) ∧
    (Work.CR.Flat.dbarCoord j (fiberBeurling R j u) z = Work.CR.Flat.dCoord j u z) ∧
    (∀ k : Fin n, k ≠ j → Work.CR.Flat.dCoord k (fiberBeurling R j u) z
        = fiberBeurling R j (Work.CR.Flat.dCoord k u) z) ∧
    (∀ k : Fin n, k ≠ j → Work.CR.Flat.dbarCoord k (fiberBeurling R j u) z
        = fiberBeurling R j (Work.CR.Flat.dbarCoord k u) z) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  -- the open set on which the fibre identities hold
  have hopen : IsOpen {y : Cn n | ‖y j‖ < R} :=
    isOpen_lt ((continuous_apply j).norm) continuous_const
  have hzmem : z ∈ {y : Cn n | ‖y j‖ < R} := hz
  have hmem : ∀ᶠ y in 𝓝 z, ‖y j‖ < R := hopen.mem_nhds hzmem
  -- the potential is `C²` near `z`
  have hPot2 : ContDiffAt ℝ 2 (fiberPot R j u) z :=
    (contDiff_fiberPot R 2 j hu).contDiffAt (hopen.mem_nhds hzmem)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fiberBeurling_dCoord_integral hR j hu z j, fiberBeurling_eq_shiftIntegral]
  · -- `∂̄_j (fiberBeurling) = ∂_j u`: commute the two Wirtinger operators for the potential
    have h1 : fiberBeurling R j u =ᶠ[𝓝 z] fun y => Work.CR.Flat.dCoord j (fiberPot R j u) y := by
      filter_upwards [hmem] with y hy
      exact (dCoord_fiberPot_self hR j hu1 hband hy).symm
    have h2 : (fun y => Work.CR.Flat.dbarCoord j (fiberPot R j u) y) =ᶠ[𝓝 z] u := by
      filter_upwards [hmem] with y hy
      exact fiberPot_dbarCoord_self R hR j hu1 hy
    rw [Work.CR.Flat.dbarCoord, h1.fderiv_eq]
    change Work.CR.Flat.dbarCoord j (fun y => Work.CR.Flat.dCoord j (fiberPot R j u) y) z
      = Work.CR.Flat.dCoord j u z
    rw [Work.CR.Flat.Cauchy.dbarCoord_dCoord_comm j j (fiberPot R j u) z hPot2]
    rw [Work.CR.Flat.dCoord, Work.CR.Flat.dCoord, h2.fderiv_eq]
  · intro k hk
    rw [fiberBeurling_dCoord_integral hR j hu z k, fiberBeurling_eq_shiftIntegral]
  · intro k hk
    rw [fiberBeurling_dbarCoord_integral hR j hu z k, fiberBeurling_eq_shiftIntegral]

/-! ### Infrastructure -/

/-- The first Wirtinger derivatives of a globally `C^{m+1}` function are globally `C^m`. -/
lemma contDiff_dCoord_global {m : ℕ} {w : Cn n → ℂ} (hw : ContDiff ℝ (m + 1) w) (l : Fin n) :
    ContDiff ℝ (m : ℕ∞) (fun z => Work.CR.Flat.dCoord l w z) := by
  have hm : ((m:ℕ):WithTop ℕ∞) + 1 ≤ (((m+1:ℕ)):WithTop ℕ∞) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfd : ContDiff ℝ (m:ℕ∞) (fderiv ℝ w) := hw.fderiv_right hm
  have h := (dCoordLin l).contDiff.comp hfd
  have h1 : (fun z => Work.CR.Flat.dCoord l w z) = (dCoordLin l) ∘ (fderiv ℝ w) := by
    funext z; exact congrFun (Work.NN.Core.dCoord_eq_comp l w) z
  rw [h1]
  exact h

lemma contDiff_dbarCoord_global {m : ℕ} {w : Cn n → ℂ} (hw : ContDiff ℝ (m + 1) w) (l : Fin n) :
    ContDiff ℝ (m : ℕ∞) (fun z => Work.CR.Flat.dbarCoord l w z) := by
  have hm : ((m:ℕ):WithTop ℕ∞) + 1 ≤ (((m+1:ℕ)):WithTop ℕ∞) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfd : ContDiff ℝ (m:ℕ∞) (fderiv ℝ w) := hw.fderiv_right hm
  have h := (Work.CR.Flat.Polydisc.dbarCoordPhi l).contDiff.comp hfd
  have h1 : (fun z => Work.CR.Flat.dbarCoord l w z)
      = (Work.CR.Flat.Polydisc.dbarCoordPhi l) ∘ (fderiv ℝ w) := by
    funext z; exact congrFun (Work.CR.Flat.Polydisc.dbarCoord_eq_comp l w) z
  rw [h1]
  exact h

/-- The band condition is inherited by the first derivatives: a `C¹` function vanishing for
`R ≤ ‖z j‖` has derivatives vanishing there as well.  It vanishes on the *open* exterior
`R < ‖z j‖`, so its derivatives vanish there, and by continuity they vanish on the closure. -/
lemma fiberBand_dCoord {R : ℝ} (hR : 0 < R) {j : Fin n} {v : Cn n → ℂ}
    (hband : fiberBand R j v) (hv : ContDiff ℝ 1 v) (k : Fin n) :
    fiberBand R j (fun z => Work.CR.Flat.dCoord k v z) ∧
      fiberBand R j (fun z => Work.CR.Flat.dbarCoord k v z) := by
  have hfd : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hcd : Continuous fun z => Work.CR.Flat.dCoord k v z :=
    ((Work.NN.Core.dCoordLin k).continuous.comp hfd)
  have hcb : Continuous fun z => Work.CR.Flat.dbarCoord k v z :=
    ((Work.CR.Flat.Polydisc.dbarCoordPhi k).continuous.comp hfd)
  have hT : ∀ z : Cn n, R < ‖z j‖ → v z = 0 := fun z hz => hband z hz.le
  have hTopen : IsOpen {z : Cn n | R < ‖z j‖} :=
    isOpen_lt continuous_const ((continuous_apply j).norm)
  have hdense : ∀ y : Cn n, R ≤ ‖y j‖ →
      y ∈ closure ({z : Cn n | R < ‖z j‖} : Set (Cn n)) := by
    intro y hy
    rw [Metric.mem_closure_iff]
    intro ε hε
    set c : ℝ := ε / (2 * (‖y‖ + 1)) with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    refine ⟨(1 + c) • y, ?_, ?_⟩
    · have hj : ((1 + c) • y) j = (1 + c) * y j := by simp [Pi.smul_apply]
      show R < ‖((1 + c) • y) j‖
      have h1c : (0 : ℝ) ≤ 1 + c := by linarith
      have hnorm : ‖((1 + (c : ℂ)))‖ = 1 + c := by
        have : ((1 : ℂ) + (c : ℂ)) = ((1 + c : ℝ) : ℂ) := by push_cast; ring
        rw [this]; exact Complex.norm_of_nonneg h1c
      rw [hj, norm_mul, hnorm]
      nlinarith [hy, hR, hcpos]
    · rw [dist_eq_norm]
      have key : y - (1 + c) • y = (-c) • y := by
        ext i
        simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul]
        push_cast
        ring
      rw [key, norm_smul]
      have h1 : ‖(-c : ℝ)‖ = c := by
        rw [Real.norm_eq_abs, abs_of_nonpos (by linarith), neg_neg]
      rw [h1]
      have h3 : 0 < ‖y‖ + 1 := by positivity
      have h4 : c * ‖y‖ < ε := by
        rw [hc, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg y]
      exact h4
  constructor
  · intro z hz
    have hZ : IsClosed {y : Cn n | Work.CR.Flat.dCoord k v y = 0} :=
      isClosed_eq hcd continuous_const
    have hsub : closure ({y : Cn n | R < ‖y j‖} : Set (Cn n))
        ⊆ {y : Cn n | Work.CR.Flat.dCoord k v y = 0} := by
      refine hZ.closure_subset_iff.mpr ?_
      intro y hy
      have hmem : {z : Cn n | R < ‖z j‖} ∈ 𝓝 y := hTopen.mem_nhds hy
      have hev : v =ᶠ[𝓝 y] (fun _ => (0 : ℂ)) :=
        Filter.eventually_of_mem hmem (fun z hz => hT z hz)
      exact Work.CR.Flat.Cauchy.dCoord_eq_zero_of_eventuallyEq_zero k hev
    exact hsub (hdense z hz)
  · intro z hz
    have hZ : IsClosed {y : Cn n | Work.CR.Flat.dbarCoord k v y = 0} :=
      isClosed_eq hcb continuous_const
    have hsub : closure ({y : Cn n | R < ‖y j‖} : Set (Cn n))
        ⊆ {y : Cn n | Work.CR.Flat.dbarCoord k v y = 0} := by
      refine hZ.closure_subset_iff.mpr ?_
      intro y hy
      have hmem : {z : Cn n | R < ‖z j‖} ∈ 𝓝 y := hTopen.mem_nhds hy
      have hev : v =ᶠ[𝓝 y] (fun _ => (0 : ℂ)) :=
        Filter.eventually_of_mem hmem (fun z hz => hT z hz)
      exact Work.CR.Flat.Cauchy.dbarCoord_eq_zero_of_eventuallyEq_zero k hev
    exact hsub (hdense z hz)

/-- The fibrewise Beurling transform of band-supported `C^{m+1}` data is `C^m` on the polydisc
`polydisc 0 r` (with `r j < R`): it agrees there with `∂_j (fiberPot R j w)`. -/
lemma contDiffOn_fiberBeurling {R : ℝ} (hR : 0 < R) {j : Fin n} {m : ℕ} {w : Cn n → ℂ}
    {r : Fin n → ℝ} (hrR : r j < R) (hw : ContDiff ℝ (m + 1) w) (hband : fiberBand R j w) :
    ContDiffOn ℝ m (fiberBeurling R j w) (Work.CR.Flat.polydisc 0 r) := by
  have hsub : Work.CR.Flat.polydisc (0 : Cn n) r ⊆ {z : Cn n | ‖z j‖ < R} := by
    intro z hz
    have h := hz j
    simpa using lt_of_lt_of_le h hrR.le
  have hP : ContDiffOn ℝ (m + 1) (fiberPot R j w) (Work.CR.Flat.polydisc 0 r) :=
    (contDiff_fiberPot R (m + 1) j hw).mono hsub
  have hm : ((m:ℕ):WithTop ℕ∞) + 1 ≤ (((m+1:ℕ)):WithTop ℕ∞) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfd : ContDiffOn ℝ (m:ℕ∞) (fun z => fderiv ℝ (fiberPot R j w) z)
      (Work.CR.Flat.polydisc 0 r) :=
    hP.fderiv_of_isOpen (Work.CR.Flat.isOpen_polydisc 0 r) hm
  have hcomp : ContDiffOn ℝ (m:ℕ∞) (fun z => dCoordLin j (fderiv ℝ (fiberPot R j w) z))
      (Work.CR.Flat.polydisc 0 r) := (dCoordLin j).contDiff.comp_contDiffOn hfd
  refine hcomp.congr fun z hz => ?_
  have hzR : ‖z j‖ < R := hsub hz
  have hw1 : ContDiff ℝ 1 w :=
    hw.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega))
  have h := dCoord_fiberPot_self hR j hw1 hband hzR
  have h2 : Work.CR.Flat.dCoord j (fiberPot R j w) z
      = dCoordLin j (fderiv ℝ (fiberPot R j w) z) := congrFun (dCoord_eq_comp j _) z
  exact h.symm.trans h2

/-- **The induction.**  For every `m` there is a single constant controlling both the fixed-disc
potential of band-supported `C^m` data on `C^{m,α}`, and the fibrewise Beurling transform of
band-supported `C^{m+1}` data on `C^{m,α}` (one order lower, since it is a derivative of the
potential).  The step uses the `n`-dimensional Wirtinger estimate `holderNorm_le_wirtinger_coord_on`
together with the identities `∂̄_j (fiberPot) = w`, `∂_j (fiberPot) = fiberBeurling` and
`∂_k (fiberPot) = fiberPot (∂_k w)` (`k ≠ j`), and the Wirtinger identities for
`fiberBeurling`. -/
theorem fiberPot_fiberBeurling_induction {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα : 0 < α)
    (hα1 : α < 1) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ w : Cn n → ℂ, ContDiff ℝ m w → fiberBand R j w →
        Work.CR.Flat.holderNorm m α (fiberPot R j w) (Work.CR.Flat.polydisc 0 r)
          ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm m α w (fiberAccess r j R)) ∧
      (∀ w : Cn n → ℂ, ContDiff ℝ (m + 1) w → fiberBand R j w →
        Work.CR.Flat.holderNorm m α (fiberBeurling R j w) (Work.CR.Flat.polydisc 0 r)
          ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm (m + 1) α w (fiberAccess r j R)) := by
  induction m with
  | zero =>
    obtain ⟨C₀, hC₀, hP₀⟩ := holderNorm_zero_fiberPot_le hR j hα hα1 hr hrR
    obtain ⟨D₀, hD₀, hS₀⟩ := holderNorm_zero_fiberBeurling_le hR j hα hα1 hr hrR
    refine ⟨max C₀ D₀, lt_max_of_lt_left hC₀, ?_, ?_⟩
    · intro w hw hband
      exact (hP₀ w hw hband).trans
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (le_refl _))
    · intro w hw hband
      exact (hS₀ w hw hband).trans
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) (le_refl _))
  | succ m ih =>
    obtain ⟨Cm, hCm, hPm, hSm⟩ := ih
    obtain ⟨C₀, hC₀, hP₀⟩ := holderNorm_zero_fiberPot_le hR j hα hα1 hr hrR
    obtain ⟨D₀, hD₀, hS₀⟩ := holderNorm_zero_fiberBeurling_le hR j hα hα1 hr hrR
    obtain ⟨K, hK, hW⟩ := holderNorm_le_wirtinger_coord_on (n := n) m (α := α)
      (Ω := Work.CR.Flat.polydisc 0 r) (Work.CR.Flat.isOpen_polydisc 0 r)
    obtain ⟨C1, hC1, hR8a⟩ := exists_holderNorm_wirtinger_le (n := n) (m + 1) (α := α)
      (Ω := fiberAccess r j R) (fiberAccess_isOpen r j R)
    obtain ⟨C2, hC2, hR8b⟩ := exists_holderNorm_wirtinger_le (n := n) m (α := α)
      (Ω := fiberAccess r j R) (fiberAccess_isOpen r j R)
    set Ω : Set (Cn n) := Work.CR.Flat.polydisc 0 r with hΩdef
    set A : Set (Cn n) := fiberAccess r j R with hAdef
    have hΩopen : IsOpen Ω := by rw [hΩdef]; exact Work.CR.Flat.isOpen_polydisc 0 r
    have hAopen : IsOpen A := by rw [hAdef]; exact fiberAccess_isOpen r j R
    have hΩA : Ω ⊆ A := by rw [hΩdef, hAdef]; exact polydisc_subset_fiberAccess (hrR j)
    -- the constants of the step
    set E : ℝ := max (Cm * C1) C2 with hEdef
    have hEpos : 0 < E := lt_max_of_lt_left (mul_pos hCm hC1)
    have hEnn : 0 ≤ E := hEpos.le
    have hECm : Cm * C1 ≤ E := le_max_left _ _
    have hEC2 : C2 ≤ E := le_max_right _ _
    have h2Enn : (0 : ℝ) ≤ 2 * E := by linarith
    set E' : ℝ := max 1 (max Cm (Cm * C2)) with hE'def
    have hE'pos : 0 < E' := lt_max_of_lt_left one_pos
    have hE'nn : 0 ≤ E' := hE'pos.le
    have hE'1 : (1:ℝ) ≤ E' := le_max_left _ _
    have hE'Cm : Cm ≤ E' :=
      le_trans (le_max_left Cm (Cm * C2)) (le_max_right (1:ℝ) (max Cm (Cm * C2)))
    have hE'CmC2 : Cm * C2 ≤ E' :=
      le_trans (le_max_right Cm (Cm * C2)) (le_max_right (1:ℝ) (max Cm (Cm * C2)))
    have h2E'nn : (0 : ℝ) ≤ 2 * E' := by linarith
    set DP : ℝ := (K + 1) * (C₀ + (n : ℝ) * (2 * E') + 1) + 1 with hDPdef
    set DS : ℝ := (K + 1) * (D₀ + (n : ℝ) * (2 * E) + 1) + 1 with hDSdef
    have hnP : (0 : ℝ) ≤ (n : ℝ) * (2 * E') := mul_nonneg (Nat.cast_nonneg n) h2E'nn
    have hnS : (0 : ℝ) ≤ (n : ℝ) * (2 * E) := mul_nonneg (Nat.cast_nonneg n) h2Enn
    have hDPpos : 0 < DP := by
      rw [hDPdef]; nlinarith [hK, hC₀, hnP]
    have hDSpos : 0 < DS := by
      rw [hDSdef]; nlinarith [hK, hD₀, hnS]
    have hDPbase : C₀ ≤ DP := by
      rw [hDPdef]; nlinarith [hK, hC₀, hnP]
    have hDPscale : K * (C₀ + (n : ℝ) * (2 * E')) ≤ DP := by
      rw [hDPdef]; nlinarith [hK, hC₀, hnP]
    have hDSbase : D₀ ≤ DS := by
      rw [hDSdef]; nlinarith [hK, hD₀, hnS]
    have hDSscale : K * (D₀ + (n : ℝ) * (2 * E)) ≤ DS := by
      rw [hDSdef]; nlinarith [hK, hD₀, hnS]
    refine ⟨max DS DP, lt_max_of_lt_left hDSpos, ?_, ?_⟩
    · -- the fixed-disc potential
      intro w hw hband
      have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
      have hPsmooth : ContDiffOn ℝ (m + 1) (fiberPot R j w) Ω := by
        rw [hΩdef]
        refine (contDiff_fiberPot R (m + 1) j hw).mono ?_
        intro z hz
        have h := hz j
        simpa using lt_of_lt_of_le h (hrR j).le
      have hWir := hW (fiberPot R j w) hPsmooth
      have hmonoP0 : Work.CR.Flat.holderNorm 0 α w A ≤ Work.CR.Flat.holderNorm (m + 1) α w A :=
        Work.CR.Flat.holderNorm_mono_k (Nat.zero_le (m + 1)) α w A
      have hmonoPm : Work.CR.Flat.holderNorm m α w A ≤ Work.CR.Flat.holderNorm (m + 1) α w A :=
        Work.CR.Flat.holderNorm_mono_k (Nat.le_succ m) α w A
      have hbase : Work.CR.Flat.holderNorm 0 α (fiberPot R j w) Ω
          ≤ ENNReal.ofReal C₀ * Work.CR.Flat.holderNorm (m + 1) α w A := by
        refine (hP₀ w (hw.of_le (by exact_mod_cast (by omega : 0 ≤ m + 1))) hband).trans ?_
        exact mul_le_mul' (le_refl (ENNReal.ofReal C₀)) hmonoP0
      have hsum : ∑ l : Fin n,
            (Work.CR.Flat.holderNorm m α
                (fun z => Work.CR.Flat.dCoord l (fiberPot R j w) z) Ω
              + Work.CR.Flat.holderNorm m α
                (fun z => Work.CR.Flat.dbarCoord l (fiberPot R j w) z) Ω)
          ≤ ENNReal.ofReal ((n : ℝ) * (2 * E')) * Work.CR.Flat.holderNorm (m + 1) α w A := by
        refine sum_fin_le_ofReal_mul (E := 2 * E') h2E'nn fun l => ?_
        refine add_le_ofReal_two_mul hE'nn ?_ ?_
        · -- `∂_l` of the potential
          rcases eq_or_ne l j with hl | hl
          · rw [hl]
            have hcong : Work.CR.Flat.holderNorm m α
                  (fun z => Work.CR.Flat.dCoord j (fiberPot R j w) z) Ω
                = Work.CR.Flat.holderNorm m α (fiberBeurling R j w) Ω := by
              refine holderNorm_congr fun z hz => ?_
              have hzR : ‖z j‖ < R := by
                have h : z ∈ Work.CR.Flat.polydisc (0:Cn n) r := by rw [← hΩdef]; exact hz
                have h' := h j
                simpa using lt_of_lt_of_le h' (hrR j).le
              exact dCoord_fiberPot_self hR j hw1 hband hzR
            rw [hcong]
            exact (hSm w hw hband).trans
              (mul_le_mul' (ENNReal.ofReal_le_ofReal hE'Cm) (le_refl _))
          · have hcong : Work.CR.Flat.holderNorm m α
                  (fun z => Work.CR.Flat.dCoord l (fiberPot R j w) z) Ω
                = Work.CR.Flat.holderNorm m α
                    (fiberPot R j (fun z => Work.CR.Flat.dCoord l w z)) Ω := by
              refine holderNorm_congr fun z hz => ?_
              have hzOz : z ∈ Ω := hz
              have hd : DifferentiableAt ℝ (fiberPot R j w) z :=
                (hPsmooth.differentiableOn (by simp)).differentiableAt (hΩopen.mem_nhds hzOz)
              exact dCoord_fiberPot R j hl hw1 z hd
            rw [hcong]
            refine (hPm _ (contDiff_dCoord_global hw l)
                (fiberBand_dCoord hR hband hw1 l).1).trans ?_
            refine (mul_le_mul' (le_refl _)
              (hR8b w (hw.contDiffOn.mono (Set.subset_univ A)) l).2).trans ?_
            rw [← mul_assoc, ← ENNReal.ofReal_mul hCm.le]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal hE'CmC2) (le_refl _)
        · -- `∂̄_l` of the potential
          rcases eq_or_ne l j with hl | hl
          · rw [hl]
            have hcong : Work.CR.Flat.holderNorm m α
                  (fun z => Work.CR.Flat.dbarCoord j (fiberPot R j w) z) Ω
                = Work.CR.Flat.holderNorm m α w Ω := by
              refine holderNorm_congr fun z hz => ?_
              have hzR : ‖z j‖ < R := by
                have h : z ∈ Work.CR.Flat.polydisc (0:Cn n) r := by rw [← hΩdef]; exact hz
                have h' := h j
                simpa using lt_of_lt_of_le h' (hrR j).le
              exact fiberPot_dbarCoord_self R hR j hw1 hzR
            rw [hcong]
            refine (Work.CR.Flat.holderNorm_mono_set hAopen hΩopen hΩA m α w).trans ?_
            have hone : Work.CR.Flat.holderNorm m α w A
                = ENNReal.ofReal (1 : ℝ) * Work.CR.Flat.holderNorm m α w A := by
              rw [ENNReal.ofReal_one, one_mul]
            rw [hone]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal hE'1) hmonoPm
          · have hcong : Work.CR.Flat.holderNorm m α
                  (fun z => Work.CR.Flat.dbarCoord l (fiberPot R j w) z) Ω
                = Work.CR.Flat.holderNorm m α
                    (fiberPot R j (fun z => Work.CR.Flat.dbarCoord l w z)) Ω := by
              refine holderNorm_congr fun z hz => ?_
              have hzOz : z ∈ Ω := hz
              have hd : DifferentiableAt ℝ (fiberPot R j w) z :=
                (hPsmooth.differentiableOn (by simp)).differentiableAt (hΩopen.mem_nhds hzOz)
              exact fiberPot_dbarCoord R j hl hw1 z hd
            rw [hcong]
            refine (hPm _ (contDiff_dbarCoord_global hw l)
                (fiberBand_dCoord hR hband hw1 l).2).trans ?_
            refine (mul_le_mul' (le_refl _)
              (hR8b w (hw.contDiffOn.mono (Set.subset_univ A)) l).1).trans ?_
            rw [← mul_assoc, ← ENNReal.ofReal_mul hCm.le]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal hE'CmC2) (le_refl _)
      have hcomb := add_le_ofReal_mul hC₀.le hnP hbase hsum
      have hstep : ENNReal.ofReal K * (Work.CR.Flat.holderNorm 0 α (fiberPot R j w) Ω
            + ∑ l : Fin n,
              (Work.CR.Flat.holderNorm m α
                  (fun z => Work.CR.Flat.dCoord l (fiberPot R j w) z) Ω
                + Work.CR.Flat.holderNorm m α
                  (fun z => Work.CR.Flat.dbarCoord l (fiberPot R j w) z) Ω))
          ≤ ENNReal.ofReal (max DS DP) * Work.CR.Flat.holderNorm (m + 1) α w A := by
        calc ENNReal.ofReal K * (Work.CR.Flat.holderNorm 0 α (fiberPot R j w) Ω
              + ∑ l : Fin n,
                (Work.CR.Flat.holderNorm m α
                    (fun z => Work.CR.Flat.dCoord l (fiberPot R j w) z) Ω
                  + Work.CR.Flat.holderNorm m α
                    (fun z => Work.CR.Flat.dbarCoord l (fiberPot R j w) z) Ω))
            ≤ ENNReal.ofReal (K * (C₀ + (n : ℝ) * (2 * E')))
                * Work.CR.Flat.holderNorm (m + 1) α w A :=
              ofReal_mul_le_mul hK.le (add_nonneg hC₀.le hnP) hcomb
          _ ≤ ENNReal.ofReal (max DS DP) * Work.CR.Flat.holderNorm (m + 1) α w A :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal (le_trans hDPscale (le_max_right _ _))) le_rfl
      exact hWir.trans hstep
    · -- the fibrewise Beurling transform
      intro w hw hband
      have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast (by omega : 1 ≤ m + 2))
      have hw2 : ContDiff ℝ 2 w := hw.of_le (by exact_mod_cast (by omega : 2 ≤ m + 2))
      have hGs : ContDiffOn ℝ (m + 1) (fiberBeurling R j w) Ω :=
        contDiffOn_fiberBeurling hR (hrR := hrR j) (m := m + 1) hw hband
      have hwon : ContDiffOn ℝ (m + 1) w A :=
        (hw.of_le (by exact_mod_cast (by omega : m + 1 ≤ m + 2))).contDiffOn.mono
          (Set.subset_univ A)
      have hWir := hW (fiberBeurling R j w) hGs
      have hN : Work.CR.Flat.holderNorm (m + 1) α w A
          ≤ Work.CR.Flat.holderNorm (m + 2) α w A :=
        Work.CR.Flat.holderNorm_mono_k (Nat.le_succ (m + 1)) α w A
      have hmonoS1 : Work.CR.Flat.holderNorm 1 α w A
          ≤ Work.CR.Flat.holderNorm (m + 2) α w A :=
        Work.CR.Flat.holderNorm_mono_k (by omega) α w A
      have hbase : Work.CR.Flat.holderNorm 0 α (fiberBeurling R j w) Ω
          ≤ ENNReal.ofReal D₀ * Work.CR.Flat.holderNorm (m + 2) α w A := by
        refine (hS₀ w (hw.of_le (by exact_mod_cast (by omega : 1 ≤ m + 2))) hband).trans ?_
        exact mul_le_mul' (le_refl (ENNReal.ofReal D₀)) hmonoS1
      have hsum : ∑ l : Fin n,
            (Work.CR.Flat.holderNorm m α
                (fun z => Work.CR.Flat.dCoord l (fiberBeurling R j w) z) Ω
              + Work.CR.Flat.holderNorm m α
                (fun z => Work.CR.Flat.dbarCoord l (fiberBeurling R j w) z) Ω)
          ≤ ENNReal.ofReal ((n : ℝ) * (2 * E)) * Work.CR.Flat.holderNorm (m + 2) α w A := by
        refine sum_fin_le_ofReal_mul (E := 2 * E) h2Enn fun l => ?_
        refine add_le_ofReal_two_mul hEnn ?_ ?_
        · -- `∂_l` of `fiberBeurling`
          rcases eq_or_ne l j with hl | hl
          · rw [hl]
            have hcong : Work.CR.Flat.holderNorm m α
                  (fun z => Work.CR.Flat.dCoord j (fiberBeurling R j w) z) Ω
                = Work.CR.Flat.holderNorm m α
                    (fiberBeurling R j (fun z => Work.CR.Flat.dCoord j w z)) Ω := by
              refine holderNorm_congr fun z hz => ?_
              have hzR : ‖z j‖ < R := by
                have h : z ∈ Work.CR.Flat.polydisc (0:Cn n) r := by rw [← hΩdef]; exact hz
                have h' := h j
                simpa using lt_of_lt_of_le h' (hrR j).le
              exact (fiberBeurling_wirtinger_band hR j hw2 hband hzR).1
            rw [hcong]
            refine (hSm _ (contDiff_dCoord_global hw j)
                (fiberBand_dCoord hR hband hw1 j).1).trans ?_
            refine (mul_le_mul' (le_refl _)
              (hR8a w (hw.contDiffOn.mono (Set.subset_univ A)) j).2).trans ?_
            rw [← mul_assoc, ← ENNReal.ofReal_mul hCm.le]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal hECm) (le_refl _)
          · have hcong : Work.CR.Flat.holderNorm m α
                  (fun z => Work.CR.Flat.dCoord l (fiberBeurling R j w) z) Ω
                = Work.CR.Flat.holderNorm m α
                    (fiberBeurling R j (fun z => Work.CR.Flat.dCoord l w z)) Ω := by
              refine holderNorm_congr fun z hz => ?_
              have hzR : ‖z j‖ < R := by
                have h : z ∈ Work.CR.Flat.polydisc (0:Cn n) r := by rw [← hΩdef]; exact hz
                have h' := h j
                simpa using lt_of_lt_of_le h' (hrR j).le
              exact (fiberBeurling_wirtinger_band hR j hw2 hband hzR).2.2.1 l hl
            rw [hcong]
            refine (hSm _ (contDiff_dCoord_global hw l)
                (fiberBand_dCoord hR hband hw1 l).1).trans ?_
            refine (mul_le_mul' (le_refl _)
              (hR8a w (hw.contDiffOn.mono (Set.subset_univ A)) l).2).trans ?_
            rw [← mul_assoc, ← ENNReal.ofReal_mul hCm.le]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal hECm) (le_refl _)
        · -- `∂̄_l` of `fiberBeurling`
          rcases eq_or_ne l j with hl | hl
          · rw [hl]
            have hcong : Work.CR.Flat.holderNorm m α
                  (fun z => Work.CR.Flat.dbarCoord j (fiberBeurling R j w) z) Ω
                = Work.CR.Flat.holderNorm m α (fun z => Work.CR.Flat.dCoord j w z) Ω := by
              refine holderNorm_congr fun z hz => ?_
              have hzR : ‖z j‖ < R := by
                have h : z ∈ Work.CR.Flat.polydisc (0:Cn n) r := by rw [← hΩdef]; exact hz
                have h' := h j
                simpa using lt_of_lt_of_le h' (hrR j).le
              exact (fiberBeurling_wirtinger_band hR j hw2 hband hzR).2.1
            rw [hcong]
            refine (Work.CR.Flat.holderNorm_mono_set hAopen hΩopen hΩA m α
                (fun z => Work.CR.Flat.dCoord j w z)).trans ?_
            exact ((hR8b w hwon j).2).trans
              (mul_le_mul' (ENNReal.ofReal_le_ofReal hEC2) hN)
          · have hcong : Work.CR.Flat.holderNorm m α
                  (fun z => Work.CR.Flat.dbarCoord l (fiberBeurling R j w) z) Ω
                = Work.CR.Flat.holderNorm m α
                    (fiberBeurling R j (fun z => Work.CR.Flat.dbarCoord l w z)) Ω := by
              refine holderNorm_congr fun z hz => ?_
              have hzR : ‖z j‖ < R := by
                have h : z ∈ Work.CR.Flat.polydisc (0:Cn n) r := by rw [← hΩdef]; exact hz
                have h' := h j
                simpa using lt_of_lt_of_le h' (hrR j).le
              exact (fiberBeurling_wirtinger_band hR j hw2 hband hzR).2.2.2 l hl
            rw [hcong]
            refine (hSm _ (contDiff_dbarCoord_global hw l)
                (fiberBand_dCoord hR hband hw1 l).2).trans ?_
            refine (mul_le_mul' (le_refl _)
              (hR8a w (hw.contDiffOn.mono (Set.subset_univ A)) l).1).trans ?_
            rw [← mul_assoc, ← ENNReal.ofReal_mul hCm.le]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal hECm) (le_refl _)
      have hcomb := add_le_ofReal_mul hD₀.le hnS hbase hsum
      have hstep : ENNReal.ofReal K * (Work.CR.Flat.holderNorm 0 α (fiberBeurling R j w) Ω
            + ∑ l : Fin n,
              (Work.CR.Flat.holderNorm m α
                  (fun z => Work.CR.Flat.dCoord l (fiberBeurling R j w) z) Ω
                + Work.CR.Flat.holderNorm m α
                  (fun z => Work.CR.Flat.dbarCoord l (fiberBeurling R j w) z) Ω))
          ≤ ENNReal.ofReal (max DS DP) * Work.CR.Flat.holderNorm (m + 2) α w A := by
        calc ENNReal.ofReal K * (Work.CR.Flat.holderNorm 0 α (fiberBeurling R j w) Ω
              + ∑ l : Fin n,
                (Work.CR.Flat.holderNorm m α
                    (fun z => Work.CR.Flat.dCoord l (fiberBeurling R j w) z) Ω
                  + Work.CR.Flat.holderNorm m α
                    (fun z => Work.CR.Flat.dbarCoord l (fiberBeurling R j w) z) Ω))
            ≤ ENNReal.ofReal (K * (D₀ + (n : ℝ) * (2 * E)))
                * Work.CR.Flat.holderNorm (m + 2) α w A :=
              ofReal_mul_le_mul hK.le (add_nonneg hD₀.le hnS) hcomb
          _ ≤ ENNReal.ofReal (max DS DP) * Work.CR.Flat.holderNorm (m + 2) α w A :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal (le_trans hDSscale (le_max_left _ _))) le_rfl
      exact hWir.trans hstep

end

end Work.NN.Core
