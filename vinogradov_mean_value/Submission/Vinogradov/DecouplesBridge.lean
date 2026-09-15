/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.FromDecLin
import Submission.Commons.Analysis.Inequalities.sum_rpow_le_card_mul_sum_rpow
import Submission.Commons.Analysis.Integral.weighted_l2_minkowski_rpow
import Submission.Vinogradov.BallInflation
import Submission.Commons.Measure.Integral.lintegral_ell2_minkowski_rpow
import Submission.Commons.Analysis.Integral.lp_ell2_minkowski_real
import Submission.Commons.Measure.Integral.integral_smoothing_rpow_le_of_integrable
import Submission.Commons.Measure.Integral.integral_integral_swap_of_lintegral_bound

/-!
# From the GLYZ decoupling theorem to BDG's discrete restriction theorem

This module assembles the **localisation bridge**: it deduces BDG's Theorem 1.2 in the
ball-weighted form (`bdg_thm_ntmain`) from the ℓ²-decoupling inequality of
Guo–Li–Yung–Zorin-Kranich (arXiv:1912.09798, Theorem 1.1) in the form in which this
repository states it after the localisation, i.e. with plates that are *enlarged by the
fixed factor `2`* (`DecLinScale k N 2 K`, see `FromDecLin.lean`).

The mechanism is the standard one: localise the pieces `E_{J_i}g` of the extension operator
to a ball by multiplying with the dilated localisation weight `locWeight k c' (ΛR)` (whose
Fourier transform is supported in a ball of radius `≲ 1/R`, small enough for the localised
pieces to stay inside the plates after the enlargement), apply the decoupling inequality for
each centre `c'`, and turn the `c'`-average back into the ball weight with the transfer
estimate `exists_locWeight_transfer_pow`.

The declarations in this module:

* `critQ k = k(k+1)` — the critical exponent in real form;
* `lpNorm_pow_eq_lintegral`, `ofReal_lpNorm_pow` — the conversion between the extended
  (`ℝ≥0∞`) `L^p`-norm used by the GLYZ chain and the ordinary real integrals;
* `integrable_locWeight_mul_pow` — the localised pieces have integrable `Q`-th powers;
* `decoupling_real` — the decoupling inequality with ordinary integrals.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal Interval

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Submission.Vinogradov


/-- The critical exponent `k(k+1)` of the moment curve in real form. -/
def critQ (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) + 1)

@[simp] lemma critQ_eq (k : ℕ) : critQ k = (k : ℝ) * ((k : ℝ) + 1) := rfl
lemma two_le_critQ {k : ℕ} (hk : 1 ≤ k) : 2 ≤ critQ k := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  rw [critQ_eq]; nlinarith
lemma critQ_pos {k : ℕ} (hk : 1 ≤ k) : 0 < critQ k := lt_of_lt_of_le (by norm_num) (two_le_critQ hk)

/-- The critical power of the extended `L^p` norm is the integral of the `Q`-th power. -/
lemma lpNorm_pow_eq_lintegral (k : ℕ) (hk : 1 ≤ k) (f : E k → ℂ) :
    (lpNorm k (pE k) f) ^ (critQ k)
      = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ critQ k) := by
  have hcast : (((k * (k + 1) : ℕ) : ℝ≥0) : ℝ) = critQ k := by
    rw [critQ_eq]; push_cast; ring
  have hq : ((k * (k + 1) : ℕ) : ℝ≥0) ≠ 0 := by
    rw [ne_eq, Nat.cast_eq_zero]
    exact fun h => pE_ne_zero hk (by rw [pE]; exact_mod_cast h)
  rw [lpNorm, pE, ← hcast]
  rw [eLpNorm_nnreal_pow_eq_lintegral (p := ((k * (k+1) : ℕ) : ℝ≥0)) hq]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm (f x)]
  exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
    (by positivity : (0:ℝ) ≤ (((k * (k+1) : ℕ) : ℝ≥0) : ℝ))


/-- The localised piece `Φ·F` has an integrable `Q`-th power, for `Q ≥ 1` and `F` bounded. -/
lemma integrable_locWeight_mul_pow (k : ℕ) (hk : 1 ≤ k) {Q : ℝ} (hQ : 1 ≤ Q) {R : ℝ}
    (hR : 0 < R) (c' : E k) {F : E k → ℂ} (hFm : AEStronglyMeasurable F volume) {M : ℝ}
    (hM : ∀ x, ‖F x‖ ≤ M) :
    Integrable (fun x : E k => ‖locWeight k c' R x * F x‖ ^ Q) volume := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM c')
  have hL : Integrable (fun x : E k => ‖locWeight k c' R x‖ ^ Q) volume := by
    have h := (memLp_locWeight k c' hR (p := Q) (by linarith : (0:ℝ) ≤ Q)).integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr (by linarith : (0:ℝ) < Q)).ne' ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ Q)] using h
  refine (hL.const_mul (M ^ Q)).mono' ?_ ?_
  · have hinner : AEMeasurable (fun x : E k => ‖locWeight k c' R x * F x‖) volume :=
      (((continuous_locWeight k c' R).aestronglyMeasurable.mul hFm).aemeasurable).norm
    exact (hinner.pow_const Q).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity), norm_mul, mul_comm ‖locWeight k c' R x‖,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (hM x) (le_trans zero_le_one hQ)) (by positivity)


/-- The `Q`-th power of the extended `L^p` norm as the integral of the `Q`-th power. -/
lemma ofReal_lpNorm_pow (k : ℕ) (hk : 1 ≤ k) {F : E k → ℂ}
    (hF : Integrable (fun x => ‖F x‖ ^ critQ k) volume) :
    (lpNorm k (pE k) F) ^ (critQ k) = ENNReal.ofReal (∫ x, ‖F x‖ ^ critQ k) := by
  rw [lpNorm_pow_eq_lintegral k hk]
  exact (ofReal_integral_eq_lintegral_ofReal hF
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) (critQ k))).symm

/-- **Decoupling in real-integral form**: the extended-`L^p` form of the ℓ²-decoupling
inequality implies the same inequality with ordinary integrals. -/
theorem decoupling_real (k : ℕ) (hk : 1 ≤ k) {m : ℕ} {K : ℝ} (hK : 0 ≤ K)
    {f : Fin m → E k → ℂ}
    (hD : lpNorm k (pE k) (fun x => ∑ i, f i x)
        ≤ ENNReal.ofReal K * l2Norm (fun i => lpNorm k (pE k) (f i)))
    (hA : Integrable (fun x => ‖∑ i, f i x‖ ^ critQ k) volume)
    (hBi : ∀ i, Integrable (fun x => ‖f i x‖ ^ critQ k) volume) :
    (∫ x, ‖∑ i, f i x‖ ^ critQ k) ^ (1 / critQ k)
      ≤ K * (∑ i, (∫ x, ‖f i x‖ ^ critQ k) ^ (2 / critQ k)) ^ ((1 : ℝ) / 2) := by
  have hQ2 : 2 ≤ critQ k := two_le_critQ hk
  have hQ0 : 0 < critQ k := lt_of_lt_of_le (by norm_num) hQ2
  have hQle : (0 : ℝ) ≤ critQ k := hQ0.le
  have hQne : critQ k ≠ 0 := ne_of_gt hQ0
  have h2e : critQ k * (2 / critQ k) = 2 := by
    rw [mul_div_assoc', mul_comm (critQ k) 2, mul_div_cancel_right₀ 2 hQne]
  have hA0 : 0 ≤ ∫ x, ‖∑ i, f i x‖ ^ critQ k :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hB0 : ∀ i, 0 ≤ ∫ x, ‖f i x‖ ^ critQ k :=
    fun i => integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hlpA := ofReal_lpNorm_pow k hk hA
  have hlpB : ∀ i, (lpNorm k (pE k) (f i)) ^ (critQ k)
      = ENNReal.ofReal (∫ x, ‖f i x‖ ^ critQ k) := fun i => ofReal_lpNorm_pow k hk (hBi i)
  have hl2 : (l2Norm (fun i => lpNorm k (pE k) (f i))) ^ (critQ k)
      = ENNReal.ofReal ((∑ i, (∫ x, ‖f i x‖ ^ critQ k) ^ (2 / critQ k)) ^ (critQ k / 2)) := by
    have hsum : (∑ i, (lpNorm k (pE k) (f i)) ^ (2 : ℝ))
        = ENNReal.ofReal (∑ i, (∫ x, ‖f i x‖ ^ critQ k) ^ (2 / critQ k)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (hB0 i) _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have haux : (lpNorm k (pE k) (f i)) ^ (2 : ℝ)
          = ((lpNorm k (pE k) (f i)) ^ (critQ k)) ^ (2 / critQ k) := by
        rw [← ENNReal.rpow_mul, h2e]
      rw [haux, hlpB i, ENNReal.ofReal_rpow_of_nonneg (hB0 i) (by positivity)]
    rw [l2Norm, hsum, ← ENNReal.rpow_mul]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hB0 i) _) (by positivity)]
    congr 1
    ring
  have hstep : ENNReal.ofReal (∫ x, ‖∑ i, f i x‖ ^ critQ k)
      ≤ ENNReal.ofReal (K ^ critQ k
          * (∑ i, (∫ x, ‖f i x‖ ^ critQ k) ^ (2 / critQ k)) ^ (critQ k / 2)) := by
    rw [← hlpA]
    refine (ENNReal.rpow_le_rpow hD hQle).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hQle, ENNReal.ofReal_rpow_of_nonneg hK hQle, hl2,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ K ^ critQ k)]
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hstep
  have hroot : (∫ x, ‖∑ i, f i x‖ ^ critQ k) ^ (1 / critQ k)
      ≤ K * (∑ i, (∫ x, ‖f i x‖ ^ critQ k) ^ (2 / critQ k)) ^ ((1 : ℝ) / 2) := by
    have h1 : (∫ x, ‖∑ i, f i x‖ ^ critQ k) ^ (1 / critQ k)
        ≤ (K ^ critQ k * (∑ i, (∫ x, ‖f i x‖ ^ critQ k) ^ (2 / critQ k))
            ^ (critQ k / 2)) ^ (1 / critQ k) :=
      Real.rpow_le_rpow hA0 hstep (by positivity)
    refine h1.trans (le_of_eq ?_)
    have hZ0 : 0 ≤ ∑ i, (∫ x, ‖f i x‖ ^ critQ k) ^ (2 / critQ k) :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hB0 i) _
    have hKQ : (K ^ critQ k) ^ (1 / critQ k) = K := by
      have he : critQ k * (1 / critQ k) = 1 := by field_simp
      rw [← Real.rpow_mul hK, he, Real.rpow_one]
    have hZQ : ((∑ i, (∫ x, ‖f i x‖ ^ critQ k) ^ (2 / critQ k)) ^ (critQ k / 2))
        ^ (1 / critQ k) = (∑ i, (∫ x, ‖f i x‖ ^ critQ k) ^ (2 / critQ k)) ^ ((1 : ℝ) / 2) := by
      have he : critQ k / 2 * (1 / critQ k) = 1 / 2 := by field_simp
      rw [← Real.rpow_mul hZ0, he]
    rw [Real.mul_rpow (by positivity) (by positivity), hKQ, hZQ]
  exact hroot


/-! ## The localised decoupling inequality -/

/-- The `Q`-th power of the localised piece `ψ·F` (`ψ` the dilation-`R` weight at `c'`):
`∫ ‖ψ·F‖^Q`.  Factored out so that the elaborator does not have to unfold it repeatedly. -/
noncomputable def localisedPow (k : ℕ) (c' : E k) (R Q : ℝ) (F : E k → ℂ) : ℝ :=
  ∫ x : E k, ‖locWeight k c' R x * F x‖ ^ Q

lemma localisedPow_nonneg (k : ℕ) (c' : E k) (R Q : ℝ) (F : E k → ℂ) :
    0 ≤ localisedPow k c' R Q F :=
  integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _

/-- **The localised decoupling inequality**: for a fixed centre `c'`, the `L^Q`-norm of
`E_{[0,1]}g` over the ball `B(c',R)` is bounded by the `ℓ²`-sum of the localised pieces
`‖locWeight k c' (lwScale k * R)·E_{J_i}g‖_{L^Q}`.  This is `DecLinScale k N 2 K` applied to
the tuple `(locWeight · E_{J_i}g)_i`, whose members lie in the class of the enlarged plate
`plate k (1/N) (pieceCenter N i)` by `FromDecLin.localised_piece_isFourierRep`. -/
theorem localised_decoupling (k : ℕ) (hk : 1 ≤ k) {N : ℕ} (hN : 1 ≤ N) {R : ℝ}
    (hR : (N : ℝ) ^ k ≤ R) {K : ℝ} (hK : 0 ≤ K) (hD : DecLinScale k N 2 (ENNReal.ofReal K))
    (c' : E k) {g : ℝ → ℂ} (hgm : Measurable g) (hgi : Integrable g volume) :
    ∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ critQ k
      ≤ K ^ critQ k * (∑ i : Fin N, (localisedPow k c' (lwScale k * R) (critQ k)
            (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k))
          ^ (critQ k / 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hW : (0 : ℝ) < lwScale k * R := mul_pos (lwScale_pos k) (lt_of_lt_of_le (by positivity) hR)
  have hQ1 : (1 : ℝ) ≤ critQ k := le_trans (by norm_num) (two_le_critQ hk)
  have hQ0 : (0 : ℝ) < critQ k := lt_of_lt_of_le (by norm_num) hQ1
  have hgi01 : IntegrableOn g (Set.Icc (0 : ℝ) 1) volume := hgi.integrableOn
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (by positivity) hR
  have hng : IntervalIntegrable (fun t : ℝ => ‖g t‖) volume 0 1 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact IntegrableOn.mono_set hgi01.norm fun t ht => ⟨le_of_lt ht.1, ht.2⟩
  have hle1 : ∀ i : Fin N, (((i : ℕ) : ℝ) + 1) / N ≤ 1 := by
    intro i
    rw [div_le_one hNpos]
    have := i.isLt
    exact_mod_cast Nat.succ_le_of_lt this
  -- the localised pieces lie in the class of the enlarged plates
  have hcls : ∀ i : Fin N, IsFourierRep k (plateScale k N 2 i)
      (fun x : E k => locWeight k c' (lwScale k * R) x
        * extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x) := by
    intro i
    have hset : plateScale k N 2 i = plate k ((1 : ℝ) / N) (pieceCenter N i) := by
      rw [plateScale, show (2 : ℝ) / (2 * (N : ℝ)) = 1 / (N : ℝ) by field_simp]
    rw [hset]
    exact localised_piece_isFourierRep k hk hN hR c' i hgm hgi01
  -- integrability of the localised pieces
  have hIntB : ∀ i : Fin N, Integrable (fun x : E k => ‖locWeight k c' (lwScale k * R) x
      * extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖ ^ critQ k) volume := by
    intro i
    refine integrable_locWeight_mul_pow k hk hQ1 hW c' ?_ (M := ∫ t in (0 : ℝ)..1, ‖g t‖) ?_
    · exact aestronglyMeasurable_extOp k g (piece_le N i.val)
        (intervalIntegrable_piece N hN g hgi01 i.val i.isLt)
    · intro x
      refine le_trans (extOp_norm_le k g (piece_le N i.val) x) ?_
      exact intervalIntegral.integral_mono_interval (by positivity) (piece_le N i.val) (hle1 i)
        (Filter.Eventually.of_forall fun t => norm_nonneg _) hng
  -- integrability of the localised sum
  have hIntSumW : Integrable (fun x : E k => ‖locWeight k c' (lwScale k * R) x
      * (∑ i : Fin N, extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x)‖ ^ critQ k)
      volume := by
    refine integrable_locWeight_mul_pow k hk hQ1 hW c' ?_
      (M := (N : ℝ) * ∫ t in (0 : ℝ)..1, ‖g t‖) ?_
    · have hs : AEStronglyMeasurable (fun x : E k =>
          ∑ i : Fin N, extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x) volume := by
        refine (Finset.aestronglyMeasurable_sum Finset.univ fun (i : Fin N) _ =>
          aestronglyMeasurable_extOp k g
            (piece_le N i.val) (intervalIntegrable_piece N hN g hgi01 i.val i.isLt)).congr ?_
        filter_upwards with x
        rw [Finset.sum_apply]
      exact hs
    · intro x
      calc ‖∑ i : Fin N, extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖
          ≤ ∑ i : Fin N, ‖extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _i : Fin N, ∫ t in (0 : ℝ)..1, ‖g t‖ := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine le_trans (extOp_norm_le k g (piece_le N i.val) x) ?_
            exact intervalIntegral.integral_mono_interval (by positivity) (piece_le N i.val) (hle1 i)
              (Filter.Eventually.of_forall fun t => norm_nonneg _) hng
        _ = (N : ℝ) * ∫ t in (0 : ℝ)..1, ‖g t‖ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hIntA : Integrable (fun x : E k => ‖∑ i : Fin N, locWeight k c' (lwScale k * R) x
      * extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖ ^ critQ k) volume := by
    refine hIntSumW.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖locWeight k c' (lwScale k * R) x
        * (∑ i : Fin N, extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x)‖ ^ critQ k
      = ‖∑ i : Fin N, locWeight k c' (lwScale k * R) x
          * extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖ ^ critQ k
    rw [Finset.mul_sum]
  -- the decoupling inequality in real form
  have hreal := decoupling_real k hk (K := K) hK (f := fun i x => locWeight k c'
      (lwScale k * R) x * extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x)
    (hD _ hcls) hIntA hIntB
  -- the ball integral is dominated by the localised sum
  have hdom : ∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ critQ k
      ≤ ∫ x : E k, ‖∑ i : Fin N, locWeight k c' (lwScale k * R) x
          * extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖ ^ critQ k := by
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) hIntA ?_
    · by_cases hx : x ∈ Metric.ball c' R
      · rw [Set.indicator_of_mem hx]; positivity
      · rw [Set.indicator_of_notMem hx]; simp
    · refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ Metric.ball c' R
      · rw [Set.indicator_of_mem hx]
        have hxc : ‖x - c'‖ < R := by
          rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx
        have h1 : ‖(lwScale k * R)⁻¹ • (x - c')‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hW), inv_mul_le_iff₀ hW]
          refine le_trans hxc.le ?_
          rw [mul_one]
          exact le_mul_of_one_le_left hRpos.le (one_le_lwScale k)
        have h2 : (1 : ℝ) ≤ ‖locWeight k c' (lwScale k * R) x‖ := by
          rw [locWeight]
          exact (locBump_re_ge_one k h1).trans (Complex.re_le_norm _)
        have hsum : ∑ i : Fin N, locWeight k c' (lwScale k * R) x
            * extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x
            = locWeight k c' (lwScale k * R) x * extOp k g 0 1 x := by
          rw [extOp_sum_pieces k N hN g hgi01 x, Finset.mul_sum]
        show ‖extOp k g 0 1 x‖ ^ critQ k
          ≤ ‖∑ i : Fin N, locWeight k c' (lwScale k * R) x
              * extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖ ^ critQ k
        rw [hsum, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
        have h3 : (1 : ℝ) ≤ ‖locWeight k c' (lwScale k * R) x‖ ^ critQ k :=
          Real.one_le_rpow h2 hQ0.le
        calc ‖extOp k g 0 1 x‖ ^ critQ k = 1 * ‖extOp k g 0 1 x‖ ^ critQ k := by ring
          _ ≤ ‖locWeight k c' (lwScale k * R) x‖ ^ critQ k * ‖extOp k g 0 1 x‖ ^ critQ k :=
              mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (norm_nonneg _) _)
      · rw [Set.indicator_of_notMem hx]
        positivity
  -- combine
  have hsum0 : 0 ≤ ∫ x : E k, ‖∑ i : Fin N, locWeight k c' (lwScale k * R) x
      * extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖ ^ critQ k :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hS0 : 0 ≤ ∑ i : Fin N, (localisedPow k c' (lwScale k * R) (critQ k)
      (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (localisedPow_nonneg k c' _ _ _) _
  calc ∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ critQ k
      ≤ ∫ x : E k, ‖∑ i : Fin N, locWeight k c' (lwScale k * R) x
          * extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖ ^ critQ k := hdom
    _ = ((∫ x : E k, ‖∑ i : Fin N, locWeight k c' (lwScale k * R) x
          * extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖ ^ critQ k)
          ^ ((1 : ℝ) / critQ k)) ^ critQ k := by
        rw [← Real.rpow_mul hsum0, show (1 : ℝ) / critQ k * critQ k = 1 by field_simp,
          Real.rpow_one]
    _ ≤ (K * (∑ i : Fin N, (localisedPow k c' (lwScale k * R) (critQ k)
            (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k))
          ^ ((1 : ℝ) / 2)) ^ critQ k := by
        have h1 : (∫ x : E k, ‖∑ i : Fin N, locWeight k c' (lwScale k * R) x
              * extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖ ^ critQ k)
              ^ ((1 : ℝ) / critQ k)
            ≤ K * (∑ i : Fin N, (localisedPow k c' (lwScale k * R) (critQ k)
              (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N)))
              ^ (2 / critQ k)) ^ ((1 : ℝ) / 2) := by
          simpa only [localisedPow] using hreal
        refine Real.rpow_le_rpow ?_ h1 hQ0.le
        exact Real.rpow_nonneg hsum0 _
    _ = K ^ critQ k * (∑ i : Fin N, (localisedPow k c' (lwScale k * R) (critQ k)
            (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k))
          ^ (critQ k / 2) := by
        rw [Real.mul_rpow hK (Real.rpow_nonneg hS0 _), ← Real.rpow_mul hS0,
          show (1 : ℝ) / 2 * critQ k = critQ k / 2 by ring]

/-! ## The uniform localisation bound and the `c'`-integration -/

/-- **Uniform (in the centre) bound for the `Q`-th power of the localisation weight.**
For `k ≥ 1`, `Q ≥ 1`, `Λ ≥ 1`, `R > 0` there is `C > 0` with
`∫⁻ x, ofReal(‖locWeight k c' (ΛR) x‖^Q) ≤ ofReal C` for *every* centre `c'`. -/
lemma lintegral_locWeight_pow_le (k : ℕ) (hk : 1 ≤ k) {Q : ℝ} (hQ : 1 ≤ Q) {Λ R : ℝ}
    (hΛ : 1 ≤ Λ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ c' : E k,
      ∫⁻ x, ENNReal.ofReal (‖locWeight k c' (Λ * R) x‖ ^ Q) ≤ ENNReal.ofReal C := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.Analysis.Distribution.schwartzMap_decay_one_add_norm (locBump k) (100*k)
  have hΛR : (0 : ℝ) < Λ * R := mul_pos (lt_of_lt_of_le one_pos hΛ) hR
  have hBR : (k : ℝ) < 100 * (k : ℝ) * Q := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hQ1 : (1 : ℝ) ≤ Q := hQ
    nlinarith
  have hbint : Integrable (fun u : E k => (1 + ‖u‖) ^ (-(100 * (k : ℝ) * Q))) volume := by
    have h := integrable_one_add_norm (E := E k) (μ := (volume : Measure (E k)))
      (r := 100 * (k : ℝ) * Q) (by simpa [finrank_euclideanSpace] using hBR)
    simpa using h
  set B : ℝ := 100 * (k : ℝ) * Q with hBdef
  refine ⟨C₀ ^ Q * ((Λ * R) ^ k * (1 + ∫ u : E k, (1 + ‖u‖) ^ (-B))), by positivity,
    fun c' => ?_⟩
  have hdec : ∀ x : E k, ‖locWeight k c' (Λ * R) x‖ ^ Q
      ≤ C₀ ^ Q * (1 + ‖((Λ * R)⁻¹ : ℝ) • (x - c')‖) ^ (-B) := by
    intro x
    have h1 : ‖locWeight k c' (Λ * R) x‖
        ≤ C₀ * (1 + ‖((Λ * R)⁻¹ : ℝ) • (x - c')‖) ^ (-(100 * (k : ℝ))) := by
      rw [locWeight]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hC₀ _
    have h2 := Real.rpow_le_rpow (norm_nonneg _) h1 (le_trans zero_le_one hQ)
    have h3 : (C₀ * (1 + ‖((Λ * R)⁻¹ : ℝ) • (x - c')‖) ^ (-(100 * (k : ℝ)))) ^ Q
        = C₀ ^ Q * (1 + ‖((Λ * R)⁻¹ : ℝ) • (x - c')‖) ^ (-B) := by
      rw [Real.mul_rpow hC₀pos.le (Real.rpow_nonneg (by positivity) _),
        ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1 + ‖((Λ * R)⁻¹ : ℝ) • (x - c')‖)]
      congr 2
      ring
    exact h2.trans (le_of_eq h3)
  have htrans : Integrable (fun x : E k =>
      (1 + ‖((Λ * R)⁻¹ : ℝ) • (x - c')‖) ^ (-B)) volume := by
    have hsc : Integrable (fun u : E k => (1 + ‖((Λ * R)⁻¹ : ℝ) • u‖) ^ (-B)) volume :=
      (integrable_comp_smul_iff volume (fun z : E k => (1 + ‖z‖) ^ (-B))
        (inv_ne_zero hΛR.ne')).2 (by simpa [hBdef] using hbint)
    refine ((measurePreserving_add_right volume (-c')).integrable_comp_of_integrable hsc).congr ?_
    filter_upwards with x
    simp only [Function.comp_apply, sub_eq_add_neg]
  have hval : ∫ x : E k, (1 + ‖((Λ * R)⁻¹ : ℝ) • (x - c')‖) ^ (-B)
      = (Λ * R) ^ k * ∫ v : E k, (1 + ‖v‖) ^ (-B) := by
    have hshift : (fun x : E k => (1 + ‖((Λ * R)⁻¹ : ℝ) • (x - c')‖) ^ (-B))
        = fun u : E k => (1 + ‖((Λ * R)⁻¹ : ℝ) • (c' - u)‖) ^ (-B) := by
      funext x
      rw [show x - c' = -(c' - x) by abel, smul_neg, norm_neg]
    have hcont : AEStronglyMeasurable (fun z : E k => (1 + ‖((Λ * R)⁻¹ : ℝ) • z‖) ^ (-B)) volume :=
      ((continuous_const.add (continuous_norm.comp (continuous_const_smul _))).rpow_const
        (fun z => Or.inl (ne_of_gt (by positivity : (0:ℝ) < 1 + ‖((Λ * R)⁻¹ : ℝ) • z‖)))
        ).aestronglyMeasurable
    rw [hshift, (integral_sub_left k c' (fun z : E k => (1 + ‖((Λ * R)⁻¹ : ℝ) • z‖) ^ (-B))
      hcont).symm]
    have hsc := integral_smul_inv k hΛR (fun z : E k => (1 + ‖z‖) ^ (-B))
    simpa only using hsc
  refine le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hdec x)) ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (htrans.const_mul (C₀ ^ Q))
    (Filter.Eventually.of_forall fun x => mul_nonneg (by positivity)
      (Real.rpow_nonneg (by positivity) _))]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∫ x : E k, C₀ ^ Q * (1 + ‖((Λ * R)⁻¹ : ℝ) • (x - c')‖) ^ (-B)
      = C₀ ^ Q * ∫ x : E k, (1 + ‖((Λ * R)⁻¹ : ℝ) • (x - c')‖) ^ (-B) :=
        integral_const_mul _ _
    _ = C₀ ^ Q * ((Λ * R) ^ k * ∫ v : E k, (1 + ‖v‖) ^ (-B)) := by rw [hval]
    _ ≤ C₀ ^ Q * ((Λ * R) ^ k * (1 + ∫ u : E k, (1 + ‖u‖) ^ (-B))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith

/-- Boundedness of the localisation bump (from its Schwartz decay). -/
lemma norm_locBump_le (k : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : E k, ‖locBump k z‖ ≤ M := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.Analysis.Distribution.schwartzMap_decay_one_add_norm (locBump k) (100*k)
  refine ⟨C₀, hC₀pos, fun z => ?_⟩
  have h1 : (1 + ‖z‖) ^ (-(↑(100 * k) : ℝ)) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) ?_
    have : (0:ℝ) ≤ (↑(100 * k) : ℝ) := by positivity
    linarith
  calc ‖locBump k z‖ ≤ C₀ * (1 + ‖z‖) ^ (-(↑(100 * k) : ℝ)) := hC₀ z
    _ ≤ C₀ * 1 := mul_le_mul_of_nonneg_left h1 hC₀pos.le
    _ = C₀ := mul_one _

/-- **The `c'`-transfer in `ℝ≥0∞` form.**  For every bounded measurable `F`, the double lintegral
of the localised `Q`-th powers of `F` (first over the centre `c'`, then over the space variable
`x`) is dominated by the ball-weighted `Q`-th power of `F`.  This is the finiteness *and* the
value bound for the `c'`-integrand of the bridge. -/
theorem lintegral_locWeight_transfer (k : ℕ) (hk : 1 ≤ k) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : E k) {R : ℝ}, 0 < R → ∀ {F : E k → ℂ}
      (_hF : AEStronglyMeasurable F volume) {M : ℝ} (_hM : ∀ x, ‖F x‖ ≤ M),
      ∫⁻ c' : E k, ∫⁻ x : E k,
          ENNReal.ofReal (ballWeight k c R c' * ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q)
        ≤ ENNReal.ofReal (C * R ^ k * ∫ x : E k, ‖F x‖ ^ Q * ballWeight k c R x) := by
  have hΛ : (1 : ℝ) ≤ lwScale k := one_le_lwScale k
  obtain ⟨C₁, hC₁pos, hC₁⟩ := exists_locWeight_transfer_pow k hk hQ hΛ
  refine ⟨C₁, hC₁pos, fun c {R} hR {F} hF {M} hM => ?_⟩
  obtain ⟨Mb, hMbpos, hMb⟩ := norm_locBump_le k
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hWpos : ∀ c' : E k, 0 < ballWeight k c R c' := fun c' => ballWeight_pos k c hR c'
  have hWint : Integrable (fun c' : E k => ballWeight k c R c') volume :=
    ballWeight_integrable k hk c hR
  have hFW : Integrable (fun x : E k => ‖F x‖ ^ Q * ballWeight k c R x) volume := by
    refine Integrable.mono' (hWint.const_mul (M ^ Q)) ?_ ?_
    · exact (((hF.aemeasurable.norm).pow_const Q).aestronglyMeasurable).mul
        (ballWeight_continuous k c hR).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (hWpos x).le)]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) (hM x) hQ0) (hWpos x).le
  -- joint measurability of the kernel
  have hkernel : AEMeasurable (fun p : E k × E k =>
      ‖locWeight k p.1 (lwScale k * R) p.2 * F p.2‖ ^ Q) (volume.prod volume) := by
    have hcont : Continuous (Function.uncurry (fun c' x : E k => locWeight k c' (lwScale k * R) x)) := by
      have h1 : Continuous (fun p : E k × E k => ((lwScale k * R)⁻¹ : ℝ) • (p.2 - p.1)) :=
        (continuous_snd.sub continuous_fst).const_smul ((lwScale k * R)⁻¹)
      exact (locBump k).continuous.comp h1
    have h2 : AEMeasurable (fun p : E k × E k => locWeight k p.1 (lwScale k * R) p.2)
        (volume.prod volume) := hcont.aemeasurable
    have h3 : AEMeasurable (fun p : E k × E k => F p.2) (volume.prod volume) :=
      hF.aemeasurable.comp_snd
    exact ((h2.mul h3).norm).pow_const Q
  have hjoint : AEMeasurable (Function.uncurry (fun c' x : E k =>
      ENNReal.ofReal (ballWeight k c R c' * ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q)))
      (volume.prod volume) := by
    have h1 : AEMeasurable (Function.uncurry (fun c' x : E k =>
        ballWeight k c R c' * ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q)) (volume.prod volume) :=
      ((ballWeight_continuous k c hR).aemeasurable.comp_fst).mul hkernel
    exact h1.ennreal_ofReal
  -- Tonelli
  rw [lintegral_lintegral_swap (μ := (volume : Measure (E k))) (ν := (volume : Measure (E k)))
    hjoint]
  -- pointwise (in `x`) bound of the inner `c'`-lintegral
  have hinner : ∀ x : E k, ∫⁻ c' : E k,
      ENNReal.ofReal (ballWeight k c R c' * ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q)
      ≤ ENNReal.ofReal (‖F x‖ ^ Q) * ENNReal.ofReal (C₁ * R ^ k * ballWeight k c R x) := by
    intro x
    have hfac : ∀ c' : E k, ENNReal.ofReal (ballWeight k c R c' * ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q)
        = ENNReal.ofReal (ballWeight k c R c') * ENNReal.ofReal (‖locWeight k c' (lwScale k * R) x‖ ^ Q)
          * ENNReal.ofReal (‖F x‖ ^ Q) := by
      intro c'
      rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
        ENNReal.ofReal_mul (hWpos c').le,
        ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _), mul_assoc]
    have hint : Integrable (fun c' : E k =>
        ballWeight k c R c' * ‖locWeight k c' (lwScale k * R) x‖ ^ Q) volume := by
      refine Integrable.mono' (hWint.const_mul (Mb ^ Q)) ?_ ?_
      · have hcontc : Continuous (fun c' : E k => locWeight k c' (lwScale k * R) x) :=
          (locBump k).continuous.comp
            (by fun_prop : Continuous fun c' : E k => ((lwScale k * R)⁻¹ : ℝ) • (x - c'))
        exact ((ballWeight_continuous k c hR).aemeasurable.mul
          (hcontc.aemeasurable.norm.pow_const Q)).aestronglyMeasurable
      · filter_upwards with c'
        rw [Real.norm_of_nonneg (mul_nonneg (hWpos c').le
          (Real.rpow_nonneg (norm_nonneg _) _))]
        calc ballWeight k c R c' * ‖locWeight k c' (lwScale k * R) x‖ ^ Q
            ≤ ballWeight k c R c' * Mb ^ Q :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (norm_nonneg _) (by rw [locWeight]; exact hMb _) hQ0)
                (hWpos c').le
          _ = Mb ^ Q * ballWeight k c R c' := by ring
    have hAe : AEMeasurable (fun c' : E k => ENNReal.ofReal (ballWeight k c R c')
        * ENNReal.ofReal (‖locWeight k c' (lwScale k * R) x‖ ^ Q)) volume := by
      have hcontc : Continuous (fun c' : E k => locWeight k c' (lwScale k * R) x) :=
        (locBump k).continuous.comp
          (by fun_prop : Continuous fun c' : E k => ((lwScale k * R)⁻¹ : ℝ) • (x - c'))
      exact ((ballWeight_continuous k c hR).aemeasurable.ennreal_ofReal).mul
        ((hcontc.aemeasurable.norm.pow_const Q).ennreal_ofReal)
    rw [lintegral_congr fun c' => hfac c']
    rw [show (fun c' : E k => ENNReal.ofReal (ballWeight k c R c')
            * ENNReal.ofReal (‖locWeight k c' (lwScale k * R) x‖ ^ Q) * ENNReal.ofReal (‖F x‖ ^ Q))
        = fun c' : E k => ENNReal.ofReal (‖F x‖ ^ Q) * (ENNReal.ofReal (ballWeight k c R c')
            * ENNReal.ofReal (‖locWeight k c' (lwScale k * R) x‖ ^ Q)) from by
          funext c'; ring]
    rw [lintegral_const_mul' (ENNReal.ofReal (‖F x‖ ^ Q))
      (fun c' : E k => ENNReal.ofReal (ballWeight k c R c')
        * ENNReal.ofReal (‖locWeight k c' (lwScale k * R) x‖ ^ Q)) ENNReal.ofReal_ne_top]
    refine mul_le_mul' le_rfl ?_
    rw [show (fun c' : E k => ENNReal.ofReal (ballWeight k c R c')
        * ENNReal.ofReal (‖locWeight k c' (lwScale k * R) x‖ ^ Q))
        = fun c' : E k => ENNReal.ofReal (ballWeight k c R c'
            * ‖locWeight k c' (lwScale k * R) x‖ ^ Q) from by
          funext c'; exact (ENNReal.ofReal_mul (hWpos c').le).symm]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun c' => mul_nonneg (hWpos c').le
        (Real.rpow_nonneg (norm_nonneg _) _))]
    exact ENNReal.ofReal_le_ofReal (hC₁ c hR x)
  -- the outer lintegral
  refine le_trans (lintegral_mono hinner) (le_of_eq ?_)
  have hfun1 : (fun x : E k => ENNReal.ofReal (‖F x‖ ^ Q)
        * ENNReal.ofReal (C₁ * R ^ k * ballWeight k c R x))
      = fun x : E k => ENNReal.ofReal (C₁ * R ^ k) * (ENNReal.ofReal (‖F x‖ ^ Q)
          * ENNReal.ofReal (ballWeight k c R x)) := by
    funext x
    rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C₁ * R ^ k), ← mul_assoc,
      mul_comm (ENNReal.ofReal (‖F x‖ ^ Q)) (ENNReal.ofReal (C₁ * R ^ k)), mul_assoc]
  rw [hfun1]
  rw [lintegral_const_mul' (ENNReal.ofReal (C₁ * R ^ k))
    (fun x : E k => ENNReal.ofReal (‖F x‖ ^ Q) * ENNReal.ofReal (ballWeight k c R x))
    ENNReal.ofReal_ne_top]
  rw [show (fun x : E k => ENNReal.ofReal (‖F x‖ ^ Q) * ENNReal.ofReal (ballWeight k c R x))
      = fun x : E k => ENNReal.ofReal (‖F x‖ ^ Q * ballWeight k c R x) from by
        funext x; exact (ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)).symm]
  rw [← ofReal_integral_eq_lintegral_ofReal hFW
    (Filter.Eventually.of_forall fun x => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (hWpos x).le)]
  rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C₁ * R ^ k)]


/-- **The per-piece `c'`-transfer, real form**: the `c'`-integrand
`c' ↦ w_{B(c,R)}(c') ∫_x ‖locWeight k c' (lwScale k·R) x · F x‖^Q` is integrable, and its
integral is dominated by the ball-weighted `Q`-th power of `F`.  (This is the finiteness *and*
the value bound needed for the weighted `ℓ²`-Minkowski step of the bridge.) -/
theorem integrable_and_integral_locWeight_transfer (k : ℕ) (hk : 1 ≤ k) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : E k) {R : ℝ}, 0 < R → ∀ {F : E k → ℂ}
      (hF : AEStronglyMeasurable F volume) {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M),
      Integrable (fun c' : E k => ballWeight k c R c'
        * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q)) volume ∧
      (∫ c' : E k, ballWeight k c R c'
        * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q))
        ≤ C * R ^ k * ∫ x : E k, ‖F x‖ ^ Q * ballWeight k c R x := by
  obtain ⟨C, hCpos, hC⟩ := lintegral_locWeight_transfer k hk hQ
  refine ⟨C, hCpos, fun c {R} hR {F} hF {M} hM => ?_⟩
  have hC := hC c hR hF hM
  have hWpos : ∀ c' : E k, 0 < ballWeight k c R c' := fun c' => ballWeight_pos k c hR c'
  have hRdil : 0 < lwScale k * R := mul_pos (lwScale_pos k) hR
  have hinner_int : ∀ c' : E k,
      Integrable (fun x : E k => ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q) volume :=
    fun c' => integrable_locWeight_mul_pow k hk hQ hRdil c' hF hM
  -- measurability in the centre
  have hker : AEStronglyMeasurable (fun p : E k × E k =>
      ‖locWeight k p.1 (lwScale k * R) p.2 * F p.2‖ ^ Q) (volume.prod volume) := by
    have hcont : Continuous (Function.uncurry (fun c' x : E k => locWeight k c' (lwScale k * R) x)) := by
      have h1 : Continuous (fun p : E k × E k => ((lwScale k * R)⁻¹ : ℝ) • (p.2 - p.1)) :=
        (continuous_snd.sub continuous_fst).const_smul ((lwScale k * R)⁻¹)
      exact (locBump k).continuous.comp h1
    have h2 : AEMeasurable (fun p : E k × E k => locWeight k p.1 (lwScale k * R) p.2)
        (volume.prod volume) := hcont.aemeasurable
    have h3 : AEMeasurable (fun p : E k × E k => F p.2) (volume.prod volume) :=
      hF.aemeasurable.comp_snd
    exact ((((h2.mul h3).norm).pow_const Q).aestronglyMeasurable)
  have hAmeas : AEMeasurable (fun c' : E k => ballWeight k c R c'
      * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q)) volume :=
    ((ballWeight_continuous k c hR).aemeasurable).mul
      ((hker.integral_prod_right').aemeasurable)
  have hnn : ∀ c' : E k, 0 ≤ ballWeight k c R c'
      * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q) := fun c' =>
    mul_nonneg (hWpos c').le (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)
  -- the lintegral identity
  have hlid : (∫⁻ c' : E k, ENNReal.ofReal (ballWeight k c R c'
        * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q)))
      = ∫⁻ c' : E k, ∫⁻ x : E k,
          ENNReal.ofReal (ballWeight k c R c' * ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q) := by
    refine lintegral_congr fun c' => ?_
    rw [ENNReal.ofReal_mul (hWpos c').le]
    have hfac : (fun x : E k => ENNReal.ofReal (ballWeight k c R c'
          * ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q))
        = fun x : E k => ENNReal.ofReal (ballWeight k c R c')
          * ENNReal.ofReal (‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q) := by
      funext x
      exact ENNReal.ofReal_mul (hWpos c').le
    rw [hfac, lintegral_const_mul' (ENNReal.ofReal (ballWeight k c R c'))
      (fun x : E k => ENNReal.ofReal (‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q))
      ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal (hinner_int c')
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)]
  have hfin : (∫⁻ c' : E k, ENNReal.ofReal (ballWeight k c R c'
      * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q))) ≠ ∞ := by
    rw [hlid]
    exact ne_of_lt (lt_of_le_of_lt hC ENNReal.ofReal_lt_top)
  have hint : Integrable (fun c' : E k => ballWeight k c R c'
      * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q)) volume :=
    (lintegral_ofReal_ne_top_iff_integrable hAmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hnn)).mp hfin
  refine ⟨hint, ?_⟩
  have hconv : ENNReal.ofReal (∫ c' : E k, ballWeight k c R c'
        * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q))
      = ∫⁻ c' : E k, ENNReal.ofReal (ballWeight k c R c'
        * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q)) :=
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)
  calc ∫ c' : E k, ballWeight k c R c'
        * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q)
      = (ENNReal.ofReal (∫ c' : E k, ballWeight k c R c'
          * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ Q))).toReal :=
        (ENNReal.toReal_ofReal (integral_nonneg hnn)).symm
    _ ≤ (ENNReal.ofReal (C * R ^ k * ∫ x : E k, ‖F x‖ ^ Q * ballWeight k c R x)).toReal := by
        refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
        rw [hconv, hlid]
        exact hC
    _ = C * R ^ k * ∫ x : E k, ‖F x‖ ^ Q * ballWeight k c R x :=
        ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hCpos.le (by positivity))
          (integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
            (hWpos x).le))


/-! ## The `c'`-integrand of the decoupled expression -/

/-- The localised `Q`-th power of the `i`-th piece of the extension operator. -/
noncomputable def localPiecePow (k : ℕ) (c' : E k) (R : ℝ) (N : ℕ) (g : ℝ → ℂ) (i : Fin N) : ℝ :=
  localisedPow k c' (lwScale k * R) (critQ k)
    (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))

lemma localPiecePow_nonneg (k : ℕ) (c' : E k) (R : ℝ) (N : ℕ) (g : ℝ → ℂ) (i : Fin N) :
    0 ≤ localPiecePow k c' R N g i :=
  localisedPow_nonneg k c' _ _ _

/-- The pointwise bound on the pieces of the extension operator: `‖E_{J_i}g x‖ ≤ ∫_0^1 ‖g‖`. -/
lemma extOp_piece_norm_le (k : ℕ) {N : ℕ} (hN : 1 ≤ N) {g : ℝ → ℂ}
    (hgi : IntegrableOn g (Set.Icc (0 : ℝ) 1) volume) :
    ∀ i : Fin N, ∀ x : E k,
      ‖extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖ ≤ ∫ t in (0 : ℝ)..1, ‖g t‖ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hng : IntervalIntegrable (fun t : ℝ => ‖g t‖) volume 0 1 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact IntegrableOn.mono_set hgi.norm fun t ht => ⟨le_of_lt ht.1, ht.2⟩
  intro i x
  have hle1 : (((i : ℕ) : ℝ) + 1) / N ≤ 1 := by
    rw [div_le_one hNpos]
    have := i.isLt
    exact_mod_cast Nat.succ_le_of_lt this
  refine le_trans (extOp_norm_le k g (piece_le N i.val) x) ?_
  exact intervalIntegral.integral_mono_interval (by positivity) (piece_le N i.val) hle1
    (Filter.Eventually.of_forall fun t => norm_nonneg _) hng

/-- **Per-piece integrability of the `c'`-integrand.** -/
theorem integrable_localPiecePow (k : ℕ) (hk : 1 ≤ k) {N : ℕ} (hN : 1 ≤ N) {R : ℝ}
    (hR : 0 < R) (c : E k) {g : ℝ → ℂ} (hgm : Measurable g) (hgi : Integrable g volume)
    (hbe : ∀ i : Fin N, ∀ x : E k,
      ‖extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) x‖ ≤ ∫ t in (0 : ℝ)..1, ‖g t‖)
    (i : Fin N) :
    Integrable (fun c' : E k => ballWeight k c R c' * localPiecePow k c' R N g i) volume := by
  have hQ1 : (1 : ℝ) ≤ critQ k := le_trans (by norm_num) (two_le_critQ hk)
  have hgi01 : IntegrableOn g (Set.Icc (0 : ℝ) 1) volume := hgi.integrableOn
  obtain ⟨C, _hCpos, hC⟩ := integrable_and_integral_locWeight_transfer k hk (Q := critQ k) hQ1
  simpa only [localPiecePow, localisedPow] using
    (hC c hR (F := extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))
      (aestronglyMeasurable_extOp k g (piece_le N i.val)
        (intervalIntegrable_piece N hN g hgi01 i.val i.isLt))
      (hbe i)).1

/-- Measurability in the centre of the localised `Q`-th power of a piece. -/
lemma aestronglyMeasurable_localPiecePow (k : ℕ) (hk : 1 ≤ k) {N : ℕ} (hN : 1 ≤ N) {R : ℝ}
    (hR : 0 < R) (c : E k) {g : ℝ → ℂ} (hgm : Measurable g) (hgi : Integrable g volume)
    (i : Fin N) : AEMeasurable (fun c' : E k => localPiecePow k c' R N g i) volume := by
  have hgi01 : IntegrableOn g (Set.Icc (0 : ℝ) 1) volume := hgi.integrableOn
  have hker : AEStronglyMeasurable (fun p : E k × E k =>
      ‖locWeight k p.1 (lwScale k * R) p.2 * extOp k g (((i : ℕ) : ℝ) / N)
        ((((i : ℕ) : ℝ) + 1) / N) p.2‖ ^ critQ k) (volume.prod volume) := by
    have hcont : Continuous (Function.uncurry (fun c' x : E k =>
        locWeight k c' (lwScale k * R) x)) := by
      have h1 : Continuous (fun p : E k × E k => ((lwScale k * R)⁻¹ : ℝ) • (p.2 - p.1)) :=
        (continuous_snd.sub continuous_fst).const_smul ((lwScale k * R)⁻¹)
      exact (locBump k).continuous.comp h1
    have h2 : AEMeasurable (fun p : E k × E k => locWeight k p.1 (lwScale k * R) p.2)
        (volume.prod volume) := hcont.aemeasurable
    have h3 : AEStronglyMeasurable (fun p : E k × E k =>
        extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N) p.2) (volume.prod volume) :=
      (aestronglyMeasurable_extOp k g (piece_le N i.val)
        (intervalIntegrable_piece N hN g hgi01 i.val i.isLt)).comp_snd
    exact ((((h2.mul h3.aemeasurable).norm).pow_const (critQ k))).aestronglyMeasurable
  simpa only [localPiecePow, localisedPow] using (hker.integral_prod_right').aemeasurable

/-- **Integrability of the `c'`-integrand of the decoupled expression.**  This is the second
integrability fact needed by the weighted `ℓ²`-Minkowski step: it follows from the per-piece
integrability (`integrable_and_integral_locWeight_transfer`) and the power-mean inequality
`(Σ_i a_i^{2/Q})^{Q/2} ≤ N^{(Q/2)-1} Σ_i a_i`. -/
theorem integrable_decoupled_integrand (k : ℕ) (hk : 1 ≤ k) {N : ℕ} (hN : 1 ≤ N) {R : ℝ}
    (hR : 0 < R) (c : E k) {g : ℝ → ℂ} (hgm : Measurable g) (hgi : Integrable g volume) :
    Integrable (fun c' : E k => ballWeight k c R c'
      * (∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k))
          ^ (critQ k / 2)) volume := by
  have hQ2 : 2 ≤ critQ k := two_le_critQ hk
  have hQ0 : (0 : ℝ) < critQ k := lt_of_lt_of_le (by norm_num) hQ2
  have hQle : (0 : ℝ) ≤ critQ k := hQ0.le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hgi01 : IntegrableOn g (Set.Icc (0 : ℝ) 1) volume := hgi.integrableOn
  have hng : IntervalIntegrable (fun t : ℝ => ‖g t‖) volume 0 1 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact IntegrableOn.mono_set hgi01.norm fun t ht => ⟨le_of_lt ht.1, ht.2⟩
  obtain ⟨C, _hCpos, hC⟩ := integrable_and_integral_locWeight_transfer k hk (Q := critQ k) (by linarith)
  have hbe := extOp_piece_norm_le k hN hgi01
  -- the per-piece integrability
  have hAi : ∀ i : Fin N, Integrable (fun c' : E k => ballWeight k c R c'
      * localPiecePow k c' R N g i) volume :=
    fun i => integrable_localPiecePow k hk hN hR c hgm hgi hbe i
  have hWpos : ∀ c' : E k, 0 < ballWeight k c R c' := fun c' => ballWeight_pos k c hR c'
  -- the power-mean bound
  have hholder : ∀ c' : E k,
      (∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k)) ^ (critQ k / 2)
        ≤ (N : ℝ) ^ (critQ k / 2 - 1) * ∑ i : Fin N, localPiecePow k c' R N g i := by
    intro c'
    have h1 := Commons.Analysis.Inequalities.sum_rpow_le_card_mul_sum_rpow Finset.univ
      (fun i : Fin N => (localPiecePow k c' R N g i) ^ (2 / critQ k)) (critQ k / 2)
      (fun i _ => Real.rpow_nonneg (localPiecePow_nonneg k c' R N g i) _) (by linarith)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Real.rpow_mul (localPiecePow_nonneg k c' R N g i),
      show 2 / critQ k * (critQ k / 2) = 1 by field_simp, Real.rpow_one]
  -- the dominating function is integrable
  have hsum : Integrable (fun c' : E k => ballWeight k c R c'
      * ∑ i : Fin N, localPiecePow k c' R N g i) volume := by
    have h1 : Integrable (fun c' : E k =>
        ∑ i : Fin N, ballWeight k c R c' * localPiecePow k c' R N g i) volume :=
      integrable_finsetSum _ fun i _ => hAi i
    refine h1.congr (Filter.Eventually.of_forall fun c' => ?_)
    show (∑ i : Fin N, ballWeight k c R c' * localPiecePow k c' R N g i)
      = ballWeight k c R c' * ∑ i : Fin N, localPiecePow k c' R N g i
    rw [Finset.mul_sum]
  have hdom : Integrable (fun c' : E k => (N : ℝ) ^ (critQ k / 2 - 1)
      * (ballWeight k c R c' * ∑ i : Fin N, localPiecePow k c' R N g i)) volume :=
    hsum.const_mul _
  -- the measurability of the integrand
  have hAm : ∀ i : Fin N, AEMeasurable (fun c' : E k => localPiecePow k c' R N g i) volume :=
    fun i => aestronglyMeasurable_localPiecePow k hk hN hR c hgm hgi i
  have hmeas : AEMeasurable (fun c' : E k => ballWeight k c R c'
      * (∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k))
          ^ (critQ k / 2)) volume := by
    have hbase : AEMeasurable (fun c' : E k =>
        ∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k)) volume := by
      have hff : (fun c' : E k => ∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k))
          = ∑ i : Fin N, (fun c' : E k => (localPiecePow k c' R N g i) ^ (2 / critQ k)) := by
        funext c'
        rw [Finset.sum_apply]
      rw [hff]
      exact Finset.aemeasurable_sum (s := Finset.univ)
        (f := fun (i : Fin N) (c' : E k) => (localPiecePow k c' R N g i) ^ (2 / critQ k))
        (fun i _ => (hAm i).pow_const (2 / critQ k))
    exact ((ballWeight_continuous k c hR).aemeasurable.mul (hbase.pow_const (critQ k / 2)))
  refine hdom.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with c'
  rw [Real.norm_of_nonneg (mul_nonneg (le_of_lt (hWpos c'))
    (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg
      (localPiecePow_nonneg k c' R N g i) _) _))]
  calc ballWeight k c R c'
        * (∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k)) ^ (critQ k / 2)
      ≤ ballWeight k c R c' * ((N : ℝ) ^ (critQ k / 2 - 1)
          * ∑ i : Fin N, localPiecePow k c' R N g i) :=
        mul_le_mul_of_nonneg_left (hholder c') (hWpos c').le
    _ = (N : ℝ) ^ (critQ k / 2 - 1)
          * (ballWeight k c R c' * ∑ i : Fin N, localPiecePow k c' R N g i) := by ring


/-! ## The bridge: enlarged decoupling ⟹ BDG's ball-weighted decoupling -/

/-- The transfer constant of the bridge: the `c'`-transfer estimate at the critical exponent
(`Classical.choose` of the uniform bound `integrable_and_integral_locWeight_transfer`). -/
noncomputable def transferConst (k : ℕ) (hk : 1 ≤ k) : ℝ :=
  Classical.choose (integrable_and_integral_locWeight_transfer k hk (Q := critQ k)
    (le_trans (by norm_num) (two_le_critQ hk)))

lemma transferConst_pos (k : ℕ) (hk : 1 ≤ k) : 0 < transferConst k hk :=
  (Classical.choose_spec (integrable_and_integral_locWeight_transfer k hk (Q := critQ k)
    (le_trans (by norm_num) (two_le_critQ hk)))).1

lemma transferConst_spec (k : ℕ) (hk : 1 ≤ k) (c : E k) {R : ℝ} (hR : 0 < R) {F : E k → ℂ}
    (hF : AEStronglyMeasurable F volume) {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M) :
    Integrable (fun c' : E k => ballWeight k c R c'
      * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ critQ k)) volume ∧
    (∫ c' : E k, ballWeight k c R c'
      * (∫ x : E k, ‖locWeight k c' (lwScale k * R) x * F x‖ ^ critQ k))
      ≤ transferConst k hk * R ^ k * ∫ x : E k, ‖F x‖ ^ critQ k * ballWeight k c R x :=
  (Classical.choose_spec (integrable_and_integral_locWeight_transfer k hk (Q := critQ k)
    (le_trans (by norm_num) (two_le_critQ hk)))).2 c hR hF hM

/-- **The bridge.**  The `λ = 2`-enlarged ℓ²-decoupling inequality for the moment curve at scale
`N` implies BDG's ball-weighted decoupling inequality at the critical exponent `k(k+1)` and the
ball radius `R ≥ Nᵏ`, with a constant `V` independent of the ball centre and of `g`. -/
theorem decouples_ball_weighted (k : ℕ) (hk : 1 ≤ k) {N : ℕ} (hN : 1 ≤ N) {R : ℝ}
    (hR1 : 1 ≤ R) (hR : (N : ℝ) ^ k ≤ R) {K : ℝ} (hK : 0 ≤ K)
    (hD : DecLinScale k N 2 (ENNReal.ofReal K)) :
    ∀ (c : E k) {g : ℝ → ℂ}, Measurable g → Integrable g volume →
      (wLpPow k c R (critQ k) (extOp k g 0 1)) ^ (1 / critQ k)
        ≤ max 1 (((2 : ℝ) ^ (100 * k) / ballVol k 0 1 * K ^ critQ k
            * transferConst k hk) ^ (1 / critQ k))
          * (∑ i : Fin N, (wLpPow k c R (critQ k)
              (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k))
            ^ ((1 : ℝ) / 2) := by
  have hQ2 : 2 ≤ critQ k := two_le_critQ hk
  have hQ0 : (0 : ℝ) < critQ k := lt_of_lt_of_le (by norm_num) hQ2
  have hQ1 : (1 : ℝ) ≤ critQ k := le_trans (by norm_num) hQ2
  have hQle : (0 : ℝ) ≤ critQ k := hQ0.le
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  set Ct := transferConst k hk with hCt
  have hCpos : 0 < Ct := transferConst_pos k hk
  have hC := transferConst_spec k hk
  have hbase0 : (0 : ℝ) ≤ (2 : ℝ) ^ (100 * k) / ballVol k 0 1 * K ^ critQ k * Ct :=
    mul_nonneg (mul_nonneg (div_nonneg (pow_nonneg (by norm_num) _)
      (ballVol_pos k hk 0 (by norm_num)).le)
      (Real.rpow_nonneg hK _)) hCpos.le
  intro c g hgm hgi
  have hgi01 : IntegrableOn g (Set.Icc (0 : ℝ) 1) volume := hgi.integrableOn
  have hbe := extOp_piece_norm_le k hN hgi01
  have hWpos : ∀ c' : E k, 0 < ballWeight k c R c' := fun c' => ballWeight_pos k c hRpos c'
  -- (1) the local average step
  have h1 := local_average_step k hk g hgi01 hQle c hR1
  -- (2) the per-centre decoupling bound
  have h2 : ∀ c' : E k, (∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ critQ k)
      ≤ K ^ critQ k * (∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k))
          ^ (critQ k / 2) := by
    intro c'
    simpa only [localPiecePow, localisedPow] using
      localised_decoupling k hk hN hR hK hD c' hgm hgi
  -- the second integrability fact (with the weight on the right, as the Minkowski wants it)
  have hI2 : Integrable (fun c' : E k =>
      (∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k)) ^ (critQ k / 2)
        * ballWeight k c R c') volume :=
    (integrable_decoupled_integrand k hk hN hRpos c hgm hgi).congr
      (Filter.Eventually.of_forall fun c' => by
        show ballWeight k c R c' * (∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k))
            ^ (critQ k / 2)
          = (∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k)) ^ (critQ k / 2)
            * ballWeight k c R c'
        rw [mul_comm])
  -- (3) integrate the pointwise bound over the centre and apply the weighted ℓ²-Minkowski
  have h3 : (∫ c' : E k, ballWeight k c R c'
        * (∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ critQ k))
      ≤ K ^ critQ k * (∑ i : Fin N, (∫ c' : E k, ballWeight k c R c'
            * localPiecePow k c' R N g i) ^ (2 / critQ k)) ^ (critQ k / 2) := by
    calc (∫ c' : E k, ballWeight k c R c'
          * (∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ critQ k))
        ≤ ∫ c' : E k, ballWeight k c R c' * (K ^ critQ k * (∑ i : Fin N,
            (localPiecePow k c' R N g i) ^ (2 / critQ k)) ^ (critQ k / 2)) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun c' =>
            mul_nonneg (hWpos c').le (integral_nonneg fun x =>
              Real.rpow_nonneg (norm_nonneg _) _)) ?_ ?_
          · refine (hI2.const_mul (K ^ critQ k)).congr (Filter.Eventually.of_forall fun c' => ?_)
            show K ^ critQ k * ((∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k))
                ^ (critQ k / 2) * ballWeight k c R c')
              = ballWeight k c R c' * (K ^ critQ k
                * (∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k)) ^ (critQ k / 2))
            ring
          exact Filter.Eventually.of_forall fun c' =>
            mul_le_mul_of_nonneg_left (h2 c') (hWpos c').le
      _ = K ^ critQ k * ∫ c' : E k, (∑ i : Fin N, (localPiecePow k c' R N g i) ^ (2 / critQ k))
              ^ (critQ k / 2) * ballWeight k c R c' := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
          ring
      _ ≤ K ^ critQ k * (∑ i : Fin N, (∫ c' : E k, ballWeight k c R c'
            * localPiecePow k c' R N g i) ^ (2 / critQ k)) ^ (critQ k / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hmink := Commons.Analysis.Integral.weighted_l2_minkowski_rpow
            (μ := (volume : Measure (E k))) (w := fun c' : E k => ballWeight k c R c')
            (fun c' => (hWpos c').le) (ballWeight_continuous k c hRpos).measurable
            (ballWeight_integrable k hk c hRpos) hQ2
            (A := fun (i : Fin N) (c' : E k) => localPiecePow k c' R N g i)
            (fun i c' => localPiecePow_nonneg k c' R N g i)
            (fun i => (aestronglyMeasurable_localPiecePow k hk hN hRpos c hgm hgi i
              ).aestronglyMeasurable)
            (fun i => (integrable_localPiecePow k hk hN hRpos c hgm hgi hbe i).congr
              (Filter.Eventually.of_forall fun c' => by
                show ballWeight k c R c' * localPiecePow k c' R N g i
                  = localPiecePow k c' R N g i * ballWeight k c R c'
                rw [mul_comm]))
            (by simpa only [mul_comm] using hI2)
          simpa only [mul_comm] using hmink
  -- (4) the per-piece value bounds
  have h4 : ∀ i : Fin N, (∫ c' : E k, ballWeight k c R c' * localPiecePow k c' R N g i)
      ≤ Ct * R ^ k * wLpPow k c R (critQ k)
          (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N)) := by
    intro i
    simpa only [localPiecePow, localisedPow, wLpPow] using
      (hC c hRpos (F := extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))
        (aestronglyMeasurable_extOp k g (piece_le N i.val)
          (intervalIntegrable_piece N hN g hgi01 i.val i.isLt))
        (hbe i)).2
  -- (5) the monomial factorisation
  have hmono : (∑ i : Fin N, (Ct * R ^ k * wLpPow k c R (critQ k)
        (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k))
        ^ (critQ k / 2)
      = Ct * R ^ k * (∑ i : Fin N, (wLpPow k c R (critQ k)
          (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k))
          ^ (critQ k / 2) := by
    have hc0 : (0 : ℝ) ≤ Ct * R ^ k := mul_nonneg hCpos.le (by positivity)
    have hfac : ∀ i : Fin N, (Ct * R ^ k * wLpPow k c R (critQ k)
          (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k)
        = (Ct * R ^ k) ^ (2 / critQ k) * (wLpPow k c R (critQ k)
          (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k) := by
      intro i
      rw [Real.mul_rpow hc0 (wLpPow_nonneg k c hRpos (critQ k) _)]
    rw [Finset.sum_congr rfl fun i _ => hfac i, ← Finset.mul_sum,
      Real.mul_rpow (Real.rpow_nonneg hc0 _)
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (wLpPow_nonneg k c hRpos (critQ k) _) _),
      ← Real.rpow_mul hc0, show 2 / critQ k * (critQ k / 2) = 1 by field_simp,
      Real.rpow_one]
  -- (6) assembling
  have hmain : wLpPow k c R (critQ k) (extOp k g 0 1)
      ≤ ((2 : ℝ) ^ (100 * k) / ballVol k 0 1 * K ^ critQ k * Ct)
        * (∑ i : Fin N, (wLpPow k c R (critQ k)
            (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k))
          ^ (critQ k / 2) := by
    refine h1.trans ?_
    have hK1nn : (0 : ℝ) ≤ (2 : ℝ) ^ (100 * k) / ballVol k 0 1 * (R ^ k)⁻¹ :=
      mul_nonneg (div_nonneg (pow_nonneg (by norm_num) _) (ballVol_pos k hk 0 (by norm_num)).le)
        (inv_nonneg.mpr (pow_nonneg hRpos.le _))
    calc (2 : ℝ) ^ (100 * k) / ballVol k 0 1 * (R ^ k)⁻¹
          * ∫ c' : E k, ballWeight k c R c'
              * (∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ critQ k)
        ≤ (2 : ℝ) ^ (100 * k) / ballVol k 0 1 * (R ^ k)⁻¹ * (K ^ critQ k
            * (∑ i : Fin N, (∫ c' : E k, ballWeight k c R c'
                * localPiecePow k c' R N g i) ^ (2 / critQ k)) ^ (critQ k / 2)) :=
          mul_le_mul_of_nonneg_left h3 hK1nn
      _ ≤ (2 : ℝ) ^ (100 * k) / ballVol k 0 1 * (R ^ k)⁻¹ * (K ^ critQ k
            * (∑ i : Fin N, (Ct * R ^ k * wLpPow k c R (critQ k)
                (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k))
              ^ (critQ k / 2)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
            (Real.rpow_nonneg hK _)) hK1nn
          refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg
            (integral_nonneg fun x => mul_nonneg (hWpos x).le
              (localPiecePow_nonneg k x R N g i)) _) ?_ (by linarith [hQ0])
          exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (integral_nonneg fun x =>
            mul_nonneg (hWpos x).le (localPiecePow_nonneg k x R N g i)) (h4 i)
            (by positivity : (0:ℝ) ≤ 2 / critQ k)
      _ = (2 : ℝ) ^ (100 * k) / ballVol k 0 1 * K ^ critQ k * Ct
            * (∑ i : Fin N, (wLpPow k c R (critQ k)
                (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k))
              ^ (critQ k / 2) := by
          rw [hmono]
          field_simp
  -- (7) taking the `Q`-th root
  have hfin := Real.rpow_le_rpow (wLpPow_nonneg k c hRpos (critQ k) (extOp k g 0 1)) hmain
    (by positivity : (0 : ℝ) ≤ 1 / critQ k)
  refine hfin.trans ?_
  have hZ0 : (0 : ℝ) ≤ ∑ i : Fin N, (wLpPow k c R (critQ k)
      (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (wLpPow_nonneg k c hRpos (critQ k) _) _
  have hsplit : (((2 : ℝ) ^ (100 * k) / ballVol k 0 1 * K ^ critQ k * Ct)
        * (∑ i : Fin N, (wLpPow k c R (critQ k)
            (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k))
          ^ (critQ k / 2)) ^ (1 / critQ k)
      = ((2 : ℝ) ^ (100 * k) / ballVol k 0 1 * K ^ critQ k * Ct) ^ (1 / critQ k)
        * (∑ i : Fin N, (wLpPow k c R (critQ k)
            (extOp k g (((i : ℕ) : ℝ) / N) ((((i : ℕ) : ℝ) + 1) / N))) ^ (2 / critQ k))
          ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow hbase0 (Real.rpow_nonneg hZ0 (critQ k / 2)),
      ← Real.rpow_mul hZ0, show critQ k / 2 * (1 / critQ k) = 1 / 2 by field_simp]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right
    (le_max_right (1 : ℝ) (((2 : ℝ) ^ (100 * k) / ballVol k 0 1 * K ^ critQ k * Ct)
      ^ (1 / critQ k))) (Real.rpow_nonneg hZ0 ((1 : ℝ) / 2))


/-- **BDG's Theorem 1.2 from the enlarged GLYZ decoupling family.**  If at every scale `N ≥ 1`
the `λ = 2`-enlarged ℓ²-decoupling inequality holds with the constant `K N^ε`, then BDG's
ball-weighted decoupling inequality at the critical exponent `k(k+1)` and the ball radius `Nᵏ`
holds with a constant `C` and the same `N^ε` loss — which is exactly the shape of
`Submission.Vinogradov.bdg_thm_ntmain` (`critQ k` is definitionally `k(k+1)`). -/
theorem bdg_thm_ntmain_of_decLinScale (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) {K : ℝ}
    (hK : 0 < K)
    (hD : ∀ N : ℕ, 1 ≤ N → DecLinScale k N 2 (ENNReal.ofReal (K * (N : ℝ) ^ ε))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (c : E k), ∀ g : ℝ → ℂ, Measurable g →
      Integrable g volume →
      (wLpPow k c ((N : ℝ) ^ k) (critQ k) (extOp k g 0 1)) ^ (1 / critQ k)
        ≤ C * (N : ℝ) ^ ε
          * (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) (critQ k)
              (extOp k g (((i : ℕ) : ℝ) / (N : ℝ)) ((((i : ℕ) : ℝ) + 1) / (N : ℝ))))
                ^ (2 / critQ k)) ^ ((1 : ℝ) / 2) := by
  have hQ2 : 2 ≤ critQ k := two_le_critQ hk
  have hQ0 : (0 : ℝ) < critQ k := lt_of_lt_of_le (by norm_num) hQ2
  set D : ℝ := ((2 : ℝ) ^ (100 * k) / ballVol k 0 1 * K ^ critQ k * transferConst k hk)
      ^ (1 / critQ k) with hDdef
  refine ⟨max 1 D, lt_of_lt_of_le one_pos (le_max_left (1 : ℝ) D), ?_⟩
  intro N hN c g hgm hgi
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hNε1 : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hKN : (0 : ℝ) ≤ K * (N : ℝ) ^ ε :=
    mul_nonneg hK.le (Real.rpow_nonneg (by positivity) _)
  have hRN : (1 : ℝ) ≤ (N : ℝ) ^ k := one_le_pow₀ hN1
  have hmain := decouples_ball_weighted k hk hN hRN le_rfl hKN (hD N hN) c hgm hgi
  -- the constant of `decouples_ball_weighted` splits as `D · N^ε`
  have hconst : (K * (N : ℝ) ^ ε) ^ critQ k = K ^ critQ k * (N : ℝ) ^ (ε * critQ k) := by
    rw [Real.mul_rpow hK.le (Real.rpow_nonneg (by positivity) _),
      Real.rpow_mul (by positivity)]
  have harg : ((2 : ℝ) ^ (100 * k) / ballVol k 0 1 * (K * (N : ℝ) ^ ε) ^ critQ k
        * transferConst k hk) ^ (1 / critQ k) = D * (N : ℝ) ^ ε := by
    rw [hconst, hDdef]
    have hx0 : (0 : ℝ) ≤ (2 : ℝ) ^ (100 * k) / ballVol k 0 1 * K ^ critQ k * transferConst k hk :=
      mul_nonneg (mul_nonneg (div_nonneg (pow_nonneg (by norm_num) _)
        (ballVol_pos k hk 0 (by norm_num)).le) (Real.rpow_nonneg hK.le _))
        (transferConst_pos k hk).le
    have hr : (2 : ℝ) ^ (100 * k) / ballVol k 0 1 * (K ^ critQ k * (N : ℝ) ^ (ε * critQ k))
          * transferConst k hk
        = ((2 : ℝ) ^ (100 * k) / ballVol k 0 1 * K ^ critQ k * transferConst k hk)
          * (N : ℝ) ^ (ε * critQ k) := by ring
    rw [hr, Real.mul_rpow hx0 (Real.rpow_nonneg (by positivity) _),
      ← Real.rpow_mul hNpos.le, show ε * critQ k * (1 / critQ k) = ε by field_simp]
  -- the sum is nonnegative
  have hS0 : (0 : ℝ) ≤ (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) (critQ k)
      (extOp k g (((i : ℕ) : ℝ) / (N : ℝ)) ((((i : ℕ) : ℝ) + 1) / (N : ℝ))))
        ^ (2 / critQ k)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg
      (wLpPow_nonneg k c (by positivity) (critQ k) _) _) _
  calc (wLpPow k c ((N : ℝ) ^ k) (critQ k) (extOp k g 0 1)) ^ (1 / critQ k)
      ≤ max 1 (((2 : ℝ) ^ (100 * k) / ballVol k 0 1 * (K * (N : ℝ) ^ ε) ^ critQ k
            * transferConst k hk) ^ (1 / critQ k))
          * (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) (critQ k)
              (extOp k g (((i : ℕ) : ℝ) / (N : ℝ)) ((((i : ℕ) : ℝ) + 1) / (N : ℝ))))
                ^ (2 / critQ k)) ^ ((1 : ℝ) / 2) := hmain
    _ = max 1 (D * (N : ℝ) ^ ε)
          * (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) (critQ k)
              (extOp k g (((i : ℕ) : ℝ) / (N : ℝ)) ((((i : ℕ) : ℝ) + 1) / (N : ℝ))))
                ^ (2 / critQ k)) ^ ((1 : ℝ) / 2) := by rw [harg]
    _ ≤ max 1 D * (N : ℝ) ^ ε
          * (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) (critQ k)
              (extOp k g (((i : ℕ) : ℝ) / (N : ℝ)) ((((i : ℕ) : ℝ) + 1) / (N : ℝ))))
                ^ (2 / critQ k)) ^ ((1 : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_right ?_ hS0
        rcases le_total (1 : ℝ) (D * (N : ℝ) ^ ε) with h | h
        · rw [max_eq_right h]
          exact mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) D)
            (Real.rpow_nonneg hNpos.le _)
        · rw [max_eq_left h]
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ max 1 D * (N : ℝ) ^ ε :=
                mul_le_mul (le_max_left (1 : ℝ) D) hNε1 zero_le_one
                  (by positivity)


end Submission.Vinogradov
