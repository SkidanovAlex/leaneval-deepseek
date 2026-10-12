import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.wSmall1Pair_fibre_abs_le
import Submission.Work.BoseFixB1S.integrableOn_boxQInd_sq_mul_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxFibLine` — the `Q²`-fibre line of the per-box payment

Step 1 of `Submission/Work/BoseFixB1S/NOTES_a0A2Q_reduction.md` §3: the excited-count
weighting of the localised one-body fibre

    Σ_i ∫_{abox N ℓ} (Q_{B(u),i}Φ x)² · fib(x i)  ≤  C · n₊(B(u)) ,
    fib(z) = ∫_{acube ℓ} w_{1,B(u)}(z,y) dy ,  n₊(B(u)) = Σ_i ∫ (Q_{B(u),i}Φ)² .

The two inputs are the *pointwise sign and size* of the fibre, both at the sharp
`R₀ ≤ ℓd/16`, `R₀ ≤ ℓ·chiR0` regime:

* `boxFibLine_fibre_nonneg` — `0 ≤ fib(z)`: the integrand of the fibre is a.e. nonnegative
  (`g₀ ≥ 0` a.e., every cutoff and both renormalisation denominators `≥ 0`);
* `boxFibLine_fibre_le` — the uniform upper bound `fib(z) ≤ K_f`, from
  `Work.BoseFixB1.wSmall1Pair_fibre_abs_le` (`|fib| ≤ (χ·D_M)·(2(χ·D_M)/smallConvLower M·8π a v)`).

The passage from the pointwise bound to the sum is the monotonicity of the integral on
nonnegative integrands (`integral_mono_of_nonneg`), which needs the integrability of the
dominating function `(Q_{B(u),i}Φ)²·K_f` on the compact box `abox N ℓ` — supplied by
`Work.BoseFixB1S.integrableOn_boxQInd_sq_mul_const` (this session's sibling module), for
**every** value of the box mass `volA ≥ 0`
(the sliding box `B(u)` can degenerate to a measure-zero set, in which case `1/volA = 0`
and the box projection still obeys `|P_{B,i}Φ| ≤ sup|Φ|`).
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped Real BigOperators

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The sign and size of the localised one-body fibre -/

/-- **Nonnegativity of the localised one-body fibre** `fib(z) = ∫_{acube ℓ} w_{1,B(u)}(z,y) dy`.

The integrand is a.e. nonnegative: `g₀ ≥ 0` a.e. (`Work.SmallBoxSliding.ae_g0_comp_sub`),
the two cutoff factors and both renormalisation denominators (`χ_M⋆χ_M` evaluated at the
scaled difference and `χ⋆χ` evaluated at `(z−y)/ℓ`) are pointwise nonnegative. -/
theorem boxFibLine_fibre_nonneg {v : E3 → ℝ} {R0 : ℝ} (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0)
    (h : ∃ w : E3 → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d : ℝ} (u z : E3) :
    0 ≤ Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z := by
  rw [Submission.BoseGases.w1Fibre]
  refine integral_nonneg_of_ae (ae_restrict_of_ae ?_)
  filter_upwards [Work.SmallBoxSliding.ae_g0_comp_sub hv hvrad hv_supp hR0 h z] with y hy
  simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
    Submission.BoseGases.wSmallScaled]
  exact mul_nonneg
    (mul_nonneg (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u z)
      (div_nonneg (div_nonneg hy (Work.SmallBoxSliding.convScaleSmall_nonneg M (ℓ * d) (z - y)))
        (Submission.BoseGases.convScale_nonneg ℓ (z - y))))
    (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u y)

/-- **Uniform upper bound of the localised one-body fibre**, from the proved absolute
fibre bound `Work.BoseFixB1.wSmall1Pair_fibre_abs_le`. -/
theorem boxFibLine_fibre_le {v : E3 → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : E3 → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u z : E3) :
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z ≤
      (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            / Work.SmallBoxSliding.smallConvLower M)
          * (8 * Real.pi * _root_.BoseGases.a v)) := by
  refine le_trans (le_abs_self _) ?_
  simpa only [Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair] using
    Work.BoseFixB1.wSmall1Pair_fibre_abs_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z

/-! ## 2. A by-product: the box projection is bounded on the box for every box mass `volA ≥ 0`

The route the sibling module `Work.BoseFixB1S.integrableOn_boxQInd_sq_mul_const` takes avoids
this point (it works with the `L∞` bound of `Work.SlotWord`); the bound below is recorded
because the sliding box `B(u)` *can* degenerate (`boxMass ℓ d u = 0` for `u` with the small
box sitting outside `acube ℓ`), so the positivity of the box mass — which the corpus lemmas
`Work.BoseFixB1S.Q0C.abs_boxPInd_le` / `Work.BoseFixB1S.abs_boxQInd_le` assume — is not
available in the target's hypotheses. -/

/-- `|P_{B,i}Φ| ≤ C` on the box, where `C` bounds `|Φ|` there.  Neither the positivity of
`volA` nor its nonvanishing is needed: when `volA = 0` one has `1/volA = 0`, and
`|volA⁻¹|·volA ≤ 1` holds for every `volA ≥ 0`. -/
theorem boxPInd_abs_le_noPos {N : ℕ} {ℓ volA C : ℝ} (hℓ : 0 < ℓ) (hvol : 0 ≤ volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N) {Φ : Submission.BoseGases.X N → ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C := by
  intro x hx
  have hfinA : (MeasureTheory.volume : MeasureTheory.Measure E3) A < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono hAc)
      (by rw [Submission.BoseGases.acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top)
  have hI : |∫ z in A, Φ (Function.update x i z)| ≤ C * volA := by
    have hb : ∀ z ∈ A, ‖Φ (Function.update x i z)‖ ≤ C := fun z hz => by
      rw [Real.norm_eq_abs]
      exact hC _ (Work.BoseFixB1S.Q0C.update_mem_abox hAc hx i hz)
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfinA hb
    rw [MeasureTheory.Measure.real_def, ← hvolA] at h
    simpa [Real.norm_eq_abs] using h
  have hσ : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases hmem : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hmem]
  have hkey : |volA⁻¹| * volA ≤ 1 := by
    rcases eq_or_lt_of_le hvol with h0 | hpos
    · subst h0; simp
    · rw [abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]
  have hmain : |volA⁻¹| * |∫ z in A, Φ (Function.update x i z)|
        * |A.indicator (fun _ => (1 : ℝ)) (x i)|
      ≤ |volA⁻¹| * (C * volA) * 1 := by
    refine mul_le_mul (mul_le_mul le_rfl hI (abs_nonneg _) (abs_nonneg _)) hσ
      (abs_nonneg _) (mul_nonneg (abs_nonneg _) (mul_nonneg hC0 hvol))
  rw [Work.UBBInputs8.boxPInd, one_div]
  calc |volA⁻¹ * (∫ z in A, Φ (Function.update x i z)) * A.indicator (fun _ => (1 : ℝ)) (x i)|
      = |volA⁻¹| * |∫ z in A, Φ (Function.update x i z)|
          * |A.indicator (fun _ => (1 : ℝ)) (x i)| := by rw [abs_mul, abs_mul]
    _ ≤ |volA⁻¹| * (C * volA) * 1 := hmain
    _ = C * (|volA⁻¹| * volA) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hkey hC0
    _ = C := mul_one C

/-! ## 3. The target -/

theorem boxFibLine {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
            * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
        ≤ C * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ := by
  let Kf : ℝ := (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            / Work.SmallBoxSliding.smallConvLower M)
          * (8 * Real.pi * _root_.BoseGases.a v))
  have hle : ∀ z : E3,
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z ≤ Kf :=
    fun z => boxFibLine_fibre_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
  have hfi_nn : ∀ z : E3,
      0 ≤ Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
    fun z => boxFibLine_fibre_nonneg hR0 hv hvrad hv_supp h u z
  have hKf_nn : 0 ≤ Kf := le_trans (hfi_nn 0) (hle 0)
  refine ⟨Kf, hKf_nn, ?_⟩
  have hvolnn : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
    rw [Work.SmallBoxSliding.boxMass]
    refine integral_nonneg (fun x => ?_)
    simp only [Work.SmallBoxSliding.boxInd]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    fun x hx => hx.1
  rw [boxQCount, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hint : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 * Kf)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    Work.BoseFixB1S.integrableOn_boxQInd_sq_mul_const hℓ hvolnn hA hvolA hAc i hΦc
  calc ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
          * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 * Kf :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hfi_nn (x i))))
          hint
          (Filter.Eventually.of_forall
            (fun x => mul_le_mul_of_nonneg_left (hle (x i)) (sq_nonneg _)))
    _ = Kf * ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 := by
        rw [MeasureTheory.integral_mul_const, mul_comm]

end

end Work.BoseFixB1S
