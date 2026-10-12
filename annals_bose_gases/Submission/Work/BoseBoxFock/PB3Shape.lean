import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PB3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3Shape` — the block-III pair shape at the pinned condensate

`b3PairSum Θ A B K` is the `pairSet n`-sum of the triple integrals

    ∫_x ∫_y ∫_u star(Θ x) · A (x p.1) · star(B y) · K (x p.2) u · Θ(x[p.1↦y][p.2↦u])

in which one condensate pin sits on a *configuration* coordinate (`A (x p.1)`) and the other on a
*free* integration variable (`star (B y)`), while `b3SlotSum ℓ Θ K` is the slot form

    ∫_x star(Θ x) · (K)_{p.2}(P_{p.1}Θ)(x),

with `(K)_j` the slot-`j` one-body operator of the kernel and `P_i` the slot-`i` box mean
(`aPC ℓ i`).  The theorem identifies the two at the pinned condensate
`A = B = pinCond v μ c = c·θ_Λ` (`θ_Λ` the sharp indicator of the box `Λ = boxL (ellH v μ)`) under the
normalisation `c̄c = (ellH v μ)⁻³` (`hc`), the state being supported in the `n`-particle box.

The proof is two steps, and both are *pointwise* except for one Fubini interchange:

* every occurrence of `pinCond` is the scalar `c` (resp. `c̄`) on the box and `0` off it.  Since
  `Θ` is supported in `boxPow n (ellH v μ)`, a configuration factor `pinCond (x p.1)` equals `c`
  when `Θ x ≠ 0`, and the free factor `star (pinCond y)` is *identically*
  `c̄ · 1_{boxL}(y)`.  Hence, using `c̄c = ẖ³⁻¹` and `Function.update_comm` (`p.1 ≠ p.2`),
  the integrand of `b3PairSum` is `r · (1_{boxL}(y) · star(Θ x) · K (x p.2) u · Θ(x[p.2↦u][p.1↦y]))`
  with `r = ((ellH v μ)³)⁻¹`, pointwise in `(x, y, u)` (`hc` is used only here);
* the slot form expands to `r · ∫_x ∫_u ∫_{y ∈ acube} star(Θ x) · K (x p.2) u · Θ(x[p.2↦u][p.1↦y])`,
  because `aPC` is the normalised mean over `acube ℓ = boxL ℓ`.  Comparing the two needs the
  interchange of the `y`- and `u`-integrals; that is `MeasureTheory.integral_integral_swap`, whose
  integrability hypothesis is supplied by the boundedness hypotheses `hΘb`/`hKb` together with the
  support hypothesis `hΘs` (the joint integrand is supported in `boxL × boxL`, a box of finite
  volume: `b3Joint_integrable`).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The pinned condensate is the scalar `c` on the box and `0` off it: `pinCond v μ c = c·1_Λ`. -/
lemma b3PinCond_indicator {v : E3 → ℝ} {μ : ℝ} (c : ℂ) (y : E3) :
    pinCond v μ c y
      = c * (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y := by
  rw [pinCond, Work.BoseB4.BoxData.thetaFun_apply]
  rfl

/-- The conjugate of the pinned condensate: `star (pinCond v μ c) = c̄·1_Λ`. -/
lemma b3StarPinCond_indicator {v : E3 → ℝ} {μ : ℝ} (c : ℂ) (y : E3) :
    star (pinCond v μ c y)
      = star c * (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y := by
  rw [b3PinCond_indicator, star_mul]
  have h : star ((Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y)
      = (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y := by
    by_cases hy : y ∈ Work.BoseK15.corpusBox.boxL (ellH v μ) <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  rw [h, mul_comm]

/-- **The joint `(y,u)`-integrand of the block-III pair shape is integrable.**  It is measurable,
bounded by `‖Θ x‖·‖K‖·‖Θ‖`, and supported in `boxL × boxL` (the `y`-factor by its explicit
indicator, the `u`-factor by the box support of `Θ`, since `(x[p.2↦u][p.1↦y]) p.2 = u`). -/
lemma b3Joint_integrable {n : ℕ} {v : E3 → ℝ} {μ : ℝ} {Θ : Work.BoseDict.Xn n → ℂ}
    {K : E3 → E3 → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n (ellH v μ))
    (hKm : Measurable (Function.uncurry K)) (hKb : ∃ C : ℝ, ∀ w y, ‖K w y‖ ≤ C)
    (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (x : Work.BoseDict.Xn n) :
    Integrable (fun z : E3 × E3 =>
      (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) z.1
        * (star (Θ x) * K (x p.2) z.2 * Θ (Function.update (Function.update x p.2 z.2) p.1 z.1)))
      (volume.prod volume) := by
  classical
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  obtain ⟨CK, hCK⟩ := hKb
  have hCΘnn : 0 ≤ CΘ := le_trans (norm_nonneg _) (hCΘ fun _ => 0)
  have hCKnn : 0 ≤ CK := le_trans (norm_nonneg _) (hCK (x p.2) 0)
  set S := Work.BoseK15.corpusBox.boxL (ellH v μ) with hSdef
  have hSm : MeasurableSet S := Work.BoseB4.BoxData.boxL_measurableSet _ _
  have hSfin : (volume : Measure E3) S ≠ ⊤ := by
    rw [Work.BoseB4.BoxData.volume_boxL _ (ellH_pos v μ)]
    exact ENNReal.ofReal_ne_top
  have hfind : Integrable (S.indicator (fun _ : E3 => (1:ℝ))) (volume : Measure E3) :=
    IntegrableOn.integrable_indicator (integrableOn_const hSfin (by simp)) hSm
  have hgint : Integrable (fun z : E3 × E3 =>
      (S.indicator (fun _ : E3 => (1:ℝ)) z.1) * (S.indicator (fun _ : E3 => (1:ℝ)) z.2))
      (volume.prod volume) := hfind.mul_prod hfind
  have hmajor : Integrable (fun z : E3 × E3 => (CΘ * CK * CΘ) *
      ((S.indicator (fun _ : E3 => (1:ℝ)) z.1) * (S.indicator (fun _ : E3 => (1:ℝ)) z.2)))
      (volume.prod volume) := hgint.const_mul _
  refine Integrable.mono' hmajor ?_ (Filter.Eventually.of_forall ?_)
  · have hmeas1 : Measurable (fun z : E3 × E3 => S.indicator (fun _ : E3 => (1:ℂ)) z.1) :=
      (measurable_const.indicator hSm).comp measurable_fst
    have hmeas2 : Measurable (fun z : E3 × E3 => K (x p.2) z.2) := by
      have hp2 : Measurable (fun z : E3 × E3 => (x p.2, z.2)) := by fun_prop
      exact hKm.comp hp2
    have hcont3 : Continuous (fun z : E3 × E3 =>
        Function.update (Function.update x p.2 z.2) p.1 z.1) := by
      have hp2c : Continuous (fun z : E3 × E3 => (x, z.2)) := by fun_prop
      have hf : Continuous (fun z : E3 × E3 => Function.update x p.2 z.2) :=
        (continuous_update p.2).comp hp2c
      exact hf.update p.1 continuous_fst
    have hmeas3 : Measurable (fun z : E3 × E3 =>
        Θ (Function.update (Function.update x p.2 z.2) p.1 z.1)) :=
      hΘm.comp hcont3.measurable
    exact ((hmeas1.mul ((measurable_const.mul hmeas2).mul hmeas3))).aestronglyMeasurable
  · intro z
    have hΘu : ‖Θ (Function.update (Function.update x p.2 z.2) p.1 z.1)‖
        ≤ CΘ * S.indicator (fun _ : E3 => (1:ℝ)) z.2 := by
      by_cases hu : z.2 ∈ S
      · rw [Set.indicator_of_mem hu, mul_one]; exact hCΘ _
      · have hupd2 : (Function.update (Function.update x p.2 z.2) p.1 z.1) p.2 = z.2 := by
          rw [Function.update_of_ne hp.symm, Function.update_self]
        have hnot : ¬ (Function.update (Function.update x p.2 z.2) p.1 z.1
            ∈ Work.MB.boxPow n (ellH v μ)) := by
          rw [Work.MB.mem_boxPow_iff]
          intro hall
          exact hu (hupd2 ▸ hall p.2)
        have hz : Θ (Function.update (Function.update x p.2 z.2) p.1 z.1) = 0 := by
          by_contra hcon
          exact hnot (hΘs (Function.mem_support.mpr hcon))
        rw [hz, norm_zero, Set.indicator_of_notMem hu, mul_zero]
    by_cases hy : z.1 ∈ S
    · have hCy : S.indicator (fun _ : E3 => (1:ℂ)) z.1 = 1 := Set.indicator_of_mem hy _
      have hRy : S.indicator (fun _ : E3 => (1:ℝ)) z.1 = 1 := Set.indicator_of_mem hy _
      rw [hCy, hRy, one_mul, one_mul]
      have h1 : ‖star (Θ x)‖ ≤ CΘ := by rw [norm_star]; exact hCΘ x
      have h2 : ‖K (x p.2) z.2‖ ≤ CK := hCK _ _
      calc ‖star (Θ x) * K (x p.2) z.2 * Θ (Function.update (Function.update x p.2 z.2) p.1 z.1)‖
          = ‖star (Θ x)‖ * ‖K (x p.2) z.2‖
              * ‖Θ (Function.update (Function.update x p.2 z.2) p.1 z.1)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ CΘ * CK * (CΘ * S.indicator (fun _ : E3 => (1:ℝ)) z.2) :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hCΘnn) hΘu (norm_nonneg _)
              (mul_nonneg hCΘnn hCKnn)
        _ = (CΘ * CK * CΘ) * S.indicator (fun _ : E3 => (1:ℝ)) z.2 := by ring
    · have hCy : S.indicator (fun _ : E3 => (1:ℂ)) z.1 = 0 := Set.indicator_of_notMem hy _
      have hRy : S.indicator (fun _ : E3 => (1:ℝ)) z.1 = 0 := Set.indicator_of_notMem hy _
      rw [hCy, hRy, zero_mul, norm_zero, zero_mul, mul_zero]

theorem PB3Shape {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {c : ℂ}
    (hc : (starRingEnd ℂ) c * c = (((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ : ℝ))
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n (Work.BoseBoxFock.ellH v μ))
    (K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hKm : Measurable (Function.uncurry K)) (hKb : ∃ C : ℝ, ∀ w y, ‖K w y‖ ≤ C) :
    Work.BoseBoxFock.b3PairSum Θ (Work.BoseBoxFock.pinCond v μ c) (Work.BoseBoxFock.pinCond v μ c) K
      = Work.BoseBoxFock.b3SlotSum (Work.BoseBoxFock.ellH v μ) Θ K := by
  classical
  have hℓpos : 0 < ellH v μ := ellH_pos v μ
  have hcc : c * star c = ((((ellH v μ) ^ 3)⁻¹ : ℝ) : ℂ) := by rw [mul_comm]; exact hc
  rw [b3PairSum, b3SlotSum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  simp only [starRingEnd_apply]
  set r : ℂ := ((((ellH v μ) ^ 3)⁻¹ : ℝ) : ℂ) with hrdef
  have hr'' : ((1 / (ellH v μ) ^ 3 : ℝ) : ℂ) = r := by rw [hrdef, one_div]
  have hcc' : c * star c = r := by rw [hrdef]; exact hcc
  -- the integrand of the pair shape at the pinned condensate
  have hpt : ∀ x y u, star (Θ x) * pinCond v μ c (x p.1) * star (pinCond v μ c y) * K (x p.2) u
        * Θ (Function.update (Function.update x p.1 y) p.2 u)
      = r * ((Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y *
          (star (Θ x) * K (x p.2) u * Θ (Function.update (Function.update x p.2 u) p.1 y))) := by
    intro x y u
    by_cases hx : Θ x = 0
    · rw [hx, star_zero]; ring
    · have hxmem : x ∈ Work.MB.boxPow n (ellH v μ) := hΘs (Function.mem_support.mpr hx)
      have hx1 : x p.1 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ) :=
        (Work.MB.mem_boxPow_iff.mp hxmem) p.1
      have hpin : pinCond v μ c (x p.1) = c := by
        rw [b3PinCond_indicator]; simp [Set.indicator_of_mem hx1]
      have hupd : Function.update (Function.update x p.1 y) p.2 u
          = Function.update (Function.update x p.2 u) p.1 y := Function.update_comm hpne y u x
      rw [hpin, b3StarPinCond_indicator, hupd]
      by_cases hy : y ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
      · rw [Set.indicator_of_mem hy]
        calc star (Θ x) * c * (star c * (1:ℂ)) * K (x p.2) u
              * Θ (Function.update (Function.update x p.2 u) p.1 y)
            = star (Θ x) * (c * star c) * K (x p.2) u
              * Θ (Function.update (Function.update x p.2 u) p.1 y) := by ring
          _ = star (Θ x) * r * K (x p.2) u
              * Θ (Function.update (Function.update x p.2 u) p.1 y) := by rw [hcc']
          _ = r * ((1:ℂ) * (star (Θ x) * K (x p.2) u
              * Θ (Function.update (Function.update x p.2 u) p.1 y))) := by ring
      · rw [Set.indicator_of_notMem hy]; ring
  -- the slot mean `aPC` at the pinned condensate
  have h3 : ∀ x u, star (Θ x) * (K (x p.2) u * aPC (ellH v μ) p.1 Θ (Function.update x p.2 u))
      = r * ∫ y in Submission.BoseGases.acube (ellH v μ), star (Θ x) * K (x p.2) u *
          Θ (Function.update (Function.update x p.2 u) p.1 y) := by
    intro x u
    show star (Θ x) * (K (x p.2) u * (((1 / (ellH v μ) ^ 3 : ℝ) : ℂ) *
        ∫ y in Submission.BoseGases.acube (ellH v μ),
          Θ (Function.update (Function.update x p.2 u) p.1 y)))
      = r * ∫ y in Submission.BoseGases.acube (ellH v μ), (star (Θ x) * K (x p.2) u *
          Θ (Function.update (Function.update x p.2 u) p.1 y))
    rw [hr'', MeasureTheory.integral_const_mul]
    ring
  -- ### the pair shape
  have hEq1 : (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * pinCond v μ c (x p.1) * star (pinCond v μ c y) * K (x p.2) u
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      = ∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
          r * ((Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y *
            (star (Θ x) * K (x p.2) u
              * Θ (Function.update (Function.update x p.2 u) p.1 y))) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    exact hpt x y u
  have hPull : (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
          r * ((Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y *
            (star (Θ x) * K (x p.2) u
              * Θ (Function.update (Function.update x p.2 u) p.1 y))))
      = r * (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
          (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y *
            (star (Θ x) * K (x p.2) u
              * Θ (Function.update (Function.update x p.2 u) p.1 y))) := by
    simp only [MeasureTheory.integral_const_mul]
  have hSwap : (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
          (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y *
            (star (Θ x) * K (x p.2) u
              * Θ (Function.update (Function.update x p.2 u) p.1 y)))
      = ∫ x : Work.BoseDict.Xn n, ∫ u : E3, ∫ y : E3,
          (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y *
            (star (Θ x) * K (x p.2) u
              * Θ (Function.update (Function.update x p.2 u) p.1 y)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact MeasureTheory.integral_integral_swap (f := fun y u =>
      (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y *
        (star (Θ x) * K (x p.2) u
          * Θ (Function.update (Function.update x p.2 u) p.1 y)))
      (b3Joint_integrable hΘm hΘb hΘs hKm hKb p hpne x)
  have hInd : (∫ x : Work.BoseDict.Xn n, ∫ u : E3, ∫ y : E3,
          (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y *
            (star (Θ x) * K (x p.2) u
              * Θ (Function.update (Function.update x p.2 u) p.1 y)))
      = ∫ x : Work.BoseDict.Xn n, ∫ u : E3, ∫ y in Submission.BoseGases.acube (ellH v μ),
          star (Θ x) * K (x p.2) u
            * Θ (Function.update (Function.update x p.2 u) p.1 y) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    have hstep : (∫ y : E3, (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator
          (fun _ => (1:ℂ)) y * (star (Θ x) * K (x p.2) u
            * Θ (Function.update (Function.update x p.2 u) p.1 y)))
        = ∫ y : E3, (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator
            (fun y => star (Θ x) * K (x p.2) u
              * Θ (Function.update (Function.update x p.2 u) p.1 y)) y := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      show (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1:ℂ)) y *
          (star (Θ x) * K (x p.2) u * Θ (Function.update (Function.update x p.2 u) p.1 y))
        = (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator
            (fun y => star (Θ x) * K (x p.2) u
              * Θ (Function.update (Function.update x p.2 u) p.1 y)) y
      by_cases hy : y ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
    show (∫ y : E3, (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator
          (fun _ => (1:ℂ)) y * (star (Θ x) * K (x p.2) u
            * Θ (Function.update (Function.update x p.2 u) p.1 y)))
        = ∫ y in Submission.BoseGases.acube (ellH v μ), star (Θ x) * K (x p.2) u
            * Θ (Function.update (Function.update x p.2 u) p.1 y)
    rw [hstep, MeasureTheory.integral_indicator
      (Work.BoseB4.BoxData.boxL_measurableSet _ _), boxL_eq_acube hℓpos]
  have hL : (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * pinCond v μ c (x p.1) * star (pinCond v μ c y) * K (x p.2) u
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      = r * (∫ x : Work.BoseDict.Xn n, ∫ u : E3, ∫ y in Submission.BoseGases.acube (ellH v μ),
          star (Θ x) * K (x p.2) u
            * Θ (Function.update (Function.update x p.2 u) p.1 y)) := by
    rw [hEq1, hPull, hSwap, hInd]
  -- ### the slot shape
  have hR1 : (∫ x : Work.BoseDict.Xn n, star (Θ x) * slotOne K p.2 (aPC (ellH v μ) p.1 Θ) x)
      = ∫ x : Work.BoseDict.Xn n, ∫ u : E3,
          star (Θ x) * (K (x p.2) u * aPC (ellH v μ) p.1 Θ (Function.update x p.2 u)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show star (Θ x) * (∫ u : E3, K (x p.2) u * aPC (ellH v μ) p.1 Θ (Function.update x p.2 u))
        = ∫ u : E3, star (Θ x) * (K (x p.2) u * aPC (ellH v μ) p.1 Θ (Function.update x p.2 u))
    rw [MeasureTheory.integral_const_mul]
  have hR2 : (∫ x : Work.BoseDict.Xn n, ∫ u : E3,
          star (Θ x) * (K (x p.2) u * aPC (ellH v μ) p.1 Θ (Function.update x p.2 u)))
      = ∫ x : Work.BoseDict.Xn n, ∫ u : E3, r * ∫ y in Submission.BoseGases.acube (ellH v μ),
          star (Θ x) * K (x p.2) u
            * Θ (Function.update (Function.update x p.2 u) p.1 y) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    exact h3 x u
  have hR : (∫ x : Work.BoseDict.Xn n, star (Θ x) * slotOne K p.2 (aPC (ellH v μ) p.1 Θ) x)
      = r * (∫ x : Work.BoseDict.Xn n, ∫ u : E3, ∫ y in Submission.BoseGases.acube (ellH v μ),
          star (Θ x) * K (x p.2) u
            * Θ (Function.update (Function.update x p.2 u) p.1 y)) := by
    rw [hR1, hR2]
    simp only [MeasureTheory.integral_const_mul]
  rw [hL, hR]

end Work.BoseBoxFock
