import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.H2.DivQ.hardyIter_good_point
import Submission.Work.FTS.H2.DivQ.hardyIter_tendsto_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Filter
open scoped Topology

/-! ### Elementary auxiliary facts -/

/-- AM-GM in the form `2ab ≤ t a² + b²/t` for `t > 0`. -/
private lemma two_mul_le_mul_sq_add_div_sq {t a b : ℝ} (ht : 0 < t) :
    2 * a * b ≤ t * a ^ 2 + b ^ 2 / t := by
  have h : 0 ≤ (t * a - b) ^ 2 := sq_nonneg _
  rw [show t * a ^ 2 + b ^ 2 / t = (t ^ 2 * a ^ 2 + b ^ 2) / t by
    field_simp]
  rw [le_div_iff₀ ht]
  nlinarith [h]

/-- Every iterated derivative of a function of class `C^∞` on the closed interval `[0,x₁]` is
continuous on the open interval `(0,x₁)`.  (At the endpoint `x₁` this is false in general: the
global `iteratedDeriv m f` there depends on the values of `f` to the right of `x₁`.) -/
private theorem iteratedDeriv_continuousOn_Ioo {f : ℝ → ℝ} {x₁ : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Icc 0 x₁)) (m : ℕ) :
    ContinuousOn (fun x : ℝ => iteratedDeriv m f x) (Set.Ioo 0 x₁) := by
  have hsub : Set.Ioo (0 : ℝ) x₁ ⊆ Set.Icc (0 : ℝ) x₁ := fun x hx => ⟨hx.1.le, hx.2.le⟩
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) x₁) := isOpen_Ioo.uniqueDiffOn
  have hcont : ContinuousOn (iteratedDerivWithin m f (Set.Ioo (0 : ℝ) x₁)) (Set.Ioo (0 : ℝ) x₁) :=
    (hf.mono hsub).continuousOn_iteratedDerivWithin (by simp) hs
  exact hcont.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm

/-- The `k`-th iterated derivative of a function of class `C^∞` on an open set is again of class
`C^∞` there.  (Only the `C^1` statement is needed below.) -/
private theorem contDiffOn_one_iteratedDeriv {g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (k : ℕ)
    (hg : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g s) :
    ContDiffOn ℝ 1 (fun x : ℝ => iteratedDeriv k g x) s := by
  have hk : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g s := hg.of_le (by simp)
  have h1 : ContDiffOn ℝ 1 (iteratedDerivWithin k g s) s :=
    ((contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin (f := g) hs.uniqueDiffOn).mp
      hk).2
  exact h1.congr fun x hx => (iteratedDerivWithin_of_isOpen hs hx).symm

/-- Leibniz relation between the iterated derivatives of `f` and of `H = f/x` on the region
`x ≠ 0`.  (This is the `∞` (i.e. `C^∞`) version of `hardyIter_leibniz`.) -/
private theorem leibniz_fts {f : ℝ → ℝ} {x : ℝ} (k : ℕ) (hx : x ≠ 0)
    (hf : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f x) :
    iteratedDeriv (k + 1) f x
      = x * iteratedDeriv (k + 1) (fun y : ℝ => f y / y) x
        + ((k : ℝ) + 1) * iteratedDeriv k (fun y : ℝ => f y / y) x := by
  have hsm : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => f y / y) x :=
    hf.div contDiffAt_id hx
  have hev : f =ᶠ[nhds x] id * (fun y : ℝ => f y / y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hx)] with y hy
    simp only [Pi.mul_apply, id_eq]
    exact (mul_div_cancel₀ (f y) hy).symm
  rw [hev.iteratedDeriv_eq (k + 1),
    iteratedDeriv_mul (f := id) (g := fun y : ℝ => f y / y) (x := x) (n := k + 1)
      contDiffAt_id (hsm.of_le (by simp))]
  rw [Finset.sum_range_succ']
  rw [Finset.sum_range_succ']
  have htail : ∑ k_1 ∈ Finset.range k,
      ↑((k + 1).choose (k_1 + 1 + 1)) * iteratedDeriv (k_1 + 1 + 1) id x *
        iteratedDeriv (k + 1 - (k_1 + 1 + 1)) (fun y : ℝ => f y / y) x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [iteratedDeriv_id]
    simp only [show ¬(i + 1 + 1 = 0) by omega, show ¬(i + 1 + 1 = 1) by omega, ite_false,
      mul_zero, zero_mul]
  rw [htail]
  simp only [Nat.choose_zero_right, iteratedDeriv_id]
  simp
  ring

/-- Weighted integration by parts for the Hardy inequality, `C^1` version: for `0 < y < x₁` and
`v` of class `C^1` on the closed interval `[y,x₁]`,

`(1+γ)/2 * ∫_y^{x₁} x^{2k-γ} v²
   = ∫_y^{x₁} x^{2k-γ} v (x v' + (k+1) v) - ½(x₁^{2k+1-γ} v(x₁)²) + ½(y^{2k+1-γ} v(y)²)`.

(This is the `C^1` version of `hardyIter_ibp`; the latter assumes analyticity, which is not
available here.) -/
private theorem ibp_fts {v : ℝ → ℝ} {γ x₁ y : ℝ} (k : ℕ) (hy : 0 < y) (hyx : y < x₁)
    (hv : ContDiffOn ℝ 1 v (Set.Icc y x₁)) :
    (1 + γ) / 2 * (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x ^ 2)
      = (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x * (x * deriv v x + ((k : ℝ) + 1) * v x))
        - 1 / 2 * (x₁ ^ (2 * (k : ℝ) + 1 - γ) * v x₁ ^ 2)
        + 1 / 2 * (y ^ (2 * (k : ℝ) + 1 - γ) * v y ^ 2) := by
  have hyle : y ≤ x₁ := le_of_lt hyx
  have hpos : ∀ x ∈ Set.Icc y x₁, 0 < x := fun x hx => lt_of_lt_of_le hy hx.1
  have hdv : ∀ x ∈ Set.Ioo y x₁, HasDerivAt v (deriv v x) x := by
    intro x hx
    have hmem : Set.Icc y x₁ ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    exact ((hv.contDiffAt hmem).differentiableAt (by simp)).hasDerivAt
  have hdvW : ∀ x ∈ Set.Ioo y x₁, derivWithin v (Set.Icc y x₁) x = deriv v x :=
    fun x hx => derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
  have hcontv : ContinuousOn v (Set.Icc y x₁) := hv.continuousOn
  have hcontdvW : ContinuousOn (derivWithin v (Set.Icc y x₁)) (Set.Icc y x₁) :=
    hv.continuousOn_derivWithin (uniqueDiffOn_Icc hyx) le_rfl
  have hcont_rpow_p : ContinuousOn (fun x : ℝ => x ^ (2 * (k : ℝ) + 1 - γ)) (Set.Icc y x₁) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  have hcont_rpow_a : ContinuousOn (fun x : ℝ => x ^ (2 * (k : ℝ) - γ)) (Set.Icc y x₁) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  have hcontDp : ContinuousOn
      (fun x : ℝ => (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
        + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x))
      (Set.Icc y x₁) := by
    refine ((continuousOn_const.mul hcont_rpow_a).mul (hcontv.pow 2)).add ?_
    exact ((hcont_rpow_p.mul hcontv).mul hcontdvW).const_mul 2
  have hII : IntervalIntegrable
      (fun x : ℝ => (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
        + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x)) volume y x₁ :=
    ContinuousOn.intervalIntegrable_of_Icc hyle hcontDp
  have hderivP : ∀ x ∈ Set.Ioo y x₁,
      HasDerivAt (fun x : ℝ => x ^ (2 * (k : ℝ) + 1 - γ) * v x ^ 2)
        ((2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
          + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x)) x := by
    intro x hx
    have hx0 : 0 < x := hpos x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hexp : 2 * (k : ℝ) + 1 - γ - 1 = 2 * (k : ℝ) - γ := by ring
    have hp : HasDerivAt (fun x : ℝ => x ^ (2 * (k : ℝ) + 1 - γ))
        ((2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ)) x := by
      have h := Real.hasDerivAt_rpow_const (x := x) (p := 2 * (k : ℝ) + 1 - γ)
        (Or.inl (ne_of_gt hx0))
      rwa [hexp] at h
    have hvsq : HasDerivAt (fun x : ℝ => v x ^ 2) (2 * v x * deriv v x) x := by
      convert (hdv x hx).pow 2 using 1
      ring
    have hmain := hp.mul hvsq
    have hval : (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
        + x ^ (2 * (k : ℝ) + 1 - γ) * (2 * v x * deriv v x)
        = (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
          + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x) := by
      rw [hdvW x hx]; ring
    rwa [hval] at hmain
  have hcontP : ContinuousOn (fun x : ℝ => x ^ (2 * (k : ℝ) + 1 - γ) * v x ^ 2) (Set.Icc y x₁) :=
    hcont_rpow_p.mul (hcontv.pow 2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hyle hcontP hderivP hII
  have hFTC' : (∫ x in y..x₁, (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
        + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x))
      = x₁ ^ (2 * (k : ℝ) + 1 - γ) * v x₁ ^ 2 - y ^ (2 * (k : ℝ) + 1 - γ) * v y ^ 2 := by
    simpa using hFTC
  have hpt : ∀ x ∈ Set.Icc y x₁,
      (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
        + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x)
      = 2 * (x ^ (2 * (k : ℝ) - γ) * v x
            * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x))
        - (1 + γ) * (x ^ (2 * (k : ℝ) - γ) * v x ^ 2) := by
    intro x hx
    have hx0 : 0 < x := hpos x hx
    have hpow : x ^ (2 * (k : ℝ) + 1 - γ) = x ^ (2 * (k : ℝ) - γ) * x := by
      rw [show 2 * (k : ℝ) + 1 - γ = (2 * (k : ℝ) - γ) + 1 by ring, Real.rpow_add hx0,
        Real.rpow_one]
    rw [hpow]
    ring
  have hcontG1 : ContinuousOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * v x
        * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x)) (Set.Icc y x₁) :=
    (hcont_rpow_a.mul hcontv).mul
      ((continuousOn_id.mul hcontdvW).add (hcontv.const_mul _))
  have hcontG2 : ContinuousOn (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * v x ^ 2) (Set.Icc y x₁) :=
    hcont_rpow_a.mul (hcontv.pow 2)
  have hII1 : IntervalIntegrable (fun x : ℝ => 2 * (x ^ (2 * (k : ℝ) - γ) * v x
      * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x))) volume y x₁ :=
    (ContinuousOn.intervalIntegrable_of_Icc hyle hcontG1).const_mul 2
  have hII2 : IntervalIntegrable (fun x : ℝ => (1 + γ) * (x ^ (2 * (k : ℝ) - γ) * v x ^ 2))
      volume y x₁ :=
    (ContinuousOn.intervalIntegrable_of_Icc hyle hcontG2).const_mul (1 + γ)
  have hDp_eq : (∫ x in y..x₁, (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
        + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x))
      = ∫ x in y..x₁, (2 * (x ^ (2 * (k : ℝ) - γ) * v x
            * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x))
          - (1 + γ) * (x ^ (2 * (k : ℝ) - γ) * v x ^ 2)) :=
    intervalIntegral.integral_congr (fun x hx => hpt x (by rwa [Set.uIcc_of_le hyle] at hx))
  have hsplit : (∫ x in y..x₁, (2 * (x ^ (2 * (k : ℝ) - γ) * v x
            * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x))
          - (1 + γ) * (x ^ (2 * (k : ℝ) - γ) * v x ^ 2)))
      = 2 * (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x
            * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x))
        - (1 + γ) * (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x ^ 2) := by
    rw [intervalIntegral.integral_sub hII1 hII2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have key : 2 * (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x
            * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x))
        - (1 + γ) * (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x ^ 2)
      = x₁ ^ (2 * (k : ℝ) + 1 - γ) * v x₁ ^ 2 - y ^ (2 * (k : ℝ) + 1 - γ) * v y ^ 2 := by
    rw [← hsplit, ← hDp_eq]
    exact hFTC'
  have hCeq : (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x * (x * deriv v x + ((k : ℝ) + 1) * v x))
      = ∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x
          * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ x₁ := by
      change ({x₁}ᶜ : Set ℝ) ∈ MeasureTheory.ae (volume : Measure ℝ)
      rw [MeasureTheory.compl_mem_ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [hne] with x hx
    intro hmem
    have hmemIoc : x ∈ Set.Ioc y x₁ := by rwa [Set.uIoc_of_le hyle] at hmem
    have hxIoo : x ∈ Set.Ioo y x₁ := ⟨hmemIoc.1, lt_of_le_of_ne hmemIoc.2 hx⟩
    rw [hdvW x hxIoo]
  rw [hCeq]
  linarith [key]

/-- Continuity from the right of the set integral in its upper endpoint. -/
private theorem tendsto_setIntegral_Ioc_right {u : ℝ → ℝ} {y x₁ : ℝ} (hy : y < x₁)
    (hu : IntegrableOn u (Set.Ioc y x₁)) :
    Tendsto (fun x : ℝ => ∫ t in Set.Ioc y x, u t) (nhdsWithin x₁ (Set.Iio x₁))
      (nhds (∫ t in Set.Ioc y x₁, u t)) := by
  set ũ : ℝ → ℝ := (Set.Ioc y x₁).indicator u with hũ
  have hũint : Integrable ũ volume := hu.integrable_indicator measurableSet_Ioc
  have hyx_ev : ∀ᶠ x : ℝ in nhdsWithin x₁ (Set.Iio x₁), y < x :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hy)
  have hleft : Tendsto (fun x : ℝ => ∫ t in Set.Ioc x x₁, u t)
      (nhdsWithin x₁ (Set.Iio x₁)) (nhds 0) := by
    have hkey : Tendsto (fun x : ℝ => ∫ t, (Set.Ioc x x₁).indicator ũ t)
        (nhdsWithin x₁ (Set.Iio x₁)) (nhds 0) := by
      have hmain : Tendsto (fun x : ℝ => ∫ t, (Set.Ioc x x₁).indicator ũ t)
          (nhdsWithin x₁ (Set.Iio x₁)) (nhds (∫ t, (fun _ : ℝ => 0) t)) := by
        refine tendsto_integral_filter_of_dominated_convergence (α := ℝ) (G := ℝ) (ι := ℝ)
          (l := nhdsWithin x₁ (Set.Iio x₁)) (μ := volume)
          (F := fun x (t : ℝ) => (Set.Ioc x x₁).indicator ũ t) (f := fun _ : ℝ => 0)
          (fun t => ‖ũ t‖) ?_ ?_ hũint.norm ?_
        · filter_upwards with x
          exact hũint.aestronglyMeasurable.indicator measurableSet_Ioc
        · filter_upwards with x
          filter_upwards with t
          by_cases ht : t ∈ Set.Ioc x x₁
          · rw [Set.indicator_of_mem ht]
          · rw [Set.indicator_of_notMem ht]; simp
        · have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ x₁ := by
            rw [Filter.Eventually, mem_ae_iff]
            simpa using measure_singleton x₁
          filter_upwards [hae] with t htne
          rcases lt_or_gt_of_ne htne with ht | ht
          · have hev : ∀ᶠ x : ℝ in nhdsWithin x₁ (Set.Iio x₁),
                (Set.Ioc x x₁).indicator ũ t = 0 := by
              filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds ht)]
                with x hx
              rw [Set.indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr hx.le))]
            exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)
          · have hev : ∀ᶠ x : ℝ in nhdsWithin x₁ (Set.Iio x₁),
                (Set.Ioc x x₁).indicator ũ t = 0 := by
              filter_upwards [self_mem_nhdsWithin] with x hx
              rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_le.mpr ht))]
            exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)
      simpa using hmain
    refine hkey.congr' ?_
    filter_upwards [hyx_ev] with x hxy
    rw [integral_indicator measurableSet_Ioc]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht => by
      have hmem : t ∈ Set.Ioc y x₁ := ⟨hxy.trans ht.1, ht.2⟩
      rw [hũ, Set.indicator_of_mem hmem]
  have hadd : ∀ᶠ x : ℝ in nhdsWithin x₁ (Set.Iio x₁),
      ∫ t in Set.Ioc y x, u t = (∫ t in Set.Ioc y x₁, u t) - (∫ t in Set.Ioc x x₁, u t) := by
    filter_upwards [self_mem_nhdsWithin, hyx_ev] with x hx1 hxy
    have hunion : Set.Ioc y x ∪ Set.Ioc x x₁ = Set.Ioc y x₁ :=
      Set.Ioc_union_Ioc_eq_Ioc hxy.le hx1.le
    have h1 : IntegrableOn u (Set.Ioc y x) :=
      hu.mono_set fun t ht => ⟨ht.1, ht.2.trans hx1.le⟩
    have h2 : IntegrableOn u (Set.Ioc x x₁) :=
      hu.mono_set fun t ht => ⟨hxy.trans ht.1, ht.2⟩
    have h3 := setIntegral_union (s := Set.Ioc y x) (t := Set.Ioc x x₁)
      (Set.disjoint_left.mpr fun t ht1 ht2 => absurd ht2.1 (not_lt.mpr ht1.2))
      measurableSet_Ioc h1 h2
    rw [hunion] at h3
    linarith
  have hsub' : Tendsto (fun x : ℝ => (∫ t in Set.Ioc y x₁, u t) - (∫ t in Set.Ioc x x₁, u t))
      (nhdsWithin x₁ (Set.Iio x₁)) (nhds (∫ t in Set.Ioc y x₁, u t)) := by
    have h : Tendsto (fun _ : ℝ => (∫ t in Set.Ioc y x₁, u t))
        (nhdsWithin x₁ (Set.Iio x₁)) (nhds (∫ t in Set.Ioc y x₁, u t)) := tendsto_const_nhds
    have h2 := h.sub hleft
    rwa [sub_zero] at h2
  have heq : (fun x : ℝ => (∫ t in Set.Ioc y x₁, u t) - (∫ t in Set.Ioc x x₁, u t))
      =ᶠ[nhdsWithin x₁ (Set.Iio x₁)] fun x : ℝ => ∫ t in Set.Ioc y x, u t :=
    hadd.mono fun x hx => hx.symm
  exact hsub'.congr' heq

/-! ### The one-dimensional weighted Hardy inequality for iterated derivatives of `f/x` -/

/-- Core estimate: the weighted Hardy inequality with the constant `4/(1+γ)²`, stated for an
abstract pair `(v, F1)` related by `F1 = x·v' + (k+1)·v` on `(0,x₁)` (the relation satisfied by
`v = ∂^k(f/x)` and `F1 = ∂^{k+1}f`).  The left-hand side may take the junk value `0` when it is
not integrable. -/
private theorem core {k : ℕ} {γ x₁ : ℝ} (hx₁ : 0 < x₁) (hγ : -1 < γ)
    {v F1 : ℝ → ℝ}
    (hvC1 : ContDiffOn ℝ 1 v (Set.Ioo 0 x₁))
    (hF1cont : ContinuousOn F1 (Set.Ioo 0 x₁))
    (hJ : IntegrableOn (fun x => x ^ (2 * (k : ℝ) - γ) * F1 x ^ 2) (Set.Ioc 0 x₁))
    (hleib : ∀ x ∈ Set.Ioo 0 x₁, F1 x = x * deriv v x + ((k : ℝ) + 1) * v x) :
    (∫ x in Set.Ioc 0 x₁, x ^ (2 * (k : ℝ) - γ) * v x ^ 2)
      ≤ 4 / (1 + γ) ^ 2 * (∫ x in Set.Ioc 0 x₁, x ^ (2 * (k : ℝ) - γ) * F1 x ^ 2) := by
  set u : ℝ → ℝ := fun x => x ^ (2 * (k : ℝ) - γ) * v x ^ 2 with hu
  set A : ℝ := ∫ x in Set.Ioc 0 x₁, u x with hA
  set B : ℝ := ∫ x in Set.Ioc 0 x₁, x ^ (2 * (k : ℝ) - γ) * F1 x ^ 2 with hBdef
  have hγ1 : (0 : ℝ) < 1 + γ := by linarith
  have hne : (1 + γ) ≠ 0 := ne_of_gt hγ1
  have hPnn : ∀ x : ℝ, 0 < x → 0 ≤ x ^ (2 * (k : ℝ) - γ) :=
    fun x hx => Real.rpow_nonneg hx.le _
  have hunn : ∀ x : ℝ, 0 < x → 0 ≤ u x := fun x hx => by
    rw [hu]; exact mul_nonneg (hPnn x hx) (sq_nonneg _)
  have hwt : ContinuousOn (fun t : ℝ => t ^ (2 * (k : ℝ) - γ)) (Set.Ioo (0 : ℝ) x₁) := fun t ht =>
    (Real.continuousAt_rpow_const t _ (Or.inl (ne_of_gt ht.1))).continuousWithinAt
  by_cases hI : IntegrableOn u (Set.Ioc 0 x₁)
  · -- the left-hand side is honest
    have key : ∀ ε : ℝ, 0 < ε → 2 * ε < x₁ →
        (∫ x in Set.Ioc 0 x₁, u x) - (∫ x in Set.Ioc 0 (2 * ε), u x)
          ≤ 4 / (1 + γ) ^ 2 * B + (1 + 4 / (1 + γ)) * (∫ x in Set.Ioc 0 (2 * ε), u x) := by
      intro ε hε h2ε
      have hIccsub : Set.Icc ε (2 * ε) ⊆ Set.Ioo (0 : ℝ) x₁ :=
        fun t ht => ⟨lt_of_lt_of_le hε ht.1, ht.2.trans_lt h2ε⟩
      have hucont : ContinuousOn u (Set.Icc ε (2 * ε)) := by
        rw [hu]
        refine ContinuousOn.mul ?_ ?_
        · exact fun t ht =>
            (Real.continuousAt_rpow_const t _ (Or.inl (ne_of_gt (hIccsub ht).1))).continuousWithinAt
        · exact (hvC1.mono hIccsub).continuousOn.pow 2
      have hnnIoc : ∀ x ∈ Set.Ioc 0 (2 * ε), 0 ≤ u x := fun x hx => hunn x hx.1
      have hintIoc : IntegrableOn u (Set.Ioc 0 (2 * ε)) :=
        hI.mono_set fun t ht => ⟨ht.1, le_of_lt (ht.2.trans_lt h2ε)⟩
      obtain ⟨y, hy_mem, hy_bd⟩ := hardyIter_good_point hε hucont hnnIoc hintIoc
      set C : ℝ := ∫ x in Set.Ioc 0 (2 * ε), u x with hC
      have hy_bd' : y * u y ≤ 2 * C := by rw [hC]; exact hy_bd
      have hy_pos : 0 < y := lt_of_lt_of_le hε hy_mem.1
      have hy_lt : y < x₁ := lt_of_le_of_lt hy_mem.2 h2ε
      have hy_le : y ≤ 2 * ε := hy_mem.2
      have hu_y : IntegrableOn u (Set.Ioc y x₁) :=
        hI.mono_set fun t ht => ⟨hy_pos.trans ht.1, ht.2⟩
      have hF_y : IntegrableOn (fun t => t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2) (Set.Ioc y x₁) :=
        hJ.mono_set fun t ht => ⟨hy_pos.trans ht.1, ht.2⟩
      -- the per-`x` chain: IBP plus AM-GM
      have hchain : ∀ x : ℝ, y < x → x < x₁ →
          (1 + γ) / 2 * (∫ t in Set.Ioc y x, u t)
            ≤ 1 / 2 * ((1 + γ) / 2 * (∫ t in Set.Ioc y x, u t)
                + (2 / (1 + γ)) * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
              + 1 / 2 * (y * u y) := by
        intro x hyx hxx
        have hsub : Set.Icc y x ⊆ Set.Ioo (0 : ℝ) x₁ :=
          fun t ht => ⟨lt_of_lt_of_le hy_pos ht.1, ht.2.trans_lt hxx⟩
        have hwtc : ContinuousOn (fun t : ℝ => t ^ (2 * (k : ℝ) - γ)) (Set.Icc y x) := hwt.mono hsub
        have hvc : ContinuousOn v (Set.Icc y x) := (hvC1.mono hsub).continuousOn
        have hFc : ContinuousOn F1 (Set.Icc y x) := hF1cont.mono hsub
        have hIntV : IntegrableOn (fun t => t ^ (2 * (k : ℝ) - γ) * v t ^ 2) (Set.Ioc y x) :=
          ((hwtc.mul (hvc.pow 2)).integrableOn_compact isCompact_Icc).mono_set
            Set.Ioc_subset_Icc_self
        have hIntF : IntegrableOn (fun t => t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2) (Set.Ioc y x) :=
          ((hwtc.mul (hFc.pow 2)).integrableOn_compact isCompact_Icc).mono_set
            Set.Ioc_subset_Icc_self
        -- the integration-by-parts inequality
        have hibp_le : (1 + γ) / 2 * (∫ t in Set.Ioc y x, u t)
            ≤ (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t|)
              + 1 / 2 * (y * u y) := by
          have hvsub : ContDiffOn ℝ 1 v (Set.Icc y x) := hvC1.mono hsub
          have hibp := ibp_fts (k := k) (γ := γ) (x₁ := x) (y := y) hy_pos hyx hvsub
          have h1 : (∫ t in y..x, t ^ (2 * (k : ℝ) - γ) * v t ^ 2) = ∫ t in Set.Ioc y x, u t :=
            intervalIntegral.integral_of_le hyx.le
          have h2 : (∫ t in y..x, t ^ (2 * (k : ℝ) - γ) * v t
                * (t * deriv v t + ((k : ℝ) + 1) * v t))
              = ∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * v t * F1 t := by
            rw [intervalIntegral.integral_of_le hyx.le]
            refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
            rw [hleib t (hsub (Set.Ioc_subset_Icc_self ht))]
          rw [h1, h2] at hibp
          have hyb : y ^ (2 * (k : ℝ) + 1 - γ) * v y ^ 2 = y * u y := by
            have hrr : y ^ (2 * (k : ℝ) + 1 - γ) = y ^ (2 * (k : ℝ) - γ) * y := by
              have h := Real.rpow_add_one (ne_of_gt hy_pos) (2 * (k : ℝ) - γ)
              rwa [show 2 * (k : ℝ) - γ + 1 = 2 * (k : ℝ) + 1 - γ from by ring] at h
            rw [hrr, hu]
            ring
          rw [hyb] at hibp
          have hxn : 0 ≤ x ^ (2 * (k : ℝ) + 1 - γ) * v x ^ 2 :=
            mul_nonneg (Real.rpow_nonneg (le_of_lt (hy_pos.trans hyx)) _) (sq_nonneg _)
          have habs : (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * v t * F1 t)
              ≤ ∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t| := by
            have hle : (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * v t * F1 t)
                ≤ ∫ t in Set.Ioc y x, |t ^ (2 * (k : ℝ) - γ) * v t * F1 t| :=
              le_trans (le_abs_self _) abs_integral_le_integral_abs
            have heq : (∫ t in Set.Ioc y x, |t ^ (2 * (k : ℝ) - γ) * v t * F1 t|)
                = ∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t| := by
              refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
              have ht0 : 0 ≤ t ^ (2 * (k : ℝ) - γ) :=
                Real.rpow_nonneg (le_of_lt (hy_pos.trans ht.1)) _
              rw [abs_mul, abs_mul, abs_of_nonneg ht0]
            rw [heq] at hle
            exact hle
          linarith [hibp, habs, hxn]
        -- AM-GM at the weight
        have hamgm_x : 2 * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t|)
            ≤ (1 + γ) / 2 * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
              + (2 / (1 + γ)) * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2) := by
          have hpw : ∀ t ∈ Set.Ioc y x,
              2 * (t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t|)
                ≤ (1 + γ) / 2 * (t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
                  + (2 / (1 + γ)) * (t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2) := by
            intro t ht
            have ht0 : 0 < t := hy_pos.trans ht.1
            have hw : 0 ≤ t ^ (2 * (k : ℝ) - γ) := Real.rpow_nonneg ht0.le _
            have ham := two_mul_le_mul_sq_add_div_sq (t := (1 + γ) / 2) (a := |v t|)
              (b := |F1 t|) (by linarith)
            have hdiv : |F1 t| ^ 2 / ((1 + γ) / 2) = (2 / (1 + γ)) * F1 t ^ 2 := by
              rw [sq_abs]
              field_simp [hne] <;> ring
            rw [hdiv, sq_abs] at ham
            have hmul := mul_le_mul_of_nonneg_left ham hw
            nlinarith [hmul]
          have hgcont : ContinuousOn (fun t => (1 + γ) / 2 * (t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
              + (2 / (1 + γ)) * (t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2)) (Set.Icc y x) :=
            ContinuousOn.add
              (ContinuousOn.const_mul (hwtc.mul (hvc.pow 2)) _)
              (ContinuousOn.const_mul (hwtc.mul (hFc.pow 2)) _)
          have hgint : IntegrableOn (fun t => (1 + γ) / 2 * (t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
              + (2 / (1 + γ)) * (t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2)) (Set.Ioc y x) :=
            (hgcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
          have hmono := setIntegral_mono_of_nonneg
            (f := fun t => 2 * (t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t|))
            (g := fun t => (1 + γ) / 2 * (t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
              + (2 / (1 + γ)) * (t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
            (fun t ht => mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg
              (Real.rpow_nonneg (le_of_lt (hy_pos.trans ht.1)) _) (abs_nonneg _))
              (abs_nonneg _))) hpw hgint
          have hL : (∫ t in Set.Ioc y x, 2 * (t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t|))
              = 2 * ∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t| :=
            integral_const_mul 2 _
          have hR : (∫ t in Set.Ioc y x, (1 + γ) / 2 * (t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
                + (2 / (1 + γ)) * (t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
              = (1 + γ) / 2 * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
                + (2 / (1 + γ)) * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2) := by
            rw [integral_add]
            · rw [integral_const_mul, integral_const_mul]
            · exact hIntV.const_mul _
            · exact hIntF.const_mul _
          rw [hL, hR] at hmono
          exact hmono
        linarith [hibp_le, hamgm_x]
      -- pass to the limit `x → x₁⁻`
      have hlim1 : Tendsto (fun x : ℝ => (1 + γ) / 2 * (∫ t in Set.Ioc y x, u t))
          (nhdsWithin x₁ (Set.Iio x₁))
          (nhds ((1 + γ) / 2 * (∫ t in Set.Ioc y x₁, u t))) :=
        (tendsto_setIntegral_Ioc_right hy_lt hu_y).const_mul _
      have hGlim : Tendsto (fun x : ℝ => 1 / 2 * ((1 + γ) / 2 * (∫ t in Set.Ioc y x, u t)
              + (2 / (1 + γ)) * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
            + 1 / 2 * (y * u y))
          (nhdsWithin x₁ (Set.Iio x₁))
          (nhds (1 / 2 * ((1 + γ) / 2 * (∫ t in Set.Ioc y x₁, u t)
              + (2 / (1 + γ)) * (∫ t in Set.Ioc y x₁, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
            + 1 / 2 * (y * u y))) := by
        refine Tendsto.add ?_ tendsto_const_nhds
        refine Tendsto.const_mul _ ?_
        exact Tendsto.add ((tendsto_setIntegral_Ioc_right hy_lt hu_y).const_mul _)
          ((tendsto_setIntegral_Ioc_right hy_lt hF_y).const_mul _)
      have hchain_ev : ∀ᶠ x : ℝ in nhdsWithin x₁ (Set.Iio x₁),
          (1 + γ) / 2 * (∫ t in Set.Ioc y x, u t)
            ≤ 1 / 2 * ((1 + γ) / 2 * (∫ t in Set.Ioc y x, u t)
                + (2 / (1 + γ)) * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
              + 1 / 2 * (y * u y) := by
        filter_upwards [self_mem_nhdsWithin,
          Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hy_lt)] with x hxx hyx
        exact hchain x hyx hxx
      have hlim := le_of_tendsto_of_tendsto hlim1 hGlim hchain_ev
      -- rearrange the resulting inequality
      have hAy_le : (∫ t in Set.Ioc y x₁, u t)
          ≤ (4 / (1 + γ) ^ 2) * (∫ t in Set.Ioc y x₁, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2)
            + (2 / (1 + γ)) * (y * u y) := by
        have hpos : (0 : ℝ) < 4 / (1 + γ) := div_pos (by norm_num) hγ1
        have hmul := mul_le_mul_of_nonneg_left hlim hpos.le
        have e1 : 4 / (1 + γ) * ((1 + γ) / 2 * (∫ t in Set.Ioc y x₁, u t))
            = 2 * (∫ t in Set.Ioc y x₁, u t) := by
          field_simp [hne] <;> ring
        have e2 : 4 / (1 + γ) * (1 / 2 * ((1 + γ) / 2 * (∫ t in Set.Ioc y x₁, u t)
              + (2 / (1 + γ)) * (∫ t in Set.Ioc y x₁, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
              + 1 / 2 * (y * u y))
            = (∫ t in Set.Ioc y x₁, u t)
              + (4 / (1 + γ) ^ 2) * (∫ t in Set.Ioc y x₁, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2)
              + (2 / (1 + γ)) * (y * u y) := by
          field_simp [hne] <;> ring
        rw [e1, e2] at hmul
        linarith [hmul]
      -- comparison of `B` and of the two tail integrals
      have hBy_le : (∫ t in Set.Ioc y x₁, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2) ≤ B := by
        rw [hBdef]
        refine setIntegral_mono_set hJ ?_ ?_
        · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
          exact Eventually.of_forall fun t ht => mul_nonneg (hPnn t ht.1) (sq_nonneg _)
        · exact Eventually.of_forall fun t ht => ⟨hy_pos.trans ht.1, ht.2⟩
      have h4 : (∫ t in Set.Ioc y x₁, u t)
          ≤ (4 / (1 + γ) ^ 2) * B + (2 / (1 + γ)) * (y * u y) :=
        hAy_le.trans (add_le_add (mul_le_mul_of_nonneg_left hBy_le
          (div_nonneg (by norm_num) (sq_nonneg _))) le_rfl)
      have h5 : (∫ t in Set.Ioc y x₁, u t) ≤ (4 / (1 + γ) ^ 2) * B + (4 / (1 + γ)) * C := by
        refine h4.trans (add_le_add le_rfl ?_)
        have h2 : (2 / (1 + γ)) * (y * u y) ≤ (2 / (1 + γ)) * (2 * C) :=
          mul_le_mul_of_nonneg_left hy_bd' (div_nonneg (by norm_num) hγ1.le)
        have e : (2 / (1 + γ)) * (2 * C) = (4 / (1 + γ)) * C := by ring
        rw [e] at h2
        exact h2
      have hsplit : (∫ x in Set.Ioc 0 x₁, u x)
          = (∫ x in Set.Ioc 0 y, u x) + (∫ x in Set.Ioc y x₁, u x) := by
        have hunion : Set.Ioc 0 y ∪ Set.Ioc y x₁ = Set.Ioc 0 x₁ :=
          Set.Ioc_union_Ioc_eq_Ioc hy_pos.le hy_lt.le
        have h1 : IntegrableOn u (Set.Ioc 0 y) :=
          hI.mono_set fun t ht => ⟨ht.1, ht.2.trans hy_lt.le⟩
        have h3 := setIntegral_union (s := Set.Ioc 0 y) (t := Set.Ioc y x₁)
          (Set.disjoint_left.mpr fun t ht1 ht2 => absurd ht2.1 (not_lt.mpr ht1.2))
          measurableSet_Ioc h1 hu_y
        rw [hunion] at h3
        exact h3
      have hCy : (∫ x in Set.Ioc 0 y, u x) ≤ C := by
        rw [hC]
        refine setIntegral_mono_set hintIoc ?_ ?_
        · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
          exact Eventually.of_forall fun t ht => hunn t ht.1
        · exact Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans hy_le⟩
      have hCnn : 0 ≤ C := by
        rw [hC]
        exact setIntegral_nonneg measurableSet_Ioc fun t ht => hunn t ht.1
      have harith : (1 + 4 / (1 + γ)) * C = C + (4 / (1 + γ)) * C := by ring
      rw [harith]
      linarith [h5, hCy, hCnn, hsplit]
    -- pass to the limit `ε → 0⁺`
    have hlimC : Tendsto (fun ε : ℝ => ∫ x in Set.Ioc 0 (2 * ε), u x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      refine (hardyIter_tendsto_zero hx₁ hI).comp ?_
      have h2 : Tendsto (fun ε : ℝ => 2 * ε) (nhds (0 : ℝ)) (nhds (2 * 0)) :=
        tendsto_id.const_mul 2
      simpa using h2.mono_left nhdsWithin_le_nhds
    have hL : Tendsto (fun ε : ℝ => (∫ x in Set.Ioc 0 x₁, u x) - (∫ x in Set.Ioc 0 (2 * ε), u x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∫ x in Set.Ioc 0 x₁, u x)) := by
      simpa using tendsto_const_nhds.sub hlimC
    have hR : Tendsto (fun ε : ℝ => 4 / (1 + γ) ^ 2 * B
          + (1 + 4 / (1 + γ)) * (∫ x in Set.Ioc 0 (2 * ε), u x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (4 / (1 + γ) ^ 2 * B)) := by
      simpa using tendsto_const_nhds.add
        (hlimC.const_mul (1 + 4 / (1 + γ)))
    have hev : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 2 * ε < x₁ := by
      have h1 : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < x₁ / 2 :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Iio_mem_nhds (show (0 : ℝ) < x₁ / 2 by linarith))
      filter_upwards [h1] with ε hε
      linarith
    have hkey_ev : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (∫ x in Set.Ioc 0 x₁, u x) - (∫ x in Set.Ioc 0 (2 * ε), u x)
          ≤ 4 / (1 + γ) ^ 2 * B + (1 + 4 / (1 + γ)) * (∫ x in Set.Ioc 0 (2 * ε), u x) := by
      filter_upwards [self_mem_nhdsWithin, hev] with ε hε h2ε
      exact key ε hε h2ε
    have hfin := le_of_tendsto_of_tendsto hL hR hkey_ev
    rw [hA]
    exact hfin
  · -- the left-hand side is the junk value `0`
    rw [hA, integral_undef hI, hBdef]
    exact mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _))
      (setIntegral_nonneg measurableSet_Ioc fun t ht =>
        mul_nonneg (hPnn t ht.1) (sq_nonneg _))

/-- **Elgindi's Lemma of tex 1301** (the paper's "variant on `HardyInequality2`"): the weighted
Hardy inequality for iterated derivatives of `f/x`,

  `∫_0^{x₁} x^{2k-γ}(∂_x^k (f/x))² dx ≤ C/(1+γ)² ∫_0^{x₁} x^{2k-γ}(∂_x^{k+1} f)² dx`,

for `f` of class `C^∞` on the closed interval `[0,x₁]`, every `k : ℕ` and every `γ > -1`, with `C`
a universal constant; the right-hand side is assumed honest, the left-hand side may be the junk
value `0`.  This is the second of the two lemmas from which the paper derives Proposition
`DivisionBySin`; with the substitution `x = sin 2θ` the weight `x^{2k-γ}` is the paper's angular
weight and `f/x` becomes `f/sin(2θ)`.

ROUTE (the paper's own proof, tex 1301, made junk-safe).  With `H = f/x` we have
`∂_x^{k+1}f = x ∂_x^{k+1}H + (k+1) ∂_x^k H`; integrating by parts over `(ε,x₁)` and using
`C(k+1,k) = k+1`,

  `(1+γ)/2 * A_ε = ∫_ε^{x₁} x^{2k-γ} H^{(k)} f^{(k+1)}
      - (1/2)x₁^{2k+1-γ}(H^{(k)}(x₁))² + (1/2)ε^{2k+1-γ}(H^{(k)}(ε))²`,  `A_ε = ∫_ε^{x₁}x^{2k-γ}(H^{(k)})²`.

Cauchy–Schwarz with `B = ∫_0^{x₁}x^{2k-γ}(f^{(k+1)})²` (honest) gives
`(1+γ)/2 A_ε ≤ A_ε^{1/2}B^{1/2} + (1/2)εu(ε)` with `u(x) = x^{2k-γ}(H^{(k)}(x))²`.  If `u` is not
integrable the conclusion holds because the left integral is junk `0`.  Otherwise `u` is
continuous on `(0,x₁)` and integrable, so `xu(x) → 0` as `x → 0⁺` (if `x_n u(x_n) ≥ c > 0` along
`x_n → 0`, continuity gives `u ≥ c/(4x_n)` on an interval of length `∝ x_n`, contradicting
`∫_0^δ u → 0`), hence `εu(ε) → 0`; solving the quadratic inequality gives `A_ε ≤ C/(1+γ)² B`
uniformly in `ε`, and monotone convergence gives the claim.

FORMALISATION.  The estimate is proved in `core` above.  The varying point `ε` of the paper is
replaced by the mean-value "good point" `y ∈ [ε,2ε]` of `hardyIter_good_point` (which controls the
boundary term `y·u(y)` by twice the tail integral `∫_0^{2ε}u`, whence by `0` in the limit), the
inequality `2ab ≤ λa² + b²/λ` replaces Cauchy–Schwarz (so that no square root appears), and the
integration by parts `ibp_fts` is applied on the *interior* interval `(y,x)` with `x → x₁⁻`: this
is necessary because the endpoint value `(f/x)^{(k)}(x₁)` is junk (the hypothesis constrains `f`
only on `[0,x₁]`), while the corresponding boundary term is anyway dropped. -/
theorem paperHardyIter :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (γ x₁ : ℝ), 0 < x₁ → -1 < γ → ∀ f : ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Icc 0 x₁) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2) (Set.Ioc 0 x₁) →
      (∫ x in (0 : ℝ)..x₁,
          x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv k (fun y : ℝ => f y / y) x) ^ 2)
        ≤ C / (1 + γ) ^ 2 *
          (∫ x in (0 : ℝ)..x₁,
            x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2) := by
  refine ⟨4, by norm_num, ?_⟩
  intro k γ x₁ hx₁ hγ f hf hB
  have hgm : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f x / x) (Set.Ioo 0 x₁) :=
    (hf.mono Set.Ioo_subset_Icc_self).div contDiffOn_id fun x hx => ne_of_gt hx.1
  have hvC1 : ContDiffOn ℝ 1 (fun x : ℝ => iteratedDeriv k (fun y : ℝ => f y / y) x)
      (Set.Ioo 0 x₁) := contDiffOn_one_iteratedDeriv isOpen_Ioo k hgm
  have hF1cont : ContinuousOn (fun x : ℝ => iteratedDeriv (k + 1) f x) (Set.Ioo 0 x₁) :=
    iteratedDeriv_continuousOn_Ioo hf (k + 1)
  have hleib : ∀ x ∈ Set.Ioo (0 : ℝ) x₁,
      iteratedDeriv (k + 1) f x
        = x * deriv (fun y : ℝ => iteratedDeriv k (fun z : ℝ => f z / z) y) x
          + ((k : ℝ) + 1) * iteratedDeriv k (fun y : ℝ => f y / y) x := by
    intro x hx
    have hxn : x ≠ 0 := ne_of_gt hx.1
    have hfd : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f x :=
      hf.contDiffAt (Icc_mem_nhds hx.1 hx.2)
    have h := leibniz_fts (f := f) (x := x) k hxn hfd
    rw [h, iteratedDeriv_succ]
  rw [intervalIntegral.integral_of_le hx₁.le, intervalIntegral.integral_of_le hx₁.le]
  exact core hx₁ hγ hvC1 hF1cont hB hleib

end Work.FTS.H2.DivQ
