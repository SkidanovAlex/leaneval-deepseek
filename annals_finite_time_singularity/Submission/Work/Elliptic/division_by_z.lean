/-
Copyright: work module for the Elgindi finite-time singularity project.

# `(z+1)/z · f` gains one derivative in the `𝒲^{4,∞}`-scale

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021, §H2.

The paper's Proposition (tex 1216): if `f` is smooth with `f(0,θ) = 0` for all `θ`,
then `|(z+1)/z · f|_{𝒲^{4,∞}} ≤ C |f|_{𝒲^{5,∞}}`, "the proof simply consisting of
examining the Taylor expansion of `f` in `z`".

Formally: write `g = (z+1)/z · f = f + f/z`.  The quotient `f/z` gains one order of
`z`-differentiability, because the Taylor quotient of a function vanishing at `0` is
smooth at `0`.  We realise that extension by the parameter integral

`DivExtN h k z = ∫_0^1 t^k · h^{(k+1)}(t z) dt`,

which for `k = 0` equals `h z / z` for `z ≠ 0` and extends it smoothly across `z = 0`;
its derivatives at `0` are the Taylor coefficients of `h/z`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.HkAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The `z`-slice calculus -/

/-- The `k`-th iterated `z`-derivative of a curried function is the iterated derivative of
its `z`-slice. -/
theorem pzIter_eq_iteratedDeriv (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter k f z θ = iteratedDeriv k (fun z' => f z' θ) z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pz, iteratedDeriv_succ]
    have hfun : (fun z' => Work.Spaces.pzIter k f z' θ)
        = fun z' => iteratedDeriv k (fun z'' => f z'' θ) z' := funext fun z' => ih z'
    rw [hfun]

/-- The `z`-slice of a function smooth on a neighbourhood of the closed quadrant is smooth
on an open neighbourhood of `[0,∞)`. -/
theorem contDiffOn_slice_smoothNbhd {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ContDiffOn ℝ ⊤ (fun z => f z θ) (Set.Ioi (-1 : ℝ)) := by
  have hι : ContDiffOn ℝ ⊤ (fun z : ℝ => (z, θ)) (Set.Ioi (-1 : ℝ)) :=
    contDiffOn_id.prodMk contDiffOn_const
  have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (-1 : ℝ))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := by
    intro z hz
    exact ⟨hz, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have h := hf.comp hι hmap
  simpa [Function.comp_def, Function.uncurry] using h

/-! ## The Taylor quotient of a function of one variable -/

/-- The Taylor quotient of `h` written as a parameter integral:
`DivExtN h k z = ∫_0^1 t^k h^{(k+1)}(t z) dt`.  For `k = 0` this equals `h z / z` for
`z ≠ 0` and gives a smooth extension of the quotient to `z = 0`. -/
noncomputable def DivExtN (h : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => ∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) h (t * z)

/-- Iterated derivatives of a function smooth on `(-1,∞)` are smooth there. -/
theorem iteratedDeriv_contDiffOn_Ioi {h : ℝ → ℝ} (hh : ContDiffOn ℝ ⊤ h (Set.Ioi (-1)))
    (m : ℕ) : ContDiffOn ℝ ⊤ (iteratedDeriv m h) (Set.Ioi (-1)) := by
  induction m with
  | zero => simpa using hh
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen isOpen_Ioi (le_top : (⊤ : ℕ∞ω) + 1 ≤ ⊤)

/-- The derivative of the parameter integral `DivExtN h k`. -/
theorem DivExtN_hasDerivAt (h : ℝ → ℝ) (hh : ContDiffOn ℝ ⊤ h (Set.Ioi (-1))) (k : ℕ)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    HasDerivAt (DivExtN h k) (DivExtN h (k + 1) z) z := by
  have hz' : (-1 : ℝ) < z := hz
  set a : ℝ := min 0 ((z - 1) / 2) with ha
  set b : ℝ := z + 1 with hb
  have ha_le : a ≤ 0 := by rw [ha]; exact min_le_left _ _
  have ha_le' : a ≤ (z - 1) / 2 := by rw [ha]; exact min_le_right _ _
  have ha_gt : -1 < a := by
    rw [ha]; exact lt_min (by norm_num) (by linarith)
  have hb_pos : 0 < b := by rw [hb]; linarith
  have haz : a < z := by linarith
  have hzb : z < b := by rw [hb]; linarith
  have hsub : Set.Icc a b ⊆ Set.Ioi (-1 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1]
  have hcont : ContinuousOn (iteratedDeriv (k + 2) h) (Set.Icc a b) :=
    (iteratedDeriv_contDiffOn_Ioi hh (k + 2)).continuousOn.mono hsub
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hmem : ∀ x ∈ Set.Ioo a b, ∀ t ∈ Set.Icc (0 : ℝ) 1, t * x ∈ Set.Icc a b := by
    intro x hx t ht
    obtain ⟨ht0, ht1⟩ := ht
    obtain ⟨hxa, hxb⟩ := hx
    constructor
    · rcases lt_or_ge 0 x with hx0 | hx0
      · exact le_trans ha_le (mul_nonneg ht0 (le_of_lt hx0))
      · have h1 : x ≤ t * x := by
          nlinarith [mul_nonneg_of_nonpos_of_nonpos hx0
            (show t - 1 ≤ 0 by linarith)]
        linarith
    · rcases lt_or_ge 0 x with hx0 | hx0
      · have h2 : t * x ≤ x := by nlinarith
        linarith
      · have : t * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hx0
        linarith
  have hs_nhds : Set.Ioo a b ∈ 𝓝 z := isOpen_Ioo.mem_nhds ⟨haz, hzb⟩
  have hcontF : ∀ x ∈ Set.Ioo a b,
      ContinuousOn (fun t : ℝ => t ^ k * iteratedDeriv (k + 1) h (t * x))
        (Set.uIcc (0 : ℝ) 1) := by
    intro x hx
    refine ContinuousOn.mul (continuous_pow k).continuousOn ?_
    refine (iteratedDeriv_contDiffOn_Ioi hh (k + 1)).continuousOn.comp
      (continuousOn_id.mul_const x) ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hsub (hmem x hx t ht)
  have hcontG : ContinuousOn
      (fun t : ℝ => t ^ (k + 1) * iteratedDeriv (k + 2) h (t * z)) (Set.uIcc (0 : ℝ) 1) := by
    refine ContinuousOn.mul (continuous_pow (k + 1)).continuousOn ?_
    refine (iteratedDeriv_contDiffOn_Ioi hh (k + 2)).continuousOn.comp
      (continuousOn_id.mul_const z) ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hsub (hmem z ⟨haz, hzb⟩ t ht)
  have huIoc_sub : Set.uIoc (0 : ℝ) 1 ⊆ Set.uIcc (0 : ℝ) 1 := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hIt : ∀ t ∈ Set.uIoc (0 : ℝ) 1, t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun t : ℝ => t ^ k * iteratedDeriv (k + 1) h (t * x))
      ((volume : Measure ℝ).restrict (Set.uIoc 0 1)) := by
    filter_upwards [hs_nhds] with x hx
    exact ((hcontF x hx).mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable
      (fun t : ℝ => t ^ k * iteratedDeriv (k + 1) h (t * z)) volume 0 1 :=
    (hcontF z ⟨haz, hzb⟩).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => t ^ (k + 1) * iteratedDeriv (k + 2) h (t * z))
      ((volume : Measure ℝ).restrict (Set.uIoc 0 1)) :=
    (hcontG.mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ x ∈ Set.Ioo a b, ‖t ^ (k + 1) * iteratedDeriv (k + 2) h (t * x)‖ ≤ C := by
    filter_upwards with t ht x hx
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := hIt t ht
    rw [Real.norm_eq_abs, abs_mul]
    have hpow : |t ^ (k + 1)| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg ht'.1 _)]
      exact pow_le_one₀ ht'.1 ht'.2
    have hg2 : |iteratedDeriv (k + 2) h (t * x)| ≤ C := by
      simpa [Real.norm_eq_abs] using hC (t * x) (hmem x hx t ht')
    calc |t ^ (k + 1)| * |iteratedDeriv (k + 2) h (t * x)| ≤ 1 * C :=
          mul_le_mul hpow hg2 (abs_nonneg _) (by positivity)
      _ = C := one_mul C
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ x ∈ Set.Ioo a b,
        HasDerivAt (fun x : ℝ => t ^ k * iteratedDeriv (k + 1) h (t * x))
          (t ^ (k + 1) * iteratedDeriv (k + 2) h (t * x)) x := by
    filter_upwards with t ht x hx
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := hIt t ht
    have hd : HasDerivAt (iteratedDeriv (k + 1) h)
        (iteratedDeriv (k + 2) h (t * x)) (t * x) := by
      have hdAt : DifferentiableAt ℝ (iteratedDeriv (k + 1) h) (t * x) :=
        ((iteratedDeriv_contDiffOn_Ioi hh (k + 1)).differentiableOn (n := ⊤) (by simp)).differentiableAt
          (isOpen_Ioi.mem_nhds (hsub (hmem x hx t ht')))
      have h2 : iteratedDeriv (k + 2) h = deriv (iteratedDeriv (k + 1) h) := iteratedDeriv_succ
      rw [h2]
      exact hdAt.hasDerivAt
    have hg : HasDerivAt (fun y : ℝ => t * y) t x := by
      simpa using (hasDerivAt_id x).const_mul t
    have hcomp : HasDerivAt (fun y : ℝ => iteratedDeriv (k + 1) h (t * y))
        (iteratedDeriv (k + 2) h (t * x) * t) x := HasDerivAt.comp x hd hg
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hcomp.const_mul (t ^ k)
  have hkey := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t => t ^ k * iteratedDeriv (k + 1) h (t * x))
    (F' := fun x t => t ^ (k + 1) * iteratedDeriv (k + 2) h (t * x))
    (x₀ := z) (s := Set.Ioo a b) (a := (0 : ℝ)) (b := (1 : ℝ))
    (μ := (volume : Measure ℝ)) (bound := fun _ => C)
    hs_nhds hF_meas hF_int hF'_meas h_bound intervalIntegrable_const hdiff
  exact hkey.2

/-- `DivExtN h 0` agrees with the quotient `h z / z` off `0`. -/
theorem DivExtN_zero_eq_div (h : ℝ → ℝ) (hh : ContDiffOn ℝ ⊤ h (Set.Ioi (-1))) (hh0 : h 0 = 0)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) (hz0 : z ≠ 0) :
    DivExtN h 0 z = h z / z := by
  have hsubu : Set.uIcc (0 : ℝ) z ⊆ Set.Ioi (-1) := by
    intro x hx
    have hx' : x ∈ Set.Icc (min (0 : ℝ) z) (max (0 : ℝ) z) := hx
    have h1 : -1 < min (0 : ℝ) z := lt_min (by norm_num) hz
    exact lt_of_lt_of_le h1 hx'.1
  have hftc : ∫ x in (0 : ℝ)..z, deriv h x = h z - h 0 := by
    refine intervalIntegral.integral_deriv_eq_sub ?_ ?_
    · intro x hx
      exact (hh.differentiableOn (n := ⊤) (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds (hsubu hx))
    · have h1 : IntervalIntegrable (iteratedDeriv 1 h) volume 0 z :=
        ((iteratedDeriv_contDiffOn_Ioi hh 1).continuousOn.mono hsubu).intervalIntegrable
      simpa [iteratedDeriv_one] using h1
  have hsubst : ∫ t in (0 : ℝ)..1, deriv h (t * z) = z⁻¹ * ∫ x in (0 : ℝ)..z, deriv h x := by
    have h1 := intervalIntegral.integral_comp_mul_right (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := deriv h) (c := z) hz0
    simpa using h1
  rw [DivExtN]
  simp only [Nat.zero_add, pow_zero, one_mul, iteratedDeriv_one]
  rw [hsubst, hftc, hh0, sub_zero, div_eq_inv_mul]

/-- The `m`-th derivative of `DivExtN h n` is `DivExtN h (n + m)`. -/
theorem DivExtN_iteratedDeriv (h : ℝ → ℝ) (hh : ContDiffOn ℝ ⊤ h (Set.Ioi (-1))) (m n : ℕ) :
    Set.EqOn (iteratedDeriv m (DivExtN h n)) (DivExtN h (n + m)) (Set.Ioi (-1)) := by
  induction m with
  | zero => intro z hz; simp [DivExtN]
  | succ m ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have hev : (iteratedDeriv m (DivExtN h n)) =ᶠ[𝓝 z] (DivExtN h (n + m)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact ih hw
    rw [hev.deriv_eq, (DivExtN_hasDerivAt h hh (n + m) hz).deriv]
    rw [show n + m + 1 = n + (m + 1) from by omega]

/-- Every `DivExtN h n` is smooth on `(-1,∞)`. -/
theorem DivExtN_contDiffOn (h : ℝ → ℝ) (hh : ContDiffOn ℝ ⊤ h (Set.Ioi (-1))) (n k : ℕ) :
    ContDiffOn ℝ k (DivExtN h n) (Set.Ioi (-1)) := by
  refine contDiffOn_of_differentiableOn_deriv (n := (k : ℕ∞)) ?_
  intro m _
  have h1 : DifferentiableOn ℝ (iteratedDeriv m (DivExtN h n)) (Set.Ioi (-1)) := by
    have h2 : DifferentiableOn ℝ (DivExtN h (n + m)) (Set.Ioi (-1)) := fun z hz =>
      (DivExtN_hasDerivAt h hh (n + m) hz).differentiableAt.differentiableWithinAt
    refine h2.congr ?_
    intro x hx
    exact (DivExtN_iteratedDeriv h hh m n) hx
  refine h1.congr ?_
  intro x hx
  exact iteratedDerivWithin_of_isOpen isOpen_Ioi hx

/-! ## The jump lemma -/

/-- At `0`, a function which agrees with a differentiable function on `(0,ε)` has derivative
either `0` (the junk value when it is not differentiable) or the derivative of that function. -/
theorem deriv_jump {F A : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hFA : ∀ z ∈ Set.Ioo (0 : ℝ) ε, F z = A z) (hA : DifferentiableAt ℝ A 0) :
    deriv F 0 = 0 ∨ deriv F 0 = deriv A 0 := by
  rcases em (DifferentiableAt ℝ F 0) with hd | hd
  · right
    have hmem : Set.Ioo (0 : ℝ) ε ∈ 𝓝[Set.Ioi (0 : ℝ)] 0 := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Ioo (-1) ε, isOpen_Ioo, ⟨by norm_num, hε⟩,
        fun x hx => ⟨hx.2, hx.1.2⟩⟩
    have hF0 : F 0 = A 0 := by
      have h1 : Tendsto F (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (F 0)) :=
        hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto F (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (A 0)) := by
        have hAc : Tendsto A (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (A 0)) :=
          hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        refine hAc.congr' ?_
        filter_upwards [hmem] with w hw
        exact (hFA w hw).symm
      exact tendsto_nhds_unique h1 h2
    have hev : (fun t : ℝ => (F t - F 0) / t) =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
        (fun t : ℝ => (A t - A 0) / t) := by
      filter_upwards [hmem] with t ht
      rw [hFA t ht, hF0]
    have hFt : Tendsto (fun t : ℝ => (F t - F 0) / t) (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 (deriv F 0)) := by
      have hle : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝[({0} : Set ℝ)ᶜ] 0 :=
        nhdsWithin_mono 0 (fun x hx => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hx)
      refine ((hd.hasDerivAt.tendsto_slope_zero).mono_left hle).congr' ?_
      filter_upwards with t
      simp [div_eq_inv_mul]
    have hAt : Tendsto (fun t : ℝ => (A t - A 0) / t) (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 (deriv A 0)) := by
      have hle : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝[({0} : Set ℝ)ᶜ] 0 :=
        nhdsWithin_mono 0 (fun x hx => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hx)
      refine ((hA.hasDerivAt.tendsto_slope_zero).mono_left hle).congr' ?_
      filter_upwards with t
      simp [div_eq_inv_mul]
    exact tendsto_nhds_unique (hFt.congr' hev) hAt
  · left
    exact deriv_zero_of_not_differentiableAt hd

/-- The jump lemma for iterated derivatives. -/
theorem iteratedDeriv_jump {F A : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hFA : ∀ z ∈ Set.Ioo (0 : ℝ) ε, F z = A z) {k : ℕ} (hk : 1 ≤ k)
    (hA : ContDiffAt ℝ k A 0) :
    iteratedDeriv k F 0 = 0 ∨ iteratedDeriv k F 0 = iteratedDeriv k A 0 := by
  induction k generalizing F A with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simpa [iteratedDeriv_one] using deriv_jump hε hFA (hA.differentiableAt_one)
    · have hFA' : ∀ z ∈ Set.Ioo (0 : ℝ) ε, deriv F z = deriv A z := by
        intro z hz
        exact (Filter.EventuallyEq.deriv_eq
          (by
            filter_upwards [isOpen_Ioo.mem_nhds hz] with w hw
            exact hFA w hw))
      have hA' : ContDiffAt ℝ k (deriv A) 0 := hA.derivWithin (m := k) (by rw [Nat.cast_add, Nat.cast_one])
      rcases ih hFA' hkpos hA' with h | h
      · left
        simpa [iteratedDeriv_succ'] using h
      · right
        simpa [iteratedDeriv_succ'] using h

/-! ## The main estimate -/

/-- The angular weight `sin(2θ)^{-α/5}/(α + sin(2θ))` is nonnegative on `[0,π/2]`. -/
theorem sin_weight_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) := by
  have hsin : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  exact div_nonneg (Real.rpow_nonneg hsin _) (by linarith)

/-- The parameter integral `∫_0^1 t^k h^{(k+1)}(tz) dt`, weighted by `(z+1)^k` and `W`, is bounded
by the sup of `(u+1)^{k+1} h^{(k+1)}(u) W`: the remaining factor
`t^k (z+1)^k/(tz+1)^{k+1}` is at most `1` on `[0,1]`. -/
theorem divz_integral_bound (k : ℕ) (h : ℝ → ℝ) {W M : ℝ} (hW : 0 ≤ W)
    (hM : ∀ u ∈ Set.Ici (0 : ℝ), |(u + 1) ^ (k + 1) * iteratedDeriv (k + 1) h u| * W ≤ M)
    {z : ℝ} (hz : 0 < z) :
    |(z + 1) ^ k * (∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) h (t * z)) * W| ≤ M := by
  have hMnn : 0 ≤ M := by
    have h0 := hM 0 (by simp)
    nlinarith [abs_nonneg ((0 + 1) ^ (k + 1) * iteratedDeriv (k + 1) h 0), hW, h0]
  have hz1 : 0 < z + 1 := by linarith
  have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      |t ^ k * ((z + 1) ^ k * W) * iteratedDeriv (k + 1) h (t * z)| ≤ M := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have hden : 0 < (t * z + 1) ^ (k + 1) :=
      pow_pos (by nlinarith) _
    have hG : |(t * z + 1) ^ (k + 1) * iteratedDeriv (k + 1) h (t * z)| * W ≤ M :=
      hM (t * z) (mul_nonneg ht0 (le_of_lt hz))
    have hφle : t ^ k * (z + 1) ^ k / (t * z + 1) ^ (k + 1) ≤ 1 := by
      rw [div_le_one hden]
      have hstep : t * (z + 1) ≤ t * z + 1 := by nlinarith [ht.2]
      calc t ^ k * (z + 1) ^ k = (t * (z + 1)) ^ k := (mul_pow t (z + 1) k).symm
        _ ≤ (t * z + 1) ^ k := pow_le_pow_left₀ (by positivity) hstep k
        _ ≤ (t * z + 1) ^ (k + 1) := by
            exact pow_le_pow_right₀ (by nlinarith) (Nat.le_succ k)
    have hφnn : 0 ≤ t ^ k * (z + 1) ^ k / (t * z + 1) ^ (k + 1) :=
      div_nonneg (by positivity) hden.le
    have hsing : |t ^ k * ((z + 1) ^ k * W) * iteratedDeriv (k + 1) h (t * z)|
        = t ^ k * (z + 1) ^ k * W * |iteratedDeriv (k + 1) h (t * z)| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht0 k),
        abs_of_nonneg (pow_nonneg (le_of_lt hz1) k), abs_of_nonneg hW]
      ring
    have hden' : |(t * z + 1) ^ (k + 1) * iteratedDeriv (k + 1) h (t * z)|
        = (t * z + 1) ^ (k + 1) * |iteratedDeriv (k + 1) h (t * z)| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by nlinarith) _)]
    have hkey : |t ^ k * ((z + 1) ^ k * W) * iteratedDeriv (k + 1) h (t * z)|
        = (t ^ k * (z + 1) ^ k / (t * z + 1) ^ (k + 1))
          * (|(t * z + 1) ^ (k + 1) * iteratedDeriv (k + 1) h (t * z)| * W) := by
      rw [hsing, hden']
      field_simp
    rw [hkey]
    calc (t ^ k * (z + 1) ^ k / (t * z + 1) ^ (k + 1))
          * (|(t * z + 1) ^ (k + 1) * iteratedDeriv (k + 1) h (t * z)| * W)
        ≤ 1 * M := mul_le_mul hφle hG (mul_nonneg (abs_nonneg _) hW) (by norm_num)
      _ = M := one_mul M
  calc |(z + 1) ^ k * (∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) h (t * z)) * W|
      = |∫ t in (0 : ℝ)..1, t ^ k * ((z + 1) ^ k * W) * iteratedDeriv (k + 1) h (t * z)| := by
        congr 1
        have hcongr : (fun t : ℝ => t ^ k * ((z + 1) ^ k * W) * iteratedDeriv (k + 1) h (t * z))
            = fun t : ℝ => (t ^ k * iteratedDeriv (k + 1) h (t * z)) * ((z + 1) ^ k * W) := by
          funext t; ring
        rw [hcongr, intervalIntegral.integral_mul_const]
        ring
    _ ≤ M := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
          (C := M) (f := fun t : ℝ => t ^ k * ((z + 1) ^ k * W) * iteratedDeriv (k + 1) h (t * z))
          (fun t ht => by rw [Real.norm_eq_abs]; exact hpt t ht)
        simpa using h

/-- **The slice estimate.**  If `H` vanishes at `0` and `(u+1)^j H^{(j)}(u) W` is bounded by `M`
for `j = k` and `j = k+1`, then the same bound (with constant `2`) holds for the quotient
`(z+1)/z H` at level `k`. -/
theorem slice_div_z (k : ℕ) (H : ℝ → ℝ) (W M : ℝ) (hW : 0 ≤ W)
    (hH : ContDiffOn ℝ ⊤ H (Set.Ioi (-1))) (hH0 : H 0 = 0)
    (hb1 : ∀ z ∈ Set.Ici (0 : ℝ), |(z + 1) ^ k * iteratedDeriv k H z| * W ≤ M)
    (hb2 : ∀ z ∈ Set.Ici (0 : ℝ), |(z + 1) ^ (k + 1) * iteratedDeriv (k + 1) H z| * W ≤ M) :
    ∀ z ∈ Set.Ici (0 : ℝ),
      |(z + 1) ^ k * iteratedDeriv k (fun z => (z + 1) / z * H z) z * W| ≤ 2 * M := by
  have hMnn : 0 ≤ M := by
    have h := hb1 0 (by simp)
    nlinarith [abs_nonneg ((0 + 1) ^ k * iteratedDeriv k H 0), hW, h]
  intro z hz
  rcases lt_or_ge 0 z with hzpos | hzle
  · have hzIoi : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
    have hmem : Set.Ioo (z / 2) (3 * z / 2) ∈ 𝓝 z :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have hHc : ContDiffAt ℝ k H z :=
      (hH.contDiffAt (isOpen_Ioi.mem_nhds hzIoi)).of_le le_top
    have hqc : ContDiffAt ℝ k (fun w => H w / w) z :=
      hHc.div contDiffAt_id (by simpa using hzpos.ne')
    have hev1 : (fun w : ℝ => (w + 1) / w * H w) =ᶠ[𝓝 z] (fun w => H w + H w / w) := by
      filter_upwards [hmem] with w hw
      have hw0 : w ≠ 0 := ne_of_gt (by linarith [hw.1])
      field_simp
    have hqeq : iteratedDeriv k (fun w => H w / w) z = DivExtN H k z := by
      have hev2 : (fun w : ℝ => H w / w) =ᶠ[𝓝 z] DivExtN H 0 := by
        filter_upwards [hmem] with w hw
        have hw0 : w ≠ 0 := ne_of_gt (by linarith [hw.1])
        have hwIoi : w ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith [hw.1]
        exact (DivExtN_zero_eq_div H hH hH0 hwIoi hw0).symm
      rw [Filter.EventuallyEq.iteratedDeriv_eq k hev2]
      simpa using (DivExtN_iteratedDeriv H hH k 0) hzIoi
    have hsum : iteratedDeriv k (fun w : ℝ => (w + 1) / w * H w) z
        = iteratedDeriv k H z + DivExtN H k z := by
      rw [Filter.EventuallyEq.iteratedDeriv_eq k hev1]
      rw [show (fun w : ℝ => H w + H w / w) = H + (fun w => H w / w) from rfl]
      rw [iteratedDeriv_add hHc hqc]
      rw [hqeq]
    rw [hsum]
    have hDiv : DivExtN H k z = ∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) H (t * z) := rfl
    rw [hDiv]
    have hb1' : |(z + 1) ^ k * iteratedDeriv k H z| * W ≤ M := hb1 z hz
    have hb2' : |(z + 1) ^ k * (∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) H (t * z)) * W|
        ≤ M := divz_integral_bound k H hW hb2 hzpos
    calc |(z + 1) ^ k * (iteratedDeriv k H z
            + ∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) H (t * z)) * W|
        = |(z + 1) ^ k * iteratedDeriv k H z * W
            + (z + 1) ^ k * (∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) H (t * z)) * W| := by
          congr 1; ring
      _ ≤ |(z + 1) ^ k * iteratedDeriv k H z * W|
            + |(z + 1) ^ k * (∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) H (t * z)) * W| :=
          abs_add_le _ _
      _ = |(z + 1) ^ k * iteratedDeriv k H z| * W
            + |(z + 1) ^ k * (∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) H (t * z)) * W| := by
          rw [abs_mul, abs_of_nonneg hW]
      _ ≤ M + M := add_le_add hb1' hb2'
      _ = 2 * M := by ring
  · have hz0 : z = 0 := le_antisymm hzle hz
    subst hz0
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [iteratedDeriv_zero]
      have hzero : |(0 + 1) ^ 0 * ((0 + 1) / 0 * H 0) * W| = 0 := by simp
      rw [hzero]
      linarith
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      set A : ℝ → ℝ := fun w => H w + DivExtN H 0 w with hA
      have hAc : ContDiffAt ℝ (k' + 1) H 0 :=
        (hH.contDiffAt (isOpen_Ioi.mem_nhds (by norm_num))).of_le le_top
      have hDc : ContDiffAt ℝ (k' + 1) (DivExtN H 0) 0 :=
        (DivExtN_contDiffOn H hH 0 (k' + 1)).contDiffAt (isOpen_Ioi.mem_nhds (by norm_num))
      have hFA : ∀ w ∈ Set.Ioo (0 : ℝ) 1, (fun w => (w + 1) / w * H w) w = A w := by
        intro w hw
        have hw0 : w ≠ 0 := ne_of_gt hw.1
        have hwIoi : w ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith [hw.1]
        have hdiv := DivExtN_zero_eq_div H hH hH0 hwIoi hw0
        rw [hA]
        simp only []
        rw [hdiv]
        field_simp
      have hAcd : ContDiffAt ℝ (k' + 1) A 0 := by
        rw [hA]
        exact ContDiffAt.add hAc hDc
      rcases iteratedDeriv_jump (ε := 1) (by norm_num) hFA (show 1 ≤ k' + 1 from by omega) hAcd with hJ | hJ
      · rw [hJ]
        simp only [mul_zero, zero_mul, abs_zero]
        linarith
      · rw [hJ]
        have hAeq : iteratedDeriv (k' + 1) A 0
            = iteratedDeriv (k' + 1) H 0 + DivExtN H (k' + 1) 0 := by
          rw [hA]
          rw [show (fun w : ℝ => H w + DivExtN H 0 w) = H + DivExtN H 0 from rfl]
          rw [iteratedDeriv_add hAc hDc]
          rw [show iteratedDeriv (k' + 1) (DivExtN H 0) 0 = DivExtN H (k' + 1) 0 from by
            simpa using (DivExtN_iteratedDeriv H hH (k' + 1) 0)
              (show (0 : ℝ) ∈ Set.Ioi (-1) from by simp)]
        rw [hAeq]
        have hb1'' : |iteratedDeriv (k' + 1) H 0| * W ≤ M := by
          have h := hb1 0 (by simp)
          simpa using h
        have hb2'' : |DivExtN H (k' + 1) 0| * W ≤ M := by
          have hc : |iteratedDeriv (k' + 2) H 0| * W ≤ M := by
            have h := hb2 0 (by simp)
            simpa using h
          have hintegral : DivExtN H (k' + 1) 0
              = ∫ t in (0 : ℝ)..1, t ^ (k' + 1) * iteratedDeriv (k' + 2) H 0 := by
            simp [DivExtN]
          rw [hintegral]
          have hbd : |∫ t in (0 : ℝ)..1, t ^ (k' + 1) * iteratedDeriv (k' + 2) H 0|
              ≤ |iteratedDeriv (k' + 2) H 0| := by
            have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
              (C := |iteratedDeriv (k' + 2) H 0|)
              (f := fun t : ℝ => t ^ (k' + 1) * iteratedDeriv (k' + 2) H 0) (fun t ht => by
                rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
                rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt ht.1) _)]
                calc t ^ (k' + 1) * |iteratedDeriv (k' + 2) H 0|
                    ≤ 1 * |iteratedDeriv (k' + 2) H 0| :=
                      mul_le_mul_of_nonneg_right (pow_le_one₀ (le_of_lt ht.1) ht.2)
                        (abs_nonneg _)
                  _ = |iteratedDeriv (k' + 2) H 0| := one_mul _)
            simpa using h
          exact le_trans (mul_le_mul_of_nonneg_right hbd hW) hc
        calc |(0 + 1) ^ (k' + 1) * (iteratedDeriv (k' + 1) H 0 + DivExtN H (k' + 1) 0) * W|
            = |iteratedDeriv (k' + 1) H 0 * W + DivExtN H (k' + 1) 0 * W| := by
              congr 1
              norm_num
              ring
          _ ≤ |iteratedDeriv (k' + 1) H 0 * W| + |DivExtN H (k' + 1) 0 * W| := abs_add_le _ _
          _ = |iteratedDeriv (k' + 1) H 0| * W + |DivExtN H (k' + 1) 0| * W := by
              rw [abs_mul, abs_mul, abs_of_nonneg hW]
          _ ≤ M + M := add_le_add hb1'' hb2''
          _ = 2 * M := by ring

/-! ## The main theorem -/

/-- `D_θ^j` commutes with multiplication by a function of `z` alone. -/
theorem DthIter_mul_zfun (j : ℕ) (c : ℝ → ℝ) (h : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter j (fun z θ => c z * h z θ)
      = fun z θ => c z * Work.Spaces.DthIter j h z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
    funext z θ
    rw [Work.Spaces.Dth, Work.Spaces.Dth, Work.Spaces.pth, Work.Spaces.pth, deriv_const_mul_field]
    ring

/-- If `f` vanishes on the line `z = 0`, so does every angular iterate `D_θ^j f`. -/
theorem DthIter_apply_zero_z (f : ℝ → ℝ → ℝ) (hf0 : ∀ θ, f 0 θ = 0) (j : ℕ) :
    ∀ θ, Work.Spaces.DthIter j f 0 θ = 0 := by
  induction j with
  | zero => exact hf0
  | succ j ih =>
    intro θ
    rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    have hfun : (fun θ' => Work.Spaces.DthIter j f 0 θ') = fun _ => (0 : ℝ) := funext ih
    rw [hfun, deriv_const, mul_zero]

theorem division_by_z : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.SmoothNbhd f → (∀ θ, f 0 θ = 0) →
    Work.Spaces.WlInfMem α 5 f →
    Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z * f z θ) ∧
      Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z * f z θ)
        ≤ C * Work.Spaces.WlInf α 5 f := by
  refine ⟨100, by norm_num, ?_⟩
  intro α f hα hα1 hsm hf0 hmem
  set g : ℝ → ℝ → ℝ := fun z θ => (z + 1) / z * f z θ with hg
  set W5 : ℝ := Work.Spaces.WlInf α 5 f with hW5
  have hW5nn : 0 ≤ W5 := by
    rw [hW5, Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 5 f hmem)
      (Work.Spaces.wlThSum_nonneg α 5 f hmem)
  have hZ : ∀ k ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k g z θ| ≤ 2 * W5 := by
    intro k hk z hz θ hθ
    have h1 : Work.Spaces.pzIter k g z θ
        = iteratedDeriv k (fun w => (w + 1) / w * f w θ) z := by
      simp only [pzIter_eq_iteratedDeriv, hg]
    rw [h1]
    have hb1 : ∀ u ∈ Set.Ici (0 : ℝ),
        |(u + 1) ^ k * iteratedDeriv k (fun w => f w θ) u| * 1 ≤ W5 := by
      intro u hu
      have h := Work.Spaces.WlInf_z_bound α 5 f hmem k (by omega) u θ hu hθ
      rw [pzIter_eq_iteratedDeriv] at h
      simpa using h
    have hb2 : ∀ u ∈ Set.Ici (0 : ℝ),
        |(u + 1) ^ (k + 1) * iteratedDeriv (k + 1) (fun w => f w θ) u| * 1 ≤ W5 := by
      intro u hu
      have h := Work.Spaces.WlInf_z_bound α 5 f hmem (k + 1) (by omega) u θ hu hθ
      rw [pzIter_eq_iteratedDeriv] at h
      simpa using h
    simpa using slice_div_z k (fun w => f w θ) 1 W5 (by norm_num)
      (contDiffOn_slice_smoothNbhd hsm hθ) (hf0 θ) hb1 hb2 z hz
  have hW : ∀ (j k : ℕ), 1 ≤ j → k + j ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ 2 * W5 := by
    intro j k hj hjk z hz θ hθ
    have hDj : Work.Spaces.DthIter j g
        = fun z θ => (z + 1) / z * Work.Spaces.DthIter j f z θ := by
      simp only [hg]
      exact DthIter_mul_zfun j (fun z => (z + 1) / z) f
    have h1 : Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
        = iteratedDeriv k (fun w => (w + 1) / w * Work.Spaces.DthIter j f w θ) z := by
      simp only [hDj, pzIter_eq_iteratedDeriv]
    rw [h1]
    have hb1 : ∀ u ∈ Set.Ici (0 : ℝ),
        |(u + 1) ^ k * iteratedDeriv k (fun w => Work.Spaces.DthIter j f w θ) u|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ W5 := by
      intro u hu
      have h := Work.Spaces.WlInf_mixed_bound α 5 f hmem j k hj (by omega) u θ hu hθ
      rw [pzIter_eq_iteratedDeriv] at h
      have hs : 0 ≤ Real.sin (2 * θ) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
      have hd : 0 < α + Real.sin (2 * θ) := by linarith
      have habs : |(u + 1) ^ k * iteratedDeriv k (fun w => Work.Spaces.DthIter j f w θ) u
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          = |(u + 1) ^ k * iteratedDeriv k (fun w => Work.Spaces.DthIter j f w θ) u|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
        rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs _), abs_of_pos hd]
        ring
      rw [← habs]
      exact h
    have hb2 : ∀ u ∈ Set.Ici (0 : ℝ),
        |(u + 1) ^ (k + 1) * iteratedDeriv (k + 1) (fun w => Work.Spaces.DthIter j f w θ) u|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ W5 := by
      intro u hu
      have h := Work.Spaces.WlInf_mixed_bound α 5 f hmem j (k + 1) hj (by omega) u θ hu hθ
      rw [pzIter_eq_iteratedDeriv] at h
      have hs : 0 ≤ Real.sin (2 * θ) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
      have hd : 0 < α + Real.sin (2 * θ) := by linarith
      have habs : |(u + 1) ^ (k + 1)
            * iteratedDeriv (k + 1) (fun w => Work.Spaces.DthIter j f w θ) u
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          = |(u + 1) ^ (k + 1) * iteratedDeriv (k + 1) (fun w => Work.Spaces.DthIter j f w θ) u|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
        rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs _), abs_of_pos hd]
        ring
      rw [← habs]
      exact h
    simpa [mul_div_assoc] using slice_div_z k (fun w => Work.Spaces.DthIter j f w θ)
      ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) W5
      (sin_weight_nonneg hα hθ)
      (contDiffOn_slice_smoothNbhd (Work.Spaces.smoothNbhd_DthIter hsm j) hθ)
      (DthIter_apply_zero_z f hf0 j θ) hb1 hb2 z hz
  have hmemg : Work.Spaces.WlInfMem α 4 g := by
    refine ⟨fun k hk => Work.Spaces.supFinite_of_pointwise (hZ k hk), ?_⟩
    intro j hj k hk hj1 hjk
    exact Work.Spaces.supFinite_of_pointwise (hW j k hj1 hjk)
  have hbound : Work.Spaces.WlInf α 4 g ≤ 100 * W5 := by
    have h1 : (∑ k ∈ Finset.range (4 + 1),
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k g z θ)) ≤ 50 * W5 := by
      calc (∑ k ∈ Finset.range (4 + 1),
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k g z θ))
          ≤ ∑ k ∈ Finset.range (4 + 1), (2 * W5) :=
            Finset.sum_le_sum fun k hk =>
              Work.Spaces.supAbs_le (hZ k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
        _ = 5 * (2 * W5) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        _ ≤ 50 * W5 := by linarith
    have h2 : (∑ j ∈ Finset.range (4 + 1), ∑ k ∈ Finset.range (4 + 1),
            if 1 ≤ j ∧ k + j ≤ 4 then
              Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                * Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            else 0) ≤ 50 * W5 := by
      calc (∑ j ∈ Finset.range (4 + 1), ∑ k ∈ Finset.range (4 + 1),
            if 1 ≤ j ∧ k + j ≤ 4 then
              Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                * Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            else 0)
          ≤ ∑ j ∈ Finset.range (4 + 1), ∑ k ∈ Finset.range (4 + 1), (2 * W5) := by
            refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
            by_cases h : 1 ≤ j ∧ k + j ≤ 4
            · rw [if_pos h]
              exact Work.Spaces.supAbs_le (hW j k h.1 h.2)
            · rw [if_neg h]
              linarith
        _ = 25 * (2 * W5) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
              Finset.card_range, nsmul_eq_mul]
            ring
        _ ≤ 50 * W5 := by linarith
    rw [Work.Spaces.WlInf]
    linarith
  exact ⟨hmemg, hbound⟩

end Work.Elliptic
