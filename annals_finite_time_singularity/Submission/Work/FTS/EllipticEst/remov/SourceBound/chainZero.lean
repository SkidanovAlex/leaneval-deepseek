import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false

/-! ## Elementary facts about the angular profile `sinCos2` -/

theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

theorem sinCos2_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  unfold Work.Elliptic.sinCos2
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]))
    (pow_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩) 2)

theorem sinCos2_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    0 < Work.Elliptic.sinCos2 θ := by
  unfold Work.Elliptic.sinCos2
  exact mul_pos (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos]))
    (pow_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩) 2)

theorem sinCos2_zero_left : Work.Elliptic.sinCos2 0 = 0 := by
  simp [Work.Elliptic.sinCos2]

theorem sinCos2_zero_right : Work.Elliptic.sinCos2 (Real.pi / 2) = 0 := by
  simp [Work.Elliptic.sinCos2]

/-! ## Differentiating the partial derivative, and continuity of the slices -/

/-- `∂_z` lowers the order of differentiability by one on an open set. -/
theorem contDiffOn_uncurry_pz_of_isOpen {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {n : ℕ} (h : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry G) U) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz G)) U := by
  have hfd : ContDiffOn ℝ (n : WithTop ℕ∞) (fderiv ℝ (Function.uncurry G)) U :=
    h.fderiv_of_isOpen hU (by simp)
  have hcomp : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p (1, 0)) U :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr ?_
  intro p hp
  exact Work.Spaces.pz_eq_fderiv
    ((h.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp))

/-- A `z`-slice of a function continuous on `U` is continuous. -/
theorem continuousOn_zslice {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hc : ContinuousOn (Function.uncurry G) U) {θ : ℝ} {S : Set ℝ}
    (hS : ∀ r ∈ S, (r, θ) ∈ U) : ContinuousOn (fun r => G r θ) S := by
  have h1 : ContinuousOn (fun r : ℝ => (r, θ)) S := by fun_prop
  have h2 := hc.comp h1 hS
  simpa [Function.comp_def] using h2

/-- A `θ`-slice of a function continuous on `U` is continuous. -/
theorem continuousOn_thslice {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hc : ContinuousOn (Function.uncurry G) U) {x : ℝ} {S : Set ℝ}
    (hS : ∀ θ ∈ S, (x, θ) ∈ U) : ContinuousOn (fun θ => G x θ) S := by
  have h1 : ContinuousOn (fun θ : ℝ => (x, θ)) S := by fun_prop
  have h2 := hc.comp h1 hS
  simpa [Function.comp_def] using h2

/-- A.e. strong measurability on `Iθ` from continuity on the open interval. -/
theorem aesm_of_continuousOn_Ioo {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
  have h1 : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hf.aestronglyMeasurable measurableSet_Ioo
  rwa [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc] at h1

/-- The `z`-slice is differentiable with derivative the partial `∂_z`. -/
theorem hasDerivAt_zslice {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry G) U) {s θ : ℝ}
    (hp : (s, θ) ∈ U) : HasDerivAt (fun r => G r θ) (Work.Spaces.pz G s θ) s := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (s, θ) :=
    (h.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simpa only [Work.Spaces.pz] using (Work.Spaces.differentiableAt_curry_left hd).hasDerivAt

/-- A point of `uIcc s₁ s₂` with `s₁, s₂ > 0` is positive. -/
theorem pos_of_mem_uIcc {x s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (hx : x ∈ Set.uIcc s₁ s₂) : 0 < x := by
  rcases Set.mem_uIcc.mp hx with ⟨ha, _⟩ | ⟨ha, _⟩ <;> linarith

/-- `a ≤ x` for `x ∈ uIcc a b` and `a ≤ b`. -/
theorem a_le_of_mem_uIcc {x a b : ℝ} (hab : a ≤ b) (hx : x ∈ Set.uIcc a b) : a ≤ x := by
  rcases Set.mem_uIcc.mp hx with ⟨ha, _⟩ | ⟨ha, _⟩
  · exact ha
  · linarith

/-! ## The fundamental theorem of calculus along `z`, slice by slice -/

/-- FTC along `z` for the slices of `g`. -/
theorem sliceZ_ftc {g : ℝ → ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    g s₂ θ - g s₁ θ = ∫ r in s₁..s₂, Work.Spaces.pz g r θ := by
  have hU : IsOpen (Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have h1 : ContDiffOn ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hsmooth 1
  have hderiv : ∀ x ∈ Set.uIcc s₁ s₂, HasDerivAt (fun r => g r θ)
      (Work.Spaces.pz g x θ) x := by
    intro x hx
    exact hasDerivAt_zslice hU h1 ⟨pos_of_mem_uIcc h₁ h₂ hx, hθ⟩
  have hcont : ContinuousOn (fun r => Work.Spaces.pz g r θ) (Set.uIcc s₁ s₂) :=
    continuousOn_zslice (contDiffOn_uncurry_pz_of_isOpen hU h1).continuousOn
      (fun r hr => ⟨pos_of_mem_uIcc h₁ h₂ hr, hθ⟩)
  have hint : IntervalIntegrable (fun r => Work.Spaces.pz g r θ) volume s₁ s₂ :=
    hcont.intervalIntegrable
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  linarith [hkey]

/-- FTC along `z` for the slices of `∂_z g`. -/
theorem sliceZ_ftc_pz {g : ℝ → ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    Work.Spaces.pz g s₂ θ - Work.Spaces.pz g s₁ θ
      = ∫ r in s₁..s₂, Work.Spaces.pzIter 2 g r θ := by
  have hU : IsOpen (Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have hpz : ContDiffOn ℝ (1 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_uncurry_pz_of_isOpen hU (n := 1) (hsmooth 2)
  have hpp : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.pzIter 2 g)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h' := contDiffOn_uncurry_pz_of_isOpen hU hpz
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h'
  have hderiv : ∀ x ∈ Set.uIcc s₁ s₂, HasDerivAt (fun r => Work.Spaces.pz g r θ)
      (Work.Spaces.pzIter 2 g x θ) x := by
    intro x hx
    have h' := hasDerivAt_zslice hU hpz (G := Work.Spaces.pz g)
      ⟨pos_of_mem_uIcc h₁ h₂ hx, hθ⟩
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h'
  have hcont : ContinuousOn (fun r => Work.Spaces.pzIter 2 g r θ) (Set.uIcc s₁ s₂) :=
    continuousOn_zslice hpp.continuousOn
      (fun r hr => ⟨pos_of_mem_uIcc h₁ h₂ hr, hθ⟩)
  have hint : IntervalIntegrable (fun r => Work.Spaces.pzIter 2 g r θ) volume s₁ s₂ :=
    hcont.intervalIntegrable
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  linarith [hkey]

/-- A.e. strong measurability of the `θ`-slices of `g` and of `∂_z g`. -/
theorem aesm_slices {g : ℝ → ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {x : ℝ} (hx : 0 < x) :
    (AEStronglyMeasurable (fun θ => g x θ * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    (AEStronglyMeasurable (fun θ => Work.Spaces.pz g x θ * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hU : IsOpen (Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have hcg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hsmooth 0).continuousOn
  have hcpg : ContinuousOn (Function.uncurry (Work.Spaces.pz g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (contDiffOn_uncurry_pz_of_isOpen hU (n := 0) (hsmooth 1)).continuousOn
  constructor
  · exact aesm_of_continuousOn_Ioo
      ((continuousOn_thslice hcg (fun θ hθ => ⟨hx, hθ⟩)).mul continuous_sinCos2.continuousOn)
  · exact aesm_of_continuousOn_Ioo
      ((continuousOn_thslice hcpg (fun θ hθ => ⟨hx, hθ⟩)).mul continuous_sinCos2.continuousOn)

/-- The norm of an interval integral over a subinterval of `[a,b]`. -/
theorem norm_intervalIntegral_le {f : ℝ → ℝ} {z₀ x a b : ℝ}
    (haz : a < z₀) (hzb : z₀ < b) (hax : a < x) (hxb : x < b)
    (hint : IntervalIntegrable (fun r => ‖f r‖) volume a b) :
    ‖∫ r in z₀..x, f r‖ ≤ ∫ r in a..b, ‖f r‖ := by
  rcases le_total z₀ x with h | h
  · exact le_trans (intervalIntegral.norm_integral_le_integral_norm h)
      (intervalIntegral.integral_mono_interval (le_of_lt haz) h (le_of_lt hxb)
        (Filter.Eventually.of_forall fun r => norm_nonneg _) hint)
  · rw [intervalIntegral.integral_symm x z₀, norm_neg]
    exact le_trans (intervalIntegral.norm_integral_le_integral_norm h)
      (intervalIntegral.integral_mono_interval (le_of_lt hax) h (le_of_lt hzb)
        (Filter.Eventually.of_forall fun r => norm_nonneg _) hint)

/-- **The angular-moment chain rule (general form).**

Let `g : ℝ → ℝ → ℝ` be smooth on the open quadrant, `0 < a`, `z₀ ∈ (a,b)`.  Assume
* every slice `θ ↦ g z θ * sinθcos²θ` is integrable on `Iθ` for `z ∈ [a,b]`,
* the slice of `∂_z g` at `z₀` is integrable against `sinθcos²θ` on `Iθ`,
* the second derivative `(z,θ) ↦ ∂_z²g z θ * sinθcos²θ` is integrable on the product of `(a,b]`
  and `Iθ`,
* the moment `Θ(g)(z) = ∫_{Iθ} g z θ * sinθcos²θ dθ` vanishes for every `z ∈ [a,b]`.

Then `Θ(∂_z g)(z) = ∫_{Iθ} ∂_zg z θ * sinθcos²θ dθ = 0` for every `z ∈ (a,b)`.

Proof sketch (differentiation under the integral sign for a totalised integral, valid because all
the slices involved are honest).

1. *FTC in `z`*: for `θ ∈ (0,π/2)` and `s₁,s₂ > 0`, `g s₂ θ - g s₁ θ = ∫ r in s₁..s₂, ∂_z g r θ`,
   because `r ↦ g r θ` is `C¹` on `(0,∞)` (`hsmooth`).
2. *Box integrability of `∂_z g · sinθcos²θ`*: combining step 1 with
   `‖∫ r in z₀..z, ∂_z²g r θ‖ ≤ ∫ r in a..b, ‖∂_z²g r θ‖` and Tonelli (using `hbox2`), the
   function `(z,θ) ↦ ∂_z g z θ * sinθcos²θ` is dominated by an integrable function on
   `(a,b] × Iθ`; a.e. strong measurability is `hsmooth`.
3. *The chain*: for `z ∈ (a,b)`, using `hzero`, `hslice`, step 1 and Fubini
   (`MeasureTheory.intervalIntegral_integral_swap`, valid by step 2),
   `0 = Θ(g)(z) - Θ(g)(z₀) = ∫ r in z₀..z, Θ(∂_z g)(r)`.
4. *Continuity*: step 1 and Tonelli with `hbox2` show that `r ↦ Θ(∂_zg)(r)` is (absolutely)
   continuous on `(a,b)`.
5. Step 3 says the function `z ↦ ∫ r in z₀..z, Θ(∂_zg)(r)` is identically zero on `(a,b)`; by
   step 4 and the FTC its derivative is `Θ(∂_zg)`, which is therefore identically zero on
   `(a,b)`. -/
theorem chainZero {g : ℝ → ℝ → ℝ} {a b z₀ : ℝ} (ha : 0 < a) (hz₀ : z₀ ∈ Set.Ioo a b)
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hslice : ∀ z ∈ Set.Icc a b, MeasureTheory.IntegrableOn
      (fun θ => g z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hslpz : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz g z₀ θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hbox2 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.Spaces.pz (Work.Spaces.pz g) z θ
        * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hzero : ∀ z ∈ Set.Icc a b,
      (∫ θ in Work.Spaces.Iθ, g z θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ z ∈ Set.Ioo a b,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ) = 0 := by
  intro z hz
  have hab : a ≤ b := le_of_lt (lt_trans hz₀.1 hz₀.2)
  have hU : IsOpen (Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have hz0 : 0 < z := lt_trans ha hz.1
  have hz₀0 : 0 < z₀ := lt_trans ha hz₀.1
  -- joint continuity of `∂_z² g` on the open quadrant
  have hcpp : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h' := contDiffOn_uncurry_pz_of_isOpen hU
      (contDiffOn_uncurry_pz_of_isOpen hU (n := 1) (hsmooth 2))
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h'.continuousOn
  -- the dominating function
  set bound : ℝ → ℝ := fun θ => ‖Work.Spaces.pz g z₀ θ * Work.Elliptic.sinCos2 θ‖
      + ∫ s in a..b, ‖Work.Spaces.pzIter 2 g s θ * Work.Elliptic.sinCos2 θ‖ with hbound
  have hbox2' : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.Spaces.pzIter 2 g z θ
        * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hbox2
  have hbound_int : MeasureTheory.Integrable bound
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [hbound]
    refine (hslpz.norm).add ?_
    have hT := hbox2'.integral_norm_prod_right
      (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    refine hT.congr ?_
    filter_upwards with θ
    rw [← intervalIntegral.integral_of_le hab]
    rfl
  -- the pointwise domination
  have h_bound_pt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioo a b,
      ‖Work.Spaces.pz g x θ * Work.Elliptic.sinCos2 θ‖ ≤ bound θ := by
    intro θ hθ x hx
    rw [hbound]
    have hsc : 0 ≤ Work.Elliptic.sinCos2 θ := le_of_lt (sinCos2_pos hθ.1 hθ.2)
    have hx0 : 0 < x := lt_trans ha hx.1
    have hftc := sliceZ_ftc_pz hsmooth hθ hz₀0 hx0
    have hkey : ‖∫ r in z₀..x, Work.Spaces.pzIter 2 g r θ‖
        ≤ ∫ s in a..b, ‖Work.Spaces.pzIter 2 g s θ‖ := by
      have hcont : ContinuousOn (fun r => ‖Work.Spaces.pzIter 2 g r θ‖) (Set.uIcc a b) :=
        (continuousOn_zslice hcpp
          (fun r hr => ⟨lt_of_lt_of_le ha (a_le_of_mem_uIcc hab hr), hθ⟩)).norm
      exact norm_intervalIntegral_le hz₀.1 hz₀.2 hx.1 hx.2 hcont.intervalIntegrable
    have hpx : ‖Work.Spaces.pz g x θ‖
        ≤ ‖Work.Spaces.pz g z₀ θ‖ + ‖∫ r in z₀..x, Work.Spaces.pzIter 2 g r θ‖ := by
      have hsum : Work.Spaces.pz g x θ
          = Work.Spaces.pz g z₀ θ + ∫ r in z₀..x, Work.Spaces.pzIter 2 g r θ := by
        linarith [hftc]
      rw [hsum]
      exact norm_add_le _ _
    have hint_eq : (∫ s in a..b, ‖Work.Spaces.pzIter 2 g s θ * Work.Elliptic.sinCos2 θ‖)
        = (∫ s in a..b, ‖Work.Spaces.pzIter 2 g s θ‖) * Work.Elliptic.sinCos2 θ := by
      rw [← intervalIntegral.integral_mul_const]
      exact intervalIntegral.integral_congr (fun s _ => by
        rw [norm_mul, Real.norm_of_nonneg hsc])
    calc ‖Work.Spaces.pz g x θ * Work.Elliptic.sinCos2 θ‖
        = ‖Work.Spaces.pz g x θ‖ * Work.Elliptic.sinCos2 θ := by
          rw [norm_mul, Real.norm_of_nonneg hsc]
      _ ≤ (‖Work.Spaces.pz g z₀ θ‖ + ∫ s in a..b, ‖Work.Spaces.pzIter 2 g s θ‖)
            * Work.Elliptic.sinCos2 θ := by
          refine mul_le_mul_of_nonneg_right ?_ hsc
          linarith [hpx, hkey]
      _ = ‖Work.Spaces.pz g z₀ θ‖ * Work.Elliptic.sinCos2 θ
            + (∫ s in a..b, ‖Work.Spaces.pzIter 2 g s θ‖) * Work.Elliptic.sinCos2 θ := by
          ring
      _ = ‖Work.Spaces.pz g z₀ θ * Work.Elliptic.sinCos2 θ‖
            + ∫ s in a..b, ‖Work.Spaces.pzIter 2 g s θ * Work.Elliptic.sinCos2 θ‖ := by
          rw [norm_mul, Real.norm_of_nonneg hsc, hint_eq]
  -- measurability hypotheses
  have hF_meas : ∀ᶠ x in 𝓝 z,
      AEStronglyMeasurable (fun θ => g x θ * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with x hx
    exact (aesm_slices hsmooth (lt_trans ha hx.1)).1
  have hF'_meas : AEStronglyMeasurable
      (fun θ => Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (aesm_slices hsmooth hz0).2
  -- the domination hypothesis (a.e. in `θ`; the two endpoints are null)
  have h_bound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ x ∈ Set.Ioo a b, ‖Work.Spaces.pz g x θ * Work.Elliptic.sinCos2 θ‖ ≤ bound θ := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
        ∀ x ∈ Set.Ioo a b, ‖Work.Spaces.pz g x θ * Work.Elliptic.sinCos2 θ‖ ≤ bound θ :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => h_bound_pt θ hθ)
    rwa [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc] at h1
  -- the derivative hypothesis (a.e. in `θ`)
  have h_diff : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ x ∈ Set.Ioo a b,
        HasDerivAt (fun x' => g x' θ * Work.Elliptic.sinCos2 θ)
          (Work.Spaces.pz g x θ * Work.Elliptic.sinCos2 θ) x := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
        ∀ x ∈ Set.Ioo a b,
          HasDerivAt (fun x' => g x' θ * Work.Elliptic.sinCos2 θ)
            (Work.Spaces.pz g x θ * Work.Elliptic.sinCos2 θ) x :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ x hx => by
        have hx0 : 0 < x := lt_trans ha hx.1
        exact (hasDerivAt_zslice hU (n := 0) (hsmooth 1)
          (G := g) (s := x) (θ := θ) ⟨hx0, hθ⟩).mul_const _)
    rwa [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc] at h1
  -- differentiation under the integral sign
  obtain ⟨_, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (F := fun x θ => g x θ * Work.Elliptic.sinCos2 θ)
    (F' := fun x θ => Work.Spaces.pz g x θ * Work.Elliptic.sinCos2 θ)
    (bound := bound) (s := Set.Ioo a b) (x₀ := z)
    (isOpen_Ioo.mem_nhds hz) hF_meas (hslice z ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
    hF'_meas h_bound hbound_int h_diff
  have hzw : (fun x => ∫ θ in Work.Spaces.Iθ, g x θ * Work.Elliptic.sinCos2 θ)
      =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with x hx
    exact hzero x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hder0 : HasDerivAt (fun _ : ℝ => (0 : ℝ))
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ) z :=
    hder.congr_of_eventuallyEq hzw.symm
  exact hder0.unique (hasDerivAt_const z (0 : ℝ))

end Work.FTS.EllipticEst.remov.SourceBound
