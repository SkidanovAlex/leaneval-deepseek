import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst (thEta)

namespace Work.EllipticEst.Core

/-! ## 1. The integrands vanish off the support

`f` vanishes off `Icc a b`; since `Icc a b` is closed, the complement is an open
neighbourhood of every point outside it, so all the derivatives of `f` that occur in the
Agmon inequality vanish there as well. -/

theorem suppDerivZero {f : ℝ → ℝ} {a b : ℝ}
    (hsupp : ∀ θ : ℝ, θ ∉ Set.Icc a b → f θ = 0) :
    ∀ θ : ℝ, θ ∉ Set.Icc a b → f θ = 0 ∧ deriv f θ = 0 ∧ deriv (deriv f) θ = 0 := by
  have hopen : IsOpen (Set.Icc a b)ᶜ := isClosed_Icc.isOpen_compl
  intro θ hθ
  have hnb : (Set.Icc a b)ᶜ ∈ 𝓝 θ := hopen.mem_nhds hθ
  have hf0 : f =ᶠ[𝓝 θ] (fun _ => (0:ℝ)) := by
    filter_upwards [hnb] with y hy
    exact hsupp y hy
  have hdf0 : deriv f =ᶠ[𝓝 θ] (fun _ => (0:ℝ)) := by
    filter_upwards [hnb] with y hy
    have h1 : f =ᶠ[𝓝 y] (fun _ => (0:ℝ)) := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      exact hsupp z hz
    rw [h1.deriv_eq]; simp
  exact ⟨hsupp θ hθ, by rw [hf0.deriv_eq]; simp, by rw [hdf0.deriv_eq]; simp⟩

/-! ## 2. Set integral over `Iθ` versus interval integral over `[a,b]` -/

theorem setIntegral_Iθ_eq_intervalIntegral_of_support {g : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) (hab : a ≤ b)
    (hg : ∀ θ ∈ Work.Spaces.Iθ, θ ∉ Set.Icc a b → g θ = 0) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in a..b, g θ := by
  have h1 : (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in Set.Icc a b, g θ :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
      (fun θ hθ => by
        simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ ⊢
        exact ⟨le_trans ha hθ.1, le_trans hθ.2 hb⟩)
      (fun θ hθ => hg θ hθ.1 hθ.2)
  rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-! ## 3. Vanishing at the endpoints of the support -/

theorem endpointZero {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hb : b < Real.pi / 2) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (Real.pi / 2)))
    (hsupp : ∀ θ : ℝ, θ ∉ Set.Icc a b → f θ = 0) : f a = 0 ∧ f b = 0 := by
  have hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)) := hf.continuousOn
  have hmem : ∀ c : ℝ, 0 < c → c < Real.pi / 2 →
      Set.Icc (0:ℝ) (Real.pi / 2) ∈ 𝓝 c :=
    fun c h1 h2 => Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨h1, h2⟩) Set.Ioo_subset_Icc_self
  have hleft : ∀ c : ℝ, 0 < c → c < Real.pi / 2 → (∀ x : ℝ, x < c → f x = 0) → f c = 0 := by
    intro c h1 h2 hz'
    have hca : ContinuousAt f c := hcont.continuousAt (hmem c h1 h2)
    have hlim1 : Tendsto f (𝓝[Set.Iio c] c) (𝓝 (f c)) := hca.tendsto.mono_left inf_le_left
    have hev : f =ᶠ[𝓝[Set.Iio c] c] (fun _ => (0:ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hz' x hx
    have hlim2 : Tendsto f (𝓝[Set.Iio c] c) (𝓝 (0:ℝ)) :=
      (Filter.tendsto_congr' hev).mpr tendsto_const_nhds
    exact tendsto_nhds_unique' (mem_closure_iff_nhdsWithin_neBot.mp (by simp)) hlim1 hlim2
  have hright : ∀ c : ℝ, 0 < c → c < Real.pi / 2 → (∀ x : ℝ, c < x → f x = 0) → f c = 0 := by
    intro c h1 h2 hz'
    have hca : ContinuousAt f c := hcont.continuousAt (hmem c h1 h2)
    have hlim1 : Tendsto f (𝓝[Set.Ioi c] c) (𝓝 (f c)) := hca.tendsto.mono_left inf_le_left
    have hev : f =ᶠ[𝓝[Set.Ioi c] c] (fun _ => (0:ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hz' x hx
    have hlim2 : Tendsto f (𝓝[Set.Ioi c] c) (𝓝 (0:ℝ)) :=
      (Filter.tendsto_congr' hev).mpr tendsto_const_nhds
    exact tendsto_nhds_unique' (mem_closure_iff_nhdsWithin_neBot.mp (by simp)) hlim1 hlim2
  constructor
  · by_cases hab : a ≤ b
    · exact hleft a ha (lt_of_le_of_lt hab hb)
        (fun x hx => hsupp x (fun h => absurd h.1 (not_le.mpr hx)))
    · exact hsupp a (fun h => hab h.2)
  · by_cases hab : a ≤ b
    · exact hright b (lt_of_lt_of_le ha hab) hb
        (fun x hx => hsupp x (fun h => absurd h.2 (not_le.mpr hx)))
    · exact hsupp b (fun h => hab h.1)

/-! ## 4. `thEta` is `C²` at every point of `[a,b] ⊆ (0,π/2)` -/

theorem contDiffAt_thEta {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) :
    ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 2 thEta x := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have hxp : x < Real.pi / 2 := lt_of_le_of_lt hx.2 hb
  have hsin : Real.sin (2*x) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have h1 : ContDiffAt ℝ 2 (fun θ : ℝ => Real.sin (2*θ)) x := by fun_prop
  exact h1.rpow_const_of_ne hsin

/-! ## 5. The second derivative of the weight `thEta θ = sin(2θ)^{-η}`

On `(0,π/2)` one has `ρ'' = 4η(η+1) sin(2θ)^{-(η+2)} - 4η² ρ`. -/

theorem thEtaDeriv2 {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    deriv (deriv thEta) θ
      = 4 * Work.Spaces.eta * (Work.Spaces.eta + 1)
            * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta + 2))
        - 4 * Work.Spaces.eta ^ 2 * thEta θ := by
  have hs : 0 < Real.sin (2*θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsne : Real.sin (2*θ) ≠ 0 := ne_of_gt hs
  -- `sin (2·) ≠ 0` holds on a neighbourhood of `θ`
  have hnb : {x : ℝ | Real.sin (2*x) ≠ 0} ∈ 𝓝 θ := by
    refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hθ) ?_
    intro x hx
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos]))
  -- the derivative of `sin (2·)`
  have hsin_d : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.sin (2*y)) (2 * Real.cos (2*x)) x := by
    intro x
    have h2 : HasDerivAt (fun y : ℝ => (2:ℝ) * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2:ℝ)
    exact (h2.sin).congr_deriv (by ring)
  have hcos_d : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.cos (2*y)) (-2 * Real.sin (2*x)) x := by
    intro x
    have h2 : HasDerivAt (fun y : ℝ => (2:ℝ) * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2:ℝ)
    exact (h2.cos).congr_deriv (by ring)
  -- the first derivative, as a germ equality
  have hgerm1 : deriv thEta =ᶠ[𝓝 θ]
      (fun x : ℝ => (2 * Real.cos (2*x)) * (-(Work.Spaces.eta))
        * (Real.sin (2*x)) ^ (-(Work.Spaces.eta) - 1)) := by
    filter_upwards [hnb] with x hx
    have hth : HasDerivAt thEta ((2 * Real.cos (2*x)) * (-(Work.Spaces.eta))
        * (Real.sin (2*x)) ^ (-(Work.Spaces.eta) - 1)) x :=
      (hsin_d x).rpow_const (p := -(Work.Spaces.eta)) (Or.inl hx)
    exact hth.deriv
  -- the second derivative of the germ
  have hGd : HasDerivAt (fun x : ℝ => (2 * Real.cos (2*x)) * (-(Work.Spaces.eta))
        * (Real.sin (2*x)) ^ (-(Work.Spaces.eta) - 1))
      ((-2*Work.Spaces.eta) * ((-2 * Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta) - 1)
        + Real.cos (2*θ) * ((2 * Real.cos (2*θ)) * (-(Work.Spaces.eta) - 1)
            * (Real.sin (2*θ)) ^ ((-(Work.Spaces.eta) - 1) - 1)))) θ := by
    have hB : HasDerivAt (fun y : ℝ => (Real.sin (2*y)) ^ (-(Work.Spaces.eta) - 1))
        ((2 * Real.cos (2*θ)) * (-(Work.Spaces.eta) - 1)
          * (Real.sin (2*θ)) ^ ((-(Work.Spaces.eta) - 1) - 1)) θ :=
      (hsin_d θ).rpow_const (p := -(Work.Spaces.eta) - 1) (Or.inl hsne)
    have hraw : HasDerivAt
        (fun y : ℝ => Real.cos (2*y) * (Real.sin (2*y)) ^ (-(Work.Spaces.eta) - 1))
        ((-2 * Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta) - 1)
          + Real.cos (2*θ) * ((2 * Real.cos (2*θ)) * (-(Work.Spaces.eta) - 1)
              * (Real.sin (2*θ)) ^ ((-(Work.Spaces.eta) - 1) - 1))) θ :=
      (hcos_d θ).mul hB
    have hsc := hraw.const_mul (-2*Work.Spaces.eta)
    convert hsc using 1
    funext y; ring
  rw [hgerm1.deriv_eq, hGd.deriv]
  -- the elementary algebra
  have halg : (-2*Work.Spaces.eta)
      * ((-2 * Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta) - 1)
        + Real.cos (2*θ) * ((2 * Real.cos (2*θ)) * (-(Work.Spaces.eta) - 1)
            * (Real.sin (2*θ)) ^ ((-(Work.Spaces.eta) - 1) - 1)))
      = 4 * Work.Spaces.eta * (Work.Spaces.eta + 1)
            * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta + 2))
        - 4 * Work.Spaces.eta ^ 2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) := by
    set s : ℝ := Real.sin (2*θ) with hsd
    set c : ℝ := Real.cos (2*θ) with hcd
    rw [show (-(Work.Spaces.eta) - 1) - 1 = -(Work.Spaces.eta + 2) by ring]
    have hcos2 : c^2 = 1 - s^2 := by
      have h := Real.sin_sq_add_cos_sq (2*θ)
      rw [← hcd, ← hsd] at h
      linarith
    have h1 : s * s ^ (-(Work.Spaces.eta) - 1) = s ^ (-(Work.Spaces.eta)) := by
      nth_rewrite 1 [← Real.rpow_one s]
      rw [← Real.rpow_add hs,
        show (1:ℝ) + (-(Work.Spaces.eta) - 1) = -(Work.Spaces.eta) by ring]
    have h2 : s^2 * s ^ (-(Work.Spaces.eta + 2)) = s ^ (-(Work.Spaces.eta)) := by
      have hcast : s ^ (2:ℝ) = s ^ 2 := Real.rpow_natCast s 2
      nth_rewrite 1 [← hcast]
      rw [← Real.rpow_add hs,
        show (2:ℝ) + (-(Work.Spaces.eta + 2)) = -(Work.Spaces.eta) by ring]
    have hP : (-2*Work.Spaces.eta)
        * ((-2 * s) * s ^ (-(Work.Spaces.eta) - 1)
          + c * ((2 * c) * (-(Work.Spaces.eta) - 1) * s ^ (-(Work.Spaces.eta + 2))))
        = 4 * Work.Spaces.eta * (s * s ^ (-(Work.Spaces.eta) - 1))
          + 4 * Work.Spaces.eta * (Work.Spaces.eta + 1) * c^2
              * s ^ (-(Work.Spaces.eta + 2)) := by
      ring
    rw [hP, h1, hcos2]
    have hQ : 4 * Work.Spaces.eta * s ^ (-(Work.Spaces.eta))
          + 4 * Work.Spaces.eta * (Work.Spaces.eta + 1) * (1 - s^2)
              * s ^ (-(Work.Spaces.eta + 2))
        = 4 * Work.Spaces.eta * s ^ (-(Work.Spaces.eta))
          + 4 * Work.Spaces.eta * (Work.Spaces.eta + 1) * s ^ (-(Work.Spaces.eta + 2))
          - 4 * Work.Spaces.eta * (Work.Spaces.eta + 1)
              * (s^2 * s ^ (-(Work.Spaces.eta + 2))) := by
      ring
    rw [hQ, h2]
    ring
  rw [halg]
  rfl

/-! ## 6. Weighted integration by parts on `[a,b]` -/

theorem weightedIBP {f ρ : ℝ → ℝ} {a b : ℝ} (hab : a < b) (ha : 0 < a) (hb : b < Real.pi/2)
    (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (Real.pi/2)))
    (hfa : f a = 0) (hfb : f b = 0)
    (hρ : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 2 ρ x) :
    (∫ θ in a..b, (deriv f θ)^2 * ρ θ)
      = -(∫ θ in a..b, f θ * deriv (deriv f) θ * ρ θ)
        + (1/2) * (∫ θ in a..b, (f θ)^2 * deriv (deriv ρ) θ) := by
  have habI : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab.le
  have hImem : ∀ x ∈ Set.Icc a b, Set.Icc (0:ℝ) (Real.pi/2) ∈ 𝓝 x := by
    intro x hx
    refine Filter.mem_of_superset
      (isOpen_Ioo.mem_nhds ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩)
      Set.Ioo_subset_Icc_self
  -- differentiability at every point of the closed interval
  have hdf : ∀ x ∈ Set.Icc a b, HasDerivAt f (deriv f x) x := by
    intro x hx
    exact ((hf.contDiffAt (hImem x hx)).differentiableAt (by norm_num)).hasDerivAt
  have hddf : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    intro x hx
    exact (((hf.contDiffAt (hImem x hx)).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hdρ : ∀ x ∈ Set.Icc a b, HasDerivAt ρ (deriv ρ x) x := by
    intro x hx
    exact ((hρ x hx).differentiableAt (by norm_num)).hasDerivAt
  have hddρ : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv ρ) (deriv (deriv ρ) x) x := by
    intro x hx
    exact (((hρ x hx).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  -- continuity on the closed interval
  have hcf : ContinuousOn f (Set.uIcc a b) :=
    hf.continuousOn.mono (fun x hx => by
      rw [habI] at hx
      exact ⟨le_trans ha.le hx.1, le_trans hx.2 hb.le⟩)
  have hcdf : ContinuousOn (fun x => deriv f x) (Set.uIcc a b) := by
    intro x hx
    rw [habI] at hx
    exact ((hf.contDiffAt (hImem x hx)).derivWithin (m := 1)
      (by norm_num)).continuousAt.continuousWithinAt
  have hcddf : ContinuousOn (fun x => deriv (deriv f) x) (Set.uIcc a b) := by
    intro x hx
    rw [habI] at hx
    have h1 : ContDiffAt ℝ 1 (deriv f) x :=
      (hf.contDiffAt (hImem x hx)).derivWithin (m := 1) (by norm_num)
    exact ((h1.derivWithin (m := 0) (by norm_num)).continuousAt).continuousWithinAt
  have hcρ : ContinuousOn ρ (Set.uIcc a b) := by
    intro x hx
    rw [habI] at hx
    exact (hρ x hx).continuousAt.continuousWithinAt
  have hcdρ : ContinuousOn (fun x => deriv ρ x) (Set.uIcc a b) := by
    intro x hx
    rw [habI] at hx
    exact ((hρ x hx).derivWithin (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have hcddρ : ContinuousOn (fun x => deriv (deriv ρ) x) (Set.uIcc a b) := by
    intro x hx
    rw [habI] at hx
    have h1 : ContDiffAt ℝ 1 (deriv ρ) x := (hρ x hx).derivWithin (m := 1) (by norm_num)
    exact ((h1.derivWithin (m := 0) (by norm_num)).continuousAt).continuousWithinAt
  -- the three integrands of the first application
  have hintA : IntervalIntegrable (fun x => (deriv f x)^2 * ρ x) volume a b :=
    ((hcdf.pow 2).mul hcρ).intervalIntegrable
  have hintB : IntervalIntegrable (fun x => f x * deriv (deriv f) x * ρ x) volume a b :=
    ((hcf.mul hcddf).mul hcρ).intervalIntegrable
  have hintC : IntervalIntegrable (fun x => f x * deriv f x * deriv ρ x) volume a b :=
    ((hcf.mul hcdf).mul hcdρ).intervalIntegrable
  -- first IBP:  ∫ (f')²ρ + ∫ f f'' ρ + ∫ f f' ρ' = 0
  have hF1 : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y => f y * deriv f y * ρ y)
      ((deriv f x)^2 * ρ x + f x * deriv (deriv f) x * ρ x + f x * deriv f x * deriv ρ x) x := by
    intro x hx
    rw [habI] at hx
    have h2 : HasDerivAt (fun y => f y * deriv f y * ρ y)
        ((deriv f x * deriv f x + f x * deriv (deriv f) x) * ρ x
          + (f x * deriv f x) * deriv ρ x) x :=
      ((hdf x hx).mul (hddf x hx)).mul (hdρ x hx)
    exact h2.congr_deriv (by ring)
  have hintF1 : IntervalIntegrable
      (fun x => (deriv f x)^2 * ρ x + f x * deriv (deriv f) x * ρ x
        + f x * deriv f x * deriv ρ x) volume a b := (hintA.add hintB).add hintC
  have hFTC1 : (∫ x in a..b, (deriv f x)^2 * ρ x + f x * deriv (deriv f) x * ρ x
        + f x * deriv f x * deriv ρ x) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hF1 hintF1
    simpa [hfa, hfb] using h
  have hPQR : (∫ x in a..b, (deriv f x)^2 * ρ x) + (∫ x in a..b, f x * deriv (deriv f) x * ρ x)
      + (∫ x in a..b, f x * deriv f x * deriv ρ x) = 0 := by
    rw [← intervalIntegral.integral_add hintA hintB,
      ← intervalIntegral.integral_add (hintA.add hintB) hintC]
    exact hFTC1
  -- second IBP:  ∫ f² ρ'' = - 2 ∫ f f' ρ'
  have hF3 : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y => (f y)^2) (2 * f x * deriv f x) x := by
    intro x hx
    rw [habI] at hx
    have h2 : HasDerivAt (fun y => f y * f y) (2 * f x * deriv f x) x :=
      ((hdf x hx).mul (hdf x hx)).congr_deriv (by ring)
    rw [show (fun y : ℝ => f y * f y) = (fun y : ℝ => f y ^ 2) from
      funext fun y => by ring] at h2
    exact h2
  have hintF3u : IntervalIntegrable (fun x => 2 * f x * deriv f x) volume a b :=
    ((continuousOn_const.mul hcf).mul hcdf).intervalIntegrable
  have hFTC3 : (∫ x in a..b, (f x)^2 * deriv (deriv ρ) x)
      = - (∫ x in a..b, (2 * f x * deriv f x) * deriv ρ x) := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun x => (f x)^2) (v := fun x => deriv ρ x)
      (u' := fun x => 2 * f x * deriv f x) (v' := fun x => deriv (deriv ρ) x)
      (fun x hx => hF3 x hx)
      (fun x hx => hddρ x (by rw [habI] at hx; exact hx))
      hintF3u hcddρ.intervalIntegrable
    simpa [hfa, hfb] using h
  have hR3 : (∫ x in a..b, (2 * f x * deriv f x) * deriv ρ x)
      = 2 * (∫ x in a..b, f x * deriv f x * deriv ρ x) := by
    have hpt : ∀ x ∈ Set.uIcc a b,
        (2 * f x * deriv f x) * deriv ρ x = 2 * (f x * deriv f x * deriv ρ x) := by
      intro x hx; ring
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
  -- combine
  have hSR : (∫ x in a..b, (f x)^2 * deriv (deriv ρ) x)
      = - 2 * (∫ x in a..b, f x * deriv f x * deriv ρ x) := by
    rw [hFTC3, hR3]; ring
  linarith [hPQR, hSR]

/-! ## 7. The integral of `f² ρ''` -/

theorem integral_f_sq_deriv2_thEta {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hb : b < Real.pi/2) (hf : ContinuousOn f (Set.Icc a b)) :
    (∫ θ in a..b, (f θ)^2 * deriv (deriv thEta) θ)
      = 4 * Work.Spaces.eta * (Work.Spaces.eta + 1)
          * (∫ θ in a..b, (f θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta + 2)))
        - 4 * Work.Spaces.eta ^ 2
          * (∫ θ in a..b, (f θ)^2 * thEta θ) := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hspos : ∀ θ ∈ Set.uIcc a b, 0 < Real.sin (2*θ) := by
    intro θ hθ
    rw [huIcc] at hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [ha, hθ.1])
      (by linarith [hθ.2, hb, Real.pi_pos])
  have hcs : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.uIcc a b) :=
    Real.continuous_sin.comp_continuousOn (continuous_const.mul continuous_id).continuousOn
  have hcs2 : ContinuousOn (fun θ : ℝ => (Real.sin (2*θ)) ^ (-(Work.Spaces.eta + 2)))
      (Set.uIcc a b) :=
    hcs.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hspos θ hθ)))
  have hcth : ContinuousOn thEta (Set.uIcc a b) :=
    hcs.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hspos θ hθ)))
  have hcf2 : ContinuousOn (fun θ : ℝ => (f θ)^2) (Set.uIcc a b) :=
    (hf.mono (by rw [huIcc])).pow 2
  have hintA : IntervalIntegrable
      (fun θ : ℝ => 4 * Work.Spaces.eta * (Work.Spaces.eta + 1)
        * ((f θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta + 2)))) volume a b :=
    (continuousOn_const.mul (hcf2.mul hcs2)).intervalIntegrable
  have hintB : IntervalIntegrable
      (fun θ : ℝ => 4 * Work.Spaces.eta ^ 2 * ((f θ)^2 * thEta θ)) volume a b :=
    (continuousOn_const.mul (hcf2.mul hcth)).intervalIntegrable
  have hpt : ∀ θ ∈ Set.uIcc a b,
      (f θ)^2 * deriv (deriv thEta) θ
        = 4 * Work.Spaces.eta * (Work.Spaces.eta + 1)
            * ((f θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta + 2)))
          - 4 * Work.Spaces.eta ^ 2 * ((f θ)^2 * thEta θ) := by
    intro θ hθ
    rw [huIcc] at hθ
    have hθ' : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) :=
      ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
    rw [thEtaDeriv2 hθ']
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub hintA hintB,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-! ## 8. The angular Agmon inequality -/

theorem thetaAgmonCompact : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℝ → ℝ) (a b : ℝ), 0 < a → b < Real.pi / 2 →
      ContDiffOn ℝ 2 f (Set.Icc 0 (Real.pi / 2)) →
      (∀ θ : ℝ, θ ∉ Set.Icc a b → f θ = 0) →
      (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
          * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ
              * Work.FTS.EllipticEst.thEta θ)
          + C * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  have hη0 : 0 ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  have hη1 : Work.Spaces.eta < 1 := by norm_num [Work.Spaces.eta]
  obtain ⟨C0, hC0pos, hHardy⟩ :=
    Work.FTS.EllipticEst.hardy_shift_two_same_weight Work.Spaces.eta hη0 hη1
  refine ⟨max (2 * Work.Spaces.eta * (Work.Spaces.eta + 1) * C0 - 2 * Work.Spaces.eta ^ 2) 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro f a b ha hb hf hsupp
  rcases lt_or_ge a b with hab | hba
  · -- the support `[a,b]` is non-degenerate
    have hfaa : f a = 0 := (endpointZero ha hb hf hsupp).1
    have hfbb : f b = 0 := (endpointZero ha hb hf hsupp).2
    have hz := suppDerivZero hsupp
    -- the five relevant numbers
    set P : ℝ := ∫ θ in a..b, (deriv f θ)^2 * thEta θ with hP
    set Q : ℝ := ∫ θ in a..b, f θ * deriv (deriv f) θ * thEta θ with hQ
    set N : ℝ := ∫ θ in a..b, (f θ)^2 * thEta θ with hN
    set Hq : ℝ := ∫ θ in a..b, (f θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta + 2)) with hHq
    set Rq : ℝ := ∫ θ in a..b, (f θ)^2 * deriv (deriv thEta) θ with hRq
    -- the transfers from `Iθ` to `[a,b]`
    have trLI : (∫ θ in Work.Spaces.Iθ, (deriv f θ)^2 * thEta θ) = P := by
      rw [hP]
      exact setIntegral_Iθ_eq_intervalIntegral_of_support ha.le hb.le hab.le (fun θ _ hθ => by
        obtain ⟨-, h2, -⟩ := hz θ hθ
        rw [h2]; ring)
    have trMI : (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * thEta θ) = Q := by
      rw [hQ]
      exact setIntegral_Iθ_eq_intervalIntegral_of_support ha.le hb.le hab.le (fun θ _ hθ => by
        obtain ⟨h1, -, -⟩ := hz θ hθ
        rw [h1]; ring)
    have trNI : (∫ θ in Work.Spaces.Iθ, (f θ)^2 * thEta θ) = N := by
      rw [hN]
      exact setIntegral_Iθ_eq_intervalIntegral_of_support ha.le hb.le hab.le (fun θ _ hθ => by
        obtain ⟨h1, -, -⟩ := hz θ hθ
        rw [h1]; ring)
    -- the integration by parts
    have hIBP : P = -Q + (1/2) * Rq := by
      rw [hP, hQ, hRq]
      exact weightedIBP hab ha hb hf hfaa hfbb (contDiffAt_thEta ha hb)
    have hRthEta : Rq = 4 * Work.Spaces.eta * (Work.Spaces.eta + 1) * Hq
        - 4 * Work.Spaces.eta ^ 2 * N := by
      rw [hRq, hHq, hN]
      exact integral_f_sq_deriv2_thEta hab.le ha hb
        (hf.continuousOn.mono (fun x hx => ⟨le_trans ha.le hx.1, le_trans hx.2 hb.le⟩))
    -- the Hardy inequality, transferred to `[a,b]`
    have hf0 : f 0 = 0 := hsupp 0 (fun h => absurd h.1 (not_le.mpr ha))
    have hfp : f (Real.pi / 2) = 0 := hsupp (Real.pi / 2) (fun h => absurd h.2 (not_le.mpr hb))
    have hHardy0 := hHardy f (hf.of_le (by norm_num)) hf0 hfp
    have hspos : ∀ θ ∈ Set.Icc a b, 0 < Real.sin (2*θ) := by
      intro θ hθ
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [ha, hθ.1])
        (by linarith [hθ.2, hb, Real.pi_pos])
    have tH1 : (∫ θ in Work.Spaces.Iθ, f θ ^ 2 / (Real.sin (2*θ)) ^ (2 + Work.Spaces.eta))
        = ∫ θ in a..b, f θ ^ 2 / (Real.sin (2*θ)) ^ (2 + Work.Spaces.eta) :=
      setIntegral_Iθ_eq_intervalIntegral_of_support ha.le hb.le hab.le (fun θ _ hθ => by
        rw [hsupp θ hθ]; simp)
    have tL1 : (∫ θ in Work.Spaces.Iθ, (deriv f θ)^2 / (Real.sin (2*θ)) ^ Work.Spaces.eta)
        = ∫ θ in a..b, (deriv f θ)^2 / (Real.sin (2*θ)) ^ Work.Spaces.eta :=
      setIntegral_Iθ_eq_intervalIntegral_of_support ha.le hb.le hab.le (fun θ _ hθ => by
        obtain ⟨-, h2, -⟩ := hz θ hθ
        rw [h2]; simp)
    have tN1 : (∫ θ in Work.Spaces.Iθ, f θ ^ 2 / (Real.sin (2*θ)) ^ Work.Spaces.eta)
        = ∫ θ in a..b, f θ ^ 2 / (Real.sin (2*θ)) ^ Work.Spaces.eta :=
      setIntegral_Iθ_eq_intervalIntegral_of_support ha.le hb.le hab.le (fun θ _ hθ => by
        rw [hsupp θ hθ]; simp)
    have cH : (∫ θ in a..b, f θ ^ 2 / (Real.sin (2*θ)) ^ (2 + Work.Spaces.eta))
        = ∫ θ in a..b, f θ ^ 2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta + 2)) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le hab.le] at hθ
      have hs := hspos θ hθ
      show f θ ^ 2 / (Real.sin (2*θ)) ^ (2 + Work.Spaces.eta)
          = f θ ^ 2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta + 2))
      rw [div_eq_mul_inv, show -(Work.Spaces.eta + 2) = -(2 + Work.Spaces.eta) by ring,
        Real.rpow_neg (le_of_lt hs)]
    have cL : (∫ θ in a..b, (deriv f θ)^2 / (Real.sin (2*θ)) ^ Work.Spaces.eta)
        = ∫ θ in a..b, (deriv f θ)^2 * thEta θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le hab.le] at hθ
      have hs := hspos θ hθ
      show (deriv f θ)^2 / (Real.sin (2*θ)) ^ Work.Spaces.eta
          = (deriv f θ)^2 * thEta θ
      rw [div_eq_mul_inv, thEta, Real.rpow_neg (le_of_lt hs)]
    have cN : (∫ θ in a..b, f θ ^ 2 / (Real.sin (2*θ)) ^ Work.Spaces.eta)
        = ∫ θ in a..b, f θ ^ 2 * thEta θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le hab.le] at hθ
      have hs := hspos θ hθ
      show f θ ^ 2 / (Real.sin (2*θ)) ^ Work.Spaces.eta
          = f θ ^ 2 * thEta θ
      rw [div_eq_mul_inv, thEta, Real.rpow_neg (le_of_lt hs)]
    have hHi : Hq ≤ 1 / (Work.Spaces.eta + 1) ^ 2 * P + C0 * N := by
      rw [hHq, hP, hN]
      calc (∫ θ in a..b, (f θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta + 2)))
          = ∫ θ in a..b, f θ ^ 2 / (Real.sin (2*θ)) ^ (2 + Work.Spaces.eta) := cH.symm
        _ = ∫ θ in Work.Spaces.Iθ, f θ ^ 2 / (Real.sin (2*θ)) ^ (2 + Work.Spaces.eta) :=
              tH1.symm
        _ ≤ 1 / (Work.Spaces.eta + 1) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (deriv f θ)^2 / (Real.sin (2*θ)) ^ Work.Spaces.eta)
            + C0 * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 / (Real.sin (2*θ)) ^ Work.Spaces.eta) :=
              hHardy0
        _ = 1 / (Work.Spaces.eta + 1) ^ 2
              * (∫ θ in a..b, (deriv f θ)^2 / (Real.sin (2*θ)) ^ Work.Spaces.eta)
            + C0 * (∫ θ in a..b, f θ ^ 2 / (Real.sin (2*θ)) ^ Work.Spaces.eta) := by
              rw [tL1, tN1]
        _ = 1 / (Work.Spaces.eta + 1) ^ 2 * (∫ θ in a..b, (deriv f θ)^2 * thEta θ)
            + C0 * (∫ θ in a..b, f θ ^ 2 * thEta θ) := by rw [cL, cN]
    -- nonnegativity of `N`
    have hNnn : 0 ≤ N := by
      rw [hN]
      refine intervalIntegral.integral_nonneg hab.le (fun θ hθ => ?_)
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg (by
        simp only [Work.Spaces.Iθ, Set.mem_Icc]
        exact ⟨le_trans ha.le hθ.1, le_trans hθ.2 hb.le⟩))
    -- the final combination
    have hcoef : 2 * Work.Spaces.eta * (Work.Spaces.eta + 1)
        * (1 / (Work.Spaces.eta + 1) ^ 2) = 2 * Work.Spaces.eta / (1 + Work.Spaces.eta) := by
      have h1 : (1:ℝ) + Work.Spaces.eta ≠ 0 := by positivity
      field_simp; ring
    have hHm : (2 * Work.Spaces.eta * (Work.Spaces.eta + 1)) * Hq
        ≤ (2 * Work.Spaces.eta * (Work.Spaces.eta + 1))
            * (1 / (Work.Spaces.eta + 1) ^ 2 * P + C0 * N) :=
      mul_le_mul_of_nonneg_left hHi (by positivity)
    have hHm' : (2 * Work.Spaces.eta * (Work.Spaces.eta + 1))
          * (1 / (Work.Spaces.eta + 1) ^ 2 * P + C0 * N)
        = (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * P
          + (2 * Work.Spaces.eta * (Work.Spaces.eta + 1) * C0) * N := by
      have h2 : (2 * Work.Spaces.eta * (Work.Spaces.eta + 1))
          * (1 / (Work.Spaces.eta + 1) ^ 2 * P)
          = (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * P := by
        rw [← mul_assoc, hcoef]
      rw [mul_add, h2]; ring
    have hCmax : 2 * Work.Spaces.eta * (Work.Spaces.eta + 1) * C0 - 2 * Work.Spaces.eta ^ 2
        ≤ max (2 * Work.Spaces.eta * (Work.Spaces.eta + 1) * C0 - 2 * Work.Spaces.eta ^ 2) 1 :=
      le_max_left _ _
    have hCN : (2 * Work.Spaces.eta * (Work.Spaces.eta + 1) * C0 - 2 * Work.Spaces.eta ^ 2) * N
        ≤ max (2 * Work.Spaces.eta * (Work.Spaces.eta + 1) * C0 - 2 * Work.Spaces.eta ^ 2) 1
            * N :=
      mul_le_mul_of_nonneg_right hCmax hNnn
    have hid : 1 - 2 * Work.Spaces.eta / (1 + Work.Spaces.eta)
        = (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta) := by
      have h1 : (1:ℝ) + Work.Spaces.eta ≠ 0 := by positivity
      field_simp; ring
    have hidL : (1 - 2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * P
        = (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta) * P := by rw [hid]
    have hmain : (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta) * P
        ≤ -Q + (max (2 * Work.Spaces.eta * (Work.Spaces.eta + 1) * C0
              - 2 * Work.Spaces.eta ^ 2) 1) * N := by
      linarith [hIBP, hRthEta, hHm, hHm', hCN, hidL]
    rw [trLI, trMI, trNI]
    exact hmain
  · -- the support is degenerate: `f` vanishes identically
    have hfzero : f = fun _ => (0:ℝ) := by
      funext θ
      by_cases hθ : θ ∈ Set.Icc a b
      · have hθa : θ = a := le_antisymm (le_trans hθ.2 hba) hθ.1
        rw [hθa]
        exact (endpointZero ha hb hf hsupp).1
      · exact hsupp θ hθ
    rw [hfzero]
    simp

end Work.EllipticEst.Core
