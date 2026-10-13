import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.STBounds2
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.EllSol.WeakSlice.sliceV_DzIter_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The angular trace at `θ = π/4`

The level-six transport estimates need the *angular* trace of a weighted `D_z`-iterate at the
fixed angle `θ = π/4`.  Because `sin(2θ) = 1` there, the two angular weights
`sin(2θ)^{-η/2}` and `sin(2θ)^{-γ/2}` of the `ℋ⁶`-integrand are *bounded below* by `1` near
`π/4` (and above by an absolute constant), so — in contrast with the uniform-in-`θ`
Agmon/`SliceSupOpen` bounds, which lose a factor `1/α` — the trace estimate is *α-uniform*.

The route is the classical one-dimensional Morrey inequality on a fixed subinterval
`J = [π/8, 3π/8] ∋ π/4` on which `sin(2θ) ≥ 1/2`:
`h(π/4)² ≤ (2/|J|)∫_J h² + 2|J|∫_J (h')²`, applied to the angular slice
`h = fun θ => D_z^j g z θ`, followed by the pointwise slot comparisons
`w(z)²(D_z^j g)² ≤ HkIntegrand` and `w(z)²(∂_θD_z^j g)² ≤ 4·HkIntegrand`
(the latter through `∂_θ D_z^j g = mixed j 1 g / sin(2θ)`). -/

/-- **One-dimensional trace (Morrey) inequality.**  For `a < x₀ < b` and `h` of class
`C¹` on `[a,b]` (with `deriv h` continuous there), the value of `h` at the interior point
`x₀` is controlled by the `L²`-norms of `h` and of `deriv h` on `[a,b]`:
`h(x₀)² ≤ (2/(b-a))∫ h² + 2(b-a)∫ (h')²`. -/
theorem trace_morrey {h : ℝ → ℝ} {a x₀ b : ℝ} (hax : a < x₀) (hxb : x₀ < b)
    (hcont : ContinuousOn h (Set.Icc a b))
    (hdc : ContinuousOn (deriv h) (Set.Icc a b))
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt h (deriv h x) x) :
    (h x₀) ^ 2 ≤ (2 / (b - a)) * (∫ x in Set.Icc a b, (h x) ^ 2)
      + 2 * (b - a) * (∫ x in Set.Icc a b, (deriv h x) ^ 2) := by
  have hab : a < b := lt_trans hax hxb
  have hbma : 0 < b - a := by linarith
  have hInt1 : IntegrableOn (fun x => |deriv h x|) (Set.Icc a b) :=
    hdc.abs.integrableOn_compact isCompact_Icc
  have hInt0 : IntegrableOn (fun x => (h x) ^ 2) (Set.Icc a b) :=
    (hcont.pow 2).integrableOn_compact isCompact_Icc
  have hInt2 : IntegrableOn (fun x => (deriv h x) ^ 2) (Set.Icc a b) :=
    (hdc.pow 2).integrableOn_compact isCompact_Icc
  have hvol_ne : (volume : Measure ℝ) (Set.Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  set S : ℝ := ∫ x in Set.Icc a b, |deriv h x| with hSdef
  -- the difference `h x₀ - h y` is bounded by the `L¹`-norm of `h'`
  have hdiff : ∀ y ∈ Set.Icc a b, (h x₀ - h y) ^ 2 ≤ S ^ 2 := by
    intro y hy
    have hyb : y ≤ b := hy.2
    have hay : a ≤ y := hy.1
    have hsub : Set.Ioc (min y x₀) (max y x₀) ⊆ Set.Icc a b := by
      intro x hx
      rw [Set.mem_Ioc] at hx
      have h1 : a ≤ min y x₀ := le_min hay hax.le
      have h2 : max y x₀ ≤ b := max_le hyb hxb.le
      exact ⟨le_of_lt (lt_of_le_of_lt h1 hx.1), le_trans hx.2 h2⟩
    have hmono : (∫ x in Set.Ioc (min y x₀) (max y x₀), |deriv h x|) ≤ S := by
      rw [hSdef]
      refine MeasureTheory.setIntegral_mono_set hInt1 ?_ ?_
      · exact Eventually.of_forall (fun x => abs_nonneg (deriv h x))
      · exact Eventually.of_forall (fun x hx => hsub hx)
    have key : |h x₀ - h y| ≤ ∫ x in Set.Ioc (min y x₀) (max y x₀), |deriv h x| := by
      rcases le_total y x₀ with hyx | hxy
      · -- `y ≤ x₀`: fundamental theorem of calculus on `[y,x₀]`
        have hFTC : ∫ x in y..x₀, deriv h x = h x₀ - h y := by
          refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hyx ?_ ?_ ?_
          · exact hcont.mono (Set.Icc_subset_Icc hay (le_of_lt hxb))
          · intro x hx
            exact hd x ⟨lt_of_le_of_lt hay hx.1, lt_of_lt_of_le hx.2 (le_of_lt hxb)⟩
          · refine ContinuousOn.intervalIntegrable (a := y) (b := x₀) ?_
            rw [Set.uIcc_of_le hyx]
            exact hdc.mono (Set.Icc_subset_Icc hay (le_of_lt hxb))
        have hset : Set.Ioc (min y x₀) (max y x₀) = Set.Ioc y x₀ := by
          rw [min_eq_left hyx, max_eq_right hyx]
        rw [hset, ← hFTC, intervalIntegral.integral_of_le hyx]
        exact MeasureTheory.abs_integral_le_integral_abs
      · -- `x₀ ≤ y`: the same on `[x₀,y]`
        have hFTC : ∫ x in x₀..y, deriv h x = h y - h x₀ := by
          refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy ?_ ?_ ?_
          · exact hcont.mono (Set.Icc_subset_Icc (le_of_lt hax) hyb)
          · intro x hx
            exact hd x ⟨lt_trans hax hx.1, lt_of_lt_of_le hx.2 hyb⟩
          · refine ContinuousOn.intervalIntegrable (a := x₀) (b := y) ?_
            rw [Set.uIcc_of_le hxy]
            exact hdc.mono (Set.Icc_subset_Icc (le_of_lt hax) hyb)
        have hset : Set.Ioc (min y x₀) (max y x₀) = Set.Ioc x₀ y := by
          rw [min_eq_right hxy, max_eq_left hxy]
        have hneg : h x₀ - h y = -(∫ x in x₀..y, deriv h x) := by rw [hFTC]; ring
        rw [hset, hneg, abs_neg, intervalIntegral.integral_of_le hxy]
        exact MeasureTheory.abs_integral_le_integral_abs
    have h2 : |h x₀ - h y| ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (le_trans key hmono) 2
    rwa [sq_abs] at h2
  -- pointwise: `h x₀² ≤ 2 h y² + 2 S²`
  have hpoint : ∀ y ∈ Set.Icc a b, (h x₀) ^ 2 ≤ 2 * (h y) ^ 2 + 2 * S ^ 2 := by
    intro y hy
    have h1 := hdiff y hy
    nlinarith [h1, sq_nonneg (h x₀ - 2 * h y)]
  have hIntRhs : IntegrableOn (fun y => 2 * (h y) ^ 2 + 2 * S ^ 2) (Set.Icc a b) :=
    (hInt0.const_mul 2).add (integrableOn_const (C := 2 * S ^ 2) hvol_ne)
  -- average the pointwise inequality over `y ∈ [a,b]`
  have hmono2 : (∫ y in Set.Icc a b, (h x₀) ^ 2)
      ≤ ∫ y in Set.Icc a b, (2 * (h y) ^ 2 + 2 * S ^ 2) :=
    MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun y => sq_nonneg _)) hIntRhs
      (ae_restrict_of_forall_mem measurableSet_Icc hpoint)
  have hL : (∫ y in Set.Icc a b, (h x₀) ^ 2) = (b - a) * (h x₀) ^ 2 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a), smul_eq_mul]
  have hR : (∫ y in Set.Icc a b, (2 * (h y) ^ 2 + 2 * S ^ 2))
      = 2 * (∫ y in Set.Icc a b, (h y) ^ 2) + 2 * (b - a) * S ^ 2 := by
    rw [MeasureTheory.integral_add (hInt0.const_mul 2) (integrableOn_const (C := 2 * S ^ 2) hvol_ne),
      MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a), smul_eq_mul]
    ring
  -- Cauchy–Schwarz: `S² ≤ (b-a) ∫ (h')²`
  have hCS : S ^ 2 ≤ (b - a) * (∫ x in Set.Icc a b, (deriv h x) ^ 2) := by
    have hmem1 : MemLp (fun _ : ℝ => (1:ℝ)) 2 (volume.restrict (Set.Icc a b)) := memLp_const 1
    have hmem0 : MemLp (deriv h) 2 (volume.restrict (Set.Icc a b)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq
        (measurable_deriv h).aestronglyMeasurable).mpr hInt2
    have hmem2 : MemLp (fun x => |deriv h x|) 2 (volume.restrict (Set.Icc a b)) := by
      simpa using hmem0.norm
    have hcs := Work.Spaces.cs_integral hmem1 hmem2
    have h1 : (∫ x in Set.Icc a b, (1:ℝ) * |deriv h x|) = S := by
      rw [hSdef]
      exact MeasureTheory.integral_congr_ae (Eventually.of_forall (fun x => by simp))
    have h2 : (∫ x in Set.Icc a b, (1:ℝ) ^ 2) = b - a := by
      rw [one_pow, MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a), smul_eq_mul, mul_one]
    have h3 : (∫ x in Set.Icc a b, |deriv h x| ^ 2)
        = ∫ x in Set.Icc a b, (deriv h x) ^ 2 :=
      MeasureTheory.integral_congr_ae (Eventually.of_forall (fun x => by simp [sq_abs]))
    rw [h1, h2, h3] at hcs
    exact hcs
  have hmain : (b - a) * (h x₀) ^ 2
      ≤ 2 * (∫ y in Set.Icc a b, (h y) ^ 2) + 2 * (b - a) * S ^ 2 := by
    rw [← hL, ← hR]
    exact hmono2
  have hfin : (b - a) * (h x₀) ^ 2
      ≤ (b - a) * ((2 / (b - a)) * (∫ x in Set.Icc a b, (h x) ^ 2)
          + 2 * (b - a) * (∫ x in Set.Icc a b, (deriv h x) ^ 2)) := by
    have hX : 2 * (b - a) * S ^ 2
        ≤ 2 * (b - a) * ((b - a) * (∫ x in Set.Icc a b, (deriv h x) ^ 2)) :=
      mul_le_mul_of_nonneg_left hCS (by linarith)
    calc (b - a) * (h x₀) ^ 2
        ≤ 2 * (∫ x in Set.Icc a b, (h x) ^ 2) + 2 * (b - a) * S ^ 2 := hmain
      _ ≤ 2 * (∫ x in Set.Icc a b, (h x) ^ 2)
            + 2 * (b - a) * ((b - a) * (∫ x in Set.Icc a b, (deriv h x) ^ 2)) := by linarith [hX]
      _ = (b - a) * ((2 / (b - a)) * (∫ x in Set.Icc a b, (h x) ^ 2)
          + 2 * (b - a) * (∫ x in Set.Icc a b, (deriv h x) ^ 2)) := by
        field_simp
  exact le_of_mul_le_mul_left hfin hbma

/-! ## The two pointwise slot comparisons -/

/-- The radial weight is nonnegative. -/
theorem w_nonneg_pi4 (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

/-- A weighted pure `D_z`-slot is dominated pointwise by the `ℋ^k`-integrand. -/
theorem wsq_dzIter_le_HkIntegrand_pi4 {α : ℝ} {g : ℝ → ℝ → ℝ} {j k : ℕ} (hjk : j ≤ k)
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hsinθ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsinθ _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hsinθ.le (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hL : Work.Spaces.w z ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hspos]
    nlinarith [w_nonneg_pi4 z, hsle]
  calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2
      = (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    _ ≤ (Work.Spaces.DzIter j g z θ) ^ 2
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (w_nonneg_pi4 z) hL 2) (sq_nonneg _)
    _ = (Work.Spaces.DzIter j g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α k g z θ j hjk

/-- A weighted mixed slot is dominated pointwise by the `ℋ^k`-integrand. -/
theorem wsq_mixed_le_HkIntegrand_pi4 {α : ℝ} (hα : 0 ≤ α) {g : ℝ → ℝ → ℝ} {i j k : ℕ}
    (hi : 1 ≤ i) (hij : i + j ≤ k) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hsinθ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam_nn : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hsinθ _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2) ≤ 1 :=
    Real.rpow_le_one hsinθ.le hsle1 (by linarith)
  have hone : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Real.rpow_neg hsinθ.le]
    exact (one_le_inv₀ hspos).mpr hsle
  have hL : Work.Spaces.w z ≤ Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    simpa using mul_le_mul_of_nonneg_left hone (w_nonneg_pi4 z)
  calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2
      = (Work.Spaces.mixed j i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    _ ≤ (Work.Spaces.mixed j i g z θ) ^ 2
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (w_nonneg_pi4 z) hL 2) (sq_nonneg _)
    _ = (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
        ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ i j hi hij

/-- On `[π/8, 3π/8]` the angle satisfies `sin(2θ) ≥ 1/2` (used to convert the `θ`-derivative
of a `D_z`-iterate into the corresponding mixed slot). -/
theorem half_le_sin_two_pi4 {x : ℝ} (hx : x ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) :
    (1 : ℝ) / 2 ≤ Real.sin (2 * x) := by
  have hxIθ : x ∈ Work.Spaces.Iθ :=
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hmin : Real.pi / 8 ≤ min x (Real.pi / 2 - x) :=
    le_min (by linarith [hx.1]) (by linarith [hx.2])
  have h1 := Work.FTS.H2.min_le_sin x hxIθ
  nlinarith [h1, hmin, Real.pi_pos]

theorem tracePi4 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (g : ℝ → ℝ → ℝ) (j : ℕ),
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g → j ≤ 2 →
      (∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z (Real.pi / 4)) ^ 2)
        ≤ C * Work.Spaces.HkSq α 6 g := by
  refine ⟨10, by norm_num, ?_⟩
  intro α hα g j hg hmem hj
  have hα0 : 0 < α := hα.1
  have hj6 : j ≤ 6 := by omega
  -- the subinterval `J = [π/8, 3π/8]` around the trace angle `π/4`
  have hsubI : Set.Icc (Real.pi / 8) (3 * Real.pi / 8) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hsubI' : Set.Icc (Real.pi / 8) (3 * Real.pi / 8) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  -- the pointwise-in-`z` trace bound
  have hkey : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z (Real.pi / 4)) ^ 2
        ≤ 10 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · -- `z = 0`: the radial weight vanishes
      subst hz0
      have hw0 : Work.Spaces.w 0 = 0 := by
        rw [Work.Spaces.w]; norm_num
      rw [hw0]
      have h0 : (0:ℝ) ^ 2 = 0 := by norm_num
      rw [h0, zero_mul]
      exact mul_nonneg (by norm_num)
        (integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 6 g 0 θ))
    · -- `z > 0`: the genuine estimate
      have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j g) := hg.DzIter j
      set h : ℝ → ℝ := fun θ => Work.Spaces.DzIter j g z θ with hh
      have hcont : ContinuousOn h (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) :=
        (hsm.curry_θ hzpos).continuousOn.mono hsubI'
      have hdc : ContinuousOn (deriv h) (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) := by
        refine ContinuousOn.congr ((hsm.pth.curry_θ hzpos).continuousOn.mono hsubI') ?_
        intro x hx
        have := Work.FTS.EllSol.WeakSlice.pth_DzIter_Q0 hg j hzpos (hsubI' hx)
        simpa only [hh, Work.Spaces.pth] using this
      have hd : ∀ x ∈ Set.Ioo (Real.pi / 8) (3 * Real.pi / 8),
          HasDerivAt h (deriv h x) x := by
        intro x hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
          ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
        have := ((hsm.curry_θ hzpos).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hx')
        simpa only [hh] using this.hasDerivAt
      have hmor := trace_morrey (h := h) (a := Real.pi / 8) (x₀ := Real.pi / 4)
        (b := 3 * Real.pi / 8) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        hcont hdc hd
      have hbma : (3:ℝ) * Real.pi / 8 - Real.pi / 8 = Real.pi / 4 := by ring
      rw [hbma] at hmor
      -- the `L²`-block: `∫_J w² h² ≤ K`
      have hIntHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 6 g z θ)
          (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) :=
        (hmem.1 z hz).mono_set hsubI
      have hI1 : (Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
            (h x) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ := by
        rw [← MeasureTheory.integral_const_mul]
        refine le_trans (MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))) hIntHk
          (ae_restrict_of_forall_mem measurableSet_Icc
            (fun x hx => wsq_dzIter_le_HkIntegrand_pi4 hj6 (hsubI' hx)))) ?_
        exact MeasureTheory.setIntegral_mono_set (hmem.1 z hz)
          (Eventually.of_forall (fun x => Work.Spaces.HkIntegrand_nonneg α 6 g z x))
          (Eventually.of_forall (fun x hx => hsubI hx))
      -- the `H¹`-block: `∫_J w² (h')² ≤ 4K`
      have hpt2 : ∀ x ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
          (Work.Spaces.w z) ^ 2 * (deriv h x) ^ 2
            ≤ 4 * Work.Spaces.HkIntegrand α 6 g z x := by
        intro x hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hsubI' hx
        have hsinpos : 0 < Real.sin (2 * x) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hx'.1])
            (by linarith [hx'.2, Real.pi_pos])
        have hder : deriv h x = Work.Spaces.DzIter j (Work.Spaces.pth g) z x := by
          have := Work.FTS.EllSol.WeakSlice.pth_DzIter_Q0 hg j hzpos hx'
          simpa only [hh, Work.Spaces.pth] using this
        have hmix : Work.Spaces.mixed j 1 g z x
            = Real.sin (2 * x) * Work.Spaces.DzIter j (Work.Spaces.pth g) z x :=
          (Work.FTS.H2.sin_mul_dzIter_pth g j z x).symm
        have hsin := half_le_sin_two_pi4 hx
        have hsinne : Real.sin (2 * x) ≠ 0 := ne_of_gt hsinpos
        have habs : |Work.Spaces.DzIter j (Work.Spaces.pth g) z x|
            = |Work.Spaces.mixed j 1 g z x| / Real.sin (2 * x) := by
          have h3 : Real.sin (2 * x)
              * |Work.Spaces.DzIter j (Work.Spaces.pth g) z x|
              = |Work.Spaces.mixed j 1 g z x| := by
            rw [← abs_of_pos hsinpos, ← abs_mul, ← hmix]
          rw [eq_div_iff hsinne, mul_comm]
          exact h3
        have hbound : |deriv h x| ≤ 2 * |Work.Spaces.mixed j 1 g z x| := by
          rw [hder, habs, div_le_iff₀ hsinpos]
          nlinarith [abs_nonneg (Work.Spaces.mixed j 1 g z x), hsin]
        have hd2 : (deriv h x) ^ 2 ≤ 4 * (Work.Spaces.mixed j 1 g z x) ^ 2 := by
          have h3 := pow_le_pow_left₀ (abs_nonneg _) hbound 2
          rw [sq_abs, mul_pow, sq_abs] at h3
          nlinarith [h3]
        calc (Work.Spaces.w z) ^ 2 * (deriv h x) ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * (4 * (Work.Spaces.mixed j 1 g z x) ^ 2) :=
              mul_le_mul_of_nonneg_left hd2 (sq_nonneg _)
          _ = 4 * ((Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j 1 g z x) ^ 2) := by ring
          _ ≤ 4 * Work.Spaces.HkIntegrand α 6 g z x :=
              mul_le_mul_of_nonneg_left
                (wsq_mixed_le_HkIntegrand_pi4 hα0.le (by norm_num) (by omega) hx') (by norm_num)
      have hI2 : (Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
            (deriv h x) ^ 2)
          ≤ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) := by
        rw [← MeasureTheory.integral_const_mul]
        have hInt4 : IntegrableOn (fun θ => 4 * Work.Spaces.HkIntegrand α 6 g z θ)
            (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) := hIntHk.const_mul 4
        refine le_trans (MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))) hInt4
          (ae_restrict_of_forall_mem measurableSet_Icc hpt2)) ?_
        rw [MeasureTheory.integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 4)
        exact MeasureTheory.setIntegral_mono_set (hmem.1 z hz)
          (Eventually.of_forall (fun x => Work.Spaces.HkIntegrand_nonneg α 6 g z x))
          (Eventually.of_forall (fun x hx => hsubI hx))
      set K : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ with hK
      have hKnn : 0 ≤ K := by
        rw [hK]; exact integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 6 g z θ)
      have hc1 : 2 / (Real.pi / 4) = 8 / Real.pi := by
        field_simp
        norm_num
      have hc2 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
      have hcoef : 8 / Real.pi + 2 * Real.pi ≤ 10 := by
        have hp1 : (1:ℝ) ≤ Real.pi := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
        have hp4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
        have hprod : (Real.pi - 1) * (Real.pi - 4) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
        have heq : 8 / Real.pi + 2 * Real.pi = (8 + 2 * Real.pi * Real.pi) / Real.pi := by
          field_simp
        rw [heq, div_le_iff₀ Real.pi_pos]
        nlinarith [hprod]
      calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z (Real.pi / 4)) ^ 2
          = (Work.Spaces.w z) ^ 2 * (h (Real.pi / 4)) ^ 2 := by rw [hh]
        _ ≤ (Work.Spaces.w z) ^ 2 * ((2 / (Real.pi / 4)) * (∫ x in Set.Icc (Real.pi / 8)
                (3 * Real.pi / 8), (h x) ^ 2)
              + 2 * (Real.pi / 4) * (∫ x in Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
                (deriv h x) ^ 2)) := mul_le_mul_of_nonneg_left hmor (sq_nonneg _)
        _ = (2 / (Real.pi / 4)) * ((Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8)
                (3 * Real.pi / 8), (h x) ^ 2))
              + 2 * (Real.pi / 4) * ((Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8)
                (3 * Real.pi / 8), (deriv h x) ^ 2)) := by ring
        _ = (8 / Real.pi) * ((Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8)
                (3 * Real.pi / 8), (h x) ^ 2))
              + (Real.pi / 2) * ((Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8)
                (3 * Real.pi / 8), (deriv h x) ^ 2)) := by rw [hc1, hc2]
        _ ≤ (8 / Real.pi) * K + (Real.pi / 2) * (4 * K) := by
            have h8 : 0 ≤ (8:ℝ) / Real.pi := by positivity
            have hp2 : 0 ≤ Real.pi / 2 := by positivity
            have hA := mul_le_mul_of_nonneg_left hI1 h8
            have hB := mul_le_mul_of_nonneg_left hI2 hp2
            rw [hK] at hA hB ⊢
            linarith
        _ = (8 / Real.pi + 2 * Real.pi) * K := by ring
        _ ≤ 10 * K := mul_le_mul_of_nonneg_right hcoef hKnn
  -- integrate the pointwise bound in `z`
  have hZi : MeasureTheory.Integrable
      (fun z => 10 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2.const_mul 10
  have hmono : (∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z (Real.pi / 4)) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz,
          10 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))) hZi
      (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) hkey)
  calc (∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z (Real.pi / 4)) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz,
          10 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) := hmono
    _ = 10 * Work.Spaces.HkSq α 6 g := by
        rw [MeasureTheory.integral_const_mul]
        rfl

end
end Work.FTS.StrongPersist.N6Trans.SixRoute
