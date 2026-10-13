/-
Copyright: work module for the Elgindi finite-time singularity project.

# The radial Hardy inequality `HardyZ`

This file proves the one-dimensional Hardy-type inequality in the radial variable `z`
that is used in §H2 of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887.

For a function `g` smooth on a neighbourhood of the closed quadrant whose `θ`-slice
`z ↦ g z θ` vanishes at `z = ∞`, one has, for every `z ≥ 0`,

  `g(z,θ)² ≤ ∫₀^∞ (D_z g)(s,θ)² w(s)² ds`,   `w(s) = (1+s)²/s²`,  `D_z = z ∂_z`.

The proof is the classical one: write `g(z,θ) = -∫_z^∞ ∂_s g(s,θ) ds` (since
`g(·,θ) → 0` at `∞`), split the integrand as
`∂_s g · 1 = (s ∂_s g · w(s)) · (1/(s w(s)))`, and apply Cauchy–Schwarz on the
interval `[z,B]`.  The point is that the weight `1/(s w(s)) = s/(1+s)²` is
integrable near `0` and at `∞` with total mass `≤ 1`:

  `∫_z^B (s/(1+s)²)² ds ≤ ∫_z^B 1/(1+s)² ds = 1/(1+z) - 1/(1+B) ≤ 1`.

Hence `|g(z,θ)| ≤ √(∫₀^∞ (D_z g)² w²)` for `z > 0`; the case `z = 0` follows by
continuity of the slice at `z = 0`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## Smoothness of the `θ`-slice of a `SmoothNbhd` function -/

/-- The `θ`-slice `z ↦ g z θ` of a function smooth on a neighbourhood of the closed
quadrant is smooth on `(-1,∞)`. -/
theorem hardyZ_contDiffOn_slice (g : ℝ → ℝ → ℝ) (hsm : SmoothNbhd g) {θ : ℝ} (hθ : θ ∈ Iθ) :
    ContDiffOn ℝ ⊤ (fun z => g z θ) (Set.Ioi (-1)) := by
  have hθ' : θ ∈ Set.Ioo (-1) (π/2 + 1) := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (-1))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1)) := fun z hz => ⟨hz, hθ'⟩
  exact hsm.comp (contDiffOn_id.prodMk contDiffOn_const) hmap

/-- The slice `z ↦ g z θ` has derivative `pz g z θ` on `(-1,∞)`. -/
theorem hardyZ_hasDerivAt_slice (g : ℝ → ℝ → ℝ) (hsm : SmoothNbhd g) {θ : ℝ} (hθ : θ ∈ Iθ)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) : HasDerivAt (fun z => g z θ) (pz g z θ) z := by
  have hd : DifferentiableOn ℝ (fun z => g z θ) (Set.Ioi (-1)) :=
    (hardyZ_contDiffOn_slice g hsm hθ).differentiableOn (by simp)
  exact hd.hasDerivAt (isOpen_Ioi.mem_nhds hz)

/-- The derivative `z ↦ pz g z θ` of the slice is continuous on `(-1,∞)`. -/
theorem hardyZ_continuousOn_pz_slice (g : ℝ → ℝ → ℝ) (hsm : SmoothNbhd g) {θ : ℝ}
    (hθ : θ ∈ Iθ) : ContinuousOn (fun z => pz g z θ) (Set.Ioi (-1)) := by
  have hcd := (hardyZ_contDiffOn_slice g hsm hθ).continuousOn_derivWithin
    (isOpen_Ioi.uniqueDiffOn) le_top
  have : ContinuousOn (fun z => deriv (fun z => g z θ) z) (Set.Ioi (-1)) :=
    hcd.congr (fun x hx => (derivWithin_of_isOpen isOpen_Ioi hx).symm)
  simpa [pz] using this

/-- Elementary membership helper. -/
theorem hardyZ_mem_Ioi (a x : ℝ) (ha : 0 ≤ a) (hx : a ≤ x) : x ∈ Set.Ioi (-1) := by
  simp only [Set.mem_Ioi]; linarith

/-- The fundamental theorem of calculus for the `θ`-slice of a `SmoothNbhd` function:
`∫_a^b ∂_z g(s,θ) ds = g(b,θ) - g(a,θ)`. -/
theorem hardyZ_integral_pz_eq_sub (g : ℝ → ℝ → ℝ) (hsm : SmoothNbhd g) {θ : ℝ} (hθ : θ ∈ Iθ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ s in a..b, pz g s θ = g b θ - g a θ := by
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun z => g z θ) (pz g x θ) x :=
    fun x hx => hardyZ_hasDerivAt_slice g hsm hθ (hardyZ_mem_Ioi a x ha hx.1.le)
  have hcont : ContinuousOn (fun z => g z θ) (Set.Icc a b) :=
    (hardyZ_contDiffOn_slice g hsm hθ).continuousOn.mono
      (fun x hx => hardyZ_mem_Ioi a x ha hx.1)
  have hint : IntervalIntegrable (fun s => pz g s θ) volume a b := by
    refine (hardyZ_continuousOn_pz_slice g hsm hθ).mono (fun x hx => ?_) |>.intervalIntegrable
    rw [Set.uIcc_of_le hab] at hx
    exact hardyZ_mem_Ioi a x ha hx.1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint

/-! ## Two elementary real-variable lemmas -/

/-- Cauchy–Schwarz (Bunyakovsky) for the interval integral. -/
theorem hardyZ_interval_integral_mul_le_sqrt (a b : ℝ) (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.uIcc a b)) (hg : ContinuousOn g (Set.uIcc a b)) :
    |∫ x in a..b, f x * g x| ≤
      Real.sqrt (∫ x in a..b, f x ^ 2) * Real.sqrt (∫ x in a..b, g x ^ 2) := by
  have hfI : ContinuousOn f (Set.Icc a b) := by simpa [Set.uIcc_of_le hab] using hf
  have hgI : ContinuousOn g (Set.Icc a b) := by simpa [Set.uIcc_of_le hab] using hg
  have hIoc : MeasurableSet (Set.Ioc a b) := measurableSet_Ioc
  have hsub : Set.Ioc a b ⊆ Set.Icc a b := Set.Ioc_subset_Icc_self
  have h1 : |∫ x in a..b, f x * g x| ≤ ∫ x in a..b, |f x| * |g x| := by
    have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hab
      (f := fun x => f x * g x)
    simpa [Real.norm_eq_abs, abs_mul] using h
  have h2 : ∫ x in a..b, |f x| * |g x| = ∫ x in Set.Ioc a b, |f x| * |g x| :=
    intervalIntegral.integral_of_le hab
  have hmf : AEStronglyMeasurable (fun x => |f x|) (volume.restrict (Set.Ioc a b)) :=
    (hfI.abs.mono hsub).aestronglyMeasurable hIoc
  have hmg : AEStronglyMeasurable (fun x => |g x|) (volume.restrict (Set.Ioc a b)) :=
    (hgI.abs.mono hsub).aestronglyMeasurable hIoc
  have hfi : IntegrableOn (fun x => |f x| ^ 2) (Set.Ioc a b) :=
    ((hfI.abs.pow 2).integrableOn_compact isCompact_Icc).mono_set hsub
  have hgi : IntegrableOn (fun x => |g x| ^ 2) (Set.Ioc a b) :=
    ((hgI.abs.pow 2).integrableOn_compact isCompact_Icc).mono_set hsub
  have hLf : MemLp (fun x => |f x|) (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) := by
    rw [show ENNReal.ofReal (2:ℝ) = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hmf).mpr hfi
  have hLg : MemLp (fun x => |g x|) (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) := by
    rw [show ENNReal.ofReal (2:ℝ) = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hmg).mpr hgi
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Set.Ioc a b))
    (p := 2) (q := 2) (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun x => abs_nonneg (f x))
    (Filter.Eventually.of_forall fun x => abs_nonneg (g x)) hLf hLg
  have h3f : ∫ x in Set.Ioc a b, |f x| ^ 2 = ∫ x in a..b, f x ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_congr_fun hIoc (fun x _ => sq_abs (f x))
  have h3g : ∫ x in Set.Ioc a b, |g x| ^ 2 = ∫ x in a..b, g x ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_congr_fun hIoc (fun x _ => sq_abs (g x))
  calc |∫ x in a..b, f x * g x| ≤ ∫ x in a..b, |f x| * |g x| := h1
    _ = ∫ x in Set.Ioc a b, |f x| * |g x| := h2
    _ ≤ (∫ x in Set.Ioc a b, |f x| ^ 2) ^ (1 / 2 : ℝ) *
          (∫ x in Set.Ioc a b, |g x| ^ 2) ^ (1 / 2 : ℝ) := hH
    _ = Real.sqrt (∫ x in Set.Ioc a b, |f x| ^ 2) *
          Real.sqrt (∫ x in Set.Ioc a b, |g x| ^ 2) := by
        simp only [Real.sqrt_eq_rpow, Real.rpow_two]
    _ = Real.sqrt (∫ x in a..b, f x ^ 2) * Real.sqrt (∫ x in a..b, g x ^ 2) := by
        rw [h3f, h3g]

/-- The weight `ψ(s) = s/(1+s)²` has interval integral of its square at most `1`. -/
theorem hardyZ_integral_psi_sq_le_one {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ s in a..b, (s / (1 + s) ^ 2) ^ 2 ≤ 1 := by
  have hpt : ∀ x ∈ Set.Icc a b, (x / (1 + x) ^ 2) ^ 2 ≤ 1 / (1 + x) ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans ha hx.1
    have h2 : (0:ℝ) < (1 + x) ^ 2 := by positivity
    rw [div_pow, div_le_div_iff₀ (by positivity) h2]
    have hsq : x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
    calc x ^ 2 * (1 + x) ^ 2 ≤ (1 + x) ^ 2 * (1 + x) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq h2.le
      _ = 1 * ((1 + x) ^ 2) ^ 2 := by ring
  have hcf : ContinuousOn (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) (Set.Icc a b) := by
    apply ContinuousOn.pow
    apply ContinuousOn.div
    · exact continuousOn_id
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1
      positivity
  have hcg : ContinuousOn (fun s : ℝ => 1 / (1 + s) ^ 2) (Set.Icc a b) := by
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1
      positivity
  have hif : IntervalIntegrable (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hig : IntervalIntegrable (fun s : ℝ => 1 / (1 + s) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hmono : ∫ s in a..b, (s / (1 + s) ^ 2) ^ 2 ≤ ∫ s in a..b, 1 / (1 + s) ^ 2 :=
    intervalIntegral.integral_mono_on hab hif hig hpt
  have hval : ∫ s in a..b, 1 / (1 + s) ^ 2 = (1 + a)⁻¹ - (1 + b)⁻¹ := by
    have hderiv : ∀ x ∈ Set.Ioo a b,
        HasDerivAt (fun s : ℝ => -(1 + s)⁻¹) (1 / (1 + x) ^ 2) x := by
      intro x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1.le
      have hx1 : 0 < 1 + x := by linarith
      have h2 := ((hasDerivAt_id x).const_add (1:ℝ)).inv (ne_of_gt hx1)
      have h3 := h2.neg
      have hfun : (fun s : ℝ => -(1 + s)⁻¹) = -(fun x => 1 + id x)⁻¹ := rfl
      rw [hfun]
      convert h3 using 1
      simp only [id_eq]
      ring
    have hcont : ContinuousOn (fun s : ℝ => -(1 + s)⁻¹) (Set.Icc a b) := by
      apply ContinuousOn.neg
      apply ContinuousOn.inv₀
      · exact continuousOn_const.add continuousOn_id
      · intro x hx
        have hx0 : 0 ≤ x := le_trans ha hx.1
        linarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hig]
    ring
  calc ∫ s in a..b, (s / (1 + s) ^ 2) ^ 2 ≤ ∫ s in a..b, 1 / (1 + s) ^ 2 := hmono
    _ = (1 + a)⁻¹ - (1 + b)⁻¹ := hval
    _ ≤ (1 + a)⁻¹ := by
        have : 0 ≤ (1 + b)⁻¹ := by
          rw [inv_nonneg]; linarith
        linarith
    _ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)

/-- Monotonicity of the set integral for `[a,b] ⊆ [0,∞)`. -/
theorem hardyZ_integral_Ioc_le_integral_Iz {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hint : IntegrableOn f Iz) (h0 : ∀ x ∈ Iz, 0 ≤ f x) :
    (∫ x in a..b, f x) ≤ ∫ x in Iz, f x := by
  rw [intervalIntegral.integral_of_le hab]
  have h_ae : 0 ≤ᵐ[volume.restrict Iz] f := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with x hx
    exact h0 x hx
  refine setIntegral_mono_set hint h_ae ?_
  exact Filter.Eventually.of_forall (fun x hx => le_trans ha hx.1.le)

/-- The algebraic identity behind the weighted Cauchy–Schwarz step:
`(D_z g · w)(s) · ψ(s) = ∂_s g(s,θ)` for `s > 0`, where `ψ(s) = s/(1+s)²`. -/
theorem hardyZ_mul_w_mul_psi (g : ℝ → ℝ → ℝ) {θ s : ℝ} (hs : 0 < s) :
    (Dz g s θ * w s) * (s / (1 + s) ^ 2) = pz g s θ := by
  have h1 : (1 + s) ≠ 0 := ne_of_gt (by linarith)
  simp only [Dz, w]
  field_simp

/-! ## The Hardy inequality -/

theorem HardyZ (g : ℝ → ℝ → ℝ) (θ : ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (hθ : θ ∈ Work.Spaces.Iθ) (hdec : Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.Dz g z θ) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    ∀ z ∈ Work.Spaces.Iz, (g z θ) ^ 2 ≤
      ∫ s in Work.Spaces.Iz, (Work.Spaces.Dz g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
  set P : ℝ := ∫ s in Iz, (Dz g s θ) ^ 2 * (w s) ^ 2 with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact integral_nonneg fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmain : ∀ z, 0 ≤ z → 0 < z → (g z θ) ^ 2 ≤ P := by
    intro z hz hzpos
    have hkey : ∀ B, z ≤ B → |g z θ| ≤ |g B θ| + Real.sqrt P := by
      intro B hzB
      have hFTC : ∫ s in z..B, pz g s θ = g B θ - g z θ :=
        hardyZ_integral_pz_eq_sub g hsm hθ hz hzB
      have hpzc : ContinuousOn (fun s => pz g s θ) (Set.Icc z B) :=
        (hardyZ_continuousOn_pz_slice g hsm hθ).mono
          (fun x hx => hardyZ_mem_Ioi z x hz hx.1)
      have hwc : ContinuousOn w (Set.Icc z B) := by
        unfold w
        apply ContinuousOn.div
        · exact (continuousOn_const.add continuousOn_id).pow 2
        · exact continuousOn_id.pow 2
        · intro x hx
          have hx0 : 0 < x := lt_of_lt_of_le hzpos hx.1
          positivity
      have hcontA : ContinuousOn (fun s => Dz g s θ * w s) (Set.uIcc z B) := by
        rw [Set.uIcc_of_le hzB]
        unfold Dz
        exact (continuousOn_id.mul hpzc).mul hwc
      have hcontψ : ContinuousOn (fun s => s / (1 + s) ^ 2) (Set.uIcc z B) := by
        rw [Set.uIcc_of_le hzB]
        apply ContinuousOn.div
        · exact continuousOn_id
        · exact (continuousOn_const.add continuousOn_id).pow 2
        · intro x hx
          have hx0 : 0 < x := lt_of_lt_of_le hzpos hx.1
          positivity
      have hcs := hardyZ_interval_integral_mul_le_sqrt z B hzB hcontA hcontψ
      have hcongr : ∫ x in z..B, (Dz g x θ * w x) * (x / (1 + x) ^ 2)
          = ∫ x in z..B, pz g x θ := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hzB] at hx
        exact hardyZ_mul_w_mul_psi g (lt_of_lt_of_le hzpos hx.1)
      have hA2le : ∫ x in z..B, (Dz g x θ * w x) ^ 2 ≤ P := by
        have h1 : ∫ x in z..B, (Dz g x θ * w x) ^ 2
            = ∫ x in z..B, (Dz g x θ) ^ 2 * (w x) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro x _
          ring
        rw [h1, hPdef]
        exact hardyZ_integral_Ioc_le_integral_Iz hz hzB hint
          (fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have hψle : ∫ x in z..B, (x / (1 + x) ^ 2) ^ 2 ≤ 1 :=
        hardyZ_integral_psi_sq_le_one hz hzB
      have hchain : |∫ x in z..B, pz g x θ| ≤ Real.sqrt P := by
        rw [← hcongr]
        calc |∫ x in z..B, (Dz g x θ * w x) * (x / (1 + x) ^ 2)|
            ≤ Real.sqrt (∫ x in z..B, (Dz g x θ * w x) ^ 2) *
                Real.sqrt (∫ x in z..B, (x / (1 + x) ^ 2) ^ 2) := hcs
          _ ≤ Real.sqrt P * Real.sqrt 1 := by
              exact mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hψle)
                (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          _ = Real.sqrt P := by rw [Real.sqrt_one, mul_one]
      have hchain' : |g B θ - g z θ| ≤ Real.sqrt P := by
        rw [← hFTC]
        exact hchain
      have hsplit : g z θ = g B θ - (g B θ - g z θ) := by ring
      calc |g z θ| = |g B θ - (g B θ - g z θ)| := congrArg abs hsplit
        _ ≤ |g B θ| + |g B θ - g z θ| := abs_sub _ _
        _ ≤ |g B θ| + Real.sqrt P := by linarith [hchain']
    have hlim : Filter.Tendsto (fun B => |g B θ| + Real.sqrt P) Filter.atTop
        (nhds (Real.sqrt P)) := by
      have habs : Filter.Tendsto (fun B => |g B θ|) Filter.atTop (nhds 0) := by
        simpa using hdec.abs
      simpa using habs.add_const (Real.sqrt P)
    have hev : ∀ᶠ B in Filter.atTop, |g z θ| ≤ |g B θ| + Real.sqrt P :=
      (eventually_ge_atTop z).mono fun B hB => hkey B hB
    have hle : |g z θ| ≤ Real.sqrt P := ge_of_tendsto hlim hev
    calc (g z θ) ^ 2 = |g z θ| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.sqrt P) ^ 2 := by
          nlinarith [hle, abs_nonneg (g z θ), Real.sqrt_nonneg P]
      _ = P := Real.sq_sqrt hPnn
  intro z hz
  have hz0 : 0 ≤ z := hz
  rcases lt_or_eq_of_le hz0 with hlt | hzero
  · exact hmain z hz0 hlt
  · subst hzero
    have hcont0 : ContinuousAt (fun z => g z θ) 0 :=
      (hardyZ_contDiffOn_slice g hsm hθ).continuousOn.continuousAt
        (isOpen_Ioi.mem_nhds (by simp))
    have hlim2 : Filter.Tendsto (fun z => (g z θ) ^ 2) (𝓝[>] (0:ℝ)) (nhds ((g 0 θ) ^ 2)) := by
      have h := (hcont0.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).pow 2
      simpa using h
    refine le_of_tendsto hlim2 ?_
    refine Filter.eventually_of_mem (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ 𝓝[>] (0:ℝ)) ?_
    intro z hz'
    exact hmain z (le_of_lt hz') hz'

end Work.Spaces
