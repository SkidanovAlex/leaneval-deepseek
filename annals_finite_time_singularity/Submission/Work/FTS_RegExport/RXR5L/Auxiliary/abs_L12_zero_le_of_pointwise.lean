/-
Copyright: work module for the Elgindi finite-time singularity project.

# A pointwise majorant for `L₁₂` at the origin

`Work.FTS_RegExport.RXR5L.aux.abs_L12_zero_le_of_pointwise`: if `f` is dominated, on the
half-strip `(0,∞) × Iθ`, by `M · Rwt` with `M ≥ 0`, where `Rwt z = z^{3/2}/(1+z)²`, then

  `|L₁₂(f)(0)| ≤ 3·(π/2)·M·2`.

No regularity of `f` whatsoever is assumed.  The route is the two elementary mean
inequalities:

* the angular density `L₁₂dens(f)(s) = ∫_{Iθ} K(θ)·f(s,θ)/s dθ` (`s > 0`) is bounded by
  `3·(π/2)·M·Rwt s / s`: pointwise `|K(θ)| ≤ 3` and `vol(Iθ) = π/2`
  (`dens_bound`);
* `Rwt s / s = s^{1/2}/(1+s)² ≤ (1+s)^{-3/2}` and `∫_0^∞ (1+s)^{-3/2} ds = 2`
  (`integral_Ioi_one_add_rpow`), so the outer `s`-integral is at most
  `3·(π/2)·M·2`.

Everything rests only on Mathlib (the antiderivative `-2(1+s)^{-1/2}`) and on the standing
definitions of `Submission.Work.FM`, `Submission.Work.Construction` and
`Submission.Work.FTS_RegExport.RXT.L12Iter`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXR5L.aux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Two elementary integrals -/

/-- The integral of a constant over `Iθ = [0,π/2]` is the constant times `π/2`. -/
private theorem integral_Iθ_const (c : ℝ) :
    (∫ _θ in Work.Spaces.Iθ, c) = c * (Real.pi / 2) := by
  rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- `∫_0^∞ (1+s)^{-3/2} ds = 2`, with the antiderivative `-2(1+s)^{-1/2}`. -/
private theorem integral_Ioi_one_add_rpow :
    (∫ s : ℝ in Set.Ioi (0 : ℝ), (1 + s) ^ (-(3 : ℝ) / 2)) = 2 := by
  rw [show (∫ s : ℝ in Set.Ioi (0 : ℝ), (1 + s) ^ (-(3 : ℝ) / 2))
      = ∫ s : ℝ in Set.Ioi (0 : ℝ), (s + 1) ^ (-(3 : ℝ) / 2) from
        setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [add_comm]]
  have hd : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => (t + 1) ^ (-(3 : ℝ) / 2 + 1) / (-(3 : ℝ) / 2 + 1))
        ((x + 1) ^ (-(3 : ℝ) / 2)) x := by
    intro x hx
    have hne : x + 1 ≠ 0 := by linarith [Set.mem_Ici.mp hx]
    have h1 : HasDerivAt (fun t : ℝ => t + 1) 1 x := (hasDerivAt_id x).add_const 1
    have h2 : HasDerivAt (fun t : ℝ => (t + 1) ^ (-(3 : ℝ) / 2 + 1))
        (1 * (-(3 : ℝ) / 2 + 1) * (x + 1) ^ (-(3 : ℝ) / 2 + 1 - 1)) x :=
      h1.rpow_const (Or.inl hne)
    have h3 := h2.div_const (-(3 : ℝ) / 2 + 1)
    convert h3 using 1
    ring_nf
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ (x + 1) ^ (-(3 : ℝ) / 2) :=
    fun x hx => Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp hx]) _
  have hlim : Filter.Tendsto
      (fun t : ℝ => (t + 1) ^ (-(3 : ℝ) / 2 + 1) / (-(3 : ℝ) / 2 + 1))
      Filter.atTop (nhds 0) := by
    have hb : Filter.Tendsto (fun t : ℝ => (t + 1) ^ (-(3 : ℝ) / 2 + 1))
        Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) Filter.atTop (nhds 0) :=
        tendsto_rpow_neg_atTop (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num)
      have h3 : Filter.Tendsto (fun t : ℝ => (t + 1) ^ (-(1 / 2 : ℝ))) Filter.atTop (nhds 0) := by
        simpa only [Function.comp_def, id_eq] using
          h2.comp (Filter.tendsto_atTop_add_const_right _ 1 tendsto_id)
      convert h3 using 1
      ext t
      rw [show (-(3 : ℝ) / 2 + 1) = -(1 / 2 : ℝ) by norm_num]
    simpa using hb.div_const ((-(3 : ℝ) / 2 + 1))
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (g := fun t : ℝ => (t + 1) ^ (-(3 : ℝ) / 2 + 1) / (-(3 : ℝ) / 2 + 1))
    (g' := fun x : ℝ => (x + 1) ^ (-(3 : ℝ) / 2)) hd hpos hlim
  rw [key]
  norm_num

/-! ## The angular mean inequality for the density -/

/-- **The pointwise bound on the density of `L₁₂`.**  Under the standing majorant
`|f z θ| ≤ M · Rwt z` on `(0,∞) × Iθ` and for `s > 0`,

  `‖L₁₂dens(f)(s)‖ ≤ 3·(π/2)·(M · Rwt s / s)`,

from `|K| ≤ 3`, `vol(Iθ) = π/2` and the pointwise domination of the angular integrand. -/
private theorem dens_bound {f : ℝ → ℝ → ℝ} {M : ℝ}
    (hb : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |f z θ| ≤ M * Work.FTS_RegExport.RXT.L12Iter.Rwt z)
    {s : ℝ} (hs : 0 < s) :
    ‖Work.FM.L12dens Work.Spaces.K f s‖
      ≤ 3 * (Real.pi / 2) * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := by
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      ‖Work.Spaces.K θ * f s θ / s‖
        ≤ 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := by
    intro θ hθ
    have hf : |f s θ| ≤ M * Work.FTS_RegExport.RXT.L12Iter.Rwt s := hb s θ hs hθ
    have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_le_three θ
    have hnum : |Work.Spaces.K θ| * |f s θ|
        ≤ 3 * (M * Work.FTS_RegExport.RXT.L12Iter.Rwt s) :=
      mul_le_mul hK hf (abs_nonneg _) (by norm_num)
    have h2 : 3 * (M * Work.FTS_RegExport.RXT.L12Iter.Rwt s) / s
        = 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := by ring
    calc ‖Work.Spaces.K θ * f s θ / s‖ = |Work.Spaces.K θ| * |f s θ| / s := by
          rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hs]
      _ ≤ 3 * (M * Work.FTS_RegExport.RXT.L12Iter.Rwt s) / s :=
          div_le_div_of_nonneg_right hnum hs.le
      _ = 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := h2
  have hint : MeasureTheory.Integrable
      (fun _ : ℝ => 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)))
      (volume.restrict Work.Spaces.Iθ) := MeasureTheory.integrable_const _
  have h1 : ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ / s‖
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := by
    refine MeasureTheory.norm_integral_le_of_norm_le
      (g := fun _ => 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s))) hint ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt θ hθ)
  have h2 : (∫ θ in Work.Spaces.Iθ, 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)))
      = 3 * (Real.pi / 2) * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := by
    rw [integral_Iθ_const]
    ring
  rw [Work.FM.L12dens]
  calc ‖∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), Work.Spaces.K θ * f s θ / s‖
      = ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ / s‖ := rfl
    _ ≤ _ := h1
    _ = _ := h2

/-! ## The main bound -/

theorem abs_L12_zero_le_of_pointwise {f : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |f z θ| ≤ M * Work.FTS_RegExport.RXT.L12Iter.Rwt z) :
    |Work.Construction.L12 f 0| ≤ 3 * (Real.pi / 2) * M * 2 := by
  -- the density is dominated by `3·(π/2)·M·(1+s)^{-3/2}`
  have hle : ∀ s ∈ Set.Ioi (0 : ℝ),
      ‖Work.FM.L12dens Work.Spaces.K f s‖
        ≤ 3 * (Real.pi / 2) * M * (1 + s) ^ (-(3 : ℝ) / 2) := by
    intro s hs
    have hs0 : 0 < s := hs
    have h1 := dens_bound hb hs0
    have h2 : Work.FTS_RegExport.RXT.L12Iter.Rwt s / s
        = s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 :=
      Work.FTS_RegExport.RXT.L12Iter.Rwt_div s hs0
    have h3 : s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ (1 + s) ^ (-(3 : ℝ) / 2) := by
      have hbase : (0 : ℝ) < 1 + s := by linarith
      have hroot : s ^ ((1 : ℝ) / 2) ≤ (1 + s) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hs0.le (by linarith) (by norm_num)
      have hdiv : s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2
          ≤ (1 + s) ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 :=
        div_le_div_of_nonneg_right hroot (by positivity)
      have heq : (1 + s) ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 = (1 + s) ^ (-(3 : ℝ) / 2) := by
        rw [← Real.rpow_natCast (1 + s) 2, ← Real.rpow_sub hbase]
        norm_num
      linarith [hdiv, le_of_eq heq]
    calc ‖Work.FM.L12dens Work.Spaces.K f s‖
        ≤ 3 * (Real.pi / 2) * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := h1
      _ = 3 * (Real.pi / 2) * (M * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by rw [h2]
      _ ≤ 3 * (Real.pi / 2) * (M * ((1 + s) ^ (-(3 : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hM) (by positivity)
      _ = 3 * (Real.pi / 2) * M * (1 + s) ^ (-(3 : ℝ) / 2) := by ring
  -- the majorant is integrable on `(0,∞)`
  have hmaj : MeasureTheory.Integrable
      (fun s : ℝ => 3 * (Real.pi / 2) * M * (1 + s) ^ (-(3 : ℝ) / 2))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h0 : MeasureTheory.Integrable (fun s : ℝ => (s + 1) ^ (-(3 : ℝ) / 2))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      integrableOn_add_rpow_Ioi_of_lt (a := -(3 : ℝ) / 2) (c := 0) (m := 1)
        (by norm_num) (by norm_num)
    have h1 : MeasureTheory.Integrable
        (fun s : ℝ => 3 * (Real.pi / 2) * M * (s + 1) ^ (-(3 : ℝ) / 2))
        (volume.restrict (Set.Ioi (0 : ℝ))) := h0.const_mul _
    refine h1.congr (Filter.Eventually.of_forall fun s => ?_)
    dsimp only
    rw [add_comm]
  have hle' : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Work.FM.L12dens Work.Spaces.K f s‖
        ≤ 3 * (Real.pi / 2) * M * (1 + s) ^ (-(3 : ℝ) / 2) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hle
  have hmain : ‖∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K f s‖
      ≤ ∫ s in Set.Ioi (0 : ℝ), 3 * (Real.pi / 2) * M * (1 + s) ^ (-(3 : ℝ) / 2) :=
    MeasureTheory.norm_integral_le_of_norm_le hmaj hle'
  have hval : (∫ s in Set.Ioi (0 : ℝ), 3 * (Real.pi / 2) * M * (1 + s) ^ (-(3 : ℝ) / 2))
      = 3 * (Real.pi / 2) * M * 2 := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_one_add_rpow]
  have hgoal : |Work.Construction.L12 f 0|
      = ‖∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K f s‖ := by
    rw [Work.Construction.L12, Work.FM.L12, Real.norm_eq_abs]
  rw [hgoal]
  linarith [hmain, le_of_eq hval]

/-! ## The difference (τ-modulus) form -/

/-- **The `L₁₂`-difference bound.**  If `f - g` is dominated by `C · Rwt` on the half-strip and
`L₁₂` is *subtractive* on the pair `(f, g)`, then the two `L₁₂`-values at `0` differ by at most
`3·(π/2)·C·2`.

The subtractivity is an explicit **hypothesis**, not a consequence of the majorant: the identity
`L₁₂ f 0 - L₁₂ g 0 = L₁₂ (f - g) 0` needs the integrability certificates of
`Work.FTS.StrongEps.EComparison.L12_sub_of_integrable` — precisely the data that
`abs_L12_zero_le_of_pointwise` is designed *not* to require.

**Which provider supplies it depends on the pair `(f, g)` at hand.**  `L12_sub_C4` (hypotheses
`ContDiffOn ℝ 4 · Q0` and `HkMem α 4 ·` *of `f` and `g` themselves*) supplies it when the two
functions are themselves of that class.  It does **not** supply it for functions *derived* from
such data: for `f_τ = 3·D_θ(slice g τ)/(1+z)` (the τ-Lipschitz consumer `RXR5L/aux/Tlim_bounds`)
the needed `C⁴`/`HkMem` data of `f_τ` is **not** inherited from `RegPkgMin.c4`/`mem4` of the slice
(`f_τ` is a `θ`-derivative, so `ContDiffOn ℝ 4` of `f_τ` would need `C⁵` of the slice, and
`HkMem α 4 f_τ` is a new weighted-integrability statement).  There the provider must be
`L12_sub_of_integrable` with its four certificates *for the pair* — see
`Auxiliary/_probe_compose_Tlim_bounds.lean` (machine-checked: the whole Tlim assembly follows from
this subtractivity plus the two `DynOK'` majorants). -/
theorem abs_L12_zero_sub_le_of_pointwise {f g : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hsub : ∀ z ∈ Work.Spaces.Iz, Work.Construction.L12 (fun z θ => f z θ - g z θ) z
      = Work.Construction.L12 f z - Work.Construction.L12 g z)
    (hb : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |f z θ - g z θ| ≤ C * Work.FTS_RegExport.RXT.L12Iter.Rwt z) :
    |Work.Construction.L12 f 0 - Work.Construction.L12 g 0| ≤ 3 * (Real.pi / 2) * C * 2 := by
  rw [← hsub 0 (by simp [Work.Spaces.Iz])]
  exact abs_L12_zero_le_of_pointwise hC hb

end Work.FTS_RegExport.RXR5L.aux
