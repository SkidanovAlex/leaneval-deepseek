/-
Copyright: work module for the Elgindi finite-time singularity project.

# The level-`n` weighted `L²`-bound for the angular moment `Qang g i`, open-quadrant class

For `g` of the *open-quadrant* class `Work.FTS.EllipticEst.SmoothOpen g` (smoothness of the
uncurried `g` on `z > 0`, `0 < θ < π/2` — no hypothesis on the strip `-1 < z ≤ 0`, hence no
analyticity, cf. the class-B discussion in `Submission/Work/FTS/EllipticEst/OpenQDefs.lean`) and
`Work.Spaces.HkMem α n g`, every angular moment

  `Qang g i z = ∫_θ Ktheta θ · D_z^i g z θ dθ`   (`i ≤ n`)

satisfies the honest `IntegrableOn` statement on `Iz = [0,∞)` together with

  `∫_z (Qang g i z)² w(z)² dz ≤ (∫_θ Ktheta θ²) · HkSq α n g`.

This is the open-quadrant counterpart of the delivered interior-class statement
`Work.FTS.CoercivityFix.Transfer.E1Norm.Qang_sq_w_sq_le_HkSq` (which assumes
`Work.FTS.LocData.SmoothQuad g`, i.e. `C^∞` on `z > -1`).  The statement below is byte-for-byte
the one requested by the `E1Open` consumer; the only new input is the general-level
Cauchy–Schwarz bound in `θ` in the open-quadrant class,
`Work.FTS.OpenPkg.Qang_sq_leQ_gen_open`.

The proof is the assembly of

* the pointwise (in `z > 0`) bound obtained from that Cauchy–Schwarz bound in `θ` and the
  slicewise domination `(D_z^i g z θ)² w(z)² ≤ HkIntegrand α n g z θ`
  (`Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` times `w²`), valid because `w ≥ 1`;
* the a.e. transfer of the pointwise bound from `(0,∞)` to `Iz` (the singleton `{0}` is null)
  together with a.e. strong measurability of `z ↦ (Qang g i z)² w(z)²`;
* the monotonicity of the Bochner integral against the integrable majorant
  `(∫_θ Ktheta θ²) · ∫_θ HkIntegrand α n g z θ` (`hmem.2`), whose integral *is* `HkSq α n g`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.H2.QangAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Qang_sq_w_sq_le_HkSq
import Submission.Work.FTS.OpenPkg.Qang_sq_leQ_gen_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.E1Open

open MeasureTheory
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Null sets and the radial weight -/

/-- The `z = 0`-slice of `Iz = [0,∞)` is null, so every almost-everywhere statement on `Iz`
may be proved on the open half-line. -/
private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

/-- The two angular endpoints of `Iθ = [0,π/2]` are null. -/
private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- The radial weight `w` squared is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

/-! ## The slicewise domination by the `ℋ^k`-integrand -/

/-- For `z > 0` and `0 < θ < π/2` the square of the weighted pure `D_z`-iterate is
dominated by the `ℋ^k`-integrand, `(D_z^i g z θ)² w(z)² ≤ HkIntegrand α k g z θ` (`i ≤ k`).
This is `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` multiplied by `w² > 0`; the level `k` is
arbitrary (that is what makes the level-`n` statement below possible). -/
private theorem DzIter_sq_w_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {k i : ℕ} (hi : i ≤ k)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α k g i hi hz hθ
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (Work.Spaces.w z))
  rwa [div_mul_cancel₀ _
    (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hz)))] at h2

/-! ## The target -/

theorem Qang_sq_w_sq_le_HkSq_O (n : ℕ) :
    ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α n g → ∀ i : ℕ, i ≤ n →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n g := by
  intro α g hα hα1 hO hmem i hi
  -- the pointwise (in `z > 0`) bound
  have hpt : ∀ z : ℝ, 0 < z →
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) := by
    intro z hz
    -- Cauchy–Schwarz in `θ`, at level `n`, in the open-quadrant class
    have hCS := Work.FTS.OpenPkg.Qang_sq_leQ_gen_open α g hO hmem i hi hz
    -- the `θ`-slice domination, with the weight `w z` on the left
    have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α n g z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => DzIter_sq_w_sq_le_HkIntegrand α g hi hz hθ)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 z (le_of_lt hz)) hae
      simpa only [MeasureTheory.integral_mul_const] using hmono
    calc (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2))
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hCS (sq_nonneg _)
      _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
      _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) :=
          mul_le_mul_of_nonneg_left hslice
            (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
  -- the bound holds almost everywhere on `Iz`
  have hle : (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ)) := by
    rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt
  -- a.e. strong measurability of the left-hand side
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hQ : AEStronglyMeasurable (fun z => Work.Elliptic.Qang g i z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have h := (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter i g p.1 p.2)
        (Work.FTS.OpenPkg.QangOpen.continuousOn_Ktheta_DzIter_open hO i)).integral_prod_right'
      simpa only [Work.Elliptic.Qang] using h
    have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
      exact continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi
    exact (hQ.pow 2).mul hw
  -- the dominating function is integrable
  have hdom : MeasureTheory.Integrable
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2.const_mul _
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [hle] with z hz
    rwa [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  · have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      hdom hle
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono.trans (le_of_eq rfl)

end Work.FTS.StrongEps.EpsE4Thr.E1Open
