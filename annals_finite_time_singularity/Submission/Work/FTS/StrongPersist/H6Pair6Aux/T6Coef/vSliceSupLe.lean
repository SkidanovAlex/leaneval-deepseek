import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.supDz_zslice6
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.OpenPkg.ProdOpen.SlicesOpen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux.sliceZAgmon
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux.slotRadialIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

/-- **The angular-slice bound for the lowest mixed slot `D_θf`.**

For a datum `f` which is `C^∞` on the open quadrant and honestly in `ℋ⁴`, and for every `z > 0`,
the angular slice at `z` of the mixed slot `mixed 0 1 f = D_θ f`, weighted by `sin(2θ)^{-γ}`, is
dominated by twice the `ℋ⁴`-square of `f`:

  `∫_θ sin(2θ)^{-γ} (D_θ f z θ)² dθ ≤ 2 |f|²_{ℋ⁴}`.

The two ingredients are the one-dimensional weighted radial Agmon inequality
(`SixAux.zslice6_hardy`, applied at the fixed angle `θ` to the radial slice `z ↦ sin(2θ)^{-γ/2}
D_θf(z,θ)`) and the Tonelli identity `SdaAux.sda_HkSqSwap_open` for the `ℋ⁴`-integrand of an
open-class datum, which supplies the radial integrability of the slices for almost every angle.
The equality case of the constant `2` is the Agmon constant: the two radial `L²`-integrals
`∫ (D_θf)² Wt²` and `∫ (D_zD_θf)² Wt²` are the two summands `(i,j) = (1,0)` resp. `(1,1)` of
`HkIntegrand α 4 f`, and each is at most `HkSq α 4 f`. -/
theorem vSliceSupLe : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 0 1 f z θ) ^ 2)
        ≤ 2 * Work.Spaces.HkSq α 4 f := by
  intro α f hα hα1 hF hmem z hz
  obtain ⟨hswap, hGint, hGslice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hF hmem
  -- the pointwise (in `θ`) slice bound, dominated by the `ℋ⁴`-integrand of `f`
  have hleG : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 0 1 f z θ) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s θ) := by
    filter_upwards [hGslice, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθint hθ
    obtain ⟨h1, h2⟩ :=
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux.slotRadialIntegrable α f θ hθ hF hθint
    have hA :=
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux.sliceZAgmon α f z θ hz hθ hF h1 h2
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    -- the `(1,1)`-summand of `HkIntegrand` dominates the Agmon right-hand side
    have hmono : (∫ s in Work.Spaces.Iz, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s θ := by
      refine MeasureTheory.setIntegral_mono_of_nonneg (fun s _ => ?_) (fun s _ => ?_) hθint
      · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hsin.le _) (sq_nonneg _))
          (sq_nonneg _)
      · have hkey : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            = (Work.Spaces.mixed 1 1 f s θ * Work.Spaces.Wt α s θ) ^ 2 := by
          rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α s θ hsin]
          ring
        rw [hkey]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s θ 1 1 le_rfl (by norm_num)
    calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 0 1 f z θ) ^ 2
        ≤ 2 * ∫ s in Work.Spaces.Iz, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := hA
      _ ≤ 2 * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s θ := by
          linarith
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 0 1 f z θ) ^ 2) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (Real.rpow_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])) _) (sq_nonneg _))
  calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 0 1 f z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ,
          2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s θ) :=
        MeasureTheory.integral_mono_of_nonneg hnn (hGint.const_mul 2) hleG
    _ = 2 * Work.Spaces.HkSq α 4 f := by
        rw [MeasureTheory.integral_const_mul, hswap]

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
