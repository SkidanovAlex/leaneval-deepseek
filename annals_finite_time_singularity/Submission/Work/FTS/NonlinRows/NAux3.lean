import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.Nonlinear.n4norm_exists
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.NonlinRows.NAux3` — the auxiliary rows `rak`/`rl0`/`rl2` in the primed context

The three auxiliary rows of the §8 table in the open-quadrant vocabulary
(`Work.FTS.NonlinRows.Ctx`, i.e. `GalClass α g` + `StarPkgo α Cs Φs` + `EllPkgGo α Ce g Φg`),
each with its own uniform constant:

* `rak`: `AK α = (Γ(θ)/c)·2z²/(1+z)³` is honest in `ℋ⁴` (`HkMem_AK`, proved here) and its
  norm is bounded by a universal constant (`rak_bound`, from `Pieces/rowsAux.lean`);
* `rl0`: the zero mode of `N₀` — the primed context gives `GalClass α g`, hence `RegQ α 4 g`;
  the estimate is the delivered `rl0_bound`, instantiated with an *inhabitant* `N4Norm Ci α₂`
  supplied by `n4norm_exists` (its conclusion is independent of `Ci`, so no loss);
* `rl2`: the zero mode of `3 D_θ g/(1+z)` — the delivered `rl2_bound`, whose hypotheses are
  exactly `SmoothQuad g` and `HkMem α 4 g`.
-/

namespace Work.FTS.NonlinRows

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- **The `ℋ⁴`-honesty of the auxiliary block `AK α = (Γ(θ)/c α)·2z²/(1+z)³`.**

`AK α` is a *separable* datum `ρ(z)·Γ(θ)` with `ρ z = 2z²/(1+z)³/c α`.  The `ℋ⁴`-integrand of a
separable datum is dominated by `((k+1) + (k+1)²·Rθ)·R·angMaj α θ/(1+z)²`
(`LocDataExt.HkIntegrand_sepGam_le`), where `R` prices the radial jets of `ρ`
(`AkRhoJetBasic.akRho_jet_bound`, `R = 100·720²` after the loss `1/c ≤ 10`) and `Rθ = 10¹⁰`
prices the angular jets of `Γ` (`LocDataExt.hGam5`).  Since `angMaj α` is integrable on `Iθ`
and `z ↦ (1/(1+z))²` is integrable on `Iz`, `HkMem_of_majorant` applies. -/
theorem HkMem_AK (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.HkMem α 4 (Work.Construction.AK α) := by
  obtain ⟨hc1, _hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  obtain ⟨R₀, hR₀0, hB₀⟩ := Work.FTS.NonlinRows.AkRhoJetBasic.akRho_jet_bound
  have hR0 : (0 : ℝ) ≤ 100 * R₀ := by linarith
  -- the radial jet bound for the normalised profile `ρ z = 2z²/(1+z)³/c α`
  have hB : ∀ j ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ' : ℝ,
      (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) z θ'
          * Work.Spaces.w z) ^ 2 ≤ 100 * R₀ / (1 + z) ^ 2 := by
    intro j hj z hz θ'
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
    · subst h0
      have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
      rw [hw0, mul_zero, sq, zero_mul]
      exact div_nonneg hR0 (by norm_num)
    · have hfun : (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α)
          = fun z _ : ℝ => (1 / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) := by
        funext z θ''
        ring
      have hmult := congrFun (congrFun (Work.FTS.Nonlinear.Pieces.RowsN0Aux.DzIter_const_mul j
        (1 / Work.Spaces.c α) (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3)) z) θ'
      rw [hfun, hmult]
      have hc10 : (1 / Work.Spaces.c α) ≤ 10 := by
        rw [div_le_iff₀ hc0]
        linarith
      have hsq : (1 / Work.Spaces.c α) ^ 2 ≤ 100 := by
        have h1 : (0 : ℝ) ≤ 1 / Work.Spaces.c α := by positivity
        nlinarith [hc10, h1]
      calc ((1 / Work.Spaces.c α)
              * Work.Spaces.DzIter j (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) z θ'
              * Work.Spaces.w z) ^ 2
          = (1 / Work.Spaces.c α) ^ 2
              * (Work.Spaces.DzIter j (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) z θ'
                * Work.Spaces.w z) ^ 2 := by ring
        _ ≤ 100 * (R₀ / (1 + z) ^ 2) :=
            mul_le_mul hsq (hB₀ j hj hzpos θ') (sq_nonneg _) (by norm_num)
        _ = 100 * R₀ / (1 + z) ^ 2 := by ring
  -- the angular jet bound for `Γ`
  have hΓ : ∀ i ≤ 4, ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ') ^ 2 := by
    intro i hi θ' hθ'
    exact Work.FTS.LocDataExt.hGam5 α hα hα1 (by omega) hθ'
  -- `AK α` is the separable datum `ρ(z)·Γ(θ)`
  have hAK : Work.Construction.AK α = fun z θ =>
      (2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
    funext z θ
    rw [Work.Construction.AK]
    ring
  refine Work.FTS.LocData.HkMem_of_majorant
    (M := fun z θ => (((5 : ℝ) + 25 * (10 : ℝ) ^ 10) * (100 * R₀) / (1 + z) ^ 2)
      * Work.FTS.LocData.angMaj α θ) α 4
    (Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn (F := Work.Construction.AK α) α
      (n := 4) (k := 4) le_rfl (Work.FTS.OpenPkg.contDiffOn_four_AK α hα hα1)) ?_ ?_ ?_
  · -- the `θ`-slices of the majorant are integrable
    intro z _hz
    exact ((Work.FTS.LocData.angMaj_mem α hα hα1).1).const_mul
      (((5 : ℝ) + 25 * (10 : ℝ) ^ 10) * (100 * R₀) / (1 + z) ^ 2)
  · -- the `z`-integral of the majorant is integrable
    have hkey : IntegrableOn (fun z : ℝ => (((5 : ℝ) + 25 * (10 : ℝ) ^ 10) * (100 * R₀)
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        (Set.Ioi 0) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul
        (((5 : ℝ) + 25 * (10 : ℝ) ^ 10) * (100 * R₀)
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ))
    have hkeyIz : IntegrableOn (fun z : ℝ => (((5 : ℝ) + 25 * (10 : ℝ) ^ 10) * (100 * R₀)
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        (Set.Ici 0) :=
      hkey.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have heqfun : (fun z : ℝ => (((5 : ℝ) + 25 * (10 : ℝ) ^ 10) * (100 * R₀)
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        = fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            (((5 : ℝ) + 25 * (10 : ℝ) ^ 10) * (100 * R₀) / (1 + z) ^ 2)
              * Work.FTS.LocData.angMaj α θ := by
      funext z
      rw [MeasureTheory.integral_const_mul]
      rw [one_div, inv_pow, div_eq_mul_inv]
      ring
    rw [← heqfun]
    exact hkeyIz
  · -- the pointwise domination
    intro z hz θ hθ
    rw [hAK]
    have h1 := Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 4 hR0 (by norm_num) hB hΓ hz hθ
    refine le_trans h1 (le_of_eq ?_)
    rw [div_eq_mul_inv]
    norm_num
    ring


end Work.FTS.NonlinRows
