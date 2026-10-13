import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Open.Row23

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option linter.unusedVariables false

/-- **Priced row 23**: the `ℋ⁴`-honesty and the `α³`-bound of the profile-only star piece
`N₄^{**} = -(1/2) sin(2θ) · FK(F_*) · ∂_θF_*`, with a *constant* independent of all data.

This piece does not involve `g`, `Φs` or `Φg` at all: it is the explicit function
`-(2α²/c(α)) · (sin(2θ) · ∂_θΓ(θ)) · (z²/(1+z)⁴)`, an angular `×` radial product.  The
corresponding row of the open vocabulary is `Work.FTS.Nonlinear.Open.Row23`, whose statement
carries the interfaces `N4Norm'`, `N4Extra'`, `GalClass α g`, `StarPkgo α Cs Φs`, `EllPkgGo α Ce g Φg`
and the three hypotheses `0 < α`, `α ≤ 1`, `α ≤ α₂` — but its proof uses *only* `0 < α` and
`α ≤ 1` (the remaining hypotheses are never touched: the body works with the explicit
factorisation `N4ss α = fun z θ => a θ * r z`, the angular `D_θ`-iterates of
`sin²θ`-type profiles and `Work.Spaces.hKer`; the constants are `Csh`, `Cr` of the
`AngRadHkMem`/`hkerSq_radial_alt` machinery and are independent of every hypothesis).  So the
proof is a verbatim copy of that proof with the interface hypotheses dropped. -/
theorem N4ssPriced : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4ss α) ∧
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4ss α) ≤ C * α ^ 3 := by
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp
  obtain ⟨Cr, hCrpos, hCr⟩ := Work.FTS.Nonlinear.Pieces.RNP.hkerSq_radial_alt
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
  refine ⟨Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) * Cr + 1, ?_, ?_⟩
  · have h1 : 0 ≤ Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) := Real.sqrt_nonneg _
    nlinarith [hCrpos]
  · intro α hαIoc
    have hα : 0 < α := hαIoc.1
    have hα1 : α ≤ 1 := hαIoc.2
    -- the weight `c(α)` of the fundamental solution is bounded below by `1/10`
    have hcge : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    -- the angular profile, the radial profile, and their angular majorant
    set a : ℝ → ℝ := fun θ => (-(2 * α ^ 2 / Work.Spaces.c α))
      * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ with ha
    set r : ℝ → ℝ := fun z => (Work.Spaces.hKer z) ^ 2 with hr
    set G : ℝ → ℝ := fun θ => Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) with hG
    -- ### 1. the factorisation `N₄^{**} = a(θ)·r(z)`
    have hid : Work.FTS.Nonlin.N4ss α = fun z θ => a θ * r z := by
      funext z θ
      rw [Work.FTS.Nonlin.N4ss]
      have hpth : Work.Spaces.pth (Work.Construction.Fstar α) z θ
          = (α * Work.FM.Fstar z / Work.Spaces.c α)
            * deriv (fun t => Work.Spaces.Gam α t) θ := by
        rw [Work.Spaces.pth]
        rw [show (fun θ' => Work.Construction.Fstar α z θ')
            = fun θ' => (α * Work.FM.Fstar z / Work.Spaces.c α)
                * Work.Spaces.Gam α θ' from by
          funext θ'; rw [Work.Construction.Fstar]; ring]
        rw [Work.Spaces.deriv_const_mul']
      rw [Work.FTS.Nonlin.FK_Fstar hα hα1, hpth]
      simp only [ha, hr, Work.Spaces.dthU_apply, Work.Spaces.hKer_apply, Work.FM.Fstar,
        Work.Construction.s2]
      ring_nf
    -- ### 2. the bounds on the two profiles
    have hc2 : 2 * α ^ 2 / Work.Spaces.c α ≤ 20 * α ^ 2 := by
      rw [div_le_iff₀ hcpos]
      nlinarith [hcge, sq_nonneg α, hα]
    have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ := by
      intro θ hθ
      have h1 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have h2 : 0 ≤ Real.sin (2 * θ) :=
        Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
      rw [hG]
      positivity
    have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ 27 * α ^ 3 := by
      intro θ hθ
      have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hΓ1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
      have hdth := Work.FTS.Nonlinear.Pieces.RNP.dthIter_one_Gam_le hα hα1 θ hθ
      have hrepr : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
          Function.iterate_one]
      have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
          ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by rw [hrepr]; exact hdth
      have hc2' : (0 : ℝ) ≤ 2 * α ^ 2 / Work.Spaces.c α :=
        div_nonneg (by positivity) hcpos.le
      have habs : |a θ| = (2 * α ^ 2 / Work.Spaces.c α)
          * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ| := by
        simp only [ha]
        rw [abs_mul, abs_neg, abs_of_nonneg hc2']
      rw [habs]
      calc (2 * α ^ 2 / Work.Spaces.c α)
              * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
          ≤ (2 * α ^ 2 / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
            mul_le_mul_of_nonneg_left hb hc2'
        _ ≤ (20 * α ^ 2) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
            mul_le_mul_of_nonneg_right hc2 (by positivity)
        _ ≤ 27 * α ^ 3 := by
          have hα3 : (0 : ℝ) ≤ α ^ 3 := by positivity
          have h := mul_le_mul_of_nonneg_left hΓ1
            (by positivity : (0 : ℝ) ≤ (80 / 3) * α ^ 3)
          nlinarith [h, hα3]
    have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ (20 * Cg * α ^ 3) * G θ := by
      intro i hi hi4 θ hθ
      have hrepr : Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ
          = (-(2 * α ^ 2 / Work.Spaces.c α))
            * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq i a 0 θ]
        simp only [ha]
        rw [Work.Spaces.dthU_iter_const_mul, Work.Spaces.dthU_iter_comp]
      have hchild := hCg α hα hα1 θ hθ (i + 1) (by omega) (by omega)
      have hc2' : (0 : ℝ) ≤ 2 * α ^ 2 / Work.Spaces.c α :=
        div_nonneg (by positivity) hcpos.le
      have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hsin0 : 0 ≤ Real.sin (2 * θ) :=
        Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
      have hGunfold : G θ = Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by rw [hG]
      rw [hrepr, abs_mul, abs_neg, abs_of_nonneg hc2', hGunfold]
      have h1 : (2 * α ^ 2 / Work.Spaces.c α)
            * |Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
          ≤ (2 * α ^ 2 / Work.Spaces.c α)
            * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
        mul_le_mul_of_nonneg_left hchild hc2'
      have h2 : (2 * α ^ 2 / Work.Spaces.c α)
            * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
          ≤ (20 * Cg * α ^ 3) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
        rw [show (2 * α ^ 2 / Work.Spaces.c α)
              * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
            = ((2 * α ^ 2 / Work.Spaces.c α) * Cg * α)
              * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) from by ring]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (2 * α ^ 2 / Work.Spaces.c α) * Cg * α
            = (2 * α ^ 2 / Work.Spaces.c α) * (Cg * α) := by ring
          _ ≤ (20 * α ^ 2) * (Cg * α) :=
              mul_le_mul_of_nonneg_right hc2 (by positivity)
          _ = 20 * Cg * α ^ 3 := by ring
      exact h1.trans h2
    -- ### 3. the `θ`-mass of the angular profile
    obtain ⟨hI1raw, hm1raw⟩ := hM α hα hα1
    have hGae : (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
        = fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ := by
      funext θ; rw [hG]; ring
    have hI1 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
        Work.Spaces.Iθ := by rw [hGae]; exact hI1raw
    have hm1 : ∫ θ in Work.Spaces.Iθ, G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ
        ≤ M := by rw [hGae]; exact hm1raw
    -- ### 4. the radial function
    obtain ⟨hrmemR, hXnR⟩ := hCr α hα hα1
    have hrmem : Work.Spaces.HkMem α 4 (fun z θ => r z) := by rw [hr]; exact hrmemR
    have hXnR' : Work.FTS.Nonlin.Xn α (fun z θ => r z) ≤ Cr := by rw [hr]; exact hXnR
    -- ### 5. the smoothness of the two factors (for the `ℋ⁴`-honesty)
    have ha_sm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) := by
      simp only [ha]
      exact contDiffOn_const.mul (Work.FTS.Nonlinear.Open.row23_smoothOpen_dthU_Gam α)
    have hr_sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) := by
      simp only [hr]
      exact Work.FTS.Nonlinear.Open.row23_smoothOpen_radial
        (fun n => (Work.FTS.Nonlinear.Open.row23_contDiffOn_hKer n).pow 2)
    have hHk : Work.Spaces.HkMem α 4 (fun z θ => a θ * r z) :=
      Work.FTS.Nonlinear.Open.AngRadHkMem (α := α) (a := a) (r := r) (G := G)
        (B0 := 27 * α ^ 3) (B1 := 20 * Cg * α ^ 3) ha_sm hr_sm hGnn hI1 ha0 ha1 hrmem
    -- ### 6. the separated `ℋ⁴`-estimate
    have hmain := Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα a r G
      (B0 := 27 * α ^ 3) (B1 := 20 * Cg * α ^ 3) (M1 := M) (by positivity) (by positivity)
      (le_of_lt hMpos) hGnn ha0 ha1 hI1 hm1 hrmem
    -- ### 7. the arithmetic
    have hsqrt : Real.sqrt ((27 * α ^ 3) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 3) ^ 2 * M)
        = α ^ 3 * Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) := by
      rw [show (27 * α ^ 3) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 3) ^ 2 * M
          = (α ^ 3) ^ 2 * (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) from by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    constructor
    · rw [hid]; exact hHk
    · rw [hid]
      calc Work.FTS.Nonlin.Xn α (fun z θ => a θ * r z)
          ≤ Real.sqrt ((27 * α ^ 3) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 3) ^ 2 * M)
              * Work.FTS.Nonlin.Xn α (fun z θ => r z) := hmain
        _ ≤ Real.sqrt ((27 * α ^ 3) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 3) ^ 2 * M) * Cr :=
            mul_le_mul_of_nonneg_left hXnR' (Real.sqrt_nonneg _)
        _ = α ^ 3 * (Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) * Cr) := by
            rw [hsqrt]; ring
        _ ≤ (Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) * Cr + 1) * α ^ 3 := by
            nlinarith [sq_nonneg α, le_of_lt hα]

end Work.FTS.StrongPersist.L3Rhs
