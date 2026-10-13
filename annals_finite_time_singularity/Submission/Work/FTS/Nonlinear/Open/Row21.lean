/-
# Row 21 of the §8 design table, open-quadrant (primed) form

`N₄^{gs}(z,θ) = -(1/2) sin(2θ) FK(g)(z) ∂_θF_*(z,θ)`.  Since `∂_θF_* = D_θF_*/sin(2θ)`, the
piece factors as a product of an angular profile and a radial function,

  `N₄^{gs} = A(θ) · r(z)`,  `A(θ) = -(α / c α) · D_θΓ(θ)`,  `r(z) = FK g z · hKer z`,

where `hKer z = z/(1+z)²` and `Γ = Gam α` (this is `RNP.N4gs_factor`, unconditional).

* the `ℋ⁴`-honesty conjunct is the angular × radial separation lemma `HkMem_ang_rad_le`:
  `|A| ≤ 27α²`, the `D_θ`-iterates of `A` are `≤ 20 C α² · Γ(α+sin 2θ)`
  (`dthIter_one_Gam_le`, `dthU_pow_Gam_sharp`), `Γ(α+sin 2θ)² · sin(2θ)^{-γ}` is integrable
  (`gamWeightInt`), `sin(2θ)^{-η}` is integrable (`sin_two_rpow`), and the radial factor is
  honest by `FKhKerProd`;
* the norm bound is the separation estimate `XnAngProfHKer`
  (`|A·r|_{ℋ⁴} ≤ α²K₂·|r|_{ℋ⁴}`) together with `|FK g·hKer|_{ℋ⁴} ≤ 10¹²·|g|_{ℋ⁴}`
  (`FKhKerProd`); `α² ≤ α^{3/2}` for `α ≤ 1` finishes.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row21
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row25
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.PhiStar.Psi0Est.exists_AClass
import Submission.Work.FTS.NonlinRows.AngRad.HkMem_ang_rad_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-! ## The continuity of the angular and radial iterates of the two factors -/

/-- The angular profile `A θ = -(α/c α)·dthU Γ(θ)` has continuous `D_θ`-iterates of order `≤ 4`
on the open angular interval. -/
private theorem contDthIter_angProf {α : ℝ} (hα : 0 < α) :
    ∀ i : ℕ, i ≤ 4 → ContinuousOn
      (fun θ : ℝ => Work.Spaces.DthIter i
        (fun _ (θ' : ℝ) => -(α / Work.Spaces.c α)
          * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ') 0 θ)
      (Set.Ioo 0 (π / 2)) := by
  intro i _
  have hrepr : (fun θ : ℝ => Work.Spaces.DthIter i
        (fun _ (θ' : ℝ) => -(α / Work.Spaces.c α)
          * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ') 0 θ)
      = fun θ : ℝ => -(α / Work.Spaces.c α)
          * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ := by
    funext θ
    rw [Work.FTS.LocData.DthIter_rad_eq i
        (fun θ' => -(α / Work.Spaces.c α)
          * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ') 0 θ,
      Work.Spaces.dthU_iter_const_mul, Work.Spaces.dthU_iter_comp]
  rw [hrepr]
  have hc := (Work.FTS.PhiStar.Psi0Est.contDiffOn_dthU_iter_aux
    (Work.FTS.LocData.contDiffOn_Gam_Ioo α) (i + 1)).continuousOn
  exact continuousOn_const.mul hc

/-- The radial profile `r z = FK g z · hKer z` has continuous `D_z`-iterates of order `≤ 4` on
`(0,∞)`: `FK g` is `C⁴` there (`RNP24.fk_contDiffOn_four`), `hKer z = z/(1+z)²` is smooth, and
each `DzdIter b` lowers the order by one. -/
private theorem contDzdIter_FKhKer {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 6 g) :
    ∀ b : ℕ, b ≤ 4 → ContinuousOn
      (fun z : ℝ => Work.Elliptic.DzdIter b
        (fun z => Work.Construction.FK g z * Work.Spaces.hKer z) z) (Set.Ioi 0) := by
  have hFK : ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z) (Set.Ioi 0) :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four hα hα1 hsm hmem
  have hker : ContDiffOn ℝ 4 (fun z : ℝ => Work.Spaces.hKer z) (Set.Ioi 0) := by
    have hfun : (fun z : ℝ => Work.Spaces.hKer z) = fun z : ℝ => z / (1 + z) ^ 2 := by
      funext z; rw [Work.Spaces.hKer_apply]
    rw [hfun]
    refine ContDiffOn.div contDiffOn_id ((contDiffOn_const.add contDiffOn_id).pow 2) ?_
    intro z hz
    have h : (0 : ℝ) < 1 + z := by have := Set.mem_Ioi.mp hz; linarith
    exact pow_ne_zero 2 (ne_of_gt h)
  have h4 : ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z * Work.Spaces.hKer z)
      (Set.Ioi 0) := hFK.mul hker
  intro b hb
  have hc := Work.FTS.Nonlinear.Pieces.RNP.contDiffOn_dzdIter_of h4 b hb
  have h0 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
      (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK g z * Work.Spaces.hKer z))
      (Set.Ioi 0) := hc.of_le (by simp)
  exact (contDiffOn_zero (𝕜 := ℝ)).mp h0

theorem Row21 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4gs α g) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g) ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp
  obtain ⟨K₂, hK₂pos, hK₂⟩ := Work.FTS.Nonlinear.Pieces.RNP.XnAngProfHKer
  refine ⟨10 ^ 12 * K₂ + 1, by positivity, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hgal hstar hell
  have hsm : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 g := hgal.reg.2.1
  have hR : ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z) (Set.Ioi 0) :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four hα hα1 hsm hmem6
  obtain ⟨hmemR, hXnR⟩ := Work.FTS.Nonlinear.Pieces.RNP.FKhKerProd hα hα1 hsm hmem6 hR
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  -- the two factors
  set A : ℝ → ℝ := fun θ => -(α / Work.Spaces.c α)
    * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ with hA
  set R : ℝ → ℝ := fun z => Work.Construction.FK g z * Work.Spaces.hKer z with hRdef
  -- the factorisation of the piece
  have hfac : Work.FTS.Nonlin.N4gs α g = fun z θ => A θ * R z := by
    rw [Work.FTS.Nonlinear.Pieces.RNP.N4gs_factor α g, hA, hRdef]
  -- ## the size of the angular profile
  have hcge : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcnn : (0 : ℝ) ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  have hc2 : α / Work.Spaces.c α ≤ 10 * α := by
    rw [div_le_iff₀ hcpos]; nlinarith [hcge, hα]
  have hGnn : ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by
    intro θ hθ
    have h1 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have h2 : 0 ≤ Real.sin (2 * θ) := Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    positivity
  have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |A θ| ≤ 27 * α ^ 2 := by
    intro θ hθ
    have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hΓ1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by
      have hrepr : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
          Function.iterate_one]
      rw [hrepr]
      exact Work.FTS.Nonlinear.Pieces.RNP.dthIter_one_Gam_le hα hα1 θ hθ
    have habs : |A θ| = (α / Work.Spaces.c α)
        * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ| := by
      rw [hA]
      rw [abs_mul, abs_neg, abs_of_nonneg hcnn]
    rw [habs]
    calc (α / Work.Spaces.c α) * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (α / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_left hb hcnn
      _ ≤ (10 * α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_right hc2 (mul_nonneg (by positivity) hΓ0)
      _ ≤ 27 * α ^ 2 := by
          have h := mul_le_mul_of_nonneg_left hΓ1 (by positivity : (0 : ℝ) ≤ (40 / 3) * α ^ 2)
          nlinarith [h, sq_nonneg α]
  have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => A θ') 0 θ|
        ≤ (20 * Cg * α ^ 2) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
    intro i hi hi4 θ hθ
    have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hsin2 : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    have hrepr : Work.Spaces.DthIter i (fun _ (θ' : ℝ) => A θ') 0 θ
        = (-(α / Work.Spaces.c α))
          * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ := by
      rw [Work.FTS.LocData.DthIter_rad_eq i A 0 θ, hA]
      rw [Work.Spaces.dthU_iter_const_mul, Work.Spaces.dthU_iter_comp]
    rw [hrepr, abs_mul, abs_neg, abs_of_nonneg hcnn]
    have hchild := hCg α hα hα1 θ hθ (i + 1) (by omega) (by omega)
    have h1 : (α / Work.Spaces.c α)
          * |Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ (α / Work.Spaces.c α)
          * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
      mul_le_mul_of_nonneg_left hchild hcnn
    have h2 : (α / Work.Spaces.c α)
          * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
        ≤ (20 * Cg * α ^ 2) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
      rw [show (α / Work.Spaces.c α)
            * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
          = ((α / Work.Spaces.c α) * Cg * α)
            * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) from by ring]
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hΓ0 (by linarith [hα, hsin2]))
      calc (α / Work.Spaces.c α) * Cg * α = (α / Work.Spaces.c α) * (Cg * α) := by ring
        _ ≤ (10 * α) * (Cg * α) := mul_le_mul_of_nonneg_right hc2 (by positivity)
        _ = 10 * Cg * α ^ 2 := by ring
        _ ≤ 20 * Cg * α ^ 2 := by nlinarith [hCgpos, sq_nonneg α]
    exact h1.trans h2
  -- ## the integrability of the two angular weights
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
  have hI1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ := by
    refine (hM α hα hα1).1.congr (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hI2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ) Work.Spaces.Iθ := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)).1
    simpa only [Work.FTS.Nonlinear.RadialProd.smE] using h
  constructor
  · -- ## the `ℋ⁴`-honesty conjunct
    rw [hfac]
    refine Work.FTS.NonlinRows.AngRad.HkMem_ang_rad_le (α := α)
      (a := A) (r := R) (B0 := 27 * α ^ 2) (B1 := 20 * Cg * α ^ 2)
      (G := fun θ => Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
      (by positivity) (by positivity) hGnn ha0 ha1 hI1 hI2 ?_ ?_ ?_
    · simpa only [hRdef] using hmemR
    · exact contDthIter_angProf hα
    · exact contDzdIter_FKhKer hα hα1 hsm hmem6
  · -- ## the norm bound
    have hstep : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g)
        ≤ α ^ 2 * K₂ * (10 ^ 12 * Work.FTS.Nonlin.Xn α g) := by
      rw [hfac]
      refine (hK₂ α hα hα1 R ?_).trans (mul_le_mul_of_nonneg_left hXnR (by positivity))
      simpa only [hRdef] using hmemR
    have hα32 : α ^ 2 ≤ α ^ (3 / 2 : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num : (3 / 2 : ℝ) ≤ 2)
      simpa using h
    refine hstep.trans ?_
    calc α ^ 2 * K₂ * (10 ^ 12 * Work.FTS.Nonlin.Xn α g)
        = (10 ^ 12 * K₂) * (α ^ 2 * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ (10 ^ 12 * K₂) * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hα32 hXn0) (by positivity)
      _ ≤ (10 ^ 12 * K₂ + 1) * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_right (by linarith)
            (mul_nonneg (Real.rpow_nonneg hα.le _) hXn0)

end Work.FTS.Nonlinear.Open
