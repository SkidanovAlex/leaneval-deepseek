import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.VocabO
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Open.AngRadHkMem
import Submission.Work.FTS.Nonlinear.Open.Row23

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

/-- `SmoothOpen` is preserved by multiplication of the angular variable by a constant. -/
private theorem smoothOpen_ang_const_mul {c : ℝ} {a : ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ)) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => c * a θ) :=
  ContDiffOn.const_smul (𝕜 := ℝ) c ha

/-- **The two `F_*`-products with the angular moment `FK (F_*)` are `ℋ⁴`-honest with bounded
`ℋ⁴`-norm (uniformly in `α ∈ (0,1]`).**

`FK (F_*) z = (F_*, K)_{L²_θ}(z) = ∫_θ F_* z θ · K(θ)` is the angular moment of the fundamental
profile; `Work.FTS.Nonlin.FK_Fstar` gives the explicit value
`FK (F_*) z = α·2z/(1+z)² = 2α·hKer z` where `hKer z = z/(1+z)²` (`Work.Spaces.hKer`), and
`F_* = α(Γ/c)·2hKer`, `D_θF_* = α(D_θΓ/c)·2hKer`.

Route: both products are separable angular `×` radial:
* `FK(F_*)·D_θF_* = (D_θΓ/c)(θ) · (4α² hKer²)(z)`,
* `FK(F_*)·F_*  = (Γ/c)(θ) · (4α² hKer²)(z)`,
so `Work.FTS.Nonlinear.Open.AngRadHkMem` applies (with the angular majorant
`G = Γ·(α + sin 2θ)` of `Row23`, i.e. `gamWeightInt`'s sharp data, and the radial input
`hkerSq_radial_alt` composed with `HkMem_const_mul`) and the norm bound follows from
`Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen`.  The pattern is `Row23` (which does
`N4ss = -(2α²/c)dθUΓ·hKer²`) and `NRow26`.  The constant may depend on `α` but must be uniform
over `α ∈ (0,1]`. -/
theorem StarAtomsFK : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    Work.FTS.VocabO.HQo α 4 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C ∧
    Work.FTS.VocabO.HQo α 4 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Construction.Fstar α z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Construction.Fstar α z θ) ≤ C := by
  obtain ⟨Cr, hCrpos, hCr⟩ := Work.FTS.Nonlinear.Pieces.RNP.hkerSq_radial_alt
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
  -- the two constants produced by the angular `×` radial engine, one for each product
  set K1 : ℝ := Real.sqrt ((160 / 3) ^ 2 * 10000 + 4 * (40 * Cg) ^ 2 * M) * Cr with hK1
  set K2 : ℝ := Real.sqrt (40 ^ 2 * 10000 + 4 * (160 / 3 + 40 * Cg) ^ 2 * M) * Cr with hK2
  have hK1nn : 0 ≤ K1 := by
    rw [hK1]; exact mul_nonneg (Real.sqrt_nonneg _) hCrpos.le
  have hK2nn : 0 ≤ K2 := by
    rw [hK2]; exact mul_nonneg (Real.sqrt_nonneg _) hCrpos.le
  refine ⟨K1 + K2 + 1, by linarith, fun α hαIoc => ?_⟩
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- the normalisation constant `c(α) ∈ [1/10, 10]`
  have hcge : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hc4 : 4 * α ^ 2 / Work.Spaces.c α ≤ 40 * α ^ 2 := by
    rw [div_le_iff₀ hcpos]; nlinarith [hcge, sq_nonneg α, hα]
  have hc4nn : (0 : ℝ) ≤ 4 * α ^ 2 / Work.Spaces.c α := div_nonneg (by positivity) hcpos.le
  have hDle40 : 4 * α ^ 2 / Work.Spaces.c α ≤ 40 := by
    have hα2 : α ^ 2 ≤ 1 := (pow_le_one₀ hα.le hα1 : α ^ 2 ≤ 1)
    nlinarith [hc4, sq_nonneg α]
  have hα3 : α ^ 3 ≤ 1 := (pow_le_one₀ hα.le hα1 : α ^ 3 ≤ 1)
  -- ### the radial profile `r = hKer²` and its `ℋ⁴`-data
  set r : ℝ → ℝ := fun z => (Work.Spaces.hKer z) ^ 2 with hr
  have hr_sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) := by
    rw [hr]
    exact Work.FTS.Nonlinear.Open.row23_smoothOpen_radial
      (fun n => (Work.FTS.Nonlinear.Open.row23_contDiffOn_hKer n).pow 2)
  obtain ⟨hrmemR, hXnR⟩ := hCr α hα hα1
  have hrmem : Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => r z) := by rw [hr]; exact hrmemR
  have hXnR' : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) ≤ Cr := by rw [hr]; exact hXnR
  -- ### the sharp angular majorant `G = Γ·(α + sin 2θ)`
  set G : ℝ → ℝ := fun θ => Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) with hG
  have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ := by
    intro θ hθ
    have h1 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have h2 : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    rw [hG]; positivity
  obtain ⟨hI1raw, hm1raw⟩ := hM α hα hα1
  have hGae : (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
      = fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    funext θ; rw [hG]; ring
  have hI1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ := by
    rw [hGae]; exact hI1raw
  have hm1 : ∫ θ in Work.Spaces.Iθ, G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ ≤ M := by
    rw [hGae]; exact hm1raw
  -- ### product 1: `FK(F_*)·D_θF_* = a₁(θ)·r(z)` with `a₁ = (4α²/c)·D_θΓ`
  set a1 : ℝ → ℝ := fun θ => (4 * α ^ 2 / Work.Spaces.c α)
    * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ with ha1
  have ha1_sm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a1 θ) := by
    rw [ha1]
    exact smoothOpen_ang_const_mul (Work.FTS.Nonlinear.Open.row23_smoothOpen_dthU_Gam α)
  have ha1_0 : ∀ θ ∈ Work.Spaces.Iθ, |a1 θ| ≤ 160 / 3 := by
    intro θ hθ
    rw [ha1]
    have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hΓ1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have hdth := Work.FTS.Nonlinear.Pieces.RNP.dthIter_one_Gam_le hα hα1 θ hθ
    have hrepr : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
        = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
      rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
        Function.iterate_one]
    have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by rw [hrepr]; exact hdth
    have habs : |(4 * α ^ 2 / Work.Spaces.c α)
          * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        = (4 * α ^ 2 / Work.Spaces.c α)
          * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ| := by
      rw [abs_mul, abs_of_nonneg hc4nn]
    rw [habs]
    calc (4 * α ^ 2 / Work.Spaces.c α) * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 * α ^ 2 / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_left hb hc4nn
      _ ≤ 40 * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_right hDle40 (by positivity)
      _ = (160 / 3) * α * Work.Spaces.Gam α θ := by ring
      _ ≤ 160 / 3 := by nlinarith [hα1, hΓ1, hΓ0, hα.le]
  have ha1_1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a1 θ') 0 θ| ≤ (40 * Cg) * G θ := by
    intro i hi1 hi4 θ hθ
    have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    have hprodnn : (0 : ℝ) ≤ Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) :=
      mul_nonneg hΓ0 (by linarith)
    have hrepr : Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a1 θ') 0 θ
        = (4 * α ^ 2 / Work.Spaces.c α)
          * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ := by
      rw [Work.FTS.LocData.DthIter_rad_eq i a1 0 θ]
      simp only [ha1]
      rw [Work.Spaces.dthU_iter_const_mul, Work.Spaces.dthU_iter_comp]
    rw [hrepr, abs_mul, abs_of_nonneg hc4nn, hG]
    have hb := hCg α hα hα1 θ hθ (i + 1) (by omega) (by omega)
    have hcoef : (4 * α ^ 2 / Work.Spaces.c α) * Cg * α ≤ 40 * Cg := by
      have h1 : (4 * α ^ 2 / Work.Spaces.c α) * Cg ≤ 40 * α ^ 2 * Cg :=
        mul_le_mul_of_nonneg_right hc4 hCgpos.le
      have h2 : (4 * α ^ 2 / Work.Spaces.c α) * Cg * α ≤ 40 * α ^ 2 * Cg * α :=
        mul_le_mul_of_nonneg_right h1 hα.le
      have h3 : 40 * α ^ 2 * Cg * α ≤ 40 * Cg := by
        rw [show 40 * α ^ 2 * Cg * α = 40 * Cg * α ^ 3 from by ring]
        exact mul_le_of_le_one_right (by positivity) hα3
      exact h2.trans h3
    calc (4 * α ^ 2 / Work.Spaces.c α)
          * |Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 * α ^ 2 / Work.Spaces.c α)
            * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_left hb hc4nn
      _ = ((4 * α ^ 2 / Work.Spaces.c α) * Cg * α)
            * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by ring
      _ ≤ (40 * Cg) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right hcoef hprodnn
  have hid1 : (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) = fun z θ => a1 θ * r z := by
    funext z θ
    have hFK : Work.Construction.FK (Work.Construction.Fstar α) z = α * Work.FM.Fstar z := by
      rw [Work.FTS.Nonlin.FK_Fstar hα hα1, Work.FM.Fstar]
    have hpth : Work.Spaces.pth (Work.Construction.Fstar α) z θ
        = (α * Work.FM.Fstar z / Work.Spaces.c α)
          * deriv (fun t => Work.Spaces.Gam α t) θ := by
      rw [Work.Spaces.pth]
      rw [show (fun θ' => Work.Construction.Fstar α z θ')
          = fun θ' => (α * Work.FM.Fstar z / Work.Spaces.c α) * Work.Spaces.Gam α θ' from by
        funext θ'; rw [Work.Construction.Fstar]; ring]
      rw [Work.Spaces.deriv_const_mul']
    rw [Work.Spaces.Dth, hFK, hpth]
    simp only [ha1, hr, Work.Spaces.dthU_apply, Work.Spaces.hKer_apply, Work.FM.Fstar]
    ring_nf
  have hHk1 : Work.Spaces.HkMem α 4 (fun z θ => a1 θ * r z) :=
    Work.FTS.Nonlinear.Open.AngRadHkMem (α := α) (a := a1) (r := r) (G := G)
      (B0 := 160 / 3) (B1 := 40 * Cg) ha1_sm hr_sm hGnn hI1 ha1_0 ha1_1 hrmem
  have hXn1 : Work.FTS.Nonlin.Xn α (fun z θ => a1 θ * r z)
      ≤ Real.sqrt ((160 / 3) ^ 2 * 10000 + 4 * (40 * Cg) ^ 2 * M) * Cr := by
    have hmain := Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα a1 r G
      (B0 := 160 / 3) (B1 := 40 * Cg) (M1 := M) (by norm_num) (by positivity)
      hMpos.le hGnn ha1_0 ha1_1 hI1 hm1 hrmem
    exact hmain.trans (mul_le_mul_of_nonneg_left hXnR' (Real.sqrt_nonneg _))
  -- ### product 2: `FK(F_*)·F_* = a₂(θ)·r(z)` with `a₂ = (4α²/c)·Γ`
  set a2 : ℝ → ℝ := fun θ => (4 * α ^ 2 / Work.Spaces.c α) * Work.Spaces.Gam α θ with ha2
  have ha2_sm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a2 θ) := by
    rw [ha2]
    exact smoothOpen_ang_const_mul (Work.FTS.Nonlinear.Open.row23_smoothOpen_Gam α)
  have ha2_0 : ∀ θ ∈ Work.Spaces.Iθ, |a2 θ| ≤ 40 := by
    intro θ hθ
    rw [ha2]
    have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hΓ1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
    rw [abs_mul, abs_of_nonneg hc4nn, abs_of_nonneg hΓ0]
    calc (4 * α ^ 2 / Work.Spaces.c α) * Work.Spaces.Gam α θ
        ≤ 40 * Work.Spaces.Gam α θ := mul_le_mul_of_nonneg_right hDle40 hΓ0
      _ ≤ 40 := by nlinarith [hΓ1]
  have ha2_1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a2 θ') 0 θ|
        ≤ (160 / 3 + 40 * Cg) * G θ := by
    intro i hi1 hi4 θ hθ
    have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    have hprodnn : (0 : ℝ) ≤ Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) :=
      mul_nonneg hΓ0 (by linarith)
    have hrepr : Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a2 θ') 0 θ
        = (4 * α ^ 2 / Work.Spaces.c α)
          * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ := by
      rw [Work.FTS.LocData.DthIter_rad_eq i a2 0 θ]
      simp only [ha2]
      rw [Work.Spaces.dthU_iter_const_mul]
    rw [hrepr, abs_mul, abs_of_nonneg hc4nn, hG]
    have hcoef : (4 * α ^ 2 / Work.Spaces.c α) * Cg * α ≤ 40 * Cg := by
      have h1 : (4 * α ^ 2 / Work.Spaces.c α) * Cg ≤ 40 * α ^ 2 * Cg :=
        mul_le_mul_of_nonneg_right hc4 hCgpos.le
      have h2 : (4 * α ^ 2 / Work.Spaces.c α) * Cg * α ≤ 40 * α ^ 2 * Cg * α :=
        mul_le_mul_of_nonneg_right h1 hα.le
      have h3 : 40 * α ^ 2 * Cg * α ≤ 40 * Cg := by
        rw [show 40 * α ^ 2 * Cg * α = 40 * Cg * α ^ 3 from by ring]
        exact mul_le_of_le_one_right (by positivity) hα3
      exact h2.trans h3
    rcases eq_or_lt_of_le hi1 with h1 | h1
    · -- `i = 1`: the first-order bound `|D_θ Γ| ≤ (4/3)αΓ` suffices
      subst h1
      rw [Function.iterate_one]
      have hdth := Work.FTS.Nonlinear.Pieces.RNP.dthIter_one_Gam_le hα hα1 θ hθ
      have hrepr1 : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
          Function.iterate_one]
      have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
          ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by rw [hrepr1]; exact hdth
      calc (4 * α ^ 2 / Work.Spaces.c α)
            * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
          ≤ (4 * α ^ 2 / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
            mul_le_mul_of_nonneg_left hb hc4nn
        _ ≤ 40 * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
            mul_le_mul_of_nonneg_right hDle40 (by positivity)
        _ = (160 / 3) * α * Work.Spaces.Gam α θ := by ring
        _ ≤ (160 / 3) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
            nlinarith [mul_nonneg hΓ0 hsin0]
        _ ≤ (160 / 3 + 40 * Cg) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_right (by linarith) hprodnn
    · -- `i ≥ 2`: the sharp iterate bound
      have hb := hCg α hα hα1 θ hθ i (by omega) (by omega)
      calc (4 * α ^ 2 / Work.Spaces.c α)
            * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
          ≤ (4 * α ^ 2 / Work.Spaces.c α)
              * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_left hb hc4nn
        _ = ((4 * α ^ 2 / Work.Spaces.c α) * Cg * α)
              * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by ring
        _ ≤ (40 * Cg) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_right hcoef hprodnn
        _ ≤ (160 / 3 + 40 * Cg) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_right (by linarith) hprodnn
  have hid2 : (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ) = fun z θ => a2 θ * r z := by
    funext z θ
    have hFK : Work.Construction.FK (Work.Construction.Fstar α) z = α * Work.FM.Fstar z := by
      rw [Work.FTS.Nonlin.FK_Fstar hα hα1, Work.FM.Fstar]
    rw [hFK]
    simp only [ha2, hr, Work.Construction.Fstar, Work.Spaces.hKer_apply, Work.FM.Fstar]
    ring_nf
  have hHk2 : Work.Spaces.HkMem α 4 (fun z θ => a2 θ * r z) :=
    Work.FTS.Nonlinear.Open.AngRadHkMem (α := α) (a := a2) (r := r) (G := G)
      (B0 := 40) (B1 := 160 / 3 + 40 * Cg) ha2_sm hr_sm hGnn hI1 ha2_0 ha2_1 hrmem
  have hXn2 : Work.FTS.Nonlin.Xn α (fun z θ => a2 θ * r z)
      ≤ Real.sqrt (40 ^ 2 * 10000 + 4 * (160 / 3 + 40 * Cg) ^ 2 * M) * Cr := by
    have hmain := Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα a2 r G
      (B0 := 40) (B1 := 160 / 3 + 40 * Cg) (M1 := M) (by norm_num) (by linarith)
      hMpos.le hGnn ha2_0 ha2_1 hI1 hm1 hrmem
    exact hmain.trans (mul_le_mul_of_nonneg_left hXnR' (Real.sqrt_nonneg _))
  -- ### assembly
  have hQ1 : Work.FTS.VocabO.HQo α 4 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) := by
    rw [hid1]
    exact ⟨Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad ha1_sm hr_sm, hHk1⟩
  have hQ2 : Work.FTS.VocabO.HQo α 4 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Construction.Fstar α z θ) := by
    rw [hid2]
    exact ⟨Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad ha2_sm hr_sm, hHk2⟩
  refine ⟨hQ1, ?_, hQ2, ?_⟩
  · rw [hid1, hK1]
    linarith [hXn1, hK2nn]
  · rw [hid2, hK2]
    linarith [hXn2, hK1nn]

end

end Work.FTS.StrongEps.ClassCRHS
