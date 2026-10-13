import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row23
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.NonlinRows.AuxAngRad.AngRadWeights
import Submission.Work.FTS.Nonlinear.Open.AngRadHkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

set_option linter.unusedVariables false

/-! ## Smoothness of a radial factor and of the angular profile `dthU Γ`

The two facts used to feed the `ℋ⁴`-honesty of `N₄^{**} = a(θ)·r(z)` into the angular `×` radial
product lemma. -/

/-- A radial function smooth on `(0,∞)` gives a `SmoothOpen` function of `z` alone. -/
theorem row23_smoothOpen_radial {r : ℝ → ℝ}
    (hr : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => r z) (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  exact (hr n).comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- `Γ(θ) = (sinθ·cos²θ)^{α/3}` is `C^∞` on the open quadrant. -/
theorem row23_smoothOpen_Gam (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Spaces.Gam α θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hbase : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2) Work.FTS.EllipticEst.Q0 :=
    (((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top
  have hpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin p.2 * Real.cos p.2 ^ 2 := by
    intro p hp
    have hp' := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hp'.2.1, Real.pi_pos]) (by linarith [hp'.2.2, Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp'.2.1, Real.pi_pos], hp'.2.2⟩
    positivity
  exact hbase.rpow_const_of_ne (fun p hp => ne_of_gt (hpos p hp))

/-- The angular profile `dthU Γ = sin(2θ)·Γ'` is `C^∞` on the open quadrant. -/
theorem row23_smoothOpen_dthU_Gam (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun _ (θ : ℝ) => Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ) := by
  have h : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (fun _ (θ : ℝ) => Work.Spaces.Gam α θ)) :=
    (row23_smoothOpen_Gam α).Dth
  refine h.congr (fun p _ => ?_)
  simp only [Work.Spaces.Dth, Work.Spaces.pth, Work.Spaces.dthU_apply, Function.uncurry]

/-- `hKer z = z/(1+z)²` is `C^∞` on `(0,∞)`. -/
theorem row23_contDiffOn_hKer :
    ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => Work.Spaces.hKer z) (Set.Ioi 0) := by
  intro n
  have h : ContDiffOn ℝ n (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi 0) :=
    contDiffOn_id.div ((contDiffOn_const.add contDiffOn_id).pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt (by linarith [Set.mem_Ioi.mp hz])))
  simpa only [Work.Spaces.hKer_apply] using h

theorem Row23 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4ss α) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4ss α) ≤ K * (α ^ 3) := by
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp
  obtain ⟨Cr, hCrpos, hCr⟩ := Work.FTS.Nonlinear.Pieces.RNP.hkerSq_radial_alt
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
  refine ⟨Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) * Cr + 1, ?_, ?_⟩
  · have h1 : 0 ≤ Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) := Real.sqrt_nonneg _
    nlinarith [hCrpos]
  · intro α g Φs Φg hα hα1 hαα₂ hgal hstar hell
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
      exact contDiffOn_const.mul (row23_smoothOpen_dthU_Gam α)
    have hr_sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) := by
      simp only [hr]
      exact row23_smoothOpen_radial (fun n => (row23_contDiffOn_hKer n).pow 2)
    have hHk : Work.Spaces.HkMem α 4 (fun z θ => a θ * r z) :=
      AngRadHkMem (α := α) (a := a) (r := r) (G := G) (B0 := 27 * α ^ 3)
        (B1 := 20 * Cg * α ^ 3) ha_sm hr_sm hGnn hI1 ha0 ha1 hrmem
    -- ### 6. the separated `ℋ⁴`-estimate
    have hmain := Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα a r G (B0 := 27 * α ^ 3)
      (B1 := 20 * Cg * α ^ 3) (M1 := M) (by positivity) (by positivity) (le_of_lt hMpos)
      hGnn ha0 ha1 hI1 hm1 hrmem
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

end Work.FTS.Nonlinear.Open
