import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.OpenPkg.FourFactors
import Submission.Work.FTS.OpenPkg.angmul_field
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.HkSq_congr_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Local helpers (pointwise and `ℋ⁴`-level facts about the factors of row 5)

Row 5 of the §8 table is the piece `N₀₅ᵃ = -c2m(θ)·L₁₂(g)(z)·D_zF_*`, i.e. the product of the
`𝒲^{4,∞}`-factor `D_zF_*` (with norm `≤ Cα`, `Work.FTS.Nonlin.DzFstar_W`) with the `ℋ⁴`-coefficient
`c2m(θ)·L₁₂(g)(z)`.  The plan is therefore the `wprod` clause of `N4Norm'` (which prices the
`𝒲^{4,∞}`-factor by `α^{-1/2}·α = √α` and yields both the honesty and the bound of the piece),
applied to the coefficient `c2m·L₁₂(g)`, whose `ℋ⁴`-honesty and norm bound come from
`Work.FTS.OpenPkg.angmul_field` (multiplication by the bounded angular profile `c2m` is honest
with an absolute constant, so no knowledge of `Ci` is needed) together with `N4Norm'.l12H`. -/

/-- `c2m(θ) = cos 2θ - sin²θ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_c2m : Work.FTS.EllipticEst.SmoothOpen
    (fun (_ : ℝ) (θ : ℝ) => Work.Construction.c2m θ) :=
  Work.FTS.EllipticEst.smoothOpen_of_forall fun n => Work.FTS.OpenPkg.contDiffOn_c2m_Q0 n

/-- The `D_θ`-iterates of `c2m` are `O(sin 2θ)` on `Iθ` — the form needed by
`Work.FTS.OpenPkg.angmul_field` with the profile bound `Ca = 1000`. -/
theorem DthIter_c2m_le_sin (i : ℕ) (hi : 1 ≤ i) (hi4 : i ≤ 4) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
      ≤ 1000 * Real.sin (2 * θ) := by
  have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi hi4 θ
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsq : (Real.sin (2 * θ)) ^ (2 : ℝ) ≤ Real.sin (2 * θ) := by
    rw [Real.rpow_two]
    nlinarith
  have h1000 : 1000 * (Real.sin (2 * θ)) ^ (2 : ℝ) ≤ 1000 * Real.sin (2 * θ) :=
    mul_le_mul_of_nonneg_left hsq (by norm_num)
  linarith [h]

/-- Negation preserves `HkMem` (a local copy, to avoid depending on the module
`Work.FTS.EllipticEst.HypAPI`). -/
theorem HkMem_neg' (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (-f) := by
  obtain ⟨h1, h2⟩ := h
  have hfac : ∀ z θ, Work.Spaces.HkIntegrand α k (-f) z θ = Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [show (fun θ => Work.Spaces.HkIntegrand α k (-f) z θ)
          = (fun θ => Work.Spaces.HkIntegrand α k f z θ) from funext fun θ => hfac z θ]
    exact h1 z hz
  · have hIθ : (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (-f) z θ)
        = (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      funext fun z => MeasureTheory.setIntegral_congr_fun
        (by show MeasurableSet (Set.Icc (0 : ℝ) (Real.pi / 2)); exact measurableSet_Icc)
        (fun θ _ => hfac z θ)
    rw [hIθ]
    exact h2

theorem NRow5 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.NonlinRows.Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α g) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05aF α g)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨_, _⟩ := hE.pos
  obtain ⟨Cdz, hCdz, hDzF⟩ := Work.FTS.Nonlin.DzFstar_W
  obtain ⟨Ca, hCa, hang⟩ := Work.FTS.OpenPkg.angmul_field
  refine ⟨Ci * Ci * (Cdz + 1) * (Ca * 1000) + 1, by positivity, ?_⟩
  intro α g Φs Φg hctx
  obtain ⟨hα, hα1, hαα₂, hgal, _hstar, hell⟩ := hctx
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  -- ---------------------------------------------------------------------
  -- the radial factor `L₁₂(g)`: smoothness, honesty, norm bound
  -- ---------------------------------------------------------------------
  have hLsm : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => Work.Construction.L12 g z) :=
    smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  obtain ⟨hLmem, hLle⟩ := hN.l12H α hIoc g (Work.FTS.OpenPkg.galClass_HQo4 hgal) hgal.l12
  have hLX0 : 0 ≤ Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => Work.Construction.L12 g z) :=
    Work.Spaces.HkNorm_nonneg α 4 _
  -- ---------------------------------------------------------------------
  -- the fixed profile: `D_zF_*` is `SmoothOpen` and `𝒲^{4,∞}` with norm `≤ Cdz·α`
  -- ---------------------------------------------------------------------
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hDzFsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFsm.Dz
  obtain ⟨hDzFmem, hDzFle⟩ := hDzF α hα hα1
  have hDzFle' : Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α))
      ≤ (Cdz + 1) * α :=
    le_trans hDzFle (mul_le_mul_of_nonneg_right (by linarith) hα.le)
  -- ---------------------------------------------------------------------
  -- the coefficient `coef = c2m·L₁₂(g)`: `HQo α 4` with `Xn ≤ Ca·1000·Ci·Xn g`
  -- ---------------------------------------------------------------------
  set coef : Fn := fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z with hcoef
  have hcoefSm : Work.FTS.EllipticEst.SmoothOpen coef := by
    rw [hcoef]
    exact smoothOpen_c2m_L12 hα hell.smooth hell.V.1.1
  have hangc := hang α hα hα1 (fun θ => Work.Construction.c2m θ)
    (fun z (_ : ℝ) => Work.Construction.L12 g z) 1000 smoothOpen_c2m
    (fun θ hθ => le_trans (Work.FTS.Nonlinear.Pieces.abs_c2m_le_two hθ) (by norm_num))
    (fun i hi hi4 θ hθ => DthIter_c2m_le_sin i hi hi4 hθ) hLsm hLmem
  have hcoefHk : Work.Spaces.HkMem α 4 coef := by
    rw [hcoef]
    exact hangc.1
  have hcoefXn : Work.FTS.Nonlin.Xn α coef
      ≤ (Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [hcoef]
    refine hangc.2.trans ?_
    exact mul_le_mul_of_nonneg_left hLle (by positivity)
  have hQo : Work.FTS.VocabO.HQo α 4 coef := ⟨hcoefSm, hcoefHk⟩
  -- ---------------------------------------------------------------------
  -- the `𝒲^{4,∞}`-product rule
  -- ---------------------------------------------------------------------
  have hprod := hN.wprod α hIoc (Work.Spaces.Dz (Work.Construction.Fstar α)) coef
    hDzFsm hDzFmem hQo
  -- ---------------------------------------------------------------------
  -- `N₀₅ᵃ` is `-` the product
  -- ---------------------------------------------------------------------
  have heq : Work.FTS.Nonlin.N05aF α g
      = -(fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ * coef z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a, hcoef, Pi.neg_apply]
    ring
  constructor
  · rw [heq]
    exact HkMem_neg' α 4 hprod.1
  · -- the norm bound
    have hXnprod : Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ * coef z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * ((Cdz + 1) * α)
            * ((Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g)) := by
      refine hprod.2.trans ?_
      refine mul_le_mul ?_ hcoefXn (Work.Spaces.HkNorm_nonneg α 4 coef) ?_
      · exact mul_le_mul_of_nonneg_left hDzFle'
          (mul_nonneg hCi.le (Real.rpow_nonneg hα.le _))
      · exact mul_nonneg (mul_nonneg hCi.le (Real.rpow_nonneg hα.le _))
          (mul_nonneg (by linarith : (0 : ℝ) ≤ Cdz + 1) hα.le)
    have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
      rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
      exact h.symm
    have hkey : Ci * α ^ (-(1 / 2 : ℝ)) * ((Cdz + 1) * α)
          * ((Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g))
        = (Ci * Ci * (Cdz + 1) * (Ca * 1000)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
      rw [show Ci * α ^ (-(1 / 2 : ℝ)) * ((Cdz + 1) * α)
            * ((Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g))
          = (Ci * Ci * (Cdz + 1) * (Ca * 1000)) * (α ^ (-(1 / 2 : ℝ)) * α)
              * Work.FTS.Nonlin.Xn α g from by ring, hsqrt]
      ring
    have hS : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) hXg
    calc Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05aF α g)
        = Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ * coef z θ) := by
          rw [heq]
          exact Work.FTS.EllipticEst.HkNorm_neg α 4
            (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ * coef z θ)
      _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * ((Cdz + 1) * α)
            * ((Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g)) := hXnprod
      _ = (Ci * Ci * (Cdz + 1) * (Ca * 1000)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := hkey
      _ ≤ (Ci * Ci * (Cdz + 1) * (Ca * 1000) + 1)
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_right (by linarith) hS

end Work.FTS.NonlinRows
