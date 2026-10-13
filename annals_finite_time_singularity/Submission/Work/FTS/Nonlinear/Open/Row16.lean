import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row16
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **Row 16 of the design table** (`|(N₃^{gg}, g)| ≤ K X³`, Elgindi §8), open-quadrant form.

`N₃^{gg} = -2α V(Φ̃_g)·D_z g`, so the piece is a constant times the product
`f·D_z g` of the coefficient `f = V(Φ̃_g)` and the `D_z`-derivative of the perturbation.

* the `ℋ⁴`-honesty conjunct is the interface product rule `N4Norm'.prod` applied to
  `f ∈ HQo α 4` (`EllPkgGo.V`) and to `D_z g` (`HkMem_Dz_quad`, from `HkMem α 5 g` of
  `GalClass`), transported along the constant multiplication `-2α`;
* the pairing bound is the `D_z`-transport clause `N4Extra'.t2`, whose hypotheses
  (`SmoothOpen f`, `HkMem α 4 f`, `CoefThMem 1 f`, `RegQ α 4 g`, `HkMem α 5 g`,
  `DecayAll 4 g`) are exactly what `EllPkgGo` (the `V`-clause and `Vth`) and `GalClass`
  supply.  It gives `|(f·D_z g, g)| ≤ Ct α^{-1/2}(|f|_{ℋ⁴} + CoefTh 1 f) X²`, and both
  coefficient norms are controlled by `Ce·X` resp. `Ce α^{-1/2} X`, so the prefactor
  `2α` and the loss `α^{-1/2}` combine (`α·α^{-1/2}·α^{-1/2} = 1`, `α^{1/2} ≤ 1` for
  `α ≤ 1`) into an absolute constant times `X³`. -/
theorem Row16 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3gg α g Φg) ∧
      |IP α (Work.FTS.Nonlin.N3gg α g Φg) g| ≤ K * Work.FTS.Nonlin.Xn α g ^ 3 := by
  have hCt : 0 < Ct := hE.pos.1
  have hCmax : 0 ≤ max Ce 1 := le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right Ce 1))
  refine ⟨8 * Ct * max Ce 1 + 1, by positivity, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hgal hstar hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- the coefficient `V(Φ̃_g)`
  have hVnorm : Work.FTS.Nonlin.Xn α
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) ≤ Ce * Work.FTS.Nonlin.Xn α g :=
    hell.V.2
  have hVthb : Work.FTS.VocabO.CoefTh 1
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
      ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g := hell.Vth.2
  -- the `g`-side: `D_z g ∈ ℋ⁴`
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hsmQ : Work.FTS.LocData.SmoothQuad g := hreg4.1
  have hmem5 : Work.Spaces.HkMem α 5 g := Work.FTS.OpenPkg.galClass_HkMem5 hgal
  have hDzMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.CoercivityFix.QuadPorts.HkMem_Dz_quad α 4 hsmQ hmem5
  have hDzSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) :=
    (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hsmQ).Dz
  -- the product `V(Φ̃_g)·D_z g` is in `ℋ⁴`
  have hprod := (hN.prod α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
    (Work.Spaces.Dz g) hell.V.1 ⟨hDzSm, hDzMem⟩).1
  -- `N₃^{gg}` is `-2α` times that product
  have hN3 : Work.FTS.Nonlin.N3gg α g Φg
      = fun z θ => (-2 * α) * (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
          * Work.Spaces.Dz g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N3gg]
    ring
  have hIPeq : IP α (Work.FTS.Nonlin.N3gg α g Φg) g
      = (-2 * α) * IP α (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
          * Work.Spaces.Dz g z θ) g := by
    rw [hN3]
    exact hE.smul α hIoc (-2 * α) _ g hprod hreg4
  constructor
  · rw [hN3]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-2 * α) hprod
  · rw [hIPeq]
    have habs : |(-2 : ℝ) * α| = 2 * α := by
      rw [abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]
      ring
    rw [abs_mul, habs]
    -- the `D_z`-transport estimate for the coefficient `V(Φ̃_g)`
    have ht2 := hE.t2 α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) g
      hell.V.1.1 hell.V.1.2 hell.Vth.1 hreg4 hmem5
      (Work.FTS.OpenPkg.galClass_DecayAll4 hgal)
    refine (mul_le_mul_of_nonneg_left ht2 (by linarith : (0 : ℝ) ≤ 2 * α)).trans ?_
    -- the two coefficient norms, in terms of `X = |g|_{ℋ⁴}`
    have h1 : Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
      hVnorm.trans (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hX0)
    have h2 : Work.FTS.VocabO.CoefTh 1
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ max Ce 1 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g :=
      hVthb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hA0) hX0)
    -- `α·α^{-1/2} ≤ 1` and `α·α^{-1/2}·α^{-1/2} = 1`
    have hαhalf : α * α ^ (-(1 / 2 : ℝ)) = α ^ (1 / 2 : ℝ) := by
      calc α * α ^ (-(1 / 2 : ℝ)) = α ^ (1 : ℝ) * α ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ = α ^ ((1 : ℝ) + -(1 / 2)) := (Real.rpow_add hα 1 (-(1 / 2))).symm
        _ = α ^ (1 / 2 : ℝ) := by norm_num
    have hhalf_le : α ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
    have hA1 : α ^ (1 / 2 : ℝ) * α ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hα (1 / 2) (-(1 / 2)),
        show (1 / 2 : ℝ) + -(1 / 2) = 0 by norm_num, Real.rpow_zero]
    have hAA : α * α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [hαhalf, hA1]
    -- the weighted sum of the two coefficient norms
    have hsum_bound : α * α ^ (-(1 / 2 : ℝ))
        * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
          + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)))
        ≤ 2 * (max Ce 1) * Work.FTS.Nonlin.Xn α g := by
      have e1 : α * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
          ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g := by
        calc α * α ^ (-(1 / 2 : ℝ))
              * Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
            ≤ α * α ^ (-(1 / 2 : ℝ)) * (max Ce 1 * Work.FTS.Nonlin.Xn α g) :=
              mul_le_mul_of_nonneg_left h1 (mul_nonneg hα.le hA0)
          _ = max Ce 1 * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by
              rw [hαhalf]
              ring
          _ ≤ max Ce 1 * 1 * Work.FTS.Nonlin.Xn α g := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhalf_le hCmax) hX0
          _ = max Ce 1 * Work.FTS.Nonlin.Xn α g := by ring
      have e2 : α * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
          ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g := by
        calc α * α ^ (-(1 / 2 : ℝ))
              * Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
            ≤ α * α ^ (-(1 / 2 : ℝ))
              * (max Ce 1 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g) :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg hα.le hA0)
          _ = max Ce 1 * (α * α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 / 2 : ℝ)))
              * Work.FTS.Nonlin.Xn α g := by ring
          _ = max Ce 1 * 1 * Work.FTS.Nonlin.Xn α g := by rw [hAA]
          _ = max Ce 1 * Work.FTS.Nonlin.Xn α g := by ring
      linarith [add_le_add e1 e2]
    -- the final arithmetic
    have hkey : 2 * α * (Ct * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
            + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)))
          * Work.FTS.Nonlin.Xn α g ^ 2)
        ≤ (8 * Ct * max Ce 1 + 1) * Work.FTS.Nonlin.Xn α g ^ 3 := by
      have hre : 2 * α * (Ct * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
              + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)))
            * Work.FTS.Nonlin.Xn α g ^ 2)
          = 2 * Ct * (α * α ^ (-(1 / 2 : ℝ))
              * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
                + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))))
            * Work.FTS.Nonlin.Xn α g ^ 2 := by ring
      rw [hre]
      calc 2 * Ct * (α * α ^ (-(1 / 2 : ℝ))
              * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
                + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))))
            * Work.FTS.Nonlin.Xn α g ^ 2
          ≤ 2 * Ct * (2 * (max Ce 1) * Work.FTS.Nonlin.Xn α g) * Work.FTS.Nonlin.Xn α g ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hX0 2)
            exact mul_le_mul_of_nonneg_left hsum_bound (mul_nonneg (by norm_num) hCt.le)
        _ = 4 * Ct * max Ce 1 * Work.FTS.Nonlin.Xn α g ^ 3 := by ring
        _ ≤ (8 * Ct * max Ce 1 + 1) * Work.FTS.Nonlin.Xn α g ^ 3 := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hX0 3)
            linarith [mul_nonneg hCt.le hCmax]
    exact hkey

end Work.FTS.Nonlinear.Open
