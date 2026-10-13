/-
# Row 13 of the §8 table, in the open-quadrant (primed) vocabulary

Elgindi §8 (tex 1450): the piece `N₂^{g*} = -2·U(Φ̃_g)·∂_θF_*` (the `g`-stream-function /
star-profile cross term of the second row), comes with the `ℋ⁴`-honesty of `N₂^{g*}`
(`PiecesHk`) and the norm bound `|N₂^{g*}|_{ℋ⁴} ≤ K·α^{3/2}·|g|_{ℋ⁴}`.

The coefficient `F_*` (and all its derivatives) is **not** in `ℋ⁴`: the `z`-weight
`w(z) ≍ 1/z²` is not square-integrable against the profile `2z/(1+z)²`, so the honest
product rule `N4Norm'.prod` cannot be applied.  The correct clause is the
`𝒲^{4,∞}`-priced form `N4Norm'.wprod`, which multiplies a `𝒲^{4,∞}`-function by an
`ℋ⁴`-function.

The piece is rewritten in the shape required by that clause:

  `N₂^{g*} = -2·(U(Φ̃_g)/sin 2θ)·D_θF_*`      (`D_θ = sin(2θ)∂_θ`),

i.e. as `-2` times the product of the `ℋ⁴`-coefficient `c = U(Φ̃_g)/sin 2θ` of `EllPkgGo`
and the `𝒲^{4,∞}`-function `D_θF_*`:

* `D_θF_* ∈ 𝒲^{4,∞}` with `|D_θF_*|_{𝒲^{4,∞}} ≤ CF·α²` (`Work.FTS.Nonlin.DthFstar_W`; the
  angular derivative `D_θ` hits `Γ = (sinθcos²θ)^{α/3}`, gaining one further factor `α`);
* `D_θF_*` is `SmoothOpen` (`SmoothQuad_Fstar` + `SmoothOpen.Dth`);
* `c ∈ ℋ⁴` with `|c|_{ℋ⁴} ≤ Ce·|g|_{ℋ⁴}` (`EllPkgGo.U`).

Two technical points:

* the two functions agree on `(0,∞) × [0,π/2]`: on the open angle interval because
  `sin 2θ ≠ 0` there, and on the boundary lines `θ = 0, π/2` because `U(Φ̃_g)` vanishes
  there (`EllPkgGo.vanishU`), so that both sides are `0`.  The `ℋ⁴`-honesty therefore
  transfers along `HkMem_congr_Ioi`, and the *norm* transfers because `HkNorm` only sees the
  open quadrant (`HkSq_congr_open`);
* the scalar factor `-2` is pulled out by `Xn_const_mul`.

The exponents combine as `α^{-1/2}·α² = α^{3/2}`, the rate of the row.  Nothing here uses
`Φs`, the star package or `IP`; the row is an `EllPkgGo`-only row.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.Coercivity.HkMem_congr_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

theorem NRow13 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.NonlinRows.Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2gs α g Φg) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg)
          ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨CF, hCF, hF⟩ := Work.FTS.Nonlin.DthFstar_W
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * Ci * CF * max Ce 1 + 1, ?_, ?_⟩
  · have hpos : 0 < 2 * Ci * CF * max Ce 1 :=
      mul_pos (mul_pos (mul_pos (by norm_num) hCi) hCF) hmax
    linarith
  · intro α g Φs Φg hctx
    have hα : 0 < α := hctx.hα
    have hα1 : α ≤ 1 := hctx.hα1
    have hαα₂ : α ≤ α₂ := hctx.hαα₂
    have hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg := hctx.hell
    have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
    -- the `ℋ⁴`-coefficient `c = U(Φ̃_g)/sin 2θ` of the elliptic package
    set c : Fn := fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
      / Work.Construction.s2 θ with hc
    have hcHQo : Work.FTS.VocabO.HQo α 4 c := by
      rw [hc]
      simpa only [Work.FTS.Nonlin.PhiTg] using hell.U.1
    have hcB : Work.FTS.Nonlin.Xn α c ≤ Ce * Work.FTS.Nonlin.Xn α g := by
      rw [hc]
      simpa only [Work.FTS.Nonlin.PhiTg] using hell.U.2
    -- `D_θF_*` is smooth on the open quadrant and in `𝒲^{4,∞}}` with norm `≤ CF·α²`
    have hFsmooth : Work.FTS.EllipticEst.SmoothOpen
        (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)).Dth
    obtain ⟨hFWmem, hFWle⟩ := hF α hα hα1
    -- the `𝒲^{4,∞}`-priced product rule
    have hprod := hN.wprod α hIoc (Work.Spaces.Dth (Work.Construction.Fstar α)) c
      hFsmooth hFWmem hcHQo
    -- the honest representative `P = D_θF_* · c`
    set P : Fn := fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ * c z θ with hP
    have hPmem : Work.Spaces.HkMem α 4 P := by
      rw [hP]
      exact hprod.1
    -- `N₂^{g*} = -2·P` on `(0,∞) × [0,π/2]`
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        Work.FTS.Nonlin.N2gs α g Φg z θ = -2 * P z θ := by
      intro z _hz θ hθ
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · -- `θ = 0`: both sides vanish, `U(Φ̃_g)(·,0) = 0`
        subst h0
        simp only [hP, hc, Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg, Work.Spaces.Dth,
          Work.Construction.s2_eq]
        simp [hell.vanishU.1 z]
      · rcases eq_or_lt_of_le hθ.2 with hpi | hlt
        · -- `θ = π/2`: both sides vanish, `U(Φ̃_g)(·,π/2) = 0`
          subst hpi
          simp only [hP, hc, Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg, Work.Spaces.Dth,
            Work.Construction.s2_eq]
          simp [hell.vanishU.2 z]
        · -- interior: cancel `sin 2θ`
          have hsin2 : Real.sin (2 * θ) ≠ 0 := by
            intro hzero
            have hsinpos : 0 < Real.sin θ :=
              Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [Real.pi_pos])
            have hcospos : 0 < Real.cos θ :=
              Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩
            rw [Real.sin_two_mul] at hzero
            nlinarith [mul_pos hsinpos hcospos]
          simp only [hP, hc, Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg, Work.Spaces.Dth,
            Work.Construction.s2_eq]
          field_simp
    -- the `ℋ⁴`-honesty of `N₂^{g*}`, transferred from the honest representative
    have hmem : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2gs α g Φg) :=
      Work.Coercivity.HkMem_congr_Ioi α 4
        (Work.FTS.LocData.HkMem_const_mul α 4 (-2) hPmem)
        (fun z hz θ hθ => (hpt z hz θ hθ).symm)
    -- the norm only sees the open quadrant, so `|N₂^{g*}| = 2·|P|`
    have hXn_eq : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg)
        = 2 * Work.FTS.Nonlin.Xn α P := by
      have hcong : Work.FTS.Nonlin.Xn α (fun z θ => -2 * P z θ)
          = Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg) := by
        change Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => -2 * P z θ))
          = Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N2gs α g Φg))
        rw [Work.FTS.EllipticEst.HkSq_congr_open α 4
            (fun z θ hz hθ hlt =>
              (hpt z (Set.mem_Ioi.mpr hz) θ ⟨le_of_lt hθ, le_of_lt hlt⟩).symm)]
      have htwo : Work.FTS.Nonlin.Xn α (fun z θ => -2 * P z θ)
          = 2 * Work.FTS.Nonlin.Xn α P := by
        rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (-2) P,
          abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
        norm_num
      exact hcong.symm.trans htwo
    refine ⟨hmem, ?_⟩
    rw [hXn_eq]
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hXc : 0 ≤ Work.FTS.Nonlin.Xn α c := Work.Spaces.HkNorm_nonneg α 4 c
    have hrp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have hCnn : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCi.le hrp
    have hcB' : Work.FTS.Nonlin.Xn α c ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
      le_trans hcB (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg)
    have hXnP : Work.FTS.Nonlin.Xn α P
        ≤ Ci * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
          * Work.FTS.Nonlin.Xn α c := by
      rw [hP]
      exact hprod.2
    have hstep : Work.FTS.Nonlin.Xn α P
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
          * (max Ce 1 * Work.FTS.Nonlin.Xn α g) := by
      refine le_trans hXnP (mul_le_mul ?_ hcB' hXc ?_)
      · exact mul_le_mul_of_nonneg_left hFWle hCnn
      · exact mul_nonneg hCnn (mul_nonneg hCF.le (sq_nonneg α))
    have hrpow : α ^ (-(1 / 2 : ℝ)) * α ^ 2 = α ^ (3 / 2 : ℝ) := by
      rw [show α ^ 2 = α ^ (2 : ℝ) by norm_num]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (2 : ℝ)
      rw [show -(1 / 2 : ℝ) + 2 = 3 / 2 by norm_num] at h
      exact h.symm
    calc 2 * Work.FTS.Nonlin.Xn α P
        ≤ 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
            * (max Ce 1 * Work.FTS.Nonlin.Xn α g)) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = (2 * Ci * CF * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * α ^ 2)
            * Work.FTS.Nonlin.Xn α g := by ring
      _ = (2 * Ci * CF * max Ce 1)
            * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
          rw [hrpow]
          ring
      _ ≤ (2 * Ci * CF * max Ce 1 + 1)
            * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
          refine mul_le_mul_of_nonneg_right (by linarith) ?_
          exact mul_nonneg (Real.rpow_nonneg hα.le _) hXg

end Work.FTS.NonlinRows
