/-
# Row 14 of the §8 table, in the `StarPkgo2` vocabulary (open quadrant)

Elgindi §8 (tex 1472ff): the piece

  `N₂^{sg} = -2·𝒰(Φ̃_*)·∂_θ g`

comes with the `ℋ⁴`-honesty of `N₂^{sg}` and the pairing bound
`|⟨N₂^{sg}, g⟩| ≤ C √α · X²`, `X = Xn α g`.

**The two objects.**  `𝒰 = Construction.Uop` is the coefficient `𝒰(Ψ) = -3Ψ - α z ∂_zΨ`, and

  `Φ̃_* = PhiTs α Φs = PhiTil α (Fstar α) Φs`

is the star stream function of the modulation.  The row's coefficient is *not* honest through
`𝒰(Φ̃_*)` itself (a `WDMem`-only datum: the workspace refuted the `WDMem`-product rule,
`OpenPkg.wprod_field`), but through the quotient

  `Ǔ := 𝒰(Φ̃_*)/sin 2θ`,

which is exactly the object priced by the `StarPkgo2` field `UsW`
(`WlInfMem α 4 Ǔ`, `WlInf α 4 Ǔ ≤ Cs·α`; the docstring of `UsW` names this row).

**Route.**

* On the open quadrant `sin 2θ ≠ 0`, so `𝒰(Φ̃_*)·∂_θ g = Ǔ · D_θg` with `D_θ = sin 2θ·∂_θ`;
  at the two angular ends both sides vanish (`s2 = 0` on the left, `StarPkgo.vanishU` on the
  right).  Hence the honesty transfers across `HkMem_congr_Ioi`.
* **Honesty.**  `Ǔ` has `WlInfMem α 4` (`UsW`), `D_θg` is `ℋ⁴` because `g ∈ RegQ α 5`
  (`HkMem_dth_of_RegQ_ge`), so `N4Norm'.wprod` proves `HkMem α 4 (Ǔ · D_θg)`, and
  `HkMem_congr_Ioi` carries it to `N₂^{sg}`.
* **Bound.**  `N4Extra'.t4` is the transport clause for a coefficient known only in the
  `D`-sup norm: `|⟨Ǔ·D_θg, g⟩| ≤ Ct α^{-1/2} WDp 4 Ǔ · X²`.  The pointwise bound
  `OpenPkg.mixed_le_WlInf_200` turns `WlInfMem α 4 Ǔ` into `WDMem 4 Ǔ`, and
  `OpenPkg.WDp_le_WlInf` gives `WDp 4 Ǔ ≤ 5000·WlInf α 4 Ǔ ≤ 5000·Cs·α`; the exponents
  combine to `α^{-1/2}·α = √α`.  The factor `-2` is pulled out of the pairing by
  `N4Extra'.smul`, and `N4Extra'.congr` identifies the two first arguments on the open
  quadrant.

The constant is `K = 2·CW·Ct·max Cs 0 + 1` with `CW = 5000` the constant of
`OpenPkg.WDp_le_WlInf` (`CW` is obtained by `obtain`, so no explicit value is needed).

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row14
import Submission.Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen
import Submission.Work.FTS.EllipticEst.RPFresh.DivSinOpen.Defs
import Submission.Work.FTS.EllipticEst.Uop_bound_reg
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.OpenPkg.WDp_le_WlInf
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge
import Submission.Work.FTS.LocDataExt.Monotone
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open

theorem Row14 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2sg α Φs g) ∧
      |IP α (Work.FTS.Nonlin.N2sg α Φs g) g| ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨CW, hCW0, hCW⟩ := Work.FTS.OpenPkg.WDp_le_WlInf
  obtain ⟨hCt, _hα₂⟩ := hE.pos
  refine ⟨2 * (CW * (Ct * max Cs 0)) + 1, ?_, ?_⟩
  · have h1 : 0 ≤ CW * (Ct * max Cs 0) :=
      mul_nonneg hCW0.le (mul_nonneg hCt.le (le_max_right Cs 0))
    linarith
  · intro α g Φs Φg hα hα1 hαα₂ hgal hs2 hell
    have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
    have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
    have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
    have hreg6 : Work.FTS.Nonlin.RegQ α 6 g := hgal.reg
    have hreg5 : Work.FTS.Nonlin.RegQ α 5 g :=
      Work.FTS.LocDataExt.RegQ_mono (by norm_num) hreg6
    have hSmG : Work.FTS.EllipticEst.SmoothOpen g :=
      Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hreg6.1
    -- the coefficient `Ǔ = 𝒰(Φ̃_*)/sin 2θ` priced by `StarPkgo2.UsW`
    set Uv : Work.FTS.Galerkin.Fn := fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ with hUv
    have hUvmem : Work.Spaces.WlInfMem α 4 Uv := by
      rw [hUv]; exact hs2.UsW.1
    have hUvle : Work.Spaces.WlInf α 4 Uv ≤ Cs * α := by
      rw [hUv]; exact hs2.UsW.2
    have hΦ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
      Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα hα1 hs
    have hUopsm : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) := by
      rw [Work.FTS.EllipticEst.Uop_eq]
      exact Work.FTS.EllipticEst.smoothOpen_Uop hΦ
    have hUvsm : Work.FTS.EllipticEst.SmoothOpen Uv := by
      rw [hUv]
      exact Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin hUopsm
    -- `D_θg` is `ℋ⁴`, since `D_θ` lowers the order of the regular class by one
    have hDthHQo : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth g) :=
      ⟨hSmG.Dth,
        Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge α 4 (by linarith) hreg5⟩
    -- the honest product `Ǔ · D_θg`, by the `𝒲^{4,∞}`-product rule
    have hprod := hN.wprod α hαIoc Uv (Work.Spaces.Dth g) hUvsm hUvmem hDthHQo
    have hprod2 : Work.Spaces.HkMem α 4
        (fun z θ => -2 * (Uv z θ * Work.Spaces.Dth g z θ)) :=
      Work.FTS.LocData.HkMem_const_mul α 4 (-2) hprod.1
    -- `Ǔ·D_θg = 𝒰(Φ̃_*)·∂_θg` on `(0,∞) × Iθ` (both sides vanish at `θ = 0, π/2`)
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        (fun z θ => -2 * (Uv z θ * Work.Spaces.Dth g z θ)) z θ
          = Work.FTS.Nonlin.N2sg α Φs g z θ := by
      intro z _hz θ hθ
      have hv1 : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z 0 = 0 := hs.vanishU.1 z
      have hv2 : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 2) = 0 :=
        hs.vanishU.2 z
      have hsin : Real.sin (2 * (Real.pi / 2)) = 0 := by
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp only [hUv, Work.FTS.Nonlin.N2sg, Work.Spaces.Dth, Work.Spaces.pth,
        Work.Construction.s2]
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · subst h0
        simp [hv1]
      · rcases eq_or_lt_of_le hθ.2 with hpi | hlt
        · subst hpi
          simp [hv2, hsin]
        · have hsne : Real.sin (2 * θ) ≠ 0 :=
            ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
              (by linarith [Real.pi_pos]))
          field_simp
    -- the `ℋ⁴`-honesty of `N₂^{sg}`, transferred from the honest product
    have hmemN2 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2sg α Φs g) :=
      Work.Coercivity.HkMem_congr_Ioi α 4 hprod2 hpt
    refine ⟨hmemN2, ?_⟩
    -- ## the bound
    -- `WlInfMem` gives the `D`-sup membership, with the pointwise constant `200`
    have hWdMem : Work.FTS.VocabO.WDMem 4 Uv := by
      intro b j hbj
      refine ⟨200 * Work.Spaces.WlInf α 4 Uv, ?_⟩
      intro z θ hz hθ hθ2
      exact Work.FTS.OpenPkg.mixed_le_WlInf_200 hα hα1 hUvsm hUvmem hbj hz ⟨hθ, hθ2⟩
    -- the transport clause for a `D`-sup coefficient
    have ht4 := hE.t4 α hαIoc Uv g hWdMem hreg4
    have hWDp : Work.FTS.VocabO.WDp 4 Uv ≤ CW * Work.Spaces.WlInf α 4 Uv :=
      hCW α Uv hα hα1 hUvsm hUvmem
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
      rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
      exact h.symm
    -- the pairing at the honest representative
    have hIPval : IP α (Work.FTS.Nonlin.N2sg α Φs g) g
        = -2 * IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g := by
      have hsm := hE.smul α hαIoc (-2) (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g
        hprod.1 hreg4
      have hcg := hE.congr α hαIoc (Work.FTS.Nonlin.N2sg α Φs g)
        (fun z θ => -2 * (Uv z θ * Work.Spaces.Dth g z θ)) g hmemN2 hprod2 hreg4
        (fun z θ hQd => (hpt z hQd.1 θ ⟨le_of_lt hQd.2.1, le_of_lt hQd.2.2⟩).symm)
      rw [hcg, hsm]
    have hWlL : Work.Spaces.WlInf α 4 Uv ≤ max Cs 0 * α :=
      le_trans hUvle (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
    have hWDpL : Work.FTS.VocabO.WDp 4 Uv ≤ CW * (max Cs 0 * α) :=
      le_trans hWDp (mul_le_mul_of_nonneg_left hWlL hCW0.le)
    have hIPb : |IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g|
        ≤ CW * Ct * max Cs 0 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
      refine le_trans ht4 ?_
      have hA : 0 ≤ Ct * α ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg hCt.le (Real.rpow_nonneg hα.le _)
      have hstep : Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.VocabO.WDp 4 Uv
            * Work.FTS.Nonlin.Xn α g ^ 2
          ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (CW * (max Cs 0 * α))
            * Work.FTS.Nonlin.Xn α g ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWDpL hA) (sq_nonneg _)
      refine le_trans hstep (le_of_eq ?_)
      rw [show Ct * α ^ (-(1 / 2 : ℝ)) * (CW * (max Cs 0 * α)) * Work.FTS.Nonlin.Xn α g ^ 2
          = CW * Ct * max Cs 0 * (α ^ (-(1 / 2 : ℝ)) * α)
            * Work.FTS.Nonlin.Xn α g ^ 2 from by ring, hsqrt]
      ring
    have hfin : 2 * |IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g|
        ≤ (2 * (CW * (Ct * max Cs 0)) + 1)
          * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
      have hX2nn : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2 :=
        mul_nonneg (Real.sqrt_nonneg α) (sq_nonneg _)
      calc 2 * |IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g|
          ≤ 2 * (CW * Ct * max Cs 0 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)) :=
            mul_le_mul_of_nonneg_left hIPb (by norm_num)
        _ = 2 * (CW * (Ct * max Cs 0)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by ring
        _ ≤ (2 * (CW * (Ct * max Cs 0)) + 1)
              * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ hX2nn
            linarith
    calc |IP α (Work.FTS.Nonlin.N2sg α Φs g) g|
        = |(-2) * IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g| := by rw [hIPval]
      _ = 2 * |IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g| := by
            rw [abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]; ring
      _ ≤ _ := hfin

end Work.FTS.Nonlinear.Open
