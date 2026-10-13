/-
# Row 15 of the §8 table, in the `StarPkgo2` vocabulary (open quadrant)

Elgindi §8: the piece `N₂^{**} = -2 U(Φ̃_*) ∂_θF_*` comes with the `ℋ⁴`-honesty of `N₂^{**}`
and the norm bound `|N₂^{**}|_{ℋ⁴} ≤ C α²`.

The design (`FTS/STARPKG_T2_LEAD.md` §1.1, row 15) writes the whole row as a *product of a
weighted star coefficient and an angular⊗radial profile*.  With

* `G15 α Φs = ((z+1)/z)·(U(Φ̃_*)/sin 2θ)` — the weighted star coefficient priced by the field
  `StarPkgo2.UszW` (`WlInfMem α 4`, with `WlInf ≤ Cs·α`);
* `C15 α θ = -2(α/c(α))·D_θΓ(θ)` — the angular coefficient, `Γ = (sinθcos²θ)^{α/3}`;
* `ψ(z) = z²/(1+z)³` — the radial factor,

one has, on the open quadrant `Q0`,

  `N₂^{**}(z,θ) = ψ(z)·(2·C15 α θ·G15 α Φs z θ)`,

i.e. a product of a `z`-only factor, a `θ`-only factor and the `𝒲^{4,∞}`-coefficient `G15`
(`NRow15T2Aux.Defs`, here re-derived as `N2ss_open_eq`).

The machinery lives in the sibling modules:

* `Row15Aux/Defs` — the factors `A15`, `AG15`, `N2ssO`, the identity `N2ss_open_eq`, the
  smoothness lemmas and the angular jet bounds `dthU_iter_A15_flat_le` /
  `dthU_iter_A15_weight_le`;
* `Row15Aux/Jets` — the `z`-jets of `AG15`, with the `(z+1)^{-k}`-decay;
* `Row15Aux/Bound` — `row15_pointwise`, the two families
  `|(1+z)w(z)z^m·∂_z^m N₂^{**}| ≤ 200000·W` and
  `|(1+z)w(z)z^l·∂_z^l D_θ^i N₂^{**}| ≤ 200000·W·(α+sin 2θ)sin(2θ)^{α/5}` with
  `W = (10⁷·Cψ·(KA+KB+1)+1)·α·Λ`, `Λ = |G15 α Φs|_{𝒲^{4,∞}}`.

The present file is the assembly: `wtoHQ_of_pointwise_open` turns the two families into
`HkMem α 4 N₂^{**}` and `Xn α N₂^{**} ≤ Cw·W`, and `Λ ≤ max Cs 0·α` (the field `UszW`) turns
the bound into `K·α²`.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.Defs
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.Jets
import Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open
import Submission.Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
import Submission.Work.FTS.H2.STBounds
import Submission.Work.FTS.Nonlinear.Open.Row15Aux.Defs
import Submission.Work.FTS.Nonlinear.Open.Row15Aux.Jets
import Submission.Work.FTS.Nonlinear.Open.Row15Aux.Bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem Row15 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2ss α Φs) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ K * (α ^ 2) := by
  obtain ⟨Cw, hCw, hwto⟩ := Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
  obtain ⟨Cpsi, hCpsipos, hpsib⟩ := Work.FTS.NonlinRows.pzIter_psi15_le
  obtain ⟨KA, hKApos, hKAb0⟩ := dthU_iter_A15_flat_le
  obtain ⟨KB, hKBpos, hKBb0⟩ := dthU_iter_A15_weight_le
  refine ⟨Cw * (10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * (max Cs 0) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) < 10 ^ 7 * Cpsi * (KA + KB + 1) + 1 := by positivity
    have h2 : 0 ≤ Cw * (10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * max Cs 0 :=
      mul_nonneg (mul_nonneg hCw.le h1.le) (le_max_right Cs 0)
    linarith
  · intro α g Φs Φg hα hα1 hαα₂ hgal hs2 hell
    have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
    have hGm : Work.Spaces.WlInfMem α 4 (Work.FTS.NonlinRows.G15 α Φs) := hs2.UszW.1
    have hGle : Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) ≤ Cs * α := hs2.UszW.2
    have hΛ : 0 ≤ Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
      Work.FTS.H2.WlInf_nonneg hGm
    have hΛle : Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) ≤ max Cs 0 * α :=
      le_trans hGle (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
    obtain ⟨hSO, hAfam, hBfam⟩ := row15_pointwise hα hα1 hs hKApos.le hKBpos.le hCpsipos
      (fun c m hcm hm z hz θ => hpsib c m hcm hm z hz θ)
      (fun a ha θ hθ => hKAb0 α hα hα1 a ha θ hθ)
      (fun a ha θ hθ => hKBb0 α hα hα1 a ha θ hθ)
      (Work.FTS.NonlinRows.smoothOpen_G15 hα hα1 hs) hGm
    set CW : ℝ := 10 ^ 7 * Cpsi * (KA + KB + 1) + 1 with hCW
    set Λ : ℝ := Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) with hΛdef
    set W : ℝ := CW * α * Λ with hWdef
    have hCW0 : 0 < CW := by rw [hCW]; positivity
    have hW0 : 0 ≤ W := by
      rw [hWdef]; exact mul_nonneg (mul_nonneg hCW0.le hα.le) hΛ
    obtain ⟨hmem, hxn⟩ := hwto α (Work.FTS.Nonlin.N2ss α Φs) W hα hα1 hW0 hSO
      (fun m hm z hz θ hθ => by
        have := hAfam m hm z hz θ hθ
        rwa [hWdef, hCW, hΛdef] at this)
      (fun i l hi hli z hz θ hθ => by
        have := hBfam i l hi hli z hz θ hθ
        rwa [hWdef, hCW, hΛdef] at this)
    refine ⟨hmem, hxn.trans ?_⟩
    have hX : W ≤ CW * (max Cs 0) * α ^ 2 := by
      rw [hWdef, hΛdef]
      have hstep : α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
          ≤ α * (max Cs 0 * α) := mul_le_mul_of_nonneg_left hΛle hα.le
      calc CW * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
          = CW * (α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)) := by ring
        _ ≤ CW * (α * (max Cs 0 * α)) := mul_le_mul_of_nonneg_left hstep hCW0.le
        _ = CW * (max Cs 0) * α ^ 2 := by ring
    have h1 : Cw * W ≤ Cw * (CW * (max Cs 0) * α ^ 2) :=
      mul_le_mul_of_nonneg_left hX hCw.le
    have h2 : Cw * (CW * (max Cs 0) * α ^ 2)
        ≤ (Cw * (10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * (max Cs 0) + 1) * α ^ 2 := by
      rw [hCW]
      have h4 : (0 : ℝ) ≤ Cw * (10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * max Cs 0 :=
        mul_nonneg (mul_nonneg hCw.le (by positivity)) (le_max_right Cs 0)
      have h5 : 0 ≤ α ^ 2 := sq_nonneg α
      nlinarith
    exact h1.trans h2

end Work.FTS.Nonlinear.Open
