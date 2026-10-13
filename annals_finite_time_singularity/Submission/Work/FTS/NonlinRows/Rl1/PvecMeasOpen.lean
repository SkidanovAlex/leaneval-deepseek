/-
# `PvecMeasOpen` — a.e. measurability of the twenty pieces in the *open* class

This is the open-quadrant counterpart of
`Work.FTS.Nonlinear.Pieces.rl1Tools.PvecMeas`.  There the datum `g` was a `GalClass` (whose
regularity clause is `RegQ`, i.e. `C^∞` on the strip `(-1,∞) × (0,π/2)`) and the two elliptic
packages were the frozen `StarPkg`/`EllPkgG`, whose smoothness clauses are `SmoothQuad`
(analyticity on a neighbourhood of the closed quadrant).  Here the packages are the *open*
ones `StarPkgo`/`EllPkgGo`, whose regularity clauses are only `SmoothOpen` (i.e. `C^∞` on the
open quadrant `(0,∞) × (0,π/2)`).

The measurability statement is robust under this weakening: the product measure of the
statement is `volume ↾ (0,∞) ⊗ volume ↾ Iθ`, and `(0,∞) × Iθ` differs from the open quadrant
`Q0` only by the two angular boundary lines `θ = 0`, `θ = π/2`, which are null
(`Work.FTS.Nonlinear.Pieces.rl1Tools.qd_ae`).  Consequently a function merely *continuous* on
the open quadrant is a.e. strongly measurable (`aesm_of_contOn_Qd`), and all the closure
lemmas of `PvecMeas` (`aesm_mul`, `aesm_const_mul`, the angular factors `s2`, `sin²`, the
moment `FK`, and the "divide by `sin 2θ`" step `aesm_Uop_of_div`) apply verbatim.

The only new inputs are therefore the *smoothness* of the elliptic coefficients in the open
class:

* `Φ̃_* = Φ_* - Θ_*(α)` is `C^∞` on `Q0` from `StarPkgo.smooth` and the explicit profile
  identity `L₁₂(F_*) = 2α/(1+z)` (`smoothOpen_Theta_Fstar`, `smoothOpen_PhiTs`), and the
  three operators `ℛ`, `𝒰`, `𝒱` preserve it (`smoothOpen_Rop` and the two local lemmas
  below);
* for the `g`-side the packages give the smoothness of the three coefficients directly
  (`EllPkgGo.R`, `EllPkgGo.U`, `EllPkgGo.V` are `HQo`, i.e. `SmoothOpen` + `HkMem`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.PvecMeas
import Submission.Work.FTS.NonlinRows.smoothOpen_radA

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.Rl1

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin Work.Construction Work.Spaces
open Work.FTS.Nonlinear.Pieces.rl1Tools (aesm_congr aesm_mul aesm_const_mul aesm_neg
  aesm_s2_mul aesm_sinsq_mul aesm_FK aesm_Uop_of_div aesm_of_contOn_Qd aesm_g_ops aesm_F_ops
  aesm_FK_ops QdMeas pv)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The bridge `SmoothOpen ⟹` a.e. strong measurability -/

/-- A function which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)` is a.e. strongly
measurable for the product measure `volume ↾ (0,∞) ⊗ volume ↾ Iθ` (the two sets differ by the
null angular boundary lines). -/
theorem aesm_of_smoothOpen {f : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (Function.uncurry f) QdMeas :=
  aesm_of_contOn_Qd h.continuousOn

/-! ## `SmoothOpen` is preserved by `𝒰` and `𝒱`

`ℛ` is handled by `Work.FTS.NonlinRows.smoothOpen_Rop` (delivered in
`NonlinRows/smoothOpen_radA.lean`); the other two operators are closed under `SmoothOpen` for
purely algebraic reasons, proved here so that no extra module is needed:

* `𝒰(Ψ) = -3Ψ - α D_zΨ` (with `D_z = z∂_z`) is a linear combination of `Ψ` and `D_zΨ`;
* `𝒱(Ψ) = ∂_θΨ - tan θ · Ψ`, and `tan` is `C^∞` on the open quadrant. -/

theorem smoothOpen_Uop_open {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Uop α Ψ) := by
  rw [show Work.Construction.Uop α Ψ
      = fun z θ => -3 * Ψ z θ - α * Work.Spaces.Dz Ψ z θ from by
    funext z θ; simp only [Work.Construction.Uop, Work.Spaces.Dz]; ring]
  exact Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-3) hΨ)
    (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl α hΨ.Dz)

theorem smoothOpen_Vop_open {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := by
  have hprod : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hΨ
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (f := fun z θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ)
    (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hΨ.pth hprod) ?_
  intro z θ _ _ _
  rfl

/-! ## The three `g`-side coefficients of `EllPkgGo`

`EllPkgGo.R`/`.U`/`.V` are `HQo α 4`, i.e. `SmoothOpen` plus `HkMem`, so the a.e. strong
measurability of `ℛ(Φ̃_g)`, `𝒰(Φ̃_g)`, `𝒱(Φ̃_g)` is immediate (for `𝒰` one first undoes the
division by `sin 2θ` with `aesm_Uop_of_div`). -/

theorem aesm_Tg_ops_open {α Ce : ℝ} {g Φg : Fn}
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    AEStronglyMeasurable (Function.uncurry
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg))) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))) QdMeas :=
  ⟨aesm_of_smoothOpen hell.R.1.1,
    aesm_Uop_of_div (aesm_of_smoothOpen hell.U.1.1),
    aesm_of_smoothOpen hell.V.1.1⟩

/-! ## The three star-side coefficients of `StarPkgo`

Here the package only gives `SmoothOpen Φ_*`, so the coefficients are obtained by first
forming `Φ̃_* = Φ_* - Θ_*(α)` (`smoothOpen_PhiTs`, which uses `0 < α ≤ 1` for the explicit
profile identity `L₁₂(F_*) = 2α/(1+z)`) and then applying the three operators. -/

theorem aesm_star_ops_open {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    AEStronglyMeasurable (Function.uncurry
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) QdMeas := by
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hs
  exact ⟨aesm_of_smoothOpen (Work.FTS.NonlinRows.smoothOpen_Rop hPhi),
    aesm_of_smoothOpen (smoothOpen_Uop_open hPhi),
    aesm_of_smoothOpen (smoothOpen_Vop_open hPhi)⟩

/-! ## The target statement -/

theorem PvecMeasOpen {α Ce Cs : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.VocabO.StarPkgo α Cs Φs)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    (∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), ∀ k : Fin 20, AEMeasurable
        (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ
          * Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    (∀ k : Fin 20, AEMeasurable
        (fun r : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ
          * Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ|)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
  obtain ⟨hg, hpthg, hDzg, hDthg⟩ := aesm_g_ops hgal
  obtain ⟨hF, hpthF, hDzF⟩ := aesm_F_ops α
  obtain ⟨hRopTg, hUopTg, hVopTg⟩ := aesm_Tg_ops_open hell
  obtain ⟨hFKg, hFKF⟩ := aesm_FK_ops hgal
  obtain ⟨hRopTs, hUopTs, hVopTs⟩ := aesm_star_ops_open hα hα1 hs
  -- the twenty pieces of `pv`
  have hpiece : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ)) QdMeas := by
    intro k
    fin_cases k
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α g Φg) z θ * g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α g Φg) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α g Φg) z θ * pth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α g Φg) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α g Φg) z θ * Dz g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α g Φg) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK g z * Dth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKg hDthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK g z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKg hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK (Fstar α) z * Dth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKF hDthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK (Fstar α) z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKF hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK g z * g z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKg hg))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK g z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKg hF))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * g z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hg))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hF))) (fun z θ => ?_)
      ring
  -- the `ENNReal`-valued versions, with the angular weight `K`
  have hENN : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlinear.Pieces.rl1Tools.pv
        α g Φs Φg k r θ|)) QdMeas := by
    intro k
    have hKcont : Continuous fun p : ℝ × ℝ => Work.Spaces.K p.2 := by
      simp only [Work.Spaces.K]; fun_prop
    have hK : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) QdMeas :=
      hKcont.aestronglyMeasurable
    have hpair : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.K p.2, Function.uncurry (fun r θ =>
          Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ) p)) QdMeas :=
      hK.prodMk (hpiece k)
    have hcomp : Continuous (fun q : ℝ × ℝ => ENNReal.ofReal |q.1 * q.2|) :=
      ENNReal.continuous_ofReal.comp
        (continuous_abs.comp (continuous_fst.mul continuous_snd))
    exact hcomp.comp_aestronglyMeasurable hpair
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_all.2 fun k => (hENN k).prodMk_left] with r hr
    intro k
    exact (hr k).aemeasurable
  · intro k
    exact (hENN k).aemeasurable.lintegral_prod_right

end

end Work.FTS.NonlinRows.Rl1
