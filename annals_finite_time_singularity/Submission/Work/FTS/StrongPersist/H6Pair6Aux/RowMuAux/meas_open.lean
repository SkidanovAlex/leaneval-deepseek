/-
# `meas_open` — a.e. measurability of the twenty pieces in the *open* class (`SmoothOpen`)

This is the open-quadrant measurability statement needed by the `RowMuAux` rows, in the
vocabulary of `Submission/Work/FTS/NonlinRows/Rl1/PvecMeasOpen.lean` (which is the
`GalClass`-version of the same statement).  There the datum `g` came with `RegQ` (i.e. `C^∞`
on the *strip* `(-1,∞) × (0,π/2)`, plus `HkMem` and the boundary traces); here the datum is
only assumed `SmoothOpen f`, i.e. `C^∞` on the *open quadrant* `(0,∞) × (0,π/2)`, together
with `HkMem α 4 f`.  Nothing on the boundary is used.

The product measure of the statement is `QdMeas = volume ↾ (0,∞) ⊗ volume ↾ Iθ`, and
`(0,∞) × Iθ` differs from the open quadrant only by the two angular boundary lines
`θ = 0`, `θ = π/2`, a null set (`qd_ae`).  Hence a function merely *continuous* on the open
quadrant is a.e. strongly measurable (`aesm_of_contOn_Qd`), and every atom of the twenty
pieces is obtained by that route:

* `f`, `∂_θf`, `D_zf`, `D_θf` from `SmoothOpen f` and its closure properties
  (`SmoothOpen.pth`, `.Dz`, `.Dth`), and the moment `FK f` from `aesm_FK`;
* the three `g`-side coefficients `ℛ(Φ_g)`, `𝒰(Φ_g)`, `𝒱(Φ_g)` from the package `EllPkgGo`
  (`aesm_Tg_ops_open`);
* the three star-side coefficients from `StarPkgo` (`aesm_star_ops_open`);
* the profile `F_*` and its derivatives from the explicit profile (`aesm_F_ops`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.NonlinRows.Rl1.PvecMeasOpen
import Submission.Work.FTS.NonlinRows.Rl1.tools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin Work.Construction Work.Spaces
open Work.FTS.Nonlinear.Pieces.rl1Tools (aesm_congr aesm_mul aesm_const_mul aesm_neg
  aesm_s2_mul aesm_sinsq_mul aesm_FK aesm_Uop_of_div aesm_of_contOn_Qd
  aesm_F_ops QdMeas pv)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The bridge `SmoothOpen ⟹` a.e. strong measurability of the atoms -/

/-- A function which is `C^∞` on the open quadrant has a.e. strongly measurable uncurried
form, together with its angular derivative, its radial weight derivative and its angular
weight derivative.  This is the `SmoothOpen` counterpart of `aesm_g_ops`. -/
theorem aesm_f_ops_open {f : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (Function.uncurry f) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.pth f)) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dz f)) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dth f)) QdMeas :=
  ⟨aesm_of_contOn_Qd h.continuousOn,
    aesm_of_contOn_Qd h.pth.continuousOn,
    aesm_of_contOn_Qd h.Dz.continuousOn,
    aesm_of_contOn_Qd h.Dth.continuousOn⟩

/-! ## The target statement -/

theorem meas_open {α Ce Cs : ℝ} {f Φs Ξg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (hell : Work.FTS.VocabO.EllPkgGo α Ce f Ξg) :
    (∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), ∀ k : Fin 20,
        AEMeasurable (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ
          * Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Ξg k r θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∀ k : Fin 20, AEMeasurable
        (fun r : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ
          * Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Ξg k r θ|)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
  obtain ⟨hf, hpthf, hDzf, hDthf⟩ := aesm_f_ops_open hso
  obtain ⟨hF, hpthF, hDzF⟩ := aesm_F_ops α
  obtain ⟨hRopTg, hUopTg, hVopTg⟩ := Work.FTS.NonlinRows.Rl1.aesm_Tg_ops_open hell
  have hFKf : AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Construction.FK f z)) QdMeas := aesm_FK hf
  have hFKF : AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z))
      QdMeas := aesm_FK hF
  obtain ⟨hRopTs, hUopTs, hVopTs⟩ :=
    Work.FTS.NonlinRows.Rl1.aesm_star_ops_open hα hα1 hs
  -- the twenty pieces of `pv`
  have hpiece : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Ξg k r θ)) QdMeas := by
    intro k
    fin_cases k
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α f Ξg) z θ * f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α f Ξg) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α f Ξg) z θ * pth f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α f Ξg) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α f Ξg) z θ * Dz f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α f Ξg) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK f z * Dth f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKf hDthf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK f z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKf hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK (Fstar α) z * Dth f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKF hDthf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK (Fstar α) z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKF hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK f z * f z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKf hf))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK f z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKf hF))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * f z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hf))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hF))) (fun z θ => ?_)
      ring
  -- the `ENNReal`-valued versions, with the angular weight `K`
  have hENN : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlinear.Pieces.rl1Tools.pv
        α f Φs Ξg k r θ|)) QdMeas := by
    intro k
    have hKcont : Continuous fun p : ℝ × ℝ => Work.Spaces.K p.2 := by
      simp only [Work.Spaces.K]; fun_prop
    have hK : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) QdMeas :=
      hKcont.aestronglyMeasurable
    have hpair : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.K p.2, Function.uncurry (fun r θ =>
          Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Ξg k r θ) p)) QdMeas :=
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

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux
