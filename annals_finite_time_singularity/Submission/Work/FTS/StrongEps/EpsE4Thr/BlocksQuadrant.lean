/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/BlocksQuadrant.lean` — the three block slots of
# `EpsDecay` on the **open quadrant**, with every hypothesis discharged

`EpsEngine/BlocksConcrete.lean` states the three `EpsDecay`-block bounds with one residual
hypothesis: the *decomposition identity*

    Rop α (PhiTil α f (Φs + E f)) = Rop α (PhiTil α f (E f)) + Rop α (PhiTil α F_* Φs)
                                    + Rop α (Theta α F_*)      (and its Uop/s2, Vop twins).

This module **discharges** it: the identity is `Rop_block_decomp` / `Uop_div_decomp` / `Vop_decomp`,
whose eight differentiability inputs are produced by `EpsEngine.BlocksDecompDiffAt` from
`ClassC.reg`, `ClassC.mem` (via `HkMem_of_le_of_smoothOpen`), `EllPkgGo.smooth` and
`StarPkgo2.smooth`.

The resulting three theorems take exactly the hypotheses of the target's route
(`ClassC α f`, the ball `Xn α f ≤ C₀α²`, `hEll`, `hstar`, the numeric smallness
`K·(Ce·C₀α²) + Cs·α ≤ …`), and conclude

    |Rop α (PhiTil α f (Φs + E f)) z θ| ≤ 1,        (Rop slot)
    |Uop α (PhiTil α f (Φs + E f)) z θ / s2 θ| ≤ 3, (Uop slot)
    |Vop (PhiTil α f (Φs + E f)) z θ| ≤ 3,          (Vop slot)

for every interior point `(z,θ)` of the open quadrant.  (The constants `1`/`3` are those of the
lead's ruling on `Maj`; the `Maj ≤ 1` clause of the frozen `EpsDecay` is the interface item
recorded in `EpsE4Thr/NOTES_Maj.md`.)

**Off the open quadrant** nothing is claimed here: `SlotMaj` quantifies over *all* real `θ`, while
`EllPkgGo`/`StarPkgo2` constrain `Φs`/`E f` only on the quadrant.  The off-quadrant half is
`EpsE4Thr/BlocksJunk.lean` (conditional on the normal forms).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EpsEngine.BlocksConcrete
import Submission.Work.FTS.EpsEngine.BlocksDecompDiffAt
import Submission.Work.FTS.EpsEngine.RopBlockDecomp
import Submission.Work.FTS.StrongPersist.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The eight differentiability inputs of the three block decompositions, from the route's
smoothness data.  (`ClassC.mem` is at order `7`, hence at order `4`; `hα1 : α ≤ 1` is what
`smoothOpen_Theta_Fstar` needs.) -/
private theorem decompDiffAt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2)
    (hf : Work.FTS.ClassC.ClassC α f)
    (hEf : Work.FTS.EllipticEst.SmoothOpen (E f))
    (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) :
    (DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α f (E f) z' θ) z ∧
     DifferentiableAt ℝ (fun z' => Φs z' θ) z ∧
     DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
       Φs z' θ) z ∧
     DifferentiableAt ℝ (fun z' => Work.Construction.Theta α (Work.Construction.Fstar α)
       z' θ) z ∧
     DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α f (E f) z θ') θ ∧
     DifferentiableAt ℝ (fun θ' => Φs z θ') θ ∧
     DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
       Φs z θ') θ ∧
     DifferentiableAt ℝ (fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α)
       z θ') θ) :=
  Work.FTS.EpsEngine.BlocksDecompDiffAt hα hα1 hz hθ0 hθ1 hf.reg
    (Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hf.reg hf.mem) hEf hΦs

/-- **The `Rop` block slot on the open quadrant, with every hypothesis discharged.** -/
theorem Rop_block_le_one {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCe : 0 ≤ Ce)
    (hCs : 0 ≤ Cs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C₀ : ℝ), 0 ≤ C₀ →
      ∀ {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      K * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1 / 4 →
      Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      |Work.Construction.Rop α (Work.Construction.PhiTil α f
        (fun z θ => Φs z θ + E f z θ)) z θ| ≤ 1 := by
  obtain ⟨K, hK, hconc⟩ :=
    Work.FTS.EpsEngine.Rop_slot_concrete (α := α) (Ce := Ce) (Cs := Cs) hα hα1 hCe hCs
  refine ⟨K, hK, fun C₀ hC₀ f Φs E z θ hz hθ hsmall hf hball hEll hstar => ?_⟩
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ :=
    decompDiffAt hα hα1 hz hθ.1 hθ.2 hf (hEll f hf).1.smooth hstar.smooth
  exact hconc (C₀ := C₀) (f := f) (Φs := Φs) (E := E) (z := z) (θ := θ)
    hC₀ hz hθ hsmall hf hball hEll hstar
    (Work.FTS.EpsEngine.Rop_block_decomp d1 d2 d3 d4 d5 d6 d7 d8)

/-- **The `Uop / sin 2θ` block slot on the open quadrant, with every hypothesis discharged.** -/
theorem Uop_block_le_three {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCe : 0 ≤ Ce)
    (hCs : 0 ≤ Cs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C₀ : ℝ), 0 ≤ C₀ →
      ∀ {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      K * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1 →
      Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      |Work.Construction.Uop α (Work.Construction.PhiTil α f
        (fun z θ => Φs z θ + E f z θ)) z θ / Work.Construction.s2 θ| ≤ 3 := by
  obtain ⟨K, hK, hconc⟩ :=
    Work.FTS.EpsEngine.Uop_slot_concrete (α := α) (Ce := Ce) (Cs := Cs) hα hα1 hCe hCs
  refine ⟨K, hK, fun C₀ hC₀ f Φs E z θ hz hθ hsmall hf hball hEll hstar => ?_⟩
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ :=
    decompDiffAt hα hα1 hz hθ.1 hθ.2 hf (hEll f hf).1.smooth hstar.smooth
  exact hconc (C₀ := C₀) (f := f) (Φs := Φs) (E := E) (z := z) (θ := θ)
    hC₀ hz hθ hsmall hf hball hEll hstar
    (Work.FTS.EpsEngine.Uop_div_decomp d1 d2 d3 d4 d5 d6 d7 d8)

/-- **The `Vop` block slot on the open quadrant, with every hypothesis discharged.** -/
theorem Vop_block_le_three {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCe : 0 ≤ Ce)
    (hCs : 0 ≤ Cs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C₀ : ℝ), 0 ≤ C₀ →
      ∀ {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      K * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1 →
      Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      |Work.Construction.Vop (Work.Construction.PhiTil α f
        (fun z θ => Φs z θ + E f z θ)) z θ| ≤ 3 := by
  obtain ⟨K, hK, hconc⟩ :=
    Work.FTS.EpsEngine.Vop_slot_concrete (α := α) (Ce := Ce) (Cs := Cs) hα hα1 hCe hCs
  refine ⟨K, hK, fun C₀ hC₀ f Φs E z θ hz hθ hsmall hf hball hEll hstar => ?_⟩
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ :=
    decompDiffAt hα hα1 hz hθ.1 hθ.2 hf (hEll f hf).1.smooth hstar.smooth
  exact hconc (C₀ := C₀) (f := f) (Φs := Φs) (E := E) (z := z) (θ := θ)
    hC₀ hz hθ hsmall hf hball hEll hstar
    (Work.FTS.EpsEngine.Vop_decomp d1 d2 d3 d4 d5 d6 d7 d8)

end Work.FTS.StrongEps.EpsE4Thr
