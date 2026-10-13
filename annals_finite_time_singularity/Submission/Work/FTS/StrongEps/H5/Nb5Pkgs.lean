/-
# `H5/Nb5Pkgs` — the atomic packages of the level-`5` `N`-block

The four packages of atomic facts consumed by `H5.Nb5Pieces` / `H5.Nb5Core`, together with the
scalar-multiple norm lemma used for the two fixed `ℋ⁵`-atoms.

* `HAtoms5Pkg` — the `ℋ⁵`-honest atoms (`Rop`, `Uop/sin 2θ`, `Vop`, `w`, `D_θw`, `D_zw`, `FK w`,
  `φw`, `φD_θw`, `φD_zw`), the statement of `H5.Atoms.HAtoms5`;
* `WStar5Pkg` — the three star coefficients as `𝒲^{5,∞}`-atoms, the statement of
  `H5.Atoms.WAtomsStar5`;
* `WFixed5Pkg` — the four fixed `𝒲^{5,∞}`-atoms `F_*`, `D_θF_*`, `D_zF_*`, `-2α hKer`, the
  statement of `H5.Atoms.WAtomsFixed5`;
* `HFixed5Pkg` — the five fixed `ℋ⁵`-atoms `φF_*`, `φD_θF_*`, `φD_zF_*`, `FK(F_*)·D_θF_*`,
  `FK(F_*)·F_*`, the statement of `H5.Atoms.FixedAtoms5` with its angular-`×`-radial engine
  hypothesis discharged;
* `SinSqSlot5Pkg` — the order-`5` angular slot bound for `-sin²θ`, the statement of
  `H5.Atoms.SinSqSlot5`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.VocabO2
import Submission.Work.Construction.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.StrongEps.HkSq_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `HkNorm` of a scalar multiple of a level-`5` function. -/
theorem HkNorm_const_mul5 (α : ℝ) (c : ℝ) (X : Fn) :
    Work.Spaces.HkNorm α 5 (fun z θ => c * X z θ) = |c| * Work.Spaces.HkNorm α 5 X := by
  have hsq : Work.Spaces.HkSq α 5 (fun z θ => c * X z θ)
      = c ^ 2 * Work.Spaces.HkSq α 5 X := Work.FTS.StrongEps.HkSq_const_mul α 5 c X
  calc Work.Spaces.HkNorm α 5 (fun z θ => c * X z θ)
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => c * X z θ)) := rfl
    _ = Real.sqrt (c ^ 2 * Work.Spaces.HkSq α 5 X) := by rw [hsq]
    _ = Real.sqrt (c ^ 2) * Real.sqrt (Work.Spaces.HkSq α 5 X) :=
        Real.sqrt_mul (sq_nonneg c) _
    _ = |c| * Work.Spaces.HkNorm α 5 X := by
        rw [Real.sqrt_sq_eq_abs]
        rfl

/-- **The `ℋ⁵`-honest atoms** (the statement of `H5.Atoms.HAtoms5`). -/
def HAtoms5Pkg : Prop :=
  ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      (Work.FTS.VocabO.HQo α 5 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ∧
        Work.Spaces.HkNorm α 5 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ∧
        Work.Spaces.HkNorm α 5 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 w ∧ Work.Spaces.HkNorm α 5 w ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (Work.Spaces.Dth w) ∧
        Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (Work.Spaces.Dz w) ∧
        Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z _ => Work.Construction.FK w z) ∧
        Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.FK w z) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * w z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * w z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) ≤ a)

/-- **The three star coefficients as `𝒲^{5,∞}`-atoms** (the statement of
`H5.Atoms.WAtomsStar5`); the constant is independent of `Φs`. -/
def WStar5Pkg : Prop :=
  ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {Cs6 : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {Φs : Fn}, Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
      (Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInfMem α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
          * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ)) ∧
        Work.Spaces.WlInfMem α 5 (fun z θ => (z + 1) / z
          * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ)) ∧
        Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
          * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ)) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInfMem α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ a)

/-- **The four fixed `𝒲^{5,∞}`-atoms** (the statement of `H5.Atoms.WAtomsFixed5`). -/
def WFixed5Pkg : Prop :=
  ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
    ∃ a : ℝ, 0 < a ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) ∧
        Work.Spaces.WlInfMem α 5 (Work.Construction.Fstar α) ∧
        Work.Spaces.WlInf α 5 (Work.Construction.Fstar α) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInfMem α 5 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInf α 5 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInfMem α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInf α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ∧
        Work.Spaces.WlInfMem α 5 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ∧
        Work.Spaces.WlInf α 5 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ≤ a)

/-- **The five fixed `ℋ⁵`-atoms** (`φ·F_*`, `φ·D_θF_*`, `φ·D_zF_*`, `FK(F_*)·D_θF_*`,
`FK(F_*)·F_*`), the statement of `H5.Atoms.FixedAtoms5` with its engine hypothesis discharged. -/
def HFixed5Pkg : Prop :=
  ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z)
          * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z)
          * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z)
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z)
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * Work.Construction.Fstar α z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * Work.Construction.Fstar α z θ) ≤ a)

/-- The order-`5` angular slot bound for `-sin²θ` (the statement of `H5.Atoms.SinSqSlot5`). -/
def SinSqSlot5Pkg : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.DthIter 5 (fun _ (θ' : ℝ) => -(Real.sin θ') ^ 2) 0 θ| ≤ B * Real.sin (2 * θ)

end Work.FTS.StrongEps.H5
