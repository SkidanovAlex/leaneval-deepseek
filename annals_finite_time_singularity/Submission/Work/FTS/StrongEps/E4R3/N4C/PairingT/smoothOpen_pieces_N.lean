/-
# `E4R3/N4C/PairingT/smoothOpen_pieces_N`

**Target.** The twenty `SmoothOpen`-atoms of the `N₁`--`N₅` block of the §8 split
(`Work.FTS.Nonlin.Ni_xy`): each of the pieces of `N` is `C^∞` on the *open* quadrant
`(0,∞) × (0,π/2)` as soon as the honest context

* `ClassC α g` (open-quadrant smoothness of `g`, plus the `z`-smoothness of the radial moment
  `z ↦ FK g z`),
* `EllPkgGo α Ce g Φg` (`SmoothOpen` of the three transported coefficients
  `ℛ`, `𝒰`, `𝒱` of the `g`-residual `Φ̃_g = PhiTil α g Φg`),
* `StarPkgo2 α Cs Φs` (the same for the `F_*`-residual `Φ̃_* = PhiTil α F_* Φs`)

is available.  The twelve atoms are collected in `AtomsO` by `atomsO_of_ctx`; here they are
combined by the closure of `SmoothOpen` under products (`so_mul`), constant multiples
(`so_const_mul`) and the operators `pth`, `Dz`, `Dth` (`SmoothOpen.pth`, `.Dz`, `.Dth`), plus
the two elementary angular atoms `sin(2θ)` and `sin²θ`.

Note `Φ̃_g`/`Φ̃_*` enter only through `Rop/Uop/Vop`, and `F_*`, `FK g`, `FK F_*` and `s2` are the
fixed smooth data; no hypothesis on `α` beyond `0 < α` and `α ≤ 1` is used (they are inherited
from the packages).  Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.Atoms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.PairingT

open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Local closure helpers for the products occurring in the pieces -/

/-- `c·A·B`. -/
private theorem so_c2 (c : ℝ) {A B : ℝ → ℝ → ℝ} (hA : SmoothOpen A) (hB : SmoothOpen B) :
    SmoothOpen (fun z θ => c * A z θ * B z θ) :=
  Work.FTS.StrongPersist.H6Pair6Aux.so_mul
    (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul c hA) hB

/-- `c·A·B·C`. -/
private theorem so_c3 (c : ℝ) {A B C : ℝ → ℝ → ℝ} (hA : SmoothOpen A) (hB : SmoothOpen B)
    (hC : SmoothOpen C) : SmoothOpen (fun z θ => c * A z θ * B z θ * C z θ) :=
  Work.FTS.StrongPersist.H6Pair6Aux.so_mul
    (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul c hA) hB) hC

/-- `A·B·C`. -/
private theorem so_three {A B C : ℝ → ℝ → ℝ} (hA : SmoothOpen A) (hB : SmoothOpen B)
    (hC : SmoothOpen C) : SmoothOpen (fun z θ => A z θ * B z θ * C z θ) :=
  Work.FTS.StrongPersist.H6Pair6Aux.so_mul
    (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hA hB) hC

/-- `-sin²θ` as a function of `θ` alone. -/
private theorem so_negSinSq : SmoothOpen (fun _ (θ : ℝ) => -(Real.sin θ) ^ 2) :=
  Work.FTS.StrongPersist.H6Pair6Aux.so_snd ((Real.contDiff_sin.pow 2).neg)

/-! ## The target -/

theorem smoothOpen_pieces_N {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Cs Ce : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hg : Work.FTS.ClassC.ClassC α g) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1gg α g Φg) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1gs α g Φg) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1sg α Φs g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1ss α Φs) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2gg α g Φg) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2gs α g Φg) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2sg α Φs g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3gg α g Φg) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3gs α g Φg) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3sg α Φs g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3ss α Φs) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4gg α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4gs α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4sg α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4ss α) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5gg g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5gs α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5sg α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5ss α) := by
  have A : Work.FTS.StrongEps.E4R3.N4C.AtomsO α g Φs Φg :=
    atomsO_of_ctx hα hα1 hg hell hstar
  -- the atoms
  have hG : SmoothOpen g := A.sg
  have hFs : SmoothOpen (Work.Construction.Fstar α) := A.sFs
  have hFKg := A.sFKg
  have hFKFs := A.sFKFs
  have hRg : SmoothOpen (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := A.sRg
  have hUg : SmoothOpen (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg)) := A.sUg
  have hVg : SmoothOpen (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) := A.sVg
  have hRs : SmoothOpen (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) := A.sRs
  have hUs : SmoothOpen (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) := A.sUs
  have hVs : SmoothOpen (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) := A.sVs
  -- the derived atoms
  have hPG : SmoothOpen (Work.Spaces.pth g) := hG.pth
  have hPFs : SmoothOpen (Work.Spaces.pth (Work.Construction.Fstar α)) := hFs.pth
  have hDzG : SmoothOpen (Work.Spaces.Dz g) := hG.Dz
  have hDzFs : SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFs.Dz
  have hDthG : SmoothOpen (Work.Spaces.Dth g) := hG.Dth
  have hS2 : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.s2 θ) := smoothOpen_s2
  have hSinSq : SmoothOpen (fun _ (θ : ℝ) => -(Real.sin θ) ^ 2) := so_negSinSq
  -- the twenty pieces
  have p1 : SmoothOpen (Work.FTS.Nonlin.N1gg α g Φg) := by
    unfold Work.FTS.Nonlin.N1gg
    exact so_c2 2 hRg hG
  have p2 : SmoothOpen (Work.FTS.Nonlin.N1gs α g Φg) := by
    unfold Work.FTS.Nonlin.N1gs
    exact so_c2 2 hRg hFs
  have p3 : SmoothOpen (Work.FTS.Nonlin.N1sg α Φs g) := by
    unfold Work.FTS.Nonlin.N1sg
    exact so_c2 2 hRs hG
  have p4 : SmoothOpen (Work.FTS.Nonlin.N1ss α Φs) := by
    unfold Work.FTS.Nonlin.N1ss
    exact so_c2 2 hRs hFs
  have p5 : SmoothOpen (Work.FTS.Nonlin.N2gg α g Φg) := by
    unfold Work.FTS.Nonlin.N2gg
    exact so_c2 (-2) hUg hPG
  have p6 : SmoothOpen (Work.FTS.Nonlin.N2gs α g Φg) := by
    unfold Work.FTS.Nonlin.N2gs
    exact so_c2 (-2) hUg hPFs
  have p7 : SmoothOpen (Work.FTS.Nonlin.N2sg α Φs g) := by
    unfold Work.FTS.Nonlin.N2sg
    exact so_c2 (-2) hUs hPG
  have p8 : SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) := by
    unfold Work.FTS.Nonlin.N2ss
    exact so_c2 (-2) hUs hPFs
  have p9 : SmoothOpen (Work.FTS.Nonlin.N3gg α g Φg) := by
    unfold Work.FTS.Nonlin.N3gg
    exact so_c2 (-2 * α) hVg hDzG
  have p10 : SmoothOpen (Work.FTS.Nonlin.N3gs α g Φg) := by
    unfold Work.FTS.Nonlin.N3gs
    exact so_c2 (-2 * α) hVg hDzFs
  have p11 : SmoothOpen (Work.FTS.Nonlin.N3sg α Φs g) := by
    unfold Work.FTS.Nonlin.N3sg
    exact so_c2 (-2 * α) hVs hDzG
  have p12 : SmoothOpen (Work.FTS.Nonlin.N3ss α Φs) := by
    unfold Work.FTS.Nonlin.N3ss
    exact so_c2 (-2 * α) hVs hDzFs
  have p13 : SmoothOpen (Work.FTS.Nonlin.N4gg α g) := by
    unfold Work.FTS.Nonlin.N4gg
    exact so_c2 (-(1 / 2)) hFKg hDthG
  have p14 : SmoothOpen (Work.FTS.Nonlin.N4gs α g) := by
    unfold Work.FTS.Nonlin.N4gs
    exact so_c3 (-(1 / 2)) hS2 hFKg hPFs
  have p15 : SmoothOpen (Work.FTS.Nonlin.N4sg α g) := by
    unfold Work.FTS.Nonlin.N4sg
    exact so_c2 (-(1 / 2)) hFKFs hDthG
  have p16 : SmoothOpen (Work.FTS.Nonlin.N4ss α) := by
    unfold Work.FTS.Nonlin.N4ss
    exact so_c3 (-(1 / 2)) hS2 hFKFs hPFs
  have p17 : SmoothOpen (Work.FTS.Nonlin.N5gg g) := by
    unfold Work.FTS.Nonlin.N5gg
    exact so_three hSinSq hFKg hG
  have p18 : SmoothOpen (Work.FTS.Nonlin.N5gs α g) := by
    unfold Work.FTS.Nonlin.N5gs
    exact so_three hSinSq hFKg hFs
  have p19 : SmoothOpen (Work.FTS.Nonlin.N5sg α g) := by
    unfold Work.FTS.Nonlin.N5sg
    exact so_three hSinSq hFKFs hG
  have p20 : SmoothOpen (Work.FTS.Nonlin.N5ss α) := by
    unfold Work.FTS.Nonlin.N5ss
    exact so_three hSinSq hFKFs hFs
  exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18,
    p19, p20⟩

end Work.FTS.StrongEps.E4R3.N4C.PairingT
