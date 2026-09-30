/-
# `HomologyIso/`: generated SDR data (the five cusp complexes A_v)

**This file is generated** by `Submission/Work/HomologyIso/scripts/gen_sdr_data.py` from the exact
Ratcliffe--Tschantz data in `rtdata/`; do not edit by hand, rerun the script.

The five cusp cube complexes `A_1, …, A_5` of `M̄`.  Each is a `T³`;
cusps 1–4 have `4/12/12/4` cubes while cusp 5 (of covolume 8 times
larger) has `32/96/96/32`.  Their homology is `(ℤ, ℤ³, ℤ³, ℤ)`.

This module contains the five complexes one after the other, so that
each check is verified on the cusp it belongs to.

Everything below is integral; every identity is re-checked by the Lean kernel, one degree at a
time (`decide` on the sparse data), and assembled with `Work.Certificates.FinChainCx.bdCheck_sound`
and `Work.Certificates.SDR.sound`.
-/
import Mathlib
import Submission.Work.Certificates.SDR
import Submission.Work.Certificates.SDR.check_of_pieces
import Submission.Work.Certificates.SDR.sound
import Submission.Work.Certificates.FinChainCx.bdCheck_sound
import Submission.Work.Certificates.FinChainCx.bdCheck_of_pieces

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open CategoryTheory

namespace Work.HomologyIso.Gen

open Work.Certificates


/-- The number of cells in each dimension: `4, 12, 12, 4` (and `0` above). -/
def cusp1Dim : ℕ → ℕ
  | 0 => 4 | 1 => 12 | 2 => 12 | 3 => 4
  | _ => 0

/-- The complex has no cells in degree `≥ 4`. -/
theorem cusp1Dim_eq_zero (k : ℕ) (hk : 4 ≤ k) : cusp1Dim k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 => rfl

/-- `∂_1 : C_1 → C_0`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `12` generators of `C_1` -/
def cusp1Bdzero : SOp 4 12 :=
  SOp.ofList [
    [(2, -1), (3, 1)],
    [],
    [],
    [(0, -1), (1, 1)],
    [],
    [],
    [(1, -1), (3, 1)],
    [(0, -1), (2, 1)],
    [(1, -1), (3, 1)],
    [(0, -1), (2, 1)],
    [(0, 1), (1, -1)],
    [(2, 1), (3, -1)],
  ]

/-- `∂_2 : C_2 → C_1`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `12` generators of `C_2` -/
def cusp1Bdone : SOp 12 12 :=
  SOp.ofList [
    [(1, 1), (2, -1)],
    [(4, 1), (5, -1)],
    [(0, -1), (3, 1), (6, 1), (7, -1)],
    [(0, -1), (3, 1), (8, 1), (9, -1)],
    [(1, -1), (4, 1)],
    [(1, -1), (4, 1)],
    [(2, -1), (5, 1)],
    [(2, -1), (5, 1)],
    [(4, 1), (5, -1)],
    [(1, 1), (2, -1)],
    [(8, 1), (9, -1), (10, -1), (11, 1)],
    [(6, 1), (7, -1), (10, -1), (11, 1)],
  ]

/-- `∂_3 : C_3 → C_2`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `4` generators of `C_3` -/
def cusp1Bdtwo : SOp 12 4 :=
  SOp.ofList [
    [(0, 1), (1, -1), (4, 1), (6, -1)],
    [(0, 1), (1, -1), (5, 1), (7, -1)],
    [(5, -1), (7, 1), (8, 1), (9, -1)],
    [(4, -1), (6, 1), (8, 1), (9, -1)],
  ]

/-- The boundary of the complex, in the indexing of `FinChainCx`
(`bd k = ∂_{{k+1}} : C_{{k+1}} → C_k`). -/
def cusp1Bd : ∀ k, SOp (cusp1Dim k) (cusp1Dim (k+1))
  | 0 => cusp1Bdzero
  | 1 => cusp1Bdone
  | 2 => cusp1Bdtwo
  | _ => SOp.zero _ _

theorem cusp1BdCheck_zero : FinChainCx.bdCheckDeg cusp1Dim cusp1Bd 0 = true := by decide +kernel
theorem cusp1BdCheck_one : FinChainCx.bdCheckDeg cusp1Dim cusp1Bd 1 = true := by decide +kernel
theorem cusp1BdCheck_two : FinChainCx.bdCheckDeg cusp1Dim cusp1Bd 2 = true := by decide +kernel
theorem cusp1BdCheck_three : FinChainCx.bdCheckDeg cusp1Dim cusp1Bd 3 = true := by decide +kernel

/-- `∂ ∘ ∂ = 0`, checked one degree at a time. -/
theorem cusp1BdCheck (k : ℕ) (hk : k < 4) :
    FinChainCx.bdCheckDeg cusp1Dim cusp1Bd k = true := by
  interval_cases k
  exacts [cusp1BdCheck_zero, cusp1BdCheck_one, cusp1BdCheck_two, cusp1BdCheck_three]

/-- **The cell complex** (a finite free `ℤ`-chain complex). -/
def cusp1Cx : FinChainCx where
  dim := cusp1Dim
  bd := cusp1Bd
  bd_comp := FinChainCx.bdCheck_sound (fun k hk => cusp1Dim_eq_zero k hk)
    (FinChainCx.bdCheck_of_pieces fun k hk => cusp1BdCheck k hk)

/-- The ranks of the homology: `1, 3, 3, 1` (and `0` above). -/
def cusp1B : ℕ → ℕ
  | 0 => 1 | 1 => 3 | 2 => 3 | 3 => 1
  | _ => 0

theorem cusp1B_eq_zero (k : ℕ) (hk : 4 ≤ k) : cusp1B k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 => rfl

/-- `Z_0 : ℤ^{1} → C_0` (the section: the generators map to cycles) -/
def cusp1Zzero : SOp 4 1 :=
  SOp.ofList [
    [(3, 1)],
  ]

/-- `Z_1 : ℤ^{3} → C_1` (the section: the generators map to cycles) -/
def cusp1Zone : SOp 12 3 :=
  SOp.ofList [
    [(0, 1), (3, -1), (6, -1), (9, 1)],
    [(2, 1)],
    [(0, 1), (11, 1)],
  ]

/-- `Z_2 : ℤ^{3} → C_2` (the section: the generators map to cycles) -/
def cusp1Ztwo : SOp 12 3 :=
  SOp.ofList [
    [(0, -1), (9, 1)],
    [(4, -1), (5, 1)],
    [(2, -1), (3, 1), (10, -1), (11, 1)],
  ]

/-- `Z_3 : ℤ^{1} → C_3` (the section: the generators map to cycles) -/
def cusp1Zthree : SOp 4 1 :=
  SOp.ofList [
    [(0, 1), (1, -1), (2, -1), (3, 1)],
  ]

/-- `ρ_0 : C_0 → ℤ^{1}` (the retraction) -/
def cusp1Rhozero : SOp 1 4 :=
  SOp.ofList [
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
  ]

/-- `ρ_1 : C_1 → ℤ^{3}` (the retraction) -/
def cusp1Rhoone : SOp 3 12 :=
  SOp.ofList [
    [],
    [(1, 1)],
    [(1, 1)],
    [],
    [(1, 1)],
    [(1, 1)],
    [],
    [],
    [(0, 1)],
    [(0, 1)],
    [(2, 1)],
    [(2, 1)],
  ]

/-- `ρ_2 : C_2 → ℤ^{3}` (the retraction) -/
def cusp1Rhotwo : SOp 3 12 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
    [],
    [(1, 1)],
    [],
    [(1, 1)],
    [(0, 1)],
    [(0, 1)],
    [],
    [(2, 1)],
  ]

/-- `ρ_3 : C_3 → ℤ^{1}` (the retraction) -/
def cusp1Rhothree : SOp 1 4 :=
  SOp.ofList [
    [],
    [],
    [],
    [(0, 1)],
  ]

/-- `h_0 : C_0 → C_{1}` (the homotopy) -/
def cusp1Hzero : SOp 12 4 :=
  SOp.ofList [
    [(3, -1), (6, -1)],
    [(6, -1)],
    [(0, -1)],
    [],
  ]

/-- `h_1 : C_1 → C_{2}` (the homotopy) -/
def cusp1Hone : SOp 12 12 :=
  SOp.ofList [
    [],
    [(0, 1)],
    [],
    [],
    [(0, 1), (4, 1)],
    [(0, 1), (1, -1), (4, 1)],
    [],
    [(2, -1)],
    [(3, 1)],
    [],
    [(3, 1), (10, -1)],
    [],
  ]

/-- `h_2 : C_2 → C_{3}` (the homotopy) -/
def cusp1Htwo : SOp 4 12 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
    [],
    [],
    [(0, -1)],
    [(1, -1)],
    [(1, 1), (2, 1)],
    [],
    [],
    [],
  ]

/-- `h_3 : C_3 → C_{4}` (the homotopy) -/
def cusp1Hthree : SOp 0 4 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
  ]

/-- The section in every degree. -/
def cusp1Z : ∀ k, SOp (cusp1Dim k) (cusp1B k)
  | 0 => cusp1Zzero
  | 1 => cusp1Zone
  | 2 => cusp1Ztwo
  | 3 => cusp1Zthree
  | _ => SOp.zero _ _

/-- The retraction in every degree. -/
def cusp1Rho : ∀ k, SOp (cusp1B k) (cusp1Dim k)
  | 0 => cusp1Rhozero
  | 1 => cusp1Rhoone
  | 2 => cusp1Rhotwo
  | 3 => cusp1Rhothree
  | _ => SOp.zero _ _

/-- The homotopy in every degree. -/
def cusp1H : ∀ k, SOp (cusp1Dim (k+1)) (cusp1Dim k)
  | 0 => cusp1Hzero
  | 1 => cusp1Hone
  | 2 => cusp1Htwo
  | 3 => cusp1Hthree
  | _ => SOp.zero _ _

/-- **The strong deformation retract certificate.** -/
def cusp1SDR : SDR cusp1Cx where
  N := 4
  b := cusp1B
  Z := cusp1Z
  ρ := cusp1Rho
  h := cusp1H
  dim_zero := fun k hk => cusp1Dim_eq_zero k hk
  b_zero := fun k hk => cusp1B_eq_zero k hk

theorem cusp1SDR_checkHomZero : cusp1SDR.checkHomZero = true := by decide +kernel

theorem cusp1SDR_checkZ_zero : cusp1SDR.checkZ 0 = true := by decide +kernel
theorem cusp1SDR_checkZ_one : cusp1SDR.checkZ 1 = true := by decide +kernel
theorem cusp1SDR_checkZ_two : cusp1SDR.checkZ 2 = true := by decide +kernel
theorem cusp1SDR_checkZ_three : cusp1SDR.checkZ 3 = true := by decide +kernel

theorem cusp1SDR_checkZ (k : ℕ) (hk : k < 4) : cusp1SDR.checkZ k = true := by
  interval_cases k
  exacts [cusp1SDR_checkZ_zero, cusp1SDR_checkZ_one, cusp1SDR_checkZ_two, cusp1SDR_checkZ_three]

theorem cusp1SDR_checkRho_zero : cusp1SDR.checkRho 0 = true := by decide +kernel
theorem cusp1SDR_checkRho_one : cusp1SDR.checkRho 1 = true := by decide +kernel
theorem cusp1SDR_checkRho_two : cusp1SDR.checkRho 2 = true := by decide +kernel
theorem cusp1SDR_checkRho_three : cusp1SDR.checkRho 3 = true := by decide +kernel

theorem cusp1SDR_checkRho (k : ℕ) (hk : k < 4) : cusp1SDR.checkRho k = true := by
  interval_cases k
  exacts [cusp1SDR_checkRho_zero, cusp1SDR_checkRho_one, cusp1SDR_checkRho_two, cusp1SDR_checkRho_three]

theorem cusp1SDR_checkRhoZ_zero : cusp1SDR.checkRhoZ 0 = true := by decide +kernel
theorem cusp1SDR_checkRhoZ_one : cusp1SDR.checkRhoZ 1 = true := by decide +kernel
theorem cusp1SDR_checkRhoZ_two : cusp1SDR.checkRhoZ 2 = true := by decide +kernel
theorem cusp1SDR_checkRhoZ_three : cusp1SDR.checkRhoZ 3 = true := by decide +kernel

theorem cusp1SDR_checkRhoZ (k : ℕ) (hk : k < 4) : cusp1SDR.checkRhoZ k = true := by
  interval_cases k
  exacts [cusp1SDR_checkRhoZ_zero, cusp1SDR_checkRhoZ_one, cusp1SDR_checkRhoZ_two, cusp1SDR_checkRhoZ_three]

theorem cusp1SDR_checkHom_zero : cusp1SDR.checkHom 0 = true := by decide +kernel
theorem cusp1SDR_checkHom_one : cusp1SDR.checkHom 1 = true := by decide +kernel
theorem cusp1SDR_checkHom_two : cusp1SDR.checkHom 2 = true := by decide +kernel
theorem cusp1SDR_checkHom_three : cusp1SDR.checkHom 3 = true := by decide +kernel

theorem cusp1SDR_checkHom (k : ℕ) (hk : k < 4) : cusp1SDR.checkHom k = true := by
  interval_cases k
  exacts [cusp1SDR_checkHom_zero, cusp1SDR_checkHom_one, cusp1SDR_checkHom_two, cusp1SDR_checkHom_three]

/-- **The certificate passes**: `∂Z = 0`, `ρ∂ = 0`, `ρZ = 1` and `1 - Zρ = ∂h + h∂`. -/
theorem cusp1SDR_check : cusp1SDR.check = true :=
  SDR.check_of_pieces cusp1SDR cusp1SDR_checkHomZero (fun k hk =>
    ⟨cusp1SDR_checkZ k hk, cusp1SDR_checkRho k hk, cusp1SDR_checkRhoZ k hk,
      cusp1SDR_checkHom k hk⟩)

/-- **The homology of the complex**: `H_k ≅ ℤ^{cusp1 k}`. -/
theorem cusp1Cx_homology (k : ℕ) :
    Nonempty (cusp1Cx.homology k ≅ ModuleCat.of ℤ (Fin (cusp1B k) → ℤ)) :=
  SDR.sound cusp1SDR cusp1SDR_check k

end Work.HomologyIso.Gen

open Work.Certificates


/-- The number of cells in each dimension: `4, 12, 12, 4` (and `0` above). -/
def cusp2Dim : ℕ → ℕ
  | 0 => 4 | 1 => 12 | 2 => 12 | 3 => 4
  | _ => 0

/-- The complex has no cells in degree `≥ 4`. -/
theorem cusp2Dim_eq_zero (k : ℕ) (hk : 4 ≤ k) : cusp2Dim k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 => rfl

/-- `∂_1 : C_1 → C_0`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `12` generators of `C_1` -/
def cusp2Bdzero : SOp 4 12 :=
  SOp.ofList [
    [(2, -1), (3, 1)],
    [(0, -1), (1, 1)],
    [(1, -1), (3, 1)],
    [(0, -1), (2, 1)],
    [(2, -1), (3, 1)],
    [(0, -1), (1, 1)],
    [],
    [],
    [],
    [],
    [(0, 1), (2, -1)],
    [(1, 1), (3, -1)],
  ]

/-- `∂_2 : C_2 → C_1`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `12` generators of `C_2` -/
def cusp2Bdone : SOp 12 12 :=
  SOp.ofList [
    [(0, -1), (1, 1), (2, 1), (3, -1)],
    [(2, 1), (3, -1), (4, -1), (5, 1)],
    [(6, 1), (7, -1)],
    [(6, 1), (7, -1)],
    [(8, 1), (9, -1)],
    [(8, 1), (9, -1)],
    [(6, 1), (8, -1)],
    [(7, 1), (9, -1)],
    [(4, -1), (5, 1), (10, 1), (11, -1)],
    [(0, -1), (1, 1), (10, 1), (11, -1)],
    [(7, 1), (9, -1)],
    [(6, 1), (8, -1)],
  ]

/-- `∂_3 : C_3 → C_2`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `4` generators of `C_3` -/
def cusp2Bdtwo : SOp 12 4 :=
  SOp.ofList [
    [(2, -1), (4, 1), (6, 1), (7, -1)],
    [(3, -1), (5, 1), (6, 1), (7, -1)],
    [(3, 1), (5, -1), (10, 1), (11, -1)],
    [(2, 1), (4, -1), (10, 1), (11, -1)],
  ]

/-- The boundary of the complex, in the indexing of `FinChainCx`
(`bd k = ∂_{{k+1}} : C_{{k+1}} → C_k`). -/
def cusp2Bd : ∀ k, SOp (cusp2Dim k) (cusp2Dim (k+1))
  | 0 => cusp2Bdzero
  | 1 => cusp2Bdone
  | 2 => cusp2Bdtwo
  | _ => SOp.zero _ _

theorem cusp2BdCheck_zero : FinChainCx.bdCheckDeg cusp2Dim cusp2Bd 0 = true := by decide +kernel
theorem cusp2BdCheck_one : FinChainCx.bdCheckDeg cusp2Dim cusp2Bd 1 = true := by decide +kernel
theorem cusp2BdCheck_two : FinChainCx.bdCheckDeg cusp2Dim cusp2Bd 2 = true := by decide +kernel
theorem cusp2BdCheck_three : FinChainCx.bdCheckDeg cusp2Dim cusp2Bd 3 = true := by decide +kernel

/-- `∂ ∘ ∂ = 0`, checked one degree at a time. -/
theorem cusp2BdCheck (k : ℕ) (hk : k < 4) :
    FinChainCx.bdCheckDeg cusp2Dim cusp2Bd k = true := by
  interval_cases k
  exacts [cusp2BdCheck_zero, cusp2BdCheck_one, cusp2BdCheck_two, cusp2BdCheck_three]

/-- **The cell complex** (a finite free `ℤ`-chain complex). -/
def cusp2Cx : FinChainCx where
  dim := cusp2Dim
  bd := cusp2Bd
  bd_comp := FinChainCx.bdCheck_sound (fun k hk => cusp2Dim_eq_zero k hk)
    (FinChainCx.bdCheck_of_pieces fun k hk => cusp2BdCheck k hk)

/-- The ranks of the homology: `1, 3, 3, 1` (and `0` above). -/
def cusp2B : ℕ → ℕ
  | 0 => 1 | 1 => 3 | 2 => 3 | 3 => 1
  | _ => 0

theorem cusp2B_eq_zero (k : ℕ) (hk : 4 ≤ k) : cusp2B k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 => rfl

/-- `Z_0 : ℤ^{1} → C_0` (the section: the generators map to cycles) -/
def cusp2Zzero : SOp 4 1 :=
  SOp.ofList [
    [(3, 1)],
  ]

/-- `Z_1 : ℤ^{3} → C_1` (the section: the generators map to cycles) -/
def cusp2Zone : SOp 12 3 :=
  SOp.ofList [
    [(9, 1)],
    [(1, -1), (5, 1)],
    [(2, 1), (11, 1)],
  ]

/-- `Z_2 : ℤ^{3} → C_2` (the section: the generators map to cycles) -/
def cusp2Ztwo : SOp 12 3 :=
  SOp.ofList [
    [(0, -1), (1, 1), (8, -1), (9, 1)],
    [(2, 1), (3, -1)],
    [(6, -1), (11, 1)],
  ]

/-- `Z_3 : ℤ^{1} → C_3` (the section: the generators map to cycles) -/
def cusp2Zthree : SOp 4 1 :=
  SOp.ofList [
    [(0, 1), (1, -1), (2, -1), (3, 1)],
  ]

/-- `ρ_0 : C_0 → ℤ^{1}` (the retraction) -/
def cusp2Rhozero : SOp 1 4 :=
  SOp.ofList [
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
  ]

/-- `ρ_1 : C_1 → ℤ^{3}` (the retraction) -/
def cusp2Rhoone : SOp 3 12 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
    [(1, 1)],
    [(1, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(2, 1)],
    [(2, 1)],
  ]

/-- `ρ_2 : C_2 → ℤ^{3}` (the retraction) -/
def cusp2Rhotwo : SOp 3 12 :=
  SOp.ofList [
    [],
    [],
    [(1, 1)],
    [],
    [(1, 1)],
    [],
    [],
    [],
    [],
    [(0, 1)],
    [(2, 1)],
    [(2, 1)],
  ]

/-- `ρ_3 : C_3 → ℤ^{1}` (the retraction) -/
def cusp2Rhothree : SOp 1 4 :=
  SOp.ofList [
    [],
    [],
    [],
    [(0, 1)],
  ]

/-- `h_0 : C_0 → C_{1}` (the homotopy) -/
def cusp2Hzero : SOp 12 4 :=
  SOp.ofList [
    [(1, -1), (2, -1)],
    [(2, -1)],
    [(0, -1)],
    [],
  ]

/-- `h_1 : C_1 → C_{2}` (the homotopy) -/
def cusp2Hone : SOp 12 12 :=
  SOp.ofList [
    [],
    [],
    [],
    [(0, -1)],
    [(0, 1), (1, -1)],
    [],
    [(5, 1), (6, 1)],
    [(3, -1), (5, 1), (6, 1)],
    [(5, 1)],
    [],
    [(0, 1), (1, -1), (8, 1)],
    [],
  ]

/-- `h_2 : C_2 → C_{3}` (the homotopy) -/
def cusp2Htwo : SOp 4 12 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
    [(0, 1), (1, -1)],
    [],
    [],
    [(1, -1)],
    [],
    [],
    [(2, 1)],
    [],
  ]

/-- `h_3 : C_3 → C_{4}` (the homotopy) -/
def cusp2Hthree : SOp 0 4 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
  ]

/-- The section in every degree. -/
def cusp2Z : ∀ k, SOp (cusp2Dim k) (cusp2B k)
  | 0 => cusp2Zzero
  | 1 => cusp2Zone
  | 2 => cusp2Ztwo
  | 3 => cusp2Zthree
  | _ => SOp.zero _ _

/-- The retraction in every degree. -/
def cusp2Rho : ∀ k, SOp (cusp2B k) (cusp2Dim k)
  | 0 => cusp2Rhozero
  | 1 => cusp2Rhoone
  | 2 => cusp2Rhotwo
  | 3 => cusp2Rhothree
  | _ => SOp.zero _ _

/-- The homotopy in every degree. -/
def cusp2H : ∀ k, SOp (cusp2Dim (k+1)) (cusp2Dim k)
  | 0 => cusp2Hzero
  | 1 => cusp2Hone
  | 2 => cusp2Htwo
  | 3 => cusp2Hthree
  | _ => SOp.zero _ _

/-- **The strong deformation retract certificate.** -/
def cusp2SDR : SDR cusp2Cx where
  N := 4
  b := cusp2B
  Z := cusp2Z
  ρ := cusp2Rho
  h := cusp2H
  dim_zero := fun k hk => cusp2Dim_eq_zero k hk
  b_zero := fun k hk => cusp2B_eq_zero k hk

theorem cusp2SDR_checkHomZero : cusp2SDR.checkHomZero = true := by decide +kernel

theorem cusp2SDR_checkZ_zero : cusp2SDR.checkZ 0 = true := by decide +kernel
theorem cusp2SDR_checkZ_one : cusp2SDR.checkZ 1 = true := by decide +kernel
theorem cusp2SDR_checkZ_two : cusp2SDR.checkZ 2 = true := by decide +kernel
theorem cusp2SDR_checkZ_three : cusp2SDR.checkZ 3 = true := by decide +kernel

theorem cusp2SDR_checkZ (k : ℕ) (hk : k < 4) : cusp2SDR.checkZ k = true := by
  interval_cases k
  exacts [cusp2SDR_checkZ_zero, cusp2SDR_checkZ_one, cusp2SDR_checkZ_two, cusp2SDR_checkZ_three]

theorem cusp2SDR_checkRho_zero : cusp2SDR.checkRho 0 = true := by decide +kernel
theorem cusp2SDR_checkRho_one : cusp2SDR.checkRho 1 = true := by decide +kernel
theorem cusp2SDR_checkRho_two : cusp2SDR.checkRho 2 = true := by decide +kernel
theorem cusp2SDR_checkRho_three : cusp2SDR.checkRho 3 = true := by decide +kernel

theorem cusp2SDR_checkRho (k : ℕ) (hk : k < 4) : cusp2SDR.checkRho k = true := by
  interval_cases k
  exacts [cusp2SDR_checkRho_zero, cusp2SDR_checkRho_one, cusp2SDR_checkRho_two, cusp2SDR_checkRho_three]

theorem cusp2SDR_checkRhoZ_zero : cusp2SDR.checkRhoZ 0 = true := by decide +kernel
theorem cusp2SDR_checkRhoZ_one : cusp2SDR.checkRhoZ 1 = true := by decide +kernel
theorem cusp2SDR_checkRhoZ_two : cusp2SDR.checkRhoZ 2 = true := by decide +kernel
theorem cusp2SDR_checkRhoZ_three : cusp2SDR.checkRhoZ 3 = true := by decide +kernel

theorem cusp2SDR_checkRhoZ (k : ℕ) (hk : k < 4) : cusp2SDR.checkRhoZ k = true := by
  interval_cases k
  exacts [cusp2SDR_checkRhoZ_zero, cusp2SDR_checkRhoZ_one, cusp2SDR_checkRhoZ_two, cusp2SDR_checkRhoZ_three]

theorem cusp2SDR_checkHom_zero : cusp2SDR.checkHom 0 = true := by decide +kernel
theorem cusp2SDR_checkHom_one : cusp2SDR.checkHom 1 = true := by decide +kernel
theorem cusp2SDR_checkHom_two : cusp2SDR.checkHom 2 = true := by decide +kernel
theorem cusp2SDR_checkHom_three : cusp2SDR.checkHom 3 = true := by decide +kernel

theorem cusp2SDR_checkHom (k : ℕ) (hk : k < 4) : cusp2SDR.checkHom k = true := by
  interval_cases k
  exacts [cusp2SDR_checkHom_zero, cusp2SDR_checkHom_one, cusp2SDR_checkHom_two, cusp2SDR_checkHom_three]

/-- **The certificate passes**: `∂Z = 0`, `ρ∂ = 0`, `ρZ = 1` and `1 - Zρ = ∂h + h∂`. -/
theorem cusp2SDR_check : cusp2SDR.check = true :=
  SDR.check_of_pieces cusp2SDR cusp2SDR_checkHomZero (fun k hk =>
    ⟨cusp2SDR_checkZ k hk, cusp2SDR_checkRho k hk, cusp2SDR_checkRhoZ k hk,
      cusp2SDR_checkHom k hk⟩)

/-- **The homology of the complex**: `H_k ≅ ℤ^{cusp2 k}`. -/
theorem cusp2Cx_homology (k : ℕ) :
    Nonempty (cusp2Cx.homology k ≅ ModuleCat.of ℤ (Fin (cusp2B k) → ℤ)) :=
  SDR.sound cusp2SDR cusp2SDR_check k


open Work.Certificates


/-- The number of cells in each dimension: `4, 12, 12, 4` (and `0` above). -/
def cusp3Dim : ℕ → ℕ
  | 0 => 4 | 1 => 12 | 2 => 12 | 3 => 4
  | _ => 0

/-- The complex has no cells in degree `≥ 4`. -/
theorem cusp3Dim_eq_zero (k : ℕ) (hk : 4 ≤ k) : cusp3Dim k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 => rfl

/-- `∂_1 : C_1 → C_0`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `12` generators of `C_1` -/
def cusp3Bdzero : SOp 4 12 :=
  SOp.ofList [
    [],
    [],
    [(2, -1), (3, 1)],
    [],
    [],
    [(0, -1), (1, 1)],
    [(1, -1), (3, 1)],
    [(0, -1), (2, 1)],
    [(1, -1), (3, 1)],
    [(0, -1), (2, 1)],
    [(0, 1), (1, -1)],
    [(2, 1), (3, -1)],
  ]

/-- `∂_2 : C_2 → C_1`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `12` generators of `C_2` -/
def cusp3Bdone : SOp 12 12 :=
  SOp.ofList [
    [(0, -1), (1, 1)],
    [(3, -1), (4, 1)],
    [(0, -1), (3, 1)],
    [(1, -1), (4, 1)],
    [(0, -1), (3, 1)],
    [(1, -1), (4, 1)],
    [(2, -1), (5, 1), (6, 1), (7, -1)],
    [(2, -1), (5, 1), (8, 1), (9, -1)],
    [(3, -1), (4, 1)],
    [(0, -1), (1, 1)],
    [(8, 1), (9, -1), (10, -1), (11, 1)],
    [(6, 1), (7, -1), (10, -1), (11, 1)],
  ]

/-- `∂_3 : C_3 → C_2`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `4` generators of `C_3` -/
def cusp3Bdtwo : SOp 12 4 :=
  SOp.ofList [
    [(0, 1), (1, -1), (2, -1), (3, 1)],
    [(0, 1), (1, -1), (4, -1), (5, 1)],
    [(4, 1), (5, -1), (8, 1), (9, -1)],
    [(2, 1), (3, -1), (8, 1), (9, -1)],
  ]

/-- The boundary of the complex, in the indexing of `FinChainCx`
(`bd k = ∂_{{k+1}} : C_{{k+1}} → C_k`). -/
def cusp3Bd : ∀ k, SOp (cusp3Dim k) (cusp3Dim (k+1))
  | 0 => cusp3Bdzero
  | 1 => cusp3Bdone
  | 2 => cusp3Bdtwo
  | _ => SOp.zero _ _

theorem cusp3BdCheck_zero : FinChainCx.bdCheckDeg cusp3Dim cusp3Bd 0 = true := by decide +kernel
theorem cusp3BdCheck_one : FinChainCx.bdCheckDeg cusp3Dim cusp3Bd 1 = true := by decide +kernel
theorem cusp3BdCheck_two : FinChainCx.bdCheckDeg cusp3Dim cusp3Bd 2 = true := by decide +kernel
theorem cusp3BdCheck_three : FinChainCx.bdCheckDeg cusp3Dim cusp3Bd 3 = true := by decide +kernel

/-- `∂ ∘ ∂ = 0`, checked one degree at a time. -/
theorem cusp3BdCheck (k : ℕ) (hk : k < 4) :
    FinChainCx.bdCheckDeg cusp3Dim cusp3Bd k = true := by
  interval_cases k
  exacts [cusp3BdCheck_zero, cusp3BdCheck_one, cusp3BdCheck_two, cusp3BdCheck_three]

/-- **The cell complex** (a finite free `ℤ`-chain complex). -/
def cusp3Cx : FinChainCx where
  dim := cusp3Dim
  bd := cusp3Bd
  bd_comp := FinChainCx.bdCheck_sound (fun k hk => cusp3Dim_eq_zero k hk)
    (FinChainCx.bdCheck_of_pieces fun k hk => cusp3BdCheck k hk)

/-- The ranks of the homology: `1, 3, 3, 1` (and `0` above). -/
def cusp3B : ℕ → ℕ
  | 0 => 1 | 1 => 3 | 2 => 3 | 3 => 1
  | _ => 0

theorem cusp3B_eq_zero (k : ℕ) (hk : 4 ≤ k) : cusp3B k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 => rfl

/-- `Z_0 : ℤ^{1} → C_0` (the section: the generators map to cycles) -/
def cusp3Zzero : SOp 4 1 :=
  SOp.ofList [
    [(3, 1)],
  ]

/-- `Z_1 : ℤ^{3} → C_1` (the section: the generators map to cycles) -/
def cusp3Zone : SOp 12 3 :=
  SOp.ofList [
    [(2, 1), (5, -1), (6, -1), (9, 1)],
    [(4, 1)],
    [(2, 1), (11, 1)],
  ]

/-- `Z_2 : ℤ^{3} → C_2` (the section: the generators map to cycles) -/
def cusp3Ztwo : SOp 12 3 :=
  SOp.ofList [
    [(0, -1), (9, 1)],
    [(3, -1), (5, 1)],
    [(6, -1), (7, 1), (10, -1), (11, 1)],
  ]

/-- `Z_3 : ℤ^{1} → C_3` (the section: the generators map to cycles) -/
def cusp3Zthree : SOp 4 1 :=
  SOp.ofList [
    [(0, 1), (1, -1), (2, -1), (3, 1)],
  ]

/-- `ρ_0 : C_0 → ℤ^{1}` (the retraction) -/
def cusp3Rhozero : SOp 1 4 :=
  SOp.ofList [
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
  ]

/-- `ρ_1 : C_1 → ℤ^{3}` (the retraction) -/
def cusp3Rhoone : SOp 3 12 :=
  SOp.ofList [
    [(1, 1)],
    [(1, 1)],
    [],
    [(1, 1)],
    [(1, 1)],
    [],
    [],
    [],
    [(0, 1)],
    [(0, 1)],
    [(2, 1)],
    [(2, 1)],
  ]

/-- `ρ_2 : C_2 → ℤ^{3}` (the retraction) -/
def cusp3Rhotwo : SOp 3 12 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
    [(1, 1)],
    [(1, 1)],
    [],
    [],
    [(0, 1)],
    [(0, 1)],
    [],
    [(2, 1)],
  ]

/-- `ρ_3 : C_3 → ℤ^{1}` (the retraction) -/
def cusp3Rhothree : SOp 1 4 :=
  SOp.ofList [
    [],
    [],
    [],
    [(0, 1)],
  ]

/-- `h_0 : C_0 → C_{1}` (the homotopy) -/
def cusp3Hzero : SOp 12 4 :=
  SOp.ofList [
    [(5, -1), (6, -1)],
    [(6, -1)],
    [(2, -1)],
    [],
  ]

/-- `h_1 : C_1 → C_{2}` (the homotopy) -/
def cusp3Hone : SOp 12 12 :=
  SOp.ofList [
    [(0, -1), (3, -1)],
    [(3, -1)],
    [],
    [(0, -1), (2, 1), (3, -1)],
    [],
    [],
    [],
    [(6, -1)],
    [(7, 1)],
    [],
    [(7, 1), (10, -1)],
    [],
  ]

/-- `h_2 : C_2 → C_{3}` (the homotopy) -/
def cusp3Htwo : SOp 4 12 :=
  SOp.ofList [
    [],
    [(0, -1)],
    [],
    [],
    [(0, 1), (1, -1)],
    [],
    [],
    [],
    [(0, -1), (1, 1), (2, 1)],
    [],
    [],
    [],
  ]

/-- `h_3 : C_3 → C_{4}` (the homotopy) -/
def cusp3Hthree : SOp 0 4 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
  ]

/-- The section in every degree. -/
def cusp3Z : ∀ k, SOp (cusp3Dim k) (cusp3B k)
  | 0 => cusp3Zzero
  | 1 => cusp3Zone
  | 2 => cusp3Ztwo
  | 3 => cusp3Zthree
  | _ => SOp.zero _ _

/-- The retraction in every degree. -/
def cusp3Rho : ∀ k, SOp (cusp3B k) (cusp3Dim k)
  | 0 => cusp3Rhozero
  | 1 => cusp3Rhoone
  | 2 => cusp3Rhotwo
  | 3 => cusp3Rhothree
  | _ => SOp.zero _ _

/-- The homotopy in every degree. -/
def cusp3H : ∀ k, SOp (cusp3Dim (k+1)) (cusp3Dim k)
  | 0 => cusp3Hzero
  | 1 => cusp3Hone
  | 2 => cusp3Htwo
  | 3 => cusp3Hthree
  | _ => SOp.zero _ _

/-- **The strong deformation retract certificate.** -/
def cusp3SDR : SDR cusp3Cx where
  N := 4
  b := cusp3B
  Z := cusp3Z
  ρ := cusp3Rho
  h := cusp3H
  dim_zero := fun k hk => cusp3Dim_eq_zero k hk
  b_zero := fun k hk => cusp3B_eq_zero k hk

theorem cusp3SDR_checkHomZero : cusp3SDR.checkHomZero = true := by decide +kernel

theorem cusp3SDR_checkZ_zero : cusp3SDR.checkZ 0 = true := by decide +kernel
theorem cusp3SDR_checkZ_one : cusp3SDR.checkZ 1 = true := by decide +kernel
theorem cusp3SDR_checkZ_two : cusp3SDR.checkZ 2 = true := by decide +kernel
theorem cusp3SDR_checkZ_three : cusp3SDR.checkZ 3 = true := by decide +kernel

theorem cusp3SDR_checkZ (k : ℕ) (hk : k < 4) : cusp3SDR.checkZ k = true := by
  interval_cases k
  exacts [cusp3SDR_checkZ_zero, cusp3SDR_checkZ_one, cusp3SDR_checkZ_two, cusp3SDR_checkZ_three]

theorem cusp3SDR_checkRho_zero : cusp3SDR.checkRho 0 = true := by decide +kernel
theorem cusp3SDR_checkRho_one : cusp3SDR.checkRho 1 = true := by decide +kernel
theorem cusp3SDR_checkRho_two : cusp3SDR.checkRho 2 = true := by decide +kernel
theorem cusp3SDR_checkRho_three : cusp3SDR.checkRho 3 = true := by decide +kernel

theorem cusp3SDR_checkRho (k : ℕ) (hk : k < 4) : cusp3SDR.checkRho k = true := by
  interval_cases k
  exacts [cusp3SDR_checkRho_zero, cusp3SDR_checkRho_one, cusp3SDR_checkRho_two, cusp3SDR_checkRho_three]

theorem cusp3SDR_checkRhoZ_zero : cusp3SDR.checkRhoZ 0 = true := by decide +kernel
theorem cusp3SDR_checkRhoZ_one : cusp3SDR.checkRhoZ 1 = true := by decide +kernel
theorem cusp3SDR_checkRhoZ_two : cusp3SDR.checkRhoZ 2 = true := by decide +kernel
theorem cusp3SDR_checkRhoZ_three : cusp3SDR.checkRhoZ 3 = true := by decide +kernel

theorem cusp3SDR_checkRhoZ (k : ℕ) (hk : k < 4) : cusp3SDR.checkRhoZ k = true := by
  interval_cases k
  exacts [cusp3SDR_checkRhoZ_zero, cusp3SDR_checkRhoZ_one, cusp3SDR_checkRhoZ_two, cusp3SDR_checkRhoZ_three]

theorem cusp3SDR_checkHom_zero : cusp3SDR.checkHom 0 = true := by decide +kernel
theorem cusp3SDR_checkHom_one : cusp3SDR.checkHom 1 = true := by decide +kernel
theorem cusp3SDR_checkHom_two : cusp3SDR.checkHom 2 = true := by decide +kernel
theorem cusp3SDR_checkHom_three : cusp3SDR.checkHom 3 = true := by decide +kernel

theorem cusp3SDR_checkHom (k : ℕ) (hk : k < 4) : cusp3SDR.checkHom k = true := by
  interval_cases k
  exacts [cusp3SDR_checkHom_zero, cusp3SDR_checkHom_one, cusp3SDR_checkHom_two, cusp3SDR_checkHom_three]

/-- **The certificate passes**: `∂Z = 0`, `ρ∂ = 0`, `ρZ = 1` and `1 - Zρ = ∂h + h∂`. -/
theorem cusp3SDR_check : cusp3SDR.check = true :=
  SDR.check_of_pieces cusp3SDR cusp3SDR_checkHomZero (fun k hk =>
    ⟨cusp3SDR_checkZ k hk, cusp3SDR_checkRho k hk, cusp3SDR_checkRhoZ k hk,
      cusp3SDR_checkHom k hk⟩)

/-- **The homology of the complex**: `H_k ≅ ℤ^{cusp3 k}`. -/
theorem cusp3Cx_homology (k : ℕ) :
    Nonempty (cusp3Cx.homology k ≅ ModuleCat.of ℤ (Fin (cusp3B k) → ℤ)) :=
  SDR.sound cusp3SDR cusp3SDR_check k


open Work.Certificates


/-- The number of cells in each dimension: `4, 12, 12, 4` (and `0` above). -/
def cusp4Dim : ℕ → ℕ
  | 0 => 4 | 1 => 12 | 2 => 12 | 3 => 4
  | _ => 0

/-- The complex has no cells in degree `≥ 4`. -/
theorem cusp4Dim_eq_zero (k : ℕ) (hk : 4 ≤ k) : cusp4Dim k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 => rfl

/-- `∂_1 : C_1 → C_0`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `12` generators of `C_1` -/
def cusp4Bdzero : SOp 4 12 :=
  SOp.ofList [
    [(2, -1), (3, 1)],
    [],
    [],
    [(0, -1), (1, 1)],
    [],
    [],
    [(2, -1), (3, 1)],
    [(0, -1), (1, 1)],
    [(1, -1), (3, 1)],
    [(0, -1), (2, 1)],
    [(0, 1), (2, -1)],
    [(1, 1), (3, -1)],
  ]

/-- `∂_2 : C_2 → C_1`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `12` generators of `C_2` -/
def cusp4Bdone : SOp 12 12 :=
  SOp.ofList [
    [(1, 1), (2, -1)],
    [(4, 1), (5, -1)],
    [(1, 1), (2, -1)],
    [(4, 1), (5, -1)],
    [(0, -1), (3, 1), (8, 1), (9, -1)],
    [(6, -1), (7, 1), (8, 1), (9, -1)],
    [(1, -1), (4, 1)],
    [(2, -1), (5, 1)],
    [(6, -1), (7, 1), (10, 1), (11, -1)],
    [(0, -1), (3, 1), (10, 1), (11, -1)],
    [(2, -1), (5, 1)],
    [(1, -1), (4, 1)],
  ]

/-- `∂_3 : C_3 → C_2`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `4` generators of `C_3` -/
def cusp4Bdtwo : SOp 12 4 :=
  SOp.ofList [
    [(0, 1), (1, -1), (6, 1), (7, -1)],
    [(2, 1), (3, -1), (6, 1), (7, -1)],
    [(2, -1), (3, 1), (10, 1), (11, -1)],
    [(0, -1), (1, 1), (10, 1), (11, -1)],
  ]

/-- The boundary of the complex, in the indexing of `FinChainCx`
(`bd k = ∂_{{k+1}} : C_{{k+1}} → C_k`). -/
def cusp4Bd : ∀ k, SOp (cusp4Dim k) (cusp4Dim (k+1))
  | 0 => cusp4Bdzero
  | 1 => cusp4Bdone
  | 2 => cusp4Bdtwo
  | _ => SOp.zero _ _

theorem cusp4BdCheck_zero : FinChainCx.bdCheckDeg cusp4Dim cusp4Bd 0 = true := by decide +kernel
theorem cusp4BdCheck_one : FinChainCx.bdCheckDeg cusp4Dim cusp4Bd 1 = true := by decide +kernel
theorem cusp4BdCheck_two : FinChainCx.bdCheckDeg cusp4Dim cusp4Bd 2 = true := by decide +kernel
theorem cusp4BdCheck_three : FinChainCx.bdCheckDeg cusp4Dim cusp4Bd 3 = true := by decide +kernel

/-- `∂ ∘ ∂ = 0`, checked one degree at a time. -/
theorem cusp4BdCheck (k : ℕ) (hk : k < 4) :
    FinChainCx.bdCheckDeg cusp4Dim cusp4Bd k = true := by
  interval_cases k
  exacts [cusp4BdCheck_zero, cusp4BdCheck_one, cusp4BdCheck_two, cusp4BdCheck_three]

/-- **The cell complex** (a finite free `ℤ`-chain complex). -/
def cusp4Cx : FinChainCx where
  dim := cusp4Dim
  bd := cusp4Bd
  bd_comp := FinChainCx.bdCheck_sound (fun k hk => cusp4Dim_eq_zero k hk)
    (FinChainCx.bdCheck_of_pieces fun k hk => cusp4BdCheck k hk)

/-- The ranks of the homology: `1, 3, 3, 1` (and `0` above). -/
def cusp4B : ℕ → ℕ
  | 0 => 1 | 1 => 3 | 2 => 3 | 3 => 1
  | _ => 0

theorem cusp4B_eq_zero (k : ℕ) (hk : 4 ≤ k) : cusp4B k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 => rfl

/-- `Z_0 : ℤ^{1} → C_0` (the section: the generators map to cycles) -/
def cusp4Zzero : SOp 4 1 :=
  SOp.ofList [
    [(3, 1)],
  ]

/-- `Z_1 : ℤ^{3} → C_1` (the section: the generators map to cycles) -/
def cusp4Zone : SOp 12 3 :=
  SOp.ofList [
    [(2, 1)],
    [(0, -1), (6, 1)],
    [(8, 1), (11, 1)],
  ]

/-- `Z_2 : ℤ^{3} → C_2` (the section: the generators map to cycles) -/
def cusp4Ztwo : SOp 12 3 :=
  SOp.ofList [
    [(4, -1), (5, 1), (8, -1), (9, 1)],
    [(0, 1), (2, -1)],
    [(6, -1), (11, 1)],
  ]

/-- `Z_3 : ℤ^{1} → C_3` (the section: the generators map to cycles) -/
def cusp4Zthree : SOp 4 1 :=
  SOp.ofList [
    [(0, 1), (1, -1), (2, -1), (3, 1)],
  ]

/-- `ρ_0 : C_0 → ℤ^{1}` (the retraction) -/
def cusp4Rhozero : SOp 1 4 :=
  SOp.ofList [
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
  ]

/-- `ρ_1 : C_1 → ℤ^{3}` (the retraction) -/
def cusp4Rhoone : SOp 3 12 :=
  SOp.ofList [
    [],
    [(0, 1)],
    [(0, 1)],
    [],
    [(0, 1)],
    [(0, 1)],
    [(1, 1)],
    [(1, 1)],
    [],
    [],
    [(2, 1)],
    [(2, 1)],
  ]

/-- `ρ_2 : C_2 → ℤ^{3}` (the retraction) -/
def cusp4Rhotwo : SOp 3 12 :=
  SOp.ofList [
    [(1, 1)],
    [(1, 1)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(0, 1)],
    [(2, 1)],
    [(2, 1)],
  ]

/-- `ρ_3 : C_3 → ℤ^{1}` (the retraction) -/
def cusp4Rhothree : SOp 1 4 :=
  SOp.ofList [
    [],
    [],
    [],
    [(0, 1)],
  ]

/-- `h_0 : C_0 → C_{1}` (the homotopy) -/
def cusp4Hzero : SOp 12 4 :=
  SOp.ofList [
    [(3, -1), (8, -1)],
    [(8, -1)],
    [(0, -1)],
    [],
  ]

/-- `h_1 : C_1 → C_{2}` (the homotopy) -/
def cusp4Hone : SOp 12 12 :=
  SOp.ofList [
    [],
    [(2, 1)],
    [],
    [],
    [(2, 1), (6, 1)],
    [(2, 1), (3, -1), (6, 1)],
    [],
    [(4, -1), (5, 1)],
    [],
    [(4, -1)],
    [(4, 1), (5, -1), (8, 1)],
    [],
  ]

/-- `h_2 : C_2 → C_{3}` (the homotopy) -/
def cusp4Htwo : SOp 4 12 :=
  SOp.ofList [
    [],
    [(0, -1), (1, 1)],
    [],
    [],
    [],
    [],
    [],
    [(1, -1)],
    [],
    [],
    [(2, 1)],
    [],
  ]

/-- `h_3 : C_3 → C_{4}` (the homotopy) -/
def cusp4Hthree : SOp 0 4 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
  ]

/-- The section in every degree. -/
def cusp4Z : ∀ k, SOp (cusp4Dim k) (cusp4B k)
  | 0 => cusp4Zzero
  | 1 => cusp4Zone
  | 2 => cusp4Ztwo
  | 3 => cusp4Zthree
  | _ => SOp.zero _ _

/-- The retraction in every degree. -/
def cusp4Rho : ∀ k, SOp (cusp4B k) (cusp4Dim k)
  | 0 => cusp4Rhozero
  | 1 => cusp4Rhoone
  | 2 => cusp4Rhotwo
  | 3 => cusp4Rhothree
  | _ => SOp.zero _ _

/-- The homotopy in every degree. -/
def cusp4H : ∀ k, SOp (cusp4Dim (k+1)) (cusp4Dim k)
  | 0 => cusp4Hzero
  | 1 => cusp4Hone
  | 2 => cusp4Htwo
  | 3 => cusp4Hthree
  | _ => SOp.zero _ _

/-- **The strong deformation retract certificate.** -/
def cusp4SDR : SDR cusp4Cx where
  N := 4
  b := cusp4B
  Z := cusp4Z
  ρ := cusp4Rho
  h := cusp4H
  dim_zero := fun k hk => cusp4Dim_eq_zero k hk
  b_zero := fun k hk => cusp4B_eq_zero k hk

theorem cusp4SDR_checkHomZero : cusp4SDR.checkHomZero = true := by decide +kernel

theorem cusp4SDR_checkZ_zero : cusp4SDR.checkZ 0 = true := by decide +kernel
theorem cusp4SDR_checkZ_one : cusp4SDR.checkZ 1 = true := by decide +kernel
theorem cusp4SDR_checkZ_two : cusp4SDR.checkZ 2 = true := by decide +kernel
theorem cusp4SDR_checkZ_three : cusp4SDR.checkZ 3 = true := by decide +kernel

theorem cusp4SDR_checkZ (k : ℕ) (hk : k < 4) : cusp4SDR.checkZ k = true := by
  interval_cases k
  exacts [cusp4SDR_checkZ_zero, cusp4SDR_checkZ_one, cusp4SDR_checkZ_two, cusp4SDR_checkZ_three]

theorem cusp4SDR_checkRho_zero : cusp4SDR.checkRho 0 = true := by decide +kernel
theorem cusp4SDR_checkRho_one : cusp4SDR.checkRho 1 = true := by decide +kernel
theorem cusp4SDR_checkRho_two : cusp4SDR.checkRho 2 = true := by decide +kernel
theorem cusp4SDR_checkRho_three : cusp4SDR.checkRho 3 = true := by decide +kernel

theorem cusp4SDR_checkRho (k : ℕ) (hk : k < 4) : cusp4SDR.checkRho k = true := by
  interval_cases k
  exacts [cusp4SDR_checkRho_zero, cusp4SDR_checkRho_one, cusp4SDR_checkRho_two, cusp4SDR_checkRho_three]

theorem cusp4SDR_checkRhoZ_zero : cusp4SDR.checkRhoZ 0 = true := by decide +kernel
theorem cusp4SDR_checkRhoZ_one : cusp4SDR.checkRhoZ 1 = true := by decide +kernel
theorem cusp4SDR_checkRhoZ_two : cusp4SDR.checkRhoZ 2 = true := by decide +kernel
theorem cusp4SDR_checkRhoZ_three : cusp4SDR.checkRhoZ 3 = true := by decide +kernel

theorem cusp4SDR_checkRhoZ (k : ℕ) (hk : k < 4) : cusp4SDR.checkRhoZ k = true := by
  interval_cases k
  exacts [cusp4SDR_checkRhoZ_zero, cusp4SDR_checkRhoZ_one, cusp4SDR_checkRhoZ_two, cusp4SDR_checkRhoZ_three]

theorem cusp4SDR_checkHom_zero : cusp4SDR.checkHom 0 = true := by decide +kernel
theorem cusp4SDR_checkHom_one : cusp4SDR.checkHom 1 = true := by decide +kernel
theorem cusp4SDR_checkHom_two : cusp4SDR.checkHom 2 = true := by decide +kernel
theorem cusp4SDR_checkHom_three : cusp4SDR.checkHom 3 = true := by decide +kernel

theorem cusp4SDR_checkHom (k : ℕ) (hk : k < 4) : cusp4SDR.checkHom k = true := by
  interval_cases k
  exacts [cusp4SDR_checkHom_zero, cusp4SDR_checkHom_one, cusp4SDR_checkHom_two, cusp4SDR_checkHom_three]

/-- **The certificate passes**: `∂Z = 0`, `ρ∂ = 0`, `ρZ = 1` and `1 - Zρ = ∂h + h∂`. -/
theorem cusp4SDR_check : cusp4SDR.check = true :=
  SDR.check_of_pieces cusp4SDR cusp4SDR_checkHomZero (fun k hk =>
    ⟨cusp4SDR_checkZ k hk, cusp4SDR_checkRho k hk, cusp4SDR_checkRhoZ k hk,
      cusp4SDR_checkHom k hk⟩)

/-- **The homology of the complex**: `H_k ≅ ℤ^{cusp4 k}`. -/
theorem cusp4Cx_homology (k : ℕ) :
    Nonempty (cusp4Cx.homology k ≅ ModuleCat.of ℤ (Fin (cusp4B k) → ℤ)) :=
  SDR.sound cusp4SDR cusp4SDR_check k


open Work.Certificates


/-- The number of cells in each dimension: `32, 96, 96, 32` (and `0` above). -/
def cusp5Dim : ℕ → ℕ
  | 0 => 32 | 1 => 96 | 2 => 96 | 3 => 32
  | _ => 0

/-- The complex has no cells in degree `≥ 4`. -/
theorem cusp5Dim_eq_zero (k : ℕ) (hk : 4 ≤ k) : cusp5Dim k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 => rfl

/-- `∂_1 : C_1 → C_0`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `96` generators of `C_1` -/
def cusp5Bdzero : SOp 32 96 :=
  SOp.ofList [
    [(21, -1), (23, 1)],
    [(22, -1), (25, 1)],
    [(18, 1), (21, -1)],
    [(20, 1), (22, -1)],
    [(9, 1), (21, -1)],
    [(15, 1), (22, -1)],
    [(12, -1), (25, 1)],
    [(13, -1), (25, 1)],
    [(2, -1), (23, 1)],
    [(3, -1), (23, 1)],
    [(12, -1), (15, 1)],
    [(13, -1), (20, 1)],
    [(2, -1), (9, 1)],
    [(3, -1), (18, 1)],
    [(0, -1), (8, 1)],
    [(1, -1), (14, 1)],
    [(0, -1), (18, 1)],
    [(1, -1), (20, 1)],
    [(0, -1), (9, 1)],
    [(1, -1), (15, 1)],
    [(12, -1), (14, 1)],
    [(13, -1), (14, 1)],
    [(2, -1), (8, 1)],
    [(3, -1), (8, 1)],
    [(21, -1), (31, 1)],
    [(22, -1), (31, 1)],
    [(0, -1), (28, 1)],
    [(1, -1), (28, 1)],
    [(14, 1), (26, -1)],
    [(25, 1), (27, -1)],
    [(8, 1), (26, -1)],
    [(23, 1), (27, -1)],
    [(26, -1), (28, 1)],
    [(27, -1), (31, 1)],
    [(21, -1), (24, 1)],
    [(22, -1), (24, 1)],
    [(0, -1), (10, 1)],
    [(1, -1), (10, 1)],
    [(4, -1), (14, 1)],
    [(5, -1), (25, 1)],
    [(4, -1), (8, 1)],
    [(5, -1), (23, 1)],
    [(4, -1), (10, 1)],
    [(5, -1), (24, 1)],
    [(16, -1), (20, 1)],
    [(17, -1), (20, 1)],
    [(16, -1), (18, 1)],
    [(17, -1), (18, 1)],
    [(16, -1), (24, 1)],
    [(17, -1), (31, 1)],
    [(10, 1), (16, -1)],
    [(17, -1), (28, 1)],
    [(6, -1), (15, 1)],
    [(7, -1), (15, 1)],
    [(6, -1), (9, 1)],
    [(7, -1), (9, 1)],
    [(6, -1), (24, 1)],
    [(7, -1), (31, 1)],
    [(6, -1), (10, 1)],
    [(7, -1), (28, 1)],
    [(12, -1), (29, 1)],
    [(13, -1), (30, 1)],
    [(26, -1), (30, 1)],
    [(27, -1), (30, 1)],
    [(26, -1), (29, 1)],
    [(27, -1), (29, 1)],
    [(11, 1), (12, -1)],
    [(13, -1), (19, 1)],
    [(4, -1), (19, 1)],
    [(5, -1), (19, 1)],
    [(4, -1), (11, 1)],
    [(5, -1), (11, 1)],
    [(2, -1), (29, 1)],
    [(3, -1), (30, 1)],
    [(2, -1), (11, 1)],
    [(3, -1), (19, 1)],
    [(16, -1), (19, 1)],
    [(17, -1), (30, 1)],
    [(6, -1), (11, 1)],
    [(7, -1), (29, 1)],
    [(1, -1), (14, 1)],
    [(0, -1), (8, 1)],
    [(3, -1), (18, 1)],
    [(2, -1), (9, 1)],
    [(13, -1), (20, 1)],
    [(12, -1), (15, 1)],
    [(22, -1), (25, 1)],
    [(21, -1), (23, 1)],
    [(5, -1), (24, 1)],
    [(4, -1), (10, 1)],
    [(27, -1), (31, 1)],
    [(26, -1), (28, 1)],
    [(7, -1), (29, 1)],
    [(6, -1), (11, 1)],
    [(17, -1), (30, 1)],
    [(16, -1), (19, 1)],
  ]

/-- `∂_2 : C_2 → C_1`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `96` generators of `C_2` -/
def cusp5Bdone : SOp 96 96 :=
  SOp.ofList [
    [(0, -1), (4, 1), (8, 1), (12, -1)],
    [(1, -1), (5, 1), (6, 1), (10, -1)],
    [(0, 1), (2, -1), (9, -1), (13, 1)],
    [(1, 1), (3, -1), (7, -1), (11, 1)],
    [(12, -1), (14, -1), (18, 1), (22, 1)],
    [(10, -1), (15, -1), (19, 1), (20, 1)],
    [(13, 1), (14, 1), (16, -1), (23, -1)],
    [(11, 1), (15, 1), (17, -1), (21, -1)],
    [(14, -1), (26, 1), (30, 1), (32, -1)],
    [(15, -1), (27, 1), (28, 1), (32, -1)],
    [(0, 1), (24, -1), (31, -1), (33, 1)],
    [(1, 1), (25, -1), (29, -1), (33, 1)],
    [(14, -1), (36, 1), (40, 1), (42, -1)],
    [(15, -1), (37, 1), (38, 1), (42, -1)],
    [(0, 1), (34, -1), (41, -1), (43, 1)],
    [(1, 1), (35, -1), (39, -1), (43, 1)],
    [(2, -1), (34, 1), (46, 1), (48, -1)],
    [(3, -1), (35, 1), (44, 1), (48, -1)],
    [(2, 1), (24, -1), (47, -1), (49, 1)],
    [(3, 1), (25, -1), (45, -1), (49, 1)],
    [(16, -1), (36, 1), (46, 1), (50, -1)],
    [(17, -1), (37, 1), (44, 1), (50, -1)],
    [(16, 1), (26, -1), (47, -1), (51, 1)],
    [(17, 1), (27, -1), (45, -1), (51, 1)],
    [(4, -1), (34, 1), (54, 1), (56, -1)],
    [(5, -1), (35, 1), (52, 1), (56, -1)],
    [(4, 1), (24, -1), (55, -1), (57, 1)],
    [(5, 1), (25, -1), (53, -1), (57, 1)],
    [(18, -1), (36, 1), (54, 1), (58, -1)],
    [(19, -1), (37, 1), (52, 1), (58, -1)],
    [(18, 1), (26, -1), (55, -1), (59, 1)],
    [(19, 1), (27, -1), (53, -1), (59, 1)],
    [(20, -1), (28, 1), (60, 1), (64, -1)],
    [(21, -1), (28, 1), (61, 1), (62, -1)],
    [(6, 1), (29, -1), (60, -1), (65, 1)],
    [(7, 1), (29, -1), (61, -1), (63, 1)],
    [(20, -1), (38, 1), (66, 1), (70, -1)],
    [(21, -1), (38, 1), (67, 1), (68, -1)],
    [(6, 1), (39, -1), (66, -1), (71, 1)],
    [(7, 1), (39, -1), (67, -1), (69, 1)],
    [(22, -1), (30, 1), (64, -1), (72, 1)],
    [(23, -1), (30, 1), (62, -1), (73, 1)],
    [(8, 1), (31, -1), (65, 1), (72, -1)],
    [(9, 1), (31, -1), (63, 1), (73, -1)],
    [(22, -1), (40, 1), (70, -1), (74, 1)],
    [(23, -1), (40, 1), (68, -1), (75, 1)],
    [(8, 1), (41, -1), (71, 1), (74, -1)],
    [(9, 1), (41, -1), (69, 1), (75, -1)],
    [(10, -1), (52, 1), (66, 1), (78, -1)],
    [(11, -1), (44, 1), (67, 1), (76, -1)],
    [(10, 1), (53, -1), (60, -1), (79, 1)],
    [(11, 1), (45, -1), (61, -1), (77, 1)],
    [(12, -1), (54, 1), (74, 1), (78, -1)],
    [(13, -1), (46, 1), (75, 1), (76, -1)],
    [(12, 1), (55, -1), (72, -1), (79, 1)],
    [(13, 1), (47, -1), (73, -1), (77, 1)],
    [(42, -1), (50, 1), (68, 1), (76, -1)],
    [(43, -1), (48, 1), (69, 1), (76, -1)],
    [(32, 1), (51, -1), (62, -1), (77, 1)],
    [(33, 1), (49, -1), (63, -1), (77, 1)],
    [(42, -1), (58, 1), (70, 1), (78, -1)],
    [(43, -1), (56, 1), (71, 1), (78, -1)],
    [(32, 1), (59, -1), (64, -1), (79, 1)],
    [(33, 1), (57, -1), (65, -1), (79, 1)],
    [(17, 1), (21, 1), (80, -1), (84, -1)],
    [(16, 1), (23, 1), (81, -1), (82, -1)],
    [(19, -1), (20, -1), (80, 1), (85, 1)],
    [(18, -1), (22, -1), (81, 1), (83, 1)],
    [(3, 1), (7, 1), (84, -1), (86, -1)],
    [(2, 1), (9, 1), (82, -1), (87, -1)],
    [(5, -1), (6, -1), (85, 1), (86, 1)],
    [(4, -1), (8, -1), (83, 1), (87, 1)],
    [(35, 1), (39, 1), (86, -1), (88, -1)],
    [(34, 1), (41, 1), (87, -1), (88, -1)],
    [(37, -1), (38, -1), (80, 1), (89, 1)],
    [(36, -1), (40, -1), (81, 1), (89, 1)],
    [(25, 1), (29, 1), (86, -1), (90, -1)],
    [(24, 1), (31, 1), (87, -1), (90, -1)],
    [(27, -1), (28, -1), (80, 1), (91, 1)],
    [(26, -1), (30, -1), (81, 1), (91, 1)],
    [(47, 1), (73, 1), (82, -1), (94, -1)],
    [(55, 1), (72, 1), (83, -1), (92, -1)],
    [(46, -1), (75, -1), (82, 1), (95, 1)],
    [(54, -1), (74, -1), (83, 1), (93, 1)],
    [(45, 1), (61, 1), (84, -1), (94, -1)],
    [(53, 1), (60, 1), (85, -1), (92, -1)],
    [(44, -1), (67, -1), (84, 1), (95, 1)],
    [(52, -1), (66, -1), (85, 1), (93, 1)],
    [(57, 1), (65, 1), (90, -1), (92, -1)],
    [(59, 1), (64, 1), (91, -1), (92, -1)],
    [(56, -1), (71, -1), (88, 1), (93, 1)],
    [(58, -1), (70, -1), (89, 1), (93, 1)],
    [(49, 1), (63, 1), (90, -1), (94, -1)],
    [(51, 1), (62, 1), (91, -1), (94, -1)],
    [(48, -1), (69, -1), (88, 1), (95, 1)],
    [(50, -1), (68, -1), (89, 1), (95, 1)],
  ]

/-- `∂_3 : C_3 → C_2`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `32` generators of `C_3` -/
def cusp5Bdtwo : SOp 96 32 :=
  SOp.ofList [
    [(4, -1), (12, 1), (28, -1), (44, -1), (52, 1), (60, -1)],
    [(5, -1), (13, 1), (29, -1), (36, -1), (48, 1), (60, -1)],
    [(6, -1), (12, -1), (20, 1), (45, 1), (53, -1), (56, 1)],
    [(7, -1), (13, -1), (21, 1), (37, 1), (49, -1), (56, 1)],
    [(0, -1), (14, -1), (24, -1), (46, 1), (52, 1), (61, -1)],
    [(1, -1), (15, -1), (25, -1), (38, 1), (48, 1), (61, -1)],
    [(2, -1), (14, 1), (16, 1), (47, -1), (53, -1), (57, 1)],
    [(3, -1), (15, 1), (17, 1), (39, -1), (49, -1), (57, 1)],
    [(4, 1), (8, -1), (30, -1), (40, 1), (54, 1), (62, -1)],
    [(5, 1), (9, -1), (31, -1), (32, 1), (50, 1), (62, -1)],
    [(6, 1), (8, 1), (22, 1), (41, -1), (55, -1), (58, 1)],
    [(7, 1), (9, 1), (23, 1), (33, -1), (51, -1), (58, 1)],
    [(0, 1), (10, 1), (26, -1), (42, -1), (54, 1), (63, -1)],
    [(1, 1), (11, 1), (27, -1), (34, -1), (50, 1), (63, -1)],
    [(2, 1), (10, -1), (18, 1), (43, 1), (55, -1), (59, 1)],
    [(3, 1), (11, -1), (19, 1), (35, 1), (51, -1), (59, 1)],
    [(19, 1), (35, 1), (68, -1), (76, 1), (84, 1), (92, -1)],
    [(18, 1), (43, 1), (69, -1), (77, 1), (80, 1), (92, -1)],
    [(27, -1), (34, -1), (70, -1), (76, -1), (85, -1), (88, 1)],
    [(26, -1), (42, -1), (71, -1), (77, -1), (81, -1), (88, 1)],
    [(23, 1), (33, -1), (64, -1), (78, -1), (84, 1), (93, -1)],
    [(22, 1), (41, -1), (65, -1), (79, -1), (80, 1), (93, -1)],
    [(31, -1), (32, 1), (66, -1), (78, 1), (85, -1), (89, 1)],
    [(30, -1), (40, 1), (67, -1), (79, 1), (81, -1), (89, 1)],
    [(17, 1), (39, -1), (68, 1), (72, -1), (86, 1), (94, -1)],
    [(16, 1), (47, -1), (69, 1), (73, -1), (82, 1), (94, -1)],
    [(25, -1), (38, 1), (70, 1), (72, 1), (87, -1), (90, 1)],
    [(24, -1), (46, 1), (71, 1), (73, 1), (83, -1), (90, 1)],
    [(21, 1), (37, 1), (64, 1), (74, 1), (86, 1), (95, -1)],
    [(20, 1), (45, 1), (65, 1), (75, 1), (82, 1), (95, -1)],
    [(29, -1), (36, -1), (66, 1), (74, -1), (87, -1), (91, 1)],
    [(28, -1), (44, -1), (67, 1), (75, -1), (83, -1), (91, 1)],
  ]

/-- The boundary of the complex, in the indexing of `FinChainCx`
(`bd k = ∂_{{k+1}} : C_{{k+1}} → C_k`). -/
def cusp5Bd : ∀ k, SOp (cusp5Dim k) (cusp5Dim (k+1))
  | 0 => cusp5Bdzero
  | 1 => cusp5Bdone
  | 2 => cusp5Bdtwo
  | _ => SOp.zero _ _

theorem cusp5BdCheck_zero : FinChainCx.bdCheckDeg cusp5Dim cusp5Bd 0 = true := by decide +kernel
theorem cusp5BdCheck_one : FinChainCx.bdCheckDeg cusp5Dim cusp5Bd 1 = true := by decide +kernel
theorem cusp5BdCheck_two : FinChainCx.bdCheckDeg cusp5Dim cusp5Bd 2 = true := by decide +kernel
theorem cusp5BdCheck_three : FinChainCx.bdCheckDeg cusp5Dim cusp5Bd 3 = true := by decide +kernel

/-- `∂ ∘ ∂ = 0`, checked one degree at a time. -/
theorem cusp5BdCheck (k : ℕ) (hk : k < 4) :
    FinChainCx.bdCheckDeg cusp5Dim cusp5Bd k = true := by
  interval_cases k
  exacts [cusp5BdCheck_zero, cusp5BdCheck_one, cusp5BdCheck_two, cusp5BdCheck_three]

/-- **The cell complex** (a finite free `ℤ`-chain complex). -/
def cusp5Cx : FinChainCx where
  dim := cusp5Dim
  bd := cusp5Bd
  bd_comp := FinChainCx.bdCheck_sound (fun k hk => cusp5Dim_eq_zero k hk)
    (FinChainCx.bdCheck_of_pieces fun k hk => cusp5BdCheck k hk)

/-- The ranks of the homology: `1, 3, 3, 1` (and `0` above). -/
def cusp5B : ℕ → ℕ
  | 0 => 1 | 1 => 3 | 2 => 3 | 3 => 1
  | _ => 0

theorem cusp5B_eq_zero (k : ℕ) (hk : 4 ≤ k) : cusp5B k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 => rfl

/-- `Z_0 : ℤ^{1} → C_0` (the section: the generators map to cycles) -/
def cusp5Zzero : SOp 32 1 :=
  SOp.ofList [
    [(31, 1)],
  ]

/-- `Z_1 : ℤ^{3} → C_1` (the section: the generators map to cycles) -/
def cusp5Zone : SOp 96 3 :=
  SOp.ofList [
    [(12, -1), (14, -1), (18, 1), (20, 1), (28, -1), (30, 1), (66, -1), (74, 1)],
    [(3, 1), (8, 1), (12, -1), (14, -1), (15, 1), (17, -1), (18, 1), (25, -1), (28, -1), (30, 1), (31, -1), (90, 1)],
    [(15, -1), (17, 1), (21, 1), (44, -1), (67, -1), (95, 1)],
  ]

/-- `Z_2 : ℤ^{3} → C_2` (the section: the generators map to cycles) -/
def cusp5Ztwo : SOp 96 3 :=
  SOp.ofList [
    [(2, 1), (3, -1), (14, -1), (15, 1), (23, -1), (33, 1), (51, 1), (55, -1), (64, 1), (68, -1), (69, 1), (72, 1), (73, -1), (78, 1), (80, -1), (93, 1)],
    [(3, 1), (6, 1), (7, -1), (8, 1), (9, -1), (11, -1), (16, 1), (17, -1), (18, 1), (20, -1), (21, 1), (24, -1), (25, 1), (26, -1), (27, 1), (28, 1), (29, -1), (30, 1), (31, -1), (33, 1), (35, 1), (41, -1), (55, -1), (59, 1)],
    [(1, 1), (3, 1), (5, -1), (7, -1), (64, -1), (66, -1), (68, 1), (70, 1)],
  ]

/-- `Z_3 : ℤ^{1} → C_3` (the section: the generators map to cycles) -/
def cusp5Zthree : SOp 32 1 :=
  SOp.ofList [
    [(0, -1), (1, 1), (2, -1), (3, 1), (4, 1), (5, -1), (6, 1), (7, -1), (8, -1), (9, 1), (10, -1), (11, 1), (12, 1), (13, -1), (14, 1), (15, -1), (16, 1), (17, -1), (18, 1), (19, -1), (20, -1), (21, 1), (22, -1), (23, 1), (24, 1), (25, -1), (26, 1), (27, -1), (28, -1), (29, 1), (30, -1), (31, 1)],
  ]

/-- `ρ_0 : C_0 → ℤ^{1}` (the retraction) -/
def cusp5Rhozero : SOp 1 32 :=
  SOp.ofList [
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
    [(0, 1)],
  ]

/-- `ρ_1 : C_1 → ℤ^{3}` (the retraction) -/
def cusp5Rhoone : SOp 3 96 :=
  SOp.ofList [
    [(1, -1), (2, -1)],
    [(1, -1), (2, -1)],
    [],
    [],
    [(1, -1), (2, -1)],
    [(1, -1), (2, -1)],
    [],
    [(1, -1), (2, -1)],
    [],
    [],
    [],
    [],
    [],
    [(1, 1), (2, 1)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(1, 1), (2, 1)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(1, 1), (2, 1)],
    [],
    [(0, -1)],
    [],
    [(0, -1)],
    [],
    [],
    [(0, -1)],
    [(0, -1)],
    [(0, -1)],
    [(0, -1), (1, 1), (2, 1)],
    [],
    [],
    [(0, -1)],
    [],
    [(0, -1)],
    [],
    [(0, -1)],
    [],
    [],
    [],
    [(0, -1)],
    [],
    [(0, -1), (1, 1), (2, 1)],
    [(1, 1), (2, 1)],
    [(0, -1)],
    [],
    [],
    [],
    [],
    [(1, 1), (2, 1)],
    [],
    [],
    [],
    [],
    [],
    [(1, 1), (2, 1)],
    [],
    [],
    [],
    [(1, 1), (2, 1)],
    [(0, 1)],
    [(0, 1), (1, 1), (2, 1)],
    [],
    [],
    [],
    [],
    [(2, 1)],
    [(2, 1)],
    [(1, 1)],
    [(2, -1)],
    [(2, -1)],
    [(2, -1)],
    [(1, -1)],
    [(1, -1)],
    [(0, -1), (1, 1)],
    [(0, -1), (2, -1)],
    [(1, 1)],
    [(2, -1)],
    [(2, 1)],
    [(2, 1)],
    [(2, 1)],
    [(2, 1)],
  ]

/-- `ρ_2 : C_2 → ℤ^{3}` (the retraction) -/
def cusp5Rhotwo : SOp 3 96 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(1, -1)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(1, 1)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(2, 1)],
    [(2, 1)],
    [],
    [],
    [],
    [],
    [],
    [(0, 1)],
    [],
    [(0, -1)],
    [],
    [],
    [],
    [],
    [(0, 1)],
    [(0, 1)],
    [],
    [],
    [(0, 1), (2, 1)],
    [(0, 1)],
    [(2, -1)],
    [],
    [(0, 1)],
    [(0, 1)],
    [],
    [],
  ]

/-- `ρ_3 : C_3 → ℤ^{1}` (the retraction) -/
def cusp5Rhothree : SOp 1 32 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(0, 1)],
  ]

/-- `h_0 : C_0 → C_{1}` (the homotopy) -/
def cusp5Hzero : SOp 96 32 :=
  SOp.ofList [
    [(3, 1), (14, -1), (15, 1), (17, -1), (25, -1), (28, -1), (30, 1)],
    [(3, 1), (17, -1), (25, -1)],
    [(3, 1), (12, -1), (14, -1), (15, 1), (17, -1), (18, 1), (25, -1), (28, -1), (30, 1)],
    [(3, 1), (8, 1), (9, -1), (12, -1), (14, -1), (15, 1), (17, -1), (18, 1), (25, -1), (28, -1), (30, 1)],
    [(3, 1), (15, 1), (17, -1), (25, -1), (38, -1)],
    [(3, 1), (8, 1), (12, -1), (14, -1), (15, 1), (17, -1), (18, 1), (25, -1), (28, -1), (29, 1), (30, 1), (31, -1), (39, -1)],
    [(3, 1), (17, -1), (19, 1), (25, -1), (52, -1)],
    [(3, 1), (17, -1), (19, 1), (25, -1), (53, -1)],
    [(3, 1), (15, 1), (17, -1), (25, -1), (28, -1), (30, 1)],
    [(3, 1), (14, -1), (15, 1), (17, -1), (18, 1), (25, -1), (28, -1), (30, 1)],
    [(3, 1), (14, -1), (15, 1), (17, -1), (25, -1), (28, -1), (30, 1), (36, 1)],
    [(3, 1), (15, 1), (17, -1), (20, -1), (25, -1), (66, 1)],
    [(3, 1), (15, 1), (17, -1), (20, -1), (25, -1)],
    [(3, 1), (15, 1), (17, -1), (21, -1), (25, -1)],
    [(3, 1), (15, 1), (17, -1), (25, -1)],
    [(3, 1), (17, -1), (19, 1), (25, -1)],
    [(3, 1), (25, -1), (44, -1)],
    [(3, 1), (25, -1), (45, -1)],
    [(3, 1), (14, -1), (15, 1), (16, 1), (17, -1), (25, -1), (28, -1), (30, 1)],
    [(3, 1), (15, 1), (17, -1), (21, -1), (25, -1), (67, 1)],
    [(3, 1), (25, -1)],
    [(24, -1)],
    [(25, -1)],
    [(3, 1), (8, 1), (12, -1), (14, -1), (15, 1), (17, -1), (18, 1), (25, -1), (28, -1), (30, 1)],
    [(24, -1), (34, 1)],
    [(3, 1), (8, 1), (12, -1), (14, -1), (15, 1), (17, -1), (18, 1), (25, -1), (28, -1), (29, 1), (30, 1), (31, -1)],
    [(3, 1), (15, 1), (17, -1), (25, -1), (28, -1)],
    [(3, 1), (8, 1), (12, -1), (14, -1), (15, 1), (17, -1), (18, 1), (25, -1), (28, -1), (30, 1), (31, -1)],
    [(3, 1), (14, -1), (15, 1), (17, -1), (25, -1), (26, 1), (28, -1), (30, 1)],
    [(3, 1), (15, 1), (17, -1), (20, -1), (25, -1), (60, 1)],
    [(3, 1), (15, 1), (17, -1), (21, -1), (25, -1), (61, 1)],
    [],
  ]

/-- `h_1 : C_1 → C_{2}` (the homotopy) -/
def cusp5Hone : SOp 96 96 :=
  SOp.ofList [
    [(3, 1), (7, -1), (10, 1), (11, -1), (16, 1), (17, -1), (39, 1), (47, -1), (69, 1), (72, 1), (73, -1), (76, -1), (82, 1)],
    [(3, 1), (7, -1), (16, 1), (17, -1), (39, 1), (47, -1), (69, 1), (72, 1), (73, -1), (76, -1), (82, 1)],
    [(8, -1), (9, 1), (16, -1), (17, 1), (20, 1), (21, -1), (24, 1), (25, -1), (26, 1), (27, -1), (28, -1), (29, 1), (30, -1), (31, 1)],
    [],
    [(0, 1), (3, 1), (7, -1), (10, 1), (11, -1), (16, 1), (17, -1), (39, 1), (47, -1), (69, 1), (72, 1), (73, -1), (76, -1), (82, 1)],
    [(0, 1), (3, 1), (7, -1), (8, 1), (9, -1), (10, 1), (11, -1), (16, 1), (17, -1), (26, -1), (27, 1), (30, 1), (31, -1), (39, 1), (47, -1), (69, 1), (72, 1), (73, -1), (76, -1), (82, 1)],
    [(0, -1), (1, 1), (5, -1), (8, -1), (9, 1), (10, -1), (11, 1), (26, 1), (27, -1), (30, -1), (31, 1)],
    [(16, 1), (17, -1), (39, 1), (47, -1), (69, 1), (72, 1), (73, -1), (76, -1), (82, 1)],
    [],
    [],
    [(5, -1)],
    [(7, 1)],
    [],
    [(2, 1), (3, -1), (7, 1), (8, -1), (9, 1), (10, -1), (11, 1), (16, -2), (17, 2), (20, 1), (21, -1), (24, 1), (25, -1), (26, 1), (27, -1), (28, -1), (29, 1), (30, -1), (31, 1), (39, -1), (47, 1), (69, -1), (72, -1), (73, 1), (76, 1), (82, -1)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(4, 1)],
    [(2, 1), (3, -1), (6, -1), (7, 1), (8, -1), (9, 1), (10, -1), (11, 1), (16, -2), (17, 2), (20, 1), (21, -1), (24, 1), (25, -1), (26, 1), (27, -1), (28, -1), (29, 1), (30, -1), (31, 1), (39, -1), (47, 1), (69, -1), (72, -1), (73, 1), (76, 1), (82, -1)],
    [],
    [],
    [],
    [(8, -1), (9, 1)],
    [],
    [],
    [],
    [],
    [(8, -1)],
    [(3, -1), (7, 1), (11, 1), (16, -1), (17, 1), (39, -1), (47, 1), (69, -1), (72, -1), (73, 1), (76, 1), (82, -1)],
    [],
    [(0, 1), (1, -1), (5, 1), (8, 1), (9, -1), (14, 1), (15, -1), (26, -1), (27, 1), (30, 1), (31, -1), (38, 1), (46, -1)],
    [],
    [(0, 1), (1, -1), (5, 1), (14, 1), (15, -1), (24, 1), (25, -1), (28, -1), (29, 1), (38, 1), (46, -1)],
    [],
    [],
    [(0, 1), (1, -1), (5, 1), (12, 1), (13, -1), (14, 1), (15, -1), (24, 1), (25, -1), (28, -1), (29, 1), (38, 1), (46, -1)],
    [(0, 1), (1, -1), (5, 1), (8, 1), (9, -1), (10, 1), (11, -1), (26, -1), (27, 1), (30, 1), (31, -1), (38, 1), (46, -1)],
    [(0, 1), (1, -1), (5, 1), (13, -1), (14, 1), (15, -1), (24, 1), (25, -1), (28, -1), (29, 1), (38, 1), (46, -1)],
    [(0, 1), (1, -1), (3, -1), (5, 1), (7, 1), (8, 1), (9, -1), (14, 1), (16, -1), (17, 1), (26, -1), (27, 1), (30, 1), (31, -1), (38, 1), (39, -1), (46, -1), (47, 1), (69, -1), (72, -1), (73, 1), (76, 1), (82, -1)],
    [],
    [],
    [(0, 1), (1, -1), (5, 1), (14, 1), (15, -1), (20, 1), (21, -1), (24, 1), (25, -1), (28, -1), (29, 1), (38, 1), (46, -1)],
    [(6, 1), (7, -1), (33, 1), (41, -1), (51, 1), (55, -1)],
    [(0, 1), (1, -1), (5, 1), (8, 1), (9, -1), (14, 1), (15, -1), (17, -1), (26, -1), (27, 1), (30, 1), (31, -1), (38, 1), (46, -1)],
    [(6, 1), (7, -1), (8, 1), (9, -1), (16, 1), (17, -1), (18, 1), (20, -1), (21, 1), (24, -1), (25, 1), (26, -1), (27, 1), (28, 1), (29, -1), (30, 1), (31, -1), (33, 1), (41, -1), (51, 1), (55, -1)],
    [(0, 1), (1, -1), (5, 1), (14, 1), (15, -1), (21, -1), (24, 1), (25, -1), (28, -1), (29, 1), (38, 1), (46, -1)],
    [(8, -1), (9, 1), (23, 1)],
    [],
    [],
    [(0, 1), (1, -1), (5, 1), (14, 1), (15, -1), (24, 1), (25, -1), (38, 1), (46, -1)],
    [(8, -1), (9, 1), (30, -1), (31, 1)],
    [(1, -1), (3, -1), (5, 1), (7, 1), (10, -1), (11, 1), (14, 1), (15, -1), (16, -1), (17, 1), (25, -1), (38, 1), (39, -1), (46, -1), (47, 1), (69, -1), (72, -1), (73, 1), (76, 1), (82, -1)],
    [(0, -1), (3, -1), (7, 1), (8, -1), (9, 1), (10, -1), (11, 1), (16, -1), (17, 1), (26, 1), (30, -1), (31, 1), (39, -1), (47, 1), (69, -1), (72, -1), (73, 1), (76, 1), (82, -1)],
    [(0, 1), (1, -1), (5, 1), (14, 1), (15, -1), (24, 1), (25, -1), (28, -1), (38, 1), (46, -1)],
    [(8, -1), (9, 1), (31, 1)],
    [],
    [],
    [(33, -1)],
    [(3, -1), (6, -1), (7, 1), (8, -1), (9, 1), (11, 1), (16, -2), (17, 2), (18, -1), (20, 1), (21, -1), (24, 1), (25, -1), (26, 1), (27, -1), (28, -1), (29, 1), (30, -1), (31, 1), (33, -1), (39, -1), (41, 1), (47, 1), (55, 1), (59, -1), (69, -1), (72, -1), (73, 1), (76, 1), (82, -1)],
    [(32, -1)],
    [(0, 1), (1, -1), (5, 1), (8, 1), (9, -1), (10, 1), (11, -1), (26, -1), (27, 1), (30, 1), (31, -1), (34, 1)],
    [],
    [],
    [(7, -1), (13, -1), (21, 1), (49, -1), (56, 1)],
    [(16, -1), (17, 1), (47, 1), (69, -1), (72, -1), (73, 1), (76, 1), (82, -1)],
    [(36, -1)],
    [(0, 1), (1, -1), (5, 1), (8, 1), (9, -1), (10, 1), (11, -1), (26, -1), (27, 1), (30, 1), (31, -1), (38, 1)],
    [(4, 1), (32, -1), (40, 1)],
    [(2, 1), (3, -1), (6, -1), (7, 1), (8, -1), (9, 1), (10, -1), (11, 1), (16, -2), (17, 2), (20, 1), (21, -1), (24, 1), (25, -1), (26, 1), (27, -1), (28, -1), (29, 1), (30, -1), (31, 1), (33, -1), (39, -1), (41, 1), (47, 1), (69, -1), (72, -1), (73, 1), (76, 1), (82, -1)],
    [],
    [(0, -1), (1, 1), (5, -1), (8, -1), (9, 1), (10, -1), (11, 1), (16, -1), (17, 1), (26, 1), (27, -1), (30, -1), (31, 1), (38, -1), (46, 1), (69, -1), (72, -1), (73, 1), (76, 1), (82, -1)],
    [(7, -1), (49, -1)],
    [(7, -1), (51, 1)],
    [(5, 1), (48, -1)],
    [(5, 1), (50, 1)],
    [(16, -1), (17, 1), (39, -1), (47, 1), (64, -1), (68, 1), (69, -1), (72, -1), (73, 1), (82, -1)],
    [(2, 1), (3, -1), (6, -1), (7, 1), (14, -1), (15, 1), (16, -1), (17, 1), (39, -1), (47, 1), (65, -1), (82, -1)],
    [(8, -1), (9, 1), (10, -1), (11, 1), (14, 1), (15, -1), (16, -1), (17, 1), (20, 1), (21, -1), (24, 1), (25, -1), (26, 1), (27, -1), (28, -1), (29, 1), (30, -1), (31, 1), (69, -1), (72, -1), (73, 1), (76, 1)],
    [(2, -1), (3, 1), (4, 1), (6, 1), (7, -1), (14, 1), (15, -1), (16, 1), (17, -1), (39, 1), (47, -1), (65, 1), (67, 1), (82, 1)],
    [(16, 1), (17, -1), (39, 1), (47, -1), (68, -1), (69, 1), (72, 1), (73, -1), (82, 1)],
    [(16, 1), (17, -1), (39, 1), (47, -1), (64, 1), (66, 1), (68, -1), (69, 1), (72, 1), (73, -1), (82, 1)],
    [(76, -1)],
    [(10, 1), (11, -1), (14, -1), (15, 1), (72, 1), (73, -1), (76, -1)],
    [(0, 1), (1, -1), (5, 1), (8, 1), (9, -1), (14, 1), (15, -1), (26, -1), (27, 1), (30, 1), (31, -1), (38, 1), (46, -1), (72, -1), (76, 1)],
    [(0, 1), (1, -1), (5, 1), (14, 1), (15, -1), (16, 1), (17, -1), (24, 1), (25, -1), (28, -1), (29, 1), (38, 1), (39, 1), (46, -1), (47, -1), (64, 1), (68, -1), (69, 1), (72, 1), (73, -1), (74, 1), (82, 1)],
    [],
    [(8, -1), (9, 1), (16, 1), (17, -1), (39, 1), (47, -1), (64, 1), (68, -1), (69, 1), (72, 1), (73, -1), (78, 1), (82, 1)],
    [(2, 1), (3, -1), (6, -1), (7, 1), (8, -1), (9, 1), (14, -1), (15, 1), (16, -1), (17, 1), (30, -1), (31, 1), (32, -1), (39, -1), (40, 1), (47, 1), (65, -1), (67, -1), (81, -1), (82, -1)],
    [(0, 1), (1, -1), (2, 1), (3, -1), (4, -1), (5, 1), (6, -1), (7, 1), (16, -1), (17, 1), (24, 1), (25, -1), (38, 1), (39, -1), (46, -1), (47, 1), (65, -1), (67, -1), (82, -1), (83, 1)],
    [(2, 1), (3, -1), (14, -1), (15, 1), (16, -1), (17, 1), (39, -1), (47, 1), (51, 1), (55, -1), (80, -1), (82, -1)],
    [],
  ]

/-- `h_2 : C_2 → C_{3}` (the homotopy) -/
def cusp5Htwo : SOp 32 96 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(15, 1)],
    [],
    [],
    [(10, 1), (11, -1)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(3, 1)],
    [],
    [],
    [],
    [],
    [(8, 1), (9, -1), (12, -1), (13, 1)],
    [(14, 1)],
    [(0, -1), (1, 1), (4, 1), (5, -1)],
    [(2, 1), (6, -1), (7, 1)],
    [],
    [],
    [],
    [],
    [],
    [],
    [(4, 1), (5, -1)],
    [(6, -1), (7, 1)],
    [(8, 1), (9, -1)],
    [],
    [],
    [(7, 1)],
    [(11, 1)],
    [],
    [(1, -1)],
    [(5, -1)],
    [(9, -1)],
    [(13, -1)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(8, -1), (9, 1), (10, -1), (11, 1), (12, 1), (13, -1), (14, 1), (15, -1), (16, 1), (17, -1), (18, 1), (19, -1), (20, -1), (21, 1), (22, -1), (23, 1)],
    [],
    [],
    [],
    [(2, -1), (3, 1), (6, 1), (7, -1), (24, 1), (25, -1), (28, -1), (29, 1)],
    [],
    [(14, -1), (15, 1), (16, -1), (17, 1), (20, 1)],
    [],
    [(10, 1), (11, -1), (21, -1)],
    [],
    [],
    [],
    [],
    [(20, 1)],
    [(10, -1), (11, 1), (21, 1), (22, -1), (23, 1)],
    [(24, 1), (25, -1)],
    [(8, 1), (9, -1), (10, 1), (11, -1), (12, -1), (13, 1), (14, -1), (15, 1), (16, -1), (17, 1), (18, -1), (19, 1), (20, 1), (21, -1), (22, 1), (23, -1), (26, -1), (27, 1)],
    [(10, -1), (11, 1), (18, 1), (21, 1), (22, -1), (23, 1)],
    [(10, -1), (11, 1), (21, 1), (23, 1)],
    [(8, 1), (9, -1), (10, 1), (11, -1), (12, -1), (13, 1), (14, -1), (15, 1), (16, -1), (17, 1), (18, -1), (19, 1), (20, 1), (21, -1), (22, 1), (23, -1), (27, 1)],
    [(8, 1), (9, -1), (10, 1), (11, -1), (12, -1), (13, 1), (14, -1), (15, 1), (16, -1), (17, 1), (18, -1), (19, 1), (20, 1), (21, -1), (22, 1), (23, -1), (26, -1), (27, 1), (30, 1)],
    [(15, 1), (16, -1), (20, 1)],
    [],
    [(25, -1)],
    [(3, 1), (24, 1), (25, -1), (28, -1)],
  ]

/-- `h_3 : C_3 → C_{4}` (the homotopy) -/
def cusp5Hthree : SOp 0 32 :=
  SOp.ofList [
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
  ]

/-- The section in every degree. -/
def cusp5Z : ∀ k, SOp (cusp5Dim k) (cusp5B k)
  | 0 => cusp5Zzero
  | 1 => cusp5Zone
  | 2 => cusp5Ztwo
  | 3 => cusp5Zthree
  | _ => SOp.zero _ _

/-- The retraction in every degree. -/
def cusp5Rho : ∀ k, SOp (cusp5B k) (cusp5Dim k)
  | 0 => cusp5Rhozero
  | 1 => cusp5Rhoone
  | 2 => cusp5Rhotwo
  | 3 => cusp5Rhothree
  | _ => SOp.zero _ _

/-- The homotopy in every degree. -/
def cusp5H : ∀ k, SOp (cusp5Dim (k+1)) (cusp5Dim k)
  | 0 => cusp5Hzero
  | 1 => cusp5Hone
  | 2 => cusp5Htwo
  | 3 => cusp5Hthree
  | _ => SOp.zero _ _

/-- **The strong deformation retract certificate.** -/
def cusp5SDR : SDR cusp5Cx where
  N := 4
  b := cusp5B
  Z := cusp5Z
  ρ := cusp5Rho
  h := cusp5H
  dim_zero := fun k hk => cusp5Dim_eq_zero k hk
  b_zero := fun k hk => cusp5B_eq_zero k hk

theorem cusp5SDR_checkHomZero : cusp5SDR.checkHomZero = true := by decide +kernel

theorem cusp5SDR_checkZ_zero : cusp5SDR.checkZ 0 = true := by decide +kernel
theorem cusp5SDR_checkZ_one : cusp5SDR.checkZ 1 = true := by decide +kernel
theorem cusp5SDR_checkZ_two : cusp5SDR.checkZ 2 = true := by decide +kernel
theorem cusp5SDR_checkZ_three : cusp5SDR.checkZ 3 = true := by decide +kernel

theorem cusp5SDR_checkZ (k : ℕ) (hk : k < 4) : cusp5SDR.checkZ k = true := by
  interval_cases k
  exacts [cusp5SDR_checkZ_zero, cusp5SDR_checkZ_one, cusp5SDR_checkZ_two, cusp5SDR_checkZ_three]

theorem cusp5SDR_checkRho_zero : cusp5SDR.checkRho 0 = true := by decide +kernel
theorem cusp5SDR_checkRho_one : cusp5SDR.checkRho 1 = true := by decide +kernel
theorem cusp5SDR_checkRho_two : cusp5SDR.checkRho 2 = true := by decide +kernel
theorem cusp5SDR_checkRho_three : cusp5SDR.checkRho 3 = true := by decide +kernel

theorem cusp5SDR_checkRho (k : ℕ) (hk : k < 4) : cusp5SDR.checkRho k = true := by
  interval_cases k
  exacts [cusp5SDR_checkRho_zero, cusp5SDR_checkRho_one, cusp5SDR_checkRho_two, cusp5SDR_checkRho_three]

theorem cusp5SDR_checkRhoZ_zero : cusp5SDR.checkRhoZ 0 = true := by decide +kernel
theorem cusp5SDR_checkRhoZ_one : cusp5SDR.checkRhoZ 1 = true := by decide +kernel
theorem cusp5SDR_checkRhoZ_two : cusp5SDR.checkRhoZ 2 = true := by decide +kernel
theorem cusp5SDR_checkRhoZ_three : cusp5SDR.checkRhoZ 3 = true := by decide +kernel

theorem cusp5SDR_checkRhoZ (k : ℕ) (hk : k < 4) : cusp5SDR.checkRhoZ k = true := by
  interval_cases k
  exacts [cusp5SDR_checkRhoZ_zero, cusp5SDR_checkRhoZ_one, cusp5SDR_checkRhoZ_two, cusp5SDR_checkRhoZ_three]

theorem cusp5SDR_checkHom_zero : cusp5SDR.checkHom 0 = true := by decide +kernel
theorem cusp5SDR_checkHom_one : cusp5SDR.checkHom 1 = true := by decide +kernel
theorem cusp5SDR_checkHom_two : cusp5SDR.checkHom 2 = true := by decide +kernel
theorem cusp5SDR_checkHom_three : cusp5SDR.checkHom 3 = true := by decide +kernel

theorem cusp5SDR_checkHom (k : ℕ) (hk : k < 4) : cusp5SDR.checkHom k = true := by
  interval_cases k
  exacts [cusp5SDR_checkHom_zero, cusp5SDR_checkHom_one, cusp5SDR_checkHom_two, cusp5SDR_checkHom_three]

/-- **The certificate passes**: `∂Z = 0`, `ρ∂ = 0`, `ρZ = 1` and `1 - Zρ = ∂h + h∂`. -/
theorem cusp5SDR_check : cusp5SDR.check = true :=
  SDR.check_of_pieces cusp5SDR cusp5SDR_checkHomZero (fun k hk =>
    ⟨cusp5SDR_checkZ k hk, cusp5SDR_checkRho k hk, cusp5SDR_checkRhoZ k hk,
      cusp5SDR_checkHom k hk⟩)

/-- **The homology of the complex**: `H_k ≅ ℤ^{cusp5 k}`. -/
theorem cusp5Cx_homology (k : ℕ) :
    Nonempty (cusp5Cx.homology k ≅ ModuleCat.of ℤ (Fin (cusp5B k) → ℤ)) :=
  SDR.sound cusp5SDR cusp5SDR_check k

