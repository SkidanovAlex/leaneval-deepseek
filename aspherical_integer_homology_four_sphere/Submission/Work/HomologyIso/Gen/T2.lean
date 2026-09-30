/-
# `HomologyIso/`: generated SDR data (the filling torus T²)

**This file is generated** by `Submission/Work/HomologyIso/scripts/gen_sdr_data.py` from the exact
Ratcliffe--Tschantz data in `rtdata/`; do not edit by hand, rerun the script.

The minimal cell structure of the `(y₂,y₃)` torus `T²_v`: one vertex, two
loops and one face, with all boundaries zero.  Its homology is
`(ℤ, ℤ², ℤ)` — the graded ranks of `H_k(B) = ⊕_v H_k(T²_v)`.

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


/-- The number of cells in each dimension: `1, 2, 1` (and `0` above). -/
def t2Dim : ℕ → ℕ
  | 0 => 1 | 1 => 2 | 2 => 1
  | _ => 0

/-- The complex has no cells in degree `≥ 3`. -/
theorem t2Dim_eq_zero (k : ℕ) (hk : 3 ≤ k) : t2Dim k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | k + 3 => rfl

/-- `∂_1 : C_1 → C_0`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `2` generators of `C_1` -/
def t2Bdzero : SOp 1 2 :=
  SOp.ofList [
    [],
    [],
  ]

/-- `∂_2 : C_2 → C_1`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `1` generators of `C_2` -/
def t2Bdone : SOp 2 1 :=
  SOp.ofList [
    [],
  ]

/-- The boundary of the complex, in the indexing of `FinChainCx`
(`bd k = ∂_{{k+1}} : C_{{k+1}} → C_k`). -/
def t2Bd : ∀ k, SOp (t2Dim k) (t2Dim (k+1))
  | 0 => t2Bdzero
  | 1 => t2Bdone
  | _ => SOp.zero _ _

theorem t2BdCheck_zero : FinChainCx.bdCheckDeg t2Dim t2Bd 0 = true := by decide
theorem t2BdCheck_one : FinChainCx.bdCheckDeg t2Dim t2Bd 1 = true := by decide
theorem t2BdCheck_two : FinChainCx.bdCheckDeg t2Dim t2Bd 2 = true := by decide

/-- `∂ ∘ ∂ = 0`, checked one degree at a time. -/
theorem t2BdCheck (k : ℕ) (hk : k < 3) :
    FinChainCx.bdCheckDeg t2Dim t2Bd k = true := by
  interval_cases k <;> (first | rfl | decide)

/-- **The cell complex** (a finite free `ℤ`-chain complex). -/
def t2Cx : FinChainCx where
  dim := t2Dim
  bd := t2Bd
  bd_comp := FinChainCx.bdCheck_sound (fun k hk => t2Dim_eq_zero k hk)
    (FinChainCx.bdCheck_of_pieces fun k hk => t2BdCheck k hk)

/-- The ranks of the homology: `1, 2, 1` (and `0` above). -/
def t2B : ℕ → ℕ
  | 0 => 1 | 1 => 2 | 2 => 1
  | _ => 0

theorem t2B_eq_zero (k : ℕ) (hk : 3 ≤ k) : t2B k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | k + 3 => rfl

/-- `Z_0 : ℤ^{1} → C_0` (the section: the generators map to cycles) -/
def t2Zzero : SOp 1 1 :=
  SOp.ofList [
    [(0, 1)],
  ]

/-- `Z_1 : ℤ^{2} → C_1` (the section: the generators map to cycles) -/
def t2Zone : SOp 2 2 :=
  SOp.ofList [
    [(0, 1)],
    [(1, 1)],
  ]

/-- `Z_2 : ℤ^{1} → C_2` (the section: the generators map to cycles) -/
def t2Ztwo : SOp 1 1 :=
  SOp.ofList [
    [(0, 1)],
  ]

/-- `ρ_0 : C_0 → ℤ^{1}` (the retraction) -/
def t2Rhozero : SOp 1 1 :=
  SOp.ofList [
    [(0, 1)],
  ]

/-- `ρ_1 : C_1 → ℤ^{2}` (the retraction) -/
def t2Rhoone : SOp 2 2 :=
  SOp.ofList [
    [(0, 1)],
    [(1, 1)],
  ]

/-- `ρ_2 : C_2 → ℤ^{1}` (the retraction) -/
def t2Rhotwo : SOp 1 1 :=
  SOp.ofList [
    [(0, 1)],
  ]

/-- `h_0 : C_0 → C_{1}` (the homotopy) -/
def t2Hzero : SOp 2 1 :=
  SOp.ofList [
    [],
  ]

/-- `h_1 : C_1 → C_{2}` (the homotopy) -/
def t2Hone : SOp 1 2 :=
  SOp.ofList [
    [],
    [],
  ]

/-- `h_2 : C_2 → C_{3}` (the homotopy) -/
def t2Htwo : SOp 0 1 :=
  SOp.ofList [
    [],
  ]

/-- The section in every degree. -/
def t2Z : ∀ k, SOp (t2Dim k) (t2B k)
  | 0 => t2Zzero
  | 1 => t2Zone
  | 2 => t2Ztwo
  | _ => SOp.zero _ _

/-- The retraction in every degree. -/
def t2Rho : ∀ k, SOp (t2B k) (t2Dim k)
  | 0 => t2Rhozero
  | 1 => t2Rhoone
  | 2 => t2Rhotwo
  | _ => SOp.zero _ _

/-- The homotopy in every degree. -/
def t2H : ∀ k, SOp (t2Dim (k+1)) (t2Dim k)
  | 0 => t2Hzero
  | 1 => t2Hone
  | 2 => t2Htwo
  | _ => SOp.zero _ _

/-- **The strong deformation retract certificate.** -/
def t2SDR : SDR t2Cx where
  N := 3
  b := t2B
  Z := t2Z
  ρ := t2Rho
  h := t2H
  dim_zero := fun k hk => t2Dim_eq_zero k hk
  b_zero := fun k hk => t2B_eq_zero k hk

theorem t2SDR_checkHomZero : t2SDR.checkHomZero = true := by decide

theorem t2SDR_checkZ_zero : t2SDR.checkZ 0 = true := by decide
theorem t2SDR_checkZ_one : t2SDR.checkZ 1 = true := by decide
theorem t2SDR_checkZ_two : t2SDR.checkZ 2 = true := by decide

theorem t2SDR_checkZ (k : ℕ) (hk : k < 3) : t2SDR.checkZ k = true := by
  interval_cases k <;> (first | rfl | decide)

theorem t2SDR_checkRho_zero : t2SDR.checkRho 0 = true := by decide
theorem t2SDR_checkRho_one : t2SDR.checkRho 1 = true := by decide
theorem t2SDR_checkRho_two : t2SDR.checkRho 2 = true := by decide

theorem t2SDR_checkRho (k : ℕ) (hk : k < 3) : t2SDR.checkRho k = true := by
  interval_cases k <;> (first | rfl | decide)

theorem t2SDR_checkRhoZ_zero : t2SDR.checkRhoZ 0 = true := by decide
theorem t2SDR_checkRhoZ_one : t2SDR.checkRhoZ 1 = true := by decide
theorem t2SDR_checkRhoZ_two : t2SDR.checkRhoZ 2 = true := by decide

theorem t2SDR_checkRhoZ (k : ℕ) (hk : k < 3) : t2SDR.checkRhoZ k = true := by
  interval_cases k <;> (first | rfl | decide)

theorem t2SDR_checkHom_zero : t2SDR.checkHom 0 = true := by decide
theorem t2SDR_checkHom_one : t2SDR.checkHom 1 = true := by decide
theorem t2SDR_checkHom_two : t2SDR.checkHom 2 = true := by decide

theorem t2SDR_checkHom (k : ℕ) (hk : k < 3) : t2SDR.checkHom k = true := by
  interval_cases k <;> (first | rfl | decide)

/-- **The certificate passes**: `∂Z = 0`, `ρ∂ = 0`, `ρZ = 1` and `1 - Zρ = ∂h + h∂`. -/
theorem t2SDR_check : t2SDR.check = true :=
  SDR.check_of_pieces t2SDR t2SDR_checkHomZero (fun k hk =>
    ⟨t2SDR_checkZ k hk, t2SDR_checkRho k hk, t2SDR_checkRhoZ k hk,
      t2SDR_checkHom k hk⟩)

/-- **The homology of the complex**: `H_k ≅ ℤ^{t2 k}`. -/
theorem t2Cx_homology (k : ℕ) :
    Nonempty (t2Cx.homology k ≅ ModuleCat.of ℤ (Fin (t2B k) → ℤ)) :=
  SDR.sound t2SDR t2SDR_check k

end Work.HomologyIso.Gen
