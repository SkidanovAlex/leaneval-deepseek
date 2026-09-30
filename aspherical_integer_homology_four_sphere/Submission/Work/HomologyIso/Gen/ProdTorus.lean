/-
# `HomologyIso/`: generated SDR data (the product torus B_v)

**This file is generated** by `Submission/Work/HomologyIso/scripts/gen_sdr_data.py` from the exact
Ratcliffe--Tschantz data in `rtdata/`; do not edit by hand, rerun the script.

The product cell structure `S¹_u × T²_{y₂,y₃}`: the `u`-circle has four
edges (the perimeter of the square), and the `y₂`- and `y₃`-circles have a
single vertex and a single loop each, so that all boundaries in those two
directions vanish.  `4/12/12/4` cells, homology `(ℤ, ℤ³, ℤ³, ℤ)`.

This is the boundary of the filling piece (the glued `T³`), the second side
of the torus bridge of `rtdata/data/mv_certificate.json`.

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
def prodTorusDim : ℕ → ℕ
  | 0 => 4 | 1 => 12 | 2 => 12 | 3 => 4
  | _ => 0

/-- The complex has no cells in degree `≥ 4`. -/
theorem prodTorusDim_eq_zero (k : ℕ) (hk : 4 ≤ k) : prodTorusDim k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 => rfl

/-- `∂_1 : C_1 → C_0`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `12` generators of `C_1` -/
def prodTorusBdzero : SOp 4 12 :=
  SOp.ofList [
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([(0, -1), (1, 1)] : List (Fin 4 × ℤ)),
    ([(1, -1), (2, 1)] : List (Fin 4 × ℤ)),
    ([(2, -1), (3, 1)] : List (Fin 4 × ℤ)),
    ([(0, 1), (3, -1)] : List (Fin 4 × ℤ)),
  ]

/-- `∂_2 : C_2 → C_1`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `12` generators of `C_2` -/
def prodTorusBdone : SOp 12 12 :=
  SOp.ofList [
    ([] : List (Fin 12 × ℤ)),
    ([] : List (Fin 12 × ℤ)),
    ([] : List (Fin 12 × ℤ)),
    ([] : List (Fin 12 × ℤ)),
    ([(0, -1), (2, 1)] : List (Fin 12 × ℤ)),
    ([(1, -1), (3, 1)] : List (Fin 12 × ℤ)),
    ([(2, -1), (4, 1)] : List (Fin 12 × ℤ)),
    ([(3, -1), (5, 1)] : List (Fin 12 × ℤ)),
    ([(4, -1), (6, 1)] : List (Fin 12 × ℤ)),
    ([(5, -1), (7, 1)] : List (Fin 12 × ℤ)),
    ([(0, 1), (6, -1)] : List (Fin 12 × ℤ)),
    ([(1, 1), (7, -1)] : List (Fin 12 × ℤ)),
  ]

/-- `∂_3 : C_3 → C_2`, the boundary of the complex in the indexing of
`FinChainCx`: the images of the `4` generators of `C_3` -/
def prodTorusBdtwo : SOp 12 4 :=
  SOp.ofList [
    ([(0, -1), (1, 1)] : List (Fin 12 × ℤ)),
    ([(1, -1), (2, 1)] : List (Fin 12 × ℤ)),
    ([(2, -1), (3, 1)] : List (Fin 12 × ℤ)),
    ([(0, 1), (3, -1)] : List (Fin 12 × ℤ)),
  ]

/-- The boundary of the complex, in the indexing of `FinChainCx`
(`bd k = ∂_{{k+1}} : C_{{k+1}} → C_k`). -/
def prodTorusBd : ∀ k, SOp (prodTorusDim k) (prodTorusDim (k+1))
  | 0 => prodTorusBdzero
  | 1 => prodTorusBdone
  | 2 => prodTorusBdtwo
  | _ => SOp.zero _ _

theorem prodTorusBdCheck_zero : FinChainCx.bdCheckDeg prodTorusDim prodTorusBd 0 = true := by decide
theorem prodTorusBdCheck_one : FinChainCx.bdCheckDeg prodTorusDim prodTorusBd 1 = true := by decide
theorem prodTorusBdCheck_two : FinChainCx.bdCheckDeg prodTorusDim prodTorusBd 2 = true := by decide
theorem prodTorusBdCheck_three : FinChainCx.bdCheckDeg prodTorusDim prodTorusBd 3 = true := by decide

/-- `∂ ∘ ∂ = 0`, checked one degree at a time. -/
theorem prodTorusBdCheck (k : ℕ) (hk : k < 4) :
    FinChainCx.bdCheckDeg prodTorusDim prodTorusBd k = true := by
  interval_cases k
  exacts [prodTorusBdCheck_zero, prodTorusBdCheck_one, prodTorusBdCheck_two, prodTorusBdCheck_three]

/-- **The cell complex** (a finite free `ℤ`-chain complex). -/
def prodTorusCx : FinChainCx where
  dim := prodTorusDim
  bd := prodTorusBd
  bd_comp := FinChainCx.bdCheck_sound (fun k hk => prodTorusDim_eq_zero k hk)
    (FinChainCx.bdCheck_of_pieces fun k hk => prodTorusBdCheck k hk)

/-- The ranks of the homology: `1, 3, 3, 1` (and `0` above). -/
def prodTorusB : ℕ → ℕ
  | 0 => 1 | 1 => 3 | 2 => 3 | 3 => 1
  | _ => 0

theorem prodTorusB_eq_zero (k : ℕ) (hk : 4 ≤ k) : prodTorusB k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 => rfl

/-- `Z_0 : ℤ^{1} → C_0` (the section: the generators map to cycles) -/
def prodTorusZzero : SOp 4 1 :=
  SOp.ofList [
    ([(3, 1)] : List (Fin 4 × ℤ)),
  ]

/-- `Z_1 : ℤ^{3} → C_1` (the section: the generators map to cycles) -/
def prodTorusZone : SOp 12 3 :=
  SOp.ofList [
    ([(1, 1)] : List (Fin 12 × ℤ)),
    ([(2, 1)] : List (Fin 12 × ℤ)),
    ([(8, 1), (9, 1), (10, 1), (11, 1)] : List (Fin 12 × ℤ)),
  ]

/-- `Z_2 : ℤ^{3} → C_2` (the section: the generators map to cycles) -/
def prodTorusZtwo : SOp 12 3 :=
  SOp.ofList [
    ([(1, 1)] : List (Fin 12 × ℤ)),
    ([(4, 1), (6, 1), (8, 1), (10, 1)] : List (Fin 12 × ℤ)),
    ([(5, 1), (7, 1), (9, 1), (11, 1)] : List (Fin 12 × ℤ)),
  ]

/-- `Z_3 : ℤ^{1} → C_3` (the section: the generators map to cycles) -/
def prodTorusZthree : SOp 4 1 :=
  SOp.ofList [
    ([(0, 1), (1, 1), (2, 1), (3, 1)] : List (Fin 4 × ℤ)),
  ]

/-- `ρ_0 : C_0 → ℤ^{1}` (the retraction) -/
def prodTorusRhozero : SOp 1 4 :=
  SOp.ofList [
    ([(0, 1)] : List (Fin 1 × ℤ)),
    ([(0, 1)] : List (Fin 1 × ℤ)),
    ([(0, 1)] : List (Fin 1 × ℤ)),
    ([(0, 1)] : List (Fin 1 × ℤ)),
  ]

/-- `ρ_1 : C_1 → ℤ^{3}` (the retraction) -/
def prodTorusRhoone : SOp 3 12 :=
  SOp.ofList [
    ([(1, 1)] : List (Fin 3 × ℤ)),
    ([(0, 1)] : List (Fin 3 × ℤ)),
    ([(1, 1)] : List (Fin 3 × ℤ)),
    ([(0, 1)] : List (Fin 3 × ℤ)),
    ([(1, 1)] : List (Fin 3 × ℤ)),
    ([(0, 1)] : List (Fin 3 × ℤ)),
    ([(1, 1)] : List (Fin 3 × ℤ)),
    ([(0, 1)] : List (Fin 3 × ℤ)),
    ([] : List (Fin 3 × ℤ)),
    ([] : List (Fin 3 × ℤ)),
    ([] : List (Fin 3 × ℤ)),
    ([(2, 1)] : List (Fin 3 × ℤ)),
  ]

/-- `ρ_2 : C_2 → ℤ^{3}` (the retraction) -/
def prodTorusRhotwo : SOp 3 12 :=
  SOp.ofList [
    ([(0, 1)] : List (Fin 3 × ℤ)),
    ([(0, 1)] : List (Fin 3 × ℤ)),
    ([(0, 1)] : List (Fin 3 × ℤ)),
    ([(0, 1)] : List (Fin 3 × ℤ)),
    ([] : List (Fin 3 × ℤ)),
    ([] : List (Fin 3 × ℤ)),
    ([] : List (Fin 3 × ℤ)),
    ([] : List (Fin 3 × ℤ)),
    ([] : List (Fin 3 × ℤ)),
    ([] : List (Fin 3 × ℤ)),
    ([(1, 1)] : List (Fin 3 × ℤ)),
    ([(2, 1)] : List (Fin 3 × ℤ)),
  ]

/-- `ρ_3 : C_3 → ℤ^{1}` (the retraction) -/
def prodTorusRhothree : SOp 1 4 :=
  SOp.ofList [
    ([] : List (Fin 1 × ℤ)),
    ([] : List (Fin 1 × ℤ)),
    ([] : List (Fin 1 × ℤ)),
    ([(0, 1)] : List (Fin 1 × ℤ)),
  ]

/-- `h_0 : C_0 → C_{1}` (the homotopy) -/
def prodTorusHzero : SOp 12 4 :=
  SOp.ofList [
    ([(8, -1), (9, -1), (10, -1)] : List (Fin 12 × ℤ)),
    ([(9, -1), (10, -1)] : List (Fin 12 × ℤ)),
    ([(10, -1)] : List (Fin 12 × ℤ)),
    ([] : List (Fin 12 × ℤ)),
  ]

/-- `h_1 : C_1 → C_{2}` (the homotopy) -/
def prodTorusHone : SOp 12 12 :=
  SOp.ofList [
    ([(4, -1)] : List (Fin 12 × ℤ)),
    ([] : List (Fin 12 × ℤ)),
    ([] : List (Fin 12 × ℤ)),
    ([(5, 1)] : List (Fin 12 × ℤ)),
    ([(6, 1)] : List (Fin 12 × ℤ)),
    ([(5, 1), (7, 1)] : List (Fin 12 × ℤ)),
    ([(6, 1), (8, 1)] : List (Fin 12 × ℤ)),
    ([(5, 1), (7, 1), (9, 1)] : List (Fin 12 × ℤ)),
    ([] : List (Fin 12 × ℤ)),
    ([] : List (Fin 12 × ℤ)),
    ([] : List (Fin 12 × ℤ)),
    ([] : List (Fin 12 × ℤ)),
  ]

/-- `h_2 : C_2 → C_{3}` (the homotopy) -/
def prodTorusHtwo : SOp 4 12 :=
  SOp.ofList [
    ([(0, -1)] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([(1, 1)] : List (Fin 4 × ℤ)),
    ([(1, 1), (2, 1)] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
    ([] : List (Fin 4 × ℤ)),
  ]

/-- `h_3 : C_3 → C_{4}` (the homotopy) -/
def prodTorusHthree : SOp 0 4 :=
  SOp.ofList [
    ([] : List (Fin 0 × ℤ)),
    ([] : List (Fin 0 × ℤ)),
    ([] : List (Fin 0 × ℤ)),
    ([] : List (Fin 0 × ℤ)),
  ]

/-- The section in every degree. -/
def prodTorusZ : ∀ k, SOp (prodTorusDim k) (prodTorusB k)
  | 0 => prodTorusZzero
  | 1 => prodTorusZone
  | 2 => prodTorusZtwo
  | 3 => prodTorusZthree
  | _ => SOp.zero _ _

/-- The retraction in every degree. -/
def prodTorusRho : ∀ k, SOp (prodTorusB k) (prodTorusDim k)
  | 0 => prodTorusRhozero
  | 1 => prodTorusRhoone
  | 2 => prodTorusRhotwo
  | 3 => prodTorusRhothree
  | _ => SOp.zero _ _

/-- The homotopy in every degree. -/
def prodTorusH : ∀ k, SOp (prodTorusDim (k+1)) (prodTorusDim k)
  | 0 => prodTorusHzero
  | 1 => prodTorusHone
  | 2 => prodTorusHtwo
  | 3 => prodTorusHthree
  | _ => SOp.zero _ _

/-- **The strong deformation retract certificate.** -/
def prodTorusSDR : SDR prodTorusCx where
  N := 4
  b := prodTorusB
  Z := prodTorusZ
  ρ := prodTorusRho
  h := prodTorusH
  dim_zero := fun k hk => prodTorusDim_eq_zero k hk
  b_zero := fun k hk => prodTorusB_eq_zero k hk

theorem prodTorusSDR_checkHomZero : prodTorusSDR.checkHomZero = true := by decide

theorem prodTorusSDR_checkZ_zero : prodTorusSDR.checkZ 0 = true := by decide
theorem prodTorusSDR_checkZ_one : prodTorusSDR.checkZ 1 = true := by decide
theorem prodTorusSDR_checkZ_two : prodTorusSDR.checkZ 2 = true := by decide
theorem prodTorusSDR_checkZ_three : prodTorusSDR.checkZ 3 = true := by decide

theorem prodTorusSDR_checkZ (k : ℕ) (hk : k < 4) : prodTorusSDR.checkZ k = true := by
  interval_cases k
  exacts [prodTorusSDR_checkZ_zero, prodTorusSDR_checkZ_one, prodTorusSDR_checkZ_two, prodTorusSDR_checkZ_three]

theorem prodTorusSDR_checkRho_zero : prodTorusSDR.checkRho 0 = true := by decide
theorem prodTorusSDR_checkRho_one : prodTorusSDR.checkRho 1 = true := by decide
theorem prodTorusSDR_checkRho_two : prodTorusSDR.checkRho 2 = true := by decide
theorem prodTorusSDR_checkRho_three : prodTorusSDR.checkRho 3 = true := by decide

theorem prodTorusSDR_checkRho (k : ℕ) (hk : k < 4) : prodTorusSDR.checkRho k = true := by
  interval_cases k
  exacts [prodTorusSDR_checkRho_zero, prodTorusSDR_checkRho_one, prodTorusSDR_checkRho_two, prodTorusSDR_checkRho_three]

theorem prodTorusSDR_checkRhoZ_zero : prodTorusSDR.checkRhoZ 0 = true := by decide
theorem prodTorusSDR_checkRhoZ_one : prodTorusSDR.checkRhoZ 1 = true := by decide
theorem prodTorusSDR_checkRhoZ_two : prodTorusSDR.checkRhoZ 2 = true := by decide
theorem prodTorusSDR_checkRhoZ_three : prodTorusSDR.checkRhoZ 3 = true := by decide

theorem prodTorusSDR_checkRhoZ (k : ℕ) (hk : k < 4) : prodTorusSDR.checkRhoZ k = true := by
  interval_cases k
  exacts [prodTorusSDR_checkRhoZ_zero, prodTorusSDR_checkRhoZ_one, prodTorusSDR_checkRhoZ_two, prodTorusSDR_checkRhoZ_three]

theorem prodTorusSDR_checkHom_zero : prodTorusSDR.checkHom 0 = true := by decide
theorem prodTorusSDR_checkHom_one : prodTorusSDR.checkHom 1 = true := by decide
theorem prodTorusSDR_checkHom_two : prodTorusSDR.checkHom 2 = true := by decide
theorem prodTorusSDR_checkHom_three : prodTorusSDR.checkHom 3 = true := by decide

theorem prodTorusSDR_checkHom (k : ℕ) (hk : k < 4) : prodTorusSDR.checkHom k = true := by
  interval_cases k
  exacts [prodTorusSDR_checkHom_zero, prodTorusSDR_checkHom_one, prodTorusSDR_checkHom_two, prodTorusSDR_checkHom_three]

/-- **The certificate passes**: `∂Z = 0`, `ρ∂ = 0`, `ρZ = 1` and `1 - Zρ = ∂h + h∂`. -/
theorem prodTorusSDR_check : prodTorusSDR.check = true :=
  SDR.check_of_pieces prodTorusSDR prodTorusSDR_checkHomZero (fun k hk =>
    ⟨prodTorusSDR_checkZ k hk, prodTorusSDR_checkRho k hk, prodTorusSDR_checkRhoZ k hk,
      prodTorusSDR_checkHom k hk⟩)

/-- **The homology of the complex**: `H_k ≅ ℤ^{prodTorus k}`. -/
theorem prodTorusCx_homology (k : ℕ) :
    Nonempty (prodTorusCx.homology k ≅ ModuleCat.of ℤ (Fin (prodTorusB k) → ℤ)) :=
  SDR.sound prodTorusSDR prodTorusSDR_check k

end Work.HomologyIso.Gen
