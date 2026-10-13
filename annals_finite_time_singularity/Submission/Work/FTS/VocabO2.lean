import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.FTS.NonlinRows.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Scratch type-check of `cbc/fts_starpkg_t2.md` (Claude, curric-46, 2026-10-06).
LEAD-FROZEN (curric-46, 2026-10-06) lead file. Design: Submission/Work/FTS/STARPKG_T2_LEAD.md. Do not edit. Was: proposed lead file `FTS/VocabO2.lean` (Part A: definitions) + node statements (Part B, `sorry`). -/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.VocabO2

open Work.FTS.Galerkin (Fn)
open Work.FTS.VocabO

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Part A — definitions (the file the lead freezes) -/

/-- `Φ̃_* = Φ_* - (1/4α) sin 2θ L₁₂(F_*)`. -/
abbrev PhiTs (α : ℝ) (Φs : Fn) : Fn :=
  Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs

/-- **The star package with the `𝒲^{4,∞}` (closed-domain `WlInf`) fields the rows consume.**
Every new field is in exactly the form of the consumer clause (`N4Norm'.wprod`, `N4Norm'.wtoh`
via `wtoHQ_of_pointwise_open`, `VocabO.T3Clause`). -/
structure StarPkgo2 (α Cs : ℝ) (Φs : Fn) : Prop extends StarPkgo α Cs Φs where
  /-- rows 10, 11 (`NRow10_of_WlInfStar`, `NRow11_of_wlInf`) -/
  RW : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z * Work.Construction.Rop α (PhiTs α Φs) z θ) ∧
    Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z * Work.Construction.Rop α (PhiTs α Φs) z θ)
      ≤ Cs * α
  /-- row 18 (`T3Clause` + `wprod` honesty) -/
  VW : Work.Spaces.WlInfMem α 4 (Work.Construction.Vop (PhiTs α Φs)) ∧
    Work.Spaces.WlInf α 4 (Work.Construction.Vop (PhiTs α Φs)) ≤ Cs * α
  /-- row 19 (`wtoh` on `((z+1)³/z²)N₃^{**} = -2α[((z+1)/z)V]·[((z+1)²/z)D_zF_*]`) -/
  VzW : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z * Work.Construction.Vop (PhiTs α Φs) z θ) ∧
    Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z * Work.Construction.Vop (PhiTs α Φs) z θ)
      ≤ Cs * α
  /-- row 14 (`N₂^{sg} = -2(U/s2)·D_θ g` on `Qd`, `wprod` honesty) -/
  UsW : Work.Spaces.WlInfMem α 4
      (fun z θ => Work.Construction.Uop α (PhiTs α Φs) z θ / Work.Construction.s2 θ) ∧
    Work.Spaces.WlInf α 4
      (fun z θ => Work.Construction.Uop α (PhiTs α Φs) z θ / Work.Construction.s2 θ) ≤ Cs * α
  /-- row 15 (`((z+1)³/z²)N₂^{**} = -2[((z+1)/z)(U/s2)]·[((z+1)²/z)D_θF_*]`) -/
  UszW : Work.Spaces.WlInfMem α 4
      (fun z θ => (z + 1) / z * (Work.Construction.Uop α (PhiTs α Φs) z θ / Work.Construction.s2 θ)) ∧
    Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * (Work.Construction.Uop α (PhiTs α Φs) z θ / Work.Construction.s2 θ))
      ≤ Cs * α

/-- `Ŷ = ((z+1)/z)·Φ̃_*/sin 2θ` — the single object whose flat `𝒲`-bound gives every star field. -/
def Ycheck (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => (z + 1) / z * (PhiTs α Φs z θ / Work.Construction.s2 θ)

/-- **Flat `𝒲^{l,∞}`-type bound on the open quadrant**: plain `(z+1)^k∂_z^k` up to order `l`, and
the flat angular part `(z+1)^k∂_z^k D_θ^i ∂_θ f` for `k+i+1 ≤ l`. -/
def FlatW (l : ℕ) (f : Fn) (K : ℝ) : Prop :=
  ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
    (∀ k : ℕ, k ≤ l → |(z + 1) ^ k * Work.Spaces.pzIter k f z θ| ≤ K) ∧
    (∀ k i : ℕ, k + i + 1 ≤ l →
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Spaces.pth f)) z θ| ≤ K)

/-- **The analysis target of `FTS/PhiStar`** (replaces the field-by-field targets). -/
structure StarCore (α Cs : ℝ) (Φs : Fn) : Prop where
  sol : Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) Φs
  smooth : Work.FTS.EllipticEst.SmoothOpen Φs
  /-- normal form of the witness: `Φ̃_*` is extended by `0` off the open quadrant
  (free: `IsBslSol` only sees `Q0` and the two boundary lines, where `Θ = 0`) -/
  zeroOff : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → PhiTs α Φs z θ = 0
  core : FlatW 7 (Ycheck α Φs) (Cs * α)

/-- rows 8–26 with row 16 at the rate `X³` (in `Pbd`'s `α^{-3/2}X³` budget). -/
structure NRows2 (IP : ℝ → Fn → Fn → ℝ) (α K : ℝ) (g Φs Φg : Fn) : Prop where
  r8 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gg α g Φg)
    ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)
  r9 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gs α g Φg) ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  r10 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g) ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  r11 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ K * α ^ 2
  r12 : |IP α (Work.FTS.Nonlin.N2gg α g Φg) g| ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
  r13 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg) ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)
  r14 : |IP α (Work.FTS.Nonlin.N2sg α Φs g) g| ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)
  r15 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ K * α ^ 2
  /-- **relaxed** (was `K·√α·X³`) -/
  r16 : |IP α (Work.FTS.Nonlin.N3gg α g Φg) g| ≤ K * Work.FTS.Nonlin.Xn α g ^ 3
  r17 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3gs α g Φg) ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)
  r18 : |IP α (Work.FTS.Nonlin.N3sg α Φs g) g| ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2)
  r19 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * α ^ 3
  r20 : |IP α (Work.FTS.Nonlin.N4gg α g) g| ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
  r21 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g) ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)
  r22 : |IP α (Work.FTS.Nonlin.N4sg α g) g| ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)
  r23 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4ss α) ≤ K * α ^ 3
  r24 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gg g) ≤ K * Work.FTS.Nonlin.Xn α g ^ 2
  r25 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gs α g) + Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5sg α g)
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  r26 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5ss α) ≤ K * α ^ 2

/-- the row context with the upgraded packages -/
def Ctx2 (α₂ Ci Ct Ce Cs α : ℝ) (g Φs Φg : Fn) : Prop :=
  0 < α ∧ α ≤ 1 ∧ α ≤ α₂ ∧ Work.FTS.Nonlin.GalClass α g ∧
    StarPkgo2 α Cs Φs ∧ EllPkgGo α Ce g Φg

/-! ### The seven row nodes, restated (each `∃ K, 0 < K ∧ ∀ …, Ctx2 … → honesty ∧ bound`) -/

end Work.FTS.VocabO2
