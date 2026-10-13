/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS.ClassC.Defs` — the linear elliptic class `ClassC` and the package `EllPkgK`

This module fixes the vocabulary of the area `FTS/ClassC` (design (A) of
`Submission/Work/FTS/FTS_HARD_DESIGN.md`, statements from
`Submission/Work/FTS/FTS_HARD_STMTS.lean.txt`), whose deliverable is

  `ExistsEllSolC : ∃ Ce > 0, ∃ α₀ > 0, ∀ α ∈ (0,α₀], ∃ E : Fn →ₗ[ℝ] Fn,
     ∀ g, ClassC α g → EllPkgGo α Ce g (E g) ∧ EllPkgK α 6 Ce g (E g)`

— a **linear** elliptic solution operator on the class `ClassC` of profiles, together with the
`ℋ⁴`-package `EllPkgGo` of the transport/coercivity chapter and the `ℋ⁶`-package `EllPkgK`
of the `StrongPersist` chapter.

## Why the class changed

The previous design (`FTS_ELL_GALERKIN.md` §1) used `Work.FTS.Nonlin.GalClass` as the class of
profiles.  That class contains the fields `DecayInZ`/`DecayAll` and an axis condition, and it is
**not** closed under addition (the failure is at `θ = 0, π/2`, `Refute.not_galClass_lin`, proved
in `FTS/EllSol/Refute/`); consequently `ellClassO_lin` had to assume `GalClass` of *both*
summands and *not* of the sum, and the elliptic existence node `ellClassO_exists` is **false**
on `GalClass` (`FTS/EllExist/Necessary.lean`).

`ClassC` replaces it by a *linear* class: every one of its seven fields is an open-quadrant
value, a limit, or an integral, so `ClassC α` is a subspace; it is inhabited by the Galerkin
basis and by all mollified slices, and it drops the `DecayAll` junk trap.  The all-order
smoothness of the angular moment `F_*(g)` (`fsm`) is what the old class was missing — it is
exactly the analytic input that `FTS/EllExist` proved to be *necessary* for `EllClassO`.

## Contents

* `normTh`, `normThL` — the canonical angular normalisation;
* `ClassC` — the class, with the constructor and the field projections in the namespace
  `ClassC`;
* `EllPkgK` — the elliptic package at order `k` (perturbation part only);
* `ExistsEllSolC` — the target of the area;
* the elementary API used by the sibling modules of the area.

Everything here is definitional; the proofs of the area live in `A1`–`A6` and `Main`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.ThetaTraces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.dupNamespace false

/-! ## The angular normalisation -/

/-- canonical angular normalisation: kills the junk at θ ∉ (0,π/2). -/
def normTh (g : Fn) : Fn := fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then g z θ else 0

/-- `normTh` as a linear map (it is the identity on the class, but it is a genuine projection). -/
def normThL : Fn →ₗ[ℝ] Fn where
  toFun := normTh
  map_add' f g := by
    funext z θ; by_cases h : θ ∈ Set.Ioo 0 (π / 2) <;> simp [normTh, h]
  map_smul' c f := by
    funext z θ; by_cases h : θ ∈ Set.Ioo 0 (π / 2) <;> simp [normTh, h]

@[simp] theorem normThL_apply (g : Fn) : normThL g = normTh g := rfl

@[simp] theorem normTh_apply_of_mem {g : Fn} {z θ : ℝ} (h : θ ∈ Set.Ioo 0 (π / 2)) :
    normTh g z θ = g z θ := by simp [normTh, h]

@[simp] theorem normTh_apply_of_not_mem {g : Fn} {z θ : ℝ} (h : θ ∉ Set.Ioo 0 (π / 2)) :
    normTh g z θ = 0 := by simp [normTh, h]

/-! ## The class `ClassC` -/

/-- **The source class `C`** (design (A)): open-quadrant smoothness and `ℋ⁷`-honesty, the
`BdryTraces`-vanishing of the integration-by-parts boundary terms up to order `6`, all-order
smoothness of the angular moment `F_*(g)`, an axis condition, and the vanishing of the `L₁₂`
mode at `z = 0`.

Every field is either an open-quadrant value, a limit, or an integral of `g`, so the class is
closed under `+` and `c • ·` (`classC_add`, `classC_smul` in `A1`).

## The two extra fields `mem8`, `tr7` (lead ruling, 2026-10-08 09:50)

The level-`6` `U`-slot of `EllPkgK` is `HkMem α 6 (Uop α Ξ / sin 2θ)`, whose top summand
`α·D_z⁷Ξ/sin 2θ` needs the trace of `D_z⁷Ξ` at the angular boundary for **every** `z`: the
`ℋ⁷`-honesty of the class supplies the traces only up to `j = 6`, so the frozen class is one
order short.  The lead's ruling adds `HkMem α 8 g` and `BdryTraces α 7 g` (the level-`8` weak
class supplies the `j = 7` trace), and the level-`6` slots are then stated over
`EllClassOk 8`; the level-`4` slots stay over `EllClassOk 7` by `EllClassOk`-monotonicity.
`ExistsEllSolC` is unchanged.

## The field `mem10` (lead ruling, 2026-10-11)

`PhiStar.bslOp_sol_exists` (`HkMem α k F ⇒ EllWeakPos α k`) is false at `k = 8` (top-order
counterexample, `cbc/fts_phistar_REVIEW.md` §2), and one order of slack is not enough either
(§3).  The repaired node `bslOp_sol_exists_pp` assumes `HkMem α (k+2) F`; A2 uses it at `k = 8`,
so the class carries `HkMem α 10 g`.  `EllClassOk 8` and everything downstream are unchanged.

## The field `thTr` (lead install R6, 2026-10-11)

`cbc/fts_ellnode_ruling.md` §4.4 + review fixes: `bslOp_sol_exists_pp 8` cannot be proved with the
in-tree machinery (compact-source density needs vanishing θ-traces, which do not follow from
`HkMem`).  The node on the path is now `PhiStar.EllNode8tr`, which also assumes
`ThetaTraces α 10` of the orthogonalised source; the class carries `ThetaTraces α 10 g` as its
LAST field (positional destructurings stay valid). -/
structure ClassC (α : ℝ) (g : Fn) : Prop where
  /-- `g` is already normalised in the angular variable: the only field that is not
  automatic for a general element of the ambient space. -/
  norm : normTh g = g
  /-- open-quadrant `C^∞` -/
  reg : Work.FTS.EllipticEst.SmoothOpen g
  /-- honesty of the `ℋ⁷`-integrand -/
  mem : Work.Spaces.HkMem α 7 g
  /-- honesty of the `ℋ⁸`-integrand (needed by the level-`6` slots) -/
  mem8 : Work.Spaces.HkMem α 8 g
  /-- honesty of the `ℋ¹⁰`-integrand (lead ruling 2026-10-11, `cbc/fts_phistar_REVIEW.md` §3):
  the repaired existence node `PhiStar.bslOp_sol_exists_pp 8` needs `HkMem α 10` of the
  orthogonalised source — two orders of slack over `EllWeakPos α 8`. -/
  mem10 : Work.Spaces.HkMem α 10 g
  /-- vanishing of the integration-by-parts boundary terms up to order `6` -/
  tr : Work.FTS.Nonlin.BdryTraces α 6 g
  /-- vanishing of the integration-by-parts boundary terms up to order `7` -/
  tr7 : Work.FTS.Nonlin.BdryTraces α 7 g
  /-- all-order smoothness of the angular moment `F_*(g)` on `(0,∞)` (`EllExist` proved this to be
  *necessary* for the existence node `EllClassO`, and it is the field the old class lacked) -/
  fsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0)
  /-- the axis condition `g(z,θ)/z → 0` as `z → 0⁺` -/
  axis : ∀ θ ∈ Set.Ioo 0 (π / 2), Tendsto (fun z => g z θ / z) (𝓝[>] 0) (𝓝 0)
  /-- the zero mode of `L₁₂` vanishes -/
  l12 : Work.Construction.L12 g 0 = 0
  /-- θ-traces of `D_z^s g`, `s ≤ 9` (lead install R6, 2026-10-11): the input of
  `PhiStar.EllNode8tr` beyond `mem10` (via `PhiStar.thetaTraces_orthSource`). -/
  thTr : Work.FTS.PhiStar.ThetaTraces α 10 g

/-! ## The package `EllPkgK` -/

/-- **The elliptic package at order `k`** (perturbation part only; the star part stays of
`StarPkgo`-type): the solution law, open-quadrant smoothness, and the `ℋ^k`-estimates for the
three operators `ℛ`, `U/sin 2θ`, `V` of §Modulation applied to `Φ̃ = PhiTil α g Φg`. -/
structure EllPkgK (α : ℝ) (k : ℕ) (Ce : ℝ) (g Φg : Fn) : Prop where
  sol : Work.FTS.StrongGlobal.IsBslSolPos α g Φg
  smooth : Work.FTS.EllipticEst.SmoothOpen Φg
  R : Work.FTS.VocabO.HQo α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg))
        ≤ Ce * Work.Spaces.HkNorm α k g
  U : Work.FTS.VocabO.HQo α k (fun z θ => Work.Construction.Uop α
        (Work.Construction.PhiTil α g Φg) z θ / Work.Construction.s2 θ) ∧
      Work.Spaces.HkNorm α k (fun z θ => Work.Construction.Uop α
        (Work.Construction.PhiTil α g Φg) z θ / Work.Construction.s2 θ)
        ≤ Ce * Work.Spaces.HkNorm α k g
  V : Work.FTS.VocabO.HQo α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
        ≤ Ce * Work.Spaces.HkNorm α k g

/-- **(A) the linear solution operator on the class C**, packages at orders `4` and `6`. -/
def ExistsEllSolC : Prop :=
  ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∃ E : Fn →ₗ[ℝ] Fn, ∀ g, ClassC α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧ EllPkgK α 6 Ce g (E g)

/-! ## Elementary API of the class -/

theorem ClassC.smoothOpen {α : ℝ} {g : Fn} (h : ClassC α g) :
    Work.FTS.EllipticEst.SmoothOpen g := h.reg

theorem ClassC.hkMem_seven {α : ℝ} {g : Fn} (h : ClassC α g) : Work.Spaces.HkMem α 7 g := h.mem

theorem ClassC.hkMem_eight {α : ℝ} {g : Fn} (h : ClassC α g) : Work.Spaces.HkMem α 8 g := h.mem8

theorem ClassC.hkMem_ten {α : ℝ} {g : Fn} (h : ClassC α g) : Work.Spaces.HkMem α 10 g := h.mem10

theorem ClassC.bdry {α : ℝ} {g : Fn} (h : ClassC α g) :
    Work.FTS.Nonlin.BdryTraces α 6 g := h.tr

theorem ClassC.bdry_seven {α : ℝ} {g : Fn} (h : ClassC α g) :
    Work.FTS.Nonlin.BdryTraces α 7 g := h.tr7

theorem ClassC.fstar_smooth {α : ℝ} {g : Fn} (h : ClassC α g) (m : ℕ) :
    ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0) := h.fsm m

theorem ClassC.axis_tendsto {α : ℝ} {g : Fn} (h : ClassC α g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Tendsto (fun z => g z θ / z) (𝓝[>] 0) (𝓝 0) := h.axis θ hθ

theorem ClassC.l12_zero {α : ℝ} {g : Fn} (h : ClassC α g) :
    Work.Construction.L12 g 0 = 0 := h.l12

/-- The `BdryTraces` clause of the class at any level `≤ 6`. -/
theorem ClassC.bdry_le_six {α : ℝ} {g : Fn} (h : ClassC α g) {k : ℕ} (hk : k ≤ 6) :
    Work.FTS.Nonlin.BdryTraces α k g := fun a b hab => h.tr a b (le_trans hab hk)

/-- **`BdryTraces` is monotone in the level.** -/
theorem bdryTraces_mono {α : ℝ} {f : Fn} {k l : ℕ} (hkl : k ≤ l)
    (h : Work.FTS.Nonlin.BdryTraces α l f) : Work.FTS.Nonlin.BdryTraces α k f :=
  fun a b hab => h a b (le_trans hab hkl)

/-- **The class is inhabited**: `0` satisfies every field. -/
theorem classC_zero (α : ℝ) : ClassC α (0 : Fn) := by
  have htr : ∀ k : ℕ, Work.FTS.Nonlin.BdryTraces α k (0 : Fn) := by
    intro k a b hab
    have hmix : Work.Spaces.mixed b a (0 : Fn) = 0 := Work.FTS.EllipticEst.mixed_zero_fun b a
    refine ⟨?_, ?_⟩
    · intro θ hθ
      have h1 : (fun z => z * (Work.Spaces.mixed b a (0 : Fn) z θ * Work.Spaces.w z) ^ 2)
          = fun _ : ℝ => (0 : ℝ) := by
        funext z; rw [hmix]; simp
      rw [h1]; exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
    · intro z hz
      have h1 : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (0 : Fn) z θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
        funext θ; rw [hmix]; simp
      rw [h1]; exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  refine ⟨?_, ?_, Work.FTS.EllipticEst.HkMem_zero α 7, Work.FTS.EllipticEst.HkMem_zero α 8,
    Work.FTS.EllipticEst.HkMem_zero α 10, htr 6, htr 7, ?_, ?_, ?_,
    fun s hs z hz => (htr 10 0 s (by omega)).2 z hz⟩
  · funext z θ
    by_cases h : θ ∈ Set.Ioo 0 (π / 2) <;> simp [normTh, h]
  · rw [Work.FTS.EllipticEst.SmoothOpen]
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (fun _ : ℝ × ℝ => (0 : ℝ)) Work.FTS.EllipticEst.Q0
    exact contDiffOn_const
  · intro m
    have h1 : Work.Elliptic.Fstar (0 : Fn) = fun _ : ℝ => (0 : ℝ) := by
      funext z
      simp [Work.Elliptic.Fstar]
    rw [h1]
    exact contDiffOn_const
  · intro θ hθ
    have h1 : (fun z => (0 : Fn) z θ / z) = fun _ : ℝ => (0 : ℝ) := by
      funext z; simp
    rw [h1]; exact tendsto_const_nhds
  · simp [Work.Construction.L12, Work.Construction.L12dens, Work.FM.L12, Work.FM.L12dens]

/-- **`normTh` is idempotent.** -/
theorem normTh_idem (g : Fn) : normTh (normTh g) = normTh g := by
  funext z θ
  by_cases h : θ ∈ Set.Ioo 0 (π / 2) <;> simp [normTh, h]

/-- **Any `ClassC` element is fixed by `normTh`** (the field `norm` is definitionally that). -/
theorem normTh_eq_self {α : ℝ} {g : Fn} (h : ClassC α g) : normTh g = g := h.norm

end Work.FTS.ClassC
