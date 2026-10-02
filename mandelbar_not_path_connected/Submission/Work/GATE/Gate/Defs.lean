/-
# The gate of §2.3: the `α₁`-Böttcher branch and the angle transport (G1–G4)

This module fixes the vocabulary of the §2.3 chain (`Submission/Work/NOTES_LEAD_mandelbar_residuals.md`
§2.3) and isolates its two halves:

* `BranchData φ α` — **the named residual**, i.e. `G1` + `G2`: a right inverse `Λ` of the second
  return map `F_e = (T_c)^{10}` on the Böttcher tube `S` (which is the design's domain `D` of thin
  tube shape), invariant under `Λ`, *and* normalised at the direction `α`: in the `α`-relative
  Böttcher argument (the `deviation` below) the branch divides the displacement from `α` by
  `1024`.  This is exactly the statement that along the critical orbit the inverse branch fixing
  `±a` agrees with the `α`-Böttcher branch (the two ends of each segment `ρ_k`), with the branch
  chosen so that the direction `α` is fixed — the design's `φ_e(Λ z) = (φ_e z)^{1/1024}` with the
  branch fixing the direction `α` (for `α = 371/1023` the fixing lift is
  `ϑ ↦ (ϑ + 371)/1024`, since `(α + 371)/1024 = α`).
* `BaseWindow φ α S F` — **the base of `G2` + `G3`**: the m-th iterate of the parameter `e` is a
  point of the tube whose `α`-relative Böttcher argument is within `windowEps` of `α`.  At `c₀`
  this is `A1` (proved in `Submission/Work/GATE/Nest/`), transported to `e` by the joint
  continuity of the Böttcher coordinate.

The *transport* itself — the `m`-fold iteration of the branch relation and the window arithmetic,
i.e. the design's `G4` (`extAngle e = α₁ + (ϑ_e p_e - α₁)/1024^m`) — is **proved** in
`Submission/Work/GATE/Gate/Transport.lean`.
-/
import Submission.Work.Final.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE

open LeanEval.ComplexAnalysis (Mandelbar)

/-! ## The Böttcher argument and its `α`-relative lift -/

/-- The **Böttcher argument** of a point `z` for a Böttcher coordinate `φ`, in revolutions: the
argument of `φ z` divided by `2π`.  For `φ = Work.ParamRays.Phi` at a parameter `c ∉ Mandelbar`
this is the external angle of `c` up to the normalisation `[0,1)`
(`Work.ParamRays.extAngle`). -/
noncomputable def bAngle (φ : ℂ → ℂ) (z : ℂ) : ℝ := Complex.arg (φ z) / (2 * Real.pi)

/-- The **`α`-relative lift** of the Böttcher argument: the representative of the angle of `φ z`
in the interval `(α - 1/2, α + 1/2]`.  On the Böttcher tube of the direction `α` this is the
normalisation in which the design's `φ_e(Λ z) = (φ_e z)^{1/1024}` "fixes the direction `α`". -/
noncomputable def liftAngle (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) : ℝ :=
  bAngle φ z + ((⌊α - bAngle φ z + 1 / 2⌋ : ℤ) : ℝ)

/-- The **deviation** of the Böttcher argument from the direction `α`: `liftAngle - α`.  It lies
in `(-1/2, 1/2]`. -/
noncomputable def deviation (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) : ℝ := liftAngle φ α z - α

theorem deviation_def (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    deviation φ α z = liftAngle φ α z - α := rfl

theorem liftAngle_sub_bAngle (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    liftAngle φ α z - bAngle φ z = ((⌊α - bAngle φ z + 1 / 2⌋ : ℤ) : ℝ) := by
  rw [liftAngle]; ring

theorem bAngle_le_liftAngle (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    liftAngle φ α z ≤ α + 1 / 2 := by
  have h := Int.floor_le (α - bAngle φ z + 1 / 2)
  rw [liftAngle]
  linarith

theorem liftAngle_lt (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    α - 1 / 2 < liftAngle φ α z := by
  have h := Int.lt_floor_add_one (α - bAngle φ z + 1 / 2)
  rw [liftAngle] at *
  push_cast at h
  linarith

/-- The deviation lies in `(-1/2, 1/2]`. -/
theorem deviation_mem (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    -(1 / 2 : ℝ) < deviation φ α z ∧ deviation φ α z ≤ 1 / 2 :=
  ⟨by rw [deviation_def]; linarith [liftAngle_lt φ α z],
    by rw [deviation_def]; linarith [bAngle_le_liftAngle φ α z]⟩

/-- The `α`-relative lift is the Böttcher argument up to an integer shift. -/
theorem liftAngle_eq_bAngle_add_int (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    ∃ k : ℤ, liftAngle φ α z = bAngle φ z + (k : ℝ) :=
  ⟨⌊α - bAngle φ z + 1 / 2⌋, by rw [liftAngle]⟩

/-- The normalised external angle `toIcoMod 0 1` of an `α`-relative lift is the external angle of
the Böttcher argument (the integer shift does not change the class). -/
theorem toIcoMod_liftAngle (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    toIcoMod one_pos 0 (liftAngle φ α z) = toIcoMod one_pos 0 (bAngle φ z) := by
  obtain ⟨k, hk⟩ := liftAngle_eq_bAngle_add_int φ α z
  rw [hk, show bAngle φ z + (k : ℝ) = bAngle φ z + k • (1 : ℝ) by simp,
    toIcoMod_add_zsmul]

/-- If the `α`-relative deviation is small and `α` is away from `0` and `1` (which holds for both
root angles `α₁ = 371/1023`, `α₂ = 404/1023`), the normalised external angle **is** the
`α`-relative lift: the normalisation does not move it. -/
theorem toIcoMod_eq_alpha_add_deviation {φ : ℂ → ℂ} {α : ℝ} {z : ℂ}
    (hα0 : 1 / 4 < α) (hα1 : α < 3 / 4) (hε : |deviation φ α z| < 1 / 4) :
    toIcoMod one_pos 0 (liftAngle φ α z) = α + deviation φ α z := by
  have hl : liftAngle φ α z = α + deviation φ α z := by rw [deviation_def]; ring
  rw [hl, toIcoMod_eq_self]
  have h := hε
  rw [abs_lt] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ## The branch data (G1 + G2) -/

/-- **The `α`-Böttcher branch along the critical orbit** — the design's `G1` + `G2` of §2.3 as a
single named residual.

* `F` is the second return map (`Work.EL.F e = (T_e)^{10}`, degree `1024`);
* `S` is the Böttcher tube (the design's domain `D`: a thin tube along the orbit chain, avoiding
  the critical values), on which the deviations are small;
* `Λ` is the branch of `F⁻¹` on `S` that follows the critical orbit (`hright`: `F (Λ z) = z`,
  `hmem`: `S` is `Λ`-invariant);
* `hdev` is the normalisation: **in the `α`-relative Böttcher argument the branch divides the
  displacement from `α` by `1024`**.  For the direction `α = 371/1023` this is exactly
  `φ_e(Λ z) = (φ_e z)^{1/1024}` with the branch fixing `α` (the fixing lift of the `1024`-th root
  is `ϑ ↦ (ϑ + 371)/1024`, since `(α + 371)/1024 = α`).

The *risk* of the design (whether the branch fixing `±a` on `D` agrees with this one) lives
entirely in `hright`+`hmem`+`hdev` as a triple; everything downstream is proved in
`Submission/Work/GATE/Gate/Transport.lean`. -/
structure BranchData (φ : ℂ → ℂ) (α : ℝ) where
  /-- the second return map `(T_c)^{10}`, of degree `1024`. -/
  F : ℂ → ℂ
  /-- the inverse branch on the tube. -/
  Λ : ℂ → ℂ
  /-- the Böttcher tube (the design's `D`). -/
  S : Set ℂ
  /-- `Λ` is a right inverse of `F` on the tube. -/
  hright : ∀ z ∈ S, F (Λ z) = z
  /-- the tube is invariant under the branch. -/
  hmem : ∀ z ∈ S, Λ z ∈ S
  /-- the deviations are small on the tube (the normalisation is meaningful there). -/
  hS_dev : ∀ z ∈ S, |deviation φ α z| ≤ 1 / 4
  /-- **the branch fixes the direction `α`**: the `α`-displacement is divided by `1024`. -/
  hdev : ∀ z ∈ S, deviation φ α (Λ z) = deviation φ α z / 1024

/-- **The base window** — the design's `G3` output: the `m`-th iterate of the parameter `e`
under the second return map is a point `p` of the tube whose `α`-relative Böttcher argument lies
within `windowEps` of `α`.

At `c₀` the window statement for `p` is `A1` (§2.2, proved in `Submission/Work/GATE/Nest/`);
its transport from `c₀` to `e` uses the joint continuity of the Böttcher coordinate (NAKANE), and
the connecting path `P` of `G3` is what makes `F^[m] e` the transport of the base point. -/
structure BaseWindow {φ : ℂ → ℂ} {α : ℝ} (bd : BranchData φ α) (e : ℂ) where
  /-- the number of gate iterations. -/
  m : ℕ
  /-- the base point of the connecting path. -/
  p : ℂ
  /-- the base point lies in the tube. -/
  hpS : p ∈ bd.S
  /-- **the design's `G3` identity** `e = Λ_e^[m](p_e)`. -/
  hbase : e = bd.Λ^[m] p
  /-- the base point sits in the `α`-window (A1 at `c₀`, transported). -/
  hwin : |deviation φ α p| < Work.Final.windowEps

namespace BaseWindow

variable {φ : ℂ → ℂ} {α : ℝ} {bd : BranchData φ α} {e : ℂ} (bw : BaseWindow bd e)

/-- The `m`-th iterate of `e` under the second return map is the base point: `Λ` is a right
inverse of `F` on the tube.  This is the dynamical content of the design's `e = Λ^[m] p_e`. -/
theorem iterate_eq : bd.F^[bw.m] e = bw.p := by
  cases bw with
  | mk m p hpS hbase hwin =>
    have hmem_iter : ∀ k : ℕ, bd.Λ^[k] p ∈ bd.S := by
      intro k
      induction k with
      | zero => simpa using hpS
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact bd.hmem _ ih
    have hgen : ∀ k : ℕ, bd.F^[k] (bd.Λ^[k] p) = p := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
        rw [bd.hright (bd.Λ^[k] p) (hmem_iter k)]
        exact ih
    simpa [← hbase] using hgen m

end BaseWindow

end Work.GATE
