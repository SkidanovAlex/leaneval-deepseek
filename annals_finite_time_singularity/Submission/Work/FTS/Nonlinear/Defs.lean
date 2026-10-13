/-
# N4 — the nonlinear estimates of §8 of Elgindi's paper (the `Work.FTS.Nonlin` chapter)

This directory (`Submission/Work/FTS/Nonlinear/`) builds **node N4** of the route of
`FTS_AUDIT_LEAD.md` §4 and of the design `FTS/N45_DESIGN_LEAD.md` §3: the term-by-term
estimates of §8 of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), 1--70,

i.e. the proof of the paper's Proposition `innerproductestimate` (tex 1536) and of
`muestimate` (tex 1507), in the form needed by the a-priori (N5) and existence (N6) nodes.

## The deliverable

`Work.FTS.Nonlin.pairing_bound` (design §3.6, L-N4.11): for an admissible inner product `IP`
uniform in `α` (`UnifIP`) and the `IP`-level transport interface `N4Extra` (see
`Interface.lean`), for `α ≤ α₄` and a Galerkin-class perturbation `g` with elliptic packages
`EllPkgG` (N1) and `StarPkg` (N3),

* `|μ| ≤ C(α + α⁻¹X + α^{-5/2}X²)` and `|μ| ≤ 1/2` whenever `X = |g|_{ℋ⁴} ≤ α^{7/4}`;
* `|IP (gRHS α μ (lamfun μ) F Φ g) g| ≤ C · Pbd α X`.

**The honest (open-quadrant) chapter.**  The packages `StarPkg`/`EllPkgG` above are the *frozen*
ones of `Submission/Work/FTS/Vocab.lean`, whose `smooth` field is `SmoothQuad` (`C^∞` *through*
`z = 0`) and whose `RegQ` carries `BdryTraces`; the true stream functions of the route have
neither property, so `pairing_bound` is a statement about the frozen interface and *not* directly
about the paper's objects.  The sub-chapter `Submission/Work/FTS/Nonlinear/Open/` therefore
restates the whole §8 per-piece table in the lead-frozen honest vocabulary
(`VocabO.N4Extra'`, `VocabO2.StarPkgo2`, `VocabO.EllPkgGo`, `N4Norm'`, with row 16 at the relaxed
rate `X³`), and its output is `Work.FTS.Nonlinear.Open.n4Rows2` — the row bundle a
`pairing_bound_open2`-style assembly consumes.

## Layout of the chapter

* `Defs.lean` (this file): the vocabulary of the *pieces*.  The paper's `N₀, N, N_*`
  (already named in `Work.Construction.Terms`) are split, as the paper does, into the
  elementary summands of the table of design §3.4.
* `Infra.lean`: the algebra of the split (`Uop/Vop/Rop/Dz/pth/FK/L12/Theta` are additive,
  `PhiTil` splits, `IP` is additive on `RegQ`, `HkSq` only sees the values on `Qd`).
* `FstarPkg.lean`: the `F_*`-package of design §3.2.
* `Mu.lean`: the `L₁₂`-piece bounds, `μ̄` and `μ` (design §3.5, L-N4.6--L-N4.8).
* `NstarAK.lean`: `L-N4.9`/`L-N4.10`, the `N_*` and `AK` pairings.
* `Pieces.lean`: the 26 rows of the table of design §3.4.
* `Assembly.lean`: L-N4.11, the assembly of `pairing_bound` from the rows.

## Conventions

The frozen vocabulary is `Submission/Work/FTS/Vocab.lean` (`Work.FTS.Nonlin.Xn`,
`RegQ`, `GalClass`, `CoerAdm`, `UnifIP`, `EllPkgG`, `StarPkg`, `Pbd`, `PsiCan`,
`GalBasis`); it is imported, never redefined.  In particular `RegQ α k f` is the
*interior* class `SmoothQuad f ∧ HkMem α k f ∧ BdryTraces α k f` — `Work.Spaces.SmoothNbhd`
(`ContDiffOn ℝ ⊤` = real-analyticity on a neighbourhood) is never used here, since it is
unsatisfiable for `F_*`, for cut-off data and for PDE solutions (design §5 T1).

The letter `X` always abbreviates `Xn α g = Spaces.HkNorm α 4 g`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Vocab
import Submission.Work.Construction.Terms
import Submission.Work.Construction.GammaN0
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlin

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false

/-! ## The stream functions of the two halves of `F = F_* + g` -/

/-- `Φ̃_g = Φ_g - (1/(4α)) sin(2θ) L₁₂(g)`: the elliptic residual belonging to the
perturbation (the argument of the elliptic estimates of N1). -/
def PhiTg (α : ℝ) (g Φg : Fn) : Fn := Work.Construction.PhiTil α g Φg

/-- `Φ̃_* = Φ_s - (1/(4α)) sin(2θ) L₁₂(F_*)`: the elliptic residual belonging to `F_*`
(the argument of `PhiStarRegularity`, N3). -/
def PhiTs (α : ℝ) (Φs : Fn) : Fn :=
  Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs

@[simp] theorem PhiTg_apply (α : ℝ) (g Φg : Fn) (z θ : ℝ) :
    PhiTg α g Φg z θ = Work.Construction.PhiTil α g Φg z θ := rfl

@[simp] theorem PhiTs_apply (α : ℝ) (Φs : Fn) (z θ : ℝ) :
    PhiTs α Φs z θ = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ := rfl

/-! ## The pieces of `N₀` (design §3.4 rows 1--7)

The names `N01, …, N06`, `N04a/b`, `N05a/b` are those of `Work.Construction.Terms`;
they are re-stated here only to fix the *shapes* the rows are about.  Row 1 is the
pair `N01 + N02`; row 3 is `N04a`; row 4 is `N04b`; row 5 is `N05a`; row 6 is `N05b`;
row 7 is `N06`; row 2 is `N03`.
-/

/-- Row 1: the two pure-`F_*` terms `N01 + N02` of `N₀`. -/
def N0fix (α : ℝ) : Fn := fun z θ =>
  Work.Construction.N01 α (Work.Construction.Ftot α (fun _ _ => 0)) (fun _ _ => 0) z θ
    + Work.Construction.N02 α (Work.Construction.Ftot α (fun _ _ => 0)) (fun _ _ => 0) z θ

/-- Row 2: `N₀₃ = (1/α) L₁₂(g) g`. -/
def N03g (α : ℝ) (g : Fn) : Fn := Work.Construction.N03 α (Work.Construction.Ftot α g) g

/-- Row 3: `N₀₄ᵃ = (3/(2α)) sin(2θ) L₁₂(g) ∂_θF_*`. -/
def N04aF (α : ℝ) (g : Fn) : Fn :=
  Work.Construction.N04a α (Work.Construction.Ftot α g) g

/-- Row 4: `N₀₄ᵇ = (3/(2α)) L₁₂(g) D_θ g`. -/
def N04bF (α : ℝ) (g : Fn) : Fn :=
  Work.Construction.N04b α (Work.Construction.Ftot α g) g

/-- Row 5: `N₀₅ᵃ = -c2m(θ) L₁₂(g) D_z F_*`. -/
def N05aF (α : ℝ) (g : Fn) : Fn :=
  Work.Construction.N05a α (Work.Construction.Ftot α g) g

/-- Row 6: `N₀₅ᵇ = -c2m(θ) L₁₂(g) D_z g`. -/
def N05bF (α : ℝ) (g : Fn) : Fn :=
  Work.Construction.N05b α (Work.Construction.Ftot α g) g

/-- Row 7: `N₀₆ = -c2m(θ) L₁₂(F_*) D_z g`, i.e. `-c2m(θ)·(2α/(1+z))·D_z g`. -/
def N06F (α : ℝ) (g : Fn) : Fn :=
  Work.Construction.N06 α (Work.Construction.Ftot α g) g

/-! ## The four-way splits of `N₁, …, N₅` (design §3.4 rows 8--26)

Following the paper, `Φ̃ = Φ̃_g + Φ̃_*` and `F = F_* + g`, so each `N_i` splits into
`N_i^{gg} + N_i^{gs} + N_i^{sg} + N_i^{ss}`, the first index recording which stream
function (`g` for `Φ̃_g`, `s` for `Φ̃_*`) and the second which profile (`g` for the
`g`-factor, `s` for the `F_*`-factor) occurs.  The labels of the design table:
`N_i^{gg} = N i gg`, `N_i^{g*} = N i gs`, `N_i^{*g} = N i sg`, `N_i^{**} = N i ss`.
-/

/-- `N₁^{gg} = 2ℛ(Φ̃_g) g` (row 8). -/
def N1gg (α : ℝ) (g Φg : Fn) : Fn :=
  fun z θ => 2 * Work.Construction.Rop α (PhiTg α g Φg) z θ * g z θ

/-- `N₁^{gs} = 2ℛ(Φ̃_g) F_*` (row 9). -/
def N1gs (α : ℝ) (g Φg : Fn) : Fn :=
  fun z θ => 2 * Work.Construction.Rop α (PhiTg α g Φg) z θ * Work.Construction.Fstar α z θ

/-- `N₁^{sg} = 2ℛ(Φ̃_*) g` (row 10). -/
def N1sg (α : ℝ) (Φs g : Fn) : Fn :=
  fun z θ => 2 * Work.Construction.Rop α (PhiTs α Φs) z θ * g z θ

/-- `N₁^{ss} = 2ℛ(Φ̃_*) F_*` (row 11). -/
def N1ss (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => 2 * Work.Construction.Rop α (PhiTs α Φs) z θ * Work.Construction.Fstar α z θ

/-- `N₂^{gg} = -2U(Φ̃_g) ∂_θ g` (row 12). -/
def N2gg (α : ℝ) (g Φg : Fn) : Fn :=
  fun z θ => -2 * Work.Construction.Uop α (PhiTg α g Φg) z θ * Work.Spaces.pth g z θ

/-- `N₂^{gs} = -2U(Φ̃_g) ∂_θ F_*` (row 13). -/
def N2gs (α : ℝ) (g Φg : Fn) : Fn :=
  fun z θ => -2 * Work.Construction.Uop α (PhiTg α g Φg) z θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ

/-- `N₂^{sg} = -2U(Φ̃_*) ∂_θ g` (row 14). -/
def N2sg (α : ℝ) (Φs g : Fn) : Fn :=
  fun z θ => -2 * Work.Construction.Uop α (PhiTs α Φs) z θ * Work.Spaces.pth g z θ

/-- `N₂^{ss} = -2U(Φ̃_*) ∂_θ F_*` (row 15). -/
def N2ss (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => -2 * Work.Construction.Uop α (PhiTs α Φs) z θ
    * Work.Spaces.pth (Work.Construction.Fstar α) z θ

/-- `N₃^{gg} = -2α V(Φ̃_g) D_z g` (row 16). -/
def N3gg (α : ℝ) (g Φg : Fn) : Fn :=
  fun z θ => -2 * α * Work.Construction.Vop (PhiTg α g Φg) z θ * Work.Spaces.Dz g z θ

/-- `N₃^{gs} = -2α V(Φ̃_g) D_z F_*` (row 17). -/
def N3gs (α : ℝ) (g Φg : Fn) : Fn :=
  fun z θ => -2 * α * Work.Construction.Vop (PhiTg α g Φg) z θ
    * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- `N₃^{sg} = -2α V(Φ̃_*) D_z g` (row 18). -/
def N3sg (α : ℝ) (Φs g : Fn) : Fn :=
  fun z θ => -2 * α * Work.Construction.Vop (PhiTs α Φs) z θ * Work.Spaces.Dz g z θ

/-- `N₃^{ss} = -2α V(Φ̃_*) D_z F_*` (row 19). -/
def N3ss (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => -2 * α * Work.Construction.Vop (PhiTs α Φs) z θ
    * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- `N₄^{gg} = -(1/2) sin(2θ) FK(g) ∂_θ g = -(1/2) FK(g) D_θ g` (row 20). -/
def N4gg (α : ℝ) (g : Fn) : Fn :=
  fun z θ => -(1 / 2) * Work.Construction.FK g z * Work.Spaces.Dth g z θ

/-- `N₄^{gs} = -(1/2) sin(2θ) FK(g) ∂_θ F_*` (row 21). -/
def N4gs (α : ℝ) (g : Fn) : Fn :=
  fun z θ => -(1 / 2) * Work.Construction.s2 θ * Work.Construction.FK g z
    * Work.Spaces.pth (Work.Construction.Fstar α) z θ

/-- `N₄^{sg} = -(1/2) FK(F_*) D_θ g` (row 22). -/
def N4sg (α : ℝ) (g : Fn) : Fn :=
  fun z θ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z
    * Work.Spaces.Dth g z θ

/-- `N₄^{ss} = -(1/2) sin(2θ) FK(F_*) ∂_θ F_*` (row 23). -/
def N4ss (α : ℝ) : Fn :=
  fun z θ => -(1 / 2) * Work.Construction.s2 θ
    * Work.Construction.FK (Work.Construction.Fstar α) z
    * Work.Spaces.pth (Work.Construction.Fstar α) z θ

/-- `N₅^{gg} = -sin²θ FK(g) g` (row 24). -/
def N5gg (g : Fn) : Fn :=
  fun z θ => -(Real.sin θ) ^ 2 * Work.Construction.FK g z * g z θ

/-- `N₅^{gs} = -sin²θ FK(g) F_*` (row 25a). -/
def N5gs (α : ℝ) (g : Fn) : Fn :=
  fun z θ => -(Real.sin θ) ^ 2 * Work.Construction.FK g z
    * Work.Construction.Fstar α z θ

/-- `N₅^{sg} = -sin²θ FK(F_*) g` (row 25b). -/
def N5sg (α : ℝ) (g : Fn) : Fn :=
  fun z θ => -(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z * g z θ

/-- `N₅^{ss} = -sin²θ FK(F_*) F_*` (row 26). -/
def N5ss (α : ℝ) : Fn :=
  fun z θ => -(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z
    * Work.Construction.Fstar α z θ

/-! ## The pieces of `N_*` (design §3.4 row `N_*`; §3.5 L-N4.9) -/

/-- `N_{*,1} = -μg`. -/
def Ns1 (μ : ℝ) (g : Fn) : Fn := fun z θ => -μ * g z θ

/-- `N_{*,2} = -(μ+λ+μλ) D_z g`, which for `λ = lamfun μ` collapses to `μ D_z g`. -/
def Ns2 (μ lam : ℝ) (g : Fn) : Fn :=
  fun z θ => -(μ + lam + μ * lam) * Work.Spaces.Dz g z θ

/-- `N_*` with the paper's choice `λ = -2μ/(1+μ)`: `μ (D_z g - g)`. -/
def NstarLam (μ : ℝ) (g : Fn) : Fn :=
  fun z θ => μ * (Work.Spaces.Dz g z θ - g z θ)

/-! ## The `μ̄`-term -/

/-- The `μ̄ AK` term of `gRHS`, with `μ̄ = L₁₂(N₀) + L₁₂(N)`. -/
def MuAK (α : ℝ) (g Φs Φg : Fn) : Fn := fun z θ =>
  Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
      (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) * Work.Construction.AK α z θ

/-! ## The monomials of `Pbd`, and the elementary comparisons

`Pbd α X = α²X + √α X² + α^{-3/2}X³ + α^{-5/2}X⁴` is the polynomial of the paper's
estimate (frozen in `Vocab.lean`).  Every per-piece bound of design §3.4 is one of
`α²`, `α²X`, `√α X`, `√α X²`, `α^{3/2}X`, `α^{3/2}X²`, `α^{-1/2}X²`, `α^{-1}X²`,
`α^{-3/2}X³`, `X²`; the lemmas below reduce each of these to `Pbd α X`.
-/

/-- `α²·X ≤ Pbd α X` (only the nonnegativity of the remaining three summands is used). -/
theorem alpha_sq_mul_le_Pbd {α X : ℝ} (hα : 0 < α) (hX : 0 ≤ X) :
    α ^ 2 * X ≤ Pbd α X := by
  have h1 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h2 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  have h3 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  rw [Pbd]; linarith

/-- `α² ≤ Pbd α X` for `X ≥ 1` (the pairing of a forcing piece `|·|_{ℋ⁴} ≤ Cα²` with `g`). -/
theorem alpha_sq_le_Pbd {α X : ℝ} (hα : 0 < α) (hX : 1 ≤ X) : α ^ 2 ≤ Pbd α X := by
  have h1 : α ^ 2 ≤ α ^ 2 * X := by
    nth_rewrite 1 [← mul_one (α ^ 2)]
    exact mul_le_mul_of_nonneg_left hX (by positivity)
  exact le_trans h1 (alpha_sq_mul_le_Pbd hα (by positivity))

/-- `√α·X² ≤ Pbd α X`. -/
theorem sqrt_mul_sq_le_Pbd {α X : ℝ} (hα : 0 < α) (hX : 0 ≤ X) :
    Real.sqrt α * X ^ 2 ≤ Pbd α X := by
  have h0 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h2 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  have h3 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  rw [Pbd]; linarith

/-- `α^{-1/2}X³ ≤ Pbd α X` for `0 < α ≤ 1`. -/
theorem rpow_neg_half_mul_cube_le_Pbd {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    α ^ (-(1 / 2 : ℝ)) * X ^ 3 ≤ Pbd α X := by
  have hle : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
  have h : α ^ (-(1 / 2 : ℝ)) * X ^ 3 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_le_mul_of_nonneg_right hle (by positivity)
  have h0 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h3 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h4 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  rw [Pbd] at *; linarith

/-- `α^{-1}X³ ≤ Pbd α X` for `0 < α ≤ 1`. -/
theorem rpow_neg_one_mul_cube_le_Pbd {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    α ^ (-(1 : ℝ)) * X ^ 3 ≤ Pbd α X := by
  have hle : α ^ (-(1 : ℝ)) ≤ α ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
  have h : α ^ (-(1 : ℝ)) * X ^ 3 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_le_mul_of_nonneg_right hle (by positivity)
  have h0 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h3 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h4 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  rw [Pbd] at *; linarith

/-- `α^{3/2}X² ≤ Pbd α X` for `0 < α ≤ 1`. -/
theorem rpow_three_half_mul_sq_le_Pbd {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    α ^ (3 / 2 : ℝ) * X ^ 2 ≤ Pbd α X := by
  have hle : α ^ (3 / 2 : ℝ) ≤ Real.sqrt α := by
    rw [Real.sqrt_eq_rpow]
    have h : α ^ (3 / 2 : ℝ) = α ^ (1 / 2 : ℝ) * α ^ (1 : ℝ) := by
      rw [← Real.rpow_add hα]; norm_num
    rw [h, Real.rpow_one]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hα.le _) hα1
  have hs : Real.sqrt α * X ^ 2 ≤ Pbd α X := sqrt_mul_sq_le_Pbd hα hX
  have h : α ^ (3 / 2 : ℝ) * X ^ 2 ≤ Real.sqrt α * X ^ 2 :=
    mul_le_mul_of_nonneg_right hle (by positivity)
  linarith

/-- `X³ ≤ Pbd α X` for `0 < α ≤ 1`. -/
theorem cube_le_Pbd {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    X ^ 3 ≤ Pbd α X := by
  have hle : (1 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (x := α)
      (y := (0 : ℝ)) (z := -(3 / 2 : ℝ)) (by norm_num)
    simpa using h
  have h : X ^ 3 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 := by
    simpa using mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ X ^ 3)
  have h0 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h3 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h4 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  rw [Pbd] at *; linarith

end Work.FTS.Nonlin
