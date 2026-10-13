/-
# `Work.FTS.Final.Small` — the pointwise smallness of the perturbation (audit item 2)

**Deliverable of this module**: `hsmall_of_H4`, the pointwise bound

  `|g z θ τ| ≤ 3α/200`   for `τ ≥ 0`, `z ∈ Iz = [0,∞)`, `θ ∈ Iθ = [0,π/2]`

in the *exact* form in which `Work.FTS.FireFix.blowupAtTop_of_regPkg'` consumes it
(its hypothesis `hsmall`), from

* the uniform `ℋ⁴`-bound `Xn (pExp α) (slice g τ) ≤ C₀ · (pExp α)²`, and
* a **pointwise sup bound** `|g z θ τ| ≤ Cg · Xn (pExp α) (slice g τ)`.

The second hypothesis is the "`N4Norm'` sup bound" of the integration audit §4 item 2: the
pointwise control of the ℋ⁴-size which the norm interface of the rows chapter provides.  Its
canonical discharge — the ℋ⁴ → sup embedding of the paper's `Linf_H2` corollary, with the
constant `Cg = √(100/(γ-1)) = √(1000/(3α))` — is *also* proved here, as
`sup_le_Xn_of_HkMem` (from `Work.FTS.Galerkin.linf_of_HkNorm_four`), together with the combined
corollary `hsmall_of_HkMem` in which the sup hypothesis is discharged; the remaining hypotheses of
that corollary (`SmoothNbhd`, `VanishTheta`, `DecayInZ 2`, `HkMem α 4`) are the slice-level class
data of the profile, supplied in the strong route by the regularity package of the slices.

## The exponent bookkeeping (why the constants are what they are)

The challenge exponent is `α`; the *profile* exponent is `pExp α = 3α`.  With
`Xn ≤ C₀ (3α)² = 9 C₀ α²` and the sup bound with constant `Cg`,

  `|g| ≤ Cg · 9 C₀ α²`,

and `|g| ≤ 3α/200` is **equivalent** (for `α > 0`) to `α · (600 · Cg · C₀) ≤ 1`.  That is the
smallness hypothesis of `hsmall_of_H4`; it is exactly the "`α` small enough" condition of the
paper's stability analysis, and it is satisfiable at every `Cg, C₀` by taking `α` small (the sup
constant of the ℋ⁴-embedding even grows like `α^{-1/2}`, `Cg = √(1000/(3α))`, so the condition
reads `√α · 600 C₀ √(1000/3) ≤ 1`, still satisfiable).
-/
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.Final.Defs
import Submission.Work.FTS.Galerkin.Compactness

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open MeasureTheory Set Filter

namespace Work.FTS.Final

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The ℋ⁴ → sup embedding (the canonical "`N4Norm'` sup bound") -/

/-- **The pointwise bound from the `ℋ⁴`-norm.**  For a slice `f` which is smooth on a neighbourhood
of the closed quadrant, vanishes on the two angular boundary lines, decays at `∞` and lies in `ℋ⁴`,
the pointwise value is dominated by the `ℋ⁴`-norm with the paper's constant
`√(100/(γ-1)) = √(1000/α)`:

  `|f z θ| ≤ √(100/(γ-1)) · Xn α f`   on `Iz ×ˢ Iθ`.

This is the paper's `Linf_H2` corollary chained with `ℋ⁴ ⊆ ℋ²`
(`Work.FTS.Galerkin.linf_of_HkNorm_four` at `B = Xn α f`); it is the *shape* in which the rows
chapter's norm interface supplies the sup bound consumed by `hsmall_of_H4`. -/
theorem sup_le_Xn_of_HkMem {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Work.Spaces.SmoothNbhd f) (hv : Work.Spaces.VanishTheta f)
    (hd : Work.Spaces.DecayInZ 2 f) (hm : Work.Spaces.HkMem α 4 f)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |f z θ| ≤ Real.sqrt (100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f := by
  have hgam1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hc : 0 ≤ 100 / (Work.Spaces.gam α - 1) := by positivity
  have h := Work.FTS.Galerkin.linf_of_HkNorm_four hα hα1
    (Work.Spaces.HkNorm_nonneg α 4 f) hsm hv hd hm hz hθ le_rfl
  have hsq : (f z θ) ^ 2 ≤ (Real.sqrt (100 / (Work.Spaces.gam α - 1))
      * Work.Spaces.HkNorm α 4 f) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc]
    exact h
  exact abs_le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg _) (Work.Spaces.HkNorm_nonneg α 4 f))

/-! ## The main lemma -/

/-- **`hsmall_of_H4` (audit §4 item 2).**  From the uniform `ℋ⁴`-bound `Xn (pExp α) (slice g τ) ≤
C₀(pExp α)²`, the pointwise sup bound `|g| ≤ Cg · Xn (pExp α) (slice g τ)` and the smallness
`α(600 Cg C₀) ≤ 1`, the perturbation is pointwise small,

  `|g z θ τ| ≤ 3α/200`   for `τ ≥ 0`, `z ∈ Iz`, `θ ∈ Iθ`,

which is the exact form of the `hsmall` hypothesis of
`Work.FTS.FireFix.blowupAtTop_of_regPkg'` (same quantifier order, same `Iz`/`Iθ`, same constant
`3α/200`, `α` the *challenge* exponent). -/
theorem hsmall_of_H4 {α Cg C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hCg : 0 ≤ Cg)
    (hC₀ : 0 < C₀) (hsmall : α * (600 * Cg * C₀) ≤ 1)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hXN : ∀ τ : ℝ, 0 ≤ τ → Xn (Work.FTS.Regularity.pExp α) (slice g τ)
      ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2)
    (hsup : ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |g z θ τ| ≤ Cg * Xn (Work.FTS.Regularity.pExp α) (slice g τ)) :
    ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |g z θ τ| ≤ 3 * α / 200 := by
  have hC₀nn : 0 ≤ C₀ := hC₀.le
  have hkey : Cg * C₀ * (9 * α) ≤ 3 / 200 := by
    have h1 : (α * (600 * Cg * C₀)) * (1 / 200 : ℝ) ≤ 1 * (1 / 200 : ℝ) :=
      mul_le_mul_of_nonneg_right hsmall (by norm_num)
    nlinarith [h1, hα, hCg, hC₀nn]
  intro τ hτ z hz θ hθ
  have h1 : |g z θ τ| ≤ Cg * Xn (Work.FTS.Regularity.pExp α) (slice g τ) := hsup τ hτ z hz θ hθ
  have h2 : Cg * Xn (Work.FTS.Regularity.pExp α) (slice g τ) ≤ Cg * (C₀ * (3 * α) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hCg
    refine le_trans (hXN τ hτ) ?_
    rw [Work.FTS.Regularity.pExp_eq]
  have h3 : Cg * (C₀ * (3 * α) ^ 2) ≤ 3 * α / 200 := by
    have h : Cg * (C₀ * (3 * α) ^ 2) = α * (Cg * C₀ * (9 * α)) := by ring
    rw [h]
    calc α * (Cg * C₀ * (9 * α)) ≤ α * (3 / 200) := mul_le_mul_of_nonneg_left hkey hα.le
      _ = 3 * α / 200 := by ring
  exact le_trans h1 (le_trans h2 h3)

/-- **The same with the sup bound discharged** by the ℋ⁴ → sup embedding: if the slice carries the
class data of the paper's pointwise bound (`SmoothNbhd`, `VanishTheta`, `DecayInZ 2`, `HkMem α 4`),
then the sup hypothesis `hsup` of `hsmall_of_H4` holds with the paper's constant `√(1000/(3α))`, and
the smallness condition becomes the *explicit* `√α`-condition below. -/
theorem hsmall_of_HkMem {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hC₀ : 0 < C₀)
    (hsmall : α * (600 * Real.sqrt (1000 / (3 * α)) * C₀) ≤ 1)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hXN : ∀ τ : ℝ, 0 ≤ τ → Xn (Work.FTS.Regularity.pExp α) (slice g τ)
      ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2)
    (hcls : ∀ τ : ℝ, 0 ≤ τ → Work.Spaces.SmoothNbhd (slice g τ) ∧
      Work.Spaces.VanishTheta (slice g τ) ∧ Work.Spaces.DecayInZ 2 (slice g τ) ∧
      Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 (slice g τ)) :
    ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |g z θ τ| ≤ 3 * α / 200 := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hCg : 0 ≤ Real.sqrt (1000 / (3 * α)) := Real.sqrt_nonneg _
  have hgam : Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1 = 3 * α / 10 := by
    rw [Work.Spaces.gam_sub_one, Work.FTS.Regularity.pExp_eq]
  have hgampos : 0 < Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1 := by
    rw [hgam]; positivity
  have hconst : 100 / (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      = 1000 / (3 * α) := by
    rw [hgam]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hsup : ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |g z θ τ| ≤ Real.sqrt (1000 / (3 * α)) * Xn (Work.FTS.Regularity.pExp α) (slice g τ) := by
    intro τ hτ z hz θ hθ
    obtain ⟨hsm, hv, hd, hm⟩ := hcls τ hτ
    have h := sup_le_Xn_of_HkMem hαG hαG1 hsm hv hd hm hz hθ
    simpa only [hconst, Work.FTS.Nonlin.Xn, Work.FTS.Galerkin.slice_apply] using h
  exact hsmall_of_H4 hα hα13 hCg hC₀ hsmall hXN hsup

end Work.FTS.Final
