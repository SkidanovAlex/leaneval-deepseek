/-
# The CONSTRUCTION area: the individual terms of `N₀`, `N` and `N_*`

The a-priori estimate of §Modulation is a term-by-term estimate of the `ℋ⁴` inner product of
`\eqref{gEquationFinal}` with `g`.  This module fixes the *names* of the individual terms of
`N₀` (tex `\eqref{N0}`, called `I^{N₀}_1, …, I^{N₀}_6` in the paper), of `N`
(tex `\eqref{N}`, called `I^{N}_1, …, I^{N}_5`) and of `N_*` (tex `\eqref{N*}`), together with
the two splits the paper performs inside `I^{N₀}_4, I^{N₀}_5` (the `F_*`-part and the `g`-part
of the transported factor), and the sum identities

* `N0_eq_sum`, `N_eq_sum`, `Nstar_eq_sum`.

These are the objects every estimate in `Submission/Work/Construction/Apriori.lean` is about.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## The terms of `N₀` -/

/-- `I^{N₀}_1 = (3/(2α)) sin(2θ) L₁₂(F_*) ∂_θF_*` (first half of tex 1398). -/
def N01 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth (Fstar α) z θ

/-- `I^{N₀}_2 = -(cos2θ - sin²θ) L₁₂(F_*) z∂_zF_*` (second half of tex 1398). -/
def N02 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -c2m θ * L12 (Fstar α) z * Work.Spaces.Dz (Fstar α) z θ

/-- `I^{N₀}_3 = (1/α) L₁₂(g) g`. -/
def N03 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (1 / α) * L12 g z * g z θ

/-- `I^{N₀}_4 = (3/(2α))sin(2θ)L₁₂(g)∂_θF` (with the full `F = F_* + g`). -/
def N04 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (3 / (2 * α)) * s2 θ * L12 g z * Work.Spaces.pth F z θ

/-- First half of `I^{N₀}_4`: `(3/(2α))sin(2θ)L₁₂(g)∂_θF_*`. -/
def N04a (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (3 / (2 * α)) * s2 θ * L12 g z * Work.Spaces.pth (Fstar α) z θ

/-- Second half of `I^{N₀}_4`: `(3/(2α))sin(2θ)L₁₂(g)∂_θg`. -/
def N04b (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (3 / (2 * α)) * s2 θ * L12 g z * Work.Spaces.pth g z θ

/-- `I^{N₀}_5 = -(cos2θ-sin²θ)L₁₂(g)z∂_zF` (with the full `F = F_* + g`). -/
def N05 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -c2m θ * L12 g z * Work.Spaces.Dz F z θ

/-- First half of `I^{N₀}_5`: `-(cos2θ-sin²θ)L₁₂(g)z∂_zF_*`. -/
def N05a (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -c2m θ * L12 g z * Work.Spaces.Dz (Fstar α) z θ

/-- Second half of `I^{N₀}_5`: `-(cos2θ-sin²θ)L₁₂(g)z∂_zg`. -/
def N05b (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -c2m θ * L12 g z * Work.Spaces.Dz g z θ

/-- `I^{N₀}_6 = -(cos2θ-sin²θ)L₁₂(F_*)z∂_zg`. -/
def N06 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -c2m θ * L12 (Fstar α) z * Work.Spaces.Dz g z θ

theorem N0_eq_sum (α : ℝ) (F g : ℝ → ℝ → ℝ) :
    N0 α F g = N01 α F g + N02 α F g + N03 α F g + N04 α F g + N05 α F g + N06 α F g := by
  funext z θ
  simp only [N0, N01, N02, N03, N04, N05, N06, Pi.add_apply]
  ring

/-- The paper's split of `I^{N₀}_4` into its `F_*`-part and its `g`-part. -/
theorem N04_eq_halves (α : ℝ) {F g : ℝ → ℝ → ℝ}
    (hpth : ∀ z θ, Work.Spaces.pth F z θ
      = Work.Spaces.pth (Fstar α) z θ + Work.Spaces.pth g z θ) :
    N04 α F g = fun z θ => N04a α F g z θ + N04b α F g z θ := by
  funext z θ
  simp only [N04, N04a, N04b]
  rw [hpth z θ]
  ring

/-- The paper's split of `I^{N₀}_5` into its `F_*`-part and its `g`-part. -/
theorem N05_eq_halves (α : ℝ) {F g : ℝ → ℝ → ℝ}
    (hDz : ∀ z θ, Work.Spaces.Dz F z θ
      = Work.Spaces.Dz (Fstar α) z θ + Work.Spaces.Dz g z θ) :
    N05 α F g = fun z θ => N05a α F g z θ + N05b α F g z θ := by
  funext z θ
  simp only [N05, N05a, N05b]
  rw [hDz z θ]
  ring

/-! ## The terms of `N` -/

/-- `I^{N}_1 = 2ℛ(Φ - (1/4α)sin2θL₁₂(F)) F`. -/
def N1 (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  2 * Rop α (PhiTil α F Φ) z θ * F z θ

/-- `I^{N}_2 = -2U(Φ - (1/4α)sin2θL₁₂(F)) ∂_θF`. -/
def N2 (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -2 * Uop α (PhiTil α F Φ) z θ * Work.Spaces.pth F z θ

/-- `I^{N}_3 = -2αV(Φ - (1/4α)sin2θL₁₂(F)) z∂_zF`. -/
def N3 (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -2 * α * Vop (PhiTil α F Φ) z θ * Work.Spaces.Dz F z θ

/-- `I^{N}_4 = -(1/2)sin(2θ)(F,K)_{L²_θ}∂_θF` (the angular-moment term; the paper writes the
coefficient `-α`, see the module docstring of `Defs.lean`). -/
def N4 (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -(1 / 2) * s2 θ * FK F z * Work.Spaces.pth F z θ

/-- `I^{N}_5 = -sin²θ (F,K)_{L²_θ} F` (the second angular-moment term). -/
def N5 (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -Real.sin θ ^ 2 * FK F z * F z θ

theorem N_eq_sum (α : ℝ) (F Φ : ℝ → ℝ → ℝ) :
    N α F Φ = N1 α F Φ + N2 α F Φ + N3 α F Φ + N4 α F Φ + N5 α F Φ := by
  funext z θ
  simp only [N, N1, N2, N3, N4, N5, Pi.add_apply]
  ring

/-! ## The terms of `N_*` -/

/-- `N_*,1 = -μg`. -/
def Ns1 (μ lam : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => -μ * g z θ

/-- `N_*,2 = -(μ+λ+μλ)z∂_zg`. -/
def Ns2 (μ lam : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -(μ + lam + μ * lam) * Work.Spaces.Dz g z θ

theorem Nstar_eq_sum (μ lam : ℝ) (g : ℝ → ℝ → ℝ) :
    Nstar μ lam g = Ns1 μ lam g + Ns2 μ lam g := by
  funext z θ
  simp only [Nstar, Ns1, Ns2, Pi.add_apply]
  ring

end Work.Construction
