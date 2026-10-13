/-
# `lamContDiffOn`: the truncated angular moment `lam n F` is `C^m` on `(0,∞)`

The moment of the truncated source is

  `lam n F z = ∫ θ in Iθ, zetaR n θ · F z θ · sinθcos²θ`,

with `zetaR n` the angular cutoff of `CptApp.Defs`, supported in `(1/n, π/2 - 1/n)` — strictly
inside the open angular interval.  Hence the angular integration is a *local* (compactly
supported) operation in `θ`, and every `z`-derivative may be pulled through it.  The present
module records that the resulting function of `z` is `C^m` on the whole half-line `(0,∞)`,
for every `m` — this is the smoothness input for the estimates on the cutoff family
(`CptApp.Estimate`).

The proof is the `D_z`-bootstrap of the sibling module `CptApp.lamDzDeriv`: writing

  `lamSlice n F j z = ∫ θ in Iθ, zetaR n θ · D_z^j F z θ · sinθcos²θ`

for the angular moment of the `j`-th `D_z`-iterate of `F` (so that `lamSlice n F 0 = lam n F`),
`hasDerivAt_lamSlice` gives, for every `z > 0`,

  `(lamSlice n F j)' z = ∫ θ, zetaR n θ · ∂_z(D_z^j F) z θ · sinθcos²θ = z⁻¹ · lamSlice n F (j+1) z`,

the second equality because `D_z^{j+1} F = z · ∂_z(D_z^j F)` (`D_z = z ∂_z`).  Since
`z ↦ z⁻¹` is smooth on `(0,∞)`, a downward induction on the order promotes the chain
`(g j)' = z⁻¹ · g (j+1)` to `ContDiffOn ℝ m (g 0) (Ioi 0)`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.lamDzDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty.CptApp.LamEst

/-! ## The iterated `D_z`-moments -/

/-- The angular moment of the `j`-th `D_z`-iterate of `F`:
`lamSlice n F j z = ∫ θ in Iθ, zetaR n θ · D_z^j F z θ · sinθcos²θ`. -/
def lamSlice (n : ℕ) (F : ℝ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ,
    Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ * Work.Spaces.DzIter j F z θ
      * Work.Elliptic.sinCos2 θ

/-- The `0`-th iterate is the moment `lam` itself. -/
theorem lamSlice_zero (n : ℕ) (F : ℝ → ℝ → ℝ) :
    lamSlice n F 0 = fun z => Work.FTS.PhiStar.Honesty.CptApp.lam n F z := rfl

/-- Since `D_z^{j+1} F = z · ∂_z(D_z^j F)`, pulling the factor `z` out of the angular integral
turns the derivative of the `j`-th slice into the `(j+1)`-st slice. -/
theorem inv_mul_integral_DzIter_succ (F : ℝ → ℝ → ℝ) (n j : ℕ) {z : ℝ} (hz : z ≠ 0) :
    z⁻¹ * lamSlice n F (j + 1) z = ∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter j F) z θ
        * Work.Elliptic.sinCos2 θ := by
  have hpt : ∀ θ : ℝ, Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ *
        Work.Spaces.DzIter (j + 1) F z θ * Work.Elliptic.sinCos2 θ
      = z * (Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ *
        Work.Spaces.pz (Work.Spaces.DzIter j F) z θ * Work.Elliptic.sinCos2 θ) := by
    intro θ
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    ring
  rw [lamSlice, MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul, inv_mul_cancel_left₀ hz]

/-! ## The `C^m`-bootstrap along the chain `(g j)' = z⁻¹ · g (j+1)` -/

/-- Bootstrap step: if `f` has derivative `f'` on the open set `U` and `f'` is `C^n` there,
then `f` is `C^{n+1}`. -/
theorem contDiffOn_succ_of_hasDerivAt {f f' : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (n : ℕ)
    (h : ∀ z ∈ U, HasDerivAt f (f' z) z) (hf' : ContDiffOn ℝ n f' U) :
    ContDiffOn ℝ (n + 1) f U := by
  rw [contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨fun z hz => (h z hz).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro hn
    exact absurd hn (by norm_num)
  · exact hf'.congr (fun x hx => (h x hx).deriv)

/-- Given a sequence `g j` on an open set `U ⊆ (0,∞)` with derivative `(g j)' = z⁻¹ · g (j+1)`
for every `j`, the function `g 0` is `C^m` on `U`.

Indeed, `g (m-1)` is continuously differentiable because its derivative `z⁻¹ · g m` is
continuous (`g m` is differentiable by hypothesis), and one then inducts backwards on the
number of remaining derivatives. -/
theorem contDiffOn_of_hasDerivAt_inv_succ {g : ℕ → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hUpos : ∀ z ∈ U, 0 < z)
    (h : ∀ j : ℕ, ∀ z ∈ U, HasDerivAt (g j) (z⁻¹ * g (j + 1) z) z) (m : ℕ) :
    ContDiffOn ℝ m (g 0) U := by
  -- `key k` states that `g j` is `C^k` whenever `m - j = k`, i.e. `g (m-k)` is `C^k`.
  have key : ∀ k : ℕ, ∀ j : ℕ, m - j = k → ContDiffOn ℝ k (g j) U := by
    intro k
    induction k with
    | zero =>
      -- `m - j = 0` means `j ≥ m`; `g j` is merely differentiable, hence continuous.
      intro j _hj
      exact contDiffOn_zero.mpr (DifferentiableOn.continuousOn
        (fun z hz => (h j z hz).differentiableAt.differentiableWithinAt))
    | succ k ih =>
      -- If `m - j = k + 1`, then `m - (j+1) = k`, so `g (j+1)` is `C^k` by the induction
      -- hypothesis; `z⁻¹ · g (j+1) z` is then also `C^k`, and it is the derivative of `g j`.
      intro j hj
      have hjm : m - (j + 1) = k := by omega
      have hgj : ContDiffOn ℝ k (g (j + 1)) U := ih (j + 1) hjm
      have hinv : ContDiffOn ℝ k (fun z : ℝ => z⁻¹) U :=
        (contDiffOn_inv ℝ).mono (fun z hz => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact ne_of_gt (hUpos z hz))
      have hf' : ContDiffOn ℝ k (fun z : ℝ => z⁻¹ * g (j + 1) z) U := hinv.mul hgj
      exact contDiffOn_succ_of_hasDerivAt hU k (h j) hf'
  exact key m 0 (Nat.sub_zero m)

/-! ## The result -/

theorem lamContDiffOn {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    ContDiffOn ℝ m (fun z : ℝ => Work.FTS.PhiStar.Honesty.CptApp.lam n F z) (Set.Ioi 0) := by
  have hderiv : ∀ j : ℕ, ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (lamSlice n F j) (z⁻¹ * lamSlice n F (j + 1) z) z := by
    intro j z hz
    have hz' : (0 : ℝ) < z := hz
    have h := Work.FTS.PhiStar.Honesty.CptApp.hasDerivAt_lamSlice hsm hn j hz'
    rw [inv_mul_integral_DzIter_succ F n j (ne_of_gt hz')]
    exact h
  have hmain : ContDiffOn ℝ m (lamSlice n F 0) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_of_hasDerivAt_inv_succ isOpen_Ioi (fun z hz => hz) hderiv m
  rw [lamSlice_zero] at hmain
  exact hmain

end Work.FTS.PhiStar.Honesty.CptApp.LamEst
