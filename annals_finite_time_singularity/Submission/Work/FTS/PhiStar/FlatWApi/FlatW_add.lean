/-
# `FTS/PhiStar/FlatWApi/FlatW_add.lean` — the flat class `FlatW` is closed under addition

`Work.FTS.VocabO2.FlatW l f K` records, on the open quadrant `Q0 = (0,∞) × (0,π/2)`,

* `|(z+1)^k · ∂_z^k f| ≤ K` for `k ≤ l`, and
* `|(z+1)^k · ∂_z^k D_θ^i (∂_θ f)| ≤ K` for `k + i + 1 ≤ l`.

This file proves that `FlatW` is closed under pointwise addition, with the additive constant
`K₁ + K₂` (the requested statement allows the universal constant `1`).

The analytic input is the **pointwise additivity of the iterated operators on the open
quadrant** for `C^∞` data:

* `∂_z^k (f + g) = ∂_z^k f + ∂_z^k g` — this is `Work.FTS.PhiStar.CoreAux.pzIter_DthIter_add_Q0`
  (proved in `CoreAux/F0_add.lean`), used here at `D_θ`-order `0` for the first conjunct and at
  `D_θ`-order `i` for the `∂_θ`-family;
* for the second conjunct one must first replace `∂_θ(f + g)` by `∂_θf + ∂_θg`, which is the
  product-free instance of `deriv_add` on the `θ`-slices (both slices are `C^∞` at interior
  angles by `SmoothOpen.curry_θ`), and then transfer pointwise equalities on the open quadrant
  through the *local* operators `∂_θ`, `D_θ`, `∂_z` (`agree_pzIter`, `agree_DthIter` below).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWApi

set_option autoImplicit false

/-! ## Locality of the iterated operators on the open quadrant

`∂_z`, `∂_θ`, `D_θ = sin(2·)·∂_θ` are all built from `deriv`, which only depends on the germ of
a function at the point; hence so are all their iterates.  No smoothness is needed for these
two lemmas, only that the open quadrant is a neighbourhood of the point in the relevant
variable. -/

/-- `∂_z^k` respects agreement on the open quadrant. -/
private theorem agree_pzIter {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (k : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pzIter k F z θ = Work.Spaces.pzIter k G z θ := by
  induction k with
  | zero => exact h
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' : ℝ => Work.Spaces.pzIter n F z' θ)
          =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.pzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      exact heq.deriv_eq

/-- `D_θ^i` respects agreement on the open quadrant. -/
private theorem agree_DthIter {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i F z θ = Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
      have heq : (fun θ' : ℝ => Work.Spaces.DthIter n F z θ')
          =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.DthIter n G z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq]

/-! ## The `θ`-derivative of a sum -/

/-- **`∂_θ(f + g) = ∂_θf + ∂_θg` on the open quadrant** for `C^∞` data: the `θ`-slices are
differentiable at every interior angle, so `deriv_add` applies. -/
private theorem pth_add_Q0 {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pth f z θ + Work.Spaces.pth g z θ := by
  intro z θ hz h1 h2
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
  have hd1 : DifferentiableAt ℝ (fun θ' : ℝ => f z θ') θ :=
    ((hf.curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hd2 : DifferentiableAt ℝ (fun θ' : ℝ => g z θ') θ :=
    ((hg.curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  simp only [Work.Spaces.pth]
  rw [show (fun θ' : ℝ => f z θ' + g z θ')
      = ((fun θ' : ℝ => f z θ') + (fun θ' : ℝ => g z θ')) from by funext θ'; rfl]
  exact deriv_add hd1 hd2

/-! ## Additivity of `∂_z^k D_θ^i ∂_θ` -/

/-- **Additivity of `∂_z^k D_θ^i (∂_θ ·)` on the open quadrant** for `C^∞` data.  The point is
that `∂_θ(f + g) = ∂_θf + ∂_θg` pointwise on `Q0` (`pth_add_Q0`), after which the additivity of
`∂_z^k D_θ^i` (`Work.FTS.PhiStar.CoreAux.pzIter_DthIter_add_Q0`, applied to `∂_θf` and
`∂_θg`) is transferred to `∂_θ(f + g)` through the locality of `D_θ^i` and `∂_z^k`. -/
private theorem pzIter_DthIter_pth_add {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (i k : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pzIter k (Work.Spaces.DthIter i
          (Work.Spaces.pth (fun z θ => f z θ + g z θ))) z θ
        = Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Spaces.pth f)) z θ
          + Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Spaces.pth g)) z θ := by
  have hpth := pth_add_Q0 hf hg
  intro z θ hz h1 h2
  -- transfer `∂_θ(f + g)` to `∂_θf + ∂_θg` under `∂_z^k D_θ^i`
  have hloc : Work.Spaces.pzIter k (Work.Spaces.DthIter i
        (Work.Spaces.pth (fun z θ => f z θ + g z θ))) z θ
      = Work.Spaces.pzIter k (Work.Spaces.DthIter i
          (fun z θ => Work.Spaces.pth f z θ + Work.Spaces.pth g z θ)) z θ :=
    agree_pzIter
      (F := Work.Spaces.DthIter i (Work.Spaces.pth (fun z θ => f z θ + g z θ)))
      (G := Work.Spaces.DthIter i (fun z θ => Work.Spaces.pth f z θ + Work.Spaces.pth g z θ))
      (fun z θ hz h1 h2 => agree_DthIter hpth i z θ hz h1 h2) k z θ hz h1 h2
  rw [hloc]
  exact Work.FTS.PhiStar.CoreAux.pzIter_DthIter_add_Q0 (hf.pth) (hg.pth) i k z θ hz h1 h2

/-! ## The main theorem -/

theorem FlatW_add : ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ) (f g : ℝ → ℝ → ℝ) (K₁ K₂ : ℝ),
    0 ≤ K₁ → 0 ≤ K₂ →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
    Work.FTS.VocabO2.FlatW l f K₁ → Work.FTS.VocabO2.FlatW l g K₂ →
    Work.FTS.VocabO2.FlatW l (fun z θ => f z θ + g z θ) (C * (K₁ + K₂)) := by
  refine ⟨1, one_pos, ?_⟩
  intro l f g K₁ K₂ hK₁ hK₂ hf hg hF hG z θ hz h1 h2
  simp only [one_mul]
  obtain ⟨hF1, hF2⟩ := hF z θ hz h1 h2
  obtain ⟨hG1, hG2⟩ := hG z θ hz h1 h2
  refine ⟨?_, ?_⟩
  · intro k hk
    have hsplit := Work.FTS.PhiStar.CoreAux.pzIter_DthIter_add_Q0 hf hg 0 k z θ hz h1 h2
    simp only [Work.Spaces.DthIter_zero] at hsplit
    rw [hsplit, mul_add]
    exact le_trans (abs_add_le _ _) (add_le_add (hF1 k hk) (hG1 k hk))
  · intro k i hki
    have hsplit := pzIter_DthIter_pth_add hf hg i k z θ hz h1 h2
    rw [hsplit, mul_add]
    exact le_trans (abs_add_le _ _) (add_le_add (hF2 k i hki) (hG2 k i hki))

end Work.FTS.PhiStar.FlatWApi
