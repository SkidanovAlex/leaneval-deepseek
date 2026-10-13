/-
# `Work.FTS.RegPkgGal.Der.sup2_extG_ext` — `sup2_extG` for the *extension's* slice data

The sibling `Work.FTS.RegPkgGal.Der.sup2_extG` bounds `|∂_z²g̃|` uniformly on
`{z > 0} × Iθ × [0,S]` from the *slice data of `g`*: for `0 < z ≤ 2` it consumes the class
hypothesis `|∂_z²(g-slice)| ≤ Q₂`, and for `z > 2` the `ℋ⁴`-norm `hHkn`.  In downstream uses the
near-axis hypothesis is naturally available for the **extension** `g̃ = extG g` instead, i.e.

  `|∂_z²(g̃-slice)| ≤ Q₂`  on `0 < z ≤ 2`.

Since for `τ ≥ 0` and `z > 0` the extension slice `z' ↦ extG g z' θ τ` *is* the slice of `g`
(`extG_of_pos`), the two hypotheses are equivalent: `deriv` is local, so `∂_z²` agrees on the open
half line `Ioi 0` (`pz_pz_extG_eq`).  The present lemma is therefore the same statement as
`sup2_extG` with the hypothesis transported, and its proof is the reduction
`(∂_z² of the extension slice) = (∂_z² of the g-slice)` followed by `sup2_extG`.

The statement is unchanged from the requested one; only the missing `open scoped Real` is added
(without it the bare `π` of the statement is an unknown identifier under `autoImplicit = false`,
cf. the identical fix in `sup2_extG.lean`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegPkgGal.Der.sup2_extG
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real
open Set

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

/-- **Congruence of `∂_z²` between the extension slice and the slice of `g`.**  For `τ ≥ 0` the
two functions `z' ↦ extG g z' θ τ` and `z' ↦ g z' θ τ` agree on the open half line `Ioi 0`
(`extG_of_pos`), and `pz` is a local operator, so their second `z`-derivatives agree at every
`z > 0`.  (This is a verbatim copy of the private lemma of the same name in `sup2_extG.lean`,
which is not exported.) -/
private lemma pz_pz_extG_eq {g : Work.FTS.RegPkgGal.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z) :
    Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ
      = Work.Spaces.pz (Work.Spaces.pz (fun z θ => g z θ τ)) z θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hagree : EqOn (Function.uncurry (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ))
      (Function.uncurry (fun z θ => g z θ τ)) (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    rintro ⟨z', θ'⟩ ⟨hz', -⟩
    exact Work.FTS.RegPkgGal.extG_of_pos hz' hτ
  have h1 : EqOn (Function.uncurry (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)))
      (Function.uncurry (Work.Spaces.pz (fun z θ => g z θ τ)))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    intro y hy
    exact Work.Spaces.pz_congr_of_isOpen hV hagree hy
  exact Work.Spaces.pz_congr_of_isOpen hV h1 ⟨hz, trivial⟩

theorem sup2_extG_ext {α S : ℝ} {g : Work.FTS.RegPkgGal.Fam} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hS : 0 < S)
    (hRQ : ∀ τ ∈ Set.Icc 0 S, Work.FTS.Nonlin.RegQ (Work.FTS.Regularity.pExp α) 4
      (Work.FTS.Regularity.gSlice g τ))
    (hHkn : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ τ ∈ Set.Icc 0 S,
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (Work.FTS.Regularity.gSlice g τ) ≤ C₀)
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0)
    (hq2 : ∃ Q₂ : ℝ, 0 ≤ Q₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ,
      0 < z → z ≤ 2 →
      |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG g) τ))
        z θ| ≤ Q₂) :
    ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ| ≤ M₂ := by
  obtain ⟨Q₂, hQ₂nn, hQ₂bd⟩ := hq2
  -- the near-axis hypothesis, transported from the extension slice to the slice of `g`
  refine sup2_extG hα hα13 hS hRQ hHkn hvan ⟨Q₂, hQ₂nn, ?_⟩
  intro τ hτ θ hθ z hz hz2
  show |Work.Spaces.pz (Work.Spaces.pz (fun z θ => g z θ τ)) z θ| ≤ Q₂
  have h : |Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ|
      ≤ Q₂ := hQ₂bd τ hτ θ hθ z hz hz2
  rwa [pz_pz_extG_eq (g := g) hτ.1 hz] at h

end Work.FTS.RegPkgGal.Der
