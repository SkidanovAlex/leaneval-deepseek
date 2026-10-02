import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.isDbarDeriv_moll_contDiff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Adding the identity to a function with weak `∂̄`-derivative `g`

Since `∂̄ z = 0` (both pointwise and in the weak sense), the weak `∂̄`-derivative of
`z ↦ z + F z` is again `g` whenever `F` has weak `∂̄`-derivative `g`.  Equivalently: adding
an analytic function does not change the weak `∂̄`-derivative.

The proof splits into two, purely formal, pieces:

* `isDbarDeriv_add` — the weak `∂̄`-derivative is additive (`IsDbarDeriv` is a conjunction of
  local integrability statements and an integral identity, both of which are additive);
* `isDbarDeriv_id_zero_aux` — the identity has weak `∂̄`-derivative `0`, obtained from the pointwise
  Wirtinger computation `∂̄(id) = 0` together with `isDbarDeriv_dzbar` (`Work.MRMT.Weyl`),
  which says that for a smooth function the distributional `∂̄` is the pointwise one.

The target is then `isDbarDeriv_id_zero_aux` added to the hypothesis, followed by replacing
`0 + g` by `g` pointwise.
-/

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Sobolev

/-- The weak `∂̄`-derivative is additive: if `g₁ = ∂̄F₁` and `g₂ = ∂̄F₂` in the
distributional sense, then `g₁ + g₂ = ∂̄(F₁ + F₂)`. -/
theorem isDbarDeriv_add {F₁ F₂ g₁ g₂ : ℂ → ℂ} (h₁ : Work.MRMT.IsDbarDeriv F₁ g₁)
    (h₂ : Work.MRMT.IsDbarDeriv F₂ g₂) :
    Work.MRMT.IsDbarDeriv (fun z : ℂ => F₁ z + F₂ z) (fun z : ℂ => g₁ z + g₂ z) := by
  obtain ⟨hF₁, hg₁, hψ₁⟩ := h₁
  obtain ⟨hF₂, hg₂, hψ₂⟩ := h₂
  refine ⟨hF₁.add hF₂, hg₁.add hg₂, fun φ => ?_⟩
  obtain ⟨ha₁, hb₁, hc₁⟩ := hψ₁ φ
  obtain ⟨ha₂, hb₂, hc₂⟩ := hψ₂ φ
  have ha : (fun z : ℂ => F₁ z * Work.MRMT.dzbar (φ : ℂ → ℂ) z
        + F₂ z * Work.MRMT.dzbar (φ : ℂ → ℂ) z)
      = fun z : ℂ => (F₁ z + F₂ z) * Work.MRMT.dzbar (φ : ℂ → ℂ) z := by
    funext z; ring
  have hb : (fun z : ℂ => g₁ z * (φ : ℂ → ℂ) z + g₂ z * (φ : ℂ → ℂ) z)
      = fun z : ℂ => (g₁ z + g₂ z) * (φ : ℂ → ℂ) z := by
    funext z; ring
  have hL : ∫ z, (F₁ z + F₂ z) * Work.MRMT.dzbar (φ : ℂ → ℂ) z
      = (∫ z, F₁ z * Work.MRMT.dzbar (φ : ℂ → ℂ) z)
        + ∫ z, F₂ z * Work.MRMT.dzbar (φ : ℂ → ℂ) z := by
    rw [← ha, integral_add ha₁ ha₂]
  have hR : ∫ z, (g₁ z + g₂ z) * (φ : ℂ → ℂ) z
      = (∫ z, g₁ z * (φ : ℂ → ℂ) z) + ∫ z, g₂ z * (φ : ℂ → ℂ) z := by
    rw [← hb, integral_add hb₁ hb₂]
  refine ⟨?_, ?_, ?_⟩
  · rw [← ha]; exact ha₁.add ha₂
  · rw [← hb]; exact hb₁.add hb₂
  · rw [hL, hR, hc₁, hc₂]; ring

/-- The identity map has weak `∂̄`-derivative `0`. -/
theorem isDbarDeriv_id_zero_aux : Work.MRMT.IsDbarDeriv (fun z : ℂ => z) (0 : ℂ → ℂ) :=
  Work.MRMT.Weyl.isDbarDeriv_congr
    (Work.MRMT.Weyl.isDbarDeriv_dzbar (u := fun z : ℂ => z) (n := ⊤) contDiff_id (by simp))
    (fun z => Work.MRMT.dzbar_id z)

/-- **Adding the identity does not change the weak `∂̄`-derivative.** -/
theorem isDbarDeriv_id_add {F g : ℂ → ℂ} (h : Work.MRMT.IsDbarDeriv F g) :
    Work.MRMT.IsDbarDeriv (fun z : ℂ => z + F z) g := by
  refine Work.MRMT.Weyl.isDbarDeriv_congr (g := fun z : ℂ => (0 : ℂ) + g z)
    (isDbarDeriv_add isDbarDeriv_id_zero_aux h) (fun z => by simp)

end Work.MRMT.Sobolev
