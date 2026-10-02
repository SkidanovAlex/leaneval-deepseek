import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.ELRig.deriv_ne_zero_of_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

/-!
# A bounded open set cannot be biholomorphic to `ℂ`

Let `U ⊆ ℂ` be open and bounded, `φ : ℂ → ℂ` holomorphic on `U`, injective on `U` and
surjective onto `ℂ`.  Then `False`.

The argument is Liouville's theorem.  Choose a set-theoretic right inverse
`G τ := Classical.choose (hsurj τ)`, so that `G τ ∈ U` and `φ (G τ) = τ` for every `τ`.  Since
`φ` is injective on `U`, `G ∘ φ` agrees near each `x ∈ U` with the identity on `U`, hence is
analytic at `x`; as `φ` is analytic at `x` and `deriv φ x ≠ 0` (an injective holomorphic map has
no critical point, `Work.ELRig.deriv_ne_zero_of_injOn`), Mathlib's analytic inverse-function
lemma `analyticAt_comp_iff_of_deriv_ne_zero` upgrades this to analyticity of `G` at `φ x`.  Since
`φ` is surjective, `G` is entire; and `G` is bounded because it takes values in the bounded set
`U`.  Liouville forces `G` to be constant, whence `0 = φ (G 0) = φ (G 1) = 1`, a contradiction.
-/
theorem false_of_bounded_of_holomorphic_bijection {U : Set ℂ} {φ : ℂ → ℂ} (hopen : IsOpen U)
    (hdiff : DifferentiableOn ℂ φ U) (hbdd : Bornology.IsBounded U)
    (hinj : Set.InjOn φ U) (hsurj : ∀ τ : ℂ, ∃ z ∈ U, φ z = τ) : False := by
  classical
  -- a set-theoretic right inverse of `φ`
  set G : ℂ → ℂ := fun τ => Classical.choose (hsurj τ) with hG_def
  have hGmem : ∀ τ, G τ ∈ U := fun τ => (Classical.choose_spec (hsurj τ)).1
  have hGeq : ∀ τ, φ (G τ) = τ := fun τ => (Classical.choose_spec (hsurj τ)).2
  -- injectivity makes `G` a left inverse of `φ` on `U`
  have hGleft : ∀ w ∈ U, G (φ w) = w := fun w hw => hinj (hGmem (φ w)) hw (hGeq (φ w))
  -- `G` is analytic at every point of the image of `φ`
  have hGan : ∀ x ∈ U, AnalyticAt ℂ G (φ x) := by
    intro x hx
    have hfx_an : AnalyticAt ℂ φ x := (hdiff.analyticOn hopen).analyticAt (hopen.mem_nhds hx)
    have hfx' : deriv φ x ≠ 0 := Work.ELRig.deriv_ne_zero_of_injOn hdiff hopen hinj hx
    have hcomp : AnalyticAt ℂ (G ∘ φ) x := by
      refine analyticAt_id.congr ?_
      filter_upwards [hopen.mem_nhds hx] with w hw
      exact (hGleft w hw).symm
    exact (analyticAt_comp_iff_of_deriv_ne_zero hfx_an hfx').mp hcomp
  -- hence `G` is entire, since `φ` is surjective
  have hGan' : ∀ τ, AnalyticAt ℂ G τ := by
    intro τ
    have hτ : τ = φ (G τ) := (hGeq τ).symm
    rw [hτ]
    exact hGan (G τ) (hGmem τ)
  have hGentire : Differentiable ℂ G := fun τ => (hGan' τ).differentiableAt
  -- and bounded, because it takes values in the bounded set `U`
  have hbddG : Bornology.IsBounded (Set.range G) :=
    hbdd.subset (Set.range_subset_iff.mpr hGmem)
  -- Liouville
  obtain ⟨c, hc⟩ := hGentire.exists_eq_const_of_bounded hbddG
  have h01 : (0 : ℂ) = 1 := by
    rw [← hGeq 0, ← hGeq 1, congr_fun hc 0, congr_fun hc 1]
    simp
  exact zero_ne_one h01

end Work.FatouParabolic.Core
