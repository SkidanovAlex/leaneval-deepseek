import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Core.extFatou_injective_of_injOn
import Submission.Work.FatouParabolic.Basin.mapsTo_puncturedBasin
import Submission.Work.ELRig.deriv_ne_zero_of_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

/-!
# Liouville: the punctured basin cannot carry an injective, surjective Fatou coordinate

If `extFatou fl` were injective on the punctured basin `U = puncturedBasin F z₀`, holomorphic
there (`hdiff`), and surjective onto `ℂ` (`hsurj`), while `U` were bounded (`hbdd`), then `ℂ`
would be biholomorphic to the bounded open set `U`, contradicting Liouville's theorem.

The contradiction is obtained exactly along these lines, but *without* ever exhibiting the
inverse as a holomorphic function by hand.  Choose a set-theoretic right inverse
`G τ := Classical.choose (hsurj τ)`, so that `f (G τ) = τ` and `G τ ∈ U`.  For `x ∈ U`, the
function `G ∘ f` agrees near `x` with the identity (because `f` is injective on `U`), hence is
analytic at `x`; since `f` is analytic at `x` with `deriv f x ≠ 0`
(`Work.ELRig.deriv_ne_zero_of_injOn`), the analytic inverse-function theorem in the form
`analyticAt_comp_iff_of_deriv_ne_zero` upgrades this to analyticity of `G` at `f x`.  As
`f` is surjective, `G` is entire, and it is bounded because it maps into the bounded set `U`.
Liouville then makes `G` constant, so `0 = f (G 0) = f (G 1) = 1`.
-/
theorem false_of_bounded_of_injOn_of_surjective {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀)
    (hopen : IsOpen (Work.FatouParabolic.puncturedBasin F z₀))
    (hdiff : DifferentiableOn ℂ (Work.FatouParabolic.extFatou fl)
      (Work.FatouParabolic.puncturedBasin F z₀))
    (hbdd : Bornology.IsBounded (Work.FatouParabolic.puncturedBasin F z₀))
    (hinj : Set.InjOn (Work.FatouParabolic.extFatou fl) (Work.FatouParabolic.puncturedBasin F z₀))
    (hsurj : ∀ τ : ℂ, ∃ z ∈ Work.FatouParabolic.puncturedBasin F z₀,
      Work.FatouParabolic.extFatou fl z = τ) : False := by
  classical
  set f := Work.FatouParabolic.extFatou fl with hf_def
  set U := Work.FatouParabolic.puncturedBasin F z₀ with hU_def
  -- a set-theoretic right inverse of `f` on the basin
  set G : ℂ → ℂ := fun τ => Classical.choose (hsurj τ) with hG_def
  have hGmem : ∀ τ, G τ ∈ U := fun τ => (Classical.choose_spec (hsurj τ)).1
  have hGeq : ∀ τ, f (G τ) = τ := fun τ => (Classical.choose_spec (hsurj τ)).2
  -- injectivity makes `G` a left inverse of `f` on `U`
  have hGleft : ∀ w ∈ U, G (f w) = w := fun w hw => hinj (hGmem (f w)) hw (hGeq (f w))
  -- `G` is analytic at every point of the image of `f`
  have hGan : ∀ x ∈ U, AnalyticAt ℂ G (f x) := by
    intro x hx
    have hfx_an : AnalyticAt ℂ f x := (hdiff.analyticOn hopen).analyticAt (hopen.mem_nhds hx)
    have hfx' : deriv f x ≠ 0 := Work.ELRig.deriv_ne_zero_of_injOn hdiff hopen hinj hx
    have hcomp : AnalyticAt ℂ (G ∘ f) x := by
      refine analyticAt_id.congr ?_
      filter_upwards [hopen.mem_nhds hx] with w hw
      exact (hGleft w hw).symm
    exact (analyticAt_comp_iff_of_deriv_ne_zero hfx_an hfx').mp hcomp
  -- hence `G` is entire, since `f` is surjective
  have hGan' : ∀ τ, AnalyticAt ℂ G τ := by
    intro τ
    have hτ : τ = f (G τ) := (hGeq τ).symm
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
    rfl
  exact zero_ne_one h01

end Work.FatouParabolic.Core
