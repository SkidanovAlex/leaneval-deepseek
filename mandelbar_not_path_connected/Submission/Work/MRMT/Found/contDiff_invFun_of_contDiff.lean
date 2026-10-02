import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The inverse of a bijective `C¹` local diffeomorphism is `C¹`

Let `F : ℂ → ℂ` be a `C¹` map (over `ℝ`) which is bijective and whose Fréchet derivative
at every point is an invertible `ℝ`-linear map.  Then `Function.invFun F`, the set-theoretic
inverse of `F`, is again `C¹`.

The proof is the classical one: by the inverse function theorem `F` is a local diffeomorphism
everywhere, so at each point `x` the local inverse `(hF.contDiffAt).localInverse hf' hn` is `C¹`
near `F x` (`ContDiffAt.to_localInverse`).  Since `F` is bijective, `Function.invFun F` agrees
with that local inverse near `F x` (`HasStrictFDerivAt.localInverse_unique`), and `C¹`-ness is a
local property (`ContDiffAt.congr_of_eventuallyEq`).  Finally `ContDiff ℝ 1` is the pointwise
statement `∀ y, ContDiffAt ℝ 1 · y` (`contDiff_iff_contDiffAt`).
-/

namespace Work.MRMT.Found

open Function
open scoped Topology

theorem contDiff_invFun_of_contDiff {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hbij : Function.Bijective F)
    (hd : ∀ z : ℂ, ∃ f' : ℂ ≃L[ℝ] ℂ, HasFDerivAt F (f' : ℂ →L[ℝ] ℂ) z) :
    ContDiff ℝ 1 (Function.invFun F) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  obtain ⟨x, rfl⟩ := hbij.2 y
  obtain ⟨f', hf'⟩ := hd x
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  -- the two functions are inverse to each other
  have hg : ∀ᶠ t in 𝓝 x, Function.invFun F (F t) = t :=
    Filter.Eventually.of_forall fun t => Function.leftInverse_invFun hbij.1 t
  -- the local inverse of `F` at `x` agrees with `Function.invFun F` near `F x`
  have heq : Function.invFun F =ᶠ[𝓝 (F x)] ((hF.contDiffAt).localInverse hf' hn) :=
    (ContDiffAt.hasStrictFDerivAt' hF.contDiffAt hf' hn).localInverse_unique hg
  -- the local inverse is `C¹` at `F x`, and `C¹`-ness is local
  exact (ContDiffAt.to_localInverse _ hf' hn).congr_of_eventuallyEq heq

end Work.MRMT.Found
