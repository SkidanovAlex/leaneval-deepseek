import Mathlib
import Submission.Work.Serre.RatTower.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The inclusion of a pair is an isomorphism when the larger relative group vanishes

For a triple `A ⊆ B ⊆ X`, the first map of the short exact sequence of the triple
`0 → C^*(B,A) → C^*(X,A) → C^*(X,B) → 0` induces `H_k(B,A) → H_k(X,A)`; this map is an isomorphism
as soon as the relative groups `H_k(X,B)` and `H_{k+1}(X,B)` vanish (the long exact sequence of the
triple is `H_{k+1}(X,B) → H_k(B,A) → H_k(X,A) → H_k(X,B)`, so the two outer terms vanishing gives
both injectivity and surjectivity).

This is the "extension of a relative class" step of the cell-by-cell construction of the relative
Thom class: a class over the old part of an attachment extends to (and is determined by) a class
over the whole attachment as soon as the new-cell groups vanish in the two relevant degrees.
-/

set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **The inclusion `H_k(B,A) → H_k(X,A)` of a triple is an isomorphism** when the relative
cohomology of `(X,B)` vanishes in degrees `k` and `k+1`. -/
theorem isIso_triple_f_of_isZero (X : TopCat) (A B : Set X) (hAB : A ⊆ B) (k : ℕ)
    (h₁ : IsZero ((Work.StemsB.relChainsR ℚ X B).homology k))
    (h₂ : IsZero ((Work.StemsB.relChainsR ℚ X B).homology (k + 1))) :
    IsIso (HomologicalComplex.homologyMap (RatTower.tripleShortR X A B hAB).f k) := by
  have hS := RatTower.tripleShortR_shortExact X A B hAB
  -- surjectivity, from the vanishing of the third term in degree `k`
  have hg0 : HomologicalComplex.homologyMap (RatTower.tripleShortR X A B hAB).g k = 0 :=
    h₁.eq_zero_of_tgt _
  haveI : Epi (HomologicalComplex.homologyMap (RatTower.tripleShortR X A B hAB).f k) :=
    (hS.homology_exact₂ k).epi_f_iff.mpr hg0
  -- injectivity, from the vanishing of the third term in degree `k+1`
  have hδ0 : hS.δ (k + 1) k (by simp [ComplexShape.down]) = 0 :=
    h₂.eq_zero_of_src _
  haveI : Mono (HomologicalComplex.homologyMap (RatTower.tripleShortR X A B hAB).f k) :=
    (hS.homology_exact₁ (k + 1) k (by simp [ComplexShape.down])).mono_g_iff.mpr hδ0
  exact isIso_of_mono_of_epi _

end

end Work.Serre
