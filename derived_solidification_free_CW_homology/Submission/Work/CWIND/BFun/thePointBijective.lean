import Mathlib
import Submission.Work.CWIND.Basic

/-!
# CWIND/BFun: the canonical point of `X^{Δⁿ}` is a bijection onto the underlying set at a point

The light condensed set `topCatToLightCondSet.obj (X^{Δⁿ})` is the presheaf
`S ↦ C(S, X^{Δⁿ})` on light profinite sets.  At the one-point light profinite set `↧PUnit` its
value is `C(↧PUnit, X^{Δⁿ})`, which is *canonically* the set `C(Δⁿ, X)` of continuous maps
`Δⁿ ⟶ X` — i.e. the set of singular `n`-simplices of `X`.

`Work.CWIND.thePoint X n` is exactly this comparison: it sends a singular `n`-simplex `x` (a
continuous map `Δⁿ ⟶ X`) to the constant map `↧PUnit ⟶ X^{Δⁿ}` at `x`.  Since `↧PUnit` is a
one-point space, every continuous map `↧PUnit ⟶ X^{Δⁿ}` is constant and is determined by its value
at the unique point, so `thePoint X n` is a bijection.  This is what makes the comparison map
`bLevel` (`Basic.lean`) the "identity on simplices" in level `n`.
-/

noncomputable section

open CategoryTheory Opposite

namespace Work.CWIND.BFun

/-- The map sending a point of a space to the corresponding constant map out of the one-point
light profinite set `↧PUnit` is injective: evaluate at the unique point. -/
lemma const'_injective (Y : TopCat.{0}) :
    Function.Injective (fun y : ↥Y =>
      ContinuousMap.const' (X := ↥(LightProfinite.of PUnit.{1})) (Y := ↥Y) y) := by
  intro a b h
  have h2 := congrArg (fun f : C(↥(LightProfinite.of PUnit.{1}), ↥Y) => f default) h
  simpa using h2

/-- The map sending a point of a space to the corresponding constant map out of the one-point
light profinite set `↧PUnit` is surjective: a continuous map out of a one-point space is constant,
with value its value at the unique point. -/
lemma const'_surjective (Y : TopCat.{0}) :
    Function.Surjective (fun y : ↥Y =>
      ContinuousMap.const' (X := ↥(LightProfinite.of PUnit.{1})) (Y := ↥Y) y) := by
  intro f
  refine ⟨f default, ?_⟩
  ext p
  obtain rfl : p = default := Subsingleton.elim p default
  rfl

/-- The set of singular `n`-simplices of `X` is the underlying set at `↧PUnit` of the light
condensed set `X^{Δⁿ}`: every point is a constant map, hence is given by a continuous map
`Δⁿ ⟶ X`. -/
theorem thePointBijective (X : TopCat.{0}) (n : ℕ) :
    Function.Bijective (Work.CWIND.thePoint X n) := by
  have h1 : Function.Bijective (fun y : ↥(Work.CWIND.singSpace X n) =>
      ContinuousMap.const' (X := ↥(LightProfinite.of PUnit.{1}))
        (Y := ↥(Work.CWIND.singSpace X n)) y) :=
    ⟨const'_injective _, const'_surjective _⟩
  exact h1.comp (TopCat.toSSetObjEquiv X _).bijective

end Work.CWIND.BFun
