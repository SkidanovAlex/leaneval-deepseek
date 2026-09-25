/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Shimizu's residue-character detector from the units of the completion and local reciprocity

`NK.LocalTame.Zl2ResidueChar p κ K'` says that `p` is the unique prime `ℓ` for which
`G_κ` has a `ℤ_ℓ²`-quotient.  Its two directions are now:

* **`ℓ ≠ p`**: `NK.TameStructureDeep.Tame.not_hasZl2Quotient_of_ne_resCharAt` — **unconditional**
  at every place, and *group-theoretic*: a hom `G_κ ↠ (ℤ/ℓ^n)²` kills the pro-`p` wild inertia and
  hence factors through the abstract abelianisation `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}`, whose
  `ℤ_ℓ²`-quotients are killed by the counting bound
  `|Ψ '' Ẑ| · |Ψ '' μ_{q-1}| ≤ ℓ^n · ℓ^{v_ℓ(q-1)} < ℓ^{2n}`.  **No openness of finite-index
  subgroups and no local class field theory are used.**
* **`ℓ = p`**: `NK.Mine.hasZl2Quotient_of_hasZl2Quotient_completionUnits` — from the infinite-level
  reciprocity isomorphism `κˣ^{∧} ≅ G_κ^{ab}` (an `ArtinReciprocity` datum for the completion, via
  `NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion`) and the `ℤ_p²`-detection for the units
  (`NK.Mine.hasZl2Quotient_completionUnits_iff`, from `NK.LocalInputs.LocalFieldInputs`, i.e. from
  the structure `𝒪_κ^× ⧸ U¹ ≅ μ_{q-1}`, `U¹ ≅ ℤ_p^{[κ:ℚ_p]}` of Serre, *Local Fields*, Ch. II §5).

So Shimizu's detector at a place needs exactly the two named sibling inputs
`NK.LocalInputs.LocalFieldInputs K 𝔭 p` and `NK.LocalCFT.ArtinReciprocity (K_𝔭) K'`, and outside
those it is proved here.  Note in particular that the previous route
(`NK.Mine.zl2ResidueChar_adicCompletion`) needed openness of the index-`ℓ` normal subgroups
(Nikolov–Segal) — that hypothesis is **no longer used**.
-/
import Submission.NK.TameStructureDeep.Tame.not_hasZl2Quotient_of_ne_resCharAt
import Submission.NK.Mine.zl2ResidueChar_adicCompletion
import Submission.NK.Mine.hasZl2Quotient_completionUnits_iff
import Submission.NK.LocalCFT.All

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
  [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']

/-- **Shimizu's residue-character detector at a place, from the units and local reciprocity.**

For `κ = K_𝔭`, `p` a prime with `CharP (ResidueField 𝒪_κ) p`, a separable closure `K'`, an
`ArtinReciprocity` datum `D` for `(κ, K')` and the local-field input on the units
`NK.LocalInputs.LocalFieldInputs K 𝔭 p`, the prime `p` is the unique prime `ℓ` for which
`Gal(K'/κ)` has a `ℤ_ℓ²`-quotient. -/
theorem zl2ResidueChar_of_localFieldInputs {p : ℕ} (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (hF : NK.LocalInputs.LocalFieldInputs K 𝔭 p)
    (D : NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) K') :
    NK.LocalTame.Zl2ResidueChar p (𝔭.adicCompletion K) K' := by
  obtain ⟨Φ⟩ := NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion D
  have hp_eq : ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) = p :=
    ringChar.eq_iff.mpr hchar
  refine ⟨hp, fun ℓ hℓ => ⟨fun hZ => ?_, fun hℓp => ?_⟩⟩
  · by_contra hne
    refine not_hasZl2Quotient_of_ne_resCharAt 𝔭 hℓ (fun hcon => hne ?_) hZ
    exact hcon.trans hp_eq
  · subst hℓp
    exact NK.Mine.hasZl2Quotient_of_hasZl2Quotient_completionUnits 𝔭 K' Φ
      ((NK.Mine.hasZl2Quotient_completionUnits_iff 𝔭 hp hp hchar hF).mpr rfl)

end

end NK.TameStructureDeep.Tame
