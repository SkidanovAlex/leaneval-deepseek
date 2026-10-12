import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.DvApriori

theorem fsT_congr_of_Qfree_eq {ℓ d s εT b : ℝ} {ψ ψ' : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.BoseKinLoc.Qfree ℓ 0 ψ = Work.BoseKinLoc.Qfree ℓ 0 ψ') :
    Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ = Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ' := by
  simp only [Work.BoseKinLoc.Qfree] at h
  simp only [Work.BoseKinLoc.fsT, Work.BoseKinLoc.neuWord, Work.BoseKinLoc.gapWord,
    Work.BoseKinLoc.gapBare, Work.BoseKinLoc.momWord, Work.BoseKinLoc.momForm,
    Work.BoseKinLoc.mainWord, Work.BoseKinLoc.Qfree, Work.BSKinetic.bsOneBody, h]

/-- **The general-`u` congruence** underlying `fsT_congr_of_Qfree_eq`, recorded because the
same argument applies at every translation parameter `u` (the moving-box family of FS
`lem:LocKinEn`): `fsT ℓ d s εT b u` reads its one-body state only through `Qfree ℓ u`.

Each of the four defining pieces of `fsT` (`neuWord`, `gapWord`, `momWord`, `mainWord` —
resp. `neuFrac`, `gapBare`, `momForm`, `bsOneBody`) has `Qfree ℓ u ψ` as its only state
argument, so unfolding the definitions exhibits the two sides as syntactically identical
terms in `bsQ ℓ u ψ` resp. `bsQ ℓ u ψ'` (and `Qfree ℓ u ψ` unfolds to `bsQ ℓ u ψ`);

* `neuWord ℓ d εT u ψ = ½ε_T(dℓ)⁻² · neuFrac ℓ ((dℓ)⁻²) u (Qfree ℓ u ψ)`;
* `gapWord ℓ b u ψ = bℓ⁻² · ∫_{Λ(u)} (Qfree ℓ u ψ)²`;
* `momWord ℓ d εT b u ψ = bε_T(dℓ)⁻² · momForm ℓ d u ψ`, and `momForm` only uses
  `Qfree ℓ u ψ` (through `kinFT`);
* `mainWord ℓ d s εT u ψ = (1−ε_T)·bsOneBody ℓ F₁ u ψ + ε_T·bsOneBody ℓ F₂ u ψ`, and
  `bsOneBody` only uses `bsQ ℓ u ψ`.

This is the interface lemma that lets a consumer replace a fibre state by another state with
the same box mean-free part when computing the slot words of FS `eq:Def_HB`. -/
theorem fsT_congr_of_Qfree_eq' {ℓ d s εT b : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {ψ ψ' : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.BoseKinLoc.Qfree ℓ u ψ = Work.BoseKinLoc.Qfree ℓ u ψ') :
    Work.BoseKinLoc.fsT ℓ d s εT b u ψ = Work.BoseKinLoc.fsT ℓ d s εT b u ψ' := by
  simp only [Work.BoseKinLoc.Qfree] at h
  simp only [Work.BoseKinLoc.fsT, Work.BoseKinLoc.neuWord, Work.BoseKinLoc.gapWord,
    Work.BoseKinLoc.gapBare, Work.BoseKinLoc.momWord, Work.BoseKinLoc.momForm,
    Work.BoseKinLoc.mainWord, Work.BoseKinLoc.Qfree, Work.BSKinetic.bsOneBody, h]

end Work.BoseFixB2.DvApriori
