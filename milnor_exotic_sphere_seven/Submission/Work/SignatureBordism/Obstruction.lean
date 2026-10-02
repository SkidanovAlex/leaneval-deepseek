import Mathlib
import Submission.Work.SignatureBordism.Capped
import Submission.Work.SignatureBordism.Hirzebruch
import Submission.Work.SignatureBordism.Numbers
import Submission.Work.SignatureBordism.Bordism

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The endgame assembled: the three inputs and the contradiction

This file is the *consumable* form of the signature/bordism chapter for the exotic-`7`-sphere
project.  Let `X = D(ξ) ∪_F D⁸` be the closed oriented smooth `8`-manifold obtained from the disc
bundle `ξ = Vk (-2)` over `S⁴` by capping along a diffeomorphism `F : Mk (-2) ≃ S⁷`
(`Submission/Work/Milnor/CappedManifold.lean`).  The endgame of `Submission/NOTES.md` §14.8 needs
three inputs:

* **(i) Poincaré duality in the middle degree**, i.e. `H⁴(X;ℤ) = ℤ⟨x⟩` with `⟨x ⌣ x, [X]⟩ = ±1`,
  which is `Work.Cohomology.capped_cupSquare_generates` together with
  `Work.Milnor.capped_generator_pairings`.  Its consequence, **proved in this chapter**, is
  `Work.SignatureBordism.sigma_capped_eq_pm_one`: `σ(X) = ±1`.
* **(ii) the characteristic-class value** `p₁(X) = ±6 · x`, i.e. `⟨p₁(X)², [X]⟩ = 36 σ(X)`
  (the parallel subproject `Submission/Work/CharacteristicClasses/`).
* **(iii) the dimension-`8` Hirzebruch identity** `45 σ = 7 p₂ - p₁²` for `X`
  (`Work.SignatureBordism.HirzebruchEight`); see
  `Submission/Work/SignatureBordism/Hirzebruch.lean` for why the identity itself is not proved
  here.

Given (i)–(iii) the contradiction is `36 ≡ 1 ≢ 4 (mod 7)`: the identity forces
`p₁² ≡ 4 σ (mod 7)`, while (i) gives `σ = ±1` and (ii) gives `p₁² = 36 σ`, and
`36 σ ≢ 4 σ (mod 7)` because `36 - 4 = 32` is not divisible by `7`.

## Main results

* `Work.SignatureBordism.capped_hirzebruch_obstruction` — the contradiction from the identity in
  the form `HirzebruchEight σ (36 σ) p₂`, `σ = ±1`;
* `Work.SignatureBordism.capped_obstruction_of_p₁Sq` — the same from `p₁² = 36 σ` for a chosen
  class `p₁`, i.e. from the identity for the manifold;
* `Work.SignatureBordism.capped_obstruction_of_selfIntersection` — the same from the raw inputs
  `p₁ = ±6 · x` and `⟨x ⌣ x, [X]⟩ = ±1`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.SignatureBordism

open Work.Cohomology

noncomputable section

variable (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
variable (hF : Work.Milnor.IsCappingDiffeo F)

/-- **The endgame, from the identity and `σ(X) = ±1` and `p₁(X)² = 36 σ(X)`.**  If the capped
manifold's numbers satisfy the dimension-`8` Hirzebruch identity with `p₁² = 36 σ`, then `False`:
by `Work.SignatureBordism.sigma_capped_eq_pm_one` the signature is `±1`, and
`Work.SignatureBordism.hirzebruchEight_endgame_six` rules out `45 σ = 7 p₂ - 36 σ`. -/
theorem capped_hirzebruch_obstruction (c : (chainC ℤ (cappedSSet F hF)).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) (p₂ : ℤ)
    (h : HirzebruchEight (sigma 4 (cappedSSet F hF) c)
      (36 * sigma 4 (cappedSSet F hF) c) p₂) : False := by
  rcases sigma_capped_eq_pm_one F hF c hc with h1 | h1
  · exact hirzebruchEight_endgame_six 1 p₂ (Or.inl rfl) (by rw [h1] at h; simpa using h)
  · exact hirzebruchEight_endgame_six (-1) p₂ (Or.inr rfl) (by rw [h1] at h; simpa using h)

/-- **The endgame, from the identity for the manifold and the value of `p₁(X)²`.**  Inputs: a class
`p₁ ∈ H⁴(X;ℤ)` whose square-number is `36 σ(X)` (this is what the characteristic-class input
`p₁(X) = ±6 · x` together with `σ(X) = ±1` gives), a class `p₂ ∈ H⁸(X;ℤ)`, and the dimension-`8`
Hirzebruch identity `HirzebruchEightManifold`. -/
theorem capped_obstruction_of_p₁Sq (c : (chainC ℤ (cappedSSet F hF)).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) (p₁ : (cochainC ℤ (cappedSSet F hF)).homology 4)
    (p₂ : (cochainC ℤ (cappedSSet F hF)).homology 8)
    (hp : p₁SqNumber (cappedSSet F hF) c p₁ = 36 * sigma 4 (cappedSSet F hF) c)
    (h : HirzebruchEightManifold (cappedSSet F hF) c p₁ p₂) : False := by
  unfold HirzebruchEightManifold at h
  rw [hp] at h
  exact capped_hirzebruch_obstruction F hF c hc _ h

/-- **The endgame from the raw geometric inputs.**  Suppose `H⁴(X;ℤ) = ℤ⟨x⟩` with
`⟨x ⌣ x, [X]⟩ = m`, that `m = ±1` (Poincaré duality, `Work.Cohomology.capped_cupSquare_generates`
plus `Work.Milnor.capped_generator_pairings`), that `p₁(X) = q · x` with `q = ±6` (the
characteristic-class input) and that the dimension-`8` Hirzebruch identity holds for `X` with these
classes.  Then `False`. -/
theorem capped_obstruction_of_selfIntersection (c : (chainC ℤ (cappedSSet F hF)).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) (x p₁ : (cochainC ℤ (cappedSSet F hF)).homology 4)
    (p₂ : (cochainC ℤ (cappedSSet F hF)).homology 8)
    (hx : Submodule.span ℤ {x} = ⊤)
    {m q : ℤ} (hm : interForm ℤ (cappedSSet F hF) 4 4 c x x = m)
    (hm1 : m = 1 ∨ m = -1) (hp : p₁ = q • x) (hq : q = 6 ∨ q = -6)
    (h : HirzebruchEightManifold (cappedSSet F hF) c p₁ p₂) : False := by
  have hm0 : m ≠ 0 := by rcases hm1 with h | h <;> rw [h] <;> norm_num
  have hsig : sigma 4 (cappedSSet F hF) c = m := by
    have h2 := sigma_of_span_singleton 4 (cappedSSet F hF) c x hx hm hm0
    rcases hm1 with h1 | h1
    · rw [h1] at h2 ⊢; simpa using h2
    · rw [h1] at h2 ⊢; simpa using h2
  have hsq : p₁SqNumber (cappedSSet F hF) c p₁ = q ^ 2 * m :=
    p₁SqNumber_eq_sq (cappedSSet F hF) c x p₁ hp hm
  have hq2 : q ^ 2 = 36 := by rcases hq with h1 | h1 <;> rw [h1] <;> norm_num
  refine capped_obstruction_of_p₁Sq F hF c hc p₁ p₂ ?_ h
  rw [hsq, hsig, hq2]

/-! ## The endgame from the single named geometric hypothesis

The theorems below take the *only* remaining geometric input as a single hypothesis: that the
numbers of `X` lie in the rational span of the numbers of the two generators of `Ω^SO_8 ⊗ ℚ`
(`Work.SignatureBordism.NumbersInSpan8`, or the semantic form
`Work.SignatureBordism.BordismPresentation8`).  Everything else — `σ(X) = ±1`, the arithmetic of
`45σ = 7p₂ - p₁²`, and the generator checks on `ℂP⁴`, `ℂP² × ℂP²` — is discharged in this chapter.
-/

/-- **The arithmetic refutation of the generation hypothesis.**  There is no integer `p₂` for
which the triple `(±1, ±36, p₂)` — the numbers forced on the capped manifold by `σ(X) = ±1`
(`Work.SignatureBordism.sigma_capped_eq_pm_one`) and the characteristic-class input
`p₁(X)² = 36 σ(X)` — lies in the rational span of the two generator triples `(1,25,10)`,
`(1,18,9)`.

Indeed a span membership would give the Hirzebruch identity
(`Work.SignatureBordism.hirzebruchEight_of_mem_span`), which
`Work.SignatureBordism.hirzebruchEight_endgame_six` refutes.  This is the endgame in its purest
form: *generation of `Ω^SO_8 ⊗ ℚ` (the geometric input) is incompatible with the numbers of `X`*.
-/
theorem not_mem_span_of_unimodular (σ p₂ : ℤ) (hm : σ = 1 ∨ σ = -1)
    (h : ((σ : ℚ), ((36 * σ : ℤ) : ℚ), (p₂ : ℚ)) ∈ Submodule.span ℚ
      {cp4Tuple, cp2cp2Tuple}) : False :=
  hirzebruchEight_endgame_six σ p₂ hm (hirzebruchEight_of_mem_span σ (36 * σ) p₂ h)

/-- **The endgame from the single named bordism hypothesis.**  Hypotheses: `p₁(X)² = 36 σ(X)`
(the characteristic-class input `p₁(X) = ±6·x` together with `σ(X) = ±1`) and
`Work.SignatureBordism.NumbersInSpan8` for `X` — bordism invariance of the three numbers plus the
generation `Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}`.  Conclusion: `False`. -/
theorem capped_obstruction_of_numbersInSpan (c : (chainC ℤ (cappedSSet F hF)).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) (p₁ : (cochainC ℤ (cappedSSet F hF)).homology 4)
    (p₂ : (cochainC ℤ (cappedSSet F hF)).homology 8)
    (hp : p₁SqNumber (cappedSSet F hF) c p₁ = 36 * sigma 4 (cappedSSet F hF) c)
    (h : NumbersInSpan8 (cappedSSet F hF) c p₁ p₂) : False :=
  capped_obstruction_of_p₁Sq F hF c hc p₁ p₂ hp
    (HirzebruchEightManifold_of_numbersInSpan _ _ _ _ h)

/-- **The dimension-`8` Hirzebruch congruence for `X = D(ξ) ∪_F D⁸`, from the single named bordism
hypothesis**: `⟨p₁ ⌣ p₁, [X]⟩ ≡ 4 σ(X) (mod 7)`.

This is input `(iii)` of `Submission/NOTES.md` §14.8 for the manifold `X`, with all of its
arithmetic discharged and the only remaining input the named geometric hypothesis
`Work.SignatureBordism.NumbersInSpan8`. -/
theorem capped_congruence_of_numbersInSpan (c : (chainC ℤ (cappedSSet F hF)).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) (p₁ : (cochainC ℤ (cappedSSet F hF)).homology 4)
    (p₂ : (cochainC ℤ (cappedSSet F hF)).homology 8)
    (h : NumbersInSpan8 (cappedSSet F hF) c p₁ p₂) :
    p₁SqNumber (cappedSSet F hF) c p₁ ≡ 4 * sigma 4 (cappedSSet F hF) c [ZMOD 7] :=
  hirzebruchEightManifold_congruence _ _ _ _
    (HirzebruchEightManifold_of_numbersInSpan _ _ _ _ h)

/-- **The endgame from a bordism presentation.**  The same as
`Work.SignatureBordism.capped_obstruction_of_numbersInSpan`, with the geometric input given in its
semantic form: a rational model of `Ω^SO_8 ⊗ ℚ` in which the three numbers are `ℚ`-linear
functionals, spanned by the classes of `ℂP⁴` and `ℂP² × ℂP²` with their numbers `(1,25,10)`,
`(1,18,9)`, together with a class carrying the numbers of `X`. -/
theorem capped_obstruction_of_presentation (c : (chainC ℤ (cappedSSet F hF)).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) (p₁ : (cochainC ℤ (cappedSSet F hF)).homology 4)
    (p₂ : (cochainC ℤ (cappedSSet F hF)).homology 8)
    (hp : p₁SqNumber (cappedSSet F hF) c p₁ = 36 * sigma 4 (cappedSSet F hF) c)
    (P : BordismPresentation8 (sigma 4 (cappedSSet F hF) c)
      (p₁SqNumber (cappedSSet F hF) c p₁) (p₂Number (cappedSSet F hF) c p₂)) : False :=
  capped_obstruction_of_p₁Sq F hF c hc p₁ p₂ hp (HirzebruchEight.of_presentation P)

/-- **The endgame from the raw geometric inputs and the single named bordism hypothesis.**  The
hypotheses are exactly those of `Submission/NOTES.md` §14.8: `H⁴(X;ℤ) = ℤ⟨x⟩` with
`⟨x ⌣ x, c⟩ = m = ±1` (Poincaré duality), `p₁(X) = ±6 · x` (the characteristic-class input) and the
bordism input `Work.SignatureBordism.NumbersInSpan8`; the conclusion is `False`. -/
theorem capped_obstruction_of_selfIntersection_of_numbersInSpan
    (c : (chainC ℤ (cappedSSet F hF)).homology 8) (hc : Submodule.span ℤ {c} = ⊤)
    (x p₁ : (cochainC ℤ (cappedSSet F hF)).homology 4)
    (p₂ : (cochainC ℤ (cappedSSet F hF)).homology 8)
    (hx : Submodule.span ℤ {x} = ⊤)
    {m q : ℤ} (hm : interForm ℤ (cappedSSet F hF) 4 4 c x x = m)
    (hm1 : m = 1 ∨ m = -1) (hp : p₁ = q • x) (hq : q = 6 ∨ q = -6)
    (h : NumbersInSpan8 (cappedSSet F hF) c p₁ p₂) : False :=
  capped_obstruction_of_selfIntersection F hF c hc x p₁ p₂ hx hm hm1 hp hq
    (HirzebruchEightManifold_of_numbersInSpan _ _ _ _ h)

/-- **The generic dimension-`8` obstruction.**  Let `X` be a closed oriented smooth `8`-manifold
(presented as a simplicial set with a fundamental class `c ∈ H₈(X;ℤ)`), let `x ∈ H⁴(X;ℤ)` generate
`H⁴(X;ℤ)` with `⟨x ⌣ x, c⟩ = m = ±1` (Poincaré duality in the middle degree — this, together with
the degrees, is the only property of `X` used), let `p₁ ∈ H⁴(X;ℤ)` be `±6 · x` (the
characteristic-class input) and suppose the numbers of `X` admit the bordism presentation
`Work.SignatureBordism.NumbersInSpan8`.  Then `False`.

Nothing here is special to `X = D(ξ) ∪_F D⁸`: *any* closed oriented smooth `8`-manifold with these
properties is obstructed, and the only remaining geometric input is the named bordism hypothesis.
The proof is the arithmetic of the endgame: `σ(X) = m = ±1`
(`Work.SignatureBordism.sigma_eq_of_span_singleton_of_unimodular`), hence `p₁(X)² = 36 σ(X)`
(`Work.SignatureBordism.p₁SqNumber_eq_sq`), and generation is incompatible with the numbers
`(±1, ±36, p₂)` (`Work.SignatureBordism.not_mem_span_of_unimodular`). -/
theorem obstruction_of_generation (X : SSet) (c : (chainC ℤ X).homology 8)
    (x p₁ : (cochainC ℤ X).homology 4) (p₂ : (cochainC ℤ X).homology 8)
    (hx : Submodule.span ℤ {x} = ⊤)
    {m q : ℤ} (hm : interForm ℤ X 4 4 c x x = m) (hm1 : m = 1 ∨ m = -1)
    (hp : p₁ = q • x) (hq : q = 6 ∨ q = -6)
    (h : NumbersInSpan8 X c p₁ p₂) : False := by
  have hsig : sigma 4 X c = m := sigma_eq_of_span_singleton_of_unimodular 4 X c x hx hm hm1
  have hsq : p₁SqNumber X c p₁ = 36 * sigma 4 X c := by
    rw [p₁SqNumber_eq_sq X c x p₁ hp hm, hsig]
    rcases hq with h1 | h1 <;> rw [h1] <;> rcases hm1 with h2 | h2 <;> rw [h2] <;> norm_num
  unfold NumbersInSpan8 at h
  rw [hsq] at h
  rcases hm1 with h1 | h1
  · exact not_mem_span_of_unimodular (sigma 4 X c) (p₂Number X c p₂)
      (Or.inl (by rw [hsig, h1])) h
  · exact not_mem_span_of_unimodular (sigma 4 X c) (p₂Number X c p₂)
      (Or.inr (by rw [hsig, h1])) h

end

end Work.SignatureBordism
