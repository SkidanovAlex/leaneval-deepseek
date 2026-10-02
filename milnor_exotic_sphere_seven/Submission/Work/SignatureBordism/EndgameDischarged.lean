import Mathlib
import Submission.Work.SignatureBordism.Obstruction
import Submission.Work.CharacteristicClasses.Capped
import Submission.Work.CharacteristicClasses.Milnor

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The endgame with the characteristic-class input *discharged*

This module is the integration point with the parallel subproject
`Submission/Work/CharacteristicClasses/`, which has landed the first Pontryagin class of `TX` as a
class `Work.Milnor.cappedPontryaginClass F hF ∈ H⁴(X;ℤ)` for the capped manifold
`X = D(ξ) ∪_F D⁸`, the coefficient statement
`Work.Milnor.cappedPontryaginClass_eq_pm_smul` (`p₁(TX) = ±p₁(ξ)·x` for every generator `x` of
`H⁴(X;ℤ)`) and the value `Work.Milnor.p1_xi` (`p₁(ξ) = 6`).

Consequently input **(ii)** of `Submission/NOTES.md` §14.8 is no longer a hypothesis at the endgame:

* `Work.SignatureBordism.capped_p₁SqNumber_eq_thirtysix_sigma` :
  **`⟨p₁(TX) ⌣ p₁(TX), [X]⟩ = 36 σ(X)`** is a theorem;
* `Work.SignatureBordism.capped_obstruction_of_generation` :
  `False` from a fundamental class of `X` and **one** hypothesis — `NumbersInSpan8` for the
  *concrete* class `cappedPontryaginClass F hF`, i.e. bordism invariance of the three numbers plus
  the generation `Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}`.

This file is deliberately *not* part of `Submission.Work.SignatureBordism.Chapter`: the rest of the
chapter is self-contained, whereas this module depends on a subproject that is still in flight.
Import it explicitly when the characteristic-class chapter is available.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.SignatureBordism

open Work.Cohomology

noncomputable section

variable (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
variable (hF : Work.Milnor.IsCappingDiffeo F)

/-- The `p₁²`-number of `p₁(TX)` is `36 σ(X)`: the characteristic-class input in the numerical form
used by the endgame.  By `Work.Milnor.cappedPontryaginClass_six` the class `p₁(TX)` is `q · x` with
`q ∈ {6,-6}` for any generator `x` of `H⁴(X;ℤ)`; with `⟨x ⌣ x, [X]⟩ = ±1`
(`Work.SignatureBordism.capped_selfIntersection_eq_pm_one`) and `σ(X) = ⟨x ⌣ x, [X]⟩`
(`Work.SignatureBordism.sigma_eq_of_span_singleton_of_unimodular`) this is
`q² · m = 36 σ(X)`. -/
theorem capped_p₁SqNumber_eq_thirtysix_sigma
    (c : (chainC ℤ (cappedSSet F hF)).homology 8) (hc : Submodule.span ℤ {c} = ⊤) :
    p₁SqNumber (cappedSSet F hF) c (Work.Milnor.cappedPontryaginClass F hF)
      = 36 * sigma 4 (cappedSSet F hF) c := by
  obtain ⟨x, hx, hxcup⟩ := capped_cupSquare_generates F hF
  have hx' : Submodule.span ℤ {x} = ⊤ := (span_singleton_eq_top_iff x).mpr hx
  obtain ⟨q, hq, hp⟩ := Work.Milnor.cappedPontryaginClass_six F hF x hx
  rcases capped_selfIntersection_eq_pm_one F hF x hx' hxcup c hc with hm | hm
  · have hsig : sigma 4 (cappedSSet F hF) c = 1 :=
      sigma_eq_of_span_singleton_of_unimodular 4 (cappedSSet F hF) c x hx' hm (Or.inl rfl)
    rw [p₁SqNumber_eq_sq (cappedSSet F hF) c x _ hp hm, hsig]
    rcases hq with h | h <;> rw [h] <;> norm_num
  · have hsig : sigma 4 (cappedSSet F hF) c = -1 :=
      sigma_eq_of_span_singleton_of_unimodular 4 (cappedSSet F hF) c x hx' hm (Or.inr rfl)
    rw [p₁SqNumber_eq_sq (cappedSSet F hF) c x _ hp hm, hsig]
    rcases hq with h | h <;> rw [h] <;> norm_num

/-- **The endgame with the characteristic-class input discharged: `False` from the named bordism
hypothesis alone.**  Hypotheses: a fundamental class `c` of `X = D(ξ) ∪_F D⁸`, a class `p₂`, and
`Work.SignatureBordism.NumbersInSpan8` for the *concrete* first Pontryagin class
`Work.Milnor.cappedPontryaginClass F hF`.  Everything else is a theorem of this workspace:
`σ(X) = ±1` (`sigma_capped_eq_pm_one`), `⟨x ⌣ x, c⟩ = ±1` (`capped_selfIntersection_eq_pm_one`),
and `p₁(TX) = ±6·x` with `p₁(TX)² = 36 σ(X)` (`Work.Milnor.cappedPontryaginClass_eq_pm_smul`,
`Work.Milnor.p1_xi`, `capped_p₁SqNumber_eq_thirtysix_sigma`). -/
theorem capped_obstruction_of_generation (c : (chainC ℤ (cappedSSet F hF)).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) (p₂ : (cochainC ℤ (cappedSSet F hF)).homology 8)
    (h : NumbersInSpan8 (cappedSSet F hF) c (Work.Milnor.cappedPontryaginClass F hF) p₂) : False :=
  capped_obstruction_of_numbersInSpan F hF c hc (Work.Milnor.cappedPontryaginClass F hF) p₂
    (capped_p₁SqNumber_eq_thirtysix_sigma F hF c hc) h

/-- **The endgame, existentially in the fundamental class**: from the named bordism hypothesis for
*some* fundamental class of `X` and the concrete class `p₁(TX)`, `False`. -/
theorem exists_capped_obstruction_of_generation (p₂ : (cochainC ℤ (cappedSSet F hF)).homology 8)
    (h : ∃ c : (chainC ℤ (cappedSSet F hF)).homology 8, Submodule.span ℤ {c} = ⊤ ∧
      NumbersInSpan8 (cappedSSet F hF) c (Work.Milnor.cappedPontryaginClass F hF) p₂) : False := by
  obtain ⟨c, hc, hgen⟩ := h
  exact capped_obstruction_of_generation F hF c hc p₂ hgen

/-- **Generation fails for the capped manifold.**  For every fundamental class `c` of
`X = D(ξ) ∪_F D⁸` and every class `p₂`, the triple of numbers `(σ(X), p₁(TX)², p₂(X))` does **not**
lie in the rational span of the numbers of `ℂP⁴` and `ℂP² × ℂP²`.

Indeed the span condition is equivalent to the Hirzebruch identity
(`Work.SignatureBordism.mem_span_iff_hirzebruchEight`), which with `σ(X) = ±1`
(`Work.SignatureBordism.sigma_capped_eq_pm_one`) and `p₁(TX)² = 36 σ(X)`
(`Work.SignatureBordism.capped_p₁SqNumber_eq_thirtysix_sigma`) would force `81 σ(X) = 7 p₂(X)` — an
impossibility in `ℤ`.

This is the sharpest statement of the endgame: *the geometric input (generation of `Ω^SO_8 ⊗ ℚ`) and
the existence of the capped manifold are incompatible*, which is exactly why a proof of generation
would finish the project (`Work.SignatureBordism.capped_obstruction_of_generation` is the same
statement in the direction used at the assembly). -/
theorem not_numbersInSpan_capped (c : (chainC ℤ (cappedSSet F hF)).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) (p₂ : (cochainC ℤ (cappedSSet F hF)).homology 8) :
    ¬ NumbersInSpan8 (cappedSSet F hF) c (Work.Milnor.cappedPontryaginClass F hF) p₂ := by
  intro h
  have hsq := capped_p₁SqNumber_eq_thirtysix_sigma F hF c hc
  obtain ⟨x, hx, hxcup⟩ := capped_cupSquare_generates F hF
  have hx' : Submodule.span ℤ {x} = ⊤ := (span_singleton_eq_top_iff x).mpr hx
  unfold NumbersInSpan8 at h
  rw [hsq] at h
  rcases capped_selfIntersection_eq_pm_one F hF x hx' hxcup c hc with hm | hm
  · have hsig : sigma 4 (cappedSSet F hF) c = 1 :=
      sigma_eq_of_span_singleton_of_unimodular 4 (cappedSSet F hF) c x hx' hm (Or.inl rfl)
    rw [hsig] at h
    have hH : HirzebruchEight 1 (36 * 1) (p₂Number (cappedSSet F hF) c p₂) :=
      (mem_span_iff_hirzebruchEight 1 (36 * 1) (p₂Number (cappedSSet F hF) c p₂)).mp h
    unfold HirzebruchEight at hH
    omega
  · have hsig : sigma 4 (cappedSSet F hF) c = -1 :=
      sigma_eq_of_span_singleton_of_unimodular 4 (cappedSSet F hF) c x hx' hm (Or.inr rfl)
    rw [hsig] at h
    have hH : HirzebruchEight (-1) (36 * -1) (p₂Number (cappedSSet F hF) c p₂) :=
      (mem_span_iff_hirzebruchEight (-1) (36 * -1) (p₂Number (cappedSSet F hF) c p₂)).mp h
    unfold HirzebruchEight at hH
    omega

/-- **The endgame cannot be closed from pointwise data about `X`.**  For every fundamental class `c`
and every class `p₂`, the named hypothesis `NumbersInSpan8` for the concrete first Pontryagin class
of `X` is *equivalent to* `False`.

Consequently `Work.SignatureBordism.capped_obstruction_of_generation` can only be instanced from a
**general** theorem giving the span membership for all closed oriented smooth `8`-manifolds — the
hard core of `Submission/NOTES.md` §8.4: bordism invariance of `σ`, `p₁²`, `p₂` together with the
generation `Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}`.  (Inside the hypothetical `IsCappingDiffeo F`
both that general theorem and this refutation hold, and their conjunction is exactly
`Work.Milnor.no_cappingDiffeo`.) -/
theorem numbersInSpan_capped_iff_false (c : (chainC ℤ (cappedSSet F hF)).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) (p₂ : (cochainC ℤ (cappedSSet F hF)).homology 8) :
    NumbersInSpan8 (cappedSSet F hF) c (Work.Milnor.cappedPontryaginClass F hF) p₂ ↔ False :=
  ⟨not_numbersInSpan_capped F hF c hc p₂, False.elim⟩

end

end Work.SignatureBordism
