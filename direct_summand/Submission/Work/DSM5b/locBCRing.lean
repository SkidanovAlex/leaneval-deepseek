import Mathlib
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSM5b.honestKillFlat
import Submission.Work.DSM5b.chartRingBaseChange

/-!
# `Work.DSM5b.locBCRing` — the base-change map of the chart **rings** (step 2)

`Work.DSM5b.locBC` is a map of localisations `R₀_{t_S} → R_{t_S}`.  Restricting it to the chart rings
needs the base-change identification `Work.DSM5b.chartRingBaseChange`
(`x ∈ chartRing (algebraMap ∘ t) S ↔ x ∈ Submodule.span R ((chartRing t S).map locBC : Set _)`,
which is *proved and axiom-clean*).  This file provides the restriction

    locBCRing : chartRing t S →ₐ[R₀] chartRing (algebraMap ∘ t) S

and the fact that it commutes with the restriction maps `rhoH` (which is the chart-ring-level form of
step 2: "the differential `HCd` of the base-changed complex is the base change of `HCd`", since `HCd`
is built out of `rhoH` and the scalars `(-1)^i`).

This file cannot live inside `honestKillFlat.lean`: the proved `chartRingBaseChange` imports that
file, so importing it back there would be cyclic.

## What remains for step 2

Read off componentwise that the differential is the base change of the differential: for
## Step 2 is COMPLETE

The differential statement is **proved and axiom-clean** by `Work.DSM5b.hCdBaseChange`
(`hCdBaseChange.lean`, axioms `[propext, Classical.choice, Quot.sound]`):

    HCd (algebraMap ∘ t) m (HCXb (R := R) t m z) = HCXb (R := R) t (m + 1) (HCd t m z)

i.e. the differential of the base-changed complex is the base change of the differential.  (The one
real obligation, as the reviewers identified, was the scalar consistency
`algebraMap R₀ R ((-1 : R₀) ^ i) = (-1 : R) ^ i`, proved in `honestKillFlat.lean` as
`algebraMap_neg_one_pow`.)

## What remains (step 3, flat descent of the killing)

* `hcxbSpanTop` (in flight): for `[Finite ι]`, `⊤ = Submodule.span R (Set.range (HCXb t m))` — the
  base change *sees* every cochain.  (Note: this needs `[Finite ι]`; for infinite `ι` it is FALSE —
  the reviewers' counterexample `R₀ = ℚ`, `R = ℚ[y]`, `ι = ℕ`, `t ≡ 1`, cochain `σ ↦ y^{σ 0}` —
  which is why the hypothesis is there.)
* the flatness bookkeeping: for flat `R₀ → R`, `ker (d ⊗ R) = ker d ⊗ R` and
  `range (d ⊗ R) = range d ⊗ R`, so uniform honest killing over `R₀` implies it over `R`.
* application: for `R₀ = 𝔽_p[T, t_i]` a polynomial ring, `R₀ → R₀^{perf}` is flat (`R₀ → R₀^{1/p}`
  is free, then a filtered colimit of flat modules), so `honestKillCoordNoeth` for `R₀` gives
  `honestKillCoord` for `R = R₀^{perf}`.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

section RingBaseChange

variable {R₀ : Type a} [CommRing R₀] {R : Type a} [CommRing R] [Algebra R₀ R]
variable {ι : Type a} [DecidableEq ι]

/-- **The base-change map of the chart rings**: `locBC` restricted to `chartRing t S`, using the
proved `chartRingBaseChange` for the codomain. -/
noncomputable def locBCRing (t : ι → R₀) (S : Finset ι) :
    chartRing t S →ₐ[R₀] chartRing (fun i => algebraMap R₀ R (t i)) S where
  toFun y := ⟨locBC t S y.1,
    (chartRingBaseChange (R := R) t S (locBC t S y.1)).mpr
      (Submodule.subset_span ⟨y.1, y.2, rfl⟩)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' y z := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' y z := by apply Subtype.ext; simp
  commutes' r := by apply Subtype.ext; simp

@[simp] lemma locBCRing_coe (t : ι → R₀) (S : Finset ι) (y : chartRing t S) :
    ((locBCRing (R := R) t S y : chartRing (fun i => algebraMap R₀ R (t i)) S) :
      Localization.Away (tS (fun i => algebraMap R₀ R (t i)) S)) = locBC t S y.1 := rfl

/-- `locBCRing` commutes with the restriction maps `rhoH`: the chart-level square of step 2. -/
lemma locBCRing_rhoH (t : ι → R₀) {S T : Finset ι} (h : S ⊆ T) (y : chartRing t S) :
    locBCRing (R := R) t T (rhoH t h y)
      = rhoH (fun i => algebraMap R₀ R (t i)) h (locBCRing (R := R) t S y) := by
  apply Subtype.ext
  simp only [locBCRing_coe, rhoH_coe]
  exact locBC_comp_locRes_apply t h y.1

/-- **The base-change map of the terms of the honest complex**: a cochain over `R₀` becomes a
cochain over `R` by applying `locBCRing` componentwise. -/
noncomputable def HCXb (t : ι → R₀) (m : ℕ) :
    HCX t m →ₗ[R₀] HCX (fun i => algebraMap R₀ R (t i)) m where
  toFun z := fun σ => locBCRing (R := R) t (tupRng σ) (z σ)
  map_add' z z' := by funext σ; simp
  map_smul' r z := by funext σ; simp

@[simp] lemma HCXb_apply (t : ι → R₀) (m : ℕ) (z : HCX t m) (σ : Fin (m + 1) → ι) :
    HCXb (R := R) t m z σ = locBCRing (R := R) t (tupRng σ) (z σ) := rfl

end RingBaseChange

end Work.DSM5b
