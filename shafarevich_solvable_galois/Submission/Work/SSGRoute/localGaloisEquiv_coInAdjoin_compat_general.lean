import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Work.SSGRoute.localGaloisEquiv_adjoin_coInAdjoin_compat

/-!
# `localGaloisEquiv` is the *extension* of `σ` to the completion: the `τ_σ` trap is void

`Work.SSGRoute.localGaloisEquiv_adjoin_coInAdjoin_compat` records, for `σ ∈ D_A = decomp k A` and
`x : K` (a finite Galois `K/k` inside `Ω`), that the automorphism of `κ^sep` attached to `σ` by
`NK.Mine.localGaloisEquiv` sends the image of `x` to the image of `σ|_K(x)`.

The present file records the **same statement for all `y : Ω`** — i.e. *without* restricting to the
finite level `K`:

    (localGaloisEquiv σ) (e (coInAdjoin y)) = e (coInAdjoin (σ y))      for all y : Ω,

where `e = NK.Mine.adjoinSepEquiv : κ·Ω ≃ₐ[κ] κ^sep`.

**Why this matters.**  `PT/NOTE_e1aChainC_localComparison.md` §11.3 records as its "second trap"
that `localField_subfield_place_compat`'s compatibility clause `hcompatΦ` is stated only on `K`, so
that `Φ(σ)|_Ω = σ τ_σ` for a cocycle `τ : D_A → Gal(Ω/K)`, which would make the coefficient change
`Ωˣ → Mˣ` fail to be a `D_A`-module map (the obstruction one would then have to remove by proving
`τ` inner).  **That trap is void**: `Φ = NK.Mine.localGaloisEquiv` is, by construction
(`NK.NeukirchUchida.decompositionToAdjoin` is built from
`Submission.NeukirchUchida.Local.completionRingEquiv`, i.e. from the *unique continuous extension*
of `σ` to the completion, which restricts to `σ` on the base field), compatible with the restriction
to `Ω` *everywhere*, and the proof below is the proof of
`localGaloisEquiv_adjoin_coInAdjoin_compat` with the last step (`x : K` ⟹ `σ` vs `σ|_K`) simply
deleted.  In particular `Φ(σ)|_Ω = σ`, so the coefficient change
`Hom_ℤ(R, Ωˣ) → Hom_ℤ(R, Mˣ)` *is* a `D_A`-module map (with the `D_A`-action on `Mˣ` transported
along `Φ`) and no `τ_σ` correction is needed in the comparison square.

Note also that the statement does not mention `K` at all: the finite level is irrelevant, only
`k`, `Ω`, `A` enter.
-/

namespace Work.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-- **`localGaloisEquiv` is the extension of `σ` to the completion, evaluated on all of `Ω`.**

For a finite place `A` of `Ω` over `k` and `σ` in the decomposition group `D_A`, the automorphism
attached to `σ` by `NK.Mine.localGaloisEquiv` sends the image in `κ^sep` of any `y : Ω` to the image
of `σ y`. -/
theorem localGaloisEquiv_coInAdjoin_compat_general (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) :=
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
    ∀ (σ : ↥(SSGRoute.decomp k A)) (y : Ω),
      (NK.Mine.localGaloisEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
          (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
            (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)) σ)
        (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
          (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A y)) =
      NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
        (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
          ((σ : Ω ≃ₐ[k] Ω) y)) := by
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
  intro σ y
  have hloc : (NK.Mine.adjoinLocalEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
        (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
          (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)) σ)
        (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A y)
      = NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
          ((σ : Ω ≃ₐ[k] Ω) y) :=
    (DFunLike.congr_fun
        (NK.Mine.adjoinLocalEquiv_apply (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
          (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
            (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)) σ)
        (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A y)).trans
      (NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)
        (fun z => rfl) σ y)
  calc
    (NK.Mine.localGaloisEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
        (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
          (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)) σ)
        (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
          (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A y))
      = AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω)
            (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)
            (fun z => rfl))
          (NK.Mine.adjoinLocalEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
            (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
            (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
              (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)) σ)
          (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
            (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
            (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A y)) :=
        rfl
    _ = NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
          ((NK.Mine.adjoinLocalEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
            (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
            (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
              (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)) σ)
            (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A y)) :=
        algEquiv_autCongr_apply_apply _ _ _
    _ = NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
          (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
            ((σ : Ω ≃ₐ[k] Ω) y)) :=
        congrArg (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)) hloc

end

end Work.SSGRoute
