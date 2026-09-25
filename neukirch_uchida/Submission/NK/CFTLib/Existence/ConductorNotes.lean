/-!
# Notes for `NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles`

This file has no content.  It records how to prove

`isUnramified_of_normClassSubgroup_le_integralIdeles`:

for a number field `K` (with **no** assumption that `K` contains a primitive `p`-th root of unity),
a finite Galois extension `L / K` of degree `p` (`p` prime) whose norm class subgroup contains the
image of the integral idèles is unramified at every finite place and at every infinite place.

This is the existing theorem
`NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles_kummer`, whose
hypothesis `{ζ : K} (hζ : IsPrimitiveRoot ζ p)` is **never used**: in that file the only occurrence
of `hζ` is as an argument to
`NK.CFTLib.Existence.localUnits_le_range_localNorm_of_integralIdeles`, and in *that* lemma the
argument `hζ` does not occur in the proof either (the proof only uses `hgap`, `hray`, `hdeg`, and
`localNormUnits_of_fiber_prod` / the archimedean norm computations).  So it suffices to repeat the
two proofs with the `hζ` argument dropped.

## What to do

1. **Reproduce the local extraction without `hζ`.**  Copy
   `NK.CFTLib.Existence.localUnits_le_range_localNorm_of_integralIdeles` (its statement and its
   proof) into your file as a private/auxiliary lemma with the `(p : ℕ) [Fact p.Prime] {ζ : K}
   (hζ : IsPrimitiveRoot ζ p)` arguments deleted (keep `hdeg` and `hray`, and keep `hgap` as the
   explicit hypothesis it is there).  The proof is literally that of the existing lemma with `hζ`
   never mentioned; all the auxiliary lemmas it calls
   (`exists_principalIdele_mul_mem_normImage_of_mem_integralIdeles`,
   `mem_normImage_of_eq_one_off`, `localNormUnits_of_fiber_prod`,
   `NormIndex.localNormInfinite_range_eq_top_of_real_real`,
   `NormIndex.localNormInfinite_range_eq_top_of_complex_complex`,
   `false_of_isReal_of_isComplex`) can be imported from that same file — hence the dependency on
   `Submission.NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles_kummer`.

2. **Reproduce the finite-place conclusion.**  Copy the proof of
   `isUnramified_of_normClassSubgroup_le_integralIdeles_kummer` itself, again with `hζ` deleted:
   * `hcyc : IsCyclic (L ≃ₐ[K] L)` from `isCyclic_of_prime_card` and
     `IsGalois.card_aut_eq_finrank`;
   * the two named conclusions of step 1 (finite and infinite places);
   * the finite places via `NK.CFTLib.Existence.differentIdeal_eq_top_of_ramificationIdx_heightOne`
     (which lives in the same file) together with
     `NK.CFTLib.Existence.ramificationIdx_eq_one_of_localUnits_le_localNorm`;
   * the infinite places by the same case distinction `isReal_or_isComplex` on `v` and `w` and the
     `NormIndex.localNormInfinite_range_eq_top_of_*` lemmas, with
     `false_of_isReal_of_isComplex` for the mixed real/complex case.

## Warning: import clash (do not trip over it)

The modules `Submission.NK.CFTLib.unramifiedAbelianDegreeLe` and
`Submission.NK.CFTLib.integralIdelesLeNormImage` **both define the name**
`NK.CFTLib.ramificationIdx_eq_one_of_differentIdeal_eq_top`, so no file may import both.
Importing `Submission.NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles_kummer`
transitively imports `unramifiedAbelianDegreeLe`.  Therefore: do **not** import
`Submission.NK.CFTLib.integralIdelesLeNormImage` nor
`Submission.NK.CFTLib.Existence.differentIdeal_eq_top_of_intermediateField_of_prime_finrank`
(which imports it) in your file, and do not use anything from them.  The statement above needs
neither.
-/

namespace NK.CFTLib.Existence

end NK.CFTLib.Existence
