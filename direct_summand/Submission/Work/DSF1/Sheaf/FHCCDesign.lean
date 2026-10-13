/-!
# Design notes for `Work.DSF1.Sheaf.flasque_hasCechCohomology`

Target (the file `Submission/Work/DSF1/Sheaf/flasque_hasCechCohomology.lean`):

```
theorem flasque_hasCechCohomology {X : AlgebraicGeometry.Scheme.{u}}
    (F : SheafOfModules X.ringCatSheaf)
    (hF : TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj) :
    Work.DSF1.Sheaf.HasCechCohomology F
```

i.e. for every finite family `U : ι → X.Opens` and every `p`, every Čech `(p+1)`-cocycle of
Mathlib's complex `cechComplex U F` is a coboundary.  This is Stacks 09SZ + 0A36 ("flasque
coefficients have vanishing higher Čech cohomology") in the *ordered* convention of
`CategoryTheory.cechComplexFunctor` (indexing tuples `Fin (n+1) → ι`, repetitions allowed).

## Architecture

Write `P := ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj` (the underlying presheaf of
abelian groups, a sheaf), `U : ι → X.Opens` finite, `V := ⨆ i, U i`, and

* `R := restrL P V`, the sheaf `W ↦ P (W ⊓ V) = P W` for `W ≤ V`;
* `A n := cechSheafTerm U P n`, the presheaf `W ↦ ∏_{x : Fin (n+1) → ι} P (W ⊓ ⋂_a U (x a))`
  (each `A n` is a sheaf: `isSheaf_pi` + `restrL_isSheaf`);
* `d n : A n ⟶ A (n+1)` the Čech differential (`cechSheafD`), with `d n ≫ d (n+1) = 0`
  (`cechSheafD_comp`);
* `aug : R ⟶ A 0`, the (componentwise) restriction, which is injective on every open `W ≤ V`
  because the family `W ⊓ U i` covers `W`.

Note `A n (V) = ∏_{x} P (⋂_a U (x a))` and `A n (⊤) = ∏_{x} P (⊤ ⊓ ⋂_a U (x a))`; these are the
degree-`n` terms of `cechComplex U F` (up to the identification `V ⊓ ⋂ = ⋂`, `⊤ ⊓ ⋂ = ⋂`).

The plan is then:

1. **Local exactness** (delegated: `DSF1/Sheaf/cechTrivAll_local`).  For `W ≤ U i₀` the complex
   `(cechComplexP U P).obj (op W)` (i.e. `A •` evaluated at `W`) is exact in positive degrees.
   This is the "insert `i₀` at position 0" contractibility (Stacks 0A36's local computation):
   since every `W ⊓ U i ≤ W = W ⊓ U i₀`, inserting `i₀` at position `0` gives a contracting
   homotopy *on the nose*.  The statement is already available for the complex
   `(cechComplexFunctor (fun i => W ⊓ U i)).obj P` as `Work.DSMX0bU.cechTrivAll_of_le_mem`
   (proved); the content of the delegated lemma is the (pointwise) identification of the two
   complexes.

2. **Dévissage** (delegated: `DSF1/Sheaf/cechTrivAt_of_flasque_terms`).  For a complex of
   *sheaves* `K` with `K n` flasque, an augmentation `F ⟶ K 0` injective on opens `W ≤ V`, and
   *local* triviality of cocycles (finite covers) on opens `W ≤ V`, conclude that on every
   `W ≤ V` every cocycle in `K (n+1) (W)` is a coboundary.  The proof is the standard flasque
   dévissage: with `Z q := ker (K q ⟶ K (q+1))`,
   * `Z 0 = 0` (injectivity of the augmentation), and if `Z q` is flasque on opens `≤ V` then
     so is `Z (q+1)`, because the previous degree's conclusion writes `Z (q+1) (W')` as
     `d (K q (W'))` and `K q` is flasque;
   * given a cocycle `x` of `K (n+1) (W)`, lift it on a finite cover `(W' i)` of `W`, glue the
     differences `y i - y j ∈ Z n (W' i ⊓ W' j)` using the flasqueness of `Z n` (splitting a
     1-cocycle with values in a flasque sheaf: the greedy argument along a well-order of the
     finite index set, using only surjectivity of restrictions and the sheaf condition), and
     glue the corrected `y i` on the cover.

3. **Assembly** (own work): `V := ⨆ U`, `R := restrL P V`, `K := cechSheafTerm U P •`,
   supply the hypotheses of 2. (flasqueness of the terms: a product of flasque presheaves is
   flasque and `restrL P T` is flasque for flasque `P`; injectivity of `aug` on `W ≤ V`: the
   family `W ⊓ U i` covers `W` and `P` is a sheaf; `hlocal`: from 1. with the cover
   `W ⊓ U i` of `W`), then transport the conclusion at `V` to the terms of `cechComplex U F`
   at `⊤`.
-/
