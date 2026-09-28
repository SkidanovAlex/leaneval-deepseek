import Mathlib
import Submission.Work.Serre.crossProduct_defs
import Submission.Work.Serre.crossProduct_coker_rat
import Submission.Work.Serre.tpC_homologyMap_cokernel_subsingleton
import Submission.Work.Serre.tensorRat_subsingleton_of_subsingleton
import Submission.Work.Kunneth.Chapter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The rationalisation of the cokernel of the cross product with a generator

For a cycle `z` of a chain complex `D` of `ℤ`-modules whose rational homology vanishes in degrees
`≤ N+1` except in degree `r+1`, where it is generated (up to torsion) by the class of `z`
(hypotheses `hvan`, `hgen`), the map

`H_n (tpMap C C ℤ[r+1] D 𝟙 (dzMap r D z)) : H_n (tpC C ℤ[r+1]) ⟶ H_n (tpC C D)`

-- i.e. the cross product with `z` -- has a cokernel which is a torsion group for every `n ≤ N+1`.

## Proof

The coefficient complex `ℤ[r+1]` (`Work.Serre.dzComplex r`) is concentrated in degree `r+1`, where
the map `Work.Serre.dzMap r D z` sends the generator to `z`.

* If the class of `z` survives rationalisation (`[z] ⊗ 1 ≠ 0`), then `dzMap r D z` is a monomorphism
  (`Work.Serre.mono_dzMap`, using `Work.Serre.z_chain_not_torsion`), and the rational homology of
  the quotient complex `D ⧸ ℤz` vanishes in degrees `≤ N+1`
  (`Work.Serre.coker_dzMap_homology_rat_subsingleton`, the analytic heart of the argument: a cycle of
  the quotient lifts to `D` where its boundary is a multiple of `z`, and the generating hypothesis
  plus the non-torsion of `[z]` kill it).  Hence, by the acyclicity lemma
  `Work.Serre.tensorRat_subsingleton_of_subsingleton` applied in the second variable, the rational
  homology of `tpC C (D ⧸ ℤz)` vanishes in degrees `≤ N+1`, and the degreewise short exact sequence
  `0 → tpC C ℤ[r+1] → tpC C D → tpC C (D ⧸ ℤz) → 0` (right exactness of `tpC C -` on rational
  homology, `Work.Serre.tpC_homologyMap_cokernel_subsingleton`) produces the long exact sequence
  whose cokernel term embeds into `H_•(tpC C (D ⧸ ℤz))`.
* If instead `[z] ⊗ 1 = 0`, the generating hypothesis forces the whole rational homology of `D` in
  degrees `≤ N+1` to vanish (`Work.Serre.subsingleton_homology_rat_of_hgen`), hence so does that of
  `tpC C D` (`Work.Serre.tensorRat_subsingleton_of_subsingleton`); the cokernel of our map is a
  quotient of `H_n(tpC C D)` and rationalisation is right exact
  (`Work.Serre.subsingleton_tensorRat_of_surjective`).
-/

namespace Work.Serre.Surj

theorem tpMapDzCokerTorsion (C D : ChainComplex (ModuleCat ℤ) ℕ) (hC : ∀ i, Module.Free ℤ ↥(C.X i)) (r N : ℕ) (z : ↥(D.cycles (r + 1))) (hznt : ∀ k : ℤ, (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) ((D.iCycles (r + 1)) z)) k = 0 → k = 0) (hvan : ∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 → Subsingleton (TensorProduct ℤ ↥(D.homology j) ℚ)) (hgen : ∀ w : ↥(D.homology (r + 1)), ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, TensorProduct.tmul ℤ (n • w) (1 : ℚ) = TensorProduct.tmul ℤ (m • ((D.homologyπ (r + 1)).hom z)) (1 : ℚ)) : ∀ n : ℕ, n ≤ N + 1 → Subsingleton (TensorProduct ℤ ↥(CategoryTheory.Limits.cokernel (HomologicalComplex.homologyMap (Work.Kunneth.tpMap C C (Work.Serre.dzComplex r) D (CategoryTheory.CategoryStruct.id C) (Work.Serre.dzMap r D z)) n)) ℚ) := by
  intro n hn
  by_cases hzt : TensorProduct.tmul ℤ ((D.homologyπ (r + 1)).hom z) (1 : ℚ) = 0
  · -- The class of `z` dies after rationalisation, so `H_n (tpC C D)` is rationally trivial and the
    -- cokernel of our map, being a quotient of it, is rationally trivial as well.
    have hD := Work.Serre.subsingleton_homology_rat_of_hgen D r N z hvan hgen hzt
    have htp := Work.Serre.tensorRat_subsingleton_of_subsingleton C D (N + 1) hC hD n hn
    exact Work.Serre.subsingleton_tensorRat_of_surjective
      (CategoryTheory.Limits.cokernel.π (HomologicalComplex.homologyMap
        (Work.Kunneth.tpMap C C (Work.Serre.dzComplex r) D (CategoryTheory.CategoryStruct.id C)
          (Work.Serre.dzMap r D z)) n))
      ((ModuleCat.epi_iff_surjective _).mp inferInstance) htp
  · -- The class of `z` survives rationalisation: use the quotient complex `D ⧸ ℤz`.
    have hmono : CategoryTheory.Mono (Work.Serre.dzMap r D z) :=
      Work.Serre.mono_dzMap r D z (Work.Serre.z_chain_not_torsion D r z hzt)
    have hKrat := Work.Serre.coker_dzMap_homology_rat_subsingleton D r N z hvan hgen hzt
    have hquot : ∀ j, j ≤ N + 1 → Subsingleton (TensorProduct ℤ
        ↥((Work.Kunneth.tpC C (Work.Serre.dzCoker D r z)).homology j) ℚ) :=
      fun j hj => Work.Serre.tensorRat_subsingleton_of_subsingleton C
        (Work.Serre.dzCoker D r z) (N + 1) hC hKrat j hj
    exact Work.Serre.tpC_homologyMap_cokernel_subsingleton C D (Work.Serre.dzComplex r) (N + 1)
      (Work.Serre.dzMap r D z) hmono hC hquot n hn

end Work.Serre.Surj
