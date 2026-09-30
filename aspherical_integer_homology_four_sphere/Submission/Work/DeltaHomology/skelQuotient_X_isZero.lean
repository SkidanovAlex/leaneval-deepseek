import Mathlib
import Submission.Work.DeltaHomology.Chain
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.SkeletonMap
import Submission.Work.DeltaHomology.isZero_chainX_of_dim_lt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- **The quotient of the `(k+1)`-skeleton chain complex by the `k`-skeleton chain complex
vanishes outside degree `k+1`.**  Degreewise, `(K.skel k).chain.X j ⟶ (K.skel (k+1)).chain.X j`
is an isomorphism for `j ≤ k` (`skel_card_eq`, `skelHomOfLe` acting as `Fin.cast`) and a map
out of a zero object for `j > k` (`skel_card_eq_zero`, `isZero_chainX_of_dim_lt`), so its
cokernel vanishes for `j ≠ k+1`. -/
theorem skelQuotient_X_isZero (K : DeltaCx) (k : ℕ) {j : ℕ} (hj : j ≠ k + 1) :
    IsZero ((cokernel (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))).X j) := by
  -- The evaluation functor to degree `j` preserves colimits, hence cokernels, so the cokernel
  -- of the chain map in degree `j` is the cokernel of its degreewise component.
  have e : (cokernel (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))).X j ≅
      cokernel ((DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))).f j) :=
    PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) j) _
  -- It now suffices that the degreewise component is an epimorphism.
  haveI : Epi ((DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))).f j) := by
    change Epi ((K.skelLE (Nat.le_succ k)).chainMapFun j)
    by_cases hjk : j ≤ k
    · -- Case `j ≤ k`: the two skeleta agree in degree `j` and the map is an isomorphism.
      have hcard : (K.skel k).card j = (K.skel (k + 1)).card j := by
        rw [DeltaCx.skel_card_eq K k hjk, DeltaCx.skel_card_eq K (k + 1) (by omega)]
      let ψ : (K.skel (k + 1)).chainX j ⟶ (K.skel k).chainX j :=
        Sigma.desc fun τ : Fin ((K.skel (k + 1)).card j) =>
          (K.skel k).chainι j (Fin.cast hcard.symm τ)
      have h1 : (K.skelLE (Nat.le_succ k)).chainMapFun j ≫ ψ = 𝟙 _ := by
        apply DeltaCx.chainX_hom_ext
        intro σ
        rw [← Category.assoc, DeltaCx.Hom.chainMapFun_chainι, DeltaCx.skelLE_map,
          skelHomOfLe_eq K (Nat.le_succ k) hjk σ]
        dsimp only [ψ]
        rw [Sigma.ι_comp_desc, Category.comp_id]
        refine congrArg (fun x : Fin ((K.skel k).card j) => (K.skel k).chainι j x) ?_
        apply Fin.ext
        simp only [Fin.val_cast]
      have h2 : ψ ≫ (K.skelLE (Nat.le_succ k)).chainMapFun j = 𝟙 _ := by
        apply DeltaCx.chainX_hom_ext
        intro τ
        rw [← Category.assoc]
        dsimp only [ψ]
        rw [Sigma.ι_comp_desc, DeltaCx.Hom.chainMapFun_chainι, DeltaCx.skelLE_map,
          skelHomOfLe_eq K (Nat.le_succ k) hjk (Fin.cast hcard.symm τ)]
        rw [Category.comp_id]
        refine congrArg (fun x : Fin ((K.skel (k + 1)).card j) =>
          (K.skel (k + 1)).chainι j x) ?_
        apply Fin.ext
        simp only [Fin.val_cast]
      haveI : IsIso ((K.skelLE (Nat.le_succ k)).chainMapFun j) := ⟨ψ, h1, h2⟩
      exact inferInstance
    · -- Case `j > k + 1`: the target `(K.skel (k+1)).chainX j` is a zero object.
      have hz : IsZero ((K.skel (k + 1)).chainX j) :=
        isZero_chainX_of_dim_lt (K.skel (k + 1)) (by rw [DeltaCx.skel_dim]; omega)
      exact hz.epi _
  exact IsZero.of_iso (isZero_cokernel_of_epi _) e

end Work.DeltaHomology
