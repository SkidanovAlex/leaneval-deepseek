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

/-- **The quotient of the `(k+1)`-skeleton chain complex by the `k`-skeleton chain complex in
degree `k+1` is free on the `(k+1)`-simplices.**  In degree `k+1` the source
`(K.skel k).chain.X (k+1)` is a zero object (`skel_card_eq_zero`, as `k < k+1`) and the target
is `∐ (fun _ : Fin (K.card (k+1)) => ℤ)` (`skel_card_eq`), so the cokernel is the target. -/
theorem skelQuotient_X_iso (K : DeltaCx) (k : ℕ) :
    Nonempty ((cokernel (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))).X (k + 1) ≅
      (∐ fun _ : Fin (K.card (k + 1)) => ModuleCat.of ℤ ℤ)) := by
  -- The evaluation functor to degree `k + 1` preserves colimits, hence cokernels, so the
  -- cokernel of the chain map in degree `k + 1` is the cokernel of its degree `k + 1` component.
  have e₁ : (cokernel (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))).X (k + 1) ≅
      cokernel ((DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))).f (k + 1)) :=
    PreservesCokernel.iso
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) (k + 1)) _
  -- In degree `k + 1` the source object `(K.skel k).chainX (k+1)` vanishes, as `k < k + 1`.
  have hzero : IsZero ((K.skel k).chainX (k + 1)) :=
    isZero_chainX_of_dim_lt (K.skel k) (by rw [DeltaCx.skel_dim]; omega)
  have h0 : (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))).f (k + 1) = 0 :=
    hzero.eq_of_src _ _
  -- So the cokernel is the target, which is free on the `(k+1)`-simplices of `K.skel (k+1)`,
  -- i.e. on the `(k+1)`-simplices of `K` by `skel_card_eq`.
  have e₂ : cokernel ((DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))).f (k + 1)) ≅
      (K.skel (k + 1)).chainX (k + 1) :=
    cokernelIsoOfEq h0 ≪≫ cokernelZeroIsoTarget
  have e₃ : (K.skel (k + 1)).chainX (k + 1) ≅
      (∐ fun _ : Fin (K.card (k + 1)) => ModuleCat.of ℤ ℤ) :=
    Sigma.whiskerEquiv
      (f := fun _ : Fin ((K.skel (k + 1)).card (k + 1)) => Work.Homology.ZMod)
      (g := fun _ : Fin (K.card (k + 1)) => Work.Homology.ZMod)
      (finCongr (K.skel_card_eq (k + 1) (le_refl (k + 1)))) (fun _ => Iso.refl _)
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩

end Work.DeltaHomology
