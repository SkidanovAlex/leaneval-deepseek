import Mathlib
import Submission.Work.Kunneth.AWAux
import Submission.Work.Kunneth.awKey

/-!
# The two decompositions of the Alexander--Whitney comparison

Writing `z` for an `(n+1)`-simplex of `X ⊗ Y`, this file proves the two "component" forms of the
Alexander--Whitney comparison:

* `awDecU` — the Koszul differential `tpD` of the Alexander--Whitney chain of `z` is the sum
  `∑_{a} tpLof ⟨(a, n+1-(a+1))⟩ (awU a)` of the `(a, n-a)`-components `awU`;
* `awDecV` — the Alexander--Whitney chain of the boundary `∂z` is the same sum, with the
  components `awV` of the boundary.

Together with the pointwise identity `awKey` (`awU = awV`) these give the chain-map property of
`awHom` (`awHom_d`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth
noncomputable section
attribute [-instance] AddCommGroup.toIntModule

/-- **The `(a, n-a)`-components of the Koszul differential of the Alexander–Whitney chain:**
the differential of the Alexander–Whitney chain of an `(n+1)`-simplex `z` of `X ⊗ Y`, decomposed
into the contributions of the bidegree `(a, n-a)`. -/
theorem awDecU_exp (X Y : SSet) (n : ℕ) (z : (X ⊗ Y) _⦋n+1⦌) :
    tpD (sChain X) (sChain Y) n ((awGen X Y (n+1) z).hom 1)
      = (∑ a : Fin (n+1), tpLof (sChain X) (sChain Y) n ⟨(a.val, n+1-(a.val+1)), by omega⟩
          (((sChain X).d (a.val+1) a.val).hom
              (genCh X (Work.Cohomology.frontFace X (a.val+1) (n+1) (by omega) z.1))
            ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n+1-(a.val+1)) (n+1) (by omega) z.2)))
        + (∑ a : Fin (n+1), (-1 : ℤ)^(a.val) •
            tpLof (sChain X) (sChain Y) n ⟨(a.val, n+1-(a.val+1)), by omega⟩
              (genCh X (Work.Cohomology.frontFace X a.val (n+1) (by omega) z.1)
                ⊗ₜ[ℤ] ((sChain Y).d (n+1-a.val) (n+1-a.val-1)).hom
                    (genCh Y (backFaceLE Y (n+1-a.val) (n+1) (by omega) z.2)))) := by
  rw [awGen_hom_one, map_sum]
  rw [Finset.sum_congr rfl (fun p _ =>
    tpD_lof_tmul (sChain X) (sChain Y) n ⟨(p.val, n+1-p.val), by omega⟩
      (genCh X (Work.Cohomology.frontFace X p.val (n+1) (by omega) z.1))
      (genCh Y (backFaceLE Y (n+1-p.val) (n+1) (by omega) z.2)))]
  rw [Finset.sum_add_distrib]
  conv_lhs =>
    arg 1
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.sub_zero]
    rw [dif_neg (show ¬ (1 ≤ (0:ℕ)) by omega)]
    rw [zero_add]
  conv_lhs =>
    arg 2
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, Subtype.coe_mk]
    rw [dif_neg (show ¬ (1 ≤ (0:ℕ)) by omega)]
    rw [add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [dif_pos (show 1 ≤ (a:ℕ)+1 by omega), dif_pos (show 1 ≤ n+1-(a:ℕ) by omega)]
  rfl

/-- **The `(a, n-a)`-join of the Koszul differential of the Alexander–Whitney chain.** -/
theorem awDecU (X Y : SSet) (n : ℕ) (z : (X ⊗ Y) _⦋n+1⦌) :
    tpD (sChain X) (sChain Y) n ((awGen X Y (n+1) z).hom 1)
      = ∑ a : Fin (n+1), tpLof (sChain X) (sChain Y) n ⟨(a.val, n+1-(a.val+1)), by omega⟩
          (awU X Y n a z.1 z.2) := by
  rw [awDecU_exp, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [awU, map_add]
  exact (congrArg₂ (· + ·) rfl (tpLof_zsmul (sChain X) (sChain Y) n
    ⟨(a.val, n+1-(a.val+1)), by omega⟩ ((-1 : ℤ)^(a.val))
    (genCh X (Work.Cohomology.frontFace X a.val (n+1) (by omega) z.1)
      ⊗ₜ[ℤ] ((sChain Y).d (n+1-a.val) (n+1-a.val-1)).hom
          (genCh Y (backFaceLE Y (n+1-a.val) (n+1) (by omega) z.2))))).symm

/-- **The `(a, n-a)`-components of the Alexander–Whitney chain of the boundary:** the Alexander–
Whitney chain of the boundary of `z` is the sum `∑_{a} tpLof ⟨(a, n+1-(a+1))⟩ (awV a)`. -/
theorem awDecV (X Y : SSet) (n : ℕ) (z : (X ⊗ Y) _⦋n+1⦌) :
    (∑ k : Fin (n+2), (-1 : ℤ)^(k:ℕ) •
        (awGen X Y n (ConcreteCategory.hom (SimplicialObject.δ (X ⊗ Y) k) z)).hom 1)
      = ∑ a : Fin (n+1), tpLof (sChain X) (sChain Y) n ⟨(a.val, n+1-(a.val+1)), by omega⟩
          (awV X Y n a z.1 z.2) := by
  rw [show (∑ a : Fin (n+1), tpLof (sChain X) (sChain Y) n ⟨(a.val, n+1-(a.val+1)), by omega⟩
        (awV X Y n a z.1 z.2))
      = ∑ a : Fin (n+1), ∑ k : Fin (n+2), (-1 : ℤ)^(k:ℕ) •
          tpLof (sChain X) (sChain Y) n ⟨(a.val, n+1-(a.val+1)), by omega⟩
            (genCh X (Work.Cohomology.frontFace X a.val n (by omega) (X.δ k z.1))
              ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n+1-a.val-1) n (by omega) (Y.δ k z.2))) from by
    apply Finset.sum_congr rfl
    intro a _
    rw [awV, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact tpLof_zsmul (sChain X) (sChain Y) n ⟨(a.val, n+1-(a.val+1)), by omega⟩ ((-1:ℤ)^(k:ℕ))
      (genCh X (Work.Cohomology.frontFace X a.val n (by omega) (X.δ k z.1))
        ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n+1-a.val-1) n (by omega) (Y.δ k z.2)))]
  have hK : ∀ k : Fin (n+2), (-1 : ℤ)^(k:ℕ) •
        (awGen X Y n (ConcreteCategory.hom (SimplicialObject.δ X k) z.1,
                       ConcreteCategory.hom (SimplicialObject.δ Y k) z.2)).hom 1
      = ∑ p : Fin (n+1), (-1 : ℤ)^(k:ℕ) •
          tpLof (sChain X) (sChain Y) n ⟨(p.val, n-p.val), by omega⟩
            (genCh X (Work.Cohomology.frontFace X p.val n (by omega) (X.δ k z.1))
              ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n-p.val) n (by omega) (Y.δ k z.2))) := fun k => by
    exact (congrArg (fun u => (-1:ℤ)^(k:ℕ) • u)
      (awGen_hom_one X Y n (ConcreteCategory.hom (SimplicialObject.δ X k) z.1,
                            ConcreteCategory.hom (SimplicialObject.δ Y k) z.2))).trans
      (Finset.sum_zsmul (fun p : Fin (n+1) =>
          tpLof (sChain X) (sChain Y) n ⟨(p.val, n-p.val), by omega⟩
            (genCh X (Work.Cohomology.frontFace X p.val n (by omega) (X.δ k z.1))
              ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n-p.val) n (by omega) (Y.δ k z.2))))
        Finset.univ ((-1:ℤ)^(k:ℕ))).symm
  simp only [prod_delta]
  rw [Finset.sum_congr rfl (fun k _ => hK k)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  have key : tpLof (sChain X) (sChain Y) n ⟨(a.val, n-a.val), by omega⟩
        (genCh X (Work.Cohomology.frontFace X a.val n (by omega) (X.δ k z.1))
          ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n-a.val) n (by omega) (Y.δ k z.2)))
      = tpLof (sChain X) (sChain Y) n ⟨(a.val, n+1-(a.val+1)), by omega⟩
        (genCh X (Work.Cohomology.frontFace X a.val n (by omega) (X.δ k z.1))
          ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n+1-a.val-1) n (by omega) (Y.δ k z.2))) := by
    have h1 := tpLof_congr (C := sChain X) (D := sChain Y)
      (show n - a.val = n+1-(a.val+1) by omega) (show a.val + (n - a.val) = n by omega)
      (show a.val + (n+1-(a.val+1)) = n by omega)
      (genCh X (Work.Cohomology.frontFace X a.val n (by omega) (X.δ k z.1))
        ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n-a.val) n (by omega) (Y.δ k z.2)))
    have h2 := cast_tmul (C := sChain X) (D := sChain Y)
      (p := a.val) (q := n - a.val) (q' := n+1-(a.val+1))
      (show n - a.val = n+1-(a.val+1) by omega)
      (genCh X (Work.Cohomology.frontFace X a.val n (by omega) (X.δ k z.1)))
      (genCh Y (backFaceLE Y (n-a.val) n (by omega) (Y.δ k z.2)))
    have h3 : cast (congrArg (fun j => ↥((sChain Y).X j)) (show n - a.val = n+1-(a.val+1) by omega))
          (genCh Y (backFaceLE Y (n-a.val) n (by omega) (Y.δ k z.2)))
        = genCh Y (backFaceLE Y (n+1-a.val-1) n (by omega) (Y.δ k z.2)) :=
      (genCh_cast (Y := Y) (show n - a.val = n+1-(a.val+1) by omega)
        (backFaceLE Y (n-a.val) n (by omega) (Y.δ k z.2))).trans
      (congrArg (genCh Y) (cast_backFaceLE (X := Y)
        (show n - a.val = n+1-(a.val+1) by omega) (by omega) (by omega) (Y.δ k z.2)))
    exact h1.trans ((congrArg (fun u => tpLof (sChain X) (sChain Y) n
        ⟨(a.val, n+1-(a.val+1)), by omega⟩ u) h2).trans
      (congrArg (fun w => tpLof (sChain X) (sChain Y) n
        ⟨(a.val, n+1-(a.val+1)), by omega⟩
        (genCh X (Work.Cohomology.frontFace X a.val n (by omega) (X.δ k z.1)) ⊗ₜ[ℤ] w)) h3))
  exact congrArg (fun u => (-1:ℤ)^(k:ℕ) • u) key

end
end Work.Kunneth
