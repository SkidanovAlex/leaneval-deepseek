import Mathlib
import Submission.Work.Cohomology.Crux33.ShuffleIndex
import Submission.Work.Cohomology.Crux33.EzGenAux
import Submission.Work.Cohomology.Crux33.EzGen
import Submission.Work.Cohomology.Crux33.ezGen_isCycle
import Submission.Work.Cohomology.Crux33.ezBridge
import Submission.Work.Cohomology.Kunneth.ezSetup
import Submission.Work.Cohomology.Kunneth.ezEval

/-!
# The Eilenberg–Zilber shuffle chain on chains, as sums of generators

This file is a self-contained copy of the chain-level Eilenberg–Zilber material needed by the
chain-level cup-product witness `Work.Cohomology.Crux33.prodSph33_cup_witness`: a chain is the sum
of its generators (`chain_eq_sum_gen`), the shuffle chain of two chains is the corresponding double
sum of shuffle chains of generators (`ezChain_eq_sum`), the shuffle chain of two cycles is a cycle
(`ezChain_isCycle`), and the boundary identity in linearised form (`ezGen_boundary_lin`).

The pinned spellings `prObj`, `prFst`, `prSnd`, `prPullFst`, `prPullSnd` are local to this file.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Cohomology.Crux33

noncomputable section

/-! ## Pinned spellings for the product of two simplicial sets -/

/-- The product (levelwise product) of two simplicial sets, pinned. -/
abbrev prObj (X Y : SSet) : SSet := X ⊗ Y

/-- The first projection of the product of simplicial sets, pinned. -/
abbrev prFst (X Y : SSet) : prObj X Y ⟶ X := CategoryTheory.SemiCartesianMonoidalCategory.fst X Y

/-- The second projection of the product of simplicial sets, pinned. -/
abbrev prSnd (X Y : SSet) : prObj X Y ⟶ Y := CategoryTheory.SemiCartesianMonoidalCategory.snd X Y

/-- Pullback of a cochain along the first projection. -/
abbrev prPullFst (X Y : SSet) (n : ℕ)
    (Θ : Work.Cohomology.Cochain ℤ X n) : Work.Cohomology.Cochain ℤ (prObj X Y) n :=
  Work.Cohomology.Kunneth.ssetPullback (prObj X Y) X (prFst X Y) n Θ

/-- Pullback of a cochain along the second projection. -/
abbrev prPullSnd (X Y : SSet) (n : ℕ)
    (B : Work.Cohomology.Cochain ℤ Y n) : Work.Cohomology.Cochain ℤ (prObj X Y) n :=
  Work.Cohomology.Kunneth.ssetPullback (prObj X Y) Y (prSnd X Y) n B

/-! ## 1. Chains as sums of generators -/

/-- The `ℤ`-linear map `mk` on a general finitely supported function, expanded. -/
theorem mk_eq_sum_gen (X : SSet) (n : ℕ) (c : X _⦋n⦌ →₀ ℤ) :
    mk X n c = ∑ x ∈ c.support, (c x) • (X.ιChainComplex (R := ezR) x).hom 1 := by
  change (Finsupp.liftAddHom
    (fun x : X _⦋n⦌ => (ModuleCat.Hom.hom (X.ιChainComplex (R := ezR) x)).toAddMonoidHom)) c
    = ∑ x ∈ c.support, (c x) • (X.ιChainComplex (R := ezR) x).hom 1
  rw [Finsupp.liftAddHom_apply, Finsupp.sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  show (ModuleCat.Hom.hom (X.ιChainComplex (R := ezR) x)) (c x) = _
  rw [show c x = (c x) • (1 : ℤ) from ((smul_eq_mul _ _).trans (mul_one _)).symm, map_zsmul,
    show (c x) • (1 : ℤ) = c x from (smul_eq_mul _ _).trans (mul_one _)]

/-- **A chain is the sum of its generators.** -/
theorem chain_eq_sum_gen (X : SSet) (n : ℕ) (u : (X.chainComplex ezR).X n) :
    u = ∑ x ∈ (coords X n u).support, (coords X n u x) • (X.ιChainComplex (R := ezR) x).hom 1 := by
  rw [← mk_eq_sum_gen X n (coords X n u)]
  exact (LinearMap.congr_fun (mk_comp_coords X n) u).symm

/-! ## 2. Bilinearity of the Eilenberg–Zilber shuffle chain -/

/-- Linearity of the shuffle chain in a finite sum in the first variable. -/
theorem ezChain_finset_sum_left (X Y : SSet) (s : Finset (S3 X)) (a : S3 X → ℤ)
    (w : S3 X → (X.chainComplex ezR).X 3) (v : (Y.chainComplex ezR).X 3) :
    Work.Cohomology.Kunneth.ezChain X Y (∑ i ∈ s, a i • w i) v
      = ∑ i ∈ s, a i • Work.Cohomology.Kunneth.ezChain X Y (w i) v := by
  have h : ((Work.Cohomology.Kunneth.ez X Y).hom
        (∑ i ∈ s, a i • w i : (X.chainComplex ezR).X 3))
      = ∑ i ∈ s, a i • ((Work.Cohomology.Kunneth.ez X Y).hom (w i)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => map_zsmul _ (a i) (w i))
  unfold Work.Cohomology.Kunneth.ezChain
  rw [h]
  change (∑ i ∈ s, (a i • ((Work.Cohomology.Kunneth.ez X Y).hom (w i)) :
    ↑((Y.chainComplex ezR).X 3) →ₗ[ℤ] ↑(((X ⊗ Y).chainComplex ezR).X 6))) v
    = ∑ i ∈ s, a i • (((Work.Cohomology.Kunneth.ez X Y).hom (w i)) v)
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-- Linearity of the shuffle chain in a finite sum in the second variable. -/
theorem ezChain_finset_sum_right (X Y : SSet) (s : Finset (S3 Y)) (b : S3 Y → ℤ)
    (w : S3 Y → (Y.chainComplex ezR).X 3) (u : (X.chainComplex ezR).X 3) :
    Work.Cohomology.Kunneth.ezChain X Y u (∑ i ∈ s, b i • w i)
      = ∑ i ∈ s, b i • Work.Cohomology.Kunneth.ezChain X Y u (w i) := by
  show (((Work.Cohomology.Kunneth.ez X Y).hom u) (∑ i ∈ s, b i • w i)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_zsmul _ (b i) (w i))

/-- **The shuffle chain of two chains, expanded into generators.** -/
theorem ezChain_eq_sum (X Y : SSet) (u : (X.chainComplex ezR).X 3)
    (v : (Y.chainComplex ezR).X 3) :
    Work.Cohomology.Kunneth.ezChain X Y u v
      = ∑ σ ∈ (coords X 3 u).support, ∑ τ ∈ (coords Y 3 v).support,
          (coords X 3 u σ * coords Y 3 v τ) • ezGen 3 3 X Y σ τ := by
  conv_lhs => rw [chain_eq_sum_gen X 3 u]
  refine (ezChain_finset_sum_left X Y (coords X 3 u).support (fun σ => coords X 3 u σ)
    (fun σ => gen3 X σ) v).trans ?_
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  conv_lhs => rw [chain_eq_sum_gen Y 3 v]
  rw [ezChain_finset_sum_right, ← Finset.sum_zsmul]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Work.Cohomology.Kunneth.ezChain_gen]
  exact (mul_smul _ _ _).symm

/-! ## 3. The linearised boundary identity -/

/-- The sum `∑ᵢ (-1)ⁱ δᵢσ` is the boundary of the generator of `σ`. -/
theorem sum_faces_X (X : SSet) (σ : S3 X) :
    (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • (X.ιChainComplex (R := ezR) (X.δ i σ)).hom 1)
      = d32 X (gen3 X σ) := by
  have h2 := congrArg (fun (f : ezR ⟶ (X.chainComplex ezR).X 2) => f.hom (1 : ℤ))
    (SSet.ιChainComplex_d X ezR (n := 2) σ)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.comp_apply] at h2
  exact h2.symm

/-- The `(2,3)`-shuffle sum over the faces of `σ` is the linear extension applied to `∂σ`. -/
theorem ezLin23_sum (X Y : SSet) (σ : S3 X) (τ : S3 Y) :
    (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • ezGen 2 3 X Y (X.δ i σ) τ)
      = (ezLin23 X Y τ).hom (d32 X (gen3 X σ)) := by
  rw [← sum_faces_X X σ, map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_zsmul, ezLin23_apply])

/-- The `(3,2)`-shuffle sum over the faces of `τ` is the linear extension applied to `∂τ`. -/
theorem ezLin32_sum (X Y : SSet) (σ : S3 X) (τ : S3 Y) :
    (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • ezGen 3 2 X Y σ (Y.δ i τ))
      = (ezLin32 X Y σ).hom (d32 Y (gen3 Y τ)) := by
  have hgen : (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • (Y.ιChainComplex (R := ezR) (Y.δ i τ)).hom 1)
      = d32 Y (gen3 Y τ) := sum_faces_X Y τ
  rw [← hgen, map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_zsmul, ezLin32_apply])

/-- **The boundary of the shuffle chain, in linearised form.** -/
theorem ezGen_boundary_lin (X Y : SSet) (σ : S3 X) (τ : S3 Y) :
    Td65 X Y (ezC X Y σ τ)
      = (ezLin23 X Y τ).hom (d32 X (gen3 X σ))
        + (-1 : ℤ) ^ 3 • (ezLin32 X Y σ).hom (d32 Y (gen3 Y τ)) := by
  have h1 : Td65 X Y (ezC X Y σ τ) = ∑ t : EzTL, ezCoefL t • ezG X Y σ τ (ezIdxL t) := by
    rw [ezC, ezGen, map_sum]
    rw [Fintype.sum_prod_type (f := fun t : EzTL => ezCoefL t • ezG X Y σ τ (ezIdxL t))]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [map_zsmul, d65_apply_gen6, ← Finset.sum_zsmul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ezCoefL, mul_smul]
    congr 1
    rw [tensor_delta, map_delta X j (aHom (p := 3) (q := 3) S.1 S.2) σ,
      map_delta Y j (bHom (p := 3) (q := 3) S.1 S.2) τ]
    simp only [ezG, ezIdxL]
  have h2 : (∑ t : EzTL, ezCoefL t • ezG X Y σ τ (ezIdxL t))
      = ∑ y ∈ ezSupp, ezLfun y • ezG X Y σ τ y := by
    simpa only [ezLfun] using (ezSum_reindex ezIdxL ezCoefL (ezG X Y σ τ) ezSupp
      (fun t => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))))
  have h3 : (∑ y ∈ ezSupp, ezLfun y • ezG X Y σ τ y)
      = ∑ y ∈ ezSupp, ezRfun y • ezG X Y σ τ y := by
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [ezLfun_eq_ezRfun y hy]
  have h4 : (∑ y ∈ ezSupp, ezRfun y • ezG X Y σ τ y)
      = ∑ t : EzTR, ezCoefR t • ezG X Y σ τ (ezIdxR t) := by
    simpa only [ezRfun] using (ezSum_reindex ezIdxR ezCoefR (ezG X Y σ τ) ezSupp
      (fun t => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ t)))).symm
  have h5 : (∑ t : EzTR, ezCoefR t • ezG X Y σ τ (ezIdxR t))
      = (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • ezGen 2 3 X Y (X.δ i σ) τ)
        + ((-1 : ℤ) ^ 3) • (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • ezGen 3 2 X Y σ (Y.δ i τ)) := by
    rw [Fintype.sum_sum_type]
    congr 1
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [ezGen, ← Finset.sum_zsmul]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      simp only [ezCoefR, ezIdxR, ezG, Sum.elim_inl]
      rw [mul_smul, delta_map X i (aHom (p := 2) (q := 3) S.1 S.2) σ]
    · rw [← Finset.sum_zsmul, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [ezGen, ← Finset.sum_zsmul, ← Finset.sum_zsmul]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      simp only [ezCoefR, ezIdxR, ezG, Sum.elim_inr]
      rw [mul_smul, mul_smul, delta_map Y i (bHom (p := 3) (q := 2) S.1 S.2) τ]
  rw [h1, h2, h3, h4, h5, ezLin23_sum X Y σ τ, ezLin32_sum X Y σ τ]

/-! ## 4. Cyclicity of the shuffle chain of two cycles -/

/-- The boundary of the shuffle chain of two cycles is zero. -/
theorem ezChain_isCycle (X Y : SSet) (u : (X.chainComplex ezR).X 3) (v : (Y.chainComplex ezR).X 3)
    (hu : d32 X u = 0) (hv : d32 Y v = 0) :
    Td65 X Y (Work.Cohomology.Kunneth.ezChain X Y u v) = 0 := by
  have hdXu : (∑ σ ∈ (coords X 3 u).support, (coords X 3 u σ) • d32 X (gen3 X σ)) = d32 X u := by
    have e1 : (∑ σ ∈ (coords X 3 u).support, (coords X 3 u σ) • d32 X (gen3 X σ))
        = ∑ σ ∈ (coords X 3 u).support, d32 X ((coords X 3 u σ) • gen3 X σ) :=
      Finset.sum_congr rfl (fun σ _ => (map_zsmul (d32 X) (coords X 3 u σ) (gen3 X σ)).symm)
    rw [e1, ← map_sum, ← chain_eq_sum_gen X 3 u]
  have hdYu : (∑ τ ∈ (coords Y 3 v).support, (coords Y 3 v τ) • d32 Y (gen3 Y τ)) = d32 Y v := by
    have e1 : (∑ τ ∈ (coords Y 3 v).support, (coords Y 3 v τ) • d32 Y (gen3 Y τ))
        = ∑ τ ∈ (coords Y 3 v).support, d32 Y ((coords Y 3 v τ) • gen3 Y τ) :=
      Finset.sum_congr rfl (fun τ _ => (map_zsmul (d32 Y) (coords Y 3 v τ) (gen3 Y τ)).symm)
    rw [e1, ← map_sum, ← chain_eq_sum_gen Y 3 v]
  have h23 : (∑ σ ∈ (coords X 3 u).support, ∑ τ ∈ (coords Y 3 v).support,
        (coords X 3 u σ * coords Y 3 v τ) • ((ezLin23 X Y τ).hom (d32 X (gen3 X σ)))) = 0 := by
    rw [Finset.sum_comm]
    have h1 : ∀ τ ∈ (coords Y 3 v).support,
        (∑ σ ∈ (coords X 3 u).support,
          (coords X 3 u σ * coords Y 3 v τ) • ((ezLin23 X Y τ).hom (d32 X (gen3 X σ))))
        = (coords Y 3 v τ) • (∑ σ ∈ (coords X 3 u).support,
          (coords X 3 u σ) • ((ezLin23 X Y τ).hom (d32 X (gen3 X σ)))) := by
      intro τ _
      rw [← Finset.sum_zsmul]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [mul_comm, mul_zsmul]
    have h2 : ∀ τ : S3 Y,
        (∑ σ ∈ (coords X 3 u).support,
          (coords X 3 u σ) • ((ezLin23 X Y τ).hom (d32 X (gen3 X σ))))
        = (ezLin23 X Y τ).hom (d32 X u) := by
      intro τ
      rw [← hdXu, map_sum]
      exact Finset.sum_congr rfl
        (fun σ _ => (map_zsmul ((ezLin23 X Y τ).hom) (coords X 3 u σ) (d32 X (gen3 X σ))).symm)
    have hA : (∑ τ ∈ (coords Y 3 v).support,
        (coords Y 3 v τ) • ((ezLin23 X Y τ).hom (d32 X u))) = 0 := by
      rw [hu]
      apply Finset.sum_eq_zero
      intro τ _
      rw [LinearMap.map_zero, zsmul_zero]
    exact (Finset.sum_congr rfl (fun τ hτ => h1 τ hτ)).trans
      ((Finset.sum_congr rfl (fun τ _ => by rw [h2 τ])).trans hA)
  have h32 : (∑ σ ∈ (coords X 3 u).support, ∑ τ ∈ (coords Y 3 v).support,
        (coords X 3 u σ * coords Y 3 v τ) • ((ezLin32 X Y σ).hom (d32 Y (gen3 Y τ)))) = 0 := by
    have h1 : ∀ σ ∈ (coords X 3 u).support,
        (∑ τ ∈ (coords Y 3 v).support,
          (coords X 3 u σ * coords Y 3 v τ) • ((ezLin32 X Y σ).hom (d32 Y (gen3 Y τ))))
        = (coords X 3 u σ) • (∑ τ ∈ (coords Y 3 v).support,
          (coords Y 3 v τ) • ((ezLin32 X Y σ).hom (d32 Y (gen3 Y τ)))) := by
      intro σ _
      rw [← Finset.sum_zsmul]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [mul_zsmul]
    have h2 : ∀ σ : S3 X,
        (∑ τ ∈ (coords Y 3 v).support,
          (coords Y 3 v τ) • ((ezLin32 X Y σ).hom (d32 Y (gen3 Y τ))))
        = (ezLin32 X Y σ).hom (d32 Y v) := by
      intro σ
      rw [← hdYu, map_sum]
      exact Finset.sum_congr rfl
        (fun τ _ => (map_zsmul ((ezLin32 X Y σ).hom) (coords Y 3 v τ) (d32 Y (gen3 Y τ))).symm)
    have hB : (∑ σ ∈ (coords X 3 u).support,
        (coords X 3 u σ) • ((ezLin32 X Y σ).hom (d32 Y v))) = 0 := by
      rw [hv]
      apply Finset.sum_eq_zero
      intro σ _
      rw [LinearMap.map_zero, zsmul_zero]
    exact (Finset.sum_congr rfl (fun σ hσ => h1 σ hσ)).trans
      ((Finset.sum_congr rfl (fun σ _ => by rw [h2 σ])).trans hB)
  have split_inner : ∀ σ : S3 X,
      (∑ τ ∈ (coords Y 3 v).support,
          (coords X 3 u σ * coords Y 3 v τ) •
            ((ezLin23 X Y τ).hom (d32 X (gen3 X σ))
              + (-1 : ℤ) ^ 3 • (ezLin32 X Y σ).hom (d32 Y (gen3 Y τ))))
        = (∑ τ ∈ (coords Y 3 v).support,
              (coords X 3 u σ * coords Y 3 v τ) • ((ezLin23 X Y τ).hom (d32 X (gen3 X σ))))
          + (-1 : ℤ) ^ 3 • (∑ τ ∈ (coords Y 3 v).support,
              (coords X 3 u σ * coords Y 3 v τ) • ((ezLin32 X Y σ).hom (d32 Y (gen3 Y τ)))) := by
    intro σ
    rw [← Finset.sum_zsmul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    calc (coords X 3 u σ * coords Y 3 v τ) •
            ((ezLin23 X Y τ).hom (d32 X (gen3 X σ))
              + (-1 : ℤ) ^ 3 • (ezLin32 X Y σ).hom (d32 Y (gen3 Y τ)))
        = (coords X 3 u σ * coords Y 3 v τ) • ((ezLin23 X Y τ).hom (d32 X (gen3 X σ)))
            + (coords X 3 u σ * coords Y 3 v τ) •
              ((-1 : ℤ) ^ 3 • (ezLin32 X Y σ).hom (d32 Y (gen3 Y τ))) := zsmul_add _ _ _
      _ = (coords X 3 u σ * coords Y 3 v τ) • ((ezLin23 X Y τ).hom (d32 X (gen3 X σ)))
            + ((coords X 3 u σ * coords Y 3 v τ) * (-1 : ℤ) ^ 3) •
              ((ezLin32 X Y σ).hom (d32 Y (gen3 Y τ))) := by rw [← mul_zsmul]
      _ = (coords X 3 u σ * coords Y 3 v τ) • ((ezLin23 X Y τ).hom (d32 X (gen3 X σ)))
            + ((-1 : ℤ) ^ 3 * (coords X 3 u σ * coords Y 3 v τ)) •
              ((ezLin32 X Y σ).hom (d32 Y (gen3 Y τ))) := by
        rw [show ((coords X 3 u σ * coords Y 3 v τ) * (-1 : ℤ) ^ 3)
          = ((-1 : ℤ) ^ 3 * (coords X 3 u σ * coords Y 3 v τ)) from mul_comm _ _]
      _ = (coords X 3 u σ * coords Y 3 v τ) • ((ezLin23 X Y τ).hom (d32 X (gen3 X σ)))
            + (-1 : ℤ) ^ 3 • ((coords X 3 u σ * coords Y 3 v τ) •
              ((ezLin32 X Y σ).hom (d32 Y (gen3 Y τ)))) := by
        rw [show ((-1 : ℤ) ^ 3 * (coords X 3 u σ * coords Y 3 v τ)) •
              ((ezLin32 X Y σ).hom (d32 Y (gen3 Y τ)))
            = (-1 : ℤ) ^ 3 • ((coords X 3 u σ * coords Y 3 v τ) •
              ((ezLin32 X Y σ).hom (d32 Y (gen3 Y τ)))) from mul_zsmul _ _ _]
  have split_outer :
      (∑ σ ∈ (coords X 3 u).support,
          ((∑ τ ∈ (coords Y 3 v).support,
              (coords X 3 u σ * coords Y 3 v τ) • ((ezLin23 X Y τ).hom (d32 X (gen3 X σ))))
            + (-1 : ℤ) ^ 3 • (∑ τ ∈ (coords Y 3 v).support,
              (coords X 3 u σ * coords Y 3 v τ) • ((ezLin32 X Y σ).hom (d32 Y (gen3 Y τ))))))
        = (∑ σ ∈ (coords X 3 u).support, ∑ τ ∈ (coords Y 3 v).support,
              (coords X 3 u σ * coords Y 3 v τ) • ((ezLin23 X Y τ).hom (d32 X (gen3 X σ))))
          + (-1 : ℤ) ^ 3 • (∑ σ ∈ (coords X 3 u).support,
              ∑ τ ∈ (coords Y 3 v).support,
              (coords X 3 u σ * coords Y 3 v τ) • ((ezLin32 X Y σ).hom (d32 Y (gen3 Y τ)))) := by
    rw [← Finset.sum_zsmul, ← Finset.sum_add_distrib]
  calc Td65 X Y (Work.Cohomology.Kunneth.ezChain X Y u v)
      = ∑ σ ∈ (coords X 3 u).support, ∑ τ ∈ (coords Y 3 v).support,
          (coords X 3 u σ * coords Y 3 v τ) • Td65 X Y (ezGen 3 3 X Y σ τ) := by
        rw [ezChain_eq_sum, map_sum]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [map_sum]
        exact Finset.sum_congr rfl (fun τ _ => map_zsmul _ _ _)
    _ = ∑ σ ∈ (coords X 3 u).support, ∑ τ ∈ (coords Y 3 v).support,
          (coords X 3 u σ * coords Y 3 v τ) •
            ((ezLin23 X Y τ).hom (d32 X (gen3 X σ))
              + (-1 : ℤ) ^ 3 • (ezLin32 X Y σ).hom (d32 Y (gen3 Y τ))) := by
        refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun τ _ => ?_))
        rw [ezGen_boundary_lin]
    _ = _ := by exact Finset.sum_congr rfl (fun σ _ => split_inner σ)
    _ = _ := split_outer
    _ = 0 := by rw [h23, h32, zero_add, zsmul_zero]

end

end Work.Cohomology.Crux33
