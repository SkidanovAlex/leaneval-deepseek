import Mathlib
import Submission.Work.Cohomology.StageSplitDefs
import Submission.Work.Cohomology.LK_decomposition
import Submission.Work.Cohomology.StageSplitTransport
import Submission.Work.Cohomology.union_ball_chain
import Submission.Work.Cohomology.lkMap_isIso_of_convex
import Submission.Work.Cohomology.LK_closedBall_union_injective
import Submission.Work.Cohomology.lkMap_isIso_of_connected_balls
import Submission.Work.Cohomology.exists_connected_piece_decomposition

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The stage splitting in the local homology of a union of balls

For `T = ⋃_j closedBall (c j) (r j)` and `S = ⋃_j closedBall (c' j) (r' j)` finite unions of closed
balls in `ℝ^N` with `S ⊆ interior T` and every connected component of `T` meeting `S`, the stage map
`lkMap : LK N T → LK N S` admits a left inverse (i.e. `LK N T` is a direct summand of `LK N S`).
This is the "local homology" (`L`-group) form of `Work.Cohomology.euclidean_stage_split`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Work.Cohomology
noncomputable section
variable {N : ℕ}

/-- Re-indexing a finite union by `Fin s.card`. -/
theorem iUnion_finset_equivFin {ι : Type} (s : Finset ι)
    (B : ι → Set (EuclideanSpace ℝ (Fin N))) :
    (⋃ j ∈ s, B j) = ⋃ i : Fin s.card, B ((Finset.equivFin s).symm i) := by
  rw [show (⋃ j ∈ s, B j) = ⋃ j : ↥s, B (j : ι) from by rw [Set.iUnion_subtype]]
  refine Set.iUnion_congr_of_surjective (Finset.equivFin s) (Finset.equivFin s).surjective ?_
  intro x
  exact congrArg B (congrArg Subtype.val (Equiv.symm_apply_apply (Finset.equivFin s) x))

/-- `lkMap` only depends on the underlying function of the inclusion. -/
theorem lkMap_congr_proofs {K K' : Set (EuclideanSpace ℝ (Fin N))} (h h' : K ⊆ K') :
    lkMap (N := N) h = lkMap (N := N) h' := by
  simp only [lkMap]

/-- Transport of `LK` along an equality of compact sets. -/
noncomputable def LKcongr {K K' : Set (EuclideanSpace ℝ (Fin N))} (h : K = K') :
    LK N K ≃ₗ[ℤ] LK N K' where
  toFun a := h ▸ a
  invFun b := h.symm ▸ b
  left_inv a := by cases h; rfl
  right_inv b := by cases h; rfl
  map_add' a b := by cases h; rfl
  map_smul' c a := by cases h; rfl

/-- Naturality of the transport with respect to the stage maps. -/
theorem LKcongr_natural {A K K' : Set (EuclideanSpace ℝ (Fin N))} (h : K = K')
    (hAK : A ⊆ K) (hAK' : A ⊆ K') :
    (lkMap (N := N) hAK').comp (LKcongr (N := N) h).toLinearMap = lkMap (N := N) hAK := by
  cases h
  ext a
  show lkMap (N := N) hAK' a = lkMap (N := N) hAK a
  exact congrArg (fun f : LK N K →ₗ[ℤ] LK N A => f a) (lkMap_congr_proofs (N := N) hAK' hAK)

/-- Composition of stage maps along a chain of inclusions. -/
theorem lkMap_apply_comp {A B C D : Set (EuclideanSpace ℝ (Fin N))} (h1 : A ⊆ B) (h2 : B ⊆ C)
    (h3 : C ⊆ D) (x : LK N D) :
    lkMap (N := N) h1 (lkMap (N := N) h2 (lkMap (N := N) h3 x))
      = lkMap (N := N) (h1.trans (h2.trans h3)) x := by
  have h : ((lkMap (N := N) h1).comp ((lkMap (N := N) h2).comp (lkMap (N := N) h3))) x
      = lkMap (N := N) (h1.trans (h2.trans h3)) x := by
    rw [lkMap_comp (N := N) h2 h3, lkMap_comp (N := N) h1 (h2.trans h3)]
  exact h

/-- Tupling of linear maps into a product, in the form used for the stage splitting. -/
noncomputable def piMap {ι : Type*} {M : Type*} [AddCommGroup M] [Module ℤ M]
    {K : ι → Set (EuclideanSpace ℝ (Fin N))}
    (f : ∀ i, M →ₗ[ℤ] LK N (K i)) : M →ₗ[ℤ] ((i : ι) → LK N (K i)) where
  toFun a i := f i a
  map_add' a b := by funext i; simp only [Pi.add_apply, map_add]
  map_smul' c a := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    exact (LinearMap.map_smul (f i) c a).trans (int_smul_eq_zsmul ((LKC N (K i)).isModule) c _)


/-- **The stage splitting in the `L`-groups.** -/
theorem LK_stage_split {N : ℕ} (hN : 1 ≤ N) {k l : ℕ}
    (c : Fin k → EuclideanSpace ℝ (Fin N)) (r : Fin k → ℝ) (hr : ∀ j, 0 < r j)
    (c' : Fin l → EuclideanSpace ℝ (Fin N)) (r' : Fin l → ℝ) (hr' : ∀ j, 0 < r' j)
    (hsub : (⋃ j, Metric.closedBall (c' j) (r' j)) ⊆
      interior (⋃ j, Metric.closedBall (c j) (r j)))
    (hcomp : ∀ x ∈ (⋃ j, Metric.closedBall (c j) (r j)),
      ∃ y ∈ (⋃ j, Metric.closedBall (c' j) (r' j)),
        x ∈ connectedComponentIn (⋃ j, Metric.closedBall (c j) (r j)) y) :
    ∃ s : LK N (⋃ j, Metric.closedBall (c' j) (r' j)) →ₗ[ℤ]
        LK N (⋃ j, Metric.closedBall (c j) (r j)),
      s.comp (lkMap (N := N) (hsub.trans interior_subset)) = LinearMap.id := by
  classical
  set S : Set (EuclideanSpace ℝ (Fin N)) := ⋃ j, Metric.closedBall (c' j) (r' j) with hSdef
  set T : Set (EuclideanSpace ℝ (Fin N)) := ⋃ j, Metric.closedBall (c j) (r j) with hTdef
  have hST : S ⊆ T := hsub.trans interior_subset
  have hcomp' : ∀ x ∈ (⋃ j, Metric.closedBall (c j) (r j)),
      ∃ y ∈ S, x ∈ connectedComponentIn (⋃ j, Metric.closedBall (c j) (r j)) y := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcomp x hx
    exact ⟨y, by rwa [hSdef], hxy⟩
  obtain ⟨m, idx, y, hyS, hyP, hconnP, hdisjP, hunionP⟩ :=
    exists_connected_piece_decomposition (N := N) c r (S := S) hcomp'
  set P : Fin m → Set (EuclideanSpace ℝ (Fin N)) := fun i => ⋃ i' : Fin (idx i).card,
    Metric.closedBall (c ((Finset.equivFin (idx i)).symm i'))
      (r ((Finset.equivFin (idx i)).symm i')) with hPdef
  have hyP' : ∀ i, y i ∈ P i := by
    intro i
    simp only [hPdef]
    rw [← iUnion_finset_equivFin (idx i) (fun j => Metric.closedBall (c j) (r j))]
    exact hyP i
  have hconnP' : ∀ i, IsConnected (P i) := by
    intro i
    simp only [hPdef]
    rw [← iUnion_finset_equivFin (idx i) (fun j => Metric.closedBall (c j) (r j))]
    exact hconnP i
  have hPi_sub : ∀ i, P i ⊆ T := by
    intro i x hx
    simp only [hPdef] at hx
    obtain ⟨i', hi'⟩ := Set.mem_iUnion.mp hx
    rw [hTdef]
    exact Set.mem_iUnion.mpr ⟨(Finset.equivFin (idx i)).symm i', hi'⟩
  have hPT : (⋃ i, P i) = T := by
    rw [hTdef]
    simp only [hPdef]
    rw [← hunionP]
    simp only [iUnion_finset_equivFin]
  have hPc : ∀ i, IsCompact (P i) := by
    intro i
    simp only [hPdef]
    exact isCompact_iUnion (fun i' => isCompact_closedBall _ _)
  have hPdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j) := by
    intro i j hij
    simp only [hPdef]
    rw [← iUnion_finset_equivFin (idx i) (fun j => Metric.closedBall (c j) (r j)),
      ← iUnion_finset_equivFin (idx j) (fun j => Metric.closedBall (c j) (r j))]
    exact hdisjP i j hij
  -- decomposition of `LK N (⋃ i, P i)` over the pieces
  obtain ⟨e, he⟩ := LK_decomposition (N := N) hN P hPc hPdisj
  -- transport to `T`
  let cT : LK N (⋃ i, P i) ≃ₗ[ℤ] LK N T := LKcongr (N := N) hPT
  have hcT : ∀ (a : LK N (⋃ i, P i)) (i : Fin m),
      lkMap (N := N) (hPi_sub i) (cT a) = lkMap (N := N) (Set.subset_iUnion P i) a := fun a i =>
    LinearMap.congr_fun (LKcongr_natural (N := N) hPT (Set.subset_iUnion P i) (hPi_sub i)) a
  -- per-piece localizations
  let hPi_iso : ∀ i : Fin m, LK N (P i) ≃ₗ[ℤ] LK N ({y i} : Set (EuclideanSpace ℝ (Fin N))) :=
    fun i => LinearEquiv.ofBijective (lkMap (N := N) (Set.singleton_subset_iff.mpr (hyP' i)))
      (lkMap_isIso_of_connected_balls (N := N) hN
        (fun i' : Fin (idx i).card => c ((Finset.equivFin (idx i)).symm i'))
        (fun i' : Fin (idx i).card => r ((Finset.equivFin (idx i)).symm i'))
        (fun i' => hr _) (hconnP' i) (y i) (hyP' i))
  -- the tupling map
  let Ψ : LK N S →ₗ[ℤ] ((i : Fin m) → LK N (P i)) :=
    piMap (N := N) (fun i : Fin m => (hPi_iso i).symm.toLinearMap.comp
      ((lkMap (N := N) (Set.singleton_subset_iff.mpr (⟨hyS i, hyP' i⟩ : y i ∈ S ∩ P i))).comp
        (lkMap (N := N) (Set.inter_subset_left : S ∩ P i ⊆ S))))
  refine ⟨cT.toLinearMap.comp (e.symm.toLinearMap.comp Ψ), ?_⟩
  apply LinearMap.ext
  intro a
  have hkey : Ψ (lkMap (N := N) hST a) = e (cT.symm a) := by
    funext i
    have h1' : S ∩ P i ⊆ S := Set.inter_subset_left
    have h2' : ({y i} : Set (EuclideanSpace ℝ (Fin N))) ⊆ S ∩ P i :=
      Set.singleton_subset_iff.mpr ⟨hyS i, hyP' i⟩
    show (hPi_iso i).symm (lkMap (N := N) h2' (lkMap (N := N) h1' (lkMap (N := N) hST a)))
      = e (cT.symm a) i
    rw [he i (cT.symm a), ← hcT (cT.symm a) i, LinearEquiv.apply_symm_apply cT a]
    rw [lkMap_apply_comp (N := N) h2' h1' hST a]
    rw [show lkMap (N := N) (h2'.trans (h1'.trans hST)) a
        = lkMap (N := N) ((Set.singleton_subset_iff.mpr (hyP' i)).trans (hPi_sub i)) a from
      congrArg (fun f : LK N T →ₗ[ℤ] LK N ({y i}) => f a)
        (lkMap_congr_proofs (N := N) _ _)]
    have hL : lkMap (N := N) ((Set.singleton_subset_iff.mpr (hyP' i)).trans (hPi_sub i))
        = (hPi_iso i).toLinearMap.comp (lkMap (N := N) (hPi_sub i)) := by
      rw [← lkMap_comp (N := N) (Set.singleton_subset_iff.mpr (hyP' i)) (hPi_sub i)]
      rfl
    rw [hL, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    exact LinearEquiv.symm_apply_apply (hPi_iso i) (lkMap (N := N) (hPi_sub i) a)
  show cT (e.symm (Ψ (lkMap (N := N) hST a))) = a
  rw [hkey, LinearEquiv.symm_apply_apply]
  exact LinearEquiv.apply_symm_apply cT a

end
end Work.Cohomology
