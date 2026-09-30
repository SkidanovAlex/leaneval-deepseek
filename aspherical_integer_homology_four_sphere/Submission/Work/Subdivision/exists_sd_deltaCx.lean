/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SdChain
import Submission.Work.DeltaHomology.Chain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# The subdivision of a `PolyCW` as a `Δ`-complex

For every finite polyhedral CW complex `P` there is a finite `Δ`-complex
`Work.Subdivision.PolyCW.sdCx P` whose `k`-simplices are the strictly increasing
`(k+1)`-tuples of cells of `P`, and whose `i`-th face map deletes the `i`-th
vertex.  Its `Δ`-chain complex is canonically isomorphic to the barycentric
subdivision `P.sdChain` of `P` (the order complex of the cell poset).

The isomorphism is degreewise the identification of the free `ℤ`-module on the
`k`-simplices with the coproduct of `card k` copies of `ℤ`.

## Main result

* `Work.Subdivision.exists_sd_deltaCx`.
-/

namespace Work.Subdivision

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The semi-simplicial identity for the order complex -/

/-- The `Δ`-identity in the normal form required by `DeltaCx.face_face`:
deleting the `(j+1)`-st vertex and then the `i`-th vertex agrees with deleting
the `i`-th and then the `j`-th, for `i ≤ j`. -/
theorem Simplex.face_face_succ {α : Type*} [Preorder α] {k : ℕ} (i j : Fin (k + 2))
    (hij : i ≤ j) (σ : Simplex α (k + 2)) :
    Simplex.face i (Simplex.face (Fin.succ j) σ) =
      Simplex.face j (Simplex.face (Fin.castSucc i) σ) := by
  have h1 : i.predAbove (Fin.succ j) = j := Fin.predAbove_succ_of_le i j hij
  have h2 : (Fin.succ j).succAbove i = Fin.castSucc i := by
    apply Fin.succAbove_of_castSucc_lt
    simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc]
    omega
  rw [Simplex.face_face i (Fin.succ j) σ, h1, h2]

namespace PolyCW

/-! ## The `Δ`-complex of the subdivision -/

variable (P : PolyCW.{0})

/-- The number of `k`-simplices of the barycentric subdivision of `P`. -/
noncomputable def sdCard (k : ℕ) : ℕ := Fintype.card (Simplex P.Cell k)

/-- The simplices of the subdivision, labelled by `Fin (sdCard P k)`. -/
noncomputable def sdEquiv (k : ℕ) : Fin (sdCard P k) ≃ Simplex P.Cell k :=
  (Fintype.equivFin (Simplex P.Cell k)).symm

/-- In a strictly increasing tuple of cells the `i`-th cell has dimension at
least `i`. -/
theorem le_dim_apply {k : ℕ} (σ : Simplex P.Cell k) (i : Fin (k + 1)) :
    (i : ℕ) ≤ P.dim (σ i) := by
  induction i using Fin.induction with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hlt : P.dim (σ i.castSucc) < P.dim (σ i.succ) :=
      P.dim_lt' (σ.strictMono Fin.castSucc_lt_succ)
    simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢
    omega

/-- There are no simplices of the subdivision above the dimension of `P`. -/
theorem isEmpty_simplex_of_lt {k : ℕ} (h : P.maxDim < k) : IsEmpty (Simplex P.Cell k) :=
  ⟨fun σ => by
    have h1 := P.le_dim_apply σ (Fin.last k)
    have h2 := P.dim_le_maxDim (σ (Fin.last k))
    simp only [Fin.val_last] at h1
    omega⟩

theorem sdCard_eq_zero {k : ℕ} (h : P.maxDim < k) : sdCard P k = 0 :=
  Fintype.card_eq_zero_iff.mpr (P.isEmpty_simplex_of_lt h)

/-- The `Δ`-complex underlying the barycentric subdivision of `P`. -/
noncomputable abbrev sdCx : DeltaHomology.DeltaCx where
  dim := P.maxDim
  card := sdCard P
  face := fun {k} σ i => (sdEquiv P k).symm (Simplex.face i (sdEquiv P (k + 1) σ))
  face_face := fun {k} σ i j hij => by
    refine congrArg (sdEquiv P k).symm ?_
    simp only [Equiv.apply_symm_apply]
    exact Simplex.face_face_succ i j hij (sdEquiv P (k + 2) σ)
  card_eq_zero := fun k h => sdCard_eq_zero P h

@[simp] theorem sdCx_dim : (sdCx P).dim = P.maxDim := rfl

@[simp] theorem sdCx_card (k : ℕ) : (sdCx P).card k = sdCard P k := rfl

theorem sdCx_face (k : ℕ) (σ : Fin (sdCard P (k + 1))) (i : Fin (k + 2)) :
    (sdCx P).face σ i = (sdEquiv P k).symm (Simplex.face i (sdEquiv P (k + 1) σ)) := rfl

/-! ## The identification of the chain groups -/

/-- For a `ℤ`-linear map out of `ℤ`, evaluation at `c` is `c` times evaluation
at `1`. -/
theorem LinearMap.int_apply_eq_smul_one {M : Type*} [AddCommMonoid M] [Module ℤ M]
    (f : ℤ →ₗ[ℤ] M) (c : ℤ) : f c = c • f 1 := by
  conv_lhs => rw [show c = c • (1 : ℤ) from by rw [smul_eq_mul, mul_one]]
  rw [LinearMap.map_smul]

/-- `ModuleCat.ofHom` commutes with finite sums of linear maps. -/
theorem ModuleCat.ofHom_finset_sum {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] {ι : Type} (s : Finset ι) (f : ι → M →ₗ[ℤ] N) :
    ModuleCat.ofHom (∑ i ∈ s, f i) = ∑ i ∈ s, ModuleCat.ofHom (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [ModuleCat.ofHom_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ModuleCat.ofHom_add, ih]

/-- `ModuleCat.ofHom` commutes with `ℤ`-scalar multiples of linear maps. -/
theorem ModuleCat.ofHom_zsmul {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (z : ℤ) (f : M →ₗ[ℤ] N) :
    ModuleCat.ofHom (z • f) = z • ModuleCat.ofHom f := rfl

variable {n : ℕ} {ι : Type}

/-- If `ι` is finite and identified with `Fin n` by `e`, then the free
`ℤ`-module on `ι` (i.e. the coproduct of `n` copies of `ℤ`) is `ι →₀ ℤ`. -/
noncomputable def freeIso (e : Fin n ≃ ι) :
    (∐ (fun _ : Fin n => Homology.ZMod)) ≅ ModuleCat.of ℤ (ι →₀ ℤ) where
  hom := Sigma.desc (fun a => ModuleCat.ofHom (Finsupp.lsingle (e a) : ℤ →ₗ[ℤ] (ι →₀ ℤ)))
  inv := ModuleCat.ofHom (Finsupp.linearCombination ℤ
    (fun b => (Sigma.ι (fun _ : Fin n => Homology.ZMod) (e.symm b)) (1 : ℤ)))
  hom_inv_id := by
    apply Sigma.hom_ext
    intro a
    rw [← Category.assoc, Sigma.ι_comp_desc, Category.comp_id]
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
    apply LinearMap.ext
    intro c
    rw [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.linearCombination_single]
    rw [LinearMap.int_apply_eq_smul_one
      (ModuleCat.Hom.hom (Sigma.ι (fun _ : Fin n => Homology.ZMod) a)) c]
    congr 1
    simp only [Equiv.symm_apply_apply]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    apply Finsupp.lhom_ext
    intro a b
    rw [LinearMap.comp_apply, Finsupp.linearCombination_single]
    rw [← LinearMap.int_apply_eq_smul_one]
    rw [← LinearMap.comp_apply]
    rw [← ModuleCat.hom_comp, Sigma.ι_comp_desc, ModuleCat.hom_ofHom]
    rw [Finsupp.lsingle_apply, Equiv.apply_symm_apply]
    rfl

variable (P : PolyCW.{0})

/-- The degreewise isomorphism between the `Δ`-chain groups of `sdCx P` and the
subdivision chain complex. -/
noncomputable def sdIsoComponent (k : ℕ) :
    (sdCx P).chainX k ≅ ModuleCat.of ℤ (chainMod P.Cell k) :=
  freeIso (sdEquiv P k)

theorem sdIsoComponent_hom (k : ℕ) :
    (sdIsoComponent P k).hom =
      Sigma.desc (fun a => ModuleCat.ofHom
        (Finsupp.lsingle (sdEquiv P k a) : ℤ →ₗ[ℤ] (Simplex P.Cell k →₀ ℤ))) :=
  rfl

theorem sdCx_faceMap_eq (k : ℕ) (i : Fin (k + 2)) :
    (sdCx P).faceMap i = Sigma.desc (fun σ : Fin (sdCard P (k + 1)) =>
      (sdCx P).chainι k ((sdCx P).face σ i)) :=
  rfl

/-- `faceLM i` composed with the singleton at `x` is the singleton at the `i`-th
face of `x`. -/
theorem faceLM_comp_lsingle {k : ℕ} (i : Fin (k + 2)) (x : Simplex P.Cell (k + 1)) :
    faceLM (α := P.Cell) i ∘ₗ Finsupp.lsingle x = Finsupp.lsingle (Simplex.face i x) := by
  apply LinearMap.ext
  intro c
  rw [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.lsingle_apply]
  rw [show (Finsupp.single x c) = c • (Finsupp.single x 1) from by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
  rw [LinearMap.map_smul, faceLM_single, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The `i`-th face maps of `sdCx P` intertwine the two chain differentials. -/
theorem sdCx_faceMap_natural (k : ℕ) (i : Fin (k + 2)) :
    (sdIsoComponent P (k + 1)).hom ≫ ModuleCat.ofHom (faceLM (α := P.Cell) i)
      = (sdCx P).faceMap i ≫ (sdIsoComponent P k).hom := by
  simp only [sdIsoComponent_hom, sdCx_faceMap_eq]
  apply Sigma.hom_ext
  intro σ
  rw [← Category.assoc, Sigma.ι_comp_desc]
  rw [← Category.assoc, Sigma.ι_comp_desc]
  rw [Sigma.ι_comp_desc]
  rw [← ModuleCat.ofHom_comp]
  rw [show (sdEquiv P k) ((sdCx P).face σ i)
        = Simplex.face i (sdEquiv P (k + 1) σ) from by
    rw [sdCx_face, Equiv.apply_symm_apply]]
  exact congrArg ModuleCat.ofHom (faceLM_comp_lsingle P i (sdEquiv P (k + 1) σ))

/-- The subdivision differential expressed with `ModuleCat.ofHom`. -/
theorem sdCx_ofHom_D (k : ℕ) :
    ModuleCat.ofHom (D (α := P.Cell) k) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ModuleCat.ofHom (faceLM (α := P.Cell) i) := by
  rw [D, ModuleCat.ofHom_finset_sum]
  exact Finset.sum_congr rfl fun i _ => ModuleCat.ofHom_zsmul _ _

/-- The chain differentials of `sdCx P` and of the subdivision agree. -/
theorem sdCx_chainD_natural (k : ℕ) :
    (sdIsoComponent P (k + 1)).hom ≫ ModuleCat.ofHom (D (α := P.Cell) k)
      = (sdCx P).chainD k ≫ (sdIsoComponent P k).hom := by
  rw [sdCx_ofHom_D, DeltaHomology.DeltaCx.chainD]
  rw [Preadditive.comp_sum]
  simp only [Preadditive.comp_zsmul, sdCx_faceMap_natural]
  rw [Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp]

/-- The chain complex of `sdCx P` is the barycentric subdivision of `P`. -/
noncomputable def sdCxChainIso : (sdCx P).chain ≅ PolyCW.sdChain P :=
  HomologicalComplex.Hom.isoOfComponents (fun k => sdIsoComponent P k) (fun i j hij => by
    obtain rfl : i = j + 1 := hij.symm
    rw [PolyCW.sdChain_d, DeltaHomology.DeltaCx.chain_d]
    exact sdCx_chainD_natural P j)

end PolyCW

end

/-- Every finite polyhedral CW complex `P` has a `Δ`-complex model whose
`Δ`-chain complex is isomorphic to the barycentric subdivision `P.sdChain`. -/
theorem exists_sd_deltaCx (P : Work.Subdivision.PolyCW) :
    ∃ K : Work.DeltaHomology.DeltaCx,
      Nonempty (K.chain ≅ Work.Subdivision.PolyCW.sdChain P) :=
  ⟨PolyCW.sdCx P, ⟨PolyCW.sdCxChainIso P⟩⟩

end Work.Subdivision
