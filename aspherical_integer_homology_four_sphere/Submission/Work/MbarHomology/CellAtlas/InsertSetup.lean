/-
# The cell-by-cell step of the atlas filtration: set-up

This file collects the auxiliary definitions used in
`quasiIso_levelMap_insert.lean`, the induction step of the cell-by-cell
refinement of the atlas filtration.  The relative subcomplexes carried by a
single new cell are `CellAtlas.CPiece`/`CellAtlas.KPiece` (in `Core.lean`); here
we build the comparison map between the two quotient complexes.

The atlas chain complex of `K` is identified with the free module
`kMod K k = ℤ^{(Fin (K.card k))}` along `CellAtlas.kIso`.  On that model the
piece carried by the new `(n+1)`-cell (indexed by `f₀`) is spanned by the
simplices whose carrier is `⟨n+1, f₀⟩`, i.e. — through `lift` — by the simplices
of the order complex of `P` with top vertex `root (n+1) f₀`.  The linear map
`kPsi` is the resulting comparison map from the order complex of the root face
to the chains of `K`; its key properties are that it carries the local chains
`leSub` into `kSup (insert f₀ E)`, that it kills `ltSub`, and that it is a chain
map up to the subcomplex `kSup E`.
-/
import Mathlib
import Submission.Work.MbarHomology.CellAtlas.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.MbarHomology

open CategoryTheory

noncomputable section

namespace CellAtlas

namespace Insert

-- As in `Core.lean`: pin the module structures on free modules.
attribute [local instance 2000] Pi.Function.module Finsupp.module

universe u

variable {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW.{u}}
  {C : Work.Certificates.FinChainCx}

/-! ## The lift of the atlas -/

theorem liftEquiv_apply (A : CellAtlas K P C) (k n : ℕ) (e : Fin (C.dim n))
    (σ : Fin (K.card k)) (h : A.car σ = ⟨n, e⟩) :
    (A.liftEquiv k n e) ⟨σ, h⟩ =
      (⟨A.lift σ, by rw [A.lift_top σ, h]⟩ :
        {s : Work.Subdivision.Simplex P.Cell k // s (Fin.last k) = A.root n e}) := rfl

/-- The inverse of `liftEquiv` on a simplex of the subdivision with top vertex the
root of the corresponding carrier. -/
theorem lift_liftEquiv_symm (A : CellAtlas K P C) (k n : ℕ) (e : Fin (C.dim n))
    (s : Work.Subdivision.Simplex P.Cell k) (h : s (Fin.last k) = A.root n e) :
    A.lift ((A.liftEquiv k n e).symm ⟨s, h⟩).1 = s :=
  congrArg Subtype.val (Equiv.apply_symm_apply (A.liftEquiv k n e) ⟨s, h⟩)

theorem car_liftEquiv_symm (A : CellAtlas K P C) (k n : ℕ) (e : Fin (C.dim n))
    (s : Work.Subdivision.Simplex P.Cell k) (h : s (Fin.last k) = A.root n e) :
    A.car ((A.liftEquiv k n e).symm ⟨s, h⟩).1 = ⟨n, e⟩ :=
  ((A.liftEquiv k n e).symm ⟨s, h⟩).2

/-- The inverse of `liftEquiv` at the lift of a simplex with the given carrier is
that simplex. -/
theorem liftEquiv_symm_lift (A : CellAtlas K P C) (k n : ℕ) (e : Fin (C.dim n))
    (σ : Fin (K.card k)) (h : A.car σ = ⟨n, e⟩) :
    (A.liftEquiv k n e).symm
        ⟨A.lift σ, by rw [A.lift_top σ, h]⟩ = ⟨σ, h⟩ := by
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext rfl

/-- The lift is injective on simplices with the same carrier. -/
theorem lift_injective_of_car_eq (A : CellAtlas K P C) {k n : ℕ} {e : Fin (C.dim n)}
    {σ₁ σ₂ : Fin (K.card k)} (h₁ : A.car σ₁ = ⟨n, e⟩) (h₂ : A.car σ₂ = ⟨n, e⟩)
    (h : A.lift σ₁ = A.lift σ₂) : σ₁ = σ₂ := by
  have hinj := (A.lift_bij k n e).1
  have hsub : (⟨σ₁, h₁⟩ : {σ : Fin (K.card k) // A.car σ = ⟨n, e⟩}) = ⟨σ₂, h₂⟩ :=
    hinj (by apply Subtype.ext; exact h)
  exact congrArg Subtype.val hsub

/-! ## The refinement predicate -/

/-- A cell of dimension `n+1` lies in the level `E` exactly when its index does. -/
theorem inD_succ_iff {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))} (f : Fin (C.dim (n + 1))) :
    InD (C := C) n E ⟨n + 1, f⟩ ↔ f ∈ E := by
  constructor
  · rintro (h | ⟨f', hf', he⟩)
    · exact absurd h (by simp)
    · have h2 : f = f' := eq_of_heq (Sigma.mk.inj_iff.mp he).2
      rw [← h2] at hf'
      exact hf'
  · exact fun hf => Or.inr ⟨f, hf, rfl⟩

theorem inD_insert_iff_of_ne {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))}
    {f₀ : Fin (C.dim (n + 1))} {k : ℕ} (hk : k ≠ n + 1) (b : Fin (C.dim k)) :
    InD (C := C) n (insert f₀ E) ⟨k, b⟩ ↔ InD (C := C) n E ⟨k, b⟩ := by
  rw [inD_insert_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd (congrArg (fun c : CellIdx C => c.1) h) hk
  · exact Or.inl

/-- The `f₀`-th generator of the `C`-chains lies in the new level. -/
theorem cGen_mem_CMod_insert {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))}
    (f₀ : Fin (C.dim (n + 1))) :
    cGen C (n + 1) f₀ ∈ CMod C n (insert f₀ E) (n + 1) := by
  rw [mem_CMod]
  intro b hb
  show (Pi.single f₀ (1 : ℤ) : Fin (C.dim (n + 1)) → ℤ) b = 0
  have hbf : b ≠ f₀ := fun h =>
    hb ((inD_succ_iff (E := insert f₀ E) b).mpr (by rw [h]; exact Finset.mem_insert_self f₀ E))
  exact Pi.single_eq_of_ne (M := fun _ => ℤ) (i := f₀) (i' := b) hbf (1 : ℤ)

/-- In degree `n+1` the new level is everything. -/
theorem CMod_insert_eq_top_of_le {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))}
    {f₀ : Fin (C.dim (n + 1))} {k : ℕ} (hk : k ≤ n) :
    CMod C n (insert f₀ E) k = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  rw [mem_CMod]
  intro b hb
  exact absurd (Or.inl hk) hb

/-! ## The comparison map on the free model -/

/-- The basis vector of the free model attached to a simplex `s` of the
subdivision whose top vertex is the root of the new cell; zero otherwise. -/
noncomputable def kGen (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1)))
    (k : ℕ) (s : Work.Subdivision.Simplex P.Cell k) : kMod K k :=
  if h : s (Fin.last k) = A.root (n + 1) f₀ then
    Finsupp.single ((A.liftEquiv k (n + 1) f₀).symm ⟨s, h⟩).1 (1 : ℤ)
  else 0

/-- The comparison map, on the free model, from the order complex of the face
`root (n+1) f₀` to the `k`-th chains of `K`. -/
noncomputable def kPsi (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1)))
    (k : ℕ) : Work.Subdivision.chainMod P.Cell k →ₗ[ℤ] kMod K k :=
  Finsupp.linearCombination ℤ (kGen A n f₀ k)

theorem kPsi_sdElem (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1)))
    (k : ℕ) (s : Work.Subdivision.Simplex P.Cell k) :
    kPsi A n f₀ k (Finsupp.single s (1 : ℤ)) = kGen A n f₀ k s := by
  rw [kPsi, Finsupp.linearCombination_single, one_smul]

theorem kGen_eq_zero (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1)))
    (k : ℕ) (s : Work.Subdivision.Simplex P.Cell k)
    (h : s (Fin.last k) ≠ A.root (n + 1) f₀) : kGen A n f₀ k s = 0 :=
  dif_neg h

theorem kGen_eq_single (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1)))
    (k : ℕ) (s : Work.Subdivision.Simplex P.Cell k)
    (h : s (Fin.last k) = A.root (n + 1) f₀) :
    kGen A n f₀ k s = Finsupp.single ((A.liftEquiv k (n + 1) f₀).symm ⟨s, h⟩).1 (1 : ℤ) :=
  dif_pos h

theorem kGen_mem_kSup_insert (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (s : Work.Subdivision.Simplex P.Cell k) :
    kGen A n f₀ k s ∈ kSup A n (insert f₀ E) k := by
  by_cases h : s (Fin.last k) = A.root (n + 1) f₀
  · rw [kGen_eq_single A n f₀ k s h]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    rw [car_liftEquiv_symm, inD_insert_iff]
    exact Or.inr rfl
  · rw [kGen_eq_zero A n f₀ k s h]
    exact Submodule.zero_mem _

theorem kPsi_mem_kSup_insert (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (z : Work.Subdivision.chainMod P.Cell k) :
    kPsi A n f₀ k z ∈ kSup A n (insert f₀ E) k := by
  rw [kPsi, Finsupp.linearCombination_apply]
  rw [Finsupp.sum]
  refine Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ ?_
  exact kGen_mem_kSup_insert A n E f₀ k s

theorem kPsi_ltSub_eq_zero (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1)))
    (k : ℕ) {z : Work.Subdivision.chainMod P.Cell k}
    (hz : z ∈ Work.Subdivision.PolyCW.ltSub P (A.root (n + 1) f₀) k) :
    kPsi A n f₀ k z = 0 := by
  have hsupp := Work.Subdivision.PolyCW.ltSub_support (P := P) hz
  rw [kPsi, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [kGen_eq_zero A n f₀ k s (ne_of_lt (hsupp s hs (Fin.last k))), smul_zero]

/-- The coefficient of `rootCoeff` is the coefficient of the subdivision chain. -/
theorem rootCoeff_def (A : CellAtlas K P C) (k : ℕ) (e : Fin (C.dim k))
    (s : Work.Subdivision.Simplex P.Cell k) :
    A.rootCoeff k e s =
      (Work.Subdivision.PolyCW.subdivCell P k ⟨A.root k e, A.dim_root k e⟩) s := rfl

/-- The comparison map expanded as a sum over the simplices. -/
theorem kPsi_sum (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1)))
    (k : ℕ) (z : Work.Subdivision.chainMod P.Cell k) :
    kPsi A n f₀ k z =
      ∑ s : Work.Subdivision.Simplex P.Cell k, z s • kGen A n f₀ k s := by
  rw [kPsi, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finset.sum_subset (Finset.subset_univ _) fun s _ hs => by
    rw [Finsupp.notMem_support_iff.mp hs, zero_smul]]

/-- The comparison map sends the subdivision chain of the new cell to the image
of the corresponding generator of `C` under the atlas map. -/
theorem kPsi_subdivCell (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1))) :
    kPsi A n f₀ (n + 1)
        (Work.Subdivision.PolyCW.subdivCell P (n + 1)
          ⟨A.root (n + 1) f₀, A.dim_root (n + 1) f₀⟩) =
      kz A (n + 1) f₀ := by
  rw [kPsi_sum, kz_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : s (Fin.last (n + 1)) = A.root (n + 1) f₀
  · rw [kGen_eq_single A n f₀ (n + 1) s h, dif_pos h, rootCoeff_def]
  · rw [kGen_eq_zero A n f₀ (n + 1) s h, dif_neg h, smul_zero]

/-! ## The `C`-side generator of the piece -/

/-- The class of the new cell in the `C`-piece. -/
noncomputable def cPieceGen (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) :
    (CPiece (C := C) n E f₀).quot.X (n + 1) :=
  Submodule.Quotient.mk
    (⟨cGen C (n + 1) f₀, cGen_mem_CMod_insert (C := C) f₀⟩ :
      ↥(CMod C n (insert f₀ E) (n + 1)))

/-- The coefficient map `ℤ → (CPiece).quot.X (n+1)`, `1 ↦ [new cell]`. -/
noncomputable def cPieceCoeffF (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) :
    Work.Subdivision.unitMod.{0} ⟶ (CPiece (C := C) n E f₀).quot.X (n + 1) :=
  Work.Subdivision.PolyCW.spanMap (cPieceGen A n E f₀)

/-- The `K`-side comparison map, transported to the chain module of `K`. -/
noncomputable def kPsiK (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1)))
    (k : ℕ) : Work.Subdivision.chainMod P.Cell k →ₗ[ℤ] K.chainX k :=
  ((kIso K k).inv.hom).comp (kPsi A n f₀ k)

theorem kSup_le_insert (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ) :
    kSup A n E k ≤ kSup A n (insert f₀ E) k := by
  intro y hy
  rw [mem_kSup] at hy ⊢
  exact fun σ hσ => InD.mono (Finset.subset_insert f₀ E) (hy σ hσ)

theorem kPsiK_apply (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1)))
    (k : ℕ) (z : Work.Subdivision.chainMod P.Cell k) :
    kPsiK A n f₀ k z = (kIso K k).inv (kPsi A n f₀ k z) := rfl

end Insert

end CellAtlas

end

end Work.MbarHomology
