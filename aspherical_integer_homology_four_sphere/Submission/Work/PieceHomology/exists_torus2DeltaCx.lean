import Mathlib
import Submission.Work.PieceHomology.Basic
import Submission.Work.PieceHomology.torus2Data
import Submission.Work.PieceHomology.coprodIsoFreeMod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.PieceHomology

noncomputable section

/- Helper namespace for the proof of `exists_torus2DeltaCx`, kept separate so that the helper
names cannot collide with the (independently useful) comparison `torus2ChainIso` proved in
`Submission/Work/PieceHomology/torus2ChainIso.lean`. -/
namespace ExistsTorus2

/-! ## The comparison of the `Δ`-chain complex of `T²` with its matrix presentation

The `Δ`-chain groups of `torus2DeltaCx` are copowers `∐_{i : Fin n} ℤ`, while the matrix
presentation `torus2Cx.toChainComplex` uses the products `Fin n → ℤ`.  Everything below is
therefore stated in the copower presentation first (where the compositions typecheck
syntactically) and transported to the `ChainComplex` objects at the very end. -/

/-- The degreewise isomorphism, in the copower presentation. -/
def torus2CoprodComponent (k : ℕ) :
    (∐ (fun _ : Fin (torus2Card k) => Work.Homology.ZMod)) ≅
      ModuleCat.of ℤ (Fin (torus2Card k) → ℤ) :=
  coprodIsoFreeMod (torus2Card k)

/-- The same isomorphism between the actual `Δ`-chain groups and the matrix presentation. -/
def torus2ChainIsoComponent (k : ℕ) :
    torus2DeltaCx.chainX k ≅ torus2Cx.toChainComplex.X k :=
  coprodIsoFreeMod (torus2Card k)

theorem torus2ChainIsoComponent_hom (k : ℕ) :
    (torus2ChainIsoComponent k).hom
      = (coprodIsoFreeMod (torus2Card k)).hom := rfl

/-- The boundary of the `Δ`-chain complex, in the copower presentation. -/
def torus2ChainDcoprod (k : ℕ) :
    (∐ (fun _ : Fin (torus2Card (k+1)) => Work.Homology.ZMod)) ⟶
      (∐ (fun _ : Fin (torus2Card k) => Work.Homology.ZMod)) :=
  torus2DeltaCx.chainD k

/-- The boundary of a triangle, in matrix form: `∂T = a + b - c`. -/
theorem torus2Bd_one_mulVec (σ : Fin (torus2Card 2)) :
    (Matrix.toLin' ((torus2Bd 1).toMatrix)) (Pi.single σ 1)
      = ∑ j : Fin 3, (-1 : ℤ) ^ (j : ℕ) • Pi.single (torus2Face (k := 1) σ j) (1 : ℤ) := by
  funext i
  fin_cases σ <;> fin_cases i <;> decide

/-- The zero matrix is the zero linear map. -/
theorem toLin'_zero_mat {n m : ℕ} :
    Matrix.toLin' (0 : Matrix (Fin n) (Fin m) ℤ) = 0 := by
  ext x i
  simp

/-- `∂₀ = 0` in the copower presentation. -/
theorem torus2ChainDcoprod_zero : torus2ChainDcoprod 0 = 0 := by
  rw [torus2ChainDcoprod]
  exact torus2DeltaCx_chainD_zero

/-- A finite sum of `ofHom`s is the `ofHom` of the sum of the linear maps. -/
theorem ofHom_sum_fin {n : ℕ} {N : Type} [AddCommGroup N] [Module ℤ N]
    (f : Fin n → (ℤ →ₗ[ℤ] N)) :
    ModuleCat.ofHom (∑ i, f i) = ∑ i, ModuleCat.ofHom (f i) := by
  induction n with
  | zero => simp
  | succ m ih => rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ModuleCat.ofHom_add, ih]

/-- The boundary on the coproduct injections: `Σ.ι σ ≫ ∂ = ∑ j (-1)^j • Σ.ι (d_j σ)`. -/
theorem torus2ChainDcoprod_chainι (k : ℕ) (σ : Fin (torus2Card (k+1))) :
    (Sigma.ι (fun _ : Fin (torus2Card (k+1)) => Work.Homology.ZMod) σ
        ≫ torus2ChainDcoprod k)
      = ∑ j : Fin (k+2),
          (-1 : ℤ) ^ (j : ℕ) • Sigma.ι (fun _ : Fin (torus2Card k) => Work.Homology.ZMod)
            (torus2DeltaCx.face σ j) := by
  rw [torus2ChainDcoprod]
  exact DeltaHomology.DeltaCx.ι_chainD torus2DeltaCx k σ

/-- The coproduct injection of the boundary, pushed into the matrix presentation. -/
theorem torus2ChainDcoprod_chainι_comp (k : ℕ) (σ : Fin (torus2Card (k+1))) :
    ((Sigma.ι (fun _ : Fin (torus2Card (k+1)) => Work.Homology.ZMod) σ
        ≫ torus2ChainDcoprod k) ≫ (coprodIsoFreeMod (torus2Card k)).hom)
      = ∑ j : Fin (k+2),
          (-1 : ℤ) ^ (j : ℕ) •
            ModuleCat.ofHom (LinearMap.single ℤ (fun _ : Fin (torus2Card k) => ℤ)
              (torus2DeltaCx.face σ j)) := by
  rw [torus2ChainDcoprod_chainι, Preadditive.sum_comp]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Preadditive.zsmul_comp]
  congr 1
  exact coprodIsoFreeMod_ι (torus2Card k) (torus2DeltaCx.face σ j)

/-- **The differentials correspond**, in the copower presentation of the `Δ`-chain complex. -/
theorem torus2ChainIso_commCoprod (k : ℕ) :
    (torus2CoprodComponent (k+1)).hom
        ≫ ModuleCat.ofHom (Matrix.toLin' ((torus2Bd k).toMatrix))
      = torus2ChainDcoprod k ≫ (torus2CoprodComponent k).hom := by
  match k with
  | 0 =>
    rw [torus2Bd_zero_matrix, toLin'_zero_mat, ModuleCat.ofHom_zero, Limits.comp_zero,
      torus2ChainDcoprod_zero, Limits.zero_comp]
  | 1 =>
    simp only [Nat.reduceAdd, torus2CoprodComponent]
    apply Limits.Sigma.hom_ext (f := fun _ : Fin (torus2Card 2) => Work.Homology.ZMod)
    intro σ
    rw [← Category.assoc, coprodIsoFreeMod_ι, ← ModuleCat.ofHom_comp]
    rw [← Category.assoc]
    rw [torus2ChainDcoprod_chainι_comp]
    simp only [← Work.Subdivision.PolyCW.ModuleCat.ofHom_zsmul]
    rw [← ofHom_sum_fin]
    congr 1
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.single_apply]
    exact torus2Bd_one_mulVec σ
  | k + 2 =>
    apply CategoryTheory.Limits.IsZero.eq_of_src
      (DeltaHomology.isZero_chainX_of_dim_lt torus2DeltaCx (k := k+3) (by simp [torus2DeltaCx]))

/-- **The differentials correspond**, in the presentation of the two chain complexes. -/
theorem torus2ChainIso_comm (k : ℕ) :
    (torus2ChainIsoComponent (k+1)).hom ≫ torus2Cx.toChainComplex.d (k+1) k
      = torus2DeltaCx.chain.d (k+1) k ≫ (torus2ChainIsoComponent k).hom := by
  rw [torus2ChainIsoComponent_hom, torus2Cx_d, DeltaHomology.DeltaCx.chain_d]
  exact torus2ChainIso_commCoprod k

/-- **The `Δ`-chain complex of the torus is its matrix presentation.** -/
noncomputable def torus2ChainIsoAlt : torus2DeltaCx.chain ≅ torus2Cx.toChainComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun k => torus2ChainIsoComponent k)
    (fun i j hij => by
      obtain rfl : i = j + 1 := hij.symm
      exact torus2ChainIso_comm j)

end ExistsTorus2

open ExistsTorus2

/-! ## The main theorem -/

theorem exists_torus2DeltaCx :
    ∃ K : Work.DeltaHomology.DeltaCx,
      K.card 0 = 1 ∧ K.card 1 = 3 ∧ K.card 2 = 2 ∧
      (∀ k : ℕ, Nonempty (K.chain.homology k
        ≅ Work.HomologyMV.freeMod (Work.HomologyIso.rankT2 (k : ℤ)))) := by
  refine ⟨torus2DeltaCx, rfl, rfl, rfl, fun k => ?_⟩
  exact ⟨(Work.Certificates.SDR.homology_iso_of_iso torus2SDR torus2SDR_check
    torus2ChainIsoAlt.symm k).some ≪≫ Work.HomologyIso.freeModCast (torus2B_eq_rankT2 k)⟩

end

end Work.PieceHomology
