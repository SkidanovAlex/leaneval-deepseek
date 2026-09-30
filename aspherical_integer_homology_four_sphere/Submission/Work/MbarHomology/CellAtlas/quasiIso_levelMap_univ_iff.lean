import Mathlib
import Submission.Work.MbarHomology.CellAtlas.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The level `(n, univ)` is the level `(n+1, ∅)`

The refined filtration `InD n E` of `Submission.Work.MbarHomology.CellAtlas.Core`
records the cells of `C` of dimension `≤ n` together with the `(n+1)`-cells listed
in `E`.  For `E = univ` it therefore consists exactly of the cells of dimension
`≤ n + 1`, which is the same level as `InD (n+1) ∅`.  Hence the two subcomplex
data `CSD C n univ` and `CSD C (n+1) ∅` (on the `C`-side) and `KSD A n univ` and
`KSD A (n+1) ∅` (on the `K`-side) coincide, and the restricted maps
`levelMap A h n univ` and `levelMap A h (n+1) ∅` differ only in the proof of the
compatibility condition; transporting along the equalities of subcomplex data
(`Work.Subdivision.SubData.quasiIso_of_sub_data_eq`) identifies their
quasi-isomorphism statements.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.MbarHomology

open CategoryTheory

noncomputable section

namespace CellAtlas

variable {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW}
  {C : Work.Certificates.FinChainCx}

/-! ## The refinement predicate at the two extreme levels -/

/-- A cell of `C` lies in the level `(n, univ)` if and only if it lies in the
level `(n+1, ∅)`: both mean dimension at most `n+1`. -/
theorem inD_univ_iff_inD_empty_succ {n : ℕ} (c : CellIdx C) :
    InD (C := C) n (Finset.univ : Finset (Fin (C.dim (n + 1)))) c ↔
      InD (C := C) (n + 1) (∅ : Finset (Fin (C.dim (n + 2)))) c := by
  obtain ⟨k, e⟩ := c
  rw [inD_univ_iff, inD_empty_iff]

/-! ## The two filtrations of the `C`-side -/

/-- The submodule of `C`-chains supported on a level depends only on the level
as a predicate on cells of `C`. -/
theorem CMod_congr {m n : ℕ} {E : Finset (Fin (C.dim (m + 1)))}
    {E' : Finset (Fin (C.dim (n + 1)))} (k : ℕ)
    (h : ∀ e : Fin (C.dim k),
      InD (C := C) m E ⟨k, e⟩ ↔ InD (C := C) n E' ⟨k, e⟩) :
    CMod C m E k = CMod C n E' k := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_CMod] at hx ⊢
    exact fun b hb => hx b (fun hc => hb ((h b).mp hc))
  · intro x hx
    rw [mem_CMod] at hx ⊢
    exact fun b hb => hx b (fun hc => hb ((h b).mpr hc))

theorem CMod_univ_eq_CMod_empty_succ (n k : ℕ) :
    CMod C n (Finset.univ : Finset (Fin (C.dim (n + 1)))) k =
      CMod C (n + 1) (∅ : Finset (Fin (C.dim (n + 2)))) k :=
  CMod_congr (C := C) (m := n) (n := n + 1)
    (E := (Finset.univ : Finset (Fin (C.dim (n + 1)))))
    (E' := (∅ : Finset (Fin (C.dim (n + 2))))) k
    fun e => inD_univ_iff_inD_empty_succ ⟨k, e⟩

/-- The two extreme levels define the same subcomplex data on the `C`-side. -/
theorem CSD_univ_eq_CSD_empty_succ (n : ℕ) :
    CSD (C := C) n (Finset.univ : Finset (Fin (C.dim (n + 1)))) =
      CSD (C := C) (n + 1) (∅ : Finset (Fin (C.dim (n + 2)))) :=
  Work.Subdivision.SubData.ext fun k => CMod_univ_eq_CMod_empty_succ (C := C) n k

/-! ## The two filtrations of the `K`-side -/

theorem kSet_univ_eq_kSet_empty_succ (A : CellAtlas K P C) (n k : ℕ) :
    kSet A n (Finset.univ : Finset (Fin (C.dim (n + 1)))) k =
      kSet A (n + 1) (∅ : Finset (Fin (C.dim (n + 2)))) k := by
  ext y
  simp only [kSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, (inD_univ_iff_inD_empty_succ (A.car σ)).mp hσ, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, (inD_univ_iff_inD_empty_succ (A.car σ)).mpr hσ, rfl⟩

theorem kSup_univ_eq_kSup_empty_succ (A : CellAtlas K P C) (n k : ℕ) :
    kSup A n (Finset.univ : Finset (Fin (C.dim (n + 1)))) k =
      kSup A (n + 1) (∅ : Finset (Fin (C.dim (n + 2)))) k := by
  rw [kSup, kSup, kSet_univ_eq_kSet_empty_succ]

theorem KMod_univ_eq_KMod_empty_succ (A : CellAtlas K P C) (n k : ℕ) :
    KMod A n (Finset.univ : Finset (Fin (C.dim (n + 1)))) k =
      KMod A (n + 1) (∅ : Finset (Fin (C.dim (n + 2)))) k := by
  rw [KMod, KMod, kSup_univ_eq_kSup_empty_succ]

/-- The two extreme levels define the same subcomplex data on the `K`-side. -/
theorem KSD_univ_eq_KSD_empty_succ (A : CellAtlas K P C) (n : ℕ) :
    KSD A n (Finset.univ : Finset (Fin (C.dim (n + 1)))) =
      KSD A (n + 1) (∅ : Finset (Fin (C.dim (n + 2)))) :=
  Work.Subdivision.SubData.ext fun k => KMod_univ_eq_KMod_empty_succ A n k

/-! ## The target -/

theorem quasiIso_levelMap_univ_iff {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW} {C : Work.Certificates.FinChainCx} (A : Work.MbarHomology.CellAtlas K P C) (h : A.BoundaryCompat) (n : ℕ) : QuasiIso (Work.MbarHomology.CellAtlas.levelMap A h n (Finset.univ : Finset (Fin (C.dim (n + 1))))) ↔ QuasiIso (Work.MbarHomology.CellAtlas.levelMap A h (n + 1) (∅ : Finset (Fin (C.dim (n + 2))))) :=
  (Work.Subdivision.SubData.quasiIso_of_sub_data_eq
      (CSD (C := C) n (Finset.univ : Finset (Fin (C.dim (n + 1)))))
      (CSD (C := C) (n + 1) (∅ : Finset (Fin (C.dim (n + 2)))))
      (KSD A n (Finset.univ : Finset (Fin (C.dim (n + 1)))))
      (KSD A (n + 1) (∅ : Finset (Fin (C.dim (n + 2)))))
      (CSD_univ_eq_CSD_empty_succ (C := C) n).symm
      (KSD_univ_eq_KSD_empty_succ A n).symm
      (A.zMap h) (levelHf A h n (Finset.univ)) (levelHf A h (n + 1) ∅)).symm

end CellAtlas

end

end Work.MbarHomology
