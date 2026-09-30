/-
# The pieces of a stage step

For a `PolyCW` `P`, a cell `a` and a *stage* `T` of `a` (`PolyCW.IsStage`, `SupportCx.lean`),
the two support filtrations of `SupportCx.lean` refine as

* `cellPieceS P hdd T a h` — the relative cellular subcomplex of `cellS (insert a T)` over
  `cellS T`, whose only non-zero chain module is (the class of) the new cell `a`,
* `sdPieceS P T a h` — the relative subdivided subcomplex, whose chains are the simplices
  containing the new vertex `a`.

The maps induced by the subdivision on these pieces are the local maps of the cell `a`: the
successive quotients are `unitCx (dim a)` and the local complex `locCx a`, and the induced map is
`locMap a` up to these identifications.  This is the support-form analogue of
`Work.Subdivision.Piece`/`PieceQuot`/`PieceIso`/`PieceSquare`, and it is what makes the cell-by-cell
induction of the localized (star) filtration work.
-/
import Mathlib
import Submission.Work.MbarHomology.Local.SupportCx
import Submission.Work.Subdivision.PieceSquare
import Submission.Work.Subdivision.SubDataEq
import Submission.Work.Subdivision.ComapChainIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

namespace PolyCW

variable (P : PolyCW.{u})

set_option allowUnsafeReducibility true
attribute [local reducible] cellChain sdChain cellS sdS cellSMod sdSMod leSub ltSub
  SubData.chain SubData.quot SubData.quotOf PolyCW.icF PolyCW.ioF

/-! ### The relative subcomplexes of a stage step -/

/-- The cellular piece carried by the new cell `a`. -/
noncomputable abbrev cellPieceS (hdd : P.HasDdZero) {T : Finset P.Cell} (a : P.Cell)
    (h : IsStage P a T) : SubData ((cellS P hdd (insert a T) h.insert_lower).chain) :=
  SubData.comapChain (cellS P hdd (insert a T) h.insert_lower) (cellSMod P hdd T)
    (fun k => cellSMod_mono P hdd (Finset.subset_insert a T) k)
    (cellS P hdd T h.lower).d_mem

/-- The subdivided piece carried by the new cell `a`. -/
noncomputable abbrev sdPieceS {T : Finset P.Cell} (a : P.Cell) (h : IsStage P a T) :
    SubData ((sdS P (insert a T)).chain) :=
  SubData.comapChain (sdS P (insert a T)) (sdSMod P T)
    (fun k => sdSMod_mono P (Finset.subset_insert a T) k)
    (sdS P T).d_mem

/-- The subdivision restricted to the stage `insert a T`. -/
noncomputable def levelMapS (hdd : P.HasDdZero) (haug : P.HasAugZero) {T : Finset P.Cell}
    (a : P.Cell) (h : IsStage P a T) :
    (cellS P hdd (insert a T) h.insert_lower).chain ⟶ (sdS P (insert a T)).chain :=
  (cellS P hdd (insert a T) h.insert_lower).restrictMap (sdS P (insert a T)) (subdiv P hdd haug)
    (subdivCpt_mem_S P hdd haug h.insert_lower)

/-- The subdivision restricted to the stage `T` itself. -/
noncomputable def levelMapS' (hdd : P.HasDdZero) (haug : P.HasAugZero) {T : Finset P.Cell}
    (a : P.Cell) (h : IsStage P a T) :
    (cellS P hdd T h.lower).chain ⟶ (sdS P T).chain :=
  (cellS P hdd T h.lower).restrictMap (sdS P T) (subdiv P hdd haug)
    (subdivCpt_mem_S P hdd haug h.lower)

@[simp] theorem levelMapS_f (hdd : P.HasDdZero) (haug : P.HasAugZero) {T : Finset P.Cell}
    (a : P.Cell) (h : IsStage P a T) (k : ℕ) :
    (levelMapS P hdd haug a h).f k =
      (cellS P hdd (insert a T) h.insert_lower).restrictCptMap (sdS P (insert a T))
        (subdiv P hdd haug) (subdivCpt_mem_S P hdd haug h.insert_lower) k := rfl

@[simp] theorem levelMapS'_f (hdd : P.HasDdZero) (haug : P.HasAugZero) {T : Finset P.Cell}
    (a : P.Cell) (h : IsStage P a T) (k : ℕ) :
    (levelMapS' P hdd haug a h).f k =
      (cellS P hdd T h.lower).restrictCptMap (sdS P T)
        (subdiv P hdd haug) (subdivCpt_mem_S P hdd haug h.lower) k := rfl

/-- The value of the restricted subdivision on a chain of the stage, as an element of the
subdivided filtration. -/
theorem levelMapS_f_apply (hdd : P.HasDdZero) (haug : P.HasAugZero) {T : Finset P.Cell}
    (a : P.Cell) (h : IsStage P a T) (k : ℕ)
    (x : ↥((cellS P hdd (insert a T) h.insert_lower).chain.X k)) :
    ((((cellS P hdd (insert a T) h.insert_lower).restrictCptMap (sdS P (insert a T))
      (subdiv P hdd haug) (subdivCpt_mem_S P hdd haug h.insert_lower) k) x :
        ↥(sdSMod P (insert a T) k))) =
      (⟨subdivLM P k ((x : ↥(cellSMod P hdd (insert a T) k)) : (cellChain P hdd).X k),
        (subdivCpt_mem_S P hdd haug h.insert_lower k x.2)⟩ :
        ↥(sdSMod P (insert a T) k)) := rfl

/-- The compatibility of the subdivision with the pieces of a stage step. -/
theorem cellPieceS_hf (hdd : P.HasDdZero) (haug : P.HasAugZero) {T : Finset P.Cell}
    (a : P.Cell) (h : IsStage P a T) :
    ∀ k, (cellPieceS P hdd a h).sub k ≤
      ((sdPieceS P a h).sub k).comap ((levelMapS P hdd haug a h).f k).hom := by
  intro k x hx
  have hx' : ((x : ↥(cellSMod P hdd (insert a T) k)) : (cellChain P hdd).X k) ∈
      cellSMod P hdd T k := hx
  have hmem := Submodule.mem_comap.mp (subdivCpt_mem_S P hdd haug h.lower k hx')
  refine Submodule.mem_comap.mpr ?_
  rw [levelMapS_f P hdd haug a h k]
  rw [levelMapS_f_apply P hdd haug a h k x]
  rw [Submodule.mem_comap]
  simpa using hmem

/-- The relative quotient map of the stage step. -/
noncomputable def stageQuotMap (hdd : P.HasDdZero) (haug : P.HasAugZero) {T : Finset P.Cell}
    (a : P.Cell) (h : IsStage P a T) :
    (cellPieceS P hdd a h).quot ⟶ (sdPieceS P a h).quot :=
  (cellPieceS P hdd a h).quotMap (sdPieceS P a h) (levelMapS P hdd haug a h)
    (cellPieceS_hf P hdd haug a h)

/-! ### The coefficient-sum retraction of the closed cell

The order complex of the closed cell of `e` is a cone, so it is chain-homotopy equivalent to `ℤ`
concentrated in degree `0`; the retraction is the coefficient sum of the `0`-simplices
(`leSubRetr`).  This is what relates the subdivision map on the closed cell to the cellular
augmentation in `Work.MbarHomology.Local.locallySpherical_of_closed`.
-/

/-- The coefficient sum of the boundary of a `1`-chain vanishes. -/
theorem coeffSum_comp_D (P : PolyCW.{u}) :
    (coeffSum (α := P.Cell)).comp (D (α := P.Cell) 0) = 0 := by
  refine Finsupp.lhom_ext fun σ b => ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [show (Finsupp.single σ b : chainMod P.Cell 1) = b • Finsupp.single σ (1 : ℤ) from by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
  rw [map_smul, map_smul]
  have h : coeffSum (D (α := P.Cell) 0 (Finsupp.single σ (1 : ℤ))) = 0 := by
    rw [D_single, map_sum]
    have h2 : ∀ i : Fin 2, coeffSum ((-1 : ℤ) ^ (i : ℕ) •
        Finsupp.single (Simplex.face i σ) (1 : ℤ)) = (-1 : ℤ) ^ (i : ℕ) := by
      intro i
      rw [map_smul, coeffSum_single, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun i _ => h2 i, Fin.sum_univ_two]
    norm_num
  rw [h, smul_zero]

/-- The coefficient sum of the `0`-simplices of the order complex of the closed cell of `e`. -/
noncomputable def leSubCoeff (e : P.Cell) : ↥(sdSMod P (icF P e) 0) →ₗ[ℤ] ULift ℤ :=
  (ULift.moduleEquiv (R := ℤ) (M := ℤ)).symm.toLinearMap.comp
    ((coeffSum (α := P.Cell)).comp (Submodule.subtype (sdSMod P (icF P e) 0)))

/-- The coefficient-sum retraction of the order complex of the closed cell of `e`: it sends every
`0`-simplex to `1` (with coefficients) and vanishes in all other degrees. -/
noncomputable def leSubRetr (e : P.Cell) : leSubCx P e ⟶ unitCx 0 :=
  HomologicalComplex.mkHomToSingle (K := leSubCx P e) (j := 0) (A := unitMod)
    (ModuleCat.ofHom (leSubCoeff P e))
    (fun i hi => by
      have hi' : i = 1 := by
        have h := hi
        simp only [ComplexShape.down_Rel] at h
        omega
      subst hi'
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      show (leSubCoeff P e) ((leSubCx P e).d 1 0 x) = 0
      have hval : (leSubCoeff P e) ((leSubCx P e).d 1 0 x) =
          ULift.up ((coeffSum (α := P.Cell)) ((D (α := P.Cell) 0) (x : (sdChain P).X 1))) := rfl
      rw [hval, ← LinearMap.comp_apply, coeffSum_comp_D, LinearMap.zero_apply]
      rfl)

/-- The value of the retraction on the `0`-simplex at a cell `v ≤ e`. -/
theorem leSubRetr_sdElem_vertex (e v : P.Cell) (hv : v ≤ e) :
    (leSubRetr P e).f 0 (⟨sdElem P (Simplex.vertex v),
      sdElem_mem_sdSMod P (icF P e) 0 (Simplex.vertex v)
        (fun _ => by simpa [icF] using hv)⟩ : ↥(sdSMod P (icF P e) 0)) = ULift.up (1 : ℤ) := by
  show ULift.up ((coeffSum (α := P.Cell)) (sdElem P (Simplex.vertex v))) = ULift.up (1 : ℤ)
  rw [show sdElem P (Simplex.vertex v) = (Finsupp.single (Simplex.vertex v) (1 : ℤ)) from rfl,
    coeffSum_single]

