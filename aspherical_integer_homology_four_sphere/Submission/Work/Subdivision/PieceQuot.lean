/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.Local
import Submission.Work.Subdivision.Level
import Submission.Work.Subdivision.Piece
import Submission.Work.Subdivision.sdTopMod_insert
import Submission.Work.Subdivision.sdTopMod_inf_leSub
import Submission.Work.Subdivision.cellTopMod_insert_succ
import Submission.Work.Subdivision.cellTopMod_inf_span
import Submission.Work.Subdivision.SubdivAssembly
import Submission.Work.Subdivision.SubDataCpt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The two pieces of a skeletal level, identified (set-up)

Refining the two filtrations `cellTop P hdd n E` and `sdTop P n E` (`Level.lean`)
by a single further `(n+1)`-cell `a` produces two **pieces**, and the quotients
of those pieces are canonically

* `(sdPiece P n E a).quot ≅ locCx P a` — the local complex of the new cell, and
* `(cellPiece P hdd n E a).quot ≅ unitCx (n+1)` — the one-dimensional model
  complex.

Both identifications are built from the second isomorphism theorem, in the form of
`Submodule.mapQ` of the inclusion `leSub a k ↪ sdTopMod n (insert a E) k`
(respectively of the line spanned by the new cell into
`cellTopMod n (insert a E) (n+1)`); the advantage of this formulation is that the
value on representatives is computable by `Submodule.mapQ_apply`: `mk x ↦ mk x`.

## Note on the `ℤ`-module diamond

The ambient of every submodule mentioned below is written as the *type*
`chainMod P.Cell k` (or an explicit `↥p`) rather than as the `ModuleCat` object
`(sdChain P).X k`, which is only definitionally equal to it: instance synthesis
for `Module ℤ ((sdChain P).X k)` does not always succeed through the `ModuleCat`
coercion, so the `Submodule.inclusion`/`mapQ` arguments are stated over the plain
type.  The two ambients are interchangeable by definitional unfolding.
-/

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

/-- A quotient by the whole module is a subsingleton. -/
theorem subsingleton_quotient_of_eq_top {M : Type*} [AddCommGroup M] [Module ℤ M]
    {q : Submodule ℤ M} (hq : q = ⊤) : Subsingleton (M ⧸ q) := by
  have hzero : ∀ x : M ⧸ q, x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ a => exact (Submodule.Quotient.mk_eq_zero q).mpr (by rw [hq]; trivial)
  exact ⟨fun x y => by rw [hzero x, hzero y]⟩

/-- The one-dimensional model complex is trivial away from its degree. -/
theorem unitCx_subsingleton {n : ℕ} {k : ℕ} (hk : k ≠ n + 1) :
    Subsingleton ((unitCx (n + 1)).X k) :=
  ModuleCat.subsingleton_of_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) (n + 1) unitMod k hk)

/-- The generator of `spanMap x` is `x`. -/
theorem spanMap_one {M : ModuleCat ℤ} (x : M) :
    PolyCW.spanMap x (ULift.up (1 : ℤ)) = x := by
  show LinearMap.toSpanSingleton (R := ℤ) (M := ↥M) x
    ((ULift.moduleEquiv (M := ℤ)) (ULift.up (1 : ℤ))) = x
  rw [show (ULift.moduleEquiv (M := ℤ)) (ULift.up (1 : ℤ)) = (1 : ℤ) from rfl]
  exact LinearMap.toSpanSingleton_apply_one (R := ℤ) (M := ↥M) x

namespace PolyCW

variable (P : PolyCW.{u})

/-! ### The subdivided piece -/

/-- The chains with all vertices `< a` lie in `sdTopMod P n E` when `a` has
dimension `n+1`. -/
theorem ltSub_le_sdTopMod (n : ℕ) (E : Finset P.Cell) {a : P.Cell} (ha : P.dim a = n + 1)
    (k : ℕ) : ltSub P a k ≤ sdTopMod P n E k :=
  SdTopModInf.ltSub_le P n E ha k

/-- The inclusion `leSub a k ↪ sdTopMod n (insert a E) k`, over the plain chain
module. -/
noncomputable abbrev sdInc (n : ℕ) (E : Finset P.Cell) {a : P.Cell} (ha : P.dim a = n + 1)
    (k : ℕ) : ↥(leSub P a k) →ₗ[ℤ] ↥(sdTopMod P n (insert a E) k) :=
  Submodule.inclusion (R := ℤ) (M := chainMod P.Cell k) (p := leSub P a k)
    (p' := sdTopMod P n (insert a E) k) (leSub_le_sdTopMod_insert P ha E k)

@[simp] theorem sdInc_apply (n : ℕ) (E : Finset P.Cell) {a : P.Cell} (ha : P.dim a = n + 1)
    (k : ℕ) (x : ↥(leSub P a k)) :
    (sdInc P n E ha k x : ↥(sdTopMod P n (insert a E) k)) =
      (⟨(x : chainMod P.Cell k), leSub_le_sdTopMod_insert P ha E k x.2⟩ :
        ↥(sdTopMod P n (insert a E) k)) := rfl

/-- The inclusion `leSub a k ↪ sdTopMod n (insert a E) k` carries `ltSub a k`
into `sdTopMod n E k`. -/
theorem leSub_le_sdTopMod_insert' (n : ℕ) (E : Finset P.Cell) {a : P.Cell}
    (ha : P.dim a = n + 1) (k : ℕ) :
    locRel P a k ≤ ((sdPiece P n E a).sub k).comap (sdInc P n E ha k) := by
  intro x hx
  have hx' : (x : chainMod P.Cell k) ∈ ltSub P a k := hx
  have hmem : (x : chainMod P.Cell k) ∈ sdTopMod P n E k := ltSub_le_sdTopMod P n E ha k hx'
  refine Submodule.mem_comap.mpr ?_
  show (sdInc P n E ha k x : ↥(sdTopMod P n (insert a E) k)) ∈ (sdPiece P n E a).sub k
  rw [sdInc_apply]
  exact hmem

/-- **The subdivided piece, compared with the local complex of the new cell.**
The second isomorphism theorem, in the form of `Submodule.mapQ` of the inclusion,
identifies the local module `locMod P a k = leSub a k ⧸ ltSub a k` with the
quotient of `sdTopMod P n (insert a E) k` by `sdTopMod P n E k`. -/
noncomputable def sdPieceMapLin (n : ℕ) (E : Finset P.Cell) {a : P.Cell}
    (ha : P.dim a = n + 1) (k : ℕ) :
    locMod P a k →ₗ[ℤ] ((sdTop P n (insert a E)).chain.X k ⧸ (sdPiece P n E a).sub k) :=
  Submodule.mapQ (locRel P a k) ((sdPiece P n E a).sub k) (sdInc P n E ha k)
    (leSub_le_sdTopMod_insert' P n E ha k)

/-- The computation rule for `sdPieceMapLin`: on the class of a chain supported
below `a` it is again that class. -/
theorem sdPieceMapLin_apply (n : ℕ) (E : Finset P.Cell) {a : P.Cell} (ha : P.dim a = n + 1)
    (k : ℕ) (y : ↥(leSub P a k)) :
    sdPieceMapLin P n E ha k (Submodule.Quotient.mk y) =
      (Submodule.Quotient.mk (sdInc P n E ha k y) : ((sdPiece P n E a).quot).X k) :=
  Submodule.mapQ_apply _ _ _ y

/-! ### The cellular piece -/

/-- In degrees other than `n+1` the refined cellular filtration is the `n`-skeleton. -/
theorem cellTopMod_eq_cellSubMod_of_ne (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell)
    {k : ℕ} (hk : k ≠ n + 1) : cellTopMod P hdd n E k = cellSubMod P hdd n k := by
  have hset : {y : (cellChain P hdd).X k |
      ∃ e : {e : P.Cell // P.dim e = k}, e.1 ∈ E ∧ P.dim e.1 = n + 1 ∧
        y = cellElem P hdd k e} = (∅ : Set ((cellChain P hdd).X k)) := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨e, -, hd, -⟩
    exact absurd (e.2 ▸ hd : k = n + 1) hk
  rw [cellTopMod, hset, Submodule.span_empty, sup_bot_eq]

/-- In degrees other than `n+1` the piece quotient of the refined cellular
filtration vanishes. -/
theorem cellPiece_subsingleton (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (a : P.Cell)
    {k : ℕ} (hk : k ≠ n + 1) : Subsingleton ((cellPiece P hdd n E a).quot.X k) := by
  have hsub : (cellPiece P hdd n E a).sub k = ⊤ := by
    refine eq_top_iff.mpr fun x _ => Submodule.mem_comap.mpr ?_
    have hx : x.1 ∈ cellTopMod P hdd n (insert a E) k := x.2
    rw [cellTopMod_eq_cellSubMod_of_ne P hdd n (insert a E) hk] at hx
    rw [cellTopMod_eq_cellSubMod_of_ne P hdd n E hk]
    exact hx
  have h := subsingleton_quotient_of_eq_top hsub
  exact ⟨fun x y => h.elim x y⟩

/-- The generator of the cellular piece: the class of the new cell. -/
noncomputable def cellPieceGen (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) {a : P.Cell}
    (ha : P.dim a = n + 1) : ((cellPiece P hdd n E a).quot).X (n + 1) :=
  Submodule.Quotient.mk
    (⟨cellElem P hdd (n + 1) ⟨a, ha⟩,
      cellElem_mem_cellTopMod P hdd n (insert a E) (n + 1) ⟨a, ha⟩
        (Finset.mem_insert_self a E) ha⟩ :
      ↥(cellTopMod P hdd n (insert a E) (n + 1)))

/-- The coefficient map `ℤ → (cellPiece).quot.X (n+1)`, `1 ↦ [a]`. -/
noncomputable def cellPieceCoeffF (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell)
    {a : P.Cell} (ha : P.dim a = n + 1) :
    unitMod.{u} ⟶ ((cellPiece P hdd n E a).quot).X (n + 1) :=
  spanMap (cellPieceGen P hdd n E ha)

@[simp] theorem cellPieceCoeffF_one (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell)
    {a : P.Cell} (ha : P.dim a = n + 1) :
    (cellPieceCoeffF P hdd n E ha) (ULift.up (1 : ℤ)) = cellPieceGen P hdd n E ha :=
  spanMap_one _

end PolyCW

end

end Work.Subdivision
