/-
# Cell atlases: comparing a `Δ`-complex with a `PolyCW` through a finite chain complex

This file fixes the interface used to compute the homology of the barycentric subdivision of the
Ratcliffe--Tschantz piece `M̄` without a huge `SDR` certificate (work package **W6** of
`Submission/Work/NOTES_LEAD_eA.md`).

A `CellAtlas K P C` organises the simplices of a finite `Δ`-complex `K` — in our case the orbits of
flags of `Q̄₀ ⊔ Q̄₁` under the side pairings — by the cells of a finite chain complex `C` — in our
case `Work.HomologyIso.Gen.mbarCx`, the `482`-cell polytopal complex of `M̄` — with *regular* local
models in a `PolyCW` `P` (the face poset of `Q̄`):

* every `k`-simplex `σ` of `K` has a **carrier** `car σ = (n, e)`, the cell of `C` it lies over,
  and a **lift** `lift σ`, a `k`-simplex of the barycentric subdivision of `P` whose top vertex is
  the root face `root n e` of its carrier;
* dropping a vertex other than the last one keeps the carrier and commutes with the lift
  (`face_ne_last`); dropping the last one strictly lowers the carrier dimension (`face_last`);
* the lift is a bijection from the simplices with carrier `(n, e)` onto the `k`-simplices of the
  subdivision of `P` whose top vertex is `root n e` (`lift_bij`).

The associated chain map `zMap : C.toChainComplex ⟶ K.chain` sends the generator `e` of `C` in
degree `n` to `z n e`, the image in `K.chain` of the subdivision chain `subdivCell P n (root n e)`
read through the inverse of `lift`.  Its being a chain map is the hypothesis `BoundaryCompat`,
which is exactly the comparison of the boundary of `C` with the boundary formula for `subdivCell`
of `P` (in the application it is checked by `decide` against `Gen.mbarBd`, work package **W7**).

The main theorem is `CellAtlas.zMap_quasiIso`: if the local complexes of `P` are spherical
(`P.LocallySpherical`), then `zMap` is a quasi-isomorphism.  It is stated in
`Submission/Work/MbarHomology/CellAtlas/QuasiIso.lean`.
-/
import Mathlib
import Submission.Work.Certificates.ChainCx
import Submission.Work.DeltaHomology.Chain
import Submission.Work.Subdivision.Local
import Submission.Work.Subdivision.Subdiv

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

-- The `ℤ`-module structure on the carrier of a `ModuleCat ℤ`-object: the generic instances
-- derived from `ZSMul` and from the `ℤ`-action of an `AddCommGroup` would otherwise win the
-- synthesis of `SMul ℤ ↥M`, and they are *not* the `ℤ`-module one (`add_smul` and friends do not
-- apply to them).  This is the same kind of priority fix as in
-- `Submission/Work/Subdivision/SubComplex.lean`.
attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

noncomputable section

/-- **A cell atlas**: a `Δ`-complex whose simplices are organised by the cells of a finite chain
complex `C`, with regular local models in a `PolyCW` `P`. -/
structure CellAtlas (K : Work.DeltaHomology.DeltaCx) (P : Work.Subdivision.PolyCW)
    (C : Work.Certificates.FinChainCx) where
  /-- The root face of the `e`-th cell of `C` in degree `n`. -/
  root : ∀ n : ℕ, Fin (C.dim n) → P.Cell
  /-- Roots have the expected dimension. -/
  dim_root : ∀ (n : ℕ) (e : Fin (C.dim n)), P.dim (root n e) = n
  /-- The carrier cell of a simplex: the cell of `C` that it lies over. -/
  car : ∀ {k : ℕ}, Fin (K.card k) → Σ n : ℕ, Fin (C.dim n)
  /-- The lift of a simplex to a simplex of the subdivision of `P`. -/
  lift : ∀ {k : ℕ}, Fin (K.card k) → Work.Subdivision.Simplex P.Cell k
  /-- The lift ends at the root face of its carrier. -/
  lift_top : ∀ {k : ℕ} (σ : Fin (K.card k)),
    lift σ (Fin.last k) = root (car σ).1 (car σ).2
  /-- The lift is a bijection from the simplices with a given carrier onto the simplices of the
  subdivision of `P` whose top vertex is the root of that carrier. -/
  lift_bij : ∀ (k n : ℕ) (e : Fin (C.dim n)), Function.Bijective
    (fun σ : {σ : Fin (K.card k) // car σ = ⟨n, e⟩} =>
      (⟨lift σ.1, by rw [lift_top σ.1, σ.2]⟩ :
        {s : Work.Subdivision.Simplex P.Cell k // s (Fin.last k) = root n e}))
  /-- Dropping a vertex other than the last keeps the carrier and commutes with the lift. -/
  face_ne_last : ∀ {k : ℕ} (σ : Fin (K.card (k + 1))) (i : Fin (k + 1)),
    car (K.face σ i.castSucc) = car σ ∧
      lift (K.face σ i.castSucc) = (lift σ).face i.castSucc
  /-- Dropping the last vertex strictly lowers the carrier dimension. -/
  face_last : ∀ {k : ℕ} (σ : Fin (K.card (k + 1))),
    (car (K.face σ (Fin.last (k + 1)))).1 < (car σ).1

namespace CellAtlas

variable {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW}
  {C : Work.Certificates.FinChainCx}

/-- The lift as a function on the simplices with a fixed carrier, with the subtype proofs
discharged. -/
def liftFun (A : CellAtlas K P C) (k n : ℕ) (e : Fin (C.dim n)) :
    {σ : Fin (K.card k) // A.car σ = ⟨n, e⟩} →
      {s : Work.Subdivision.Simplex P.Cell k // s (Fin.last k) = A.root n e} :=
  fun σ => ⟨A.lift σ.1, by rw [A.lift_top σ.1, σ.2]⟩

/-- The inverse of `lift` on the simplices of the subdivision with a fixed top vertex. -/
def liftEquiv (A : CellAtlas K P C) (k n : ℕ) (e : Fin (C.dim n)) :
    {σ : Fin (K.card k) // A.car σ = ⟨n, e⟩} ≃
      {s : Work.Subdivision.Simplex P.Cell k // s (Fin.last k) = A.root n e} :=
  Equiv.ofBijective (A.liftFun k n e) (A.lift_bij k n e)

/-- The coefficient of a simplex in the subdivision chain of `root n e`. -/
def rootCoeff (A : CellAtlas K P C) (n : ℕ) (e : Fin (C.dim n))
    (s : Work.Subdivision.Simplex P.Cell n) : ℤ :=
  (Work.Subdivision.PolyCW.subdivCell P n ⟨A.root n e, A.dim_root n e⟩) s

/-- **The `e`-th chain of the atlas**: the image in `K.chain` of the subdivision chain of the root
face of the cell `e`, read through the inverse of `lift`. -/
def z (A : CellAtlas K P C) (n : ℕ) (e : Fin (C.dim n)) : K.chainX n :=
  ∑ s : Work.Subdivision.Simplex P.Cell n,
    if h : s (Fin.last n) = A.root n e then
      A.rootCoeff n e s •
        (K.chainι n ((A.liftEquiv n n e).symm ⟨s, h⟩).1) (1 : ℤ)
    else 0

/-- `0 • x = 0` for the `ℤ`-module structure; stated for a generic module because the instance
search for `SMulWithZero` does not find the module structure on the carrier of a `ModuleCat`. -/
theorem zero_smul_int {M : Type*} [AddCommGroup M] [Module ℤ M] (x : M) : (0 : ℤ) • x = 0 := by
  have h : (0 : ℤ) = 1 + (-1) := by norm_num
  rw [h, add_smul, one_smul, neg_smul, one_smul, add_neg_cancel]

/-- The degree-`k` component of `zMap`, as an explicit linear map on
`ℤ^{(C.dim k)} = (Fin (C.dim k) → ℤ)`: the generator `e` is mapped to `z k e`. -/
def zMapLin (A : CellAtlas K P C) (k : ℕ) : (Fin (C.dim k) → ℤ) →ₗ[ℤ] ↥(K.chainX k) where
  toFun v := ∑ e : Fin (C.dim k), v e • A.z k e
  map_add' u v := by
    rw [Finset.sum_congr rfl (fun b _ => by rw [Pi.add_apply, add_smul]), Finset.sum_add_distrib]
  map_smul' c v := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      rw [RingHom.id_apply, Pi.smul_apply, smul_assoc]

/-- The degree-`k` component of `zMap`, on the chain module `C_k = ℤ^{(C.dim k)}`. -/
def zMapFun (A : CellAtlas K P C) (k : ℕ) :
    C.toChainComplex.X k ⟶ K.chainX k :=
  ModuleCat.ofHom (A.zMapLin k)

/-- The value of `zMapLin` on the standard basis vector `Pi.single e 1`. -/
theorem zMapLin_piSingle (A : CellAtlas K P C) (k : ℕ) (e : Fin (C.dim k)) :
    A.zMapLin k (Pi.single e (1 : ℤ)) = A.z k e := by
  rw [zMapLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul_int]
  · intro he; exact absurd (Finset.mem_univ e) he

/-- The value of `zMapFun` on the standard basis vector `Pi.single e 1`. -/
@[simp] theorem zMapFun_piSingle (A : CellAtlas K P C) (k : ℕ) (e : Fin (C.dim k)) :
    A.zMapFun k (Pi.single e (1 : ℤ)) = A.z k e :=
  A.zMapLin_piSingle k e

/-- Two `ℤ`-linear maps on the free module `Fin n → ℤ` agree as soon as they agree on the
standard basis `Pi.single e 1`. -/
theorem LinearMap.ext_piSingle {n : ℕ} {M : Type*} [AddCommMonoid M] [Module ℤ M]
    {f g : (Fin n → ℤ) →ₗ[ℤ] M} (h : ∀ e, f (Pi.single e (1 : ℤ)) = g (Pi.single e (1 : ℤ))) :
    f = g := by
  apply LinearMap.ext
  intro v
  have hv : v = ∑ e : Fin n, v e • (Pi.single e (1 : ℤ) : Fin n → ℤ) := by
    funext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [hv, map_sum, map_sum]
  exact Finset.sum_congr rfl fun e _ => by rw [map_smul, map_smul, h e]

/-- **The boundary compatibility of an atlas**: on the generators of `C`, the differential of `C`
agrees with the differential of `K` applied to `z`.  This is what makes `zMap` a chain map. -/
def BoundaryCompat (A : CellAtlas K P C) : Prop :=
  ∀ (n : ℕ) (e : Fin (C.dim (n + 1))),
    A.zMapFun n ((C.toChainComplex).d (n + 1) n (Pi.single e (1 : ℤ)))
      = K.chainD n (A.zMapFun (n + 1) (Pi.single e (1 : ℤ)))

/-- The boundary compatibility, written with the `Δ`-differential `chainD` of `K`. -/
theorem BoundaryCompat.chainD (A : CellAtlas K P C) (h : A.BoundaryCompat) (n : ℕ) :
    A.zMapFun (n + 1) ≫ K.chainD n
      = (C.toChainComplex).d (n + 1) n ≫ A.zMapFun n := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  refine LinearMap.ext_piSingle fun e => ?_
  show K.chainD n (A.zMapFun (n + 1) (Pi.single e (1 : ℤ)))
    = A.zMapFun n ((C.toChainComplex).d (n + 1) n (Pi.single e (1 : ℤ)))
  exact (h n e).symm

/-- The boundary compatibility in the form of a chain-map equation. -/
theorem BoundaryCompat.chain (A : CellAtlas K P C) (h : A.BoundaryCompat) (n : ℕ) :
    A.zMapFun (n + 1) ≫ (K.chain).d (n + 1) n
      = (C.toChainComplex).d (n + 1) n ≫ A.zMapFun n := by
  rw [Work.DeltaHomology.DeltaCx.chain_d]
  exact BoundaryCompat.chainD A h n

/-- **The chain map of an atlas**: `C.toChainComplex ⟶ K.chain`, carrying the generator `e` of `C`
in degree `n` to `z n e`. -/
def zMap (A : CellAtlas K P C) (h : A.BoundaryCompat) : C.toChainComplex ⟶ K.chain :=
  ChainComplex.ofHom (fun k => A.zMapFun k) fun k => BoundaryCompat.chain A h k

@[simp] theorem zMap_f (A : CellAtlas K P C) (h : A.BoundaryCompat) (k : ℕ) :
    (A.zMap h).f k = A.zMapFun k := rfl

end CellAtlas

end

end Work.MbarHomology
