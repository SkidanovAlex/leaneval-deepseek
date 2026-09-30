/-
# The coordinate presentation of the closed cell of a `PolyCW` cell

For a `PolyCW` `P`, a cell `e`, and a finite chain complex `C` of free `ℤ`-modules, suppose we are
given an enumeration `c k : Fin (C.dim k) → {f // P.dim f = k}` of the `k`-cells of the closed cell
of `e`, and that the boundary matrix of `C` is the coordinate matrix of the cellular
differential `P.cellD` in that enumeration (`hbd`).

Then `C.toChainComplex` is isomorphic to the cellular chain complex of the closed cell of `e`,
`Work.MbarHomology.cellLe P hdd e` (spanned by the cells `f ≤ e`): the `i`-th standard basis
vector of `C_k` corresponds to the chain `⟨c k i⟩`.

This is the "coordinate presentation" lemma that lets the per-cell `SDR` certificates of
`Submission/Work/MbarHomology/Qbar/` speak about `cellLe`: those certificates are stated with
sparse `Fin`-indexed boundary matrices, and this file converts them into statements about the
geometric chain complex.
-/
import Mathlib
import Submission.Work.Certificates.ChainCx
import Submission.Work.MbarHomology.Local.CellLe
import Submission.Work.MbarHomology.Qbar.CellDApply

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.MbarHomology.Qbar

open CategoryTheory

noncomputable section

/-- Indexing data: an enumeration of the `k`-cells of the closed cell of `e` by the generators of
the finite chain complex `C` in degree `k`. -/
structure CoordData (P : Work.Subdivision.PolyCW) (e : P.Cell)
    (C : Work.Certificates.FinChainCx) where
  /-- The `i`-th `k`-cell below `e`. -/
  c : ∀ k, Fin (C.dim k) → {f : P.Cell // P.dim f = k}
  /-- Every indexed cell lies below `e`. -/
  le : ∀ k i, (c k i).1 ≤ e
  /-- The indexing is injective. -/
  inj : ∀ k, Function.Injective (c k)
  /-- The indexing is surjective onto the `k`-cells below `e`. -/
  surj : ∀ k (f : P.Cell) (hf : f ≤ e) (hd : P.dim f = k), ∃ i, (c k i).1 = f

section

variable {P : Work.Subdivision.PolyCW} {e : P.Cell} {C : Work.Certificates.FinChainCx}

/-! ### Two elementary facts about `ℤ`-linear maps on `Fin n → ℤ` -/

/-- Two `ℤ`-linear maps out of the free module `Fin n → ℤ` agree as soon as they agree on the
standard basis `Pi.single i 1`. -/
theorem LinearMap.ext_piSingle {n : ℕ} {M : Type*} [AddCommMonoid M] [Module ℤ M]
    {f g : (Fin n → ℤ) →ₗ[ℤ] M}
    (h : ∀ i, f (Pi.single i (1 : ℤ)) = g (Pi.single i (1 : ℤ))) : f = g := by
  apply LinearMap.ext
  intro v
  have hv : v = ∑ i : Fin n, v i • (Pi.single i (1 : ℤ) : Fin n → ℤ) := by
    funext j
    have h1 : (∑ i : Fin n, v i • (Pi.single i (1 : ℤ) : Fin n → ℤ)) j
        = ∑ i : Fin n, (v i • (Pi.single i (1 : ℤ) : Fin n → ℤ)) j :=
      Finset.sum_apply j Finset.univ _
    have h2 : ∑ i : Fin n, (v i • (Pi.single i (1 : ℤ) : Fin n → ℤ)) j = v j := by
      refine (Finset.sum_eq_single (M := ℤ) j ?_ ?_).trans ?_
      · intro b _ hb
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    rw [h1, h2]
  rw [hv, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, h i]

/-! ### The coordinate maps -/

/-- The ambient coordinate map: the `i`-th standard basis vector of `ℤ^{(C.dim k)}` is the chain
`⟨c k i⟩`. -/
def coordAmb (D : CoordData P e C) (k : ℕ) : (Fin (C.dim k) → ℤ) →ₗ[ℤ] P.cellMod k where
  toFun v := ∑ i : Fin (C.dim k), v i • Finsupp.single (D.c k i) (1 : ℤ)
  map_add' u v := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, add_smul]), Finset.sum_add_distrib]
  map_smul' a v := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [RingHom.id_apply, Pi.smul_apply, smul_assoc]

/-- `coordAmb` on a standard basis vector. -/
theorem coordAmb_piSingle (D : CoordData P e C) (k : ℕ) (i : Fin (C.dim k)) :
    coordAmb D k (Pi.single i (1 : ℤ)) = Finsupp.single (D.c k i) (1 : ℤ) := by
  rw [coordAmb, LinearMap.coe_mk, AddHom.coe_mk]
  refine (Finset.sum_eq_single (M := P.cellMod k) i ?_ ?_).trans ?_
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h
  · rw [Pi.single_eq_same, one_smul]

/-- Evaluation of `coordAmb` at the cell `c k j`. -/
theorem coordAmb_apply_gen (D : CoordData P e C) (k : ℕ) (v : Fin (C.dim k) → ℤ)
    (j : Fin (C.dim k)) : coordAmb D k v (D.c k j) = v j := by
  rw [coordAmb, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.finsetSum_apply]
  refine (Finset.sum_eq_single (M := ℤ) j ?_ ?_).trans ?_
  · intro i _ hi
    rw [Finsupp.smul_apply,
      Finsupp.single_eq_of_ne (show D.c k j ≠ D.c k i from fun h => hi (D.inj k h).symm),
      smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h
  · rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]

/-- The `i`-th cell of the closed cell of `e`, as a chain. -/
def coordGen (D : CoordData P e C) (k : ℕ) (i : Fin (C.dim k)) :
    ↥(Work.MbarHomology.cellSubMod P e k) :=
  ⟨Finsupp.single (D.c k i) (1 : ℤ),
    Work.MbarHomology.mem_cellSubMod_single P e k (D.c k i) (D.le k i)⟩

/-- The coordinate map into the subcomplex of the closed cell of `e`. -/
def coordLin (D : CoordData P e C) (k : ℕ) :
    (Fin (C.dim k) → ℤ) →ₗ[ℤ] ↥(Work.MbarHomology.cellSubMod P e k) where
  toFun v := ⟨coordAmb D k v, by
    change (∑ i : Fin (C.dim k), v i • Finsupp.single (D.c k i) (1 : ℤ))
      ∈ Work.MbarHomology.cellSubMod P e k
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Work.MbarHomology.mem_cellSubMod_single P e k (D.c k i) (D.le k i))⟩
  map_add' u v := Subtype.ext (LinearMap.map_add (coordAmb D k) u v)
  map_smul' a v := Subtype.ext (LinearMap.map_smul (coordAmb D k) a v)

/-- `coordLin` on a standard basis vector. -/
theorem coordLin_piSingle (D : CoordData P e C) (k : ℕ) (i : Fin (C.dim k)) :
    coordLin D k (Pi.single i (1 : ℤ)) = coordGen D k i :=
  Subtype.ext (coordAmb_piSingle D k i)

/-- `coordLin` on a standard basis vector, read in the ambient module. -/
theorem coordLin_piSingle_coe (D : CoordData P e C) (k : ℕ) (i : Fin (C.dim k)) :
    ((coordLin D k (Pi.single i (1 : ℤ)) : ↥(Work.MbarHomology.cellSubMod P e k)) :
      P.cellMod k) = Finsupp.single (D.c k i) (1 : ℤ) :=
  coordAmb_piSingle D k i

/-! ### Expansion in the coordinates

Three Finsupp computations: the support of an element of `cellSubMod`, the support of `∂` of a
generator, and the resulting expansion of a supported chain in the coordinates `c k i`. -/

/-- Elements of `cellSubMod P e k` are supported on the cells below `e`. -/
theorem cellSubMod_support_le (k : ℕ) {x : P.cellMod k}
    (hx : x ∈ Work.MbarHomology.cellSubMod P e k) :
    ∀ g : {f : P.Cell // P.dim f = k}, x g ≠ 0 → g.1 ≤ e := by
  rw [Work.MbarHomology.cellSubMod] at hx
  refine Submodule.span_induction
    (p := fun x _ => ∀ g : {f : P.Cell // P.dim f = k}, x g ≠ 0 → g.1 ≤ e) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨f, hf, rfl⟩ g hg
    by_contra hcon
    rw [Finsupp.single_eq_of_ne (show g ≠ f from fun h => hcon (by rw [h]; exact hf))] at hg
    exact hg rfl
  · intro g hg
    exact absurd Finsupp.zero_apply hg
  · intro x y _ _ ihx ihy g hg
    rw [Finsupp.add_apply] at hg
    by_cases h : x g = 0
    · exact ihy g (by rwa [h, zero_add] at hg)
    · exact ihx g h
  · intro a x _ ih g hg
    exact ih g (fun h0 => hg (by rw [Finsupp.smul_apply, h0, smul_zero]))

/-- The differential of a generator of the closed cell of `e` is supported below `e`. -/
theorem cellD_support_le (k : ℕ) (g : {f : P.Cell // P.dim f = k + 1}) (hg : g.1 ≤ e)
    (f : {f : P.Cell // P.dim f = k}) (hf : P.cellD k (Finsupp.single g 1) f ≠ 0) :
    f.1 ≤ e := by
  rw [Work.Subdivision.PolyCW.cellD_apply_single] at hf
  by_contra hle
  have hmem : f.1 ∈ P.facets g.1 := by
    by_contra hmem
    rw [ite_eq_right hmem] at hf
    exact hf rfl
  exact hle (le_trans (le_of_lt ((P.mem_facets g.1 f.1).1 hmem).1) hg)

/-- A chain supported below `e` is the linear combination of the generators `c k i` with its own
values as coefficients. -/
theorem chainExpand (D : CoordData P e C) (k : ℕ) (y : P.cellMod k)
    (hy : ∀ g : {f : P.Cell // P.dim f = k}, y g ≠ 0 → g.1 ≤ e) :
    y = ∑ i : Fin (C.dim k), y (D.c k i) • Finsupp.single (D.c k i) (1 : ℤ) := by
  ext g
  rw [Finsupp.finsetSum_apply]
  by_cases hg : g.1 ≤ e
  · obtain ⟨i₀, hi₀⟩ := D.surj k g.1 hg g.2
    have hsub : D.c k i₀ = g := Subtype.ext hi₀
    have hsum : (∑ i : Fin (C.dim k),
        (y (D.c k i) • Finsupp.single (D.c k i) (1 : ℤ)) g) = y g := by
      refine (Finset.sum_eq_single (M := ℤ) i₀ ?_ ?_).trans ?_
      · intro i _ hi
        rw [Finsupp.smul_apply,
          Finsupp.single_eq_of_ne (show g ≠ D.c k i from
            fun h => hi (D.inj k (hsub.trans h)).symm), smul_zero]
      · intro h; exact absurd (Finset.mem_univ i₀) h
      · rw [Finsupp.smul_apply, hsub, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    exact hsum.symm
  · have hy0 : y g = 0 := by
      by_contra h
      exact hg (hy g h)
    rw [hy0]
    exact (Finset.sum_eq_zero (M := ℤ) fun i _ => by
      rw [Finsupp.smul_apply,
        Finsupp.single_eq_of_ne (show g ≠ D.c k i from fun h => hg (by rw [h]; exact D.le k i)),
        smul_zero]).symm

/-! ### The coordinate linear equivalence -/

theorem coordLin_injective (D : CoordData P e C) (k : ℕ) :
    Function.Injective (coordLin D k) := by
  intro u v huv
  funext j
  have h : coordAmb D k u (D.c k j) = coordAmb D k v (D.c k j) := by
    have h2 := congrArg (fun w : ↥(Work.MbarHomology.cellSubMod P e k) =>
      (w : P.cellMod k) (D.c k j)) huv
    change coordAmb D k u (D.c k j) = coordAmb D k v (D.c k j) at h2
    exact h2
  rw [coordAmb_apply_gen D k u j, coordAmb_apply_gen D k v j] at h
  exact h

theorem coordLin_surjective (D : CoordData P e C) (k : ℕ) :
    Function.Surjective (coordLin D k) := by
  intro y
  refine ⟨fun i => (y : P.cellMod k) (D.c k i), ?_⟩
  apply Subtype.ext
  change coordAmb D k (fun i => (y : P.cellMod k) (D.c k i)) = (y : P.cellMod k)
  exact (chainExpand D k (y : P.cellMod k) (cellSubMod_support_le (k := k) y.2)).symm

/-- The coordinate linear equivalence in degree `k`. -/
def coordEquiv (D : CoordData P e C) (k : ℕ) :
    (Fin (C.dim k) → ℤ) ≃ₗ[ℤ] ↥(Work.MbarHomology.cellSubMod P e k) :=
  LinearEquiv.ofBijective (coordLin D k) ⟨coordLin_injective D k, coordLin_surjective D k⟩

theorem coordEquiv_apply (D : CoordData P e C) (k : ℕ) (v : Fin (C.dim k) → ℤ) :
    (coordEquiv D k) v = coordLin D k v :=
  LinearEquiv.ofBijective_apply (coordLin D k) v

theorem coordEquiv_symm_apply_coordLin (D : CoordData P e C) (k : ℕ)
    (v : Fin (C.dim k) → ℤ) :
    ((coordEquiv D k).symm : ↥(Work.MbarHomology.cellSubMod P e k) →ₗ[ℤ]
      (Fin (C.dim k) → ℤ)) (coordLin D k v) = v :=
  (coordEquiv D k).symm_apply_apply v

theorem coordLin_apply_coordEquiv_symm (D : CoordData P e C) (k : ℕ)
    (y : ↥(Work.MbarHomology.cellSubMod P e k)) :
    coordLin D k (((coordEquiv D k).symm : ↥(Work.MbarHomology.cellSubMod P e k) →ₗ[ℤ]
      (Fin (C.dim k) → ℤ)) y) = y :=
  (coordEquiv D k).apply_symm_apply y

/-! ### The chain isomorphism -/

/-- The restriction of the cellular differential to the closed cell of `e`, with the
`cellSubMod`-instances made explicit (it is the differential of `cellLe P hdd e` in degree `k`). -/
abbrev cellDLe (hdd : P.HasDdZero) (k : ℕ) :
    ↥(Work.MbarHomology.cellSubMod P e (k+1)) →ₗ[ℤ] ↥(Work.MbarHomology.cellSubMod P e k) :=
  (Work.MbarHomology.cellSubData P hdd e).dL k

/-- The cellular differential of `P.cellChain hdd`, evaluated on a chain. -/
theorem cellChain_d_apply (hdd : P.HasDdZero) (k : ℕ) (x : P.cellMod (k+1)) :
    (ModuleCat.Hom.hom ((P.cellChain hdd).d (k+1) k)) x = P.cellD k x := by
  rw [Work.Subdivision.PolyCW.cellChain_d]
  rfl

/-- The value of the differential of the closed cell of `e` on a chain of `cellSubMod`. -/
theorem cellDLe_apply (D : CoordData P e C) (hdd : P.HasDdZero) (k : ℕ)
    (x : ↥(Work.MbarHomology.cellSubMod P e (k+1))) :
    ((cellDLe (P := P) (e := e) hdd k x : ↥(Work.MbarHomology.cellSubMod P e k)) :
        P.cellMod k)
      = P.cellD k (x : P.cellMod (k+1)) := by
  have h1 := Work.Subdivision.SubData.dL_apply (Work.MbarHomology.cellSubData P hdd e) k x
  have h2 : (ModuleCat.Hom.hom ((P.cellChain hdd).d (k+1) k)) (x : P.cellMod (k+1))
      = P.cellD k (x : P.cellMod (k+1)) :=
    cellChain_d_apply (P := P) (hdd := hdd) k (x : P.cellMod (k+1))
  exact h1.trans h2


/-- The coordinate maps commute with the differentials. -/
theorem coordLin_comm (D : CoordData P e C) (hdd : P.HasDdZero)
    (hbd : ∀ (k : ℕ) (i : Fin (C.dim k)) (j : Fin (C.dim (k+1))),
      (P.cellD k (Finsupp.single (D.c (k+1) j) 1)) (D.c k i) = (C.bd k).toMatrix i j)
    (k : ℕ) :
    (cellDLe (P := P) (e := e) hdd k).comp (coordLin D (k+1)) =
      (coordLin D k).comp (Matrix.toLin' ((C.bd k).toMatrix)) := by
  apply LinearMap.ext_piSingle
  intro j
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  apply Subtype.ext
  have hd : ((↑((cellDLe (P := P) (e := e) hdd k)
        (coordLin D (k+1) (Pi.single j (1 : ℤ)))) : P.cellMod k))
      = P.cellD k (Finsupp.single (D.c (k+1) j) 1) := by
    rw [cellDLe_apply D hdd k (coordLin D (k+1) (Pi.single j (1 : ℤ))),
      coordLin_piSingle_coe D (k+1) j]
  rw [hd]
  change P.cellD k (Finsupp.single (D.c (k+1) j) 1) =
    ∑ i : Fin (C.dim k), (Matrix.col ((C.bd k).toMatrix) j) i
      • Finsupp.single (D.c k i) (1 : ℤ)
  rw [chainExpand D k (P.cellD k (Finsupp.single (D.c (k+1) j) 1))
    (cellD_support_le (k := k) (D.c (k+1) j) (D.le (k+1) j))]
  exact Finset.sum_congr rfl fun i _ => by rw [hbd k i j, Matrix.col_apply]

/-- The commutation for the inverse coordinate maps. -/
theorem coordLin_symm_comm (D : CoordData P e C) (hdd : P.HasDdZero)
    (hbd : ∀ (k : ℕ) (i : Fin (C.dim k)) (j : Fin (C.dim (k+1))),
      (P.cellD k (Finsupp.single (D.c (k+1) j) 1)) (D.c k i) = (C.bd k).toMatrix i j)
    (k : ℕ) :
    (Matrix.toLin' ((C.bd k).toMatrix)).comp
        (((coordEquiv D (k+1)).symm : ↥(Work.MbarHomology.cellSubMod P e (k+1)) →ₗ[ℤ]
          (Fin (C.dim (k+1)) → ℤ))) =
      (((coordEquiv D k).symm : ↥(Work.MbarHomology.cellSubMod P e k) →ₗ[ℤ]
          (Fin (C.dim k) → ℤ))).comp
        (cellDLe (P := P) (e := e) hdd k) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have h := congrArg (fun (f : (Fin (C.dim (k+1)) → ℤ) →ₗ[ℤ]
        ↥(Work.MbarHomology.cellSubMod P e k)) =>
      f ((((coordEquiv D (k+1)).symm : ↥(Work.MbarHomology.cellSubMod P e (k+1)) →ₗ[ℤ]
        (Fin (C.dim (k+1)) → ℤ))) x)) (coordLin_comm D hdd hbd k)
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    coordLin_apply_coordEquiv_symm D (k+1) x] at h
  rw [h]
  exact (coordEquiv_symm_apply_coordLin D k
    (Matrix.toLin' ((C.bd k).toMatrix)
      ((((coordEquiv D (k+1)).symm : ↥(Work.MbarHomology.cellSubMod P e (k+1)) →ₗ[ℤ]
        (Fin (C.dim (k+1)) → ℤ))) x))).symm

/-- The chain map `C.toChainComplex ⟶ cellLe P hdd e` in degree `k`. -/
theorem coordHom_comm (D : CoordData P e C) (hdd : P.HasDdZero)
    (hbd : ∀ (k : ℕ) (i : Fin (C.dim k)) (j : Fin (C.dim (k+1))),
      (P.cellD k (Finsupp.single (D.c (k+1) j) 1)) (D.c k i) = (C.bd k).toMatrix i j)
    (k : ℕ) :
    ModuleCat.ofHom (coordLin D (k+1)) ≫ (Work.MbarHomology.cellLe P hdd e).d (k+1) k =
      (C.toChainComplex).d (k+1) k ≫ ModuleCat.ofHom (coordLin D k) := by
  simp only [Work.MbarHomology.cellLe, Work.Subdivision.SubData.chain_d,
    Work.Certificates.FinChainCx.toChainComplex, ChainComplex.of_d, ← ModuleCat.ofHom_comp]
  exact congrArg ModuleCat.ofHom (coordLin_comm D hdd hbd k)

/-- The commutation for the inverse chain map. -/
theorem coordInv_comm (D : CoordData P e C) (hdd : P.HasDdZero)
    (hbd : ∀ (k : ℕ) (i : Fin (C.dim k)) (j : Fin (C.dim (k+1))),
      (P.cellD k (Finsupp.single (D.c (k+1) j) 1)) (D.c k i) = (C.bd k).toMatrix i j)
    (k : ℕ) :
    ModuleCat.ofHom (((coordEquiv D (k+1)).symm : ↥(Work.MbarHomology.cellSubMod P e (k+1))
        →ₗ[ℤ] (Fin (C.dim (k+1)) → ℤ))) ≫ (C.toChainComplex).d (k+1) k =
      (Work.MbarHomology.cellLe P hdd e).d (k+1) k ≫
        ModuleCat.ofHom (((coordEquiv D k).symm : ↥(Work.MbarHomology.cellSubMod P e k)
          →ₗ[ℤ] (Fin (C.dim k) → ℤ))) := by
  simp only [Work.MbarHomology.cellLe, Work.Subdivision.SubData.chain_d,
    Work.Certificates.FinChainCx.toChainComplex, ChainComplex.of_d, ← ModuleCat.ofHom_comp]
  exact congrArg ModuleCat.ofHom (coordLin_symm_comm D hdd hbd k)

/-- The chain map `C.toChainComplex ⟶ cellLe P hdd e` of a coordinate presentation. -/
def coordMap (D : CoordData P e C) (hdd : P.HasDdZero)
    (hbd : ∀ (k : ℕ) (i : Fin (C.dim k)) (j : Fin (C.dim (k+1))),
      (P.cellD k (Finsupp.single (D.c (k+1) j) 1)) (D.c k i) = (C.bd k).toMatrix i j) :
    C.toChainComplex ⟶ Work.MbarHomology.cellLe P hdd e :=
  ChainComplex.ofHom (fun k => ModuleCat.ofHom (coordLin D k))
    fun k => coordHom_comm D hdd hbd k

/-- The inverse chain map. -/
def coordMapInv (D : CoordData P e C) (hdd : P.HasDdZero)
    (hbd : ∀ (k : ℕ) (i : Fin (C.dim k)) (j : Fin (C.dim (k+1))),
      (P.cellD k (Finsupp.single (D.c (k+1) j) 1)) (D.c k i) = (C.bd k).toMatrix i j) :
    Work.MbarHomology.cellLe P hdd e ⟶ C.toChainComplex :=
  ChainComplex.ofHom (fun k => ModuleCat.ofHom
    (((coordEquiv D k).symm : ↥(Work.MbarHomology.cellSubMod P e k) →ₗ[ℤ]
      (Fin (C.dim k) → ℤ)))) fun k => coordInv_comm D hdd hbd k

theorem coordMap_f (D : CoordData P e C) (hdd : P.HasDdZero)
    (hbd : ∀ (k : ℕ) (i : Fin (C.dim k)) (j : Fin (C.dim (k+1))),
      (P.cellD k (Finsupp.single (D.c (k+1) j) 1)) (D.c k i) = (C.bd k).toMatrix i j)
    (k : ℕ) : (coordMap D hdd hbd).f k = ModuleCat.ofHom (coordLin D k) := rfl

theorem coordMapInv_f (D : CoordData P e C) (hdd : P.HasDdZero)
    (hbd : ∀ (k : ℕ) (i : Fin (C.dim k)) (j : Fin (C.dim (k+1))),
      (P.cellD k (Finsupp.single (D.c (k+1) j) 1)) (D.c k i) = (C.bd k).toMatrix i j)
    (k : ℕ) : (coordMapInv D hdd hbd).f k = ModuleCat.ofHom
      (((coordEquiv D k).symm : ↥(Work.MbarHomology.cellSubMod P e k) →ₗ[ℤ]
        (Fin (C.dim k) → ℤ))) := rfl

theorem hom_coordMap_f (D : CoordData P e C) (hdd : P.HasDdZero)
    (hbd : ∀ (k : ℕ) (i : Fin (C.dim k)) (j : Fin (C.dim (k+1))),
      (P.cellD k (Finsupp.single (D.c (k+1) j) 1)) (D.c k i) = (C.bd k).toMatrix i j)
    (k : ℕ) : ModuleCat.Hom.hom ((coordMap D hdd hbd).f k) =
      (coordLin D k : (C.toChainComplex).X k →ₗ[ℤ]
        (Work.MbarHomology.cellLe P hdd e).X k) :=
  ModuleCat.hom_ofHom (coordLin D k)

theorem hom_coordMapInv_f (D : CoordData P e C) (hdd : P.HasDdZero)
    (hbd : ∀ (k : ℕ) (i : Fin (C.dim k)) (j : Fin (C.dim (k+1))),
      (P.cellD k (Finsupp.single (D.c (k+1) j) 1)) (D.c k i) = (C.bd k).toMatrix i j)
    (k : ℕ) : ModuleCat.Hom.hom ((coordMapInv D hdd hbd).f k) =
      (((coordEquiv D k).symm : ↥(Work.MbarHomology.cellSubMod P e k) →ₗ[ℤ]
        (Fin (C.dim k) → ℤ)) : (Work.MbarHomology.cellLe P hdd e).X k →ₗ[ℤ]
          (C.toChainComplex).X k) :=
  ModuleCat.hom_ofHom (((coordEquiv D k).symm : ↥(Work.MbarHomology.cellSubMod P e k) →ₗ[ℤ]
    (Fin (C.dim k) → ℤ)))

/-- The inverse coordinate equivalence is a left inverse of `coordLin`. -/
theorem coordEquiv_symm_comp_coordLin (D : CoordData P e C) (hdd : P.HasDdZero) (k : ℕ) :
    (((coordEquiv D k).symm : ↥(Work.MbarHomology.cellSubMod P e k) →ₗ[ℤ]
      (Fin (C.dim k) → ℤ))).comp (coordLin D k) = LinearMap.id :=
  LinearMap.ext fun v => coordEquiv_symm_apply_coordLin D k v

/-- `coordLin` is a left inverse of the inverse coordinate equivalence. -/
theorem coordLin_comp_coordEquiv_symm (D : CoordData P e C) (hdd : P.HasDdZero) (k : ℕ) :
    (coordLin D k).comp (((coordEquiv D k).symm : ↥(Work.MbarHomology.cellSubMod P e k) →ₗ[ℤ]
      (Fin (C.dim k) → ℤ))) = LinearMap.id :=
  LinearMap.ext fun v => coordLin_apply_coordEquiv_symm D k v

/-- The coordinate isomorphism. -/
def coordIso (D : CoordData P e C) (hdd : P.HasDdZero)
    (hbd : ∀ (k : ℕ) (i : Fin (C.dim k)) (j : Fin (C.dim (k+1))),
      (P.cellD k (Finsupp.single (D.c (k+1) j) 1)) (D.c k i) = (C.bd k).toMatrix i j) :
    C.toChainComplex ≅ Work.MbarHomology.cellLe P hdd e :=
  Iso.mk (coordMap D hdd hbd) (coordMapInv D hdd hbd)
    (by
      apply HomologicalComplex.hom_ext
      intro k
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, hom_coordMapInv_f, hom_coordMap_f,
        HomologicalComplex.id_f, ModuleCat.hom_id]
      exact LinearMap.congr_fun (coordEquiv_symm_comp_coordLin D hdd k) x)
    (by
      apply HomologicalComplex.hom_ext
      intro k
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, hom_coordMap_f, hom_coordMapInv_f,
        HomologicalComplex.id_f, ModuleCat.hom_id]
      exact LinearMap.congr_fun (coordLin_comp_coordEquiv_symm D hdd k) x)

end

end

theorem cellLe_iso_finChainCx (P : Work.Subdivision.PolyCW) (hdd : P.HasDdZero) (e : P.Cell)
    (C : Work.Certificates.FinChainCx)
    (c : ∀ k, Fin (C.dim k) → {f : P.Cell // P.dim f = k})
    (hc_le : ∀ k i, (c k i).1 ≤ e)
    (hc_inj : ∀ k, Function.Injective (c k))
    (hc_surj : ∀ k (f : P.Cell) (hf : f ≤ e) (hd : P.dim f = k), ∃ i, (c k i).1 = f)
    (hbd : ∀ (k : ℕ) (i : Fin (C.dim k)) (j : Fin (C.dim (k+1))),
      (P.cellD k (Finsupp.single (c (k+1) j) 1)) (c k i) = (C.bd k).toMatrix i j) :
    Nonempty (C.toChainComplex ≅ Work.MbarHomology.cellLe P hdd e) :=
  ⟨coordIso ⟨c, hc_le, hc_inj, hc_surj⟩ hdd hbd⟩

end Work.MbarHomology.Qbar
