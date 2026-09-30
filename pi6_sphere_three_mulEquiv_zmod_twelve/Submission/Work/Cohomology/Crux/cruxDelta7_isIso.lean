import Mathlib
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Cohomology.cokernel_biprod_map_iso
import Submission.Work.Cohomology.cokernelComponent
import Submission.Work.Cohomology.relMV_quasiIso
import Submission.Work.Cohomology.Endgame.overlapQuasiIso
import Submission.Work.Milnor.fibreNorm

set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology.Crux

/-!
# The relative Mayer--Vietoris connecting isomorphism of the two-chart cover of `Vk (-2)`

`Work.Cohomology.cruxδ X A U V 7` is the connecting map
`H₈(C^{U,V}(X,A)) ⟶ H₇(C^{U,V}(U∩V, U∩V∩A))` of the canonical relative Mayer--Vietoris short exact
sequence (`cruxShort X A U V`) of the cover `U ∪ V = X`.  For the two chart images `U = vkU`,
`V = vkV` of `Vk (-2)` and `A = vkPairA = Mk (-2)` it is an isomorphism: both groups are `ℤ` and
the transgression is an isomorphism (Mayer--Vietoris).

ROUTE (all ingredients are in the workspace):
* `ShortComplex.ShortExact.isIso_δ` reduces the goal to `IsZero ((cruxMid X A U V).homology 7)` and
  `IsZero ((cruxMid X A U V).homology 8)`.
* `cruxMid X A U V = cokernel (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))`, both maps are
  `subInclChain U V inter_subset_left`, and `Work.Cohomology.cokernel_biprod_map_iso` gives
  `cokernel (biprod.map f g) ≅ cokernel f ⊞ cokernel g`.  So it suffices that
  `H_n (relMVUU X A U V) = 0` and `H_n (relMVVV X A U V) = 0` for `n = 7, 8`, where
  `relMVUU = relSmallChains U V U (U ∩ A)` is the cokernel of `subInclChain U V (U ∩ A ⊆ U)`.

* **U-component.**  By `Work.Cohomology.vk_chartPair_group 7/8` the relative homology of the
  genuine chart pair `(TopCat.of ↥vkU, {x : ↥vkU | (x : vkPairX) ∈ vkPairA})` is `0` in degrees
  `7, 8` (its value is `Fin (if n = 4 then 1 else 0) → ℤ`).  So it suffices to know that
  `relMVUU` is *quasi-isomorphic* to those genuine relative chains.  This can be shown exactly as
  `Work.Cohomology.relMVUV_quasiIso` does it: `SSet.chainComplexMap (smallInLift U V U) ℤ` is an
  isomorphism of chain complexes because
  `smallInSubcomplex U V U = Subfunctor.range (TopCat.toSSet.map (subtypeIncl X U))`
  (every simplex whose image lies in `U` is small for `(U,V)`; this is the same argument as
  `Work.Cohomology.smallInSubcomplex_inter_eq_range` in the `U ∩ V` case, and gives
  `IsIso (smallInLift U V U)` just as `isIso_smallInLift_inter` does for `U ∩ V`), and the
  analogous statement for `U ∩ A ⊆ U` (whose proof only needs `U ∩ A ⊆ U` and
  `exists_map_inclUX_of_range_subset`); the compatibility with the inclusions is a naturality
  square proved by cancelling `toSSet.map (subtypeIncl X U)` and using `smallInLift_comp`, exactly
  as `subInclChain_natural` does.  The induced map on cokernels is then an isomorphism (or apply
  `HomologicalComplex.HomologySequence.quasiIso_τ₃` to the morphism of short exact sequences
  `(hPairShort (TopCat.of ↥U) (interAU A U))`).

* **V-component, avoiding the mirrored chart computation.**  Here one should *not* redo
  `vk_chartPair_group` for the second chart `ιY`.  Instead use the short exact sequence
  `0 → smallInChains U V (V ∩ A) → smallInChains U V V → relMVVV → 0` and its long exact sequence:
  since `IsIso (smallInToSingA U V V)` holds for an *arbitrary* subset (`isIso_smallInToSingA`)
  and `V` is contractible (`Work.Milnor.contractibleSpace_range_ιY`), one has
  `H_n (smallInChains U V V) = 0` for `n ≥ 1`; similarly `isIso_smallInToSingA U V (V ∩ A)`
  identifies `H_n (smallInChains U V (V ∩ A))` with `H_n (singularChains ℤ (TopCat.of ↥(V ∩ A)))`.
  So it suffices that the subspace `↥(V ∩ A)` has vanishing homology in degrees `6, 7, 8`.  This
  follows because `V ∩ A` is, via the chart `ιY`, the unit sphere bundle over the chart: using
  `Work.Milnor.fibreNorm (-2)` (there is a continuous `N : Vk (-2) → ℝ` with
  `N ((vData k).ιX p) = ‖p.2‖` and `N ((vData k).ιY p) = ‖p.2‖` for both charts, so that on the
  second chart `ιY p ∈ A` is equivalent to `‖p.2‖ = 1`), the homeomorphism
  `(vData (-2)).isOpenEmbedding_ιY.isEmbedding.toHomeomorph` identifies `(↥(V ∩ A))` with the
  subspace `{p : MSpace8 | ‖p.2‖ = 1} ≃ S³` of `MSpace8 = ℝ⁴ × ℍ`, whose homology vanishes in
  positive degrees; hence `≃ S³` by contraction of the first factor
  (`Work.Cohomology.homotopyEquiv_prod_fst`, `Work.Cohomology.sphereHomologyZero`).
-/



open CategoryTheory AlgebraicTopology Limits
open Work.Cohomology

noncomputable section

/-! ## General vanishing lemmas for the cokernel of a subcomplex inclusion -/

/-- The short complex `0 ⟶ C^{U,V}(C) ⟶ C^{U,V}(B) ⟶ C^{U,V}(B,C) ⟶ 0` attached to an
inclusion of subsets `C ⊆ B` is short exact. -/
theorem subInclChain_shortExact_aux {X : TopCat} (U V : Set X) {C B : Set X} (h : C ⊆ B) :
    (ShortComplex.mk (subInclChain U V h) (cokernel.π (subInclChain U V h))
      (cokernel.condition (subInclChain U V h))).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (subInclChain U V h))
    (mono_subInclChain U V h) inferInstance

/-- **Vanishing of the relative small chains from vanishing of the two adjacent absolute
groups.**  If `H_{k+1}` and `H_k` of the small chains lying in `B` vanish, as does `H_k` of those
lying in `C`, then `H_{k+1}` of the relative small chains `C^{U,V}(B,C)` vanishes: the connecting
map of the sequence of the inclusion is an isomorphism onto `H_k(C) = 0`. -/
theorem isZero_relSmallChains_homology {X : TopCat} (U V B C : Set X) (hCB : C ⊆ B) (k : ℕ)
    (hB : IsZero ((smallInChains U V B).homology (k + 1)))
    (hB' : IsZero ((smallInChains U V B).homology k))
    (hC : IsZero ((smallInChains U V C).homology k)) :
    IsZero ((relSmallChains U V B C hCB).homology (k + 1)) := by
  have hS := subInclChain_shortExact_aux U V hCB
  let hij : (ComplexShape.down ℕ).Rel (k + 1) k := by simp [ComplexShape.down]
  exact IsZero.of_iso hC (hS.δIso (k + 1) k hij hB hB')

/-- Vanishing of the small chains lying in a contractible subset, in positive degrees. -/
theorem isZero_smallInChains_of_contractible {X : TopCat} (U V B : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    [ContractibleSpace ↥B] (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((smallInChains U V B).homology n) := by
  haveI := isIso_smallInToSingA U V B hU hV hcov n
  exact IsZero.of_iso (homologyContractible (X := TopCat.of ↥B) n (by omega))
    (asIso (HomologicalComplex.homologyMap (smallInToSingA U V B) n))

/-- Vanishing of the small chains lying in a subset, transported from the singular chains of that
subset along `smallInToSingA`. -/
theorem isZero_smallInChains_of_singular {X : TopCat} (U V B : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (n : ℕ)
    (h : IsZero ((singularChains ℤ (TopCat.of ↥B)).homology n)) :
    IsZero ((smallInChains U V B).homology n) := by
  haveI := isIso_smallInToSingA U V B hU hV hcov n
  exact IsZero.of_iso h (asIso (HomologicalComplex.homologyMap (smallInToSingA U V B) n))

/-! ## The homology of the middle term `cruxMid` -/

/-- The middle term of the relative Mayer–Vietoris complex is the biproduct of the two relative
complexes of the charts. -/
theorem cruxMid_iso_biprod (X : TopCat) (A U V : Set X) :
    Nonempty (cruxMid X A U V ≅ relMVUU X A U V ⊞ relMVVV X A U V) :=
  cokernel_biprod_map_iso (relMVτ₂U U V A) (relMVτ₂V U V A)

/-! ## The homology of the chart pieces of the sphere bundle

On either chart of `Vk (-2)`, the unit sphere bundle `Mk (-2)` is the product of the chart with the
unit sphere `S³ ⊆ ℍ`, so the chart-intersection `range ι ∩ Mk (-2)` has the homology of `S³`.
-/

private theorem quatSph_mem (y : ↥(Metric.sphere (0 : Quaternion ℝ) 1)) :
    Quaternion.linearIsometryEquivTuple y.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
  have h : ‖y.1‖ = 1 := by
    have := Metric.mem_sphere.mp y.2
    rwa [dist_zero_right] at this
  rw [Metric.mem_sphere, dist_zero_right, Quaternion.linearIsometryEquivTuple.norm_map]
  exact h

private theorem quatSph_symm_mem (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :
    Quaternion.linearIsometryEquivTuple.symm y.1 ∈ Metric.sphere (0 : Quaternion ℝ) 1 := by
  have h : ‖y.1‖ = 1 := by
    have := Metric.mem_sphere.mp y.2
    rwa [dist_zero_right] at this
  rw [Metric.mem_sphere, dist_zero_right,
    ← Quaternion.linearIsometryEquivTuple.norm_map
      (Quaternion.linearIsometryEquivTuple.symm y.1),
    LinearIsometryEquiv.apply_symm_apply]
  exact h

private noncomputable def quatSphHomeo :
    ↥(Metric.sphere (0 : Quaternion ℝ) 1) ≃ₜ
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  toFun y := ⟨Quaternion.linearIsometryEquivTuple y.1, quatSph_mem y⟩
  invFun y := ⟨Quaternion.linearIsometryEquivTuple.symm y.1, quatSph_symm_mem y⟩
  left_inv y := Subtype.ext (Quaternion.linearIsometryEquivTuple.symm_apply_apply y.1)
  right_inv y := Subtype.ext (Quaternion.linearIsometryEquivTuple.apply_symm_apply y.1)
  continuous_toFun := Continuous.subtype_mk
    (Quaternion.linearIsometryEquivTuple.continuous.comp continuous_subtype_val) quatSph_mem
  continuous_invFun := Continuous.subtype_mk
    (Quaternion.linearIsometryEquivTuple.symm.continuous.comp continuous_subtype_val)
    quatSph_symm_mem

private noncomputable def msphProd :
    ↥{p : Submission.Milnor.MSpace8 | ‖p.2‖ = 1} ≃ₜ
      (EuclideanSpace ℝ (Fin 4) × ↥(Metric.sphere (0 : Quaternion ℝ) 1)) :=
  (Homeomorph.setCongr (by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and, Metric.mem_sphere,
        dist_eq_norm, sub_zero])).trans
    ((Homeomorph.Set.prod (Set.univ : Set (EuclideanSpace ℝ (Fin 4)))
        (Metric.sphere (0 : Quaternion ℝ) 1)).trans
      ((Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 4))).prodCongr (Homeomorph.refl _)))

private noncomputable def msphProdHomotopy :
    ContinuousMap.HomotopyEquiv
      (EuclideanSpace ℝ (Fin 4) × ↥(Metric.sphere (0 : Quaternion ℝ) 1))
      ↥(Metric.sphere (0 : Quaternion ℝ) 1) :=
  (Homeomorph.prodComm (EuclideanSpace ℝ (Fin 4))
    ↥(Metric.sphere (0 : Quaternion ℝ) 1)).toHomotopyEquiv.trans
    (Work.Cohomology.homotopyEquiv_prod_fst ↥(Metric.sphere (0 : Quaternion ℝ) 1)
      (EuclideanSpace ℝ (Fin 4))).some

/-- **The chart-intersection with the sphere bundle has the homology of `S³`**: for a chart map
`g : ℝ⁴ × ℍ → Vk (-2)` onto an open subset on which the fibre norm is the norm of the second
coordinate, the subspace `↥(range g ∩ Mk (-2))` is homotopy equivalent to `S³`, so its `ℤ`-homology
vanishes in every degree `≠ 0, 3`. -/
private theorem interRangeHomologyIsZero
    (g : Submission.Milnor.MSpace8 → Submission.Milnor.Vk (-2))
    (hg : Topology.IsOpenEmbedding g)
    (hgnorm : ∀ p : Submission.Milnor.MSpace8,
      Work.Milnor.fibreNormFun (-2) (g p) = ‖p.2‖)
    (n : ℕ) (hn0 : n ≠ 0) (hn3 : n ≠ 3) :
    CategoryTheory.Limits.IsZero (HomologicalComplex.homology
      (Work.Cohomology.singularChains ℤ (TopCat.of ↥(Set.range g ∩ Work.Cohomology.vkPairA)))
      n) := by
  let cH : Submission.Milnor.MSpace8 ≃ₜ ↥(Set.range g) := hg.isEmbedding.toHomeomorph
  let piece : Set ↥(Set.range g) := {y | (y : Submission.Milnor.Vk (-2)) ∈ Work.Cohomology.vkPairA}
  let piece' : Set Submission.Milnor.MSpace8 := cH ⁻¹' piece
  have hpiece' : piece' = {p : Submission.Milnor.MSpace8 | ‖p.2‖ = 1} := by
    ext p
    simp only [piece', piece, Set.mem_preimage, Set.mem_setOf_eq]
    rw [show ((cH p : ↥(Set.range g)) : Submission.Milnor.Vk (-2)) = g p from rfl,
      Work.Milnor.mem_range_mkToVkFun_iff, hgnorm p]
  let pieceHomeo : ↥piece' ≃ₜ ↥piece :=
    { toFun := fun p => ⟨cH p.1, Set.mem_preimage.mp p.2⟩
      invFun := fun y => ⟨cH.symm y.1, by
        show cH (cH.symm y.1) ∈ piece
        rw [Homeomorph.apply_symm_apply]
        exact y.2⟩
      left_inv := fun p => Subtype.ext (cH.symm_apply_apply p.1)
      right_inv := fun y => Subtype.ext (cH.apply_symm_apply y.1)
      continuous_toFun := Continuous.subtype_mk
        (cH.continuous.comp continuous_subtype_val) (fun p => Set.mem_preimage.mp p.2)
      continuous_invFun := Continuous.subtype_mk
        (cH.symm.continuous.comp continuous_subtype_val) (fun y => by
          show cH (cH.symm y.1) ∈ piece
          rw [Homeomorph.apply_symm_apply]
          exact y.2) }
  let hHE : ContinuousMap.HomotopyEquiv ↥piece
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    (pieceHomeo.symm.trans (Homeomorph.setCongr hpiece')).toHomotopyEquiv.trans
      (msphProd.toHomotopyEquiv.trans
        (msphProdHomotopy.trans quatSphHomeo.toHomotopyEquiv))
  have hflat := Work.Cohomology.flatHomeo (α := Submission.Milnor.Vk (-2))
    (q := fun x : Submission.Milnor.Vk (-2) => x ∈ Set.range g)
    (P := fun x : Submission.Milnor.Vk (-2) => x ∈ Work.Cohomology.vkPairA)
  exact Work.Cohomology.isZero_homology_of_homotopyEquiv
    (hflat.symm.toHomotopyEquiv.trans hHE) n
    (Work.Cohomology.sphereVanishing 3 n (by norm_num) hn0 hn3)

private theorem vkU_inter_mk_homologyIsZero (n : ℕ) (hn0 : n ≠ 0) (hn3 : n ≠ 3) :
    CategoryTheory.Limits.IsZero (HomologicalComplex.homology
      (Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(vkU ∩ Work.Cohomology.vkPairA))) n) :=
  interRangeHomologyIsZero (Submission.Milnor.vData (-2)).ιX
    (Submission.Milnor.vData (-2)).isOpenEmbedding_ιX
    (fun p => Work.Milnor.fibreNormFun_ιX (-2) p) n hn0 hn3

private theorem vkV_inter_mk_homologyIsZero (n : ℕ) (hn0 : n ≠ 0) (hn3 : n ≠ 3) :
    CategoryTheory.Limits.IsZero (HomologicalComplex.homology
      (Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(vkV ∩ Work.Cohomology.vkPairA))) n) :=
  interRangeHomologyIsZero (Submission.Milnor.vData (-2)).ιY
    (Submission.Milnor.vData (-2)).isOpenEmbedding_ιY
    (fun p => Work.Milnor.fibreNormFun_ιY (-2) p) n hn0 hn3

theorem cruxDelta7_isIso :
    CategoryTheory.IsIso (Work.Cohomology.cruxδ Work.Cohomology.vkPairX Work.Cohomology.vkPairA
      Work.Cohomology.Crux.vkU Work.Cohomology.Crux.vkV 7) := by
  have hU : IsOpen vkU := vkU_isOpen
  have hV : IsOpen vkV := vkV_isOpen
  have hcov : vkU ∪ vkV = Set.univ := vkU_union_vkV
  haveI : ContractibleSpace ↥vkU := Work.Milnor.contractibleSpace_range_ιX (-2)
  haveI : ContractibleSpace ↥vkV := Work.Milnor.contractibleSpace_range_ιY (-2)
  -- the geometric inputs: the chart-intersection with the sphere bundle has the homology of `S³`
  have hUA6 : IsZero ((singularChains ℤ (TopCat.of ↥(vkU ∩ vkPairA))).homology 6) :=
    vkU_inter_mk_homologyIsZero 6 (by norm_num) (by norm_num)
  have hUA7 : IsZero ((singularChains ℤ (TopCat.of ↥(vkU ∩ vkPairA))).homology 7) :=
    vkU_inter_mk_homologyIsZero 7 (by norm_num) (by norm_num)
  have hVA6 : IsZero ((singularChains ℤ (TopCat.of ↥(vkV ∩ vkPairA))).homology 6) :=
    vkV_inter_mk_homologyIsZero 6 (by norm_num) (by norm_num)
  have hVA7 : IsZero ((singularChains ℤ (TopCat.of ↥(vkV ∩ vkPairA))).homology 7) :=
    vkV_inter_mk_homologyIsZero 7 (by norm_num) (by norm_num)
  -- small chains of the two chart pieces and of the two sphere-bundle pieces
  have hUU6 : IsZero ((smallInChains vkU vkV vkU).homology 6) :=
    isZero_smallInChains_of_contractible vkU vkV vkU hU hV hcov 6 (by norm_num)
  have hUU7 : IsZero ((smallInChains vkU vkV vkU).homology 7) :=
    isZero_smallInChains_of_contractible vkU vkV vkU hU hV hcov 7 (by norm_num)
  have hUU8 : IsZero ((smallInChains vkU vkV vkU).homology 8) :=
    isZero_smallInChains_of_contractible vkU vkV vkU hU hV hcov 8 (by norm_num)
  have hUA6' : IsZero ((smallInChains vkU vkV (vkU ∩ vkPairA)).homology 6) :=
    isZero_smallInChains_of_singular vkU vkV (vkU ∩ vkPairA) hU hV hcov 6 hUA6
  have hUA7' : IsZero ((smallInChains vkU vkV (vkU ∩ vkPairA)).homology 7) :=
    isZero_smallInChains_of_singular vkU vkV (vkU ∩ vkPairA) hU hV hcov 7 hUA7
  have hVV6 : IsZero ((smallInChains vkU vkV vkV).homology 6) :=
    isZero_smallInChains_of_contractible vkU vkV vkV hU hV hcov 6 (by norm_num)
  have hVV7 : IsZero ((smallInChains vkU vkV vkV).homology 7) :=
    isZero_smallInChains_of_contractible vkU vkV vkV hU hV hcov 7 (by norm_num)
  have hVV8 : IsZero ((smallInChains vkU vkV vkV).homology 8) :=
    isZero_smallInChains_of_contractible vkU vkV vkV hU hV hcov 8 (by norm_num)
  have hVA6' : IsZero ((smallInChains vkU vkV (vkV ∩ vkPairA)).homology 6) :=
    isZero_smallInChains_of_singular vkU vkV (vkV ∩ vkPairA) hU hV hcov 6 hVA6
  have hVA7' : IsZero ((smallInChains vkU vkV (vkV ∩ vkPairA)).homology 7) :=
    isZero_smallInChains_of_singular vkU vkV (vkV ∩ vkPairA) hU hV hcov 7 hVA7
  -- the two components of the middle term
  have hrelUU7 : IsZero ((relMVUU vkPairX vkPairA vkU vkV).homology 7) :=
    isZero_relSmallChains_homology vkU vkV vkU (vkU ∩ vkPairA) Set.inter_subset_left 6
      hUU7 hUU6 hUA6'
  have hrelUU8 : IsZero ((relMVUU vkPairX vkPairA vkU vkV).homology 8) :=
    isZero_relSmallChains_homology vkU vkV vkU (vkU ∩ vkPairA) Set.inter_subset_left 7
      hUU8 hUU7 hUA7'
  have hrelVV7 : IsZero ((relMVVV vkPairX vkPairA vkU vkV).homology 7) :=
    isZero_relSmallChains_homology vkU vkV vkV (vkV ∩ vkPairA) Set.inter_subset_left 6
      hVV7 hVV6 hVA6'
  have hrelVV8 : IsZero ((relMVVV vkPairX vkPairA vkU vkV).homology 8) :=
    isZero_relSmallChains_homology vkU vkV vkV (vkV ∩ vkPairA) Set.inter_subset_left 7
      hVV8 hVV7 hVA7'
  -- the middle term is the biproduct of the two components
  have hMid (n : ℕ) (h1 : IsZero ((relMVUU vkPairX vkPairA vkU vkV).homology n))
      (h2 : IsZero ((relMVVV vkPairX vkPairA vkU vkV).homology n)) :
      IsZero ((cruxMid vkPairX vkPairA vkU vkV).homology n) := by
    obtain ⟨e⟩ := cruxMid_iso_biprod vkPairX vkPairA vkU vkV
    exact IsZero.of_iso (isZero_homology_biprod _ _ n h1 h2)
      (asIso (HomologicalComplex.homologyMap e.hom n))
  have hMid7 := hMid 7 hrelUU7 hrelVV7
  have hMid8 := hMid 8 hrelUU8 hrelVV8
  exact ShortComplex.ShortExact.isIso_δ (cruxShort_shortExact vkPairX vkPairA vkU vkV) 8 7
    (by simp [ComplexShape.down]) hMid8 hMid7

end

end Work.Cohomology.Crux
