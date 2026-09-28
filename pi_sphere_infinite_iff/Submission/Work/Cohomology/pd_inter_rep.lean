import Mathlib
import Submission.Work.Cohomology.pd_glue3
import Submission.Work.Cohomology.pd_goodD_rep
import Submission.Work.Cohomology.pd_localFundClass_natural
import Submission.Work.Cohomology.cap_mem_range_inclChains
import Submission.Work.Cohomology.cap_natural
import Submission.Work.Cohomology.pd_mvdelta_apply
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_crux_weak
import Submission.Work.Cohomology.pd_alpha2_zeta
import Submission.Work.Cohomology.pd_inter_lift
import Submission.Work.Cohomology.pd_inter_capchi
namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false

/-!
# Representation of the class of the intersection

`Work.Cohomology.pd_inter_rep`: given a relative cocycle `u ∈ Z^{k+1}(U∪V, (U∪V)∖(K∩L))`, a degree-`k`
cochain `χ` vanishing on `(U∪V)∖K` and on `(U∪V)∖L` with `δχ = δφA - u`, the Hatcher decomposition
`d α₂ = g - e - f` of the (middle) chain `α₂` supported in `U ∩ V`, and a relative cycle `γ₂` of
`(U∩V, (U∩V)∖(K∩L))` whose underlying chain is the projection of `β` (with `incl β = α₂`) and whose
class is the local fundamental class of `c` at `K ∩ L`, there is a cycle `s` of `C_*(U∩V)` whose image
in `M` is the cap product of `δα` with `α₂` (pushed from `U∪V`) and whose class is the image of the
class of `u` under the duality map of `U ∩ V`.

The construction: the relative cap product `z ⌢ γ₂` of the restriction `z` of `u` to `U ∩ V` with
`γ₂` is an absolute cycle of `U ∩ V` whose underlying chain is `δχ ⌢ α₂` modulo the boundary of a
chain of `U ∩ V`; adding that boundary corrects the chain representative to `δφA ⌢ α₂` while keeping
the homology class, which is `[u]| ⌢ μ_{K∩L}` by the computation rule for `relCapPairZ`.
-/

/-! ## Small cast and naturality lemmas for the proof of `pd_inter_rep` -/

/-- A function commutes with the transport of its arguments along an equality of degrees. -/
theorem pdInter_cast_apply_aux {A B : ℕ → Type*} (f : ∀ n, A n → B n) {a b : ℕ}
    (h : a = b) (x : A a) : h ▸ f a x = f b (h ▸ x) := by cases h; rfl

/-- The two ways of transporting along the two orientations of an equality agree. -/
theorem pdInter_cast_symm_apply {ι : Type*} {P : ι → Type*} {a b : ι} (h : a = b)
    (x : P a) : h ▸ x = h.symm ▸ x := by cases h; rfl

/-- Transport does not depend on the proof of the degree equality. -/
theorem pdInter_cast_eq_of_eq {ι : Type*} {P : ι → Type*} {a b : ι} (h h' : a = b)
    (x : P a) : h ▸ x = h' ▸ x := by rw [Subsingleton.elim h h']

/-- Transport of relative cycles. -/
theorem pdInter_cast_iCycles_rel {X : TopCat} (A : Set X) {a b : ℕ} (h : a = b)
    (z : (relChains X A).cycles a) :
    (relChains X A).iCycles b (h ▸ z) = h ▸ ((relChains X A).iCycles a z) := by
  cases h; rfl

/-- Transport of the projection to the relative chains. -/
theorem pdInter_cast_cokerπ {X : TopCat} (A : Set X) {a b : ℕ} (h : a = b)
    (x : (singularChains ℤ X).X a) :
    ((cokernel.π (inclChains X A)).f b) (h ▸ x)
      = h ▸ (((cokernel.π (inclChains X A)).f a) x) := by
  cases h; rfl

/-- Transport of classes in the homology of a relative chain complex. -/
theorem pdInter_cast_homologyπ_rel {X : TopCat} (A : Set X) {a b : ℕ} (h : a = b)
    (z : (relChains X A).cycles a) :
    (relChains X A).homologyπ b (h ▸ z) = h ▸ ((relChains X A).homologyπ a z) :=
  (pdInter_cast_apply_aux (fun n (x : (relChains X A).cycles n) => (relChains X A).homologyπ n x)
    h z).symm

/-- Transport of chains along a chain map. -/
theorem pdInter_cast_chainMap {X Y : TopCat} (f : X ⟶ Y) {a b : ℕ} (h : a = b)
    (x : (singularChains ℤ X).X a) :
    (chainMap ℤ X Y f).f b (h ▸ x) = h ▸ ((chainMap ℤ X Y f).f a x) := by
  cases h; rfl

/-- A morphism of `ℤ`-modules commutes with the integer scalar multiples. -/
theorem pdInter_map_zsmul {M N : ModuleCat ℤ} (f : M ⟶ N) (r : ℤ) (x : M) :
    f (r • x) = r • f x := by
  show (ModuleCat.Hom.hom f) (r • x) = r • (ModuleCat.Hom.hom f) x
  rw [map_zsmul]

/-- The inverse of the trace followed by the inclusion is the inclusion of the trace. -/
theorem pdInter_pdTrInv_comp_pdIncl {M : TopCat} {W S : Set M} (h : S ⊆ W) :
    pdTrInv h ≫ pdIncl W S h = subtypeIncl (TopCat.of W) (pdTr W S) := by
  ext x; rfl

/-- The inclusion of the chains of `S` inside `M` factors through the inclusion `S ⊆ W`. -/
theorem pdInter_inclChains_comp {M : TopCat} {S W : Set M} (h : S ⊆ W) (n : ℕ)
    (x : (singularChains ℤ (TopCat.of S)).X n) :
    (inclChains M S).f n x = (inclChains M W).f n
      ((chainMap ℤ (TopCat.of S) (TopCat.of W) (pdIncl W S h)).f n x) := by
  rw [pdIncl_eq_inclChainsSub h]
  rw [← inclChainsSub_comp M S W h, HomologicalComplex.comp_f, ModuleCat.comp_apply]

/-- Naturality of the cap product along the inclusion of a subspace. -/
theorem pdInter_cap_natural {M : TopCat} {S W : Set M} (h : S ⊆ W) {k m : ℕ}
    (ψ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of W)) k)
    (y : (singularChains ℤ (TopCat.of S)).X (k + m)) :
    (chainMap ℤ (TopCat.of S) (TopCat.of W) (pdIncl W S h)).f m
        (cap ℤ (TopCat.toSSet.obj (TopCat.of S))
          (ψ.comp ((chainMap ℤ (TopCat.of S) (TopCat.of W) (pdIncl W S h)).f k).hom) m y)
      = cap ℤ (TopCat.toSSet.obj (TopCat.of W)) ψ m
          ((chainMap ℤ (TopCat.of S) (TopCat.of W) (pdIncl W S h)).f (k + m) y) :=
  cap_natural ℤ (TopCat.toSSet.map (pdIncl W S h)) ψ y

/-- The underlying cochain of the image cycle is the image of the underlying cochain. -/
theorem pdInter_iCycles_cyclesMap_apply {K L : CochainComplex (ModuleCat ℤ) ℕ}
    (φ : K ⟶ L) (N : ℕ) (z : K.cycles N) :
    (L.iCycles N).hom ((HomologicalComplex.cyclesMap φ N).hom z)
      = (φ.f N).hom ((K.iCycles N).hom z) := by
  have h2 := congrArg (fun (g : K.cycles N ⟶ L.X N) => g.hom z)
    (HomologicalComplex.cyclesMap_i φ N)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- Naturality of `homologyπ` for cochain complexes. -/
theorem pdInter_homologyMap_homologyπ_cyclesMap {K L : CochainComplex (ModuleCat ℤ) ℕ}
    (φ : K ⟶ L) (N : ℕ) (z : K.cycles N) :
    (HomologicalComplex.homologyMap φ N).hom ((K.homologyπ N).hom z)
      = (L.homologyπ N).hom ((HomologicalComplex.cyclesMap φ N).hom z) := by
  have h2 := congrArg (fun (g : K.cycles N ⟶ L.homology N) => g.hom z)
    (HomologicalComplex.homologyπ_naturality φ N)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- `goodD` does not depend on the proof of the degree bookkeeping. -/
theorem pdInter_goodD_hkm_irrel {M : TopCat} [T2Space M] {N : ℕ}
    (c : (singularChains ℤ M).homology N) (W : Set M) (hW : IsOpen W) (K : Set M)
    (hKW : K ⊆ W) (hKc : IsCompact K) (k m : ℕ) (hkm hkm' : k + m = N)
    (x : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k) :
    goodD N c W hW K hKW hKc k m hkm x = goodD N c W hW K hKW hKc k m hkm' x := by
  simp only [goodD]

theorem pd_inter_rep {M : TopCat} [T2Space M] {k mj : ℕ}
    (c : (singularChains ℤ M).homology (k + (mj + 1)))
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hI : IsOpen (U ∩ V)) {K L : Set M} (hKc : IsCompact K) (hLc : IsCompact L)
    (hKU : K ⊆ U) (hLV : L ⊆ V)
    (φA : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) k)
    (α₂ : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X (k + (mj + 1)))
    (β : (singularChains ℤ (TopCat.of ↥(pdTr (U ∪ V) (U ∩ V)))).X (k + (mj + 1)))
    (hβ : (inclChains (TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) (U ∩ V))).f (k + (mj + 1)) β = α₂)
    (u : (relComplex ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).cycles (k + 1))
    (χ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) k)
    (hχK : χ ∈ relKern ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) K) k)
    (hχL : χ ∈ relKern ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) L) k)
    (hχd : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) χ
        = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) φA
          - pdCohUnderCycle (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L)) (k + 1) u)
    (hdα₂ : ∃ (g e f : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X (k + mj)),
        (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₂ = g - e - f ∧
        g ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdRelSub (U ∪ V) (K ∪ L))).f (k + mj)).hom ∧
        e ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdRelSub (U ∪ V) L)).f (k + mj)).hom ∧
        f ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdRelSub (U ∪ V) K)).f (k + mj)).hom)
    (γ₂ : (relChains (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))).cycles (k + (mj + 1)))
    (hγ₂ : (relChains (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))).iCycles (k + (mj + 1)) γ₂
        = ((CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of ↥(U ∩ V))
            (pdRelSub (U ∩ V) (K ∩ L)))).f (k + (mj + 1)))
            ((chainMap ℤ (TopCat.of ↥(pdTr (U ∪ V) (U ∩ V))) (TopCat.of ↥(U ∩ V))
              (pdTrInv (Set.inter_subset_left.trans Set.subset_union_left))).f (k + (mj + 1)) β))
    (hγ₂c : (relChains (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))).homologyπ (k + (mj + 1)) γ₂
        = localFundClass (k + (mj + 1)) c (U ∩ V) hI (K ∩ L)
            (Set.inter_subset_inter hKU hLV) (hKc.inter hLc)) :
    ∃ (s : (singularChains ℤ (TopCat.of ↥(U ∩ V))).cycles mj),
      (inclChains M (U ∩ V)).f mj ((singularChains ℤ (TopCat.of ↥(U ∩ V))).iCycles mj s)
        = (inclChains M (U ∪ V)).f mj
            (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
              (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) φA) mj
              ((capIdx k mj) ▸ α₂))
      ∧ goodD (k + (mj + 1)) c (U ∩ V) hI (K ∩ L)
          (Set.inter_subset_inter hKU hLV) (hKc.inter hLc) (k + 1) mj (by omega)
          (HomologicalComplex.homologyMap
            (relComplexMap ℤ (pdRelSub (U ∩ V) (K ∩ L)) (pdRelSub (U ∪ V) (K ∩ L))
              (pdIncl (U ∪ V) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left))
              (fun y hy => hy)) (k + 1)
            ((relComplex ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).homologyπ (k + 1) u))
        = (singularChains ℤ (TopCat.of ↥(U ∩ V))).homologyπ mj s := by
  classical
  have hIW : U ∩ V ⊆ (U ∪ V : Set M) := Set.inter_subset_left.trans Set.subset_union_left
  have hKLI : K ∩ L ⊆ U ∩ V := Set.inter_subset_inter hKU hLV
  -- (0) the restriction of the relative complex of `(U∪V, U∪V∖(K∩L))` to the intersection
  let ψ :=
    relComplexMap ℤ (pdRelSub (U ∩ V) (K ∩ L)) (pdRelSub (U ∪ V) (K ∩ L)) (pdIncl (U ∪ V) (U ∩ V) hIW) (fun y hy => hy)
  let z := HomologicalComplex.cyclesMap ψ (k + 1) u
  have hzclass : (HomologicalComplex.homologyMap ψ (k + 1)).hom
        (((relComplex ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L)))).homologyπ (k + 1) u)
      = ((relComplex ℤ (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L)))).homologyπ (k + 1) z :=
    pdInter_homologyMap_homologyπ_cyclesMap ψ (k + 1) u
  -- (1) the chain of `U ∩ V` corresponding to `β`
  let ξ :=
    (chainMap ℤ (TopCat.of ↥(pdTr (U ∪ V) (U ∩ V))) (TopCat.of ↥(U ∩ V))
      (pdTrInv (Set.inter_subset_left.trans Set.subset_union_left))).f (k + (mj + 1)) β
  have hξγ : ((relChains (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L)))).iCycles (k + (mj + 1)) γ₂
      = ((CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of ↥(U ∩ V))
          (pdRelSub (U ∩ V) (K ∩ L)))).f (k + (mj + 1))) ξ := hγ₂
  -- (2) the same objects in degree `(k+1)+mj`
  let γ₂' := (capIdx k mj) ▸ γ₂
  let ξ' := (capIdx k mj) ▸ ξ
  have hξγ' : ((relChains (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L)))).iCycles ((k + 1) + mj) γ₂'
      = ((CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of ↥(U ∩ V))
          (pdRelSub (U ∩ V) (K ∩ L)))).f ((k + 1) + mj)) ξ' := by
    rw [show γ₂' = (capIdx k mj) ▸ γ₂ from rfl, show ξ' = (capIdx k mj) ▸ ξ from rfl]
    rw [pdInter_cast_iCycles_rel, pdInter_cast_cokerπ, hξγ]
  have hγ₂'' : ((relChains (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L)))).homologyπ ((k + 1) + mj) γ₂'
      = (capIdx k mj).symm ▸ localFundClass (k + (mj + 1)) c (U ∩ V) hI (K ∩ L)
          (Set.inter_subset_inter hKU hLV) (hKc.inter hLc) := by
    rw [show γ₂' = (capIdx k mj) ▸ γ₂ from rfl]
    rw [pdInter_cast_homologyπ_rel]
    rw [hγ₂c]
  -- (3) the duality identity on representatives
  have hgd₀ : goodD (k + (mj + 1)) c (U ∩ V) hI (K ∩ L)
        (Set.inter_subset_inter hKU hLV) (hKc.inter hLc) (k + 1) mj (capIdx k mj).symm
        (HomologicalComplex.homologyMap ψ (k + 1)
          (((relComplex ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L)))).homologyπ (k + 1) u))
      = ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).homologyπ mj
          (relCapPairZ (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))
            (k + 1) mj z γ₂') := by
    rw [hzclass]
    exact goodD_homologyπ c (U ∩ V) hI (K ∩ L) (Set.inter_subset_inter hKU hLV)
      (hKc.inter hLc) (k + 1) mj (capIdx k mj).symm z γ₂' hγ₂'' ξ' hξγ'
  -- (4) the support of `α₂`
  have hα₂mem : α₂ ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (U ∩ V))).f (k + (mj + 1))).hom := ⟨β, hβ⟩
  obtain ⟨y, hy⟩ := pd_inter_lift (χ := χ) (α₂ := α₂) hα₂mem
  let w := -((-1 : ℤ) ^ k) • ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).d (mj + 1) mj y
  have hw : ((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left)))).f mj w
      = cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) χ) mj ((capIdx k mj) ▸ α₂) := by
    have hnat : ((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left)))).f mj (((singularChains ℤ (TopCat.of ↥(U ∩ V)))).d (mj + 1) mj y)
        = ((singularChains ℤ (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj (((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left)))).f (mj + 1) y) := by
      have h := congrArg (fun (g : ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).X (mj + 1) ⟶ ((singularChains ℤ (TopCat.of ↥(U ∪ V)))).X mj) => g.hom y)
        (((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left)))).comm (mj + 1) mj)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h.symm
    rw [show w = -((-1 : ℤ) ^ k) • ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).d (mj + 1) mj y from rfl]
    rw [pdInter_map_zsmul, hnat, hy, pd_inter_capchi χ α₂ hχK hχL hdα₂]

  have hsum : (pdCohUnderCycle (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L)) (k + 1) u) + cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) χ = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) φA := by
    rw [hχd]; abel

  -- (5) the cochain underlying `z` and the image of the chain `ξ'`
  let z₀ := (((relComplex ℤ (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))).iCycles (k + 1)).hom z).1
  have hz₀ : z₀ = ((pdCohUnderCycle (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L)) (k + 1) u)).comp ((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) (U ∩ V) hIW)).f (k + 1)).hom := by
    have h1 : ((relComplex ℤ (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))).iCycles (k + 1)).hom z
        = (ψ.f (k + 1)).hom (((relComplex ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).iCycles (k + 1)).hom u) :=
      pdInter_iCycles_cyclesMap_apply ψ (k + 1) u
    have h2 : (ψ.f (k + 1)).hom (((relComplex ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).iCycles (k + 1)).hom u)
        = (relMapLM ℤ (pdRelSub (U ∩ V) (K ∩ L)) (pdRelSub (U ∪ V) (K ∩ L))
            (pdIncl (U ∪ V) (U ∩ V) hIW) (fun y hy => hy) (k + 1))
            (((relComplex ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).iCycles (k + 1)).hom u) := by
      rw [show ψ = relComplexMap ℤ (pdRelSub (U ∩ V) (K ∩ L))
          (pdRelSub (U ∪ V) (K ∩ L)) (pdIncl (U ∪ V) (U ∩ V) hIW) (fun y hy => hy) from rfl]
      exact congrArg (fun (g : ((relComplex ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).X (k + 1) ⟶
          (relComplex ℤ (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))).X (k + 1))) => g.hom
            (((relComplex ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).iCycles (k + 1)).hom u))
        (relComplexMap_f ℤ (pdRelSub (U ∩ V) (K ∩ L)) (pdRelSub (U ∪ V) (K ∩ L))
          (pdIncl (U ∪ V) (U ∩ V) hIW) (fun y hy => hy) (k + 1))
    have h12 : z₀ = ((relMapLM ℤ (pdRelSub (U ∩ V) (K ∩ L)) (pdRelSub (U ∪ V) (K ∩ L))
            (pdIncl (U ∪ V) (U ∩ V) hIW) (fun y hy => hy) (k + 1))
            (((relComplex ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).iCycles (k + 1)).hom u)).1 :=
      congrArg (fun t => t.1) (h1.trans h2)
    refine h12.trans ?_
    rw [relMapLM_coe, dualChainMap_f_hom]
    apply LinearMap.ext
    intro cc
    rfl
  have hξ'incl : ((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left)))).f ((k + 1) + mj) ξ' = (capIdx k mj) ▸ α₂ := by
    rw [show ξ' = (capIdx k mj) ▸ ξ from rfl]
    rw [pdInter_cast_chainMap]
    congr 1
    show ((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left)))).f (k + (mj + 1))
        ((chainMap ℤ (TopCat.of ↥(pdTr (U ∪ V) (U ∩ V))) (TopCat.of ↥(U ∩ V))
          (pdTrInv hIW)).f (k + (mj + 1)) β) = α₂
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f]
    rw [show ((chainMap ℤ (TopCat.of ↥(pdTr (U ∪ V) (U ∩ V))) (TopCat.of ↥(U ∩ V)) (pdTrInv hIW))
          ≫ (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) (U ∩ V) hIW)))
        = chainMap ℤ (TopCat.of ↥(pdTr (U ∪ V) (U ∩ V))) (TopCat.of ↥(U ∪ V))
            (pdTrInv hIW ≫ pdIncl (U ∪ V) (U ∩ V) hIW) from chainMap_compPD _ _ _ _ _]
    rw [pdInter_pdTrInv_comp_pdIncl]
    exact hβ
  -- (6) the image in `U∪V` of the cap product computed in `U∩V`
  have hcapM : ((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left)))).f mj
        (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) z₀ mj ξ')
      = cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) ((pdCohUnderCycle (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L)) (k + 1) u)) mj ((capIdx k mj) ▸ α₂) := by
    rw [hz₀]
    rw [pdInter_cap_natural (S := U ∩ V) (W := U ∪ V) hIW ((pdCohUnderCycle (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L)) (k + 1) u)) ξ']
    rw [hξ'incl]
  -- (7) the cap product on representatives
  -- (7a)
  have hy₀ : ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).iCycles mj
        (relCapPairZ (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))
          (k + 1) mj z γ₂')
      = cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) z₀ mj ξ' :=
    relCapPairZ_iCycles_apply (X := TopCat.of ↥(U ∩ V)) (A := pdRelSub (U ∩ V) (K ∩ L)) (n := k + 1) (m := mj) (z := z) (γ := γ₂') (ξ := ξ') hξγ'
  -- (7b)
  have hb : ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).iCycles mj
        ((-((-1 : ℤ) ^ k)) • ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).toCycles (mj + 1) mj y)
      = -((-1 : ℤ) ^ k) • ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).d (mj + 1) mj y := by
    rw [pdInter_map_zsmul, toCycles_i_C]
  -- (8) the cycle
  let y₀ :=
    relCapPairZ (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L)) (k + 1) mj z γ₂'
  let b := (-((-1 : ℤ) ^ k)) • ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).toCycles (mj + 1) mj y
  let s := y₀ + b
  let capI : ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).X mj := cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) z₀ mj ξ'
  let w₂ : ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).X mj := -((-1 : ℤ) ^ k) • ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).d (mj + 1) mj y
  -- (8b) the underlying chain of s
  have hiCyc_s : ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).iCycles mj s = capI + w₂ := by
    rw [show s = y₀ + b from rfl, map_add]
    rw [show y₀ = relCapPairZ (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))
        (k + 1) mj z γ₂' from rfl, hy₀]
    rw [show b = (-((-1 : ℤ) ^ k)) • ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).toCycles (mj + 1) mj y from rfl, hb]
  -- (8c) the image in U∪V
  have hImageW : ((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left)))).f mj (((singularChains ℤ (TopCat.of ↥(U ∩ V)))).iCycles mj s)
      = cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) φA) mj ((capIdx k mj) ▸ α₂) := by
    rw [hiCyc_s, map_add]
    rw [show ((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left)))).f mj capI = cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) ((pdCohUnderCycle (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L)) (k + 1) u)) mj ((capIdx k mj) ▸ α₂) from hcapM]
    rw [show ((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left)))).f mj w₂
        = cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) χ) mj ((capIdx k mj) ▸ α₂) from hw]
    show (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) ((pdCohUnderCycle (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L)) (k + 1) u)) mj) ((capIdx k mj) ▸ α₂)
        + (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) χ) mj) ((capIdx k mj) ▸ α₂)
      = (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) φA) mj) ((capIdx k mj) ▸ α₂)
    rw [← LinearMap.add_apply, ← cap_add', hsum]
  -- (8d) the two goals
  refine ⟨s, ?_, ?_⟩
  · rw [pdInter_inclChains_comp (S := U ∩ V) (W := U ∪ V) hIW mj (((singularChains ℤ (TopCat.of ↥(U ∩ V)))).iCycles mj s)]
    rw [hImageW]
  · have hb0 : ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).homologyπ mj b = 0 := by
      rw [show b = (-((-1 : ℤ) ^ k)) • ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).toCycles (mj + 1) mj y from rfl]
      rw [pdInter_map_zsmul, homologyπ_toCycles_C, zsmul_zero]
    have hs : ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).homologyπ mj s = ((singularChains ℤ (TopCat.of ↥(U ∩ V)))).homologyπ mj y₀ := by
      rw [show s = y₀ + b from rfl, map_add, hb0, add_zero]
    rw [hs]
    rw [show y₀ = relCapPairZ (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))
        (k + 1) mj z γ₂' from rfl]
    rw [← hgd₀]
    -- (8f): the two sides differ only in the proof of the degree equality, so `rw` closes the goal

end Work.Cohomology
