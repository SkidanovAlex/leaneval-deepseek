import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_goodD_incl
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.pd_hatcher_decomp
import Submission.Work.Cohomology.pd_hatcher_cycles_inter
import Submission.Work.Cohomology.pd_union_crux_zero
import Submission.Work.Cohomology.pd_union_extend
import Submission.Work.Cohomology.pd_ab_clean
import Submission.Work.Cohomology.pdABCoh_quasiIso
import Submission.Work.Cohomology.pdABdelta_natural
import Submission.Work.Cohomology.pd_glue2
import Submission.Work.Cohomology.cap_cochainDiff_mem_range
import Submission.Work.Cohomology.pd_localFundClass_of_cycle
import Submission.Work.Cohomology.pd_goodD_rep
import Submission.Work.Cohomology.pd_union_aux
import Submission.Work.Cohomology.mem_range_inclChains_of_image
import Submission.Work.Cohomology.pdHom_iUnion_kill
import Submission.Work.Cohomology.pdABInclRel_comp_pdABEnlarge
import Submission.Work.Cohomology.pd_ab_enlarge
import Submission.Work.Cohomology.pd_localFundClass_natural
import Submission.Work.Cohomology.cap_natural
import Submission.Work.Cohomology.pd_relsub_aux
import Submission.Work.Cohomology.pd_crux


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section


/-- **A chain of `W` lying in the chains of the trace `pdTr W S` lifts to a chain of `S`.**
(Copy of `Work.Cohomology.mem_range_pdIncl_of_mem_range_pdTr` from `pd_glue3`.) -/
theorem mem_range_pdIncl_of_mem_range_pdTr {M : TopCat} {W S : Set M} (h : S ⊆ W) {n : ℕ}
    {y : (singularChains ℤ (TopCat.of W)).X n}
    (hy : y ∈ LinearMap.range ((inclChains (TopCat.of W) (pdTr W S)).f n).hom) :
    y ∈ LinearMap.range ((chainMap ℤ (TopCat.of S) (TopCat.of W) (pdIncl W S h)).f n).hom := by
  obtain ⟨z, rfl⟩ := hy
  refine ⟨(ModuleCat.Hom.hom ((chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S)
    (pdTrInv h)).f n)) z, ?_⟩
  have hkey : (ModuleCat.Hom.hom (((chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S)
        (pdTrInv h)) ≫ inclChainsSub M S W h).f n)) z
      = (ModuleCat.Hom.hom ((inclChains (TopCat.of W) (pdTr W S)).f n)) z := by
    rw [← inclChains_eq_pdTrInv (M := M) h]
  have hsub : inclChainsSub M S W h
      = chainMap ℤ (TopCat.of S) (TopCat.of W) (pdIncl W S h) := rfl
  rw [hsub] at hkey
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hkey
  exact hkey



set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

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

theorem pd_inter_lift {M : TopCat} {U V : Set M} {k mj : ℕ}
    (χ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) k)
    (α₂ : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X (k + (mj + 1)))
    (hα₂ : α₂ ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdTr (U ∪ V) (U ∩ V))).f (k + (mj + 1))).hom) :
    ∃ y : (singularChains ℤ (TopCat.of ↥(U ∩ V))).X (mj + 1),
      (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V))
        (pdIncl (U ∪ V) (U ∩ V)
          (Set.inter_subset_left.trans Set.subset_union_left))).f (mj + 1) y
        = cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ (mj + 1) α₂ := by
  have h1 : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ (mj + 1) α₂
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdTr (U ∪ V) (U ∩ V))).f (mj + 1)).hom :=
    cap_mem_range_inclChains (M := TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) (U ∩ V))
      k (mj + 1) χ hα₂
  have h2 := mem_range_pdIncl_of_mem_range_pdTr (M := M) (W := U ∪ V) (S := U ∩ V)
    (Set.inter_subset_left.trans Set.subset_union_left) (n := mj + 1) h1
  obtain ⟨y, hy⟩ := h2
  exact ⟨y, hy⟩


private lemma pd_inter_capchi_zsmul (s : ℤ) (hs : s * s = 1) {A : Type*} [AddCommGroup A]
    (dc c : A) (h : dc = s • (0 - c)) : c = (-s) • dc := by
  rw [h, neg_zsmul, ← mul_zsmul, hs, one_smul, neg_sub, sub_zero]

theorem pd_inter_capchi {M : TopCat} {U V : Set M} {K L : Set M} {k mj : ℕ}
    (χ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) k)
    (α₂ : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X (k + (mj + 1)))
    (hχK : χ ∈ relKern ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) K) k)
    (hχL : χ ∈ relKern ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) L) k)
    (hdα₂ : ∃ (g e f : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X (k + mj)),
        (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₂ = g - e - f ∧
        g ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdRelSub (U ∪ V) (K ∪ L))).f (k + mj)).hom ∧
        e ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdRelSub (U ∪ V) L)).f (k + mj)).hom ∧
        f ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdRelSub (U ∪ V) K)).f (k + mj)).hom) :
    cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
        (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) χ) mj
        ((capIdx k mj) ▸ α₂)
      = -((-1 : ℤ) ^ k) • (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (mj + 1) mj
          (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ (mj + 1) α₂) := by
  obtain ⟨g, e, f, hd, hg, he, hf⟩ := hdα₂
  -- `(W∖(K∪L)) ⊆ (W∖K)`, so `χ` (relative for `K`) kills the first summand of `d α₂`
  have hsub : pdRelSub (U ∪ V) (K ∪ L) ⊆ pdRelSub (U ∪ V) K := by
    intro y hy hyK
    exact hy (Or.inl hyK)
  have hg0 : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ mj g = 0 :=
    cap_eq_zero_of_mem_range_inclChains (TopCat.of ↥(U ∪ V)) _ _ hsub χ hχK hg
  have he0 : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ mj e = 0 :=
    cap_eq_zero_of_mem_range_inclChains (TopCat.of ↥(U ∪ V)) _ _ (fun _ h => h) χ hχL he
  have hf0 : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ mj f = 0 :=
    cap_eq_zero_of_mem_range_inclChains (TopCat.of ↥(U ∪ V)) _ _ (fun _ h => h) χ hχK hf
  -- hence `χ` kills `d α₂`
  have hzero : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ mj
      ((ModuleCat.Hom.hom (((TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))).chainComplex
        (ModuleCat.of ℤ ℤ)).d (k + (mj + 1)) (k + mj))) α₂) = 0 := by
    rw [show (ModuleCat.Hom.hom (((TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))).chainComplex
        (ModuleCat.of ℤ ℤ)).d (k + (mj + 1)) (k + mj))) α₂
        = (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₂ from rfl]
    rw [hd, map_sub, map_sub, hg0, he0, hf0]
    simp
  have hs : ((-1:ℤ)^k) * ((-1:ℤ)^k) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩
  -- the boundary formula `cap_d` for `χ`, with the vanishing term removed
  have hz : (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (mj + 1) mj
        (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ (mj + 1) α₂)
      = ((-1:ℤ)^k) • ((0 : ↑(((TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))).chainComplex
            (ModuleCat.of ℤ ℤ)).X mj))
          - cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
          (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) χ) mj
          ((capIdx k mj) ▸ α₂)) := by
    have h := cap_d ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) (m := mj) χ α₂
    rw [hzero] at h
    exact h.trans (int_smul_eq_zsmul (inferInstance : Module ℤ
      (↑(((TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))).chainComplex (ModuleCat.of ℤ ℤ)).X mj)))
      ((-1:ℤ)^k) (0 - cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
          (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) χ) mj
          ((capIdx k mj) ▸ α₂)))
  exact pd_inter_capchi_zsmul ((-1:ℤ)^k) hs _ _ hz




/-! ## The duality computation on the intersection slot -/

/-- The cochain underlying a relative cochain, with the `Cochain` type made explicit. -/
abbrev kcUnder (X : TopCat) (A : Set X) (n : ℕ) (x : (relComplex ℤ X A).X n) :
    Cochain ℤ (TopCat.toSSet.obj X) n := x.1

/-- The cochain underlying a relative cycle. -/
abbrev kcUnderCycle (X : TopCat) (A : Set X) (n : ℕ) (z : (relComplex ℤ X A).cycles n) :
    Cochain ℤ (TopCat.toSSet.obj X) n :=
  kcUnder X A n ((relComplex ℤ X A).iCycles n z)


end


/-! ## Duality on the intersection slot (copy of `pd_inter_rep`) -/

namespace PDSplitKC
/-- **The duality computation on the `U ∩ V`-slot** (reproduction of
`Work.Cohomology.pd_inter_rep`, in a form that avoids importing `pd_glue3`). -/

theorem pd_split_duality {M : TopCat} [T2Space M] {k mj : ℕ}
    (c : (singularChains ℤ M).homology (k + (mj + 1)))
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    {K L : Set M} (hKc : IsCompact K) (hLc : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (φA : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k)
    (u : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K ∩ L))).cycles (k + 1))
    (χ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k)
    (hχK : χ ∈ relKern ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K) k)
    (hχL : χ ∈ relKern ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) L) k)
    (hχd : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) χ
        = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φA
          - kcUnderCycle (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L))
              (k + 1) u)
    (α₂ : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X (k + (mj + 1)))
    (hα₂ : α₂ ∈ LinearMap.range ((inclChains (TopCat.of (U ∪ V : Set M))
        (pdTr (U ∪ V) (U ∩ V))).f (k + (mj + 1))).hom)
    (hdα₂ : ∃ (g e f : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X (k + mj)),
        (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k + (mj + 1)) (k + mj) α₂ = g - e - f ∧
        g ∈ LinearMap.range ((inclChains (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K ∪ L))).f (k + mj)).hom ∧
        e ∈ LinearMap.range ((inclChains (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) L)).f (k + mj)).hom ∧
        f ∈ LinearMap.range ((inclChains (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K)).f (k + mj)).hom)
    (ξ : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).X (k + (mj + 1)))
    (hξ : (chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (U ∪ V : Set M))
              (pdIncl (U ∪ V : Set M) (U ∩ V : Set M)
                (Set.inter_subset_left.trans Set.subset_union_left))).f (k + (mj + 1)) ξ = α₂)
    (γ₂ : (relChains (TopCat.of (U ∩ V : Set M))
            (pdRelSub (U ∩ V : Set M) (K ∩ L))).cycles (k + (mj + 1)))
    (hγ₂ : (relChains (TopCat.of (U ∩ V : Set M))
            (pdRelSub (U ∩ V : Set M) (K ∩ L))).iCycles (k + (mj + 1)) γ₂
        = ((CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of (U ∩ V : Set M))
            (pdRelSub (U ∩ V : Set M) (K ∩ L)))).f (k + (mj + 1))) ξ)
    (hγ₂c : (relChains (TopCat.of (U ∩ V : Set M))
            (pdRelSub (U ∩ V : Set M) (K ∩ L))).homologyπ (k + (mj + 1)) γ₂
        = localFundClass (k + (mj + 1)) c (U ∩ V) hI (K ∩ L)
            (Set.inter_subset_inter hKU hLV) (hKc.inter hLc)) :
    ∃ (s : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).cycles mj),
      (inclChains M (U ∩ V : Set M)).f mj
          ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).iCycles mj s)
        = (inclChains M (U ∪ V : Set M)).f mj
            (cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)))
              (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φA) mj
              ((capIdx k mj) ▸ α₂))
      ∧ goodD (k + (mj + 1)) c (U ∩ V) hI (K ∩ L)
          (Set.inter_subset_inter hKU hLV) (hKc.inter hLc) (k + 1) mj (by omega)
          (HomologicalComplex.homologyMap
            (relComplexMap ℤ (pdRelSub (U ∩ V : Set M) (K ∩ L))
              (pdRelSub (U ∪ V : Set M) (K ∩ L))
              (pdIncl (U ∪ V : Set M) (U ∩ V : Set M)
                (Set.inter_subset_left.trans Set.subset_union_left))
              (fun y hy => hy)) (k + 1)
            ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) (K ∩ L))).homologyπ (k + 1) u))
        = (singularChains ℤ (TopCat.of (U ∩ V : Set M))).homologyπ mj s := by
  classical
  let ψmap : relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) ⟶ relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L)) :=
    relComplexMap ℤ (X₁ := (TopCat.of (U ∩ V : Set M))) (X₂ := (TopCat.of (U ∪ V : Set M))) (pdRelSub (U ∩ V : Set M) (K ∩ L)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left)) (fun y hy => hy)
  let z : (relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L))).cycles (k + 1) := (HomologicalComplex.cyclesMap ψmap (k + 1)).hom u
  -- (1) the cochain of the restricted cycle is the pullback of the cochain of `u`
  have hzy : (((relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L))).iCycles (k + 1)).hom z).1
      = (kcUnder (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (k + 1)
          ((relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L))).iCycles (k + 1) u)).comp ((chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left))).f (k + 1)).hom := by
    have h1 : (((relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L))).iCycles (k + 1)).hom z).1
        = (((ψmap.f (k + 1)).hom ((relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L))).iCycles (k + 1) u)).1) :=
      congrArg Subtype.val (pdInter_iCycles_cyclesMap_apply ψmap (k + 1) u)
    have hψf : ψmap.f (k + 1)
        = ModuleCat.ofHom (relMapLM ℤ (pdRelSub (U ∩ V : Set M) (K ∩ L)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left)) (fun y hy => hy) (k + 1)) :=
      relComplexMap_f ℤ (pdRelSub (U ∩ V : Set M) (K ∩ L)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left)) (fun y hy => hy) (k + 1)
    have hcp : ((dualChainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left))).f (k + 1))
        = cochainPullbackHom ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left)) (k + 1) := rfl
    rw [h1, hψf]
    change (relMapLM ℤ (pdRelSub (U ∩ V : Set M) (K ∩ L)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left)) (fun y hy => hy) (k + 1) ((relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L))).iCycles (k + 1) u)).1
      = (kcUnder (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (k + 1) ((relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L))).iCycles (k + 1) u)).comp ((chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left))).f (k + 1)).hom
    rw [relMapLM_coe, hcp]
    apply LinearMap.ext
    intro c
    rw [LinearMap.comp_apply]
    exact cochainPullbackHom_apply ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left)) (k + 1) (kcUnder (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (k + 1) ((relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L))).iCycles (k + 1) u)) c
  -- (2) the chain of `U ∩ V` whose image under the inclusion is the cap product of `χ`
  obtain ⟨b, hb⟩ := pd_inter_lift (M := M) (U := U) (V := V) (k := k) (mj := mj) χ α₂ hα₂
  -- (3) the image of `s` in `M` agrees with the cap product of `dφA`
  have hKXeq : (chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left))) = inclChainsSub M (U ∩ V) (U ∪ V) (Set.inter_subset_left.trans Set.subset_union_left) :=
    pdIncl_eq_inclChainsSub (Set.inter_subset_left.trans Set.subset_union_left)
  have hξγ' : (relChains (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L))).iCycles ((k + 1) + mj) ((capIdx k mj) ▸ γ₂)
      = ((cokernel.π (inclChains (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L)))).f ((k + 1) + mj)) ((capIdx k mj) ▸ ξ) := by
    rw [pdInter_cast_iCycles_rel, pdInter_cast_cokerπ]
    exact congrArg (fun t : (relChains (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L))).X (k + (mj + 1)) => (capIdx k mj) ▸ t) hγ₂
  have hbcorr : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).iCycles mj ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).toCycles (mj + 1) mj ((-((-1 : ℤ) ^ k)) • b))
      = -((-1 : ℤ) ^ k) • (singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (mj + 1) mj b := by
    rw [toCycles_i_C]
    exact map_zsmul (ModuleCat.Hom.hom ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (mj + 1) mj))
      (-((-1 : ℤ) ^ k)) b
  have hIs : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).iCycles mj
        (relCapPairZ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L)) (k + 1) mj z ((capIdx k mj) ▸ γ₂) + ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).toCycles (mj + 1) mj ((-((-1 : ℤ) ^ k)) • b)))
      = (singularChains ℤ (TopCat.of (U ∩ V : Set M))).iCycles mj (relCapPairZ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L)) (k + 1) mj z ((capIdx k mj) ▸ γ₂))
        + (-((-1 : ℤ) ^ k)) • (singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (mj + 1) mj b := by
    rw [map_add, hbcorr]
  have hIMeq : (inclChains M (U ∩ V : Set M)).f mj ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).iCycles mj
        (relCapPairZ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L)) (k + 1) mj z ((capIdx k mj) ▸ γ₂) + ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).toCycles (mj + 1) mj ((-((-1 : ℤ) ^ k)) • b))))
      = (inclChains M (U ∪ V : Set M)).f mj (((chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left))).f mj) ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).iCycles mj
        (relCapPairZ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L)) (k + 1) mj z ((capIdx k mj) ▸ γ₂) + ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).toCycles (mj + 1) mj ((-((-1 : ℤ) ^ k)) • b))))) := by
    rw [hKXeq]
    have hcomp := congrArg (fun (g : singularChains ℤ (TopCat.of (U ∩ V : Set M)) ⟶ singularChains ℤ M) =>
      (g.f mj).hom ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).iCycles mj
        (relCapPairZ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L)) (k + 1) mj z ((capIdx k mj) ▸ γ₂) + ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).toCycles (mj + 1) mj ((-((-1 : ℤ) ^ k)) • b)))))
      (inclChainsSub_comp M (U ∩ V) (U ∪ V) (Set.inter_subset_left.trans Set.subset_union_left))
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
    exact hcomp.symm
  have hKXd : ((chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left))).f mj) ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (mj + 1) mj b)
      = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (mj + 1) mj
          (cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) χ (mj + 1) α₂) := by
    have hcomm := congrArg (fun (g : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).X (mj + 1) ⟶
        (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X mj) => g b) (((chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left)))).comm (mj + 1) mj)
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
    rw [hb] at hcomm
    exact hcomm.symm
  have hcapnat : ((chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left))).f mj) ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).iCycles mj
        (relCapPairZ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L)) (k + 1) mj z ((capIdx k mj) ▸ γ₂)))
      = cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (kcUnder (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (k + 1) ((relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L))).iCycles (k + 1) u)) mj ((capIdx k mj) ▸ α₂) := by
    rw [relCapPairZ_iCycles_apply (X := (TopCat.of (U ∩ V : Set M))) (n := k + 1) (m := mj) (pdRelSub (U ∩ V : Set M) (K ∩ L)) z ((capIdx k mj) ▸ γ₂) hξγ', hzy]
    rw [pdInter_cap_natural (M := M) (S := U ∩ V) (W := U ∪ V) (k := k + 1) (m := mj) (Set.inter_subset_left.trans Set.subset_union_left)
      (kcUnder (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (k + 1) ((relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L))).iCycles (k + 1) u))
      ((capIdx k mj) ▸ ξ)]
    congr 1
    rw [pdInter_cast_chainMap (X := (TopCat.of (U ∩ V : Set M))) (Y := (TopCat.of (U ∪ V : Set M))) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left)) (capIdx k mj) ξ, hξ]
  have hcapchi := pd_inter_capchi (M := M) (U := U) (V := V) (K := K) (L := L)
    (k := k) (mj := mj) χ α₂ hχK hχL hdα₂
  have hχd' : kcUnder (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (k + 1) ((relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L))).iCycles (k + 1) u)
        + cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) χ
      = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φA := by
    rw [hχd]; abel
  have hKs : ((chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left))).f mj) ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).iCycles mj
        (relCapPairZ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L)) (k + 1) mj z ((capIdx k mj) ▸ γ₂) + ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).toCycles (mj + 1) mj ((-((-1 : ℤ) ^ k)) • b))))
      = cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φA) mj ((capIdx k mj) ▸ α₂) := by
    have hcch : (-((-1 : ℤ) ^ k)) • (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (mj + 1) mj
          (cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) χ (mj + 1) α₂)
        = cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) χ) mj ((capIdx k mj) ▸ α₂) := hcapchi.symm
    have hca : cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)))
          (kcUnder (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (k + 1) ((relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L))).iCycles (k + 1) u)
            + cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) χ) mj ((capIdx k mj) ▸ α₂)
        = (cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (kcUnder (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (k + 1) ((relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L))).iCycles (k + 1) u)) mj ((capIdx k mj) ▸ α₂))
          + (cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) χ) mj ((capIdx k mj) ▸ α₂)) := by
      rw [cap_add', LinearMap.add_apply]
    rw [hIs, map_add, map_zsmul, hcapnat, hKXd, hcch, ← hca, hχd']
  -- (4) the goodD of the restricted class is the homology class of `s`
  have hzclass : (HomologicalComplex.homologyMap ψmap (k + 1)).hom
        ((relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) (K ∩ L))).homologyπ (k + 1) u)
      = (relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L))).homologyπ (k + 1) z :=
    pdInter_homologyMap_homologyπ_cyclesMap ψmap (k + 1) u
  have hγ₂'' : (relChains (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L))).homologyπ ((k + 1) + mj) ((capIdx k mj) ▸ γ₂)
      = (capIdx k mj).symm ▸ localFundClass (k + (mj + 1)) c (U ∩ V) hI (K ∩ L) (Set.inter_subset_inter hKU hLV) (IsCompact.inter hKc hLc) := by
    rw [pdInter_cast_homologyπ_rel, hγ₂c]
  have hgdB : goodD (k + (mj + 1)) c (U ∩ V) hI (K ∩ L) (Set.inter_subset_inter hKU hLV) (IsCompact.inter hKc hLc) (k + 1) mj (by omega)
        ((relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L))).homologyπ (k + 1) z)
      = (singularChains ℤ (TopCat.of (U ∩ V : Set M))).homologyπ mj
          (relCapPairZ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L)) (k + 1) mj z ((capIdx k mj) ▸ γ₂)) :=
    goodD_homologyπ c (U ∩ V) hI (K ∩ L) (Set.inter_subset_inter hKU hLV) (IsCompact.inter hKc hLc) (k + 1) mj ((capIdx k mj).symm)
      z ((capIdx k mj) ▸ γ₂) hγ₂'' ((capIdx k mj) ▸ ξ) hξγ'
  refine ⟨relCapPairZ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V : Set M) (K ∩ L)) (k + 1) mj z ((capIdx k mj) ▸ γ₂) + ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).toCycles (mj + 1) mj ((-((-1 : ℤ) ^ k)) • b)), ?_, ?_⟩
  · rw [hIMeq, hKs]
  · have eh : (relComplexMap ℤ (pdRelSub (U ∩ V : Set M) (K ∩ L)) (pdRelSub (U ∪ V : Set M) (K ∩ L)) (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) (Set.inter_subset_left.trans Set.subset_union_left)) (fun y hy => hy)) = ψmap := rfl
    rw [eh, hzclass, hgdB]
    rw [map_add, homologyπ_toCycles_C ℤ (singularChains ℤ (TopCat.of (U ∩ V : Set M))) (mj + 1) mj
      ((-((-1 : ℤ) ^ k)) • b), add_zero]

end PDSplitKC

end Work.Cohomology
