import Mathlib
import Submission.Work.Cohomology.relChains_vanishing_compact_specific
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.Cohomology.relChains_empty_homology_iso
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.mem_range_inclChains_of_image
import Submission.Work.Cohomology.pd_union_aux
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.pd_hatcher_decomp
import Submission.Work.Cohomology.Sd_comm
import Submission.Work.Cohomology.smallLift_cov
import Submission.Work.Cohomology.homology_vanishing_relative_compact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `H_m(W) = 0` for `W ⊆ ℝᴺ` open and `m > N`

The singular homology of an open subset of `ℝᴺ` vanishes strictly above the dimension.  This is
the "dimension bound" for an `N`-manifold: Hatcher, *Algebraic Topology*, Lemma 3.27(b) gives the
relative vanishing `H_i(M, M∖A) = 0` for `A` compact and `i > N`, and the long exact sequence of
the triple `(W∖A) ⊆ (W∖(A∖U)) ⊆ W` converts it into the vanishing of `H_m(U)` for any open `U`
contained in a compact subset of `W`.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## The support of a singular chain -/

/-- **The support of a singular chain is compact.**  Every chain of `C_n(X)` is a finite
`ℤ`-linear combination of generators `1 • σ`, each of which has compact image in `X`; the union of
finitely many of those images is therefore compact, and it contains the support of the chain. -/
theorem exists_compact_range_of_chain {X : TopCat} (n : ℕ) (c : (singularChains ℤ X).X n) :
    ∃ K : Set X, IsCompact K ∧ c ∈ LinearMap.range ((inclChains X K).f n).hom := by
  classical
  set co := Crux33.coords (TopCat.toSSet.obj X) n c with hco
  set K : Set X := ⋃ σ ∈ co.support, simplexRange X σ with hK
  have hKc : IsCompact K := by
    rw [hK]
    exact Finset.isCompact_biUnion co.support (fun σ _ => isCompact_simplexRange X σ)
  refine ⟨K, hKc, ?_⟩
  have hsum : c = ∑ σ ∈ co.support, (co σ) • gen X n σ := by
    have h := Crux33.chain_eq_sum_gen (TopCat.toSSet.obj X) n c
    exact h
  rw [hsum]
  refine Submodule.sum_mem _ (fun σ hσ => ?_)
  have hrange : Set.range (fun z : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌) σ z) ⊆ K := by
    intro w hw
    rw [hK]
    exact Set.mem_iUnion₂.mpr ⟨σ, hσ, by simpa [simplexRange] using hw⟩
  obtain ⟨τ, hτ⟩ := exists_map_inclUX_of_range_subset K (Opposite.op ⦋n⦌) σ hrange
  have hgen : gen X n σ ∈ LinearMap.range ((inclChains X K).f n).hom := by
    refine ⟨gen (TopCat.of K) n τ, ?_⟩
    have h1 : (ModuleCat.Hom.hom ((inclChains X K).f n)) (gen (TopCat.of K) n τ)
        = gen X n ((TopCat.toSSet.map (inclUX K)).app (Opposite.op ⦋n⦌) τ) :=
      chainComplexMap_ι_apply (TopCat.toSSet.map (inclUX K)) n τ 1
    rw [h1, hτ]
  exact AddSubgroup.zsmul_mem (LinearMap.range ((inclChains X K).f n).hom).toAddSubgroup hgen (co σ)

/-! ## Descending a chain supported in an open subspace -/

/-- The differential of a cycle is zero. -/
lemma iCycles_d_apply {K : ChainComplex (ModuleCat ℤ) ℕ} (i : ℕ) [K.HasHomology i]
    (z : K.cycles i) : K.d i (i - 1) ((K.iCycles i) z) = 0 :=
  CategoryTheory.ConcreteCategory.congr_hom (HomologicalComplex.iCycles_d K i (i - 1)) z

/-- **The class of a cycle supported in a subspace vanishes as soon as the homology of that
subspace vanishes.**  If the underlying chain of the cycle `γ` lies in the image of
`C_*(U) ⟶ C_*(W)` for an open `U ⊆ ↥W`, and `H_m(U) = 0`, then `[γ] = 0` in `H_m(W)`. -/
theorem homologyπ_eq_zero_of_support {N : ℕ} {W : Set (EuclideanSpace ℝ (Fin N))} (m : ℕ)
    (U : Set ↥W) (hU : IsOpen U)
    {γ : (singularChains ℤ (TopCat.of ↥W)).cycles m}
    (hγ : (singularChains ℤ (TopCat.of ↥W)).iCycles m γ
        ∈ LinearMap.range ((inclChains (TopCat.of ↥W) U).f m).hom)
    (hsub : Subsingleton ((singularChains ℤ (TopCat.of U)).homology m)) :
    (HomologicalComplex.homologyπ (singularChains ℤ (TopCat.of ↥W)) m γ) = 0 := by
  obtain ⟨c', hc'⟩ := hγ
  have hd : (singularChains ℤ (TopCat.of U)).d m (m - 1) c' = 0 := by
    apply inclChains_f_injective (TopCat.of ↥W) U (m - 1)
    have hcomm := HomologicalComplex.Hom.comm (inclChains (TopCat.of ↥W) U) m (m - 1)
    have h1 : (inclChains (TopCat.of ↥W) U).f (m - 1)
          ((singularChains ℤ (TopCat.of U)).d m (m - 1) c')
        = (singularChains ℤ (TopCat.of ↥W)).d m (m - 1)
          ((inclChains (TopCat.of ↥W) U).f m c') := by
      have h := CategoryTheory.ConcreteCategory.congr_hom hcomm c'
      simp only [CategoryTheory.ConcreteCategory.comp_apply] at h
      exact h.symm
    rw [h1, hc']
    simpa using iCycles_d_apply m γ
  set γ' : (singularChains ℤ (TopCat.of U)).cycles m := cycleOf m c' hd with hγ'def
  haveI : Subsingleton ↥((singularChains ℤ (TopCat.of U)).homology m) := hsub
  have hzero : HomologicalComplex.homologyπ (singularChains ℤ (TopCat.of U)) m γ' = 0 :=
    Subsingleton.elim _ _
  have hcyc : HomologicalComplex.cyclesMap (inclChains (TopCat.of ↥W) U) m γ' = γ := by
    have hinj := (ModuleCat.mono_iff_injective
      (HomologicalComplex.iCycles (singularChains ℤ (TopCat.of ↥W)) m)).mp inferInstance
    apply hinj
    have hcm := CategoryTheory.ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (inclChains (TopCat.of ↥W) U) m) γ'
    simp only [CategoryTheory.ConcreteCategory.comp_apply] at hcm
    rw [hcm, iCycles_cycleOf]
    exact hc'
  calc (HomologicalComplex.homologyπ (singularChains ℤ (TopCat.of ↥W)) m γ)
      = HomologicalComplex.homologyMap (inclChains (TopCat.of ↥W) U) m
          (HomologicalComplex.homologyπ (singularChains ℤ (TopCat.of U)) m γ') := by
        have hnat := CategoryTheory.ConcreteCategory.congr_hom
          (HomologicalComplex.homologyπ_naturality (inclChains (TopCat.of ↥W) U) m) γ'
        simp only [CategoryTheory.ConcreteCategory.comp_apply] at hnat
        rw [← hcyc]
        exact hnat.symm
    _ = HomologicalComplex.homologyMap (inclChains (TopCat.of ↥W) U) m 0 := by rw [hzero]
    _ = 0 := by simp

/-! ## The triple sequence step -/

/-- **The middle term of the homology long exact sequence of a triple.**  If the relative homology
of the pair `(M, M∖S)` vanishes in degree `i` and that of `(M, M∖T)` vanishes in degree `i + 1`,
for a triple `S ⊆ T ⊆ M`, then the relative homology of the model `(T, S)` of the triple vanishes
in degree `i`. -/
theorem isZero_homology_coker_of_triple {M : TopCat} {S T : Set M} (hST : S ⊆ T) (i : ℕ)
    (h2 : IsZero ((relChains M S).homology i))
    (h3 : IsZero ((relChains M T).homology (i + 1))) :
    IsZero ((cokernel (inclChainsSub M S T hST)).homology i) := by
  let SEX : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := tripleShort M S T hST
  have hSEX : SEX.ShortExact := relChains_triple_shortExact M S T hST
  have h2' : IsZero (SEX.X₂.homology i) := h2
  have h3' : IsZero (SEX.X₃.homology (i + 1)) := h3
  have hd0 : ModuleCat.Hom.hom (hSEX.δ (i + 1) i (by simp [ComplexShape.down])) = 0 := by
    rw [IsZero.eq_zero_of_src (show IsZero (SEX.X₃.homology (i + 1)) from h3')
      (hSEX.δ (i + 1) i (by simp [ComplexShape.down]))]
    exact ModuleCat.hom_zero
  have hex1 := hSEX.homology_exact₁ (i + 1) i (by simp [ComplexShape.down])
  have hker : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap SEX.f i)) = ⊥ := by
    have h := CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hex1
    rw [hd0, LinearMap.range_zero] at h
    exact h.symm
  have hinj : Function.Injective ⇑(ModuleCat.Hom.hom (HomologicalComplex.homologyMap SEX.f i)) :=
    LinearMap.ker_eq_bot.mp hker
  haveI hsub2 : Subsingleton ↥(SEX.X₂.homology i) := ModuleCat.isZero_iff_subsingleton.mp h2'
  have hsub1 : Subsingleton ↥(SEX.X₁.homology i) :=
    ⟨fun a b => hinj (Subsingleton.elim (α := ↥(SEX.X₂.homology i)) _ _)⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr hsub1


/-! ## The main theorem -/

theorem euclidean_open_homology_gt_vanishing {N : ℕ} (hN : 1 ≤ N)
    (W : Set (EuclideanSpace ℝ (Fin N))) (hW : IsOpen W) :
    ∀ m, N < m → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥W)).homology m) := by
  intro m hm
  have key : ∀ γ : (singularChains ℤ (TopCat.of ↥W)).cycles m,
      (singularChains ℤ (TopCat.of ↥W)).homologyπ m γ = 0 := by
    intro γ
    set c := (singularChains ℤ (TopCat.of ↥W)).iCycles m γ with hc
    obtain ⟨K, hKc, hKmem⟩ := exists_compact_range_of_chain m c
    set K' : Set (EuclideanSpace ℝ (Fin N)) := Subtype.val '' K with hK'def
    have hK'c : IsCompact K' := hKc.image continuous_subtype_val
    have hK'W : K' ⊆ W := by rintro y ⟨z, -, rfl⟩; exact z.2
    obtain ⟨δ, hδpos, hδsub⟩ := hK'c.exists_cthickening_subset_open hW hK'W
    set Ut : Set (EuclideanSpace ℝ (Fin N)) := Metric.thickening (δ / 2) K' with hUtdef
    set A : Set (EuclideanSpace ℝ (Fin N)) := Metric.cthickening (δ / 2) K' with hAdef
    have hUtopen : IsOpen Ut := Metric.isOpen_thickening
    have hUtA : Ut ⊆ A := Metric.thickening_subset_cthickening _ _
    have hAc : IsCompact A := hK'c.cthickening
    have hAW : A ⊆ W := fun y hy => hδsub (Metric.cthickening_mono (by linarith) K' hy)
    have hK'Ut : K' ⊆ Ut := Metric.self_subset_thickening (by linarith) K'
    have hCc : IsCompact (A \ Ut) :=
      hAc.of_isClosed_subset (hAc.isClosed.sdiff hUtopen) Set.sdiff_subset
    have hCW : A \ Ut ⊆ W := fun y hy => hAW hy.1
    set Vl : Set ↥W := pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W A with hVldef
    set Zl : Set ↥W :=
      pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (A \ Ut) with hZldef
    have hVZ : Vl ⊆ Zl :=
      pdRelSub_mono (M := TopCat.of (EuclideanSpace ℝ (Fin N))) (W := W)
        (K := A \ Ut) (K' := A) Set.sdiff_subset
    have h2 : IsZero ((relChains (TopCat.of ↥W) Vl).homology m) :=
      relChains_vanishing_compact_specific hN W hW A hAW hAc m hm
    have h3 : IsZero ((relChains (TopCat.of ↥W) Zl).homology (m + 1)) :=
      relChains_vanishing_compact_specific hN W hW (A \ Ut) hCW hCc (m + 1) (by omega)
    have h1 : IsZero ((cokernel (inclChainsSub (TopCat.of ↥W) Vl Zl hVZ)).homology m) :=
      isZero_homology_coker_of_triple hVZ m h2 h3
    obtain ⟨e1⟩ := coker_inclChainsSub_homology_iso (M := TopCat.of ↥W) hVZ m
    set V2 : Set ↥Zl := {y | (y : ↥W) ∈ Vl} with hV2def
    have h4 : IsZero ((relChains (TopCat.of ↥Zl) V2).homology m) :=
      IsZero.of_iso h1 e1.symm
    set U2 : Set ↥Zl := {y | ((y : ↥W) : EuclideanSpace ℝ (Fin N)) ∈ Ut} with hU2def
    have hU2open : IsOpen U2 := by
      have hcont : Continuous (fun y : ↥Zl => ((y : ↥W) : EuclideanSpace ℝ (Fin N))) :=
        continuous_subtype_val.comp continuous_subtype_val
      exact hUtopen.preimage hcont
    have hV2open : IsOpen V2 := by
      have hcont : Continuous (fun y : ↥Zl => ((y : ↥W) : EuclideanSpace ℝ (Fin N))) :=
        continuous_subtype_val.comp continuous_subtype_val
      exact hAc.isClosed.isOpen_compl.preimage hcont
    have hcov : U2 ∪ V2 = Set.univ := by
      ext y
      constructor
      · intro _; trivial
      · intro _
        by_cases hyA : ((y : ↥W) : EuclideanSpace ℝ (Fin N)) ∈ A
        · left
          by_contra hyUt
          exact (y.2 : ((y : ↥W) : EuclideanSpace ℝ (Fin N)) ∉ (A \ Ut)) ⟨hyA, hyUt⟩
        · right
          exact hyA
    obtain ⟨e2⟩ := homologyTwoCover (TopCat.of ↥Zl) U2 V2 hU2open hV2open hcov m
    set U1 : Set ↥U2 := {y | (y : ↥Zl) ∈ V2} with hU1def
    have h5 : IsZero ((relChains (TopCat.of ↥U2) U1).homology m) :=
      IsZero.of_iso h4 e2.symm
    have hU1 : U1 = ∅ := by
      ext y
      constructor
      · intro hy
        exact hy (hUtA y.2)
      · intro hy
        exact (Set.notMem_empty y hy).elim
    rw [hU1] at h5
    have h5' : IsZero ((cokernel (inclChains (TopCat.of ↥U2) ∅)).homology m) := h5
    have hsubU2 : Subsingleton ↑((singularChains ℤ (TopCat.of ↥U2)).homology m) := by
      haveI : IsIso (HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of ↥U2) ∅)) m) :=
        relChains_empty_homology_iso (TopCat.of ↥U2) m
      exact ModuleCat.isZero_iff_subsingleton.mp
        (IsZero.of_iso h5' (asIso (HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of ↥U2) ∅)) m)))
    set Uw : Set ↥W := {z | (z : EuclideanSpace ℝ (Fin N)) ∈ Ut} with hUwdef
    have h7 : Subsingleton ↑((singularChains ℤ (TopCat.of ↥Uw)).homology m) := by
      have hhom : ↥Uw ≃ₜ ↥U2 := {
        toFun := fun z => ⟨⟨z.1, fun h => h.2 z.2⟩, z.2⟩
        invFun := fun w => ⟨w.1.1, w.2⟩
        left_inv := fun z => Subtype.ext rfl
        right_inv := fun w => Subtype.ext rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      exact subsingleton_homology_of_homeomorph (X := TopCat.of ↥Uw)
        (Y := TopCat.of ↥U2) hhom m hsubU2
    have hUwopen : IsOpen Uw := hUtopen.preimage continuous_subtype_val
    have hKUt : K ⊆ Uw := fun z hz => hK'Ut ⟨z, hz, rfl⟩
    have hsupp : (singularChains ℤ (TopCat.of ↥W)).iCycles m γ
        ∈ LinearMap.range ((inclChains (TopCat.of ↥W) Uw).f m).hom :=
      mem_range_inclChains_of_subset (M := TopCat.of ↥W) (S := K) (T := Uw) hKUt hKmem
    exact homologyπ_eq_zero_of_support m Uw hUwopen hsupp h7
  have hzero : ∀ x : ↥((singularChains ℤ (TopCat.of ↥W)).homology m), x = 0 := by
    intro x
    obtain ⟨γ, hγ⟩ := (ModuleCat.epi_iff_surjective
      ((singularChains ℤ (TopCat.of ↥W)).homologyπ m)).mp inferInstance x
    rw [← hγ]
    exact key γ
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => by rw [hzero a, hzero b]⟩

end

end Work.Cohomology
