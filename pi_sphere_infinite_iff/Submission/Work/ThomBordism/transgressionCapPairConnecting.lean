import Mathlib
import Submission.Work.ThomBordism.bdryInterfaces
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.CapH
import Submission.Work.Cohomology.cap_natural

/-!
# The transgression identity for the pair `(W, ∂W)`

For a topological space `X` and a subspace `A ⊆ X` the connecting maps of the long exact sequences
of the pair `(X,A)` in homology (`hPairδ`) and in cohomology (`pairδ`) are related to the cap
product by the **transgression identity**

`i_*(y ⌢ ∂w) = (δy) ⌢ w`   (`y ∈ H⁴(A)`, `w ∈ H₉(X,A)`).

Its proof is the Leibniz rule for the cap product: if `a ∈ C⁴(X)` lifts the cocycle `b = a|_A` and
`ŵ ∈ C₉(X)` lifts the relative cycle `w`, then with `x₁ ∈ C₈(A)` the chain with `i(x₁) = d ŵ`,

`(da) ⌢ ŵ = a ⌢ (dŵ) - d(a ⌢ ŵ)`  (`Work.Cohomology.cap_coboundary_formula`),

and the two sides are the chain representatives of `(δy) ⌢ w` and of `i_*(y ⌢ ∂w)` respectively.

This file proves the identity in the degrees needed for the boundary of a `NullBordismFamily`
(`H⁴(∂W)`, `H₉(W,∂W)`) and then the requested specialisation
`Work.ThomBordism.transgressionCapPairConnecting`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.ThomBordism

noncomputable section

/-! ## Elementary cycle lemmas for a chain complex -/

/-- `iCycles` of `cyclesMk`. -/
lemma iCycles_cyclesMk_C (C : ChainComplex (ModuleCat ℤ) ℕ) {n j : ℕ} (x : C.X n)
    (hj : (ComplexShape.down ℕ).next n = j) (hx : C.d n j x = 0) :
    C.iCycles n (HomologicalComplex.cyclesMk C x j hj hx) = x := by
  have h := HomologicalComplex.i_cyclesMk (K := C) (x := x) (j := j) (hj := hj) (hx := hx)
  simpa using h

/-- The underlying chain of a cycle is killed by the differential. -/
lemma iCycles_d_C (C : ChainComplex (ModuleCat ℤ) ℕ) (n j : ℕ) (c : C.cycles n) :
    C.d n j (C.iCycles n c) = 0 := by
  have h := congrArg (fun (g : C.cycles n ⟶ C.X j) => (ModuleCat.Hom.hom g) c)
    (HomologicalComplex.iCycles_d C n j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- `cyclesMk` of the underlying chain of a cycle is the cycle. -/
lemma cyclesMk_iCycles_C (C : ChainComplex (ModuleCat ℤ) ℕ) {n j : ℕ}
    (hj : (ComplexShape.down ℕ).next n = j) (c : C.cycles n)
    (hx : C.d n j (C.iCycles n c) = 0) :
    HomologicalComplex.cyclesMk C (C.iCycles n c) j hj hx = c := by
  apply Work.Cohomology.iCycles_injective_C ℤ C n
  rw [iCycles_cyclesMk_C]

/-- The elementwise form of the naturality of `homologyπ`. -/
lemma homologyMap_homologyπ_C (C D : ChainComplex (ModuleCat ℤ) ℕ) (φ : C ⟶ D) (n : ℕ)
    (z : C.cycles n) :
    HomologicalComplex.homologyMap φ n (C.homologyπ n z)
      = D.homologyπ n (HomologicalComplex.cyclesMap φ n z) := by
  have h := congrArg (fun (g : C.cycles n ⟶ D.homology n) => (ModuleCat.Hom.hom g) z)
    (HomologicalComplex.homologyπ_naturality φ n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The elementwise form of `cyclesMap_i`. -/
lemma iCycles_cyclesMap_C (C D : ChainComplex (ModuleCat ℤ) ℕ) (φ : C ⟶ D) (n : ℕ)
    (z : C.cycles n) :
    D.iCycles n (HomologicalComplex.cyclesMap φ n z) = (φ.f n) (C.iCycles n z) := by
  have h := congrArg (fun (g : C.cycles n ⟶ D.X n) => (ModuleCat.Hom.hom g) z)
    (HomologicalComplex.cyclesMap_i φ n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The elementwise form of the commutation of a chain map with the differential. -/
lemma chainMap_comm_apply' (C D : ChainComplex (ModuleCat ℤ) ℕ) (φ : C ⟶ D) (n m : ℕ)
    (x : C.X n) : D.d n m (φ.f n x) = φ.f m (C.d n m x) := by
  simpa using Work.Cohomology.chainMap_comm_apply C D φ n m x

/-- `iCycles` of `toCycles`. -/
lemma toCycles_i_C' (C : ChainComplex (ModuleCat ℤ) ℕ) (n m : ℕ) (x : C.X (n+1)) :
    C.iCycles m (C.toCycles (n+1) m x) = C.d (n+1) m x := by
  simpa using Work.Cohomology.toCycles_i_C ℤ C (n+1) m x

/-- `iCycles` of `toCycles`, in terms of `ModuleCat.Hom.hom`. -/
lemma toCycles_i_C'' (C : ChainComplex (ModuleCat ℤ) ℕ) (n m : ℕ) (x : C.X (n+1)) :
    C.iCycles m (C.toCycles (n+1) m x) = (C.d (n+1) m).hom x := by
  simpa using Work.Cohomology.toCycles_i_C ℤ C (n+1) m x

/-- `homologyπ` of `toCycles` vanishes. -/
lemma homologyπ_toCycles_C' (C : ChainComplex (ModuleCat ℤ) ℕ) (n m : ℕ) (x : C.X (n+1)) :
    C.homologyπ m (C.toCycles (n+1) m x) = 0 := by
  simpa using Work.Cohomology.homologyπ_toCycles_C ℤ C (n+1) m x

/-- Un-doing the degree transport of `Work.Cohomology.capIdx` in the cap product formula. -/
lemma capIdx_cast_eq (X : TopCat)
    (x : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X (4 + (4 + 1))) :
    ((Work.Cohomology.capIdx 4 4) ▸ x :
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X ((4 + 1) + 4)) = x := by
  cases Work.Cohomology.capIdx 4 4
  rfl

/-! ## The connecting map `hPairδ` on the class of a cycle -/

/-- **The connecting map `hPairδ` of the homology pair sequence on the class of a cycle.**  Given a
relative `9`-cycle `c` of `(X,A)`, a lift `x₂` of it to a `9`-chain of `X` and a chain `x₁` of `A`
with `i(x₁) = d x₂`, the boundary of the class of `c` is the class of `x₁`. -/
theorem hPairδ_homologyπ_eq {X : TopCat} {A : Set X}
    (c : (Work.Cohomology.relChains X A).cycles 9)
    (x₂ : (Work.Cohomology.singularChains ℤ X).X 9)
    (hx₂ : ((cokernel.π (Work.Cohomology.inclChains X A)).f 9) x₂
        = (Work.Cohomology.relChains X A).iCycles 9 c)
    (x₁ : (Work.Cohomology.singularChains ℤ (TopCat.of A)).X 8)
    (hx₁ : ((Work.Cohomology.inclChains X A).f 8) x₁
        = ((Work.Cohomology.singularChains ℤ X).d 9 8) x₂) :
    ∃ ζ : (Work.Cohomology.singularChains ℤ (TopCat.of A)).cycles 8,
      (Work.Cohomology.singularChains ℤ (TopCat.of A)).iCycles 8 ζ = x₁ ∧
      Work.Cohomology.hPairδ X A 8 ((Work.Cohomology.relChains X A).homologyπ 9 c)
        = (Work.Cohomology.singularChains ℤ (TopCat.of A)).homologyπ 8 ζ := by
  have hx₃ : ((Work.Cohomology.relChains X A).d 9 8) ((Work.Cohomology.relChains X A).iCycles 9 c)
      = 0 := iCycles_d_C (Work.Cohomology.relChains X A) 9 8 c
  have hcm := cyclesMk_iCycles_C (Work.Cohomology.relChains X A)
    (ComplexShape.next_eq' (ComplexShape.down ℕ) (i := 9) (j := 8) (by simp [ComplexShape.down]))
    c hx₃
  refine ⟨HomologicalComplex.cyclesMk (Work.Cohomology.singularChains ℤ (TopCat.of A)) x₁ 7
      (ComplexShape.next_eq' (ComplexShape.down ℕ) (i := 8) (j := 7) (by simp [ComplexShape.down]))
      ?_, ?_, ?_⟩
  · exact CategoryTheory.ShortComplex.ShortExact.d_eq_zero_of_f_eq_d_apply
      (Work.Cohomology.hPairShort_shortExact X A) (i := 9) (j := 8) x₂ x₁ hx₁ 7
  · exact iCycles_cyclesMk_C _ x₁ _ _
  · have hδ := CategoryTheory.ShortComplex.ShortExact.δ_apply
      (Work.Cohomology.hPairShort_shortExact X A) (i := 9) (j := 8)
      (show (ComplexShape.down ℕ).Rel 9 8 from by simp [ComplexShape.down])
      ((Work.Cohomology.relChains X A).iCycles 9 c) hx₃ x₂ hx₂ x₁ hx₁ 7
      (ComplexShape.next_eq' (ComplexShape.down ℕ) (i := 8) (j := 7) (by simp [ComplexShape.down]))
    rw [← hcm]
    exact hδ

/-! ## The relative cap product on the class of a cycle -/

/-- **The underlying chain of the relative cap product.** -/
theorem relCapPairZ_iCycles_apply {X : TopCat} {A : Set X}
    (z : (Work.Cohomology.relComplex ℤ X A).cycles 5)
    (c : (Work.Cohomology.relChains X A).cycles 9)
    (x : (Work.Cohomology.singularChains ℤ X).X 9)
    (hx : (cokernel.π ((Work.Cohomology.inclChains X A).f 9)) x
        = (Work.Cohomology.relChains_cokernelIso X A 9).hom
            ((Work.Cohomology.relChains X A).iCycles 9 c)) :
    (Work.Cohomology.singularChains ℤ X).iCycles 4
        ((Work.Cohomology.relCapPairZ X A 5 4) z c)
      = Work.Cohomology.cap ℤ (TopCat.toSSet.obj X)
          (((Work.Cohomology.relComplex ℤ X A).iCycles 5) z).1 4 x := by
  rw [Work.Cohomology.relCapPairZ_iCycles, ← hx]
  exact Work.Cohomology.relCapHalf_apply_incl (m := 4) X A
    (((Work.Cohomology.relComplex ℤ X A).iCycles 5) z) x

/-- **The underlying chain of the absolute cap product.** -/
theorem capPairZ_iCycles_apply (Z : TopCat)
    (z : (Work.Cohomology.singularCochainComplex ℤ Z).cycles 4)
    (c : (Work.Cohomology.singularChains ℤ Z).cycles 8) :
    (Work.Cohomology.singularChains ℤ Z).iCycles 4
        ((Work.Cohomology.capPairZ ℤ (TopCat.toSSet.obj Z) 4 4) z c)
      = Work.Cohomology.cap ℤ (TopCat.toSSet.obj Z)
          ((Work.Cohomology.singularCochainComplex ℤ Z).iCycles 4 z) 4
          ((Work.Cohomology.singularChains ℤ Z).iCycles 8 c) :=
  Work.Cohomology.capPairZ_iCycles ℤ (TopCat.toSSet.obj Z) 4 4 z c

/-- **The computation rule for the absolute cap product.** -/
theorem capPair_apply_sing (Z : TopCat)
    (z : (Work.Cohomology.SSetCochainComplex ℤ (TopCat.toSSet.obj Z)).cycles 4)
    (c : (Work.Cohomology.singularChains ℤ Z).cycles 8) :
    (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj Z) 4 4)
        ((Work.Cohomology.SSetCochainComplex ℤ (TopCat.toSSet.obj Z)).homologyπ 4 z)
        ((Work.Cohomology.singularChains ℤ Z).homologyπ 8 c)
      = (Work.Cohomology.singularChains ℤ Z).homologyπ 4
          ((Work.Cohomology.capPairZ ℤ (TopCat.toSSet.obj Z) 4 4) z c) :=
  Work.Cohomology.capPair_apply ℤ (TopCat.toSSet.obj Z) 4 4 z c

/-! ## Naturality of the cap product along `C_*(A) ⟶ C_*(X)` -/

/-- The restriction map `C^n(X) ⟶ C^n(A)` is the transpose of the inclusion of the chains. -/
lemma restr_eq_comp {X : TopCat} {A : Set X} {n : ℕ}
    (bt : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) n) :
    ((Work.Cohomology.restr ℤ X A).f n) bt
      = bt ∘ₗ (ModuleCat.Hom.hom ((SSet.chainComplexMap
          (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)) (ModuleCat.of ℤ ℤ)).f n)) := rfl

/-- **The cap product is natural for the inclusion of the boundary chains.** -/
theorem inclChains_cap {X : TopCat} {A : Set X}
    (bt : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) 4)
    (x₁ : (Work.Cohomology.singularChains ℤ (TopCat.of A)).X 8) :
    ((Work.Cohomology.inclChains X A).f 4)
        (Work.Cohomology.cap ℤ (TopCat.toSSet.obj (TopCat.of A))
          (((Work.Cohomology.restr ℤ X A).f 4) bt) 4 x₁)
      = Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) bt 4
          (((Work.Cohomology.inclChains X A).f 8) x₁) := by
  have h := Work.Cohomology.cap_natural ℤ (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))
    (n := 4) (m := 4) bt x₁
  rw [restr_eq_comp bt]
  exact h

/-! ## Lifting a relative cycle, and the boundary of its lift -/

/-- Every relative `9`-cycle of `(X,A)` lifts to a `9`-chain of `X`. -/
lemma exists_lift_relcycle {X : TopCat} {A : Set X} (c : (Work.Cohomology.relChains X A).cycles 9) :
    ∃ x₂ : (Work.Cohomology.singularChains ℤ X).X 9,
      ((cokernel.π (Work.Cohomology.inclChains X A)).f 9) x₂
        = (Work.Cohomology.relChains X A).iCycles 9 c :=
  (ModuleCat.epi_iff_surjective ((cokernel.π (Work.Cohomology.inclChains X A)).f 9)).mp
    inferInstance _

/-- The boundary of a lift of a relative cycle lies in the chains of `A`. -/
lemma exists_chain_of_lift {X : TopCat} {A : Set X}
    (c : (Work.Cohomology.relChains X A).cycles 9)
    (x₂ : (Work.Cohomology.singularChains ℤ X).X 9)
    (hx₂ : ((cokernel.π (Work.Cohomology.inclChains X A)).f 9) x₂
        = (Work.Cohomology.relChains X A).iCycles 9 c) :
    ∃ x₁ : (Work.Cohomology.singularChains ℤ (TopCat.of A)).X 8,
      ((Work.Cohomology.inclChains X A).f 8) x₁
        = ((Work.Cohomology.singularChains ℤ X).d 9 8) x₂ := by
  have hcomm := chainMap_comm_apply' (Work.Cohomology.singularChains ℤ X)
    (Work.Cohomology.relChains X A) (cokernel.π (Work.Cohomology.inclChains X A)) 9 8 x₂
  have hcyc : ((Work.Cohomology.relChains X A).d 9 8)
      ((Work.Cohomology.relChains X A).iCycles 9 c) = 0 :=
    iCycles_d_C (Work.Cohomology.relChains X A) 9 8 c
  have hzero : ((cokernel.π (Work.Cohomology.inclChains X A)).f 8)
      (((Work.Cohomology.singularChains ℤ X).d 9 8) x₂) = 0 :=
    hcomm.symm.trans ((congrArg (fun z => ((Work.Cohomology.relChains X A).d 9 8) z)
      hx₂).trans hcyc)
  have hzero2 : (cokernel.π ((Work.Cohomology.inclChains X A).f 8))
      (((Work.Cohomology.singularChains ℤ X).d 9 8) x₂) = 0 := by
    calc (cokernel.π ((Work.Cohomology.inclChains X A).f 8))
          (((Work.Cohomology.singularChains ℤ X).d 9 8) x₂)
        = (Work.Cohomology.relChains_cokernelIso X A 8).hom
            (((cokernel.π (Work.Cohomology.inclChains X A)).f 8)
              (((Work.Cohomology.singularChains ℤ X).d 9 8) x₂)) :=
          (Work.Cohomology.relChains_cokernelIso_canon_apply X A 8
            (((Work.Cohomology.singularChains ℤ X).d 9 8) x₂)).symm
      _ = (Work.Cohomology.relChains_cokernelIso X A 8).hom 0 := by rw [hzero]
      _ = 0 := map_zero _
  have hmem : ((Work.Cohomology.singularChains ℤ X).d 9 8) x₂
      ∈ LinearMap.range (((Work.Cohomology.inclChains X A).f 8)).hom := by
    rw [ShortComplex.Exact.moduleCat_range_eq_ker
      (ShortComplex.exact_cokernel ((Work.Cohomology.inclChains X A).f 8))]
    exact LinearMap.mem_ker.mpr hzero2
  obtain ⟨x₁, hx₁⟩ := LinearMap.mem_range.mp hmem
  exact ⟨x₁, hx₁⟩

/-! ## The connecting map `pairδ` of the cohomology pair sequence on the class of a cocycle -/

/-- `cocycleOfK` is `liftCycles` of the corresponding singleton map. -/
lemma liftCycles_ofHom_hom_one (K : CochainComplex (ModuleCat ℤ) ℕ) {n : ℕ} (α : ↑(K.X n))
    (j : ℕ) (hj : (ComplexShape.up ℕ).next n = j) (hj' : j = n + 1)
    (hk : ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (K.X n) α) ≫ K.d n j = 0)
    (h : (ModuleCat.Hom.hom (K.d n (n + 1))) α = 0) :
    (K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (K.X n) α)) j hj hk).hom 1
      = Work.Cohomology.cocycleOfK K α h := by
  subst hj'
  unfold Work.Cohomology.cocycleOfK
  rfl

/-- **The connecting map `pairδ` on the class of a cocycle.**  If `b` is a cocycle of `C^n(A)` and
`bt` a lift of it to `C^n(X)`, then `δ[b]` is the class of `d bt` in `C^{n+1}(X,A)`. -/
theorem pairδ_classOf_lift {X : TopCat} {A : Set X} (n : ℕ)
    (b : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of A)) n)
    (hb : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of A)) b = 0)
    (bt : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) n)
    (hbt : ((Work.Cohomology.restr ℤ X A).f n) bt = b) :
    ∃ (hmem : ((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt
        ∈ Work.Cohomology.relKern ℤ X A (n + 1)),
      ∃ (hcoc : Work.Cohomology.relDiffLM ℤ X A (n + 1)
          ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩ = 0),
        Work.Cohomology.pairδ ℤ X A n
            (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of A)) b hb)
          = Work.Cohomology.relClassOf ℤ X A
              ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩ hcoc := by
  have hmem : ((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt
      ∈ Work.Cohomology.relKern ℤ X A (n + 1) := by
    rw [Work.Cohomology.relKern, LinearMap.mem_ker]
    have h := congrArg ModuleCat.Hom.hom ((Work.Cohomology.restr ℤ X A).comm n (n + 1))
    simp only [ModuleCat.hom_comp] at h
    have h2 := LinearMap.congr_fun h bt
    simp only [LinearMap.comp_apply] at h2
    rw [Work.Cohomology.singularCochain_d_apply ℤ (TopCat.of A), hbt, hb] at h2
    exact h2.symm
  have hcoc : Work.Cohomology.relDiffLM ℤ X A (n + 1)
      ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩ = 0 := by
    apply Subtype.ext
    rw [Work.Cohomology.relDiffLM_coe, Submodule.coe_zero]
    have h := HomologicalComplex.d_comp_d (Work.Cohomology.singularCochainComplex ℤ X) n (n+1) (n+2)
    have h2 := congrArg ModuleCat.Hom.hom h
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
    exact LinearMap.congr_fun h2 bt
  refine ⟨hmem, hcoc, ?_⟩
  have hx₃ : (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
        (((Work.Cohomology.pairShort ℤ X A).X₃).X n) b))
      ≫ ((Work.Cohomology.pairShort ℤ X A).X₃.d n (n+1)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, map_smul, ModuleCat.hom_zero, LinearMap.zero_apply]
    change r • ((Work.Cohomology.singularCochainComplex ℤ (TopCat.of A)).d n (n + 1)) b = 0
    rw [Work.Cohomology.singularCochain_d_apply ℤ (TopCat.of A), hb, smul_zero]
  have hx₂ : (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
        (((Work.Cohomology.pairShort ℤ X A).X₂).X n) bt))
      ≫ ((Work.Cohomology.pairShort ℤ X A).g.f n)
      = (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
          (((Work.Cohomology.pairShort ℤ X A).X₃).X n) b)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, map_smul]
    change r • ((Work.Cohomology.restr ℤ X A).f n) bt = r • b
    rw [hbt]
  have hx₁ : (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
        (((Work.Cohomology.pairShort ℤ X A).X₁).X (n+1))
        ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩))
      ≫ ((Work.Cohomology.pairShort ℤ X A).f.f (n+1))
      = (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
          (((Work.Cohomology.pairShort ℤ X A).X₂).X n) bt))
        ≫ ((Work.Cohomology.pairShort ℤ X A).X₂.d n (n+1)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, map_smul]
    change r • (⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩ :
        Work.Cohomology.relKern ℤ X A (n+1)) = r •
        ((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt
    simp
  have hb' : (ModuleCat.Hom.hom (((Work.Cohomology.pairShort ℤ X A).X₃).d n (n + 1))) b = 0 := by
    change (ModuleCat.Hom.hom
      ((Work.Cohomology.singularCochainComplex ℤ (TopCat.of A)).d n (n + 1))) b = 0
    rw [Work.Cohomology.singularCochain_d_apply ℤ (TopCat.of A)]; exact hb
  have hcoc' : (ModuleCat.Hom.hom (((Work.Cohomology.pairShort ℤ X A).X₁).d (n + 1) (n + 2)))
      ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩ = 0 := by
    change (ModuleCat.Hom.hom ((Work.Cohomology.relComplex ℤ X A).d (n + 1) (n + 2)))
      ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩ = 0
    rw [Work.Cohomology.relComplex_d_apply]; exact hcoc
  have hpk : (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
        (((Work.Cohomology.pairShort ℤ X A).X₁).X (n+1))
        ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩))
      ≫ ((Work.Cohomology.pairShort ℤ X A).X₁.d (n+1) (n+2)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, map_smul, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [hcoc', smul_zero]
  have key : ∀ (hij : (ComplexShape.up ℕ).Rel n (n+1)),
      (Work.Cohomology.pairShort_shortExact ℤ X A).δ n (n+1) hij
        (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of A)) b hb)
      = Work.Cohomology.relClassOf ℤ X A
          ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n+1)) bt, hmem⟩ hcoc := by
    intro hij
    have hδ := CategoryTheory.ShortComplex.ShortExact.δ_eq
      (hS := Work.Cohomology.pairShort_shortExact ℤ X A)
      n (n+1) hij
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
        (((Work.Cohomology.pairShort ℤ X A).X₃).X n) b)) hx₃
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
        (((Work.Cohomology.pairShort ℤ X A).X₂).X n) bt)) hx₂
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
        (((Work.Cohomology.pairShort ℤ X A).X₁).X (n+1))
        ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩)) hx₁
      (n+2) (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (n+1) (n+2) from rfl))
    have hδ' := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
        (((Work.Cohomology.pairShort ℤ X A).X₁).homology (n+1))) => g.hom 1) hδ
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hδ'
    have h₃ : (((Work.Cohomology.pairShort ℤ X A).X₃.liftCycles
          (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
            (((Work.Cohomology.pairShort ℤ X A).X₃).X n) b)) (n+1)
          ((ComplexShape.up ℕ).next_eq' hij) hx₃).hom 1)
        = Work.Cohomology.cocycleOfK ((Work.Cohomology.pairShort ℤ X A).X₃) b hb' :=
      liftCycles_ofHom_hom_one ((Work.Cohomology.pairShort ℤ X A).X₃) b (n+1)
        ((ComplexShape.up ℕ).next_eq' hij) rfl hx₃ hb'
    have h₁ : (((Work.Cohomology.pairShort ℤ X A).X₁.liftCycles
          (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
            (((Work.Cohomology.pairShort ℤ X A).X₁).X (n+1))
            ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩)) (n+2)
          (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (n+1) (n+2) from rfl)) hpk).hom 1)
        = Work.Cohomology.cocycleOfK ((Work.Cohomology.pairShort ℤ X A).X₁)
            ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩ hcoc' :=
      liftCycles_ofHom_hom_one ((Work.Cohomology.pairShort ℤ X A).X₁)
        ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩ (n+2)
        (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (n+1) (n+2) from rfl)) rfl hpk hcoc'
    rw [h₃, h₁] at hδ'
    change (ModuleCat.Hom.hom ((Work.Cohomology.pairShort_shortExact ℤ X A).δ n (n + 1) hij))
        ((ModuleCat.Hom.hom ((Work.Cohomology.singularCochainComplex ℤ (TopCat.of A)).homologyπ n))
          (Work.Cohomology.cocycleOfK (Work.Cohomology.singularCochainComplex ℤ (TopCat.of A)) b hb')) =
        (ModuleCat.Hom.hom ((Work.Cohomology.relComplex ℤ X A).homologyπ (n + 1)))
          (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℤ X A)
            ⟨((Work.Cohomology.singularCochainComplex ℤ X).d n (n + 1)) bt, hmem⟩ hcoc')
    exact hδ'
  exact key _

/-! ## The transgression identity -/

/-- **The transgression identity** for a pair `(X,A)`. -/
theorem transgression_general (X : TopCat) (A : Set X)
    (y : (Work.Cohomology.singularCochainComplex ℤ (TopCat.of A)).homology 4)
    (w : (Work.Cohomology.relChains X A).homology 9) :
    (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) 4)
        ((Work.Cohomology.capPair ℤ (TopCat.toSSet.obj (TopCat.of A)) 4 4) y
          (Work.Cohomology.hPairδ X A 8 w))
      = (Work.Cohomology.relCapPair X A 5 4) ((Work.Cohomology.pairδ ℤ X A 4) y) w := by
  -- a cocycle representing `y`, and a lift of it
  obtain ⟨b, hb, hy⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of A)) 4 y
  let z' := Work.Cohomology.cocycleOf ℤ (TopCat.toSSet.obj (TopCat.of A)) b hb
  have hz' : (Work.Cohomology.SSetCochainComplex ℤ
      (TopCat.toSSet.obj (TopCat.of A))).homologyπ 4 z' = y := hy
  obtain ⟨bt, hbt⟩ := Work.Cohomology.surjective_restr ℤ X A 4 b
  have hbt' : ((Work.Cohomology.restr ℤ X A).f 4) bt
      = (Work.Cohomology.singularCochainComplex ℤ (TopCat.of A)).iCycles 4 z' :=
    hbt.trans (Work.Cohomology.iCycles_cocycleOf ℤ (TopCat.toSSet.obj (TopCat.of A)) b hb).symm
  obtain ⟨hmem, hcoc, hδ⟩ := pairδ_classOf_lift (X := X) (A := A) 4 b hb bt hbt
  -- a cycle representing `w` and its lifts
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective
    ((Work.Cohomology.relChains X A).homologyπ 9)).mp inferInstance w
  obtain ⟨x₂, hx₂⟩ := exists_lift_relcycle (X := X) (A := A) c
  obtain ⟨x₁, hx₁⟩ := exists_chain_of_lift (X := X) (A := A) c x₂ hx₂
  obtain ⟨ζ, hζi, hζh⟩ := hPairδ_homologyπ_eq (X := X) (A := A) c x₂ hx₂ x₁ hx₁
  have hx₁' : ((Work.Cohomology.inclChains X A).f 8) x₁
      = ((Work.Cohomology.singularChains ℤ X).d 9 8).hom x₂ := hx₁
  have hxdeg : (cokernel.π ((Work.Cohomology.inclChains X A).f 9)) x₂
      = (Work.Cohomology.relChains_cokernelIso X A 9).hom
          ((Work.Cohomology.relChains X A).iCycles 9 c) := by
    rw [← Work.Cohomology.relChains_cokernelIso_canon_apply, hx₂]
  -- notation
  set z5 : (Work.Cohomology.relKern ℤ X A 5) :=
    ⟨((Work.Cohomology.singularCochainComplex ℤ X).d 4 5) bt, hmem⟩ with hz5def
  have hz5 : z5.1 = ((Work.Cohomology.singularCochainComplex ℤ X).d 4 5) bt := rfl
  -- the relative cap product side
  set ζR : (Work.Cohomology.singularChains ℤ X).cycles 4 :=
    (Work.Cohomology.relCapPairZ X A 5 4)
      (Work.Cohomology.relCocycleOf ℤ X A z5 hcoc) c with hζR
  have hζRi : (Work.Cohomology.singularChains ℤ X).iCycles 4 ζR
      = Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) z5.1 4 x₂ := by
    rw [hζR, relCapPairZ_iCycles_apply (X := X) (A := A)
      (z := Work.Cohomology.relCocycleOf ℤ X A z5 hcoc) (c := c) (x := x₂) hxdeg,
      Work.Cohomology.iCycles_relCocycleOf]
  -- the absolute cap product side
  set capp : (Work.Cohomology.singularChains ℤ (TopCat.of A)).cycles 4 :=
    (Work.Cohomology.capPairZ ℤ (TopCat.toSSet.obj (TopCat.of A)) 4 4) z' ζ with hcapp
  have hcappi : (Work.Cohomology.singularChains ℤ (TopCat.of A)).iCycles 4 capp
      = Work.Cohomology.cap ℤ (TopCat.toSSet.obj (TopCat.of A))
          ((Work.Cohomology.singularCochainComplex ℤ (TopCat.of A)).iCycles 4 z') 4
          ((Work.Cohomology.singularChains ℤ (TopCat.of A)).iCycles 8 ζ) := by
    rw [hcapp]; exact capPairZ_iCycles_apply _ _ _
  set w₂ : (Work.Cohomology.singularChains ℤ X).cycles 4 :=
    HomologicalComplex.cyclesMap (Work.Cohomology.inclChains X A) 4 capp with hw₂
  have hw₂i : (Work.Cohomology.singularChains ℤ X).iCycles 4 w₂
      = Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) bt 4
          (((Work.Cohomology.singularChains ℤ X).d 9 8).hom x₂) := by
    rw [hw₂, iCycles_cyclesMap_C, hcappi, hζi, ← hbt', ← hx₁']
    rw [inclChains_cap bt x₁, hx₁']
  -- the Leibniz rule
  have hsub : w₂ - ζR = (Work.Cohomology.singularChains ℤ X).toCycles 5 4
      (Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) bt 5 x₂) := by
    apply Work.Cohomology.iCycles_injective_C ℤ (Work.Cohomology.singularChains ℤ X) 4
    rw [map_sub, hw₂i, hζRi, toCycles_i_C'']
    have h := Work.Cohomology.cap_coboundary_formula ℤ (TopCat.toSSet.obj X) (k := 4) (m := 4)
      bt x₂
    rw [capIdx_cast_eq X x₂] at h
    rw [← Work.Cohomology.singularCochain_d_apply ℤ X bt, ← hz5] at h
    simp only [show ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (4 + (4 + 1)) (4 + 4)
          = (Work.Cohomology.singularChains ℤ X).d 9 8 from rfl,
      show ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (4 + 1) 4
          = (Work.Cohomology.singularChains ℤ X).d 5 4 from rfl] at h
    rw [h]
    rw [show ((-1 : ℤ) ^ 4) = 1 from by norm_num]
    module
  have hhom : (Work.Cohomology.singularChains ℤ X).homologyπ 4 w₂
      = (Work.Cohomology.singularChains ℤ X).homologyπ 4 ζR := by
    have hzero : (Work.Cohomology.singularChains ℤ X).homologyπ 4 (w₂ - ζR) = 0 := by
      rw [hsub]
      exact homologyπ_toCycles_C' _ _ _ _
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero
  -- the two sides
  have hL1 : (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) 4)
      ((Work.Cohomology.capPair ℤ (TopCat.toSSet.obj (TopCat.of A)) 4 4) y
        (Work.Cohomology.hPairδ X A 8 w))
      = (Work.Cohomology.singularChains ℤ X).homologyπ 4 w₂ := by
    rw [← hz', ← hc, hζh]
    rw [capPair_apply_sing]
    rw [homologyMap_homologyπ_C]
  have hR : (Work.Cohomology.relCapPair X A 5 4) ((Work.Cohomology.pairδ ℤ X A 4) y) w
      = (Work.Cohomology.singularChains ℤ X).homologyπ 4 ζR := by
    rw [← hy, ← hc, hδ]
    rw [Work.Cohomology.relClassOf, Work.Cohomology.relCapPair_apply]
  rw [hL1, hhom, hR]

/-- **The transgression identity for the pair `(W, ∂W)` of a null-bordism family.** -/
theorem transgressionCapPairConnecting {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F)
    (y : (Work.Cohomology.singularCochainComplex ℤ (TopCat.of (bdrySet W.W))).homology 4) :
    (HomologicalComplex.homologyMap (Work.Cohomology.inclChains (TopCat.of W.W) (bdrySet W.W)) 4)
        ((Work.Cohomology.capPair ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 4) y
          (Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8 W.w))
      = (Work.Cohomology.relCapPair (TopCat.of W.W) (bdrySet W.W) 5 4)
            ((Work.Cohomology.pairδ ℤ (TopCat.of W.W) (bdrySet W.W) 4) y) W.w :=
  transgression_general (TopCat.of W.W) (bdrySet W.W) y W.w

end

end Work.ThomBordism
