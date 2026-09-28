import Mathlib
import Submission.Work.Cohomology.pd_split_prep
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.pd_hatcher_data
import Submission.Work.Cohomology.pd_hatcher_Xdata
import Submission.Work.Cohomology.pd_hatcher_inter4
import Submission.Work.Cohomology.pd_union_crux_zero_wk
import Submission.Work.Cohomology.pd_inter_cap_boundary
import Submission.Work.Cohomology.pd_split_setup
import Submission.Work.Cohomology.pd_boundary_of_zero_class
import Submission.Work.Cohomology.pd_us_cycles_eq_of_class_eq

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

namespace PDSplitKC

/-! ## Elementary rewrites for the singular cochain differential -/

/-- The differential of the singular cochain complex is `cochainDiff`. -/
theorem pd_kc_singularD_eq_cochainDiff (X : TopCat) (n : ℕ)
    (φ : Cochain ℤ (TopCat.toSSet.obj X) n) :
    (ConcreteCategory.hom ((singularCochainComplex ℤ X).d n (n+1))) φ
      = cochainDiff ℤ (TopCat.toSSet.obj X) (n := n) φ := by
  simp only [singularCochainComplex_eq, SSetCochainComplex_d]
  exact cochainDiffLM_apply ℤ (TopCat.toSSet.obj X) n φ

/-! ## The setup: a cycle representative and the lift along the difference map -/

/-- **Setup**: from a relative cohomology class of the pair `(U∪V, (U∪V)∖(K₁∪K₂))` produce a
cycle representative together with a lift of its underlying cochain along the `A+B` difference
map. -/
theorem pd_kc_setup {M : TopCat} [T2Space M] {k : ℕ} {U V : Set M} {K₁ K₂ : Set M}
    (x : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homology k) :
    ∃ (z : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).cycles k)
      (hz : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homologyπ k z = x)
      (φA : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K₁)).X k)
      (φB : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K₂)).X k),
      ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z).1 = φA.1 - φB.1 := by
  classical
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k)).mp inferInstance x
  set φ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k :=
    ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z).1 with hφdef
  have hφmem : φ ∈ relKern ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) k :=
    ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z).2
  have h0 : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).d k (k+1)
      ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z) = 0 := by
    have hcomp : (ConcreteCategory.hom
        ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k ≫
          (relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).d k (k+1))) z
        = (ConcreteCategory.hom ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).d k (k+1)))
          ((ConcreteCategory.hom ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k)) z) :=
      CategoryTheory.ConcreteCategory.comp_apply _ _ z
    rw [← hcomp]
    exact congrArg (fun (g : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).cycles k ⟶
        (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).X (k+1)) =>
        (ConcreteCategory.hom g) z)
      (HomologicalComplex.iCycles_d (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k (k+1))
  have hφd : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φ = 0 := by
    have hcomm := congrArg
      (fun (g : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).X k ⟶
          (singularCochainComplex ℤ (TopCat.of (U ∪ V : Set M))).X (k+1)) =>
        (ConcreteCategory.hom g) ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z))
      ((relIncl ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).comm k (k+1))
    simp only [CategoryTheory.ConcreteCategory.comp_apply] at hcomm
    rw [h0, map_zero] at hcomm
    have hrel : (ConcreteCategory.hom ((relIncl ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).f k))
          ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z) = φ := rfl
    rw [hrel] at hcomm
    rw [pd_kc_singularD_eq_cochainDiff] at hcomm
    exact hcomm
  -- the lift
  have hsplit : pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)
      = pdRelSub (U ∪ V : Set M) K₁ ∩ pdRelSub (U ∪ V : Set M) K₂ :=
    pdRelSub_union (U ∪ V : Set M) K₁ K₂
  have hφmem' : φ ∈ relKern ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) K₁ ∩ pdRelSub (U ∪ V : Set M) K₂) k := hsplit ▸ hφmem
  obtain ⟨φt, hφt⟩ := PDABClean.pdBiprodToInter_surj (TopCat.of (U ∪ V : Set M))
    (pdRelSub (U ∪ V : Set M) K₁) (pdRelSub (U ∪ V : Set M) K₂) k ⟨φ, hφmem'⟩
  set y₁ : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) K₁)).X k :=
    (ModuleCat.Hom.hom ((biprod.fst : relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₁) ⊞
        relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₂) ⟶
        relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₁)).f k)) φt with hy₁
  set y₂ : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) K₂)).X k :=
    (ModuleCat.Hom.hom ((biprod.snd : relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₁) ⊞
        relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₂) ⟶
        relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₂)).f k)) φt with hy₂
  refine ⟨z, hz, y₁, y₂, ?_⟩
  have htotal : (ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ
        (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₁) ⟶
        relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K₁) ⊞
        relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K₂)).f k)) y₁
      + (ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ
        (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₂) ⟶
        relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K₁) ⊞
        relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K₂)).f k)) y₂ = φt :=
    PDABClean.pdBiprod_total (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) K₁)
      (pdRelSub (U ∪ V : Set M) K₂) k φt
  have hcoe := PDABClean.pdBiprodToInter_coe (TopCat.of (U ∪ V : Set M))
    (pdRelSub (U ∪ V : Set M) K₁) (pdRelSub (U ∪ V : Set M) K₂) k y₁ y₂
  rw [htotal] at hcoe
  have h3 : ((show relKern ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) K₁
        ∩ pdRelSub (U ∪ V : Set M) K₂) k from
      (ModuleCat.Hom.hom ((pdBiprodToInter (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₁)
        (pdRelSub (U ∪ V : Set M) K₂)).f k)) φt)).1 = φ := by
    rw [hφt]
  exact hφdef ▸ (h3.symm.trans hcoe)


/-- **The cap product of a coboundary with the "middle" chain is a boundary in `U ∩ V`** (weak
form): the boundary of the total chain `α₁+α₂+α₃` is only required to be *supported* in
`Kᶜ ∩ Lᶜ`. -/
theorem pd_kc_cap_cochainDiff_weak {X : TopCat} {U V K L : Set X} {N k mj : ℕ}
    (hkN : k + (mj + 1) = N)
    (α₁ α₂ α₃ : (singularChains ℤ X).X N)
    (hα₂ : α₂ ∈ LinearMap.range (((inclChains X (U ∩ V)).f N).hom))
    (hL : (singularChains ℤ X).d N (N-1) α₁ ∈
      LinearMap.range (((inclChains X Lᶜ).f (N-1)).hom))
    (hK : (singularChains ℤ X).d N (N-1) α₃ ∈
      LinearMap.range (((inclChains X Kᶜ).f (N-1)).hom))
    (hd : (singularChains ℤ X).d N (N-1) (α₁ + α₂ + α₃) ∈
      LinearMap.range (((inclChains X (Kᶜ ∩ Lᶜ)).f (N-1)).hom))
    {θ : Cochain ℤ (TopCat.toSSet.obj X) k}
    (hθ : θ ∈ relKern ℤ X Kᶜ k ⊓ relKern ℤ X Lᶜ k) :
    ∃ γ ∈ LinearMap.range (((inclChains X (U ∩ V)).f (mj+1)).hom),
      (singularChains ℤ X).d (mj+1) mj γ =
        (-1:ℤ)^(k+1) • cap ℤ (TopCat.toSSet.obj X)
          (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) θ) mj
            ((capIdx k mj) ▸ (hkN.symm ▸ α₂)) := by
  subst N
  rw [show (k + (mj + 1)) - 1 = k + mj by omega] at hL hK hd
  obtain ⟨e', he'⟩ := hL
  obtain ⟨f', hf'⟩ := hK
  obtain ⟨g', hg'⟩ := hd
  -- `θ` kills the chains supported in `Lᶜ` ...
  have hzeroL : cap ℤ (TopCat.toSSet.obj X) θ mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁) = 0 := by
    rw [← he']
    exact cap_inclChains_eq_zero X Lᶜ θ hθ.2 mj e'
  -- ... and the chains supported in `Kᶜ`.
  have hzeroK : cap ℤ (TopCat.toSSet.obj X) θ mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃) = 0 := by
    rw [← hf']
    exact cap_inclChains_eq_zero X Kᶜ θ hθ.1 mj f'
  -- ... and the chains supported in `Kᶜ ∩ Lᶜ`.
  have hzeroG : cap ℤ (TopCat.toSSet.obj X) θ mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃)) = 0 := by
    rw [← hg']
    exact cap_eq_zero_of_mem_range_inclChains X Kᶜ (Kᶜ ∩ Lᶜ)
      (Set.inter_subset_left : Kᶜ ∩ Lᶜ ⊆ Kᶜ) θ hθ.1 ⟨g', rfl⟩
  -- hence `θ` kills the boundary of the middle chain
  have hsum : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃)
      = (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁
        + (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂
        + (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃ := by
    rw [map_add, map_add]
  have hdα₂ : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂
      = (singularChains ℤ X).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃)
        - (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁
        - (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃ := by
    rw [hsum]; abel
  have hzero : cap ℤ (TopCat.toSSet.obj X) θ mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂) = 0 := by
    rw [hdα₂, map_sub, map_sub, hzeroG, hzeroL, hzeroK, sub_zero, sub_zero]
  refine ⟨cap ℤ (TopCat.toSSet.obj X) θ (mj+1) α₂, ?_, ?_⟩
  · exact cap_mem_range_inclChains (M := X) (S := U ∩ V) k (mj+1) θ hα₂
  · have hcapd : (singularChains ℤ X).d (mj+1) mj
        (cap ℤ (TopCat.toSSet.obj X) θ (mj+1) α₂)
        = (-1:ℤ)^k • (cap ℤ (TopCat.toSSet.obj X) θ mj
              ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
            - cap ℤ (TopCat.toSSet.obj X)
              (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) θ) mj
              ((capIdx k mj) ▸ α₂)) := by
      refine (cap_d ℤ (TopCat.toSSet.obj X) (n := k) (m := mj) θ α₂).trans ?_
      exact int_smul_eq_zsmul (inferInstance : Module ℤ
        ↑(((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X mj)) ((-1:ℤ)^k) _
    rw [hzero] at hcapd
    rw [hcapd, zero_sub, zsmul_neg]
    rw [show (-1:ℤ)^(k+1) = -((-1:ℤ)^k) by rw [pow_succ]; ring, neg_zsmul]

/-- The differential of a pulled-back cochain is the pull-back of the differential. -/
theorem pd_kc_cochainDiff_pullback {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (φ : Cochain ℤ (TopCat.toSSet.obj Y) n) :
    cochainDiff ℤ (TopCat.toSSet.obj X) (n := n)
        (φ.comp ((chainMap ℤ X Y f).f n).hom)
      = (cochainDiff ℤ (TopCat.toSSet.obj Y) (n := n) φ).comp
          ((chainMap ℤ X Y f).f (n+1)).hom := by
  have hcomm := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.Hom.comm (chainMap ℤ X Y f) (n+1) n)
  simp only [ModuleCat.hom_comp] at hcomm
  apply LinearMap.ext
  intro c
  have hc := LinearMap.congr_fun hcomm c
  simp only [LinearMap.comp_apply] at hc
  simp only [cochainDiff, LinearMap.comp_apply]
  exact (congrArg φ hc).symm

/-- The underlying cochain of the pull-back of a relative cochain. -/
theorem pd_kc_relMap_coe {X Y : TopCat} (A : Set X) (C : Set Y) (f : X ⟶ Y)
    (h : ∀ x ∈ A, f x ∈ C) (n : ℕ) (x : relKern ℤ Y C n) :
    (((relComplexMap ℤ A C f h).f n) x).1 = x.1.comp ((chainMap ℤ X Y f).f n).hom := by
  have hcp : ((dualChainMap ℤ X Y f).f n) = cochainPullbackHom ℤ X Y f n := rfl
  rw [relComplexMap_f]
  change (relMapLM ℤ A C f h n x).1 = _
  rw [relMapLM_coe, hcp]
  apply LinearMap.ext
  intro c
  rw [LinearMap.comp_apply]
  exact cochainPullbackHom_apply ℤ X Y f n x.1 c

/-- The cycle of a cochain complex associated with a cocycle. -/
noncomputable def pd_kc_cycleC {C : CochainComplex (ModuleCat ℤ) ℕ} (n : ℕ) (x : C.X n)
    (hx : C.d n (n+1) x = 0) : C.cycles n :=
  (C.sc n).moduleCatCyclesIso.inv ⟨x, by
    have hnext : (ComplexShape.up ℕ).next n = n + 1 :=
      (ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk n (n + 1) rfl)
    show C.d n ((ComplexShape.up ℕ).next n) x = 0
    rw [hnext]
    exact hx⟩

/-- The underlying cochain of `pd_kc_cycleC` is the original cocycle. -/
theorem pd_kc_iCycles_cycleC {C : CochainComplex (ModuleCat ℤ) ℕ} (n : ℕ) (x : C.X n)
    (hx : C.d n (n+1) x = 0) : C.iCycles n (pd_kc_cycleC n x hx) = x := by
  show (C.sc n).iCycles ((C.sc n).moduleCatCyclesIso.inv _) = x
  rw [← ModuleCat.comp_apply, ShortComplex.moduleCatCyclesIso_inv_iCycles]
  rfl

/-- `iCycles` of a `cyclesMk`. -/
theorem pd_kc_iCycles_cyclesMk {C : CochainComplex (ModuleCat ℤ) ℕ} {i : ℕ} (x : C.X i)
    (j : ℕ) (hj : (ComplexShape.up ℕ).next i = j) (hx : C.d i j x = 0) :
    C.iCycles i (HomologicalComplex.cyclesMk C x j hj hx) = x := by
  have h := HomologicalComplex.i_cyclesMk (K := C) (x := x) (j := j) (hj := hj) (hx := hx)
  simpa using h

/-- Transport of a cohomology class along an equality of cochain complexes. -/
theorem pd_kc_cast_homologyπ {C C' : CochainComplex (ModuleCat ℤ) ℕ} (h : C = C') {k : ℕ}
    (z : C.cycles k) : h ▸ ((C.homologyπ k) z) = (C'.homologyπ k) (h ▸ z) := by
  cases h; rfl

/-- Transport of a cohomology class along an equality of relative sets. -/
theorem pd_kc_cast_homologyπ' {X : TopCat} {S S' : Set X} (h : S = S') {k : ℕ}
    (z : (relComplex ℤ X S).cycles k) :
    h ▸ ((relComplex ℤ X S).homologyπ k z)
      = (relComplex ℤ X S').homologyπ k (h ▸ z) := by
  cases h; rfl

/-- Transport of the underlying cochain of a relative cycle. -/
theorem pd_kc_iCycles_cast {X : TopCat} {S S' : Set X} (h : S = S') {k : ℕ}
    (z : (relComplex ℤ X S).cycles k) :
    ((relComplex ℤ X S').iCycles k (h ▸ z)).1
      = ((relComplex ℤ X S).iCycles k z).1 := by
  cases h; rfl

/-- Transport of zero. -/
theorem pd_kc_cast_zero {ι : Sort*} {P : ι → Type*} [∀ i, Zero (P i)] {a b : ι}
    (h : a = b) : h ▸ (0 : P a) = (0 : P b) := by cases h; rfl

/-- Transport of the value of a pair map along equalities of the relative sets. -/
theorem pd_kc_castApply {X : TopCat} {S₁ S₁' S₂ S₂' : Set X} (h₁ : S₁ = S₁') (h₂ : S₂ = S₂')
    (f : X ⟶ X) (hf : ∀ x ∈ S₁, f x ∈ S₂) (hf' : ∀ x ∈ S₁', f x ∈ S₂') (k : ℕ)
    (y : (relComplex ℤ X S₂).homology k) :
    (HomologicalComplex.homologyMap (relComplexMap ℤ S₁ S₂ f hf) k) y
      = h₁.symm ▸ ((HomologicalComplex.homologyMap
          (relComplexMap ℤ S₁' S₂' f hf') k) (h₂ ▸ y)) := by
  subst h₁
  subst h₂
  rw [capRel_relComplexMap_congr ℤ S₁ S₂ rfl hf hf']

/-- The underlying cochain of `pdABInclB`. -/
theorem pd_kc_pdABInclB_val {X : TopCat} {A B : Set X} (n : ℕ) (x : (pdABCoh X A B).X n) :
    ((show ↥(relKern ℤ X B n) from (pdABInclB X A B).f n x) :
        ↑((singularCochainComplex ℤ X).X n))
      = (show ↥(pdABKern X A B n) from x).1 := rfl

/-- The differential of the relative complex, on underlying cochains. -/
theorem pd_kc_relDiff_coe {X : TopCat} {A : Set X} (n : ℕ) (x : (relComplex ℤ X A).X n) :
    (((relComplex ℤ X A).d n (n+1)) x).1
      = cochainDiff ℤ (TopCat.toSSet.obj X) (n := n) x.1 := by
  rw [relComplex_d]
  show (relDiffLM ℤ X A n x).1 = cochainDiff ℤ (TopCat.toSSet.obj X) (n := n) x.1
  rw [relDiffLM_coe]
  exact PDSplitKC.pd_kc_singularD_eq_cochainDiff X n x.1

/-- The differential of the biproduct of two complexes, on the `inl` summand. -/
theorem pd_kc_biprod_d_inl {X : TopCat} {A B : Set X} {k : ℕ} (a : (relComplex ℤ X A).X k) :
    (relComplex ℤ X A ⊞ relComplex ℤ X B).d k (k+1)
        ((ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ X A ⟶
          relComplex ℤ X A ⊞ relComplex ℤ X B).f k)) a)
      = (ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ X A ⟶
          relComplex ℤ X A ⊞ relComplex ℤ X B).f (k+1)))
          ((relComplex ℤ X A).d k (k+1) a) := by
  have hcomm := congrArg (fun (g : (relComplex ℤ X A).X k ⟶
      (relComplex ℤ X A ⊞ relComplex ℤ X B).X (k+1)) => (ModuleCat.Hom.hom g) a)
    ((biprod.inl : relComplex ℤ X A ⟶ relComplex ℤ X A ⊞ relComplex ℤ X B).comm k (k+1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hcomm

/-- The differential of the biproduct of two complexes, on the `inr` summand. -/
theorem pd_kc_biprod_d_inr {X : TopCat} {A B : Set X} {k : ℕ} (b : (relComplex ℤ X B).X k) :
    (relComplex ℤ X A ⊞ relComplex ℤ X B).d k (k+1)
        ((ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ X B ⟶
          relComplex ℤ X A ⊞ relComplex ℤ X B).f k)) b)
      = (ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ X B ⟶
          relComplex ℤ X A ⊞ relComplex ℤ X B).f (k+1)))
          ((relComplex ℤ X B).d k (k+1) b) := by
  have hcomm := congrArg (fun (g : (relComplex ℤ X B).X k ⟶
      (relComplex ℤ X A ⊞ relComplex ℤ X B).X (k+1)) => (ModuleCat.Hom.hom g) b)
    ((biprod.inr : relComplex ℤ X B ⟶ relComplex ℤ X A ⊞ relComplex ℤ X B).comm k (k+1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hcomm

/-- Vanishing of a pair map transported along equalities of the relative sets. -/
theorem pd_kc_castApply_zero {X : TopCat} {S₁ S₁' S₂ S₂' : Set X} (h₁ : S₁ = S₁') (h₂ : S₂ = S₂')
    (f : X ⟶ X) (hf : ∀ x ∈ S₁, f x ∈ S₂) (hf' : ∀ x ∈ S₁', f x ∈ S₂') (k : ℕ)
    (y : (relComplex ℤ X S₂).homology k)
    (h : (HomologicalComplex.homologyMap (relComplexMap ℤ S₁' S₂' f hf') k) (h₂ ▸ y) = 0) :
    (HomologicalComplex.homologyMap (relComplexMap ℤ S₁ S₂ f hf) k) y = 0 := by
  subst h₁
  subst h₂
  rw [capRel_relComplexMap_congr ℤ S₁ S₂ rfl hf hf']
  exact h

/-- Transport of a difference. -/
theorem pd_kc_cast_sub {ι : Sort*} {P : ι → Type*} [∀ i, AddGroup (P i)] {a b : ι}
    (h : a = b) (x y : P a) : h ▸ (x - y) = h ▸ x - h ▸ y := by cases h; rfl

/-- The elementwise computation of `pdABδ` on a concrete lift. -/
theorem pd_kc_pdABδ_of_lift {X : TopCat} {A B : Set X} {k : ℕ}
    (φ : (relComplex ℤ X (A ∩ B)).X k)
    (hφd : (relComplex ℤ X (A ∩ B)).d k (k+1) φ = 0)
    (φt : (relComplex ℤ X A ⊞ relComplex ℤ X B).X k)
    (hφt : (pdBiprodToInter X A B).f k φt = φ)
    (ψ : (pdABCoh X A B).X (k+1))
    (hx₁ : (pdABDiag X A B).f (k+1) ψ = (relComplex ℤ X A ⊞ relComplex ℤ X B).d k (k+1) φt)
    (hψd : (pdABCoh X A B).d (k+1) (k+2) ψ = 0) :
    PDABClean.pdABδ X A B k ((relComplex ℤ X (A ∩ B)).homologyπ k
        (HomologicalComplex.cyclesMk (relComplex ℤ X (A ∩ B)) φ (k+1)
          ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk k (k+1) rfl)) hφd))
      = (pdABCoh X A B).homologyπ (k+1)
        (HomologicalComplex.cyclesMk (pdABCoh X A B) ψ (k+2)
          ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (k+1) (k+2) rfl)) hψd) := by
  have h := CategoryTheory.ShortComplex.ShortExact.δ_apply (PDABClean.pdAB_shortExact X A B) k (k + 1)
    (ComplexShape.up_mk k (k + 1) rfl) φ hφd φt hφt ψ hx₁ (k + 2)
    ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (k + 1) (k + 2) rfl))
  convert h using 2 <;> rfl

end PDSplitKC

theorem pd_split_kc {M : TopCat} [T2Space M] {N : ℕ}
    {c : (Work.Cohomology.singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Work.Cohomology.Good N c U hU) (hVV : Work.Cohomology.Good N c V hV)
    (hII : Work.Cohomology.Good N c (U ∩ V) hI)
    (k m : ℕ) (hkm : k + m = N) (hm : 1 ≤ m)
    {K₁ K₂ : Set M} (hK₁U : K₁ ⊆ U) (hK₂V : K₂ ⊆ V)
    (hK₁c : IsCompact K₁) (hK₂c : IsCompact K₂)
    (x : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homology k)
    (hx : Work.Cohomology.goodD N c (U ∪ V : Set M) (hU.union hV) (K₁ ∪ K₂)
            (Set.union_subset (hK₁U.trans Set.subset_union_left)
              (hK₂V.trans Set.subset_union_right)) (hK₁c.union hK₂c) k m hkm x = 0) :
    ∃ (K₁' K₂' : Set M) (h₁ : K₁ ⊆ K₁') (h₂ : K₂ ⊆ K₂') (hK₁'U : K₁' ⊆ U) (hK₂'V : K₂' ⊆ V)
      (hK₁'c : IsCompact K₁') (hK₂'c : IsCompact K₂')
      (x₁ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁')).homology k)
      (x₂ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂')).homology k),
      (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
        (Set.union_subset (h₁.trans Set.subset_union_left)
          (h₂.trans Set.subset_union_right) : K₁ ∪ K₂ ⊆ K₁' ∪ K₂')) k) x
        = (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂')) k) x₁
          - (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂')) k) x₂ := by
  classical
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  subst N
  let W : Set M := U ∪ V
  let X : TopCat := TopCat.of W
  have hW : IsOpen W := hU.union hV
  have hK₁W : K₁ ⊆ W := hK₁U.trans Set.subset_union_left
  have hK₂W : K₂ ⊆ W := hK₂V.trans Set.subset_union_right
  have hK₁₂W : K₁ ∪ K₂ ⊆ W := Set.union_subset hK₁W hK₂W
  have hK₁₂c : IsCompact (K₁ ∪ K₂) := hK₁c.union hK₂c
  have hUVW : U ∩ V ⊆ W := Set.inter_subset_left.trans Set.subset_union_left
  have hK₁₂I : K₁ ∩ K₂ ⊆ U ∩ V := Set.inter_subset_inter hK₁U hK₂V
  have hK₁₂Ic : IsCompact (K₁ ∩ K₂) := hK₁c.inter hK₂c
  -- the `A+B` slots
  let A : Set X := pdRelSub W K₁
  let B : Set X := pdRelSub W K₂
  have hAB : pdRelSub W (K₁ ∪ K₂) = A ∩ B := pdRelSub_union W K₁ K₂
  let x' : (relComplex ℤ X (A ∩ B)).homology k := hAB ▸ x
  -- ============ step 1: the setup
  obtain ⟨z₀, hz₀, φA, φB, hdecomp⟩ := PDSplitKC.pd_kc_setup (U := U) (V := V) (K₁ := K₁) (K₂ := K₂) x
  have hz₀' : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).homologyπ k z₀ = x := hz₀
  let φ : Cochain ℤ (TopCat.toSSet.obj X) k :=
    ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z₀).1
  have hφd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φ = 0 := by
    have h0 : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).d k (k + 1)
        ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z₀) = 0 := by
      have hcomp : (ConcreteCategory.hom ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k ≫
            (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).d k (k + 1))) z₀
          = (ConcreteCategory.hom ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).d k (k + 1)))
            ((ConcreteCategory.hom ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k)) z₀) :=
        CategoryTheory.ConcreteCategory.comp_apply _ _ z₀
      rw [← hcomp]
      exact congrArg (fun (g : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).cycles k ⟶
          (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).X (k + 1)) =>
          (ConcreteCategory.hom g) z₀)
        (HomologicalComplex.iCycles_d (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))) k (k + 1))
    have hcomm := congrArg
      (fun (g : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).X k ⟶
          (singularCochainComplex ℤ X).X (k+1)) =>
        (ConcreteCategory.hom g)
          ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z₀))
      ((relIncl ℤ X (pdRelSub W (K₁ ∪ K₂))).comm k (k+1))
    simp only [CategoryTheory.ConcreteCategory.comp_apply] at hcomm
    rw [h0, map_zero] at hcomm
    have hrel : (ConcreteCategory.hom ((relIncl ℤ X (pdRelSub W (K₁ ∪ K₂))).f k))
          ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z₀) = φ := rfl
    rw [hrel] at hcomm
    rw [PDSplitKC.pd_kc_singularD_eq_cochainDiff] at hcomm
    exact hcomm
  -- ============ the `A+B` cocycle `ψ`
  have hψAmem : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1 ∈ relKern ℤ X A (k + 1) := by
    rw [← PDSplitKC.pd_kc_singularD_eq_cochainDiff X k φA.1]
    exact relKern_d_mem X A k φA.1 φA.2
  have hψBmem : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1 ∈ relKern ℤ X B (k + 1) := by
    have hsub : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) (φA.1 - φB.1) = 0 := by
      rw [← hdecomp, ← hφd]
    have hsubD : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k)
        (φA.1 - φB.1) = cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1
          - cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φB.1 := by
      change cochainDiffLM ℤ (TopCat.toSSet.obj X) k (φA.1 - φB.1)
        = cochainDiffLM ℤ (TopCat.toSSet.obj X) k φA.1
          - cochainDiffLM ℤ (TopCat.toSSet.obj X) k φB.1
      exact map_sub (cochainDiffLM ℤ (TopCat.toSSet.obj X) k) φA.1 φB.1
    have heq : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1
        = cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φB.1 := by
      have h2 : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1
          - cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φB.1 = 0 := by
        rw [← hsubD, hsub]
      exact sub_eq_zero.mp h2
    rw [heq, ← PDSplitKC.pd_kc_singularD_eq_cochainDiff X k φB.1]
    exact relKern_d_mem X B k φB.1 φB.2
  let ψ : (pdABCoh X A B).X (k + 1) :=
    ⟨cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1, Submodule.mem_inf.mpr ⟨hψAmem, hψBmem⟩⟩
  -- ============ step 2: the Hatcher decomposition in `M`
  obtain ⟨w, hwc, aM, bM, dM, jM, hα, ⟨a', ha'⟩, ⟨b'', hb''⟩, ⟨d', hd'⟩, ⟨j', hj'⟩⟩ :=
    pd_hatcher_data (M := M) (N := k + (m' + 1)) c hU hV hK₁c hK₂c hK₁U hK₂V
  -- ============ step 3: the decomposition in `X = U ∪ V`
  obtain ⟨α₁X, α₂X, α₃X, ξX, γX, h1incl, h2incl, h3incl, hξdef, ⟨a'', ha''⟩, ⟨bX, hbX⟩,
    ⟨dX, hdX⟩, hbd1, hbd2, hDξ, hlocX, hγXi⟩ :=
    pd_hatcher_Xdata (M := M) (N := k + (m' + 1)) (U := U) (V := V) (K := K₁) (L := K₂)
      hU hV hK₁c hK₂c hK₁U hK₂V w aM bM dM jM hα ⟨j', hj'⟩ ⟨a', ha'⟩ ⟨b'', hb''⟩
      ⟨d', hd'⟩ hwc
  have hξZ : (relChains X (pdRelSub W (K₁ ∪ K₂))).iCycles (k + (m' + 1)) γX
      = ((cokernel.π (inclChains X (pdRelSub W (K₁ ∪ K₂)))).f (k + (m' + 1))).hom
          (α₁X + α₂X + α₃X) := by
    rw [← hξdef]; exact hγXi
  have hγZ : (relChains X (pdRelSub W (K₁ ∪ K₂))).homologyπ (k + (m' + 1)) γX
      = (rfl : k + (m' + 1) = k + (m' + 1)) ▸
          localFundClass (k + (m' + 1)) c W hW (K₁ ∪ K₂) hK₁₂W hK₁₂c := hlocX
  have hgoodD : goodD (k + (m' + 1)) c W hW (K₁ ∪ K₂) hK₁₂W hK₁₂c k (m' + 1) rfl
      ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).homologyπ k z₀)
      = (singularChains ℤ X).homologyπ (m' + 1)
          (relCapPairZ X (pdRelSub W (K₁ ∪ K₂)) k (m' + 1) z₀ γX) :=
    goodD_homologyπ c W hW (K₁ ∪ K₂) hK₁₂W hK₁₂c k (m' + 1) rfl z₀ γX hγZ
      (α₁X + α₂X + α₃X) hξZ
  have hzero : (singularChains ℤ X).homologyπ (m' + 1)
      (relCapPairZ X (pdRelSub W (K₁ ∪ K₂)) k (m' + 1) z₀ γX) = 0 := by
    rw [← hgoodD, hz₀']; exact hx
  obtain ⟨β, hβ⟩ := pd_boundary_of_zero_class (singularChains ℤ X) (m' + 1)
    (relCapPairZ X (pdRelSub W (K₁ ∪ K₂)) k (m' + 1) z₀ γX) hzero
  have hcapβ : (singularChains ℤ X).d (m' + 2) (m' + 1) β
      = cap ℤ (TopCat.toSSet.obj X) φ (m' + 1) (α₁X + α₂X + α₃X) := by
    rw [hβ, relCapPairZ_iCycles_apply (X := X) (A := pdRelSub W (K₁ ∪ K₂)) z₀ γX hξZ]
  -- ============ step 4: the crux in `X`
  have hUt : IsOpen (pdTr W U) := hU.preimage continuous_subtype_val
  have hVt : IsOpen (pdTr W V) := hV.preimage continuous_subtype_val
  have hcov : pdTr W U ∪ pdTr W V = (Set.univ : Set W) := by
    rw [pdTr_union]
    ext y
    exact ⟨fun _ => trivial, fun _ => y.2⟩
  have hα₁' : α₁X ∈ LinearMap.range (((inclChains X (pdTr W U \ pdTr W K₂)).f
      (k + (m' + 1))).hom) := by
    rw [← pdTr_sdiff W U K₂]; exact ⟨a'', ha''⟩
  have hα₂' : α₂X ∈ LinearMap.range (((inclChains X (pdTr W U ∩ pdTr W V)).f
      (k + (m' + 1))).hom) := by
    rw [← pdTr_inter W U V]; exact ⟨bX, hbX⟩
  have hα₃' : α₃X ∈ LinearMap.range (((inclChains X (pdTr W V \ pdTr W K₁)).f
      (k + (m' + 1))).hom) := by
    rw [← pdTr_sdiff W V K₁]; exact ⟨dX, hdX⟩
  have hcL : (singularChains ℤ X).d (k + (m' + 1)) (k + m') α₁X
      ∈ LinearMap.range (((inclChains X (pdTr W K₂)ᶜ).f (k + m')).hom) := by
    have h := hbd1
    rw [show (k + (m' + 1)) - 1 = k + m' by omega] at h
    rw [← pdRelSub_eq_compl_pdTr W K₂]
    exact h
  have hcK : (singularChains ℤ X).d (k + (m' + 1)) (k + m') α₃X
      ∈ LinearMap.range (((inclChains X (pdTr W K₁)ᶜ).f (k + m')).hom) := by
    have h := hbd2
    rw [show (k + (m' + 1)) - 1 = k + m' by omega] at h
    rw [← pdRelSub_eq_compl_pdTr W K₁]
    exact h
  have hcD : (singularChains ℤ X).d (k + (m' + 1)) (k + m') (α₁X + α₂X + α₃X)
      ∈ LinearMap.range (((inclChains X (pdTr W K₁)ᶜ).f (k + m')).hom) := by
    have h := hDξ
    rw [show (k + (m' + 1)) - 1 = k + m' by omega] at h
    rw [hξdef] at h
    have hsub : pdRelSub W (K₁ ∪ K₂) ⊆ ((pdTr W K₁)ᶜ : Set W) := by
      intro y hy hh
      exact hy (Or.inl hh)
    exact mem_range_inclChains_of_subset hsub h
  have hφA' : φA.1 ∈ relKern ℤ X ((pdTr W K₁)ᶜ) k := by
    rw [← pdRelSub_eq_compl_pdTr W K₁]; exact φA.2
  have hφB' : φB.1 ∈ relKern ℤ X ((pdTr W K₂)ᶜ) k := by
    rw [← pdRelSub_eq_compl_pdTr W K₂]; exact φB.2
  obtain ⟨γ, hγmem, hγd⟩ := pd_union_crux_zero_wk (X := X) (U := pdTr W U) (V := pdTr W V)
    (K := pdTr W K₁) (L := pdTr W K₂) hUt hVt hcov α₁X α₂X α₃X φ φA.1 φB.1 hφA' hφB'
    hdecomp hα₁' hα₂' hα₃' hcL hcK hcD hφd ⟨β, hcapβ⟩
  have hγmem' : γ ∈ LinearMap.range (((inclChains X (pdTr W (U ∩ V))).f (m' + 1)).hom) := by
    rw [pdTr_inter W U V]; exact hγmem
  -- ============ step 5: the descent to `U ∩ V`
  obtain ⟨bInter, γ₂, hbInter, hγ₂i, hγ₂c⟩ := pd_hatcher_inter4 (M := M) (N := k + (m' + 1))
    (U := U) (V := V) hU hV hI hK₁c hK₂c hK₁U hK₂V w aM bM dM jM hα ⟨j', hj'⟩ ⟨a', ha'⟩
    ⟨b'', hb''⟩ ⟨d', hd'⟩ hwc
  let bInt : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).X ((k+1) + m') :=
    (capIdx k m') ▸ bInter
  let α₂Y : (singularChains ℤ X).X ((k+1) + m') := (capIdx k m') ▸ α₂X
  have hbInt : (inclChains M (U ∪ V)).f ((k+1)+m') α₂Y
      = (inclChains M (U ∩ V)).f ((k+1)+m') bInt := by
    have h1 : (inclChains M (U ∪ V)).f ((k+1)+m') α₂Y
        = (capIdx k m') ▸ ((inclChains M (U ∪ V)).f (k + (m' + 1)) α₂X) :=
      (pdInter_cast_apply_aux (fun n => (inclChains M (U ∪ V)).f n) (capIdx k m') α₂X).symm
    have h2 : (inclChains M (U ∩ V)).f ((k+1)+m') bInt
        = (capIdx k m') ▸ ((inclChains M (U ∩ V)).f (k + (m' + 1)) bInter) :=
      (pdInter_cast_apply_aux (fun n => (inclChains M (U ∩ V)).f n) (capIdx k m') bInter).symm
    rw [h1, h2, h2incl, hbInter]
  have hγd' : (singularChains ℤ X).d (m'+1) m' γ
      = (-1:ℤ)^(k+1) • cap ℤ (TopCat.toSSet.obj X) ψ.1 m' α₂Y := hγd
  obtain ⟨δ, hδ⟩ := pd_inter_cap_boundary (M := M) (U := U) (V := V) hUVW (k := k) (mj := m')
    ((-1:ℤ)^(k+1)) ψ.1 bInt α₂Y hbInt ⟨γ, hγmem', hγd'⟩
  -- the restricted cochain
  let ψuv : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) (k+1) :=
    ψ.1.comp ((SSet.chainComplexMap (TopCat.toSSet.map (pdIncl W (U ∩ V) hUVW))
      (ModuleCat.of ℤ ℤ)).f (k+1)).hom
  have hδ' : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (m'+1) m' δ
      = (-1:ℤ)^(k+1) • cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) ψuv m' bInt := hδ
  -- ============ step 6: the honest representative of the `(K₁∩K₂)`-slot class
  have hAopen : IsOpen A := by
    show IsOpen (pdRelSub W K₁)
    rw [pdRelSub_eq_compl_pdTr]
    exact (hK₁c.isClosed.preimage continuous_subtype_val).isOpen_compl
  have hBopen : IsOpen B := by
    show IsOpen (pdRelSub W K₂)
    rw [pdRelSub_eq_compl_pdTr]
    exact (hK₂c.isClosed.preimage continuous_subtype_val).isOpen_compl
  have hψd : (pdABCoh X A B).d (k + 1) (k + 2) ψ = 0 := by
    apply Subtype.ext
    rw [pdABCoh_d_coe]
    show ((singularCochainComplex ℤ X).d (k+1) (k+2))
        (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1) = 0
    rw [← PDSplitKC.pd_kc_singularD_eq_cochainDiff X k φA.1]
    have h := congrArg ModuleCat.Hom.hom
      (HomologicalComplex.d_comp_d (singularCochainComplex ℤ X) k (k+1) (k+2))
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h φA.1
  let ψc : (pdABCoh X A B).cycles (k + 1) := PDSplitKC.pd_kc_cycleC (k + 1) ψ hψd
  have hψc_i : (pdABCoh X A B).iCycles (k+1) ψc = ψ := PDSplitKC.pd_kc_iCycles_cycleC (k+1) ψ hψd
  let δx : (pdABCoh X A B).homology (k+1) := (pdABCoh X A B).homologyπ (k+1) ψc
  haveI hQ : IsIso (HomologicalComplex.homologyMap (pdABInclRel X A B) (k+1)) :=
    pdABCoh_quasiIso hAopen hBopen (k+1)
  let y : (relComplex ℤ X (A ∪ B)).homology (k+1) :=
    (CategoryTheory.inv (HomologicalComplex.homologyMap (pdABInclRel X A B) (k+1))).hom δx
  have hy : (HomologicalComplex.homologyMap (pdABInclRel X A B) (k+1)).hom y = δx :=
    IsIso.inv_hom_id_apply _ _
  obtain ⟨ηc, hηc⟩ := (ModuleCat.epi_iff_surjective
    ((relComplex ℤ X (A ∪ B)).homologyπ (k+1))).mp inferInstance y
  have hηcls : (HomologicalComplex.homologyMap (pdABInclRel X A B) (k+1)).hom
      ((relComplex ℤ X (A ∪ B)).homologyπ (k+1) ηc) =
        (pdABCoh X A B).homologyπ (k+1) ψc := by
    rw [hηc, hy]
  obtain ⟨χval, hχval⟩ := pd_us_cycles_eq_of_class_eq (n := k)
    ((HomologicalComplex.cyclesMap (pdABInclRel X A B) (k+1)).hom ηc) ψc
    (by rw [← pdInter_homologyMap_homologyπ_cyclesMap (pdABInclRel X A B) (k+1) ηc, hηcls])
  let χc : Cochain ℤ (TopCat.toSSet.obj X) k := χval.1
  have hcoe : (show Cochain ℤ (TopCat.toSSet.obj X) (k+1) from
      (((pdABCoh X A B).d k (k+1)) χval).1)
      = cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χc := by
    rw [pdABCoh_d]
    change (show Cochain ℤ (TopCat.toSSet.obj X) (k+1) from
      (pdABDiffLM X A B k χval).1) = cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χval.1
    rw [pdABDiffLM_coe]
    exact PDSplitKC.pd_kc_singularD_eq_cochainDiff X k χval.1
  have hχd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χc
      = ((relComplex ℤ X (A ∪ B)).iCycles (k+1) ηc).1 - ψ.1 := by
    have hsub : (show Cochain ℤ (TopCat.toSSet.obj X) (k+1) from
        (((pdABCoh X A B).d k (k+1)) χval).1)
        = ((relComplex ℤ X (A ∪ B)).iCycles (k+1) ηc).1 - ψ.1 := by
      have h := congrArg Subtype.val hχval
      rw [Submodule.coe_sub] at h
      rw [h]
      rw [pdInter_iCycles_cyclesMap_apply (pdABInclRel X A B) (k+1) ηc]
      simp only [pdABInclRel_coe]
      congr 1
      exact congrArg Subtype.val hψc_i
    rw [← hcoe]
    exact hsub
  -- the restriction to `U ∩ V`
  let incl_uv : TopCat.of (U ∩ V : Set M) ⟶ X := pdIncl W (U ∩ V) hUVW
  let ηval : Cochain ℤ (TopCat.toSSet.obj X) (k+1) :=
    ((relComplex ℤ X (A ∪ B)).iCycles (k+1) ηc).1
  let ηuv : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) (k+1) :=
    ηval.comp ((chainMap ℤ (TopCat.of (U ∩ V : Set M)) X incl_uv).f (k+1)).hom
  let χuv : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) k :=
    χc.comp ((chainMap ℤ (TopCat.of (U ∩ V : Set M)) X incl_uv).f k).hom
  have hχuv : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) (n := k) χuv
      = ηuv - ψuv := by
    have h1 : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) (n := k) χuv
        = (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χc).comp
            ((chainMap ℤ (TopCat.of (U ∩ V : Set M)) X incl_uv).f (k+1)).hom :=
      PDSplitKC.pd_kc_cochainDiff_pullback incl_uv k χc
    rw [h1, hχd, LinearMap.sub_comp]
    rfl
  -- the restriction of the honest cycle
  have hsub_AB : ∀ x ∈ pdRelSub (U ∩ V) (K₁ ∩ K₂), incl_uv x ∈ A ∪ B := by
    intro x hx
    have hx' : (x : M) ∉ K₁ ∩ K₂ := hx
    have hxa : (x : M) ∉ K₁ ∨ (x : M) ∉ K₂ := not_and_or.mp hx'
    rcases hxa with h | h
    · refine Or.inl ?_
      show ((incl_uv x : ↥W) : M) ∉ K₁
      exact h
    · refine Or.inr ?_
      show ((incl_uv x : ↥W) : M) ∉ K₂
      exact h
  let Restr : (relComplex ℤ X (A ∪ B)) ⟶
      (relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) (K₁ ∩ K₂))) :=
    relComplexMap ℤ (X₁ := TopCat.of (U ∩ V : Set M)) (X₂ := X)
      (pdRelSub (U ∩ V) (K₁ ∩ K₂)) (A ∪ B) incl_uv hsub_AB
  let zuv : (relComplex ℤ (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V) (K₁ ∩ K₂))).cycles (k+1) :=
    (HomologicalComplex.cyclesMap Restr (k+1)).hom ηc
  have hzuv_coe : ((relComplex ℤ (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V) (K₁ ∩ K₂))).iCycles (k+1) zuv).1 = ηuv := by
    have h1 := congrArg Subtype.val (pdInter_iCycles_cyclesMap_apply Restr (k+1) ηc)
    rw [h1, PDSplitKC.pd_kc_relMap_coe]
  have hzuv : (relComplex ℤ (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V) (K₁ ∩ K₂))).homologyπ (k+1) zuv
      = (HomologicalComplex.homologyMap Restr (k+1)).hom y := by
    rw [← pdInter_homologyMap_homologyπ_cyclesMap Restr (k+1) ηc, hηc]
  -- the transported middle relative cycle of `U ∩ V`
  let γ₂' : (relChains (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V) (K₁ ∩ K₂))).cycles ((k+1) + m') := (capIdx k m') ▸ γ₂
  have hγ₂'hom : (relChains (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V) (K₁ ∩ K₂))).homologyπ ((k+1) + m') γ₂'
      = (capIdx k m').symm ▸ localFundClass (k + (m' + 1)) c (U ∩ V) hI (K₁ ∩ K₂)
          hK₁₂I hK₁₂Ic := by
    rw [pdInter_cast_homologyπ_rel, hγ₂c]
  have hγ₂'cyc : (relChains (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V) (K₁ ∩ K₂))).iCycles ((k+1) + m') γ₂'
      = ((cokernel.π (inclChains (TopCat.of (U ∩ V : Set M))
          (pdRelSub (U ∩ V) (K₁ ∩ K₂)))).f ((k+1) + m')).hom bInt := by
    rw [pdInter_cast_iCycles_rel, hγ₂i, pdInter_cast_cokerπ]
  have hgoodD_uv : goodD (k + (m' + 1)) c (U ∩ V) hI (K₁ ∩ K₂) hK₁₂I hK₁₂Ic
      (k+1) m' (capIdx k m').symm
      ((relComplex ℤ (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V) (K₁ ∩ K₂))).homologyπ (k+1) zuv)
      = (singularChains ℤ (TopCat.of (U ∩ V : Set M))).homologyπ m'
          (relCapPairZ (TopCat.of (U ∩ V : Set M))
            (pdRelSub (U ∩ V) (K₁ ∩ K₂)) (k+1) m' zuv γ₂') :=
    goodD_homologyπ c (U ∩ V) hI (K₁ ∩ K₂) hK₁₂I hK₁₂Ic (k+1) m' (capIdx k m').symm
      zuv γ₂' hγ₂'hom bInt hγ₂'cyc
  -- the vanishing of the cap product
  have hUVI : pdTr W (U ∩ V) = (pdTr W U ∩ pdTr W V : Set W) := pdTr_inter W U V
  have hcDint : (singularChains ℤ X).d (k + (m' + 1)) (k + m') (α₁X + α₂X + α₃X)
      ∈ LinearMap.range (((inclChains X ((pdTr W K₁)ᶜ ∩ (pdTr W K₂)ᶜ)).f (k + m')).hom) := by
    have h := hDξ
    rw [show (k + (m' + 1)) - 1 = k + m' by omega] at h
    rw [hξdef] at h
    have hsub : pdRelSub W (K₁ ∪ K₂) ⊆ ((pdTr W K₁)ᶜ ∩ (pdTr W K₂)ᶜ : Set W) := by
      intro y hy
      exact ⟨fun h1 => hy (Or.inl h1), fun h2 => hy (Or.inr h2)⟩
    exact mem_range_inclChains_of_subset hsub h
  have hχrel : χc ∈ relKern ℤ X ((pdTr W K₁)ᶜ) k ⊓ relKern ℤ X ((pdTr W K₂)ᶜ) k := by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp χval.2
    exact Submodule.mem_inf.mpr
      ⟨by rw [← pdRelSub_eq_compl_pdTr W K₁]; exact h1,
       by rw [← pdRelSub_eq_compl_pdTr W K₂]; exact h2⟩
  -- the first boundary fact: `cap ψuv m' bInt` is a boundary
  have hbdψ : ∃ w : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).X (m'+1),
      (singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (m'+1) m' w
        = cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) ψuv m' bInt := by
    refine ⟨((-1:ℤ)^(k+1)) • δ, ?_⟩
    rw [map_zsmul, hδ', ← mul_zsmul]
    rw [show (-1:ℤ)^(k+1) * (-1:ℤ)^(k+1) = 1 by
      rw [← pow_add]; exact Even.neg_one_pow ⟨k+1, by ring⟩, one_zsmul]
  -- the second: `cap (d χuv) m' bInt` is a boundary
  have hbdχ : ∃ w : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).X (m'+1),
      (singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (m'+1) m' w
        = cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M)))
            (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) (n := k) χuv) m' bInt := by
    obtain ⟨γχ, hγχmem, hγχd⟩ := PDSplitKC.pd_kc_cap_cochainDiff_weak (X := X) (U := pdTr W U)
      (V := pdTr W V) (K := pdTr W K₁) (L := pdTr W K₂)
      (k := k) (mj := m') (N := k + (m' + 1)) rfl α₁X α₂X α₃X hα₂' hcL hcK hcDint hχrel
    have hγχmem' : γχ ∈ LinearMap.range (((inclChains X (pdTr W (U ∩ V))).f (m'+1)).hom) := by
      rw [hUVI]; exact hγχmem
    have hγχd' : (singularChains ℤ X).d (m'+1) m' γχ
        = (-1:ℤ)^(k+1) • cap ℤ (TopCat.toSSet.obj X)
            (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χc) m' α₂Y := hγχd
    obtain ⟨δχ, hδχ⟩ := pd_inter_cap_boundary (M := M) (U := U) (V := V) hUVW
      (k := k) (mj := m') ((-1:ℤ)^(k+1)) (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χc)
      bInt α₂Y hbInt ⟨γχ, hγχmem', hγχd'⟩
    refine ⟨((-1:ℤ)^(k+1)) • δχ, ?_⟩
    have hcomp : (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χc).comp
        ((SSet.chainComplexMap (TopCat.toSSet.map (pdIncl W (U ∩ V) hUVW))
          (ModuleCat.of ℤ ℤ)).f (k+1)).hom = cochainDiff ℤ
            (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) (n := k) χuv := by
      rw [PDSplitKC.pd_kc_cochainDiff_pullback]
      rfl
    rw [map_zsmul, hδχ, ← hcomp, ← mul_zsmul]
    rw [show (-1:ℤ)^(k+1) * (-1:ℤ)^(k+1) = 1 by
      rw [← pow_add]; exact Even.neg_one_pow ⟨k+1, by ring⟩, one_zsmul]
  -- hence the class of `cap ηuv m' bInt` vanishes
  have hbdη : ∃ w : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).X (m'+1),
      (singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (m'+1) m' w
        = cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) ηuv m' bInt := by
    obtain ⟨w₁, hw₁⟩ := hbdψ
    obtain ⟨w₂, hw₂⟩ := hbdχ
    refine ⟨w₁ + w₂, ?_⟩
    rw [map_add, hw₁, hw₂]
    have hsub : cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M)))
        (ηuv - ψuv) m' bInt
        = cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) ηuv m' bInt
          - cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) ψuv m' bInt :=
      cap_sub_apply ηuv ψuv bInt
    rw [← hχuv] at hsub
    rw [hsub]
    abel
  have hgoodD_zero : goodD (k + (m' + 1)) c (U ∩ V) hI (K₁ ∩ K₂) hK₁₂I hK₁₂Ic
      (k+1) m' (capIdx k m').symm
      ((relComplex ℤ (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V) (K₁ ∩ K₂))).homologyπ (k+1) zuv) = 0 := by
    rw [hgoodD_uv, pdHom_homologyπ_eq_zero_iff_d]
    obtain ⟨w, hw⟩ := hbdη
    refine ⟨w, ?_⟩
    rw [hw]
    exact ((relCapPairZ_iCycles_apply (X := TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V) (K₁ ∩ K₂)) (n := k+1) (m := m') zuv γ₂'
        (ξ := bInt) hγ₂'cyc).trans (by rw [hzuv_coe])).symm
  -- ============ step 7: the kill in the `U ∩ V` slot
  obtain ⟨L'', hK₁₂L'', hL''I, hL''c, hEnlW⟩ :=
    hII.kill (k+1) m' (capIdx k m').symm (K₁ ∩ K₂) hK₁₂I hK₁₂Ic
      ((relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) (K₁ ∩ K₂))).homologyπ (k+1) zuv)
      hgoodD_zero
  -- ============ step 8: the enlargement, and the transport of the vanishing to `X`
  let K₁' : Set M := K₁ ∪ L''
  let K₂' : Set M := K₂ ∪ L''
  have h₁ : K₁ ⊆ K₁' := fun x hx => Or.inl hx
  have h₂ : K₂ ⊆ K₂' := fun x hx => Or.inl hx
  have hK₁'U : K₁' ⊆ U := Set.union_subset hK₁U (fun x hx => (hL''I hx).1)
  have hK₂'V : K₂' ⊆ V := Set.union_subset hK₂V (fun x hx => (hL''I hx).2)
  have hK₁'c : IsCompact K₁' := hK₁c.union hL''c
  have hK₂'c : IsCompact K₂' := hK₂c.union hL''c
  let A' : Set X := pdRelSub W K₁'
  let B' : Set X := pdRelSub W K₂'
  have hA'mem : A' ⊆ A := pdRelSub_mono h₁
  have hB'mem : B' ⊆ B := pdRelSub_mono h₂
  have hInter' : K₁' ∩ K₂' = L'' := by
    show (K₁ ∪ L'') ∩ (K₂ ∪ L'') = L''
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact hK₁₂L'' ⟨h1, h2⟩
      · exact h2
      · exact h1
      · exact h1
    · intro hx; exact ⟨Or.inr hx, Or.inr hx⟩
  have hUnionAB : A' ∪ B' = pdRelSub W L'' := by
    have h1 : A' ∪ B' = pdRelSub W (K₁' ∩ K₂') := pdRelSub_union_sub W K₁' K₂'
    rw [h1, hInter']
  have hInterAB : A' ∩ B' = pdRelSub W (K₁' ∪ K₂') := (pdRelSub_union W K₁' K₂').symm
  have hsubY : ∀ x ∈ pdRelSub W L'', x ∈ A ∪ B := by
    intro x hx
    have hx' : x ∈ pdRelSub W (K₁ ∩ K₂) := pdRelSub_mono hK₁₂L'' hx
    rwa [← pdRelSub_union_sub W K₁ K₂] at hx'
  let enlY : (relComplex ℤ X (A ∪ B)) ⟶ (relComplex ℤ X (pdRelSub W L'')) :=
    relComplexMap ℤ (X₁ := X) (X₂ := X) (pdRelSub W L'') (A ∪ B) (𝟙 X) hsubY
  let Restr'' : (relComplex ℤ X (pdRelSub W L'')) ⟶
      (relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) L'')) :=
    relComplexMap ℤ (X₁ := TopCat.of (U ∩ V : Set M)) (X₂ := X)
      (pdRelSub (U ∩ V) L'') (pdRelSub W L'') incl_uv (fun x hx => hx)
  let enlU : (relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) (K₁ ∩ K₂)))
      ⟶ (relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) L'')) :=
    pdRelComplexEnlarge (U ∩ V) hK₁₂L''
  haveI hiso'' : IsIso (HomologicalComplex.homologyMap Restr'' (k+1)) :=
    pdCohExcision (M := M) (W := W) (U := U ∩ V) hUVW hI hW (K := L'') hL''I hL''c (k+1)
  have hsq1 : enlY ≫ Restr'' = relComplexMap ℤ (X₁ := TopCat.of (U ∩ V : Set M)) (X₂ := X)
      (pdRelSub (U ∩ V) L'') (A ∪ B) incl_uv (fun x hx => hsubY (incl_uv x) hx) := by
    dsimp only [enlY, Restr'']
    simpa only [Category.comp_id] using (capRel_relComplexMap_comp (R := ℤ)
      (X₀ := TopCat.of (U ∩ V : Set M)) (X₁ := X) (X₂ := X)
      (pdRelSub (U ∩ V) L'') (pdRelSub W L'') (A ∪ B)
      incl_uv (𝟙 X) (fun x hx => hx) hsubY).symm
  have hsq2 : Restr ≫ enlU = relComplexMap ℤ (X₁ := TopCat.of (U ∩ V : Set M)) (X₂ := X)
      (pdRelSub (U ∩ V) L'') (A ∪ B) incl_uv
      (fun x hx => hsub_AB x (pdRelSub_mono hK₁₂L'' hx)) := by
    dsimp only [Restr, enlU, pdRelComplexEnlarge]
    simpa only [Category.id_comp] using (capRel_relComplexMap_comp (R := ℤ)
      (X₀ := TopCat.of (U ∩ V : Set M)) (X₁ := TopCat.of (U ∩ V : Set M)) (X₂ := X)
      (pdRelSub (U ∩ V) L'') (pdRelSub (U ∩ V) (K₁ ∩ K₂)) (A ∪ B)
      (𝟙 (TopCat.of (U ∩ V : Set M))) incl_uv
      (pdRelSub_mono hK₁₂L'') hsub_AB).symm
  have hsquare : enlY ≫ Restr'' = Restr ≫ enlU := by
    rw [hsq1, hsq2]
  have henlY : (HomologicalComplex.homologyMap enlY (k+1)) y = 0 := by
    have hinj : Function.Injective (HomologicalComplex.homologyMap Restr'' (k+1)).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    apply hinj
    rw [map_zero]
    have hstep : (HomologicalComplex.homologyMap Restr'' (k+1))
        ((HomologicalComplex.homologyMap enlY (k+1)) y)
        = (HomologicalComplex.homologyMap enlU (k+1))
            ((HomologicalComplex.homologyMap Restr (k+1)) y) := by
      have hc := congrArg (fun (m : relComplex ℤ X (A ∪ B) ⟶
          relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) L'')) =>
          (HomologicalComplex.homologyMap m (k+1)) y) hsquare
      simp only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp,
        LinearMap.comp_apply] at hc
      exact hc
    rw [hstep, ← hzuv]
    exact hEnlW
  -- the vanishing in the `A' ∪ B'` slot, and hence the `A+B` naturality
  have hvanUn : (HomologicalComplex.homologyMap
        (pdRelComplexEnlargeUnion X hA'mem hB'mem) (k+1)) y = 0 :=
    PDSplitKC.pd_kc_castApply_zero hUnionAB rfl (𝟙 X)
      (Set.union_subset_union hA'mem hB'mem) hsubY (k+1) y henlY
  have hδenl : (HomologicalComplex.homologyMap (pdABEnlarge X hA'mem hB'mem) (k+1)) δx = 0 := by
    have hsq2 := congrArg (fun (m : relComplex ℤ X (A ∪ B) ⟶ pdABCoh X A' B') =>
      (HomologicalComplex.homologyMap m (k+1)) y) (pdABInclRel_comp_pdABEnlarge X hA'mem hB'mem)
    simp only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply] at hsq2
    rw [hy, hvanUn, map_zero] at hsq2
    exact hsq2
  -- ============ step 9: the connecting map on the class of `x`
  let z₁ : (relComplex ℤ X (A ∩ B)).cycles k := hAB ▸ z₀
  let φe : (relComplex ℤ X (A ∩ B)).X k := (relComplex ℤ X (A ∩ B)).iCycles k z₁
  have hφed : (relComplex ℤ X (A ∩ B)).d k (k+1) φe = 0 := by
    have h := congrArg (fun (g : (relComplex ℤ X (A ∩ B)).cycles k ⟶
        (relComplex ℤ X (A ∩ B)).X (k+1)) =>
      (ConcreteCategory.hom g) z₁)
      (HomologicalComplex.iCycles_d (relComplex ℤ X (A ∩ B)) k (k+1))
    simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h
  have hφecoe : φe.1 = φ := by
    show ((relComplex ℤ X (A ∩ B)).iCycles k (hAB ▸ z₀)).1 = φ
    rw [PDSplitKC.pd_kc_iCycles_cast]
  have hz₁ : (HomologicalComplex.homologyπ (relComplex ℤ X (A ∩ B)) k) z₁ = x' := by
    rw [← PDSplitKC.pd_kc_cast_homologyπ' hAB z₀, hz₀']
  have hφAB : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1
      = cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φB.1 := by
    have hsub : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) (φA.1 - φB.1) = 0 := by
      rw [← hdecomp, ← hφd]
    have hsubD : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k)
        (φA.1 - φB.1) = cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1
          - cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φB.1 := by
      change cochainDiffLM ℤ (TopCat.toSSet.obj X) k (φA.1 - φB.1)
        = cochainDiffLM ℤ (TopCat.toSSet.obj X) k φA.1
          - cochainDiffLM ℤ (TopCat.toSSet.obj X) k φB.1
      exact map_sub (cochainDiffLM ℤ (TopCat.toSSet.obj X) k) φA.1 φB.1
    have h2 : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1
        - cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φB.1 = 0 := by
      rw [← hsubD, hsub]
    exact sub_eq_zero.mp h2
  let φt : (relComplex ℤ X A ⊞ relComplex ℤ X B).X k :=
    (ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ X A ⟶
        relComplex ℤ X A ⊞ relComplex ℤ X B).f k)) φA
      + (ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ X B ⟶
        relComplex ℤ X A ⊞ relComplex ℤ X B).f k)) φB
  have hφt : (pdBiprodToInter X A B).f k φt = φe := by
    apply Subtype.ext
    rw [PDABClean.pdBiprodToInter_coe]
    rw [← hdecomp]
    exact hφecoe.symm
  have hdφt : (relComplex ℤ X A ⊞ relComplex ℤ X B).d k (k+1) φt
      = (ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ X A ⟶
          relComplex ℤ X A ⊞ relComplex ℤ X B).f (k+1)))
          ((relComplex ℤ X A).d k (k+1) φA)
        + (ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ X B ⟶
          relComplex ℤ X A ⊞ relComplex ℤ X B).f (k+1)))
          ((relComplex ℤ X B).d k (k+1) φB) := by
    show (relComplex ℤ X A ⊞ relComplex ℤ X B).d k (k+1)
        ((biprod.inl : relComplex ℤ X A ⟶
          relComplex ℤ X A ⊞ relComplex ℤ X B).f k φA
          + (biprod.inr : relComplex ℤ X B ⟶
            relComplex ℤ X A ⊞ relComplex ℤ X B).f k φB) = _
    rw [map_add, PDSplitKC.pd_kc_biprod_d_inl, PDSplitKC.pd_kc_biprod_d_inr]
  have hc1 : (biprod.fst : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
      relComplex ℤ X A).f (k+1) ((relComplex ℤ X A ⊞ relComplex ℤ X B).d k (k+1) φt)
      = (relComplex ℤ X A).d k (k+1) φA := by
    rw [hdφt, map_add, PDABClean.pdBiprodFst_inl, PDABClean.pdBiprodFst_inr, add_zero]
  have hc2 : (biprod.snd : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
      relComplex ℤ X B).f (k+1) ((relComplex ℤ X A ⊞ relComplex ℤ X B).d k (k+1) φt)
      = (relComplex ℤ X B).d k (k+1) φB := by
    rw [hdφt, map_add, PDABClean.pdBiprodSnd_inl, PDABClean.pdBiprodSnd_inr, zero_add]
  have hx₁d : (pdABDiag X A B).f (k+1) ψ = (relComplex ℤ X A ⊞ relComplex ℤ X B).d k (k+1) φt := by
    apply PDABClean.pdBiprod_ext
    · rw [PDABClean.pdABDiag_fst, hc1]
      apply Subtype.ext
      rw [PDABClean.pdABInclA_val]
      have hcoe2 : (((relComplex ℤ X A).d k (k+1)) φA).1
          = cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1 :=
        PDSplitKC.pd_kc_relDiff_coe (X := X) (A := A) k φA
      rw [hcoe2]
    · rw [PDABClean.pdABDiag_snd, hc2]
      apply Subtype.ext
      rw [PDSplitKC.pd_kc_pdABInclB_val]
      have hcoe2 : (((relComplex ℤ X B).d k (k+1)) φB).1
          = cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φB.1 :=
        PDSplitKC.pd_kc_relDiff_coe (X := X) (A := B) k φB
      rw [hcoe2, ← hφAB]
  -- the `pdABδ` computation
  have hcycz : HomologicalComplex.cyclesMk (relComplex ℤ X (A ∩ B)) φe (k+1)
      ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk k (k+1) rfl)) hφed = z₁ :=
    (ModuleCat.mono_iff_injective ((relComplex ℤ X (A ∩ B)).iCycles k)).mp inferInstance
      (by rw [PDSplitKC.pd_kc_iCycles_cyclesMk])
  have hcycψ : HomologicalComplex.cyclesMk (pdABCoh X A B) ψ (k+2)
      ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (k+1) (k+2) rfl)) hψd = ψc :=
    (ModuleCat.mono_iff_injective ((pdABCoh X A B).iCycles (k+1))).mp inferInstance
      (by rw [PDSplitKC.pd_kc_iCycles_cyclesMk, PDSplitKC.pd_kc_iCycles_cycleC])
  have hdel : PDABClean.pdABδ X A B k x' = δx := by
    have h := PDSplitKC.pd_kc_pdABδ_of_lift (X := X) (A := A) (B := B) (k := k)
      φe hφed φt hφt ψ hx₁d hψd
    rw [hcycz, hcycψ, hz₁] at h
    exact h
  -- the naturality and the exactness
  have hδ' : (PDABClean.pdABδ X A' B' k) ((HomologicalComplex.homologyMap
      (pdRelComplexEnlargeInter X hA'mem hB'mem) k) x') = 0 := by
    have hnat := congrArg (fun (m : (relComplex ℤ X (A ∩ B)).homology k ⟶
        (pdABCoh X A' B').homology (k+1)) => m x') (pdABdelta_natural X hA'mem hB'mem k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [hdel, hδenl] at hnat
    exact hnat.symm
  have hmem : ((HomologicalComplex.homologyMap
      (pdRelComplexEnlargeInter X hA'mem hB'mem) k) x') ∈
      LinearMap.range ((HomologicalComplex.homologyMap (PDABClean.pdABg X A' B') k).hom) := by
    have hex := PDABClean.pdAB_exact₃ X A' B' k
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
    rw [hex]
    exact LinearMap.mem_ker.mpr hδ'
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hmem
  let x₁ : (relComplex ℤ X A').homology k :=
    (HomologicalComplex.homologyMap (biprod.fst : relComplex ℤ X A' ⊞
      relComplex ℤ X B' ⟶ relComplex ℤ X A') k) z
  let x₂ : (relComplex ℤ X B').homology k :=
    (HomologicalComplex.homologyMap (biprod.snd : relComplex ℤ X A' ⊞
      relComplex ℤ X B' ⟶ relComplex ℤ X B') k) z
  have hdecomp : (HomologicalComplex.homologyMap
      (pdRelComplexEnlargeInter X hA'mem hB'mem) k) x'
      = (HomologicalComplex.homologyMap (pdToInterA X A' B') k) x₁
        - (HomologicalComplex.homologyMap (pdToInterB X A' B') k) x₂ := by
    rw [← hz]
    have hdesc : PDABClean.pdABg X A' B' = biprod.fst ≫ pdToInterA X A' B'
        + biprod.snd ≫ (-(pdToInterB X A' B')) := biprod.desc_eq
    rw [hdesc, HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_neg]
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_neg,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, sub_eq_add_neg]
    try rfl
  refine ⟨K₁', K₂', h₁, h₂, hK₁'U, hK₂'V, hK₁'c, hK₂'c, x₁, x₂, ?_⟩
  have hc0 : (HomologicalComplex.homologyMap (pdRelComplexEnlarge W
        (Set.union_subset (h₁.trans Set.subset_union_left)
          (h₂.trans Set.subset_union_right) : K₁ ∪ K₂ ⊆ K₁' ∪ K₂')) k) x
      = hInterAB ▸ ((HomologicalComplex.homologyMap
          (pdRelComplexEnlargeInter X hA'mem hB'mem) k) x') :=
    PDSplitKC.pd_kc_castApply hInterAB.symm hAB (𝟙 X)
      (pdRelSub_mono (Set.union_subset (h₁.trans Set.subset_union_left)
        (h₂.trans Set.subset_union_right) : K₁ ∪ K₂ ⊆ K₁' ∪ K₂'))
      (Set.inter_subset_inter hA'mem hB'mem) k x
  have hc1 : (HomologicalComplex.homologyMap (pdRelComplexEnlarge W
        (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂')) k) x₁
      = hInterAB ▸ ((HomologicalComplex.homologyMap (pdToInterA X A' B') k) x₁) :=
    PDSplitKC.pd_kc_castApply hInterAB.symm rfl (𝟙 X)
      (pdRelSub_mono (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂'))
      (fun x hx => hx.1) k x₁
  have hc2 : (HomologicalComplex.homologyMap (pdRelComplexEnlarge W
        (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂')) k) x₂
      = hInterAB ▸ ((HomologicalComplex.homologyMap (pdToInterB X A' B') k) x₂) :=
    PDSplitKC.pd_kc_castApply hInterAB.symm rfl (𝟙 X)
      (pdRelSub_mono (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂'))
      (fun x hx => hx.2) k x₂
  rw [hc0, hc1, hc2]
  have htr : hInterAB ▸ ((HomologicalComplex.homologyMap
      (pdRelComplexEnlargeInter X hA'mem hB'mem) k) x')
      = hInterAB ▸ ((HomologicalComplex.homologyMap (pdToInterA X A' B') k) x₁
          - (HomologicalComplex.homologyMap (pdToInterB X A' B') k) x₂) :=
    congrArg (fun w => hInterAB ▸ w) hdecomp
  have hsub := PDSplitKC.pd_kc_cast_sub
    (P := fun i => (relComplex ℤ X i).homology k) hInterAB
    ((HomologicalComplex.homologyMap (pdToInterA X A' B') k) x₁)
    ((HomologicalComplex.homologyMap (pdToInterB X A' B') k) x₂)
  exact htr.trans hsub

end

end Work.Cohomology
