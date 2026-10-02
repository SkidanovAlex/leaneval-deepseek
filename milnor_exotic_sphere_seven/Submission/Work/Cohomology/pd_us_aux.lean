import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_goodD_incl
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.pd_goodD_rep
import Submission.Work.Cohomology.pd_hatcher_data
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.pd_hatcher_Xdata
import Submission.Work.Cohomology.pd_hatcher_cycles_inter
import Submission.Work.Cohomology.cap_mem_range_inclChains
import Submission.Work.Cohomology.cap_natural
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Cohomology.pd_ab_clean
import Submission.Work.Cohomology.pd_glue2
import Submission.Work.Cohomology.mem_range_inclChains_of_image
import Submission.Work.Cohomology.chainRetract_mem_range_inclChains
import Submission.Work.Cohomology.pd_relsub_aux
import Submission.Work.Cohomology.pd_localFundClass_of_cycle
import Submission.Work.Cohomology.pd_union_crux_zero_wk
import Submission.Work.Cohomology.cap_cochainDiff_mem_range
import Submission.Work.Cohomology.pdABInclRel_comp_pdABEnlarge
import Submission.Work.Cohomology.pdABdelta_natural
import Submission.Work.Cohomology.pdABCoh_quasiIso
import Submission.Work.Cohomology.pd_boundary_of_zero_class
import Submission.Work.Cohomology.pd_split_aux
import Submission.Work.Cohomology.pd_split_setup
import Submission.Work.Cohomology.pd_us_frame
import Submission.Work.Cohomology.pd_hatcher_inter4
import Submission.Work.Cohomology.pd_inter_cap_boundary
import Submission.Work.Cohomology.pd_us_cycles_eq_of_class_eq
import Submission.Work.Cohomology.pd_us_cap_cochainDiff
import Submission.Work.Cohomology.pd_us_ab_resolve
import Submission.Work.Cohomology.pd_us_f

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Auxiliary lemmas for `Work.Cohomology.pd_union_split`
-/

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Simplicial
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {M : TopCat}

variable {M : TopCat}

/-! ## Copies of the framing lemmas of `pd_glue3` (that module clashes with `pd_relsub_aux`) -/

/-- **The relative cycle associated with a chain whose boundary lies in the relative subcomplex.** -/
noncomputable def pd_us_relCycleOf {X : TopCat} (A : Set X) (n : ℕ)
    (x : (Work.Cohomology.singularChains ℤ X).X n)
    (hx : (Work.Cohomology.singularChains ℤ X).d n (n - 1) x
      ∈ LinearMap.range ((Work.Cohomology.inclChains X A).f (n - 1)).hom) :
    (Work.Cohomology.relChains X A).cycles n :=
  Work.Cohomology.cycleOf n
    (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)).f n) x) (by
    obtain ⟨g, hg⟩ := hx
    have hcomm := congrArg (fun (h : (Work.Cohomology.singularChains ℤ X).X n ⟶
        (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains X A)).X (n - 1)) =>
          (ModuleCat.Hom.hom h) x)
      ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)).comm n (n - 1))
    change (ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
      (Work.Cohomology.inclChains X A)).f n ≫
      (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains X A)).d n (n - 1))) x = 0
    rw [hcomm]
    change (ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
      (Work.Cohomology.inclChains X A)).f (n - 1)))
      ((ModuleCat.Hom.hom ((Work.Cohomology.singularChains ℤ X).d n (n - 1))) x) = 0
    rw [← hg]
    exact Work.Cohomology.cokernel_π_f_apply_eq_zero (n - 1) g)

/-- The underlying relative chain of `pd_us_relCycleOf` is the projection of the chain. -/
theorem pd_us_relCycleOf_iCycles {X : TopCat} (A : Set X) (n : ℕ)
    (x : (Work.Cohomology.singularChains ℤ X).X n)
    (hx : (Work.Cohomology.singularChains ℤ X).d n (n - 1) x
      ∈ LinearMap.range ((Work.Cohomology.inclChains X A).f (n - 1)).hom) :
    (Work.Cohomology.relChains X A).iCycles n (pd_us_relCycleOf A n x hx)
      = ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)).f n) x :=
  Work.Cohomology.iCycles_cycleOf n _ _

/-- **Setup, with the cycle.**  From a relative cohomology class of the pair
`(U∪V, (U∪V)∖(K₁∪K₂))` produce a representing relative cocycle `z` and a lift of its underlying
cochain along the difference map `C^*(X,A₁) ⊞ C^*(X,A₂) ⟶ C^*(X, A₁∩A₂)`. -/
theorem pd_split_setup2 {M : TopCat} [T2Space M] {k : ℕ}
    {U V : Set M} {K₁ K₂ : Set M}
    (x : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homology k) :
    ∃ (z : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).cycles k)
      (hz : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homologyπ k z = x)
      (φA : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)).X k)
      (φB : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂)).X k),
      ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z).1
        = φA.1 - φB.1 := by
  classical
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyπ (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k)).mp inferInstance x
  set φ : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k :=
    ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z).1 with hφdef
  have hφmem : φ ∈ Work.Cohomology.relKern ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) k :=
    ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z).2
  have hsplit : Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)
      = Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁
        ∩ Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂ :=
    Work.Cohomology.pdRelSub_union (U ∪ V : Set M) K₁ K₂
  have hφmem' : φ ∈ Work.Cohomology.relKern ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁
        ∩ Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) k := hsplit ▸ hφmem
  obtain ⟨φt, hφt⟩ := PDABClean.pdBiprodToInter_surj (TopCat.of (U ∪ V : Set M))
    (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)
    (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) k ⟨φ, hφmem'⟩
  set y₁ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)).X k :=
    (ModuleCat.Hom.hom ((biprod.fst : Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁) ⊞
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) ⟶
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)).f k)) φt with hy₁
  set y₂ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂)).X k :=
    (ModuleCat.Hom.hom ((biprod.snd : Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁) ⊞
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) ⟶
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂)).f k)) φt with hy₂
  refine ⟨z, hz, y₁, y₂, ?_⟩
  have htotal : (ModuleCat.Hom.hom ((biprod.inl : Work.Cohomology.relComplex ℤ
        (TopCat.of (U ∪ V : Set M)) (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁) ⟶
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁) ⊞
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂)).f k)) y₁
      + (ModuleCat.Hom.hom ((biprod.inr : Work.Cohomology.relComplex ℤ
        (TopCat.of (U ∪ V : Set M)) (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) ⟶
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁) ⊞
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂)).f k)) y₂ = φt :=
    PDABClean.pdBiprod_total (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) k φt
  have hcoe := PDABClean.pdBiprodToInter_coe (TopCat.of (U ∪ V : Set M))
    (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)
    (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) k y₁ y₂
  rw [htotal] at hcoe
  have h3 : ((show Work.Cohomology.relKern ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁
        ∩ Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) k from
      (ModuleCat.Hom.hom ((pdBiprodToInter (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂)).f k)) φt)).1 = φ := by
    rw [hφt]
  rw [← hφdef]
  exact h3.symm.trans hcoe

/-- The `singularCochainComplex` differential is the `cochainDiff`. -/
theorem pd_us_singularD_eq_cochainDiff (X : TopCat) (n : ℕ)
    (φ : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) n) :
    (ConcreteCategory.hom ((Work.Cohomology.singularCochainComplex ℤ X).d n (n+1))) φ
      = Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) φ := by
  simp only [Work.Cohomology.singularCochainComplex_eq, Work.Cohomology.SSetCochainComplex_d]
  exact Work.Cohomology.cochainDiffLM_apply ℤ (TopCat.toSSet.obj X) n φ


theorem pd_us_d_comp_d_singular (X : TopCat) (k : ℕ)
    (φ : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) k) :
    (ConcreteCategory.hom ((Work.Cohomology.singularCochainComplex ℤ X).d (k+1) (k+2)))
      ((ConcreteCategory.hom ((Work.Cohomology.singularCochainComplex ℤ X).d k (k+1))) φ) = 0 := by
  have h := HomologicalComplex.d_comp_d (Work.Cohomology.singularCochainComplex ℤ X) k (k+1) (k+2)
  have h2 := congrArg (fun (g : (Work.Cohomology.singularCochainComplex ℤ X).X k ⟶
      (Work.Cohomology.singularCochainComplex ℤ X).X (k+2)) =>
      (ConcreteCategory.hom g) φ) h
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply] at h2
  exact h2

theorem pd_us_XIsoOfEq_hom_eq_cast {C : ChainComplex (ModuleCat ℤ) ℕ} {a b : ℕ} (h : a = b)
    (x : C.X a) : (C.XIsoOfEq h).hom x = (h ▸ x : C.X b) := by
  cases h
  rfl

lemma pd_us_homologyπ_eq_zero_of_isBoundary {R : Type} [CommRing R]
    {K : ChainComplex (ModuleCat R) ℕ} {n : ℕ} (z : K.cycles n)
    (h : (K.iCycles n).hom z ∈ LinearMap.range (K.d (n+1) n).hom) :
    (HomologicalComplex.homologyπ K n).hom z = 0 := by
  obtain ⟨y, hy⟩ := h
  have hi : (ComplexShape.down ℕ).prev n = n + 1 :=
    ComplexShape.prev_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel (n+1) n from rfl)
  let y' : (K.sc n).X₁ := (K.XIsoOfEq hi).inv y
  have hf : (K.sc n).f y' = (K.iCycles n).hom z := by
    have h1 : (ConcreteCategory.hom ((K.XIsoOfEq hi).hom ≫ K.d (n+1) n)) y'
        = (ConcreteCategory.hom ((K.sc n).f)) y' :=
      congrArg (fun g => (ConcreteCategory.hom g) y')
        (HomologicalComplex.XIsoOfEq_hom_comp_d K hi n)
    rw [CategoryTheory.ConcreteCategory.comp_apply] at h1
    rw [← h1]
    rw [show (ConcreteCategory.hom (K.XIsoOfEq hi).hom) y' = y from Iso.inv_hom_id_apply _ _]
    exact hy
  have h2 : (K.sc n).toCycles y' = z := by
    have hinj : Function.Injective (K.iCycles n).hom :=
      (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    apply hinj
    have h3 := congrArg (fun (g : (K.sc n).X₁ ⟶ K.X n) => (ConcreteCategory.hom g) y')
      (ShortComplex.toCycles_i (K.sc n))
    have h4 : (ConcreteCategory.hom (K.iCycles n)) ((ConcreteCategory.hom (K.sc n).toCycles) y')
        = (ConcreteCategory.hom (K.sc n).f) y' := by
      exact h3
    rw [h4]
    exact hf
  have hz : (ConcreteCategory.hom ((K.sc n).homologyπ)) ((K.sc n).toCycles y') = 0 := by
    have h := CategoryTheory.ConcreteCategory.comp_apply (K.sc n).toCycles (K.sc n).homologyπ y'
    rw [ShortComplex.toCycles_comp_homologyπ] at h
    simpa using h.symm
  rw [← h2]
  exact hz

theorem pd_us_cast_irrel_symm {α : Sort*} {P : α → Sort*} {a b : α} (h : a = b) (h' : b = a)
    (x : P a) : (h ▸ x : P b) = (h' ▸ x : P b) := by
  rw [Subsingleton.elim h h'.symm]

theorem pd_us_neg_one_pow_sq (k : ℕ) : ((-1:ℤ)^k) * ((-1:ℤ)^k) = 1 := by
  rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **Main proof of `pd_union_split`.** -/
theorem pd_us_main {M : TopCat} [T2Space M] {N : ℕ}
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
  have hkm' : k + (m' + 1) = k + (m' + 1) := rfl
  let W : Set M := U ∪ V
  let X : TopCat := TopCat.of W
  have hW : IsOpen W := hU.union hV
  have hK₁W : K₁ ⊆ W := hK₁U.trans Set.subset_union_left
  have hK₂W : K₂ ⊆ W := hK₂V.trans Set.subset_union_right
  have hKW : K₁ ∪ K₂ ⊆ W := Set.union_subset hK₁W hK₂W
  have hKc : IsCompact (K₁ ∪ K₂) := hK₁c.union hK₂c
  -- ## the setup
  obtain ⟨z, hz, φA, φB, hdecomp⟩ :=
    pd_split_setup2 (U := U) (V := V) (K₁ := K₁) (K₂ := K₂) x
  have hz' : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).homologyπ k z = x := hz
  let φ : Cochain ℤ (TopCat.toSSet.obj X) k :=
    ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z).1
  have hφd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φ = 0 := by
    have h0 : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).d k (k + 1)
        ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z) = 0 := by
      have hcomp : (ConcreteCategory.hom ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k ≫
            (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).d k (k + 1))) z
          = (ConcreteCategory.hom ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).d k (k + 1)))
            ((ConcreteCategory.hom ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k)) z) :=
        CategoryTheory.ConcreteCategory.comp_apply _ _ z
      rw [← hcomp]
      exact congrArg (fun (g : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).cycles k ⟶
          (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).X (k + 1)) =>
          (ConcreteCategory.hom g) z)
        (HomologicalComplex.iCycles_d (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))) k (k + 1))
    have hcomm := congrArg
      (fun (g : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).X k ⟶
          (singularCochainComplex ℤ X).X (k+1)) =>
        (ConcreteCategory.hom g)
          ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z))
      ((relIncl ℤ X (pdRelSub W (K₁ ∪ K₂))).comm k (k+1))
    simp only [CategoryTheory.ConcreteCategory.comp_apply] at hcomm
    rw [h0, map_zero] at hcomm
    have hrel : (ConcreteCategory.hom ((relIncl ℤ X (pdRelSub W (K₁ ∪ K₂))).f k))
          ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z) = φ := rfl
    rw [hrel] at hcomm
    have hxd : (ConcreteCategory.hom ((singularCochainComplex ℤ X).d k (k+1))) φ
        = cochainDiff ℤ (TopCat.toSSet.obj X) φ := by
      simp only [singularCochainComplex_eq, SSetCochainComplex_d]
      exact cochainDiffLM_apply ℤ (TopCat.toSSet.obj X) k φ
    rw [hxd] at hcomm
    exact hcomm
  have hsubψ : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) (φA.1 - φB.1) = 0 := by
    rw [← hdecomp, ← hφd]
  have hsubD : (ConcreteCategory.hom ((singularCochainComplex ℤ X).d k (k+1)))
      (φA.1 - φB.1) = 0 := by
    rw [pd_us_singularD_eq_cochainDiff X k (φA.1 - φB.1)]
    exact hsubψ
  have hψd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1
      = cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φB.1 := by
    have h2 : (ConcreteCategory.hom ((singularCochainComplex ℤ X).d k (k+1))) φA.1
        - (ConcreteCategory.hom ((singularCochainComplex ℤ X).d k (k+1))) φB.1 = 0 :=
      (map_sub (ConcreteCategory.hom ((singularCochainComplex ℤ X).d k (k+1)))
        φA.1 φB.1).symm.trans hsubD
    have hD : (ConcreteCategory.hom ((singularCochainComplex ℤ X).d k (k+1))) φA.1
        = (ConcreteCategory.hom ((singularCochainComplex ℤ X).d k (k+1))) φB.1 :=
      sub_eq_zero.mp h2
    rw [← pd_us_singularD_eq_cochainDiff X k φA.1, ← pd_us_singularD_eq_cochainDiff X k φB.1]
    exact hD
  have hψAmem : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1
      ∈ relKern ℤ X (pdRelSub W K₁) (k + 1) := by
    rw [← pd_us_singularD_eq_cochainDiff X k φA.1]
    exact relKern_d_mem X (pdRelSub W K₁) k φA.1 φA.2
  have hψBmem : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1
      ∈ relKern ℤ X (pdRelSub W K₂) (k + 1) := by
    rw [hψd, ← pd_us_singularD_eq_cochainDiff X k φB.1]
    exact relKern_d_mem X (pdRelSub W K₂) k φB.1 φB.2
  -- ## the Hatcher decomposition of `c` in the ambient space
  obtain ⟨w, hwc, a, b, d, j, hα, ⟨a', ha'⟩, ⟨b', hb'⟩, ⟨d', hd'⟩, ⟨j', hj'⟩⟩ :=
    pd_hatcher_data c hU hV hK₁c hK₂c hK₁U hK₂V
  -- ## the decomposition in `U ∪ V`
  obtain ⟨α₁X, α₂X, α₃X, ξX, γX, h1incl, h2incl, h3incl, hξdef, ⟨a'', ha''⟩, ⟨bX, hbX⟩,
    ⟨dX, hdX⟩, hbd1, hbd2, hDξ, hlocX, hγXi⟩ :=
    pd_hatcher_Xdata hU hV hK₁c hK₂c hK₁U hK₂V w a b d j hα ⟨j', hj'⟩ ⟨a', ha'⟩ ⟨b', hb'⟩ ⟨d', hd'⟩ hwc
  have hξZ : (relChains X (pdRelSub W (K₁ ∪ K₂))).iCycles (k + (m' + 1)) γX
      = ((cokernel.π (inclChains X (pdRelSub W (K₁ ∪ K₂)))).f (k + (m' + 1))).hom
          (α₁X + α₂X + α₃X) := by
    rw [← hξdef]
    exact hγXi
  have hγZ : (relChains X (pdRelSub W (K₁ ∪ K₂))).homologyπ (k + (m' + 1)) γX
      = (rfl : k + (m' + 1) = k + (m' + 1)) ▸
          localFundClass (k + (m' + 1)) c W hW (K₁ ∪ K₂) hKW hKc := hlocX
  have hgoodD : goodD (k + (m' + 1)) c W hW (K₁ ∪ K₂) hKW hKc k (m' + 1) rfl
      ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).homologyπ k z)
      = (singularChains ℤ X).homologyπ (m' + 1)
          (relCapPairZ X (pdRelSub W (K₁ ∪ K₂)) k (m' + 1) z γX) :=
    goodD_homologyπ c W hW (K₁ ∪ K₂) hKW hKc k (m' + 1) rfl z γX hγZ
      (α₁X + α₂X + α₃X) hξZ
  have hzero : (singularChains ℤ X).homologyπ (m' + 1)
      (relCapPairZ X (pdRelSub W (K₁ ∪ K₂)) k (m' + 1) z γX) = 0 := by
    rw [← hgoodD, hz']
    exact hx
  obtain ⟨β, hβ⟩ := pd_boundary_of_zero_class (singularChains ℤ X) (m' + 1)
    (relCapPairZ X (pdRelSub W (K₁ ∪ K₂)) k (m' + 1) z γX) hzero
  have hcapβ : (singularChains ℤ X).d (m' + 2) (m' + 1) β
      = cap ℤ (TopCat.toSSet.obj X) φ (m' + 1) (α₁X + α₂X + α₃X) := by
    rw [hβ, relCapPairZ_iCycles_apply (X := X) (A := pdRelSub W (K₁ ∪ K₂)) z γX hξZ]
  -- ## the crux
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
  have hL' : (singularChains ℤ X).d (k + (m' + 1)) (k + m') α₁X
      ∈ LinearMap.range (((inclChains X (pdTr W K₂)ᶜ).f (k + m')).hom) := by
    have h := hbd1
    rw [show (k + (m' + 1)) - 1 = k + m' by omega] at h
    rw [← pdRelSub_eq_compl_pdTr W K₂]
    exact h
  have hK' : (singularChains ℤ X).d (k + (m' + 1)) (k + m') α₃X
      ∈ LinearMap.range (((inclChains X (pdTr W K₁)ᶜ).f (k + m')).hom) := by
    have h := hbd2
    rw [show (k + (m' + 1)) - 1 = k + m' by omega] at h
    rw [← pdRelSub_eq_compl_pdTr W K₁]
    exact h
  have hd123 : (singularChains ℤ X).d (k + (m' + 1)) (k + m') (α₁X + α₂X + α₃X)
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
    hdecomp hα₁' hα₂' hα₃' hL' hK' hd123 hφd ⟨β, hcapβ⟩
  have hγmem' : γ ∈ LinearMap.range (((inclChains X (pdTr W (U ∩ V))).f (m' + 1)).hom) := by
    rw [pdTr_inter W U V]; exact hγmem
  -- ## `ψ` as a cocycle of the `A+B` complex
  set ψ : Cochain ℤ (TopCat.toSSet.obj X) (k+1) :=
    cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1 with hψdef
  have hψdd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k+1) ψ = 0 := by
    rw [hψdef, ← pd_us_singularD_eq_cochainDiff X (k+1)
        (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA.1),
      ← pd_us_singularD_eq_cochainDiff X k φA.1]
    exact pd_us_d_comp_d_singular X k φA.1
  have hψAre : ψ ∈ relKern ℤ X (pdRelSub W K₁) (k+1) := by rw [hψdef]; exact hψAmem
  have hψBre : ψ ∈ relKern ℤ X (pdRelSub W K₂) (k+1) := by rw [hψdef]; exact hψBmem
  have hψmem : ψ ∈ pdABKern X (pdRelSub W K₁) (pdRelSub W K₂) (k+1) :=
    ⟨hψAre, hψBre⟩
  have hA₁op : IsOpen (pdRelSub W K₁) := by
    rw [pdRelSub_eq_compl_pdTr]
    exact (hK₁c.isClosed.preimage continuous_subtype_val).isOpen_compl
  have hA₂op : IsOpen (pdRelSub W K₂) := by
    rw [pdRelSub_eq_compl_pdTr]
    exact (hK₂c.isClosed.preimage continuous_subtype_val).isOpen_compl
  obtain ⟨u, χ, hχmem, hχd⟩ := pd_us_ab_resolve (X := X) (A := pdRelSub W K₁)
    (B := pdRelSub W K₂) hA₁op hA₂op (n := k) ψ hψmem hψdd
  set ψu : Cochain ℤ (TopCat.toSSet.obj X) (k+1) :=
    (show Cochain ℤ (TopCat.toSSet.obj X) (k+1) from
      ((relComplex ℤ X (pdRelSub W K₁ ∪ pdRelSub W K₂)).iCycles (k+1) u).1) with hψudef
  have hχd' : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χ = ψu - ψ := by
    rw [hψudef]; exact hχd
  have hχK : χ ∈ relKern ℤ X (pdRelSub W K₁) k := hχmem.1
  have hχL : χ ∈ relKern ℤ X (pdRelSub W K₂) k := hχmem.2
  have hχK' : χ ∈ relKern ℤ X ((pdTr W K₁)ᶜ) k := by
    rw [← pdRelSub_eq_compl_pdTr W K₁]; exact hχK
  have hχL' : χ ∈ relKern ℤ X ((pdTr W K₂)ᶜ) k := by
    rw [← pdRelSub_eq_compl_pdTr W K₂]; exact hχL
  -- ## the cap product of `d χ` with the middle piece
  have hdα₂ : ∃ (g e f : (singularChains ℤ X).X (k + m')),
      (singularChains ℤ X).d (k + (m' + 1)) (k + m') α₂X = g - e - f ∧
      g ∈ LinearMap.range ((inclChains X ((pdTr W K₁) ∪ (pdTr W K₂))ᶜ).f (k + m')).hom ∧
      e ∈ LinearMap.range ((inclChains X (pdTr W K₂)ᶜ).f (k + m')).hom ∧
      f ∈ LinearMap.range ((inclChains X (pdTr W K₁)ᶜ).f (k + m')).hom := by
    have hg : (singularChains ℤ X).d (k + (m' + 1)) (k + m') ξX
        ∈ LinearMap.range ((inclChains X ((pdTr W K₁) ∪ (pdTr W K₂))ᶜ).f (k + m')).hom := by
      have h := hDξ
      rw [show (k + (m' + 1)) - 1 = k + m' by omega] at h
      rw [pdRelSub_eq_compl_pdTr, ← pdTr_union] at h
      exact h
    refine ⟨(singularChains ℤ X).d (k + (m' + 1)) (k + m') ξX,
      (singularChains ℤ X).d (k + (m' + 1)) (k + m') α₁X,
      (singularChains ℤ X).d (k + (m' + 1)) (k + m') α₃X, ?_, hg, hL', hK'⟩
    rw [hξdef, map_add, map_add]; abel
  have hcapχ := pd_us_cap_cochainDiff (X := X) (K := pdTr W K₁) (L := pdTr W K₂)
    (k := k) (mj := m') χ α₂X hχK' hχL' hdα₂
  -- solve for `d (cap χ α₂)`
  have hdχcap : (singularChains ℤ X).d (m'+1) m'
      (cap ℤ (TopCat.toSSet.obj X) χ (m'+1) α₂X)
      = (-1:ℤ)^(k+1) • cap ℤ (TopCat.toSSet.obj X)
          (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χ) m'
          ((capIdx k m') ▸ α₂X) := by
    have h := hcapχ
    rw [show -((-1:ℤ)^k) = (-1:ℤ)^(k+1) by rw [pow_succ]; ring] at h
    set_option backward.isDefEq.respectTransparency false in
    rw [h, ← mul_smul, pd_us_neg_one_pow_sq (k+1), one_smul]
  -- the decomposition `ψ = ψu - d χ`
  have hψdecomp : ψ = ψu - cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χ := by
    rw [hχd']; abel
  have hcapψ : cap ℤ (TopCat.toSSet.obj X) ψ m' ((capIdx k m') ▸ α₂X)
      = cap ℤ (TopCat.toSSet.obj X) ψu m' ((capIdx k m') ▸ α₂X)
        - cap ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χ) m'
            ((capIdx k m') ▸ α₂X) := by
    rw [hψdecomp, cap_sub_apply]
  -- ## `cap ψu` bounds a chain supported in `U ∩ V`
  have hB : ∃ γ' ∈ LinearMap.range (((inclChains X (pdTr W (U ∩ V))).f (m'+1)).hom),
      (singularChains ℤ X).d (m'+1) m' γ'
        = (-1:ℤ)^(k+1) • cap ℤ (TopCat.toSSet.obj X) ψu m'
            ((capIdx k m') ▸ α₂X) := by
    let cχ : (singularChains ℤ X).X (m'+1) := cap ℤ (TopCat.toSSet.obj X) χ (m'+1) α₂X
    have hcapmem : cχ ∈ LinearMap.range (((inclChains X (pdTr W (U ∩ V))).f (m'+1)).hom) :=
      cap_mem_range_inclChains (M := X) (pdTr W (U ∩ V)) k (m'+1) χ ⟨bX, hbX⟩
    refine ⟨γ + cχ, ?_, ?_⟩
    · exact add_mem hγmem' hcapmem
    · have hstep : (singularChains ℤ X).d (m'+1) m' (γ + cχ)
          = (-1:ℤ)^(k+1) • cap ℤ (TopCat.toSSet.obj X) ψ m' ((capIdx k m') ▸ α₂X)
            + (-1:ℤ)^(k+1) • cap ℤ (TopCat.toSSet.obj X)
                (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χ) m'
                ((capIdx k m') ▸ α₂X) := by
        set_option backward.isDefEq.respectTransparency false in
        rw [map_add, hγd]
        set_option backward.isDefEq.respectTransparency false in
        rw [show (singularChains ℤ X).d (m'+1) m' cχ
            = (-1:ℤ)^(k+1) • cap ℤ (TopCat.toSSet.obj X)
                (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χ) m'
                ((capIdx k m') ▸ α₂X) from hdχcap]
      have hcapψ2 : cap ℤ (TopCat.toSSet.obj X) ψ m' ((capIdx k m') ▸ α₂X)
          + cap ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χ) m'
              ((capIdx k m') ▸ α₂X)
          = cap ℤ (TopCat.toSSet.obj X) ψu m' ((capIdx k m') ▸ α₂X) := by
        rw [hcapψ]; abel
      have hcc : (-1:ℤ)^(k+1) • (cap ℤ (TopCat.toSSet.obj X) ψ m' ((capIdx k m') ▸ α₂X)
            + cap ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χ) m'
                ((capIdx k m') ▸ α₂X))
          = (-1:ℤ)^(k+1) • cap ℤ (TopCat.toSSet.obj X) ψu m'
              ((capIdx k m') ▸ α₂X) :=
        congrArg (fun z => (-1:ℤ)^(k+1) • z) hcapψ2
      exact hstep.trans ((zsmul_add
          (cap ℤ (TopCat.toSSet.obj X) ψ m' ((capIdx k m') ▸ α₂X))
          (cap ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χ) m'
            ((capIdx k m') ▸ α₂X)) ((-1:ℤ)^(k+1))).symm.trans hcc)
  -- ## the middle Hatcher piece in `U ∩ V`
  have hUVm : U ∩ V ⊆ (U ∪ V : Set M) :=
    Set.inter_subset_left.trans Set.subset_union_left
  obtain ⟨bI, γI, hbI, hγIi, hγIloc⟩ := pd_hatcher_inter4 (M := M) hU hV hI hK₁c hK₂c hK₁U hK₂V
    w a b d j hα ⟨j', hj'⟩ ⟨a', ha'⟩ ⟨b', hb'⟩ ⟨d', hd'⟩ hwc
  -- ## the restriction of `u` to `U ∩ V`
  have hAB : ∀ x ∈ pdRelSub (U ∩ V) (K₁ ∩ K₂),
      (pdIncl W (U ∩ V) hUVm) x ∈ pdRelSub W K₁ ∪ pdRelSub W K₂ := by
    intro x hx
    show (x : M) ∉ K₁ ∨ (x : M) ∉ K₂
    exact not_and_or.mp hx
  set ψz : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) (k+1) :=
    (relMapLM (X₁ := TopCat.of (U ∩ V : Set M)) (X₂ := X) ℤ (pdRelSub (U ∩ V) (K₁ ∩ K₂))
      (pdRelSub W K₁ ∪ pdRelSub W K₂)
      (pdIncl W (U ∩ V) hUVm) hAB (k+1)
      ((relComplex ℤ X (pdRelSub W K₁ ∪ pdRelSub W K₂)).iCycles (k+1) u)).1 with hψzdef
  have hψzmem : ψz ∈ relKern ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) (K₁ ∩ K₂)) (k+1) := by
    rw [hψzdef]
    exact (relMapLM (X₁ := TopCat.of (U ∩ V : Set M)) (X₂ := X) ℤ (pdRelSub (U ∩ V) (K₁ ∩ K₂))
      (pdRelSub W K₁ ∪ pdRelSub W K₂)
      (pdIncl W (U ∩ V) hUVm) hAB (k+1)
      ((relComplex ℤ X (pdRelSub W K₁ ∪ pdRelSub W K₂)).iCycles (k+1) u)).2
  have hpull : ψz = ψu.comp ((SSet.chainComplexMap (TopCat.toSSet.map (pdIncl W (U ∩ V) hUVm))
      (ModuleCat.of ℤ ℤ)).f (k+1)).hom := by
    set_option backward.isDefEq.respectTransparency false in
    rw [hψzdef, relMapLM_coe, hψudef, capRel_dualChainMap_f]
    simp only [dualComplexMapComp, ModuleCat.hom_ofHom, LinearMap.dualMap_apply]
    rfl
  -- ## the degree transport
  have hN : k + (m' + 1) = (k + 1) + m' := by omega
  have hkmZ : (k + 1) + m' = k + (m' + 1) := by omega
  set bIs : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).X ((k+1)+m') :=
    ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).XIsoOfEq hN).hom bI with hbIsdef
  obtain ⟨γIs, hγIsi⟩ := pd_cyclesOfEq hN γI
  have hξ : (relChains (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) (K₁ ∩ K₂))).iCycles ((k+1)+m') γIs
      = ((cokernel.π (inclChains (TopCat.of (U ∩ V : Set M))
          (pdRelSub (U ∩ V) (K₁ ∩ K₂)))).f ((k+1)+m')).hom bIs := by
    rw [hγIsi, hγIi]
    have hnat := congrArg
      (fun (g : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).X (k + (m' + 1)) ⟶
          (relChains (TopCat.of (U ∩ V : Set M))
            (pdRelSub (U ∩ V) (K₁ ∩ K₂))).X ((k+1)+m')) =>
        (ConcreteCategory.hom g) bI)
      (HomologicalComplex.XIsoOfEq_hom_naturality
        (cokernel.π (inclChains (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) (K₁ ∩ K₂)))) hN)
    simp only [CategoryTheory.ConcreteCategory.comp_apply] at hnat
    exact hnat
  have hγIg : (relChains (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) (K₁ ∩ K₂))).homologyπ ((k+1)+m') γIs
      = hkmZ ▸ localFundClass (k + (m' + 1)) c (U ∩ V : Set M) hI (K₁ ∩ K₂)
          (fun x hx => ⟨hK₁U hx.1, hK₂V hx.2⟩) (IsCompact.inter hK₁c hK₂c) := by
    rw [pd_homologyπ_cyclesOfEq hN γI γIs hγIsi, hγIloc]
  -- ## the compatibility of the two inclusions at degree `(k+1)+m'`
  have hbI' : ((singularChains ℤ M).XIsoOfEq hN).hom
        ((inclChains M (U ∩ V : Set M)).f (k + (m' + 1)) bI)
      = (inclChains M (U ∩ V : Set M)).f ((k+1)+m') bIs := by
    have hnat2 := congrArg
      (fun (g : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).X (k + (m' + 1)) ⟶
          (singularChains ℤ M).X ((k+1)+m')) => (ConcreteCategory.hom g) bI)
      (HomologicalComplex.XIsoOfEq_hom_naturality (inclChains M (U ∩ V : Set M)) hN)
    simp only [CategoryTheory.ConcreteCategory.comp_apply] at hnat2
    exact hnat2
  have hbcomp : ((singularChains ℤ M).XIsoOfEq hN).hom
        ((inclChains M (U ∪ V : Set M)).f (k + (m' + 1)) α₂X)
      = ((singularChains ℤ M).XIsoOfEq hN).hom
        ((inclChains M (U ∩ V : Set M)).f (k + (m' + 1)) bI) := by
    rw [h2incl, hbI]
  have hcapX : ((singularChains ℤ M).XIsoOfEq hN).hom
        ((inclChains M (U ∪ V : Set M)).f (k + (m' + 1)) α₂X)
      = (inclChains M (U ∪ V : Set M)).f ((k+1)+m') ((capIdx k m') ▸ α₂X) := by
    have hnat1 := congrArg
      (fun (g : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X (k + (m' + 1)) ⟶
          (singularChains ℤ M).X ((k+1)+m')) => (ConcreteCategory.hom g) α₂X)
      (HomologicalComplex.XIsoOfEq_hom_naturality (inclChains M (U ∪ V : Set M)) hN)
    simp only [CategoryTheory.ConcreteCategory.comp_apply] at hnat1
    rw [hnat1]
    congr 1
    rw [show ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).XIsoOfEq hN).hom α₂X
        = ((capIdx k m') ▸ α₂X : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X ((k+1)+m')) from
        pd_us_XIsoOfEq_hom_eq_cast hN α₂X]
  -- ## the connecting chain in `U ∩ V`
  obtain ⟨δ, hδ⟩ := pd_inter_cap_boundary (M := M) hUVm ((-1:ℤ)^(k+1)) ψu
    bIs ((capIdx k m') ▸ α₂X) (hcapX.symm.trans (hbcomp.trans hbI')) hB
  -- ## the duality class of the restricted cycle
  set φAB := relComplexMap ℤ (pdRelSub (U ∩ V) (K₁ ∩ K₂))
    (pdRelSub W K₁ ∪ pdRelSub W K₂) (pdIncl W (U ∩ V) hUVm) hAB with hφABdef
  set zI : (relComplex ℤ (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V) (K₁ ∩ K₂))).cycles (k+1) :=
    HomologicalComplex.cyclesMap φAB (k+1) u with hzIdef
  have hzIcoch : ((relComplex ℤ (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V) (K₁ ∩ K₂))).iCycles (k+1) zI).1 = ψz := by
    rw [hzIdef, Crux.cruxCyclesMap_i_apply' φAB (k+1) u, hψzdef, hφABdef, relComplexMap_f]
    rfl
  have hgoodD2 : goodD (k + (m' + 1)) c (U ∩ V : Set M) hI (K₁ ∩ K₂)
      (fun x hx => ⟨hK₁U hx.1, hK₂V hx.2⟩) (IsCompact.inter hK₁c hK₂c) (k+1) m' hkmZ
      ((relComplex ℤ (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V) (K₁ ∩ K₂))).homologyπ (k+1) zI)
      = (singularChains ℤ (TopCat.of (U ∩ V : Set M))).homologyπ m'
          (relCapPairZ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) (K₁ ∩ K₂)) (k+1) m' zI γIs) :=
    goodD_homologyπ c (U ∩ V : Set M) hI (K₁ ∩ K₂)
      (fun x hx => ⟨hK₁U hx.1, hK₂V hx.2⟩) (IsCompact.inter hK₁c hK₂c) (k+1) m' hkmZ zI γIs
      hγIg bIs hξ
  have hzero2 : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).homologyπ m'
      (relCapPairZ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) (K₁ ∩ K₂)) (k+1) m' zI γIs) = 0 := by
    have hchain : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).iCycles m'
        (relCapPairZ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) (K₁ ∩ K₂)) (k+1) m' zI γIs)
        = cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) ψz m' bIs := by
      rw [relCapPairZ_iCycles_apply (X := TopCat.of (U ∩ V : Set M))
        (A := pdRelSub (U ∩ V) (K₁ ∩ K₂)) zI γIs hξ, hzIcoch]
    have hδ' : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (m'+1) m' δ
        = (-1:ℤ)^(k+1) • cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M))) ψz m' bIs := by
      rw [hδ, ← hpull]
    refine pd_us_homologyπ_eq_zero_of_isBoundary _ ⟨(-1:ℤ)^(k+1) • δ, ?_⟩
    have hms : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (m'+1) m' ((-1:ℤ)^(k+1) • δ)
        = (-1:ℤ)^(k+1) • (singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (m'+1) m' δ :=
      map_zsmul (ModuleCat.Hom.hom ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (m'+1) m')) _ _
    rw [hms, hchain, hδ']
    set_option backward.isDefEq.respectTransparency false in
    rw [← mul_smul, pd_us_neg_one_pow_sq (k+1), one_smul]
  -- ================= Step 8: kill on `U ∩ V` =================
  have hgoodD2z : goodD (k + (m' + 1)) c (U ∩ V : Set M) hI (K₁ ∩ K₂)
      (fun x hx => ⟨hK₁U hx.1, hK₂V hx.2⟩) (IsCompact.inter hK₁c hK₂c) (k + 1) m' hkmZ
      ((relComplex ℤ (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V) (K₁ ∩ K₂))).homologyπ (k + 1) zI) = 0 := by
    rw [hgoodD2, hzero2]
  obtain ⟨L'', hK₀L'', hL''I, hL''c, hL''zero⟩ :=
    hII.kill (k + 1) m' hkmZ (K₁ ∩ K₂) (fun x hx => ⟨hK₁U hx.1, hK₂V hx.2⟩)
      (IsCompact.inter hK₁c hK₂c) ((relComplex ℤ (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V) (K₁ ∩ K₂))).homologyπ (k + 1) zI) hgoodD2z
  have hkill0 : ∃ (L'' : Set M) (h₁ : K₁ ∩ K₂ ⊆ L'') (h₂ : L'' ⊆ U ∩ V) (h₃ : IsCompact L''),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∩ V) h₁) (k + 1)).hom
        ((HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (U ∩ V) (K₁ ∩ K₂))
          (pdRelSub (U ∪ V : Set M) K₁ ∪ pdRelSub (U ∪ V : Set M) K₂)
          (pdIncl (U ∪ V : Set M) (U ∩ V) hUVm) (fun x hx => not_and_or.mp hx)) (k + 1)).hom
        ((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K₁ ∪ pdRelSub (U ∪ V : Set M) K₂)) (k + 1)).hom u)) = 0 := by
    refine ⟨L'', hK₀L'', hL''I, hL''c, ?_⟩
    have h2' : (HomologicalComplex.homologyMap φAB (k + 1)).hom
        ((HomologicalComplex.homologyπ (relComplex ℤ X (pdRelSub W K₁ ∪ pdRelSub W K₂))
          (k + 1)).hom u)
        = (relComplex ℤ (TopCat.of (U ∩ V : Set M))
            (pdRelSub (U ∩ V) (K₁ ∩ K₂))).homologyπ (k + 1) zI := by
      rw [hzIdef]
      have hnat := congrArg (fun (g : (relComplex ℤ X (pdRelSub W K₁ ∪ pdRelSub W K₂)).cycles
            (k + 1) ⟶ HomologicalComplex.homology (relComplex ℤ (TopCat.of (U ∩ V : Set M))
              (pdRelSub (U ∩ V) (K₁ ∩ K₂))) (k + 1)) => g.hom u)
        (HomologicalComplex.homologyπ_naturality (φ := φAB) (i := k + 1))
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hnat
    rw [h2']
    exact hL''zero
  exact pd_us_finish (hI := hI) (hW := hW) (hUVm := hUVm) (hK₁U := hK₁U) (hK₂V := hK₂V)
    (hK₁c := hK₁c) (hK₂c := hK₂c) (k := k) (x := x) (z := z) (hz := hz') (u := u)
    (φA := φA) (φB := φB) (hdecomp := hdecomp) (hψB := hψd.symm.trans hψdef) (χ := χ)
    (hχmem := hχmem) (hχd := hχd') (hkill0 := hkill0)

end

end Work.Cohomology
