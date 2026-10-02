import Mathlib
import Submission.Work.Whitney.tcmModelMul
import Submission.Work.Whitney.tcmRelCup_unit_right
import Submission.Work.Whitney.tcmF_inv_general
import Submission.Work.Whitney.tcmSuccOneAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The `q = 0` case of the point model product formula

The target `Work.Whitney.tcmModelMul_point_zero` is the case `q = 0` of the model product formula
over a one-point base, *with the Koszul sign* `(-1)^{p·0} = 1`:

  `tcmRelCup (pr₁^* Mpun p) (pr₂^* Mpun 0) = tcmF^* (Mpun (p+0))`.

It is the **right unit law** of the model product: the rank-`0` class `Mpun 0 Y` sits over the
*empty* closed set `tcmC Y p 0 = ∅` (the second fibre coordinate lives in `ℝ^0`, a subsingleton), so
`tcmC Y p 0 ⊆ tcmA Y p 0` and cupping with it is the identity
(`Work.Whitney.tcmRelCup_unit_right`).

The proof follows the pattern of the `n = 0` case of the rank-one formula
(`Work.Whitney.tcmProd_rankOne_zero`): applying the inverse `Φ := (Fib.tcmF_inv Y p 0)^*` of the
coordinate identification `tcmF` turns the claim into `Mpun p Y = Mpun p Y`, because

* `Φ` factors through the `A`-pair (`relCohMap_compA`), where the cup is `pr₁^* Mpun p` by the unit
  law (the absolute image of `pr₂^* Mpun 0` is the unit class, `Work.Whitney.relToAbs_Mpun_zero` and
  `Work.Thom.CohMap_oneH`),
* `tcmPr1 ∘ Fib.tcmF_inv = id` (the `ℝ^0` factor of `tcmSumLin p 0` is trivial, so the first fibre
  coordinate is untouched), whence `Φ_A (pr₁^* Mpun p) = Mpun p`,
* `Fib.tcmF_inv` is a two-sided inverse of `tcmF` on the relative groups.

The Koszul sign `(-1)^{p·0}` is literally `1`; the proof begins by normalising the goal with
`simp only [Nat.add_zero, Nat.mul_zero]`, which rewrites the `p + 0`'s of the statement
(`Punct Y (p+0)`, `Mpun (p+0)`, `ℤ (p+0)`) into `p`'s so that all the intermediate terms live in a
single degree.
-/

namespace Work.Whitney

open Work.Thom

noncomputable section

/-- In the coordinate identification `ℝ^p × ℝ^0 ≅ ℝ^{p+0}` the first fibre coordinate is unchanged:
the `ℝ^0` component is a subsingleton and the shuffle keeps the order. -/
theorem tcmSumLin_symm_zero_fst (p : ℕ) (u : EuclideanSpace ℝ (Fin (p+0))) :
    ((tcmSumLin p 0).symm u).1 = u := by
  have h : (tcmSumLin p 0).symm
      = EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := 0) := by
    simp [tcmSumLin]
  rw [h]
  ext j
  rw [Work.Thom.finAddEquivProd_fst]
  rw [finSumFinEquiv_apply_left]
  simp

/-- The pair condition of the inverse coordinate identification `Fib.tcmF_inv Y p 0` on the first
closed set: the punctured part of `Y × ℝ^{p+0}` is carried into `tcmA Y p 0`. -/
theorem tcmF_inv_mem_tcmA_zero (Y : Type) [TopologicalSpace Y] (p : ℕ) :
    ∀ x ∈ Punct Y p, Fib.tcmF_inv Y p 0 x ∈ tcmA Y p 0 := by
  intro x hx
  simp only [Fib.tcmF_inv_apply, tcmA, Set.mem_ofPred_eq] at hx ⊢
  rwa [tcmSumLin_symm_zero_fst p x.2]

/-- The pair condition of the inverse coordinate identification on the union `A ∪ C`. -/
theorem tcmF_inv_mem_union_zero (Y : Type) [TopologicalSpace Y] (p : ℕ) :
    ∀ x ∈ Punct Y p, Fib.tcmF_inv Y p 0 x ∈ tcmA Y p 0 ∪ tcmC Y p 0 :=
  fun x hx => Or.inl (tcmF_inv_mem_tcmA_zero Y p x hx)

/-- **`tcmPr1` is a left inverse of the inverse coordinate identification**: on `Y × ℝ^{p+0}`
the projection onto the first summand undoes `Fib.tcmF_inv Y p 0`. -/
theorem tcmPr1_comp_tcmF_inv_zero (Y : Type) [TopologicalSpace Y] (p : ℕ) :
    (tcmPr1 Y p 0).comp (Fib.tcmF_inv Y p 0)
      = ContinuousMap.id (Y × EuclideanSpace ℝ (Fin (p+0))) := by
  apply ContinuousMap.ext
  intro y
  exact Prod.ext rfl (tcmSumLin_symm_zero_fst p y.2)

/-- The pair condition of `tcmPr1 ∘ Fib.tcmF_inv Y p 0`, in the coordinate identification. -/
theorem tcmPr1_comp_tcmF_inv_mem_punct_zero (Y : Type) [TopologicalSpace Y] (p : ℕ) :
    ∀ x ∈ Punct Y p, (tcmPr1 Y p 0).comp (Fib.tcmF_inv Y p 0) x ∈ Punct Y p :=
  fun x hx => hx

/-- **The two composite transports of the coordinate identification are the identity**:
`(tcmF_inv)^* ∘ (tcmF)^* = id` on `H^p(tcmX Y p 0, A ∪ C)`. -/
theorem tcmF_inv_tcmF_transport_zero (Y : Type) [TopologicalSpace Y] (p : ℕ)
    (x : RelCoh ℤ p (tcmX Y p 0) (tcmA Y p 0 ∪ tcmC Y p 0)) :
    (relCohMap (tcmF Y p 0) (tcmA Y p 0 ∪ tcmC Y p 0) (Punct Y p)
        (tcmF_mem Y p 0) ℤ p).hom
      ((relCohMap (Fib.tcmF_inv Y p 0) (Punct Y p) (tcmA Y p 0 ∪ tcmC Y p 0)
        (tcmF_inv_mem_union_zero Y p) ℤ p).hom x) = x := by
  have hgf : ∀ z ∈ (tcmA Y p 0 ∪ tcmC Y p 0 : Set (tcmX Y p 0)),
      Fib.tcmF_inv Y p 0 (tcmF Y p 0 z) ∈ (tcmA Y p 0 ∪ tcmC Y p 0 : Set (tcmX Y p 0)) := by
    intro z hz
    rw [Fib.tcmF_inv_tcmF Y p 0 z]
    exact hz
  erw [relCohMap_compA_apply (tcmA Y p 0 ∪ tcmC Y p 0) (Punct Y p)
      (tcmA Y p 0 ∪ tcmC Y p 0) (tcmF Y p 0) (Fib.tcmF_inv Y p 0) (tcmF_mem Y p 0)
      (tcmF_inv_mem_union_zero Y p) hgf ℤ p x]
  have heq : (Fib.tcmF_inv Y p 0).comp (tcmF Y p 0) = ContinuousMap.id (tcmX Y p 0) :=
    ContinuousMap.ext (fun z => Fib.tcmF_inv_tcmF Y p 0 z)
  have hid : ∀ z ∈ (tcmA Y p 0 ∪ tcmC Y p 0 : Set (tcmX Y p 0)),
      (ContinuousMap.id (tcmX Y p 0)) z ∈ (tcmA Y p 0 ∪ tcmC Y p 0 : Set (tcmX Y p 0)) :=
    fun z hz => hz
  rw [relCohMap_congrA (tcmA Y p 0 ∪ tcmC Y p 0) (tcmA Y p 0 ∪ tcmC Y p 0)
      heq hgf hid ℤ p]
  rw [relCohMap_idA (tcmA Y p 0 ∪ tcmC Y p 0) ℤ p]
  simp only [ModuleCat.hom_id, LinearMap.id_apply]

/-- **The other composite is the identity**: `(tcmF)^* ∘ (tcmF_inv)^* = id` on
`H^p(Y × ℝ^{p+0}, Punct Y p)`. -/
theorem tcmF_tcmF_inv_transport_zero (Y : Type) [TopologicalSpace Y] (p : ℕ)
    (y : RelCoh ℤ p (Y × EuclideanSpace ℝ (Fin (p+0))) (Punct Y p)) :
    (relCohMap (Fib.tcmF_inv Y p 0) (Punct Y p) (tcmA Y p 0 ∪ tcmC Y p 0)
        (tcmF_inv_mem_union_zero Y p) ℤ p).hom
      ((relCohMap (tcmF Y p 0) (tcmA Y p 0 ∪ tcmC Y p 0) (Punct Y p)
        (tcmF_mem Y p 0) ℤ p).hom y) = y := by
  have hgf : ∀ x ∈ (Punct Y p : Set (Y × EuclideanSpace ℝ (Fin (p+0)))),
      tcmF Y p 0 (Fib.tcmF_inv Y p 0 x) ∈
        (Punct Y p : Set (Y × EuclideanSpace ℝ (Fin (p+0)))) := by
    intro x hx
    rw [Fib.tcmF_tcmF_inv Y p 0 x]
    exact hx
  erw [relCohMap_compA_apply (Punct Y p) (tcmA Y p 0 ∪ tcmC Y p 0) (Punct Y p)
      (Fib.tcmF_inv Y p 0) (tcmF Y p 0) (tcmF_inv_mem_union_zero Y p) (tcmF_mem Y p 0) hgf ℤ p y]
  have heq : (tcmF Y p 0).comp (Fib.tcmF_inv Y p 0)
      = ContinuousMap.id (Y × EuclideanSpace ℝ (Fin (p+0))) :=
    ContinuousMap.ext (fun z => Fib.tcmF_tcmF_inv Y p 0 z)
  have hid : ∀ x ∈ (Punct Y p : Set (Y × EuclideanSpace ℝ (Fin (p+0)))),
      (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin (p+0)))) x
        ∈ (Punct Y p : Set (Y × EuclideanSpace ℝ (Fin (p+0)))) := fun x hx => hx
  rw [relCohMap_congrA (Punct Y p) (Punct Y p) heq hgf hid ℤ p]
  erw [relCohMap_idA (Punct Y p) ℤ p]
  simp only [ModuleCat.hom_id, LinearMap.id_apply]

/-- **`(tcmF_inv)^*` inverts `pr₁^*`**: `Φ_A (pr₁^* Mpun p) = Mpun p`, because
`tcmPr1 ∘ Fib.tcmF_inv Y p 0` is the identity. -/
theorem tcmF_inv_tcmPr1_Mpun (Y : Type) [TopologicalSpace Y] (p : ℕ) :
    (relCohMap (Fib.tcmF_inv Y p 0) (Punct Y p) (tcmA Y p 0)
        (tcmF_inv_mem_tcmA_zero Y p) ℤ p).hom
      ((relCohMap (tcmPr1 Y p 0) (tcmA Y p 0) (Punct Y p) (fun x hx => hx) ℤ p).hom
        (Mpun p Y)) = Mpun p Y := by
  have hg : ∀ y ∈ (tcmA Y p 0 : Set (tcmX Y p 0)), tcmPr1 Y p 0 y ∈ Punct Y p :=
    fun y hy => hy
  have hgf : ∀ x ∈ (Punct Y p : Set (Y × EuclideanSpace ℝ (Fin (p+0)))),
      tcmPr1 Y p 0 (Fib.tcmF_inv Y p 0 x) ∈ Punct Y p :=
    fun x hx => hg _ (tcmF_inv_mem_tcmA_zero Y p x hx)
  erw [relCohMap_compA_apply (Punct Y p) (tcmA Y p 0) (Punct Y p) (Fib.tcmF_inv Y p 0)
      (tcmPr1 Y p 0) (tcmF_inv_mem_tcmA_zero Y p) (fun x hx => hx) hgf ℤ p (Mpun p Y)]
  rw [relCohMap_congrA (Punct Y p) (Punct Y p) (tcmPr1_comp_tcmF_inv_zero Y p) hgf
      (fun x hx => hx) ℤ p]
  erw [relCohMap_idA (Punct Y p) ℤ p]
  simp only [ModuleCat.hom_id, LinearMap.id_apply]

theorem tcmModelMul_point_zero (Y : Type) [TopologicalSpace Y] [Subsingleton Y] (p : ℕ) :
    Work.Whitney.tcmRelCup (Work.Whitney.tcmA Y p 0) (Work.Whitney.tcmC Y p 0)
        (Work.Whitney.isOpen_tcmA Y p 0) (Work.Whitney.isOpen_tcmC Y p 0) p 0
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 Y p 0) (Work.Whitney.tcmA Y p 0)
        (Work.Thom.Punct Y p) (fun x hx => hx) ℤ p).hom (Work.Thom.Mpun p Y))
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y p 0) (Work.Whitney.tcmC Y p 0)
        (Work.Thom.Punct Y 0) (fun x hx => hx) ℤ 0).hom (Work.Thom.Mpun 0 Y))
    = ((-1 : ℤ) ^ (p * 0)) •
      ((Work.Thom.relCohMap (Work.Whitney.tcmF Y p 0)
        (Work.Whitney.tcmA Y p 0 ∪ Work.Whitney.tcmC Y p 0) (Work.Thom.Punct Y (p + 0))
        (Work.Whitney.tcmF_mem Y p 0) ℤ (p + 0)).hom (Work.Thom.Mpun (p + 0) Y)) := by
  -- normalise the goal: the `p + 0`'s of the statement become `p`'s, and the coefficient becomes `1`
  simp only [Nat.add_zero, Nat.mul_zero]
  simp only [pow_zero, one_smul]
  -- name the three classes of the statement
  set aa : RelCoh ℤ p (tcmX Y p 0) (tcmA Y p 0) :=
    (relCohMap (tcmPr1 Y p 0) (tcmA Y p 0) (Punct Y p) (fun x hx => hx) ℤ p).hom (Mpun p Y) with haa
  set uu : RelCoh ℤ 0 (tcmX Y p 0) (tcmC Y p 0) :=
    (relCohMap (tcmPr2 Y p 0) (tcmC Y p 0) (Punct Y 0) (fun x hx => hx) ℤ 0).hom (Mpun 0 Y)
    with huu
  set bb : RelCoh ℤ p (tcmX Y p 0) (tcmA Y p 0 ∪ tcmC Y p 0) :=
    (relCohMap (tcmF Y p 0) (tcmA Y p 0 ∪ tcmC Y p 0) (Punct Y p)
      (tcmF_mem Y p 0) ℤ p).hom (Mpun p Y) with hbb
  -- the absolute image of `uu` is the unit class
  have hu : (relToAbs ℤ (tcmC Y p 0) 0).hom uu
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (tcmX Y p 0))) := by
    rw [huu]
    have hnat := relCohMap_relToAbs (tcmPr2 Y p 0) (tcmC Y p 0) (Punct Y 0)
      (fun x hx => hx) ℤ 0
    have h := congrArg (fun φ => φ.hom (Mpun 0 Y)) hnat
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [relToAbs_Mpun_zero Y, CohMap_oneH] at h
    exact h
  -- the second closed set is contained in the first (it is empty)
  have hCA : tcmC Y p 0 ⊆ tcmA Y p 0 := fun x hx => (hx (Subsingleton.elim x.2.2 0)).elim
  -- the right unit law
  have hunit : (relCohMap (ContinuousMap.id (tcmX Y p 0)) (tcmA Y p 0)
      (tcmA Y p 0 ∪ tcmC Y p 0) (fun x hx => Or.inl hx) ℤ p).hom
      (tcmRelCup (tcmA Y p 0) (tcmC Y p 0) (isOpen_tcmA Y p 0) (isOpen_tcmC Y p 0) p 0
        aa uu) = aa :=
    tcmRelCup_unit_right (tcmA Y p 0) (tcmC Y p 0) (isOpen_tcmA Y p 0) (isOpen_tcmC Y p 0)
      hCA p aa uu hu
  -- `(Fib.tcmF_inv)^*` factors through the `A`-pair
  have hFacApp : ∀ x : RelCoh ℤ p (tcmX Y p 0) (tcmA Y p 0 ∪ tcmC Y p 0),
      (relCohMap (Fib.tcmF_inv Y p 0) (Punct Y p) (tcmA Y p 0 ∪ tcmC Y p 0)
        (tcmF_inv_mem_union_zero Y p) ℤ p).hom x
      = (relCohMap (Fib.tcmF_inv Y p 0) (Punct Y p) (tcmA Y p 0)
          (tcmF_inv_mem_tcmA_zero Y p) ℤ p).hom
        ((relCohMap (ContinuousMap.id (tcmX Y p 0)) (tcmA Y p 0) (tcmA Y p 0 ∪ tcmC Y p 0)
          (fun x hx => Or.inl hx) ℤ p).hom x) := by
    intro x
    erw [relCohMap_compA_apply (Punct Y p) (tcmA Y p 0) (tcmA Y p 0 ∪ tcmC Y p 0)
      (Fib.tcmF_inv Y p 0) (ContinuousMap.id (tcmX Y p 0)) (tcmF_inv_mem_tcmA_zero Y p)
      (fun x hx => Or.inl hx) (tcmF_inv_mem_union_zero Y p) ℤ p x]
    rw [relCohMap_congrA (Punct Y p) (tcmA Y p 0 ∪ tcmC Y p 0)
      (ContinuousMap.id_comp (Fib.tcmF_inv Y p 0)) (tcmF_inv_mem_union_zero Y p)
      (tcmF_inv_mem_union_zero Y p) ℤ p]
    rfl
  -- the value of the two sides after applying `(Fib.tcmF_inv)^*`
  have hkey : (relCohMap (Fib.tcmF_inv Y p 0) (Punct Y p) (tcmA Y p 0 ∪ tcmC Y p 0)
        (tcmF_inv_mem_union_zero Y p) ℤ p).hom
      (tcmRelCup (tcmA Y p 0) (tcmC Y p 0) (isOpen_tcmA Y p 0) (isOpen_tcmC Y p 0) p 0
        aa uu) = Mpun p Y := by
    rw [hFacApp]
    rw [hunit]
    exact tcmF_inv_tcmPr1_Mpun Y p
  have hkeyb : (relCohMap (Fib.tcmF_inv Y p 0) (Punct Y p) (tcmA Y p 0 ∪ tcmC Y p 0)
        (tcmF_inv_mem_union_zero Y p) ℤ p).hom bb = Mpun p Y := by
    rw [hbb]
    exact tcmF_tcmF_inv_transport_zero Y p (Mpun p Y)
  -- conclude by the left inverse of `(Fib.tcmF_inv)^*`
  have hEq : (relCohMap (Fib.tcmF_inv Y p 0) (Punct Y p) (tcmA Y p 0 ∪ tcmC Y p 0)
        (tcmF_inv_mem_union_zero Y p) ℤ p).hom
        (tcmRelCup (tcmA Y p 0) (tcmC Y p 0) (isOpen_tcmA Y p 0) (isOpen_tcmC Y p 0) p 0
          aa uu)
      = (relCohMap (Fib.tcmF_inv Y p 0) (Punct Y p) (tcmA Y p 0 ∪ tcmC Y p 0)
        (tcmF_inv_mem_union_zero Y p) ℤ p).hom bb :=
    hkey.trans hkeyb.symm
  have hc := congrArg (fun z => (relCohMap (tcmF Y p 0) (tcmA Y p 0 ∪ tcmC Y p 0) (Punct Y p)
      (tcmF_mem Y p 0) ℤ p).hom z) hEq
  rw [tcmF_inv_tcmF_transport_zero Y p (tcmRelCup (tcmA Y p 0) (tcmC Y p 0)
        (isOpen_tcmA Y p 0) (isOpen_tcmC Y p 0) p 0 aa uu)] at hc
  rw [tcmF_inv_tcmF_transport_zero Y p bb] at hc
  exact hc

end

end Work.Whitney
