import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_union_aux
import Submission.Work.Cohomology.pd_ab_defs
import Submission.Work.Cohomology.pd_hatcher_W

/-!
# Framing lemmas for the gluing step (Hatcher, Lemma 3.36)

Elementary "bookkeeping" lemmas used by the crux square of Hatcher's Lemma 3.36, in the
situation `W = U ∪ V` of an open cover of a subspace of an ambient space `M`:

* `pdRelSub_inter`, `pdRelSub_union` — the complements inside `W` of a union/intersection;
* `relKern_mono` — `relKern` is antitone in the set;
* `range_inclChains_mono` — the range of the inclusion of chains is monotone in the set;
* `mem_range_pdIncl_of_mem_range_pdTr` — a chain of `W` lying in the image of the chains of the
  trace `pdTr W S` (for `S ⊆ W`) lifts to a chain of `S`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {M : TopCat}

/-! ## The complements inside `W` of a union and of an intersection -/

/-- The complement of `K ∪ L` inside `W` is the intersection of the complements of `K` and `L`. -/
theorem pdRelSub_inter (W : Set M) (K L : Set M) :
    pdRelSub W K ∩ pdRelSub W L = pdRelSub W (K ∪ L) := by
  ext x
  simp only [Set.mem_inter_iff, pdRelSub_mem_iff, Set.mem_union, not_or]

/-- The complement of `K ∩ L` inside `W` is the union of the complements of `K` and `L`. -/
theorem pdG3_pdRelSub_union (W : Set M) (K L : Set M) :
    pdRelSub W (K ∩ L) = pdRelSub W K ∪ pdRelSub W L := by
  ext x
  simp only [Set.mem_union, pdRelSub_mem_iff, Set.mem_inter_iff, not_and_or]

/-! ## Monotonicity of `relKern` -/

/-- `relKern` is antitone in the set: a relative cochain for the bigger set is one for the smaller
set. -/
theorem pdG3_relKern_mono {X : TopCat} {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    relKern ℤ X T n ≤ relKern ℤ X S n := by
  intro φ hφ
  have h1 : ((relMapLM ℤ S T (𝟙 X) (fun x hx => h hx) n ⟨φ, hφ⟩ : relKern ℤ X S n) :
      ↑((singularCochainComplex ℤ X).X n)) = φ := by
    rw [relMapLM_coe, dualChainMap_id]
    rfl
  have h2 : ((relMapLM ℤ S T (𝟙 X) (fun x hx => h hx) n ⟨φ, hφ⟩ : relKern ℤ X S n) :
      ↑((singularCochainComplex ℤ X).X n)) ∈ relKern ℤ X S n :=
    (relMapLM ℤ S T (𝟙 X) (fun x hx => h hx) n ⟨φ, hφ⟩).2
  rwa [h1] at h2

/-! ## Monotonicity of the ranges of the inclusions of chains -/

/-- The range of the inclusion of the chains of `S` is contained in the range of the inclusion of
the chains of `T` for `S ⊆ T`. -/
theorem range_inclChains_mono {X : TopCat} {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    LinearMap.range ((inclChains X S).f n).hom ≤ LinearMap.range ((inclChains X T).f n).hom := by
  rintro y ⟨z, rfl⟩
  refine ⟨(ModuleCat.Hom.hom ((inclChainsSub X S T h).f n)) z, ?_⟩
  have hcomp := congrArg (fun (g : singularChains ℤ (TopCat.of S) ⟶ singularChains ℤ X) =>
    (ModuleCat.Hom.hom (g.f n)) z) (inclChainsSub_comp X S T h)
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
  exact hcomp

/-! ## Lifting a chain supported in the trace -/

/-- **A chain of `W` lying in the chains of the trace `pdTr W S` lifts to a chain of `S`.** -/
theorem mem_range_pdIncl_of_mem_range_pdTr {W S : Set M} (h : S ⊆ W) {n : ℕ}
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

end

end Work.Cohomology

namespace Work.Cohomology

noncomputable section

/-- **The relative cycle associated with a chain whose boundary lies in the relative subcomplex.**
For a chain `x` of `X` whose boundary is the image of a chain of `A`, the class of `x` in the
relative chains `C_*(X,A)`. -/
noncomputable def pdRelCycleOf {X : TopCat} (A : Set X) (n : ℕ) (x : (singularChains ℤ X).X n)
    (hx : (singularChains ℤ X).d n (n - 1) x
      ∈ LinearMap.range ((inclChains X A).f (n - 1)).hom) :
    (relChains X A).cycles n :=
  cycleOf n (((cokernel.π (inclChains X A)).f n) x) (by
    obtain ⟨g, hg⟩ := hx
    have hcomm := congrArg (fun (h : (singularChains ℤ X).X n ⟶
        (cokernel (inclChains X A)).X (n - 1)) => (ModuleCat.Hom.hom h) x)
      ((cokernel.π (inclChains X A)).comm n (n - 1))
    change (ModuleCat.Hom.hom ((cokernel.π (inclChains X A)).f n ≫
      (cokernel (inclChains X A)).d n (n - 1))) x = 0
    rw [hcomm]
    change (ModuleCat.Hom.hom ((cokernel.π (inclChains X A)).f (n - 1)))
      ((ModuleCat.Hom.hom ((singularChains ℤ X).d n (n - 1))) x) = 0
    rw [← hg]
    exact cokernel_π_f_apply_eq_zero (n - 1) g)

/-- The underlying relative chain of `pdRelCycleOf` is the projection of the chain. -/
theorem pdRelCycleOf_iCycles {X : TopCat} (A : Set X) (n : ℕ) (x : (singularChains ℤ X).X n)
    (hx : (singularChains ℤ X).d n (n - 1) x
      ∈ LinearMap.range ((inclChains X A).f (n - 1)).hom) :
    (relChains X A).iCycles n (pdRelCycleOf A n x hx)
      = ((cokernel.π (inclChains X A)).f n) x :=
  iCycles_cycleOf n _ _

end

end Work.Cohomology

namespace Work.Cohomology

noncomputable section

/-- **The cochain underlying an element of a relative cochain complex.** -/
def pdCohUnder (X : TopCat) (A : Set X) (n : ℕ) (x : (relComplex ℤ X A).X n) :
    Cochain ℤ (TopCat.toSSet.obj X) n :=
  show (↑(((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n) →ₗ[ℤ] ℤ) from x.1

/-- **The cochain underlying a cycle of a relative cochain complex.** -/
def pdCohUnderCycle (X : TopCat) (A : Set X) (n : ℕ) (z : (relComplex ℤ X A).cycles n) :
    Cochain ℤ (TopCat.toSSet.obj X) n :=
  pdCohUnder X A n ((relComplex ℤ X A).iCycles n z)

@[simp] theorem pdCohUnder_apply (X : TopCat) (A : Set X) (n : ℕ)
    (x : (relComplex ℤ X A).X n) : pdCohUnder X A n x = x.1 := rfl

end

end Work.Cohomology
