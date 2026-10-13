/-
Area DSCOH — the graded free modules `⊕_{j : Fin r} S(-d j)` used to cover a finitely generated
graded `A[X₀,…,X_{n-1}]`-module.

The main theorem of the area (`Work.DSCOH.chartCech_finite_vanishing`) is proved by covering a
finitely generated graded module `M` by a finite direct sum of shifts of `S = A[X₀,…,X_{n-1}]`,
and then running a descending induction on the cohomological degree, using the long exact
sequence of the chart Čech complexes.  This file contains the *vocabulary* of that cover:

* `freeGraded d e` — the `e`-th graded piece of `⊕_{j : Fin r} S(-d j)`, presented as the product
  `Fin r → Poly A n` with the piecewise grading: the `e`-th piece consists of those `f` with
  `f j` homogeneous of degree `e - d j`.
* `freeCover g` — the `S`-linear map `⊕_{j} S → M`, `f ↦ ∑_j f j • g j`, attached to a family
  `g : Fin r → M` (the covering map).
* `kerGraded d π` — the grading induced on the kernel of the cover, by intersection with the
  pieces of `freeGraded d`.
-/
import Mathlib
import Submission.Work.DSCOH.Chart
import Submission.Work.DSCOH.Shift
import Submission.Work.DSCOH.shift_gradedSMul
import Submission.Work.DSCOH.shift_isInternal

open MvPolynomial

attribute [instance] Work.DSCOH.shift_gradedSMul

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The `e`-th graded piece of the graded free module `⊕_{j : Fin r} S(-d j)`, presented as the
product `Fin r → Poly A n`: an element lies in it when its `j`-th coordinate is homogeneous of
degree `e - d j`, i.e. lies in `shift (d j) e`. -/
noncomputable def freeGraded {r : ℕ} (d : Fin r → ℕ) (e : ℕ) :
    Submodule A (Fin r → Poly A n) :=
  ⨅ j, Submodule.comap
    ((LinearMap.proj j : (Fin r → Poly A n) →ₗ[Poly A n] Poly A n).restrictScalars A)
    (shift (A := A) (n := n) (d j) e)

lemma mem_freeGraded {r : ℕ} {d : Fin r → ℕ} {e : ℕ} {f : Fin r → Poly A n} :
    f ∈ freeGraded (A := A) (n := n) d e ↔
      ∀ j, f j ∈ shift (A := A) (n := n) (d j) e := by
  simp [freeGraded]

/-- The graded `S`-module structure on `⊕_{j : Fin r} S(-d j)`: the product of the shifted
structures `S(-d j)`. -/
lemma freeGraded_gradedSMul {r : ℕ} (d : Fin r → ℕ) :
    SetLike.GradedSMul (homSub A n) (freeGraded (A := A) (n := n) d) where
  smul_mem := by
    intro i j ai fj hai hfj
    rw [mem_freeGraded] at hfj ⊢
    intro k
    have h := (shift_gradedSMul (A := A) (n := n) (d k)).smul_mem hai (hfj k)
    simpa [Pi.smul_apply, vadd_eq_add, smul_eq_mul] using h

attribute [instance] freeGraded_gradedSMul

/-- The `S`-linear map `∏_j S → M`, `f ↦ ∑_j f j • g j`, attached to a family `g : Fin r → M`.
It is the covering map of `M` by the graded free module on generators `g j`. -/
noncomputable def freeCover {r : ℕ} {M : Type*} [AddCommGroup M] [Module (Poly A n) M]
    (g : Fin r → M) : (Fin r → Poly A n) →ₗ[Poly A n] M where
  toFun f := ∑ j, f j • g j
  map_add' f f' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a f := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_smul a (f j) (g j)

@[simp]
lemma freeCover_apply {r : ℕ} {M : Type*} [AddCommGroup M] [Module (Poly A n) M]
    (g : Fin r → M) (f : Fin r → Poly A n) :
    freeCover (A := A) (n := n) g f = ∑ j, f j • g j := rfl

/-- If the family `g` generates `M` as an `S`-module, the cover map is surjective. -/
lemma freeCover_surjective {r : ℕ} {M : Type*} [AddCommGroup M] [Module (Poly A n) M]
    {g : Fin r → M} (hg : Submodule.span (Poly A n) (Set.range g) = ⊤) :
    Function.Surjective (freeCover (A := A) (n := n) g) := by
  intro m
  have hm : m ∈ Submodule.span (Poly A n) (Set.range g) := by rw [hg]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨fun j => c j, ?_⟩
  rw [freeCover_apply]
  exact hc

/-- The cover map is graded: the image of the `e`-th piece of `⊕_j S(-d j)` lies in the `e`-th
piece of `M`, provided `g j ∈ ℳ (d j)` for all `j`. -/
lemma freeCover_map_freeGraded_le {r : ℕ} {M : Type*} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    {g : Fin r → M} {d : Fin r → ℕ} (hg : ∀ j, g j ∈ ℳ (d j)) (e : ℕ) :
    Submodule.map ((freeCover (A := A) (n := n) g).restrictScalars A)
      (freeGraded (A := A) (n := n) d e) ≤ ℳ e := by
  rintro _ ⟨f, hf, rfl⟩
  have hf' : f ∈ freeGraded (A := A) (n := n) d e := hf
  rw [mem_freeGraded] at hf'
  show (∑ j, f j • g j) ∈ ℳ e
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases h : d j ≤ e
  · have hfj : f j ∈ homSub A n (e - d j) := by simpa [shift_of_le h] using hf' j
    have hsm := SetLike.GradedSMul.smul_mem hfj (hg j)
    have hidx : e - d j + d j = e := Nat.sub_add_cancel h
    simpa only [vadd_eq_add, hidx] using hsm
  · have hfj : f j = 0 := by simpa [shift_of_not_le h] using hf' j
    rw [hfj, zero_smul]
    exact Submodule.zero_mem _

/-- The grading induced on the kernel of the cover map `π`: the intersection with the grading of
the free module. -/
noncomputable def kerGraded {r : ℕ} (d : Fin r → ℕ) {M : Type*} [AddCommGroup M]
    [Module (Poly A n) M] (π : (Fin r → Poly A n) →ₗ[Poly A n] M) (e : ℕ) :
    Submodule A (LinearMap.ker π) :=
  Submodule.comap ((LinearMap.ker π).subtype.restrictScalars A)
    (freeGraded (A := A) (n := n) d e)

lemma mem_kerGraded {r : ℕ} {d : Fin r → ℕ} {M : Type*} [AddCommGroup M]
    [Module (Poly A n) M] {π : (Fin r → Poly A n) →ₗ[Poly A n] M} {e : ℕ}
    {k : LinearMap.ker π} :
    k ∈ kerGraded (A := A) (n := n) d π e ↔
      (k : Fin r → Poly A n) ∈ freeGraded (A := A) (n := n) d e := by
  simp [kerGraded]

/-- The induced grading on the kernel of a graded cover map is a graded `S`-module structure. -/
lemma kerGraded_gradedSMul {r : ℕ} {M : Type*} [AddCommGroup M] [Module (Poly A n) M]
    (d : Fin r → ℕ) (π : (Fin r → Poly A n) →ₗ[Poly A n] M) :
    SetLike.GradedSMul (homSub A n) (kerGraded (A := A) (n := n) d π) where
  smul_mem := by
    intro i j ai kj hai hkj
    rw [mem_kerGraded] at hkj ⊢
    have h := (freeGraded_gradedSMul (A := A) (n := n) d).smul_mem hai hkj
    simpa only [vadd_eq_add, SetLike.val_smul] using h

/-! ## The chart Čech complex has no terms in degrees `≥ n` -/

/-- The `q`-th term of the chart Čech complex is the product over the `(q+1)`-element subsets of
`Fin n`.  For `n ≤ q` there are none, so the term is the product over an empty index, i.e. a
subsingleton module. -/
theorem isZero_CechTerm_of_le {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] (ℳ : ℕ → Submodule A M) {q : ℕ} (h : n ≤ q) :
    CategoryTheory.Limits.IsZero
      (ModuleCat.of A (CechTerm (A := A) (n := n) (M := M) ℳ q)) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine Subsingleton.intro (fun a b => funext fun S => ?_)
  have h1 : S.1.card ≤ n := by simpa using Finset.card_le_univ S.1
  have h2 : q + 1 ≤ n := by rw [← S.2]; exact h1
  omega

/-- The chart Čech complex is concentrated in degrees `< n`, so its homology vanishes in degrees
`≥ n` (there the kernel of the differential on a zero module is zero). -/
theorem chartCech_homology_isZero_of_le {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] (ℳ : ℕ → Submodule A M)
    [SetLike.GradedSMul (homSub A n) ℳ] {q : ℕ} (hq : n ≤ q) :
    CategoryTheory.Limits.IsZero ((chartCech (A := A) (n := n) (M := M) ℳ).homology q) := by
  have h1 : CategoryTheory.Limits.IsZero
      ((chartCech (A := A) (n := n) (M := M) ℳ).X q) :=
    isZero_CechTerm_of_le (A := A) (n := n) ℳ hq
  have h2 : CategoryTheory.Limits.IsZero
      ((chartCech (A := A) (n := n) (M := M) ℳ).sc q).X₂ := h1
  exact CategoryTheory.ShortComplex.isZero_homology_of_isZero_X₂ _ h2

/-! ## The pieces of the graded free module span and are independent -/

/-- In a direct sum, the `e`-th coordinate of a sum of `of`'s indexed by `s ∋ e` is the `e`-th
term; in particular if the sum vanishes then so does every term. -/
private lemma of_sum_eq_zero {ι : Type*} [DecidableEq ι] {N : ι → Type*}
    [∀ i, AddCommMonoid (N i)] {s : Finset ι} (v : (i : ι) → N i)
    (h : (∑ i ∈ s, DirectSum.of N i (v i)) = 0) {e : ι} (he : e ∈ s) : v e = 0 := by
  have h1 : (∑ i ∈ s, DirectSum.of N i (v i)) e = 0 := by rw [h]; rfl
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single e] at h1
  · simpa using h1
  · intro b _ hb
    exact DirectSum.of_eq_of_ne b e (v b) (Ne.symm hb)
  · intro he'
    exact absurd he he'

/-- If the recomposition of a `⨁`-element of the graded free module vanishes, the element is
zero: this is the independence of the pieces, proved coordinatewise using the independence of the
shifted gradings of the polynomial ring. -/
private lemma freeGraded_coeAddMonoidHom_eq_zero {A : Type*} [CommRing A] {n : ℕ} {r : ℕ}
    (d : Fin r → ℕ) {z : DirectSum ℕ (fun e => ↥(freeGraded (A := A) (n := n) d e))}
    (hz : DirectSum.coeAddMonoidHom (freeGraded (A := A) (n := n) d) z = 0) : z = 0 := by
  classical
  haveI hdec : ∀ j : Fin r, DirectSum.Decomposition (shift (A := A) (n := n) (d j)) :=
    fun j => (shift_isInternal (A := A) (n := n) (d j)).chooseDecomposition
  have hsum : (∑ e ∈ z.support, ((z e : Fin r → Poly A n))) = 0 := by
    have h1 : DirectSum.coeAddMonoidHom (freeGraded (A := A) (n := n) d)
        (∑ e ∈ z.support,
          DirectSum.of (fun e => ↥(freeGraded (A := A) (n := n) d e)) e (z e)) = 0 := by
      rw [DirectSum.sum_support_of z, hz]
    rw [map_sum] at h1
    simpa only [DirectSum.coeAddMonoidHom_of] using h1
  have hcoord : ∀ e ∈ z.support, ∀ j, ((z e : Fin r → Poly A n)) j = 0 := by
    intro e he j
    have hJ : (∑ e' ∈ z.support, (((z e' : Fin r → Poly A n)) j)) = 0 := by
      have h1 := congrArg (fun f : Fin r → Poly A n => f j) hsum
      simpa only [Finset.sum_apply j, Pi.zero_apply] using h1
    set w : (e' : ℕ) → ↥(shift (A := A) (n := n) (d j) e') := fun e' =>
      ⟨((z e' : Fin r → Poly A n)) j, (mem_freeGraded.mp (z e').2) j⟩ with hw
    have hw0 : (∑ e' ∈ z.support,
        DirectSum.of (fun e' => ↥(shift (A := A) (n := n) (d j) e')) e' (w e')) = 0 := by
      apply (shift_isInternal (A := A) (n := n) (d j)).1
      rw [map_zero, map_sum]
      simpa only [DirectSum.coeAddMonoidHom_of, hw] using hJ
    have hval := congrArg Subtype.val (of_sum_eq_zero w hw0 he)
    rw [hw] at hval
    simpa using hval
  refine DirectSum.ext fun e => ?_
  by_cases he : e ∈ z.support
  · exact Subtype.ext (funext fun j => by simpa using hcoord e he j)
  · by_contra hne
    exact he ((DFinsupp.mem_support_iff).mpr hne)

/-- **The graded free module `⊕_{j : Fin r} S(-d j)` is an internal direct sum** of its pieces:
a family `f : Fin r → Poly A n` is the sum of the finitely many elements cut out of it by the
shifted gradings of the polynomial ring, coordinate by coordinate. -/
theorem freeGraded_isInternal {A : Type*} [CommRing A] {n : ℕ} {r : ℕ} (d : Fin r → ℕ) :
    DirectSum.IsInternal (freeGraded (A := A) (n := n) d) := by
  classical
  haveI hdec : ∀ j : Fin r, DirectSum.Decomposition (shift (A := A) (n := n) (d j)) :=
    fun j => (shift_isInternal (A := A) (n := n) (d j)).chooseDecomposition
  constructor
  · -- injectivity of the recomposition map
    intro x y hxy
    have h0 : DirectSum.coeAddMonoidHom (freeGraded (A := A) (n := n) d) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (freeGraded_coeAddMonoidHom_eq_zero d h0)
  · -- surjectivity of the recomposition map
    intro f
    set v : ℕ → (Fin r → Poly A n) := fun e j =>
      ((DirectSum.decompose (shift (A := A) (n := n) (d j)) (f j)) e : Poly A n) with hv
    have hmem : ∀ e, v e ∈ freeGraded (A := A) (n := n) d e := by
      intro e
      rw [mem_freeGraded]
      exact fun j => (DirectSum.decompose (shift (A := A) (n := n) (d j)) (f j) e).2
    set s : Finset ℕ := Finset.univ.biUnion
      fun j : Fin r => (DirectSum.decompose (shift (A := A) (n := n) (d j)) (f j)).support
      with hs
    refine ⟨∑ e ∈ s, DirectSum.of (fun e => ↥(freeGraded (A := A) (n := n) d e)) e
      ⟨v e, hmem e⟩, ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    funext j
    rw [Finset.sum_apply j]
    have hsub : (DirectSum.decompose (shift (A := A) (n := n) (d j)) (f j)).support ⊆ s :=
      Finset.subset_biUnion_of_mem (u := fun j : Fin r =>
        (DirectSum.decompose (shift (A := A) (n := n) (d j)) (f j)).support) (Finset.mem_univ j)
    have hzero : ∀ x ∈ s, x ∉ (DirectSum.decompose (shift (A := A) (n := n) (d j))
        (f j)).support → v x j = 0 := by
      intro x _ hx
      have h0 : (DirectSum.decompose (shift (A := A) (n := n) (d j)) (f j)) x = 0 := by
        by_contra hne
        exact hx ((DFinsupp.mem_support_iff).mpr hne)
      rw [hv]
      exact congrArg Subtype.val h0
    rw [← Finset.sum_subset hsub hzero]
    exact DirectSum.sum_support_decompose (shift (A := A) (n := n) (d j)) (f j)

/-! ## The concrete description of the chart Čech cohomology

`cechConcreteH A n ℳ q` is the cohomology of the chart Čech complex in degree `q`, described
concretely as the quotient of the kernel of the differential `d^q` by the image of `d^{q-1}`
(Mathlib's `ShortComplex.moduleCatLeftHomologyData`).  This description is what allows one to
compare the cohomology of two graded modules that are related by a grading-preserving linear
equivalence *without* having to force both into the same universe. -/

/-- The chart Čech cohomology in degree `q`, as the concrete quotient
`ker (d^q) ⧸ im (d^{q-1})` of the `q`-th term of the complex. -/
noncomputable def cechConcreteH (A : Type*) [CommRing A] (n : ℕ) {M : Type*} [AddCommGroup M]
    [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] (q : ℕ) : ModuleCat A :=
  ((chartCech (A := A) (n := n) (M := M) ℳ).sc q).moduleCatLeftHomologyData.H

/-- The categorical cohomology of the chart Čech complex is the concrete quotient of the kernel
by the image. -/
noncomputable def cechHomologyIsoCechConcreteH {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] (ℳ : ℕ → Submodule A M)
    [SetLike.GradedSMul (homSub A n) ℳ] (q : ℕ) :
    (chartCech (A := A) (n := n) (M := M) ℳ).homology q ≅ cechConcreteH A n ℳ q :=
  ((chartCech (A := A) (n := n) (M := M) ℳ).sc q).moduleCatHomologyIso

end Work.DSCOH
