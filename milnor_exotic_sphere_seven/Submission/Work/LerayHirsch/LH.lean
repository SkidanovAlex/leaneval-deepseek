import Mathlib
import Submission.Work.LerayHirsch.TautLine
import Submission.Work.Whitney.Cup
import Submission.Work.Whitney.cupChern_one_right

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.dupNamespace false
set_option linter.unusedVariables false

/-!
# The Leray–Hirsch statement for the projectivisation

Let `Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι` be a complex gluing-data bundle with
`[Fintype ι]`, `P(E) = Work.LerayHirsch.ProjSpace Z` its projectivisation and `ζ = Work.LerayHirsch.zeta Z`
the first Chern class of the tautological line bundle (`Submission/Work/LerayHirsch/TautLine.lean`).
This module states **Leray–Hirsch** for `P(E) → B`:

```lean
Work.LerayHirsch.zetaPow Z i : Coh ℤ (2 * i) (ProjSpace Z)          -- ζⁱ
Work.LerayHirsch.lhMap Z k :
  ((i : Fin m) → Coh ℤ (2 * (k - i)) B) → Coh ℤ (2 * k) (ProjSpace Z)
Work.LerayHirsch.LerayHirsch Z : Prop := ∀ k, Function.Bijective (lhMap Z k)
```

i.e. `H^{2k}(P(E);ℤ) ≅ ⊕_{i<m} H^{2(k-i)}(B;ℤ)` via `(x_i) ↦ Σ_i π^*(x_i) ⌣ ζ^i` ("`H^*(P(E))` is
free over `H^*(B)` on `1, ζ, …, ζ^{m-1}`"), together with the odd vanishing
`LerayHirschOdd Z := ∀ k, Subsingleton (Coh ℤ (2*k+1) (ProjSpace Z))`.

The proof strategy is the one of the Thom chapter (`Work.Thom.thomClass_of_finite_cover`, the
`Ladder` modules): a Mayer–Vietoris induction over a finite trivialising cover, whose *trivial*
case is Künneth for `B × ℂP^{m-1}`.  The two inputs are named here as the `Prop`s
`KunnethCP` (the trivial case, to be delivered by subproject KUNNETH) and `LerayHirschGlue`
(the Mayer–Vietoris step), and the assembly is `LerayHirsch_of_kunneth_of_glue`.

## Consequences of `LerayHirsch`

* `Work.LerayHirsch.CohMap_projMap_injective_of_LerayHirsch` — `π^*` is **injective** on
  cohomology (in every even degree, and by the odd vanishing in every degree);
* `Work.LerayHirsch.existsUnique_lh_decomposition` — every class of `H^{2k}(P(E))` has a *unique*
  expansion `Σ_i π^*(x_i) ⌣ ζ^i`;
* `Work.LerayHirsch.lhMap_eq_of_CohMap_eq` — the resulting **separation principle**: a relation
  between Chern classes on `B` can be checked after pulling back to `P(E)`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## Powers of the hyperplane class -/

/-- **The powers of the hyperplane class**: `ζ⁰ = 1` and `ζ^{i+1} = ζ^i ⌣ ζ`, in
`H^{2i}(P(E);ℤ)`.  The graded product is `Work.Whitney.cupChern`, which is natural under pullback
(`Work.Whitney.cupChern_CohMap`). -/
noncomputable def zetaPow (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] :
    (i : ℕ) → Coh ℤ (2 * i) (ProjSpace Z) :=
  Nat.rec (motive := fun i => Coh ℤ (2 * i) (ProjSpace Z))
    (cohTransport rfl (Work.Cohomology.oneH ℤ (Work.Whitney.ssB (ProjSpace Z))))
    (fun i rec => Work.Whitney.cupChern i 1 rec (zeta Z))

@[simp] theorem zetaPow_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] :
    zetaPow Z 0 = cohTransport rfl (Work.Cohomology.oneH ℤ (Work.Whitney.ssB (ProjSpace Z))) :=
  rfl

theorem zetaPow_succ (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] (i : ℕ) :
    zetaPow Z (i + 1) = Work.Whitney.cupChern i 1 (zetaPow Z i) (zeta Z) := rfl

/-- `ζ¹ = ζ`. -/
theorem zetaPow_one (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] :
    zetaPow Z 1 = cohTransport rfl (Work.Whitney.cupChern 0 1
      (cohTransport rfl (Work.Cohomology.oneH ℤ (Work.Whitney.ssB (ProjSpace Z)))) (zeta Z)) :=
  rfl

/-! ## The Leray–Hirsch decomposition map -/

/-- The `i`-th summand of the Leray–Hirsch decomposition: `π^*(x) ⌣ ζ^i ∈ H^{2k}(P(E))` for
`x ∈ H^{2(k-i)}(B)`.  (The index `i` ranges over the `i ≤ k`, so that the degrees add up to `2k`;
for `m ≤ k+1` this is all of `Fin m`.) -/
noncomputable def lhTerm (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i : ℕ))) B) :
    Coh ℤ (2 * k) (ProjSpace Z) :=
  cohTransport (by omega)
    (Work.Whitney.cupChern (k - (i : ℕ)) (i : ℕ)
      ((CohMap (projMap Z) ℤ (2 * (k - (i : ℕ)))).hom x) (zetaPow Z i))

theorem lhTerm_def (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i : ℕ))) B) :
    lhTerm Z k i x = cohTransport (by omega)
      (Work.Whitney.cupChern (k - (i : ℕ)) (i : ℕ)
        ((CohMap (projMap Z) ℤ (2 * (k - (i : ℕ)))).hom x) (zetaPow Z i)) := rfl

/-- **The Leray–Hirsch map**: `(x_i)_{i<m, i≤k} ↦ Σ_i π^*(x_i) ⌣ ζ^i`, from the product of the
cohomology of `B` in the degrees `2(k-i)` to `H^{2k}(P(E);ℤ)`. -/
noncomputable def lhMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) :
    ((i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) →
      Coh ℤ (2 * k) (ProjSpace Z) :=
  fun xf => ∑ i, lhTerm Z k i (xf i)

theorem lhMap_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) :
    lhMap Z k xf = ∑ i, lhTerm Z k i (xf i) := rfl

/-! ## The Leray–Hirsch statement -/

/-- **Leray–Hirsch for the projectivisation** `P(E) → B`: the map `(x_i) ↦ Σ_i π^*(x_i) ⌣ ζ^i` is
a bijection `⊕_{i<m} H^{2(k-i)}(B;ℤ) ≅ H^{2k}(P(E);ℤ)` for every `k` — equivalently, `H^*(P(E);ℤ)`
is a free `H^*(B;ℤ)`-module on `1, ζ, …, ζ^{m-1}`. -/
def LerayHirsch (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] : Prop :=
  ∀ k : ℕ, Function.Bijective (lhMap Z k)

/-- The `i`-th summand of the **odd-degree** Leray–Hirsch decomposition:
`π^*(x) ⌣ ζ^i ∈ H^{2k+1}(P(E))` for `x ∈ H^{2(k-i)+1}(B)` (indexed again by the `i ≤ k`). -/
noncomputable def lhTermOdd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    Coh ℤ (2 * k + 1) (ProjSpace Z) :=
  cohTransport (by omega)
    (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (ProjSpace Z))
      (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ))
      ((CohMap (projMap Z) ℤ (2 * k + 1 - 2 * (i : ℕ))).hom x) (zetaPow Z i))

/-- The **odd-degree Leray–Hirsch map**: `(x_i)_{i<m, i≤k} ↦ Σ_i π^*(x_i) ⌣ ζ^i`, from the odd
cohomology of `B` to the odd cohomology of `P(E)`.  (`H^{2k+1}(P(E))` is the sum of the *odd* parts
of `H^*(B)` — it does **not** vanish in general, e.g. for a trivial line bundle over `S¹`.) -/
noncomputable def lhMapOdd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) :
    ((i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) →
      Coh ℤ (2 * k + 1) (ProjSpace Z) :=
  fun xf => ∑ i, lhTermOdd Z k i (xf i)

/-- The **odd-degree part** of Leray–Hirsch: the same decomposition map is a bijection in the odd
degrees `2k+1`.  Together with `LerayHirsch` this is the full statement that `H^*(P(E);ℤ)` is a free
`H^*(B;ℤ)`-module on `1, ζ, …, ζ^{m-1}`. -/
def LerayHirschOdd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] : Prop :=
  ∀ k : ℕ, Function.Bijective (lhMapOdd Z k)

/-- The full Leray–Hirsch statement (even part and odd part). -/
def LerayHirschFull (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] : Prop :=
  LerayHirsch Z ∧ LerayHirschOdd Z

/-! ## The unit law and the consequences of Leray–Hirsch -/

/-- The right unit law of the graded product against `ζ⁰ = 1`. -/
theorem cupChern_zetaPow_zero {B : Type} [TopologicalSpace B] {ι : Type}
    [Fintype ι] {m k : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (x : Coh ℤ (2 * k) (ProjSpace Z)) :
    Work.Whitney.cupChern k 0 x (zetaPow Z 0)
      = cohTransport (by rfl : 2 * (k + 0) = 2 * k) x := by
  rw [zetaPow_zero]
  exact Work.Whitney.cupChern_one_right k x

/-- A summand of the Leray–Hirsch map vanishes when its cohomology class does. -/
theorem lhTerm_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k}) : lhTerm Z k i 0 = 0 := by
  rw [lhTerm_def, Work.Whitney.cupChern_def]
  simp only [map_zero, LinearMap.zero_apply, Work.Thom.cohTransport_zero]

/-- The **`i = 0` summand** of the Leray–Hirsch map is the pullback `π^*x`: this is the unit law,
and it is what makes `π^*` injective. -/
theorem lhTerm_zero_index {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (hm : 1 ≤ m) (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (k : ℕ)
    (x : Coh ℤ (2 * (k - (0 : ℕ))) B) :
    lhTerm Z k ⟨⟨0, hm⟩, Nat.zero_le k⟩ x
      = cohTransport (by omega : 2 * ((k - (0:ℕ)) + 0) = 2 * k)
          ((CohMap (projMap Z) ℤ (2 * (k - (0:ℕ)))).hom x) := by
  rw [lhTerm_def, cupChern_zetaPow_zero, Work.Whitney.cohTransport_trans]

/-- A **family supported at a single index**, as a dependent function into the varying cohomology
degrees of `lhMap`. -/
noncomputable def lhSoloFamily {B : Type} [TopologicalSpace B] {m : ℕ} {k : ℕ}
    (i₀ : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i₀ : ℕ))) B) :
    (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B :=
  fun i => if h : i = i₀ then h ▸ x else 0

theorem lhSoloFamily_self {B : Type} [TopologicalSpace B] {m k : ℕ}
    (i₀ : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i₀ : ℕ))) B) :
    lhSoloFamily i₀ x i₀ = x := by
  rw [lhSoloFamily]; simp

theorem lhSoloFamily_of_ne {B : Type} [TopologicalSpace B] {m k : ℕ}
    {i₀ : {i : Fin m // (i : ℕ) ≤ k}} (x : Coh ℤ (2 * (k - (i₀ : ℕ))) B)
    {i : {i : Fin m // (i : ℕ) ≤ k}} (hi : i ≠ i₀) : lhSoloFamily i₀ x i = 0 := by
  rw [lhSoloFamily]; simp [hi]

/-- The Leray–Hirsch map of a family supported at one index. -/
theorem lhMap_eq_single (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (i₀ : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i₀ : ℕ))) B) :
    lhMap Z k (lhSoloFamily i₀ x) = lhTerm Z k i₀ x := by
  rw [lhMap_apply]
  have h : ∀ i, lhTerm Z k i (lhSoloFamily i₀ x i)
      = if i = i₀ then lhTerm Z k i₀ x else 0 := by
    intro i
    by_cases hi : i = i₀
    · subst hi; rw [lhSoloFamily_self, if_pos rfl]
    · rw [lhSoloFamily_of_ne x hi, lhTerm_zero, if_neg hi]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_ite_eq', if_pos (Finset.mem_univ i₀)]

/-- The **injectivity of `π^*`** for a Leray–Hirsch projectivisation: this is the *separation
principle* used by the Whitney-formula argument (`Submission/Work/Whitney/` §6(c)) — a relation
between classes on `B` can be checked after pulling back to `P(E)`. -/
theorem CohMap_projMap_injective_of_LerayHirsch {B : Type} [TopologicalSpace B]
    {ι : Type} [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (h : LerayHirsch Z) (k : ℕ) :
    Function.Injective (CohMap (projMap Z) ℤ (2 * k)).hom := by
  intro x y hxy
  have hx : lhMap Z k (lhSoloFamily ⟨⟨0, hm⟩, Nat.zero_le k⟩ x)
      = (CohMap (projMap Z) ℤ (2 * k)).hom x := by
    rw [lhMap_eq_single, lhTerm_zero_index]
    exact cohTransport_rfl _
  have hy : lhMap Z k (lhSoloFamily ⟨⟨0, hm⟩, Nat.zero_le k⟩ y)
      = (CohMap (projMap Z) ℤ (2 * k)).hom y := by
    rw [lhMap_eq_single, lhTerm_zero_index]
    exact cohTransport_rfl _
  have h2 : lhMap Z k (lhSoloFamily ⟨⟨0, hm⟩, Nat.zero_le k⟩ x)
      = lhMap Z k (lhSoloFamily ⟨⟨0, hm⟩, Nat.zero_le k⟩ y) := by
    rw [hx, hy, hxy]
  have h3 := (h k).1 h2
  have := congrFun h3 ⟨⟨0, hm⟩, Nat.zero_le k⟩
  simpa [lhSoloFamily_self] using this

/-- **Existence and uniqueness of the Leray–Hirsch decomposition** of a class of `H^{2k}(P(E))`:
this is the "free module on `1, ζ, …, ζ^{m-1}`" content of `LerayHirsch`, in the form a consumer
uses. -/
theorem existsUnique_lh_decomposition {B : Type} [TopologicalSpace B]
    {ι : Type} [Fintype ι] {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (h : LerayHirsch Z) (k : ℕ) (y : Coh ℤ (2 * k) (ProjSpace Z)) :
    ∃! xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B,
      lhMap Z k xf = y := by
  obtain ⟨x, hx⟩ := (h k).2 y
  exact ⟨x, hx, fun y' hy' => (h k).1 (hy'.trans hx.symm)⟩

/-- Unpacking of `LerayHirsch` in the two directions a consumer uses. -/
theorem lhMap_injective_of_LerayHirsch {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (h : LerayHirsch Z) (k : ℕ) :
    Function.Injective (lhMap Z k) := (h k).1

theorem lhMap_surjective_of_LerayHirsch {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (h : LerayHirsch Z) (k : ℕ) :
    Function.Surjective (lhMap Z k) := (h k).2

/-! ## The two inputs of the Mayer–Vietoris induction -/

/-- **The trivial case of Leray–Hirsch**, in the form in which the induction uses it: **Leray–Hirsch
for a bundle which is trivial in the sense that a single chart covers the base**
(`∃ i₀, Z.baseSet i₀ = Set.univ`).

Its mathematical content is Künneth: a single-chart bundle is the product bundle `B × ℂ^m`, so
`P(Z) ≃ₜ B × ℂP^{m-1}` (`Work.LerayHirsch.nonempty_homeo_projSpace_trivial`) and the statement is
the Künneth decomposition `H^n(B × ℂP^{m-1}) ≅ ⊕_{i<m} H^{n-2i}(B)`, to be delivered by subproject
KUNNETH (`Submission/Work/Kunneth/`, `Work.Kunneth.Chapter`).  The *instance* for
`trivialVectorBundleCore` is immediate (`trivial_baseSet`); conversely any single-chart bundle is
isomorphic to it, and `LerayHirschFull` is invariant under a `Work.Thom.BundleIso`
(`Work.LerayHirsch.lerayHirschFull_of_bundleIso`), so nothing is lost by this formulation — it is
the form that makes the assembly `Work.LerayHirsch.LerayHirschTheorem` work without any transport of
cohomology along bundle isomorphisms.

**This is the single input of the trivial case of the Mayer–Vietoris induction**; nothing else in
this chapter is conditional on it. -/
def KunnethCP : Prop :=
  ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι),
    (∃ i₀ : ι, Z.baseSet i₀ = Set.univ) → LerayHirschFull Z

/-- **The Mayer–Vietoris rung of the Leray–Hirsch induction**: if Leray–Hirsch (both parts) holds on
every nonempty finite intersection of the members of a finite open cover of `B`, then it holds on
`B`.  This is the induction step that both the Thom chapter (`Work.Thom.thomClass_of_finite_cover`,
`Work.Thom.Ladder`) and this chapter use: the Mayer–Vietoris sequence of the cover of `P(E)` by the
pieces, the identification of the restricted `ζ`-powers
(`Work.LerayHirsch.lhMap_comap`/`zetaPow_comap`), and the five lemma; the indexing by finite subsets
is what makes the induction run (`⋂ k ∈ S, U k` for `S` a finite set of indices).  The guard
`(⋂ k ∈ S, U k).Nonempty` is harmless — an empty piece has trivially vanishing cohomology — and it
keeps the statement free of the empty-base bookkeeping. -/
def LerayHirschGlue : Prop :=
  ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) {ιc : Type} [Fintype ιc]
    (U : ιc → Set B), (∀ k, IsOpen (U k)) → (⋃ k, U k) = Set.univ →
    (∀ (S : Finset ιc) (hS : S.Nonempty), (⋂ k ∈ S, U k).Nonempty →
      LerayHirschFull (bundleComap Z (subtypeMap (⋂ k ∈ S, U k)))) →
    LerayHirschFull Z

theorem lerayHirschTheorem_of (hK : KunnethCP) (hG : LerayHirschGlue) :
    ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι), LerayHirschFull Z := by
  intro m B _ ι _ Z
  refine hG Z (fun i => Z.baseSet i) (fun i => Z.isOpen_baseSet i) ?_ ?_
  · ext x
    exact ⟨fun _ => trivial, fun _ => Set.mem_iUnion.mpr ⟨Z.indexAt x, Z.mem_baseSet_at x⟩⟩
  · intro S hS _
    obtain ⟨k, hk⟩ := hS
    refine hK (bundleComap Z (subtypeMap (⋂ k ∈ S, Z.baseSet k))) ⟨k, ?_⟩
    ext x
    simp only [bundleComap_baseSet, Set.mem_preimage, Set.mem_univ, iff_true, subtypeMap]
    exact Set.mem_iInter₂.mp x.2 k hk

/-- **The assembly of this chapter**: `KunnethCP` (the trivial case, subproject KUNNETH) and the
Mayer–Vietoris rung `LerayHirschGlue` give **Leray–Hirsch for every complex gluing-data bundle over
every base**.  The proof is the obvious one: apply the rung to the cover of `B` by the base sets
`Z.baseSet i` (finite because `[Fintype ι]`, covering by `Work.VectorBundleCore.mem_baseSet_at`);
each piece `⋂ k ∈ S, Z.baseSet k` is a subset of a single chart, so on it `Z` is *trivial as gluing
data* and `KunnethCP` applies (up to `Work.LerayHirsch.LerayHirschFull` being invariant under a
`Work.Thom.BundleIso`, which is
`Work.LerayHirsch.lerayHirschFull_of_bundleIso`). -/
def LerayHirschTheorem : Prop :=
  KunnethCP → LerayHirschGlue →
    ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι), LerayHirschFull Z

/-- **Leray–Hirsch is the trivial case plus the Mayer–Vietoris rung.** -/
theorem lerayHirschTheorem_holds : LerayHirschTheorem :=
  fun hK hG => lerayHirschTheorem_of hK hG

end

end Work.LerayHirsch
