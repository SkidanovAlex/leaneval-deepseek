import Mathlib
import Submission.Work.Lattice.GraysonLattice
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.Minkowski.minkowski_second_upper

/-!
# P2/P3-general (b), step 3: Minkowski-2-upper for arbitrary rank-`r` family spans

The realiser-span Minkowski theorem of `Submission.MinkowskiRealiser` is stated for the
span of the first `j` members of a `Fin d`-indexed ambient family.  This module gives the
**direct family-span variant** used for an *arbitrary* rank-`r` subgroup: for any
`ℝ`-independent family `u : Fin r → E d` (`0 < r`) with

    `W := span ℤ (range u)`   (a rank-`r` lattice of `V := span ℝ (range u)`)

the intrinsic successive minima of `W` satisfy Minkowski's second theorem (upper bound),

    `(∏ i : Fin r, λ_{i.val+1}(W)) · vol(unit ball of V) ≤ 2^{2r} · latticeCovol W`

The transport layer is the `Submission.MinkowskiRealiser` one with the realiser-subfamily
`v ∘ castLE` replaced by the arbitrary family `u` (whose own real span is `V`); every
`Fin d`-ambient `ℝ`-independent family is here, so the theorem applies to every rank-`r`
subgroup once it is presented as the `ℤ`-span of its `ℤ`-basis (the presentation lemma
for the lattices of the §3 route is `FlowSubgroupBasis`-style, recorded in the roadmap).
The transport layer (carrier correspondence, successive-minima and covolume bridges) is
the `Submission.MinkowskiRealiser` one, re-parameterized by the arbitrary family `u`
(whose own real span is `V`); the realiser-span theorems of that module are the special
case `u := v ∘ castLE` and remain available for the exact-realiser block argument.

All declarations are Mathlib + Submission (GraysonLattice) + Commons.
-/

noncomputable section

open Set Filter Metric MeasureTheory Module Real BigOperators
open scoped ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.FamilySpanMinkowski

open Submission.GraysonData
open Submission.GraysonLattice
open Commons.Lattice.SuccessiveMinima

/-- The real span of an `ℝ`-independent family `u : Fin r → E d`: `V`. -/
abbrev Vf {d r : ℕ} (u : Fin r → E d) : Submodule ℝ (E d) :=
  Submodule.span ℝ (Set.range u)

/-- The real span of the `ℤ`-span of the family is the real span of the family. -/
lemma realSpan_spanFamily {d r : ℕ} (u : Fin r → E d) :
    realSpan (Submodule.span ℤ (Set.range u)) = Vf u := by
  dsimp [Vf]
  dsimp [realSpan]
  rw [Submodule.span_span_of_tower (R := ℤ) (S := ℝ) (M := E d) (s := Set.range u)]

/-- The family, coerced into `V` (a point of `V` whose ambient value is `u r`). -/
noncomputable def familyWv {d r : ℕ} (u : Fin r → E d) : Fin r → Vf u :=
  fun r => ⟨u r, Submodule.subset_span (Set.mem_range_self r)⟩

/-- The ambient value of the coerced family is the family member. -/
lemma familyWv_apply {d r : ℕ} (u : Fin r → E d) (i : Fin r) :
    ((familyWv u i : Vf u) : E d) = u i := by rfl

/-- The coerced family is `ℝ`-independent in `V`. -/
lemma familyWv_li {d r : ℕ} (u : Fin r → E d) (hli : LinearIndependent ℝ u) :
    LinearIndependent ℝ (familyWv u) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcE : (∑ i : Fin r, c i • (u i)) = 0 := by
    have hc' := congrArg (fun x : Vf u => (x : E d)) hc
    simpa [familyWv] using hc'
  exact (Fintype.linearIndependent_iff.mp hli) c hcE

/-- The real span of the family has dimension `r`. -/
lemma finrank_Vf {d r : ℕ} (u : Fin r → E d) (hli : LinearIndependent ℝ u) :
    Module.finrank ℝ (Vf u) = r := by
  dsimp [Vf]
  rw [finrank_span_eq_card (R := ℝ) (b := u) hli]
  simp

/-- The coerced family spans `V`. -/
lemma familyWv_span {d r : ℕ} (u : Fin r → E d) (hli : LinearIndependent ℝ u) :
    ⊤ ≤ Submodule.span ℝ (Set.range (familyWv u)) := by
  exact Submission.SubLatticeCovol.span_top_of_linearIndependent (familyWv u)
    (familyWv_li u hli) (finrank_Vf u hli)

/-- The canonical `ℝ`-basis of `V` formed by the coerced family. -/
@[reducible] noncomputable def familyBasis {d r : ℕ} (u : Fin r → E d)
    (hli : LinearIndependent ℝ u) : Basis (Fin r) ℝ (Vf u) :=
  Module.Basis.mk (familyWv_li u hli) (familyWv_span u hli)

/-- The canonical basis recovers the family members in the ambient space. -/
lemma familyBasis_apply {d r : ℕ} (u : Fin r → E d) (hli : LinearIndependent ℝ u)
    (i : Fin r) :
    ((familyBasis u hli i : Vf u) : E d) = u i := by
  have hb : (familyBasis u hli i : Vf u) = familyWv u i := by
    exact congr_fun (Module.Basis.coe_mk (familyWv_li u hli) (familyWv_span u hli)) i
  rw [hb]
  rfl

/-- The transport lattice of the family span inside its own real span: the `ℤ`-span of
the canonical basis (a full-rank lattice of `V`). -/
@[reducible] noncomputable def familySpanLattice {d r : ℕ} (u : Fin r → E d)
    (hli : LinearIndependent ℝ u) : Submodule ℤ (Vf u) :=
  Submodule.span ℤ (Set.range (familyBasis u hli))

/-- The transport lattice is full rank: `finrank ℤ (familySpanLattice) = r`. -/
lemma finrank_familySpanLattice {d r : ℕ} (_hr : 0 < r) (u : Fin r → E d)
    (hli : LinearIndependent ℝ u) :
    Module.finrank ℤ (familySpanLattice u hli) = r := by
  classical
  let L : Submodule ℤ (Vf u) := familySpanLattice u hli
  haveI : IsZLattice ℝ L := by
    dsimp [L]
    infer_instance
  have hrank := ZLattice.rank (K := ℝ) (L := L)
  simpa [L] using hrank.trans (finrank_Vf u hli)

/-- The ambient `ℤ`-span of the family is the image of the transport lattice under the
inclusion `V ↪ ℝᵈ`. -/
lemma span_eq_map_familySpanLattice {d r : ℕ} (u : Fin r → E d)
    (hli : LinearIndependent ℝ u) :
    Submodule.span ℤ (Set.range u) =
      (familySpanLattice u hli).map ((Vf u).subtype.restrictScalars ℤ) := by
  classical
  let f : Vf u →ₗ[ℤ] E d := (Vf u).subtype.restrictScalars ℤ
  have himgset : f '' (Set.range (familyBasis u hli)) = Set.range u := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, hy⟩
      refine ⟨i, ?_⟩
      exact (show f (familyBasis u hli i) = u i from by
        simpa [f] using (familyBasis_apply u hli i)).symm.trans hy
    · rintro ⟨i, rfl⟩
      refine ⟨familyBasis u hli i, ⟨i, rfl⟩, ?_⟩
      simpa [f] using (familyBasis_apply u hli i)
  calc
    Submodule.span ℤ (Set.range u) =
        Submodule.map ((Vf u).subtype.restrictScalars ℤ) (familySpanLattice u hli) := by
          symm
          dsimp [familySpanLattice]
          rw [Submodule.map_span]
          rw [himgset]

/-- **Carrier correspondence**: the transport lattice in `V` is exactly the preimage of
the ambient `ℤ`-span of the family under the inclusion `V ↪ ℝᵈ`. -/
lemma familySpanLattice_carrier {d r : ℕ} (u : Fin r → E d)
    (hli : LinearIndependent ℝ u) :
    ∀ x : Vf u, x ∈ familySpanLattice u hli ↔
      (x : E d) ∈ Submodule.span ℤ (Set.range u) := by
  classical
  intro x
  have himg := span_eq_map_familySpanLattice u hli
  constructor
  · intro hx
    rw [himg]
    rw [Submodule.mem_map]
    refine ⟨x, hx, rfl⟩
  · intro hx
    rw [himg] at hx
    rw [Submodule.mem_map] at hx
    rcases hx with ⟨y, hyL, hyx⟩
    have hyx' : y = x := by
      apply (Vf u).injective_subtype
      exact hyx
    simpa [hyx'] using hyL

/-- The ambient `ℤ`-span of the family is contained in its own real span. -/
lemma familySpan_subset_Vf {d r : ℕ} (u : Fin r → E d) :
    (Submodule.span ℤ (Set.range u) : Set (E d)) ⊆ (Vf u : Set (E d)) := by
  intro x hx
  have hx' : x ∈ realSpan (Submodule.span ℤ (Set.range u)) := Submodule.subset_span hx
  rwa [realSpan_spanFamily u] at hx'

/-- **Successive minima of the transport lattice equal those of the ambient family
span**: for every `i`, `λᵢ(L) = λᵢ(span ℤ (range u))`. -/
lemma successiveMinimum_familySpanLattice_eq {d r i : ℕ} (u : Fin r → E d)
    (hli : LinearIndependent ℝ u) :
    Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E d)
        (Submodule.span ℤ (Set.range u)) i =
      Commons.Lattice.SuccessiveMinima.successiveMinimum (E := Vf u)
        (familySpanLattice u hli) i := by
  unfold Commons.Lattice.SuccessiveMinima.successiveMinimum
  congr 1
  ext r
  constructor
  · intro hr
    rcases hr with ⟨hr0, f, hlin, hnorm⟩
    let g : Fin i → familySpanLattice u hli := fun k =>
      ⟨⟨(f k : E d), by
        have hsub : (Submodule.span ℤ (Set.range u) : Set (E d)) ⊆ (Vf u : Set (E d)) :=
          familySpan_subset_Vf u
        exact hsub (f k).2⟩,
        (familySpanLattice_carrier u hli
          ⟨(f k : E d), familySpan_subset_Vf u (f k).2⟩).2 (f k).2⟩
    refine ⟨hr0, g, ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro c hc
      have hcE : (∑ k : Fin i, c k • ((f k : E d))) = 0 := by
        have hc' := congrArg (fun x : Vf u => (x : E d)) hc
        simpa [g] using hc'
      exact (Fintype.linearIndependent_iff.mp hlin) c hcE
    · intro k
      simpa [g] using hnorm k
  · intro hr
    rcases hr with ⟨hr0, f, hlin, hnorm⟩
    let g : Fin i → Submodule.span ℤ (Set.range u) := fun k =>
      ⟨(f k : Vf u), (familySpanLattice_carrier u hli (f k)).1 (f k).2⟩
    refine ⟨hr0, g, ?_, ?_⟩
    · have hliV : LinearIndependent ℤ (fun k : Fin i =>
          ((Vf u).subtype.restrictScalars ℤ) (f k : Vf u)) :=
        hlin.map' ((Vf u).subtype.restrictScalars ℤ) (LinearMap.ker_eq_bot.mpr (by
          intro x y hxy
          exact (Vf u).injective_subtype hxy))
      have hfam : (fun k : Fin i => ((g k : Submodule.span ℤ (Set.range u)) : E d)) =
          (fun k : Fin i => ((Vf u).subtype.restrictScalars ℤ) (f k : Vf u)) := by
        funext k
        rfl
      simpa [hfam] using hliV
    · intro k
      simpa [g] using hnorm k

/-- **Covolume of the transport lattice equals the own-span covolume of the family
span**: `covol(L) = latticeCovol (span ℤ (range u))`. -/
lemma covolume_familySpanLattice_eq {d r : ℕ} (hr : 0 < r) (u : Fin r → E d)
    (hli : LinearIndependent ℝ u) :
    ZLattice.covolume (familySpanLattice u hli) =
      latticeCovol (Submodule.span ℤ (Set.range u)) := by
  classical
  have hwedge1 := Submission.SubLatticeCovol.covol_wedge_of_submodule_basis (d := d)
    (r := r) hr (Vf u) (familyBasis u hli)
  have hfam : (fun i : Fin r => ((familyBasis u hli i : Vf u) : E d)) = u := by
    funext i
    exact familyBasis_apply u hli i
  have hwedge2 : latticeCovol (Submodule.span ℤ (Set.range u)) =
      ‖exteriorPower.ιMulti ℝ r u‖ := by
    simpa using (latticeCovol_span (d := d) (r := r) hr u hli)
  calc
    ZLattice.covolume (familySpanLattice u hli)
        = ‖exteriorPower.ιMulti ℝ r (fun i : Fin r => ((familyBasis u hli i : Vf u) : E d))‖ :=
          hwedge1
    _ = ‖exteriorPower.ιMulti ℝ r u‖ := by rw [hfam]
    _ = latticeCovol (Submodule.span ℤ (Set.range u)) := hwedge2.symm

/-- **Minkowski-2-upper on the family-span transport lattice** (intrinsic form). -/
theorem minkowski_second_upper_familySpanLattice {d r : ℕ} (hr : 0 < r)
    (u : Fin r → E d) (hli : LinearIndependent ℝ u) :
    (∏ i : Fin r,
        Commons.Lattice.SuccessiveMinima.successiveMinimum (E := Vf u)
          (familySpanLattice u hli) (i.val + 1)) *
        ENNReal.toReal (volume (Metric.closedBall (0 : Vf u) 1)) ≤
      (2 : ℝ) ^ (2 * r) * ZLattice.covolume (familySpanLattice u hli) := by
  classical
  have hnt : Nontrivial (Vf u) := by
    let x : Vf u := ⟨u ⟨0, hr⟩, Submodule.subset_span (Set.mem_range_self _)⟩
    refine ⟨x, 0, ?_⟩
    intro hx0
    apply hli.ne_zero ⟨0, hr⟩
    exact congrArg (fun y : Vf u => (y : E d)) hx0
  haveI : Nontrivial (Vf u) := hnt
  haveI : DiscreteTopology (familySpanLattice u hli) := by
    dsimp [familySpanLattice]
    infer_instance
  haveI : IsZLattice ℝ (familySpanLattice u hli) := by
    dsimp [familySpanLattice]
    infer_instance
  exact Commons.Lattice.Minkowski.minkowski_second_upper (d := r) (E := Vf u)
    (L := familySpanLattice u hli) hr (finrank_familySpanLattice hr u hli)

/-- **Minkowski-2-upper for an arbitrary rank-`r` family span, general-vocabulary form**:
for an `ℝ`-independent ambient family `u : Fin r → E d` (`0 < r`), with
`W := span ℤ (range u)` and `V := span ℝ (range u)`, the product of the first `r`
successive minima of `W` (in the ambient norm) times the unit-ball volume of `V` is
bounded by `2^{2r}` times the own-span covolume `latticeCovol W`. -/
theorem minkowski_second_upper_familySpan {d r : ℕ} (hr : 0 < r) (u : Fin r → E d)
    (hli : LinearIndependent ℝ u) :
    (∏ i : Fin r, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E d)
        (Submodule.span ℤ (Set.range u)) (i.val + 1)) *
        ENNReal.toReal (volume (Metric.closedBall (0 : Vf u) 1)) ≤
      (2 : ℝ) ^ (2 * r) * latticeCovol (Submodule.span ℤ (Set.range u)) := by
  classical
  have hmain := minkowski_second_upper_familySpanLattice (d := d) (r := r) hr u hli
  have hlam : ∀ i : Fin r,
      Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E d)
        (Submodule.span ℤ (Set.range u)) (i.val + 1) =
      Commons.Lattice.SuccessiveMinima.successiveMinimum (E := Vf u)
        (familySpanLattice u hli) (i.val + 1) := by
    intro i
    exact successiveMinimum_familySpanLattice_eq u hli
  have hcov : latticeCovol (Submodule.span ℤ (Set.range u)) =
      ZLattice.covolume (familySpanLattice u hli) :=
    (covolume_familySpanLattice_eq (d := d) (r := r) hr u hli).symm
  have hmain' : (∏ i : Fin r, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E d)
        (Submodule.span ℤ (Set.range u)) (i.val + 1)) *
        ENNReal.toReal (volume (Metric.closedBall (0 : Vf u) 1)) ≤
      (2 : ℝ) ^ (2 * r) * latticeCovol (Submodule.span ℤ (Set.range u)) := by
    rw [hcov]
    rw [show (∏ i : Fin r, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E d)
        (Submodule.span ℤ (Set.range u)) (i.val + 1)) =
      (∏ i : Fin r, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := Vf u)
        (familySpanLattice u hli) (i.val + 1)) from
          Finset.prod_congr rfl (fun i hi => hlam i)]
    exact hmain
  exact hmain'

end Submission.FamilySpanMinkowski

end
