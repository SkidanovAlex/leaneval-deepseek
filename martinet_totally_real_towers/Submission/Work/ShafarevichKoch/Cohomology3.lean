import Mathlib
import Submission.Work.ConCohomology.All

/-!
# `Work.ShafarevichKoch.Cohomology3` -- continuous cohomology in degree `3`

`Submission/Work/ConCohomology/` builds the continuous cohomology `H¹` and `H²` of a topological
group with coefficients in a discrete module (`Work.ConCohomology.H1`, `...H2`), together with
`Cochain3` -- but `Cochain3` is there only to define `Z²` as a kernel ("no cohomology is taken in
degree `3`", `ConCohomology/Defs.lean`).  The classical route to the Shafarevich--Koch relation
bound (README §18.2) needs one more degree: the `ℤ`-power sequence

```
0 → H²(G,ℤ)/p → H²(G,ℤ/p) → H³(G,ℤ)[p] → 0
```

of Hajir--Maire--Ramakrishna (arXiv:2103.09508, §2), whose middle map is the connecting map of the
coefficient sequence `0 → ℤ → ℤ → ℤ/p → 0`.

This module supplies the missing degree: the `4`-cochains, the third differential `d³`, the
`3`-cocycles `Z³`, the `3`-coboundaries `B³`, and the cohomology `H³(G,M)`, with the basic API
mirroring `ConCohomology/Defs.lean` (`H3.mk`, `H3.mk_eq_mk_iff`, `B3'`, `mem_B3'`), plus the
identity `B³ ≤ Z³` (`d3Fun_d2Fun`: `d³ ∘ d² = 0`).

## Main declarations

* `Work.ShafarevichKoch.Cochain4`, `d3Fun`, `isLocallyConstant_d3Fun`, `d3Hom`;
* `Work.ShafarevichKoch.d3Fun_d2Fun` : `d3Fun (d2Fun f) = 0`;
* `Work.ShafarevichKoch.Z3`, `B3`, `B3'`, `H3`, `H3.mk`, `H3.mk_eq_mk_iff`, `mem_B3'`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ConCohomology

section Basic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M]

/-- The group of `4`-cochains: locally constant functions `G × G × G × G → M`. -/
abbrev Cochain4 (G : Type*) [TopologicalSpace G] (M : Type*) := LocallyConstant (G × G × G × G) M

/-- The third inhomogeneous coboundary. -/
def d3Fun (f : G × G × G → M) : G × G × G × G → M := fun p =>
  p.1 • f (p.2.1, p.2.2.1, p.2.2.2) - f (p.1 * p.2.1, p.2.2.1, p.2.2.2)
    + f (p.1, p.2.1 * p.2.2.1, p.2.2.2) - f (p.1, p.2.1, p.2.2.1 * p.2.2.2)
    + f (p.1, p.2.1, p.2.2.1)

@[simp] lemma d3Fun_apply (f : G × G × G → M) (σ τ ρ υ : G) :
    d3Fun f (σ, τ, ρ, υ) = σ • f (τ, ρ, υ) - f (σ * τ, ρ, υ) + f (σ, τ * ρ, υ)
      - f (σ, τ, ρ * υ) + f (σ, τ, ρ) := rfl

/-- `d³` is additive in its argument. -/
lemma d3Fun_add (f g : G × G × G → M) : d3Fun (f + g) = d3Fun f + d3Fun g := by
  funext p
  obtain ⟨σ, τ, ρ, υ⟩ := p
  simp only [d3Fun_apply, Pi.add_apply]
  rw [smul_add]
  abel

/-- `d³` is additive in its argument (negation form). -/
lemma d3Fun_neg (f : G × G × G → M) : d3Fun (-f) = -d3Fun f := by
  funext p
  obtain ⟨σ, τ, ρ, υ⟩ := p
  simp only [d3Fun_apply, Pi.neg_apply]
  rw [smul_neg]
  abel

lemma isLocallyConstant_d3Fun (f : Cochain3 G M) :
    IsLocallyConstant (d3Fun (f : G × G × G → M)) := by
  have c1 : Continuous fun p : G × G × G × G => p.1 := continuous_fst
  have c2 : Continuous fun p : G × G × G × G => p.2.1 :=
    continuous_fst.comp continuous_snd
  have c3 : Continuous fun p : G × G × G × G => p.2.2.1 :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have c4 : Continuous fun p : G × G × G × G => p.2.2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  have h1 : IsLocallyConstant fun p : G × G × G × G => f (p.2.1, p.2.2.1, p.2.2.2) :=
    f.isLocallyConstant.comp_continuous (c2.prodMk (c3.prodMk c4))
  have h2 : IsLocallyConstant fun p : G × G × G × G => p.1 • f (p.2.1, p.2.2.1, p.2.2.2) :=
    isLocallyConstant_smul_comp (φ := fun p : G × G × G × G => f (p.2.1, p.2.2.1, p.2.2.2))
      h1 c1
  have h3 : IsLocallyConstant fun p : G × G × G × G => f (p.1 * p.2.1, p.2.2.1, p.2.2.2) :=
    f.isLocallyConstant.comp_continuous ((c1.mul c2).prodMk (c3.prodMk c4))
  have h4 : IsLocallyConstant fun p : G × G × G × G => f (p.1, p.2.1 * p.2.2.1, p.2.2.2) :=
    f.isLocallyConstant.comp_continuous (c1.prodMk ((c2.mul c3).prodMk c4))
  have h5 : IsLocallyConstant fun p : G × G × G × G => f (p.1, p.2.1, p.2.2.1 * p.2.2.2) :=
    f.isLocallyConstant.comp_continuous (c1.prodMk (c2.prodMk (c3.mul c4)))
  have h6 : IsLocallyConstant fun p : G × G × G × G => f (p.1, p.2.1, p.2.2.1) :=
    f.isLocallyConstant.comp_continuous (c1.prodMk (c2.prodMk c3))
  exact (((h2.sub h3).add h4).sub h5).add h6

/-- The third differential as a homomorphism `C³(G,M) → C⁴(G,M)`. -/
def d3Hom (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    Cochain3 G M →+ Cochain4 G M where
  toFun f := ⟨d3Fun (f : G × G × G → M), isLocallyConstant_d3Fun f⟩
  map_zero' := by
    ext p
    obtain ⟨σ, τ, ρ, υ⟩ := p
    show d3Fun (G := G) (M := M) (0 : G × G × G → M) (σ, τ, ρ, υ) =
      (0 : G × G × G × G → M) (σ, τ, ρ, υ)
    simp [d3Fun]
  map_add' f g := by
    ext p
    obtain ⟨σ, τ, ρ, υ⟩ := p
    show d3Fun (f + g : G × G × G → M) (σ, τ, ρ, υ) =
      (d3Fun (f : G × G × G → M) + d3Fun (g : G × G × G → M)) (σ, τ, ρ, υ)
    simp only [d3Fun_apply, Pi.add_apply]
    rw [smul_add]
    abel

@[simp] lemma d3Hom_apply (f : Cochain3 G M) (σ τ ρ υ : G) :
    d3Hom G M f (σ, τ, ρ, υ) = σ • f (τ, ρ, υ) - f (σ * τ, ρ, υ) + f (σ, τ * ρ, υ)
      - f (σ, τ, ρ * υ) + f (σ, τ, ρ) := rfl

/-- **`d³ ∘ d² = 0`** -- the cocycle condition in degree `3`, which is what makes `H³` a
cohomology group (`B³ ≤ Z³`) and what the connecting map of a coefficient sequence consumes. -/
lemma d3Fun_d2Fun (f : G × G → M) : d3Fun (d2Fun f) = 0 := by
  funext p
  obtain ⟨σ, τ, ρ, υ⟩ := p
  simp only [d3Fun_apply, d2Fun_apply, Pi.zero_apply]
  rw [smul_sub, smul_add, smul_sub, ← mul_smul]
  repeat rw [← mul_assoc]
  abel

end Basic

/-! ## The cohomology group `H³` -/

section CohomologyGroups3

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M]

/-- The group of `3`-cocycles. -/
def Z3 (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    AddSubgroup (Cochain3 G M) := (d3Hom G M).ker

/-- The group of `3`-coboundaries. -/
def B3 (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    AddSubgroup (Cochain3 G M) := (d2Hom G M).range

/-- `B³` viewed inside `Z³`. -/
def B3' (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    AddSubgroup (Z3 G M) := (B3 G M).comap (Z3 G M).subtype

@[simp] lemma mem_Z3 {z : Cochain3 G M} : z ∈ Z3 G M ↔ d3Hom G M z = 0 := Iff.rfl

@[simp] lemma mem_B3' {z : Z3 G M} : z ∈ B3' G M ↔ (z : Cochain3 G M) ∈ B3 G M := Iff.rfl

/-- `B³ ≤ Z³`: the coboundaries are cocycles. -/
lemma B3_le_Z3 : B3 G M ≤ Z3 G M := by
  rintro _ ⟨f, rfl⟩
  show d3Hom G M (d2Hom G M f) = 0
  ext p
  obtain ⟨σ, τ, ρ, υ⟩ := p
  simpa using congrFun (d3Fun_d2Fun (G := G) (M := M) (f : G × G → M)) (σ, τ, ρ, υ)

/-- `H³(G,M)`: continuous `3`-cocycles modulo `3`-coboundaries. -/
noncomputable abbrev H3 (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] : Type _ :=
  (Z3 G M) ⧸ (B3' G M)

/-- The class of a `3`-cocycle in `H³`. -/
def H3.mk (z : Z3 G M) : H3 G M := QuotientAddGroup.mk z

lemma H3.mk_eq_mk_iff (z w : Z3 G M) : H3.mk z = H3.mk w ↔ z - w ∈ B3' G M :=
  QuotientAddGroup.eq_iff_sub_mem

end CohomologyGroups3

end Work.ShafarevichKoch
