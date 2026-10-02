import Submission.Work.Surgery.SurgeryBordism

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The surgical route to the dimension-`8` congruence

This file assembles the **surgical route** to the dimension-`8` Hirzebruch congruence

`45 σ = 7 p₂ − p₁²`,  equivalently `Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}`,

out of the two steps of the original brief (`Submission/Work/Surgery/ThreeConnected.lean`):

* **Step 1 (surgery below the middle dimension)** — every closed oriented smooth `8`-manifold is
  *surgically equivalent* to a `3`-connected one, i.e. it is bordant to one along a bordism carrying
  the Pontryagin data and the duality inputs (`Work.Surgery.SurgeryBordism`), so that its three
  numbers `(σ, p₁², p₂)` agree with those of the `3`-connected manifold;
* **Step 2 (the classification of `3`-connected `8`-manifolds)** — for a `3`-connected member the
  triple of numbers lies in the rational span of the two generator triples
  `(1,25,10)`, `(1,18,9)` (`Work.Surgery.ThreeConnectedInSpan`).

## Main results

* `Work.Surgery.Family8` — the data of a family of honest closed oriented smooth `8`-manifolds with
  the Pontryagin classes of their tangent bundles (the fields `Man`, `X`, `c`, `p₁`, `p₂` of
  `Work.Bordism.Generation8`, collected so that the statements below stay readable);
* `Work.Surgery.Family8.SurgicalReduction` — Step 1 numerically;
* `Work.Surgery.Family8.GeometricSurgicalReduction` and
  `Work.Surgery.Family8.surgicalReduction_of_geometric` — Step 1 as it is supplied by the geometry
  (a surgery bordism), reduced to the numerical form;
* `Work.Surgery.Family8.numbersInSpan8_of_surgicalReduction` — **the assembly**: Steps 1 and 2
  together give `Work.SignatureBordism.NumbersInSpan8` for *every* member of the family;
* `Work.Surgery.Family8.hirzebruchEight_of_surgicalReduction` and
  `Work.Surgery.Family8.congruence_of_surgicalReduction` — the identity and the congruence
  `7 ∣ p₁² − 4σ`;
* `Work.Surgery.Family8.threeConnectedInSpan_of_generation` — Thom's generation
  (`Work.Bordism.Generation8`) implies Step 2;
* **`Work.Surgery.Family8.Generation8.ofSurgicalRoute`** — **the surgical route *is* Thom's
  generation in this model**: from Steps 1 and 2, and the presence of the two generators in the
  family, one *constructs* `Work.Bordism.Generation8` — a `ℚ`-vector space of rank two with the
  class map given by the coordinates of `(σ, p₁², p₂)` in the basis of the two generator triples,
  the three functionals being the corresponding linear forms.  This is the precise sense in which
  the congruence for closed oriented smooth `8`-manifolds is equivalent to the two surgery steps.
-/

set_option maxHeartbeats 4000000

open scoped Manifold Topology ContDiff
open CategoryTheory

namespace Work.Surgery

open Work.Bordism Work.SignatureBordism Work.Cohomology

noncomputable section

/-- The data of a **family of honest closed oriented smooth `8`-manifolds with their Pontryagin
classes** — the fields `Man`, `X`, `c`, `p₁`, `p₂` of `Work.Bordism.Generation8`. -/
structure Family8 where
  /-- the type of honest manifolds of the family -/
  Man : Type
  /-- the underlying space of a member -/
  X : Man → TopCat.{0}
  /-- its fundamental class -/
  c : (m : Man) → (chainC ℤ (TopCat.toSSet.obj (X m))).homology 8
  /-- its first Pontryagin class -/
  p₁ : (m : Man) → (cochainC ℤ (TopCat.toSSet.obj (X m))).homology 4
  /-- its second Pontryagin class -/
  p₂ : (m : Man) → (cochainC ℤ (TopCat.toSSet.obj (X m))).homology 8

namespace Family8

variable (F : Family8)

/-- A member of the family, as a closed oriented `8`-manifold. -/
def manifold (m : F.Man) : ClosedOriented 8 := ⟨F.X m, F.c m⟩

/-- **Step 1 of the surgical route, numerically**: every member of the family is bordant — along a
bordism which carries the Pontryagin data and the duality inputs, so that the three numbers agree —
to a `3`-connected member. -/
def SurgicalReduction : Prop :=
  ∀ m : F.Man, ∃ m' : F.Man, IsThreeConnected (F.manifold m') ∧
    SameNumbers (F.X m) (F.X m') (F.c m) (F.c m') (F.p₁ m) (F.p₁ m') (F.p₂ m) (F.p₂ m')

/-- **Step 2 of the surgical route** (`Work.Surgery.ThreeConnectedInSpan`, restated for the family):
the number triple of a `3`-connected member lies in the rational span of the two generator triples
`(1,25,10)` and `(1,18,9)`. -/
def InSpan : Prop := ThreeConnectedInSpan F.Man F.X F.c F.p₁ F.p₂

/-- **Step 1 as the geometry supplies it**: every member is joined to a `3`-connected member by a
surgery bordism (`Work.Surgery.SurgeryBordism`) whose Pontryagin classes are those of the model at
both ends.  This is the honest input: it is what "surgery below the middle dimension" produces. -/
def GeometricSurgicalReduction : Prop :=
  ∀ m : F.Man, ∃ m' : F.Man, ∃ h : SurgeryBordism (F.manifold m) (F.manifold m'),
    IsThreeConnected (F.manifold m') ∧
      h.p₁M = F.p₁ m ∧ h.p₂M = F.p₂ m ∧ h.p₁N = F.p₁ m' ∧ h.p₂N = F.p₂ m'

/-- **The geometric form of Step 1 implies the numerical one**: bordism invariance of the three
numbers (`Work.Bordism.PontryaginBordism.full_numbers_eq`, packaged as
`Work.Surgery.sameNumbers_of_pontryaginBordism`) turns a surgery bordism whose Pontryagin classes
are those of the model at both ends into the numerical equivalence of the members. -/
theorem surgicalReduction_of_geometric (h : F.GeometricSurgicalReduction) : F.SurgicalReduction := by
  intro m
  obtain ⟨m', hb, h3, h₁M, h₂M, h₁N, h₂N⟩ := h m
  have hnum := hb.numbers_eq
  unfold numberTriple at hnum
  rw [h₁M, h₂M, h₁N, h₂N] at hnum
  exact ⟨m', h3,
    Int.cast_injective (α := ℚ) (congrArg (fun t : ℚ × ℚ × ℚ => t.1) hnum),
    Int.cast_injective (α := ℚ) (congrArg (fun t : ℚ × ℚ × ℚ => t.2.1) hnum),
    Int.cast_injective (α := ℚ) (congrArg (fun t : ℚ × ℚ × ℚ => t.2.2) hnum)⟩

/-- **The assembly of the surgical route**: Steps 1 and 2 together give
`Work.SignatureBordism.NumbersInSpan8` — the triple `(σ, p₁², p₂)` in the rational span of the two
generator triples — for **every** member of the family, not only the `3`-connected ones. -/
theorem numbersInSpan8_of_surgicalReduction (hred : F.SurgicalReduction)
    (hspan : F.InSpan) (m : F.Man) :
    NumbersInSpan8 (TopCat.toSSet.obj (F.X m)) (F.c m) (F.p₁ m) (F.p₂ m) := by
  obtain ⟨m', h3, hsame⟩ := hred m
  have hmem : NumbersInSpan8 (TopCat.toSSet.obj (F.X m')) (F.c m') (F.p₁ m') (F.p₂ m') := by
    unfold NumbersInSpan8
    exact hspan m' h3
  unfold NumbersInSpan8 at hmem ⊢
  exact (congrArg (fun t : ℚ × ℚ × ℚ =>
    t ∈ Submodule.span ℚ ({cp4Tuple, cp2cp2Tuple} : Set (ℚ × ℚ × ℚ)))
    (numberTriple_eq_of_sameNumbers hsame)).mpr hmem

/-- The number triple of a member is in the span of the generator triples, for every member — the
membership form of `Work.Surgery.Family8.numbersInSpan8_of_surgicalReduction`. -/
theorem mem_span_of_surgicalReduction (hred : F.SurgicalReduction) (hspan : F.InSpan)
    (m : F.Man) :
    numberTriple (F.X m) (F.c m) (F.p₁ m) (F.p₂ m) ∈
      Submodule.span ℚ ({cp4Tuple, cp2cp2Tuple} : Set (ℚ × ℚ × ℚ)) := by
  have h := F.numbersInSpan8_of_surgicalReduction hred hspan m
  unfold NumbersInSpan8 at h
  exact h

/-- **The dimension-`8` Hirzebruch identity `45 σ = 7 p₂ − p₁²` for every member of the family,
from the two surgery steps.** -/
theorem hirzebruchEight_of_surgicalReduction (hred : F.SurgicalReduction)
    (hspan : F.InSpan) (m : F.Man) :
    HirzebruchEightManifold (TopCat.toSSet.obj (F.X m)) (F.c m) (F.p₁ m) (F.p₂ m) :=
  HirzebruchEightManifold_of_numbersInSpan _ _ _ _
    (F.numbersInSpan8_of_surgicalReduction hred hspan m)

/-- **The congruence `p₁² ≡ 4 σ (mod 7)` for every member of the family, from the two surgery
steps.** -/
theorem congruence_of_surgicalReduction (hred : F.SurgicalReduction)
    (hspan : F.InSpan) (m : F.Man) :
    p₁SqNumber (TopCat.toSSet.obj (F.X m)) (F.c m) (F.p₁ m)
      ≡ 4 * sigma 4 (TopCat.toSSet.obj (F.X m)) (F.c m) [ZMOD 7] :=
  hirzebruchEightManifold_congruence _ _ _ _
    (F.hirzebruchEight_of_surgicalReduction hred hspan m)

/-! ## The surgical route and Thom's generation

The construction of `Work.Bordism.Generation8` from the surgical route — the precise sense in which
the route *is* Thom's theorem in this model — needs the model `Work.Bordism.Generation8` itself and
therefore lives in the companion module `Submission/Work/Surgery/SurgicalGeneration.lean`.  The two
generator triples `cp4Tuple = (1,25,10)` and `cp2cp2Tuple = (1,18,9)` are linearly
independent over `ℚ`, so a triple in their span has *unique* coordinates.  The surgical route gives,
for every member of the family, such coordinates, and the three numbers are the corresponding linear
forms of them.  Hence the route supplies a rank-two rational model of `Ω^SO_8 ⊗ ℚ` — the structure
`Work.Bordism.Generation8`. -/

/-- The **coordinates of a triple** in the span of the two generator triples. -/
def spanCoords {v : ℚ × ℚ × ℚ}
    (h : v ∈ Submodule.span ℚ ({cp4Tuple, cp2cp2Tuple} : Set (ℚ × ℚ × ℚ))) : ℚ × ℚ :=
  (Classical.choose (Submodule.mem_span_pair.mp h),
    Classical.choose (Classical.choose_spec (Submodule.mem_span_pair.mp h)))

theorem spanCoords_spec {v : ℚ × ℚ × ℚ}
    (h : v ∈ Submodule.span ℚ ({cp4Tuple, cp2cp2Tuple} : Set (ℚ × ℚ × ℚ))) :
    (spanCoords h).1 • cp4Tuple + (spanCoords h).2 • cp2cp2Tuple = v :=
  Classical.choose_spec (Classical.choose_spec (Submodule.mem_span_pair.mp h))

/-- **The uniqueness of the coordinates**, elementarily: two linear combinations of the generator
triples which are equal have equal coefficients (the first two coordinates of the triples already
determine the coefficients over `ℚ`). -/
theorem span_pair_unique {a b a' b' : ℚ}
    (h : a • cp4Tuple + b • cp2cp2Tuple = a' • cp4Tuple + b' • cp2cp2Tuple) :
    a = a' ∧ b = b' := by
  have h1 : a * 1 + b * 1 = a' * 1 + b' * 1 :=
    congrArg (fun t : ℚ × ℚ × ℚ => t.1) h
  have h2 : a * 25 + b * 18 = a' * 25 + b' * 18 :=
    congrArg (fun t : ℚ × ℚ × ℚ => t.2.1) h
  constructor <;> linarith

/-- The two generator triples are linearly independent. -/
theorem genPair_eq_zero {a b : ℚ} (h : a • cp4Tuple + b • cp2cp2Tuple = 0) :
    a = 0 ∧ b = 0 := by
  have h' := span_pair_unique (a' := 0) (b' := 0) (by simpa using h)
  exact h'

theorem spanCoords_eq {v : ℚ × ℚ × ℚ}
    (h : v ∈ Submodule.span ℚ ({cp4Tuple, cp2cp2Tuple} : Set (ℚ × ℚ × ℚ))) {a b : ℚ}
    (hab : a • cp4Tuple + b • cp2cp2Tuple = v) : spanCoords h = (a, b) := by
  have h' : (spanCoords h).1 • cp4Tuple + (spanCoords h).2 • cp2cp2Tuple
      = a • cp4Tuple + b • cp2cp2Tuple := by
    rw [spanCoords_spec h, hab]
  obtain ⟨h1, h2⟩ := span_pair_unique h'
  exact Prod.ext h1 h2

/-- The signature functional on the coordinates: `σ = a + b`. -/
def sigFun : ℚ × ℚ →ₗ[ℚ] ℚ := LinearMap.fst ℚ ℚ ℚ + LinearMap.snd ℚ ℚ ℚ

/-- The `p₁²`-functional on the coordinates: `p₁² = 25 a + 18 b`. -/
def p1sqFun : ℚ × ℚ →ₗ[ℚ] ℚ := 25 • LinearMap.fst ℚ ℚ ℚ + 18 • LinearMap.snd ℚ ℚ ℚ

/-- The `p₂`-functional on the coordinates: `p₂ = 10 a + 9 b`. -/
def p2Fun : ℚ × ℚ →ₗ[ℚ] ℚ := 10 • LinearMap.fst ℚ ℚ ℚ + 9 • LinearMap.snd ℚ ℚ ℚ

@[simp] theorem sigFun_apply (t : ℚ × ℚ) : sigFun t = t.1 + t.2 := by simp [sigFun]

@[simp] theorem p1sqFun_apply (t : ℚ × ℚ) : p1sqFun t = 25 * t.1 + 18 * t.2 := by
  simp [p1sqFun, mul_comm]

@[simp] theorem p2Fun_apply (t : ℚ × ℚ) : p2Fun t = 10 * t.1 + 9 * t.2 := by
  simp [p2Fun, mul_comm]

/-- The coordinate map of the surgical route: the coordinates of the number triple of a member. -/
noncomputable def coords (hred : F.SurgicalReduction) (hspan : F.InSpan) (m : F.Man) : ℚ × ℚ :=
  spanCoords (F.mem_span_of_surgicalReduction hred hspan m)

theorem coords_spec (hred : F.SurgicalReduction) (hspan : F.InSpan) (m : F.Man) :
    (F.coords hred hspan m).1 • cp4Tuple + (F.coords hred hspan m).2 • cp2cp2Tuple
      = numberTriple (F.X m) (F.c m) (F.p₁ m) (F.p₂ m) :=
  spanCoords_spec _

theorem coords_eq (hred : F.SurgicalReduction) (hspan : F.InSpan) (m : F.Man) {a b : ℚ}
    (hab : a • cp4Tuple + b • cp2cp2Tuple = numberTriple (F.X m) (F.c m) (F.p₁ m) (F.p₂ m)) :
    F.coords hred hspan m = (a, b) :=
  spanCoords_eq _ hab

end Family8

end

end Work.Surgery
