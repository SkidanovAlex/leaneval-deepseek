import Mathlib
import Submission.Work.StemsB.Rat.CollarLambdaOatIso
import Submission.Work.StemsB.FibrewiseTrivIso
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.StemsB.SerreSphereStep

/-!
# The explicit source isomorphism `γ` of the Wang transgression

The Wang transgression `θ_n = τS_n ∘ δ_{n+b} ∘ γ^{-1}_{n+b}` of
`Work.StemsB.WangCohShiftDerivation` needs an *explicit* `γ`, whose inverse is computable, so
that the geometric transgression can be identified with `θ`.  This file provides it.

Write `O = sphLoopOuter b` (contractible), `A = p ⁻¹'O`, `F_O = p ⁻¹'{(dOuter b).1}` (the fibre
`wangCohFsp`), and `Φ_O : A → O × F_O` for the trivialisation of `hT_O`.

* `outerProj : O × F_O → F_O` is the second projection; it is a homotopy equivalence because `O`
  is contractible (`sphLoopOuterContr`), so `outerProj^*` is an isomorphism.
* `outerTriv = Φ_O : A → O × F_O` is a homotopy equivalence (`fibTrivH`, `fibTrivK`), so
  `Φ_O^*` is an isomorphism.
* `wangRetr = outerProj ∘ Φ_O : A → F_O` therefore has `wangRetr^*` an isomorphism, and we take

  `γ_k := (asIso (wangRetr^*_k)).symm : H^k(A) ≅ H^k(F_O)`,  so that `γ_k.inv = wangRetr^*_k`
  *by definition*.

The point of this choice (as opposed to the naive inclusion `F_O ↪ A`) is exactly the computability
of the inverse: for `(x, y) ∈ C × F_G` one has `wangRetr (Ψ_G (x,y)) = λ_G (x, y)` (`rfl`), which is
what identifies `γ^{-1}` with the clutching map in the collar computation.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StemsB.Rat

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- The outer piece of the sphere model, as a space. -/
abbrev WangAO (b : ℕ) (p : C(E, SphModel b)) : TopCat :=
  TopCat.of ↥(p ⁻¹' sphLoopOuter b)

/-- The second projection `↥(sphLoopOuter b) × F_O → F_O`. -/
def outerProj (b : ℕ) (p : C(E, SphModel b)) :
    C(↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1}), ↥(p ⁻¹' {(dOuter b).1})) :=
  ⟨fun q => q.2, by fun_prop⟩

/-- The zero section `F_O → ↥(sphLoopOuter b) × F_O`. -/
def outerSect (b : ℕ) (p : C(E, SphModel b)) :
    C(↥(p ⁻¹' {(dOuter b).1}), ↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})) :=
  ⟨fun y => (dOuter b, y), by fun_prop⟩

/-- The trivialisation `Φ_O` of `hT_O`, as a continuous map. -/
def outerTriv (b : ℕ) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    C(↥(p ⁻¹' sphLoopOuter b), ↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})) :=
  fibTrivΦ p (sphLoopOuter b) (dOuter b) hT_O

/-- The retraction `retr = π₂ ∘ Φ_O : A → F_O`. -/
def wangRetr (b : ℕ) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    C(↥(p ⁻¹' sphLoopOuter b), ↥(p ⁻¹' {(dOuter b).1})) :=
  (outerProj b p).comp (outerTriv b p hT_O)

theorem wangRetr_apply (b : ℕ) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (x : ↥(p ⁻¹' sphLoopOuter b)) :
    wangRetr b p hT_O x = (fibTrivΦ p (sphLoopOuter b) (dOuter b) hT_O x).2 := rfl

/-- **`outerProj^*` is an isomorphism** (`sphLoopOuter b` is contractible). -/
theorem isIso_outerProjCoh (b : ℕ) (p : C(E, SphModel b)) (k : ℕ) :
    IsIso (Work.Cohomology.singularCohomologyMap ℚ
      (TopCat.of (↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})))
      (TopCat.of ↥(p ⁻¹' {(dOuter b).1}))
      (TopCat.ofHom (outerProj b p)) k) := by
  refine Work.Cohomology.homotopyEquiv ℚ (TopCat.of (↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})))
    (TopCat.of ↥(p ⁻¹' {(dOuter b).1})) (TopCat.ofHom (outerProj b p))
    (TopCat.ofHom (outerSect b p)) ?_ ?_ k
  · refine topCatHomotopyOf (X := TopCat.of (↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})))
      (Y := TopCat.of ↥(p ⁻¹' {(dOuter b).1}))
      (f := TopCat.ofHom (outerProj b p)) (g := TopCat.ofHom (outerSect b p))
      ⟨fun z => (sphLoopOuterContr b (z.1.1, z.2), z.1.2), by fun_prop⟩ ?_ ?_
    · intro z
      apply Prod.ext
      · exact sphLoopOuterContr_zero b z.1
      · rfl
    · intro z
      apply Prod.ext
      · exact (sphLoopOuterContr_one b z.1).trans (Subtype.ext rfl)
      · rfl
  · refine topCatHomotopyOf (X := TopCat.of ↥(p ⁻¹' {(dOuter b).1}))
      (Y := TopCat.of (↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})))
      (f := TopCat.ofHom (outerSect b p)) (g := TopCat.ofHom (outerProj b p))
      ⟨fun z => z.1, by fun_prop⟩ (fun z => rfl) (fun z => rfl)

/-- **`Φ_O^*` is an isomorphism** (`Φ_O` is a homotopy equivalence, with inverse `Ψ_O`). -/
theorem isIso_outerTrivCoh (b : ℕ) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ) :
    IsIso (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(p ⁻¹' sphLoopOuter b))
      (TopCat.of (↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})))
      (TopCat.ofHom (outerTriv b p hT_O)) k) := by
  refine Work.Cohomology.homotopyEquiv ℚ (TopCat.of ↥(p ⁻¹' sphLoopOuter b))
    (TopCat.of (↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})))
    (TopCat.ofHom (outerTriv b p hT_O))
    (TopCat.ofHom (fibTrivΨ p (sphLoopOuter b) (dOuter b) hT_O)) ?_ ?_ k
  · exact topCatHomotopyOf (X := TopCat.of ↥(p ⁻¹' sphLoopOuter b))
      (Y := TopCat.of (↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})))
      (f := TopCat.ofHom (outerTriv b p hT_O))
      (g := TopCat.ofHom (fibTrivΨ p (sphLoopOuter b) (dOuter b) hT_O))
      (fibTrivH p (sphLoopOuter b) (dOuter b) hT_O)
      (fibTrivH_zero p (sphLoopOuter b) (dOuter b) hT_O)
      (fun x => fibTrivH_one p (sphLoopOuter b) (dOuter b) hT_O x)
  · exact topCatHomotopyOf (X := TopCat.of (↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})))
      (Y := TopCat.of ↥(p ⁻¹' sphLoopOuter b))
      (f := TopCat.ofHom (fibTrivΨ p (sphLoopOuter b) (dOuter b) hT_O))
      (g := TopCat.ofHom (outerTriv b p hT_O))
      (fibTrivK p (sphLoopOuter b) (dOuter b) hT_O)
      (fibTrivK_zero p (sphLoopOuter b) (dOuter b) hT_O)
      (fun y => fibTrivK_one p (sphLoopOuter b) (dOuter b) hT_O y)

/-- The pullback `wangRetr^* : H^k(F_O) → H^k(A)`. -/
def wangRetrCoh (b : ℕ) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ) :
    Work.Cohomology.singularCohomology ℚ k (WangFO b p) ⟶
      Work.Cohomology.singularCohomology ℚ k (WangAO b p) :=
  Work.Cohomology.singularCohomologyMap ℚ (WangAO b p) (WangFO b p) (TopCat.ofHom (wangRetr b p hT_O)) k

/-- **`wangRetr^*` is an isomorphism.** -/
theorem isIso_wangRetrCoh (b : ℕ) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ) :
    IsIso (wangRetrCoh b p hT_O k) := by
  have h1 : wangRetrCoh b p hT_O k
      = Work.Cohomology.singularCohomologyMap ℚ
          (TopCat.of (↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})))
          (TopCat.of ↥(p ⁻¹' {(dOuter b).1})) (TopCat.ofHom (outerProj b p)) k
        ≫ Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(p ⁻¹' sphLoopOuter b))
          (TopCat.of (↥(sphLoopOuter b) × ↥(p ⁻¹' {(dOuter b).1})))
          (TopCat.ofHom (outerTriv b p hT_O)) k :=
    Work.Cohomology.singularCohomologyMap_comp ℚ (TopCat.ofHom (outerTriv b p hT_O))
      (TopCat.ofHom (outerProj b p)) k
  haveI := isIso_outerProjCoh b p k
  haveI := isIso_outerTrivCoh b p hT_O k
  rw [h1]
  infer_instance

/-- **The explicit identification `γ` of the Wang sequence**: `γ_k : H^k(A) ≅ H^k(F_O)`, defined so
that `γ_k.inv = wangRetr^*_k` by construction. -/
def wangGammaExplicit (b : ℕ) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ) :
    Work.Cohomology.singularCohomology ℚ k (WangAO b p) ≅
      Work.Cohomology.singularCohomology ℚ k (WangFO b p) := by
  haveI := isIso_wangRetrCoh b p hT_O k
  exact (asIso (wangRetrCoh b p hT_O k)).symm

@[simp] theorem wangGammaExplicit_inv (b : ℕ) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ) :
    (wangGammaExplicit b p hT_O k).inv = wangRetrCoh b p hT_O k := rfl

/-- **The key computation of `wangRetr` on the collar**: for `(x, y) ∈ C × F_G`,
`wangRetr (Ψ_G (x,y)) = λ_G (x,y)`.  (Both sides are the second component of `Φ_O (Ψ_G (x,y))`.)
This is what turns `γ^{-1}` into the clutching map `λ_G^*` in the collar computation. -/
theorem wangRetr_fibTrivΨ (b : ℕ) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (q : ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1}))) :
    wangRetr b p hT_O
        ⟨(fibTrivΨ p (sphLoopBig b) d_G hT_G q.1).1,
          fibTrivΨ_mem (sphLoopBig b) d_G hT_G q.1 (sphLoopOuter b) q.2.1⟩
      = collarLambdaG b p d_G hT_G hT_O q := rfl

end

end Work.StemsB.Rat
