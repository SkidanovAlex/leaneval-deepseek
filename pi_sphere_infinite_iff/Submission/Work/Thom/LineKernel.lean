import Mathlib
import Submission.Work.Thom.LineSection
import Submission.Work.Thom.LineComponent
import Submission.Work.Thom.LineThom
import Submission.Work.Thom.disjointCoverA

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# The kernel of the two section pullbacks for the trivial line bundle

For the trivial real line bundle `E = B × ℝ → B`, with total space `X`, zero complement `A = E∖0`
and the two constant sections `σ₊, σ₋ : X → A`, this module proves

  **`ker σ₊^* ∩ ker σ₋^* = 0`**  (`Work.Thom.eq_zero_of_sigmaPlus_sigmaMinus_eq_zero`),

i.e. a cohomology class of `A` vanishing on the images of both constant sections is zero.

The proof refines each constant section through the corresponding half of `A`
(`σ_± = i_{A_±} ∘ σ'^{±}` with `σ'^{±} : X → A_±` the retractions and `ι'^{±} : A_± → X` the
inclusions), uses `ι'^{±}{}^* ∘ σ'^{±}{}^* = id` (`Work.Thom.CohMap_iotaPrimeA_comp_sigmaPlus` and
its negative analogue, from the homotopies `Work.Thom.homotopic_sigmaPrimeA_iotaPrimeA` and
`Work.Thom.homotopic_sigmaPrimeANeg_iotaPrimeANeg`) to identify `ker σ_±^*` with `ker i_{A_±}^*`,
and then the disjoint-cover lemma
`Work.Thom.eq_zero_of_singularCohomologyMap_eq_zero_of_disjoint` for the cover `A = A₊ ⊔ A₋`.
-/

open CategoryTheory AlgebraicTopology Limits Simplicial

open scoped Topology Simplicial

open Classical

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι₀ : Type} [Inhabited ι₀]

/-! ## The two halves of `E∖0` inside `E∖0` -/

/-- The inclusion of the positive half of `E∖0` into `E∖0`. -/
def inclApos : C(↥(Apos (B := B) (ι₀ := ι₀)),
    ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of the negative half of `E∖0` into `E∖0`. -/
def inclAneg : C(↥(Aneg (B := B) (ι₀ := ι₀)),
    ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-! ## The two halves of the total space, identified with the two halves of `E∖0` -/

/-- The canonical map of the positive half of the total space onto the positive half of `E∖0`. -/
def linePosToApos : C(↥(linePos (B := B) (ι₀ := ι₀)), ↥(Apos (B := B) (ι₀ := ι₀))) where
  toFun p := ⟨⟨p.1, ne_of_gt p.2⟩, p.2⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (p := Apos (B := B) (ι₀ := ι₀))
      (f := fun p : ↥(linePos (B := B) (ι₀ := ι₀)) =>
        (⟨p.1, ne_of_gt p.2⟩ : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))))
      (Continuous.subtype_mk
        (p := zeroComplement (RealBundle.trivial B ℝ ι₀))
        (f := fun p : ↥(linePos (B := B) (ι₀ := ι₀)) => p.1)
        continuous_subtype_val (fun p => ne_of_gt p.2))
      (fun p => p.2)

/-- The inverse of `Work.Thom.linePosToApos`. -/
def AposTolinePos : C(↥(Apos (B := B) (ι₀ := ι₀)), ↥(linePos (B := B) (ι₀ := ι₀))) where
  toFun a := ⟨a.1.1, a.2⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (p := linePos (B := B) (ι₀ := ι₀))
      (f := fun a : ↥(Apos (B := B) (ι₀ := ι₀)) => a.1.1)
      (continuous_subtype_val.comp continuous_subtype_val) (fun a => a.2)

/-- The canonical map of the negative half of the total space onto the negative half of `E∖0`. -/
def lineNegToAneg : C(↥(lineNeg (B := B) (ι₀ := ι₀)), ↥(Aneg (B := B) (ι₀ := ι₀))) where
  toFun p := ⟨⟨p.1, ne_of_lt p.2⟩, p.2⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (p := Aneg (B := B) (ι₀ := ι₀))
      (f := fun p : ↥(lineNeg (B := B) (ι₀ := ι₀)) =>
        (⟨p.1, ne_of_lt p.2⟩ : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))))
      (Continuous.subtype_mk
        (p := zeroComplement (RealBundle.trivial B ℝ ι₀))
        (f := fun p : ↥(lineNeg (B := B) (ι₀ := ι₀)) => p.1)
        continuous_subtype_val (fun p => ne_of_lt p.2))
      (fun p => p.2)

/-- The inverse of `Work.Thom.lineNegToAneg`. -/
def AnegTolineNeg : C(↥(Aneg (B := B) (ι₀ := ι₀)), ↥(lineNeg (B := B) (ι₀ := ι₀))) where
  toFun a := ⟨a.1.1, a.2⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (p := lineNeg (B := B) (ι₀ := ι₀))
      (f := fun a : ↥(Aneg (B := B) (ι₀ := ι₀)) => a.1.1)
      (continuous_subtype_val.comp continuous_subtype_val) (fun a => a.2)

@[simp] theorem AposTolinePos_comp_linePosToApos :
    (AposTolinePos (B := B) (ι₀ := ι₀)).comp (linePosToApos (B := B) (ι₀ := ι₀))
      = ContinuousMap.id ↥(linePos (B := B) (ι₀ := ι₀)) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  rfl

@[simp] theorem AnegTolineNeg_comp_lineNegToAneg :
    (AnegTolineNeg (B := B) (ι₀ := ι₀)).comp (lineNegToAneg (B := B) (ι₀ := ι₀))
      = ContinuousMap.id ↥(lineNeg (B := B) (ι₀ := ι₀)) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  rfl

@[simp] theorem linePosToApos_comp_AposTolinePos :
    (linePosToApos (B := B) (ι₀ := ι₀)).comp (AposTolinePos (B := B) (ι₀ := ι₀))
      = ContinuousMap.id ↥(Apos (B := B) (ι₀ := ι₀)) := by
  apply ContinuousMap.ext
  intro a
  apply Subtype.ext
  apply Subtype.ext
  rfl

@[simp] theorem lineNegToAneg_comp_AnegTolineNeg :
    (lineNegToAneg (B := B) (ι₀ := ι₀)).comp (AnegTolineNeg (B := B) (ι₀ := ι₀))
      = ContinuousMap.id ↥(Aneg (B := B) (ι₀ := ι₀)) := by
  apply ContinuousMap.ext
  intro a
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-! ## The retractions of the two halves -/

/-- The retraction `X → A₊` of the positive half of `E∖0`. -/
def sigmaPrimeA : C((RealBundle.trivial B ℝ ι₀).TotalSpace,
    ↥(Apos (B := B) (ι₀ := ι₀))) :=
  (linePosToApos (B := B) (ι₀ := ι₀)).comp (sigmaPrime (B := B) (ι₀ := ι₀))

/-- The inclusion `A₊ → X`. -/
def iotaPrimeA : C(↥(Apos (B := B) (ι₀ := ι₀)),
    (RealBundle.trivial B ℝ ι₀).TotalSpace) :=
  (iotaPrime (B := B) (ι₀ := ι₀)).comp (AposTolinePos (B := B) (ι₀ := ι₀))

/-- The retraction `X → A₋`. -/
def sigmaPrimeANeg : C((RealBundle.trivial B ℝ ι₀).TotalSpace,
    ↥(Aneg (B := B) (ι₀ := ι₀))) :=
  (lineNegToAneg (B := B) (ι₀ := ι₀)).comp (sigmaPrimeNeg (B := B) (ι₀ := ι₀))

/-- The inclusion `A₋ → X`. -/
def iotaPrimeANeg : C(↥(Aneg (B := B) (ι₀ := ι₀)),
    (RealBundle.trivial B ℝ ι₀).TotalSpace) :=
  (iotaPrimeNeg (B := B) (ι₀ := ι₀)).comp (AnegTolineNeg (B := B) (ι₀ := ι₀))

/-! ## The constant sections factor through the halves -/

/-- `σ₊ = i_{A₊} ∘ σ'⁺`. -/
theorem sigmaPlus_eq_inclApos_comp :
    (sigmaPlus (B := B) (ι₀ := ι₀))
      = (inclApos (B := B) (ι₀ := ι₀)).comp (sigmaPrimeA (B := B) (ι₀ := ι₀)) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  rfl

/-- `σ₋ = i_{A₋} ∘ σ'⁻`. -/
theorem sigmaMinus_eq_inclAneg_comp :
    (sigmaMinus (B := B) (ι₀ := ι₀))
      = (inclAneg (B := B) (ι₀ := ι₀)).comp (sigmaPrimeANeg (B := B) (ι₀ := ι₀)) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  rfl

/-! ## The two homotopies -/

/-- The retraction of the positive half is homotopic to the identity of the positive half. -/
theorem homotopic_sigmaPrimeA_iotaPrimeA :
    ContinuousMap.Homotopic ((sigmaPrimeA (B := B) (ι₀ := ι₀)).comp
      (iotaPrimeA (B := B) (ι₀ := ι₀)))
      (ContinuousMap.id ↥(Apos (B := B) (ι₀ := ι₀))) := by
  have h2 := (ContinuousMap.Homotopic.refl (linePosToApos (B := B) (ι₀ := ι₀))).comp
    ((homotopic_sigmaPrime_iotaPrime (B := B) (ι₀ := ι₀)).comp
      (ContinuousMap.Homotopic.refl (AposTolinePos (B := B) (ι₀ := ι₀))))
  simp only [ContinuousMap.id_comp, linePosToApos_comp_AposTolinePos] at h2
  have h3 : (sigmaPrimeA (B := B) (ι₀ := ι₀)).comp (iotaPrimeA (B := B) (ι₀ := ι₀))
      = (linePosToApos (B := B) (ι₀ := ι₀)).comp
          ((sigmaPrime (B := B) (ι₀ := ι₀)).comp
            ((iotaPrime (B := B) (ι₀ := ι₀)).comp (AposTolinePos (B := B) (ι₀ := ι₀)))) := by
    simp only [sigmaPrimeA, iotaPrimeA, ContinuousMap.comp_assoc]
  rw [h3]
  exact h2

/-- The retraction of the negative half is homotopic to the identity of the negative half. -/
theorem homotopic_sigmaPrimeANeg_iotaPrimeANeg :
    ContinuousMap.Homotopic ((sigmaPrimeANeg (B := B) (ι₀ := ι₀)).comp
      (iotaPrimeANeg (B := B) (ι₀ := ι₀)))
      (ContinuousMap.id ↥(Aneg (B := B) (ι₀ := ι₀))) := by
  have h2 := (ContinuousMap.Homotopic.refl (lineNegToAneg (B := B) (ι₀ := ι₀))).comp
    ((homotopic_sigmaPrimeNeg_iotaPrimeNeg (B := B) (ι₀ := ι₀)).comp
      (ContinuousMap.Homotopic.refl (AnegTolineNeg (B := B) (ι₀ := ι₀))))
  simp only [ContinuousMap.id_comp, lineNegToAneg_comp_AnegTolineNeg] at h2
  have h3 : (sigmaPrimeANeg (B := B) (ι₀ := ι₀)).comp (iotaPrimeANeg (B := B) (ι₀ := ι₀))
      = (lineNegToAneg (B := B) (ι₀ := ι₀)).comp
          ((sigmaPrimeNeg (B := B) (ι₀ := ι₀)).comp
            ((iotaPrimeNeg (B := B) (ι₀ := ι₀)).comp (AnegTolineNeg (B := B) (ι₀ := ι₀)))) := by
    simp only [sigmaPrimeANeg, iotaPrimeANeg, ContinuousMap.comp_assoc]
  rw [h3]
  exact h2

/-! ## The pullback identities -/

/-- **`ι'⁺{}^* ∘ σ'⁺{}^* = id`**. -/
theorem iotaPrimeA_cohmMap_sigmaPrimeA (k : ℕ) :
    ((CohMap (iotaPrimeA (B := B) (ι₀ := ι₀)) ℤ k).hom).comp
        ((CohMap (sigmaPrimeA (B := B) (ι₀ := ι₀)) ℤ k).hom) = LinearMap.id := by
  have h : CohMap (sigmaPrimeA (B := B) (ι₀ := ι₀)) ℤ k
      ≫ CohMap (iotaPrimeA (B := B) (ι₀ := ι₀)) ℤ k
      = 𝟙 (Coh ℤ k ↥(Apos (B := B) (ι₀ := ι₀))) := by
    rw [← CohMap_comp (iotaPrimeA (B := B) (ι₀ := ι₀)) (sigmaPrimeA (B := B) (ι₀ := ι₀)) ℤ k,
      CohMap_homotopic (homotopic_sigmaPrimeA_iotaPrimeA (B := B) (ι₀ := ι₀)) ℤ k, CohMap_id]
  have h2 := congrArg (fun f : Coh ℤ k ↥(Apos (B := B) (ι₀ := ι₀)) ⟶
      Coh ℤ k ↥(Apos (B := B) (ι₀ := ι₀)) => f.hom) h
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_id] using h2

/-- **`ι'⁻{}^* ∘ σ'⁻{}^* = id`**. -/
theorem iotaPrimeANeg_cohmMap_sigmaPrimeANeg (k : ℕ) :
    ((CohMap (iotaPrimeANeg (B := B) (ι₀ := ι₀)) ℤ k).hom).comp
        ((CohMap (sigmaPrimeANeg (B := B) (ι₀ := ι₀)) ℤ k).hom) = LinearMap.id := by
  have h : CohMap (sigmaPrimeANeg (B := B) (ι₀ := ι₀)) ℤ k
      ≫ CohMap (iotaPrimeANeg (B := B) (ι₀ := ι₀)) ℤ k
      = 𝟙 (Coh ℤ k ↥(Aneg (B := B) (ι₀ := ι₀))) := by
    rw [← CohMap_comp (iotaPrimeANeg (B := B) (ι₀ := ι₀))
        (sigmaPrimeANeg (B := B) (ι₀ := ι₀)) ℤ k,
      CohMap_homotopic (homotopic_sigmaPrimeANeg_iotaPrimeANeg (B := B) (ι₀ := ι₀)) ℤ k,
      CohMap_id]
  have h2 := congrArg (fun f : Coh ℤ k ↥(Aneg (B := B) (ι₀ := ι₀)) ⟶
      Coh ℤ k ↥(Aneg (B := B) (ι₀ := ι₀)) => f.hom) h
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_id] using h2

/-- **`ι'⁺{}^* ∘ σ₊^* = i_{A₊}^*`**: the pullback of the positive constant section, followed by the
pullback of the retraction of the positive half, is the restriction to the positive half. -/
theorem CohMap_iotaPrimeA_comp_sigmaPlus (k : ℕ) :
    ((CohMap (iotaPrimeA (B := B) (ι₀ := ι₀)) ℤ k).hom).comp
        ((CohMap (sigmaPlus (B := B) (ι₀ := ι₀)) ℤ k).hom)
      = ((CohMap (inclApos (B := B) (ι₀ := ι₀)) ℤ k).hom) := by
  have h2 : ((CohMap (sigmaPlus (B := B) (ι₀ := ι₀)) ℤ k).hom)
      = ((CohMap (sigmaPrimeA (B := B) (ι₀ := ι₀)) ℤ k).hom).comp
          ((CohMap (inclApos (B := B) (ι₀ := ι₀)) ℤ k).hom) := by
    have h : CohMap (inclApos (B := B) (ι₀ := ι₀)) ℤ k
        ≫ CohMap (sigmaPrimeA (B := B) (ι₀ := ι₀)) ℤ k
        = CohMap (sigmaPlus (B := B) (ι₀ := ι₀)) ℤ k := by
      rw [← CohMap_comp (sigmaPrimeA (B := B) (ι₀ := ι₀)) (inclApos (B := B) (ι₀ := ι₀)) ℤ k,
        ← sigmaPlus_eq_inclApos_comp]
    have h3 := congrArg (fun f : Coh ℤ k ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)) ⟶
        Coh ℤ k (RealBundle.trivial B ℝ ι₀).TotalSpace => f.hom) h
    simpa only [ModuleCat.hom_comp] using h3.symm
  rw [h2, ← LinearMap.comp_assoc, iotaPrimeA_cohmMap_sigmaPrimeA, LinearMap.id_comp]

/-- **`ι'⁻{}^* ∘ σ₋^* = i_{A₋}^*`**. -/
theorem CohMap_iotaPrimeANeg_comp_sigmaMinus (k : ℕ) :
    ((CohMap (iotaPrimeANeg (B := B) (ι₀ := ι₀)) ℤ k).hom).comp
        ((CohMap (sigmaMinus (B := B) (ι₀ := ι₀)) ℤ k).hom)
      = ((CohMap (inclAneg (B := B) (ι₀ := ι₀)) ℤ k).hom) := by
  have h2 : ((CohMap (sigmaMinus (B := B) (ι₀ := ι₀)) ℤ k).hom)
      = ((CohMap (sigmaPrimeANeg (B := B) (ι₀ := ι₀)) ℤ k).hom).comp
          ((CohMap (inclAneg (B := B) (ι₀ := ι₀)) ℤ k).hom) := by
    have h : CohMap (inclAneg (B := B) (ι₀ := ι₀)) ℤ k
        ≫ CohMap (sigmaPrimeANeg (B := B) (ι₀ := ι₀)) ℤ k
        = CohMap (sigmaMinus (B := B) (ι₀ := ι₀)) ℤ k := by
      rw [← CohMap_comp (sigmaPrimeANeg (B := B) (ι₀ := ι₀))
          (inclAneg (B := B) (ι₀ := ι₀)) ℤ k, ← sigmaMinus_eq_inclAneg_comp]
    have h3 := congrArg (fun f : Coh ℤ k ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)) ⟶
        Coh ℤ k (RealBundle.trivial B ℝ ι₀).TotalSpace => f.hom) h
    simpa only [ModuleCat.hom_comp] using h3.symm
  rw [h2, ← LinearMap.comp_assoc, iotaPrimeANeg_cohmMap_sigmaPrimeANeg, LinearMap.id_comp]

/-! ## The kernel theorem -/

/-- **`ker σ₊^* ∩ ker σ₋^* = 0`**: a class of `H^k(E∖0;ℤ)` whose pullbacks along both constant
sections vanish is zero.  Equivalently, the two constant sections *jointly detect* the cohomology of
the zero complement of a trivial line bundle — the two ends of the line bundle lie in different
connected components, so the two projections `σ_±^*` form a monomorphism. -/
theorem eq_zero_of_sigmaPlus_sigmaMinus_eq_zero (k : ℕ)
    (v : Coh ℤ k ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))
    (h1 : (CohMap (sigmaPlus (B := B) (ι₀ := ι₀)) ℤ k).hom v = 0)
    (h2 : (CohMap (sigmaMinus (B := B) (ι₀ := ι₀)) ℤ k).hom v = 0) : v = 0 := by
  have hA : (CohMap (inclApos (B := B) (ι₀ := ι₀)) ℤ k).hom v = 0 := by
    have h := LinearMap.congr_fun (CohMap_iotaPrimeA_comp_sigmaPlus (B := B) (ι₀ := ι₀) k) v
    simp only [LinearMap.comp_apply] at h
    rw [h1, map_zero] at h
    exact h.symm
  have hB : (CohMap (inclAneg (B := B) (ι₀ := ι₀)) ℤ k).hom v = 0 := by
    have h := LinearMap.congr_fun (CohMap_iotaPrimeANeg_comp_sigmaMinus (B := B) (ι₀ := ι₀) k) v
    simp only [LinearMap.comp_apply] at h
    rw [h2, map_zero] at h
    exact h.symm
  exact disjointCoverA
    (X := TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))
    (Apos (B := B) (ι₀ := ι₀)) (Aneg (B := B) (ι₀ := ι₀))
    (isOpen_Apos (B := B) (ι₀ := ι₀)) (isOpen_Aneg (B := B) (ι₀ := ι₀))
    (disjoint_Apos_Aneg (B := B) (ι₀ := ι₀)) (Apos_union_Aneg (B := B) (ι₀ := ι₀))
    k v hA hB

end

end Work.Thom
