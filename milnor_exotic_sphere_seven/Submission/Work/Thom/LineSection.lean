import Mathlib
import Submission.Work.Thom.LineGeom
import Submission.Work.Thom.Pair

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# The two ends of the trivial real line bundle

For the trivial real line bundle `E = B × ℝ → B` with total space `X` and zero complement
`A = E∖0 ⊆ X`, this module provides the geometric maps that the "suspension" construction of the
Thom class uses:

* `Work.Thom.linePos`, `Work.Thom.lineNeg` — the two halves `A₊ = {0 < p.2}` and `A₋ = {p.2 < 0}`
  of the zero complement, with `Work.Thom.zeroComplement_eq_union` and
  `Work.Thom.disjoint_linePos_lineNeg`;
* `Work.Thom.sigmaPlus`, `Work.Thom.sigmaMinus : C(X, A)` — the constant sections
  `x ↦ ⟨x,1⟩` and `x ↦ ⟨x,-1⟩` into the zero complement;
* `Work.Thom.homotopic_secConst` — `x ↦ ⟨x,c⟩` is homotopic to the identity of `X` (the affine
  homotopy `Work.Thom.affineHom`), hence `σ_±^* ∘ (i_A)^* = id` on cohomology;
* `Work.Thom.sigmaPrime : C(X, ↥A₊)`, `Work.Thom.iotaPrime : C(↥A₊, X)` and
  `Work.Thom.homotopic_sigmaPrime_iotaPrime` — the retraction of `A₊` onto `B × {1}`.
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle Filter

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

section TrivLine

variable {ι₀ : Type} [Inhabited ι₀]

/-- The **positive half** `A₊ = {0 < p.2}` of the total space of the trivial line bundle. -/
def linePos : Set (RealBundle.trivial B ℝ ι₀).TotalSpace :=
  {p | 0 < (show ℝ from p.2)}

/-- The **negative half** `A₋ = {p.2 < 0}` of the total space of the trivial line bundle. -/
def lineNeg : Set (RealBundle.trivial B ℝ ι₀).TotalSpace :=
  {p | (show ℝ from p.2) < 0}

/-- The zero complement is the union of the two halves. -/
theorem zeroComplement_eq_union :
    zeroComplement (RealBundle.trivial B ℝ ι₀) = linePos ∪ lineNeg := by
  ext p
  constructor
  · intro hp
    rcases lt_trichotomy (show ℝ from p.2) 0 with h | h | h
    · exact Or.inr h
    · exact absurd h hp
    · exact Or.inl h
  · rintro (h | h)
    · exact ne_of_gt h
    · exact ne_of_lt h

/-- The two halves are disjoint. -/
theorem disjoint_linePos_lineNeg :
    Disjoint (linePos (B := B) (ι₀ := ι₀)) (lineNeg (B := B) (ι₀ := ι₀)) := by
  refine Set.disjoint_left.mpr ?_
  intro p hp hq
  have hp' : (0:ℝ) < (show ℝ from p.2) := hp
  have hq' : (show ℝ from p.2) < 0 := hq
  linarith

/-- The preferred trivialisation of the trivial line bundle is globally continuous (its source is
the whole space). -/
theorem continuous_localTriv_trivial (i : ι₀) :
    Continuous ((RealBundle.trivial B ℝ ι₀).localTriv i) := by
  have hsrc : ((RealBundle.trivial B ℝ ι₀).localTriv i).source = Set.univ := by
    rw [Bundle.Trivialization.source_eq,
      show ((RealBundle.trivial B ℝ ι₀).localTriv i).baseSet = Set.univ from rfl,
      Set.preimage_univ]
  rw [← continuousOn_univ, ← hsrc]
  exact ((RealBundle.trivial B ℝ ι₀).localTriv i).continuousOn_toFun

/-- **The fibre coordinate of the trivial line bundle is continuous.** -/
theorem continuous_fibreCoord_trivial :
    Continuous (fun p : (RealBundle.trivial B ℝ ι₀).TotalSpace => (show ℝ from p.2)) := by
  have h : (fun p : (RealBundle.trivial B ℝ ι₀).TotalSpace => (show ℝ from p.2)) =
      fun p => (((RealBundle.trivial B ℝ ι₀).localTriv (default : ι₀)) p).2 := by
    funext p
    rw [VectorBundleCore.localTriv_apply, RealBundle.trivial_coordChange]
    rfl
  rw [h]
  exact continuous_snd.comp (continuous_localTriv_trivial (default : ι₀))

/-- The positive half is the preimage of `(0,∞)` under the preferred trivialisation. -/
theorem linePos_eq_preimage :
    linePos (B := B) (ι₀ := ι₀) =
      ((RealBundle.trivial B ℝ ι₀).localTriv (default : ι₀)) ⁻¹'
        {q : B × ℝ | 0 < q.2} := by
  ext p
  rw [linePos, Set.mem_preimage, Set.mem_setOf_eq, VectorBundleCore.localTriv_apply,
    RealBundle.trivial_coordChange]
  rfl

/-- The negative half is the preimage of `(-∞,0)` under the preferred trivialisation. -/
theorem lineNeg_eq_preimage :
    lineNeg (B := B) (ι₀ := ι₀) =
      ((RealBundle.trivial B ℝ ι₀).localTriv (default : ι₀)) ⁻¹'
        {q : B × ℝ | q.2 < 0} := by
  ext p
  rw [lineNeg, Set.mem_preimage, Set.mem_setOf_eq, VectorBundleCore.localTriv_apply,
    RealBundle.trivial_coordChange]
  rfl

/-- The positive half is open. -/
theorem isOpen_linePos : IsOpen (linePos (B := B) (ι₀ := ι₀)) := by
  rw [linePos_eq_preimage]
  exact (isOpen_lt continuous_const continuous_snd).preimage
    (continuous_localTriv_trivial (default : ι₀))

/-- The negative half is open. -/
theorem isOpen_lineNeg : IsOpen (lineNeg (B := B) (ι₀ := ι₀)) := by
  rw [lineNeg_eq_preimage]
  exact (isOpen_lt continuous_snd continuous_const).preimage
    (continuous_localTriv_trivial (default : ι₀))

/-- The **positive constant section** `x ↦ ⟨x,1⟩`, as a map into the zero complement. -/
def sigmaPlus : C((RealBundle.trivial B ℝ ι₀).TotalSpace,
    ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :=
  ⟨fun p : (RealBundle.trivial B ℝ ι₀).TotalSpace =>
      ⟨(⟨p.1, (show (RealBundle.trivial B ℝ ι₀).Fiber p.1 from (1:ℝ))⟩ :
        (RealBundle.trivial B ℝ ι₀).TotalSpace), by
        show (show ℝ from (1:ℝ)) ≠ 0
        norm_num⟩,
    by
      apply Continuous.subtype_mk
      exact (secConst (B := B) (ι₀ := ι₀) 1).continuous⟩

/-- The **negative constant section** `x ↦ ⟨x,-1⟩`, as a map into the zero complement. -/
def sigmaMinus : C((RealBundle.trivial B ℝ ι₀).TotalSpace,
    ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :=
  ⟨fun p : (RealBundle.trivial B ℝ ι₀).TotalSpace =>
      ⟨(⟨p.1, (show (RealBundle.trivial B ℝ ι₀).Fiber p.1 from (-1:ℝ))⟩ :
        (RealBundle.trivial B ℝ ι₀).TotalSpace), by
        show (show ℝ from (-1:ℝ)) ≠ 0
        norm_num⟩,
    by
      apply Continuous.subtype_mk
      exact (secConst (B := B) (ι₀ := ι₀) (-1)).continuous⟩

@[simp] theorem sigmaPlus_apply (p : (RealBundle.trivial B ℝ ι₀).TotalSpace) :
    ((sigmaPlus (B := B) (ι₀ := ι₀) p : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
      (RealBundle.trivial B ℝ ι₀).TotalSpace) =
        (⟨p.1, (show (RealBundle.trivial B ℝ ι₀).Fiber p.1 from (1 : ℝ))⟩ :
          (RealBundle.trivial B ℝ ι₀).TotalSpace) := rfl

@[simp] theorem sigmaMinus_apply (p : (RealBundle.trivial B ℝ ι₀).TotalSpace) :
    ((sigmaMinus (B := B) (ι₀ := ι₀) p : ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
      (RealBundle.trivial B ℝ ι₀).TotalSpace) =
        (⟨p.1, (show (RealBundle.trivial B ℝ ι₀).Fiber p.1 from (-1 : ℝ))⟩ :
          (RealBundle.trivial B ℝ ι₀).TotalSpace) := rfl

/-- The inclusion of the zero complement composed with `σ₊` is the constant section at `1`. -/
theorem subtypeMap_comp_sigmaPlus :
    (subtypeMap (zeroComplement (RealBundle.trivial B ℝ ι₀))).comp (sigmaPlus (B := B) (ι₀ := ι₀))
      = secConst (B := B) (ι₀ := ι₀) 1 := rfl

/-- The inclusion of the zero complement composed with `σ₋` is the constant section at `-1`. -/
theorem subtypeMap_comp_sigmaMinus :
    (subtypeMap (zeroComplement (RealBundle.trivial B ℝ ι₀))).comp (sigmaMinus (B := B) (ι₀ := ι₀))
      = secConst (B := B) (ι₀ := ι₀) (-1) := rfl

/-- **The constant section `x ↦ ⟨x,c⟩` is homotopic to the identity** of the total space of the
trivial line bundle (the affine homotopy `Work.Thom.affineHom`). -/
theorem homotopic_secConst (c : ℝ) :
    ContinuousMap.Homotopic (secConst (B := B) (ι₀ := ι₀) c)
      (ContinuousMap.id ((RealBundle.trivial B ℝ ι₀).TotalSpace)) :=
  ⟨ContinuousMap.Homotopy.mk (affineHom (B := B) (ι₀ := ι₀) c)
    (fun p => affineHom_zero c p) (fun p => affineHom_one c p)⟩

/-- `σ₊^* ∘ (i_A)^* = id`: the composite of the inclusion of the zero complement with the positive
constant section is the identity on cohomology. -/
theorem sigmaPlus_cohmMap_subtypeMap (k : ℕ) :
    ((CohMap (sigmaPlus (B := B) (ι₀ := ι₀)) ℤ k).hom).comp
        ((CohMap (subtypeMap (zeroComplement (RealBundle.trivial B ℝ ι₀))) ℤ k).hom)
      = LinearMap.id := by
  have h := CohMap_comp (sigmaPlus (B := B) (ι₀ := ι₀))
    (subtypeMap (zeroComplement (RealBundle.trivial B ℝ ι₀))) ℤ k
  rw [subtypeMap_comp_sigmaPlus, CohMap_homotopic (homotopic_secConst 1) ℤ k, CohMap_id] at h
  have h2 := congrArg (fun f : Coh ℤ k ((RealBundle.trivial B ℝ ι₀).TotalSpace) ⟶
      Coh ℤ k ((RealBundle.trivial B ℝ ι₀).TotalSpace) => f.hom) h
  simpa [ModuleCat.hom_comp, LinearMap.comp_assoc] using h2.symm

/-- `σ₋^* ∘ (i_A)^* = id`. -/
theorem sigmaMinus_cohmMap_subtypeMap (k : ℕ) :
    ((CohMap (sigmaMinus (B := B) (ι₀ := ι₀)) ℤ k).hom).comp
        ((CohMap (subtypeMap (zeroComplement (RealBundle.trivial B ℝ ι₀))) ℤ k).hom)
      = LinearMap.id := by
  have h := CohMap_comp (sigmaMinus (B := B) (ι₀ := ι₀))
    (subtypeMap (zeroComplement (RealBundle.trivial B ℝ ι₀))) ℤ k
  rw [subtypeMap_comp_sigmaMinus, CohMap_homotopic (homotopic_secConst (-1)) ℤ k, CohMap_id] at h
  have h2 := congrArg (fun f : Coh ℤ k ((RealBundle.trivial B ℝ ι₀).TotalSpace) ⟶
      Coh ℤ k ((RealBundle.trivial B ℝ ι₀).TotalSpace) => f.hom) h
  simpa [ModuleCat.hom_comp, LinearMap.comp_assoc] using h2.symm

/-- The **retraction of the positive half onto `B × {1}`**: the map `x ↦ ⟨x,1⟩` of the total space,
viewed as a map into `A₊`. -/
def sigmaPrime : C((RealBundle.trivial B ℝ ι₀).TotalSpace,
    ↥(linePos (B := B) (ι₀ := ι₀))) :=
  ⟨fun p : (RealBundle.trivial B ℝ ι₀).TotalSpace =>
      ⟨(⟨p.1, (show (RealBundle.trivial B ℝ ι₀).Fiber p.1 from (1:ℝ))⟩ :
        (RealBundle.trivial B ℝ ι₀).TotalSpace), by
        show (0:ℝ) < (1:ℝ)
        norm_num⟩,
    by
      apply Continuous.subtype_mk
      exact (secConst (B := B) (ι₀ := ι₀) 1).continuous⟩

/-- The **inclusion of the positive half** `A₊ ↪ X`. -/
def iotaPrime : C(↥(linePos (B := B) (ι₀ := ι₀)),
    (RealBundle.trivial B ℝ ι₀).TotalSpace) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem sigmaPrime_apply (p : (RealBundle.trivial B ℝ ι₀).TotalSpace) :
    ((sigmaPrime (B := B) (ι₀ := ι₀) p : ↥(linePos (B := B) (ι₀ := ι₀))) :
      (RealBundle.trivial B ℝ ι₀).TotalSpace) =
        (⟨p.1, (show (RealBundle.trivial B ℝ ι₀).Fiber p.1 from (1:ℝ))⟩ :
          (RealBundle.trivial B ℝ ι₀).TotalSpace) := rfl

/-- The affine homotopy of the positive half, which stays positive. -/
def affineHomPos :
    C(unitInterval × ↥(linePos (B := B) (ι₀ := ι₀)), ↥(linePos (B := B) (ι₀ := ι₀))) :=
  ⟨fun tp : unitInterval × ↥(linePos (B := B) (ι₀ := ι₀)) =>
      ⟨affineHom (B := B) (ι₀ := ι₀) 1 (tp.1, tp.2.val), by
        have hp : (0:ℝ) < (show ℝ from tp.2.val.2) := tp.2.property
        have ht0 : (0:ℝ) ≤ (tp.1 : ℝ) := tp.1.2.1
        have ht1 : (tp.1 : ℝ) ≤ 1 := tp.1.2.2
        rw [affineHom_apply]
        show (0:ℝ) < ((1 - (tp.1 : unitInterval)) : ℝ) • (show ℝ from (1:ℝ)) +
          (tp.1 : ℝ) • (show ℝ from tp.2.val.2)
        rcases lt_or_eq_of_le ht1 with hlt | heq
        · have hpos : (0:ℝ) < 1 - (tp.1 : ℝ) := by linarith
          have h2 : (0:ℝ) < (1 - (tp.1 : ℝ)) • (show ℝ from (1:ℝ)) := by
            rw [smul_eq_mul, mul_one]; exact hpos
          have h3 : (0:ℝ) ≤ (tp.1 : ℝ) • (show ℝ from tp.2.val.2) :=
            smul_nonneg ht0 (le_of_lt hp)
          linarith
        · rw [heq]
          simpa using hp⟩,
    by
      apply Continuous.subtype_mk
      refine (affineHom (B := B) (ι₀ := ι₀) 1).continuous.comp ?_
      exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩

/-- **The positive half retracts onto `B × {1}`**: `σ' ∘ ι'` is homotopic to the identity of
`A₊`.  Consequently `ι'^* ∘ σ'^* = id` on cohomology, which is what identifies `ker σ₊^*` with
`ker i_{A₊}^*`. -/
theorem homotopic_sigmaPrime_iotaPrime :
    ContinuousMap.Homotopic ((sigmaPrime (B := B) (ι₀ := ι₀)).comp
      (iotaPrime (B := B) (ι₀ := ι₀)))
      (ContinuousMap.id ↥(linePos (B := B) (ι₀ := ι₀))) :=
  ⟨ContinuousMap.Homotopy.mk (affineHomPos (B := B) (ι₀ := ι₀))
    (fun p => by
      apply Subtype.ext
      exact affineHom_zero 1 p.val)
    (fun p => by
      apply Subtype.ext
      exact affineHom_one 1 p.val)⟩

/-- **`ι'^* ∘ σ'^* = id`**: the pullback along the inclusion of the positive half is a left inverse
of the pullback along the retraction. -/
theorem iotaPrime_cohmMap_sigmaPrime (k : ℕ) :
    ((CohMap (iotaPrime (B := B) (ι₀ := ι₀)) ℤ k).hom).comp
        ((CohMap (sigmaPrime (B := B) (ι₀ := ι₀)) ℤ k).hom) = LinearMap.id := by
  rw [← ModuleCat.hom_comp]
  rw [← CohMap_comp (iotaPrime (B := B) (ι₀ := ι₀)) (sigmaPrime (B := B) (ι₀ := ι₀)) ℤ k]
  rw [CohMap_homotopic (homotopic_sigmaPrime_iotaPrime (B := B) (ι₀ := ι₀)) ℤ k,
    CohMap_id, ModuleCat.hom_id]

/-! ## The retraction of the negative half onto `B × {-1}` -/

/-- The **retraction of the negative half onto `B × {-1}`**: the map `x ↦ ⟨x,-1⟩` of the total
space, viewed as a map into `A₋`. -/
def sigmaPrimeNeg : C((RealBundle.trivial B ℝ ι₀).TotalSpace,
    ↥(lineNeg (B := B) (ι₀ := ι₀))) :=
  ⟨fun p : (RealBundle.trivial B ℝ ι₀).TotalSpace =>
      ⟨(⟨p.1, (show (RealBundle.trivial B ℝ ι₀).Fiber p.1 from (-1:ℝ))⟩ :
        (RealBundle.trivial B ℝ ι₀).TotalSpace), by
        show (-1:ℝ) < 0
        norm_num⟩,
    by
      apply Continuous.subtype_mk
      exact (secConst (B := B) (ι₀ := ι₀) (-1)).continuous⟩

/-- The **inclusion of the negative half** `A₋ ↪ X`. -/
def iotaPrimeNeg : C(↥(lineNeg (B := B) (ι₀ := ι₀)),
    (RealBundle.trivial B ℝ ι₀).TotalSpace) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem sigmaPrimeNeg_apply (p : (RealBundle.trivial B ℝ ι₀).TotalSpace) :
    ((sigmaPrimeNeg (B := B) (ι₀ := ι₀) p : ↥(lineNeg (B := B) (ι₀ := ι₀))) :
      (RealBundle.trivial B ℝ ι₀).TotalSpace) =
        (⟨p.1, (show (RealBundle.trivial B ℝ ι₀).Fiber p.1 from (-1:ℝ))⟩ :
          (RealBundle.trivial B ℝ ι₀).TotalSpace) := rfl

/-- The affine homotopy of the negative half, which stays negative. -/
def affineHomNeg :
    C(unitInterval × ↥(lineNeg (B := B) (ι₀ := ι₀)), ↥(lineNeg (B := B) (ι₀ := ι₀))) :=
  ⟨fun tp : unitInterval × ↥(lineNeg (B := B) (ι₀ := ι₀)) =>
      ⟨affineHom (B := B) (ι₀ := ι₀) (-1) (tp.1, tp.2.val), by
        have ht0 : (0:ℝ) ≤ (tp.1 : unitInterval) := tp.1.2.1
        have ht1 : (tp.1 : ℝ) ≤ 1 := tp.1.2.2
        have hp : (show ℝ from tp.2.val.2) < 0 := tp.2.property
        rw [affineHom_apply]
        show ((1 - (tp.1 : unitInterval)) : ℝ) • (show ℝ from (-1:ℝ)) +
            (tp.1 : ℝ) • (show ℝ from tp.2.val.2) < 0
        rcases lt_or_eq_of_le ht1 with hlt | heq
        · have hpos : (0:ℝ) < ((1 - (tp.1 : unitInterval)) : ℝ) := by
            have hcoe : ((1 - (tp.1 : unitInterval)) : ℝ) = 1 - (tp.1 : ℝ) := rfl
            rw [hcoe]; linarith
          have h2 : ((1 - (tp.1 : unitInterval)) : ℝ) • (show ℝ from (-1:ℝ)) < 0 := by
            have heq' : ((1 - (tp.1 : unitInterval)) : ℝ) • (show ℝ from (-1:ℝ))
                = -(((1 - (tp.1 : unitInterval)) : ℝ)) := by rw [smul_eq_mul]; ring
            rw [heq']; linarith
          have h3 : (tp.1 : ℝ) • (show ℝ from tp.2.val.2) ≤ 0 :=
            smul_nonpos_of_nonneg_of_nonpos ht0 (le_of_lt hp)
          linarith
        · rw [heq]
          simpa using hp⟩,
    by
      apply Continuous.subtype_mk
      refine (affineHom (B := B) (ι₀ := ι₀) (-1)).continuous.comp ?_
      exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩

/-- **The negative half retracts onto `B × {-1}`**. -/
theorem homotopic_sigmaPrimeNeg_iotaPrimeNeg :
    ContinuousMap.Homotopic ((sigmaPrimeNeg (B := B) (ι₀ := ι₀)).comp
      (iotaPrimeNeg (B := B) (ι₀ := ι₀)))
      (ContinuousMap.id ↥(lineNeg (B := B) (ι₀ := ι₀))) :=
  ⟨ContinuousMap.Homotopy.mk (affineHomNeg (B := B) (ι₀ := ι₀))
    (fun p => by
      apply Subtype.ext
      exact affineHom_zero (-1) p.val)
    (fun p => by
      apply Subtype.ext
      exact affineHom_one (-1) p.val)⟩

/-- **`ι''^* ∘ σ''^* = id`** for the negative half. -/
theorem iotaPrimeNeg_cohmMap_sigmaPrimeNeg (k : ℕ) :
    ((CohMap (iotaPrimeNeg (B := B) (ι₀ := ι₀)) ℤ k).hom).comp
        ((CohMap (sigmaPrimeNeg (B := B) (ι₀ := ι₀)) ℤ k).hom) = LinearMap.id := by
  rw [← ModuleCat.hom_comp]
  rw [← CohMap_comp (iotaPrimeNeg (B := B) (ι₀ := ι₀)) (sigmaPrimeNeg (B := B) (ι₀ := ι₀)) ℤ k]
  rw [CohMap_homotopic (homotopic_sigmaPrimeNeg_iotaPrimeNeg (B := B) (ι₀ := ι₀)) ℤ k,
    CohMap_id, ModuleCat.hom_id]

end TrivLine

end

end Work.Thom
