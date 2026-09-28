import Mathlib
import Submission.Work.StemsB.Rat.CollarSplit
import Submission.Work.StemsB.Rat.collarSigma_cup_rat

/-!
# The collar transgression in the top degree `b - 1`

The transgression coefficient map of the collar pair is defined in
`Submission/Work/StemsB/Rat/CollarDefs.lean` as

  `Σ_m = Φ⁻¹ ∘ δ : H^{m+b}(C) → H^{m+1}(Y)`,  `m ≥ 0`,

i.e. it is indexed by the *shifted* degree `m`.  The blueprint's `C2` odd step
(`Submission/Work/Stems/EM_C2_RANGE_FINDING.md` §3/§5) needs the transgression of the
**fundamental class of the fibre**, of degree `b - 1` — that is `m = -1`, which the shifted
family cannot express — and with it the derivation property in that degree.  It is the one
missing input of the mutual induction of the `K(ℤ,n)` layer (the "deficit" of
`EM_C2_RANGE_FINDING.md`).

This file provides the missing degree:

* `collarDeltaLow` — the connecting homomorphism `δ : H^{b-1}(C) → H^b(Q,C)`;
* `collarSigmaLow` — `Σ : H^{b-1}(C) → H^0(Y)`, with the defining property `Φ_0 (Σ x) = δ x`
  (`collarSigmaLow_spec`);
* `collarSPartLow`, `collarDelta_collarSPartLow`, `collarSplitLow` — the `s`-splitting
  `x - π^*(Σ x) ⌣ s ∈ im i^*` in degree `b - 1`, the analogue of
  `Work.StemsB.Rat.collarSplit`.

The derivation property with a factor of degree `b - 1` (`collarSigma_cup_low`) and the
consequences for the Wang transgression of a fibration over a sphere are built on these in
`Submission/Work/StemsB/Rat/CollarSigmaLowCup.lean`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000

namespace Work.StemsB.Rat

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- The degree comparison `(b - 1) + 1 = b`. -/
theorem lowCast (b : ℕ) (hb : 1 ≤ b) : (b - 1) + 1 = b := Nat.sub_add_cancel hb

/-! ## The connecting homomorphism in degree `b - 1` -/

/-- **The connecting homomorphism of the collar pair in degree `b - 1`**: the connecting map
`δ : H^{b-1}(C) → H^{(b-1)+1}(Q,C)`, transported to degree `b`. -/
noncomputable def collarDeltaLow (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] :
    (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1) →ₗ[ℚ]
      Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
  ((eqToIso (congrArg (fun t => (Work.Cohomology.relComplex ℚ
      (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)).homology t)
      (lowCast b hb))).toLinearEquiv.toLinearMap).comp
    ((Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y) (b - 1)).hom)

/-- The computation rule of `collarDeltaLow`. -/
theorem collarDeltaLow_apply (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (x : (Work.Cohomology.singularCochainComplex ℚ
      (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1)) :
    collarDeltaLow b hb Y x
      = (eqToHom (congrArg (fun t => (Work.Cohomology.relComplex ℚ
          (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)).homology t)
          (lowCast b hb)))
        ((Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y) (b - 1)).hom x) := rfl

/-! ## The transgression in degree `b - 1` -/

/-- The transport `H^b(Q,C) → H^{0+b}(Q,C)` used to compare the head of `collarDeltaLow` with the
target of the Thom map `collarPhi b τ 0`. -/
noncomputable def relCohZeroAdd (b : ℕ) (Y : Type) [TopologicalSpace Y] :
    Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) →ₗ[ℚ]
      Work.Thom.RelCoh ℚ (0 + b) (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
  ((eqToIso (congrArg (fun t => (Work.Cohomology.relComplex ℚ
      (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)).homology t)
      (Nat.zero_add b).symm)).toLinearEquiv.toLinearMap)

/-- **The transgression coefficient map of the collar pair in the top degree `b - 1`**:
`Σ x ∈ H^0(Y)` is the class with `π^*(Σ x) ⌣ τ = δ x`. -/
noncomputable def collarSigmaLow (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ) :
    (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1) →ₗ[ℚ]
      Work.Thom.Coh ℚ 0 Y :=
  (LinearEquiv.ofBijective (collarPhi (Y := Y) b τ 0) (hτ 0)).symm.toLinearMap.comp
    ((relCohZeroAdd (Y := Y) b).comp (collarDeltaLow (Y := Y) b hb))

/-- **The defining property** of the top-degree transgression coefficient map: `Φ_0 (Σ x) = δ x`,
up to the definitional identity `0 + b = b` on the target degree. -/
theorem collarSigmaLow_spec (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (x : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1)) :
    collarPhi (Y := Y) b τ 0 (collarSigmaLow b hb Y τ hτ x)
      = relCohZeroAdd (Y := Y) b (collarDeltaLow (Y := Y) b hb x) := by
  show (LinearEquiv.ofBijective (collarPhi (Y := Y) b τ 0) (hτ 0))
      ((LinearEquiv.ofBijective (collarPhi (Y := Y) b τ 0) (hτ 0)).symm
        (relCohZeroAdd (Y := Y) b (collarDeltaLow (Y := Y) b hb x))) = _
  exact LinearEquiv.apply_symm_apply _ _

/-! ## The `s`-part in degree `b - 1` -/

/-- **The `s`-part of a class of the collar, in the top degree `b - 1`**:
`π^*(Σ x) ⌣ s`, where `s` is the suspension class. -/
noncomputable def collarSPartLow (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1)) :
    (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1) →ₗ[ℚ]
      (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1) :=
  ((eqToIso (congrArg (fun t => Work.Cohomology.singularCohomology ℚ t
      (TopCat.of ↥(sphLoopCollarProd b Y))) (Nat.zero_add (b - 1)))).toLinearEquiv.toLinearMap).comp
    (((LinearMap.applyₗ (R := ℚ)
        (M := Work.Cohomology.singularCohomology ℚ (b - 1)
          (TopCat.of ↥(sphLoopCollarProd b Y)))
        (M₂ := Work.Cohomology.singularCohomology ℚ (0 + (b - 1))
          (TopCat.of ↥(sphLoopCollarProd b Y))) s).comp
      (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of ↥(sphLoopCollarProd b Y)))
        0 (b - 1))).comp
      ((collarProjC (Y := Y) b 0).comp (collarSigmaLow b hb Y τ hτ)))

/-- **The computation rule of `collarSPartLow`.** -/
theorem collarSPartLow_apply (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1))
    (x : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1)) :
    collarSPartLow b hb Y τ hτ s x
      = (eqToHom (congrArg (fun t => Work.Cohomology.singularCohomology ℚ t
            (TopCat.of ↥(sphLoopCollarProd b Y))) (Nat.zero_add (b - 1))))
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of ↥(sphLoopCollarProd b Y)))
              0 (b - 1))
            (collarProjC (Y := Y) b 0 (collarSigmaLow b hb Y τ hτ x)) s) := rfl


/-- A chain of four degree transports whose composite degree is the identity cancels. -/
private lemma cast_four_cancel (K : CochainComplex (ModuleCat ℚ) ℕ) {a b c d : ℕ}
    (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) (h₄ : d = a) (y : K.homology a) :
    (eqToHom (congrArg (fun t => K.homology t) h₄)
        (eqToHom (congrArg (fun t => K.homology t) h₃)
          (eqToHom (congrArg (fun t => K.homology t) h₂)
            (eqToHom (congrArg (fun t => K.homology t) h₁) y)))) = y := by
  have e₁ : (eqToHom (congrArg (fun t => K.homology t) h₂)
        (eqToHom (congrArg (fun t => K.homology t) h₁) y))
      = eqToHom (congrArg (fun t => K.homology t) (h₁.trans h₂)) y :=
    Work.StemsB.Rat.eqToHom_homology_trans_apply (K := K) (h := h₁) (h' := h₂) (z := y)
  have e₂ : (eqToHom (congrArg (fun t => K.homology t) h₃)
        (eqToHom (congrArg (fun t => K.homology t) (h₁.trans h₂)) y))
      = eqToHom (congrArg (fun t => K.homology t) ((h₁.trans h₂).trans h₃)) y :=
    Work.StemsB.Rat.eqToHom_homology_trans_apply (K := K) (h := h₁.trans h₂) (h' := h₃) (z := y)
  have e₃ : (eqToHom (congrArg (fun t => K.homology t) h₄)
        (eqToHom (congrArg (fun t => K.homology t) ((h₁.trans h₂).trans h₃)) y))
      = eqToHom (congrArg (fun t => K.homology t) (((h₁.trans h₂).trans h₃).trans h₄)) y :=
    Work.StemsB.Rat.eqToHom_homology_trans_apply (K := K)
      (h := (h₁.trans h₂).trans h₃) (h' := h₄) (z := y)
  rw [e₁, e₂, e₃]
  exact Work.StemsB.Rat.eqToHom_homology_self K a (((h₁.trans h₂).trans h₃).trans h₄) y

/-! ## The `δ`-computation in the top degree -/

/-- **The `δ`-computation of the `s`-part in degree `b - 1`**: `δ (π^*(Σ x) ⌣ s) = δ x`, which is
the defining property of `Σ` combined with the one-sided Leibniz rule for the connecting
homomorphism.  This is the analogue of `Work.StemsB.Rat.collarDelta_collarSPart` for the top
degree `b - 1`. -/
theorem pairδ_collarSPartLow (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1))
    (hs : CollarTransgresses b hb (Y := Y) s τ)
    (x : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1)) :
    (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom
        (collarSPartLow b hb Y τ hτ s x)
      = (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom x := by
  have hk : 0 + (b - 1) = b - 1 := Nat.zero_add (b - 1)
  have hba : (b - 1) + 1 = b := lowCast b hb
  have hK1 : (0 + (b - 1)) + 1 = (b - 1) + 1 := congrArg (fun t => t + 1) hk
  have hK2 : 0 + b = 0 + ((b - 1) + 1) := congrArg (fun t => 0 + t) hba.symm
  set xq := (Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom
    (collarSigmaLow b hb Y τ hτ x) with hxq
  set w := (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) 0 (b - 1))
      ((HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (CollQ b Y) (CollA b Y)) 0).hom xq)
      s with hw
  have hσ : (Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) 0 b) xq τ
      = relCohZeroAdd (Y := Y) b (collarDeltaLow (Y := Y) b hb x) := by
    have h1 := collarSigmaLow_spec b hb Y τ hτ x
    rw [collarPhi_apply, mixedCupC_eq_mixedCup] at h1
    simpa only [hxq] using h1
  have hder := Work.StemsB.pairDelta_mixedCup_general_R ℚ (CollQ b Y) (CollA b Y) 0 (b - 1) xq s
  have hsp : collarSPartLow b hb Y τ hτ s x
      = eqToHom (congrArg (fun t => (CollKC b Y).homology t) hk) w := by
    rw [collarSPartLow_apply, collarProjC_eq_restr_apply]
    rw [← hxq, ← hw]
    rfl
  have htrans : (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom s
      = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hba.symm) τ := hs
  have hder' : (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (0 + (b - 1))).hom w
      = (Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) 0 ((b - 1) + 1)) xq
          ((Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom s) := by
    rw [hw]
    rw [hder, pow_zero, one_smul]
  have hσ' : (Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) 0 b) xq τ
      = eqToHom (congrArg (fun t => (CollRC b Y).homology t) (Nat.zero_add b).symm)
          (collarDeltaLow (Y := Y) b hb x) := hσ
  have hcd : collarDeltaLow (Y := Y) b hb x
      = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hba)
          ((Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom x) := rfl
  have congr_T1 : ∀ {u v : (CollRC b Y).homology ((0 + (b - 1)) + 1)}, u = v →
      eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK1) u
        = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK1) v :=
    fun h => congrArg _ h
  have congr_T1' : ∀ {u v : (CollRC b Y).homology (0 + ((b - 1) + 1))}, u = v →
      eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK1) u
        = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK1) v :=
    fun h => congrArg _ h
  calc (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom
        (collarSPartLow b hb Y τ hτ s x)
      = (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom
          (eqToHom (congrArg (fun t => (CollKC b Y).homology t) hk) w) := by rw [hsp]
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK1)
          ((Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (0 + (b - 1))).hom w) :=
        Work.StemsB.Rat.pairδ_eqToHom_homology (X := CollQ b Y) (A := CollA b Y)
          (i := 0 + (b - 1)) (i' := b - 1) hk w
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK1)
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) 0 ((b - 1) + 1)) xq
            ((Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom s)) :=
        congr_T1 hder'
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK1)
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) 0 ((b - 1) + 1)) xq
            (eqToHom (congrArg (fun t => (CollRC b Y).homology t) hba.symm) τ)) :=
        congr_T1 (by rw [htrans])
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK1)
          (eqToHom (congrArg (fun t => (CollRC b Y).homology (0 + t)) hba.symm)
            ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) 0 b) xq τ)) :=
        congr_T1 (Work.StemsB.Rat.mixedCup_eqToHom_homology (CollQ b Y) (CollA b Y) 0 hba.symm xq τ)
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK1)
          (eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK2)
            ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) 0 b) xq τ)) := by
        rw [show (congrArg (fun t => (CollRC b Y).homology (0 + t)) hba.symm)
            = (congrArg (fun t => (CollRC b Y).homology t) hK2) from
          Subsingleton.elim _ _]
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK1)
          (eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK2)
            (eqToHom (congrArg (fun t => (CollRC b Y).homology t) (Nat.zero_add b).symm)
              (collarDeltaLow (Y := Y) b hb x))) := by
        rw [hσ']
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK1)
          (eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK2)
            (eqToHom (congrArg (fun t => (CollRC b Y).homology t) (Nat.zero_add b).symm)
              (eqToHom (congrArg (fun t => (CollRC b Y).homology t) hba)
                ((Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom x)))) := by
        rw [hcd]
    _ = (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom x :=
        cast_four_cancel (CollRC b Y) hba (Nat.zero_add b).symm hK2 hK1 _

/-- The `collarDeltaLow` form of the `δ`-computation. -/
theorem collarDeltaLow_collarSPartLow (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1))
    (hs : CollarTransgresses b hb (Y := Y) s τ)
    (x : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1)) :
    collarDeltaLow (Y := Y) b hb (collarSPartLow b hb Y τ hτ s x)
      = collarDeltaLow (Y := Y) b hb x :=
  congrArg (fun w : (Work.Cohomology.relComplex ℚ (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y)).homology ((b - 1) + 1) =>
      (eqToHom (congrArg (fun t => (Work.Cohomology.relComplex ℚ
        (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)).homology t) (lowCast b hb))) w)
    (pairδ_collarSPartLow b hb Y τ hτ s hs x)

/-- **The exactness of the collar pair in degree `b - 1`**: the kernel of the connecting
homomorphism `collarDeltaLow` is the range of the restriction. -/
theorem collarDeltaLow_ker (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] :
    LinearMap.ker (collarDeltaLow (Y := Y) b hb)
      = LinearMap.range (collarRestr (Y := Y) b (b - 1)) := by
  have h := ShortComplex.Exact.moduleCat_range_eq_ker
    (Work.Cohomology.pair_exact₃ ℚ (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y) (b - 1))
  have hker : LinearMap.ker (collarDeltaLow (Y := Y) b hb)
      = LinearMap.ker ((Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y) (b - 1)).hom) :=
    LinearEquiv.ker_comp
      ((eqToIso (congrArg (fun t => (Work.Cohomology.relComplex ℚ
        (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)).homology t)
        (lowCast b hb))).toLinearEquiv)
      ((Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y) (b - 1)).hom)
  rw [hker]
  rw [show LinearMap.range (collarRestr (Y := Y) b (b - 1))
      = LinearMap.range (HomologicalComplex.homologyMap
          (Work.Cohomology.restr ℚ (TopCat.of (↥(sphLoopBig b) × Y))
            (sphLoopCollarProd b Y)) (b - 1)).hom from rfl]
  exact h.symm

/-- **The splitting of the collar cohomology in the top degree `b - 1`.**  For every class `x` of
degree `b - 1`, `x - π^*(Σ x) ⌣ s` lies in the image of the restriction `H^{b-1}(Q) → H^{b-1}(C)`.
This is the degree-`b - 1` analogue of `Work.StemsB.Rat.collarSplit`. -/
theorem collarSplitLow (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1))
    (hs : CollarTransgresses b hb (Y := Y) s τ)
    (x : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1)) :
    ∃ a : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of (↥(sphLoopBig b) × Y))).homology (b - 1),
      x - collarSPartLow b hb (Y := Y) τ hτ s x = collarRestr (Y := Y) b (b - 1) a := by
  have hmem : x - collarSPartLow b hb (Y := Y) τ hτ s x
      ∈ LinearMap.ker (collarDeltaLow (Y := Y) b hb) := by
    show collarDeltaLow (Y := Y) b hb (x - collarSPartLow b hb (Y := Y) τ hτ s x) = 0
    rw [map_sub, collarDeltaLow_collarSPartLow b hb Y τ hτ s hs x, sub_self]
  rw [collarDeltaLow_ker b hb Y] at hmem
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha.symm⟩

end

end Work.StemsB.Rat
