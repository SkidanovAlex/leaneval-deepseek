import Mathlib
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.Thom.Orientation.step_fibRefl
import Submission.Work.Thom.Orientation.ReflSections
import Submission.Work.Thom.disjointCoverA

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Work.Gen

open Work.Thom Work.Thom.Orientation

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-! ## Detection of `H⁰(Sph Y 1)` by its two components

`Sph Y 1 = Y × S⁰` has the two open halves `Upos`, `Uneg` (the images of the two constant
sections `sigPos`, `sigNeg`), a disjoint open cover.  A class of `H⁰` vanishing on both halves
vanishes, and pulling back along `sigPos`/`sigNeg` is injective (the sections are homeomorphisms
onto the halves). -/

/-- Pulling back along `sigPosU : Y → Upos` is injective. -/
theorem CohMap_sigPosU_injective :
    Function.Injective ((CohMap (sigPosU (Y := Y)) ℤ 0).hom) := by
  have hone : ∀ x : Coh ℤ 0 ↥(Upos (Y := Y)),
      (CohMap (sigPosUinv (Y := Y)) ℤ 0).hom ((CohMap (sigPosU (Y := Y)) ℤ 0).hom x) = x := by
    intro x
    rw [CohMap_comp_apply (sigPosUinv (Y := Y)) (sigPosU (Y := Y)) ℤ 0 x,
      sigPosU_comp_sigPosUinv, CohMap_id]
    simp
  intro x y hxy
  calc x = (CohMap (sigPosUinv (Y := Y)) ℤ 0).hom
        ((CohMap (sigPosU (Y := Y)) ℤ 0).hom x) := (hone x).symm
    _ = (CohMap (sigPosUinv (Y := Y)) ℤ 0).hom
        ((CohMap (sigPosU (Y := Y)) ℤ 0).hom y) := by rw [hxy]
    _ = y := hone y

/-- Pulling back along `sigNegU : Y → Uneg` is injective. -/
theorem CohMap_sigNegU_injective :
    Function.Injective ((CohMap (sigNegU (Y := Y)) ℤ 0).hom) := by
  have hone : ∀ x : Coh ℤ 0 ↥(Uneg (Y := Y)),
      (CohMap (sigNegUinv (Y := Y)) ℤ 0).hom ((CohMap (sigNegU (Y := Y)) ℤ 0).hom x) = x := by
    intro x
    rw [CohMap_comp_apply (sigNegUinv (Y := Y)) (sigNegU (Y := Y)) ℤ 0 x,
      sigNegU_comp_sigNegUinv, CohMap_id]
    simp
  intro x y hxy
  calc x = (CohMap (sigNegUinv (Y := Y)) ℤ 0).hom
        ((CohMap (sigNegU (Y := Y)) ℤ 0).hom x) := (hone x).symm
    _ = (CohMap (sigNegUinv (Y := Y)) ℤ 0).hom
        ((CohMap (sigNegU (Y := Y)) ℤ 0).hom y) := by rw [hxy]
    _ = y := hone y

/-- The composite `sphProj ∘ sphIncl ∘ sigPos` is the identity. -/
theorem sphProj_comp_sphIncl_comp_sigPos :
    (sphProj (Y := Y)).comp ((sphIncl (Y := Y)).comp (sigPos (Y := Y)))
      = ContinuousMap.id Y := by
  apply ContinuousMap.ext
  intro y
  rfl

/-- The composite `sphProj ∘ sphIncl ∘ sigNeg` is the identity. -/
theorem sphProj_comp_sphIncl_comp_sigNeg :
    (sphProj (Y := Y)).comp ((sphIncl (Y := Y)).comp (sigNeg (Y := Y)))
      = ContinuousMap.id Y := by
  apply ContinuousMap.ext
  intro y
  rfl

/-- A degree-zero class on `Sph Y 1` vanishing on both halves is zero. -/
theorem eq_zero_of_sigPos_sigNeg (z : Coh ℤ 0 ↥(Sph Y 1))
    (h1 : (CohMap (sigPos (Y := Y)) ℤ 0).hom z = 0)
    (h2 : (CohMap (sigNeg (Y := Y)) ℤ 0).hom z = 0) : z = 0 := by
  have hkeyP : (CohMap (sigPosU (Y := Y)) ℤ 0).hom
      ((CohMap (subtypeMap (Upos (Y := Y))) ℤ 0).hom z)
      = (CohMap (sigPos (Y := Y)) ℤ 0).hom z := by
    rw [CohMap_comp_apply (sigPosU (Y := Y)) (subtypeMap (Upos (Y := Y))) ℤ 0 z]
    exact (congrArg (fun (g : C(Y, ↥(Sph Y 1))) => (CohMap g ℤ 0).hom z)
      (sigPos_eq_subtypeMap_comp_sigPosU (Y := Y))).symm
  have hkeyN : (CohMap (sigNegU (Y := Y)) ℤ 0).hom
      ((CohMap (subtypeMap (Uneg (Y := Y))) ℤ 0).hom z)
      = (CohMap (sigNeg (Y := Y)) ℤ 0).hom z := by
    rw [CohMap_comp_apply (sigNegU (Y := Y)) (subtypeMap (Uneg (Y := Y))) ℤ 0 z]
    exact (congrArg (fun (g : C(Y, ↥(Sph Y 1))) => (CohMap g ℤ 0).hom z)
      (sigNeg_eq_subtypeMap_comp_sigNegU (Y := Y))).symm
  have hU : (CohMap (subtypeMap (Upos (Y := Y))) ℤ 0).hom z = 0 := by
    apply CohMap_sigPosU_injective
    rw [hkeyP, h1, map_zero]
  have hV : (CohMap (subtypeMap (Uneg (Y := Y))) ℤ 0).hom z = 0 := by
    apply CohMap_sigNegU_injective
    rw [hkeyN, h2, map_zero]
  exact disjointCoverA (X := TopCat.of ↥(Sph Y 1)) (Upos (Y := Y)) (Uneg (Y := Y))
    isOpen_Upos isOpen_Uneg disjoint_Upos_Uneg union_Upos_Uneg 0 z hU hV

/-- A degree-zero class on `Sph Y 1` is determined by its two components. -/
theorem eq_of_sigPos_sigNeg {z z' : Coh ℤ 0 ↥(Sph Y 1)}
    (h1 : (CohMap (sigPos (Y := Y)) ℤ 0).hom z = (CohMap (sigPos (Y := Y)) ℤ 0).hom z')
    (h2 : (CohMap (sigNeg (Y := Y)) ℤ 0).hom z = (CohMap (sigNeg (Y := Y)) ℤ 0).hom z') :
    z = z' := by
  have hz : z - z' = 0 := eq_zero_of_sigPos_sigNeg (z - z')
    (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2, sub_self])
  exact sub_eq_zero.mp hz

/-! ## The connecting map kills the symmetrisation `u + fibSph^* u` -/

/-- **The connecting homomorphism of the pair `(Y × ℝ¹, Y × S⁰)` kills `u + fibSph^*u`.**  Indeed
that class is the restriction of a class of `Y × ℝ¹`: its two components agree. -/
theorem pairDelta_flip_one (u : Coh ℤ 0 ↥(Sph Y 1)) :
    (pairδC (Sph Y 1) 0).hom ((CohMap (fibSph (Y := Y)) ℤ 0).hom u + u) = 0 := by
  set a : Coh ℤ 0 Y := (CohMap (sigPos (Y := Y)) ℤ 0).hom u
    + (CohMap (sigNeg (Y := Y)) ℤ 0).hom u with ha
  set v : Coh ℤ 0 (Y × EuclideanSpace ℝ (Fin 1)) :=
    (CohMap (sphProj (Y := Y)) ℤ 0).hom a with hv
  have hPval : (CohMap (sigPos (Y := Y)) ℤ 0).hom
      ((CohMap (fibSph (Y := Y)) ℤ 0).hom u + u) = a := by
    rw [ha, map_add, CohMap_comp_apply (sigPos (Y := Y)) (fibSph (Y := Y)) ℤ 0 u,
      fibSph_comp_sigPos, add_comm]
  have hNval : (CohMap (sigNeg (Y := Y)) ℤ 0).hom
      ((CohMap (fibSph (Y := Y)) ℤ 0).hom u + u) = a := by
    rw [ha, map_add, CohMap_comp_apply (sigNeg (Y := Y)) (fibSph (Y := Y)) ℤ 0 u,
      fibSph_comp_sigNeg]
  have hPcalc : (CohMap (sigPos (Y := Y)) ℤ 0).hom ((CohMap (sphIncl (Y := Y)) ℤ 0).hom v) = a := by
    calc (CohMap (sigPos (Y := Y)) ℤ 0).hom ((CohMap (sphIncl (Y := Y)) ℤ 0).hom v)
        = (CohMap ((sphIncl (Y := Y)).comp (sigPos (Y := Y))) ℤ 0).hom v :=
          CohMap_comp_apply (sigPos (Y := Y)) (sphIncl (Y := Y)) ℤ 0 v
      _ = (CohMap ((sphIncl (Y := Y)).comp (sigPos (Y := Y))) ℤ 0).hom
            ((CohMap (sphProj (Y := Y)) ℤ 0).hom a) := by rw [hv]
      _ = (CohMap ((sphProj (Y := Y)).comp ((sphIncl (Y := Y)).comp (sigPos (Y := Y)))) ℤ 0).hom a :=
          CohMap_comp_apply ((sphIncl (Y := Y)).comp (sigPos (Y := Y))) (sphProj (Y := Y)) ℤ 0 a
      _ = (CohMap (ContinuousMap.id Y) ℤ 0).hom a := by
          rw [sphProj_comp_sphIncl_comp_sigPos]
      _ = a := by rw [CohMap_id]; simp
  have hNcalc : (CohMap (sigNeg (Y := Y)) ℤ 0).hom ((CohMap (sphIncl (Y := Y)) ℤ 0).hom v) = a := by
    calc (CohMap (sigNeg (Y := Y)) ℤ 0).hom ((CohMap (sphIncl (Y := Y)) ℤ 0).hom v)
        = (CohMap ((sphIncl (Y := Y)).comp (sigNeg (Y := Y))) ℤ 0).hom v :=
          CohMap_comp_apply (sigNeg (Y := Y)) (sphIncl (Y := Y)) ℤ 0 v
      _ = (CohMap ((sphIncl (Y := Y)).comp (sigNeg (Y := Y))) ℤ 0).hom
            ((CohMap (sphProj (Y := Y)) ℤ 0).hom a) := by rw [hv]
      _ = (CohMap ((sphProj (Y := Y)).comp ((sphIncl (Y := Y)).comp (sigNeg (Y := Y)))) ℤ 0).hom a :=
          CohMap_comp_apply ((sphIncl (Y := Y)).comp (sigNeg (Y := Y))) (sphProj (Y := Y)) ℤ 0 a
      _ = (CohMap (ContinuousMap.id Y) ℤ 0).hom a := by
          rw [sphProj_comp_sphIncl_comp_sigNeg]
      _ = a := by rw [CohMap_id]; simp
  have heq : (CohMap (sphIncl (Y := Y)) ℤ 0).hom v
      = (CohMap (fibSph (Y := Y)) ℤ 0).hom u + u :=
    eq_of_sigPos_sigNeg (hPcalc.trans hPval.symm) (hNcalc.trans hNval.symm)
  rw [← heq]
  have h := congrArg (fun (g : Coh ℤ 0 (Y × EuclideanSpace ℝ (Fin 1)) ⟶
      RelCoh ℤ (0 + 1) (Y × EuclideanSpace ℝ (Fin 1)) (Sph Y 1)) => g.hom v)
    (restrCoh_comp_pairδC (Sph Y 1) 0)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h
  exact h

/-! ## Linearity of the inductive step in the class -/

/-- `stepSph` is additive in the class (it is a preimage under a linear isomorphism). -/
theorem stepSph_neg (n : ℕ) (τ : RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Sph Y n)) :
    stepSph Y n (-τ) = - stepSph Y n τ := by
  apply (CleanA.capRelCohIso Y n n).1
  rw [map_neg, stepSph_spec Y n (-τ), stepSph_spec Y n τ, stepDisc, stepDisc, map_neg]

/-- The inductive step `step` is additive in the class. -/
theorem step_neg (n : ℕ) (τ : RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Sph Y n)) :
    step Y n (-τ) = - step Y n τ := by
  unfold step
  rw [stepSph_neg]
  simp only [map_neg]

/-! ## The reflection acts on the model class by `-1` -/

/-- **The base case `n = 1`.**  `Sph Y 1 = Y × S⁰`, and the reflection exchanges the two
components; the connecting map kills the symmetrised class. -/
theorem Mn_one_fibRefl :
    (relCohMap (fibRefl 1 Y) (Sph Y 1) (Sph Y 1) (fibRefl_mem_sph 1 Y) ℤ 1).hom (Mn 1 Y)
      = - Mn 1 Y := by
  set w : Coh ℤ 0 ↥(Sph Y 1) :=
    (CohMap (prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin 1)) (mSph 1)).symm ℤ 0).hom
      ((relToAbs ℤ (SphB Y 0) 0).hom (stepSph Y 0 (Mn 0 Y))) with hw
  have hstep : Mn 1 Y = (pairδC (Sph Y 1) 0).hom w := by
    rw [hw]
    rfl
  have hnat := pairDeltaNatural (fibRefl 1 Y) (Sph Y 1) (Sph Y 1) (fibRefl_mem_sph 1 Y) 0 w
  have hkey := pairDelta_flip_one (Y := Y) w
  calc (relCohMap (fibRefl 1 Y) (Sph Y 1) (Sph Y 1) (fibRefl_mem_sph 1 Y) ℤ 1).hom (Mn 1 Y)
      = (relCohMap (fibRefl 1 Y) (Sph Y 1) (Sph Y 1) (fibRefl_mem_sph 1 Y) ℤ 1).hom
          ((pairδC (Sph Y 1) 0).hom w) := by rw [hstep]
    _ = (pairδC (Sph Y 1) 0).hom ((CohMap (fibSph (Y := Y)) ℤ 0).hom w) := hnat
    _ = - (pairδC (Sph Y 1) 0).hom w := by
          rw [map_add] at hkey
          exact eq_neg_of_add_eq_zero_left hkey
    _ = - Mn 1 Y := by rw [hstep]

/-- **The reflection acts on the sphere-bundle model class by `-1`.** -/
theorem Mn_fibRefl (n : ℕ) (hn : 1 ≤ n) :
    (relCohMap (fibRefl n Y) (Sph Y n) (Sph Y n) (fibRefl_mem_sph n Y) ℤ n).hom (Mn n Y)
      = - Mn n Y := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0]
      exact Mn_one_fibRefl
    · have hk1 : 1 ≤ k := hkpos
      show (relCohMap (fibRefl (k+1) Y) (Sph Y (k+1)) (Sph Y (k+1))
          (fibRefl_mem_sph (k+1) Y) ℤ (k+1)).hom (step Y k (Mn k Y))
        = - step Y k (Mn k Y)
      rw [step_fibRefl k hk1 (Mn k Y), ih hk1, step_neg]

/-- **The reflection acts on the punctured model class by `-1`.** -/
theorem Mpun_fibRefl (n : ℕ) (hn : 1 ≤ n) :
    (relCohMap (fibRefl n Y) (Punct Y n) (Punct Y n) (fibRefl_mem_punct n Y) ℤ n).hom (Mpun n Y)
      = - Mpun n Y := by
  have hj : Function.Injective ((relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n)))
      (Sph Y n) (Punct Y n) (mem_Sph_punct Y n) ℤ n).hom) := (bijective_jMap Y n n).1
  have hsq : CategoryTheory.CategoryStruct.comp
        (relCohMap (fibRefl n Y) (Punct Y n) (Punct Y n) (fibRefl_mem_punct n Y) ℤ n)
        (relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n))) (Sph Y n) (Punct Y n)
          (mem_Sph_punct Y n) ℤ n)
      = CategoryTheory.CategoryStruct.comp
        (relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n))) (Sph Y n) (Punct Y n)
          (mem_Sph_punct Y n) ℤ n)
        (relCohMap (fibRefl n Y) (Sph Y n) (Sph Y n) (fibRefl_mem_sph n Y) ℤ n) := by
    rw [relCohMap_compA (Sph Y n) (Punct Y n) (Punct Y n)
        (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n))) (fibRefl n Y)
        (fun x hx => mem_Sph_punct Y n x hx) (fibRefl_mem_punct n Y)
        (fun x hx => fibRefl_mem_punct n Y x (mem_Sph_punct Y n x hx)) ℤ n]
    rw [relCohMap_compA (Sph Y n) (Sph Y n) (Punct Y n)
        (fibRefl n Y) (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n)))
        (fibRefl_mem_sph n Y) (fun x hx => mem_Sph_punct Y n x hx)
        (fun x hx => mem_Sph_punct Y n (fibRefl n Y x) (fibRefl_mem_sph n Y x hx)) ℤ n]
    exact relCohMap_congrA (Sph Y n) (Punct Y n)
      (by rw [ContinuousMap.comp_id, ContinuousMap.id_comp]) _ _ ℤ n
  have hsq_apply : (relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n)))
        (Sph Y n) (Punct Y n) (mem_Sph_punct Y n) ℤ n).hom
        ((relCohMap (fibRefl n Y) (Punct Y n) (Punct Y n) (fibRefl_mem_punct n Y) ℤ n).hom
          (Mpun n Y))
      = (relCohMap (fibRefl n Y) (Sph Y n) (Sph Y n) (fibRefl_mem_sph n Y) ℤ n).hom
          ((relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n)))
            (Sph Y n) (Punct Y n) (mem_Sph_punct Y n) ℤ n).hom (Mpun n Y)) := by
    have := congrArg (fun φ => φ.hom (Mpun n Y)) hsq
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  apply hj
  rw [map_neg, Mpun_spec n Y, hsq_apply, Mpun_spec n Y, Mn_fibRefl n hn]

/-! ## The main theorem -/

/-- The reflection `id × flipFst n` is the gauge of the constant gauge `flipFst n`. -/
theorem fibRefl_eq_gaugeEnd (n : ℕ) :
    fibRefl n Y = gaugeEnd (fun _ : Y => flipFst n) continuous_const := by
  apply ContinuousMap.ext
  intro p
  rfl

/-- **A gauge of everywhere negative determinant acts on the punctured model class by `-1`.** -/
theorem Mpun_gaugeEnd_neg (n : ℕ) (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y]
    (D : Y → Work.Thom.Gauge n) (hD : Continuous D)
    (hdet : ∀ y, LinearMap.det (D y).toLinearMap < 0) :
    (Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct Y n) (Work.Thom.Punct Y n)
      (Work.Thom.gaugeEnd_mem D hD
        (fun y => Work.Thom.gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_lt (hdet y))))
      ℤ n).hom (Work.Thom.Mpun n Y) = - (Work.Thom.Mpun n Y) := by
  let D' : Y → Gauge n := fun y => (D y).comp (flipFst n)
  have hD' : Continuous D' := hD.clm_comp continuous_const
  have hdet' : ∀ y, 0 < LinearMap.det (D' y).toLinearMap := by
    intro y
    have h1 : (D' y).toLinearMap = (D y).toLinearMap.comp (flipFst n).toLinearMap := rfl
    rw [h1, LinearMap.det_comp]
    have h2 : LinearMap.det (flipFst n).toLinearMap < 0 := flipFst_det n (by omega)
    nlinarith [hdet y, h2]
  have hgauge : gaugeEnd D hD
      = (gaugeEnd D' hD').comp (gaugeEnd (fun _ : Y => flipFst n) continuous_const) := by
    apply ContinuousMap.ext
    intro p
    apply Prod.ext
    · rfl
    · show D p.1 p.2 = D' p.1 (flipFst n p.2)
      show D p.1 p.2 = (D p.1).comp (flipFst n) (flipFst n p.2)
      rw [ContinuousLinearMap.comp_apply, flipFst_involutive]
  have hA : ∀ p ∈ Punct Y n, gaugeEnd (fun _ : Y => flipFst n) continuous_const p ∈ Punct Y n :=
    gaugeEnd_mem (fun _ : Y => flipFst n) continuous_const
      (fun y => gaugeEnd_bijective_of_det_ne_zero (flipFst n) (ne_of_lt (flipFst_det n (by omega))))
  have hB : ∀ p ∈ Punct Y n, gaugeEnd D' hD' p ∈ Punct Y n :=
    gaugeEnd_mem D' hD' (fun y => gaugeEnd_bijective_of_det_ne_zero (D' y) (ne_of_gt (hdet' y)))
  have hDmem : ∀ p ∈ Punct Y n, gaugeEnd D hD p ∈ Punct Y n :=
    gaugeEnd_mem D hD (fun y => gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_lt (hdet y)))
  have hgf : ∀ p ∈ Punct Y n,
      gaugeEnd D' hD' (gaugeEnd (fun _ : Y => flipFst n) continuous_const p) ∈ Punct Y n := by
    intro p hp
    have h1 : gaugeEnd D' hD' (gaugeEnd (fun _ : Y => flipFst n) continuous_const p)
        = gaugeEnd D hD p := by
      rw [hgauge]; rfl
    rw [h1]; exact hDmem p hp
  have hconst : (relCohMap (gaugeEnd (fun _ : Y => flipFst n) continuous_const)
      (Punct Y n) (Punct Y n) hA ℤ n).hom (Mpun n Y) = - Mpun n Y := by
    have heq : gaugeEnd (fun _ : Y => flipFst n) continuous_const = fibRefl n Y :=
      (fibRefl_eq_gaugeEnd n).symm
    rw [relCohMap_congrA (Punct Y n) (Punct Y n) heq hA (fibRefl_mem_punct n Y) ℤ n]
    exact Mpun_fibRefl n hn
  have hgoal : (relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) hDmem ℤ n).hom (Mpun n Y)
      = -Mpun n Y := by
    rw [relCohMap_congrA (Punct Y n) (Punct Y n) hgauge hDmem hgf ℤ n]
    rw [← relCohMap_compA_apply (Punct Y n) (Punct Y n) (Punct Y n)
          (gaugeEnd (fun _ : Y => flipFst n) continuous_const) (gaugeEnd D' hD') hA hB hgf ℤ n
          (Mpun n Y)]
    rw [Mpun_gaugeEnd_invariant n hn D' hD' hdet', hconst]
  exact hgoal

end

end Work.Gen
