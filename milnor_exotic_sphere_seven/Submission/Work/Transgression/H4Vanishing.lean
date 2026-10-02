import Mathlib
import Submission.Work.Transgression.Pieces
import Submission.Work.Cohomology.sphere_compl_singleton_contractible
import Submission.Work.Cohomology.MVCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# `H⁴` of the two pieces of the punctured total space vanishes

This module proves `Work.Transgression.H4Vanishing`: the fourth cohomology of each of the two
pieces `pU a b`, `pV a b` of the Mayer–Vietoris cover of the punctured total space
`E ∖ 0` of `clutchBundle a b` vanishes.

The reason is that each piece is a product of a contractible space with the punctured `ℝ⁴`: the
local trivialisation over the chart `baseSet i` (`hemi0`, resp. `hemi1`) identifies the piece with
`↥(baseSet i) × (ℝ⁴ ∖ 0)`, both charts of `S⁴ = OnePoint ℝ⁴` are contractible
(`HemiContractible0`, `HemiContractible1`), and `ℝ⁴ ∖ 0` is homotopy equivalent to `S³`, whose
`H⁴` vanishes (`PuncturedH4Vanishing`).

## Contents

* `PuncturedH4Vanishing` — `H⁴(ℝ⁴ ∖ 0; ℤ) = 0` (via `ℝ⁴∖0 ≃ S³` and `H⁴(S³) = 0`);
* `HemiContractible0`, `HemiContractible1` — the two charts of `S⁴` are contractible;
* `Work.Transgression.H4.pieceHomeo` — the trivialisation over a chart, as a homeomorphism
  `↥(piece i a b) ≃ₜ ↥(baseSet i) × ↥(ℝ⁴ ∖ 0)`;
* `Work.Transgression.H4.pUHomeo`, `Work.Transgression.H4.pVHomeo` — its two specialisations;
* `H4Vanishing` — the statement.
-/

namespace Work.Transgression

open Work.TangentClasses Work.Thom

noncomputable section

/-! ## 1. `H⁴` of the punctured `ℝ⁴` vanishes -/

/-- **`H⁴(ℝ⁴ ∖ 0; ℤ) = 0`**: the punctured `ℝ⁴` is homotopy equivalent to `S³`, and `H⁴` of a
`3`-sphere vanishes. -/
theorem PuncturedH4Vanishing :
    Subsingleton ↥(Work.Thom.Coh ℤ 4 {v : EuclideanSpace ℝ (Fin 4) // v ≠ 0}) := by
  obtain ⟨e⟩ := Work.Cohomology.punctured_homotopyEquiv_sphere (EuclideanSpace ℝ (Fin 4))
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv e 4
  have hz : CategoryTheory.Limits.IsZero
      (Work.Thom.Coh ℤ 4 (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :=
    Work.Cohomology.sphereCohomologyZero 3 4 (by norm_num) (by norm_num) (by norm_num)
  exact (Equiv.subsingleton_congr iso.toLinearEquiv.toEquiv).mpr
    (ModuleCat.isZero_iff_subsingleton.mp hz)

/-! ## 2. The two charts of `S⁴` are contractible -/

/-- **The chart `hemi0 = {p ≠ ∞}` of `S⁴ = OnePoint ℝ⁴` is contractible**: `coord0` is a
homeomorphism onto `ℝ⁴`. -/
theorem HemiContractible0 : ContractibleSpace ↥(Work.Agree.hemi0) := by
  have e : ↥(Work.Agree.hemi0) ≃ₜ EuclideanSpace ℝ (Fin 4) :=
    { toFun := fun p => Work.Agree.coord0 (p : Work.Agree.S4)
      invFun := fun v => ⟨(v : Work.Agree.S4), OnePoint.coe_ne_infty v⟩
      left_inv := fun p => by
        apply Subtype.ext
        exact Work.Agree.coord0_mem p.2
      right_inv := fun v => Work.Agree.coord0_some v
      continuous_toFun := Work.Agree.continuous_coord0
      continuous_invFun := Continuous.subtype_mk OnePoint.isOpenEmbedding_coe.continuous
        (fun v => OnePoint.coe_ne_infty v) }
  exact Homeomorph.contractibleSpace e

/-- **The chart `hemi1 = {p ≠ ↑0}` of `S⁴` is contractible**: it is `S⁴` minus a point, and a
sphere minus a point is contractible. -/
theorem HemiContractible1 : ContractibleSpace ↥(Work.Agree.hemi1) := by
  have hc : ContractibleSpace
      {y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 //
        y ≠ Work.Agree.homeoS4Sphere (↑(0 : EuclideanSpace ℝ (Fin 4)) : Work.Agree.S4)} :=
    Work.Cohomology.sphere_compl_singleton_contractible (EuclideanSpace ℝ (Fin 5)) _
  haveI := hc
  have e : ↥(Work.Agree.hemi1) ≃ₜ
      {y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 //
        y ≠ Work.Agree.homeoS4Sphere (↑(0 : EuclideanSpace ℝ (Fin 4)) : Work.Agree.S4)} :=
    Homeomorph.subtype Work.Agree.homeoS4Sphere (fun x => by
      constructor
      · intro hx hh
        exact hx (Work.Agree.homeoS4Sphere.injective hh)
      · intro hx hh
        exact hx (by rw [hh]))
  exact Homeomorph.contractibleSpace e

/-! ## 3. The trivialisation over a chart, as a homeomorphism onto a product

Everything is phrased for an arbitrary index `i : Bool`, with `baseSet i` the corresponding chart;
`i = false` gives the piece `pU` (over `hemi0`) and `i = true` the piece `pV` (over `hemi1`). -/

namespace H4

/-- The punctured `ℝ⁴`, the fibre model of each trivialised piece. -/
abbrev Punc : Type := {v : EuclideanSpace ℝ (Fin 4) // v ≠ 0}

/-- The chart-`i` fibre coordinate of a point of the total space. -/
abbrev chartI (i : Bool) (a b : ℤ) (p : (Zb a b).TotalSpace) : EuclideanSpace ℝ (Fin 4) :=
  ((Zb a b).localTriv i p).2

/-- The part of the punctured total space lying over the chart `baseSet i`. -/
abbrev piece (i : Bool) (a b : ℤ) : Set ↥(zeroComplement (Zb a b)) :=
  {p | (p : (Zb a b).TotalSpace).1 ∈ (Zb a b).baseSet i}

/-- The chart-`i` fibre coordinate is continuous on the piece over `baseSet i`. -/
lemma continuousOn_chartI (i : Bool) (a b : ℤ) :
    ContinuousOn (chartI i a b) {p : (Zb a b).TotalSpace | p.1 ∈ (Zb a b).baseSet i} := by
  have h := ((Zb a b).localTriv i).continuousOn
  have hs : {p : (Zb a b).TotalSpace | p.1 ∈ (Zb a b).baseSet i}
      ⊆ ((Zb a b).localTriv i).source := by
    intro p hp
    rw [VectorBundleCore.mem_localTriv_source]
    exact hp
  exact continuous_snd.continuousOn.comp (h.mono hs) (fun _ _ => Set.mem_univ _)

/-- On the punctured total space and over `baseSet i`, the chart-`i` fibre coordinate does not
vanish. -/
lemma chartI_ne_zero (i : Bool) (a b : ℤ) (q : ↥(zeroComplement (Zb a b)))
    (hp : (q : (Zb a b).TotalSpace).1 ∈ (Zb a b).baseSet i) :
    chartI i a b (q : (Zb a b).TotalSpace) ≠ 0 := by
  intro h
  have h1 : fibreNorm (Zb a b) (q : (Zb a b).TotalSpace) = 0 := by
    rw [fibreNorm_localTriv (isEuclidean_clutchBundle a b) i _ hp]
    change ‖chartI i a b (q : (Zb a b).TotalSpace)‖ = 0
    rw [h, norm_zero]
  exact (SphereInDisc.mem_zeroComplement_iff_fibreNorm_ne_zero (Zb a b) _).mp q.2 h1

/-- The point of the total space with base `x` and chart-`i` fibre coordinate `v`, transported
along the inverse of the trivialisation `localTriv i`. -/
abbrev symmAt (i : Bool) (a b : ℤ) (q : ↥((Zb a b).baseSet i) × Punc) : (Zb a b).TotalSpace :=
  ((Zb a b).localTriv i).toOpenPartialHomeomorph.symm (q.1.1, q.2.1)

lemma mem_target_lt (i : Bool) (a b : ℤ) (q : ↥((Zb a b).baseSet i) × Punc) :
    (q.1.1, q.2.1) ∈ ((Zb a b).localTriv i).target := ⟨q.1.2, Set.mem_univ _⟩

lemma base_symmAt (i : Bool) (a b : ℤ) (q : ↥((Zb a b).baseSet i) × Punc) :
    (symmAt i a b q).1 = q.1.1 :=
  Bundle.Trivialization.proj_symm_apply _ (mem_target_lt i a b q)

lemma chartI_symmAt (i : Bool) (a b : ℤ) (q : ↥((Zb a b).baseSet i) × Punc) :
    chartI i a b (symmAt i a b q) = q.2.1 :=
  congrArg Prod.snd
    (Bundle.Trivialization.apply_symm_apply ((Zb a b).localTriv i) (mem_target_lt i a b q))

lemma mem_zeroComplement_symm (i : Bool) (a b : ℤ) (q : ↥((Zb a b).baseSet i) × Punc) :
    symmAt i a b q ∈ zeroComplement (Zb a b) := by
  rw [SphereInDisc.mem_zeroComplement_iff_fibreNorm_ne_zero,
    fibreNorm_localTriv (isEuclidean_clutchBundle a b) i _ (by rw [base_symmAt]; exact q.1.2)]
  change ‖chartI i a b (symmAt i a b q)‖ ≠ 0
  rw [chartI_symmAt]
  exact norm_ne_zero_iff.mpr q.2.2

lemma mem_piece_symm (i : Bool) (a b : ℤ) (q : ↥((Zb a b).baseSet i) × Punc) :
    (⟨symmAt i a b q, mem_zeroComplement_symm i a b q⟩ : ↥(zeroComplement (Zb a b))) ∈
      piece i a b := by
  show (symmAt i a b q).1 ∈ (Zb a b).baseSet i
  rw [base_symmAt]
  exact q.1.2

/-- The forward map of the piece homeomorphism: base and chart coordinate. -/
abbrev pieceToFun (i : Bool) (a b : ℤ) (p : ↥(piece i a b)) :
    ↥((Zb a b).baseSet i) × Punc :=
  (⟨(p : (Zb a b).TotalSpace).1, p.2⟩,
   ⟨chartI i a b (p : (Zb a b).TotalSpace),
     chartI_ne_zero i a b (p : ↥(zeroComplement (Zb a b))) p.2⟩)

/-- The inverse map of the piece homeomorphism: the inverse trivialisation. -/
abbrev pieceInvFun (i : Bool) (a b : ℤ) (q : ↥((Zb a b).baseSet i) × Punc) :
    ↥(piece i a b) :=
  ⟨⟨symmAt i a b q, mem_zeroComplement_symm i a b q⟩, mem_piece_symm i a b q⟩

lemma pieceTo_inv (i : Bool) (a b : ℤ) (q : ↥((Zb a b).baseSet i) × Punc) :
    pieceToFun i a b (pieceInvFun i a b q) = q := by
  apply Prod.ext
  · exact Subtype.ext (base_symmAt i a b q)
  · exact Subtype.ext (chartI_symmAt i a b q)

lemma pieceInv_to (i : Bool) (a b : ℤ) (p : ↥(piece i a b)) :
    pieceInvFun i a b (pieceToFun i a b p) = p := by
  have hsrc : (p : (Zb a b).TotalSpace) ∈ ((Zb a b).localTriv i).source := by
    rw [VectorBundleCore.mem_localTriv_source]; exact p.2
  apply Subtype.ext
  apply Subtype.ext
  exact Bundle.Trivialization.symm_apply_apply ((Zb a b).localTriv i) hsrc

lemma continuous_pieceToFun (i : Bool) (a b : ℤ) : Continuous (pieceToFun i a b) :=
  Continuous.prodMk
    (Continuous.subtype_mk (((Zb a b).continuous_proj).comp
      (continuous_subtype_val.comp continuous_subtype_val))
      (fun p : ↥(piece i a b) => p.2))
    (Continuous.subtype_mk
      ((continuousOn_chartI i a b).comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val)
        (fun p : ↥(piece i a b) => p.2))
      (fun p : ↥(piece i a b) => chartI_ne_zero i a b _ p.2))

lemma continuous_symmAt (i : Bool) (a b : ℤ) : Continuous (symmAt i a b) := by
  have h₁ : Continuous fun q : ↥((Zb a b).baseSet i) × Punc =>
      (⟨q.1.1, ((Zb a b).localTriv i).symm q.1.1 q.2.1⟩ : (Zb a b).TotalSpace) :=
    (Bundle.Trivialization.continuousOn_symm ((Zb a b).localTriv i)).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun q => ⟨q.1.2, Set.mem_univ _⟩)
  exact h₁.congr (fun q => Bundle.Trivialization.mk_symm ((Zb a b).localTriv i) q.1.2 q.2.1)

lemma continuous_pieceInvFun (i : Bool) (a b : ℤ) : Continuous (pieceInvFun i a b) :=
  Continuous.subtype_mk (Continuous.subtype_mk (continuous_symmAt i a b)
    (fun q => mem_zeroComplement_symm i a b q)) (fun q => mem_piece_symm i a b q)

/-- **The trivialisation over a chart is a homeomorphism onto the product of the chart with the
punctured `ℝ⁴`.** -/
noncomputable def pieceHomeo (i : Bool) (a b : ℤ) :
    ↥(piece i a b) ≃ₜ ↥((Zb a b).baseSet i) × Punc :=
  { toFun := pieceToFun i a b
    invFun := pieceInvFun i a b
    left_inv := pieceInv_to i a b
    right_inv := pieceTo_inv i a b
    continuous_toFun := continuous_pieceToFun i a b
    continuous_invFun := continuous_pieceInvFun i a b }

/-! ## 4. The two specialisations -/

lemma piece_false_eq_pU (a b : ℤ) : piece false a b = pU a b := by
  have h : (Zb a b).baseSet false = Work.Agree.hemi0 := by
    rw [Work.Agree.clutchBundle_baseSet]; simp
  ext p
  rw [Set.mem_ofPred_eq, mem_pU, h]

lemma piece_true_eq_pV (a b : ℤ) : piece true a b = pV a b := by
  have h : (Zb a b).baseSet true = Work.Agree.hemi1 := by
    rw [Work.Agree.clutchBundle_baseSet]; simp
  ext p
  rw [Set.mem_ofPred_eq, mem_pV, h]

lemma baseSet_false_eq_hemi0 (a b : ℤ) : (Zb a b).baseSet false = Work.Agree.hemi0 := by
  rw [Work.Agree.clutchBundle_baseSet]; simp

lemma baseSet_true_eq_hemi1 (a b : ℤ) : (Zb a b).baseSet true = Work.Agree.hemi1 := by
  rw [Work.Agree.clutchBundle_baseSet]; simp

/-- The piece over `hemi0` is a product of `hemi0` with the punctured `ℝ⁴`. -/
noncomputable def pUHomeo (a b : ℤ) : ↥(pU a b) ≃ₜ ↥(Work.Agree.hemi0) × Punc :=
  (Homeomorph.setCongr (piece_false_eq_pU a b)).symm.trans
    ((pieceHomeo false a b).trans
      ((Homeomorph.setCongr (baseSet_false_eq_hemi0 a b)).prodCongr (Homeomorph.refl Punc)))

/-- The piece over `hemi1` is a product of `hemi1` with the punctured `ℝ⁴`. -/
noncomputable def pVHomeo (a b : ℤ) : ↥(pV a b) ≃ₜ ↥(Work.Agree.hemi1) × Punc :=
  (Homeomorph.setCongr (piece_true_eq_pV a b)).symm.trans
    ((pieceHomeo true a b).trans
      ((Homeomorph.setCongr (baseSet_true_eq_hemi1 a b)).prodCongr (Homeomorph.refl Punc)))

end H4

/-! ## 5. The vanishing of `H⁴` on a piece -/

/-- Transport of `Subsingleton` of `H⁴` along a homeomorphism of spaces. -/
lemma subsingleton_cohomology_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (h : Subsingleton ↥(Work.Thom.Coh ℤ 4 Y)) :
    Subsingleton ↥(Work.Thom.Coh ℤ 4 X) := by
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv e.toHomotopyEquiv 4
  exact (Equiv.subsingleton_congr iso.toLinearEquiv.toEquiv).mpr h

/-! ## 6. The two cohomology groups vanish -/

/-- **`H⁴` of each of the two pieces of the Mayer–Vietoris cover of the punctured total space
vanishes.**  Each piece is the product of a contractible chart of `S⁴` with the punctured `ℝ⁴`
(`H4.pUHomeo`, `H4.pVHomeo`); removing the contractible factor does not change `H⁴`
(`cohomology_prod_contractible`), and `H⁴(ℝ⁴ ∖ 0) = 0` (`PuncturedH4Vanishing`). -/
theorem H4Vanishing (a b : ℤ) :
    Subsingleton ↥(Work.Thom.Coh ℤ 4 ↥(Work.Transgression.pU a b)) ∧
    Subsingleton ↥(Work.Thom.Coh ℤ 4 ↥(Work.Transgression.pV a b)) := by
  constructor
  · haveI : ContractibleSpace ↥(Work.Agree.hemi0) := HemiContractible0
    have h : Subsingleton ↥(Work.Thom.Coh ℤ 4 (↥(Work.Agree.hemi0) × H4.Punc)) := by
      obtain ⟨e⟩ := Work.Cohomology.cohomology_prod_contractible ℤ
        (TopCat.of ↥(Work.Agree.hemi0)) (TopCat.of H4.Punc) 4
      exact (Equiv.subsingleton_congr e.toLinearEquiv.toEquiv).mpr PuncturedH4Vanishing
    exact subsingleton_cohomology_of_homeo (H4.pUHomeo a b) h
  · haveI : ContractibleSpace ↥(Work.Agree.hemi1) := HemiContractible1
    have h : Subsingleton ↥(Work.Thom.Coh ℤ 4 (↥(Work.Agree.hemi1) × H4.Punc)) := by
      obtain ⟨e⟩ := Work.Cohomology.cohomology_prod_contractible ℤ
        (TopCat.of ↥(Work.Agree.hemi1)) (TopCat.of H4.Punc) 4
      exact (Equiv.subsingleton_congr e.toLinearEquiv.toEquiv).mpr PuncturedH4Vanishing
    exact subsingleton_cohomology_of_homeo (H4.pVHomeo a b) h

end

end Work.Transgression
