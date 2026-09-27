import Mathlib
import Submission.Work.Mostow.gapA.screwDefs
import Submission.Work.Mostow.gapA.screwNorm
import Submission.Work.Mostow.gapA.screwGeod
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.mem_geodSet_iff_span
import Submission.Work.Mostow.Hyper

/-!
# `screwGeodParam`: the axis of a screw motion is a parametrised geodesic

For two distinct boundary points `a ≠ b ∈ Sph 3` the file `gapA.screwDefs` defines

* `nullA a = (a,1)`, `nullB b = (b,1)`, the two future null vectors of the endpoints;
* `axisV a b s = κ (e^s · nullA a + e^{-s} · nullB b)`, `κ = kkB a b = (2(1-⟪a,b⟫))^{-1/2}`,
  the point of the geodesic with endpoints `a`, `b` at parameter `s` (as a Minkowski vector);
* `axisPt a b s`, the chart point of `axisV a b s`.

This file proves `screwGeodParam`, the bundle of parameterisation facts used by the screw-motion
argument:

* `s ↦ axisPt a b s` maps `ℝ` onto the geodesic `geodSet a b` and is injective — so it is a
  bijection `ℝ ≃ geodSet a b`;
* `span (range (axisV a b)) = span {nullA a, nullB b}`: the axis spans the plane of the two null
  vectors (both inclusions are explicit: `axisV` is an exponential combination of `nullA`, `nullB`,
  while `nullA` and `nullB` are recovered from the values at `0` and `1` through
  `e^{-1}·axisV 0 - axisV 1 = κ(e^{-1}-e)·nullA` and `e·axisV 0 - axisV 1 = κ(e-e^{-1})·nullB`);
* two values of `s` already span it (`span {axisV 0, axisV 1} = span (range (axisV a b))`);
* membership in that span is exactly vanishing of the normal component `prjN a b`.

## Ingredients used (all proved elsewhere)

* `gapA.geodFacts`: `gcAxisPt_mem_geodSet`, `hlift_gcAxisPt`, `mink_nvec_a_gcAxis`, positivity of
  `gcL`, `gcK` and the normalisation `gcK^2 · 2(1-⟪a,b⟫) = 1` (with `gcAxis = axisV`, `gcK = kkB`
  definitionally);
* `gapA.mem_geodSet_iff_span`: `u ∈ geodSet a b ↔ hlift u ∈ span {nvec a, nvec b}`;
* `gapA.screwNorm`: `smB a b = -(1 - ⟪a,b⟫) ≠ 0` and
  `prjN a b x = 0 ↔ x = alC a b x · nullA a + beC a b x · nullB b`;
* `Work.Mostow.hlift_injective` for the chart.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

/-! ## Elementary evaluations of the parametrisation -/

/-- `axisV` at `0` is `κ` times the sum of the two null vectors. -/
lemma screwGeodParam_axisV_zero_eq (a b : E 3) :
    axisV a b 0 = kkB a b • (nullA a + nullB b) := by
  simp [axisV]

/-- `axisV` at `1`. -/
lemma screwGeodParam_axisV_one_eq (a b : E 3) :
    axisV a b 1 = kkB a b • (Real.exp 1 • nullA a + Real.exp (-1) • nullB b) := by
  simp [axisV]

lemma screwGeodParam_exp_neg_one_ne_exp_one : Real.exp (-1 : ℝ) ≠ Real.exp 1 := by
  intro h
  have h3 : (-1 : ℝ) = 1 := Real.exp_injective h
  norm_num at h3

lemma screwGeodParam_exp_neg_one_sub_exp_one_ne_zero : Real.exp (-1) - Real.exp 1 ≠ 0 :=
  fun h => screwGeodParam_exp_neg_one_ne_exp_one (sub_eq_zero.mp h)

lemma screwGeodParam_exp_one_sub_exp_neg_one_ne_zero : Real.exp 1 - Real.exp (-1) ≠ 0 :=
  fun h => screwGeodParam_exp_neg_one_ne_exp_one (sub_eq_zero.mp h).symm

/-- `e^{-1} · axisV 0 - axisV 1` is a non-zero multiple of `nullA a`. -/
lemma screwGeodParam_axisV_smul_nullA (a b : E 3) :
    Real.exp (-1) • axisV a b 0 - axisV a b 1
      = (kkB a b * (Real.exp (-1) - Real.exp 1)) • nullA a := by
  rw [axisV, axisV]
  simp only [Real.exp_zero, neg_zero, one_smul, smul_add, smul_smul]
  module

/-- `e · axisV 0 - axisV 1` is a non-zero multiple of `nullB b`. -/
lemma screwGeodParam_axisV_smul_nullB (a b : E 3) :
    Real.exp 1 • axisV a b 0 - axisV a b 1
      = (kkB a b * (Real.exp 1 - Real.exp (-1))) • nullB b := by
  rw [axisV, axisV]
  simp only [Real.exp_zero, neg_zero, one_smul, smul_add, smul_smul]
  module

/-- The null vector `nullA a` is a linear combination of `axisV a b 0` and `axisV a b 1`. -/
lemma screwGeodParam_nullA_eq_smul_axisV {a b : E 3} (hkk : kkB a b ≠ 0) :
    nullA a = (kkB a b * (Real.exp (-1) - Real.exp 1))⁻¹ •
      (Real.exp (-1) • axisV a b 0 - axisV a b 1) := by
  have hc : kkB a b * (Real.exp (-1) - Real.exp 1) ≠ 0 :=
    mul_ne_zero hkk screwGeodParam_exp_neg_one_sub_exp_one_ne_zero
  rw [screwGeodParam_axisV_smul_nullA, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The null vector `nullB b` is a linear combination of `axisV a b 0` and `axisV a b 1`. -/
lemma screwGeodParam_nullB_eq_smul_axisV {a b : E 3} (hkk : kkB a b ≠ 0) :
    nullB b = (kkB a b * (Real.exp 1 - Real.exp (-1)))⁻¹ •
      (Real.exp 1 • axisV a b 0 - axisV a b 1) := by
  have hc : kkB a b * (Real.exp 1 - Real.exp (-1)) ≠ 0 :=
    mul_ne_zero hkk screwGeodParam_exp_one_sub_exp_neg_one_ne_zero
  rw [screwGeodParam_axisV_smul_nullB, smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma screwGeodParam_nullA_mem_span_axisV {a b : E 3} (hkk : kkB a b ≠ 0) :
    nullA a ∈ Submodule.span ℝ ({axisV a b 0, axisV a b 1} : Set (Fin 3 ⊕ Fin 1 → ℝ)) := by
  have hmem : Real.exp (-1) • axisV a b 0 - axisV a b 1 ∈
      Submodule.span ℝ ({axisV a b 0, axisV a b 1} : Set (Fin 3 ⊕ Fin 1 → ℝ)) :=
    Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.subset_span (by simp))
  rw [screwGeodParam_nullA_eq_smul_axisV hkk]
  exact Submodule.smul_mem _ _ hmem

lemma screwGeodParam_nullB_mem_span_axisV {a b : E 3} (hkk : kkB a b ≠ 0) :
    nullB b ∈ Submodule.span ℝ ({axisV a b 0, axisV a b 1} : Set (Fin 3 ⊕ Fin 1 → ℝ)) := by
  have hmem : Real.exp 1 • axisV a b 0 - axisV a b 1 ∈
      Submodule.span ℝ ({axisV a b 0, axisV a b 1} : Set (Fin 3 ⊕ Fin 1 → ℝ)) :=
    Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.subset_span (by simp))
  rw [screwGeodParam_nullB_eq_smul_axisV hkk]
  exact Submodule.smul_mem _ _ hmem

/-! ## The main statement -/

theorem screwGeodParam {a b : Submission.Mostow.E 3} (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b) :
    (∀ s : ℝ, Work.Mostow.gapA.axisPt a b s ∈ Work.Mostow.geodSet a b) ∧
    (∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → ∃ s : ℝ, u = Work.Mostow.gapA.axisPt a b s) ∧
    Function.Injective (Work.Mostow.gapA.axisPt a b) ∧
    (Submodule.span ℝ (Set.range (Work.Mostow.gapA.axisV a b)) = Submodule.span ℝ ({Work.Mostow.gapA.nullA a, Work.Mostow.gapA.nullB b} : Set (Fin 3 ⊕ Fin 1 → ℝ))) ∧
    (Submodule.span ℝ ({Work.Mostow.gapA.axisV a b 0, Work.Mostow.gapA.axisV a b 1} : Set (Fin 3 ⊕ Fin 1 → ℝ)) = Submodule.span ℝ (Set.range (Work.Mostow.gapA.axisV a b))) ∧
    (∀ x : Fin 3 ⊕ Fin 1 → ℝ, x ∈ Submodule.span ℝ (Set.range (Work.Mostow.gapA.axisV a b)) ↔ Work.Mostow.gapA.prjN a b x = 0) := by
  have hc : 0 < 1 - inner ℝ a b := by linarith [inner_lt_one ha hb hab]
  have hcne : (1 - inner ℝ a b) ≠ 0 := ne_of_gt hc
  have hkkpos : 0 < kkB a b := gcK_pos a b ha hb hab
  have hkkne : kkB a b ≠ 0 := ne_of_gt hkkpos
  have hkksq : kkB a b ^ 2 * (2 * (1 - inner ℝ a b)) = 1 := gcK_sq a b ha hb hab
  have hsmne : smB a b ≠ 0 := (screwNorm ha hb hab).2.2.1
  have hsm : smB a b = -(1 - inner ℝ a b) := by
    have h := (screwNorm ha hb hab).2.1
    rw [h]; rfl
  have hAA : mink (nullA a) (nullA a) = 0 := by simpa only [nullA] using mink_nvec_self ha
  have hBB : mink (nullB b) (nullB b) = 0 := by simpa only [nullB] using mink_nvec_self hb
  have hABm : mink (nullA a) (nullB b) = smB a b := rfl
  have hBAm : mink (nullB b) (nullA a) = smB a b := by rw [minkSeg_comm]; rfl
  -- the normal projection of a combination of the two null vectors vanishes
  have hprj_zero : ∀ c1 c2 : ℝ, prjN a b (c1 • nullA a + c2 • nullB b) = 0 := by
    intro c1 c2
    have h1 : mink (c1 • nullA a + c2 • nullB b) (nullB b) = c1 * smB a b := by
      rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', hABm, hBB]; ring
    have h2 : mink (c1 • nullA a + c2 • nullB b) (nullA a) = c2 * smB a b := by
      rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', hBAm, hAA]; ring
    rw [prjN_def, alC, beC, h1, h2]
    rw [mul_div_cancel_right₀ c1 hsmne, mul_div_cancel_right₀ c2 hsmne]
    abel
  -- ... and conversely
  have hprj_iff : ∀ x : Fin 3 ⊕ Fin 1 → ℝ,
      prjN a b x = 0 ↔ x ∈ Submodule.span ℝ ({nullA a, nullB b} : Set (Fin 3 ⊕ Fin 1 → ℝ)) := by
    intro x
    rw [Submodule.mem_span_pair]
    constructor
    · intro h
      refine ⟨alC a b x, beC a b x, ?_⟩
      have h' : x - alC a b x • nullA a - beC a b x • nullB b = 0 := by
        rw [← prjN_def]; exact h
      have hsub : x - (alC a b x • nullA a + beC a b x • nullB b) = 0 := by
        rw [show x - (alC a b x • nullA a + beC a b x • nullB b)
              = x - alC a b x • nullA a - beC a b x • nullB b from by abel]
        exact h'
      exact (sub_eq_zero.mp hsub).symm
    · rintro ⟨c1, c2, hc⟩
      rw [← hc]
      exact hprj_zero c1 c2
  -- spanning statements
  have hV_AB : ∀ s : ℝ,
      axisV a b s ∈ Submodule.span ℝ ({nullA a, nullB b} : Set (Fin 3 ⊕ Fin 1 → ℝ)) := by
    intro s
    rw [axisV]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  have hA01 : nullA a ∈ Submodule.span ℝ ({axisV a b 0, axisV a b 1} : Set (Fin 3 ⊕ Fin 1 → ℝ)) :=
    screwGeodParam_nullA_mem_span_axisV hkkne
  have hB01 : nullB b ∈ Submodule.span ℝ ({axisV a b 0, axisV a b 1} : Set (Fin 3 ⊕ Fin 1 → ℝ)) :=
    screwGeodParam_nullB_mem_span_axisV hkkne
  have hV_01 : ∀ s : ℝ,
      axisV a b s ∈ Submodule.span ℝ ({axisV a b 0, axisV a b 1} : Set (Fin 3 ⊕ Fin 1 → ℝ)) := by
    intro s
    rw [axisV]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ hA01) (Submodule.smul_mem _ _ hB01))
  have hgen01 : ({axisV a b 0, axisV a b 1} : Set (Fin 3 ⊕ Fin 1 → ℝ)) ⊆
      Submodule.span ℝ (Set.range (axisV a b)) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
  have hspan01_le_range : Submodule.span ℝ ({axisV a b 0, axisV a b 1} : Set (Fin 3 ⊕ Fin 1 → ℝ))
      ≤ Submodule.span ℝ (Set.range (axisV a b)) := Submodule.span_le.mpr hgen01
  have hAB_le_range : Submodule.span ℝ ({nullA a, nullB b} : Set (Fin 3 ⊕ Fin 1 → ℝ))
      ≤ Submodule.span ℝ (Set.range (axisV a b)) := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hspan01_le_range hA01
    · exact hspan01_le_range hB01
  have hrange_le_AB : Submodule.span ℝ (Set.range (axisV a b))
      ≤ Submodule.span ℝ ({nullA a, nullB b} : Set (Fin 3 ⊕ Fin 1 → ℝ)) :=
    Submodule.span_le.mpr (by rintro x ⟨s, rfl⟩; exact hV_AB s)
  have hAB_le_01 : Submodule.span ℝ ({nullA a, nullB b} : Set (Fin 3 ⊕ Fin 1 → ℝ))
      ≤ Submodule.span ℝ ({axisV a b 0, axisV a b 1} : Set (Fin 3 ⊕ Fin 1 → ℝ)) := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hA01
    · exact hB01
  have hspanAB : Submodule.span ℝ (Set.range (axisV a b))
      = Submodule.span ℝ ({nullA a, nullB b} : Set (Fin 3 ⊕ Fin 1 → ℝ)) :=
    le_antisymm hrange_le_AB hAB_le_range
  have hspan01 : Submodule.span ℝ ({axisV a b 0, axisV a b 1} : Set (Fin 3 ⊕ Fin 1 → ℝ))
      = Submodule.span ℝ (Set.range (axisV a b)) :=
    le_antisymm hspan01_le_range (by rw [hspanAB]; exact hAB_le_01)
  -- injectivity of the parametrisation
  have hinj : Function.Injective (axisPt a b) := by
    intro s t hst
    have h0 : gcAxisPt a b s = gcAxisPt a b t := hst
    have h1 : gcAxis a b s = gcAxis a b t := by
      rw [← hlift_gcAxisPt a b ha hb hab s, ← hlift_gcAxisPt a b ha hb hab t, h0]
    have h2 : mink (nvec a) (gcAxis a b s) = mink (nvec a) (gcAxis a b t) := by rw [h1]
    rw [mink_nvec_a_gcAxis a b ha hb hab s, mink_nvec_a_gcAxis a b ha hb hab t] at h2
    have hconst : -2 * gcK a b * gcL a b ≠ 0 := by
      have hL := gcL_pos a b ha hb hab
      have hK := gcK_pos a b ha hb hab
      have hpos : 0 < 2 * gcK a b * gcL a b := by nlinarith
      intro hzero
      have hz : 2 * gcK a b * gcL a b = 0 := by linarith
      linarith
    have h3 : Real.exp (-s) = Real.exp (-t) := mul_left_cancel₀ hconst h2
    have h4 : -s = -t := Real.exp_injective h3
    linarith
  refine ⟨fun s => gcAxisPt_mem_geodSet a b ha hb hab s, ?_, hinj, hspanAB, hspan01, ?_⟩
  -- surjectivity
  · intro u hu
    obtain ⟨α, β, hαβ⟩ := (mem_geodSet_iff_span a b ha hb hab u).mp hu
    have hαβ' : hlift u = α • nullA a + β • nullB b := by simpa only [nullA, nullB] using hαβ
    have hself : mink (hlift u) (hlift u) = -1 := by
      rw [Work.Mostow.mink_eq_mform]; exact Work.Mostow.mform_hlift_self u
    have hexpand : mink (α • nullA a + β • nullB b) (α • nullA a + β • nullB b)
        = -2 * α * β * (1 - inner ℝ a b) := by
      simp only [minkSeg_add_left, minkSeg_add_right, mink_smul_left'', mink_smul_right'',
        hAA, hBB, hABm, hBAm, hsm]
      ring
    have hmul1 : α * β * (1 - inner ℝ a b) = 1 / 2 := by
      have h := hself
      rw [hαβ', hexpand] at h
      linarith
    have hmul2 : kkB a b ^ 2 * (1 - inner ℝ a b) = 1 / 2 := by
      have h := hkksq
      linarith
    have hprod : α * β = kkB a b ^ 2 := mul_right_cancel₀ hcne (by rw [hmul1, hmul2])
    have htime : α + β = tpart u := by
      have h := congrFun hαβ' (Sum.inr 0)
      simp [hlift, nullA, nullB, nvec] at h
      linarith
    have htp : 0 < tpart u := tpart_pos u
    have hpp : 0 < α * β := by rw [hprod]; exact pow_pos hkkpos 2
    have hαpos : 0 < α := by
      rcases lt_trichotomy α 0 with h | h | h
      · have hβneg : β < 0 := by
          rcases lt_trichotomy β 0 with h2 | h2 | h2
          · exact h2
          · rw [h2, mul_zero] at hpp; exact absurd hpp (lt_irrefl 0)
          · exact absurd (mul_neg_of_neg_of_pos h h2) (not_lt_of_ge (le_of_lt hpp))
        linarith
      · rw [h, zero_mul] at hpp; exact absurd hpp (lt_irrefl 0)
      · exact h
    have hβpos : 0 < β := by
      rcases lt_trichotomy β 0 with h | h | h
      · exact absurd hpp (not_lt_of_ge (le_of_lt (mul_neg_of_pos_of_neg hαpos h)))
      · rw [h, mul_zero] at hpp; exact absurd hpp (lt_irrefl 0)
      · exact h
    refine ⟨Real.log (α / kkB a b), ?_⟩
    have hlogpos : 0 < α / kkB a b := div_pos hαpos hkkpos
    have hexps : Real.exp (Real.log (α / kkB a b)) = α / kkB a b := Real.exp_log hlogpos
    have hkexp : kkB a b * Real.exp (Real.log (α / kkB a b)) = α := by
      rw [hexps, ← mul_div_assoc, mul_div_cancel_left₀ α hkkne]
    have hkexpneg : kkB a b * Real.exp (-(Real.log (α / kkB a b))) = β := by
      rw [Real.exp_neg, hexps, inv_div]
      rw [show kkB a b * (kkB a b / α) = kkB a b ^ 2 / α from by ring, ← hprod,
        mul_div_cancel_left₀ β (ne_of_gt hαpos)]
    have hV : axisV a b (Real.log (α / kkB a b)) = hlift u := by
      rw [hαβ']
      simp only [axisV, smul_add, smul_smul, hkexp, hkexpneg]
    have hfin : u = axisPt a b (Real.log (α / kkB a b)) := by
      apply Work.Mostow.hlift_injective
      exact hV.symm.trans (hlift_gcAxisPt a b ha hb hab (Real.log (α / kkB a b))).symm
    exact hfin
  -- vanishing of the normal component
  · intro x
    rw [hspanAB]
    exact (hprj_iff x).symm

end

end Work.Mostow.gapA
