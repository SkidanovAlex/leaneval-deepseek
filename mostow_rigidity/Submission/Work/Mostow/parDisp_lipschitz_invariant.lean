import Mathlib
import Submission.Work.Mostow.cuspParDispDefs
import Submission.Work.Mostow.cuspThinRegionDefs
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.cuspThinRegion_eq_parDisp

/-!
# `parDisp` is `2`-Lipschitz and invariant under the stabiliser of `ξ`

For `Γ ≤ PO n 1`, `ξ ∈ parFixed Γ` (a parabolic fixed point) and `y ∈ ξ^⊥`,
`parDisp Γ ξ y` is the infimum of the flat displacements `‖y - flatAct ξ γ y‖` over the
parabolic `γ ∈ Γ` fixing `ξ`.

Here we prove the two elementary facts:

* `parDisp Γ ξ` is `2`-Lipschitz on the hyperplane `ξ^⊥`.  Indeed each `γ` in the defining
  family preserves the Busemann level (`hvan` gives `bCocy γ ξ = 0`), so `flatAct ξ γ` is a
  Euclidean isometry of `ξ^⊥` and `y ↦ y - flatAct ξ γ y` is `2`-Lipschitz; an infimum of
  `2`-Lipschitz functions is `2`-Lipschitz.
* `parDisp Γ ξ` is invariant under `flatAct ξ σ` for every `σ ∈ Γ` fixing `ξ`: conjugation
  `γ ↦ σ⁻¹ γ σ` permutes the defining family and `flatAct ξ σ` is again an isometry.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

lemma parDispSet_nonempty {Γ : Subgroup (PO n 1)} {ξ : E n} (hξ : ξ ∈ parFixed Γ) (y : E n) :
    (parDispSet Γ ξ y).Nonempty :=
  ⟨_, hξ.2.choose, hξ.2.choose_spec.1, hξ.2.choose_spec.2, rfl⟩

lemma parDispSet_bddBelow (Γ : Subgroup (PO n 1)) (ξ y : E n) :
    BddBelow (parDispSet Γ ξ y) :=
  ⟨0, fun r hr => by obtain ⟨γ, _, _, rfl⟩ := hr; exact norm_nonneg _⟩

lemma parDisp_le_disp (Γ : Subgroup (PO n 1)) (ξ y : E n) (γ : Γ)
    (hpar : IsParabolic (γ : PO n 1)) (hbd : bd (γ : PO n 1) ξ = ξ) :
    parDisp Γ ξ y ≤ ‖y - flatAct ξ (γ : PO n 1) y‖ := by
  rw [parDisp_eq_sInf]
  exact csInf_le (parDispSet_bddBelow Γ ξ y) ⟨γ, hpar, hbd, rfl⟩

/-! ## The level of the image of the base point under a stabiliser element -/

/-- For `ξ ∈ parFixed Γ` and `γ ∈ Γ` fixing `ξ`, the Busemann cocycle vanishes (`hvan`), so
`γ` preserves the Busemann level: `lev ξ (γ • 0) = 1`. -/
lemma lev_smul_zero_eq_one
    {Γ : Subgroup (PO n 1)} {ξ : E n}
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ →
      bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hξ : ξ ∈ parFixed Γ) (γ : Γ) (hbd : bd (γ : PO n 1) ξ = ξ) :
    lev ξ ((γ : PO n 1) • (0 : E n)) = 1 := by
  have hbus : busemann ξ ((γ : PO n 1) • (0 : E n)) = 0 := by
    have h := hvan γ ξ hξ hbd
    simp only [bCocy] at h
    rwa [hbd] at h
  rw [lev_eq_exp hξ.1 ((γ : PO n 1) • (0 : E n)), hbus, Real.exp_zero]

/-! ## The displacement of a single stabiliser element is `2`-Lipschitz -/

/-- On `ξ^⊥`, the flat displacement `y ↦ ‖y - flatAct ξ γ y‖` of an element `γ ∈ Γ` fixing `ξ`
is `2`-Lipschitz (because `flatAct ξ γ` is a Euclidean isometry there). -/
lemma disp_sub_le (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} {ξ : E n}
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ →
      bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hξ : ξ ∈ parFixed Γ) {γ : Γ} (hbd : bd (γ : PO n 1) ξ = ξ) {y y' : E n}
    (hy : inner ℝ y ξ = 0) (hy' : inner ℝ y' ξ = 0) :
    ‖y - flatAct ξ (γ : PO n 1) y‖ ≤
      ‖y' - flatAct ξ (γ : PO n 1) y'‖ + 2 * ‖y - y'‖ := by
  have h0 := lev_smul_zero_eq_one hvan hξ γ hbd
  have hiso : ‖flatAct ξ (γ : PO n 1) y - flatAct ξ (γ : PO n 1) y'‖ = ‖y - y'‖ :=
    flatAct_isometry hξ.1 (POBasic.ofProp hA) (HypIsoData.ofProp hI) hbd h0 hy hy'
  have hb : ‖(y - flatAct ξ (γ : PO n 1) y) - (y' - flatAct ξ (γ : PO n 1) y')‖
      ≤ 2 * ‖y - y'‖ := by
    have hsplit : (y - flatAct ξ (γ : PO n 1) y) - (y' - flatAct ξ (γ : PO n 1) y')
        = (y - y') - (flatAct ξ (γ : PO n 1) y - flatAct ξ (γ : PO n 1) y') := by
      abel
    rw [hsplit]
    calc ‖(y - y') - (flatAct ξ (γ : PO n 1) y - flatAct ξ (γ : PO n 1) y')‖
        ≤ ‖y - y'‖ + ‖flatAct ξ (γ : PO n 1) y - flatAct ξ (γ : PO n 1) y'‖ :=
          norm_sub_le _ _
      _ = ‖y - y'‖ + ‖y - y'‖ := by rw [hiso]
      _ = 2 * ‖y - y'‖ := by ring
  have hrev : ‖y - flatAct ξ (γ : PO n 1) y‖
      ≤ ‖y' - flatAct ξ (γ : PO n 1) y'‖
        + ‖(y - flatAct ξ (γ : PO n 1) y) - (y' - flatAct ξ (γ : PO n 1) y')‖ := by
    have h1 := abs_norm_sub_norm_le (y - flatAct ξ (γ : PO n 1) y)
      (y' - flatAct ξ (γ : PO n 1) y')
    have h2 := le_abs_self (‖y - flatAct ξ (γ : PO n 1) y‖
      - ‖y' - flatAct ξ (γ : PO n 1) y'‖)
    linarith
  linarith

/-! ## `parDisp` is `2`-Lipschitz on `ξ^⊥` -/

lemma parDisp_sub_le (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} {ξ : E n}
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ →
      bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hξ : ξ ∈ parFixed Γ) {y y' : E n}
    (hy : inner ℝ y ξ = 0) (hy' : inner ℝ y' ξ = 0) :
    parDisp Γ ξ y ≤ parDisp Γ ξ y' + 2 * ‖y - y'‖ := by
  have h : parDisp Γ ξ y - 2 * ‖y - y'‖ ≤ parDisp Γ ξ y' := by
    rw [parDisp_eq_sInf Γ ξ y']
    refine le_csInf (parDispSet_nonempty hξ y') ?_
    intro r hr
    obtain ⟨γ, hpar, hbd, rfl⟩ := hr
    have h1 : parDisp Γ ξ y ≤ ‖y - flatAct ξ (γ : PO n 1) y‖ := parDisp_le_disp Γ ξ y γ hpar hbd
    have h2 := disp_sub_le hA hI hvan hξ hbd hy hy'
    linarith
  linarith

lemma parDisp_abs_sub_le (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} {ξ : E n}
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ →
      bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hξ : ξ ∈ parFixed Γ) {y y' : E n}
    (hy : inner ℝ y ξ = 0) (hy' : inner ℝ y' ξ = 0) :
    |parDisp Γ ξ y - parDisp Γ ξ y'| ≤ 2 * ‖y - y'‖ := by
  refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
  · have := parDisp_sub_le hA hI hvan hξ hy hy'
    linarith
  · have h := parDisp_sub_le hA hI hvan hξ hy' hy
    rw [norm_sub_rev] at h
    linarith

lemma parDisp_lipschitzOn (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} {ξ : E n}
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ →
      bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hξ : ξ ∈ parFixed Γ) :
    LipschitzOnWith 2 (parDisp Γ ξ) {y : E n | inner ℝ y ξ = 0} := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y hy y' hy'
  rw [Real.dist_eq, dist_eq_norm]
  simpa using parDisp_abs_sub_le hA hI hvan hξ hy hy'

/-! ## Invariance under the stabiliser of `ξ` -/

/-- `flatAct ξ σ⁻¹` inverts `flatAct ξ σ` on `ξ^⊥`. -/
lemma flatAct_inv_comp (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} {ξ : E n}
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ →
      bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hξ : ξ ∈ parFixed Γ) {σ : Γ} (hbdσ : bd (σ : PO n 1) ξ = ξ) {y : E n}
    (hy : inner ℝ y ξ = 0) :
    flatAct ξ (σ : PO n 1)⁻¹ (flatAct ξ (σ : PO n 1) y) = y := by
  have hA' := POBasic.ofProp hA
  have hI' := HypIsoData.ofProp hI
  have hbdi : bd ((σ⁻¹ : Γ) : PO n 1) ξ = ξ := by
    rw [Subgroup.coe_inv]; exact bd_inv_of hξ.1 hA' hbdσ
  have h0σ := lev_smul_zero_eq_one hvan hξ σ hbdσ
  have h0i := lev_smul_zero_eq_one hvan hξ (σ⁻¹) hbdi
  have hcomp := flatAct_comp hξ.1 hA' hI'
    (g := ((σ⁻¹ : Γ) : PO n 1)) (h := (σ : PO n 1)) hbdi hbdσ h0i h0σ hy
  have hinv : ((σ⁻¹ : Γ) : PO n 1) * (σ : PO n 1) = 1 := by
    rw [Subgroup.coe_inv]; exact inv_mul_cancel _
  rw [hinv, flatAct_one hξ.1 hA' hy] at hcomp
  simpa [Subgroup.coe_inv] using hcomp.symm

/-- Conjugation of `flatAct`: for `σ, δ ∈ Γ` fixing `ξ`, the conjugate `σ δ σ⁻¹` acts on the
`σ`-translate of `y` exactly as `σ` acts on the `δ`-translate of `y`. -/
lemma flatAct_conj (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} {ξ : E n}
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ →
      bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hξ : ξ ∈ parFixed Γ) {σ : Γ} (hbdσ : bd (σ : PO n 1) ξ = ξ)
    {δ : Γ} (hbdδ : bd (δ : PO n 1) ξ = ξ) {y : E n}
    (hy : inner ℝ y ξ = 0) :
    flatAct ξ (((σ * δ * σ⁻¹ : Γ)) : PO n 1) (flatAct ξ (σ : PO n 1) y)
      = flatAct ξ (σ : PO n 1) (flatAct ξ (δ : PO n 1) y) := by
  have hSph := hξ.1
  have hA' := POBasic.ofProp hA
  have hI' := HypIsoData.ofProp hI
  have hcoe : (((σ * δ * σ⁻¹ : Γ)) : PO n 1)
      = (σ : PO n 1) * (δ : PO n 1) * (σ : PO n 1)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe]
  have hbdi : bd ((σ⁻¹ : Γ) : PO n 1) ξ = ξ := by
    rw [Subgroup.coe_inv]; exact bd_inv_of hSph hA' hbdσ
  have hbdσδ : bd ((σ : PO n 1) * (δ : PO n 1)) ξ = ξ := bd_mul_of hSph hA' hbdσ hbdδ
  have h0σδ : lev ξ (((σ : PO n 1) * (δ : PO n 1)) • (0 : E n)) = 1 := by
    have h := lev_smul_zero_eq_one hvan hξ (σ * δ) (by rw [Subgroup.coe_mul]; exact hbdσδ)
    simpa [Subgroup.coe_mul] using h
  have h0i : lev ξ ((σ : PO n 1)⁻¹ • (0 : E n)) = 1 := by
    have h := lev_smul_zero_eq_one hvan hξ (σ⁻¹) hbdi
    simpa [Subgroup.coe_inv] using h
  have h0σ := lev_smul_zero_eq_one hvan hξ σ hbdσ
  have h0δ := lev_smul_zero_eq_one hvan hξ δ hbdδ
  have s1 : flatAct ξ ((σ : PO n 1) * (δ : PO n 1) * (σ : PO n 1)⁻¹)
        (flatAct ξ (σ : PO n 1) y)
      = flatAct ξ ((σ : PO n 1) * (δ : PO n 1))
          (flatAct ξ (σ : PO n 1)⁻¹ (flatAct ξ (σ : PO n 1) y)) :=
    flatAct_comp hSph hA' hI' hbdσδ hbdi h0σδ h0i (flatAct_mem hSph (σ : PO n 1) y)
  have s2 : flatAct ξ (σ : PO n 1)⁻¹ (flatAct ξ (σ : PO n 1) y) = y :=
    flatAct_inv_comp hA hI hvan hξ hbdσ hy
  have s3 : flatAct ξ ((σ : PO n 1) * (δ : PO n 1)) y
      = flatAct ξ (σ : PO n 1) (flatAct ξ (δ : PO n 1) y) :=
    flatAct_comp hSph hA' hI' hbdσ hbdδ h0σ h0δ hy
  rw [s1, s2, s3]

/-- The displacement identity in the `δ`-form: the flat displacement of `σ δ σ⁻¹` at the
`σ`-translate of `y` equals the flat displacement of `δ` at `y`. -/
lemma flatDisp_conj_wrap (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} {ξ : E n}
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ →
      bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hξ : ξ ∈ parFixed Γ) {σ : Γ} (hbdσ : bd (σ : PO n 1) ξ = ξ)
    {δ : Γ} (hbdδ : bd (δ : PO n 1) ξ = ξ) {y : E n}
    (hy : inner ℝ y ξ = 0) :
    ‖flatAct ξ (σ : PO n 1) y - flatAct ξ (((σ * δ * σ⁻¹ : Γ)) : PO n 1)
        (flatAct ξ (σ : PO n 1) y)‖ = ‖y - flatAct ξ (δ : PO n 1) y‖ := by
  have hSph := hξ.1
  have hA' := POBasic.ofProp hA
  have hI' := HypIsoData.ofProp hI
  have h0σ := lev_smul_zero_eq_one hvan hξ σ hbdσ
  have hkey := flatAct_conj hA hI hvan hξ hbdσ hbdδ hy
  have hmemi : inner ℝ (flatAct ξ (δ : PO n 1) y) ξ = 0 := flatAct_mem hSph (δ : PO n 1) y
  have hiso : ‖flatAct ξ (σ : PO n 1) y
        - flatAct ξ (σ : PO n 1) (flatAct ξ (δ : PO n 1) y)‖
      = ‖y - flatAct ξ (δ : PO n 1) y‖ :=
    flatAct_isometry hSph hA' hI' hbdσ h0σ hy hmemi
  rw [hkey]
  exact hiso

/-- The displacement identity in the `γ`-form: the flat displacement of `γ` at the
`σ`-translate of `y` equals the flat displacement of the conjugate `σ⁻¹ γ σ` at `y`. -/
lemma flatDisp_conj_inv (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} {ξ : E n}
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ →
      bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hξ : ξ ∈ parFixed Γ) {σ : Γ} (hbdσ : bd (σ : PO n 1) ξ = ξ)
    {γ : Γ} (hbdγ : bd (γ : PO n 1) ξ = ξ) {y : E n}
    (hy : inner ℝ y ξ = 0) :
    ‖flatAct ξ (σ : PO n 1) y - flatAct ξ (γ : PO n 1) (flatAct ξ (σ : PO n 1) y)‖
      = ‖y - flatAct ξ ((σ⁻¹ * γ * σ : Γ) : PO n 1) y‖ := by
  have hSph := hξ.1
  have hA' := POBasic.ofProp hA
  have hbdi : bd ((σ⁻¹ : Γ) : PO n 1) ξ = ξ := by
    rw [Subgroup.coe_inv]; exact bd_inv_of hSph hA' hbdσ
  have hbdδ : bd (((σ⁻¹ * γ * σ : Γ)) : PO n 1) ξ = ξ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact bd_mul_of hSph hA' (bd_mul_of hSph hA' hbdi hbdγ) hbdσ
  have h := flatDisp_conj_wrap hA hI hvan hξ hbdσ hbdδ hy
  have hid : (((σ * (σ⁻¹ * γ * σ) * σ⁻¹ : Γ)) : PO n 1) = (γ : PO n 1) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rwa [hid] at h

/-- `parDisp Γ ξ` is invariant under `flatAct ξ σ` for `σ ∈ Γ` fixing `ξ`. -/
lemma parDisp_flatAct_invariant (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} {ξ : E n}
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ →
      bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hξ : ξ ∈ parFixed Γ) {σ : Γ} (hbdσ : bd (σ : PO n 1) ξ = ξ) {y : E n}
    (hy : inner ℝ y ξ = 0) :
    parDisp Γ ξ (flatAct ξ (σ : PO n 1) y) = parDisp Γ ξ y := by
  have hSph := hξ.1
  have hA' := POBasic.ofProp hA
  have hbdi : bd ((σ⁻¹ : Γ) : PO n 1) ξ = ξ := by
    rw [Subgroup.coe_inv]; exact bd_inv_of hSph hA' hbdσ
  apply le_antisymm
  · rw [parDisp_eq_sInf Γ ξ y]
    refine le_csInf (parDispSet_nonempty hξ y) ?_
    intro r hr
    obtain ⟨δ, hpar, hbdδ, rfl⟩ := hr
    have hparγ : IsParabolic (((σ * δ * σ⁻¹ : Γ)) : PO n 1) := by
      have h := isParabolic_conj hA hI (σ : PO n 1) (δ : PO n 1) hpar
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
    have hbdγ : bd (((σ * δ * σ⁻¹ : Γ)) : PO n 1) ξ = ξ := by
      have h := bd_mul_of hSph hA' (bd_mul_of hSph hA' hbdσ hbdδ) (bd_inv_of hSph hA' hbdσ)
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
    have hle := parDisp_le_disp Γ ξ (flatAct ξ (σ : PO n 1) y) (σ * δ * σ⁻¹) hparγ hbdγ
    have hconj := flatDisp_conj_wrap hA hI hvan hξ hbdσ hbdδ hy
    rwa [hconj] at hle
  · rw [parDisp_eq_sInf Γ ξ (flatAct ξ (σ : PO n 1) y)]
    refine le_csInf (parDispSet_nonempty hξ (flatAct ξ (σ : PO n 1) y)) ?_
    intro r hr
    obtain ⟨γ, hpar, hbdγ, rfl⟩ := hr
    have hparδ : IsParabolic (((σ⁻¹ * γ * σ : Γ)) : PO n 1) := by
      have h := isParabolic_conj hA hI (σ : PO n 1)⁻¹ (γ : PO n 1) hpar
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
    have hbdδ : bd (((σ⁻¹ * γ * σ : Γ)) : PO n 1) ξ = ξ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact bd_mul_of hSph hA' (bd_mul_of hSph hA' hbdi hbdγ) hbdσ
    have hle := parDisp_le_disp Γ ξ y (σ⁻¹ * γ * σ) hparδ hbdδ
    have hconj := flatDisp_conj_inv hA hI hvan hξ hbdσ hbdγ hy
    rwa [← hconj] at hle

end

end Work.Mostow

namespace Work.Mostow

theorem parDisp_lipschitz_invariant (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    LipschitzOnWith 2 (Work.Mostow.parDisp Γ ξ) {y : Submission.Mostow.E n | inner ℝ y ξ = 0} ∧
    (∀ (σ : Γ), Submission.Mostow.bd (σ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
        Work.Mostow.parDisp Γ ξ (Work.Mostow.flatAct ξ (σ : LeanEval.Geometry.MostowRigidity.PO n 1) y)
          = Work.Mostow.parDisp Γ ξ y) :=
  ⟨parDisp_lipschitzOn hA hI hvan hξ,
   fun σ hbdσ y hy => parDisp_flatAct_invariant hA hI hvan hξ (σ := σ) hbdσ (y := y) hy⟩

end Work.Mostow
