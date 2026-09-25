import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.FlatData
import Submission.Work.NN.Final.FlatOneAux
import Submission.Work.NN.Final.RecULocal
import Submission.Work.NN.Final.recUEstimateNoClosed
import Submission.Work.NN.Final.schauderIterateNoClosed
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_open_of_unit
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Holder.holderNorm_zero_comp_le
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter MeasureTheory
open Work.CR.Flat Work.CR.Flat.Cauchy Work.CR.Flat.Holder

namespace Work.NN.Final

variable {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ}

/-! ## The linear operator on a submodule and its linear extension -/

/-- The submodule of data which are continuous on the polydisc `pd n ρ 4`. -/
def contOnPd (n : ℕ) (ρ : Fin n → ℝ) : Submodule ℝ (Fin n → (Fin n → ℂ) → ℂ) where
  carrier := {f | ∀ j, ContinuousOn (f j) (pd n ρ 4)}
  zero_mem' := fun j => continuousOn_const
  add_mem' := fun hf hg j => (hf j).add (hg j)
  smul_mem' := fun c f hf => fun j => (hf j).const_smul c

/-- The rescaled `recU` operator on the submodule of data continuous on `pd n ρ 4`. -/
noncomputable def T1Lin (hρ : ∀ j, 0 < ρ j) :
    contOnPd n ρ →ₗ[ℝ] ((Fin n → ℂ) → ℂ) where
  toFun := fun f z => recU (sclData ρ f.1) (invRescaleMap 0 (scl ρ) z)
  map_add' := by
    intro f g
    funext z
    have hc1 : ∀ j, Continuous (sclData ρ f.1 j) := fun j => continuous_sclData hρ f.2 j
    have hc2 : ∀ j, Continuous (sclData ρ g.1 j) := fun j => continuous_sclData hρ g.2 j
    have hsum : sclData ρ (f.1 + g.1) = sclData ρ f.1 + sclData ρ g.1 := by
      funext j w
      simp only [sclData_apply, Pi.add_apply]
      ring
    have hkey := congrFun (recU_add hc1 hc2) (invRescaleMap 0 (scl ρ) z)
    show recU (sclData ρ (f + g).1) (invRescaleMap 0 (scl ρ) z)
      = recU (sclData ρ f.1) (invRescaleMap 0 (scl ρ) z)
        + recU (sclData ρ g.1) (invRescaleMap 0 (scl ρ) z)
    rw [show (f + g).1 = f.1 + g.1 from rfl, hsum]
    exact hkey
  map_smul' := by
    intro c f
    funext z
    have hc1 : ∀ j, Continuous (sclData ρ f.1 j) := fun j => continuous_sclData hρ f.2 j
    have hsm : sclData ρ (c • f.1) = c • sclData ρ f.1 := by
      funext j w
      simp only [sclData_apply, Pi.smul_apply]
      rw [Complex.real_smul, Complex.real_smul]
      ring
    have hkey := congrFun (recU_smul c hc1) (invRescaleMap 0 (scl ρ) z)
    show recU (sclData ρ (c • f).1) (invRescaleMap 0 (scl ρ) z)
      = c • recU (sclData ρ f.1) (invRescaleMap 0 (scl ρ) z)
    rw [show (c • f).1 = c • f.1 from rfl, hsm]
    exact hkey

/-- The localized `∂̄`-Poincaré operator, as a linear map on all data (the unique linear
extension of `T1Lin`). -/
noncomputable def flatOneLin (hρ : ∀ j, 0 < ρ j) :
    (Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) :=
  Classical.choose (LinearMap.exists_extend (T1Lin (n := n) (ρ := ρ) hρ))

lemma flatOneLin_apply (hρ : ∀ j, 0 < ρ j) (f : Fin n → (Fin n → ℂ) → ℂ)
    (hf : f ∈ contOnPd n ρ) :
    flatOneLin hρ f = T1Lin hρ ⟨f, hf⟩ := by
  have h := Classical.choose_spec (LinearMap.exists_extend (T1Lin (n := n) (ρ := ρ) hρ))
  exact congrFun (congrArg DFunLike.coe h) ⟨f, hf⟩

/-- The scaling factor `scl ρ j` is a positive multiple of `ρ j`. -/
lemma scl_eq {j : Fin n} : scl ρ j = (7 / 2) * ρ j := rfl

/-! ## The cut-off `cutoffPull` is identically one near the polydisc `pd n ρ 3` -/

lemma eventually_norm_lt' {i : Fin n} {c : ℝ} {w : Fin n → ℂ} (hw : ‖w i‖ < c) :
    {w' : Fin n → ℂ | ‖w' i‖ < c} ∈ 𝓝 w :=
  (isOpen_lt ((continuous_apply i).norm) continuous_const).mem_nhds hw

/-- Near every point of the polydisc `pd n ρ 3` the pulled-back cut-off is identically `1`. -/
lemma cutoffPull_eventuallyEq_one (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ}
    (hz : ∀ i, ‖z i‖ < 3 * ρ i) :
    ∀ᶠ z' in 𝓝 z, cutoffPull ρ z' = 1 := by
  have h : ∀ i : Fin n, ∀ᶠ z' in 𝓝 z, ‖z' i‖ < 3 * ρ i := fun i =>
    eventually_norm_lt' (hz i)
  filter_upwards [Filter.eventually_all.mpr h] with z' hz'
  exact cutoffPull_eq_one hρ (fun i => le_of_lt (hz' i))

/-- The `∂̄`-derivative of `cutoffPull ρ · f` at a point of the polydisc `pd n ρ 3` is that of
`f`. -/
lemma dbarCoord_cutoffPull_mul (hρ : ∀ j, 0 < ρ j) {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hz : ∀ i, ‖z i‖ < 3 * ρ i) (l : Fin n) :
    dbarCoord l (fun z' => cutoffPull ρ z' * f z') z = dbarCoord l f z := by
  have hev : (fun z' : Fin n → ℂ => cutoffPull ρ z' * f z') =ᶠ[𝓝 z] f := by
    filter_upwards [cutoffPull_eventuallyEq_one hρ hz] with z' hz'
    rw [hz', one_mul]
  unfold dbarCoord
  rw [hev.fderiv_eq]

/-! ## The solution property of the localized operator -/

/-- The rescaled point lies in the solution polydisc: if `‖z l‖ < c · ρ l` with `c < 21/8`,
then `z / (scl ρ)` has all coordinates of modulus `< eqRad = 3/4`. -/
lemma norm_invRescaleMap_lt_eqRad (hρ : ∀ j, 0 < ρ j) {c : ℝ} (hc : c < 21 / 8)
    {z : Fin n → ℂ} (hz : ∀ i, ‖z i‖ < c * ρ i) (l : Fin n) :
    ‖invRescaleMap 0 (scl ρ) z l‖ < eqRad := by
  have hSinv : 0 < scl ρ l := scl_pos hρ l
  have h1 : c * ρ l < (21 / 8) * ρ l := by
    have := hρ l
    nlinarith
  have h2 : ((scl ρ l)⁻¹) * ‖z l‖ < ((scl ρ l)⁻¹) * ((21 / 8) * ρ l) :=
    mul_lt_mul_of_pos_left (lt_trans (hz l) h1) (inv_pos.mpr hSinv)
  have h3 : ((scl ρ l)⁻¹) * ((21 / 8) * ρ l) = eqRad := by
    have hne : ρ l ≠ 0 := ne_of_gt (hρ l)
    have hsinv : (scl ρ l)⁻¹ = (2 / 7) * (ρ l)⁻¹ := by
      rw [show scl ρ l = (7 / 2) * ρ l from rfl, mul_inv]
      norm_num
    rw [hsinv, eqRad]
    calc (2 / 7) * (ρ l)⁻¹ * ((21 / 8) * ρ l)
        = (2 / 7) * (21 / 8) * ((ρ l)⁻¹ * ρ l) := by ring
      _ = (2 / 7) * (21 / 8) * 1 := by rw [inv_mul_cancel₀ hne]
      _ = 3 / 4 := by norm_num
  have hv' : ‖invRescaleMap 0 (scl ρ) z l‖ = ((scl ρ l)⁻¹) * ‖z l‖ := by
    rw [invRescaleMap_apply]
    simp only [Pi.zero_apply, neg_zero, zero_div, zero_add, norm_mul]
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hSinv.le)]
  rw [hv']
  exact lt_of_lt_of_le h2 (le_of_eq h3)

/-- The explicit localized operator solves `∂̄ u = f` on the polydisc `pd n ρ c` for every
`c < 21/8`. -/
lemma T1Lin_solves_on (hρ : ∀ j, 0 < ρ j) {c : ℝ} (hc : c < 21 / 8)
    {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiffOn ℝ 1 (f j) (pd n ρ 4)) (hfcl : Clos1 n ρ 4 f) :
    ∀ (j : Fin n) (z : Fin n → ℂ), z ∈ pd n ρ c →
      dbarCoord j (T1Lin (n := n) (ρ := ρ) hρ ⟨f, fun i => (hf i).continuousOn⟩) z = f j z := by
  intro j z hz
  have hf' : ∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 (fun j => 4 * ρ j)) := hf
  have hfcl' : ∀ j l z, z ∈ polydisc 0 (fun j => 4 * ρ j) →
      dbarCoord l (f j) z = dbarCoord j (f l) z := fun j l z hz' => hfcl l j z hz'
  have hsc : ∀ j, ContDiff ℝ 1 (sclData ρ f j) := fun j => contDiff_sclData hρ hf j
  have hcl : ∀ j l z, (∀ m, ‖z m‖ < kappa * cutIn) →
      dbarCoord l (sclData ρ f j) z = dbarCoord j (sclData ρ f l) z :=
    fun j l z hz' => isClosedForm_sclData hρ hf' hfcl' hz' j l
  have hR : cutOut < kappa * cutIn := by norm_num [kappa, cutOut, cutIn]
  have hsol := recU_solves_local (n := n) (R := kappa * cutIn) hR hsc hcl
  -- the rescaled point
  have hSinv : ∀ i, 0 < scl ρ i := scl_pos hρ
  have hneq : ∀ i, (scl ρ i : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.mpr (ne_of_gt (hSinv i))
  -- `z ∈ pd n ρ c` implies the rescaled point is in `solveSet`
  rw [mem_pd] at hz
  have hv : ∀ l, ‖invRescaleMap 0 (scl ρ) z l‖ < eqRad := fun l =>
    norm_invRescaleMap_lt_eqRad hρ hc hz l
  -- the chain rule
  have hdiff : DifferentiableAt ℝ (fun z' => recU (sclData ρ f) z')
      (invRescaleMap 0 (scl ρ) z) :=
    ((contDiff_recU' (k := 0) hsc).differentiable (by simp)).differentiableAt
  have hchain := Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine
    (a := fun i => (scl ρ i)⁻¹) (b := fun i => -(0 : ℂ) / (scl ρ i)) j
    (U := fun z' => recU (sclData ρ f) z') (z := z) hdiff
  have hchain' : dbarCoord j (fun z' => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z')) z
      = (((scl ρ j)⁻¹ : ℝ) : ℂ) * dbarCoord j (fun z' => recU (sclData ρ f) z')
          (invRescaleMap 0 (scl ρ) z) := hchain
  change dbarCoord j (fun z' => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z')) z = f j z
  rw [hchain', hsol j (invRescaleMap 0 (scl ρ) z) hv]
  -- identify the scaled datum at the rescaled point
  have hmem : ∀ m, ‖invRescaleMap 0 (scl ρ) z m‖ < kappa * cutIn := by
    intro m
    refine lt_of_lt_of_le (hv m) ?_
    have h1 : eqRad ≤ cutIn := le_of_lt eqRad_lt_cutIn
    have h2 : cutIn ≤ kappa * cutIn := by
      have : (1 : ℝ) ≤ kappa := by norm_num [kappa]
      nlinarith [cutIn_pos]
    exact le_trans h1 h2
  rw [sclData_eq hmem j, rescaleMap_invRescaleMap (c := (0 : Fin n → ℂ)) (r := scl ρ)
    (fun i => ne_of_gt (hSinv i)) z]
  rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ (hneq j), one_mul]

/-- The solution property of the localized operator on the polydisc `pd n ρ 2`. -/
lemma T1Lin_solves (hρ : ∀ j, 0 < ρ j) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiffOn ℝ 1 (f j) (pd n ρ 4)) (hfcl : Clos1 n ρ 4 f) :
    ∀ (j : Fin n) (z : Fin n → ℂ), z ∈ pd n ρ 2 →
      dbarCoord j (T1Lin (n := n) (ρ := ρ) hρ ⟨f, fun i => (hf i).continuousOn⟩) z = f j z :=
  T1Lin_solves_on (n := n) (ρ := ρ) hρ (c := 2) (by norm_num) hf hfcl

/-- Smooth data give a smooth primitive. -/
lemma T1Lin_contDiff (hρ : ∀ j, 0 < ρ j) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) (pd n ρ 4)) (hfcl : Clos1 n ρ 4 f) :
    ContDiffOn ℝ ∞ (fun z => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z)) (pd n ρ 2) := by
  rw [contDiffOn_infty]
  intro m
  have hsc : ∀ j, ContDiff ℝ (((m + 1 : ℕ)) : ℕ∞) (sclData ρ f j) :=
    fun j => contDiff_sclData hρ
      (fun j => (hf j).of_le (coe_le_infty (m := ((m + 1 : ℕ) : ℕ∞)))) j
  have h1 : ContDiff ℝ (((m + 1 : ℕ)) : ℕ∞) (fun z => recU (sclData ρ f) z) :=
    contDiff_recU' hsc
  have hψ : ContDiff ℝ (((m + 1 : ℕ)) : ℕ∞) (invRescaleMap 0 (scl ρ)) :=
    (contDiff_invRescaleMap 0 (scl ρ)).of_le le_top
  have h2 : ContDiff ℝ (((m + 1 : ℕ)) : ℕ∞)
      (fun z => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z)) := h1.comp hψ
  exact (h2.of_le (by exact_mod_cast Nat.le_succ m)).contDiffOn


/-! ## The a priori bound and the Schauder estimate for the localized operator -/

/-- **The a priori `C^{0,α}` bound** for the localized operator on the polydisc `pd n ρ (13/5)`,
in terms of the `C^{k,α}`-norm of the data on `pd n ρ 4`. -/
lemma aPriori_bound (hn : 0 < n) (hρ : ∀ j, 0 < ρ j) (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    ∃ CA : ℝ, 0 < CA ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) (f j) (pd n ρ 4)) → Clos1 n ρ 4 f →
      (∑ j, holderNorm k α (f j) (pd n ρ 4)) ≠ ⊤ →
      holderNorm 0 α (fun z => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z)) (pd n ρ (13 / 5))
        ≤ ENNReal.ofReal CA * ∑ j, holderNorm k α (f j) (pd n ρ 4) := by
  obtain ⟨Cres, hCrespos, hCres⟩ := recUEstimateNoClosed (n := n) hα0 hα1
  have hKexists : ∀ j : Fin n, ∃ K : ℝ, 0 < K ∧
      ∀ f : Fin n → (Fin n → ℂ) → ℂ,
        (∀ i, ContDiffOn ℝ 1 (f i) (polydisc 0 (fun i => 4 * ρ i))) →
        holderNorm 0 α (sclData ρ f j) (polydisc 0 (fun _ => 1))
          ≤ ENNReal.ofReal K * holderNorm 0 α (f j) (polydisc 0 (fun i => 4 * ρ i)) :=
    fun j => exists_holderNorm_sclData_le (n := n) hρ hα0 hα1.le j
  choose Kc hKcpos hKcest using hKexists
  have hKsum_nonneg : 0 ≤ ∑ j, Kc j := Finset.sum_nonneg fun j _ => (hKcpos j).le
  refine ⟨max 1 ((scaleRinv (scl ρ)) ^ α) * (2 * (Cres * (∑ j, Kc j + 1))), ?_, ?_⟩
  · refine mul_pos (lt_max_of_lt_left one_pos) ?_
    refine mul_pos (by norm_num) (mul_pos hCrespos ?_)
    linarith
  · intro f hf hfcl hT
    have hTne : ∀ j, holderNorm k α (f j) (pd n ρ 4) ≠ ⊤ :=
      fun j => (ENNReal.sum_ne_top.mp hT) j (Finset.mem_univ j)
    set T : ℝ≥0∞ := ∑ j, holderNorm k α (f j) (pd n ρ 4) with hTdef
    have hf1 : ∀ i, ContDiffOn ℝ 1 (f i) (pd n ρ 4) := fun i =>
      (hf i).of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
    have hsc1 : ∀ j, ContDiff ℝ 1 (sclData ρ f j) := fun j => contDiff_sclData hρ hf1 j
    -- finiteness of the `C^{0,α}`-norm of the scaled datum
    have hmul_ne : ∀ j, ENNReal.ofReal (Kc j) * holderNorm 0 α (f j) (pd n ρ 4) ≠ ⊤ :=
      fun j => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top (hTne j) (holderNorm_mono_k (Nat.zero_le k) α (f j) (pd n ρ 4)))
    have hS'fin : (∑ j, holderNorm 0 α (sclData ρ f j) (polydisc 0 (fun _ => 1))) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun j _ => ne_top_of_le_ne_top (hmul_ne j) (hKcest j f hf1)
    have hrec := hCres (sclData ρ f) hsc1 hS'fin
    set S' : ℝ := ∑ j, (holderNorm 0 α (sclData ρ f j) (polydisc 0 (fun _ => 1))).toReal
      with hS'def
    have hS'nonneg : 0 ≤ S' := Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
    -- the estimate for `recU`
    have hA : iterDerivNorm 0 (fun z => recU (sclData ρ f) z) solveSet
        ≤ ENNReal.ofReal (Cres * S') := by
      rw [iterDerivNorm_zero]
      refine iSup₂_le fun z hz => ?_
      rw [mem_solveSet] at hz
      exact ENNReal.ofReal_le_ofReal (hrec.1 z hz)
    have hB : holderSeminorm 0 α (fun z => recU (sclData ρ f) z) solveSet
        ≤ ENNReal.ofReal (Cres * S') := by
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      rw [mem_solveSet] at hx hy
      rw [norm_iteratedFDerivWithin_zero_sub]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)]
      exact hrec.2 x y hx hy
    have hnorm : holderNorm 0 α (fun z => recU (sclData ρ f) z) solveSet
        ≤ ENNReal.ofReal (2 * (Cres * S')) := by
      have h2 : ENNReal.ofReal (Cres * S') + ENNReal.ofReal (Cres * S')
          = ENNReal.ofReal (2 * (Cres * S')) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hCrespos.le hS'nonneg)
          (mul_nonneg hCrespos.le hS'nonneg)]
        congr 1
        ring
      rw [show holderNorm 0 α (fun z => recU (sclData ρ f) z) solveSet
          = iterDerivNorm 0 (fun z => recU (sclData ρ f) z) solveSet
            + holderSeminorm 0 α (fun z => recU (sclData ρ f) z) solveSet from by
            simp only [holderNorm, Nat.zero_add, Finset.sum_range_one], ← h2]
      exact add_le_add hA hB
    -- the composition with the rescaling
    have hMinvpos : 0 < scaleRinv (scl ρ) := by
      rw [scaleRinv_eq]
      have h : 0 ≤ ∑ i, (scl ρ i)⁻¹ :=
        Finset.sum_nonneg fun i _ => inv_nonneg.mpr (scl_pos hρ i).le
      linarith
    have hmap : MapsTo (invRescaleMap 0 (scl ρ)) (pd n ρ (13 / 5)) solveSet := by
      intro z hz
      rw [mem_pd] at hz
      rw [mem_solveSet]
      exact fun l => norm_invRescaleMap_lt_eqRad hρ (by norm_num) hz l
    have hcomp := holderNorm_zero_comp_le (hα := hα0) (hM := hMinvpos.le)
      (Ω := pd n ρ (13 / 5)) (Ω' := solveSet) (Φ := invRescaleMap 0 (scl ρ))
      (U := fun z => recU (sclData ρ f) z) (M := scaleRinv (scl ρ)) hmap
      (fun x _ y _ => norm_invRescaleMap_sub_le (scl_pos hρ) x y)
    -- the bound for `S'`
    have hS'le : S' ≤ (∑ j, Kc j + 1) * T.toReal := by
      have hsum1 : (∑ j, (holderNorm k α (f j) (pd n ρ 4)).toReal) = T.toReal := by
        rw [hTdef, ENNReal.toReal_sum (fun j _ => hTne j)]
      calc S' = ∑ j, (holderNorm 0 α (sclData ρ f j) (polydisc 0 (fun _ => 1))).toReal := rfl
        _ ≤ ∑ j, Kc j * (holderNorm k α (f j) (pd n ρ 4)).toReal := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h0 : holderNorm 0 α (sclData ρ f j) (polydisc 0 (fun _ => 1))
                ≤ ENNReal.ofReal (Kc j) * holderNorm 0 α (f j) (pd n ρ 4) := hKcest j f hf1
            have h2 := ENNReal.toReal_mono (hmul_ne j) h0
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hKcpos j).le] at h2
            refine h2.trans ?_
            exact mul_le_mul_of_nonneg_left
              (ENNReal.toReal_mono (hTne j) (holderNorm_mono_k (Nat.zero_le k) α (f j) (pd n ρ 4)))
              (hKcpos j).le
        _ ≤ ∑ j, Kc j * (∑ l, (holderNorm k α (f l) (pd n ρ 4)).toReal) := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul_of_nonneg_left
              (Finset.single_le_sum (f := fun l => (holderNorm k α (f l) (pd n ρ 4)).toReal)
                (fun l _ => ENNReal.toReal_nonneg) (Finset.mem_univ j))
              (hKcpos j).le
        _ = (∑ j, Kc j) * (∑ l, (holderNorm k α (f l) (pd n ρ 4)).toReal) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ (∑ j, Kc j + 1) * T.toReal := by
            rw [hsum1]
            refine mul_le_mul (le_add_of_nonneg_right zero_le_one) le_rfl
              ENNReal.toReal_nonneg (by linarith)
    -- assembling
    have hU : holderNorm 0 α (fun z => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z))
        (pd n ρ (13 / 5))
        ≤ ENNReal.ofReal (max 1 ((scaleRinv (scl ρ)) ^ α) * (2 * (Cres * (∑ j, Kc j + 1)))) * T := by
      have hstep : ENNReal.ofReal (2 * (Cres * S'))
          ≤ ENNReal.ofReal (2 * (Cres * ((∑ j, Kc j + 1) * T.toReal))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS'le hCrespos.le) (by norm_num)
      have hMα : 0 ≤ (scaleRinv (scl ρ)) ^ α := Real.rpow_nonneg hMinvpos.le α
      have hmaxnonneg : 0 ≤ max 1 ((scaleRinv (scl ρ)) ^ α) := le_trans zero_le_one (le_max_left _ _)
      have hrearr : max 1 ((scaleRinv (scl ρ)) ^ α) * (2 * (Cres * ((∑ j, Kc j + 1) * T.toReal)))
          = (max 1 ((scaleRinv (scl ρ)) ^ α) * (2 * (Cres * (∑ j, Kc j + 1)))) * T.toReal := by
        ring
      calc holderNorm 0 α (fun z => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z))
            (pd n ρ (13 / 5))
          ≤ max 1 (ENNReal.ofReal ((scaleRinv (scl ρ)) ^ α))
              * holderNorm 0 α (fun z => recU (sclData ρ f) z) solveSet := hcomp
        _ ≤ max 1 (ENNReal.ofReal ((scaleRinv (scl ρ)) ^ α))
              * ENNReal.ofReal (2 * (Cres * ((∑ j, Kc j + 1) * T.toReal))) :=
            mul_le_mul_right (hnorm.trans hstep) _
        _ = ENNReal.ofReal (max 1 ((scaleRinv (scl ρ)) ^ α)
              * (2 * (Cres * ((∑ j, Kc j + 1) * T.toReal)))) := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_max]
            exact (ENNReal.ofReal_mul hmaxnonneg).symm
        _ = ENNReal.ofReal (max 1 ((scaleRinv (scl ρ)) ^ α)
              * (2 * (Cres * (∑ j, Kc j + 1)))) * T := by
            rw [hrearr]
            have hA0 : (0 : ℝ) ≤ max 1 ((scaleRinv (scl ρ)) ^ α) * (2 * (Cres * (∑ j, Kc j + 1))) :=
              mul_nonneg hmaxnonneg
                (mul_nonneg (by norm_num) (mul_nonneg hCrespos.le (by linarith)))
            rw [ENNReal.ofReal_mul hA0, ENNReal.ofReal_toReal hT]
    exact hU


/-- **The `C^{k+1,α}` estimate for the localized `∂̄`-Poincaré operator.** -/
lemma exists_est (hn : 0 < n) (hρ : ∀ j, 0 < ρ j) (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) (f j) (pd n ρ 4)) → Clos1 n ρ 4 f →
      holderNorm (k + 1) α (fun z => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z)) (pd n ρ 2)
        ≤ ENNReal.ofReal C * ∑ j, holderNorm k α (f j) (pd n ρ 4) := by
  obtain ⟨Citer, hCiterpos, hCiter⟩ :=
    schauderIterateNoClosed (n := n) hn (c := (0 : Fin n → ℂ)) (r := fun j => 4 * ρ j)
      (ρmax := fun j => (13 / 5) * ρ j) (fun j => by have := hρ j; nlinarith)
      (fun j => by have := hρ j; nlinarith) hα0 hα1 k
  obtain ⟨CA, hCApos, hCA⟩ := aPriori_bound (n := n) hn hρ hα0 hα1 k
  obtain ⟨Cmk, hCmkpos, hCmk⟩ := holderNorm_mul_le_of_hasCompactSupport (n := n) (Ω := pd n ρ 4)
    (isOpen_pd ρ 4).uniqueDiffOn (k := k) hα0.le hα1.le
    ((contDiff_cutoffPull hρ).of_le (coe_le_infty (m := ((k + 1 : ℕ) : ℕ∞))))
    (hasCompactSupport_cutoffPull hρ)
  obtain ⟨Cm0, hCm0pos, hCm0⟩ := holderNorm_mul_le_of_hasCompactSupport (n := n) (Ω := pd n ρ 4)
    (isOpen_pd ρ 4).uniqueDiffOn (k := 0) hα0.le hα1.le
    ((contDiff_cutoffPull hρ).of_le (coe_le_infty (m := (1 : ℕ∞))))
    (hasCompactSupport_cutoffPull hρ)
  have hsumpos : 0 < Cmk + Cm0 + CA := by linarith
  refine ⟨Citer * (Cmk + Cm0 + CA) + 1, ?_, ?_⟩
  · have h2 : 0 < Citer * (Cmk + Cm0 + CA) := mul_pos hCiterpos hsumpos
    linarith
  · intro f hf hfcl
    by_cases hT : (∑ j, holderNorm k α (f j) (pd n ρ 4)) = ⊤
    · rw [hT, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by
        have h2 : 0 < Citer * (Cmk + Cm0 + CA) := mul_pos hCiterpos hsumpos
        linarith))]
      exact le_top
    · have hTne : ∀ j, holderNorm k α (f j) (pd n ρ 4) ≠ ⊤ :=
        fun j => (ENNReal.sum_ne_top.mp hT) j (Finset.mem_univ j)
      set T : ℝ≥0∞ := ∑ j, holderNorm k α (f j) (pd n ρ 4) with hTdef
      have hf1 : ∀ i, ContDiffOn ℝ 1 (f i) (pd n ρ 4) := fun i =>
        (hf i).of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
      have hu : ContDiff ℝ (k + 1)
          (fun z => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z)) :=
        (contDiff_recU' (k := k) (fun j => contDiff_sclData hρ (fun i => hf i) j)).comp
          ((contDiff_invRescaleMap 0 (scl ρ)).of_le le_top)
      have hF : ∀ j, ContDiff ℝ (k + 1) (fun z' => cutoffPull ρ z' * f j z') :=
        fun j => contDiff_mul_cutoffPull hρ (hf j)
      have hFcl : ∀ j l z, z ∈ polydisc 0 (fun j => (13 / 5) * ρ j) →
          dbarCoord j (fun z' => cutoffPull ρ z' * f l z') z
            = dbarCoord l (fun z' => cutoffPull ρ z' * f j z') z := by
        intro j l z hz
        have hz' : ∀ i, ‖z i‖ < (13 / 5) * ρ i := fun i => by simpa using hz i
        have hz3 : ∀ i, ‖z i‖ < 3 * ρ i := fun i => by
          have h1 : (13 / 5) * ρ i < 3 * ρ i := by have := hρ i; nlinarith
          exact lt_trans (hz' i) h1
        have hz4 : z ∈ pd n ρ 4 := by
          rw [mem_pd]
          intro i
          have h1 : 3 * ρ i < 4 * ρ i := by have := hρ i; linarith
          exact lt_trans (hz3 i) h1
        rw [dbarCoord_cutoffPull_mul hρ hz3 j, dbarCoord_cutoffPull_mul hρ hz3 l]
        exact hfcl j l z hz4
      have heq : ∀ j, ∀ z : Fin n → ℂ,
          (∀ i, ‖z i - (0 : Fin n → ℂ) i‖ < (13 / 5) * ρ i) →
          dbarCoord j (fun z' => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z')) z
            = cutoffPull ρ z * f j z := by
        intro j z hz
        have hz' : ∀ i, ‖z i‖ < (13 / 5) * ρ i := fun i => by simpa using hz i
        have hz3 : ∀ i, ‖z i‖ < 3 * ρ i := fun i => by
          have h1 : (13 / 5) * ρ i < 3 * ρ i := by have := hρ i; nlinarith
          exact lt_trans (hz' i) h1
        have h1 : dbarCoord j (fun z' => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z')) z
            = f j z :=
          T1Lin_solves_on (n := n) (ρ := ρ) hρ (c := 13 / 5) (by norm_num) hf1 hfcl j z
            ((mem_pd).mpr hz')
        rw [h1, cutoffPull_eq_one hρ (fun i => le_of_lt (hz3 i)), one_mul]
      have hmain := hCiter (fun z => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z))
        (fun j z => cutoffPull ρ z * f j z) hu hF hFcl heq
      rw [show (fun j : Fin n => 4 * ρ j / 2) = fun j => 2 * ρ j from by funext j; ring]
        at hmain
      have hSk : (∑ j, holderNorm k α (fun z' => cutoffPull ρ z' * f j z') (pd n ρ 4))
          ≤ ENNReal.ofReal Cmk * T := by
        have h1 : ∀ j, holderNorm k α (fun z' => cutoffPull ρ z' * f j z') (pd n ρ 4)
            ≤ ENNReal.ofReal Cmk * holderNorm k α (f j) (pd n ρ 4) := fun j =>
          hCmk (f j) ((hf j).of_le (by exact_mod_cast Nat.le_succ k))
        calc (∑ j, holderNorm k α (fun z' => cutoffPull ρ z' * f j z') (pd n ρ 4))
            ≤ ∑ j, ENNReal.ofReal Cmk * holderNorm k α (f j) (pd n ρ 4) :=
              Finset.sum_le_sum fun j _ => h1 j
          _ = ENNReal.ofReal Cmk * ∑ j, holderNorm k α (f j) (pd n ρ 4) :=
              (Finset.mul_sum _ _ _).symm
          _ = ENNReal.ofReal Cmk * T := by rw [← hTdef]
      have hS0 : (∑ j, holderNorm 0 α (fun z' => cutoffPull ρ z' * f j z') (pd n ρ 4))
          ≤ ENNReal.ofReal Cm0 * T := by
        have h1 : ∀ j, holderNorm 0 α (fun z' => cutoffPull ρ z' * f j z') (pd n ρ 4)
            ≤ ENNReal.ofReal Cm0 * holderNorm 0 α (f j) (pd n ρ 4) := fun j =>
          hCm0 (f j) ((hf j).of_le (by exact_mod_cast Nat.zero_le (k + 1)))
        calc (∑ j, holderNorm 0 α (fun z' => cutoffPull ρ z' * f j z') (pd n ρ 4))
            ≤ ∑ j, ENNReal.ofReal Cm0 * holderNorm 0 α (f j) (pd n ρ 4) :=
              Finset.sum_le_sum fun j _ => h1 j
          _ = ENNReal.ofReal Cm0 * ∑ j, holderNorm 0 α (f j) (pd n ρ 4) :=
              (Finset.mul_sum _ _ _).symm
          _ ≤ ENNReal.ofReal Cm0 * T := by
              rw [hTdef]
              exact mul_le_mul_right (Finset.sum_le_sum fun j _ =>
                holderNorm_mono_k (Nat.zero_le k) α (f j) (pd n ρ 4)) _
      have hU := hCA f hf hfcl hT
      have hsum : (∑ j, holderNorm k α (fun z' => cutoffPull ρ z' * f j z') (pd n ρ 4))
            + (∑ j, holderNorm 0 α (fun z' => cutoffPull ρ z' * f j z') (pd n ρ 4))
            + holderNorm 0 α (fun z => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z))
              (pd n ρ (13 / 5))
          ≤ ENNReal.ofReal (Cmk + Cm0 + CA) * T := by
        calc _ ≤ ENNReal.ofReal Cmk * T + ENNReal.ofReal Cm0 * T + ENNReal.ofReal CA * T :=
              add_le_add (add_le_add hSk hS0) hU
          _ = (ENNReal.ofReal Cmk + ENNReal.ofReal Cm0 + ENNReal.ofReal CA) * T := by ring
          _ ≤ ENNReal.ofReal (Cmk + Cm0 + CA) * T := by
              have hle : ENNReal.ofReal Cmk + ENNReal.ofReal Cm0 + ENNReal.ofReal CA
                  ≤ ENNReal.ofReal (Cmk + Cm0 + CA) := by
                have hp : (0 : ℝ) ≤ Cmk + Cm0 := by linarith
                have e1 : ENNReal.ofReal Cmk + ENNReal.ofReal Cm0
                    = ENNReal.ofReal (Cmk + Cm0) :=
                  (ENNReal.ofReal_add (p := Cmk) (q := Cm0) hCmkpos.le hCm0pos.le).symm
                have e2 : ENNReal.ofReal (Cmk + Cm0) + ENNReal.ofReal CA
                    = ENNReal.ofReal (Cmk + Cm0 + CA) :=
                  (ENNReal.ofReal_add (p := Cmk + Cm0) (q := CA) hp hCApos.le).symm
                rw [e1, e2]
              exact mul_le_mul_left hle T
      refine hmain.trans ?_
      calc ENNReal.ofReal Citer
            * ((∑ j, holderNorm k α (fun z' => cutoffPull ρ z' * f j z') (pd n ρ 4))
              + (∑ j, holderNorm 0 α (fun z' => cutoffPull ρ z' * f j z') (pd n ρ 4))
              + holderNorm 0 α (fun z => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z))
                (pd n ρ (13 / 5)))
          ≤ ENNReal.ofReal Citer * (ENNReal.ofReal (Cmk + Cm0 + CA) * T) :=
            mul_le_mul_right hsum _
        _ = (ENNReal.ofReal Citer * ENNReal.ofReal (Cmk + Cm0 + CA)) * T := by ring
        _ ≤ ENNReal.ofReal (Citer * (Cmk + Cm0 + CA) + 1) * T := by
            have hmul : ENNReal.ofReal Citer * ENNReal.ofReal (Cmk + Cm0 + CA)
                = ENNReal.ofReal (Citer * (Cmk + Cm0 + CA)) :=
              (ENNReal.ofReal_mul (p := Citer) (q := Cmk + Cm0 + CA) hCiterpos.le).symm
            have hle : ENNReal.ofReal Citer * ENNReal.ofReal (Cmk + Cm0 + CA)
                ≤ ENNReal.ofReal (Citer * (Cmk + Cm0 + CA) + 1) := by
              rw [hmul]
              exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)
            exact mul_le_mul_left hle T


/-- **The `(0,1)`-level open flat `∂̄`-Poincaré lemma on nested polydiscs.**

For every `n`, every `0 < α < 1` and every positive radius family `ρ` there is a linear primitive
operator `T1` with the `C^{k+1,α}` estimate on `pd n ρ 2` for `∂̄`-closed data on `pd n ρ 4`. -/
theorem flatOne {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hα0 : 0 < α) (hα1 : α < 1) :
    Nonempty (Work.NN.Final.FlatOne n α ρ) := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨hρ, hα0, hα1, (fun _ => (1 : ℝ)), (fun _ => one_pos), 0, ?_, ?_, ?_⟩
    · intro f hf hfcl j
      exact j.elim0
    · intro k f hf hfcl
      rw [LinearMap.zero_apply, holderNorm_zero]
      simp
    · intro f hf hfcl
      rw [LinearMap.zero_apply]
      exact contDiffOn_const
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hex : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ,
        (∀ j, ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) (f j) (pd n ρ 4)) → Clos1 n ρ 4 f →
        holderNorm (k + 1) α (fun z => recU (sclData ρ f) (invRescaleMap 0 (scl ρ) z))
            (pd n ρ 2) ≤ ENNReal.ofReal C * ∑ j, holderNorm k α (f j) (pd n ρ 4) :=
      fun k => exists_est (n := n) hnpos hρ hα0 hα1 k
    choose C1 hC1pos hC1est using hex
    refine ⟨hρ, hα0, hα1, C1, hC1pos, flatOneLin hρ, ?_, ?_, ?_⟩
    · intro f hf hfcl
      have hmem : f ∈ contOnPd n ρ := fun j => (hf j).continuousOn
      rw [flatOneLin_apply hρ f hmem]
      exact T1Lin_solves hρ hf hfcl
    · intro k f hf hfcl
      have hmem : f ∈ contOnPd n ρ := fun j => (hf j).continuousOn
      rw [flatOneLin_apply hρ f hmem]
      exact hC1est k f hf hfcl
    · intro f hf hfcl
      have hmem : f ∈ contOnPd n ρ := fun j =>
        ((hf j).of_le (coe_le_infty (m := (1 : ℕ∞)))).continuousOn
      rw [flatOneLin_apply hρ f hmem]
      exact T1Lin_contDiff hρ hf hfcl

end Work.NN.Final



