/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The scaled, cut-off datum for the localized `∂̄`-Poincaré operator

The construction `Work.CR.Flat.Cauchy.recU` solves the flat `∂̄`-equation on the *unit* polydisc
for globally defined data; to obtain a linear solution operator with the estimates on a polydisc
of multiradii `ρ` one rescales the datum by the diagonal map `w ↦ (j ↦ (7/2 · ρ j) w j)` and cuts
it off so that it becomes globally smooth.  This module provides the cut-off `cutCn` on `ℂⁿ`, the
scaled datum `sclData`, and their elementary properties (smoothness, closedness, size).
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolRec
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_open_of_unit
import Submission.Work.CR.Flat.Holder.holderNorm_zero_comp_le
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter
open Work.CR.Flat Work.CR.Flat.Cauchy

namespace Work.NN.Final

/-- The reserve factor of the cut-off: the cut-off is `1` on `‖w j‖ ≤ kappa * cutIn` and
vanishes for `kappa * cutOut ≤ ‖w j‖`. -/
def kappa : ℝ := 9 / 8

lemma kappa_pos : 0 < kappa := by norm_num [kappa]

/-- A finite-or-`∞` smoothness level is below the `C^∞` level `∞`. -/
lemma coe_le_infty {m : ℕ∞} : (m : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
  rw [show ((∞ : ℕ∞ω)) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

lemma kappa_cutOut_lt_one : kappa * cutOut < 1 := by norm_num [kappa, cutOut]

lemma cutOut_le_kappa_cutIn : cutOut ≤ kappa * cutIn := by norm_num [kappa, cutOut, cutIn]

lemma kappa_cutOut_lt_rat : kappa * cutOut * (7 / 2) < 4 := by norm_num [kappa, cutOut]

/-- The cut-off `χ` on `ℂⁿ`. -/
noncomputable def cutCn {n : ℕ} (w : Fin n → ℂ) : ℂ :=
  ∏ j : Fin n, openCut (w j / (kappa : ℂ))

lemma norm_cutCn_le_one {n : ℕ} (w : Fin n → ℂ) : ‖cutCn w‖ ≤ 1 := by
  simp only [cutCn, norm_prod]
  have key : ∀ s : Finset (Fin n), ∏ j ∈ s, ‖openCut (w j / (kappa : ℂ))‖ ≤ 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        have hnn : 0 ≤ ∏ j ∈ s, ‖openCut (w j / (kappa : ℂ))‖ := by
          rw [← norm_prod]; exact norm_nonneg _
        calc ‖openCut (w a / (kappa : ℂ))‖ * ∏ j ∈ s, ‖openCut (w j / (kappa : ℂ))‖
            ≤ 1 * 1 := mul_le_mul (norm_openCut_le_one _) ih hnn zero_le_one
          _ = 1 := by ring
  exact key Finset.univ

lemma cutCn_eq_one {n : ℕ} {w : Fin n → ℂ} (h : ∀ j, ‖w j‖ ≤ kappa * cutIn) :
    cutCn w = 1 := by
  rw [cutCn]
  refine Finset.prod_eq_one (s := (Finset.univ : Finset (Fin n)))
    (f := fun j => openCut (w j / (kappa : ℂ))) fun j _ => ?_
  refine openCut_eq_one_of_norm_le ?_
  rw [norm_div]
  have hk : ‖(kappa : ℂ)‖ = kappa := by
    simp [Complex.norm_real, Real.norm_of_nonneg kappa_pos.le]
  rw [hk]
  exact (div_le_iff₀ kappa_pos).mpr (by rw [mul_comm]; exact h j)

lemma cutCn_eq_zero_of_norm_ge {n : ℕ} {w : Fin n → ℂ} {j : Fin n}
    (h : kappa * cutOut ≤ ‖w j‖) : cutCn w = 0 := by
  rw [cutCn]
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  refine openCut_eq_zero_of_le_norm ?_
  rw [norm_div]
  have hk : ‖(kappa : ℂ)‖ = kappa := by
    simp [Complex.norm_real, Real.norm_of_nonneg kappa_pos.le]
  rw [hk]
  exact (le_div_iff₀ kappa_pos).mpr (by rw [mul_comm]; exact h)

lemma contDiff_cutCn {n : ℕ} : ContDiff ℝ ∞ (cutCn : (Fin n → ℂ) → ℂ) := by
  have key : ∀ s : Finset (Fin n),
      ContDiff ℝ ∞ (fun w : Fin n → ℂ => ∏ j ∈ s, openCut (w j / (kappa : ℂ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using contDiff_const (c := (1 : ℂ))
    | insert a s ha ih =>
        have h1 : ContDiff ℝ ∞ (fun w : Fin n → ℂ => openCut (w a / (kappa : ℂ))) :=
          openCut_props_infty.1.comp ((contDiff_apply ℝ ℂ a).div_const _)
        simpa [Finset.prod_insert ha] using h1.mul ih
  have h := key Finset.univ
  have heq : (fun w : Fin n → ℂ => ∏ j ∈ (Finset.univ : Finset (Fin n)),
      openCut (w j / (kappa : ℂ))) = cutCn := by
    funext w; simp [cutCn]
  rwa [heq] at h

lemma cutCn_eventuallyEq_zero {n : ℕ} {w : Fin n → ℂ} (h : ∃ j, kappa * cutOut < ‖w j‖) :
    (cutCn : (Fin n → ℂ) → ℂ) =ᶠ[𝓝 w] 0 := by
  obtain ⟨j, hj⟩ := h
  have hmem : {w' : Fin n → ℂ | kappa * cutOut < ‖w' j‖} ∈ 𝓝 w :=
    (isOpen_lt continuous_const ((continuous_apply j).norm)).mem_nhds hj
  filter_upwards [hmem] with w' hw'
  exact cutCn_eq_zero_of_norm_ge (le_of_lt hw')

/-- The Lipschitz constant of a single cut-off factor. -/
lemma exists_lipschitz_cutFactor {n : ℕ} (j : Fin n) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : Fin n → ℂ,
      ‖openCut (x j / (kappa : ℂ)) - openCut (y j / (kappa : ℂ))‖ ≤ L * ‖x - y‖ := by
  obtain ⟨L₀, hL₀, hL₀'⟩ := openCut_lipschitz
  refine ⟨L₀ / kappa, div_nonneg hL₀ kappa_pos.le, fun x y => ?_⟩
  have h1 : ‖(x j / (kappa : ℂ)) - (y j / (kappa : ℂ))‖ ≤ (1 / kappa) * ‖x - y‖ := by
    rw [show x j / (kappa : ℂ) - y j / (kappa : ℂ) = (x j - y j) / (kappa : ℂ) from by ring]
    rw [norm_div]
    have hk : ‖(kappa : ℂ)‖ = kappa := by
      simp [Complex.norm_real, Real.norm_of_nonneg kappa_pos.le]
    rw [hk, div_eq_mul_inv]
    calc ‖x j - y j‖ * kappa⁻¹ ≤ ‖x - y‖ * kappa⁻¹ :=
          mul_le_mul_of_nonneg_right (norm_le_pi_norm (x - y) j) (inv_nonneg.mpr kappa_pos.le)
      _ = (1 / kappa) * ‖x - y‖ := by rw [inv_eq_one_div]; ring
  calc ‖openCut (x j / kappa) - openCut (y j / kappa)‖
      ≤ L₀ * ‖(x j / (kappa : ℂ)) - (y j / (kappa : ℂ))‖ := hL₀' _ _
    _ ≤ L₀ * ((1 / kappa) * ‖x - y‖) := mul_le_mul_of_nonneg_left h1 hL₀
    _ = (L₀ / kappa) * ‖x - y‖ := by ring

lemma lipschitz_prod_val {n : ℕ} {f g : (Fin n → ℂ) → ℂ} {L L' : ℝ} (hL : 0 ≤ L) (_hL' : 0 ≤ L')
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) (hg : ∀ x y, ‖g x - g y‖ ≤ L' * ‖x - y‖)
    (hfb : ∀ x, ‖f x‖ ≤ 1) (hgb : ∀ x, ‖g x‖ ≤ 1) (x y : Fin n → ℂ) :
    ‖(f * g) x - (f * g) y‖ ≤ (L + L') * ‖x - y‖ := by
  have h1 : (f * g) x - (f * g) y = f x * (g x - g y) + (f x - f y) * g y := by
    rw [Pi.mul_apply, Pi.mul_apply]; ring
  rw [h1]
  calc ‖f x * (g x - g y) + (f x - f y) * g y‖
      ≤ ‖f x * (g x - g y)‖ + ‖(f x - f y) * g y‖ := norm_add_le _ _
    _ ≤ 1 * (L' * ‖x - y‖) + (L * ‖x - y‖) * 1 := by
        refine add_le_add ?_ ?_
        · rw [norm_mul]
          exact mul_le_mul (hfb x) (hg x y) (norm_nonneg _) zero_le_one
        · rw [norm_mul]
          exact mul_le_mul (hf x y) (hgb y) (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))
    _ = (L + L') * ‖x - y‖ := by ring


/-! ## The Lipschitz constant of the cut-off -/

lemma exists_lipschitz_cutCn {n : ℕ} :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : Fin n → ℂ, ‖cutCn x - cutCn y‖ ≤ L * ‖x - y‖ := by
  classical
  choose Lf hLf hLf' using fun j : Fin n => exists_lipschitz_cutFactor j
  have key : ∀ s : Finset (Fin n), ∃ L : ℝ, 0 ≤ L ∧
      (∀ x y : Fin n → ℂ,
        ‖(fun w => ∏ j ∈ s, openCut (w j / (kappa : ℂ))) x
          - (fun w => ∏ j ∈ s, openCut (w j / (kappa : ℂ))) y‖ ≤ L * ‖x - y‖) ∧
      (∀ x : Fin n → ℂ, ‖(fun w => ∏ j ∈ s, openCut (w j / (kappa : ℂ))) x‖ ≤ 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨0, le_refl 0, ?_, ?_⟩
        · intro x y; simp
        · intro x; simp
    | insert a s ha ih =>
        obtain ⟨Ls, hLs, hLs', hLsb⟩ := ih
        refine ⟨Lf a + Ls, add_nonneg (hLf a) hLs, ?_, ?_⟩
        · intro x y
          show ‖(∏ j ∈ insert a s, openCut (x j / (kappa : ℂ)))
              - (∏ j ∈ insert a s, openCut (y j / (kappa : ℂ)))‖ ≤ (Lf a + Ls) * ‖x - y‖
          rw [Finset.prod_insert ha, Finset.prod_insert ha]
          exact lipschitz_prod_val (hLf a) hLs (fun x y => hLf' a x y) hLs'
            (fun x => norm_openCut_le_one _) (fun x => hLsb x) x y
        · intro x
          show ‖(∏ j ∈ insert a s, openCut (x j / (kappa : ℂ)))‖ ≤ 1
          rw [Finset.prod_insert ha, norm_mul]
          exact mul_le_one₀ (norm_openCut_le_one _) (norm_nonneg _) (hLsb x)
  obtain ⟨L, hL, hL', -⟩ := key Finset.univ
  refine ⟨L, hL, fun x y => ?_⟩
  have hcx : cutCn x = ∏ j ∈ (Finset.univ : Finset (Fin n)), openCut (x j / (kappa : ℂ)) := by
    simp only [cutCn]
  have hcy : cutCn y = ∏ j ∈ (Finset.univ : Finset (Fin n)), openCut (y j / (kappa : ℂ)) := by
    simp only [cutCn]
  rw [hcx, hcy]
  exact hL' x y

/-! ## The elementary `C^{0,α}` bound for bounded Lipschitz functions -/

lemma norm_iteratedFDerivWithin_zero_sub {n : ℕ} (h : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ))
    (x y : Fin n → ℂ) :
    ‖iteratedFDerivWithin ℝ 0 h Ω x - iteratedFDerivWithin ℝ 0 h Ω y‖ = ‖h x - h y‖ := by
  have hx : iteratedFDerivWithin ℝ 0 h Ω x
      = ContinuousMultilinearMap.uncurry0 ℝ (Fin n → ℂ) (h x) := rfl
  have hy : iteratedFDerivWithin ℝ 0 h Ω y
      = ContinuousMultilinearMap.uncurry0 ℝ (Fin n → ℂ) (h y) := rfl
  rw [hx, hy]
  have hsub : ContinuousMultilinearMap.uncurry0 ℝ (Fin n → ℂ) (h x)
      - ContinuousMultilinearMap.uncurry0 ℝ (Fin n → ℂ) (h y)
      = ContinuousMultilinearMap.uncurry0 ℝ (Fin n → ℂ) (h x - h y) := by
    ext m
    simp [ContinuousMultilinearMap.uncurry0_apply]
  rw [hsub, ContinuousMultilinearMap.uncurry0_norm]

lemma holderNorm_zero_le_of_lipschitz {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {h : (Fin n → ℂ) → ℂ} {Ω : Set (Fin n → ℂ)} {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hb : ∀ x ∈ Ω, ‖h x‖ ≤ C) (hlip : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖h x - h y‖ ≤ L * ‖x - y‖) :
    holderNorm 0 α h Ω ≤ ENNReal.ofReal C + ENNReal.ofReal (max L (2 * C)) := by
  rw [holderNorm, Finset.sum_range_one]
  refine add_le_add ?_ ?_
  · rw [iterDerivNorm_zero]
    refine iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal (hb x hx)
  · rw [holderSeminorm]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [norm_iteratedFDerivWithin_zero_sub]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have h2C : ‖h x - h y‖ ≤ 2 * C := by
      have := norm_sub_le (h x) (h y)
      linarith [hb x hx, hb y hy]
    have hsub : ‖x - y‖ / ‖x - y‖ ^ α = ‖x - y‖ ^ (1 - α) := by
      rw [Real.rpow_sub hr (1 : ℝ) α, Real.rpow_one]
    by_cases hr1 : ‖x - y‖ ≤ 1
    · have hp : ‖x - y‖ ^ (1 - α) ≤ 1 := Real.rpow_le_one hr.le hr1 (by linarith)
      calc ‖h x - h y‖ / ‖x - y‖ ^ α ≤ (L * ‖x - y‖) / ‖x - y‖ ^ α :=
            div_le_div_of_nonneg_right (hlip x hx y hy) (Real.rpow_nonneg hr.le α)
        _ = L * ‖x - y‖ ^ (1 - α) := by rw [mul_div_assoc, hsub]
        _ ≤ L * 1 := mul_le_mul_of_nonneg_left hp hL
        _ = L := mul_one L
        _ ≤ max L (2 * C) := le_max_left _ _
    · have hr1' : 1 ≤ ‖x - y‖ := le_of_lt (not_le.mp hr1)
      have hαle : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow hr1' hα.le
      calc ‖h x - h y‖ / ‖x - y‖ ^ α ≤ (2 * C) / ‖x - y‖ ^ α :=
            div_le_div_of_nonneg_right h2C (Real.rpow_nonneg hr.le α)
        _ ≤ 2 * C := div_le_self (by linarith) hαle
        _ ≤ max L (2 * C) := le_max_right _ _

lemma exists_holderNorm_cutCn_bound {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ holderNorm 0 α (cutCn : (Fin n → ℂ) → ℂ)
      (polydisc 0 (fun _ => 1)) ≤ ENNReal.ofReal K := by
  obtain ⟨L, hL, hLip⟩ := exists_lipschitz_cutCn (n := n)
  have h := holderNorm_zero_le_of_lipschitz (n := n) (Ω := polydisc 0 (fun _ => 1))
    hα hα1 (C := 1) (L := L) zero_le_one hL (fun x _ => norm_cutCn_le_one x)
    (fun x _ y _ => hLip x y)
  refine ⟨1 + max L 2, by positivity, ?_⟩
  have h2 : max L (2 * 1) = max L 2 := by norm_num
  rw [h2] at h
  exact h.trans (le_of_eq (ENNReal.ofReal_add zero_le_one
    (le_trans (by norm_num : (0:ℝ) ≤ 2) (le_max_right L 2))).symm)


/-! ## The scaling and the scaled datum -/

/-- The scaling factor of the construction on the polydisc of multiradii `ρ`. -/
noncomputable def scl {n : ℕ} (ρ : Fin n → ℝ) : Fin n → ℝ := fun j => (7 / 2) * ρ j

lemma scl_pos {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) : ∀ j, 0 < scl ρ j :=
  fun j => by simp only [scl]; linarith [hρ j]

/-- The scaled datum: the `j`-th component is `χ · (scl ρ j · (f j ∘ rescaleMap 0 (scl ρ)))`. -/
noncomputable def sclData {n : ℕ} (ρ : Fin n → ℝ) (f : Fin n → (Fin n → ℂ) → ℂ) :
    Fin n → (Fin n → ℂ) → ℂ :=
  fun j w => cutCn w * ((scl ρ j : ℂ) * f j (rescaleMap 0 (scl ρ) w))

lemma sclData_apply {n : ℕ} (ρ : Fin n → ℝ) (f : Fin n → (Fin n → ℂ) → ℂ) (j : Fin n)
    (w : Fin n → ℂ) :
    sclData ρ f j w = cutCn w * ((scl ρ j : ℂ) * f j (rescaleMap 0 (scl ρ) w)) := rfl

lemma rescaleMap_zero_apply {n : ℕ} (S : Fin n → ℝ) (w : Fin n → ℂ) :
    rescaleMap 0 S w = fun i => (S i : ℂ) * w i := by
  funext i
  simp [rescaleMap_apply]

/-- The scaling map in the exact shape in which the chain rule
`dbarCoord_comp_diagAffine` is stated. -/
lemma rescaleMap_zero_eq {n : ℕ} (S : Fin n → ℝ) (w : Fin n → ℂ) :
    rescaleMap 0 S w = fun i => (0 : Fin n → ℂ) i + (S i : ℂ) * w i := rfl

lemma norm_rescaleMap_zero_apply {n : ℕ} (S : Fin n → ℝ) (hS : ∀ i, 0 < S i)
    (w : Fin n → ℂ) (i : Fin n) :
    ‖rescaleMap 0 S w i‖ = S i * ‖w i‖ := by
  rw [rescaleMap_zero_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt (hS i))]

/-- The scaled point `S · w` lies in the polydisc of multiradii `4ρ` as soon as
`‖w i‖ ≤ kappa * cutOut` for every `i`. -/
lemma rescaleMap_mem_polydisc {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {w : Fin n → ℂ}
    (hw : ∀ i, ‖w i‖ ≤ kappa * cutOut) :
    rescaleMap 0 (scl ρ) w ∈ polydisc 0 (fun j => 4 * ρ j) := by
  intro i
  show ‖rescaleMap 0 (scl ρ) w i - 0‖ < 4 * ρ i
  rw [sub_zero, norm_rescaleMap_zero_apply (scl ρ) (scl_pos hρ) w i]
  have h2 : scl ρ i * ‖w i‖ ≤ scl ρ i * (kappa * cutOut) :=
    mul_le_mul_of_nonneg_left (hw i) (scl_pos hρ i).le
  have h4 : (7 / 2 : ℝ) * ρ i * (kappa * cutOut) < 4 * ρ i := by
    have := kappa_cutOut_lt_rat
    nlinarith [hρ i]
  have : scl ρ i * ‖w i‖ ≤ (7 / 2) * ρ i * (kappa * cutOut) := by
    simpa [scl] using h2
  linarith

/-- The scaled point `S · w` lies in the polydisc of multiradii `4ρ` when `w` lies in the unit
polydisc. -/
lemma rescaleMap_mem_polydisc_one {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {w : Fin n → ℂ}
    (hw : ∀ i, ‖w i‖ < 1) :
    rescaleMap 0 (scl ρ) w ∈ polydisc 0 (fun j => 4 * ρ j) := by
  intro i
  show ‖rescaleMap 0 (scl ρ) w i - 0‖ < 4 * ρ i
  rw [sub_zero, norm_rescaleMap_zero_apply (scl ρ) (scl_pos hρ) w i]
  have h2 : scl ρ i * ‖w i‖ < scl ρ i * 1 :=
    mul_lt_mul_of_pos_left (hw i) (scl_pos hρ i)
  rw [mul_one] at h2
  have h3 : scl ρ i = (7 / 2) * ρ i := rfl
  rw [h3] at h2
  nlinarith [hρ i]

/-- The `(0,1)`-form `sclData ρ f` is continuous when `f` is continuous on the polydisc of
multiradii `4ρ`. -/
lemma continuous_sclData {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContinuousOn (f j) (polydisc 0 (fun j => 4 * ρ j)))
    (j : Fin n) : Continuous (sclData ρ f j) := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : ∃ j', kappa * cutOut < ‖w j'‖
  · have hev : sclData ρ f j =ᶠ[𝓝 w] 0 := by
      filter_upwards [cutCn_eventuallyEq_zero hw] with w' hw'
      simp only [sclData_apply, hw', Pi.zero_apply, zero_mul]
    exact (continuousAt_const : ContinuousAt (fun _ : Fin n → ℂ => (0 : ℂ)) w).congr hev.symm
  · push Not at hw
    have hmem := rescaleMap_mem_polydisc hρ hw
    have hfr : ContinuousAt (fun w' : Fin n → ℂ => f j (rescaleMap 0 (scl ρ) w')) w :=
      ((hf j).continuousAt ((isOpen_polydisc 0 (fun j => 4 * ρ j)).mem_nhds hmem)).comp
        ((contDiff_rescaleMap 0 (scl ρ)).continuous.continuousAt)
    rw [show sclData ρ f j
        = fun w' : Fin n → ℂ => cutCn w' * ((scl ρ j : ℂ) * f j (rescaleMap 0 (scl ρ) w')) from rfl]
    exact (contDiff_cutCn.continuous.continuousAt).mul (continuousAt_const.mul hfr)

/-- The scaled datum is `C^m` (`m` finite or `∞`) when `f` is `C^m` on the polydisc of
multiradii `4ρ`. -/
lemma contDiff_sclData {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {m : ℕ∞}
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiffOn ℝ m (f j) (polydisc 0 (fun j => 4 * ρ j)))
    (j : Fin n) : ContDiff ℝ m (sclData ρ f j) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : ∃ j', kappa * cutOut < ‖w j'‖
  · have hev : sclData ρ f j =ᶠ[𝓝 w] 0 := by
      filter_upwards [cutCn_eventuallyEq_zero hw] with w' hw'
      simp only [sclData_apply, hw', Pi.zero_apply, zero_mul]
    exact (contDiffAt_const : ContDiffAt ℝ m (fun _ : Fin n → ℂ => (0 : ℂ)) w).congr_of_eventuallyEq hev
  · push Not at hw
    have hmem := rescaleMap_mem_polydisc hρ hw
    have hfAt : ContDiffAt ℝ m (f j) (rescaleMap 0 (scl ρ) w) :=
      (hf j).contDiffAt ((isOpen_polydisc 0 (fun j => 4 * ρ j)).mem_nhds hmem)
    have hcomp : ContDiffAt ℝ m (fun w' : Fin n → ℂ => f j (rescaleMap 0 (scl ρ) w')) w :=
      hfAt.comp w (((contDiff_rescaleMap 0 (scl ρ)).contDiffAt).of_le le_top)
    rw [show sclData ρ f j
        = fun w' : Fin n → ℂ => cutCn w' * ((scl ρ j : ℂ) * f j (rescaleMap 0 (scl ρ) w')) from rfl]
    exact ((contDiff_cutCn.contDiffAt).of_le coe_le_infty).mul (contDiffAt_const.mul hcomp)


/-- The polydisc of multiradii `kappa * cutIn` is a neighbourhood of each of its points. -/
lemma eventually_norm_lt {n : ℕ} {w : Fin n → ℂ} {c : ℝ} (hw : ∀ m, ‖w m‖ < c) :
    {w' : Fin n → ℂ | ∀ m, ‖w' m‖ < c} ∈ 𝓝 w := by
  have hset : {w' : Fin n → ℂ | ∀ m, ‖w' m‖ < c}
      = ⋂ m : Fin n, {w' : Fin n → ℂ | ‖w' m‖ < c} := by
    ext w'; simp
  rw [hset]
  exact Filter.iInter_mem.mpr fun m =>
    (isOpen_lt ((continuous_apply m).norm) continuous_const).mem_nhds (hw m)

/-- The scaled datum agrees with the scaled datum of `f` (without cut-off) on the polydisc of
multiradii `kappa * cutIn`. -/
lemma sclData_eq {n : ℕ} {ρ : Fin n → ℝ} {f : Fin n → (Fin n → ℂ) → ℂ} {w : Fin n → ℂ}
    (hw : ∀ m, ‖w m‖ < kappa * cutIn) (j : Fin n) :
    sclData ρ f j w = (scl ρ j : ℂ) * f j (rescaleMap 0 (scl ρ) w) := by
  rw [sclData_apply, cutCn_eq_one (fun m => le_of_lt (hw m)), one_mul]

/-- `∂̄` of a constant multiple (with the differentiability hypothesis in the form needed
here). -/
lemma dbarCoord_const_mul' {n : ℕ} (j : Fin n) (c : ℂ) {g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hg : DifferentiableAt ℝ g z) :
    dbarCoord j (fun w => c * g w) z = c * dbarCoord j g z := by
  have h : fderiv ℝ (fun w => c * g w) z = c • fderiv ℝ g z := fderiv_const_mul hg c
  rw [dbarCoord, dbarCoord, h]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- The `∂̄`-derivative of the scaled datum. -/
lemma dbarCoord_sclData {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 (fun j => 4 * ρ j)))
    {w : Fin n → ℂ} (hw : ∀ m, ‖w m‖ < kappa * cutIn) (l j : Fin n) :
    dbarCoord l (sclData ρ f j) w
      = (scl ρ j : ℂ) * ((scl ρ l : ℂ) * dbarCoord l (f j) (rescaleMap 0 (scl ρ) w)) := by
  have hev : sclData ρ f j =ᶠ[𝓝 w]
      (fun w' : Fin n → ℂ => (scl ρ j : ℂ) * f j (rescaleMap 0 (scl ρ) w')) := by
    filter_upwards [eventually_norm_lt hw] with w' hw'
    rw [sclData_apply, cutCn_eq_one (fun m => le_of_lt (hw' m)), one_mul]
  rw [show dbarCoord l (sclData ρ f j) w
      = dbarCoord l (fun w' : Fin n → ℂ => (scl ρ j : ℂ) * f j (rescaleMap 0 (scl ρ) w')) w from by
    unfold dbarCoord
    rw [hev.fderiv_eq]]
  have hmemw : rescaleMap 0 (scl ρ) w ∈ polydisc 0 (fun j => 4 * ρ j) :=
    rescaleMap_mem_polydisc hρ fun i =>
      le_of_lt (lt_of_lt_of_le (hw i) (mul_le_mul_of_nonneg_left (le_of_lt cutIn_lt_cutOut)
        kappa_pos.le))
  rw [dbarCoord_const_mul' (g := fun w' : Fin n → ℂ => f j (rescaleMap 0 (scl ρ) w')) l
    (scl ρ j : ℂ)
    (((hf j).contDiffAt ((isOpen_polydisc 0 (fun j => 4 * ρ j)).mem_nhds hmemw)
      |>.differentiableAt (by simp)).comp w
      ((contDiff_rescaleMap 0 (scl ρ)).contDiffAt.differentiableAt (by simp)))]
  have h2 : dbarCoord l (fun w' : Fin n → ℂ => f j (rescaleMap 0 (scl ρ) w')) w
      = (scl ρ l : ℂ) * dbarCoord l (f j) (rescaleMap 0 (scl ρ) w) := by
    simpa only [rescaleMap_zero_eq] using
      (Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine (scl ρ) (0 : Fin n → ℂ) l (U := f j)
        (z := w) ((hf j).contDiffAt ((isOpen_polydisc 0 (fun j => 4 * ρ j)).mem_nhds hmemw)
          |>.differentiableAt (by simp)))
  rw [h2]

/-- The scaled datum is closed (as a `(0,1)`-form) on the polydisc of multiradii
`kappa * cutIn` when `f` is closed on the polydisc of multiradii `4ρ`. -/
lemma isClosedForm_sclData {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 (fun j => 4 * ρ j)))
    (hfcl : ∀ j l z, z ∈ polydisc 0 (fun j => 4 * ρ j) → dbarCoord l (f j) z = dbarCoord j (f l) z)
    {w : Fin n → ℂ} (hw : ∀ m, ‖w m‖ < kappa * cutIn) (j l : Fin n) :
    dbarCoord l (sclData ρ f j) w = dbarCoord j (sclData ρ f l) w := by
  rw [dbarCoord_sclData hρ hf hw l j, dbarCoord_sclData hρ hf hw j l]
  have hmem : rescaleMap 0 (scl ρ) w ∈ polydisc 0 (fun j => 4 * ρ j) :=
    rescaleMap_mem_polydisc hρ fun i =>
      le_of_lt (lt_of_lt_of_le (hw i) (mul_le_mul_of_nonneg_left (le_of_lt cutIn_lt_cutOut)
        kappa_pos.le))
  rw [hfcl j l (rescaleMap 0 (scl ρ) w) hmem]
  ring

/-- The scaling factor `scaleR (scl ρ)` is positive. -/
lemma scaleR_scl_pos {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    0 < scaleR (scl ρ) := by
  rw [scaleR_eq]
  have : 0 ≤ ∑ i, scl ρ i := Finset.sum_nonneg fun i _ => (scl_pos hρ i).le
  linarith

/-- The size of the scaled datum on the unit polydisc, in terms of the size of `f` on the
polydisc of multiradii `4ρ`. -/
lemma exists_holderNorm_sclData_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (j : Fin n) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 (fun j => 4 * ρ j))) →
      holderNorm 0 α (sclData ρ f j) (polydisc 0 (fun _ => 1))
        ≤ ENNReal.ofReal K * holderNorm 0 α (f j) (polydisc 0 (fun j => 4 * ρ j)) := by
  obtain ⟨Kc, hKc, hKc'⟩ := exists_holderNorm_cutCn_bound (n := n) hα hα1
  refine ⟨max 1 (2 * (Kc + 1) * (scl ρ j * (1 + (scaleR (scl ρ)) ^ α))), ?_, ?_⟩
  · exact lt_max_of_lt_left one_pos
  · intro f hf
    by_cases htop : holderNorm 0 α (f j) (polydisc 0 (fun j => 4 * ρ j)) = ⊤
    · rw [htop, ENNReal.mul_top
        (ENNReal.ofReal_ne_zero_iff.mpr (lt_max_of_lt_left one_pos))]
      exact le_top
    · have hKcfin : holderNorm 0 α (cutCn : (Fin n → ℂ) → ℂ) (polydisc 0 (fun _ => 1)) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKc'
      have hKc'' : holderNorm 0 α (cutCn : (Fin n → ℂ) → ℂ) (polydisc 0 (fun _ => 1))
          ≤ ENNReal.ofReal (Kc + 1) := hKc'.trans (ENNReal.ofReal_le_ofReal (by linarith))
      have hmapsto : MapsTo (rescaleMap 0 (scl ρ)) (polydisc 0 (fun _ => 1))
          (polydisc 0 (fun j => 4 * ρ j)) := by
        intro w hw'
        refine rescaleMap_mem_polydisc_one hρ fun i => ?_
        simpa using hw' i
      have hcont : ContDiffOn ℝ (0 : ℕ∞)
          (fun w' : Fin n → ℂ => f j (rescaleMap 0 (scl ρ) w'))
          (polydisc 0 (fun _ => 1)) :=
        (((hf j)).comp (((contDiff_rescaleMap 0 (scl ρ)).contDiffOn).of_le le_top)
          hmapsto).of_le (by norm_num)
      have huzero : UniqueDiffOn ℝ (polydisc (0 : Fin n → ℂ) (fun _ => 1)) :=
        (isOpen_polydisc (0 : Fin n → ℂ) (fun _ => 1)).uniqueDiffOn
      have hcomp := Work.CR.Flat.Holder.holderNorm_zero_comp_le (hα := hα)
        (hM := (scaleR_scl_pos hρ).le)
        (Ω := polydisc 0 (fun _ => 1)) (Ω' := polydisc 0 (fun j => 4 * ρ j))
        (Φ := rescaleMap 0 (scl ρ)) (U := f j) (M := scaleR (scl ρ))
        hmapsto (fun x _ y _ => norm_rescaleMap_sub_le (fun i => (scl_pos hρ i).le) x y)
      have hmax : max 1 (ENNReal.ofReal ((scaleR (scl ρ)) ^ α))
          ≤ ENNReal.ofReal (1 + (scaleR (scl ρ)) ^ α) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_max]
        refine ENNReal.ofReal_le_ofReal ?_
        have hv : (0 : ℝ) ≤ (scaleR (scl ρ)) ^ α := Real.rpow_nonneg (scaleR_scl_pos hρ).le α
        exact max_le (le_add_of_nonneg_right hv) (le_add_of_nonneg_left zero_le_one)
      have hmaxne : max 1 (ENNReal.ofReal ((scaleR (scl ρ)) ^ α)) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmax
      have hcompfin : holderNorm 0 α (fun w' : Fin n → ℂ => f j (rescaleMap 0 (scl ρ) w'))
          (polydisc 0 (fun _ => 1)) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.mul_ne_top hmaxne htop) hcomp
      have hsmul : holderNorm 0 α
          (fun w' : Fin n → ℂ => (scl ρ j : ℂ) * f j (rescaleMap 0 (scl ρ) w'))
          (polydisc 0 (fun _ => 1))
          = ENNReal.ofReal (scl ρ j)
            * holderNorm 0 α (fun w' : Fin n → ℂ => f j (rescaleMap 0 (scl ρ) w'))
              (polydisc 0 (fun _ => 1)) := by
        have h1 : (fun w' : Fin n → ℂ => (scl ρ j : ℂ) * f j (rescaleMap 0 (scl ρ) w'))
            = (scl ρ j : ℂ) • (fun w' : Fin n → ℂ => f j (rescaleMap 0 (scl ρ) w')) := by
          funext w'
          simp only [Pi.smul_apply, smul_eq_mul]
        rw [h1, Work.CR.Flat.Holder.holderNorm_smul (k := 0) (α := α) (c := (scl ρ j : ℂ))
          (f := fun w' : Fin n → ℂ => f j (rescaleMap 0 (scl ρ) w')) hcont huzero,
          Complex.norm_real, Real.norm_of_nonneg (scl_pos hρ j).le]
      have hsmulfin : holderNorm 0 α
          (fun w' : Fin n → ℂ => (scl ρ j : ℂ) * f j (rescaleMap 0 (scl ρ) w'))
          (polydisc 0 (fun _ => 1)) ≠ ⊤ := by
        rw [hsmul]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcompfin
      have hmul := Work.CR.Flat.Holder.holderNorm_mul_le (k := 0) (α := α)
        (f := cutCn) (g := fun w' : Fin n → ℂ => (scl ρ j : ℂ) * f j (rescaleMap 0 (scl ρ) w'))
        (Ω := polydisc 0 (fun _ => 1))
        ((contDiff_cutCn.contDiffOn).of_le (by simp))
        ((contDiff_const.contDiffOn).mul hcont) huzero hKcfin hsmulfin
      refine hmul.trans ?_
      rw [hsmul]
      simp only [Nat.cast_zero, zero_add, pow_one, one_mul]
      have e1 : (2 : ℝ≥0∞) * ENNReal.ofReal (Kc + 1) = ENNReal.ofReal (2 * (Kc + 1)) := by
        rw [(ENNReal.ofReal_ofNat 2).symm, ← ENNReal.ofReal_mul (by norm_num)]
      calc (2 : ℝ≥0∞) * holderNorm 0 α (cutCn : (Fin n → ℂ) → ℂ) (polydisc 0 (fun _ => 1))
            * (ENNReal.ofReal (scl ρ j)
              * holderNorm 0 α (fun w' : Fin n → ℂ => f j (rescaleMap 0 (scl ρ) w'))
                (polydisc 0 (fun _ => 1)))
          ≤ (2 : ℝ≥0∞) * ENNReal.ofReal (Kc + 1)
            * (ENNReal.ofReal (scl ρ j)
              * (max 1 (ENNReal.ofReal ((scaleR (scl ρ)) ^ α))
                * holderNorm 0 α (f j) (polydisc 0 (fun j => 4 * ρ j)))) :=
            mul_le_mul' (mul_le_mul' le_rfl hKc'') (mul_le_mul' le_rfl hcomp)
        _ ≤ (2 : ℝ≥0∞) * ENNReal.ofReal (Kc + 1)
            * (ENNReal.ofReal (scl ρ j)
              * (ENNReal.ofReal (1 + (scaleR (scl ρ)) ^ α)
                * holderNorm 0 α (f j) (polydisc 0 (fun j => 4 * ρ j)))) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hmax le_rfl))
        _ = ENNReal.ofReal (2 * (Kc + 1) * (scl ρ j * (1 + (scaleR (scl ρ)) ^ α)))
            * holderNorm 0 α (f j) (polydisc 0 (fun j => 4 * ρ j)) := by
            have e4 : ENNReal.ofReal (scl ρ j)
                * (ENNReal.ofReal (1 + (scaleR (scl ρ)) ^ α)
                  * holderNorm 0 α (f j) (polydisc 0 (fun j => 4 * ρ j)))
                = ENNReal.ofReal (scl ρ j * (1 + (scaleR (scl ρ)) ^ α))
                  * holderNorm 0 α (f j) (polydisc 0 (fun j => 4 * ρ j)) := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (scl_pos hρ j).le]
            have e5 : ENNReal.ofReal (2 * (Kc + 1))
                  * (ENNReal.ofReal (scl ρ j * (1 + (scaleR (scl ρ)) ^ α))
                    * holderNorm 0 α (f j) (polydisc 0 (fun j => 4 * ρ j)))
                = ENNReal.ofReal (2 * (Kc + 1) * (scl ρ j * (1 + (scaleR (scl ρ)) ^ α)))
                  * holderNorm 0 α (f j) (polydisc 0 (fun j => 4 * ρ j)) := by
              rw [← mul_assoc,
                ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (by linarith))]
            rw [e1, e4, e5]
        _ ≤ ENNReal.ofReal (max 1 (2 * (Kc + 1) * (scl ρ j * (1 + (scaleR (scl ρ)) ^ α))))
            * holderNorm 0 α (f j) (polydisc 0 (fun j => 4 * ρ j)) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl

end Work.NN.Final
