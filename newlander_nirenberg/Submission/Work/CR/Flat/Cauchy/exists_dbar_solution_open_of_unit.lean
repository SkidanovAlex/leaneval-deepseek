import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolDefs
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Holder.holderNorm_zero_comp_le
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-! ## The diagonal affine rescaling

To deduce the `∂̄`-solvability on an arbitrary polydisc `polydisc c r` from the
corresponding statement on the *unit* polydisc at the origin (radius `1` in every
coordinate, the equation being solved on `solveSet`, the polydisc of radius
`eqRad = 3/4`), we transport the data along the diagonal affine isomorphism

`rescaleMap c r : w ↦ (i ↦ c i + (r i : ℂ) * w i)`,

which maps `polydisc 0 1` onto `polydisc c r` and `solveSet` into `polydisc c (3r/4)`.
If `U` solves `∂̄_j U = r_j · (f_j ∘ rescaleMap)` on `solveSet`, then
`u = U ∘ invRescaleMap` solves `∂̄_j u = f_j` on `polydisc c (3r/4)`, and the
`C^{0,α}` norms are controlled by the Lipschitz constants of `rescaleMap` and
`invRescaleMap`.
-/

/-- The diagonal affine map `w ↦ (i ↦ c i + (r i : ℂ) * w i)`. -/
noncomputable def rescaleMap {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    (Fin n → ℂ) → (Fin n → ℂ) :=
  fun w i => c i + (r i : ℂ) * w i

/-- The inverse of `rescaleMap c r`, written in the affine form used by the chain
rule `dbarCoord_comp_diagAffine`. -/
noncomputable def invRescaleMap {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    (Fin n → ℂ) → (Fin n → ℂ) :=
  fun z i => -(c i) / (r i : ℂ) + (((r i)⁻¹ : ℝ) : ℂ) * z i

@[simp] lemma rescaleMap_apply {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) (w : Fin n → ℂ)
    (i : Fin n) : rescaleMap c r w i = c i + (r i : ℂ) * w i := rfl

@[simp] lemma invRescaleMap_apply {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) (z : Fin n → ℂ)
    (i : Fin n) :
    invRescaleMap c r z i = -(c i) / (r i : ℂ) + (((r i)⁻¹ : ℝ) : ℂ) * z i := rfl

/-- The quotient form of the inverse rescaling. -/
lemma invRescaleMap_apply_eq_div {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} (hr : ∀ i, r i ≠ 0)
    (z : Fin n → ℂ) (i : Fin n) : invRescaleMap c r z i = (z i - c i) / (r i : ℂ) := by
  rw [invRescaleMap_apply, Complex.ofReal_inv]
  have hri : (r i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr i)
  field_simp
  ring

lemma rescaleMap_invRescaleMap {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} (hr : ∀ i, r i ≠ 0)
    (z : Fin n → ℂ) : rescaleMap c r (invRescaleMap c r z) = z := by
  funext i
  rw [rescaleMap_apply, invRescaleMap_apply, Complex.ofReal_inv]
  have hri : (r i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr i)
  field_simp
  ring

lemma invRescaleMap_rescaleMap {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} (hr : ∀ i, r i ≠ 0)
    (w : Fin n → ℂ) : invRescaleMap c r (rescaleMap c r w) = w := by
  funext i
  rw [invRescaleMap_apply, rescaleMap_apply, Complex.ofReal_inv]
  have hri : (r i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr i)
  field_simp
  ring

lemma contDiff_rescaleMap {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    ContDiff ℝ ⊤ (rescaleMap c r) := by
  change ContDiff ℝ ⊤ (fun w : Fin n → ℂ => fun i => c i + (r i : ℂ) * w i)
  fun_prop

lemma contDiff_invRescaleMap {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    ContDiff ℝ ⊤ (invRescaleMap c r) := by
  change ContDiff ℝ ⊤
    (fun z : Fin n → ℂ => fun i => -(c i) / (r i : ℂ) + (((r i)⁻¹ : ℝ) : ℂ) * z i)
  fun_prop

/-- A Lipschitz constant for `rescaleMap c r`. -/
noncomputable def scaleR {n : ℕ} (r : Fin n → ℝ) : ℝ := 1 + ∑ i, r i

/-- A Lipschitz constant for `invRescaleMap c r`. -/
noncomputable def scaleRinv {n : ℕ} (r : Fin n → ℝ) : ℝ := 1 + ∑ i, (r i)⁻¹

lemma scaleR_eq {n : ℕ} (r : Fin n → ℝ) : scaleR r = 1 + ∑ i, r i := rfl
lemma scaleRinv_eq {n : ℕ} (r : Fin n → ℝ) : scaleRinv r = 1 + ∑ i, (r i)⁻¹ := rfl

lemma norm_diag_mul_sub_le {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (x y : Fin n → ℂ) :
    ‖(fun i => (a i : ℂ) * (x i - y i))‖ ≤ (1 + ∑ i, a i) * ‖x - y‖ := by
  have hsum : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun j _ => ha j)
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  have h1 : ‖(a i : ℂ) * (x i - y i)‖ = a i * ‖x i - y i‖ := by
    rw [norm_mul]
    simp [abs_of_nonneg (ha i)]
  rw [h1]
  have h2 : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  have h3 : ‖x i - y i‖ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) i
  calc a i * ‖x i - y i‖ ≤ (∑ j, a j) * ‖x - y‖ := mul_le_mul h2 h3 (norm_nonneg _) hsum
    _ ≤ (1 + ∑ j, a j) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

lemma norm_rescaleMap_sub_le {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} (hr : ∀ i, 0 ≤ r i)
    (x y : Fin n → ℂ) :
    ‖rescaleMap c r x - rescaleMap c r y‖ ≤ scaleR r * ‖x - y‖ := by
  have h : rescaleMap c r x - rescaleMap c r y = fun i => (r i : ℂ) * (x i - y i) := by
    funext i
    simp only [Pi.sub_apply, rescaleMap_apply]
    ring
  rw [h, scaleR_eq]
  exact norm_diag_mul_sub_le r hr x y

lemma norm_invRescaleMap_sub_le {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    (x y : Fin n → ℂ) :
    ‖invRescaleMap c r x - invRescaleMap c r y‖ ≤ scaleRinv r * ‖x - y‖ := by
  have h : invRescaleMap c r x - invRescaleMap c r y
      = fun i => (((r i)⁻¹ : ℝ) : ℂ) * (x i - y i) := by
    funext i
    simp only [Pi.sub_apply, invRescaleMap_apply]
    ring
  rw [h, scaleRinv_eq]
  exact norm_diag_mul_sub_le (fun i => (r i)⁻¹)
    (fun i => inv_nonneg.mpr (le_of_lt (hr i))) x y

lemma mapsTo_rescaleMap_polydisc {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    MapsTo (rescaleMap c r) (polydisc 0 (fun _ => 1)) (polydisc c r) := by
  intro w hw
  rw [mem_polydisc] at hw ⊢
  intro i
  have hw' : ‖w i‖ < 1 := by simpa using hw i
  have h1 : ‖(r i : ℂ) * w i‖ = r i * ‖w i‖ := by
    rw [norm_mul]
    simp [abs_of_nonneg (le_of_lt (hr i))]
  have h0 : rescaleMap c r w i - c i = (r i : ℂ) * w i := by
    rw [rescaleMap_apply]; ring
  rw [h0, h1]
  calc r i * ‖w i‖ < r i * 1 := mul_lt_mul_of_pos_left hw' (hr i)
    _ = r i := by ring

lemma mapsTo_rescaleMap_solveSet {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    MapsTo (rescaleMap c r) solveSet (polydisc c (fun j => 3 * r j / 4)) := by
  intro w hw
  rw [mem_solveSet] at hw
  rw [mem_polydisc]
  intro i
  have h1 : ‖(r i : ℂ) * w i‖ = r i * ‖w i‖ := by
    rw [norm_mul]
    simp [abs_of_nonneg (le_of_lt (hr i))]
  have h0 : rescaleMap c r w i - c i = (r i : ℂ) * w i := by
    rw [rescaleMap_apply]; ring
  rw [h0, h1]
  calc r i * ‖w i‖ < r i * eqRad := mul_lt_mul_of_pos_left (hw i) (hr i)
    _ = 3 * r i / 4 := by rw [eqRad]; ring

lemma mapsTo_invRescaleMap {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    MapsTo (invRescaleMap c r) (polydisc c (fun j => 3 * r j / 4)) solveSet := by
  intro z hz
  rw [mem_polydisc] at hz
  rw [mem_solveSet]
  intro i
  have hri : r i ≠ 0 := ne_of_gt (hr i)
  rw [invRescaleMap_apply_eq_div (fun j => ne_of_gt (hr j)) z i, norm_div]
  have hnorm : ‖((r i : ℝ) : ℂ)‖ = r i := by simp [abs_of_nonneg (le_of_lt (hr i))]
  rw [hnorm, eqRad, div_lt_iff₀ (hr i)]
  linarith [hz i]

/-- `∂̄` of a constant multiple. -/
private lemma dbarCoord_const_mul_diff {n : ℕ} (j : Fin n) (c : ℂ) {g : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (hg : DifferentiableAt ℝ g z) :
    dbarCoord j (fun w => c * g w) z = c * dbarCoord j g z := by
  have h : fderiv ℝ (fun w => c * g w) z = c • fderiv ℝ g z := fderiv_const_mul hg c
  rw [dbarCoord, dbarCoord, h]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- **The `∂̄`-Poincaré statement on an arbitrary polydisc, from the unit polydisc.**
If the flat `∂̄`-equation is solvable on the unit polydisc `polydisc 0 1` with the
equation holding on `solveSet` and with a `C^{0,α}` bound, then it is solvable on
every polydisc `polydisc c r` (`r j > 0`) with the equation holding on
`polydisc c (3r/4)` and a bound of the same shape.  The passage uses the diagonal
affine rescaling `rescaleMap c r` and the chain rule for `∂̄`. -/
theorem exists_dbar_solution_open_of_unit {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (hα1 : α < 1) (k : ℕ)
    (H : ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ (k + 1) (f j)) →
      IsClosedForm f →
      ∃ u : (Fin n → ℂ) → ℂ, ContDiff ℝ (k + 1) u ∧
        (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ < eqRad) → dbarCoord j u z = f j z) ∧
        holderNorm 0 α u solveSet ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))) :
    ∀ (c : Fin n → ℂ) (r : Fin n → ℝ), (∀ j, 0 < r j) →
      ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ (k + 1) (f j)) →
        IsClosedForm f →
        ∃ u : (Fin n → ℂ) → ℂ, ContDiff ℝ (k + 1) u ∧
          (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < 3 * r i / 4) → dbarCoord j u z = f j z) ∧
          holderNorm 0 α u (polydisc c (fun j => 3 * r j / 4))
            ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (f j) (polydisc c r) := by
  intro c r hr
  have _hn : 0 < n := hn
  obtain ⟨C₀, hC₀pos, hC₀prop⟩ := H
  set R : ℝ := scaleR r with hR
  set Rinv : ℝ := scaleRinv r with hRinv
  set K : ℝ := max 1 (R ^ α) with hK
  set Kinv : ℝ := max 1 (Rinv ^ α) with hKinv
  have hrnn : ∀ i, 0 ≤ r i := fun i => le_of_lt (hr i)
  have hRpos : 0 < R := by
    rw [hR, scaleR_eq]
    have : 0 ≤ ∑ i, r i := Finset.sum_nonneg (fun i _ => hrnn i)
    linarith
  have hRinvpos : 0 < Rinv := by
    rw [hRinv, scaleRinv_eq]
    have : 0 ≤ ∑ i, (r i)⁻¹ := Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hrnn i))
    linarith
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hKinvpos : 0 < Kinv := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨Kinv * (C₀ * (R * K)), by positivity, ?_⟩
  intro f hf hcl
  -- smoothness of the rescaling maps
  have hres : ContDiff ℝ (k + 1) (rescaleMap c r) := (contDiff_rescaleMap c r).of_le le_top
  have hinv : ContDiff ℝ (k + 1) (invRescaleMap c r) := (contDiff_invRescaleMap c r).of_le le_top
  -- the rescaled data
  set F : Fin n → (Fin n → ℂ) → ℂ :=
    fun j w => (r j : ℂ) * f j (rescaleMap c r w) with hF
  have hFsm : ∀ j, ContDiff ℝ (k + 1) (F j) := by
    intro j
    have h1 : ContDiff ℝ (k + 1) (fun w : Fin n → ℂ => f j (rescaleMap c r w)) := by
      simpa only [Function.comp_def] using (hf j).comp hres
    have h2 : ContDiff ℝ (k + 1) (fun w : Fin n → ℂ => (r j : ℂ) * f j (rescaleMap c r w)) :=
      contDiff_const.mul h1
    simpa only [hF] using h2
  -- the chain rule for the rescaled data
  have hchain : ∀ (j l : Fin n) (w : Fin n → ℂ),
      dbarCoord l (fun w' => f j (rescaleMap c r w')) w
        = (r l : ℂ) * dbarCoord l (f j) (rescaleMap c r w) := by
    intro j l w
    exact Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine r c l (U := f j) (z := w)
      ((hf j).contDiffAt.differentiableAt (by simp))
  have hFcl : IsClosedForm F := by
    intro j l w
    have h1 : dbarCoord l (F j) w
        = (r j : ℂ) * dbarCoord l (fun w' => f j (rescaleMap c r w')) w := by
      rw [hF]
      exact dbarCoord_const_mul_diff l (r j : ℂ)
        ((hf j).contDiffAt.differentiableAt (by simp) |>.comp w
          (hres.contDiffAt.differentiableAt (by simp)))
    have h2 : dbarCoord j (F l) w
        = (r l : ℂ) * dbarCoord j (fun w' => f l (rescaleMap c r w')) w := by
      rw [hF]
      exact dbarCoord_const_mul_diff j (r l : ℂ)
        ((hf l).contDiffAt.differentiableAt (by simp) |>.comp w
          (hres.contDiffAt.differentiableAt (by simp)))
    rw [h1, h2, hchain j l w, hchain l j w, hcl l j (rescaleMap c r w)]
    ring
  obtain ⟨U, hUsm, hUeq, hUbound⟩ := hC₀prop F hFsm hFcl
  have hUdiff : Differentiable ℝ U := hUsm.differentiable (by simp)
  -- the solution on `polydisc c r`
  refine ⟨fun z => U (invRescaleMap c r z), ?_, ?_, ?_⟩
  · exact hUsm.comp hinv
  · intro j z hz
    have hchain' : dbarCoord j (fun z' => U (invRescaleMap c r z')) z
        = (((r j)⁻¹ : ℝ) : ℂ) * dbarCoord j U (invRescaleMap c r z) := by
      exact Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine (fun i => (r i)⁻¹) (fun i => -(c i) / (r i : ℂ)) j
        (U := U) (z := z) (hUdiff.differentiableAt)
    have hψ : invRescaleMap c r z ∈ solveSet := mapsTo_invRescaleMap hr hz
    rw [hchain', hUeq j (invRescaleMap c r z) hψ]
    simp only [hF]
    rw [rescaleMap_invRescaleMap (fun i => ne_of_gt (hr i)) z, Complex.ofReal_inv]
    have hrj : (r j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hr j))
    field_simp
  · -- the norm bound
    have hsol : holderNorm 0 α (fun z => U (invRescaleMap c r z))
          (polydisc c (fun j => 3 * r j / 4))
        ≤ ENNReal.ofReal Kinv * holderNorm 0 α U solveSet := by
      have h := Work.CR.Flat.Holder.holderNorm_zero_comp_le (hα := hα) (hM := le_of_lt hRinvpos)
        (Ω := polydisc c (fun j => 3 * r j / 4)) (Ω' := solveSet)
        (Φ := invRescaleMap c r) (U := U) (M := Rinv)
        (mapsTo_invRescaleMap hr) (fun x _ y _ => norm_invRescaleMap_sub_le hr x y)
      have he : max 1 (ENNReal.ofReal (Rinv ^ α)) = ENNReal.ofReal Kinv := by
        rw [hKinv, ENNReal.ofReal_max, ENNReal.ofReal_one]
      rwa [he] at h
    have hdata : (∑ j, holderNorm 0 α (F j) (polydisc 0 (fun _ => 1)))
        ≤ ENNReal.ofReal (R * K) * ∑ j, holderNorm 0 α (f j) (polydisc c r) := by
      have hper : ∀ j, holderNorm 0 α (F j) (polydisc 0 (fun _ => 1))
          ≤ ENNReal.ofReal (R * K) * holderNorm 0 α (f j) (polydisc c r) := by
        intro j
        -- pull the constant `r j` out of the norm
        have hsm : holderNorm 0 α (F j) (polydisc 0 (fun _ => 1))
            = ENNReal.ofReal (r j)
              * holderNorm 0 α (fun w => f j (rescaleMap c r w)) (polydisc 0 (fun _ => 1)) := by
          have hcd : ContDiffOn ℝ (0 : ℕ∞) (fun w : Fin n → ℂ => f j (rescaleMap c r w))
              (polydisc (0 : Fin n → ℂ) (fun _ : Fin n => 1)) :=
            ((hf j).comp hres).contDiffOn.of_le (by simp)
          have hud : UniqueDiffOn ℝ (polydisc (0 : Fin n → ℂ) (fun _ : Fin n => 1)) :=
            (isOpen_polydisc _ _).uniqueDiffOn
          have h := Work.CR.Flat.Holder.holderNorm_smul (k := 0) (α := α)
            (Ω := polydisc (0 : Fin n → ℂ) (fun _ : Fin n => 1))
            (c := (r j : ℂ)) (f := fun w : Fin n → ℂ => f j (rescaleMap c r w)) hcd hud
          have e : F j = (r j : ℂ) • (fun w : Fin n → ℂ => f j (rescaleMap c r w)) := by
            rw [hF]
            funext w
            rfl
          rw [e, h]
          simp [abs_of_nonneg (hrnn j)]
        -- the composition with the rescaling
        have hcomp : holderNorm 0 α (fun w => f j (rescaleMap c r w)) (polydisc 0 (fun _ => 1))
            ≤ ENNReal.ofReal K * holderNorm 0 α (f j) (polydisc c r) := by
          have h := Work.CR.Flat.Holder.holderNorm_zero_comp_le (hα := hα) (hM := le_of_lt hRpos)
            (Ω := polydisc 0 (fun _ => 1)) (Ω' := polydisc c r)
            (Φ := rescaleMap c r) (U := f j) (M := R)
            (mapsTo_rescaleMap_polydisc hr) (fun x _ y _ => norm_rescaleMap_sub_le hrnn x y)
          have he : max 1 (ENNReal.ofReal (R ^ α)) = ENNReal.ofReal K := by
            rw [hK, ENNReal.ofReal_max, ENNReal.ofReal_one]
          rwa [he] at h
        have hrjR : r j ≤ R := by
          rw [hR, scaleR_eq]
          have := Finset.single_le_sum (fun i _ => hrnn i) (Finset.mem_univ j)
          linarith
        calc holderNorm 0 α (F j) (polydisc 0 (fun _ => 1))
            = ENNReal.ofReal (r j)
              * holderNorm 0 α (fun w => f j (rescaleMap c r w)) (polydisc 0 (fun _ => 1)) := hsm
          _ ≤ ENNReal.ofReal (r j)
              * (ENNReal.ofReal K * holderNorm 0 α (f j) (polydisc c r)) :=
              mul_le_mul_right hcomp _
          _ = ENNReal.ofReal (r j * K) * holderNorm 0 α (f j) (polydisc c r) := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (hrnn j)]
          _ ≤ ENNReal.ofReal (R * K) * holderNorm 0 α (f j) (polydisc c r) := by
              refine mul_le_mul_left ?_ _
              exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hrjR hKpos.le)
      calc (∑ j, holderNorm 0 α (F j) (polydisc 0 (fun _ => 1)))
          ≤ ∑ j, ENNReal.ofReal (R * K) * holderNorm 0 α (f j) (polydisc c r) :=
            Finset.sum_le_sum (fun j _ => hper j)
        _ = ENNReal.ofReal (R * K) * ∑ j, holderNorm 0 α (f j) (polydisc c r) := by
            rw [Finset.mul_sum]
    calc holderNorm 0 α (fun z => U (invRescaleMap c r z)) (polydisc c (fun j => 3 * r j / 4))
        ≤ ENNReal.ofReal Kinv * holderNorm 0 α U solveSet := hsol
      _ ≤ ENNReal.ofReal Kinv
            * (ENNReal.ofReal C₀ * ∑ j, holderNorm 0 α (F j) (polydisc 0 (fun _ => 1))) :=
          mul_le_mul_right hUbound _
      _ ≤ ENNReal.ofReal Kinv
            * (ENNReal.ofReal C₀
              * (ENNReal.ofReal (R * K) * ∑ j, holderNorm 0 α (f j) (polydisc c r))) :=
          mul_le_mul_right (mul_le_mul_right hdata _) _
      _ = ENNReal.ofReal (Kinv * (C₀ * (R * K)))
            * ∑ j, holderNorm 0 α (f j) (polydisc c r) := by
          have hconst : ENNReal.ofReal (Kinv * (C₀ * (R * K)))
              = ENNReal.ofReal Kinv * ENNReal.ofReal C₀ * ENNReal.ofReal (R * K) := by
            rw [ENNReal.ofReal_mul (le_of_lt hKinvpos), ENNReal.ofReal_mul hC₀pos.le]
            ring
          rw [hconst]
          ring

end Work.CR.Flat.Cauchy
