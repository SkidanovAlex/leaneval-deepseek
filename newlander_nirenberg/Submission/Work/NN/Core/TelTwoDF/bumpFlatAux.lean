/-
Auxiliary facts, used by `Work.NN.Core.TelTwoDF.holderNorm_bump_mul_le`, about a `C^{k+1}`
function `χ` which vanishes on the closed exterior `{z | ∃ j, ρ j ≤ ‖z j‖}` of the open
polydisc `polydisc 0 ρ` (with `ρ j > 0`): such a function is *flat* of order `k + 1` on that
closed exterior, and its iterated derivatives decay with the distance to the exterior.
-/
import Mathlib
import Submission.Work.CR.Flat.Polydisc

noncomputable section

namespace Work.NN.Core.TelTwoDF

open scoped NNReal ENNReal
open Set

variable {n : ℕ}

/-- Subtraction commutes with `curryLeft`, isometrically. -/
lemma norm_curryLeft_sub {i : ℕ}
    (p q : ContinuousMultilinearMap ℝ (fun _ : Fin (i + 1) => (Fin n → ℂ)) ℂ) :
    ‖p.curryLeft - q.curryLeft‖ = ‖p - q‖ := by
  rw [show p.curryLeft - q.curryLeft = (p - q).curryLeft from by
    ext v m
    simp [ContinuousMultilinearMap.curryLeft_apply]]
  exact ContinuousMultilinearMap.curryLeft_norm _

/-- The closed exterior `{z | ∃ j, ρ j ≤ ‖z j‖}` of the open polydisc `polydisc 0 ρ`, for
positive radii, is the closure of the *open* exterior `{z | ∃ j, ρ j < ‖z j‖}`. -/
lemma closure_openExterior {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    closure {z : Fin n → ℂ | ∃ j, ρ j < ‖z j‖} = {z : Fin n → ℂ | ∃ j, ρ j ≤ ‖z j‖} := by
  apply Subset.antisymm
  · refine closure_minimal ?_ ?_
    · rintro z ⟨j, hj⟩
      exact ⟨j, le_of_lt hj⟩
    · rw [show {z : Fin n → ℂ | ∃ j, ρ j ≤ ‖z j‖}
            = ⋃ j, {z : Fin n → ℂ | ρ j ≤ ‖z j‖} from by ext z; simp]
      exact isClosed_iUnion_of_finite fun j =>
        isClosed_le continuous_const ((continuous_apply j).norm)
  · intro z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨j, hj⟩ := hz
    have hzj : 0 < ‖z j‖ := lt_of_lt_of_le (hρ j) hj
    have hδpos : 0 < ε / (‖z j‖ + 1) := div_pos hε (by positivity)
    refine ⟨Function.update z j ((1 + ε / (‖z j‖ + 1)) • z j), ⟨j, ?_⟩, ?_⟩
    · rw [Function.update_self, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 + ε / (‖z j‖ + 1))]
      have h2 : 0 < (ε / (‖z j‖ + 1)) * ‖z j‖ := mul_pos hδpos hzj
      have h1 : (1 + ε / (‖z j‖ + 1)) * ‖z j‖ = ‖z j‖ + (ε / (‖z j‖ + 1)) * ‖z j‖ := by ring
      linarith [hρ j, hj, h2, h1]
    · rw [dist_eq_norm,
        show z - Function.update z j ((1 + ε / (‖z j‖ + 1)) • z j)
          = Pi.single j (z j - (1 + ε / (‖z j‖ + 1)) • z j) from by
            ext i
            by_cases hi : i = j
            · subst hi; simp [Pi.single_eq_same]
            · simp [Pi.single_eq_of_ne hi, Function.update_of_ne hi],
        Pi.norm_single]
      have he : z j - (1 + ε / (‖z j‖ + 1)) • z j = -(ε / (‖z j‖ + 1)) • z j := by module
      rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos]
      have hlt : ‖z j‖ / (‖z j‖ + 1) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      calc ε / (‖z j‖ + 1) * ‖z j‖ = ε * (‖z j‖ / (‖z j‖ + 1)) := by field_simp
        _ < ε * 1 := mul_lt_mul_of_pos_left hlt hε
        _ = ε := mul_one ε

/-- A `C^{k+1}` function which vanishes on the closed exterior of the open polydisc `polydisc 0 ρ`
is flat of order `k + 1` there: all its iterated derivatives of order at most `k + 1` vanish at
every point of the closed exterior. -/
lemma iteratedFDeriv_eq_zero_of_notMem_polydisc {k : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (k + 1) χ)
    (hχ0 : ∀ z : Fin n → ℂ, (∃ j, ρ j ≤ ‖z j‖) → χ z = 0)
    {m : ℕ} (hm : m ≤ k + 1) {z : Fin n → ℂ} (hz : ∃ j, ρ j ≤ ‖z j‖) :
    iteratedFDeriv ℝ m χ z = 0 := by
  set U : Set (Fin n → ℂ) := {w | ∃ i, ρ i < ‖w i‖} with hU
  have hUopen : IsOpen U := by
    rw [show U = ⋃ i, {w : Fin n → ℂ | ρ i < ‖w i‖} from by ext w; simp [hU]]
    exact isOpen_iUnion fun i => isOpen_lt continuous_const ((continuous_apply i).norm)
  have hvan : Set.EqOn (iteratedFDeriv ℝ m χ)
      (fun _ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => (Fin n → ℂ)) ℂ)) U := by
    intro y hy
    have hA : iteratedFDerivWithin ℝ m χ U y
        = iteratedFDerivWithin ℝ m (fun _ => (0 : ℂ)) U y :=
      iteratedFDerivWithin_congr
        (fun w hw => hχ0 w (by obtain ⟨i, hi⟩ := hw; exact ⟨i, le_of_lt hi⟩)) hy m
    have hB : iteratedFDerivWithin ℝ m χ U y = iteratedFDeriv ℝ m χ y :=
      (iteratedFDerivWithin_of_isOpen (s := U) m hUopen) hy
    have hC : iteratedFDerivWithin ℝ m (fun _ => (0 : ℂ)) U y
        = iteratedFDeriv ℝ m (fun _ => (0 : ℂ)) y :=
      (iteratedFDerivWithin_of_isOpen (s := U) m hUopen) hy
    rw [← hB, hA, hC, iteratedFDeriv_fun_zero]
    rfl
  have hcont : Continuous (iteratedFDeriv ℝ m χ) :=
    hχ.continuous_iteratedFDeriv (m := m) (by exact_mod_cast hm)
  have hzcl : z ∈ closure U := by
    rw [hU, closure_openExterior hρ]
    exact hz
  exact Set.EqOn.closure hvan hcont continuous_const hzcl

/-- If `L` bounds every iterated derivative of `χ` up to order `k + 1`, then `D^i χ` is
`L`-Lipschitz for `i ≤ k`. -/
lemma norm_iteratedFDeriv_sub_le {k : ℕ} {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (k + 1) χ)
    {L : ℝ} (hL : ∀ i, i ≤ k + 1 → ∀ z, ‖iteratedFDeriv ℝ i χ z‖ ≤ L)
    {i : ℕ} (hi : i ≤ k) (x y : Fin n → ℂ) :
    ‖iteratedFDeriv ℝ i χ x - iteratedFDeriv ℝ i χ y‖ ≤ L * ‖x - y‖ := by
  have hdiff : ∀ z, DifferentiableAt ℝ (fun w => iteratedFDeriv ℝ i χ w) z := fun z =>
    ((hχ.ftaylorSeries).fderiv i (by exact_mod_cast (Nat.lt_succ_of_le hi)) z).differentiableAt
  have hbd : ∀ z, ‖fderiv ℝ (fun w => iteratedFDeriv ℝ i χ w) z‖ ≤ L := fun z => by
    rw [norm_fderiv_iteratedFDeriv]
    exact hL (i + 1) (by omega) z
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun w => iteratedFDeriv ℝ i χ w)
    (C := L) (s := Set.univ) (fun z _ => hdiff z) (fun z _ => hbd z) convex_univ
    (Set.mem_univ x) (Set.mem_univ y)
  simpa only [norm_sub_rev] using h

/-- First-order decay of the derivatives of `χ` at the closed exterior. -/
lemma norm_iteratedFDeriv_le_dist {k : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (k + 1) χ)
    (hχ0 : ∀ z : Fin n → ℂ, (∃ j, ρ j ≤ ‖z j‖) → χ z = 0)
    {L : ℝ} (hL : ∀ i, i ≤ k + 1 → ∀ z, ‖iteratedFDeriv ℝ i χ z‖ ≤ L)
    {i : ℕ} (hi : i ≤ k) (x : Fin n → ℂ) {y : Fin n → ℂ} (hy : ∃ j, ρ j ≤ ‖y j‖) :
    ‖iteratedFDeriv ℝ i χ x‖ ≤ L * ‖x - y‖ := by
  have h1 := norm_iteratedFDeriv_sub_le hχ hL hi x y
  rw [iteratedFDeriv_eq_zero_of_notMem_polydisc hρ hχ hχ0 (by omega) hy, sub_zero] at h1
  exact h1

/-- Second-order flatness of `χ` at the closed exterior: for `i + 1 ≤ k` the `i`-th derivative at
an arbitrary point `x` is bounded by `L ‖x - y‖ ^ 2`, `y` being any point of the exterior. -/
lemma norm_iteratedFDeriv_le_sq {k : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (k + 1) χ)
    (hχ0 : ∀ z : Fin n → ℂ, (∃ j, ρ j ≤ ‖z j‖) → χ z = 0)
    {L : ℝ} (hL : ∀ i, i ≤ k + 1 → ∀ z, ‖iteratedFDeriv ℝ i χ z‖ ≤ L)
    {i : ℕ} (hi : i + 1 ≤ k) (x : Fin n → ℂ) {y : Fin n → ℂ} (hy : ∃ j, ρ j ≤ ‖y j‖) :
    ‖iteratedFDeriv ℝ i χ x‖ ≤ L * ‖x - y‖ ^ 2 := by
  have hLnn : 0 ≤ L := le_trans (norm_nonneg _) (hL 0 (by omega) 0)
  have hik : i < k + 1 := by omega
  have hik1 : i + 1 ≤ k + 1 := by omega
  have hflat_i : iteratedFDeriv ℝ i χ y = 0 :=
    iteratedFDeriv_eq_zero_of_notMem_polydisc hρ hχ hχ0 (by omega) hy
  have hflat_i1 : iteratedFDeriv ℝ (i + 1) χ y = 0 :=
    iteratedFDeriv_eq_zero_of_notMem_polydisc hρ hχ hχ0 hik1 hy
  -- the auxiliary function, whose derivative is the `(i+1)`-st derivative minus its value at `y`
  set g : (Fin n → ℂ) → ContinuousMultilinearMap ℝ (fun _ : Fin i => (Fin n → ℂ)) ℂ :=
    fun w => iteratedFDeriv ℝ i χ w - (iteratedFDeriv ℝ (i + 1) χ y).curryLeft (w - y) with hg
  have hgy : g y = 0 := by
    rw [hg]
    simp only [sub_self, map_zero, hflat_i]
  have hhas : ∀ w, HasFDerivAt g
      ((iteratedFDeriv ℝ (i + 1) χ w).curryLeft - (iteratedFDeriv ℝ (i + 1) χ y).curryLeft) w := by
    intro w
    have h1 : HasFDerivAt (fun w : Fin n → ℂ => iteratedFDeriv ℝ i χ w)
        (iteratedFDeriv ℝ (i + 1) χ w).curryLeft w :=
      (hχ.ftaylorSeries).fderiv i (by exact_mod_cast hik) w
    have h2 : HasFDerivAt
        (fun w : Fin n → ℂ => (iteratedFDeriv ℝ (i + 1) χ y).curryLeft (w - y))
        (iteratedFDeriv ℝ (i + 1) χ y).curryLeft w :=
      (ContinuousLinearMap.hasFDerivAt _).comp w ((hasFDerivAt_id w).sub_const y)
    rw [hg]
    exact h1.sub h2
  have hbound : ∀ w ∈ segment ℝ y x,
      ‖fderiv ℝ g w‖ ≤ L * ‖x - y‖ := by
    intro w hw
    rw [(hhas w).fderiv, norm_curryLeft_sub]
    calc ‖iteratedFDeriv ℝ (i + 1) χ w - iteratedFDeriv ℝ (i + 1) χ y‖
        ≤ L * ‖w - y‖ := norm_iteratedFDeriv_sub_le hχ hL (by omega) w y
      _ ≤ L * ‖x - y‖ :=
          mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hw) hLnn
  have hmv : ‖g x - g y‖ ≤ (L * ‖x - y‖) * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (f := g) (C := L * ‖x - y‖)
      (s := segment ℝ y x) (fun w _ => (hhas w).differentiableAt)
      (fun w hw => hbound w hw) (convex_segment y x)
      (left_mem_segment ℝ y x) (right_mem_segment ℝ y x)
  rw [hgy, sub_zero] at hmv
  have hzero : (iteratedFDeriv ℝ (i + 1) χ y).curryLeft = 0 := by
    rw [hflat_i1]
    ext v m
    simp [ContinuousMultilinearMap.curryLeft_apply]
  have hgx : ‖g x‖ = ‖iteratedFDeriv ℝ i χ x‖ := by
    rw [hg]
    simp [hzero, sub_zero]
  rw [← hgx]
  calc ‖g x‖ ≤ (L * ‖x - y‖) * ‖x - y‖ := hmv
    _ = L * ‖x - y‖ ^ 2 := by ring

/-- Packaging of the facts about `χ` needed below: for a compactly supported `C^{k+1}` function
vanishing on the closed exterior of the polydisc there is `L > 0` bounding all its derivatives up
to order `k + 1`, and the derivatives are flat of first and second order at the exterior. -/
theorem bumpFlat_facts {k : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (k + 1) χ) (hχs : HasCompactSupport χ)
    (hχ0 : ∀ z : Fin n → ℂ, (∃ j, ρ j ≤ ‖z j‖) → χ z = 0) :
    ∃ L : ℝ, 0 < L ∧
      (∀ i, i ≤ k + 1 → ∀ z, ‖iteratedFDeriv ℝ i χ z‖ ≤ L) ∧
      (∀ i ≤ k + 1, ∀ z, (∃ j, ρ j ≤ ‖z j‖) → iteratedFDeriv ℝ i χ z = 0) ∧
      (∀ i ≤ k, ∀ x y, (∃ j, ρ j ≤ ‖y j‖) →
        ‖iteratedFDeriv ℝ i χ x - iteratedFDeriv ℝ i χ y‖ ≤ L * ‖x - y‖) ∧
      (∀ i, i + 1 ≤ k → ∀ x y, (∃ j, ρ j ≤ ‖y j‖) →
        ‖iteratedFDeriv ℝ i χ x‖ ≤ L * ‖x - y‖ ^ 2) := by
  have hbdd : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ (i ≤ k + 1 → ∀ z,
      ‖iteratedFDeriv ℝ i χ z‖ ≤ B) := by
    intro i
    by_cases hi : i ≤ k + 1
    · have hcont : Continuous (iteratedFDeriv ℝ i χ) :=
        hχ.continuous_iteratedFDeriv (m := i) (by exact_mod_cast hi)
      obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support (hχs.iteratedFDeriv i)
      exact ⟨B, le_trans (norm_nonneg _) (hB 0), fun _ => hB⟩
    · exact ⟨0, le_rfl, fun h => absurd h hi⟩
  let B : ℕ → ℝ := fun i => Classical.choose (hbdd i)
  have hB0 : ∀ i, 0 ≤ B i := fun i => (Classical.choose_spec (hbdd i)).1
  have hBle : ∀ i, i ≤ k + 1 → ∀ z, ‖iteratedFDeriv ℝ i χ z‖ ≤ B i := fun i hi =>
    (Classical.choose_spec (hbdd i)).2 hi
  set L : ℝ := 1 + ∑ i ∈ Finset.range (k + 2), B i with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (k + 2), B i := Finset.sum_nonneg (fun i _ => hB0 i)
    linarith
  have hLbound : ∀ i, i ≤ k + 1 → ∀ z, ‖iteratedFDeriv ℝ i χ z‖ ≤ L := by
    intro i hi z
    have hi' : i ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
    calc ‖iteratedFDeriv ℝ i χ z‖ ≤ B i := hBle i hi z
      _ ≤ ∑ j ∈ Finset.range (k + 2), B j :=
          Finset.single_le_sum (fun j _ => hB0 j) hi'
      _ ≤ L := by rw [hLdef]; linarith
  exact ⟨L, hLpos, hLbound,
    (fun i hi z hz => iteratedFDeriv_eq_zero_of_notMem_polydisc hρ hχ hχ0 hi hz),
    (fun i hi x y hy => norm_iteratedFDeriv_sub_le hχ hLbound hi x y),
    (fun i hi x y hy => norm_iteratedFDeriv_le_sq hρ hχ hχ0 hLbound hi x hy)⟩

end Work.NN.Core.TelTwoDF
