import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.contraction_rate_uminus
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.mem_uminus_of_entry_form
import Submission.Work.EKLC6Core.ae_ball_in_atom
import Submission.Work.EKLC6Core.atom_generateFrom_range_eq
import Submission.Work.EKLC6Core.atom_iSup_comap_iterate_eq
import Submission.Work.EKLC6Core.neverReturnSet_null
import Submission.Work.EKLC6Core.towerDefs
import Submission.Work.EKLC6Core.countableGenEntropy
import Submission.Work.EKLC6Route.dev_estimates
import Submission.Work.EKLC6Route.uminus_inv_dev_le
import Submission.Work.EKLC6Route.dev_conj_aDiag_pow_le

/-!
# `Work.EKLC6Route.uball_smul_mem_atom`

The lower bound / openness half of Pisa 7.54 (C6GEOM_ROUTE_LEAD §2.7, L5):

Let `w` be a window (`Chart` + sub-windows `C j`) for the flow `Tm t = aDiag t ·` on `X₃`, and
let `y` be *deep* in the chart: there is `δ' > 0` with

`dU (Tm t)^[n] y ≥ δ' e^{-(λ/2) n}`   for all `n`,   `λ = lamExp t`.

Then the whole `Uminus t`-ball of radius `δ'/8` around `y` lies in the atom of `y` for the past
σ-algebra `A = pastSigSet t w.S` of the coding partition of the window.

Equivalently: the piece-labelled itinerary of the orbit of `y` is not changed by left
multiplication by any `v ∈ Uminus t` with `dev v < δ'/8`.
-/

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory Filter Topology
open scoped ENNReal
open Classical

namespace Work.EKLC6Route

open Work.EKLContract
open Work.EKLC6Core
open Work.EKLComp

variable {μ : MeasureTheory.Measure X3} {t : Fin 3 → ℝ}

/-! ## Elementary consequences of the `dev`-estimates

The three delegated lemmas `Work.EKLC6Route.dev_estimates`, `...uminus_inv_dev_le` and
`...dev_conj_aDiag_pow_le` live in their own modules and are imported above. -/

lemma dev_nonneg (g : SL3) : 0 ≤ dev g := le_trans (abs_nonneg _) (abs_dev_entry g 0 0)

lemma dev_lt_of_mem_V {g : SL3} {s : ℝ} (hg : g ∈ V s) : dev g < s :=
  (mem_V_iff_dev_lt g s).mp hg

/-! ## The contraction rate `lamExp` -/

/-- The contraction rate of the diagonal flow is positive. -/
lemma lamExp_pos (t : Fin 3 → ℝ) : 0 < lamExp t := by
  rw [lamExp]
  rw [Finset.lt_inf'_iff]
  rintro ⟨i, j⟩ -
  by_cases h : t i < t j
  · simp only [h, if_true]; linarith
  · simp only [h, if_false]; norm_num

lemma lamExp_nonneg (t : Fin 3 → ℝ) : 0 ≤ lamExp t := (lamExp_pos t).le

/-- `lamExp t` is at most every contracted gap `t j - t i`. -/
lemma lamExp_le_sub (t : Fin 3 → ℝ) {i j : Fin 3} (h : t i < t j) :
    lamExp t ≤ t j - t i := by
  have key : lamExp t ≤
      (fun p : Fin 3 × Fin 3 => if t p.1 < t p.2 then t p.2 - t p.1 else 1) (i, j) := by
    rw [lamExp]
    exact Finset.inf'_le _ (Finset.mem_univ _)
  simpa [h] using key

/-! ## The chart of a window -/

lemma Uball_mono {U : Subgroup SL3} {s s' : ℝ} (h : s ≤ s') : Uball U s ⊆ Uball U s' :=
  fun g hg => ⟨hg.1, fun i j => lt_of_lt_of_le (hg.2 i j) h⟩

/-- The window `W` sits inside the extended chart used to define `dU`. -/
lemma W_subset_E2 (w : Window μ t) :
    w.W ⊆ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ := by
  intro z hz
  simp only [Window.W, chartSet, Set.mem_ofPred_eq] at hz ⊢
  exact ⟨Uball_mono (by linarith [w.hr]) hz.1, ⟨hz.2.1.1, V_mono (by linarith [w.hρ]) hz.2.1.2⟩,
    hz.2.2⟩

lemma dU_of_mem (w : Window μ t) {z : X3}
    (hz : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ) :
    w.dU z = |dev (w.uc z) - w.r| := by
  rw [Window.dU, if_pos hz]

lemma dU_of_not_mem (w : Window μ t) {z : X3}
    (hz : z ∉ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ) : w.dU z = w.r := by
  rw [Window.dU, if_neg hz]

lemma dU_nonneg (w : Window μ t) (z : X3) : 0 ≤ w.dU z := by
  by_cases hz : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ
  · rw [dU_of_mem w hz]; exact abs_nonneg _
  · rw [dU_of_not_mem w hz]; exact w.hr.le

lemma dev_uc_lt_two_r (w : Window μ t) {z : X3}
    (hz : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ) : dev (w.uc z) < 2 * w.r := by
  simp only [chartSet, Set.mem_ofPred_eq] at hz
  exact dev_lt_of_mem_V hz.1.2

lemma dev_uc_lt_r_of_mem_W (w : Window μ t) {z : X3} (hz : z ∈ w.W) : dev (w.uc z) < w.r := by
  simp only [Window.W, chartSet, Set.mem_ofPred_eq] at hz
  exact dev_lt_of_mem_V hz.1.2

lemma dU_le_r (w : Window μ t) (z : X3) : w.dU z ≤ w.r := by
  by_cases hz : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ
  · rw [dU_of_mem w hz, abs_le]
    have h1 : dev (w.uc z) < 2 * w.r := dev_uc_lt_two_r w hz
    have h2 : 0 ≤ dev (w.uc z) := dev_nonneg _
    constructor <;> linarith
  · rw [dU_of_not_mem w hz]

lemma dev_uc_ge_r_of_mem_E2_of_not_mem_W (w : Window μ t) {z : X3}
    (hz : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ) (hzW : z ∉ w.W) :
    w.r ≤ dev (w.uc z) := by
  by_contra hcon
  push Not at hcon
  refine hzW ?_
  simp only [Window.W, chartSet, Set.mem_ofPred_eq] at hz ⊢
  refine ⟨⟨hz.1.1, fun i j => lt_of_le_of_lt (abs_dev_entry _ i j) hcon⟩, hz.2.1, hz.2.2⟩

lemma dU_eq_of_mem_W (w : Window μ t) {z : X3} (hz : z ∈ w.W) :
    w.dU z = w.r - dev (w.uc z) := by
  have hzE : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ := W_subset_E2 w hz
  have hlt : dev (w.uc z) < w.r := by
    simp only [Window.W, chartSet, Set.mem_ofPred_eq] at hz
    exact dev_lt_of_mem_V hz.1.2
  rw [dU_of_mem w hzE, abs_of_neg (by linarith)]
  ring

lemma dU_eq_of_mem_E2_of_ge (w : Window μ t) {z : X3}
    (hz : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ) (h : w.r ≤ dev (w.uc z)) :
    w.dU z = dev (w.uc z) - w.r := by
  rw [dU_of_mem w hz, abs_of_nonneg (by linarith)]

/-! ## Membership in the pieces -/

lemma mem_W_iff (w : Window μ t) (x : X3) :
    x ∈ w.W ↔ w.uc x ∈ Uball (Uminus t) w.r ∧ w.θ x ∈ VtSet t ∩ V w.ρ ∧
      (w.uc x * w.θ x) • w.z0 = x := Iff.rfl

lemma mem_E2_iff (w : Window μ t) (x : X3) :
    x ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ ↔
      w.uc x ∈ Uball (Uminus t) (2 * w.r) ∧ w.θ x ∈ VtSet t ∩ V w.ρ ∧
        (w.uc x * w.θ x) • w.z0 = x := Iff.rfl

lemma mem_N0_iff (w : Window μ t) (x : X3) :
    x ∈ w.N0 ↔ x ∈ neverReturnSet t w.W ∨ w.dU x = 0 := Iff.rfl

lemma mem_Jset_none_iff (w : Window μ t) {x : X3} :
    x ∈ w.Jset none ↔ x ∈ w.W ∧ ∀ j : ℕ, w.θ x ∈ w.C j := by
  simp only [Window.Jset, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter]

lemma mem_Jset_some_iff (w : Window μ t) {x : X3} {j : ℕ} :
    x ∈ w.Jset (some j) ↔ x ∈ w.W ∧ w.θ x ∈ w.C j ∧ w.θ x ∉ w.C (j + 1) := by
  simp only [Window.Jset, Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff]

lemma mem_D_iff (w : Window μ t) {x : X3} {i : ℕ} {J : Option ℕ} {c : Fin 3 → Fin 3 → ℤ} :
    x ∈ w.D i J c ↔ i ≠ 0 ∧ x ∈ firstReturnSet t w.W i ∧ x ∈ w.Jset J ∧
      gridIdx w.ρ (gridLev t i) (w.θ x) = c ∧ x ∉ w.N0 := by
  rw [Window.D]
  split_ifs with h
  · simp [h]
  · rw [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨h, h1, h2, h3, h4⟩
    · rintro ⟨-, h1, h2, h3, h4⟩
      exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

lemma mem_firstReturnSet_iff {Ω : Set X3} {x : X3} {i : ℕ} :
    x ∈ firstReturnSet t Ω i ↔
      x ∈ Ω ∧ ((fun y : X3 => aDiag t • y)^[i]) x ∈ Ω ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ i - 1 → ((fun y : X3 => aDiag t • y)^[j]) x ∉ Ω := by
  rw [firstReturnSet]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_iInter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun j hj1 hji => h3 j ⟨hj1, hji⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun j hj => h3 j hj.1 hj.2⟩

lemma mem_neverReturnSet_iff {Ω : Set X3} {x : X3} :
    x ∈ neverReturnSet t Ω ↔
      x ∈ Ω ∧ ∀ j : ℕ, 1 ≤ j → ((fun y : X3 => aDiag t • y)^[j]) x ∉ Ω := by
  rw [neverReturnSet]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_iInter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => h2 j hj⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => h2 j hj⟩

/-! ## The contraction on `Uminus t` -/

/-- `Uminus t` is normalised by every power of the diagonal flow. -/
lemma conj_pow_mem_uminus {t : Fin 3 → ℝ} {u : SL3} (hu : u ∈ Uminus t) (n : ℕ) :
    aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ Uminus t := by
  obtain ⟨hdiag, hzero⟩ := uminus_entry_facts t hu
  refine mem_uminus_of_entry_form (t := t) ?_ ?_
  · intro i
    rw [boxi_conj_pow_apply, hdiag i, sub_self, mul_zero, Real.exp_zero, mul_one]
  · intro i j hij hle
    rw [boxi_conj_pow_apply, hzero i j hij hle, mul_zero]
/-! ## The one-step tracking lemma -/

/-- **One step of the tracking argument.**  If `v ∈ Uminus t` is small in the sense that
`dev v ≤ η`, `dev v⁻¹ ≤ η'` with `(1 + 3 r) η < dU z` and `(1 + 3 r) η' < dU z`, then `v` moves no
piece boundary at `z`: `v • z ∈ W ↔ z ∈ W`, the `θ`-coordinate (hence the return time, the depth
label and the grid cell) is unchanged, and `dU` stays positive. -/
lemma step_pair (w : Window μ t) {v : SL3} (hv : v ∈ Uminus t) {z : X3} {η η' : ℝ}
    (hη : dev v ≤ η) (hη' : dev v⁻¹ ≤ η')
    (h1 : (1 + 3 * w.r) * η < w.dU z) (h2 : (1 + 3 * w.r) * η' < w.dU z) :
    (z ∈ w.W ↔ v • z ∈ w.W) ∧ (z ∈ w.W → w.θ (v • z) = w.θ z) ∧ 0 < w.dU (v • z) := by
  have hη0 : 0 ≤ η := le_trans (dev_nonneg v) hη
  have hη'0 : 0 ≤ η' := le_trans (dev_nonneg v⁻¹) hη'
  have hdUle : w.dU z ≤ w.r := dU_le_r w z
  have h1' : η * (1 + 3 * w.r) < w.dU z := by linarith [h1]
  have h2' : η' * (1 + 3 * w.r) < w.dU z := by linarith [h2]
  -- a uniform bound on the pull-back displacement
  have hbnd : ∀ y : SL3, dev y ≤ w.r → dev (v⁻¹ * y) ≤ w.r + η' * (1 + 3 * w.r) := by
    intro y hy
    have hmul := mul_le_mul hη' hy (dev_nonneg y) hη'0
    calc dev (v⁻¹ * y) ≤ dev v⁻¹ + dev y + 3 * dev v⁻¹ * dev y := dev_mul_le _ _
      _ ≤ η' + w.r + 3 * (η' * w.r) := by linarith
      _ = w.r + η' * (1 + 3 * w.r) := by ring
  have hbnd_lt : ∀ y : SL3, dev y ≤ w.r → dev (v⁻¹ * y) < 2 * w.r := by
    intro y hy
    linarith [hbnd y hy, h2', hdUle]
  -- pull-back of the coordinates
  have hpull : ∀ {x : X3}, v • x ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ →
      dev (w.uc (v • x)) ≤ w.r →
      x ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ ∧ w.uc x = v⁻¹ * w.uc (v • x) ∧
        w.θ x = w.θ (v • x) := by
    intro x hxE hdx
    obtain ⟨hx1, hx2, hx3⟩ := (mem_E2_iff w (v • x)).mp hxE
    have hlt : dev (v⁻¹ * w.uc (v • x)) < 2 * w.r := hbnd_lt _ hdx
    have hmem : v⁻¹ * w.uc (v • x) ∈ Uball (Uminus t) (2 * w.r) :=
      ⟨mul_mem (inv_mem hv) hx1.1, fun i j => lt_of_le_of_lt (abs_dev_entry _ i j) hlt⟩
    have hmemV : w.θ (v • x) ∈ VtSet t ∩ V (2 * w.ρ) :=
      ⟨hx2.1, V_mono (by linarith [w.hρ]) hx2.2⟩
    obtain ⟨hc1, hc2⟩ := w.coord (v⁻¹ * w.uc (v • x)) hmem (w.θ (v • x)) hmemV
    have hpt : ((v⁻¹ * w.uc (v • x)) * w.θ (v • x)) • w.z0 = x := by
      have hB : ((v⁻¹ * w.uc (v • x)) * w.θ (v • x)) • w.z0
          = v⁻¹ • ((w.uc (v • x) * w.θ (v • x)) • w.z0) := by simp only [mul_smul]
      rw [hB, hx3, inv_smul_smul]
    have hucx : w.uc x = v⁻¹ * w.uc (v • x) := by
      have h2 : w.uc x = w.uc (((v⁻¹ * w.uc (v • x)) * w.θ (v • x)) • w.z0) := by rw [hpt]
      rw [h2, hc1]
    have hθx : w.θ x = w.θ (v • x) := by
      have h2 : w.θ x = w.θ (((v⁻¹ * w.uc (v • x)) * w.θ (v • x)) • w.z0) := by rw [hpt]
      rw [h2, hc2]
    have hpt2 : (w.uc x * w.θ x) • w.z0 = x := by rw [hucx, hθx, hpt]
    refine ⟨?_, hucx, hθx⟩
    rw [mem_E2_iff]
    refine ⟨?_, ?_, hpt2⟩
    · rw [hucx]
      exact ⟨mul_mem (inv_mem hv) hx1.1, fun i j => lt_of_le_of_lt (abs_dev_entry _ i j) hlt⟩
    · rw [hθx]
      exact ⟨hx2.1, V_mono (by linarith [w.hρ]) hx2.2⟩
  -- the forward direction: a point of `w.W` stays in `w.W`
  have hsmall : z ∈ w.W → dev (v * w.uc z) < w.r := by
    intro hz
    obtain ⟨hz1, hz2, hz3⟩ := (mem_W_iff w z).mp hz
    have hdz : dev (w.uc z) < w.r := dev_lt_of_mem_V hz1.2
    have hdU : w.dU z = w.r - dev (w.uc z) := dU_eq_of_mem_W w hz
    have hkey : η * (1 + 3 * dev (w.uc z)) < w.dU z := by
      calc η * (1 + 3 * dev (w.uc z)) ≤ η * (1 + 3 * w.r) :=
            mul_le_mul_of_nonneg_left (by linarith) hη0
        _ < w.dU z := h1'
    calc dev (v * w.uc z) ≤ dev v + dev (w.uc z) + 3 * dev v * dev (w.uc z) := dev_mul_le _ _
      _ ≤ η + dev (w.uc z) + 3 * (η * dev (w.uc z)) := by
            have hm := mul_le_mul_of_nonneg_right hη (dev_nonneg (w.uc z))
            linarith
      _ = dev (w.uc z) + η * (1 + 3 * dev (w.uc z)) := by ring
      _ < dev (w.uc z) + w.dU z := by linarith
      _ = w.r := by linarith
  have hcoordW : z ∈ w.W → w.uc (v • z) = v * w.uc z ∧ w.θ (v • z) = w.θ z ∧
      ((v * w.uc z) * w.θ z) • w.z0 = v • z := by
    intro hz
    obtain ⟨hz1, hz2, hz3⟩ := (mem_W_iff w z).mp hz
    have hsm := hsmall hz
    have hmem : v * w.uc z ∈ Uball (Uminus t) (2 * w.r) :=
      ⟨mul_mem hv hz1.1, fun i j => lt_of_le_of_lt (abs_dev_entry _ i j) (by linarith [hsm, w.hr])⟩
    have hmemV : w.θ z ∈ VtSet t ∩ V (2 * w.ρ) := ⟨hz2.1, V_mono (by linarith [w.hρ]) hz2.2⟩
    obtain ⟨hc1, hc2⟩ := w.coord (v * w.uc z) hmem (w.θ z) hmemV
    have hpt : ((v * w.uc z) * w.θ z) • w.z0 = v • z := by
      have hB : ((v * w.uc z) * w.θ z) • w.z0 = v • ((w.uc z * w.θ z) • w.z0) := by
        simp only [mul_smul]
      rw [hB, hz3]
    have huc : w.uc (v • z) = v * w.uc z := by
      have h2 : w.uc (v • z) = w.uc (((v * w.uc z) * w.θ z) • w.z0) := by rw [hpt]
      rw [h2, hc1]
    have hθ : w.θ (v • z) = w.θ z := by
      have h2 : w.θ (v • z) = w.θ (((v * w.uc z) * w.θ z) • w.z0) := by rw [hpt]
      rw [h2, hc2]
    exact ⟨huc, hθ, hpt⟩
  have hWW : z ∈ w.W → v • z ∈ w.W := by
    intro hz
    obtain ⟨hz1, hz2, hz3⟩ := (mem_W_iff w z).mp hz
    obtain ⟨huc, hθ, hpt⟩ := hcoordW hz
    rw [mem_W_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [huc]
      exact ⟨mul_mem hv hz1.1, fun i j =>
        lt_of_le_of_lt (abs_dev_entry _ i j) (by linarith [hsmall hz, w.hr])⟩
    · rw [hθ]; exact hz2
    · rw [huc, hθ]; exact hpt
  have hback : z ∉ w.W → v • z ∉ w.W := by
    intro hzW hvw
    have hvwE : v • z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ := W_subset_E2 w hvw
    have hdx : dev (w.uc (v • z)) ≤ w.r := le_of_lt (dev_uc_lt_r_of_mem_W w hvw)
    have hzE : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ := (hpull hvwE hdx).1
    have hge : w.r ≤ dev (w.uc z) := dev_uc_ge_r_of_mem_E2_of_not_mem_W w hzE hzW
    have hdU : w.dU z = dev (w.uc z) - w.r := dU_eq_of_mem_E2_of_ge w hzE hge
    have hb : dev (v⁻¹ * w.uc (v • z)) ≤ w.r + η' * (1 + 3 * w.r) := hbnd _ hdx
    have hb' : dev (w.uc z) ≤ w.r + η' * (1 + 3 * w.r) := by
      rw [(hpull hvwE hdx).2.1]; exact hb
    linarith
  have hposW : z ∈ w.W → 0 < w.dU (v • z) := by
    intro hz
    obtain ⟨huc, hθ, hpt⟩ := hcoordW hz
    rw [dU_eq_of_mem_W w (hWW hz), huc]
    linarith [hsmall hz]
  have hpos_notW : z ∉ w.W → 0 < w.dU (v • z) := by
    intro hzW
    by_cases hzE : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ
    · have hge : w.r ≤ dev (w.uc z) := dev_uc_ge_r_of_mem_E2_of_not_mem_W w hzE hzW
      have hdU : w.dU z = dev (w.uc z) - w.r := dU_eq_of_mem_E2_of_ge w hzE hge
      by_contra hcon
      push Not at hcon
      have h0 : w.dU (v • z) = 0 := le_antisymm hcon (dU_nonneg w _)
      have hvzE : v • z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ := by
        by_contra h
        rw [dU_of_not_mem w h] at h0
        exact w.hr.ne' h0
      have hdx : dev (w.uc (v • z)) ≤ w.r := by
        have h := dU_of_mem w hvzE
        rw [h0] at h
        have h' := abs_eq_zero.mp h.symm
        linarith
      have hb := hbnd (w.uc (v • z)) hdx
      have hb' : dev (w.uc z) ≤ w.r + η' * (1 + 3 * w.r) := by
        rw [(hpull hvzE hdx).2.1]; exact hb
      linarith
    · by_contra hcon
      push Not at hcon
      have h0 : w.dU (v • z) = 0 := le_antisymm hcon (dU_nonneg w _)
      have hvzE : v • z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ := by
        by_contra h
        rw [dU_of_not_mem w h] at h0
        exact w.hr.ne' h0
      have hdx : dev (w.uc (v • z)) ≤ w.r := by
        have h := dU_of_mem w hvzE
        rw [h0] at h
        have h' := abs_eq_zero.mp h.symm
        linarith
      exact hzE (hpull hvzE hdx).1
  refine ⟨⟨fun hz => hWW hz, fun hvw => ?_⟩, fun hz => (hcoordW hz).2.1, ?_⟩
  · by_contra hzW
    exact hback hzW hvw
  · by_cases hz : z ∈ w.W
    · exact hposW hz
    · exact hpos_notW hz

/-! ## The main theorem -/

theorem uball_smul_mem_atom {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Work.EKLC6Route.Window μ t)
    {y : Work.EKLContract.X3} {δ' : ℝ} (hδ' : 0 < δ')
    (hmar : ∀ n : ℕ, δ' * Real.exp (-(Work.EKLC6Route.lamExp t / 2) * n) ≤
      w.dU ((Work.EKLC6Route.Tm t)^[n] y)) :
    ∀ v ∈ Work.EKLComp.Uball (Work.EKLC6Core.Uminus t) (δ' / 8),
      v • y ∈ Work.EKLContract.atom w.A y := by
  intro v hv
  obtain ⟨hvU, hvV⟩ := hv
  -- the deviations of `v` and of `v⁻¹`
  have hdev : dev v < δ' / 8 := dev_lt_of_mem_V hvV
  have hδr : δ' ≤ w.r := by
    have h0 := hmar 0
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] at h0
    exact le_trans h0 (dU_le_r w y)
  have hδ'1 : δ' ≤ 1 := by
    have h1 : 4000 * w.r ≤ w.δ := w.hrδ
    have h2 : w.δ ≤ 1 / 100 := w.hδ1
    linarith
  have hinv : dev v⁻¹ ≤ δ' / 4 := by
    have h := uminus_inv_dev_le hvU
    have hnn : 0 ≤ dev v := dev_nonneg v
    have hsq : dev v * dev v ≤ (δ' / 8) * (δ' / 8) := mul_self_le_mul_self hnn hdev.le
    nlinarith [h, hdev, hnn, hsq, hδ']
  have hsmallr : (1 + 3 * w.r) ≤ 2 := by
    have h1 : 4000 * w.r ≤ w.δ := w.hrδ
    have h2 : w.δ ≤ 1 / 100 := w.hδ1
    linarith
  -- the contraction at every time
  have hconjinv (n : ℕ) :
      (aDiag t ^ n * v * (aDiag t ^ n)⁻¹)⁻¹ = aDiag t ^ n * v⁻¹ * (aDiag t ^ n)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
  have hdevn (n : ℕ) : dev (aDiag t ^ n * v * (aDiag t ^ n)⁻¹) ≤
      Real.exp (-(lamExp t * (n : ℝ))) * (δ' / 8) :=
    le_trans (dev_conj_aDiag_pow_le hvU n)
      (mul_le_mul_of_nonneg_left hdev.le (Real.exp_pos _).le)
  have hdevnin (n : ℕ) : dev ((aDiag t ^ n * v * (aDiag t ^ n)⁻¹)⁻¹) ≤
      Real.exp (-(lamExp t * (n : ℝ))) * (δ' / 4) := by
    rw [hconjinv n]
    exact le_trans (dev_conj_aDiag_pow_le (inv_mem hvU) n)
      (mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le)
  have hexp_le (n : ℕ) :
      Real.exp (-(lamExp t * (n : ℝ))) ≤ Real.exp (-(lamExp t / 2) * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h1 : 0 ≤ lamExp t := lamExp_nonneg t
    have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hdUy (n : ℕ) : 0 < w.dU ((Tm t)^[n] y) := by
    have h := hmar n
    have hpos : 0 < δ' * Real.exp (-(lamExp t / 2) * (n : ℝ)) := by positivity
    linarith
  -- the two margin conditions of the step lemma
  have hcond (n : ℕ) :
      (1 + 3 * w.r) * dev (aDiag t ^ n * v * (aDiag t ^ n)⁻¹) < w.dU ((Tm t)^[n] y) ∧
      (1 + 3 * w.r) * dev ((aDiag t ^ n * v * (aDiag t ^ n)⁻¹)⁻¹) < w.dU ((Tm t)^[n] y) := by
    have hexppos : 0 < Real.exp (-(lamExp t / 2) * (n : ℝ)) := Real.exp_pos _
    constructor
    · have h2 : 2 * dev (aDiag t ^ n * v * (aDiag t ^ n)⁻¹) <
          δ' * Real.exp (-(lamExp t / 2) * (n : ℝ)) := by
        calc 2 * dev (aDiag t ^ n * v * (aDiag t ^ n)⁻¹)
            ≤ 2 * (Real.exp (-(lamExp t * (n : ℝ))) * (δ' / 8)) :=
              mul_le_mul_of_nonneg_left (hdevn n) (by norm_num)
          _ = (δ' / 4) * Real.exp (-(lamExp t * (n : ℝ))) := by ring
          _ ≤ (δ' / 4) * Real.exp (-(lamExp t / 2) * (n : ℝ)) :=
              mul_le_mul_of_nonneg_left (hexp_le n) (by linarith)
          _ < δ' * Real.exp (-(lamExp t / 2) * (n : ℝ)) := by nlinarith [hexppos, hδ']
      calc (1 + 3 * w.r) * dev (aDiag t ^ n * v * (aDiag t ^ n)⁻¹)
          ≤ 2 * dev (aDiag t ^ n * v * (aDiag t ^ n)⁻¹) :=
            mul_le_mul_of_nonneg_right hsmallr (dev_nonneg _)
        _ < δ' * Real.exp (-(lamExp t / 2) * (n : ℝ)) := h2
        _ ≤ w.dU ((Tm t)^[n] y) := hmar n
    · have h2 : 2 * dev ((aDiag t ^ n * v * (aDiag t ^ n)⁻¹)⁻¹) <
          δ' * Real.exp (-(lamExp t / 2) * (n : ℝ)) := by
        calc 2 * dev ((aDiag t ^ n * v * (aDiag t ^ n)⁻¹)⁻¹)
            ≤ 2 * (Real.exp (-(lamExp t * (n : ℝ))) * (δ' / 4)) :=
              mul_le_mul_of_nonneg_left (hdevnin n) (by norm_num)
          _ = (δ' / 2) * Real.exp (-(lamExp t * (n : ℝ))) := by ring
          _ ≤ (δ' / 2) * Real.exp (-(lamExp t / 2) * (n : ℝ)) :=
              mul_le_mul_of_nonneg_left (hexp_le n) (by linarith)
          _ < δ' * Real.exp (-(lamExp t / 2) * (n : ℝ)) := by nlinarith [hexppos, hδ']
      calc (1 + 3 * w.r) * dev ((aDiag t ^ n * v * (aDiag t ^ n)⁻¹)⁻¹)
          ≤ 2 * dev ((aDiag t ^ n * v * (aDiag t ^ n)⁻¹)⁻¹) :=
            mul_le_mul_of_nonneg_right hsmallr (dev_nonneg _)
        _ < δ' * Real.exp (-(lamExp t / 2) * (n : ℝ)) := h2
        _ ≤ w.dU ((Tm t)^[n] y) := hmar n
  -- the step at every time
  have horb (n : ℕ) : (Tm t)^[n] (v • y) =
      (aDiag t ^ n * v * (aDiag t ^ n)⁻¹) • ((Tm t)^[n] y) :=
    orbit_smul_eq t n v y
  have hstep (n : ℕ) : ((Tm t)^[n] (v • y) ∈ w.W ↔ (Tm t)^[n] y ∈ w.W) ∧
      ((Tm t)^[n] y ∈ w.W → w.θ ((Tm t)^[n] (v • y)) = w.θ ((Tm t)^[n] y)) ∧
      0 < w.dU ((Tm t)^[n] (v • y)) := by
    rw [horb n]
    have h := step_pair w (conj_pow_mem_uminus hvU n) (le_refl _) (le_refl _) (hcond n).1 (hcond n).2
    exact ⟨h.1.symm, h.2⟩
  have hWall (n : ℕ) : ((Tm t)^[n] (v • y) ∈ w.W) ↔ ((Tm t)^[n] y ∈ w.W) := (hstep n).1
  have hθall (n : ℕ) : ((Tm t)^[n] y ∈ w.W) →
      w.θ ((Tm t)^[n] (v • y)) = w.θ ((Tm t)^[n] y) := (hstep n).2.1
  have hposn (n : ℕ) : 0 < w.dU ((Tm t)^[n] (v • y)) := (hstep n).2.2
  have hshift : ∀ (j n : ℕ) (z : X3),
      (Tm t)^[j] ((Tm t)^[n] z) = (Tm t)^[j + n] z :=
    fun j n z => (Function.iterate_add_apply (Tm t) j n z).symm
  -- the atom of the coding σ-algebra
  have hatom : ∀ y' : X3, y' ∈ atom w.A y ↔
      ∀ n m, ((Tm t)^[n] y' ∈ w.S m) ↔ ((Tm t)^[n] y ∈ w.S m) := by
    intro y'
    rw [Window.A, pastSigSet]
    rw [atom_iSup_comap_iterate_eq (MeasurableSpace.generateFrom (Set.range w.S))
      (fun x : X3 => aDiag t • x) y]
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h n m
      have h' := h n
      rw [atom_generateFrom_range_eq w.S ((fun x : X3 => aDiag t • x)^[n] y)] at h'
      exact h' m
    · intro h n
      rw [atom_generateFrom_range_eq]
      exact fun m => h n m
  -- piece agreement
  have hpiece (n : ℕ) (p : Window.PIdx) :
      ((Tm t)^[n] (v • y) ∈ w.piece p) ↔ ((Tm t)^[n] y ∈ w.piece p) := by
    have hW := hWall n
    have hθ := hθall n
    have hNR : ((Tm t)^[n] (v • y) ∈ neverReturnSet t w.W) ↔
        ((Tm t)^[n] y ∈ neverReturnSet t w.W) := by
      rw [mem_neverReturnSet_iff, mem_neverReturnSet_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨hW.mp h1, fun j hj => ?_⟩
        have h3 := h2 j hj
        rw [hshift j n] at h3
        intro hc
        rw [hshift j n] at hc
        exact h3 ((hWall (j + n)).mpr hc)
      · rintro ⟨h1, h2⟩
        refine ⟨hW.mpr h1, fun j hj => ?_⟩
        have h3 := h2 j hj
        rw [hshift j n] at h3
        intro hc
        rw [hshift j n] at hc
        exact h3 ((hWall (j + n)).mp hc)
    have hN0 : ((Tm t)^[n] (v • y) ∈ w.N0) ↔ ((Tm t)^[n] y ∈ w.N0) := by
      rw [mem_N0_iff, mem_N0_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl (hNR.mp h)
        · exact absurd h (ne_of_gt (hposn n))
      · rintro (h | h)
        · exact Or.inl (hNR.mpr h)
        · exact absurd h (ne_of_gt (hdUy n))
    have hN0not : ((Tm t)^[n] (v • y)) ∉ w.N0 ↔ ((Tm t)^[n] y) ∉ w.N0 := not_congr hN0
    have hFR (i : ℕ) : ((Tm t)^[n] (v • y) ∈ firstReturnSet t w.W i) ↔
        ((Tm t)^[n] y ∈ firstReturnSet t w.W i) := by
      rw [mem_firstReturnSet_iff, mem_firstReturnSet_iff]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨hW.mp h1, ?_, ?_⟩
        · rw [hshift i n] at h2 ⊢
          exact (hWall (i + n)).mp h2
        · intro j hj1 hj2
          have h3j := h3 j hj1 hj2
          rw [hshift j n] at h3j
          intro hc
          rw [hshift j n] at hc
          exact h3j ((hWall (j + n)).mpr hc)
      · rintro ⟨h1, h2, h3⟩
        refine ⟨hW.mpr h1, ?_, ?_⟩
        · rw [hshift i n] at h2 ⊢
          exact (hWall (i + n)).mpr h2
        · intro j hj1 hj2
          have h3j := h3 j hj1 hj2
          rw [hshift j n] at h3j
          intro hc
          rw [hshift j n] at hc
          exact h3j ((hWall (j + n)).mp hc)
    have hJ (J : Option ℕ) : ((Tm t)^[n] (v • y) ∈ w.Jset J) ↔
        ((Tm t)^[n] y ∈ w.Jset J) := by
      by_cases hz : ((Tm t)^[n] y) ∈ w.W
      · have hθz := hθ hz
        cases J with
        | none =>
          rw [mem_Jset_none_iff, mem_Jset_none_iff]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨hW.mp h1, fun j => by simpa only [hθz] using h2 j⟩
          · rintro ⟨h1, h2⟩
            exact ⟨hW.mpr h1, fun j => by simpa only [hθz] using h2 j⟩
        | some j =>
          rw [mem_Jset_some_iff, mem_Jset_some_iff]
          constructor
          · rintro ⟨h1, h2, h3⟩
            exact ⟨hW.mp h1, by simpa only [hθz] using h2, by simpa only [hθz] using h3⟩
          · rintro ⟨h1, h2, h3⟩
            exact ⟨hW.mpr h1, by simpa only [hθz] using h2, by simpa only [hθz] using h3⟩
      · have hz' : ¬ ((Tm t)^[n] (v • y)) ∈ w.W := fun h => hz (hW.mp h)
        have hsub : ∀ {x : X3}, x ∈ w.Jset J → x ∈ w.W := by
          intro x hx
          cases J with
          | none => exact ((mem_Jset_none_iff w).mp hx).1
          | some j => exact ((mem_Jset_some_iff w).mp hx).1
        exact iff_of_false (fun h => hz' (hsub h)) (fun h => hz (hsub h))
    have hgrid (L : ℕ) (c : Fin 3 → Fin 3 → ℤ) (hz : ((Tm t)^[n] y) ∈ w.W) :
        gridIdx w.ρ L (w.θ ((Tm t)^[n] (v • y))) = c ↔
          gridIdx w.ρ L (w.θ ((Tm t)^[n] y)) = c := by
      simp only [hθ hz]
    cases p with
    | none =>
      show (((Tm t)^[n] (v • y)) ∈ (w.W ∪ w.N0)ᶜ) ↔ ((Tm t)^[n] y ∈ (w.W ∪ w.N0)ᶜ)
      rw [Set.mem_compl_iff, Set.mem_union, Set.mem_compl_iff, Set.mem_union]
      constructor
      · intro h1 h2
        rcases h2 with h | h
        · exact h1 (Or.inl (hW.mpr h))
        · exact h1 (Or.inr (hN0.mpr h))
      · intro h1 h2
        rcases h2 with h | h
        · exact h1 (Or.inl (hW.mp h))
        · exact h1 (Or.inr (hN0.mp h))
    | some J =>
      cases J with
      | none => show (((Tm t)^[n] (v • y)) ∈ w.N0) ↔ ((Tm t)^[n] y ∈ w.N0); exact hN0
      | some q =>
        obtain ⟨i, J', c⟩ := q
        show (((Tm t)^[n] (v • y)) ∈ w.D i J' c) ↔ ((Tm t)^[n] y ∈ w.D i J' c)
        by_cases hz : ((Tm t)^[n] y) ∈ w.W
        · rw [mem_D_iff, mem_D_iff]
          constructor
          · rintro ⟨hi, h1, h2, h3, h4⟩
            exact ⟨hi, (hFR i).mp h1, (hJ J').mp h2, (hgrid (gridLev t i) c hz).mp h3,
              hN0not.mp h4⟩
          · rintro ⟨hi, h1, h2, h3, h4⟩
            exact ⟨hi, (hFR i).mpr h1, (hJ J').mpr h2, (hgrid (gridLev t i) c hz).mpr h3,
              hN0not.mpr h4⟩
        · have hz' : ¬ ((Tm t)^[n] (v • y)) ∈ w.W := fun h => hz (hW.mp h)
          rw [mem_D_iff, mem_D_iff]
          refine iff_of_false ?_ ?_
          · rintro ⟨-, h1, -, -, -⟩
            exact hz' ((mem_firstReturnSet_iff.mp h1).1)
          · rintro ⟨-, h1, -, -, -⟩
            exact hz ((mem_firstReturnSet_iff.mp h1).1)
  -- conclude
  refine (hatom (v • y)).mpr ?_
  intro n m
  rw [Window.S]
  split
  · rename_i x p heq
    exact hpiece n p
  · simp

end Work.EKLC6Route
