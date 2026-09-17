import Mathlib
import Submission.Contact
import Submission.LatticeBox
import Submission.Commons.Probability.Gaussian.stdGaussian_norm_sq_tail_card

set_option synthInstance.maxHeartbeats 1000000

/-!
# The good event and the final rescaling of the exploration process

This file contains the last step of the *deterministic* bookkeeping of the exploration process of
`Submission.PLAN_V4.md` / `PLAN_V6.md`:  the process never clips and never discards a step, so it
may leave the `Λ`-free cone; the correction is paid once, at the end, by the rescaling
`A_K ↦ (1 - θ)⁻¹ A_K`.

The two ingredients are

* **freezing**: once a vector `x` is violated at some time `k₀` (i.e. `quadFormV A_{k₀} x ≤ 1`),
  then the projected increment is orthogonal to `x ⊗ x`, so `quadFormV A_k x` is *constant* for
  all `k ≥ k₀`; and
* **the increment bound**: the increment of the quadratic form at the first violation is at most
  `ε · ‖ξ‖ · ‖x‖² ≤ ε · (2d) · R² =: θ` in absolute value.

Consequently, on the event that the state stays close to `a₀·Id` and all increments are bounded
by `2d`, every nonzero lattice vector `x` with `‖x‖ ≤ R` satisfies
`quadFormV A_K x ≥ 1 - θ`, whence `(1-θ)⁻¹ A_K` is `Λ`-free.  (Vectors with `‖x‖ > R` are
automatically not violated, because the state stays close to `a₀·Id`.)
-/

namespace Submission.Rescale

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.GenProc
open Submission.OpNorm
open Submission.Contact

noncomputable section

variable {d m : ℕ}

/-! ## The projected increment is a contraction, and annihilates violated tensors -/

/-- The constraint projection is a contraction in the Frobenius (Euclidean) norm. -/
lemma norm_projL_apply_le (R : ℝ) (BoxL : Fin m → Vec d) (A w : MatV d) :
    ‖(projL R BoxL A) w‖ ≤ ‖w‖ := by
  rw [projL_apply_eq]
  exact Submodule.norm_starProjection_apply_le (K := tangentSub (violSet R BoxL A)) w

/-- The constraint projection annihilates `x ⊗ x` for every violated vector `x`. -/
lemma projL_tensorV_eq_zero (R : ℝ) (BoxL : Fin m → Vec d) (A : MatV d) {x : Vec d}
    (hx : x ∈ violSet R BoxL A) : (projL R BoxL A) (tensorV x) = 0 := by
  rw [projL_apply_eq, Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro w hw
  rw [← quadLin_eq_inner]
  exact ((mem_tangentSub (violSet R BoxL A) w).mp hw).2 x hx

/-! ## The increment of the quadratic form -/

lemma quadFormV_step (R ε : ℝ) (BoxL : Fin m → Vec d) (A ξ : MatV d) (x : Vec d) :
    quadFormV (step (projL R BoxL) ε A ξ) x
      = quadFormV A x + ε * quadFormV ((projL R BoxL A) ξ) x := by
  rw [step, quadFormV_add, quadFormV_smul]

/-- If `x` is violated at `A`, the step leaves its quadratic form unchanged. -/
lemma quadFormV_step_of_mem_violSet (R ε : ℝ) (BoxL : Fin m → Vec d) (A ξ : MatV d)
    {x : Vec d} (hx : x ∈ violSet R BoxL A) :
    quadFormV (step (projL R BoxL) ε A ξ) x = quadFormV A x := by
  rw [quadFormV_step]
  have h1 : quadFormV ((projL R BoxL A) ξ) x = 0 := by
    rw [quadFormV_eq_inner]
    rw [(good_projL R BoxL A).adj ξ (tensorV x), projL_tensorV_eq_zero R BoxL A hx,
      inner_zero_right]
  rw [h1, mul_zero, add_zero]

/-! ## Freezing -/

/-- Membership in the violated set, unfolded. -/
lemma mem_violSet_iff {R : ℝ} {BoxL : Fin m → Vec d} {A : MatV d} {x : Vec d} :
    x ∈ violSet R BoxL A ↔
      ∃ i : Fin m, ‖BoxL i‖ ≤ R ∧ quadFormV A (BoxL i) ≤ 1 ∧ BoxL i = x := by
  rw [violSet, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, hix⟩
    rw [Finset.mem_filter] at hi
    exact ⟨i, hi.2.1, hi.2.2, hix⟩
  · rintro ⟨i, h1, h2, hix⟩
    exact ⟨i, by simp [h1, h2], hix⟩

/-- **Freezing.**  A vector violated at time `k₀` keeps the same quadratic form for all later
times. -/
lemma quadFormV_frozen (R ε a₀ : ℝ) (K : ℕ) (BoxL : Fin m → Vec d)
    (ω : Fin K → MatV d × MatV d) {x : Vec d} {k₀ k : ℕ} (hk₀ : k₀ ≤ k) (hk : k ≤ K)
    (h0 : x ∈ violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k₀)) :
    x ∈ violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k) ∧
      quadFormV (proc (projL R BoxL) a₀ ε K ω k) x
        = quadFormV (proc (projL R BoxL) a₀ ε K ω k₀) x := by
  obtain ⟨n, rfl⟩ : ∃ n, k = k₀ + n := ⟨k - k₀, by omega⟩
  induction n with
  | zero => exact ⟨h0, rfl⟩
  | succ n ih =>
    obtain ⟨hmem, hval⟩ := ih (by omega) (by omega)
    have hk' : k₀ + n < K := by omega
    rw [Nat.add_succ, proc_succ]
    rw [dif_pos hk']
    have hstep : quadFormV (step (projL R BoxL) ε (proc (projL R BoxL) a₀ ε K ω (k₀ + n))
        (ω ⟨k₀ + n, hk'⟩).1) x
        = quadFormV (proc (projL R BoxL) a₀ ε K ω (k₀ + n)) x :=
      quadFormV_step_of_mem_violSet R ε BoxL _ _ hmem
    rw [hstep]
    refine ⟨?_, hval⟩
    obtain ⟨i, h1, h2, hix⟩ := (mem_violSet_iff).mp hmem
    refine (mem_violSet_iff).mpr ⟨i, h1, ?_, hix⟩
    have h2' : quadFormV (proc (projL R BoxL) a₀ ε K ω (k₀ + n)) x ≤ 1 := by
      rw [← hix]; exact h2
    rw [hix, hstep]
    exact h2'

/-! ## The deterministic rescaling -/

/-- **The main deterministic estimate.**  On the event that the state never leaves a `2r`-band
around `a₀·Id` and every increment is bounded by `2d`, every nonzero lattice vector has quadratic
form at the final time at least `1 - ε·(2d)·R²`. -/
theorem one_sub_theta_le_quadFormV (R ε a₀ : ℝ) (K : ℕ)
    (ω : Fin K → MatV d × MatV d) (BoxL : Fin m → Vec d)
    (Λ : Submodule ℤ (Vec d)) {r : ℝ}
    (hmin : ∀ x : Vec d, x ∈ Λ → x ≠ 0 → 1 ≤ ‖x‖)
    (hbox : ∀ x : Vec d, x ∈ Λ → x ≠ 0 → ‖x‖ ≤ R → ∃ i : Fin m, BoxL i = x)
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (ha₀ : 1 < a₀) (hR0 : 0 ≤ R)
    (hband : 1 ≤ (a₀ - 2 * r) * R ^ 2)
    (hξ : ∀ j : Fin K, ‖(ω j).1‖ ≤ 2 * d)
    (hbad : ω ∉ badEvent R BoxL a₀ ε K r)
    {x : Vec d} (hxΛ : x ∈ Λ) (hx0 : x ≠ 0) :
    1 - ε * (2 * d) * R ^ 2 ≤ quadFormV (proc (projL R BoxL) a₀ ε K ω K) x := by
  by_cases hcase : 1 ≤ quadFormV (proc (projL R BoxL) a₀ ε K ω K) x
  · have hnn : (0 : ℝ) ≤ ε * (2 * (d : ℝ)) * R ^ 2 := by
      have h1 : (0 : ℝ) ≤ ε := hε
      have h2 : (0 : ℝ) ≤ R ^ 2 := sq_nonneg R
      positivity
    linarith
  · push_neg at hcase
    have hR2pos : 0 < R ^ 2 := by
      by_contra h
      have h0 : R ^ 2 ≤ 0 := not_lt.mp h
      have hz : R ^ 2 = 0 := le_antisymm h0 (sq_nonneg R)
      nlinarith [hband]
    have hpos : 0 < a₀ - 2 * r := by
      by_contra h
      have h0 : a₀ - 2 * r ≤ 0 := not_lt.mp h
      have := mul_nonpos_of_nonpos_of_nonneg h0 (le_of_lt hR2pos)
      nlinarith [hband]
    have hxR : ‖x‖ ≤ R := by
      have hle1 := (quadFormV_state_squeeze R BoxL a₀ ε K hbad K le_rfl x).1
      have hlt2 : (a₀ - 2 * r) * ‖x‖ ^ 2 < 1 := lt_of_le_of_lt hle1 hcase
      have hlt3 : (a₀ - 2 * r) * ‖x‖ ^ 2 < (a₀ - 2 * r) * R ^ 2 :=
        lt_of_lt_of_le hlt2 hband
      have hsq : ‖x‖ ^ 2 < R ^ 2 := lt_of_mul_lt_mul_left hlt3 (le_of_lt hpos)
      have h4 := (sq_le_sq.mp (le_of_lt hsq))
      rwa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg hR0] at h4
    obtain ⟨i, hi⟩ := hbox x hxΛ hx0 hxR
    have hex : ∃ k, quadFormV (proc (projL R BoxL) a₀ ε K ω k) x ≤ 1 := ⟨K, le_of_lt hcase⟩
    set k₀ := Nat.find hex with hk₀def
    have hk₀le : k₀ ≤ K := Nat.find_min' hex (le_of_lt hcase)
    have hk₀viol : quadFormV (proc (projL R BoxL) a₀ ε K ω k₀) x ≤ 1 := Nat.find_spec hex
    have hA0 : 1 < quadFormV (proc (projL R BoxL) a₀ ε K ω 0) x := by
      have h1 : proc (projL R BoxL) a₀ ε K ω 0 = a₀ • oneV d := rfl
      rw [h1, quadFormV_oneV]
      have h2 : (1 : ℝ) ≤ ‖x‖ ^ 2 := by
        have h3 := hmin x hxΛ hx0
        nlinarith [norm_nonneg x]
      nlinarith
    have hk₀pos : 1 ≤ k₀ := by
      rcases Nat.eq_zero_or_pos k₀ with h | h
      · rw [h] at hk₀viol; linarith
      · exact h
    have hprev : 1 < quadFormV (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)) x := by
      by_contra hle
      push_neg at hle
      have hlt : k₀ - 1 < k₀ := by omega
      exact Nat.find_min hex hlt hle
    have hm : k₀ - 1 < K := by omega
    have hstep : quadFormV (proc (projL R BoxL) a₀ ε K ω k₀) x
        = quadFormV (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)) x
          + ε * quadFormV ((projL R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)))
              ((ω ⟨k₀ - 1, hm⟩).1)) x := by
      have hk : k₀ = (k₀ - 1) + 1 := by omega
      conv_lhs => rw [hk]
      rw [proc_succ, dif_pos hm, step, quadFormV_add, quadFormV_smul]
    have hbound : |quadFormV ((projL R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)))
        ((ω ⟨k₀ - 1, hm⟩).1)) x| ≤ (2 * d) * R ^ 2 := by
      rw [quadFormV_eq_inner]
      have h1 := abs_real_inner_le_norm
        ((projL R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1))) ((ω ⟨k₀ - 1, hm⟩).1))
        (tensorV x)
      have h2 := norm_projL_apply_le R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1))
        ((ω ⟨k₀ - 1, hm⟩).1)
      have h3 : ‖tensorV x‖ = ‖x‖ ^ 2 := norm_tensorV x
      have h4 : ‖(ω ⟨k₀ - 1, hm⟩).1‖ ≤ 2 * d := hξ ⟨k₀ - 1, hm⟩
      have h5 : (0 : ℝ) ≤ 2 * d := by positivity
      have h6 : ‖((projL R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)))
          ((ω ⟨k₀ - 1, hm⟩).1))‖ * ‖tensorV x‖ ≤ (2 * d) * R ^ 2 := by
        rw [h3]
        exact mul_le_mul (le_trans h2 h4) (by nlinarith [norm_nonneg x]) (by positivity) h5
      linarith
    have hfrozen := quadFormV_frozen R ε a₀ K BoxL ω hk₀le le_rfl
      ((mem_violSet_iff).mpr ⟨i, hi ▸ hxR, hi ▸ hk₀viol, hi⟩)
    have hfin : quadFormV (proc (projL R BoxL) a₀ ε K ω K) x
        = quadFormV (proc (projL R BoxL) a₀ ε K ω k₀) x := hfrozen.2
    have hkey : quadFormV (proc (projL R BoxL) a₀ ε K ω k₀) x
        > 1 - ε * (2 * d) * R ^ 2 := by
      have h1 : ε * quadFormV ((projL R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)))
          ((ω ⟨k₀ - 1, hm⟩).1)) x ≥ -ε * ((2 * d) * R ^ 2) := by
        nlinarith [neg_abs_le (quadFormV ((projL R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)))
          ((ω ⟨k₀ - 1, hm⟩).1)) x), hbound, hε]
      linarith [hstep, hprev, h1]
    linarith [hfin, hkey]

/-- **The rescaling keeps the ellipsoid `Λ`-free.**  Under the hypotheses of
`one_sub_theta_le_quadFormV`, the rescaled matrix `(1-θ)⁻¹ • A_K` has quadratic form at least `1`
on every nonzero lattice vector. -/
theorem inCone_rescaled (R ε a₀ : ℝ) (K : ℕ)
    (ω : Fin K → MatV d × MatV d) (BoxL : Fin m → Vec d)
    (Λ : Submodule ℤ (Vec d)) {r : ℝ}
    (hmin : ∀ x : Vec d, x ∈ Λ → x ≠ 0 → 1 ≤ ‖x‖)
    (hbox : ∀ x : Vec d, x ∈ Λ → x ≠ 0 → ‖x‖ ≤ R → ∃ i : Fin m, BoxL i = x)
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (ha₀ : 1 < a₀) (hR0 : 0 ≤ R)
    (hband : 1 ≤ (a₀ - 2 * r) * R ^ 2)
    (hθ : ε * (2 * d) * R ^ 2 < 1)
    (hξ : ∀ j : Fin K, ‖(ω j).1‖ ≤ 2 * d)
    (hbad : ω ∉ badEvent R BoxL a₀ ε K r) :
    ∀ x ∈ Λ, x ≠ 0 →
      1 ≤ quadFormV ((1 - ε * (2 * d) * R ^ 2)⁻¹ •
        proc (projL R BoxL) a₀ ε K ω K) x := by
  intro x hxΛ hx0
  have hlow := one_sub_theta_le_quadFormV R ε a₀ K ω BoxL Λ hmin hbox hε hr ha₀ hR0 hband hξ
    hbad hxΛ hx0
  have hpos : (0 : ℝ) < 1 - ε * (2 * d) * R ^ 2 := by linarith
  rw [quadFormV_smul, le_inv_mul_iff₀ hpos]
  linarith

/-! ## The increment event

The second ingredient of the good event is that no single Gaussian increment is large.  Since a
single sample coordinate of `sampleLaw d K` is a standard Gaussian on `MatV d`, the tail bound
`Commons.Probability.Gaussian.stdGaussian_norm_sq_tail_card` gives a union bound over the `K`
increments. -/

/-- The marginal law of one coordinate of the sample. -/
lemma sampleLaw_map_fst (d K : ℕ) (j : Fin K) :
    (sampleLaw d K).map (fun ω : Fin K → MatV d × MatV d => (ω j).1)
      = ProbabilityTheory.stdGaussian (MatV d) := by
  have hmp : (sampleLaw d K).map (fun ω : Fin K → MatV d × MatV d => ω j)
      = (ProbabilityTheory.stdGaussian (MatV d)).prod
          (ProbabilityTheory.stdGaussian (MatV d)) :=
    (MeasureTheory.measurePreserving_eval
      (μ := fun _ : Fin K => (ProbabilityTheory.stdGaussian (MatV d)).prod
        (ProbabilityTheory.stdGaussian (MatV d))) j).map_eq
  rw [show (fun ω : Fin K → MatV d × MatV d => (ω j).1)
      = Prod.fst ∘ (fun ω : Fin K → MatV d × MatV d => ω j) from rfl,
    ← MeasureTheory.Measure.map_map measurable_fst (measurable_pi_apply j), hmp,
    MeasureTheory.measurePreserving_fst.map_eq]

/-- Mass is transported by a measurable map. -/
lemma measureReal_preimage_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : MeasureTheory.Measure α) {f : α → β} (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) : μ.real (f ⁻¹' s) = (μ.map f).real s := by
  rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def,
    MeasureTheory.Measure.map_apply hf hs]

/-- The event that one of the Gaussian increments has norm larger than `b`. -/
def incrEvent (d K : ℕ) (b : ℝ) : Set (Fin K → MatV d × MatV d) :=
  {ω | ∃ j : Fin K, b < ‖(ω j).1‖}

theorem incrEvent_measureReal_le (d K : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (sampleLaw d K).real (incrEvent d K b)
      ≤ (K : ℝ) * ((2 : ℝ) ^ (d * d) * Real.exp (-(3 / 8) * b ^ 2)) := by
  have hsub : incrEvent d K b ⊆ ⋃ j ∈ (Finset.univ : Finset (Fin K)),
      {ω : Fin K → MatV d × MatV d | b < ‖(ω j).1‖} := by
    rintro ω ⟨j, hj⟩
    exact Set.mem_biUnion (Finset.mem_univ j) hj
  have hsingle : ∀ j : Fin K,
      (sampleLaw d K).real {ω : Fin K → MatV d × MatV d | b < ‖(ω j).1‖}
        ≤ (2 : ℝ) ^ (d * d) * Real.exp (-(3 / 8) * b ^ 2) := by
    intro j
    have hset : {ω : Fin K → MatV d × MatV d | b < ‖(ω j).1‖}
        = (fun ω : Fin K → MatV d × MatV d => (ω j).1) ⁻¹'
            {ξ : MatV d | b < ‖ξ‖} := rfl
    have hmble : MeasurableSet {ξ : MatV d | b < ‖ξ‖} :=
      measurableSet_lt measurable_const (by fun_prop)
    rw [hset, measureReal_preimage_map _ (measurable_pi_apply j).fst hmble,
      sampleLaw_map_fst]
    have hmono : (ProbabilityTheory.stdGaussian (MatV d)).real {ξ : MatV d | b < ‖ξ‖}
        ≤ (ProbabilityTheory.stdGaussian (MatV d)).real {ξ : MatV d | b ^ 2 ≤ ‖ξ‖ ^ 2} :=
      MeasureTheory.measureReal_mono (fun ξ hξ => by
        have hξ' : b < ‖ξ‖ := hξ
        have h2 : (0 : ℝ) < ‖ξ‖ + b := by linarith [norm_nonneg ξ, hξ']
        have h1 : b ^ 2 < ‖ξ‖ ^ 2 := by
          nlinarith [mul_lt_mul_of_pos_right hξ' h2, norm_nonneg ξ]
        exact h1.le) (MeasureTheory.measure_ne_top _ _)
    refine le_trans hmono ?_
    have h := Commons.Probability.Gaussian.stdGaussian_norm_sq_tail_card
      (ι := Fin d × Fin d) (u := b ^ 2) (by positivity)
    simpa [Fintype.card_prod, Fintype.card_fin] using h
  calc (sampleLaw d K).real (incrEvent d K b)
      ≤ (sampleLaw d K).real (⋃ j ∈ (Finset.univ : Finset (Fin K)),
          {ω : Fin K → MatV d × MatV d | b < ‖(ω j).1‖}) :=
        MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top _ _)
    _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin K)),
          (sampleLaw d K).real {ω : Fin K → MatV d × MatV d | b < ‖(ω j).1‖} :=
        MeasureTheory.measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin K)),
          ((2 : ℝ) ^ (d * d) * Real.exp (-(3 / 8) * b ^ 2)) :=
        Finset.sum_le_sum (fun j _ => hsingle j)
    _ = (K : ℝ) * ((2 : ℝ) ^ (d * d) * Real.exp (-(3 / 8) * b ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## Combining the two events -/

/-- If two events have probability at most `exp (-d)` each, their union does not exhaust the
sample space. -/
theorem real_lt_one_of_le (d K : ℕ) (R a₀ ε : ℝ) (BoxL : Fin m → Vec d) {r : ℝ}
    (hbad : (sampleLaw d K).real (badEvent R BoxL a₀ ε K r) ≤ Real.exp (-(d : ℝ)))
    (hincr : (sampleLaw d K).real (incrEvent d K (2 * d)) ≤ Real.exp (-(d : ℝ)))
    (hsmall : 2 * Real.exp (-(d : ℝ)) < 1) :
    (sampleLaw d K).real (badEvent R BoxL a₀ ε K r ∪ incrEvent d K (2 * d)) < 1 := by
  have h1 : (sampleLaw d K).real (badEvent R BoxL a₀ ε K r ∪ incrEvent d K (2 * d))
      ≤ (sampleLaw d K).real (badEvent R BoxL a₀ ε K r)
        + (sampleLaw d K).real (incrEvent d K (2 * d)) :=
    MeasureTheory.measureReal_union_le _ _
  linarith

/-- **Existence of a good sample.**  If the union of the state event and the increment event has
measure `< 1`, there is a sample on which the state stays in the `2r`-band and every increment
has norm at most `2d`. -/
theorem exists_good_sample (d K : ℕ) (R a₀ ε : ℝ) (BoxL : Fin m → Vec d) {r : ℝ}
    (h : (sampleLaw d K).real (badEvent R BoxL a₀ ε K r ∪ incrEvent d K (2 * d)) < 1) :
    ∃ ω : Fin K → MatV d × MatV d,
      ω ∉ badEvent R BoxL a₀ ε K r ∧ ∀ j : Fin K, ‖(ω j).1‖ ≤ 2 * d := by
  by_contra hc
  have huniv : badEvent R BoxL a₀ ε K r ∪ incrEvent d K (2 * d) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro ω
    by_contra hω
    rw [Set.mem_union, not_or] at hω
    exact hc ⟨ω, hω.1, fun j => le_of_not_gt (fun hj => hω.2 ⟨j, hj⟩)⟩
  rw [huniv] at h
  rw [MeasureTheory.Measure.real_def, MeasureTheory.measure_univ, ENNReal.toReal_one] at h
  exact lt_irrefl _ h

end

end Submission.Rescale
