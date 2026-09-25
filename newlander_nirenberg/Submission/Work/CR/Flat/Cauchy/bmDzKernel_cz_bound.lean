/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Calderón–Zygmund bounds for `∂_{z_k}(bmKernel j)`

The kernel `bmDzKernel k j x = -n · conj(x_k) · conj(x_j) · ‖x‖^{-2n-2}` is a
Calderón–Zygmund kernel of homogeneity `-2n` on `ℂⁿ = Fin n → ℂ`: it satisfies a size bound
`‖Φ x‖ ≤ A ‖x‖^{-2n}`, a difference bound `‖Φ (x-h) - Φ x‖ ≤ A ‖h‖ ‖x‖^{-2n-1}` (with `‖·‖`
the Euclidean norm `eucNorm`), and its mean over every annulus centred at the origin vanishes.

This file proves the Schauder (Hölder) estimate for the associated singular integral
`z ↦ ∫_{eucBall (4R)} Φ x · (g (z+x) - g z)` for `α`-Hölder `g` vanishing off a ball, i.e. the
statement `bmDzKernel_cz_bound`.  The `L^∞` part is proved directly here; the `α`-Hölder part
in `z` is the general Calderón–Zygmund statement `Work.CR.Flat.Cauchy.bmCz.czDifferenceEstimate`,
specialised to `Φ = bmDzKernel k j`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_bmDzKernel_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmDzKernel_eucShell_eq_zero
import Submission.Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.czKernel_holderBound

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

namespace BmDzCzAux

/-! ## Elementary facts about the Euclidean norm -/

/-- `eucNorm` is the `L²` norm of `x`. -/
lemma eucNorm_eq_norm_withLp {n : ℕ} (x : Fin n → ℂ) :
    eucNorm x = ‖(WithLp.equiv 2 (Fin n → ℂ)).symm x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [eucNorm]

lemma eucNorm_add_le {n : ℕ} (x y : Fin n → ℂ) : eucNorm (x + y) ≤ eucNorm x + eucNorm y := by
  rw [eucNorm_eq_norm_withLp (x + y), eucNorm_eq_norm_withLp x, eucNorm_eq_norm_withLp y]
  rw [show (WithLp.equiv 2 (Fin n → ℂ)).symm (x + y)
      = (WithLp.equiv 2 (Fin n → ℂ)).symm x + (WithLp.equiv 2 (Fin n → ℂ)).symm y from by
    simp [WithLp.equiv_symm_apply]]
  exact norm_add_le _ _

lemma eucNorm_sub_le {n : ℕ} (x y : Fin n → ℂ) : eucNorm (x - y) ≤ eucNorm x + eucNorm y := by
  rw [eucNorm_eq_norm_withLp (x - y), eucNorm_eq_norm_withLp x, eucNorm_eq_norm_withLp y]
  rw [show (WithLp.equiv 2 (Fin n → ℂ)).symm (x - y)
      = (WithLp.equiv 2 (Fin n → ℂ)).symm x - (WithLp.equiv 2 (Fin n → ℂ)).symm y from by
    simp [WithLp.equiv_symm_apply]]
  exact norm_sub_le _ _

/-! ## Continuity of a Hölder function -/

/-- A function on `ℂⁿ` which is Hölder continuous of positive order is continuous. -/
lemma continuous_of_holder {n : ℕ} {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    {g : (Fin n → ℂ) → ℂ} (hg : ∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) :
    Continuous g := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · have hconst : ∀ x y : Fin n → ℂ, g x = g y := by
      intro x y
      have h := hg x y
      rw [← hK0, zero_mul] at h
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
    have : g = fun _ : Fin n → ℂ => g 0 := by funext x; exact hconst x 0
    rw [this]; exact continuous_const
  · rw [Metric.continuous_iff]
    intro x ε hε
    refine ⟨(ε / (K + 1)) ^ (1 / α), by positivity, fun y hy => ?_⟩
    have hδ : ‖x - y‖ < (ε / (K + 1)) ^ (1 / α) := by
      rw [norm_sub_rev]; simpa [dist_eq_norm] using hy
    have hpow : ((ε / (K + 1)) ^ (1 / α)) ^ α = ε / (K + 1) := by
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt hα), Real.rpow_one]
    have hlt : ‖x - y‖ ^ α < ε / (K + 1) := by
      rw [← hpow]
      exact Real.rpow_lt_rpow (norm_nonneg _) hδ hα
    have h2 : ‖g x - g y‖ ≤ K * (ε / (K + 1)) := by
      calc ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α := hg x y
        _ ≤ K * (ε / (K + 1)) := le_of_lt (mul_lt_mul_of_pos_left hlt hKpos)
    have h3 : K * (ε / (K + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity : (0 : ℝ) < K + 1)]
      nlinarith [hε, hKpos]
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt h2 h3

/-! ## Measurability of the kernel -/

lemma measurable_bmDzKernel {n : ℕ} (k j : Fin n) : Measurable (bmDzKernel k j) := by
  have h1 : Measurable fun x : Fin n → ℂ => starRingEnd ℂ (x j) :=
    Complex.continuous_conj.measurable.comp (measurable_pi_apply j)
  have h2 : Measurable fun x : Fin n → ℂ => starRingEnd ℂ (x k) :=
    Complex.continuous_conj.measurable.comp (measurable_pi_apply k)
  have h3 : Measurable fun x : Fin n → ℂ => ((eucNorm x : ℂ) ^ (2 * n + 2)) :=
    (Complex.continuous_ofReal.measurable.comp continuous_eucNorm.measurable).pow_const _
  unfold bmDzKernel
  exact ((measurable_const.mul h1).mul h2).div h3

/-! ## Integrability of powers of `eucNorm` -/

/-- A function bounded by a constant on a set of finite measure is integrable there. -/
lemma integrableOn_of_norm_le_const {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {t : Set X} (hfin : μ t < ⊤) (hsm : MeasurableSet t)
    {F : X → E} (hm : AEStronglyMeasurable F μ) {C : ℝ} (hC : ∀ x ∈ t, ‖F x‖ ≤ C) :
    IntegrableOn F t μ := by
  refine IntegrableOn.of_bound hfin (hm.mono_measure Measure.restrict_le_self) C ?_
  filter_upwards [self_mem_ae_restrict hsm] with x hx
  exact hC x hx

/-- `u ↦ ‖∫_{x ∈ s} F x‖ ≤ ∫_{x ∈ s} ‖F x‖`, with no integrability hypothesis. -/
lemma norm_setIntegral_le_integral_norm {n : ℕ} {s : Set (Fin n → ℂ)} (hsm : MeasurableSet s)
    (F : (Fin n → ℂ) → ℂ) : ‖∫ x in s, F x‖ ≤ ∫ x in s, ‖F x‖ := by
  rw [← integral_indicator hsm (f := F), ← integral_indicator hsm (f := fun x => ‖F x‖)]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s <;> simp [hx]

/-- A power of `eucNorm` is integrable on a Euclidean ball, provided the exponent exceeds
`-2n`. -/
lemma integrableOn_eucNorm_rpow_eucBall {n : ℕ} (hn : 0 < n) {s : ℝ}
    (hs : -(2 * (n : ℝ)) < s) (ρ : ℝ) :
    IntegrableOn (fun x : Fin n → ℂ => eucNorm x ^ s) (eucBall (n := n) ρ) volume := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hfin : (1 : ℕ) ≤ Module.finrank ℝ (Fin n → ℂ) :=
    Nat.succ_le_of_lt Module.finrank_pos
  have hD : (Module.finrank ℝ (Fin n → ℂ) : ℝ) = 2 * (n : ℝ) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Finset.sum_const]
    ring
  have hα : -s < (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by rw [hD]; linarith
  refine IntegrableOn.mono_set ?_ eucBall_subset_ball
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (C := (Real.sqrt n) ^ s + 1)
    hfin hα ?_ (bmCz.measurable_eucNorm_rpow s).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (eucNorm_nonneg x) s), neg_neg]
  rcases lt_or_ge 0 s with hspos | hsneg
  · calc eucNorm x ^ s ≤ (Real.sqrt n * ‖x‖) ^ s :=
          Real.rpow_le_rpow (eucNorm_nonneg x) (bmCz.eucNorm_le_sqrt_mul_norm x) hspos.le
      _ = (Real.sqrt n) ^ s * ‖x‖ ^ s := Real.mul_rpow (Real.sqrt_nonneg n) (norm_nonneg x)
      _ ≤ ((Real.sqrt n) ^ s + 1) * ‖x‖ ^ s := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg x) s)
          linarith [Real.rpow_nonneg (Real.sqrt_nonneg n) s]
  · rcases eq_or_ne x 0 with rfl | hx
    · rcases eq_or_lt_of_le hsneg with h0 | hneg
      · subst h0; norm_num [Real.rpow_zero]
      · simp [Real.zero_rpow hneg.ne]
    · calc eucNorm x ^ s ≤ ‖x‖ ^ s :=
            Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hx) (pi_norm_le_eucNorm x) hsneg
        _ = 1 * ‖x‖ ^ s := by ring
        _ ≤ ((Real.sqrt n) ^ s + 1) * ‖x‖ ^ s := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg x) s)
            linarith [Real.rpow_nonneg (Real.sqrt_nonneg n) s]

/-- A power of `eucNorm` is integrable on a Euclidean annulus, for *every* real exponent. -/
lemma integrableOn_eucNorm_rpow_eucShell {n : ℕ} {s : ℝ} {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : Fin n → ℂ => eucNorm x ^ s) (eucShell (n := n) a b) volume := by
  have hsm : MeasurableSet (eucShell (n := n) a b) := measurableSet_eucShell a b
  have hfin : volume (eucShell (n := n) a b) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono ?_)
      (MeasureTheory.measure_ball_lt_top (x := (0 : Fin n → ℂ)) (r := max b 1))
    intro x hx
    rw [mem_eucShell] at hx
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le (lt_of_le_of_lt (pi_norm_le_eucNorm x) hx.2) (le_max_left _ _)
  refine integrableOn_of_norm_le_const (F := fun x : Fin n → ℂ => eucNorm x ^ s) hfin hsm
    (bmCz.measurable_eucNorm_rpow s).aestronglyMeasurable
    (C := max (a ^ s) ((max b 1) ^ s)) ?_
  intro x hx
  rw [mem_eucShell] at hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (eucNorm_nonneg x) s)]
  rcases lt_or_ge 0 s with hspos | hsneg
  · exact le_trans (Real.rpow_le_rpow (eucNorm_nonneg x)
      (le_of_lt (lt_of_lt_of_le hx.2 (le_max_left _ _))) hspos.le) (le_max_right _ _)
  · exact le_trans (Real.rpow_le_rpow_of_nonpos ha hx.1 hsneg) (le_max_left _ _)

/-! ## A pointwise bound for `bmDzKernel` -/

lemma norm_bmDzKernel_le {n : ℕ} (k j : Fin n) {x : Fin n → ℂ} (hx : x ≠ 0) :
    ‖bmDzKernel k j x‖ ≤ (n : ℝ) / (eucNorm x) ^ (2 * n) := by
  have hX : 0 < eucNorm x := eucNorm_pos hx
  have hjk : ‖x j‖ * ‖x k‖ ≤ (eucNorm x) ^ 2 := by
    have h1 := bmCz.norm_apply_le_eucNorm' x j
    have h2 := bmCz.norm_apply_le_eucNorm' x k
    calc ‖x j‖ * ‖x k‖ ≤ eucNorm x * eucNorm x :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_of_lt hX)
      _ = (eucNorm x) ^ 2 := by ring
  have hnorm : ‖bmDzKernel k j x‖ = (n : ℝ) * (‖x j‖ * ‖x k‖) / (eucNorm x) ^ (2 * n + 2) := by
    rw [bmDzKernel, norm_div, norm_mul, norm_mul, norm_neg, Complex.norm_conj, Complex.norm_conj,
      norm_pow, Complex.norm_natCast]
    rw [show ‖((eucNorm x : ℝ) : ℂ)‖ = eucNorm x from by simp [abs_of_pos hX]]
    ring
  rw [hnorm]
  calc (n : ℝ) * (‖x j‖ * ‖x k‖) / (eucNorm x) ^ (2 * n + 2)
      ≤ (n : ℝ) * (eucNorm x) ^ 2 / (eucNorm x) ^ (2 * n + 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hjk (Nat.cast_nonneg n))
          (by positivity)
    _ = (n : ℝ) / (eucNorm x) ^ (2 * n) := by
        rw [pow_add]
        field_simp

/-! ## The uniform (`L^∞`) bound -/

/-- **Uniform bound for the singular integral.**  If `Φ` satisfies the size bound of a
Calderón–Zygmund kernel of order `-2n` with constant `A`, then for every `α`-Hölder `g` the
integral `∫_{eucBall (4R)} Φ x · (g (z+x) - g z)` is bounded by `C K`, uniformly in `z`; the
constant `C` depends only on `n`, `α`, `R` and `A` (not on `Φ`). -/
theorem czSupBound {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) {R : ℝ} (hR : 0 < R)
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Φ : (Fin n → ℂ) → ℂ}, AEStronglyMeasurable Φ volume →
      (∀ x : Fin n → ℂ, x ≠ 0 → ‖Φ x‖ ≤ A / (eucNorm x) ^ (2 * n)) →
      ∀ (K : ℝ), 0 ≤ K → ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      ∀ z : Fin n → ℂ,
        ‖∫ x in eucBall (n := n) (4 * R), Φ x * (g (z + x) - g z)‖ ≤ C * K := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨C1, hC1pos, hC1⟩ := bmCz.eucRadialBound hn (α - 2 * (n : ℝ)) (by linarith)
  refine ⟨A * C1 * (4 * R) ^ α, by positivity, ?_⟩
  intro Φ hΦm hP1 K hK g hg z
  have hgcont : Continuous g := continuous_of_holder hα hK hg
  have hsm : MeasurableSet (eucBall (n := n) (4 * R)) := measurableSet_eucBall _
  have hpt : ∀ x : Fin n → ℂ,
      ‖Φ x * (g (z + x) - g z)‖ ≤ A * K * eucNorm x ^ (α - 2 * (n : ℝ)) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · have h0 : (0 : ℝ) ≤ eucNorm (0 : Fin n → ℂ) ^ (α - 2 * (n : ℝ)) :=
        Real.rpow_nonneg (eucNorm_nonneg _) _
      have : (0 : ℝ) ≤ A * K * eucNorm (0 : Fin n → ℂ) ^ (α - 2 * (n : ℝ)) :=
        mul_nonneg (mul_nonneg hA.le hK) h0
      simpa using this
    · have hX : 0 < eucNorm x := eucNorm_pos hx
      have hgx : ‖g (z + x) - g z‖ ≤ K * eucNorm x ^ α := by
        have h := hg (z + x) z
        rw [add_sub_cancel_left] at h
        exact le_trans h (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg x) (pi_norm_le_eucNorm x) hα.le) hK)
      rw [norm_mul]
      refine le_trans (mul_le_mul (hP1 x hx) hgx (norm_nonneg _) (by positivity)) (le_of_eq ?_)
      rw [Real.rpow_sub hX,
        show eucNorm x ^ (2 * (n : ℝ)) = eucNorm x ^ (2 * n) from by
          rw [show (2 : ℝ) * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
            Real.rpow_natCast]]
      field_simp
  have hIntMaj : IntegrableOn (fun x : Fin n → ℂ => A * K * eucNorm x ^ (α - 2 * (n : ℝ)))
      (eucBall (n := n) (4 * R)) :=
    (integrableOn_eucNorm_rpow_eucBall hn (by linarith) (4 * R)).const_mul (A * K)
  have hmeasF : AEStronglyMeasurable (fun x : Fin n → ℂ => Φ x * (g (z + x) - g z))
      (volume.restrict (eucBall (n := n) (4 * R))) :=
    (hΦm.mono_measure Measure.restrict_le_self).mul
      ((hgcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable.sub
        aestronglyMeasurable_const)
  have hIntF : IntegrableOn (fun x : Fin n → ℂ => Φ x * (g (z + x) - g z))
      (eucBall (n := n) (4 * R)) :=
    hIntMaj.mono' hmeasF (Filter.Eventually.of_forall fun x => hpt x)
  calc ‖∫ x in eucBall (n := n) (4 * R), Φ x * (g (z + x) - g z)‖
      ≤ ∫ x in eucBall (n := n) (4 * R), ‖Φ x * (g (z + x) - g z)‖ :=
        norm_setIntegral_le_integral_norm hsm _
    _ ≤ ∫ x in eucBall (n := n) (4 * R), A * K * eucNorm x ^ (α - 2 * (n : ℝ)) :=
        setIntegral_mono_on hIntF.norm hIntMaj hsm fun x _ => hpt x
    _ = A * K * ∫ x in eucBall (n := n) (4 * R), eucNorm x ^ (α - 2 * (n : ℝ)) :=
        integral_const_mul _ _
    _ ≤ A * K * (C1 * (4 * R) ^ α) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h := hC1 (4 * R) (by linarith)
        rwa [show α - 2 * (n : ℝ) + 2 * (n : ℝ) = α from by ring] at h
    _ = A * C1 * (4 * R) ^ α * K := by ring

/-! ## Assembly of the two bounds -/

/-- **Reduction of `bmDzKernel_cz_bound` to the Hölder estimate for the difference.**
If the singular integral of `bmDzKernel k j` against `g (z+·) - g z` satisfies the
Calderón–Zygmund difference bound with constant `CD`, then both required bounds hold. -/
theorem bmDzKernel_cz_bound_of {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R) {CD : ℝ} (hCD : 0 < CD)
    (hdiff : ∀ (k j : Fin n) (K : ℝ), 0 ≤ K → ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      ∀ z z' : Fin n → ℂ,
        ‖(∫ x in eucBall (n := n) (4 * R), bmDzKernel k j x * (g (z + x) - g z))
            - (∫ x in eucBall (n := n) (4 * R),
                bmDzKernel k j x * (g (z' + x) - g z'))‖
          ≤ CD * K * ‖z - z'‖ ^ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k j : Fin n) (K : ℝ), 0 ≤ K → ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, R ≤ eucNorm x → g x = 0) →
      (∀ z : Fin n → ℂ,
        ‖∫ x in eucBall (n := n) (4 * R), bmDzKernel k j x * (g (z + x) - g z)‖
          ≤ C * K) ∧
      (∀ z z' : Fin n → ℂ,
        ‖(∫ x in eucBall (n := n) (4 * R), bmDzKernel k j x * (g (z + x) - g z))
            - (∫ x in eucBall (n := n) (4 * R),
                bmDzKernel k j x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α) := by
  obtain ⟨C0, hC0pos, hC0⟩ := bmCz.norm_bmDzKernel_sub_le hn
  set A : ℝ := max (n : ℝ) C0 with hAdef
  have hApos : 0 < A := lt_of_lt_of_le (by exact_mod_cast hn) (le_max_left _ _)
  have hP1 : ∀ (k j : Fin n) (x : Fin n → ℂ), x ≠ 0 →
      ‖bmDzKernel k j x‖ ≤ A / (eucNorm x) ^ (2 * n) := by
    intro k j x hx
    refine le_trans (norm_bmDzKernel_le k j hx) ?_
    exact (div_le_div_iff_of_pos_right (pow_pos (eucNorm_pos hx) _)).mpr (le_max_left _ _)
  obtain ⟨C1, hC1pos, hC1⟩ := czSupBound hn hα hR (A := A) hApos
  refine ⟨max C1 CD, lt_max_of_lt_left hC1pos, ?_⟩
  intro k j K hK g hg _
  constructor
  · intro z
    refine le_trans (hC1 (measurable_bmDzKernel k j).aestronglyMeasurable
      (fun x hx => hP1 k j x hx) K hK g hg z) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hK
  · intro z z'
    refine le_trans (hdiff k j K hK g hg z z') ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hK)
      (Real.rpow_nonneg (norm_nonneg _) α)

/-! ## Further elementary estimates -/

/-- The reverse triangle inequality in the form used below. -/
lemma eucNorm_sub_le_eucNorm {n : ℕ} (x h : Fin n → ℂ) :
    eucNorm x - eucNorm h ≤ eucNorm (x - h) := by
  have h1 := eucNorm_add_le (x - h) h
  rw [show x - h + h = x from by abel] at h1
  linarith

/-- `eucNorm` is invariant under negation. -/
lemma eucNorm_neg {n : ℕ} (x : Fin n → ℂ) : eucNorm (-x) = eucNorm x := by
  simp [eucNorm]

/-- Monotonicity of the Euclidean ball in its radius. -/
lemma eucBall_mono {n : ℕ} {a b : ℝ} (h : a ≤ b) : eucBall (n := n) a ⊆ eucBall (n := n) b :=
  fun x hx => lt_of_lt_of_le hx h

/-- Translation of a set integral on `ℂⁿ`. -/
lemma setIntegral_translate_euc {n : ℕ} (c : Fin n → ℂ) (F : (Fin n → ℂ) → ℂ)
    (A : Set (Fin n → ℂ)) :
    ∫ x in A, F (x + c) = ∫ u in (fun x : Fin n → ℂ => x + c) '' A, F u := by
  have hmp : MeasurePreserving (fun x : Fin n → ℂ => x + c) volume volume :=
    MeasureTheory.measurePreserving_add_right volume c
  have hemb : MeasurableEmbedding (fun x : Fin n → ℂ => x + c) :=
    (Homeomorph.addRight c).measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb F ((fun x : Fin n → ℂ => x + c) '' A)
  rw [show (fun x : Fin n → ℂ => x + c) ⁻¹' ((fun x : Fin n → ℂ => x + c) '' A) = A from by
    ext x; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨a, ha, hax⟩; rwa [add_right_cancel hax] at ha
    · intro hx; exact ⟨x, hx, rfl⟩] at h
  exact h

/-- Sub-additivity of `x ↦ x ^ α` for `0 < α ≤ 1`. -/
theorem rpow_add_le_add_rpow {x y α : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hα0 : 0 < α)
    (hα1 : α ≤ 1) : (x + y) ^ α ≤ x ^ α + y ^ α := by
  have hsubY : ∀ {z : ℝ}, 0 < z → z ^ (α - 1) = z ^ α * z⁻¹ := by
    intro z hz
    rw [Real.rpow_sub hz α 1, div_eq_mul_inv, Real.rpow_one]
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · rw [← hx0, zero_add, Real.zero_rpow (ne_of_gt hα0), zero_add]
  rcases eq_or_lt_of_le hy with hy0 | hypos
  · rw [← hy0, add_zero, Real.zero_rpow (ne_of_gt hα0), add_zero]
  rcases le_or_gt x y with hxy | hxy
  · have h1 : (1 + x / y) ^ α ≤ 1 + x / y := by
      have hle : (1 : ℝ) ≤ 1 + x / y := by linarith [div_nonneg hx hy]
      have h := Real.rpow_le_rpow_of_exponent_le hle hα1
      rwa [Real.rpow_one] at h
    have heq : y * (1 + x / y) = x + y := by
      rw [mul_add, mul_one, mul_comm y (x / y), div_mul_cancel₀ x (ne_of_gt hypos)]; ring
    calc (x + y) ^ α = (y * (1 + x / y)) ^ α := by rw [heq]
      _ = y ^ α * (1 + x / y) ^ α := Real.mul_rpow (le_of_lt hypos) (by positivity)
      _ ≤ y ^ α * (1 + x / y) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (le_of_lt hypos) α)
      _ ≤ y ^ α + x ^ α := by
          rw [mul_add, mul_one]
          have hy1 : y ^ α * (x / y) = x * y ^ (α - 1) := by
            rw [div_eq_mul_inv, ← mul_assoc, mul_comm (y ^ α) x, mul_assoc, ← hsubY hypos]
          rw [hy1]
          have h5 : y ^ (α - 1) ≤ x ^ (α - 1) :=
            Real.rpow_le_rpow_of_nonpos hxpos hxy (by linarith)
          have h6 : x * y ^ (α - 1) ≤ x ^ α := by
            calc x * y ^ (α - 1) ≤ x * x ^ (α - 1) := mul_le_mul_of_nonneg_left h5 hx
              _ = x ^ α := by
                  nth_rewrite 1 [← Real.rpow_one x]
                  rw [← Real.rpow_add hxpos, show (1 : ℝ) + (α - 1) = α from by ring]
          linarith
      _ = x ^ α + y ^ α := by ring
  · have h1 : (1 + y / x) ^ α ≤ 1 + y / x := by
      have hle : (1 : ℝ) ≤ 1 + y / x := by linarith [div_nonneg hy hx]
      have h := Real.rpow_le_rpow_of_exponent_le hle hα1
      rwa [Real.rpow_one] at h
    have heq : x * (1 + y / x) = x + y := by
      rw [mul_add, mul_one, mul_comm x (y / x), div_mul_cancel₀ y (ne_of_gt hxpos)]
    calc (x + y) ^ α = (x * (1 + y / x)) ^ α := by rw [heq]
      _ = x ^ α * (1 + y / x) ^ α := Real.mul_rpow (le_of_lt hxpos) (by positivity)
      _ ≤ x ^ α * (1 + y / x) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (le_of_lt hxpos) α)
      _ ≤ x ^ α + y ^ α := by
          rw [mul_add, mul_one]
          have hx1 : x ^ α * (y / x) = y * x ^ (α - 1) := by
            rw [div_eq_mul_inv, ← mul_assoc, mul_comm (x ^ α) y, mul_assoc, ← hsubY hxpos]
          rw [hx1]
          have h5 : x ^ (α - 1) ≤ y ^ (α - 1) :=
            Real.rpow_le_rpow_of_nonpos hypos hxy.le (by linarith)
          have h6 : y * x ^ (α - 1) ≤ y ^ α := by
            calc y * x ^ (α - 1) ≤ y * y ^ (α - 1) := mul_le_mul_of_nonneg_left h5 hy
              _ = y ^ α := by
                  nth_rewrite 1 [← Real.rpow_one y]
                  rw [← Real.rpow_add hypos, show (1 : ℝ) + (α - 1) = α from by ring]
          linarith
      _ = x ^ α + y ^ α := by ring

/-- Concavity of `x ↦ x ^ α` in the form used for thin annuli: `a^α - b^α ≤ (a-b)^α`. -/
theorem rpow_sub_le_sub_rpow {a b α : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (hα0 : 0 < α)
    (hα1 : α ≤ 1) : a ^ α - b ^ α ≤ (a - b) ^ α := by
  have h0 : 0 ≤ a - b := by linarith
  have h := rpow_add_le_add_rpow hb h0 hα0 hα1
  rw [show b + (a - b) = a from by ring] at h
  linarith


/-- The exponent bookkeeping of the far-field Calderón–Zygmund estimate. -/
lemma inv_pow_mul_rpow_le {n : ℕ} {α u y : ℝ} (hu : 0 < u) (hy : 0 < y)
    (h : (3 / 4 : ℝ) * y ≤ u) :
    (u ^ (2 * n + 1))⁻¹ * y ^ α ≤ (4 / 3 : ℝ) ^ (2 * n + 1) * y ^ (α - 2 * (n : ℝ) - 1) := by
  have h1 : (u ^ (2 * n + 1))⁻¹ ≤ ((4 / 3 : ℝ) ^ (2 * n + 1)) * (y ^ (2 * n + 1))⁻¹ := by
    have h2 : ((3 / 4 : ℝ) * y) ^ (2 * n + 1) ≤ u ^ (2 * n + 1) :=
      pow_le_pow_left₀ (by positivity) h _
    calc (u ^ (2 * n + 1))⁻¹ ≤ (((3 / 4 : ℝ) * y) ^ (2 * n + 1))⁻¹ :=
          inv_anti₀ (by positivity) h2
      _ = ((3 / 4 : ℝ) ^ (2 * n + 1))⁻¹ * (y ^ (2 * n + 1))⁻¹ := by rw [mul_pow, mul_inv]
      _ = (4 / 3 : ℝ) ^ (2 * n + 1) * (y ^ (2 * n + 1))⁻¹ := by
          congr 1
          rw [← inv_pow]
          congr 1
          norm_num
  calc (u ^ (2 * n + 1))⁻¹ * y ^ α
      ≤ (((4 / 3 : ℝ) ^ (2 * n + 1)) * (y ^ (2 * n + 1))⁻¹) * y ^ α :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hy.le α)
    _ = (4 / 3 : ℝ) ^ (2 * n + 1) * ((y ^ (2 * n + 1))⁻¹ * y ^ α) := by ring
    _ = (4 / 3 : ℝ) ^ (2 * n + 1) * y ^ (α - 2 * (n : ℝ) - 1) := by
        congr 1
        rw [← Real.rpow_natCast y (2 * n + 1), ← Real.rpow_neg hy.le, ← Real.rpow_add hy,
          show -(((2 * n + 1 : ℕ)) : ℝ) + α = α - 2 * (n : ℝ) - 1 by push_cast; ring]

/-- For a nonnegative `f`: an integral over a set covered by `U ∪ V` is bounded by the sum of the
integrals over `U` and `V` (no disjointness needed). -/
lemma setIntegral_le_add_of_subset_union {n : ℕ} {f : (Fin n → ℂ) → ℝ} {T U V : Set (Fin n → ℂ)}
    (hT : T ⊆ U ∪ V) (hUm : MeasurableSet U) (hVm : MeasurableSet V)
    (hU : IntegrableOn f U) (hV : IntegrableOn f V) (hUV : IntegrableOn f (U ∪ V))
    (hVU : IntegrableOn f (V \ U)) (hf : ∀ x, 0 ≤ f x) :
    ∫ x in T, f x ≤ (∫ x in U, f x) + (∫ x in V, f x) := by
  refine le_trans (setIntegral_mono_set hUV (Filter.Eventually.of_forall hf)
    (Filter.Eventually.of_forall hT)) ?_
  rw [show U ∪ V = U ∪ (V \ U) from by
    ext x; simp only [Set.mem_union, Set.mem_diff]; tauto]
  rw [setIntegral_union (by rw [Set.disjoint_left]; intro x hx hx'; exact hx'.2 hx)
    (hVm.diff hUm) hU hVU]
  refine add_le_add le_rfl (setIntegral_mono_set hV (Filter.Eventually.of_forall hf)
    (Filter.Eventually.of_forall (fun x hx => hx.1)))

end BmDzCzAux

/-! ## The Calderón–Zygmund bound for `bmDzKernel` -/

theorem bmDzKernel_cz_bound {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k j : Fin n) (K : ℝ), 0 ≤ K → ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, R ≤ Work.CR.Flat.Cauchy.eucNorm x → g x = 0) →
      (∀ z : Fin n → ℂ,
        ‖∫ x in Work.CR.Flat.Cauchy.eucBall (4 * R),
            Work.CR.Flat.Cauchy.bmDzKernel k j x * (g (z + x) - g z)‖ ≤ C * K) ∧
      (∀ z z' : Fin n → ℂ,
        ‖(∫ x in Work.CR.Flat.Cauchy.eucBall (4 * R),
              Work.CR.Flat.Cauchy.bmDzKernel k j x * (g (z + x) - g z))
            - (∫ x in Work.CR.Flat.Cauchy.eucBall (4 * R),
              Work.CR.Flat.Cauchy.bmDzKernel k j x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨C0, hC0pos, hC0⟩ := bmCz.norm_bmDzKernel_sub_le hn
  set A : ℝ := max (n : ℝ) C0 with hAdef
  have hApos : 0 < A := lt_of_lt_of_le (by exact_mod_cast hn) (le_max_left _ _)
  have hP1 : ∀ (k j : Fin n) (x : Fin n → ℂ), x ≠ 0 →
      ‖bmDzKernel k j x‖ ≤ A / (eucNorm x) ^ (2 * n) := by
    intro k j x hx
    refine le_trans (BmDzCzAux.norm_bmDzKernel_le k j hx) ?_
    exact (div_le_div_iff_of_pos_right (pow_pos (eucNorm_pos hx) _)).mpr (le_max_left _ _)
  have hP2 : ∀ (k j : Fin n) (x h : Fin n → ℂ), 2 * eucNorm h ≤ eucNorm x →
      ‖bmDzKernel k j (x - h) - bmDzKernel k j x‖
        ≤ A * eucNorm h / (eucNorm x) ^ (2 * n + 1) := by
    intro k j x h hxh
    refine le_trans (hC0 k j x h hxh) ?_
    have hXA : C0 ≤ A := le_max_right _ _
    rcases eq_or_ne (eucNorm x) 0 with hX0 | hXne
    · rw [hX0, Real.zero_rpow (by linarith : -(2 * (n : ℝ) + 1) ≠ 0)]
      simp
    · have hXpos : 0 < eucNorm x := lt_of_le_of_ne (eucNorm_nonneg x) (Ne.symm hXne)
      rw [Real.rpow_neg (le_of_lt hXpos),
        show (2 * (n : ℝ) + 1) = ((2 * n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
        div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hXA (eucNorm_nonneg h)) ?_
      positivity
  have hH2 : ∀ (k j : Fin n) (a b : ℝ), 0 < a → a < b →
      ∫ x in eucShell (n := n) a b, bmDzKernel k j x = 0 :=
    fun k j a b ha _ => bmCz.integral_bmDzKernel_eucShell_eq_zero (k := k) (j := j) (ε := a) ha
  have hpair : ∀ p : Fin n × Fin n, ∃ C : ℝ, 0 < C ∧
      ∀ (K : ℝ), 0 ≤ K → ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, R ≤ eucNorm x → g x = 0) →
      ∀ z z' : Fin n → ℂ,
        ‖(∫ x in eucBall (n := n) (4 * R), bmDzKernel p.1 p.2 x * (g (z + x) - g z))
            - (∫ x in eucBall (n := n) (4 * R),
                bmDzKernel p.1 p.2 x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α := fun p => by
    obtain ⟨C, hCpos, hC⟩ := bmCz.czKernel_holderBound hn hα hα1 hR
      (BmDzCzAux.measurable_bmDzKernel p.1 p.2).aestronglyMeasurable hApos
      (hP1 p.1 p.2) (hP2 p.1 p.2) (hH2 p.1 p.2)
    exact ⟨C, hCpos, fun K hK g hg hgsupp => (hC K hK g hg hgsupp).2⟩
  choose CDfun hCDpos hCDbound using hpair
  obtain ⟨p0, -, hp0max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n)) CDfun Finset.univ_nonempty
  obtain ⟨C1, hC1pos, hC1⟩ := BmDzCzAux.czSupBound hn hα hR (A := A) hApos
  refine ⟨max C1 (CDfun p0), lt_max_of_lt_left hC1pos, ?_⟩
  intro k j K hK g hg hgsupp
  constructor
  · intro z
    refine le_trans (hC1 (BmDzCzAux.measurable_bmDzKernel k j).aestronglyMeasurable
      (fun x hx => hP1 k j x hx) K hK g hg z) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hK
  · intro z z'
    refine le_trans (hCDbound (k, j) K hK g hg hgsupp z z') ?_
    have hle : CDfun (k, j) ≤ CDfun p0 := hp0max (k, j) (Finset.mem_univ _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_trans hle (le_max_right _ _)) hK)
      (Real.rpow_nonneg (norm_nonneg _) α)

end Work.CR.Flat.Cauchy
