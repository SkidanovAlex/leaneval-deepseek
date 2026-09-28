import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.rNorm_smul
import Submission.Work.HP.evaldefs
import Submission.Work.HP.HP2.formEval_ne_zero

/-!
# A form of degree `d` takes a value comparable to the norm of its coefficient vector

We prove `Work.HP.HP2.veronese_sup`: there is a constant `c = c(d,n) > 0` such that every form
`f_a(x) = Σ_μ a_μ x^μ` of degree `d` in `n+1` variables with coefficient vector `a` satisfies
`c * eNorm a ≤ |f_a(x)|` for some `x` in the Euclidean unit ball `rNorm x ≤ 1`.

The argument is topological/functional-analytic and does not compute any integral.  The evaluation
map `T : (Mon d n → ℝ) → C(S, ℝ)`, `b ↦ (x ↦ f_b(x))`, into the sup-normed space of continuous
functions on the compact unit ball `S = {x | rNorm x ≤ 1}` is linear and *injective*: a nonzero
coefficient vector gives a nonzero form (`formEval_ne_zero`), and by homogeneity of the form in `x`
a nonzero value can be moved into the ball.  An injective continuous linear map on a
finite-dimensional space is bounded below, so `c ‖b‖ₛᵤₚ ≤ ‖T b‖` for some `c > 0`.  The sup norm
`‖T b‖` is attained at a point `y₀` of the (compact) ball by the extreme value theorem, and the
Euclidean norm is equivalent to the sup norm (`rNorm b ≤ √N ‖b‖ₛᵤₚ`, `N = #Mon d n`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.HP2

open Finset

/-! ## Elementary Euclidean facts -/

/-- The Euclidean norm is positive off the origin. -/
theorem rNorm_pos {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : v ≠ 0) : 0 < rNorm v :=
  lt_of_le_of_ne (rNorm_nonneg v) (Ne.symm fun h => hv (rNorm_eq_zero.mp h))

/-- The supremum norm is bounded by the Euclidean norm. -/
theorem norm_le_rNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ‖v‖ ≤ rNorm v := by
  rw [pi_norm_le_iff_of_nonneg (rNorm_nonneg v)]
  intro i
  simpa using abs_apply_le_rNorm v i

/-- The Euclidean norm is bounded by `√(card ι)` times the supremum norm. -/
theorem rNorm_le_sqrt_card_mul_norm {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    rNorm v ≤ Real.sqrt (Fintype.card ι : ℝ) * ‖v‖ := by
  have hsq : rNorm v ^ 2 = ∑ i, (v i) ^ 2 := rNorm_sq v
  have h2 : ∑ i, (v i) ^ 2 ≤ ∑ _i : ι, ‖v‖ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at h
    calc (v i) ^ 2 = |v i| ^ 2 := (sq_abs _).symm
      _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have h3 : ∑ _i : ι, ‖v‖ ^ 2 = (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc rNorm v = Real.sqrt (rNorm v ^ 2) := (Real.sqrt_sq (rNorm_nonneg v)).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * ‖v‖ ^ 2) := by
        rw [hsq]
        exact Real.sqrt_le_sqrt (le_trans h2 (le_of_eq h3))
    _ = Real.sqrt (Fintype.card ι : ℝ) * ‖v‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg v)]

/-! ## Continuity, scaling and boundedness of the monomials on the unit ball -/

theorem continuous_formEvalR (d n : ℕ) (b : Mon d n → ℝ) :
    Continuous fun x : Fin (n + 1) → ℝ => formEvalR d n b x := by
  simp only [formEvalR, veronese]
  fun_prop

/-- Every degree-`d` monomial is bounded by `1` on the Euclidean unit ball. -/
theorem abs_veronese_le_one (d n : ℕ) {x : Fin (n + 1) → ℝ} (hx : rNorm x ≤ 1)
    (μ : Mon d n) : |veronese d n x μ| ≤ 1 := by
  rw [veronese, Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => ?_
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (le_trans (abs_apply_le_rNorm x i) hx)

/-- A nonzero form of degree `d ≥ 1` does not vanish identically on the Euclidean unit ball. -/
theorem exists_eval_ne_zero_ball (d n : ℕ) (hd : 1 ≤ d) (b : Mon d n → ℝ) (hb : b ≠ 0) :
    ∃ x : Fin (n + 1) → ℝ, rNorm x ≤ 1 ∧ formEvalR d n b x ≠ 0 := by
  obtain ⟨y, hy⟩ := formEval_ne_zero b hb
  have hzero : formEvalR d n b 0 = 0 := by
    simp only [formEvalR]
    refine Finset.sum_eq_zero fun μ _ => ?_
    refine mul_eq_zero.mpr (Or.inr ?_)
    have hex : ∃ i, (μ.1 i : ℕ) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : (∑ i, (μ.1 i : ℕ)) = 0 := Finset.sum_eq_zero fun i _ => hcon i
      omega
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hynz : y ≠ 0 := fun h => hy (h ▸ hzero)
  have hpos : 0 < rNorm y := rNorm_pos hynz
  refine ⟨(rNorm y)⁻¹ • y, ?_, ?_⟩
  · rw [rNorm_smul, abs_inv, abs_of_nonneg (rNorm_nonneg y)]
    exact le_of_eq (inv_mul_cancel₀ (ne_of_gt hpos))
  · rw [formEvalR_homogeneous d n b y (rNorm y)⁻¹]
    exact mul_ne_zero (pow_ne_zero d (inv_ne_zero (ne_of_gt hpos))) hy


/-- A distinguished exponent vector, `x_0^d`.  (`Mon d n` is nonempty for every `d`, `n`.) -/
def mon0 (d n : ℕ) : Mon d n :=
  ⟨fun i => if i = 0 then ⟨d, Nat.lt_succ_self d⟩ else ⟨0, Nat.succ_pos d⟩, by
    refine Finset.sum_eq_single (0 : Fin (n + 1)) ?_ ?_
    · intro i _ hi
      simp [hi]
    · intro h
      exact absurd (Finset.mem_univ 0) h⟩

/-! ## The main theorem -/

/-- A form of degree `d` in `n+1` variables with coefficient vector `a` attains a value of modulus
`≥ c(d,n) * eNorm a` somewhere in the unit ball. -/
theorem veronese_sup (d n : ℕ) (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Mon d n → ℤ, ∃ x : Fin (n + 1) → ℝ, rNorm x ≤ 1 ∧
      c * eNorm a ≤ |formEvalR d n (toR a) x| := by
  -- the Euclidean unit ball, which is compact
  set S : Set (Fin (n + 1) → ℝ) := {x | rNorm x ≤ 1} with hSdef
  have hScont : Continuous fun x : Fin (n + 1) → ℝ => rNorm x := by
    simp only [rNorm]
    fun_prop
  have hSclosed : IsClosed S := by
    rw [hSdef]
    exact isClosed_le hScont continuous_const
  have hSsub : S ⊆ Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 := by
    intro x hx
    rw [hSdef] at hx
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_trans (norm_le_rNorm x) hx
  have hScompact : IsCompact S :=
    (isCompact_closedBall (0 : Fin (n + 1) → ℝ) 1).of_isClosed_subset hSclosed hSsub
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hScompact
  have hSne : S.Nonempty := ⟨0, by rw [hSdef]; simp [rNorm]⟩
  -- the evaluation map
  set T₀ : (Mon d n → ℝ) →ₗ[ℝ] C(S, ℝ) :=
    { toFun := fun b => ⟨fun y => formEvalR d n b (y : Fin (n + 1) → ℝ),
        (continuous_formEvalR d n b).comp continuous_subtype_val⟩
      map_add' := by
        intro b b'
        ext y
        simp only [ContinuousMap.add_apply, ContinuousMap.coe_mk, formEvalR, Pi.add_apply,
          add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro t b
        ext y
        simp only [ContinuousMap.smul_apply, ContinuousMap.coe_mk, formEvalR, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring } with hT₀def
  have hT₀apply : ∀ (b : Mon d n → ℝ) (y : S),
      (T₀ b) y = formEvalR d n b (y : Fin (n + 1) → ℝ) := by
    intro b y
    rw [hT₀def]
    rfl
  -- the operator is bounded
  have hbound : ∀ b : Mon d n → ℝ, ‖T₀ b‖ ≤ (Fintype.card (Mon d n) : ℝ) * ‖b‖ := by
    intro b
    rw [ContinuousMap.norm_le (T₀ b) (by positivity)]
    intro y
    rw [hT₀apply b y, Real.norm_eq_abs]
    calc |formEvalR d n b (y : Fin (n + 1) → ℝ)|
        = |∑ μ, b μ * veronese d n (y : Fin (n + 1) → ℝ) μ| := rfl
      _ ≤ ∑ μ, |b μ * veronese d n (y : Fin (n + 1) → ℝ) μ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _μ : Mon d n, ‖b‖ := by
          refine Finset.sum_le_sum fun μ _ => ?_
          rw [abs_mul]
          calc |b μ| * |veronese d n (y : Fin (n + 1) → ℝ) μ| ≤ |b μ| * 1 :=
                mul_le_mul_of_nonneg_left (abs_veronese_le_one d n y.2 μ) (abs_nonneg _)
            _ = |b μ| := mul_one _
            _ ≤ ‖b‖ := by simpa using norm_le_pi_norm b μ
      _ = (Fintype.card (Mon d n) : ℝ) * ‖b‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  set T : (Mon d n → ℝ) →L[ℝ] C(S, ℝ) :=
    T₀.mkContinuous (Fintype.card (Mon d n) : ℝ) hbound with hTdef
  have hTapply : ∀ (b : Mon d n → ℝ) (y : S),
      (T b) y = formEvalR d n b (y : Fin (n + 1) → ℝ) := by
    intro b y
    rw [hTdef, LinearMap.mkContinuous_apply, hT₀apply]
  -- the operator is injective
  have hker : ∀ b : Mon d n → ℝ, T b = 0 → b = 0 := by
    intro b hb
    by_contra hbne
    obtain ⟨x, hxS, hx⟩ := exists_eval_ne_zero_ball d n hd b hbne
    have hmem : x ∈ S := by rw [hSdef]; exact hxS
    have h1 : (T b) ⟨x, hmem⟩ = 0 := by rw [hb]; rfl
    rw [hTapply b ⟨x, hmem⟩] at h1
    exact hx h1
  have hinj : Function.Injective T := by
    intro b b' hbb
    have h0 : T (b - b') = 0 := by rw [map_sub, hbb, sub_self]
    exact sub_eq_zero.mp (hker (b - b') h0)
  -- a nonzero vector of the coefficient space
  have hsphere_ne : (Metric.sphere (0 : Mon d n → ℝ) 1).Nonempty := by
    refine ⟨fun μ => if μ = mon0 d n then (1 : ℝ) else 0, ?_⟩
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    refine le_antisymm ?_ ?_
    · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
      intro μ
      split <;> simp
    · have h := norm_le_pi_norm (fun μ : Mon d n => if μ = mon0 d n then (1 : ℝ) else 0)
        (mon0 d n)
      simpa using h
  -- the minimum of `‖T ·‖` on the coefficient sphere
  obtain ⟨b₀, hb₀mem, hb₀min⟩ :=
    (isCompact_sphere (0 : Mon d n → ℝ) 1).exists_isMinOn hsphere_ne
      (continuous_norm.comp T.continuous).continuousOn
  rw [isMinOn_iff] at hb₀min
  have hb₀ne : b₀ ≠ 0 := by
    intro h0
    rw [h0, Metric.mem_sphere, dist_self] at hb₀mem
    norm_num at hb₀mem
  have hcpos : 0 < ‖T b₀‖ := by
    rw [norm_pos_iff]
    exact fun h => hb₀ne (hker b₀ h)
  set M : ℝ := max 1 (Real.sqrt (Fintype.card (Mon d n) : ℝ)) with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hMge : Real.sqrt (Fintype.card (Mon d n) : ℝ) ≤ M := le_max_right _ _
  -- the general bound for real coefficient vectors
  have hmain : ∀ b : Mon d n → ℝ, ∃ x : Fin (n + 1) → ℝ, rNorm x ≤ 1 ∧
      (‖T b₀‖ / M) * rNorm b ≤ |formEvalR d n b x| := by
    intro b
    have hstep1 : ‖T b₀‖ * ‖b‖ ≤ ‖T b‖ := by
      by_cases hb0 : b = 0
      · rw [hb0]; simp
      · have hbnorm : ‖b‖ ≠ 0 := by rwa [norm_ne_zero_iff]
        have hsp : (‖b‖)⁻¹ • b ∈ Metric.sphere (0 : Mon d n → ℝ) 1 := by
          rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
            abs_of_nonneg (norm_nonneg b), inv_mul_cancel₀ hbnorm]
        have hmin := hb₀min _ hsp
        simp only [Function.comp_apply] at hmin
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg b)] at hmin
        calc ‖T b₀‖ * ‖b‖ ≤ (‖b‖⁻¹ * ‖T b‖) * ‖b‖ := mul_le_mul_of_nonneg_right hmin (norm_nonneg b)
          _ = ‖T b‖ := by rw [mul_comm (‖b‖⁻¹) (‖T b‖), mul_assoc, inv_mul_cancel₀ hbnorm, mul_one]
    have hstep2 : (‖T b₀‖ / M) * rNorm b ≤ ‖T b₀‖ * ‖b‖ := by
      have h1 : rNorm b ≤ M * ‖b‖ :=
        le_trans (rNorm_le_sqrt_card_mul_norm b)
          (mul_le_mul_of_nonneg_right hMge (norm_nonneg b))
      calc (‖T b₀‖ / M) * rNorm b ≤ (‖T b₀‖ / M) * (M * ‖b‖) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ‖T b₀‖ * ‖b‖ := by
            rw [← mul_assoc, div_mul_cancel₀ ‖T b₀‖ (ne_of_gt hMpos)]
    obtain ⟨y₀, hy₀S, hy₀max⟩ := hScompact.exists_isMaxOn hSne
      ((continuous_abs.comp (continuous_formEvalR d n b)).continuousOn)
    rw [isMaxOn_iff] at hy₀max
    have hy₀r : rNorm y₀ ≤ 1 := by
      rw [hSdef] at hy₀S
      exact hy₀S
    have hnorm : ‖T b‖ ≤ |formEvalR d n b y₀| :=
      (ContinuousMap.norm_le (T b) (abs_nonneg _)).mpr fun y => by
        rw [hTapply b y, Real.norm_eq_abs]
        exact hy₀max y y.2
    exact ⟨y₀, hy₀r, le_trans (le_trans hstep2 hstep1) hnorm⟩
  refine ⟨‖T b₀‖ / M, div_pos hcpos hMpos, fun a => ?_⟩
  obtain ⟨x, hxS, hx⟩ := hmain (toR a)
  exact ⟨x, hxS, by simpa only [eNorm, toR, rNorm] using hx⟩

end Work.HP.HP2
