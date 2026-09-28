import Mathlib
import Submission.Work.HP.Defs

/-!
# The quadratic form `Ψ` describing the cone condition, and elementary volume/scaling facts

For a coefficient vector `a : Mon d n → ℤ`, a parameter `α : ℝ` and `x : Fin (n+1) → ℝ` set
`Ψ a α x = 4α² ⟨a,ν(x)⟩² − ‖a‖²‖ν(x)‖²`.  Since `⟨a,ν(x)⟩ = formEvalR a x` and both terms are
nonnegative, the cone condition `a ∈ C_{ν(x)}^{(α)}` is exactly `Ψ a α x ≤ 0`.

Also proved here: the scaling behaviour of `Ψ` (homogeneous of degree `2d` in `x`), the scaling
behaviour of `Cgam` in its first argument, and the formula for the volume of the cone region
`{x : ‖x‖ ≤ T, a ∈ C_{ν(x)}^{(γ)}}` in terms of `tauArch`.
-/

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Finset
open scoped BigOperators Pointwise

namespace Work.HP

section basic
variable {ι : Type*} [Fintype ι]

/-- `⟨ν(x), a⟩ = formEvalR a x`. -/
theorem dotR_veronese {d n : ℕ} (a : Mon d n → ℤ) (x : Fin (n + 1) → ℝ) :
    dotR (veronese d n x) (toR a) = formEvalR d n (toR a) x := by
  rw [dotR, formEvalR]
  exact Finset.sum_congr rfl fun μ _ => by rw [mul_comm]

/-- `‖toR a‖ = ‖a‖`. -/
theorem rNorm_toR {d n : ℕ} (a : Mon d n → ℤ) : rNorm (toR a) = eNorm a := by
  simp [rNorm, eNorm, toR]

/-- Scaling of `dotR` in the first argument. -/
theorem dotR_const_mul (w : ι → ℝ) (c : ℝ) (t : ι → ℝ) :
    dotR (fun i => c * w i) t = c * dotR w t := by
  rw [dotR, dotR, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Scaling of `rNorm`. -/
theorem rNorm_const_mul (v : ι → ℝ) (c : ℝ) :
    rNorm (fun i => c * v i) = |c| * rNorm v := by
  rw [rNorm, rNorm]
  have h : (∑ i, (c * v i) ^ 2) = c ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]

/-- `Cgam` is invariant under positive scaling of its first argument. -/
theorem Cgam_const_mul (v : ι → ℝ) {γ c : ℝ} (hc : 0 < c) :
    Cgam (fun i => c * v i) γ = Cgam v γ := by
  ext t
  simp only [Cgam, Set.mem_ofPred_eq, dotR_const_mul, rNorm_const_mul]
  have h : c * rNorm v * rNorm t / (2 * γ) = c * (rNorm v * rNorm t / (2 * γ)) := by ring
  rw [abs_mul, abs_of_pos hc, h]
  constructor
  · intro hle
    exact le_of_mul_le_mul_left hle hc
  · intro hle
    exact mul_le_mul_of_nonneg_left hle hc.le

end basic

/-- The form `Ψ_a^{(α)}(x) = 4α²⟨a,ν(x)⟩² − ‖a‖²‖ν(x)‖²`; the cone condition `a ∈ C_{ν(x)}^{(α)}`
is equivalent to `Ψ ≤ 0`. -/
def Psi (d n : ℕ) (a : Mon d n → ℤ) (α : ℝ) (x : Fin (n + 1) → ℝ) : ℝ :=
  4 * α ^ 2 * (formEvalR d n (toR a) x) ^ 2 - (eNorm a) ^ 2 * (rNorm (veronese d n x)) ^ 2

/-- The cone condition is `Ψ ≤ 0`. -/
theorem Psi_nonpos_iff {d n : ℕ} (a : Mon d n → ℤ) {α : ℝ} (hα : 0 < α)
    (x : Fin (n + 1) → ℝ) :
    Psi d n a α x ≤ 0 ↔ (toR a) ∈ Cgam (veronese d n x) α := by
  have hQ : dotR (veronese d n x) (toR a) = formEvalR d n (toR a) x := dotR_veronese a x
  have hS : rNorm (toR a) = eNorm a := rNorm_toR a
  have h2a : (0:ℝ) < 2 * α := by linarith
  have hAnn : (0:ℝ) ≤ eNorm a := Real.sqrt_nonneg _
  have hSnn : (0:ℝ) ≤ rNorm (veronese d n x) := Real.sqrt_nonneg _
  simp only [Cgam, Set.mem_ofPred_eq, Psi, hQ, hS]
  rw [le_div_iff₀ h2a]
  constructor
  · intro h
    have h1 : (2 * α * |formEvalR d n (toR a) x|) ^ 2 ≤ (eNorm a * rNorm (veronese d n x)) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
      nlinarith [h]
    have h2 := sq_le_sq.mp h1
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα.le) (abs_nonneg _)),
        abs_of_nonneg (mul_nonneg hAnn hSnn)] at h2
    linarith [h2]
  · intro h
    have h1 : 2 * α * |formEvalR d n (toR a) x| ≤ eNorm a * rNorm (veronese d n x) := by
      have h' := mul_le_mul_of_nonneg_left h h2a.le
      have h'' : 2 * α * (eNorm a * rNorm (veronese d n x) / (2 * α)) =
          eNorm a * rNorm (veronese d n x) := by
        field_simp
      linarith [h', h'']
    have h2 : (2 * α * |formEvalR d n (toR a) x|) ^ 2 ≤ (eNorm a * rNorm (veronese d n x)) ^ 2 := by
      rw [sq, sq]
      exact mul_self_le_mul_self (by positivity) h1
    have h3 : (2 * α * |formEvalR d n (toR a) x|) ^ 2 =
        4 * α ^ 2 * (formEvalR d n (toR a) x) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]; ring
    have h4 : (eNorm a * rNorm (veronese d n x)) ^ 2 =
        (eNorm a) ^ 2 * (rNorm (veronese d n x)) ^ 2 := by ring
    rw [h3, h4] at h2
    linarith [h2]

/-- The Veronese map is homogeneous of degree `d`. -/
theorem veronese_const_mul {d n : ℕ} (T : ℝ) (u : Fin (n + 1) → ℝ) :
    veronese d n (fun i => T * u i) = fun μ => T ^ d * veronese d n u μ := by
  funext μ
  simp only [veronese]
  have h : ∏ i, (T * u i) ^ ((μ.1 i : ℕ)) =
      ∏ i, (T ^ ((μ.1 i : ℕ)) * u i ^ ((μ.1 i : ℕ))) :=
    Finset.prod_congr rfl fun i _ => by rw [mul_pow]
  rw [h, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have h2 : (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), ((μ.1 i : ℕ))) = d := by
    simpa using μ.2
  rw [h2]

/-- `formEvalR` is homogeneous of degree `d`. -/
theorem formEvalR_const_mul {d n : ℕ} (a : Mon d n → ℤ) (T : ℝ) (u : Fin (n + 1) → ℝ) :
    formEvalR d n (toR a) (fun i => T * u i) = T ^ d * formEvalR d n (toR a) u := by
  simp only [formEvalR]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => by rw [veronese_const_mul]; ring

/-- `Ψ` is homogeneous of degree `2d` in `x`. -/
theorem Psi_const_mul {d n : ℕ} (a : Mon d n → ℤ) (α T : ℝ) (u : Fin (n + 1) → ℝ)
    (hT : 0 ≤ T) :
    Psi d n a α (fun i => T * u i) = T ^ (2 * d) * Psi d n a α u := by
  have hQ := formEvalR_const_mul (d := d) (n := n) a T u
  have hS : rNorm (veronese d n (fun i => T * u i)) = T ^ d * rNorm (veronese d n u) := by
    rw [veronese_const_mul, rNorm_const_mul, abs_of_nonneg (pow_nonneg hT d)]
  simp only [Psi, hQ, hS]
  rw [Nat.mul_comm 2 d, pow_mul]
  ring

/-- Membership in the cone region is invariant under scaling `x` by a positive factor. -/
theorem Cgam_veronese_const_mul {d n : ℕ} (a : Mon d n → ℤ) {γ T : ℝ} (hT : 0 < T)
    (u : Fin (n + 1) → ℝ) :
    toR a ∈ Cgam (veronese d n (fun i => T * u i)) γ ↔ toR a ∈ Cgam (veronese d n u) γ := by
  rw [veronese_const_mul, Cgam_const_mul (v := veronese d n u) (γ := γ) (c := T ^ d)
    (pow_pos hT d)]

/-- The cone region inside the ball of radius `T` is the ball scaled cone region of radius `1`. -/
theorem cone_region_eq_smul {d n : ℕ} (a : Mon d n → ℤ) {γ T : ℝ} (hT : 0 < T) :
    {x : Fin (n + 1) → ℝ | rNorm x ≤ T ∧ (toR a) ∈ Cgam (veronese d n x) γ} =
      T • ({u : Fin (n + 1) → ℝ | rNorm u ≤ 1 ∧ (toR a) ∈ Cgam (veronese d n u) γ} :
        Set (Fin (n + 1) → ℝ)) := by
  ext x
  constructor
  · intro hx
    refine ⟨fun i => T⁻¹ * x i, ⟨?_, ?_⟩, ?_⟩
    · rw [rNorm_const_mul, abs_of_pos (inv_pos.mpr hT)]
      calc T⁻¹ * rNorm x ≤ T⁻¹ * T :=
            mul_le_mul_of_nonneg_left hx.1 (le_of_lt (inv_pos.mpr hT))
        _ = 1 := by field_simp
    · have h2 : toR a ∈ Cgam (veronese d n (fun i => T * (T⁻¹ * x i))) γ := by
        rw [show (fun i => T * (T⁻¹ * x i)) = x from by funext i; field_simp]
        exact hx.2
      exact (Cgam_veronese_const_mul a hT (fun i => T⁻¹ * x i)).mp h2
    · funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
  · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
    have hTu : (T • u : Fin (n + 1) → ℝ) = fun i => T * u i := by
      funext i; simp [Pi.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_⟩
    · change rNorm (T • u) ≤ T
      rw [hTu, rNorm_const_mul, abs_of_pos hT]
      calc T * rNorm u ≤ T * 1 := mul_le_mul_of_nonneg_left hu1 hT.le
        _ = T := mul_one T
    · change toR a ∈ Cgam (veronese d n (T • u)) γ
      rw [hTu]
      exact (Cgam_veronese_const_mul a hT u).mpr hu2

/-- The cone region of radius `1` has finite volume. -/
theorem cone_region_volume_ne_top {d n : ℕ} (a : Mon d n → ℤ) (γ : ℝ) :
    volume {u : Fin (n + 1) → ℝ | rNorm u ≤ 1 ∧ (toR a) ∈ Cgam (veronese d n u) γ} ≠ ⊤ := by
  have hsub : {u : Fin (n + 1) → ℝ | rNorm u ≤ 1 ∧ (toR a) ∈ Cgam (veronese d n u) γ} ⊆
      Metric.ball (0 : Fin (n + 1) → ℝ) 2 := by
    intro u hu
    rw [Metric.mem_ball]
    refine lt_of_le_of_lt ?_ (by norm_num : (1:ℝ) < 2)
    rw [dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 1)]
    intro i
    simp only [Pi.zero_apply, dist_zero_right, Real.norm_eq_abs]
    refine le_trans ?_ hu.1
    have : (u i) ^ 2 ≤ ∑ j, (u j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
    calc |u i| = Real.sqrt ((u i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ j, (u j) ^ 2) := Real.sqrt_le_sqrt this
      _ = rNorm u := rfl
  exact ne_top_of_le_ne_top (ne_top_of_lt (MeasureTheory.measure_ball_lt_top)) (measure_mono hsub)

/-- Volume of the cone region: `vol {x : ‖x‖ ≤ T, a ∈ C_ν(x)^{(γ)}} = T^{n+1} τ(a;γ)/γ`. -/
theorem cone_volume (d n : ℕ) (a : Mon d n → ℤ) {γ : ℝ} (hγ : 0 < γ) {T : ℝ} (hT : 0 < T) :
    (volume {x : Fin (n + 1) → ℝ | rNorm x ≤ T ∧ (toR a) ∈ Cgam (veronese d n x) γ}).toReal
      = T ^ (n + 1) * tauArch d n (toR a) γ / γ := by
  rw [cone_region_eq_smul a hT, MeasureTheory.Measure.addHaar_smul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), tauArch]
  rw [show Module.finrank ℝ (Fin (n + 1) → ℝ) = n + 1 from by simp]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ T ^ (n + 1))]
  field_simp

end Work.HP
