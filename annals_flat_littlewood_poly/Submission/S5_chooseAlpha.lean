import Mathlib
import Submission.ArcFamily
import Submission.S5_defs
import Submission.Consts
import Submission.F_cor42_full

/-! Section 5, Lemma 5.3 of the paper (choosing the colouring `α`). -/

noncomputable section
open scoped BigOperators
open MeasureTheory

set_option autoImplicit false

namespace Submission
namespace S5

/-- |∫_a^b sin(cθ) dθ| ≤ b − a when a ≤ b. -/
lemma abs_integral_sin_le_length {c a b : ℝ} (hab : a ≤ b) :
    |∫ θ in a..b, Real.sin (c * θ)| ≤ b - a := by
  have hf : ∀ x ∈ Set.Icc a b, |Real.sin (c * x)| ≤ (1 : ℝ) := by
    intro x hx
    exact Real.abs_sin_le_one (c * x)
  calc
    |∫ θ in a..b, Real.sin (c * θ)| ≤ ∫ θ in a..b, |Real.sin (c * θ)| := by
      simpa using (intervalIntegral.abs_integral_le_integral_abs (μ := MeasureTheory.volume) hab)
    _ ≤ ∫ θ in a..b, (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on hab ?hf ?hg hf
      · exact Continuous.intervalIntegrable (by fun_prop) a b
      · exact Continuous.intervalIntegrable continuous_const a b
    _ = b - a := by
      simp

/-- |coordinate of the constraint vector| ≤ 24πK/√n. -/
lemma abs_vec_coord (n N : ℕ) (hn : 0 < n) (K : ℝ) (hK0 : 0 ≤ K)
    (F : Family.Quad n N) (r : ℕ) (i : Fin N) :
    |vec n N K F r i| ≤ 24 * Real.pi * K / Real.sqrt (n : ℝ) := by
  let lo : ℝ := (F.arc i).lo
  let hi : ℝ := (F.arc i).hi
  have hle : lo ≤ hi := by
    dsimp [lo, hi]
    exact Family.Grid.lo_le_hi (F.arc i)
  have hlen : hi - lo ≤ 6 * Real.pi / (n : ℝ) := by
    dsimp [lo, hi]
    have hsub := Family.Grid.hi_sub_lo (F.arc i) (by exact_mod_cast (ne_of_gt hn))
    have hlenz : ((F.arc i).len : ℝ) ≤ (6 : ℝ) := by
      exact_mod_cast (F.len_le i)
    calc
      (F.arc i).hi - (F.arc i).lo = ((F.arc i).len : ℝ) * Real.pi / (n : ℝ) := hsub
      _ ≤ (6 : ℝ) * Real.pi / (n : ℝ) := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlenz (by positivity : 0 ≤ Real.pi)) (by positivity : 0 ≤ (n : ℝ))
  have hJ : |∫ θ in lo..hi, oddSin r θ| ≤ hi - lo := by
    dsimp [oddSin]
    exact abs_integral_sin_le_length (c := freq r) (a := lo) (b := hi) hle
  have hA0 : 0 ≤ 4 * K * Real.sqrt (n : ℝ) := by positivity
  calc
    |vec n N K F r i| = |4 * K * Real.sqrt (n : ℝ) * ∫ θ in lo..hi, oddSin r θ| := by
        simp [vec, lo, hi]
    _ ≤ (4 * K * Real.sqrt (n : ℝ)) * (hi - lo) := by
        calc
          |4 * K * Real.sqrt (n : ℝ) * ∫ θ in lo..hi, oddSin r θ|
              = |4 * K * Real.sqrt (n : ℝ)| * |∫ θ in lo..hi, oddSin r θ| := by rw [abs_mul]
          _ = (4 * K * Real.sqrt (n : ℝ)) * |∫ θ in lo..hi, oddSin r θ| := by
              rw [abs_of_nonneg hA0]
          _ ≤ (4 * K * Real.sqrt (n : ℝ)) * (hi - lo) := by
              exact mul_le_mul_of_nonneg_left hJ hA0
    _ ≤ (4 * K * Real.sqrt (n : ℝ)) * (6 * Real.pi / (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hlen hA0
    _ = 24 * Real.pi * K / Real.sqrt (n : ℝ) := by
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
        have hsq2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
        field_simp [hn0]
        ring_nf
        rw [hsq2]

/-- The coefficient vectors are bounded in sup norm by `24πK/√n`
(used inside `choose_alpha`). -/
lemma supAbs_vec_le (n N : ℕ) (hn : 0 < n) (K : ℝ) (hK0 : 0 ≤ K)
    (F : Family.Quad n N) (r : ℕ) :
    Discrepancy.supAbs (vec n N K F r) ≤ 24 * Real.pi * K / Real.sqrt (n : ℝ) := by
  refine Discrepancy.supAbs_le_of_forall (vec n N K F r) ?hM ?hM0
  · intro i
    exact abs_vec_coord n N hn K hK0 F r i
  · have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    positivity

/-- `√x = 4·e^{−log(16/x)/2}` for `0 < x`. -/
lemma sqrt_16_div_log {x : ℝ} (hx : 0 < x) :
    Real.sqrt x = 4 * Real.exp (-Real.log (16 / x) / 2) := by
  have hpos : 0 < 16 / x := by positivity
  have hxeq : x = 16 * Real.exp (-Real.log (16 / x)) := by
    have he : Real.exp (Real.log (16 / x)) = 16 / x := Real.exp_log hpos
    calc
      x = 16 * ((16 / x)⁻¹) := by
        field_simp [ne_of_gt hx]
      _ = 16 * Real.exp (-Real.log (16 / x)) := by
        rw [Real.exp_neg, he]
  calc
    Real.sqrt x = Real.sqrt (16 * Real.exp (-Real.log (16 / x))) := by
      rw [← hxeq]
    _ = Real.sqrt ((4 * Real.exp (-Real.log (16 / x) / 2)) ^ 2) := by
      congr 1
      have hexp : Real.exp (-Real.log (16 / x) / 2) ^ 2 = Real.exp (-Real.log (16 / x)) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [mul_pow, hexp]
      norm_num
    _ = 4 * Real.exp (-Real.log (16 / x) / 2) := by
      exact Real.sqrt_sq (by positivity : 0 ≤ 4 * Real.exp (-Real.log (16 / x) / 2))

/-- `u·e^{−u} ≤ u0·e^{−u0}` for `1 ≤ u0 ≤ u`. -/
lemma exp_decay_aux {u0 u : ℝ} (hu01 : 1 ≤ u0) (hu0u : u0 ≤ u) :
    u * Real.exp (-u) ≤ u0 * Real.exp (-u0) := by
  have hposu0 : 0 < u0 := by linarith
  have hw : 0 ≤ u - u0 := sub_nonneg.mpr hu0u
  have hmain : u / u0 ≤ Real.exp (u - u0) := by
    have hr : u / u0 ≤ 1 + (u - u0) := by
      rw [div_le_iff₀ hposu0]
      nlinarith [mul_nonneg hw (sub_nonneg.mpr hu01)]
    exact le_trans hr (by simpa [add_comm] using (Real.add_one_le_exp (u - u0)))
  have hm := mul_le_mul_of_nonneg_right hmain (mul_nonneg hposu0.le (Real.exp_nonneg (-u)))
  calc
    u * Real.exp (-u) = (u / u0) * (u0 * Real.exp (-u)) := by field_simp [ne_of_gt hposu0]
    _ ≤ Real.exp (u - u0) * (u0 * Real.exp (-u)) := hm
    _ = u0 * Real.exp (-u0) := by
      calc
        Real.exp (u - u0) * (u0 * Real.exp (-u))
            = u0 * (Real.exp (u - u0) * Real.exp (-u)) := by ring
        _ = u0 * Real.exp ((u - u0) + (-u)) := by rw [← Real.exp_add]
        _ = u0 * Real.exp (-u0) := by congr 1; ring

/-- `√u·e^{−u/2} ≤ √u0·e^{−u0/2}` for `1 ≤ u0 ≤ u`. -/
lemma sqrt_exp_decay {u0 u : ℝ} (hu01 : 1 ≤ u0) (hu0u : u0 ≤ u) :
    Real.sqrt u * Real.exp (-u / 2) ≤ Real.sqrt u0 * Real.exp (-u0 / 2) := by
  have hu0 : 0 ≤ u := by linarith
  have hu00 : 0 ≤ u0 := by linarith
  have hnon1 : 0 ≤ Real.sqrt u * Real.exp (-u / 2) := by positivity
  have hnon2 : 0 ≤ Real.sqrt u0 * Real.exp (-u0 / 2) := by positivity
  have hsq1 : (Real.sqrt u * Real.exp (-u / 2)) ^ 2 = u * Real.exp (-u) := by
    rw [mul_pow, Real.sq_sqrt hu0, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq2 : (Real.sqrt u0 * Real.exp (-u0 / 2)) ^ 2 = u0 * Real.exp (-u0) := by
    rw [mul_pow, Real.sq_sqrt hu00, pow_two, ← Real.exp_add]
    congr 1
    ring
  have habs : |Real.sqrt u * Real.exp (-u / 2)| ≤ |Real.sqrt u0 * Real.exp (-u0 / 2)| := by
    exact sq_le_sq.mp (by
      rw [hsq1, hsq2]
      exact exp_decay_aux hu01 hu0u)
  rwa [abs_of_nonneg hnon1, abs_of_nonneg hnon2] at habs

/-- `x ↦ (14√(log(16/x))+30)·√x` is increasing on `(0, x0]` (when
`1 ≤ log(16/x0)`). -/
lemma main_mono {x0 x : ℝ} (hx00 : 0 < x0) (hx0 : 0 < x) (hxx0 : x ≤ x0)
    (hu01 : 1 ≤ Real.log (16 / x0)) :
    (14 * Real.sqrt (Real.log (16 / x)) + 30) * Real.sqrt x
      ≤ (14 * Real.sqrt (Real.log (16 / x0)) + 30) * Real.sqrt x0 := by
  have hposx : 0 < 16 / x := by positivity
  have hposx0 : 0 < 16 / x0 := by positivity
  have hu0u : Real.log (16 / x0) ≤ Real.log (16 / x) := by
    refine Real.log_le_log hposx0 ?_
    have hdiv : 16 / x0 ≤ 16 / x := by
      rw [div_le_div_iff₀ hx00 hx0]
      nlinarith
    exact hdiv
  have hdec := sqrt_exp_decay (u0 := Real.log (16 / x0)) (u := Real.log (16 / x)) hu01 hu0u
  have hExp : Real.exp (-(Real.log (16 / x)) / 2) ≤ Real.exp (-(Real.log (16 / x0)) / 2) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have h1 : 14 * (Real.sqrt (Real.log (16 / x)) * Real.exp (-(Real.log (16 / x)) / 2))
      ≤ 14 * (Real.sqrt (Real.log (16 / x0)) * Real.exp (-(Real.log (16 / x0)) / 2)) := by
    exact mul_le_mul_of_nonneg_left hdec (by norm_num)
  have h2 : 30 * Real.exp (-(Real.log (16 / x)) / 2)
      ≤ 30 * Real.exp (-(Real.log (16 / x0)) / 2) := by
    exact mul_le_mul_of_nonneg_left hExp (by norm_num)
  calc
    (14 * Real.sqrt (Real.log (16 / x)) + 30) * Real.sqrt x
        = (14 * Real.sqrt (Real.log (16 / x)) + 30) * (4 * Real.exp (-(Real.log (16 / x)) / 2)) := by
            rw [sqrt_16_div_log hx0]
    _ = 4 * (14 * (Real.sqrt (Real.log (16 / x)) * Real.exp (-(Real.log (16 / x)) / 2))
        + 30 * Real.exp (-(Real.log (16 / x)) / 2)) := by ring
    _ ≤ 4 * (14 * (Real.sqrt (Real.log (16 / x0)) * Real.exp (-(Real.log (16 / x0)) / 2))
        + 30 * Real.exp (-(Real.log (16 / x0)) / 2)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
    _ = (14 * Real.sqrt (Real.log (16 / x0)) + 30) * (4 * Real.exp (-(Real.log (16 / x0)) / 2)) := by ring
    _ = (14 * Real.sqrt (Real.log (16 / x0)) + 30) * Real.sqrt x0 := by
        rw [← sqrt_16_div_log hx00]

/-- `√(1/2^41) ≤ 3 / 2^22`. -/
lemma sqrt_two_pow_41 : Real.sqrt (1 / (2 : ℝ) ^ 41) ≤ 3 / (2 : ℝ) ^ 22 := by
  have hx0sq : (1 / (2 : ℝ) ^ 41) ≤ (3 / (2 : ℝ) ^ 22) ^ 2 := by
    norm_num
  have hpos : 0 ≤ 3 / (2 : ℝ) ^ 22 := by positivity
  have h := Real.sqrt_le_sqrt hx0sq
  rwa [Real.sqrt_sq hpos] at h

/-- `45·log 2 ≤ 63/2`. -/
lemma log45_le : 45 * Real.log 2 ≤ (63 : ℝ) / 2 := by
  have h70 : (70 : ℝ) / 100 = 7 / 10 := by norm_num
  have hl := Submission.Consts.log_two_le_70
  rw [h70] at hl
  nlinarith

/-- `1 ≤ 45·log 2`. -/
lemma one_le_log45 : 1 ≤ 45 * Real.log 2 := by
  have hg := Real.log_two_gt_d9
  nlinarith

/-- Numerical bound behind Lemma 5.3: for `0 < x ≤ 2^(-41)` and `0 ≤ K ≤ 160`,
`(14√(log(16/x)) + 30)·√x·24π·K ≤ 1`. -/
lemma lem53_numeric {x : ℝ} (hx0 : 0 < x) (hx : x ≤ (1 : ℝ) / 2 ^ 41)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : K ≤ 160) :
    (14 * Real.sqrt (Real.log (16 / x)) + 30) * Real.sqrt x * (24 * Real.pi * K) ≤ 1 := by
  let x0 : ℝ := (1 : ℝ) / 2 ^ 41
  have hx00 : 0 < x0 := by
    dsimp [x0]
    positivity
  have hxx0 : x ≤ x0 := by
    dsimp [x0]
    exact hx
  have hdiv : (1 / (2 : ℝ) ^ 41)⁻¹ = (2 : ℝ) ^ 41 := by
    rw [one_div, inv_inv]
  have h16x0 : 16 / x0 = (2 : ℝ) ^ 45 := by
    dsimp [x0]
    calc
      16 / (1 / (2 : ℝ) ^ 41) = 16 * ((1 / (2 : ℝ) ^ 41)⁻¹) := by rw [div_eq_mul_inv]
      _ = 16 * (2 : ℝ) ^ 41 := by rw [hdiv]
      _ = (2 : ℝ) ^ 4 * (2 : ℝ) ^ 41 := by norm_num
      _ = (2 : ℝ) ^ (4 + 41) := by rw [pow_add]
      _ = (2 : ℝ) ^ 45 := by norm_num
  have hu0 : Real.log (16 / x0) = 45 * Real.log 2 := by
    rw [h16x0, Real.log_pow]
    norm_num
  have hu01 : 1 ≤ Real.log (16 / x0) := by
    rw [hu0]
    exact one_le_log45
  have hu0le : Real.log (16 / x0) ≤ (63 : ℝ) / 2 := by
    rw [hu0]
    exact log45_le
  have hmono := main_mono (x0 := x0) (x := x) hx00 hx0 hxx0 hu01
  have h24 : 0 ≤ 24 * Real.pi * K := by
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    positivity
  have h1 : (14 * Real.sqrt (Real.log (16 / x)) + 30) * Real.sqrt x * (24 * Real.pi * K)
      ≤ (14 * Real.sqrt (Real.log (16 / x0)) + 30) * Real.sqrt x0 * (24 * Real.pi * K) := by
    exact mul_le_mul_of_nonneg_right hmono h24
  have hsqrtu0 : Real.sqrt (Real.log (16 / x0)) ≤ 6 := by
    have h31 : (63 : ℝ) / 2 ≤ (6 : ℝ) ^ 2 := by norm_num
    have h1' : Real.sqrt (Real.log (16 / x0)) ≤ Real.sqrt ((63 : ℝ) / 2) :=
      Real.sqrt_le_sqrt hu0le
    have h2' : Real.sqrt ((63 : ℝ) / 2) ≤ 6 := by
      have h := Real.sqrt_le_sqrt h31
      rwa [Real.sqrt_sq (by norm_num : 0 ≤ (6 : ℝ))] at h
    exact le_trans h1' h2'
  have hA : 14 * Real.sqrt (Real.log (16 / x0)) + 30 ≤ 114 := by
    nlinarith [hsqrtu0]
  have hB : Real.sqrt x0 ≤ 3 / (2 : ℝ) ^ 22 := by
    dsimp [x0]
    exact sqrt_two_pow_41
  have hC : 24 * Real.pi * K ≤ 24 * (22 / 7 : ℝ) * 160 := by
    have hpi := Submission.Consts.pi_le_22_div_7
    have h1' : 24 * Real.pi * K ≤ 24 * (22 / 7 : ℝ) * K := by
      nlinarith [mul_le_mul_of_nonneg_left hpi (by positivity : 0 ≤ 24 * K)]
    have h2' : 24 * (22 / 7 : ℝ) * K ≤ 24 * (22 / 7 : ℝ) * 160 := by
      exact mul_le_mul_of_nonneg_left hK (by positivity)
    linarith
  have hnonA : 0 ≤ 14 * Real.sqrt (Real.log (16 / x0)) + 30 := by positivity
  have hnonB : 0 ≤ Real.sqrt x0 := Real.sqrt_nonneg x0
  have hnonC : 0 ≤ 24 * Real.pi * K := h24
  have hBC : (14 * Real.sqrt (Real.log (16 / x0)) + 30) * Real.sqrt x0 * (24 * Real.pi * K)
      ≤ 114 * (3 / (2 : ℝ) ^ 22) * (24 * (22 / 7 : ℝ) * 160) := by
    have h1' := mul_le_mul hA hB hnonB (by norm_num : (0 : ℝ) ≤ 114)
    have h2' := mul_le_mul h1' hC hnonC (by positivity : 0 ≤ 114 * (3 / (2 : ℝ) ^ 22))
    simpa [mul_assoc] using h2'
  have hnum : 114 * (3 / (2 : ℝ) ^ 22) * (24 * (22 / 7 : ℝ) * 160) ≤ 1 := by
    norm_num
  calc
    (14 * Real.sqrt (Real.log (16 / x)) + 30) * Real.sqrt x * (24 * Real.pi * K)
        ≤ (14 * Real.sqrt (Real.log (16 / x0)) + 30) * Real.sqrt x0 * (24 * Real.pi * K) := h1
    _ ≤ 114 * (3 / (2 : ℝ) ^ 22) * (24 * (22 / 7 : ℝ) * 160) := hBC
    _ ≤ 1 := hnum

/-- Lemma 5.3: exists `α` with small hat coefficients. -/
theorem choose_alpha (n N : ℕ) (K : ℝ) (F : Family.Quad n N)
    (hK0 : 0 ≤ K) (hK : K ≤ 160) (hN : (N : ℝ) ≤ (n : ℝ) / 2 ^ 41) :
    ∃ α : Fin N → ℝ, IsColoring α ∧
      ∀ r : Fin n, |ehat n N K F α r.1| ≤ 1 := by
  by_cases hN0 : N = 0
  · subst N
    refine ⟨fun i : Fin 0 => (0 : ℝ), ?_, ?_⟩
    · intro i
      exact (Fin.elim0 i)
    · intro r
      simp [ehat]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
    have hn0 : 0 < n := by
      by_contra hn0c
      have hnle : n = 0 := Nat.eq_zero_of_not_pos hn0c
      have hNle : (N : ℝ) ≤ 0 := by
        rw [hnle] at hN
        norm_num at hN ⊢
        exact hN
      linarith
    have hn0r : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn0)
    let x0 : Fin N → ℝ := fun _ => 0
    let v : Fin n → (Fin N → ℝ) := fun r => vec n N K F r.1
    let c : Fin n → ℝ := fun j =>
      14 * Real.sqrt (Real.log (16 * (n : ℝ) / (N : ℝ)))
    have hx0box : ∀ i : Fin N, x0 i ∈ Set.Icc (-1) 1 := by
      intro i
      dsimp [x0]
      norm_num
    have h1 : (N : ℝ) * (2 : ℝ) ^ 41 ≤ (n : ℝ) := by
      have hN2 : (N : ℝ) ≤ (n : ℝ) / (2 : ℝ) ^ 41 := by simpa using hN
      rwa [le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 41)] at hN2
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ 41 * 16 := by
      have hp : (1 : ℝ) ≤ (2 : ℝ) ^ 41 := by
        have h := pow_le_pow_left₀ (a := (1 : ℝ)) (b := (2 : ℝ)) (by norm_num) (by norm_num) 41
        simpa using h
      have h16 : (2 : ℝ) ^ 41 ≤ (2 : ℝ) ^ 41 * 16 := by
        exact le_mul_of_one_le_right (by positivity : 0 ≤ (2 : ℝ) ^ 41) (by norm_num : (1 : ℝ) ≤ 16)
      exact le_trans hp h16
    have hlogpos : 0 ≤ Real.log (16 * (n : ℝ) / (N : ℝ)) := by
      have hNleBig : (N : ℝ) ≤ (N : ℝ) * ((2 : ℝ) ^ 41 * 16) := by
        simpa using (mul_le_mul_of_nonneg_left hone hNposR.le)
      have h2 : (N : ℝ) * ((2 : ℝ) ^ 41 * 16) ≤ (n : ℝ) * 16 := by
        simpa [mul_assoc] using (mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 16))
      have hmain : (N : ℝ) ≤ 16 * (n : ℝ) := by
        nlinarith [hNleBig, h2]
      have harg1 : 1 ≤ 16 * (n : ℝ) / (N : ℝ) := by
        rw [le_div_iff₀ hNposR]
        nlinarith
      exact Real.log_nonneg harg1
    have hc : ∀ j : Fin n, 0 ≤ c j := by
      intro j
      dsimp [c]
      exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have hterm : ∀ j : Fin n, Real.exp (-(c j) ^ 2 / 196) = (N : ℝ) / (16 * (n : ℝ)) := by
      intro j
      have hL : Real.log (16 * (n : ℝ) / (N : ℝ)) = Real.log (16 * (n : ℝ) / (N : ℝ)) := rfl
      have hc2 : (c j) ^ 2 = 196 * Real.log (16 * (n : ℝ) / (N : ℝ)) := by
        dsimp [c]
        calc
          (14 * Real.sqrt (Real.log (16 * (n : ℝ) / (N : ℝ)))) ^ 2
              = 14 ^ 2 * (Real.sqrt (Real.log (16 * (n : ℝ) / (N : ℝ)))) ^ 2 := by ring
          _ = 196 * Real.log (16 * (n : ℝ) / (N : ℝ)) := by
            rw [Real.sq_sqrt hlogpos]
            norm_num
      have harg : 0 < 16 * (n : ℝ) / (N : ℝ) := by positivity
      calc
        Real.exp (-(c j) ^ 2 / 196)
            = Real.exp (-(196 * Real.log (16 * (n : ℝ) / (N : ℝ))) / 196) := by rw [hc2]
        _ = Real.exp (-Real.log (16 * (n : ℝ) / (N : ℝ))) := by
            congr 1
            field_simp
        _ = (N : ℝ) / (16 * (n : ℝ)) := by
            rw [Real.exp_neg, Real.exp_log harg]
            field_simp [hn0r, ne_of_gt hNposR]
    have hsum_eq : (∑ j : Fin n, Real.exp (-(c j) ^ 2 / 196)) = (N : ℝ) / 16 := by
      calc
        (∑ j : Fin n, Real.exp (-(c j) ^ 2 / 196)) = ∑ j : Fin n, (N : ℝ) / (16 * (n : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm j
        _ = (n : ℝ) * ((N : ℝ) / (16 * (n : ℝ))) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ = (N : ℝ) / 16 := by
            field_simp [hn0r]
    have hsum : (∑ j : Fin n, Real.exp (-(c j) ^ 2 / 196)) ≤ (N : ℝ) / 16 := by
      exact le_of_eq hsum_eq
    rcases Discrepancy.cor42_full N n v x0 hx0box c hc hsum with ⟨x, hx1, hx2⟩
    refine ⟨x, ?_, ?_⟩
    · intro i
      rcases hx1 i with h | h
      · right; exact h
      · left; exact h
    · intro r
      have hstep := hx2 r
      have hle0 : |ehat n N K F x r.1|
          ≤ (c r + 30) * Real.sqrt (N : ℝ) * Discrepancy.supAbs (vec n N K F r.1) := by
        have heq : |ehat n N K F x r.1|
            = |Discrepancy.dot (fun i : Fin N => x i - x0 i) (vec n N K F r.1)| := by
          congr 1
          calc
            ehat n N K F x r.1 = Discrepancy.dot x (vec n N K F r.1) := rfl
            _ = Discrepancy.dot (fun i : Fin N => x i - x0 i) (vec n N K F r.1) := by
                unfold Discrepancy.dot
                apply Finset.sum_congr rfl
                intro i hi
                dsimp [x0]
                ring
        rw [heq]
        exact hstep
      have hsup : Discrepancy.supAbs (vec n N K F r.1)
          ≤ 24 * Real.pi * K / Real.sqrt (n : ℝ) := by
        exact supAbs_vec_le n N hn0 K hK0 F r.1
      have hmult : 0 ≤ (c r + 30) * Real.sqrt (N : ℝ) := by
        exact mul_nonneg (add_nonneg (hc r) (by norm_num)) (Real.sqrt_nonneg _)
      have hle1 : (c r + 30) * Real.sqrt (N : ℝ) * Discrepancy.supAbs (vec n N K F r.1)
          ≤ (c r + 30) * Real.sqrt (N : ℝ) * (24 * Real.pi * K / Real.sqrt (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsup hmult
      have hN2 : (N : ℝ) * (2 : ℝ) ^ 41 ≤ (n : ℝ) := h1
      have hx : (N : ℝ) / (n : ℝ) ≤ (1 : ℝ) / 2 ^ 41 := by
        rw [div_le_div_iff₀ (by positivity : 0 < (n : ℝ)) (by positivity : 0 < (2 : ℝ) ^ 41)]
        simpa using hN2
      have hnum := lem53_numeric (x := (N : ℝ) / (n : ℝ)) (by positivity) hx hK0 hK
      have hB : (c r + 30) * Real.sqrt (N : ℝ) * (24 * Real.pi * K / Real.sqrt (n : ℝ))
          ≤ 1 := by
        have hsqrt : Real.sqrt ((N : ℝ) / (n : ℝ)) = Real.sqrt (N : ℝ) / Real.sqrt (n : ℝ) :=
          Real.sqrt_div (by positivity : 0 ≤ (N : ℝ)) (n : ℝ)
        have hlog : Real.log (16 * (n : ℝ) / (N : ℝ)) = Real.log (16 / ((N : ℝ) / (n : ℝ))) := by
          congr 1
          field_simp [hn0r, ne_of_gt hNposR]
        calc
          (c r + 30) * Real.sqrt (N : ℝ) * (24 * Real.pi * K / Real.sqrt (n : ℝ))
              = (c r + 30) * (Real.sqrt (N : ℝ) / Real.sqrt (n : ℝ)) * (24 * Real.pi * K) := by ring
          _ = (14 * Real.sqrt (Real.log (16 * (n : ℝ) / (N : ℝ))) + 30)
                * (Real.sqrt (N : ℝ) / Real.sqrt (n : ℝ)) * (24 * Real.pi * K) := by rfl
          _ = (14 * Real.sqrt (Real.log (16 / ((N : ℝ) / (n : ℝ)))) + 30)
                * (Real.sqrt (N : ℝ) / Real.sqrt (n : ℝ)) * (24 * Real.pi * K) := by rw [hlog]
          _ = (14 * Real.sqrt (Real.log (16 / ((N : ℝ) / (n : ℝ)))) + 30)
                * Real.sqrt ((N : ℝ) / (n : ℝ)) * (24 * Real.pi * K) := by rw [← hsqrt]
          _ ≤ 1 := hnum
      exact le_trans (le_trans hle0 (le_trans hle1 hB)) (by norm_num)

end S5
end Submission
