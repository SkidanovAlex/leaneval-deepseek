import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.dropTrace

/-!
# The `y`-window of the `A` branch is strictly increasing on `[ang (5/2), π]`

`psiA1 u = 3 * |trN1 u| - yclip * (2 * (97/100) - trS u)` is the obstruction to the `A` branch of
the trace of the cutting plane leaving the `RefuteDrop` box through one of the two `y`-faces: it is
`≤ 0` exactly where the `y`-coordinate of the `A` branch lies inside the box.

On the arc `[ang (5/2), π]` of the longitude circle the sign of `trN1` changes (from `+` to `-`),
so `psiA1 = max (3 * trN1 - yclip * (2c - trS), -3 * trN1 - yclip * (2c - trS))` there; the second
of the two functions is the one that governs the far half of the arc, and this file proves that it
is strictly increasing:

`StrictMonoOn (fun u => -3 * trN1 u - yclip * (2 * (97/100) - trS u)) (Icc (ang (5/2)) π)`.

The proof differentiates,

`F'(u) = -3 * trN1'(u) - yclip * (2c - trS u)' = 3 * (7761 sin u - 9814 cos u)/10000 + yclip * 3 A(u) A'(u)/S(u)`,

and bounds the two summands.  On the whole interval `cos u ≤ cos (ang (5/2)) = -21/29` and
`sin u ≥ 0`, so the first summand is at least `3 * (4907/5000) * (21/29) = 309141/145000 ≈ 2.132`;
the second is at least `-yclip * 3 * ((2/5) * (2/5)) / (68/100) = -yclip * 12/17 ≥ -(1764/1000) *
(12/17) ≈ -1.245`, since `|A|, |A'| ≤ 2/5`, `trS ≥ 68/100` and `yclip = (7/5) * 2^{1/3} ≤ 1764/1000`.
The total is `> 0.88 > 0`, so `F` is strictly increasing on the interval.
-/

namespace Work.RefuteDrop

open Work.BoxShrink.PinchOff.RefuteDrop
open Set

noncomputable section

/-! ## The closed form and the derivative of `trN1` -/

/-- `trN1 u = (7761/10000) cos u + (4907/5000) sin u`. -/
lemma psiA1h_trN1_closed (u : ℝ) :
    trN1 u = (7761/10000) * Real.cos u + (4907/5000) * Real.sin u := by
  simp only [trN1, trB1, trA]; ring

/-- The derivative of `trA`. -/
def psiA1h_dA (u : ℝ) : ℝ := (2/25) * Real.sin u - (39/100) * Real.cos u

lemma psiA1h_continuous_trN1 : Continuous trN1 := by
  have h : trN1 = fun u : ℝ => (7761/10000) * Real.cos u + (4907/5000) * Real.sin u :=
    funext psiA1h_trN1_closed
  rw [h]; fun_prop

lemma psiA1h_hasDerivAt_trN1 (x : ℝ) :
    HasDerivAt trN1 (-(7761/10000) * Real.sin x + (4907/5000) * Real.cos x) x := by
  have hfun : trN1 = (fun u : ℝ => (7761/10000) * Real.cos u)
      + (fun u : ℝ => (4907/5000) * Real.sin u) := by
    funext u; simp only [Pi.add_apply, psiA1h_trN1_closed]
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => (7761/10000) * Real.cos u)
      ((7761/10000) * (-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul (7761/10000 : ℝ)
  have h2 : HasDerivAt (fun u : ℝ => (4907/5000) * Real.sin u)
      ((4907/5000) * Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul (4907/5000 : ℝ)
  have h3 := h1.add h2
  have hval : ((7761/10000) * (-Real.sin x) + (4907/5000) * Real.cos x)
      = -(7761/10000) * Real.sin x + (4907/5000) * Real.cos x := by ring
  rw [hval] at h3
  exact h3

lemma psiA1h_hasDerivAt_trA (x : ℝ) : HasDerivAt trA (psiA1h_dA x) x := by
  have hfun : trA = (fun u : ℝ => (-(2/25)) * Real.cos u)
      + (fun u : ℝ => (-(39/100)) * Real.sin u) := by
    funext u; simp only [Pi.add_apply, trA]; ring
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => (-(2/25)) * Real.cos u) ((-(2/25)) * (-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul (-(2/25) : ℝ)
  have h2 : HasDerivAt (fun u : ℝ => (-(39/100)) * Real.sin u) ((-(39/100)) * Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul (-(39/100) : ℝ)
  have h3 := h1.add h2
  have hval : ((-(2/25)) * (-Real.sin x) + (-(39/100)) * Real.cos x) = psiA1h_dA x := by
    simp only [psiA1h_dA]; ring
  rw [hval] at h3
  exact h3

lemma psiA1h_hasDerivAt_trS (x : ℝ) :
    HasDerivAt trS (-(3 * trA x * psiA1h_dA x / trS x)) x := by
  have hA := psiA1h_hasDerivAt_trA x
  have hpow : HasDerivAt (fun u => (trA u)^2) (2 * trA x * psiA1h_dA x) x := by
    have h := hA.pow 2
    have h3 : HasDerivAt (fun u => trA u ^ 2) (2 * trA x ^ (2-1) * psiA1h_dA x) x := h
    have hval : (2 * trA x ^ (2-1) * psiA1h_dA x) = 2 * trA x * psiA1h_dA x := by norm_num
    rw [hval] at h3
    exact h3
  have h3 : HasDerivAt (fun u => 3 * (trA u)^2) (3 * (2 * trA x * psiA1h_dA x)) x :=
    hpow.const_mul 3
  have h4 : HasDerivAt (fun u => (97/100:ℝ)^2 - 3 * (trA u)^2)
      (-(3 * (2 * trA x * psiA1h_dA x))) x :=
    h3.const_sub ((97/100:ℝ)^2)
  have h5 : trS = fun u : ℝ => Real.sqrt ((97/100)^2 - 3 * (trA u)^2) := rfl
  rw [h5]
  have h6 := h4.sqrt (ne_of_gt (trS_arg_pos x))
  have hv : (-(3 * (2 * trA x * psiA1h_dA x))) / (2 * Real.sqrt ((97/100)^2 - 3 * (trA x)^2))
      = -(3 * trA x * psiA1h_dA x / trS x) := by
    rw [show Real.sqrt ((97/100:ℝ)^2 - 3 * (trA x)^2) = trS x from rfl]
    field_simp
  rw [hv] at h6
  exact h6

/-- The derivative of the target function. -/
lemma psiA1h_deriv_eq (x : ℝ) :
    deriv (fun u : ℝ => -3 * trN1 u - yclip * (2*(97/100) - trS u)) x
      = -3 * (-(7761/10000) * Real.sin x + (4907/5000) * Real.cos x)
        + yclip * (-(3 * trA x * psiA1h_dA x / trS x)) := by
  have h1 : HasDerivAt (fun u : ℝ => -3 * trN1 u)
      (-3 * (-(7761/10000) * Real.sin x + (4907/5000) * Real.cos x)) x :=
    (psiA1h_hasDerivAt_trN1 x).const_mul (-3)
  have h2 : HasDerivAt (fun u : ℝ => yclip * (2*(97/100) - trS u))
      (yclip * (0 - (-(3 * trA x * psiA1h_dA x / trS x)))) x :=
    ((hasDerivAt_const x (2*(97/100))).sub (psiA1h_hasDerivAt_trS x)).const_mul yclip
  have h := h1.sub h2
  have hval : (-3 * (-(7761/10000) * Real.sin x + (4907/5000) * Real.cos x)
      - yclip * (0 - (-(3 * trA x * psiA1h_dA x / trS x))))
      = -3 * (-(7761/10000) * Real.sin x + (4907/5000) * Real.cos x)
        + yclip * (-(3 * trA x * psiA1h_dA x / trS x)) := by ring
  rw [hval] at h
  exact h.deriv

/-! ## Elementary bounds -/

/-- `yclip = (7/5) * 2^{1/3} ≤ 1764/1000`. -/
lemma psiA1h_yclip_upper : yclip ≤ (1764/1000 : ℝ) := by
  have h3 : (2:ℝ) ≤ (126/100 : ℝ) ^ ((3:ℕ):ℝ) := by
    rw [Real.rpow_natCast]; norm_num
  have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 2) h3 (by norm_num : (0:ℝ) ≤ (1/3:ℝ))
  have h2 : ((126/100 : ℝ) ^ ((3:ℕ):ℝ)) ^ (1/3:ℝ) = 126/100 := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (126/100:ℝ))]
    norm_num
  rw [h2] at h
  simp only [yclip]
  nlinarith [h]

/-- `|A(u)| ≤ 2/5`. -/
lemma psiA1h_trA_abs_le (u : ℝ) : |trA u| ≤ 2/5 := by
  have h : (trA u)^2 ≤ (317/2000 : ℝ) := trA_sq_le u
  have h2 : (trA u)^2 ≤ (2/5:ℝ)^2 := by norm_num at h ⊢; linarith
  calc |trA u| = Real.sqrt ((trA u)^2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((2/5:ℝ)^2) := Real.sqrt_le_sqrt h2
    _ = 2/5 := Real.sqrt_sq (by norm_num)

/-- `|A'(u)| ≤ 2/5`. -/
lemma psiA1h_dA_abs_le (u : ℝ) : |psiA1h_dA u| ≤ 2/5 := by
  have h1 : Real.cos u ^ 2 + Real.sin u ^ 2 = 1 := Real.cos_sq_add_sin_sq u
  have key : (psiA1h_dA u)^2
      + ((2/25) * Real.cos u + (39/100) * Real.sin u)^2 = ((2/25:ℝ)^2 + (39/100)^2) := by
    simp only [psiA1h_dA]
    nlinarith [h1]
  have h3 : (psiA1h_dA u)^2 ≤ (317/2000 : ℝ) := by
    have h4 := sq_nonneg ((2/25) * Real.cos u + (39/100) * Real.sin u)
    have h5 : ((2/25:ℝ)^2 + (39/100)^2) = 317/2000 := by norm_num
    linarith [key, h4, h5.le, h5.ge]
  have h2 : (psiA1h_dA u)^2 ≤ (2/5:ℝ)^2 := by norm_num at h3 ⊢; linarith
  calc |psiA1h_dA u| = Real.sqrt ((psiA1h_dA u)^2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((2/5:ℝ)^2) := Real.sqrt_le_sqrt h2
    _ = 2/5 := Real.sqrt_sq (by norm_num)

/-- `S(u) = trS u ≥ 68/100`. -/
lemma psiA1h_trS_ge (u : ℝ) : (68/100:ℝ) ≤ trS u := by
  have h := trS_sq u
  have hA := trA_sq_le u
  have hnn := trS_nonneg u
  have h2 : ((68/100:ℝ))^2 ≤ trS u ^ 2 := by norm_num at h hA ⊢; nlinarith
  calc (68/100:ℝ) = Real.sqrt ((68/100:ℝ)^2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (trS u ^ 2) := Real.sqrt_le_sqrt h2
    _ = trS u := Real.sqrt_sq hnn

/-! ## The trigonometric bounds on the interval -/

/-- `cos u ≤ cos (ang (5/2)) = -21/29` on `[ang (5/2), π]`. -/
lemma psiA1h_cos_le {x : ℝ} (hx : x ∈ Ioo (ang (5/2)) Real.pi) : Real.cos x ≤ -(21/29) := by
  have hb : ang (5/2) ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨le_of_lt (ang_pos (by norm_num)), le_of_lt (ang_lt_pi (by norm_num))⟩
  have hu : x ∈ Set.Icc (0:ℝ) Real.pi := ⟨le_trans hb.1 (le_of_lt hx.1), le_of_lt hx.2⟩
  have hle : Real.cos x ≤ Real.cos (ang (5/2)) :=
    (Real.strictAntiOn_cos.le_iff_ge hu hb).mpr (le_of_lt hx.1)
  rw [cos_ang] at hle
  norm_num at hle
  linarith [hle]

/-- `0 ≤ sin u` on `[ang (5/2), π]`. -/
lemma psiA1h_sin_nonneg {x : ℝ} (hx : x ∈ Ioo (ang (5/2)) Real.pi) : 0 ≤ Real.sin x := by
  have hb : ang (5/2) ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨le_of_lt (ang_pos (by norm_num)), le_of_lt (ang_lt_pi (by norm_num))⟩
  have hu : x ∈ Set.Icc (0:ℝ) Real.pi := ⟨le_trans hb.1 (le_of_lt hx.1), le_of_lt hx.2⟩
  exact Real.sin_nonneg_of_mem_Icc hu

/-! ## Positivity of the derivative -/

lemma psiA1h_deriv_pos {x : ℝ} (hx : x ∈ Ioo (ang (5/2)) Real.pi) :
    0 < -3 * (-(7761/10000) * Real.sin x + (4907/5000) * Real.cos x)
      + yclip * (-(3 * trA x * psiA1h_dA x / trS x)) := by
  have hcos := psiA1h_cos_le hx
  have hsin := psiA1h_sin_nonneg hx
  have hA := psiA1h_trA_abs_le x
  have hdA := psiA1h_dA_abs_le x
  have hS := psiA1h_trS_ge x
  have hSpos : 0 < trS x := lt_of_lt_of_le (by norm_num) hS
  have hyc : yclip ≤ 1764/1000 := psiA1h_yclip_upper
  have hy0 : 0 ≤ yclip := le_trans (by norm_num) (le_of_lt yclip_lower)
  have hT1 : (309141/145000 : ℝ) ≤
      -3 * (-(7761/10000) * Real.sin x + (4907/5000) * Real.cos x) := by
    nlinarith [hsin, hcos]
  have hb1 : |3 * trA x * psiA1h_dA x / trS x| ≤ 12/17 := by
    have h1 : |3 * trA x * psiA1h_dA x| ≤ 12/25 := by
      have h3 : |3 * trA x * psiA1h_dA x| = 3 * |trA x| * |psiA1h_dA x| := by
        rw [abs_mul, abs_mul]; norm_num
      rw [h3]
      have hm := mul_le_mul hA hdA (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2/5)
      nlinarith [hm]
    rw [abs_div, abs_of_pos hSpos]
    calc |3 * trA x * psiA1h_dA x| / trS x ≤ (12/25) / (68/100) :=
          div_le_div₀ (by norm_num : (0:ℝ) ≤ 12/25) h1 (by norm_num : (0:ℝ) < 68/100) hS
      _ = 12/17 := by norm_num
  have hz : 3 * trA x * psiA1h_dA x / trS x ≤ 12/17 := (abs_le.mp hb1).2
  have hneg : -(12/17) ≤ -(3 * trA x * psiA1h_dA x / trS x) := by linarith
  have hyc' : yclip * (-(12/17)) ≤ yclip * (-(3 * trA x * psiA1h_dA x / trS x)) :=
    mul_le_mul_of_nonneg_left hneg hy0
  have hT2 : -(1764/1000) * (12/17) ≤ yclip * (-(3 * trA x * psiA1h_dA x / trS x)) := by
    have : -(1764/1000) * (12/17) ≤ yclip * (-(12/17)) := by nlinarith [hyc, hy0]
    linarith [hyc', this]
  have hfin : (0:ℝ) < 309141/145000 - 1764/1000 * (12/17) := by norm_num
  linarith [hT1, hT2, hfin]

theorem psiA1_hMono :
    StrictMonoOn (fun u : ℝ => -3 * Work.BoxShrink.PinchOff.RefuteDrop.trN1 u - Work.BoxShrink.PinchOff.RefuteDrop.yclip * (2 * (97/100) - Work.BoxShrink.PinchOff.RefuteDrop.trS u))
      (Set.Icc (Work.BoxShrink.PinchOff.RefuteDrop.ang (5/2)) Real.pi) := by
  have hcont : ContinuousOn (fun u : ℝ => -3 * trN1 u - yclip * (2 * (97/100) - trS u))
      (Set.Icc (ang (5/2)) Real.pi) := by
    refine Continuous.continuousOn ?_
    have h1 : Continuous trN1 := psiA1h_continuous_trN1
    have h2 : Continuous trS := continuous_trS
    fun_prop
  refine strictMonoOn_of_deriv_pos (convex_Icc (ang (5/2)) Real.pi) hcont ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [psiA1h_deriv_eq x]
  exact psiA1h_deriv_pos hx

end

end Work.RefuteDrop
