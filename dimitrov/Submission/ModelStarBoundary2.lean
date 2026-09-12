import Mathlib
import Submission.ModelStarMap
import Submission.ModelStarBoundary

noncomputable section
open scoped Real BigOperators Topology
open Filter Set Complex
open Submission.ModelStarMap
open Submission.ModelStarBoundary

/-!
# ModelStarBoundary2 -- per-arc ray identity of the model boundary
# (milestone (a) part 3, stage 2: PROVED)

STATUS: verified research-isolate milestone; 0 sorries; axiom-clean
[propext, Classical.choice, Quot.sound] (all declarations incl.
`modelF_boundary_ray`, `theta_prefix_form`); does NOT import
`Submission.lean` (unimported module).  Builds on Submission.ModelStarMap
(norm/boundary identities of `F`), Submission.ModelStarBoundary (half-angle
arg sub-lemmas) and the commons lemma `cpow_real_eq_norm_rpow_mul_exp`.

THEOREM (`modelF_boundary_ray`, the stage-2 core): for the model map
`F(z) = z·∏_k (1 − z₀ k·z^{-1})^(2 r k)` with junctions `z₀ k = e^{i φ k}`,
`φ k ∈ [0, 2π)`, `Σ r k = 1`, at every circle point `z = e^{it}` away from
the junctions (`t ∈ (0, 2π)`, `φ k ≠ t` for all k):

    F(e^{it}) = ρ(t)·e^{i Θ(t)},   ρ(t) := ∏_k ‖1 − e^{i(φ k − t)}‖^{2 r k} ≥ 0,
    Θ(t) := Σ r k·(φ k + π·s k),   s k := dirSign φ t k (= +1 if φ k < t else −1).

i.e. each non-junction boundary value lies on the ray of direction Θ(t).
The proof: each factor `(1 − z₀k·z^{-1})^{2rk}` splits (cpow_real_eq_norm_
rpow_mul_exp + the branch arg lemmas of ModelStarBoundary) into a positive
real modulus `‖1 − e^{i(φk−t)}‖^{2rk}` times `e^{2i·r k·(branch angle)}`;
the branch angle is `(φ k − t)/2 ± π/2` with the sign `± = −dirSign`; the
`t`-terms cancel against `arg z = t` exactly because `Σ r k = 1`
(`theta_real`), leaving `Θ(t)`.

`theta_prefix_form` records the cumulative form of the direction on an arc
whose "passed junctions" are exactly `{k ≤ j}`:
`Θ = Σ r k·φ k + π·(2·Σ_{k ≤ j} r k − 1)`  (CORRECT sign; the §36 handoff
formula `Σ r k·φ k + π − 2π·Σ_{k ≤ j} r k` was wrong -- see STATUS §37).

REMARKS: (1) `dirSign`/`s k = +1` exactly when `φ k < t`, which on a sorted
arc is `k ≤ j`; on the arc the direction is constant in `t`.  (2) The next
milestone (stage 3) is: continuity of `t ↦ F(e^{it})` on the closed arc +
`‖F(e^{it})‖ → 0` at the junctions, so the arc sweeps the segment
`[0, m_j·e^{i Θ_j}]`, `m_j := sup over the arc of ρ(t)`; then the image of
the circle is the `s`-spike star `⋃_j [0, m_j·e^{i Θ_j}]` and (with the KL
bridge `ModelStar.max_product_ge_four_rpow_inv`) a capacity-1 model star
has a spike of length ≥ 4^{1/s} -- the EASY half of Eremenko's equivalence
(Dubinin ⟹ KL); the GATE (`Step3.sym_maximality`) still needs the forward
converse (E1-E5).
-/

namespace Submission.ModelStarBoundary2

/-- `1 − exp(x·I) ≠ 0` for `x ∈ (−2π, 2π)`, `x ≠ 0` (exact half-angle
forms, both branches). -/
lemma one_sub_exp_mul_I_ne_zero_of_Ioo {x : ℝ} (hxlo : -2 * Real.pi < x)
    (hxhi : x < 2 * Real.pi) (hx0 : x ≠ 0) :
    1 - Complex.exp (x * Complex.I) ≠ 0 := by
  rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
  · have hsin : Real.sin (x / 2) < 0 := by
      exact Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [hxlo])
    have hsneg : 0 < -Real.sin (x / 2) := by linarith
    have hdec := one_sub_exp_mul_I x
    intro h0
    have harr : 1 - Complex.exp (x * Complex.I) =
        (2 * (-(Real.sin (x / 2)) : ℂ)) *
          (Complex.I * Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I)) := by
      rw [hdec]
      ring
    have hz : (2 * (-(Real.sin (x / 2)) : ℂ)) *
          (Complex.I * Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I)) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast (ne_of_gt hsneg)))
        (mul_ne_zero (by simp) (Complex.exp_ne_zero _))
    rw [harr] at h0
    exact hz h0
  · have hsin : 0 < Real.sin (x / 2) := by
      exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [hxhi])
    have hdec := one_sub_exp_mul_I x
    intro h0
    have harr : 1 - Complex.exp (x * Complex.I) =
        (2 * (Real.sin (x / 2) : ℂ)) *
          ((-Complex.I) * Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I)) := by
      rw [hdec]
      ring
    have hz : (2 * (Real.sin (x / 2) : ℂ)) *
          ((-Complex.I) * Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I)) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast (ne_of_gt hsin)))
        (mul_ne_zero (by simp) (Complex.exp_ne_zero _))
    rw [harr] at h0
    exact hz h0

/-- Sign of `φ k − t`: `+1` when `φ k < t` (negative branch of the
factor argument), `−1` otherwise (positive branch). -/
def dirSign {s : ℕ} (φ : Fin s → ℝ) (t : ℝ) (k : Fin s) : ℝ :=
  if φ k < t then 1 else -1

/-- Canonical unit-circle exponential of a real angle. -/
abbrev eAngle (x : ℝ) : ℂ := Complex.exp (((x : ℝ) : ℂ) * Complex.I)

/-- `1 − z₀·z^{-1} = 1 − exp((φ−t)·I)` when `z₀ = exp(φ·I)` and
`z = exp(t·I)`. -/
lemma factor_base_eq {s : ℕ} (z₀ : Fin s → ℂ) (φ : Fin s → ℝ)
    (hz₀ : ∀ k, z₀ k = Complex.exp (φ k * Complex.I)) {t : ℝ} (k : Fin s) :
    1 - z₀ k * (Complex.exp (t * Complex.I))⁻¹ = 1 - eAngle (φ k - t) := by
  have hzinv : (Complex.exp (t * Complex.I))⁻¹ = Complex.exp ((-t) * Complex.I) := by
    rw [← Complex.exp_neg]
    congr 1
    ring
  rw [hz₀ k, hzinv]
  congr 1
  rw [← Complex.exp_add]
  apply congrArg Complex.exp
  push_cast
  ring

/-- `1 − exp((φ k − t)·I) ≠ 0` on the arc interior (φ k ∈ [0, 2π),
`t ∈ (0, 2π)`, `φ k ≠ t`). -/
lemma factor_base_ne_zero {s : ℕ} (φ : Fin s → ℝ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2 * Real.pi) (htne : ∀ k, φ k ≠ t) (k : Fin s) :
    1 - eAngle (φ k - t) ≠ 0 := by
  have h1 : -2 * Real.pi < φ k - t := by linarith [hφlo k, ht2]
  have h2 : φ k - t < 2 * Real.pi := by linarith [hφhi k, ht0]
  exact one_sub_exp_mul_I_ne_zero_of_Ioo (x := φ k - t) h1 h2 (sub_ne_zero.mpr (htne k))

/-- Principal argument of the factor on the arc interior, both branches:
`arg (1 − exp((φ−t)·I)) = (φ−t)/2 + (π/2)·sgn(φ−t)` with `sgn = +1` if
`φ < t` (negative half-angle branch) and `−1` if `t < φ`. -/
lemma factor_arg {s : ℕ} (φ : Fin s → ℝ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2 * Real.pi) (htne : ∀ k, φ k ≠ t) (k : Fin s) :
    (1 - eAngle (φ k - t)).arg =
      (φ k - t) / 2 + Real.pi / 2 * dirSign φ t k := by
  by_cases hlt : φ k < t
  · have hθ0 : φ k - t < 0 := by linarith
    have hθm : -2 * Real.pi < φ k - t := by linarith [hφlo k, ht2]
    have harg := arg_one_sub_exp_mul_I_neg (θ := φ k - t) hθm hθ0
    rw [harg]
    rw [dirSign, if_pos hlt]
    ring
  · have htlt : t < φ k := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm (htne k))
    have hθ0 : 0 < φ k - t := by linarith
    have hθ2 : φ k - t < 2 * Real.pi := by linarith [hφhi k, ht0]
    have harg := arg_one_sub_exp_mul_I_pos (θ := φ k - t) hθ0 hθ2
    rw [harg]
    rw [dirSign, if_neg hlt]
    ring




/-- `w ^ (c : ℂ) = ‖w‖^c · exp((c · arg w)·I)` for real exponent `c` and
`w ≠ 0` (arg in the principal branch). -/
lemma cpow_real_eq_norm_rpow_mul_exp {w : ℂ} {c : ℝ} (hw : w ≠ 0) :
    w ^ (c : ℂ) = (Real.rpow ‖w‖ c : ℂ) * Complex.exp ((c * w.arg) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero hw]
  have hnpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hmain : Real.exp (Real.log ‖w‖ * c) = Real.rpow ‖w‖ c := by
    rw [← Real.rpow_def_of_pos hnpos]
    rfl
  have hA : Complex.log w * (c : ℂ) =
      ((Real.log ‖w‖ * c : ℝ) : ℂ) + ((c * w.arg : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im] <;> ring
  rw [hA, Complex.exp_add]
  rw [← Complex.ofReal_exp]
  rw [hmain]
  congr 1
  congr 1
  rw [ofReal_mul]

/-- Per-factor power expansion on the arc interior: each model factor is a
positive-real multiple of `exp((2 r k · branch angle)·I)`. -/
lemma factor_power {s : ℕ} (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (φ : Fin s → ℝ)
    (hz₀ : ∀ k, z₀ k = Complex.exp (φ k * Complex.I))
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2 * Real.pi) (htne : ∀ k, φ k ≠ t) (k : Fin s) :
    (1 - z₀ k * (Complex.exp (t * Complex.I))⁻¹) ^ ((2 * r k : ℝ) : ℂ) =
      (Real.rpow ‖1 - eAngle (φ k - t)‖ (2 * r k) : ℂ) *
        eAngle (2 * r k * ((φ k - t) / 2 + Real.pi / 2 * dirSign φ t k)) := by
  rw [factor_base_eq z₀ φ hz₀ (t := t) k]
  have hp := cpow_real_eq_norm_rpow_mul_exp (w := 1 - eAngle (φ k - t))
    (c := 2 * r k)
    (factor_base_ne_zero φ hφlo hφhi (t := t) ht0 ht2 htne k)
  rw [factor_arg φ hφlo hφhi (t := t) ht0 ht2 htne k] at hp
  -- hp : (1 − eAngle θ)^(c:ℂ) = (rpow ‖·‖ c : ℂ) * exp((c * (θ/2 + π/2 s)) * I)
  -- need: exp((c * a) * I) = eAngle (c * a)  (definitions up to coercion); close by rfl after dsimp [eAngle]
  simpa [eAngle, mul_assoc] using hp

lemma theta_real {s : ℕ} (r : Fin s → ℝ) (φ : Fin s → ℝ) {t : ℝ}
    (hsum : (∑ k : Fin s, r k) = 1) :
    t + (∑ k : Fin s, (2 * r k * ((φ k - t) / 2 + Real.pi / 2 * dirSign φ t k))) =
      ∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k)) := by
  have hpoint : ∀ k : Fin s,
      2 * r k * ((φ k - t) / 2 + Real.pi / 2 * dirSign φ t k) =
        r k * (φ k - t) + Real.pi * (r k * dirSign φ t k) := by
    intro k
    ring
  -- auxiliary: the factor-argument sum splits into the linear part and the
  -- signed-π part
  have hSplit : (∑ k : Fin s, (2 * r k * ((φ k - t) / 2 + Real.pi / 2 * dirSign φ t k))) =
      (∑ k : Fin s, r k * (φ k - t)) +
        Real.pi * (∑ k : Fin s, r k * dirSign φ t k) := by
    calc
      (∑ k : Fin s, (2 * r k * ((φ k - t) / 2 + Real.pi / 2 * dirSign φ t k)))
          = (∑ k : Fin s, (r k * (φ k - t) + Real.pi * (r k * dirSign φ t k))) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact hpoint k
      _ = (∑ k : Fin s, r k * (φ k - t)) +
            (∑ k : Fin s, Real.pi * (r k * dirSign φ t k)) := by
              rw [Finset.sum_add_distrib]
      _ = (∑ k : Fin s, r k * (φ k - t)) +
            Real.pi * (∑ k : Fin s, r k * dirSign φ t k) := by
              congr 1
              rw [← Finset.mul_sum]
  -- auxiliary: t + ∑ r k*(φ k − t) = ∑ r k*φ k
  have hCancel : t + (∑ k : Fin s, r k * (φ k - t)) = (∑ k : Fin s, r k * φ k) := by
    have hA : (∑ k : Fin s, r k * (φ k - t)) = (∑ k : Fin s, r k * φ k) - t := by
      calc
        (∑ k : Fin s, (r k * (φ k - t))) = (∑ k : Fin s, (r k * φ k - r k * t)) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = (∑ k : Fin s, r k * φ k) - (∑ k : Fin s, r k * t) := by
          rw [Finset.sum_sub_distrib]
        _ = (∑ k : Fin s, r k * φ k) - t := by
          have hB : (∑ k : Fin s, r k * t) = t := by
            rw [← Finset.sum_mul, hsum]
            ring
          rw [hB]
    rw [hA]
    ring
  -- auxiliary: ∑ rkφk + π∑ rk s = ∑ rk(φk + π s)
  have hTheta : (∑ k : Fin s, r k * φ k) +
        Real.pi * (∑ k : Fin s, r k * dirSign φ t k) =
      ∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k)) := by
    symm
    calc
      (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k)))
          = (∑ k : Fin s, (r k * φ k + r k * (Real.pi * dirSign φ t k))) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = (∑ k : Fin s, r k * φ k) +
            (∑ k : Fin s, r k * (Real.pi * dirSign φ t k)) := by
              rw [Finset.sum_add_distrib]
      _ = (∑ k : Fin s, r k * φ k) +
            (∑ k : Fin s, Real.pi * (r k * dirSign φ t k)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = (∑ k : Fin s, r k * φ k) +
            Real.pi * (∑ k : Fin s, r k * dirSign φ t k) := by
              congr 1
              rw [← Finset.mul_sum]
  calc
    t + (∑ k : Fin s, (2 * r k * ((φ k - t) / 2 + Real.pi / 2 * dirSign φ t k)))
        = t + ((∑ k : Fin s, r k * (φ k - t)) +
            Real.pi * (∑ k : Fin s, r k * dirSign φ t k)) := by
              rw [hSplit]
    _ = (t + (∑ k : Fin s, r k * (φ k - t))) +
          Real.pi * (∑ k : Fin s, r k * dirSign φ t k) := by
              rw [add_assoc]
    _ = (∑ k : Fin s, r k * φ k) +
          Real.pi * (∑ k : Fin s, r k * dirSign φ t k) := by
              rw [hCancel]
    _ = ∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k)) := hTheta



/-- **Per-arc ray identity (model boundary, stage 2).**  With junctions
`z₀ k = e^{i φ k}`, `φ k ∈ [0, 2π)`, and `Σ r k = 1`, at every point
`z = e^{it}` of the open circle away from the junctions (`t ∈ (0, 2π)`,
`φ k ≠ t` for all k) the model boundary value lies on the ray of direction
`Θ(t) := Σ r k·(φ k + π·s k)` (`s k = +1` if `φ k < t`, else `−1`), i.e.
`F(e^{it}) = ρ(t)·e^{i Θ(t)}` with the nonnegative real factor
`ρ(t) := ∏_k ‖1 − e^{i(φ k − t)}‖^{2 r k}`. -/
theorem modelF_boundary_ray {s : ℕ} (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (φ : Fin s → ℝ)
    (hz₀ : ∀ k, z₀ k = Complex.exp (φ k * Complex.I))
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1)
    {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2 * Real.pi) (htne : ∀ k, φ k ≠ t) :
    ModelStarMap.modelF z₀ r (Complex.exp (t * Complex.I)) =
      (((∏ k : Fin s, ‖1 - eAngle (φ k - t)‖ ^ (2 * r k)) : ℝ) : ℂ) *
        eAngle (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k))) := by
  let c (k : Fin s) : ℝ := 2 * r k * ((φ k - t) / 2 + Real.pi / 2 * dirSign φ t k)
  let rho : ℝ := ∏ k : Fin s, ‖1 - eAngle (φ k - t)‖ ^ (2 * r k)
  let Th : ℝ := ∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k))
  change ModelStarMap.modelF z₀ r (Complex.exp (t * Complex.I)) = (rho : ℂ) * eAngle Th
  have hfacEq : (∏ k : Fin s,
        (1 - z₀ k * (Complex.exp (t * Complex.I))⁻¹) ^ ((2 * r k : ℝ) : ℂ)) =
      (∏ k : Fin s,
        (Real.rpow ‖1 - eAngle (φ k - t)‖ (2 * r k) : ℂ) * eAngle (c k)) := by
    exact Finset.prod_congr rfl (fun k hk =>
      factor_power z₀ r φ hz₀ hφlo hφhi (t := t) ht0 ht2 htne k)
  have hNorm : (∏ k : Fin s, (Real.rpow ‖1 - eAngle (φ k - t)‖ (2 * r k) : ℂ)) = (rho : ℂ) := by
    dsimp [rho]
    rw [← Complex.ofReal_prod]
  have hProdExp : (∏ k : Fin s, eAngle (c k)) = eAngle (∑ k : Fin s, c k) := by
    dsimp [eAngle]
    rw [← Complex.exp_sum]
    congr 1
    rw [← Finset.sum_mul]
    congr 1
    rw [← Complex.ofReal_sum]
  have hComb : (Complex.exp (t * Complex.I)) * eAngle (∑ k : Fin s, c k) =
      eAngle (t + (∑ k : Fin s, c k)) := by
    dsimp [eAngle]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hTheta : t + (∑ k : Fin s, c k) = Th := by
    dsimp [c, Th]
    exact theta_real r φ (t := t) hsum
  unfold ModelStarMap.modelF ModelStarMap.modelProduct ModelStarMap.modelFactor
  rw [hfacEq]
  rw [Finset.prod_mul_distrib]
  rw [hNorm]
  rw [hProdExp]
  have hReassoc : (Complex.exp (t * Complex.I)) * ((rho : ℂ) * eAngle (∑ k : Fin s, c k)) =
      (rho : ℂ) * ((Complex.exp (t * Complex.I)) * eAngle (∑ k : Fin s, c k)) := by
    ring
  rw [hReassoc]
  rw [hComb]
  rw [hTheta]


/-- **Prefix (cumulative) form of the arc direction.**  On an arc on which
the set of junctions "passed" is exactly `{k | k ≤ j}` (i.e.
`φ k < t ⟺ k ≤ j`), the direction of the model boundary takes the
cumulative value `Σ r k·φ k + π·(2·Σ_{k ≤ j} r k − 1)` (Σ r k = 1). -/
lemma theta_prefix_form {s : ℕ} (r : Fin s → ℝ) (φ : Fin s → ℝ) {t : ℝ} {j : Fin s}
    (hsum : (∑ k : Fin s, r k) = 1)
    (hset : ∀ k : Fin s, (φ k < t ↔ k ≤ j)) :
    (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k))) =
      (∑ k : Fin s, r k * φ k) +
        Real.pi * (2 * (∑ k ∈ Finset.univ.filter (fun k : Fin s => k ≤ j), r k) - 1) := by
  have hsign : ∀ k : Fin s, dirSign φ t k = if k ≤ j then 1 else -1 := by
    intro k
    unfold dirSign
    by_cases hk : k ≤ j
    · have hφ : φ k < t := (hset k).2 hk
      rw [if_pos hφ, if_pos hk]
    · have hφ : ¬ φ k < t := fun h => hk ((hset k).1 h)
      rw [if_neg hφ, if_neg hk]
  have hPrefix : (∑ k : Fin s, r k * (if k ≤ j then 1 else 0)) =
      (∑ k ∈ Finset.univ.filter (fun k : Fin s => k ≤ j), r k) := by
    calc
      (∑ k : Fin s, r k * (if k ≤ j then 1 else 0))
          = (∑ k : Fin s, if k ≤ j then r k else 0) := by
              apply Finset.sum_congr rfl
              intro k hk
              by_cases h : k ≤ j <;> simp [h]
      _ = (∑ k ∈ Finset.univ.filter (fun k : Fin s => k ≤ j), r k) := by
              rw [← Finset.sum_filter (p := fun k : Fin s => k ≤ j) (f := fun k => r k)]
  have hMain : (∑ k : Fin s, r k * dirSign φ t k) =
      2 * (∑ k ∈ Finset.univ.filter (fun k : Fin s => k ≤ j), r k) - 1 := by
    calc
      (∑ k : Fin s, r k * dirSign φ t k)
          = (∑ k : Fin s, (2 * (r k * (if k ≤ j then 1 else 0)) - r k)) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hsign k]
              by_cases h : k ≤ j <;> simp [h] <;> ring
      _ = 2 * (∑ k : Fin s, r k * (if k ≤ j then 1 else 0)) - (∑ k : Fin s, r k) := by
              rw [Finset.sum_sub_distrib]
              congr 1
              rw [← Finset.mul_sum]
      _ = 2 * (∑ k ∈ Finset.univ.filter (fun k : Fin s => k ≤ j), r k) - (∑ k : Fin s, r k) := by
              rw [hPrefix]
      _ = 2 * (∑ k ∈ Finset.univ.filter (fun k : Fin s => k ≤ j), r k) - 1 := by
              rw [hsum]
  calc
    (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k)))
        = (∑ k : Fin s, (r k * φ k + r k * (Real.pi * dirSign φ t k))) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
    _ = (∑ k : Fin s, r k * φ k) + (∑ k : Fin s, r k * (Real.pi * dirSign φ t k)) := by
            rw [Finset.sum_add_distrib]
    _ = (∑ k : Fin s, r k * φ k) + Real.pi * (∑ k : Fin s, r k * dirSign φ t k) := by
            have hPi : (∑ k : Fin s, r k * (Real.pi * dirSign φ t k)) =
                Real.pi * (∑ k : Fin s, r k * dirSign φ t k) := by
              calc
                (∑ k : Fin s, r k * (Real.pi * dirSign φ t k))
                    = (∑ k : Fin s, Real.pi * (r k * dirSign φ t k)) := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        ring
                _ = Real.pi * (∑ k : Fin s, r k * dirSign φ t k) := by
                        rw [← Finset.mul_sum]
            rw [hPi]
    _ = (∑ k : Fin s, r k * φ k) + Real.pi * (2 * (∑ k ∈ Finset.univ.filter (fun k : Fin s => k ≤ j), r k) - 1) := by
            rw [hMain]
end Submission.ModelStarBoundary2
