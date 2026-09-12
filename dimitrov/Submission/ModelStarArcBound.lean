import Mathlib
import Submission.ModelStarImageSeg
import Submission.Commons.Analysis.SpecialFunctions.sin_pow_mul_sin_pow_le

/-!
# ModelStarArcBound -- the per-arc tip bound of a model star

STATUS: research isolate (NOT imported by `Submission.lean`); every declaration
axiom-clean.

SETTING.  For the model map `F = modelF z₀ r` with junctions
`z₀ k = eAngle (φ k)`, weights `r k ≥ 0`, `Σ r k = 1`, and `φ` monotone with
values in `[0, 2π)`, the circle is cut by the junctions into arcs; the `j`-th arc
runs from the junction angle `a := φ j` to `b := nextJunction φ j`, and the tip
of the arc is the supremum of the sweep factor `rho φ r` over the arc.

MAIN RESULTS.
  * `rho_arc_le` (the raw per-arc estimate): writing `u := (t - a)/2` and
    `v := (b - t)/2` for `t` on the arc, with `k ≠ j` an index whose junction
    `eAngle (φ k)` agrees with `eAngle b` (the wrap case has `φ k = b - 2π`),

        rho φ r t ≤ 4 · sin(u)^(2 r j) · sin(v)^(2 r k) ;

  * `rho_le_arc_balanced`: if the arc has length at most `π` then

        rho φ r t ≤ 4 · (r j/(r j + r k))^(r j) · (r k/(r j + r k))^(r k) ,

    the value that the ANTIPODAL two-junction star with the normalised adjacent
    weights attains (and which is `≥ 2` for all choices of the two weights, with
    equality exactly when `r j = r k`); this is the corrected quantitative form
    of the coalescence brick `ModelStarCoalesce.rho_le_gap_mul`;

  * `rho_le_arc_vanishing`: if the arc has length `2c ≤ π` then

        rho φ r t ≤ 4 · sin(c)^(2 (r j + r k)) ,

    which tends to `0` as the arc collapses.

The last two are the two ingredients the boundary analysis of the model-star
family needs (a uniform upper bound on a tip in terms of the adjacent weights,
and the vanishing of a tip when its arc collapses).
-/

noncomputable section

open scoped Real BigOperators Topology
open Set

namespace Submission.ModelStarArcBound

open Submission.ModelStarBoundary2 (eAngle)
open Submission.ModelStarBoundary3 (rho)

variable {s : ℕ}

/-! ## The index of the next junction -/

/-- The cyclically next junction index. -/
def nextIdx (s : ℕ) (hs : 0 < s) (j : Fin s) : Fin s :=
  if h : j.val + 1 < s then ⟨j.val + 1, h⟩ else ⟨0, hs⟩

lemma nextIdx_of_lt {hs : 0 < s} {j : Fin s} (h : j.val + 1 < s) :
    nextIdx s hs j = ⟨j.val + 1, h⟩ := dif_pos h

lemma nextIdx_of_not_lt {hs : 0 < s} {j : Fin s} (h : ¬ j.val + 1 < s) :
    nextIdx s hs j = ⟨0, hs⟩ := dif_neg h

/-- `eAngle` has period `2π`. -/
lemma eAngle_add_two_pi (x : ℝ) : eAngle (x + 2 * Real.pi) = eAngle x := by
  unfold Submission.ModelStarBoundary2.eAngle
  rw [show (((x + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
      = (x : ℂ) * Complex.I + (2 * Real.pi : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The `eAngle` of the next junction (with the wrap case `= nextJunction - 2π`). -/
lemma eAngle_phi_nextIdx (φ : Fin s → ℝ) (hs : 0 < s) (j : Fin s) :
    eAngle (φ (nextIdx s hs j))
      = eAngle (Submission.ModelStarImageSeg.nextJunction φ hs j) := by
  rcases lt_or_ge (j.val + 1) s with h | h
  · rw [nextIdx_of_lt h, Submission.ModelStarImageSeg.nextJunction_of_lt h]
  · have hnot : ¬ j.val + 1 < s := by omega
    rw [nextIdx_of_not_lt hnot, Submission.ModelStarImageSeg.nextJunction_of_not_lt hnot]
    exact (eAngle_add_two_pi (φ ⟨0, hs⟩)).symm

/-! ## The elementary geometry of a unit chord -/

/-- `‖1 - eAngle ψ‖ = 2 |sin (ψ/2)|`. -/
lemma norm_one_sub_eAngle_eq (ψ : ℝ) : ‖1 - eAngle ψ‖ = 2 * |Real.sin (ψ / 2)| := by
  have hc : (eAngle ψ).re = Real.cos ψ := by
    unfold Submission.ModelStarBoundary2.eAngle; exact Complex.exp_ofReal_mul_I_re ψ
  have hs : (eAngle ψ).im = Real.sin ψ := by
    unfold Submission.ModelStarBoundary2.eAngle; exact Complex.exp_ofReal_mul_I_im ψ
  have hz : Complex.normSq (1 - eAngle ψ) = 2 - 2 * Real.cos ψ := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hc, hs]
    have := Real.sin_sq_add_cos_sq ψ
    nlinarith [this]
  have hsq : ‖1 - eAngle ψ‖ ^ 2 = 4 * Real.sin (ψ / 2) ^ 2 := by
    rw [Complex.sq_norm, hz]
    have h1 := Real.cos_two_mul (ψ / 2)
    have h3 : Real.cos (2 * (ψ / 2)) = Real.cos ψ := by rw [show 2 * (ψ / 2) = ψ by ring]
    rw [h3] at h1
    have h2 := Real.sin_sq_add_cos_sq (ψ / 2)
    nlinarith [h1, h2]
  have hkey : (2 * |Real.sin (ψ / 2)|) ^ 2 = 4 * Real.sin (ψ / 2) ^ 2 := by
    rw [mul_pow, sq_abs]; ring
  rw [← hkey] at hsq
  have h2n : (0 : ℝ) ≤ 2 * |Real.sin (ψ / 2)| := by positivity
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have hnn : (0:ℝ) ≤ ‖1 - eAngle ψ‖ := norm_nonneg _
    linarith only [h, h2n, hnn]

/-- For `0 ≤ ψ ≤ 2π`, the chord length is `2 sin (ψ/2)`. -/
lemma norm_one_sub_eAngle_eq_two_sin {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ 2 * Real.pi) :
    ‖1 - eAngle ψ‖ = 2 * Real.sin (ψ / 2) := by
  rw [norm_one_sub_eAngle_eq, abs_of_nonneg]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)

/-- The chord in terms of the angle difference. -/
lemma norm_eAngle_sub_eq (t θ : ℝ) :
    ‖eAngle t - eAngle θ‖ = 2 * |Real.sin ((t - θ) / 2)| := by
  rw [Submission.ModelStarBoundary3.norm_eAngle_sub, norm_one_sub_eAngle_eq]
  congr 1
  rw [show (θ - t) / 2 = -((t - θ) / 2) by ring, Real.sin_neg, abs_neg]

/-! ## The per-arc estimate -/

open Submission.ModelStarImageSeg (nextJunction nextJunction_of_lt nextJunction_of_not_lt)

/-- `eAngle` is multiplicative. -/
lemma eAngle_add (a b : ℝ) : eAngle (a + b) = eAngle a * eAngle b := by
  unfold Submission.ModelStarBoundary2.eAngle
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The next junction angle is at most `2π` above `φ j` (monotone data). -/
lemma nextJunction_sub_le {φ : Fin s → ℝ} (hs : 0 < s) (hmono : Monotone φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφle : ∀ k, φ k ≤ 2 * Real.pi) (j : Fin s) :
    nextJunction φ hs j - φ j ≤ 2 * Real.pi := by
  rcases lt_or_ge (j.val + 1) s with h | h
  · rw [nextJunction_of_lt h]
    have h2 : φ ⟨j.val + 1, h⟩ ≤ 2 * Real.pi := hφle _
    have h3 : 0 ≤ φ j := hφlo _
    linarith only [h2, h3]
  · have hnot : ¬ j.val + 1 < s := by omega
    rw [nextJunction_of_not_lt hnot]
    have h1 : φ ⟨0, hs⟩ ≤ φ j := hmono (Fin.mk_le_mk.mpr (by omega))
    linarith only [h1]

/-- **The raw per-arc estimate.** -/
theorem rho_arc_le (hs : 0 < s) (φ r : Fin s → ℝ) {j k : Fin s}
    (hr : ∀ i, 0 ≤ r i) (hsum : (∑ i : Fin s, r i) = 1) (hkj : k ≠ j)
    (hmono : Monotone φ) (hφlo : ∀ i, 0 ≤ φ i) (hφle : ∀ i, φ i ≤ 2 * Real.pi)
    (hk : eAngle (φ k) = eAngle (nextJunction φ hs j))
    (t : ℝ) (ht : t ∈ Icc (φ j) (nextJunction φ hs j)) :
    rho φ r t ≤ 4 * Real.sin ((t - φ j) / 2) ^ (2 * r j)
      * Real.sin ((nextJunction φ hs j - t) / 2) ^ (2 * r k) := by
  set b : ℝ := nextJunction φ hs j with hb
  have hgap : b - φ j ≤ 2 * Real.pi := by
    rw [hb]; exact nextJunction_sub_le hs hmono hφlo hφle j
  have ht0 : φ j ≤ t := ht.1
  have ht1 : t ≤ b := ht.2
  have hu0 : 0 ≤ (t - φ j) / 2 := by linarith only [ht0]
  have hu1 : (t - φ j) / 2 ≤ Real.pi := by linarith only [hgap, ht0, ht1, Real.pi_pos]
  have hv0 : 0 ≤ (b - t) / 2 := by linarith only [ht1]
  have hv1 : (b - t) / 2 ≤ Real.pi := by linarith only [hgap, ht0, ht1, Real.pi_pos]
  have hsinu : 0 ≤ Real.sin ((t - φ j) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hu0 hu1
  have hsinv : 0 ≤ Real.sin ((b - t) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hv0 hv1
  have hfacj : ‖1 - eAngle (φ j - t)‖ = 2 * Real.sin ((t - φ j) / 2) := by
    rw [← Submission.ModelStarBoundary3.norm_eAngle_sub (t := t) (θ := φ j),
      norm_eAngle_sub_eq]
    congr 1
    rw [abs_of_nonneg hsinu]
  have hfack : ‖1 - eAngle (φ k - t)‖ = 2 * Real.sin ((b - t) / 2) := by
    have h1 : eAngle (φ k - t) = eAngle (b - t) := by
      rw [show φ k - t = φ k + (-t) by ring, eAngle_add, show b - t = b + (-t) by ring,
        eAngle_add, hk]
    rw [h1, norm_one_sub_eAngle_eq]
    congr 1
    rw [abs_of_nonneg hsinv]
  have hg : ∀ i : Fin s, 0 ≤ ‖1 - eAngle (φ i - t)‖ ^ (2 * r i) := fun i =>
    Real.rpow_nonneg (norm_nonneg _) _
  have hkjm : k ∈ Finset.univ.erase j :=
    Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩
  have hsplit1 : (∏ i : Fin s, ‖1 - eAngle (φ i - t)‖ ^ (2 * r i))
      = ‖1 - eAngle (φ j - t)‖ ^ (2 * r j)
        * ∏ i ∈ Finset.univ.erase j, ‖1 - eAngle (φ i - t)‖ ^ (2 * r i) :=
    (Finset.mul_prod_erase Finset.univ (fun i : Fin s => ‖1 - eAngle (φ i - t)‖ ^ (2 * r i))
      (Finset.mem_univ j)).symm
  have hsplit2 : (∏ i ∈ Finset.univ.erase j, ‖1 - eAngle (φ i - t)‖ ^ (2 * r i))
      = ‖1 - eAngle (φ k - t)‖ ^ (2 * r k)
        * ∏ i ∈ (Finset.univ.erase j).erase k, ‖1 - eAngle (φ i - t)‖ ^ (2 * r i) :=
    (Finset.mul_prod_erase (Finset.univ.erase j)
      (fun i : Fin s => ‖1 - eAngle (φ i - t)‖ ^ (2 * r i)) hkjm).symm
  have hsumrest : (∑ i ∈ (Finset.univ.erase j).erase k, r i) = 1 - r j - r k := by
    have h1' : (Finset.univ.erase j).erase k = Finset.univ \ {j, k} := by
      ext i; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, true_and, not_or]; tauto
    rw [h1']
    have h2' : (∑ i ∈ Finset.univ \ ({j, k} : Finset (Fin s)), r i)
        + (∑ i ∈ ({j, k} : Finset (Fin s)), r i) = ∑ i : Fin s, r i :=
      Finset.sum_sdiff (by simp)
    rw [Finset.sum_pair hkj.symm, hsum] at h2'
    linarith only [h2']
  have hrest : (∏ i ∈ (Finset.univ.erase j).erase k, ‖1 - eAngle (φ i - t)‖ ^ (2 * r i))
      ≤ (2 : ℝ) ^ (2 * (1 - r j - r k)) := by
    have h1 : (∏ i ∈ (Finset.univ.erase j).erase k,
        ‖1 - eAngle (φ i - t)‖ ^ (2 * r i))
        ≤ ∏ i ∈ (Finset.univ.erase j).erase k, (2 : ℝ) ^ (2 * r i) :=
      Finset.prod_le_prod (fun i _ => hg i) (fun i _ => Submission.ModelStarBoundary5.factor_pow_le (hr i) (θ := φ i - t))
    have h2 : (∏ i ∈ (Finset.univ.erase j).erase k, (2 : ℝ) ^ (2 * r i))
        = (2 : ℝ) ^ (2 * (1 - r j - r k)) := by
      rw [← Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2), ← Finset.mul_sum, hsumrest]
    exact h1.trans (le_of_eq h2)
  have hpow : (2 : ℝ) ^ (2 * r j) * (2 : ℝ) ^ (2 * r k) * (2 : ℝ) ^ (2 * (1 - r j - r k))
      = 4 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    have h2 : 2 * r j + 2 * r k + 2 * (1 - r j - r k) = 2 := by ring
    rw [h2, Real.rpow_two]
    norm_num
  have step1 : rho φ r t ≤ (2 * Real.sin ((t - φ j) / 2)) ^ (2 * r j)
      * ((2 * Real.sin ((b - t) / 2)) ^ (2 * r k)
        * ∏ i ∈ (Finset.univ.erase j).erase k, ‖1 - eAngle (φ i - t)‖ ^ (2 * r i)) := by
    unfold Submission.ModelStarBoundary3.rho
    rw [hsplit1, hsplit2, hfacj, hfack]
  have hA : (0:ℝ) ≤ (2 * Real.sin ((t - φ j) / 2)) ^ (2 * r j) :=
    Real.rpow_nonneg (by linarith only [hsinu]) _
  have hB : (0:ℝ) ≤ (2 * Real.sin ((b - t) / 2)) ^ (2 * r k) :=
    Real.rpow_nonneg (by linarith only [hsinv]) _
  have e1 : (2 * Real.sin ((t - φ j) / 2)) ^ (2 * r j)
      = (2:ℝ) ^ (2 * r j) * Real.sin ((t - φ j) / 2) ^ (2 * r j) :=
    Real.mul_rpow (by norm_num) hsinu
  have e2 : (2 * Real.sin ((b - t) / 2)) ^ (2 * r k)
      = (2:ℝ) ^ (2 * r k) * Real.sin ((b - t) / 2) ^ (2 * r k) :=
    Real.mul_rpow (by norm_num) hsinv
  calc rho φ r t ≤ (2 * Real.sin ((t - φ j) / 2)) ^ (2 * r j)
        * ((2 * Real.sin ((b - t) / 2)) ^ (2 * r k)
          * ∏ i ∈ (Finset.univ.erase j).erase k, ‖1 - eAngle (φ i - t)‖ ^ (2 * r i)) := step1
    _ ≤ (2 * Real.sin ((t - φ j) / 2)) ^ (2 * r j)
        * ((2 * Real.sin ((b - t) / 2)) ^ (2 * r k) * (2 : ℝ) ^ (2 * (1 - r j - r k))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrest hB) hA
    _ = 4 * Real.sin ((t - φ j) / 2) ^ (2 * r j)
          * Real.sin ((b - t) / 2) ^ (2 * r k) := by
        rw [e1, e2]
        rw [show (2:ℝ) ^ (2 * r j) * Real.sin ((t - φ j) / 2) ^ (2 * r j)
              * ((2:ℝ) ^ (2 * r k) * Real.sin ((b - t) / 2) ^ (2 * r k)
                * (2 : ℝ) ^ (2 * (1 - r j - r k)))
            = ((2:ℝ) ^ (2 * r j) * (2:ℝ) ^ (2 * r k) * (2:ℝ) ^ (2 * (1 - r j - r k)))
              * (Real.sin ((t - φ j) / 2) ^ (2 * r j)
                * Real.sin ((b - t) / 2) ^ (2 * r k)) by ring]
        rw [hpow]
        ring

/-! ## The balanced arc bound -/

/-- **Balanced per-arc bound.** -/
theorem rho_le_arc_balanced (hs : 0 < s) (φ r : Fin s → ℝ) {j k : Fin s}
    (hr : ∀ i, 0 ≤ r i) (hsum : (∑ i : Fin s, r i) = 1) (hkj : k ≠ j)
    (hmono : Monotone φ) (hφlo : ∀ i, 0 ≤ φ i) (hφle : ∀ i, φ i ≤ 2 * Real.pi)
    (hk : eAngle (φ k) = eAngle (nextJunction φ hs j))
    (hgap : nextJunction φ hs j - φ j ≤ Real.pi)
    (t : ℝ) (ht : t ∈ Icc (φ j) (nextJunction φ hs j)) :
    rho φ r t ≤ 4 * (r j / (r j + r k)) ^ (r j) * (r k / (r j + r k)) ^ (r k) := by
  set b : ℝ := nextJunction φ hs j with hb
  have hmain := rho_arc_le hs φ r hr hsum hkj hmono hφlo hφle hk t ht
  have ht0 : φ j ≤ t := ht.1
  have ht1 : t ≤ b := ht.2
  have hgap' : b - φ j ≤ Real.pi := by rw [hb]; exact hgap
  have hu0 : 0 ≤ (t - φ j) / 2 := by linarith only [ht0]
  have hv0 : 0 ≤ (b - t) / 2 := by linarith only [ht1]
  have huv : (t - φ j) / 2 + (b - t) / 2 ≤ Real.pi / 2 := by linarith only [hgap']
  have hsin := Commons.Analysis.SpecialFunctions.sin_pow_mul_sin_pow_le
    (a := 2 * r j) (b := 2 * r k) (u := (t - φ j) / 2) (v := (b - t) / 2)
    (by linarith only [hr j]) (by linarith only [hr k]) hu0 hv0 huv
  rw [show (2 * r j / (2 * r j + 2 * r k)) ^ ((2 * r j) / 2)
        = (r j / (r j + r k)) ^ (r j) from by
      rw [show (2 * r j) / 2 = r j by ring]
      congr 1
      rw [show 2 * r j + 2 * r k = 2 * (r j + r k) by ring, mul_div_mul_left _ _ (by norm_num)],
    show (2 * r k / (2 * r j + 2 * r k)) ^ ((2 * r k) / 2)
        = (r k / (r j + r k)) ^ (r k) from by
      rw [show (2 * r k) / 2 = r k by ring]
      congr 1
      rw [show 2 * r j + 2 * r k = 2 * (r j + r k) by ring, mul_div_mul_left _ _ (by norm_num)]]
    at hsin
  have h4 : 4 * (Real.sin ((t - φ j) / 2) ^ (2 * r j)
      * Real.sin ((b - t) / 2) ^ (2 * r k))
      ≤ 4 * ((r j / (r j + r k)) ^ (r j) * (r k / (r j + r k)) ^ (r k)) :=
    mul_le_mul_of_nonneg_left hsin (by norm_num)
  calc rho φ r t ≤ 4 * Real.sin ((t - φ j) / 2) ^ (2 * r j)
        * Real.sin ((b - t) / 2) ^ (2 * r k) := hmain
    _ = 4 * (Real.sin ((t - φ j) / 2) ^ (2 * r j)
          * Real.sin ((b - t) / 2) ^ (2 * r k)) := by ring
    _ ≤ 4 * ((r j / (r j + r k)) ^ (r j) * (r k / (r j + r k)) ^ (r k)) := h4
    _ = 4 * (r j / (r j + r k)) ^ (r j) * (r k / (r j + r k)) ^ (r k) := by ring

/-! ## The vanishing arc bound -/

/-- **Vanishing per-arc bound.** -/
theorem rho_le_arc_vanishing (hs : 0 < s) (φ r : Fin s → ℝ) {j k : Fin s}
    (hr : ∀ i, 0 ≤ r i) (hsum : (∑ i : Fin s, r i) = 1) (hkj : k ≠ j)
    (hmono : Monotone φ) (hφlo : ∀ i, 0 ≤ φ i) (hφle : ∀ i, φ i ≤ 2 * Real.pi)
    (hk : eAngle (φ k) = eAngle (nextJunction φ hs j))
    (hgap : nextJunction φ hs j - φ j ≤ Real.pi)
    (t : ℝ) (ht : t ∈ Icc (φ j) (nextJunction φ hs j)) :
    rho φ r t ≤ 4 * Real.sin ((nextJunction φ hs j - φ j) / 2) ^ (2 * (r j + r k)) := by
  set b : ℝ := nextJunction φ hs j with hb
  have hmain := rho_arc_le hs φ r hr hsum hkj hmono hφlo hφle hk t ht
  have ht0 : φ j ≤ t := ht.1
  have ht1 : t ≤ b := ht.2
  have hgap' : b - φ j ≤ Real.pi := by rw [hb]; exact hgap
  have hu0 : 0 ≤ (t - φ j) / 2 := by linarith only [ht0]
  have hv0 : 0 ≤ (b - t) / 2 := by linarith only [ht1]
  have hc0 : 0 ≤ (b - φ j) / 2 := by linarith only [ht0, ht1]
  have huc : (t - φ j) / 2 ≤ (b - φ j) / 2 := by linarith only [ht0, ht1]
  have hvc : (b - t) / 2 ≤ (b - φ j) / 2 := by linarith only [ht0, ht1]
  have hu : Real.sin ((t - φ j) / 2) ≤ Real.sin ((b - φ j) / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith only [hu0, Real.pi_pos]) (by linarith only [hgap', Real.pi_pos]) huc
  have hv : Real.sin ((b - t) / 2) ≤ Real.sin ((b - φ j) / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith only [hv0, Real.pi_pos]) (by linarith only [hgap', Real.pi_pos]) hvc
  have hsu0 : 0 ≤ Real.sin ((t - φ j) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hu0 (by linarith only [hgap', ht0, ht1, Real.pi_pos])
  have hsv0 : 0 ≤ Real.sin ((b - t) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hv0 (by linarith only [hgap', ht0, ht1, Real.pi_pos])
  have hsc0 : 0 ≤ Real.sin ((b - φ j) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hc0 (by linarith only [hgap', Real.pi_pos])
  have hu' : Real.sin ((t - φ j) / 2) ^ (2 * r j) ≤ Real.sin ((b - φ j) / 2) ^ (2 * r j) :=
    Real.rpow_le_rpow hsu0 hu (by linarith only [hr j])
  have hv' : Real.sin ((b - t) / 2) ^ (2 * r k) ≤ Real.sin ((b - φ j) / 2) ^ (2 * r k) :=
    Real.rpow_le_rpow hsv0 hv (by linarith only [hr k])
  have hprod : Real.sin ((t - φ j) / 2) ^ (2 * r j) * Real.sin ((b - t) / 2) ^ (2 * r k)
      ≤ Real.sin ((b - φ j) / 2) ^ (2 * (r j + r k)) := by
    have hp := mul_le_mul hu' hv' (Real.rpow_nonneg hsv0 _) (Real.rpow_nonneg hsc0 _)
    have hsum2 : Real.sin ((b - φ j) / 2) ^ (2 * r j)
        * Real.sin ((b - φ j) / 2) ^ (2 * r k)
        = Real.sin ((b - φ j) / 2) ^ (2 * (r j + r k)) := by
      by_cases hpos : 2 * r j + 2 * r k = 0
      · have hj0 : r j = 0 := by linarith only [hr j, hr k, hpos]
        have hk0 : r k = 0 := by linarith only [hr j, hr k, hpos]
        rw [hj0, hk0]; simp
      · rw [show 2 * (r j + r k) = 2 * r j + 2 * r k by ring, Real.rpow_add' hsc0 hpos]
    rwa [hsum2] at hp
  calc rho φ r t ≤ 4 * Real.sin ((t - φ j) / 2) ^ (2 * r j)
        * Real.sin ((b - t) / 2) ^ (2 * r k) := hmain
    _ = 4 * (Real.sin ((t - φ j) / 2) ^ (2 * r j)
          * Real.sin ((b - t) / 2) ^ (2 * r k)) := by ring
    _ ≤ 4 * Real.sin ((b - φ j) / 2) ^ (2 * (r j + r k)) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = 4 * Real.sin ((nextJunction φ hs j - φ j) / 2) ^ (2 * (r j + r k)) := by rw [hb]

end Submission.ModelStarArcBound
