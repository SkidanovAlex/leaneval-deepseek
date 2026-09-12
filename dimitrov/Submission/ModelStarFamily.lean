import Mathlib
import Submission.ModelStarTipBound
import Submission.ModelStarArcBound
import Submission.ModelStarImageSeg
import Submission.Commons.Topology.continuousAt_sSup_image_Icc

/-!
# ModelStarFamily -- the general-s model-star family over the junction-gap simplex

STATUS: research isolate (NOT imported by `Submission.lean`).

For `s ≥ 1`, a weight vector `r : Fin s → ℝ` with `r k > 0`, `Σ r k = 1`, and a
gap vector `g : Fin s → ℝ` with `g k ≥ 0`, `Σ g k = 1` (the standard probability
simplex `Simp`), the model star family is

    φ k := 2π · Σ_{j < k} g j ,   arc j := (φ j, φ j + 2π g j) ,

    ρ_g(t) := ∏_k ‖1 − eAngle (φ k − t)‖ ^ (2 r k) ,   tip_j(g) := sup ρ_g over arc j.

The point of this module: the weights are FORCED (by the desired spike
directions -- see `Submission.ModelStarDirection`), while the gap vector `g` is
FREE over the simplex.  We prove

* `tip` is continuous in `g` on the simplex (`continuousWithinAt_tip`,
  `continuousOn_tip`),
* `tip` vanishes on the face `g j = 0` (`tip_eq_zero_of_gap_eq_zero`),
* Konyagin–Lev: `∃ j, 4^(1/s) ≤ tip_j(g)` for every `g` in the simplex
  (`exists_tip_ge_four_rpow_inv`),

so that the KKM lemma for closed subsets of the simplex
(`Commons.Topology.Simplex.kkm_standardSimplex`) yields a gap vector whose tips
are ALL `≥ 4^(1/s)` (`exists_tip_all_ge`): the model star then contains the
hedgehog with `s` spikes of length `4^(1/s)` in its own (forced) directions, and
the "dominating model star" reduction
(`Submission.ModelStarDominating.unit_case_of_dominating_modelStar`) closes the
unit case of Dubinin's inequality.  This is the *only* topological input of that
route: no Carathéodory theory, no conformal map of a general domain.
-/

noncomputable section

open scoped Real BigOperators Topology
open Set Filter

namespace Submission.ModelStarFamily

open Submission.ModelStarBoundary2 (eAngle)
open Submission.ModelStarBoundary3 (rho)

variable {s : ℕ}

/-- Junction angles from the gap vector: `φ k = 2π Σ_{j < k} g j`. -/
def junc (g : Fin s → ℝ) : Fin s → ℝ :=
  fun k => 2 * Real.pi * ∑ j : Fin s, if j.val < k.val then g j else 0

/-- The cumulative gap sum `Σ_{j ≤ k} g j` (the angle `arcHi / 2π`). -/
def cum (g : Fin s → ℝ) (k : Fin s) : ℝ :=
  ∑ j : Fin s, if j.val ≤ k.val then g j else 0

/-- Lower end of arc `j`. -/
def arcLo (g : Fin s → ℝ) (j : Fin s) : ℝ := junc g j

/-- Upper end of arc `j`: `2π · Σ_{i ≤ j} g i`.  For `j` the last index this is
`2π` (the wrap-around arc). -/
def arcHi (g : Fin s → ℝ) (j : Fin s) : ℝ := 2 * Real.pi * cum g j

/-- Upper end of the *extended* arc `j`, used for the everywhere-continuous
extension `tipExt` of the tip: `arcLo g j + max (2π g j) 0`. -/
def arcHiExt (g : Fin s → ℝ) (j : Fin s) : ℝ := arcLo g j + max (2 * Real.pi * g j) 0

/-- The sweep factor of the family. -/
def rhoG (r : Fin s → ℝ) (g : Fin s → ℝ) (t : ℝ) : ℝ :=
  ∏ k : Fin s, ‖1 - eAngle (junc g k - t)‖ ^ (2 * r k)

/-- The tip of arc `j`: the sup of the sweep factor over the CLOSED arc.
(Defined through the extended arc `arcHiExt` so that it is continuous on ALL of
`ℝ^s`, which is what the KKM lemma for closed subsets of the ambient space
needs; on the simplex `arcHiExt = arcHi` and the definition agrees with the plain
arc tip.) -/
def tip (r : Fin s → ℝ) (g : Fin s → ℝ) (j : Fin s) : ℝ :=
  sSup (rhoG r g '' Icc (arcLo g j) (arcHiExt g j))

/-- The standard simplex of gap vectors. -/
def Simp : Set (Fin s → ℝ) := {g | (∀ k, 0 ≤ g k) ∧ ∑ k, g k = 1}

lemma rhoG_eq_rho (r : Fin s → ℝ) (g : Fin s → ℝ) (t : ℝ) :
    rhoG r g t = rho (junc g) r t := rfl

/-! ## The gap sum recurrences -/

lemma summand_split_lt (g : Fin s → ℝ) {k : Fin s} (j : Fin s) :
    (if j.val < k.val + 1 then g j else 0 : ℝ) =
      (if j.val < k.val then g j else 0) + (if j = k then g j else 0) := by
  by_cases hlt : j.val < k.val
  · have hne : ¬ (j = k) := fun hjk => by rw [hjk] at hlt; exact absurd hlt (lt_irrefl _)
    rw [if_pos (by omega), if_pos hlt, if_neg hne, add_zero]
  · by_cases heq : j.val = k.val
    · rw [if_pos (by omega), if_neg hlt, if_pos (Fin.ext heq), zero_add]
    · rw [if_neg (by omega), if_neg hlt,
        if_neg (fun hjk => heq (by rw [hjk])), add_zero]

/-- `Σ_{i ≤ k} g i = Σ_{i < k} g i + g k`. -/
lemma cum_eq_add (g : Fin s → ℝ) (k : Fin s) :
    cum g k = (∑ j : Fin s, if j.val < k.val then g j else 0) + g k := by
  have hgs : g k = ∑ j : Fin s, (if j = k then g j else 0 : ℝ) := by
    rw [Finset.sum_ite_eq' Finset.univ k (fun j => g j), if_pos (Finset.mem_univ k)]
  rw [hgs, ← Finset.sum_add_distrib]
  unfold cum
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hlt : j.val < k.val
  · have hne : ¬ (j = k) := fun hjk => by rw [hjk] at hlt; exact absurd hlt (lt_irrefl _)
    rw [if_pos (by omega), if_pos hlt, if_neg hne, add_zero]
  · by_cases heq : j.val = k.val
    · rw [if_pos (by omega), if_neg hlt, if_pos (Fin.ext heq), zero_add]
    · rw [if_neg (by omega), if_neg hlt,
        if_neg (fun hjk => heq (by rw [hjk])), add_zero]

/-- **Recurrence**: `φ (k+1) = φ k + 2π g k`. -/
lemma junc_succ (g : Fin s → ℝ) {k : Fin s} (hk : k.val + 1 < s) :
    junc g ⟨k.val + 1, hk⟩ = junc g k + 2 * Real.pi * g k := by
  have hgs : g k = ∑ j : Fin s, (if j = k then g j else 0 : ℝ) := by
    rw [Finset.sum_ite_eq' Finset.univ k (fun j => g j), if_pos (Finset.mem_univ k)]
  have hsplit : (∑ j : Fin s, (if j.val < k.val + 1 then g j else 0 : ℝ))
      = (∑ j : Fin s, (if j.val < k.val then g j else 0 : ℝ))
        + (∑ j : Fin s, (if j = k then g j else 0 : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => summand_split_lt g j)
  unfold junc
  rw [hsplit, hgs]
  ring

/-- `arcHi g j = arcLo g j + 2π g j`. -/
lemma arcHi_eq_arcLo_add (g : Fin s → ℝ) (j : Fin s) :
    arcHi g j = arcLo g j + 2 * Real.pi * g j := by
  unfold arcHi arcLo junc
  rw [cum_eq_add]
  ring

/-- `arcHi` is the next junction angle when the next index exists. -/
lemma arcHi_eq_junc_succ (g : Fin s → ℝ) {j : Fin s} (h : j.val + 1 < s) :
    arcHi g j = junc g ⟨j.val + 1, h⟩ := by
  have hsum_eq : (∑ i : Fin s, (if i.val ≤ j.val then g i else 0 : ℝ))
      = ∑ i : Fin s, (if i.val < (⟨j.val + 1, h⟩ : Fin s).val then g i else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i.val ≤ j.val
    · rw [if_pos hi, if_pos (by show i.val < j.val + 1; omega)]
    · rw [if_neg hi, if_neg (by show ¬ i.val < j.val + 1; omega)]
  unfold arcHi cum junc
  rw [hsum_eq]

lemma junc_zero (g : Fin s → ℝ) (hs : 0 < s) : junc g ⟨0, hs⟩ = 0 := by
  unfold junc
  simp

/-- For the last index, `arcHi = 2π`. -/
lemma arcHi_last (g : Fin s → ℝ) (hsum : (∑ k, g k) = 1) {j : Fin s}
    (h : ¬ j.val + 1 < s) : arcHi g j = 2 * Real.pi := by
  have hjv : j.val = s - 1 := by have := j.isLt; omega
  have hcum : cum g j = 1 := by
    unfold cum
    rw [← hsum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [if_pos (by have := i.isLt; omega)]
  rw [arcHi, hcum, mul_one]

/-- `arcHi` is the next junction angle (the tree's `nextJunction`). -/
lemma arcHi_eq_nextJunction (g : Fin s → ℝ) (hs : 0 < s) (hsum : (∑ k, g k) = 1)
    (j : Fin s) :
    arcHi g j = Submission.ModelStarImageSeg.nextJunction (junc g) hs j := by
  by_cases h : j.val + 1 < s
  · rw [Submission.ModelStarImageSeg.nextJunction_of_lt h, arcHi_eq_junc_succ g h]
  · rw [Submission.ModelStarImageSeg.nextJunction_of_not_lt h, arcHi_last g hsum h,
      junc_zero g hs, zero_add]

/-! ## Elementary monotonicity / bounds on the simplex -/

lemma junc_mono {g : Fin s → ℝ} (hg : ∀ k, 0 ≤ g k) : Monotone (junc g) := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  unfold junc
  have hle : (∑ x : Fin s, (if x.val < i.val then g x else 0 : ℝ))
      ≤ ∑ x : Fin s, (if x.val < j.val then g x else 0 : ℝ) := by
    refine Finset.sum_le_sum (fun x _ => ?_)
    by_cases hx : x.val < i.val
    · rw [if_pos hx, if_pos (by omega)]
    · rw [if_neg hx]
      by_cases hx' : x.val < j.val
      · rw [if_pos hx']; exact hg x
      · rw [if_neg hx']
  nlinarith [hle, Real.pi_pos]

lemma junc_nonneg {g : Fin s → ℝ} (hg : ∀ k, 0 ≤ g k) (i : Fin s) : 0 ≤ junc g i := by
  unfold junc
  have h : (0:ℝ) ≤ ∑ j : Fin s, (if j.val < i.val then g j else 0) := by
    refine Finset.sum_nonneg (fun j _ => ?_)
    by_cases hj : j.val < i.val
    · rw [if_pos hj]; exact hg j
    · rw [if_neg hj]
  nlinarith [Real.pi_pos]

lemma junc_le_two_pi {g : Fin s → ℝ} (hg : ∀ k, 0 ≤ g k) (hsum : (∑ k, g k) = 1)
    (i : Fin s) : junc g i ≤ 2 * Real.pi := by
  unfold junc
  have hle : (∑ j : Fin s, (if j.val < i.val then g j else 0 : ℝ)) ≤ 1 := by
    rw [← hsum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases hj : j.val < i.val
    · rw [if_pos hj]
    · rw [if_neg hj]; exact hg j
  nlinarith [Real.pi_pos]

lemma arcLo_le_arcHi {g : Fin s → ℝ} (hg : ∀ k, 0 ≤ g k) (j : Fin s) :
    arcLo g j ≤ arcHi g j := by
  rw [arcHi_eq_arcLo_add]
  have := hg j
  nlinarith [Real.pi_pos]

lemma cum_nonneg {g : Fin s → ℝ} (hg : ∀ k, 0 ≤ g k) (j : Fin s) : 0 ≤ cum g j := by
  unfold cum
  refine Finset.sum_nonneg (fun i _ => ?_)
  by_cases hi : i.val ≤ j.val
  · rw [if_pos hi]; exact hg i
  · rw [if_neg hi]

lemma cum_le_one {g : Fin s → ℝ} (hg : ∀ k, 0 ≤ g k) (hsum : (∑ k, g k) = 1)
    (j : Fin s) : cum g j ≤ 1 := by
  unfold cum
  rw [← hsum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases hi : i.val ≤ j.val
  · rw [if_pos hi]
  · rw [if_neg hi]; exact hg i


/-! ## Nonnegativity, boundedness, face vanishing -/

lemma arcLo_le_arcHiExt (g : Fin s → ℝ) (j : Fin s) : arcLo g j ≤ arcHiExt g j := by
  unfold arcHiExt
  exact le_add_of_nonneg_right (le_max_right _ _)

lemma rhoG_nonneg (r : Fin s → ℝ) (g : Fin s → ℝ) (t : ℝ) : 0 ≤ rhoG r g t :=
  Finset.prod_nonneg fun k _ => Real.rpow_nonneg (norm_nonneg _) _

lemma bddAbove_rhoG (r : Fin s → ℝ) (hr : ∀ k, 0 ≤ r k) (g : Fin s → ℝ)
    (a b : ℝ) : BddAbove (rhoG r g '' Icc a b) :=
  ⟨∏ k : Fin s, (2 : ℝ) ^ (2 * r k), by
    rintro y ⟨t, -, rfl⟩
    exact Submission.ModelStarBoundary5.rho_le_uniform_bound (junc g) r hr t⟩

lemma tip_nonneg (r : Fin s → ℝ) (hr : ∀ k, 0 ≤ r k) (g : Fin s → ℝ) (j : Fin s) :
    0 ≤ tip r g j := by
  unfold tip
  exact le_trans (rhoG_nonneg r g _)
    (le_csSup (bddAbove_rhoG r hr g _ _)
      ⟨arcLo g j, left_mem_Icc.mpr (arcLo_le_arcHiExt g j), rfl⟩)

/-- The sweep factor vanishes at every junction angle. -/
lemma rhoG_zero_at_junc (r : Fin s → ℝ) (hr : ∀ k, 0 < r k) (g : Fin s → ℝ)
    (k : Fin s) : rhoG r g (junc g k) = 0 := by
  unfold rhoG
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  rw [sub_self, show eAngle 0 = 1 from by simp [Submission.ModelStarBoundary2.eAngle],
    sub_self, norm_zero, Real.zero_rpow (by linarith [hr k] : (2 * r k) ≠ 0)]

/-- **Face vanishing**: if `g j = 0` the `j`-th tip is `0`. -/
lemma tip_eq_zero_of_gap_eq_zero (r : Fin s → ℝ) (hr : ∀ k, 0 < r k) {g : Fin s → ℝ}
    {j : Fin s} (hg : g j = 0) : tip r g j = 0 := by
  unfold tip arcHiExt
  rw [hg, mul_zero, max_self, add_zero, Icc_self, Set.image_singleton, csSup_singleton, arcLo]
  exact rhoG_zero_at_junc r hr g j

/-- **Face vanishing, nonpositive form**: if `g j ≤ 0` the `j`-th tip is `0`. -/
lemma tip_eq_zero_of_gap_nonpos (r : Fin s → ℝ) (hr : ∀ k, 0 < r k) {g : Fin s → ℝ}
    {j : Fin s} (hg : g j ≤ 0) : tip r g j = 0 := by
  unfold tip arcHiExt
  rw [max_eq_right (by nlinarith [Real.pi_pos, hg]), add_zero, Icc_self,
    Set.image_singleton, csSup_singleton, arcLo]
  exact rhoG_zero_at_junc r hr g j

/-- **Uniform vanishing bound**: the tip is controlled by the `j`-th gap alone,
with no hypothesis at all on `g`. -/
lemma tip_le_gap_bound (r : Fin s → ℝ) (hr : ∀ k, 0 < r k) (g : Fin s → ℝ) (j : Fin s) :
    tip r g j ≤ (max (2 * Real.pi * g j) 0) ^ (2 * r j) *
      2 ^ (2 * ∑ k ∈ Finset.univ.erase j, r k) := by
  have hconstnn : (0:ℝ) < 2 ^ (2 * ∑ k ∈ Finset.univ.erase j, r k) := by positivity
  unfold tip arcHiExt
  refine csSup_le ⟨rhoG r g (arcLo g j), arcLo g j,
    left_mem_Icc.mpr (le_add_of_nonneg_right (le_max_right _ _)), rfl⟩ ?_
  rintro y ⟨t, ht, rfl⟩
  rcases lt_or_ge 0 (2 * Real.pi * g j) with hcase | hcase
  · have hmax : max (2 * Real.pi * g j) 0 = 2 * Real.pi * g j := max_eq_left hcase.le
    have ht' : 0 ≤ t - arcLo g j ∧ t - arcLo g j ≤ 2 * Real.pi * g j := by
      rw [hmax] at ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hjt : |junc g j - t| ≤ 2 * Real.pi * g j := by
      rw [abs_le]
      exact ⟨by rw [show junc g j = arcLo g j from rfl]; linarith [ht'.2],
        by rw [show junc g j = arcLo g j from rfl]; linarith [ht'.1]⟩
    have hfac : ‖1 - eAngle (junc g j - t)‖ ≤ 2 * Real.pi * g j := by
      rw [Submission.ModelStarArcBound.norm_one_sub_eAngle_eq]
      have h1 : |Real.sin ((junc g j - t) / 2)| ≤ |(junc g j - t) / 2| := Real.abs_sin_le_abs
      have h2 : |(junc g j - t) / 2| ≤ Real.pi * g j := by
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        linarith
      linarith
    have hjnn : 0 ≤ ‖1 - eAngle (junc g j - t)‖ := norm_nonneg _
    have hprod : rhoG r g t ≤ ‖1 - eAngle (junc g j - t)‖ ^ (2 * r j) *
        ∏ k ∈ Finset.univ.erase j, (2 : ℝ) ^ (2 * r k) := by
      unfold rhoG
      rw [← Finset.mul_prod_erase Finset.univ
        (fun k => ‖1 - eAngle (junc g k - t)‖ ^ (2 * r k)) (Finset.mem_univ j)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hjnn _)
      refine Finset.prod_le_prod (fun k _ => Real.rpow_nonneg (norm_nonneg _) _) (fun k _ => ?_)
      have h2 : ‖1 - eAngle (junc g k - t)‖ ≤ 2 := by
        rw [Submission.ModelStarArcBound.norm_one_sub_eAngle_eq]
        have h3 := Real.abs_sin_le_one ((junc g k - t) / 2)
        linarith
      exact Real.rpow_le_rpow (norm_nonneg _) h2 (by linarith [hr k])
    have hconst : ∏ k ∈ Finset.univ.erase j, (2 : ℝ) ^ (2 * r k)
        = 2 ^ (2 * ∑ k ∈ Finset.univ.erase j, r k) := by
      rw [← Real.rpow_sum_of_pos (show (0:ℝ) < 2 by norm_num) (fun k => 2 * r k)
        (Finset.univ.erase j)]
      congr 1
      rw [Finset.mul_sum]
    calc rhoG r g t ≤ ‖1 - eAngle (junc g j - t)‖ ^ (2 * r j) *
          ∏ k ∈ Finset.univ.erase j, (2 : ℝ) ^ (2 * r k) := hprod
      _ = ‖1 - eAngle (junc g j - t)‖ ^ (2 * r j) *
          2 ^ (2 * ∑ k ∈ Finset.univ.erase j, r k) := by rw [hconst]
      _ ≤ (max (2 * Real.pi * g j) 0) ^ (2 * r j) *
          2 ^ (2 * ∑ k ∈ Finset.univ.erase j, r k) := by
          rw [hmax]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hjnn hfac (by linarith [hr j])) hconstnn.le
  · have hmax : max (2 * Real.pi * g j) 0 = 0 := max_eq_right hcase
    rw [hmax, add_zero, Icc_self] at ht
    rw [ht, arcLo, rhoG_zero_at_junc r hr g j]
    exact mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) hconstnn.le

/-! ## Continuity of the junction data -/

lemma continuous_eAngle : Continuous fun t : ℝ => eAngle t :=
  continuous_iff_continuousAt.mpr fun t => Submission.ModelStarBoundary3.eAngle_continuousAt t

lemma continuous_junc (k : Fin s) : Continuous (fun g : Fin s → ℝ => junc g k) := by
  unfold junc
  have hterm : ∀ j : Fin s, Continuous fun g : Fin s → ℝ =>
      (if j.val < k.val then g j else 0 : ℝ) := by
    intro j
    by_cases hj : j.val < k.val
    · have : (fun g : Fin s → ℝ => (if j.val < k.val then g j else 0 : ℝ)) = fun g => g j := by
        funext g; rw [if_pos hj]
      rw [this]; exact continuous_apply j
    · have : (fun g : Fin s → ℝ => (if j.val < k.val then g j else 0 : ℝ)) = fun _ => 0 := by
        funext g; rw [if_neg hj]
      rw [this]; exact continuous_const
  exact continuous_const.mul (continuous_finset_sum _ fun j _ => hterm j)

lemma continuous_cum (k : Fin s) : Continuous (fun g : Fin s → ℝ => cum g k) := by
  unfold cum
  have hterm : ∀ j : Fin s, Continuous fun g : Fin s → ℝ =>
      (if j.val ≤ k.val then g j else 0 : ℝ) := by
    intro j
    by_cases hj : j.val ≤ k.val
    · have : (fun g : Fin s → ℝ => (if j.val ≤ k.val then g j else 0 : ℝ)) = fun g => g j := by
        funext g; rw [if_pos hj]
      rw [this]; exact continuous_apply j
    · have : (fun g : Fin s → ℝ => (if j.val ≤ k.val then g j else 0 : ℝ)) = fun _ => 0 := by
        funext g; rw [if_neg hj]
      rw [this]; exact continuous_const
  exact continuous_finset_sum _ fun j _ => hterm j

lemma continuous_arcLo (j : Fin s) : Continuous (fun g : Fin s → ℝ => arcLo g j) :=
  continuous_junc j

lemma continuous_arcHiExt (j : Fin s) : Continuous (fun g : Fin s → ℝ => arcHiExt g j) := by
  have h2 : Continuous fun g : Fin s → ℝ => 2 * Real.pi * g j :=
    (continuous_const (y := 2 * Real.pi)).mul (continuous_apply j)
  exact (continuous_arcLo j).add (h2.max continuous_const)

lemma continuous_rhoG (r : Fin s → ℝ) (hr : ∀ k, 0 ≤ r k) :
    Continuous fun p : (Fin s → ℝ) × ℝ => rhoG r p.1 p.2 := by
  unfold rhoG
  refine continuous_finsetProd Finset.univ fun k _ => ?_
  have h2 : Continuous fun p : (Fin s → ℝ) × ℝ => junc p.1 k - p.2 :=
    ((continuous_junc k).comp continuous_fst).sub continuous_snd
  have h3 : Continuous fun p : (Fin s → ℝ) × ℝ => 1 - eAngle (junc p.1 k - p.2) :=
    continuous_const.sub (continuous_eAngle.comp h2)
  exact h3.norm.rpow_const (fun p => Or.inr (by linarith [hr k]))

/-! ## Continuity of the tips (everywhere) -/

/-- **The tip is continuous on all of `ℝ^s`** (via the extended arc `arcHiExt`). -/
theorem continuousAt_tip (r : Fin s → ℝ) (hr : ∀ k, 0 < r k) (g : Fin s → ℝ)
    (j : Fin s) : ContinuousAt (fun g' : Fin s → ℝ => tip r g' j) g := by
  rcases lt_or_ge 0 (2 * Real.pi * g j) with hpos | hdeg
  · -- genuine arc: sup-continuity
    have hcont := Commons.Topology.continuousAt_sSup_image_Icc
      (α := Fin s → ℝ) (f := rhoG r) (a := fun g' => arcLo g' j)
      (b := fun g' => arcHiExt g' j) (x₀ := g)
      (continuous_rhoG r (fun k => (hr k).le))
      (continuous_arcLo j).continuousAt (continuous_arcHiExt j).continuousAt
      (by unfold arcHiExt; rw [max_eq_left hpos.le]; linarith)
    exact hcont
  · -- collapsed extended arc: squeeze against the vanishing bound
    have hgj : g j ≤ 0 := by nlinarith [Real.pi_pos]
    have hval : tip r g j = 0 := tip_eq_zero_of_gap_nonpos r hr hgj
    rw [ContinuousAt]
    simp only [hval]
    rw [tendsto_order]
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · filter_upwards with g'
      exact lt_of_lt_of_le hb (tip_nonneg r (fun k => (hr k).le) g' j)
    · have hc : ContinuousAt (fun g' : Fin s → ℝ => max (2 * Real.pi * g' j) 0) g :=
        ((((continuous_const (y := 2 * Real.pi)).mul (continuous_apply j)).max
          (continuous_const (y := (0:ℝ)))).continuousAt)
      have hr2 : (0:ℝ) < 2 * r j := by linarith [hr j]
      have h1 : ContinuousAt (fun x : ℝ => x ^ (2 * r j)) (max (2 * Real.pi * g j) 0) :=
        Real.continuousAt_rpow_const _ _ (Or.inr hr2.le)
      have hcont2 : ContinuousAt (fun g' : Fin s → ℝ =>
          (max (2 * Real.pi * g' j) 0) ^ (2 * r j)) g :=
        ContinuousAt.comp (g := fun x : ℝ => x ^ (2 * r j))
          (f := fun g' : Fin s → ℝ => max (2 * Real.pi * g' j) 0) h1 hc
      have hcont : ContinuousAt (fun g' : Fin s → ℝ =>
          (max (2 * Real.pi * g' j) 0) ^ (2 * r j) *
          2 ^ (2 * ∑ k ∈ Finset.univ.erase j, r k)) g := hcont2.mul_const _
      have hz : (max (2 * Real.pi * g j) 0) ^ (2 * r j) *
          2 ^ (2 * ∑ k ∈ Finset.univ.erase j, r k) = 0 := by
        rw [max_eq_right hdeg, Real.zero_rpow (by linarith [hr j] : (2 * r j) ≠ 0), zero_mul]
      have htend := hz ▸ hcont.tendsto
      have hev : ∀ᶠ g' in 𝓝 g, (max (2 * Real.pi * g' j) 0) ^ (2 * r j) *
          2 ^ (2 * ∑ k ∈ Finset.univ.erase j, r k) < b :=
        (tendsto_order.mp htend).2 b hb
      filter_upwards [hev] with g' h1
      exact lt_of_le_of_lt (tip_le_gap_bound r hr g' j) h1

/-! ## Agreement with the simplex tip, Konyagin–Lev, closedness -/

lemma arcHiExt_eq_arcHi {g : Fin s → ℝ} {j : Fin s} (hg : 0 ≤ g j) :
    arcHiExt g j = arcHi g j := by
  have hmax : max (2 * Real.pi * g j) 0 = 2 * Real.pi * g j :=
    max_eq_left (by nlinarith [Real.pi_pos, hg])
  simp only [arcHiExt, arcHi, arcLo, junc]
  rw [hmax, cum_eq_add]
  ring

lemma tip_eq_tip_of_mem {r : Fin s → ℝ} {g : Fin s → ℝ} (hg : ∀ k, 0 ≤ g k) (j : Fin s) :
    tip r g j = sSup (rhoG r g '' Icc (arcLo g j) (arcHi g j)) := by
  unfold tip
  rw [arcHiExt_eq_arcHi (hg j)]

lemma isClosed_setOf_tip_ge (r : Fin s → ℝ) (hr : ∀ k, 0 < r k) (c : ℝ) (j : Fin s) :
    IsClosed {g : Fin s → ℝ | c ≤ tip r g j} :=
  isClosed_le (continuous_const : Continuous fun _ : Fin s → ℝ => c)
    (continuous_iff_continuousAt.mpr fun g => continuousAt_tip r hr g j :
      Continuous fun g : Fin s → ℝ => tip r g j)

lemma csSup_image_mono {f : ℝ → ℝ} {s t : Set ℝ} (h : s ⊆ t) (hb : BddAbove (f '' t))
    (h0 : ∀ x ∈ t, 0 ≤ f x) : sSup (f '' s) ≤ sSup (f '' t) := by
  by_cases hne : (f '' s).Nonempty
  · exact csSup_le hne fun y hy => le_csSup hb (Set.image_mono h hy)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty]
    rcases t.eq_empty_or_nonempty with he | hte
    · rw [he, Set.image_empty, Real.sSup_empty]
    · obtain ⟨x, hx⟩ := hte
      exact le_trans (h0 x hx) (le_csSup hb ⟨x, hx, rfl⟩)

/-- The open-arc tip of `Submission.ModelStarTipBound` is dominated by the tip of
this module, on the simplex. -/
lemma tipBound_le_tip (hs : 0 < s) (r : Fin s → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hsum : (∑ k, r k) = 1) {g : Fin s → ℝ} (hg : g ∈ Simp) (j : Fin s) :
    Submission.ModelStarTipBound.tip hs (junc g) r j ≤ tip r g j := by
  obtain ⟨hg0, hg1⟩ := hg
  rw [tip_eq_tip_of_mem hg0 j]
  unfold Submission.ModelStarTipBound.tip
  by_cases h : j.val + 1 < s
  · rw [dif_pos h]
    refine csSup_image_mono ?_ (bddAbove_rhoG r hr g _ _)
      (fun x _ => rhoG_nonneg r g x)
    rintro x ⟨h1, h2⟩
    exact ⟨le_of_lt h1, by rw [arcHi_eq_junc_succ g h]; exact le_of_lt h2⟩
  · rw [dif_neg h]
    have hlast : Submission.ModelStarBoundary7.wrapLast s hs = j := by
      apply Fin.ext
      show s - 1 = j.val
      have := j.isLt; omega
    rw [hlast]
    refine csSup_image_mono ?_ (bddAbove_rhoG r hr g _ _)
      (fun x _ => rhoG_nonneg r g x)
    rintro x ⟨h1, h2⟩
    rw [junc_zero g hs, zero_add] at h2
    exact ⟨le_of_lt h1, by rw [arcHi_last g hg1 h]; exact le_of_lt h2⟩

/-- **Konyagin–Lev for the family**: for every gap vector in the simplex some tip
is at least `4^(1/s)`. -/
theorem exists_tip_ge_four_rpow_inv (hs : 0 < s) (r : Fin s → ℝ) (hr : ∀ k, 0 < r k)
    (hsum : (∑ k, r k) = 1) {g : Fin s → ℝ} (hg : g ∈ Simp) :
    ∃ j : Fin s, (4 : ℝ) ^ (1 / (s : ℝ)) ≤ tip r g j := by
  obtain ⟨j, hj⟩ := Submission.ModelStarTipBound.max_tip_ge_four_rpow_inv hs
    (fun k => eAngle (junc g k)) r (junc g) (fun k => rfl) hsum hr
  exact ⟨j, le_trans hj (tipBound_le_tip hs r (fun k => (hr k).le) hsum hg j)⟩

/-- The set of gap vectors in the simplex all of whose tips are at least `c` is
closed in the ambient space. -/
theorem isClosed_tip_ge (hs : 0 < s) (r : Fin s → ℝ) (hr : ∀ k, 0 < r k)
    (hsum : (∑ k, r k) = 1) {c : ℝ} (hc : 0 < c) (j : Fin s) :
    IsClosed {g : Fin s → ℝ | g ∈ Simp ∧ c ≤ tip r g j} := by
  have hS : IsClosed (Simp : Set (Fin s → ℝ)) := by
    have h1 : IsClosed {g : Fin s → ℝ | ∑ k, g k = 1} :=
      isClosed_eq (continuous_finsetSum Finset.univ fun k _ => continuous_apply k)
        (continuous_const : Continuous fun _ : Fin s → ℝ => (1:ℝ))
    have h2 : IsClosed {g : Fin s → ℝ | ∀ k, 0 ≤ g k} := by
      rw [setOf_forall]
      exact isClosed_iInter fun k =>
        isClosed_le (continuous_const : Continuous fun _ : Fin s → ℝ => (0:ℝ))
          (continuous_apply k)
    have h3 : (Simp : Set (Fin s → ℝ)) = {g | ∀ k, 0 ≤ g k} ∩ {g | ∑ k, g k = 1} := rfl
    rw [h3]
    exact h2.inter h1
  have h1 := isClosed_setOf_tip_ge r hr c j
  have : {g : Fin s → ℝ | g ∈ Simp ∧ c ≤ tip r g j}
      = Simp ∩ {g : Fin s → ℝ | c ≤ tip r g j} := rfl
  rw [this]
  exact hS.inter h1

end Submission.ModelStarFamily

