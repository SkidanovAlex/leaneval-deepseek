import Submission.Grassmann.RoleTransfer
import Submission.Grassmann.RestrictedCor
import Submission.Grassmann.UpperBound

/-!
# §8 of arXiv:2209.04243: collapsing the switching sum with the restricted `D_X` corollary

`RoleTransfer.l2sq_restr_eq_DopRole` identifies the inner `l2sq` of a switching-roles summand
with the `L²`-norm of the *restricted* role-space `X`-derivative
`D_{X'} (D_{V₃,W₃,T'} f)`.  This file applies the (repaired) paper corollary
`cor:getting rid of D_X 4-norms` (`RestrictedCor.restricted_cor_4'`) to bound each single
summand by `2^{8d²} · 2 · ‖D_{V₃,W₃,T'} f‖₂²`, and then sums over the shift `T'`, comparing with
`D4 V₃ W₃ (Lsub V₃ W₃ f)`.

Main result: `SwSumP_le`, bounding the switching sum by a sum of `D4`-terms over the
reindexed pairs `(liftV t.1 p.1, liftW t.2.1 p.2)`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## Extracting a single summand from the restricted corollary -/

/-- The restricted `X`-derivative vanishes when `X` has rank larger than the degree of `h`. -/
lemma restr_lapMulN_eq_zero_of_rank_lt {m n d : ℕ} {h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hh : DegLe d h) {X : Matrix (Fin n) (Fin m) 𝔽₂} (hX : d < X.rank) :
    restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
      (lapMulN (plLE X) h) = 0 := by
  have h1 : lapMulN (plLE X) h = 0 := by
    refine eq_of_fcoeff_eq fun Y => ?_
    rw [fcoeff_lapMulN, fcoeff_zero]
    by_cases hp : plLE X Y
    · rw [if_pos hp, one_mul]
      have hr := plLE_rank_le hp
      rw [fcoeff_eq, hh Y (by omega), mul_zero]
    · rw [if_neg hp, zero_mul]
  rw [h1, restr_zero]

/-- `l2sq` version of `restr_lapMulN_eq_zero_of_rank_lt`. -/
lemma l2sq_restr_lapMulN_eq_zero_of_rank_lt {m n d : ℕ}
    {h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hh : DegLe d h)
    {X : Matrix (Fin n) (Fin m) 𝔽₂} (hX : d < X.rank) :
    l2sq (restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
      (lapMulN (plLE X) h)) = 0 := by
  rw [restr_lapMulN_eq_zero_of_rank_lt hh hX]
  simp [l2sq]

/-- **A single summand of the restricted corollary**: for any `X`,

`(l2sq (D_X h))² ≤ q^{4d·rank X} · q^{4d²} · 2 (l2sq h)²`. -/
lemma l2sq_restr_lapMulN_sq_le {m n d : ℕ} {h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hh : DegLe d h) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    (l2sq (restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
      (lapMulN (plLE X) h))) ^ 2
      ≤ (2 : ℝ) ^ (4 * d * X.rank) * ((2 : ℝ) ^ (4 * d * d) * (2 * (l2sq h) ^ 2)) := by
  have hsum := restricted_cor_4' (m := m) (n := n) (d := d) hh
  have hsingle : ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ *
        (l2sq (restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
          (lapMulN (plLE X) h))) ^ 2
      ≤ ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
          ((2 : ℝ) ^ (4 * d * Y.rank))⁻¹ *
            (l2sq (restr (Qp (LinearMap.range Y.mulVecLin))
              (Ip (LinearMap.ker Y.mulVecLin)) (lapMulN (plLE Y) h))) ^ 2 :=
    Finset.single_le_sum
      (f := fun Y : Matrix (Fin n) (Fin m) 𝔽₂ =>
        ((2 : ℝ) ^ (4 * d * Y.rank))⁻¹ *
          (l2sq (restr (Qp (LinearMap.range Y.mulVecLin))
            (Ip (LinearMap.ker Y.mulVecLin)) (lapMulN (plLE Y) h))) ^ 2)
      (fun Y _ => by positivity) (Finset.mem_univ X)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (4 * d * X.rank) := by positivity
  have h1 := mul_le_mul_of_nonneg_left (le_trans hsingle hsum) (le_of_lt hpos)
  have h2 : (2 : ℝ) ^ (4 * d * X.rank) *
      (((2 : ℝ) ^ (4 * d * X.rank))⁻¹ *
        (l2sq (restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
          (lapMulN (plLE X) h))) ^ 2)
      = (l2sq (restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
          (lapMulN (plLE X) h))) ^ 2 := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
  rwa [h2] at h1

/-- **A single summand, in weighted form**: the squared `L²`-norm of a restricted
`X`-derivative is at most `q^{4d·rank X}` times the *weighted* sum of all of them.  (This is the
form in which the corollary is used: the weight is kept, and the corollary bounds the weighted
sum.) -/
lemma l2sq_restr_lapMulN_sq_le_weighted {m n d : ℕ} {h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hh : DegLe d h) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    (l2sq (restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
      (lapMulN (plLE X) h))) ^ 2
      ≤ (2 : ℝ) ^ (4 * d * X.rank) *
        ∑ X' : Matrix (Fin n) (Fin m) 𝔽₂,
          ((2 : ℝ) ^ (4 * d * X'.rank))⁻¹ *
            (l2sq (restr (Qp (LinearMap.range X'.mulVecLin))
              (Ip (LinearMap.ker X'.mulVecLin)) (lapMulN (plLE X') h))) ^ 2 := by
  by_cases hX : X.rank ≤ d
  · have hsum := restricted_cor_4' (m := m) (n := n) (d := d) hh
    have hsingle : ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ *
          (l2sq (restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
            (lapMulN (plLE X) h))) ^ 2
        ≤ ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
            ((2 : ℝ) ^ (4 * d * Y.rank))⁻¹ *
              (l2sq (restr (Qp (LinearMap.range Y.mulVecLin))
                (Ip (LinearMap.ker Y.mulVecLin)) (lapMulN (plLE Y) h))) ^ 2 :=
      Finset.single_le_sum
        (f := fun Y : Matrix (Fin n) (Fin m) 𝔽₂ =>
          ((2 : ℝ) ^ (4 * d * Y.rank))⁻¹ *
            (l2sq (restr (Qp (LinearMap.range Y.mulVecLin))
              (Ip (LinearMap.ker Y.mulVecLin)) (lapMulN (plLE Y) h))) ^ 2)
        (fun Y _ => by positivity) (Finset.mem_univ X)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (4 * d * X.rank) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsingle (le_of_lt hpos)
    have h2 : (2 : ℝ) ^ (4 * d * X.rank) *
        (((2 : ℝ) ^ (4 * d * X.rank))⁻¹ *
          (l2sq (restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
            (lapMulN (plLE X) h))) ^ 2)
        = (l2sq (restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
            (lapMulN (plLE X) h))) ^ 2 := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
    rwa [h2] at h1
  · rw [l2sq_restr_lapMulN_eq_zero_of_rank_lt hh (not_le.mp hX)]
    norm_num
    refine Finset.sum_nonneg (fun Y _ => ?_)
    exact mul_nonneg (by positivity) (sq_nonneg _)

/-! ## The switching summand -/

/-- The inner `l2sq` of a switching-roles summand, for a fixed shift `T'`. -/
lemma SwTerm_term_le (t : Triple m n) (p : QPair m n t)
    (hp : p.1 ⊓ VrOf t = ⊥ ∧ p.2 ⊔ WrOf t = ⊤)
    {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f)
    (T' : Matrix (Fin m) (Fin n) 𝔽₂) :
    (l2sq (restr (Qp (liftV t.1 (liftV (VrOf t) (pV t p))))
        (Ip (liftW t.2.1 (liftW (WrOf t) (pW t p))))
        (shift T' (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))) ^ 2
      ≤ (2 : ℝ) ^ (4 * d * (XsOf t p).rank) *
        ((2 : ℝ) ^ (4 * d * d) *
          (2 * (l2sq (Dop0S (liftV t.1 p.1) (liftW t.2.1 p.2) T' f)) ^ 2)) := by
  rw [liftV_pV t p, liftW_pW t p]
  rw [l2sq_restr_eq_DopRole t p hp.1 hp.2 T' f]
  rw [XrR_eq t p, XrK_eq t p]
  have hdeg : DegLe d (Dop0S (liftV t.1 p.1) (liftW t.2.1 p.2) T' f) :=
    fun Y hY => degLe_Dop0S (V₂ := liftV t.1 p.1) (W₂ := liftW t.2.1 p.2) (T := T') hf Y
      (by omega)
  exact (l2sq_restr_lapMulN_sq_le_weighted hdeg (XsOf t p)).trans
    (mul_le_mul_of_nonneg_left (restricted_cor_4' hdeg) (by positivity))

/-- **The switching summand is bounded by a weighted `D4`-term.**  The weight
`q^{4d·rank X'}` is the price of extracting a single summand out of the restricted corollary; it
is kept (rather than replaced by `q^{4d²}`) because the reindexing count supplies it back. -/
theorem SwTerm_le (t : Triple m n) (p : QPair m n t)
    (hp : p.1 ⊓ VrOf t = ⊥ ∧ p.2 ⊔ WrOf t = ⊤)
    {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) :
    SwTerm t (pV t p) (pW t p) p f ≤
      (2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
          ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) *
        ((2 : ℝ) ^ (4 * d * (XsOf t p).rank) *
          ((2 : ℝ) ^ (4 * d * d) *
            (2 * ((2 : ℝ) ^ (m * n) * D4 (liftV t.1 p.1) (liftW t.2.1 p.2)
              (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f))))) := by
  have h1 : SwTerm t (pV t p) (pW t p) p f =
      (2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
          ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) *
        ∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
          (l2sq (restr (Qp (liftV t.1 (liftV (VrOf t) (pV t p))))
            (Ip (liftW t.2.1 (liftW (WrOf t) (pW t p))))
            (shift T' (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))) ^ 2 := rfl
  have hD4 : (∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
        (l2sq (Dop0S (liftV t.1 p.1) (liftW t.2.1 p.2) T' f)) ^ 2)
      = (2 : ℝ) ^ (m * n) * D4 (liftV t.1 p.1) (liftW t.2.1 p.2)
        (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f) := by
    rw [D4_Lsub_eq_sum_l2sq]
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ (m * n) ≠ 0), one_mul]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc (∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
        (l2sq (restr (Qp (liftV t.1 (liftV (VrOf t) (pV t p))))
          (Ip (liftW t.2.1 (liftW (WrOf t) (pW t p))))
          (shift T' (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))) ^ 2)
      ≤ ∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
          (2 : ℝ) ^ (4 * d * (XsOf t p).rank) *
            ((2 : ℝ) ^ (4 * d * d) *
              (2 * (l2sq (Dop0S (liftV t.1 p.1) (liftW t.2.1 p.2) T' f)) ^ 2)) :=
        Finset.sum_le_sum (fun T' _ => SwTerm_term_le t p hp hf T')
    _ = (2 : ℝ) ^ (4 * d * (XsOf t p).rank) *
          ((2 : ℝ) ^ (4 * d * d) *
            (2 * ∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
              (l2sq (Dop0S (liftV t.1 p.1) (liftW t.2.1 p.2) T' f)) ^ 2)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    _ = (2 : ℝ) ^ (4 * d * (XsOf t p).rank) *
          ((2 : ℝ) ^ (4 * d * d) *
            (2 * ((2 : ℝ) ^ (m * n) * D4 (liftV t.1 p.1) (liftW t.2.1 p.2)
              (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f)))) := by
        rw [hD4]

/-! ## The switching sum `SwSumP` -/

/-- `D4` at a pair is nonnegative (re-exported for convenience). -/
lemma D4_nonneg' {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    0 ≤ D4 V₁ W₁ f := D4_nonneg V₁ W₁ f

/-- **The switching sum is bounded by the weighted `D4`-terms of the reindexed pairs.** -/
theorem SwSumP_le (t : Triple m n) {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) :
    SwSumP t f d ≤
      ∑ p : QPair m n t,
        (if p.1 ⊓ VrOf t = ⊥ ∧ p.2 ⊔ WrOf t = ⊤ then
          (if SwGuard t d (pV t p) (pW t p) then
            (2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
                ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) *
              ((2 : ℝ) ^ (4 * d * (XsOf t p).rank) *
                ((2 : ℝ) ^ (4 * d * d) *
                  (2 * ((2 : ℝ) ^ (m * n) * D4 (liftV t.1 p.1) (liftW t.2.1 p.2)
                    (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f)))))
          else 0)
        else 0) := by
  refine Finset.sum_le_sum (fun p _ => ?_)
  by_cases hp : p.1 ⊓ VrOf t = ⊥ ∧ p.2 ⊔ WrOf t = ⊤
  · rw [if_pos hp, if_pos hp]
    by_cases hg : SwGuard t d (pV t p) (pW t p)
    · rw [if_pos hg, if_pos hg]
      exact SwTerm_le t p hp hf
    · rw [if_neg hg, if_neg hg]
  · rw [if_neg hp, if_neg hp]

/-- The weighted `D4`-sum of the switching terms: the `D4` of the reindexed pairs, weighted by
`q^{4d·rank X'}` (where `X' = XsOf t p` is the role-space matrix of the summand), and carrying
the normalising constants `q^{M'N'}` and `q^{mn}` of the switching step. -/
def SwWeightSum (t : Triple m n) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) : ℝ :=
  ∑ p : QPair m n t,
    (if p.1 ⊓ VrOf t = ⊥ ∧ p.2 ⊔ WrOf t = ⊤ then
      (if SwGuard t d (pV t p) (pW t p) then
        (2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
            ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) *
          ((2 : ℝ) ^ (4 * d * (XsOf t p).rank) *
            ((2 : ℝ) ^ (4 * d * d) *
              (2 * ((2 : ℝ) ^ (m * n) * D4 (liftV t.1 p.1) (liftW t.2.1 p.2)
                (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f)))))
      else 0) else 0)

lemma SwWeightSum_nonneg (t : Triple m n) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) :
    0 ≤ SwWeightSum t f d := by
  unfold SwWeightSum
  refine Finset.sum_nonneg (fun p _ => ?_)
  split
  · split
    · have hD4 : (0 : ℝ) ≤ D4 (liftV t.1 p.1) (liftW t.2.1 p.2)
          (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f) := D4_nonneg _ _ _
      positivity
    · exact le_refl 0
  · exact le_refl 0

/-- `SwSumP` is bounded by the weighted `D4`-sum (the guards only shrink the sum). -/
theorem SwSumP_le_weight (t : Triple m n) {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) :
    SwSumP t f d ≤ SwWeightSum t f d := by
  unfold SwWeightSum
  exact SwSumP_le t hf


/-! ## The per-triple bound

Collecting the two normalising constants `q^{M'N'}` and `q^{mn}` of `SwWeightSum` against the ones
produced by the induction step. -/

/-- **The `X`-derivative term of the induction step, bounded by the weighted `D4`-sum.**  The
switching-step factor is the *sharp* `2 ^ (3 d · rank X)` of `SwitchStep.stepD_bound_le_rank`. -/
theorem l4q_lapMulN_le_swWeight_rank (t : Triple m n) {C d : ℕ} (hIH : IHyp C (d - 1))
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f)
    (ht1 : 1 ≤ totOrder t) (htd : totOrder t ≤ d) :
    l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f)) ≤
      ((2 : ℝ) ^ (m * n))⁻¹ *
        ((2 : ℝ) ^ (C * (d - totOrder t) ^ 2) *
          (((2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
              ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))))⁻¹ *
            ((2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) *
              SwWeightSum t f d))) := by
  have hSw : (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, SwSum t T f d) = SwSumP t f d :=
    (Finset.sum_congr rfl (fun T _ => SwSum_eq_SwColl t T f d)).trans
      ((sum_SwColl_eq_SwFinal t f d).trans (SwFinal_eq_SwSumP t f d))
  have h3 : (∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
        l4q (DopXq (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f)) ≤
      (2 : ℝ) ^ (C * (d - totOrder t) ^ 2) *
        (((2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
            ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))))⁻¹ *
          ((2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) *
            SwWeightSum t f d)) := by
    have h4 : (2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) * SwSumP t f d ≤
        (2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) * SwWeightSum t f d :=
      mul_le_mul_of_nonneg_left (SwSumP_le_weight t hf)
        (show (0 : ℝ) ≤ (2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) by positivity)
    have h5 : ((2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
          ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))))⁻¹ *
          ((2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) * SwSumP t f d) ≤
        ((2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
          ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))))⁻¹ *
          ((2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) * SwWeightSum t f d) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have hmain := sum_l4q_DopXq_le_SwSum_rank (C := C) (d := d) hIH hf t ht1 htd
    rw [hSw] at hmain
    rw [rank_XtOf t.1 t.2.1 t.2.2] at hmain
    exact hmain.trans (mul_le_mul_of_nonneg_left h5
      (show (0 : ℝ) ≤ (2 : ℝ) ^ (C * (d - totOrder t) ^ 2) by positivity))
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (m * n) := by positivity
  calc l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f))
      = ((2 : ℝ) ^ (m * n))⁻¹ *
          ((2 : ℝ) ^ (m * n) * l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f))) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    _ = ((2 : ℝ) ^ (m * n))⁻¹ *
          (∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
            l4q (DopXq (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f)) := by
        rw [sum_l4q_DopXq_eq]
    _ ≤ ((2 : ℝ) ^ (m * n))⁻¹ *
          ((2 : ℝ) ^ (C * (d - totOrder t) ^ 2) *
            (((2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
                ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))))⁻¹ *
              ((2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) *
                SwWeightSum t f d))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

end
end Submission.Grassmann
