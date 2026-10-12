import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxSliding.Geom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Real
open Submission.BoseGases

namespace Work.BoseSWE

/-- The `ℓ`-scale corpus bump localises in the ball of radius `ℓ/2`: if `chiScale ℓ x ≠ 0`
then `‖x‖ < ℓ/2`.  (Converse form of the corpus `chi_eq_zero_of_half_le_norm`, at scale `ℓ`.) -/
lemma chiScale_ne_zero_norm_aux {ℓ : ℝ} (hℓ : 0 < ℓ) {x : EuclideanSpace ℝ (Fin 3)}
    (h : Submission.BoseGases.chiScale ℓ x ≠ 0) : ‖x‖ < ℓ / 2 := by
  have h2 : chi (ℓ⁻¹ • x) ≠ 0 := h
  have hlt : ‖ℓ⁻¹ • x‖ < 1 / 2 := by
    by_contra hcon
    exact h2 (chi_eq_zero_of_half_le_norm _ (le_of_not_gt hcon))
  have hnorm : ‖ℓ⁻¹ • x‖ = ‖x‖ / ℓ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ, div_eq_inv_mul, mul_comm]
  rw [hnorm] at hlt
  have := (div_lt_iff₀ hℓ).mp hlt
  linarith

/-- **Geometry of the sliding cutoff: two clipped coordinates kill the cutoff.**
The sliding box `B(u) = dlBox ℓ d u` is clipped in the coordinate `j` exactly when
`shortSide ℓ d u j < ℓ d`.  If it is clipped in two *distinct* coordinates, then the two-factor
cutoff `chiSmallB M ℓ d u` vanishes identically, provided `8 d ≤ 1`.

Reason: `chiSmallB M ℓ d u x ≠ 0` forces `‖x‖ < ℓ/2` (the `χ(x/ℓ)` factor is the *ball*-supported
corpus bump `chiScale ℓ`) and `|x_i - ((ℓd)•u)_i| ≤ ℓd/2` for every `i` (the `ℓd`-scale cosine
factor).  Clipping in coordinate `j` means `½ℓ(1+d) - |((ℓd)•u)_j| < ℓd`, i.e.
`|((ℓd)•u)_j| > ℓ/2 - ℓd/2`, so `|x_j| > ℓ/2 - ℓd`.  With two distinct clipped coordinates,
`‖x‖² ≥ x_j² + x_{j'}² > 2 (ℓ/2 - ℓd)² ≥ ℓ²/4` when `8 d ≤ 1` (`ℓ/2 - ℓd ≥ 3ℓ/8`), contradicting
`‖x‖ < ℓ/2`. -/
theorem chiSmallB_eq_zero_of_two_clip {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hd8 : 8 * d ≤ 1) {u x : EuclideanSpace ℝ (Fin 3)}
    (hclip : ∃ j j' : Fin 3, j ≠ j' ∧
      Work.SmallBoxSliding.shortSide ℓ d u j < ℓ * d ∧
      Work.SmallBoxSliding.shortSide ℓ d u j' < ℓ * d) :
    Submission.BoseGases.chiSmallB M ℓ d u x = 0 := by
  by_contra hx
  obtain ⟨j, j', hjj, hcj, hcj'⟩ := hclip
  -- `d ≤ 1/8`, hence the two clipped coordinates already force `‖x‖² > ℓ²/4`.
  have hle : d ≤ 1 / 8 := by linarith
  have h3 : 0 ≤ 3 * ℓ / 8 := by linarith
  have hs3 : 3 * ℓ / 8 ≤ ℓ / 2 - ℓ * d := by nlinarith
  -- the `ℓ`-scale factor confines `x` to the ball of radius `ℓ/2`
  have hball : ‖x‖ < ℓ / 2 := by
    have h1 : Submission.BoseGases.chiScale ℓ x ≠ 0 := by
      intro h
      exact hx (by rw [Submission.BoseGases.chiSmallB, h, zero_mul])
    exact chiScale_ne_zero_norm_aux hℓ h1
  -- clipping in coordinate `k` pushes `|x_k|` above `ℓ/2 - ℓd`
  have hkey : ∀ k : Fin 3, Work.SmallBoxSliding.shortSide ℓ d u k < ℓ * d →
      ℓ / 2 - ℓ * d < |x.ofLp k| := by
    intro k hk
    have hAk : (1 / 2) * ℓ * (1 + d) - |((ℓ * d) • u).ofLp k| < ℓ * d := by
      have h := hk
      rw [Work.SmallBoxSliding.shortSide] at h
      rw [min_lt_iff] at h
      rcases h with h | h
      · exact absurd h (lt_irrefl _)
      · exact h
    have hwk : ℓ / 2 - ℓ * d / 2 < |((ℓ * d) • u).ofLp k| := by linarith
    have hsk : |(x - (ℓ * d) • u).ofLp k| ≤ ℓ * d / 2 :=
      Submission.BoseGases.chiSmallB_support_small_box_dist hM hℓ hd hx k
    have htri : |((ℓ * d) • u).ofLp k| - |x.ofLp k| ≤ |(x - (ℓ * d) • u).ofLp k| := by
      have h1 := abs_sub_abs_le_abs_sub (((ℓ * d) • u).ofLp k) (x.ofLp k)
      rw [abs_sub_comm] at h1
      simpa [PiLp.sub_apply] using h1
    linarith
  have hj := hkey j hcj
  have hj' := hkey j' hcj'
  -- squared lower bound on the two clipped coordinates
  have hsq : 2 * (3 * ℓ / 8) ^ 2 < (x.ofLp j) ^ 2 + (x.ofLp j') ^ 2 := by
    have h1 : (3 * ℓ / 8) ^ 2 < (x.ofLp j) ^ 2 := by
      rw [← sq_abs (x.ofLp j)]
      exact pow_lt_pow_left₀ (lt_of_le_of_lt hs3 hj) h3 (by norm_num)
    have h2 : (3 * ℓ / 8) ^ 2 < (x.ofLp j') ^ 2 := by
      rw [← sq_abs (x.ofLp j')]
      exact pow_lt_pow_left₀ (lt_of_le_of_lt hs3 hj') h3 (by norm_num)
    linarith
  have hnorm : ‖x‖ ^ 2 < (ℓ / 2) ^ 2 := by
    nlinarith [norm_nonneg x, hℓ]
  have hxy : (ℓ / 2) ^ 2 < (x.ofLp j) ^ 2 + (x.ofLp j') ^ 2 := by
    have hℓ2 : 0 < ℓ ^ 2 := pow_pos hℓ 2
    nlinarith [hsq, hℓ2]
  -- the two coordinates are subordinate to the norm
  have hsum : ‖x‖ ^ 2 = ∑ i : Fin 3, (x.ofLp i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  have hpair : (x.ofLp j) ^ 2 + (x.ofLp j') ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hsum]
    have hsub : ({j, j'} : Finset (Fin 3)) ⊆ Finset.univ := Finset.subset_univ _
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i : Fin 3 => (x.ofLp i) ^ 2)
      hsub (fun i _ _ => by positivity)
    rw [Finset.sum_pair hjj] at h
    exact h
  linarith

end Work.BoseSWE
