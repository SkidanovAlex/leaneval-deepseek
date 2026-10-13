/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `sin(2θ)²` family of the pointwise angular order transfer

This module proves

`Work.FTS.EllipticEst.TT.iterFamilyA_le`,

the pointwise companion of the order-transfer estimate `iter_le_of_lower_u`.  There the
Leibniz rule applied to `D_θ² u = A · u'' + B · D_θ u` (`A θ = sin(2θ)²`, `B θ = 2 cos 2θ`)
produces a binomial convolution of the squared iterates

  `∑_{j ≤ m} C(m,j)² · (D_θ^j A θ)² · (D_θ^{m-j} g θ)²`,

and the estimate below shows that — against the weight `sin(2θ)^{-γ}` — this whole sum is
dominated by the bracket

  `g(θ)² sin(2θ)^{-η} + ∑_{k < m} (D_θ^{k+1} g θ)² sin(2θ)^{-γ}`

(the `i = 0` term contributes the `η`-weight, every `i ≥ 1` term the `γ`-weight), with the
coefficient `∑_{j ≤ m} 4^m cA_j`.

The proof is elementary and uses no smoothness at all, only the three facts about the
weights on `θ ∈ (0, π/2)`:

* `1 ≤ sin(2θ)^{-γ}` and `1 ≤ sin(2θ)^{-η}` (`γ = 1 + α/10 ≥ 0`, `η = 99/100 ≥ 0`);
* `sin(2θ)⁴ · sin(2θ)^{-γ} = sin(2θ)^{4-γ} ≤ 1` (`4 - γ ≥ 0` for `α ≤ 1/4`);
* `C(m,j)² ≤ 4^m` (`C(m,j) ≤ 2^m`).

The certificate `hcA` is the (weight-free) pointwise bound `(D_θ^j sin(2θ)²)² ≤ cA_j
sin(2θ)⁴`; with it, step 1 factors the weight out of the sum, step 2 replaces `C(m,j)²` by
`4^m`, and step 3 replaces each `(D_θ^{m-j} g θ)²` by the bracket, which dominates *every*
`(D_θ^k g θ)²` with `k ≤ m` (that is what the `1 ≤` weight bounds are for) and is weighted
by the nonnegative coefficients `4^m cA_j`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## Weight bounds on the open interval `(0, π/2)` -/

/-- `sin(2θ)^{-γ} ≥ 1` on `(0, π/2)` (the exponent `-γ ≤ 0`, the base `sin(2θ) ≤ 1`). -/
private theorem one_le_sGam {α : ℝ} (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 1 ≤ sGam α θ := by
  have h0 : 0 < Real.sin (2 * θ) := sin_two_pos hθ.1 hθ.2
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgn : 0 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.gam_pos hα)
  have hz : -(Work.Spaces.gam α) ≤ 0 := by linarith
  calc (1 : ℝ) = (1 : ℝ) ^ (-(Work.Spaces.gam α)) := (Real.one_rpow _).symm
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        Real.rpow_le_rpow_of_nonpos h0 h1 hz
    _ = sGam α θ := rfl

/-- `sin(2θ)^{-η} ≥ 1` on `(0, π/2)` (the exponent `-η ≤ 0`, the base `sin(2θ) ≤ 1`). -/
private theorem one_le_sEta {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 1 ≤ sEta θ := by
  have h0 : 0 < Real.sin (2 * θ) := sin_two_pos hθ.1 hθ.2
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hz : -(Work.Spaces.eta) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  calc (1 : ℝ) = (1 : ℝ) ^ (-(Work.Spaces.eta)) := (Real.one_rpow _).symm
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_nonpos h0 h1 hz
    _ = sEta θ := rfl

/-- `sin(2θ)⁴ · sin(2θ)^{-γ} = sin(2θ)^{4-γ} ≤ 1` on `(0, π/2)`, because `α ≤ 1/4` gives
`4 - γ ≥ 0` while `0 < sin(2θ) ≤ 1`. -/
private theorem sGam_mul_sin_pow_four_le_one {α : ℝ} (hα4 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    sGam α θ * (Real.sin (2 * θ)) ^ 4 ≤ 1 := by
  have h0 : 0 < Real.sin (2 * θ) := sin_two_pos hθ.1 hθ.2
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : 0 ≤ 4 - Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hrw : sGam α θ * (Real.sin (2 * θ)) ^ 4
      = (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by
    have hx : (Real.sin (2 * θ)) ^ 4 = (Real.sin (2 * θ)) ^ (4 : ℝ) :=
      (Real.rpow_natCast (Real.sin (2 * θ)) 4).symm
    calc sGam α θ * (Real.sin (2 * θ)) ^ 4
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Real.sin (2 * θ)) ^ (4 : ℝ) := by rw [sGam, hx]
      _ = (Real.sin (2 * θ)) ^ ((-(Work.Spaces.gam α)) + 4) :=
          (Real.rpow_add h0 (-(Work.Spaces.gam α)) 4).symm
      _ = (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by
          rw [show (-(Work.Spaces.gam α)) + 4 = 4 - Work.Spaces.gam α by ring]
  rw [hrw]
  exact Real.rpow_le_one (le_of_lt h0) h1 hexp

/-! ## The binomial coefficient bound -/

/-- `C(m,j)² ≤ 4^m`, from `C(m,j) ≤ 2^m`. -/
private theorem choose_sq_le_four_pow (m j : ℕ) :
    ((m.choose j : ℝ)) ^ 2 ≤ (4 : ℝ) ^ m := by
  have hcj : (m.choose j : ℝ) ≤ (2 : ℝ) ^ m := by
    have h := Nat.choose_le_two_pow m j
    calc (m.choose j : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h
      _ = (2 : ℝ) ^ m := by push_cast; ring
  calc ((m.choose j : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ m) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hcj 2
    _ = (4 : ℝ) ^ m := by rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, sq]

/-! ## The estimate -/

theorem iterFamilyA_le {cA : ℕ → ℝ}
    (hcA : ∀ j θ, (Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
      ≤ cA j * (Real.sin (2 * θ)) ^ 4)
    (hcAnn : ∀ j, 0 ≤ cA j) (m : ℕ) (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (g : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ)) ^ 2 *
        ((Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
          * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2))
      * Work.FTS.EllipticEst.sGam α θ
      ≤ (∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cA j) *
        ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          + ∑ k ∈ Finset.range m,
              (Work.Elliptic.Dth1Iter (k + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) := by
  have hW1 : 1 ≤ Work.FTS.EllipticEst.sGam α θ := one_le_sGam hα hθ
  have hW0 : 0 ≤ Work.FTS.EllipticEst.sGam α θ := le_trans zero_le_one hW1
  have hE1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta hθ
  have hE0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := le_trans zero_le_one hE1
  have hs4 : (Real.sin (2 * θ)) ^ 4 * Work.FTS.EllipticEst.sGam α θ ≤ 1 := by
    rw [mul_comm]; exact sGam_mul_sin_pow_four_le_one hα4 hθ
  have hsum_nn : 0 ≤ ∑ k ∈ Finset.range m,
      (Work.Elliptic.Dth1Iter (k + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ :=
    Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) hW0
  -- every `(D_θ^k g θ)²`, `k ≤ m`, is dominated by the bracket of the statement
  have hB : ∀ k ≤ m, (Work.Elliptic.Dth1Iter k g θ) ^ 2
      ≤ (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + ∑ k' ∈ Finset.range m,
            (Work.Elliptic.Dth1Iter (k' + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Work.Elliptic.Dth1Iter_zero]
      have h1 : (g θ) ^ 2 ≤ (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        calc (g θ) ^ 2 = (g θ) ^ 2 * 1 := (mul_one _).symm
          _ ≤ (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
              mul_le_mul_of_nonneg_left hE1 (sq_nonneg _)
      exact le_trans h1 (le_add_of_nonneg_right hsum_nn)
    · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      subst hk'
      have hkm : k' < m := by omega
      have hmem : k' ∈ Finset.range m := Finset.mem_range.mpr hkm
      have h1 : (Work.Elliptic.Dth1Iter (k' + 1) g θ) ^ 2
          ≤ ∑ k'' ∈ Finset.range m,
              (Work.Elliptic.Dth1Iter (k'' + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ := by
        calc (Work.Elliptic.Dth1Iter (k' + 1) g θ) ^ 2
            = (Work.Elliptic.Dth1Iter (k' + 1) g θ) ^ 2 * 1 := (mul_one _).symm
          _ ≤ (Work.Elliptic.Dth1Iter (k' + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ :=
              mul_le_mul_of_nonneg_left hW1 (sq_nonneg _)
          _ ≤ ∑ k'' ∈ Finset.range m,
              (Work.Elliptic.Dth1Iter (k'' + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ :=
              Finset.single_le_sum (f := fun k'' =>
                (Work.Elliptic.Dth1Iter (k'' + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ)
                (fun k'' _ => mul_nonneg (sq_nonneg _) hW0) hmem
      exact le_trans h1 (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) hE0))
  -- step 1: pull `sGam` inside and use the certificate `hcA`
  have hstep1 : (∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ)) ^ 2 *
        ((Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
          * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2))
      * Work.FTS.EllipticEst.sGam α θ
      ≤ ∑ j ∈ Finset.range (m + 1),
          ((m.choose j : ℝ)) ^ 2 * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro j hj
    have hAj := hcA j θ
    have hcAj := hcAnn j
    have hCn : 0 ≤ ((m.choose j : ℝ)) ^ 2 := sq_nonneg _
    have hB2 : 0 ≤ (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2 := sq_nonneg _
    calc ((m.choose j : ℝ)) ^ 2 *
            ((Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
              * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2)
            * Work.FTS.EllipticEst.sGam α θ
        ≤ ((m.choose j : ℝ)) ^ 2 *
            ((cA j * (Real.sin (2 * θ)) ^ 4)
              * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2)
            * Work.FTS.EllipticEst.sGam α θ := by
          refine mul_le_mul_of_nonneg_right ?_ hW0
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAj hB2) hCn
      _ = ((m.choose j : ℝ)) ^ 2 * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2
            * ((Real.sin (2 * θ)) ^ 4 * Work.FTS.EllipticEst.sGam α θ) := by ring
      _ ≤ ((m.choose j : ℝ)) ^ 2 * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hs4 (mul_nonneg (mul_nonneg hCn hcAj) hB2)
      _ = ((m.choose j : ℝ)) ^ 2 * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2 :=
          mul_one _
  -- step 2: `C(m,j)² ≤ 4^m`
  have hstep2 : (∑ j ∈ Finset.range (m + 1),
          ((m.choose j : ℝ)) ^ 2 * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2)
      ≤ ∑ j ∈ Finset.range (m + 1),
          (4 : ℝ) ^ m * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (choose_sq_le_four_pow m j) (hcAnn j)) (sq_nonneg _)
  -- step 3: replace the remaining iterate by the bracket
  have hstep3 : (∑ j ∈ Finset.range (m + 1),
          (4 : ℝ) ^ m * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2)
      ≤ (∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cA j) *
        ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          + ∑ k ∈ Finset.range m,
              (Work.Elliptic.Dth1Iter (k + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro j hj
    have hcnn : 0 ≤ (4 : ℝ) ^ m * cA j :=
      mul_nonneg (pow_nonneg (by norm_num) m) (hcAnn j)
    exact mul_le_mul_of_nonneg_left (hB (m - j) (Nat.sub_le m j)) hcnn
  exact le_trans hstep1 (le_trans hstep2 hstep3)

end Work.FTS.EllipticEst.TT
