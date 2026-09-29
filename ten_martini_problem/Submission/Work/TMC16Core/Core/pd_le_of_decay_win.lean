import Mathlib
import Submission.Work.TMC16Core.Core.windows
import Submission.Work.TMC16Core.Basic.poisson_bound
import Submission.Work.TMC16Core.Basic.cramer
import Submission.Work.TMC16Core.Basic.dirMat_det
import Submission.Work.TMC16Core.Basic.green_bound_reg

/-!
# `pd_le_of_decay_win` — Poisson/Cramér with the continuant bound restricted to `n₀ ≤ m`

This is the `n₀`-restricted form of `Work.Core.pd_le_of_decay` (AJ §9): for a formal solution
`u` of `H u = E u` with `u 0 = 1`, whose values at the two sites just outside a window
`[x, x₂] ∋ 0` are bounded by `B`, and whose continuants of length `≤ K` are bounded by
`e^{m (L + ε₁)}` **for the scales `m ≥ n₀` only**, the continuant of the full window is
bounded by `B (e^{(x₂-0)(L+ε₁)} + e^{(0-x)(L+ε₁)})`.

The Poisson bound gives `1 = ‖u 0‖ ≤ B (‖G(0,x)‖ + ‖G(0,x₂)‖)`; Cramér's rule writes the
Green's entries as ratios of continuants of the complementary windows, whose lengths are
exactly `(x₂ - 0).toNat` and `(0 - x).toNat`, and the hypotheses `hn1`, `hn2` say that these
two scales are `≥ n₀`, so the restricted bound `hbd` applies at them.  No other scale is
ever used, which is why the hypothesis may be restricted: this matters for small `λ`, where
the bound is simply false at scale `m = 0` (see the design notes of `Core/pd_window`).
-/

noncomputable section

namespace Work.TMC16Core.Core

/-- **The continuant of a window containing `0` is bounded by the decay of the solution at the
two ends** (restricted-scale form). -/
theorem pd_le_of_decay_win {α lam L ε₁ B : ℝ} {E : ℂ} {θ : ℝ} {u : ℤ → ℂ} {K : ℕ} {x x₂ : ℤ}
    {n₀ : ℕ}
    (hB : 0 < B) (hx₂ : x₂ = x + (K : ℤ) - 1)
    (hbd : ∀ m : ℕ, n₀ ≤ m → m ≤ K → ∀ ζ : ℝ,
      ‖Work.TMC16Core.pd α lam ζ E (m + 1)‖ ≤ Real.exp ((m : ℝ) * (L + ε₁)))
    (hm1 : (x₂ - 0).toNat ≤ K) (hm2 : (0 - x).toNat ≤ K)
    (hn1 : n₀ ≤ (x₂ - 0).toNat) (hn2 : n₀ ≤ (0 - x).toNat)
    (hsol : Work.TMC16Core.IsFormalSol α lam θ E u) (hu0 : u 0 = 1)
    (hdec1 : ‖u (x - 1)‖ ≤ B) (hdec2 : ‖u (x₂ + 1)‖ ≤ B)
    (hneg : x ≤ 0) (hpos : 0 ≤ x₂)
    (hP : Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1) ≠ 0) :
    ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
      B * (Real.exp (((x₂ - 0).toNat : ℝ) * (L + ε₁))
            + Real.exp (((0 - x).toNat : ℝ) * (L + ε₁))) := by
  have hsize : (x₂ - x + 1).toNat = K := by
    rw [hx₂]
    have h : x + (K : ℤ) - 1 - x + 1 = (K : ℤ) := by ring
    rw [h, Int.toNat_natCast]
  have hsize2 : (x₂ - x + 1).toNat + 1 = K + 1 := by rw [hsize]
  have hdet : (Work.TMC16Core.dirMat α lam (θ + (x : ℝ) * α) E (x₂ - x + 1).toNat).det ≠ 0 := by
    rw [hsize, Work.TMC16Core.Basic.dirMat_det]
    intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (by norm_num))
    · exact hP h1
  have hPoi := Work.TMC16Core.Basic.poisson_bound (x₁ := x) (x₂ := x₂) (y := 0)
    hsol hdet hneg hpos
  have hsum : (1 : ℝ) ≤
      (‖Work.TMC16Core.G α lam θ E x x₂ 0 x‖ +
        ‖Work.TMC16Core.G α lam θ E x x₂ 0 x₂‖) * B := by
    calc (1 : ℝ) = ‖u 0‖ := by rw [hu0, norm_one]
      _ ≤ ‖Work.TMC16Core.G α lam θ E x x₂ 0 x‖ * ‖u (x - 1)‖
            + ‖Work.TMC16Core.G α lam θ E x x₂ 0 x₂‖ * ‖u (x₂ + 1)‖ := hPoi
      _ ≤ ‖Work.TMC16Core.G α lam θ E x x₂ 0 x‖ * B
            + ‖Work.TMC16Core.G α lam θ E x x₂ 0 x₂‖ * B :=
            add_le_add (mul_le_mul_of_nonneg_left hdec1 (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hdec2 (norm_nonneg _))
      _ = (‖Work.TMC16Core.G α lam θ E x x₂ 0 x‖ +
            ‖Work.TMC16Core.G α lam θ E x x₂ 0 x₂‖) * B := by ring
  obtain ⟨hcr1, hcr2⟩ := Work.TMC16Core.Basic.cramer α lam θ E x x₂ 0 hneg hpos
  have hsym : ‖Work.TMC16Core.G α lam θ E x x₂ 0 x‖ =
      ‖Work.TMC16Core.G α lam θ E x x₂ x 0‖ := by
    rw [Work.TMC16Core.Basic.G_symm_local (x := 0) (y := x)]
  have hG1 : ‖Work.TMC16Core.G α lam θ E x x₂ 0 x‖ =
      ‖Work.TMC16Core.pd α lam (θ + α) E ((x₂ - 0).toNat + 1)‖
        / ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ := by
    rw [hsym, hcr1, hsize2, norm_div]
    congr 2
    ring_nf
  have hG2 : ‖Work.TMC16Core.G α lam θ E x x₂ 0 x₂‖ =
      ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E ((0 - x).toNat + 1)‖
        / ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ := by
    rw [hcr2, hsize2, norm_div]
  have hN1 : ‖Work.TMC16Core.pd α lam (θ + α) E ((x₂ - 0).toNat + 1)‖
      ≤ Real.exp (((x₂ - 0).toNat : ℝ) * (L + ε₁)) := hbd (x₂ - 0).toNat hn1 hm1 (θ + α)
  have hN2 : ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E ((0 - x).toNat + 1)‖
      ≤ Real.exp (((0 - x).toNat : ℝ) * (L + ε₁)) :=
        hbd (0 - x).toNat hn2 hm2 (θ + (x : ℝ) * α)
  have hPpos : 0 < ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ := by
    rw [norm_pos_iff]; exact hP
  have ha : ‖Work.TMC16Core.pd α lam (θ + α) E ((x₂ - 0).toNat + 1)‖
        / ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖
      + ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E ((0 - x).toNat + 1)‖
        / ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖
      ≤ (Real.exp (((x₂ - 0).toNat : ℝ) * (L + ε₁))
          + Real.exp (((0 - x).toNat : ℝ) * (L + ε₁)))
        / ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ := by
    rw [add_div]
    exact add_le_add (div_le_div_of_nonneg_right hN1 (norm_nonneg _))
      (div_le_div_of_nonneg_right hN2 (norm_nonneg _))
  have hkey : (1 : ℝ) ≤ (Real.exp (((x₂ - 0).toNat : ℝ) * (L + ε₁))
      + Real.exp (((0 - x).toNat : ℝ) * (L + ε₁))) * B
      / ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ := by
    calc (1 : ℝ) ≤ (‖Work.TMC16Core.G α lam θ E x x₂ 0 x‖ +
          ‖Work.TMC16Core.G α lam θ E x x₂ 0 x₂‖) * B := hsum
      _ = (‖Work.TMC16Core.pd α lam (θ + α) E ((x₂ - 0).toNat + 1)‖
            / ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖
            + ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E ((0 - x).toNat + 1)‖
              / ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖) * B := by rw [hG1, hG2]
      _ ≤ ((Real.exp (((x₂ - 0).toNat : ℝ) * (L + ε₁))
            + Real.exp (((0 - x).toNat : ℝ) * (L + ε₁)))
              / ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖) * B :=
            mul_le_mul_of_nonneg_right ha (le_of_lt hB)
      _ = (Real.exp (((x₂ - 0).toNat : ℝ) * (L + ε₁))
            + Real.exp (((0 - x).toNat : ℝ) * (L + ε₁))) * B
            / ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ := by ring
  have hfin := (le_div_iff₀ hPpos).mp hkey
  rw [one_mul] at hfin
  linarith [hfin]

end Work.TMC16Core.Core
