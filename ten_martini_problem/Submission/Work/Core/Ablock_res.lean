import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.windows
import Submission.Work.TMC16Core.Basic.lemma_9_2
import Submission.Work.TMC16Core.Basic.poisson_bound
import Submission.Work.TMC16Core.Basic.cramer
import Submission.Work.TMC16Core.Basic.dirMat_det
import Submission.Work.TMC16Core.Basic.green_bound_reg

/-!
# `Work.Core.Ablock_res` — the resonant `A`-block (AJ Lemma 9.11)

For a resonant scale `K = 2q_n - 1`, AJ's Lemma 9.11 produces an interval
`A = [-13q_n/8, -3q_n/8] = [-13(K+1)/16, -3(K+1)/16]` of phases whose continuants
`P_K` are bounded by `e^{(K+1)(23L/32+ε)}`, out of the *decay of the generalized
eigenfunction* at the two ends of the window: this is the estimate that cannot be obtained
from the singularity of `0` alone (Lemma 9.2) and is the reason the non-resonant and the
resonant subsections of AJ §9 are not independent.

Two ingredients suffice.

* (non-degenerate case, `L + ε₁ ≥ 0`) Poisson's formula with Cramér's rule:
  `1 = ‖u 0‖ ≤ B(‖G(0,x)‖ + ‖G(0,x₂)‖)`, and `‖G(0,·)‖·‖P_K(θ+xα)‖` is the continuant of
  the complementary window, hence
  `‖P_K‖ ≤ B(e^{(x+K-1)(L+ε₁)} + e^{-x(L+ε₁)}) ≤ 2B e^{(13K/16)(L+ε₁)} ≤ e^{(K+1)(23L/32+ε)}`
  by the numerical hypothesis `hnum` (both exponents are `≤ 13K/16` because `x ∈ A` and
  `x + K - 1 ≤ -3K/16 + K - 1`).
* (degenerate case, `L + ε₁ < 0`) all continuants shrink, so the *trivial* bound
  `‖P_K(θ+xα)‖ ≤ e^{K(L+ε₁)}` already suffices once `B ≥ 1/2`; and `B ≥ 1/2` is forced by
  reconstructing the solution from two *consecutive* decaying sites (`sol_recon`), whose
  coefficients are `≤ 1` in this regime.

## The reconstruction lemma

`sol_recon` is the transfer-matrix identity
`u (a+n) = P_n(a)·u a - P_{n-1}(a+1)·u (a-1)`, proved by two-step induction from the
three-term recursion.  It is the only place where the equation of motion `hsol` is used.
-/

namespace Work.Core

open Work.TMC16Core

/-! ## Auxiliary lemmas -/

/-- Phase/site shift of the potential: shifting the phase by `jα` shifts the site by `j`. -/
lemma amoPot_shiftZ (α lam φ : ℝ) (j n : ℤ) :
    amoPot α lam (φ + (j : ℝ) * α) n = amoPot α lam φ (n + j) := by
  simp only [amoPot]
  rw [show 2 * Real.pi * (φ + (j : ℝ) * α + (n : ℝ) * α)
      = 2 * Real.pi * (φ + ((n + j : ℤ) : ℝ) * α) by push_cast; ring]

/-- The defining recursion of the continuant. -/
lemma pd_rec (α lam φ : ℝ) (E : ℂ) (m : ℕ) :
    pd α lam φ E (m + 2) =
      (E - ((amoPot α lam φ (m : ℤ) : ℝ) : ℂ)) * pd α lam φ E (m + 1) - pd α lam φ E m := by
  rw [pd]

lemma pd_zero_l (α lam θ : ℝ) (E : ℂ) : pd α lam θ E 0 = 0 := rfl

lemma pd_one_l (α lam θ : ℝ) (E : ℂ) : pd α lam θ E 1 = 1 := rfl

/-- The three-term recursion of a formal solution. -/
lemma sol_step {α lam : ℝ} {θ : ℝ} {E : ℂ} {u : ℤ → ℂ}
    (hsol : IsFormalSol α lam θ E u) (m : ℤ) :
    u (m + 1) = (E - ((amoPot α lam θ m : ℝ) : ℂ)) * u m - u (m - 1) := by
  have h := hsol m
  simp only [IsFormalSol, amoAct] at h
  linear_combination h

/-- **Reconstruction of a formal solution from two consecutive values.**  For any solution of
the almost Mathieu equation, any `a : ℤ` and any `n : ℕ`,
`u (a+n) = P_n(a)·u a - P_{n-1}(a+1)·u (a-1)`. -/
lemma sol_recon {α lam : ℝ} {θ : ℝ} {E : ℂ} {u : ℤ → ℂ}
    (hsol : IsFormalSol α lam θ E u) (a : ℤ) :
    ∀ n : ℕ, u (a + n) =
      pd α lam (θ + (a : ℝ) * α) E (n + 1) * u a
        - pd α lam (θ + ((a + 1 : ℤ) : ℝ) * α) E n * u (a - 1) := by
  refine Nat.twoStepInduction ?_ ?_ ?_
  · show u (a + ((0 : ℕ) : ℤ)) =
      pd α lam (θ + (a : ℝ) * α) E (0 + 1) * u a
        - pd α lam (θ + ((a + 1 : ℤ) : ℝ) * α) E 0 * u (a - 1)
    rw [show a + ((0 : ℕ) : ℤ) = a by omega, pd_one_l, pd_zero_l]
    ring
  · show u (a + ((1 : ℕ) : ℤ)) =
      pd α lam (θ + (a : ℝ) * α) E (1 + 1) * u a
        - pd α lam (θ + ((a + 1 : ℤ) : ℝ) * α) E 1 * u (a - 1)
    have hpd2 : pd α lam (θ + (a : ℝ) * α) E (1 + 1) =
        E - ((amoPot α lam (θ + (a : ℝ) * α) ((0 : ℕ) : ℤ) : ℝ) : ℂ) := by
      rw [show (1 : ℕ) + 1 = 0 + 2 by omega, pd_rec, pd_one_l, pd_zero_l, mul_one,
        sub_zero]
    have hph : amoPot α lam (θ + (a : ℝ) * α) ((0 : ℕ) : ℤ) = amoPot α lam θ a := by
      have h := amoPot_shiftZ α lam θ a ((0 : ℕ) : ℤ)
      rw [show ((0 : ℕ) : ℤ) + a = a by omega] at h
      exact h
    rw [show a + ((1 : ℕ) : ℤ) = a + 1 by omega, hpd2, hph, pd_one_l, one_mul]
    exact sol_step hsol a
  · intro n ih0 ih1
    have hstep := sol_step hsol (a + (n : ℤ) + 1)
    have e1 : a + ((n + 2 : ℕ) : ℤ) = (a + (n : ℤ) + 1) + 1 := by push_cast; ring
    have e2 : (a + (n : ℤ) + 1) - 1 = a + (n : ℤ) := by ring
    rw [e1, hstep, e2]
    have hA : u (a + (n : ℤ) + 1) =
        pd α lam (θ + (a : ℝ) * α) E (n + 2) * u a
          - pd α lam (θ + ((a + 1 : ℤ) : ℝ) * α) E (n + 1) * u (a - 1) := by
      have h := ih1
      rwa [show a + ((n + 1 : ℕ) : ℤ) = a + (n : ℤ) + 1 by push_cast; ring] at h
    rw [hA, ih0]
    have hr1 : pd α lam (θ + (a : ℝ) * α) E (n + 3) =
        (E - ((amoPot α lam θ (a + (n : ℤ) + 1) : ℝ) : ℂ))
          * pd α lam (θ + (a : ℝ) * α) E (n + 2)
          - pd α lam (θ + (a : ℝ) * α) E (n + 1) := by
      rw [show (n + 3 : ℕ) = (n + 1) + 2 by omega, pd_rec]
      congr 2
      rw [amoPot_shiftZ]
      congr 1
      push_cast
      ring
    have hr2 : pd α lam (θ + ((a + 1 : ℤ) : ℝ) * α) E (n + 2) =
        (E - ((amoPot α lam θ (a + (n : ℤ) + 1) : ℝ) : ℂ))
          * pd α lam (θ + ((a + 1 : ℤ) : ℝ) * α) E (n + 1)
          - pd α lam (θ + ((a + 1 : ℤ) : ℝ) * α) E n := by
      rw [show (n + 2 : ℕ) = n + 2 by omega, pd_rec]
      congr 2
      rw [amoPot_shiftZ]
      congr 1
      push_cast
      ring
    rw [hr1, hr2]
    ring_nf

/-! ## Poisson + Cramér -/

/-- **The continuant of a window containing `0` is bounded by the decay of the solution at the
two ends.**  If `u` solves the equation with `u 0 = 1`, `‖u‖ ≤ B` at the two sites just
outside `[x, x₂] ∋ 0`, and the continuants of length `≤ K` are bounded by `e^{m(L+ε₁)}`, then
`‖P_K(θ+xα)‖ ≤ B(e^{(x₂-0)(L+ε₁)} + e^{(0-x)(L+ε₁)})`. -/
lemma pd_le_of_decay {α lam L ε₁ B : ℝ} {E : ℂ} {θ : ℝ} {u : ℤ → ℂ} {K : ℕ} {x x₂ : ℤ}
    (hB : 0 < B) (hx₂ : x₂ = x + (K : ℤ) - 1)
    (hbd : ∀ m : ℕ, m ≤ K → ∀ ζ : ℝ,
      ‖pd α lam ζ E (m + 1)‖ ≤ Real.exp ((m : ℝ) * (L + ε₁)))
    (hsol : IsFormalSol α lam θ E u) (hu0 : u 0 = 1)
    (hdec1 : ‖u (x - 1)‖ ≤ B) (hdec2 : ‖u (x₂ + 1)‖ ≤ B)
    (hneg : x ≤ 0) (hpos : 0 ≤ x₂)
    (hm1 : (x₂ - 0).toNat ≤ K) (hm2 : (0 - x).toNat ≤ K)
    (hP : pd α lam (θ + (x : ℝ) * α) E (K + 1) ≠ 0) :
    ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
      B * (Real.exp (((x₂ - 0).toNat : ℝ) * (L + ε₁))
            + Real.exp (((0 - x).toNat : ℝ) * (L + ε₁))) := by
  have hsize : (x₂ - x + 1).toNat = K := by
    rw [hx₂]
    have h : x + (K : ℤ) - 1 - x + 1 = (K : ℤ) := by ring
    rw [h, Int.toNat_natCast]
  have hsize2 : (x₂ - x + 1).toNat + 1 = K + 1 := by rw [hsize]
  have hdet : (dirMat α lam (θ + (x : ℝ) * α) E (x₂ - x + 1).toNat).det ≠ 0 := by
    rw [hsize, Work.TMC16Core.Basic.dirMat_det]
    intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (by norm_num))
    · exact hP h1
  have hPoi := Work.TMC16Core.Basic.poisson_bound (x₁ := x) (x₂ := x₂) (y := 0)
    hsol hdet hneg hpos
  have hsum : (1 : ℝ) ≤
      (‖G α lam θ E x x₂ 0 x‖ + ‖G α lam θ E x x₂ 0 x₂‖) * B := by
    calc (1 : ℝ) = ‖u 0‖ := by rw [hu0, norm_one]
      _ ≤ ‖G α lam θ E x x₂ 0 x‖ * ‖u (x - 1)‖
            + ‖G α lam θ E x x₂ 0 x₂‖ * ‖u (x₂ + 1)‖ := hPoi
      _ ≤ ‖G α lam θ E x x₂ 0 x‖ * B + ‖G α lam θ E x x₂ 0 x₂‖ * B :=
            add_le_add (mul_le_mul_of_nonneg_left hdec1 (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hdec2 (norm_nonneg _))
      _ = (‖G α lam θ E x x₂ 0 x‖ + ‖G α lam θ E x x₂ 0 x₂‖) * B := by ring
  obtain ⟨hcr1, hcr2⟩ := Work.TMC16Core.Basic.cramer α lam θ E x x₂ 0 hneg hpos
  have hsym : ‖G α lam θ E x x₂ 0 x‖ = ‖G α lam θ E x x₂ x 0‖ := by
    rw [Work.TMC16Core.Basic.G_symm_local (x := 0) (y := x)]
  have hG1 : ‖G α lam θ E x x₂ 0 x‖ =
      ‖pd α lam (θ + α) E ((x₂ - 0).toNat + 1)‖
        / ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ := by
    rw [hsym, hcr1, hsize2, norm_div]
    congr 2
    ring_nf
  have hG2 : ‖G α lam θ E x x₂ 0 x₂‖ =
      ‖pd α lam (θ + (x : ℝ) * α) E ((0 - x).toNat + 1)‖
        / ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ := by
    rw [hcr2, hsize2, norm_div]
  have hN1 : ‖pd α lam (θ + α) E ((x₂ - 0).toNat + 1)‖
      ≤ Real.exp (((x₂ - 0).toNat : ℝ) * (L + ε₁)) := hbd (x₂ - 0).toNat hm1 (θ + α)
  have hN2 : ‖pd α lam (θ + (x : ℝ) * α) E ((0 - x).toNat + 1)‖
      ≤ Real.exp (((0 - x).toNat : ℝ) * (L + ε₁)) := hbd (0 - x).toNat hm2 (θ + (x : ℝ) * α)
  have hPpos : 0 < ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ := by
    rw [norm_pos_iff]; exact hP
  have ha : ‖pd α lam (θ + α) E ((x₂ - 0).toNat + 1)‖
        / ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖
      + ‖pd α lam (θ + (x : ℝ) * α) E ((0 - x).toNat + 1)‖
        / ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖
      ≤ (Real.exp (((x₂ - 0).toNat : ℝ) * (L + ε₁))
          + Real.exp (((0 - x).toNat : ℝ) * (L + ε₁)))
        / ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ := by
    rw [add_div]
    exact add_le_add (div_le_div_of_nonneg_right hN1 (norm_nonneg _))
      (div_le_div_of_nonneg_right hN2 (norm_nonneg _))
  have hkey : (1 : ℝ) ≤ (Real.exp (((x₂ - 0).toNat : ℝ) * (L + ε₁))
      + Real.exp (((0 - x).toNat : ℝ) * (L + ε₁))) * B
      / ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ := by
    calc (1 : ℝ) ≤ (‖G α lam θ E x x₂ 0 x‖ + ‖G α lam θ E x x₂ 0 x₂‖) * B := hsum
      _ = (‖pd α lam (θ + α) E ((x₂ - 0).toNat + 1)‖
            / ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖
            + ‖pd α lam (θ + (x : ℝ) * α) E ((0 - x).toNat + 1)‖
              / ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖) * B := by rw [hG1, hG2]
      _ ≤ ((Real.exp (((x₂ - 0).toNat : ℝ) * (L + ε₁))
            + Real.exp (((0 - x).toNat : ℝ) * (L + ε₁)))
              / ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖) * B :=
            mul_le_mul_of_nonneg_right ha (le_of_lt hB)
      _ = (Real.exp (((x₂ - 0).toNat : ℝ) * (L + ε₁))
            + Real.exp (((0 - x).toNat : ℝ) * (L + ε₁))) * B
            / ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ := by ring
  have hfin := (le_div_iff₀ hPpos).mp hkey
  rw [one_mul] at hfin
  linarith [hfin]

/-! ## Arithmetic on the `A`-block -/

lemma b1316_le_cast (K : ℕ) : ((Core.b1316 K : ℤ) : ℝ) ≤ (13 : ℝ) * (K : ℝ) / 16 :=
  Int.floor_le _

lemma b316_ge_cast (K : ℕ) : (3 : ℝ) * (K : ℝ) / 16 ≤ ((Core.b316 K : ℤ) : ℝ) :=
  Int.le_ceil _

/-- The integral bounds on the two ends of the `A`-block. -/
lemma int_bounds (K : ℕ) :
    16 * Core.b1316 K ≤ 13 * (K : ℤ) ∧ 13 * (K : ℤ) - 15 ≤ 16 * Core.b1316 K ∧
    3 * (K : ℤ) ≤ 16 * Core.b316 K ∧ 16 * Core.b316 K ≤ 3 * (K : ℤ) + 15 := by
  have h1 : ((Core.b1316 K : ℤ) : ℝ) ≤ (13 : ℝ) * (K : ℝ) / 16 := Int.floor_le _
  have h2 : (13 : ℝ) * (K : ℝ) / 16 - 1 < ((Core.b1316 K : ℤ) : ℝ) := by
    have hh := Int.lt_floor_add_one ((13 : ℝ) * (K : ℝ) / 16)
    rw [Core.b1316]; linarith
  have h3 : (3 : ℝ) * (K : ℝ) / 16 ≤ ((Core.b316 K : ℤ) : ℝ) := Int.le_ceil _
  have h4 : ((Core.b316 K : ℤ) : ℝ) < (3 : ℝ) * (K : ℝ) / 16 + 1 := by
    rw [Core.b316]; exact Int.ceil_lt_add_one ((3 : ℝ) * (K : ℝ) / 16)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show (16 : ℝ) * ((Core.b1316 K : ℤ) : ℝ) ≤ 13 * (K : ℝ) by linarith)
  · have hh : (13 : ℝ) * (K : ℝ) - 16 < 16 * ((Core.b1316 K : ℤ) : ℝ) := by linarith
    have hh' : (13 * (K : ℤ) - 16 : ℤ) < 16 * Core.b1316 K := by exact_mod_cast hh
    omega
  · exact_mod_cast (show (3 : ℝ) * (K : ℝ) ≤ 16 * ((Core.b316 K : ℤ) : ℝ) by linarith)
  · have hh : 16 * ((Core.b316 K : ℤ) : ℝ) < 3 * (K : ℝ) + 16 := by linarith
    have hh' : 16 * Core.b316 K < 3 * (K : ℤ) + 16 := by exact_mod_cast hh
    omega

lemma b1316_le_pred {K : ℕ} (hK : 1 ≤ K) : Core.b1316 K ≤ (K : ℤ) - 1 := by
  have h : (13 : ℝ) * (K : ℝ) / 16 < ((K : ℤ) : ℝ) := by
    have hK' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    push_cast
    linarith
  have h' : Core.b1316 K < (K : ℤ) := by
    rw [Core.b1316]
    exact Int.floor_lt.mpr h
  omega

lemma b316_le_pred {K : ℕ} (hK : 2 ≤ K) : Core.b316 K ≤ (K : ℤ) - 1 := by
  obtain ⟨-, -, -, h4⟩ := int_bounds K
  have hK' : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  omega

lemma b316_le_b1316 {K : ℕ} (hK : 3 ≤ K) : Core.b316 K ≤ Core.b1316 K := by
  by_cases h5 : 5 ≤ K
  · obtain ⟨h1, h2, h3, h4⟩ := int_bounds K
    have h5' : (5 : ℤ) ≤ (K : ℤ) := by exact_mod_cast h5
    have hcb : 16 * Core.b316 K < 16 * Core.b1316 K := by linarith
    omega
  · have h34 : K = 3 ∨ K = 4 := by omega
    rcases h34 with rfl | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := int_bounds 3; omega
    · obtain ⟨h1, h2, h3, h4⟩ := int_bounds 4; omega

lemma b316_succ_le_b1316 {K : ℕ} (hK : 3 ≤ K) : Core.b316 K + 1 ≤ Core.b1316 K := by
  by_cases h5 : 5 ≤ K
  · obtain ⟨h1, h2, h3, h4⟩ := int_bounds K
    have h5' : (5 : ℤ) ≤ (K : ℤ) := by exact_mod_cast h5
    have hcb : (16 : ℤ) ≤ 16 * (Core.b1316 K - Core.b316 K) := by linarith
    have hcb' : (1 : ℤ) ≤ Core.b1316 K - Core.b316 K := by omega
    omega
  · have h34 : K = 3 ∨ K = 4 := by omega
    rcases h34 with rfl | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := int_bounds 3; omega
    · obtain ⟨h1, h2, h3, h4⟩ := int_bounds 4; omega

lemma b316_pos {K : ℕ} (hK : 1 ≤ K) : (0 : ℤ) < Core.b316 K := by
  obtain ⟨-, -, h3, h4⟩ := int_bounds K
  have hK' : (1 : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK
  omega

/-- Membership in the `A`-block. -/
lemma mem_A2blk {K : ℕ} {x : ℤ} :
    x ∈ Core.A2blk K ↔ -Core.b1316 K ≤ x ∧ x ≤ -Core.b316 K := by
  simp [Core.A2blk, Finset.mem_Icc]

theorem Ablock_res {α lam L ε ε₁ B : ℝ} {E : ℂ} {θ : ℝ} {n : ℕ} {u : ℤ → ℂ}
    (hL : 0 < L) (hεε₁ : ε₁ < ε) (hn : 2 ≤ n) (hB : 0 < B)
    (hbd : ∀ m : ℕ, m ≤ 2 * n - 1 → ∀ ζ : ℝ,
      ‖Work.TMC16Core.pd α lam ζ E (m + 1)‖ ≤ Real.exp ((m : ℝ) * (L + ε₁)))
    (hsol : Work.TMC16Core.IsFormalSol α lam θ E u) (hu0 : u 0 = 1)
    (hdecay : ∀ x ∈ Work.TMC16Core.Core.A2blk (2 * n - 1),
      ‖u (x - 1)‖ ≤ B ∧ ‖u (x + ((2 * n - 1 : ℕ) : ℤ))‖ ≤ B)
    (hnum : 2 * B * Real.exp ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ)))
      ≤ Real.exp (((2 * n : ℕ) : ℝ) * ((23 / 32 : ℝ) * L + ε))) :
    ∀ x ∈ Work.TMC16Core.Core.A2blk (2 * n - 1),
      ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (2 * n)‖ ≤
        Real.exp (((2 * n : ℕ) : ℝ) * ((23 / 32 : ℝ) * L + ε)) := by
  intro x hx
  obtain ⟨hxlo, hxhi⟩ := mem_A2blk.mp hx
  have hK1 : 1 ≤ 2 * n - 1 := by omega
  have hK2 : 2 ≤ 2 * n - 1 := by omega
  have hK3 : 3 ≤ 2 * n - 1 := by omega
  have hKnn : (0 : ℝ) ≤ ((2 * n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hxR : ((x : ℤ) : ℝ) ≤ -((Core.b316 (2 * n - 1) : ℤ) : ℝ) := by exact_mod_cast hxhi
  have hxloR : -((Core.b1316 (2 * n - 1) : ℤ) : ℝ) ≤ ((x : ℤ) : ℝ) := by
    exact_mod_cast hxlo
  have hb316R := b316_ge_cast (2 * n - 1)
  have hb1316R := b1316_le_cast (2 * n - 1)
  -- `x ≤ 0`
  have hx0 : x ≤ 0 := by
    have h' : (0 : ℝ) < ((Core.b316 (2 * n - 1) : ℤ) : ℝ) := by
      have : (0 : ℝ) < (3 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16 := by
        have : (0 : ℝ) < ((2 * n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * n - 1)
        linarith
      linarith
    have h'' : (0 : ℤ) < Core.b316 (2 * n - 1) := by exact_mod_cast h'
    omega
  -- `0 ≤ x + K - 1`
  have hposK : 0 ≤ x + ((2 * n - 1 : ℕ) : ℤ) - 1 := by
    have hb := b1316_le_pred (K := 2 * n - 1) hK1
    omega
  by_cases hD : 0 ≤ L + ε₁
  · -- **Case 1**: `L + ε₁ ≥ 0`
    by_cases hP : pd α lam (θ + (x : ℝ) * α) E (2 * n) = 0
    · rw [hP, norm_zero]; exact (Real.exp_pos _).le
    · have hdec1 : ‖u (x - 1)‖ ≤ B := (hdecay x hx).1
      have hdec2 : ‖u (x + ((2 * n - 1 : ℕ) : ℤ))‖ ≤ B := (hdecay x hx).2
      have hdec2' : ‖u ((x + ((2 * n - 1 : ℕ) : ℤ) - 1) + 1)‖ ≤ B := by
        rw [show x + ((2 * n - 1 : ℕ) : ℤ) - 1 + 1 = x + ((2 * n - 1 : ℕ) : ℤ) by ring]
        exact hdec2
      have hm1 : ((x + ((2 * n - 1 : ℕ) : ℤ) - 1) - 0).toNat ≤ 2 * n - 1 := by
        rw [Int.toNat_le]; omega
      have hm2 : (0 - x).toNat ≤ 2 * n - 1 := by
        rw [Int.toNat_le]
        have hb := b1316_le_pred (K := 2 * n - 1) hK1
        omega
      have hmain := pd_le_of_decay (K := 2 * n - 1) (x := x)
        (x₂ := x + ((2 * n - 1 : ℕ) : ℤ) - 1) hB rfl
        (fun m hm ζ => hbd m hm ζ) hsol hu0 hdec1 hdec2' hx0 hposK hm1 hm2
        (by rw [show 2 * n - 1 + 1 = 2 * n by omega]; exact hP)
      rw [show 2 * n - 1 + 1 = 2 * n by omega] at hmain
      have hz1 : (0 : ℤ) ≤ x + ((2 * n - 1 : ℕ) : ℤ) - 1 - 0 := by omega
      have hz2 : (0 : ℤ) ≤ 0 - x := by omega
      have hcast1 : (((x + ((2 * n - 1 : ℕ) : ℤ) - 1 - 0).toNat : ℝ))
          = ((x + ((2 * n - 1 : ℕ) : ℤ) - 1 - 0 : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hz1]
      have hcast2 : ((((0 - x).toNat : ℕ) : ℝ)) = ((0 - x : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hz2]
      have harg1 : (((x + ((2 * n - 1 : ℕ) : ℤ) - 1 - 0).toNat : ℝ))
          ≤ (13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16 := by
        rw [hcast1]
        push_cast
        linarith
      have harg2 : (((0 - x).toNat : ℝ)) ≤ (13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16 := by
        rw [hcast2]
        push_cast
        linarith
      have ht : ((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁)
          = (L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ)) := by ring
      have hA1 : Real.exp ((((x + ((2 * n - 1 : ℕ) : ℤ) - 1 - 0).toNat : ℝ) * (L + ε₁)))
          ≤ Real.exp (((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁)) :=
        Real.exp_le_exp.mpr (le_trans (mul_le_mul_of_nonneg_right harg1 hD) le_rfl)
      have hA2 : Real.exp (((((0 - x).toNat : ℝ)) * (L + ε₁)))
          ≤ Real.exp (((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁)) :=
        Real.exp_le_exp.mpr (le_trans (mul_le_mul_of_nonneg_right harg2 hD) le_rfl)
      have hsum2 : B * (Real.exp ((((x + ((2 * n - 1 : ℕ) : ℤ) - 1 - 0).toNat : ℝ) * (L + ε₁)))
              + Real.exp (((((0 - x).toNat : ℝ)) * (L + ε₁))))
          ≤ B * (Real.exp (((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁))
              + Real.exp (((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁))) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hB)
        linarith
      have hEq : B * (Real.exp (((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁))
              + Real.exp (((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁)))
          = 2 * B * Real.exp ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ))) := by
        rw [ht]; ring
      exact le_trans hmain (le_trans hsum2 (hEq.le.trans hnum))
  · -- **Case 2**: `L + ε₁ < 0`
    have hDneg : L + ε₁ < 0 := lt_of_not_ge hD
    set y : ℤ := -Core.b316 (2 * n - 1) - 1 with hydef
    have hy1 : y + 1 ∈ Core.A2blk (2 * n - 1) := by
      rw [mem_A2blk]
      constructor
      · have hb := b316_le_b1316 (K := 2 * n - 1) hK3
        omega
      · omega
    have hy : y ∈ Core.A2blk (2 * n - 1) := by
      rw [mem_A2blk]
      constructor
      · have hb := b316_succ_le_b1316 (K := 2 * n - 1) hK3
        omega
      · omega
    have hdecy : ‖u y‖ ≤ B := by
      have h := (hdecay (y + 1) hy1).1
      rwa [show y + 1 - 1 = y by ring] at h
    have hdecy1 : ‖u (y - 1)‖ ≤ B := (hdecay y hy).1
    set n₀ : ℕ := (-y).toNat with hn₀def
    have hyneg : (0 : ℤ) < -y := by
      rw [hydef]
      have := b316_pos (K := 2 * n - 1) hK1
      omega
    have hn₀z : ((n₀ : ℕ) : ℤ) = -y := Int.toNat_of_nonneg (le_of_lt hyneg)
    have hyadd : y + (n₀ : ℤ) = 0 := by rw [hn₀z]; ring
    have hn₀le : n₀ ≤ 2 * n - 1 := by
      have h1 : ((n₀ : ℕ) : ℤ) ≤ ((2 * n - 1 : ℕ) : ℤ) := by
        rw [hn₀z, hydef]
        have hb := b316_le_pred (K := 2 * n - 1) hK2
        omega
      exact_mod_cast h1
    have hn₀pos : 1 ≤ n₀ := by
      have h1 : (1 : ℤ) ≤ -y := by
        rw [hydef]
        have := b316_pos (K := 2 * n - 1) hK1
        omega
      have h2 : (1 : ℤ) ≤ ((n₀ : ℕ) : ℤ) := by rw [hn₀z]; exact h1
      exact_mod_cast h2
    have hb1 : ‖pd α lam (θ + (y : ℝ) * α) E (n₀ + 1)‖
        ≤ Real.exp ((n₀ : ℝ) * (L + ε₁)) := hbd n₀ hn₀le (θ + (y : ℝ) * α)
    have hb2 : ‖pd α lam (θ + ((y + 1 : ℤ) : ℝ) * α) E n₀‖
        ≤ Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁)) := by
      have h := hbd (n₀ - 1) (by omega) (θ + ((y + 1 : ℤ) : ℝ) * α)
      rwa [show n₀ - 1 + 1 = n₀ by omega] at h
    have hBhalf : (1 / 2 : ℝ) ≤ B := by
      have h2 : Real.exp ((n₀ : ℝ) * (L + ε₁)) ≤ 1 := by
        have hnn : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg n₀
        have hle : (n₀ : ℝ) * (L + ε₁) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hnn (le_of_lt hDneg)
        calc Real.exp ((n₀ : ℝ) * (L + ε₁)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hle
          _ = 1 := Real.exp_zero
      have h3 : Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁)) ≤ 1 := by
        have hnn : (0 : ℝ) ≤ ((n₀ - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have hle : ((n₀ - 1 : ℕ) : ℝ) * (L + ε₁) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hnn (le_of_lt hDneg)
        calc Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hle
          _ = 1 := Real.exp_zero
      have hrec := sol_recon (α := α) (lam := lam) (θ := θ) (E := E) (u := u) hsol y n₀
      rw [hyadd] at hrec
      have h1 : (1 : ℝ) ≤
          (Real.exp ((n₀ : ℝ) * (L + ε₁))
            + Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁))) * B := by
        calc (1 : ℝ) = ‖u 0‖ := by rw [hu0, norm_one]
          _ = ‖pd α lam (θ + (y : ℝ) * α) E (n₀ + 1) * u y
                - pd α lam (θ + ((y + 1 : ℤ) : ℝ) * α) E n₀ * u (y - 1)‖ := by rw [hrec]
          _ ≤ ‖pd α lam (θ + (y : ℝ) * α) E (n₀ + 1) * u y‖
                + ‖pd α lam (θ + ((y + 1 : ℤ) : ℝ) * α) E n₀ * u (y - 1)‖ :=
              norm_sub_le _ _
          _ = ‖pd α lam (θ + (y : ℝ) * α) E (n₀ + 1)‖ * ‖u y‖
                + ‖pd α lam (θ + ((y + 1 : ℤ) : ℝ) * α) E n₀‖ * ‖u (y - 1)‖ := by
              rw [norm_mul, norm_mul]
          _ ≤ Real.exp ((n₀ : ℝ) * (L + ε₁)) * B
                + Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁)) * B :=
              add_le_add (mul_le_mul hb1 hdecy (norm_nonneg _) (Real.exp_pos _).le)
                (mul_le_mul hb2 hdecy1 (norm_nonneg _) (Real.exp_pos _).le)
          _ = (Real.exp ((n₀ : ℝ) * (L + ε₁))
                + Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁))) * B := by ring
      have h4 : (Real.exp ((n₀ : ℝ) * (L + ε₁))
            + Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁))) * B ≤ 2 * B := by
        nlinarith [h2, h3, hB]
      linarith
    have hPK : ‖pd α lam (θ + (x : ℝ) * α) E (2 * n)‖
        ≤ Real.exp (((2 * n - 1 : ℕ) : ℝ) * (L + ε₁)) := by
      have h := hbd (2 * n - 1) le_rfl (θ + (x : ℝ) * α)
      rwa [show 2 * n - 1 + 1 = 2 * n by omega] at h
    have hexp1 : Real.exp (((2 * n - 1 : ℕ) : ℝ) * (L + ε₁))
        ≤ Real.exp ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hKD : ((2 * n - 1 : ℕ) : ℝ) * (L + ε₁) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hKnn (le_of_lt hDneg)
      have heq : (L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ))
          = ((13 : ℝ) / 16) * (((2 * n - 1 : ℕ) : ℝ) * (L + ε₁)) := by ring
      rw [heq]
      nlinarith [hKD]
    have hexp2 : Real.exp ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ)))
        ≤ 2 * B * Real.exp ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ))) := by
      have h1 : (1 : ℝ) ≤ 2 * B := by linarith
      have hpos := Real.exp_pos ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ)))
      nlinarith [h1, hpos]
    exact le_trans (le_trans hPK hexp1) (le_trans hexp2 hnum)

end Work.Core
