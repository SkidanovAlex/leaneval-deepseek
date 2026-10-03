/-
# Absolute summability of the inner sums of the `lip-2` expansion
(`Work.KMTAreas.A4.lip2InnerSummable`)

The main-case expansion of Proposition `lip-2` of Krause--Mirek--Tao (§5.2) writes the pairing
`⟨Ã*_N(h,g), F⟩` as the double sum

  `∑_s ∑_y h y · F (y + s) · lip2Avg N P M γ g s y`,

i.e. as `∑_s lip2Inner N P M γ F g h s` with

  `lip2Inner N P M γ F g h s = ∑'_y h y · F (y + s) · lip2Avg N P M γ g s y`

(`Work.KMTAreas.A4.lip2Inner`, `Work.KMTAreas.A4.lip2WindowExpansion`).  The truncation of the
outer `s`-sum to `|s| ≤ S` (`Work.KMTAreas.A4.lip2WindowTail`, and the pigeonhole of the assembly
`Work.KMTAreas.A4.lip2Step1`) needs the *tail* to be summable over `s` for **every** shift, not
just for the large shifts `|s| > S` covered by the decay estimate.  The present lemma supplies
exactly that absolute summability, uniformly in every parameter except that it needs `N ≥ 1`,
`M ≥ 1`, `F ∈ ℓ¹`, `g ∈ ℓ¹ ∩ ℓ^∞`, `h ∈ ℓ¹` with `‖h‖_∞ ≤ 1`.

## The argument

Write `C := ∑'_m ‖win M γ m‖` for the `ℓ¹` mass of the window `win M γ` (finite for `M ≥ 1` by
`Work.KMTAreas.A4.lip2Kernel`).  Two elementary bounds give the claim.

* **Uniform bound on the average.**  `lip2Avg N P M γ g s y` is `N⁻¹` times the sum of at most `N`
  terms `win M γ (n - s) · g (y + P(n))` with `‖g‖ ≤ 1`; the shifts `n ↦ n - s` are injective, so
  the sum of `‖win M γ (n - s)‖` over `n ∈ (N/2, N]` is a sub-sum of `∑'_m ‖win M γ m‖`.  Hence
  `‖lip2Avg N P M γ g s y‖ ≤ C` for *all* `s` and `y`
  (`norm_lip2Avg_le_of_tsum_le`; this is the global counterpart of the tail bound
  `Work.KMTAreas.A4.norm_lip2Avg_le`).

* **The `ℓ¹`-correlation.**  For summable nonnegative `a`, `b` on `ℤ` the correlation
  `s ↦ ∑'_y a y · b (y + s)` is summable (`summable_corr_lip2`): the finite partial sums are
  bounded by `(∑' a)(∑' b)` (`Work.KMTAreas.A4.finset_sum_tsum_conv_le`), which is
  `summable_of_sum_le`.

Combining the two, `‖lip2Inner s‖ ≤ C · ∑'_y ‖h y‖ ‖F (y + s)‖`, and the right-hand side is
summable in `s` by the second point with `a = ‖h‖`, `b = ‖F‖`; the target follows from
`Summable.of_nonneg_of_le`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2Main

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## The uniform bound on the windowed average -/

/-- **The windowed average is uniformly bounded by the `ℓ¹` mass of the window.**
If `N ≥ 1`, `M ≥ 1`, `‖g‖_∞ ≤ 1` and `C` dominates `∑'_m ‖win M γ m‖`, then

  `‖lip2Avg N P M γ g s y‖ ≤ C` for *every* pair of shifts `s, y`.

Indeed `lip2Avg N P M γ g s y` is `N⁻¹` times a sum of at most `N` terms
`win M γ (n - s) · g (y + P(n))`, and `n ↦ n - s` is injective, so the sum of the window norms is
at most the total `ℓ¹` mass of the window.  (This is the global counterpart of the tail estimate
`Work.KMTAreas.A4.norm_lip2Avg_le`.) -/
theorem norm_lip2Avg_le_of_tsum_le {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) {M : ℝ}
    (_hM : 1 ≤ M) (γ : FreqCircle) {g : ℤ → ℂ} (hg : ∀ y : ℤ, ‖g y‖ ≤ 1)
    (hw : Summable fun m : ℤ => ‖win M γ m‖) {C : ℝ}
    (hC : (∑' m : ℤ, ‖win M γ m‖) ≤ C) :
    ∀ s y : ℤ, ‖lip2Avg N P M γ g s y‖ ≤ C := by
  have hC0 : 0 ≤ C := (tsum_nonneg (fun m : ℤ => norm_nonneg (win M γ m))).trans hC
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNinv : (N : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hNpos).mpr (by exact_mod_cast hN)
  have hnrm : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (inv_nonneg.mpr hNpos.le)]
  -- the window mass over any finite set of shifts
  have hwinIcc : ∀ (u : Finset ℕ) (s : ℤ), (∑ n ∈ u, ‖win M γ ((n : ℤ) - s)‖) ≤ C := by
    intro u s
    have hinj : Set.InjOn (fun n : ℕ => ((n : ℤ) - s)) ↑u := by
      intro a _ b _ hab
      have h1 : (a : ℤ) - s = (b : ℤ) - s := hab
      exact Int.ofNat.inj (add_right_cancel h1)
    rw [← Finset.sum_image (f := fun m : ℤ => ‖win M γ m‖) (s := u)
      (g := fun n : ℕ => ((n : ℤ) - s)) hinj]
    exact (Summable.sum_le_tsum _ (fun i _ => norm_nonneg _) hw).trans hC
  intro s y
  rw [lip2Avg, norm_mul, hnrm]
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
          win M γ ((n : ℤ) - s) * g (y + P.eval ((n : ℤ)))‖
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          ‖win M γ ((n : ℤ) - s) * g (y + P.eval ((n : ℤ)))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hNpos.le)
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => ?_))
          (inv_nonneg.mpr hNpos.le)
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hg _)
    _ ≤ (N : ℝ)⁻¹ * C := mul_le_mul_of_nonneg_left (hwinIcc _ s) (inv_nonneg.mpr hNpos.le)
    _ ≤ C := by
        calc (N : ℝ)⁻¹ * C ≤ 1 * C := mul_le_mul_of_nonneg_right hNinv hC0
          _ = C := one_mul _

/-! ## Summability of the `ℓ¹`-correlation -/

/-- **The `ℓ¹`-correlation of two absolutely summable sequences is summable.**
For `a, b : ℤ → ℝ` summable and nonnegative, `s ↦ ∑'_y a y · b (y + s)` is summable.  Indeed every
finite partial sum is at most `(∑' a)(∑' b)` by `Work.KMTAreas.A4.finset_sum_tsum_conv_le`, so
`summable_of_sum_le` applies. -/
theorem summable_corr_lip2 {a b : ℤ → ℝ} (ha : Summable a) (hb : Summable b)
    (ha0 : ∀ y : ℤ, 0 ≤ a y) (hb0 : ∀ x : ℤ, 0 ≤ b x) :
    Summable (fun s : ℤ => ∑' y : ℤ, a y * b (y + s)) :=
  summable_of_sum_le (fun s => tsum_nonneg (fun y => mul_nonneg (ha0 y) (hb0 (y + s))))
    (fun u => finset_sum_tsum_conv_le ha hb ha0 hb0 u)

/-! ## The target -/

/-- **Absolute summability of the inner sums of the `lip-2` expansion.**  For `N ≥ 1`, `M ≥ 1`,
`F ∈ ℓ¹`, `g ∈ ℓ¹ ∩ ℓ^∞`, `h ∈ ℓ¹` with `‖h‖_∞ ≤ 1`, the family
`s ↦ lip2Inner N P M γ F g h s = ∑'_y h y · F (y + s) · lip2Avg N P M γ g s y` is absolutely
summable. -/
theorem lip2InnerSummable {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) {M : ℝ} (hM : 1 ≤ M)
    {γ : Work.Analysis.InverseTheory.FreqCircle} {F : ℤ → ℂ}
    (hFsum : Summable fun x : ℤ => ‖F x‖)
    {g h : ℤ → ℂ} (hgsum : Summable fun y : ℤ => ‖g y‖) (hhsum : Summable fun y : ℤ => ‖h y‖)
    (hgb : ∀ y : ℤ, ‖g y‖ ≤ 1) (hhb : ∀ y : ℤ, ‖h y‖ ≤ 1) :
    Summable (fun s : ℤ => ‖Work.KMTAreas.A4.lip2Inner N P M γ F g h s‖) := by
  obtain ⟨hwinSumm, ⟨Cw, _, hCw⟩, _⟩ := lip2Kernel
  have hAvg : ∀ s y : ℤ, ‖lip2Avg N P M γ g s y‖ ≤ Cw :=
    norm_lip2Avg_le_of_tsum_le hN P hM γ hgb (hwinSumm M γ hM) (hCw M γ hM)
  -- the correlation `s ↦ ∑'_y ‖h y‖ ‖F (y + s)‖` is summable
  have hcorr : Summable (fun s : ℤ => ∑' y : ℤ, ‖h y‖ * ‖F (y + s)‖) :=
    summable_corr_lip2 (a := fun y : ℤ => ‖h y‖) (b := fun x : ℤ => ‖F x‖)
      hhsum hFsum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun s => norm_nonneg _) (fun s => ?_) (hcorr.mul_left Cw)
  have hs : Summable (fun y : ℤ => ‖h y‖ * ‖F (y + s)‖) :=
    winShiftSummable (a := fun y : ℤ => ‖h y‖) (b := fun x : ℤ => ‖F x‖)
      hhsum hFsum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) s
  have hterm : Summable (fun y : ℤ => ‖h y * F (y + s) * lip2Avg N P M γ g s y‖) := by
    refine Summable.of_nonneg_of_le (fun y => norm_nonneg _) (fun y => ?_) (hs.mul_right Cw)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hAvg s y) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [lip2Inner]
  calc ‖∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y‖
      ≤ ∑' y : ℤ, ‖h y * F (y + s) * lip2Avg N P M γ g s y‖ := norm_tsum_le_tsum_norm hterm
    _ ≤ ∑' y : ℤ, (‖h y‖ * ‖F (y + s)‖) * Cw := by
        refine Summable.tsum_le_tsum (fun y => ?_) hterm (hs.mul_right Cw)
        rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (hAvg s y) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑' y : ℤ, ‖h y‖ * ‖F (y + s)‖) * Cw := tsum_mul_right
    _ = Cw * ∑' y : ℤ, ‖h y‖ * ‖F (y + s)‖ := by ring

end Work.KMTAreas.A4
