import Mathlib
import Submission.Work.Kernel.Raw

set_option maxHeartbeats 4000000

namespace Work.MainP

/-- If every entry of `f - g` (after scaling by `2^p`) is below `c`, then so is the scaled
sup-norm of the whole vector `f - g`. -/
private lemma epsComp_norm_le {n : ℕ} (p : ℕ) {f g : Fin n → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, (2 : ℝ) ^ p * ‖f i - g i‖ < c) :
    (2 : ℝ) ^ p * ‖f - g‖ ≤ c := by
  have h2p : (0 : ℝ) < (2 : ℝ) ^ p := pow_pos (by norm_num) p
  have hne : (2 : ℝ) ^ p ≠ 0 := ne_of_gt h2p
  have hpoint : ∀ i, ‖f i - g i‖ ≤ c / (2 : ℝ) ^ p := by
    intro i
    rw [le_div_iff₀ h2p]
    rw [mul_comm]
    exact le_of_lt (h i)
  have hsup : ‖f - g‖ ≤ c / (2 : ℝ) ^ p := by
    rw [pi_norm_le_iff_of_nonneg (div_nonneg hc (le_of_lt h2p))]
    intro i
    exact hpoint i
  calc (2 : ℝ) ^ p * ‖f - g‖
      ≤ (2 : ℝ) ^ p * (c / (2 : ℝ) ^ p) := mul_le_mul_of_nonneg_left hsup (le_of_lt h2p)
    _ = c := mul_div_cancel₀ c hne

/-- Paper Corollary 2.8, the error composition of three contracting maps (Prop 5.2 step 3).

Setup (`n, m > 0`): `A : ℂ^n → ℂ^m`, `T : ℂ^m → ℂ^m`, `B : ℂ^m → ℂ^n`; `T` and `B` are
*additive on differences* (`T (u-v) = T u - T v`, `B (u-v) = B u - B v`) and have sup-norm at
most 1 (`∀ u, ‖T u‖ ≤ ‖u‖`, `∀ u, ‖B u‖ ≤ ‖u‖`).  Let `u₀ ∈ ℂ^n`, and let `wsA`, `wsT`, `wsB` be
fixed-point vectors with `wsA ∈ C̃◦^m` approximating `A u₀` (error `< eA`),
`wsT ∈ C̃◦^m` approximating `T (fxVec p m wsA)` (error `< eT`), and
`wsB ∈ C̃◦^n` approximating `B (fxVec p m wsT)` (error `< eB`), in the sense of `HvdH.Approx`.

Then `(2^p)·‖wsB_i − B(T(A u₀))_i‖ < eA + eT + eB` for every `i : Fin n`: a composition of the
three approximations, using the contraction bounds to transfer the errors of `A` and `T`
backwards through `T` and `B`.  (`eA, eT, eB` are only assumed nonnegative; in the application
they are the natural numbers `D p²`, `8 T log₂T`, `D p²`.)

Proof ingredients: `Pi.norm_def : ‖f‖ = ↑(Finset.univ.sup (fun i => ‖f i‖₊))` converts "all
entries `< e`" into `(2^p)‖f‖ ≤ e`, and `norm_le_pi_norm : ‖f i‖ ≤ ‖f‖` goes the other way;
then the triangle inequality term by term. -/
theorem epsComp {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (p : ℕ)
    (A : (Fin n → ℂ) → (Fin m → ℂ)) (T : (Fin m → ℂ) → (Fin m → ℂ))
    (B : (Fin m → ℂ) → (Fin n → ℂ))
    (hT : ∀ u v, T (u - v) = T u - T v) (hTn : ∀ u, ‖T u‖ ≤ ‖u‖)
    (hB : ∀ u v, B (u - v) = B u - B v) (hBn : ∀ u, ‖B u‖ ≤ ‖u‖)
    (u₀ : Fin n → ℂ) (eA eT eB : ℝ) (hA0 : 0 ≤ eA) (hT0 : 0 ≤ eT) (hB0 : 0 ≤ eB)
    (wsA wsT wsB : List (ℤ × ℤ))
    (h1 : HvdH.Approx p wsA (A u₀) eA)
    (h2 : HvdH.Approx p wsT (T (HvdH.fxVec p m wsA)) eT)
    (h3 : HvdH.Approx p wsB (B (HvdH.fxVec p m wsT)) eB) :
    ∀ i : Fin n, (2 : ℝ) ^ p * ‖HvdH.fxC p (wsB.getD i (0, 0)) - B (T (A u₀)) i‖
      < eA + eT + eB := by
  have h2p : (0 : ℝ) < (2 : ℝ) ^ p := pow_pos (by norm_num) p
  -- error of `A` at the input level, after scaling
  have hAbound : (2 : ℝ) ^ p * ‖HvdH.fxVec p m wsA - A u₀‖ ≤ eA := by
    refine epsComp_norm_le p hA0 (f := HvdH.fxVec p m wsA) (g := A u₀) ?_
    intro j
    exact h1.2 j
  -- error of `T` at the level of its own input
  have hTbound : (2 : ℝ) ^ p * ‖HvdH.fxVec p m wsT - T (HvdH.fxVec p m wsA)‖ ≤ eT := by
    refine epsComp_norm_le p hT0 (f := HvdH.fxVec p m wsT)
      (g := T (HvdH.fxVec p m wsA)) ?_
    intro j
    exact h2.2 j
  intro i
  -- transfer the error of `B` through the contraction of `B`
  have hBTa : ‖(B (HvdH.fxVec p m wsT)) i - B (T (A u₀)) i‖
      ≤ ‖HvdH.fxVec p m wsT - T (A u₀)‖ := by
    have heq : B (HvdH.fxVec p m wsT) - B (T (A u₀))
        = B (HvdH.fxVec p m wsT - T (A u₀)) := (hB _ _).symm
    have hstep : (B (HvdH.fxVec p m wsT)) i - (B (T (A u₀))) i
        = B (HvdH.fxVec p m wsT - T (A u₀)) i := by
      have hh := congrFun heq i
      simpa using hh
    rw [hstep]
    exact le_trans (norm_le_pi_norm _ i) (hBn _)
  -- transfer the errors of `A` and `T` back through `T`'s contraction
  have hTinner : ‖HvdH.fxVec p m wsT - T (A u₀)‖
      ≤ ‖HvdH.fxVec p m wsT - T (HvdH.fxVec p m wsA)‖ + ‖HvdH.fxVec p m wsA - A u₀‖ := by
    have hdecomp : HvdH.fxVec p m wsT - T (A u₀)
        = (HvdH.fxVec p m wsT - T (HvdH.fxVec p m wsA))
          + (T (HvdH.fxVec p m wsA) - T (A u₀)) := by abel
    have hTsub : T (HvdH.fxVec p m wsA) - T (A u₀)
        = T (HvdH.fxVec p m wsA - A u₀) := (hT _ _).symm
    calc ‖HvdH.fxVec p m wsT - T (A u₀)‖
        = ‖(HvdH.fxVec p m wsT - T (HvdH.fxVec p m wsA))
            + (T (HvdH.fxVec p m wsA) - T (A u₀))‖ := by rw [hdecomp]
      _ ≤ ‖HvdH.fxVec p m wsT - T (HvdH.fxVec p m wsA)‖
            + ‖T (HvdH.fxVec p m wsA) - T (A u₀)‖ := norm_add_le _ _
      _ = ‖HvdH.fxVec p m wsT - T (HvdH.fxVec p m wsA)‖
            + ‖T (HvdH.fxVec p m wsA - A u₀)‖ := by rw [hTsub]
      _ ≤ ‖HvdH.fxVec p m wsT - T (HvdH.fxVec p m wsA)‖
            + ‖HvdH.fxVec p m wsA - A u₀‖ := add_le_add (le_refl _) (hTn _)
  have hXbound : (2 : ℝ) ^ p * ‖HvdH.fxVec p m wsT - T (A u₀)‖ ≤ eT + eA := by
    have hmul := mul_le_mul_of_nonneg_left hTinner (le_of_lt h2p)
    calc (2 : ℝ) ^ p * ‖HvdH.fxVec p m wsT - T (A u₀)‖
        ≤ (2 : ℝ) ^ p * (‖HvdH.fxVec p m wsT - T (HvdH.fxVec p m wsA)‖
            + ‖HvdH.fxVec p m wsA - A u₀‖) := hmul
      _ = (2 : ℝ) ^ p * ‖HvdH.fxVec p m wsT - T (HvdH.fxVec p m wsA)‖
            + (2 : ℝ) ^ p * ‖HvdH.fxVec p m wsA - A u₀‖ := by ring
      _ ≤ eT + eA := add_le_add hTbound hAbound
  -- triangle inequality for the two contributions
  have htri : ‖HvdH.fxC p (wsB.getD i (0, 0)) - B (T (A u₀)) i‖
      ≤ ‖HvdH.fxC p (wsB.getD i (0, 0)) - (B (HvdH.fxVec p m wsT)) i‖
        + ‖HvdH.fxVec p m wsT - T (A u₀)‖ := by
    have hsplit : HvdH.fxC p (wsB.getD i (0, 0)) - B (T (A u₀)) i
        = (HvdH.fxC p (wsB.getD i (0, 0)) - (B (HvdH.fxVec p m wsT)) i)
          + ((B (HvdH.fxVec p m wsT)) i - B (T (A u₀)) i) := by abel
    calc ‖HvdH.fxC p (wsB.getD i (0, 0)) - B (T (A u₀)) i‖
        = ‖(HvdH.fxC p (wsB.getD i (0, 0)) - (B (HvdH.fxVec p m wsT)) i)
            + ((B (HvdH.fxVec p m wsT)) i - B (T (A u₀)) i)‖ := by rw [hsplit]
      _ ≤ ‖HvdH.fxC p (wsB.getD i (0, 0)) - (B (HvdH.fxVec p m wsT)) i‖
            + ‖(B (HvdH.fxVec p m wsT)) i - B (T (A u₀)) i‖ := norm_add_le _ _
      _ ≤ ‖HvdH.fxC p (wsB.getD i (0, 0)) - (B (HvdH.fxVec p m wsT)) i‖
            + ‖HvdH.fxVec p m wsT - T (A u₀)‖ := add_le_add (le_refl _) hBTa
  calc (2 : ℝ) ^ p * ‖HvdH.fxC p (wsB.getD i (0, 0)) - B (T (A u₀)) i‖
      ≤ (2 : ℝ) ^ p * (‖HvdH.fxC p (wsB.getD i (0, 0)) - (B (HvdH.fxVec p m wsT)) i‖
          + ‖HvdH.fxVec p m wsT - T (A u₀)‖) := mul_le_mul_of_nonneg_left htri (le_of_lt h2p)
    _ = (2 : ℝ) ^ p * ‖HvdH.fxC p (wsB.getD i (0, 0)) - (B (HvdH.fxVec p m wsT)) i‖
          + (2 : ℝ) ^ p * ‖HvdH.fxVec p m wsT - T (A u₀)‖ := by ring
    _ < eB + (eT + eA) := add_lt_add_of_lt_of_le (h3.2 i) hXbound
    _ = eA + eT + eB := by ring

end Work.MainP
