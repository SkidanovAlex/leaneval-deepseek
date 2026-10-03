import Mathlib
import Submission.Work.KMTAreas.A5.tsum_conv_assoc

namespace Work.KMTAreas.A7Hi

open Work.KMTAreas.A5 (tsumConvShear)

/-- Associativity of the `tsum`-convolution over `ℤ`, with a bounded third factor:
`a ⋆ (b ⋆ u) = (a ⋆ b) ⋆ u` at the argument `n`.

Both sides are the absolutely convergent `tsum` over `ℤ × ℤ` of the double family
`(j, i) ↦ a j * b i * u (n - j - i)`: the left-hand side by the iterated-sum form of that
`tsum`, the right-hand side after the shear `(j, i) ↦ (j + i, j)` (which identifies the
`(total, outer)` index pair of `(a ⋆ b) ⋆ u` with the `(outer, inner)` pair), and the
boundedness of `u` together with `a, b ∈ ℓ¹` makes the double family absolutely summable. -/
theorem tsum_conv_conv {a b u : ℤ → ℂ} {C : ℝ}
    (ha : Summable fun j : ℤ => ‖a j‖) (hb : Summable fun j : ℤ => ‖b j‖)
    (hu : ∀ m : ℤ, ‖u m‖ ≤ C) (n : ℤ) :
    ∑' j : ℤ, a j * (∑' i : ℤ, b i * u (n - j - i))
      = ∑' m : ℤ, (∑' j : ℤ, a j * b (m - j)) * u (n - m) := by
  -- the double family `‖a‖ ‖b‖` is summable
  have hab_summable : Summable fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖ :=
    Summable.mul_of_nonneg ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hbound : Summable fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖ * C :=
    hab_summable.mul_right C
  -- `F (j, i) = a j * b i * u (n - j - i)` is summable
  have hF : Summable fun p : ℤ × ℤ => a p.1 * b p.2 * u (n - p.1 - p.2) := by
    refine Summable.of_norm_bounded hbound (fun p => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hu _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- `F (j, i) = G (j + i, j)` where `G (k, j) = a j * b (k - j) * u (n - k)`
  have hFG : ∀ p : ℤ × ℤ, a p.1 * b p.2 * u (n - p.1 - p.2)
      = a (tsumConvShear p).2 * b ((tsumConvShear p).1 - (tsumConvShear p).2)
          * u (n - (tsumConvShear p).1) := by
    intro p
    simp only [_root_.Work.KMTAreas.A5.tsumConvShear_fst,
      _root_.Work.KMTAreas.A5.tsumConvShear_snd]
    rw [show p.1 + p.2 - p.1 = p.2 by ring,
      show n - (p.1 + p.2) = n - p.1 - p.2 by ring]
  have hG : Summable fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * u (n - p.1) := by
    have h1 : Summable ((fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * u (n - p.1))
        ∘ tsumConvShear) :=
      hF.congr (fun p => hFG p)
    exact (Equiv.summable_iff tsumConvShear).mp h1
  have hSp : Summable fun p : ℤ × ℤ => a p.1 * (b p.2 * u (n - p.1 - p.2)) :=
    hF.congr (fun p => by ring)
  -- the left-hand side is the iterated double sum of `F`
  have hA : ∑' j : ℤ, a j * (∑' i : ℤ, b i * u (n - j - i))
      = ∑' p : ℤ × ℤ, a p.1 * b p.2 * u (n - p.1 - p.2) := by
    rw [show (∑' j : ℤ, a j * (∑' i : ℤ, b i * u (n - j - i)))
          = ∑' j : ℤ, ∑' i : ℤ, a j * (b i * u (n - j - i)) from
        tsum_congr (fun j =>
          (tsum_mul_left (a := a j) (f := fun i => b i * u (n - j - i))).symm)]
    rw [← hSp.tsum_prod]
    exact tsum_congr (fun p => by ring)
  -- the right-hand side is the double sum of `G`, grouped as `(∑ j, a j * b (k - j)) * u (n - k)`
  have hB : ∑' m : ℤ, (∑' j : ℤ, a j * b (m - j)) * u (n - m)
      = ∑' p : ℤ × ℤ, a p.2 * b (p.1 - p.2) * u (n - p.1) := by
    rw [hG.tsum_prod]
    refine tsum_congr (fun k => ?_)
    dsimp only
    rw [tsum_mul_right]
  -- the two double sums coincide via the shear reindexing
  have hC : (∑' p : ℤ × ℤ, a p.1 * b p.2 * u (n - p.1 - p.2))
      = ∑' p : ℤ × ℤ, a p.2 * b (p.1 - p.2) * u (n - p.1) := by
    rw [show (∑' p : ℤ × ℤ, a p.1 * b p.2 * u (n - p.1 - p.2))
          = ∑' p : ℤ × ℤ, a (tsumConvShear p).2
              * b ((tsumConvShear p).1 - (tsumConvShear p).2) * u (n - (tsumConvShear p).1)
        from tsum_congr (fun p => hFG p)]
    exact Equiv.tsum_eq tsumConvShear
      (fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * u (n - p.1))
  calc ∑' j : ℤ, a j * (∑' i : ℤ, b i * u (n - j - i))
      = ∑' p : ℤ × ℤ, a p.1 * b p.2 * u (n - p.1 - p.2) := hA
    _ = ∑' p : ℤ × ℤ, a p.2 * b (p.1 - p.2) * u (n - p.1) := hC
    _ = ∑' m : ℤ, (∑' j : ℤ, a j * b (m - j)) * u (n - m) := hB.symm

end Work.KMTAreas.A7Hi
