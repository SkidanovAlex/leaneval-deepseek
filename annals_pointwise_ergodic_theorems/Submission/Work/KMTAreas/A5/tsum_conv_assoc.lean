import Mathlib

namespace Work.KMTAreas.A5

/-- The shear `(j, i) ↦ (j + i, j)` of `ℤ × ℤ`: the change of variables that turns the
`(outer, inner)` index pair of the convolution `a ⋆ (b ⋆ u)` into the `(total, outer)` index
pair of the convolution `(a ⋆ b) ⋆ u`. -/
def tsumConvShear : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 + p.2, p.1)
  invFun p := (p.2, p.1 - p.2)
  left_inv := by rintro ⟨j, i⟩; simp
  right_inv := by rintro ⟨k, j⟩; simp

@[simp] theorem tsumConvShear_fst (p : ℤ × ℤ) : (tsumConvShear p).1 = p.1 + p.2 := rfl
@[simp] theorem tsumConvShear_snd (p : ℤ × ℤ) : (tsumConvShear p).2 = p.1 := rfl

/-- Associativity of `tsum`-convolution over `ℤ` for an `ℓ¹` weight `a ⋆ b = a`:
`∑' j, a j * (∑' i, b i * u (n - j - i)) = ∑' j, a j * u (n - j)`.

Both sides are the absolutely convergent `tsum` over `ℤ × ℤ` of the same double family
(one is obtained from the other by the shear `(j, i) ↦ (j + i, j)`), which is where the
`hab` hypothesis `a ⋆ b = a` is used. -/
theorem tsum_conv_assoc (a b u : ℤ → ℂ) {C : ℝ}
    (ha : Summable fun j : ℤ => ‖a j‖) (hb : Summable fun j : ℤ => ‖b j‖)
    (hu : ∀ m : ℤ, ‖u m‖ ≤ C)
    (hab : ∀ m : ℤ, ∑' j : ℤ, a j * b (m - j) = a m) (n : ℤ) :
    ∑' j : ℤ, a j * (∑' i : ℤ, b i * u (n - j - i)) = ∑' j : ℤ, a j * u (n - j) := by
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
    simp only [tsumConvShear_fst, tsumConvShear_snd]
    rw [show p.1 + p.2 - p.1 = p.2 by ring,
      show n - (p.1 + p.2) = n - p.1 - p.2 by ring]
  have hG : Summable fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * u (n - p.1) := by
    have h1 : Summable ((fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * u (n - p.1))
        ∘ tsumConvShear) :=
      hF.congr (fun p => hFG p)
    exact (Equiv.summable_iff tsumConvShear).mp h1
  have hSp : Summable fun p : ℤ × ℤ => a p.1 * (b p.2 * u (n - p.1 - p.2)) :=
    hF.congr (fun p => by ring)
  -- the left-hand side is the double sum of `F`
  have hA : ∑' j : ℤ, a j * (∑' i : ℤ, b i * u (n - j - i))
      = ∑' p : ℤ × ℤ, a p.1 * b p.2 * u (n - p.1 - p.2) := by
    rw [show (∑' j : ℤ, a j * (∑' i : ℤ, b i * u (n - j - i)))
          = ∑' j : ℤ, ∑' i : ℤ, a j * (b i * u (n - j - i)) from
        tsum_congr (fun j =>
          (tsum_mul_left (a := a j) (f := fun i => b i * u (n - j - i))).symm)]
    rw [← hSp.tsum_prod]
    exact tsum_congr (fun p => by ring)
  -- the right-hand side is the double sum of `G`
  have hB : ∑' k : ℤ, a k * u (n - k)
      = ∑' p : ℤ × ℤ, a p.2 * b (p.1 - p.2) * u (n - p.1) := by
    rw [hG.tsum_prod]
    refine tsum_congr (fun k => ?_)
    dsimp only
    rw [tsum_mul_right, hab k]
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
    _ = ∑' j : ℤ, a j * u (n - j) := hB.symm

end Work.KMTAreas.A5
