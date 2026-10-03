/-
# `ℓ¹`-summability of `kernComp`

The kernel of the composition of a bilinear operator with two linear convolutions
(`Work.KMTAreas.A7.kernComp`, see `ModelOps`) is the *fourfold* convolution

  `kernComp K κ κ' a b = ∑'_{a'} ∑'_{b'} K (a - a') (b - b') * κ a' * κ' b'`.

This file proves the `ℓ¹(ℤ²)` summability of that kernel from the `ℓ¹`-summability of `K`,
`κ` and `κ'` — the elementary "Young inequality" for the composition.  The proof is the standard
one, expressed as a Fubini argument: the *joint* family

  `(p, q) ↦ ‖K (p.1 - q.1) (p.2 - q.2)‖ * (‖κ q.1‖ * ‖κ' q.2‖)`

on `(ℤ²) × (ℤ²)` is summable (it is the product of the two summable families
`p ↦ ‖K p.1 p.2‖` and `q ↦ ‖κ q.1‖ ‖κ' q.2‖`, after the reindexing `(p, q) ↦ (p - q, q)`, which is
a bijection — `kernCompSubEquiv` below), hence so is its iterated sum, which dominates
`p ↦ ‖kernComp K κ κ' p.1 p.2‖` pointwise by the triangle inequality for `tsum`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps

open scoped BigOperators

namespace Work.A7.ModelApproxCore_aux

/-- The reindexing `(p, q) ↦ (p - q, q)` of `ℤ² × ℤ²`, a bijection with inverse
`(r, q) ↦ (r + q, q)`.  It turns the "difference variables" `(K (p - q), q)` of `kernComp` into
independent variables `(p, q) ↦ (r, q)`, which is what makes the Fubini argument work. -/
def kernCompSubEquiv : ((ℤ × ℤ) × (ℤ × ℤ)) ≃ ((ℤ × ℤ) × (ℤ × ℤ)) where
  toFun z := (z.1 - z.2, z.2)
  invFun w := (w.1 + w.2, w.2)
  left_inv z := by ext <;> simp
  right_inv w := by ext <;> simp

theorem summable_kernComp {K : ℤ → ℤ → ℂ} {κ κ' : ℤ → ℂ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hκ : Summable fun j : ℤ => ‖κ j‖)
    (hκ' : Summable fun j : ℤ => ‖κ' j‖) :
    Summable fun p : ℤ × ℤ => ‖Work.KMTAreas.A7.kernComp K κ κ' p.1 p.2‖ := by
  -- The `ℓ¹`-mass of `(a, b) ↦ κ a κ' b`.
  have hκκ' : Summable fun w : ℤ × ℤ => ‖κ w.1‖ * ‖κ' w.2‖ :=
    Summable.mul_of_nonneg hκ hκ' (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  -- The joint family of the fourfold sum, in independent variables.
  have hG : Summable fun z : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K z.1.1 z.1.2‖ * (‖κ z.2.1‖ * ‖κ' z.2.2‖) :=
    Summable.mul_of_nonneg (f := fun p : ℤ × ℤ => ‖K p.1 p.2‖)
      (g := fun w : ℤ × ℤ => ‖κ w.1‖ * ‖κ' w.2‖) hK hκκ' (fun _ => norm_nonneg _)
        (fun w => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- Reindex by `(p, q) ↦ (p - q, q)`: the family of `kernComp`'s summand norms.
  have hGe : Summable fun z : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K (z.1 - z.2).1 (z.1 - z.2).2‖ * (‖κ z.2.1‖ * ‖κ' z.2.2‖) :=
    (Equiv.summable_iff kernCompSubEquiv).mpr hG
  -- Fubini: the iterated sums are summable and give the majorant of `‖kernComp ·‖`.
  have hiter : Summable fun p : ℤ × ℤ =>
      ∑' q : ℤ × ℤ, ‖K (p.1 - q.1) (p.2 - q.2)‖ * (‖κ q.1‖ * ‖κ' q.2‖) :=
    Summable.prod (f := fun z : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K (z.1 - z.2).1 (z.1 - z.2).2‖ * (‖κ z.2.1‖ * ‖κ' z.2.2‖)) hGe
  have hbound : ∀ p : ℤ × ℤ, ‖Work.KMTAreas.A7.kernComp K κ κ' p.1 p.2‖
      ≤ ∑' q : ℤ × ℤ, ‖K (p.1 - q.1) (p.2 - q.2)‖ * (‖κ q.1‖ * ‖κ' q.2‖) := by
    intro p
    -- For fixed `p` the map `q ↦ (p - q, q)` is injective, so the summand norms are summable.
    have hinj : Function.Injective (fun q : ℤ × ℤ => (p - q, q)) := by
      intro q₁ q₂ h; simpa using congrArg Prod.snd h
    have hp : Summable fun q : ℤ × ℤ =>
        ‖K (p.1 - q.1) (p.2 - q.2)‖ * (‖κ q.1‖ * ‖κ' q.2‖) := by
      simpa [Function.comp_def] using hG.comp_injective hinj
    have hwnorm : Summable fun q : ℤ × ℤ =>
        ‖K (p.1 - q.1) (p.2 - q.2) * κ q.1 * κ' q.2‖ :=
      hp.congr (fun q => by rw [norm_mul, norm_mul, mul_assoc])
    have hw : Summable fun q : ℤ × ℤ => K (p.1 - q.1) (p.2 - q.2) * κ q.1 * κ' q.2 :=
      Summable.of_norm hwnorm
    -- `kernComp` is the iterated sum of that family (Fubini, now that it is summable).
    have hkern : Work.KMTAreas.A7.kernComp K κ κ' p.1 p.2
        = ∑' q : ℤ × ℤ, K (p.1 - q.1) (p.2 - q.2) * κ q.1 * κ' q.2 := by
      unfold Work.KMTAreas.A7.kernComp
      exact (Summable.tsum_prod hw).symm
    rw [hkern]
    calc ‖∑' q : ℤ × ℤ, K (p.1 - q.1) (p.2 - q.2) * κ q.1 * κ' q.2‖
        ≤ ∑' q : ℤ × ℤ, ‖K (p.1 - q.1) (p.2 - q.2) * κ q.1 * κ' q.2‖ :=
          norm_tsum_le_tsum_norm hwnorm
      _ = ∑' q : ℤ × ℤ, ‖K (p.1 - q.1) (p.2 - q.2)‖ * (‖κ q.1‖ * ‖κ' q.2‖) := by
          simp only [norm_mul, mul_assoc]
  exact Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound hiter

end Work.A7.ModelApproxCore_aux
