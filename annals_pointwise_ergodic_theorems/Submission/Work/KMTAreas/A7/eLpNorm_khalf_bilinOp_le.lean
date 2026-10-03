/-
# The `ℓ^p`-boundedness of the halved average as a bilinear convolution operator

The kernel `khalf m P` of the halved average
`Ã_m(u,v)(x) = m⁻¹ ∑_{m/2 < n ≤ m} u(x-n) v(x-P(n))` is supported on the graph of `P` over the
integer window `(m/2, m] ⊆ ℤ`, and each of its (at most `m`) non-zero entries equals `m⁻¹`; it is
therefore an *averaging* kernel: its `ℓ¹(ℤ²)` mass is at most one
(`summable_khalf_tsum_le_one`, with the maxima are attained exactly when `m` is even).

Young's inequality for bilinear convolution kernels (`Work.KMTAreas.A7.BilinOpLp`)
```
  ‖bilinOp K u v‖_{ℓ^p} ≤ ‖K‖_{ℓ¹(ℤ²)} ‖u‖_{ℓ^{p₁}} ‖v‖_{ℓ^{p₂}},   1/p₁ + 1/p₂ = 1/p,  1 ≤ p,
```
combined with that mass bound gives the unconditional **norm-one bound**

  `‖bilinOp (khalf m P) u v‖_{ℓ^p} ≤ ‖u‖_{ℓ^{p₁}} ‖v‖_{ℓ^{p₂}}`,

with no hypothesis on `u`, `v` beyond measurability on the counting measure (no summability is
needed: everything is an `ℝ≥0∞`-valued `eLpNorm`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.BilinOpLp

set_option autoImplicit false

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- **The halved-average kernel is an averaging kernel.** Its support is the graph of `P` over the
finite integer window `n ∈ ((m:ℤ)/2, m]`, on which it is constantly `m⁻¹`; there are at most `m`
such `n`, so the `ℓ¹(ℤ²)` mass of `khalf m P` is at most one. -/
theorem summable_khalf_tsum_le_one (m : ℕ) (P : Polynomial ℤ) :
    Summable (fun p : ℤ × ℤ => ‖khalf m P p.1 p.2‖) ∧
      (∑' p : ℤ × ℤ, ‖khalf m P p.1 p.2‖) ≤ 1 := by
  -- everything off the graph `a ↦ (a, P.eval a)` over `A = Ioc (m/2) m` vanishes
  have hsupp : ∀ p : ℤ × ℤ,
      p ∉ (Finset.Ioc ((m : ℤ) / 2) (m : ℤ)).image (fun a => (a, P.eval a)) →
      khalf m P p.1 p.2 = 0 := by
    rintro ⟨a, b⟩ hp
    rw [khalf]
    by_cases hc : (m / 2 : ℤ) < a ∧ a ≤ (m : ℤ) ∧ b = P.eval a
    · rw [if_pos hc]; exfalso; apply hp
      obtain ⟨h1, h2, h3⟩ := hc
      exact Finset.mem_image.mpr ⟨a, Finset.mem_Ioc.mpr ⟨h1, h2⟩, by rw [h3]⟩
    · rw [if_neg hc]
  refine ⟨summable_of_ne_finset_zero (fun p hp => by rw [hsupp p hp]; simp), ?_⟩
  set A : Finset ℤ := Finset.Ioc ((m : ℤ) / 2) (m : ℤ) with hA
  -- the `tsum` is the finite sum of the `m⁻¹` on the graph of `P` over `A`
  have h1 : (∑' p : ℤ × ℤ, ‖khalf m P p.1 p.2‖)
      = ∑ a ∈ A, ‖khalf m P a (P.eval a)‖ := by
    rw [tsum_eq_sum (s := A.image (fun a => (a, P.eval a)))
      (fun p hp => by rw [hsupp p hp]; simp)]
    rw [Finset.sum_image]
    intro a _ b _ h
    exact (Prod.ext_iff.mp h).1
  rw [h1]
  have hstep : ∑ a ∈ A, ‖khalf m P a (P.eval a)‖ ≤ ∑ _a ∈ A, ((m:ℝ))⁻¹ := by
    refine Finset.sum_le_sum (fun a _ => ?_)
    rw [khalf]
    split_ifs with _hc
    · rw [norm_inv, Complex.norm_natCast]
    · simp only [norm_zero]; positivity
  refine hstep.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- `m = 0`: the window is empty
    subst hm
    rw [hA]
    simp
  · -- at most `m` indices contribute, each with weight `m⁻¹`
    have hcard : (A.card : ℝ) ≤ (m:ℝ) := by
      rw [hA, Int.card_Ioc]
      have h2 : (m:ℤ) - (m:ℤ)/2 ≤ (m:ℤ) := by
        have : (0:ℤ) ≤ (m:ℤ)/2 := Int.ediv_nonneg (Int.natCast_nonneg m) (by norm_num)
        omega
      have := Int.toNat_le.mpr h2
      exact_mod_cast this
    have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
    calc (A.card : ℝ) * ((m:ℝ))⁻¹ ≤ (m:ℝ) * (m:ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hmpos.le)
      _ = 1 := by field_simp

/-- **The halved average has bilinear operator norm at most one on `ℓ^p`**: Young's inequality
for the finitely supported averaging kernel `khalf N P`. -/
theorem eLpNorm_khalf_bilinOp_le (P : Polynomial ℤ) (N : ℕ) (p p₁ p₂ : ENNReal)
    (hp : p₁⁻¹ + p₂⁻¹ = p⁻¹) (hp1 : 1 ≤ p) (u v : ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ =>
        Work.KMTAreas.A7.bilinOp (Work.KMTAreas.A7.khalf N P) u v x) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm u p₁ MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm v p₂ MeasureTheory.Measure.count := by
  obtain ⟨hsum, hle⟩ := summable_khalf_tsum_le_one N P
  refine (BilinOpLp (K := khalf N P) hp hp1 hsum u v).trans ?_
  have hm : ENNReal.ofReal (∑' q : ℤ × ℤ, ‖khalf N P q.1 q.2‖) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr hle
  calc ENNReal.ofReal (∑' q : ℤ × ℤ, ‖khalf N P q.1 q.2‖)
        * eLpNorm u p₁ Measure.count * eLpNorm v p₂ Measure.count
      ≤ 1 * eLpNorm u p₁ Measure.count * eLpNorm v p₂ Measure.count :=
        mul_le_mul' (mul_le_mul' hm le_rfl) le_rfl
    _ = eLpNorm u p₁ Measure.count * eLpNorm v p₂ Measure.count := by rw [one_mul]

end

end Work.KMTAreas.A7
